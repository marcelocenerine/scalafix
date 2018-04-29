package scalafix
package internal.patch

import scala.annotation.tailrec
import scala.collection.immutable.TreeMap
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.meta._
import scala.meta.contrib._
import scala.meta.tokens.Token
import scalafix.internal.config.FilterMatcher
import scalafix.internal.diff.DiffDisable
import scalafix.internal.patch.EscapeHatch._
import scalafix.lint.LintMessage
import scalafix.patch._
import scalafix.rule.RuleName
import scalafix.util.TreeExtractors.Mods

/** EscapeHatch is an algorithm to selectively disable rules. There
  * are two mechanisms to do so: anchored comments and the
  * standard `@SuppressWarnings` annotation. The latter takes
  * precedence over the former in case there are overlaps.
  * See `AnchoredEscapes` and `AnnotatedEscapes` for more details.
  */
class EscapeHatch private (
    anchoredEscapes: AnchoredEscapes,
    annotatedEscapes: AnnotatedEscapes) {

  def filter(
      patchesByName: Map[RuleName, Patch],
      ctx: RuleCtx,
      index: SemanticdbIndex,
      diff: DiffDisable): (Patch, List[LintMessage]) = {
    val usedEscapes = mutable.Set.empty[EscapeFilter]
    val lintMessages = List.newBuilder[LintMessage]

    def isDisabledByEscape(name: RuleName, start: Int): Boolean =
      // annotatedEscapes takes precedence over anchoredEscapes
      annotatedEscapes.isEnabled(name, start) match {
        case (false, Some(culprit)) => // if disabled, there must be a escape
          usedEscapes += culprit
          true
        case _ =>
          val (enabled, culprit) = anchoredEscapes.isEnabled(name, start)
          culprit.foreach(escape => usedEscapes += escape)
          !enabled
      }

    def loop(name: RuleName, patch: Patch): Patch = patch match {
      case AtomicPatch(underlying) =>
        val hasDisabledPatch = {
          val patches = Patch.treePatchApply(underlying)(ctx, index)
          patches.exists { tp =>
            val byGit = diff.isDisabled(tp.tok.pos)
            val byEscape = isDisabledByEscape(name, tp.tok.pos.start)
            byGit || byEscape
          }
        }

        if (hasDisabledPatch) EmptyPatch
        else loop(name, underlying)

      case Concat(a, b) =>
        Concat(loop(name, a), loop(name, b))

      case LintPatch(orphanLint) =>
        val lint = orphanLint.withOwner(name)

        val byGit = diff.isDisabled(lint.position)
        val byEscape = isDisabledByEscape(lint.id, lint.position.start)

        val isLintDisabled = byGit || byEscape

        if (!isLintDisabled) {
          lintMessages += lint
        }

        EmptyPatch

      case e => e
    }

    val patches =
      patchesByName.map { case (name, patch) => loop(name, patch) }.asPatch

    val unusedWarnings =
      (annotatedEscapes.unusedEscapes(usedEscapes) ++
        anchoredEscapes.unusedEscapes(usedEscapes))
        .map(UnusedWarning.at)
    val warnings = lintMessages.result() ++ unusedWarnings
    (patches, warnings)
  }
}

object EscapeHatch {

  private val UnusedWarning = LintCategory
    .warning("", "Unused Scalafix suppression. This can be removed")
    .withOwner(RuleName("UnusedScalafixSuppression"))

  private type EscapeOffset = Int
  private type EscapeTree = TreeMap[EscapeOffset, List[EscapeFilter]]

  private case class EscapeFilter(
      matcher: FilterMatcher,
      cause: Position,
      startOffset: EscapeOffset,
      endOffset: Option[EscapeOffset]) {
    def matches(id: RuleName): Boolean =
      id.identifiers.exists(i => matcher.matches(i.value))
  }

  def apply(tree: Tree, associatedComments: AssociatedComments): EscapeHatch =
    new EscapeHatch(
      AnchoredEscapes(tree, associatedComments),
      AnnotatedEscapes(tree)
    )

  /** Rules are disabled via standard `@SuppressWarnings` annotations. The
    * annotation can be placed in class, object, trait, type, def, val, var,
    * parameters and constructor definitions.
    *
    * Rules can be optionally prefixed with `scalafix:`. Besides helping to
    * users to understand where the rules are coming from, it also allows
    * Scalafix to warn when there are rules unnecessarily being suppressed.
    *
    * Use the keyword "all" to suppress all rules.
    */
  private class AnnotatedEscapes private (escapeTree: EscapeTree) {
    import AnnotatedEscapes._

    def isEnabled(
        ruleName: RuleName,
        position: Int): (Boolean, Option[EscapeFilter]) = {
      val escapesUpToPos = escapeTree.to(position).valuesIterator.flatten
      escapesUpToPos
        .collectFirst {
          case f @ EscapeFilter(_, _, _, Some(end))
              if f.matches(ruleName) && end >= position =>
            (false, Some(f))
        }
        .getOrElse(true -> None)
    }

    def unusedEscapes(used: collection.Set[EscapeFilter]): Iterable[Position] =
      escapeTree.valuesIterator.flatten
        .filter { f =>
          !used.contains(f) &&
          f.cause.text.startsWith(OptionalRulePrefix) // only report unused warnings for Scalafix rules
        }
        .map(_.cause)
        .toList
  }

  private object AnnotatedEscapes {
    private val SuppressWarnings = "SuppressWarnings"
    private val SuppressAll = "all"
    private val OptionalRulePrefix = "scalafix:"

    def apply(tree: Tree): AnnotatedEscapes = {
      val escapes =
        tree.collect {
          case t @ Mods(mods) if hasSuppressWarnings(mods) =>
            val start = t.pos.start
            val end = t.pos.end
            val rules = extractRules(mods)
            val (matchAll, matchOne) = rules.partition(_._1 == SuppressAll)
            val filters = ListBuffer.empty[EscapeFilter]

            // 'all' takes precedence over individual rules. This allows us to warn unused rules later
            for ((_, rulePos) <- matchAll) {
              val matcher = FilterMatcher.matchEverything
              filters += EscapeFilter(matcher, rulePos, start, Some(end))
            }
            for ((rule, rulePos) <- matchOne) {
              val unprefixedRuleName = rule.stripPrefix(OptionalRulePrefix)
              val matcher = FilterMatcher(unprefixedRuleName)
              filters += EscapeFilter(matcher, rulePos, start, Some(end))
            }

            (start, filters.result())
        }

      new AnnotatedEscapes(TreeMap(escapes: _*))
    }

    private def hasSuppressWarnings(mods: List[Mod]): Boolean =
      mods.exists {
        case Mod.Annot(Init(Type.Name(SuppressWarnings), _, _)) => true
        case Mod.Annot(
            Init(Type.Select(_, Type.Name(SuppressWarnings)), _, _)) =>
          true
        case _ => false
      }

    private def extractRules(mods: List[Mod]): List[(String, Position)] = {
      def process(rules: List[Term]) = rules.collect {
        case lit @ Lit.String(rule) =>
          // get the exact position of the rule name (drop surrounding quotes)
          val lo = lit.pos.start + lit.pos.text.indexOf(rule)
          val hi = lo + rule.length
          rule -> Position.Range(lit.pos.input, lo, hi)
      }

      mods.flatMap {
        case Mod.Annot(
            Init(
              Type.Name(SuppressWarnings),
              _,
              List(Term.Apply(Term.Name("Array"), rules) :: Nil))) =>
          process(rules)

        case Mod.Annot(
            Init(
              Type.Select(_, Type.Name(SuppressWarnings)),
              _,
              List(Term.Apply(Term.Name("Array"), rules) :: Nil))) =>
          process(rules)

        case _ => Nil
      }
    }
  }

  /** Rules are disabled via comments with a specific syntax:
    * `scalafix:off` or `scalafix:on` disable or enable rules until the end of file
    * `scalafix:ok` disable rules on an associated expression
    * a list of rules separated by commas can be provided to selectively
    * enable or disable rules otherwise all rules are affected
    *
    * `enabling` and `enabling` contain the offset at which you start applying a filter
    *
    * `unusedEnable` contains the unused `scalafix:on`
    */
  private class AnchoredEscapes private (
      enabling: EscapeTree,
      disabling: EscapeTree,
      unusedEnable: List[Position]) {

    /**
      * a rule r is disabled in position p if there is a comment disabling r at
      * position p1 < p and there is no comment enabling r in position p2 where p1 < p2 < p.
      */
    def isEnabled(
        ruleName: RuleName,
        position: Int): (Boolean, Option[EscapeFilter]) = {
      def findEnableWithinRange(from: EscapeOffset, to: EscapeOffset) = {
        val withinRange = enabling.range(from, to).valuesIterator.flatten
        withinRange.find(_.matches(ruleName))
      }

      @tailrec
      def loop(
          disables: List[EscapeFilter],
          culprit: Option[EscapeFilter]): (Boolean, Option[EscapeFilter]) =
        disables match {
          case x :: xs if x.matches(ruleName) =>
            x.endOffset match {
              case Some(end) =>
                if (position < end) (false, Some(x)) else loop(xs, culprit)
              case None =>
                // the disable escape is open-ended (`scalafix:off`). In this case
                // we need to check whether the rule gets re-enabled before `p`
                val enable = findEnableWithinRange(x.startOffset, position)
                if (!enable.isDefined) (false, Some(x)) else loop(xs, enable)
            }
          case _ :: xs => loop(xs, culprit)
          case Nil => (true, culprit)
        }

      loop(disabling.to(position).valuesIterator.flatten.toList, None)
    }

    def unusedEscapes(used: collection.Set[EscapeFilter]): Iterable[Position] =
      unusedEnable ++
        disabling.valuesIterator.flatten.filterNot(used).map(_.cause)
  }

  private object AnchoredEscapes {
    private val FilterDisable = "\\s?scalafix:off\\s?(.*)".r
    private val FilterEnable = "\\s?scalafix:on\\s?(.*)".r
    private val FilterExpression = "\\s?scalafix:ok\\s?(.*)".r

    def apply(
        tree: Tree,
        associatedComments: AssociatedComments): AnchoredEscapes = {
      val enableBuilder = TreeMap.newBuilder[EscapeOffset, List[EscapeFilter]]
      val disableBuilder = TreeMap.newBuilder[EscapeOffset, List[EscapeFilter]]
      val unusedAnchoredEnable = List.newBuilder[Position]
      val visitedFilterExpression = mutable.Set.empty[Position]
      var currentlyDisabledRules = Set.empty[String]

      def enable(
          rules: String,
          start: EscapeOffset,
          end: Option[EscapeOffset],
          anchor: Token.Comment): Unit =
        enableBuilder += (start -> makeFilters(start, end, anchor, rules))

      def disable(
          rules: String,
          start: EscapeOffset,
          end: Option[EscapeOffset],
          anchor: Token.Comment): Unit =
        disableBuilder += (start -> makeFilters(start, end, anchor, rules))

      def makeFilters(
          start: EscapeOffset,
          end: Option[EscapeOffset],
          anchor: Token.Comment,
          rules: String): List[EscapeFilter] = {
        val splitRules0 = splitRules(rules)

        if (splitRules0.isEmpty) { // wildcard
          EscapeFilter(FilterMatcher.matchEverything, anchor.pos, start, end) :: Nil
        } else {
          getRulesExactPosition(splitRules0, anchor).map {
            case (rule, pos) =>
              EscapeFilter(FilterMatcher(rule), pos, start, end)
          }
        }
      }

      def splitRules(rules: String): List[String] =
        rules.trim.split("\\s*,\\s*").toList

      def getRulesExactPosition(
          rules: List[String],
          anchor: Token.Comment): List[(String, Position)] = {
        val rulesToPos = ListBuffer.empty[(String, Position)]
        var fromIdx = 0

        for (rule <- rules) {
          val idx = anchor.text.indexOf(rule, fromIdx)
          val startPos = anchor.start + idx
          val endPos = startPos + rule.length
          val pos = Position.Range(anchor.input, startPos, endPos)
          fromIdx = idx + rule.length
          rulesToPos += (rule -> pos)
        }
        rulesToPos.result()
      }

      def trackUnusedRules(
          anchor: Token.Comment,
          rules: String,
          enabled: Boolean): Unit = {
        val rules0 = splitRules(rules)
        val rulesToPos = getRulesExactPosition(rules0, anchor)

        if (enabled) {
          if (currentlyDisabledRules.isEmpty && rules0.isEmpty) { // wildcard
            unusedAnchoredEnable += anchor.pos
          } else {
            rulesToPos.foreach {
              case (rule, pos) =>
                if (!currentlyDisabledRules(rule)) unusedAnchoredEnable += pos
            }
          }
        } else {
          currentlyDisabledRules ++= rules0
        }
      }

      tree.foreach { t =>
        associatedComments.trailing(t).foreach {
          // matches simple expressions
          //
          // val a = (
          //   1,
          //   2
          // ) // scalafix:ok RuleA
          //
          case comment @ Token.Comment(FilterExpression(rules))
              if !visitedFilterExpression.contains(comment.pos) =>
            disable(rules, t.pos.start, Some(t.pos.end), comment)
            visitedFilterExpression += comment.pos

          case _ => ()
        }
      }

      tree.tokens.foreach {
        case comment @ Token.Comment(rawComment) =>
          rawComment match {
            // matches off anchors
            //
            // // scalafix:off RuleA
            // ...
            //
            case FilterDisable(rules) =>
              disable(rules, comment.pos.start, None, comment)
              trackUnusedRules(comment, rules, enabled = false)

            // matches on anchors
            //
            // ...
            // // scalafix:on RuleA
            //
            case FilterEnable(rules) =>
              enable(rules, comment.pos.start, None, comment)
              trackUnusedRules(comment, rules, enabled = true)

            // matches expressions not handled by AssociatedComments
            //
            // object Dummy { // scalafix:ok NoDummy
            //   1
            // }
            case FilterExpression(rules)
                if !visitedFilterExpression.contains(comment.pos) =>
              // we approximate the position of the expression to the whole line
              val start = comment.pos.start - comment.pos.startColumn
              disable(rules, start, Some(comment.pos.end), comment)

            case _ => ()
          }

        case _ => ()
      }

      new AnchoredEscapes(
        enableBuilder.result(),
        disableBuilder.result(),
        unusedAnchoredEnable.result())
    }
  }
}
