package scalafix.internal.v1

import metaconfig.Conf
import metaconfig.Configured
import scalafix.patch.Patch
import scalafix.rule.RuleName
import scalafix.v0
import scalafix.v1.Rule
import scalafix.v1.SemanticDoc
import scalafix.v1.SemanticRule

class LegacySemanticRule(name: RuleName, fn: v0.SemanticdbIndex => v0.Rule)
    extends SemanticRule(name) {
  private[this] var conf: Conf = Conf.Obj()
  override def withConfig(conf: Conf): Configured[Rule] = {
    LegacyRule.init(conf, fn).map { _ =>
      this.conf = conf
      this
    }
  }
  override def fix(implicit doc: SemanticDoc): Patch = {
    val ctx = doc.doc.toRuleCtx
    val rule = fn(doc.toSemanticdbIndex).init(this.conf).get
    rule.fix(ctx) + LegacyRule.lints(ctx, rule)
  }
}
