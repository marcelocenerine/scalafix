---
layout: docs
title: NoInfer
---

# NoInfer

_Since 0.5.0_

This rule reports errors when the compiler infers certain types.

To use this rule:

- Enable the compiler option `-P:semanticdb:synthetics:on`

By default, no symbols are disabled.
If the rule is configured to disable `scala.Any` and `Predef.any2stringadd`:

```scala
MyCode.scala:7: error: [NoInfer.any] Inferred Any
  List(1, "")
            ^
MyCode.scala:7: error: [NoInfer.any2stringadd] Inferred any2stringadd
  def sum[A](a: A, b: String): String = { a + b }
                                          ^
```

## Configuration

It's possible to configure which symbols should not get inferred.

```tut:invisible
import scalafix.internal.config._
```
```tut:passthrough
println(
scalafix.website.rule("NoInfer", NoInferConfig.default)
)
```
