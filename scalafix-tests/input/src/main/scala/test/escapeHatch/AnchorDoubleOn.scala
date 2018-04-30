/*
rules = [
  "class:scalafix.test.NoDummy",
]
*/
package test.escapeHatch

// On and Off anchor set the filter independently 
// of how many time it was turned off

/* scalafix:off */ // assert: UnusedScalafixSuppression
/* scalafix:off NoDummy */ // assert: UnusedScalafixSuppression
/* scalafix:off NoDummy */ // assert: UnusedScalafixSuppression
/* scalafix:on NoDummy */
/* scalafix:on NoDummy */ // assert: UnusedScalafixSuppression
/* scalafix:on NoDummy */ // assert: UnusedScalafixSuppression
/* scalafix:on NoDummy */ // assert: UnusedScalafixSuppression
/* scalafix:on */
/* scalafix:on */ // assert: UnusedScalafixSuppression
/* scalafix:on */ // assert: UnusedScalafixSuppression
/* scalafix:on */ // assert: UnusedScalafixSuppression

object AnchorDoubleOn {
  object Dummy // assert: NoDummy
}