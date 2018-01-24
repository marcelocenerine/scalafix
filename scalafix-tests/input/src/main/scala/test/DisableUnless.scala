/*
rules = [
  DisableUnless
]

DisableUnless.symbols = [
  {
    unless = "test.DisableUnless.IO"
    symbols = [
      {
        symbol = "scala.Predef.println"
        message = "println has side-effects"
      }
      "java.lang.System.currentTimeMillis"
    ]
  }
  {
    unless = "scala.Option"
    symbols = [
      {
        symbol = "test.DisableUnless.dangerousFunction"
        message = "the function may return null"
      }
    ]
  }
]
*/
package test

object DisableUnless {
  object IO { // IO we deserve
    def apply[T](run: => T): Nothing = ???
  }

  println("hi") // assert: DisableUnless.println
  System.currentTimeMillis() // assert: DisableUnless.currentTimeMillis
  IO.apply {
    println("hi") // ok
  }
  IO(println("hi")) // ok
  IO {
    println("hi") // ok
  }
  IO {
    {
      println("hi") // ok
      System.currentTimeMillis() // ok
    }
  }
  IO {
    val a = 1
    val b = {
      println("hi") // ok
      2
    }
  }
  IO {
    def sideEffect(i: Int) = println("not good!") // assert: DisableUnless.println
    (i: Int) => println("also not good!") // assert: DisableUnless.println
  }
  IO {
    class SideEffect {
      def oooops = println("I may escape!") // assert: DisableUnless.println
    }

    new SideEffect() // ok
  }


  class Foo
  def dangerousFunction(): Foo = null // assert: DisableUnless.dangerousFunction

  dangerousFunction() // assert: DisableUnless.dangerousFunction
  Option {
    println("not here") // assert: DisableUnless.println
    dangerousFunction() // ok
  }
  Option.apply(dangerousFunction()) // ok
  Option(dangerousFunction()) // ok

  IO {
    Option(dangerousFunction()) // ok
  }

  Option(IO(println("boo!"))) // ok
}
