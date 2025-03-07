package dotty.tools.pc.tests.completion

import scala.meta.internal.pc.PresentationCompilerConfigImpl
import scala.meta.pc.PresentationCompilerConfig

import dotty.tools.pc.base.BaseCompletionSuite

import org.junit.Test

class CompletionCaseSuite extends BaseCompletionSuite:

  def paramHint: Option[String] = Some("param-hint")

  override def config: PresentationCompilerConfig =
    PresentationCompilerConfigImpl().copy(
      _parameterHintsCommand = paramHint
    )

  @Test def `empty` =
    check(
      """
        |object A {
        |  Option(1) match {
        |    @@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `typed` =
    check(
      """package pkg
        |trait Animal
        |case class Bird(name: String) extends Animal
        |class Cat extends Animal
        |class Dog extends Animal
        |object Elephant extends Animal
        |class HasFeet[A, B](e: T, f: B) extends Animal
        |class HasMouth[T](e: T) extends Animal
        |case class HasWings[T](e: T) extends Animal
        |case object Seal extends Animal
        |object A {
        |  val animal: Animal = ???
        |  animal match {
        |    @@
        |  }
        |}""".stripMargin,
      """|case _: Animal => pkg
         |case Bird(name) => pkg
         |case _: Cat => pkg
         |case _: Dog => pkg
         |case Elephant => pkg
         |case _: HasFeet[?, ?] => pkg
         |case _: HasMouth[?] => pkg
         |case HasWings(e) => pkg
         |case Seal => pkg
         |""".stripMargin
    )

  @Test def `case` =
    check(
      """package kase
        |object A {
        |  Option(1) match {
        |    cas@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `trailing` =
    check(
      """
        |object A {
        |  Option(1) match {
        |    case Some(a) =>
        |    cas@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `trailing-block` =
    check(
      """
        |object A {
        |  Option(1) match {
        |    case Some(a) => println(a)
        |    cas@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `either` =
    check(
      """
        |object A {
        |  (null: Either[Int, String]) match {
        |    case@@
        |  }
        |}""".stripMargin,
      """|case Left(value) => scala.util
         |case Right(value) => scala.util
         |""".stripMargin
    )

  @Test def `sealed-import` =
    check(
      """
        |object A {
        |  val t: scala.util.Try[Int] = ???
        |  t match {
        |    case@@
        |  }
        |}""".stripMargin,
      """|case Failure(exception) => scala.util
         |case Success(value) => scala.util
         |""".stripMargin
    )

  @Test def `sealed-two` =
    check(
      """
        |object Outer {
        |  sealed trait Adt
        |  sealed trait AdtTwo extends Adt
        |  case class Cls(a: Int, b: String) extends AdtTwo
        |}
        |object A {
        |  val t: Outer.Adt = ???
        |  t match {
        |    case@@
        |  }
        |}""".stripMargin,
      // Assert we don't include AdtTwo in the results.
      """|case Cls(a, b) => test.Outer
         |""".stripMargin
    )

  // TODO: `Left` has conflicting name in Scope, we should fix it so the result is the same as for scala 2
  // Issue: https://github.com/scalameta/metals/issues/4368
  @Test def `sealed-conflict` =
    check(
      """
        |object A {
        |  val e: Either[Int, String] = ???
        |  type Left = String
        |  e match {
        |    case@@
        |  }
        |}""".stripMargin,
      """|case scala.util.Left(value) =>
         |case Right(value) => scala.util
         |""".stripMargin
    )

  @Test def `sealed-import-edit` =
    checkEdit(
      """
        |object A {
        |  val t: scala.util.Try[Int] = ???
        |  t match {
        |    case@@
        |  }
        |}""".stripMargin,
      """
        |import scala.util.Failure
        |
        |object A {
        |  val t: scala.util.Try[Int] = ???
        |  t match {
        |    case Failure(exception) => $0
        |  }
        |}""".stripMargin,
      filter = _.contains("Failure")
    )

  @Test def `local-case` =
    checkEdit(
      """
        |import scala.util.Try
        |import scala.util.Success
        |object A {
        |  Try(1) match {
        |    case Success(x) =>
        |      println(x)
        |    case@@
        |  }
        |}""".stripMargin,
      """
        |import scala.util.Try
        |import scala.util.Success
        |import scala.util.Failure
        |object A {
        |  Try(1) match {
        |    case Success(x) =>
        |      println(x)
        |    case Failure(exception) => $0
        |  }
        |}""".stripMargin,
      filter = _.contains("Failure")
    )

  @Test def `apply-type` =
    check(
      """
        |object A {
        |  List(Option(1)).foreach[Int] {
        |    case None => 1
        |    case@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `lambda-function1` =
    check(
      """
        |object A {
        |  List(Option(1)).foreach {
        |    case None =>
        |    case@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `lambda-function2` =
    check(
      """
        |object A {
        |  List(1).foldLeft(0) {
        |    case (1, 2) =>
        |    case@@
        |  }
        |}""".stripMargin,
      """|case (Int, Int) => scala
         |""".stripMargin
    )

  @Test def `lambda` =
    check(
      """
        |object A {
        |  List(Option(1)).foreach {
        |    ca@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |case (exhaustive) Option (2 cases)
         |""".stripMargin
    )

  @Test def `lambda-case` =
    check(
      """
        |object A {
        |  List(Option(1)).foreach {
        |    case None =>
        |    ca@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `lambda-case-block` =
    check(
      """
        |object A {
        |  List(Option(1)).foreach {
        |    case None => println(1)
        |    ca@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `lambda-curry` =
    check(
      """
        |object A {
        |  List(Option(1)).map {
        |    ca@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |case (exhaustive) Option (2 cases)
         |""".stripMargin
    )

  @Test def `partial` =
    check(
      """
        |object A {
        |  List(Option(1)).collect {
        |    ca@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |case (exhaustive) Option (2 cases)
         |""".stripMargin
    )

  @Test def `partial-case` =
    check(
      """
        |object A {
        |  List(Option(1)).collect {
        |    case None =>
        |    ca@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `partial-case-block` =
    check(
      """
        |object A {
        |  List(Option(1)).collect {
        |    case None => println(1)
        |    ca@@
        |  }
        |}""".stripMargin,
      """|case None => scala
         |case Some(value) => scala
         |""".stripMargin
    )

  @Test def `infix` =
    check(
      """
        |object A {
        |  List(1) match {
        |    cas@@
        |  }
        |}""".stripMargin,
      """|case head :: next => scala.collection.immutable
         |case Nil => scala.collection.immutable
         |""".stripMargin
    )

  @Test def `brace` =
    checkEditLine(
      """
        |object Main {
        |  ___
        |}
        |""".stripMargin,
      "List(1 -> 2).map { c@@ }",
      "List(1 -> 2).map { case ($0) => }",
      assertSingleItem = false,
      command = paramHint
    )

  @Test def `brace-label` =
    check(
      """
        |object Main {
        |  List(1 -> 2).map { c@@ }
        |}
        |""".stripMargin,
      """|case (Int, Int) => scala
         |""".stripMargin,
      topLines = Some(1)
    )

  @Test def `brace-negative` =
    check(
      """
        |object Main {
        |  List(1 -> 2).map(@@)
        |}
        |""".stripMargin,
      "f = : A => B",
      topLines = Some(1)
    )

  @Test def `brace-function2` =
    checkEditLine(
      """
        |object Main {
        |  ___
        |}
        |""".stripMargin,
      "List(1).foldLeft(0) { cas@@ }",
      "List(1).foldLeft(0) { case ($0) => }",
      assertSingleItem = false,
      command = paramHint
    )

  @Test def `infix-custom` =
    checkEditLine(
      """package pkg
        |object Outer {
        |  sealed trait ADT
        |  case class :+:(a: Int, b: String) extends ADT
        |}
        |object Main {
        |  val l: pkg.Outer.ADT = ???
        |  import pkg.Outer.:+:
        |  l match {
        |    ___
        |  }
        |}
        |""".stripMargin,
      "cas@@",
      "case a :+: b => $0"
    )

  @Test def `infix-conflict` =
    checkEditLine(
      """
        |object Outer {
        |  sealed trait List
        |  case class ::(a: Int, b: String) extends List
        |}
        |object Main {
        |  val l: Outer.List = ???
        |  l match {
        |    ___
        |  }
        |}
        |""".stripMargin,
      "cas@@",
      // Assert we don't use infix syntax because `::` resolves to conflicting symbol in scope.
      "case Outer.::(a, b) => $0"
    )

  @Test def `scala-enum` =
    check(
      """
        |package example
        |enum Color:
        |  case Red, Blue, Green
        |
        |object Main {
        |  val x: Color = ???
        |  x match
        |    case@@
        |}""".stripMargin,
      """|case Color.Blue =>
         |case Color.Green =>
         |case Color.Red =>
         |""".stripMargin
    )

  @Test def `scala-enum2` =
    check(
      """
        |package example
        |enum Color:
        |  case Red, Blue, Green
        |
        |object Main {
        |  val colors = List(Color.Red, Color.Green).map{
        |    case C@@
        |  }
        |}""".stripMargin,
      """|Color.Blue
         |Color.Green
         |Color.Red
         |""".stripMargin,
      topLines = Some(3)
    )

  @Test def `scala-enum-with-param` =
    checkEdit(
      """
        |package withenum {
        |enum Foo:
        |  case Bla, Bar
        |  case Buzz(arg1: Int, arg2: Int)
        |}
        |package example
        |object Main {
        |  val x: withenum.Foo = ???
        |  x match
        |    case@@
        |}""".stripMargin,
      """
        |import withenum.Foo
        |
        |package withenum {
        |enum Foo:
        |  case Bla, Bar
        |  case Buzz(arg1: Int, arg2: Int)
        |}
        |package example
        |object Main {
        |  val x: withenum.Foo = ???
        |  x match
        |    case Foo.Buzz(arg1, arg2) => $0
        |}""".stripMargin,
      filter = _.contains("Buzz")
    )

  @Test def `single-case-class` =
    check(
      """
        |package example
        |case class Foo(a: Int, b: Int)
        |
        |object A {
        |
        |  List(Foo(1,2)).map{ cas@@ }
        |}""".stripMargin,
      """|case Foo(a, b) => example
         |""".stripMargin
    )

  @Test def `private-member` =
    check(
      """
        |package example
        |import scala.collection.immutable.Vector
        |object A {
        |  val x: Vector = ???
        |  x match {
        |    ca@@
        |  }
        |}""".stripMargin,
      ""
    )

  @Test def `private-member-2` =
    check(
      """
        |package example
        |object A {
        |  private enum A:
        |    case B, C
        |  def testMe(a: A) =
        |    a match
        |      cas@@
        |}""".stripMargin,
      """|case A.B =>
         |case A.C =>""".stripMargin
    )

  @Test def `same-line` =
    check(
      """
        |object A {
        |  Option(1) match {
        |    case Some(a) => cas@@
        |  }
        |}""".stripMargin,
      ""
    )

  @Test def `exhaustive-enum-tags` =
    check(
      s"""|object Tags:
          |  trait Hobby
          |  trait Chore
          |  trait Physical
          |
          |
          |import Tags.*
          |
          |enum Activity:
          |  case Reading(book: String, author: String) extends Activity, Hobby
          |  case Sports(time: Long, intensity: Double) extends Activity, Physical, Hobby
          |  case Cleaning                              extends Activity, Physical, Chore
          |  case Singing(song: String)                 extends Activity, Hobby
          |  case DishWashing(amount: Int)              extends Activity, Chore
          |
          |import Activity.*
          |
          |def energySpend(act: Activity & (Physical | Chore)): Double =
          |  act match
          |    cas@@
          |
          |""".stripMargin,
      """|case Cleaning =>Activity & Physical & Chore
         |case DishWashing(amount) => test.Activity
         |case Sports(time, intensity) => test.Activity""".stripMargin
    )

  @Test def `exhaustive-enum-tags2` =
    check(
      s"""|object Tags:
          |  trait Hobby
          |  trait Chore
          |  trait Physical
          |
          |
          |import Tags.*
          |
          |enum Activity:
          |  case Reading(book: String, author: String) extends Activity, Hobby
          |  case Sports(time: Long, intensity: Double) extends Activity, Physical, Hobby
          |  case Cleaning                              extends Activity, Physical, Chore
          |  case Singing(song: String)                 extends Activity, Hobby
          |  case DishWashing(amount: Int)              extends Activity, Chore
          |
          |import Activity.*
          |
          |def energySpend(act: Activity & Physical): Double =
          |  act match
          |    cas@@
          |
          |""".stripMargin,
      """|case Cleaning =>Activity & Physical & Chore
         |case Sports(time, intensity) => test.Activity""".stripMargin
    )

  @Test def `exhaustive-enum-tags3` =
    check(
      s"""|object Tags:
          |  sealed trait Hobby
          |  sealed trait Chore
          |  sealed trait Physical
          |
          |
          |import Tags.*
          |
          |enum Activity:
          |  case Reading(book: String, author: String) extends Activity, Hobby
          |  case Sports(time: Long, intensity: Double) extends Activity, Physical, Hobby
          |  case Cleaning                              extends Activity, Physical, Chore
          |  case Singing(song: String)                 extends Activity, Hobby
          |  case DishWashing(amount: Int)              extends Activity, Chore
          |
          |import Activity.*
          |
          |def energySpend(act: Hobby | Physical): Double =
          |  act match
          |    cas@@
          |
          |""".stripMargin,
      """|case Cleaning =>Activity & Physical & Chore
         |case Reading(book, author) => test.Activity
         |case Singing(song) => test.Activity
         |case Sports(time, intensity) => test.Activity""".stripMargin
    )
