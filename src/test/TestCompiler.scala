package graphprog.test

object TestCompiler {

  import graphprog.lang.AST._
  import graphprog.lang.{ Executor, Printer, GraphvizHelper, IteratorExecutor }
  import graphprog.Controller._
  import graphprog.Utils._
  import graphprog.lang.Compiler._
  import graphprog.synthesis.Synthesis._
  import scala.collection.mutable.HashMap
  import graphprog.Controller.ObjectLayout
  import TestCommon._

  def main(args: Array[String]) {
    parseCommandLine(args)
    println("Running parse tests")
    testCompiler()
    testClasses()
  }
  val printer = new Printer(Map[String, Value => String](), false)
  
  def testCompiler() {

    def test(text: String): List[Stmt] = {

      //println("\nTesting:\n" + text)
      val result = parse(text)
      //println("Got:\n" + result +" or\n" + printer.stringOfStmts(result))
      result
    }

    def testCheck(text: String, expected: Stmt*) {
      assert(test(text) == expected.toList)
    }

    testCheck("42", 42)
    testCheck("x", "x")
    testCheck("true", true)
    testCheck("false", false)
    testCheck("1 = 1", EQ(1, 1))
    testCheck("1 != 1", NE(1, 1))
    testCheck("1<1", LT(1, 1))
    testCheck("1 <= 1", LE(1, 1))
    testCheck("1 > 1", GT(1, 1))
    testCheck("1 >= 1", GE(1, 1))
    testCheck("x && y", And("x", "y"))
    testCheck("!x", Not("x"))
    testCheck("(!x) && y", And(Not("x"), "y"))
    test("1 + 1 + 1")
    testCheck("1 - x", Minus(1, "x"))
    testCheck("1*1", Times(1, 1))
    testCheck("1 / 1", Div(1, 1))
    testCheck("x := 42", Assign("x", 42))
    testCheck("x := 42\n  y := 1 + 2", Assign("x", 42), Assign("y", Plus(1, 2)))
    testCheck("a[5] := 42", Assign(IntArrayAccess("a", 5), 42))
    test("Array(1,2,3)")
    test("Array(1, 2,  3)")
    test("a := Array(1,2,3)")
    testCheck("null", Null)
    testCheck("x.f", FieldAccess("x", "f"))
    testCheck("p.f.g.h", FieldAccess(FieldAccess(FieldAccess("p", "f"), "g"), "h"))
    testCheck("p.f := 5", Assign(FieldAccess("p", "f"), 5))
    testCheck("a[0][0]", IntArrayAccess(IntArrayAccess("a", 0), 0))
    testCheck("a[0][0] := 42", Assign(IntArrayAccess(IntArrayAccess("a", 0), 0), 42))
    testCheck("swap(a, i, min)", Call("swap", List("a", "i", "min")))
    testCheck("a.length", ArrayLength("a"))
    testCheck("i + 1 to a.length", To(Plus("i", 1), ArrayLength("a")))
    testCheck("i + 1 until a.length - 1", Until(Plus("i", 1), Minus(ArrayLength("a"), 1)))
    testCheck("i in 1 to 10", In("i", To(1, 10)))
    testCheck("i in 1 to a.length", In("i", To(1, ArrayLength("a"))))
    testCheck("i in (i+1) to 10", In("i", To(Plus("i", 1), 10)))
    testCheck("j in (i + 1) to a.length", In("j", To(Plus("i", 1), ArrayLength("a"))))
    testCheck("j in (i + 1) until a.length - 1", In("j", Until(Plus("i", 1), Minus(ArrayLength("a"), 1))))
    // Broken
    //test("1 + 1 * 1")
    //test("1 * 1 + 1")
    //testCheck("p.f.length", ArrayLength(FieldAccess("p", "f")))
    //testCheck("0 to n", To(0, "n"))
    //testCheck("0 until n", Until(0, "n"))
    //testCheck("i in i+1 to 10", In("i", To(Plus("i", 1), 10)))
  }

  def testClasses() {
    def test(text: String): List[Type] = {
      println("\nTesting:\n" + text)
      val result = parseClasses(text)
      //println("Got:\n" + result +" or\n" + printer.stringOfStmts(result))
      result
    }

    def testCheck(text: String, expected: Stmt*) {
      assert(test(text) == expected.toList)
    }

    //test("class foo")
    test("class foo {}")
    test("class foo { field a : int}")
    test("class foo { field a : int; field b: String; field c: bool }")
    test("class foo { field a : int\nfield b: String\n field c: bool }")
    test("class foo { field a : int; field b: String\n field c: bool }")
    test("class foo { field a : int;\n field b: String\n field c: bool }")
 }
}
