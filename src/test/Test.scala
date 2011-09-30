package graphprog.test

object Test {

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
    //testExecute()
    //testIteratorExecute()
    //testCompiler()
    //testGraphviz()
    testSynthesize()
  }

  val printer = new Printer(Map[String, Value => String](), false)

  def testExecute() {

    def test(memory: Memory, stmts: List[Stmt], functions: Map[String, Program], holeHandler: Option[(Memory, Hole) => Stmt] = None) {
      println("Testing with memory " + printer.stringOfMemory(memory) + "\n" + printer.stringOfStmts(stmts))
      val executor = holeHandler match { case Some(holeHandler) => new Executor(functions, printer, holeHandler, true) case None => new Executor(functions, printer, shouldPrint = true) }
      val (result, finalMemory) = executor.executeStmts(memory, stmts)
      println("Result: " + printer.stringOfValue(result) + " with memory " + printer.stringOfMemory(finalMemory))
    }

    def testShouldFail(memory: Memory, stmts: List[Stmt], functions: Map[String, Program]) {
      try {
	test(memory, stmts, functions)
      } catch {
	case e =>
	  println("Good, we caught the error " + e)
	  return
      }
      assert(false, "We should have failed this test but we didn't.")
    }

    test(new Memory(List(("a" -> IntArray(0, List(3, 2, 4, 5, 1).toArray)))), List(
      Assign("bad", false),
      Assign("j", 1),
      LT(IntArrayAccess("a", 1), IntArrayAccess("a", 0)),
      Assign("min", 1),
      Assign("j", 2),
      LT(IntArrayAccess("a", 2), IntArrayAccess("a", 1)),
      Assign("j", 3),
      LT(IntArrayAccess("a", 3), IntArrayAccess("a", 1)),
      Assign("j", 4),
      LT(IntArrayAccess("a", 4), IntArrayAccess("a", 1)),
      Assign("min", 4),
      Assign("if1", false),
      Assign("if22", false),
      Assign("if23", false),
      Assign("if31", false),
      Assign("if32", false),
      Assign("if42", false),
      Assign("if43", false),
      Assign("if57", false),
      If(EQ("j", 4), List(Assign("if1", true)), List(), List()),
      If(EQ("j", 3), List(Assign("bad", true)), List(), List(Assign("if22", true), Assign("if23", true))),
      If(EQ("j", 4), List(Assign("if31", true),Assign("if32", true)), List(), List(Assign("bad", true))),
      If(EQ("j", 3), List(Assign("bad", true)), List((EQ("j", 4), List(Assign("if42", true),Assign("if43", true))), (EQ("j", 5), List(Assign("bad", true),Assign("bad", true)))), List(Assign("bad", true))),
      If(EQ("j", 1), List(Assign("bad", true),Assign("bad", true)), List((EQ("j", 2), List(Assign("bad", true),Assign("bad", true))), (EQ("j", 3), List(Assign("bad", true),Assign("bad", true)))), List(Assign("if57", true))),
      Assert(EQ("if1", true)),
      Assert(EQ("if22", true)),
      Assert(EQ("if23", true)),
      Assert(EQ("if31", true)),
      Assert(EQ("if32", true)),
      Assert(EQ("if42", true)),
      Assert(EQ("if43", true)),
      Assert(EQ("if57", true)),
      Assert(EQ("bad", false))
    ), Map.empty)

    // Test aliasing and double deref
    println("")
    test(new Memory(List(("o" -> Object(0, "Foo", HashMap.empty ++ List(("x" -> 0), ("f" -> Object(1, "Bar", HashMap.empty ++ List(("y" -> 0))))))))), List(
      Assign("p", "o"),
      Assign("q", "o"),
      Assign(FieldAccess("p", "x"), 1),
      Assign(FieldAccess(FieldAccess("q", "f"), "y"), 42)
    ), Map.empty)

    // Test loops
    println("")
    test(new Memory(List(("x" -> IntConstant(0)), ("list" -> Object(0, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null))))))))), List(
      Assign("cur", "list"),
      Assign("sum1", 0),
      Assign("sum2", 0),
      Loop(NE("cur", Null), List(
	Assign("sum1", Plus("sum1", FieldAccess("cur", "value"))),
	Assign("cur", FieldAccess("cur", "next"))
      )),
      Assign("i", 0),
      Loop(LE("i", "sum1"), List(
	Assign("sum2", Plus("sum2", "i")),
	Assign("i", Plus("i", 1))
      )),
      Assert(EQ("sum1", 3)),
      Assert(EQ("sum2", 6))
    ), Map.empty)

    println("")
    test(new Memory(List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null))))))))), List(
      Assign("cur", ObjectID(1)),
      Assign("prev", Null),
      Iterate(List(
	(NE(ObjectID(1), Null), List(
	  Assign("next", ObjectID(2)),
	  Assign(FieldAccess("cur", "next"), Null),
	  Assign("prev", ObjectID(1)),
	  Assign("cur", ObjectID(2))
	)),
	(NE(ObjectID(2), Null), List(
	  Assign("next", Null),
	  Assign(FieldAccess("cur", "next"), ObjectID(1)),
	  Assign("prev", ObjectID(2)),
	  Assign("cur", Null)
	)),
	(NE(Null, Null), List())
      )),
      Assert(And(EQ(FieldAccess(ObjectID(2), "next"), ObjectID(1)), EQ(FieldAccess(FieldAccess(ObjectID(2), "next"), "next"), Null))),
      ObjectID(2)
    ), Map.empty)

    println("")
    test(new Memory(List(("a" -> IntArray(0, List(3, 2, 4, 5, 1).toArray)))), List(
      Call("swap", List("a", 0, 4)),
      Assert(EQ(IntArrayAccess("a", 0), 1)),
      Assert(EQ(IntArrayAccess("a", 4), 3)),
      Assign("x", Call("answer", Nil))
    ), mapOfPrograms(swapProgram, answerProgram))
 
    println("")
    test(new Memory, List(
      Assert(EQ(Call("fib", List(0)), 0)),
      Assert(EQ(Call("fib", List(5)), 5))
    ), mapOfPrograms(fibProgram))
 
    println("")
    test(new Memory, List(
      Assign("count1", 0),
      Loop(In("i", To(1, 10)), List(
	Assign("count1", Plus("count1", 1))
      )),
      Assign("count2", 0),
      Loop(In("i", Until(0, 10)), List(
	Assign("count2", Plus("count2", 1))
      )),
      Assert(EQ("count1", 10)),
      Assert(EQ("count2", 10))
    ), Map.empty)
 
    println("")
    test(new Memory, List(
      Loop(In("i", To(1, 10)), List(
	Break
      ))
    ), Map.empty)
 
    println("")
    test(new Memory, List(
      UnorderedStmts(List(
	Assign("x", 42),
	Assign("y", 137)
      ))
    ), Map.empty)
 
    // This should fail
    println("")
    test(new Memory, List(
      UnorderedStmts(List(
	Assign("x", 42),
	Assign("x", 137)
      ))
    ), Map.empty)

    println("")
    test(new Memory(List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null))))))))), List(
      UnorderedStmts(List(
	Assign("list", ObjectID(2)),
	Assign(FieldAccess(ObjectID(1), "next"), Null),
	Assign(FieldAccess(ObjectID(2), "next"), ObjectID(1))
      ))
    ), Map.empty)

    // This should fail
    println("")
    test(new Memory(List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null))))))))), List(
      UnorderedStmts(List(
	Assign("list", ObjectID(2)),
	Assign(FieldAccess(ObjectID(1), "next"), Null),
	Assign(FieldAccess(ObjectID(2), "next"), ObjectID(1)),
	Assign(FieldAccess(ObjectID(2), "next"), ObjectID(2))
      ))
    ), Map.empty)

    println("")
    test(new Memory(List(("a" -> IntArray(0, List(1, 0).toArray)))), List(
      UnorderedStmts(List(
	Assign(IntArrayAccess("a", 0), IntArrayAccess("a", 1)),
	Assign(IntArrayAccess("a", 1), IntArrayAccess("a", 0))
      ))
    ), Map.empty)

    // This should fail
    println("")
    test(new Memory(List(("a" -> IntArray(0, List(1, 0).toArray)))), List(
      UnorderedStmts(List(
	Assign(IntArrayAccess("a", 0), IntArrayAccess("a", 42)),
	Assign(IntArrayAccess("a", 0), IntArrayAccess("a", 137))
      ))
    ), Map.empty)
 
    println("")
    testShouldFail(new Memory, List(
      If(EQ(Div(1, 0), true), List(Assert(false)), Nil, List(Assert(false)))
    ), Map.empty)
 
    // Test scoping
    println("")
    testShouldFail(new Memory, List(
      Loop(In("i", To(1, 10)), List(
	Assign("count", "i")
      )),
      "count"
    ), Map.empty)
 
    // Test scoping
    println("")
    testShouldFail(new Memory, List(
      If(false, List(Assign("x", 1)), Nil, Nil),
      "x"
    ), Map.empty)
 
    // Test scoping
    println("")
    testShouldFail(new Memory, List(
      If(true, List(Assign("x", 1)), Nil, Nil),
      "x"
    ), Map.empty)

    println("")
    test(new Memory(List()), List(
      Println(StringConstant("Hello, world."))
    ), Map.empty)
 
    // Test shadowing
    println("")
    test(new Memory, List(
      Assign("x", true),
      If(true, List(Assign("x", 1)), Nil, Nil),
      "x"
    ), Map.empty)

    // Test array aliasing
    println("")
    test(new Memory(List(("a" -> IntArray(0, List(1, 0).toArray)))), List(
      Assign("b", "a"),
      Assign(IntArrayAccess("a", 0), 42),
      Assert(EQ(IntArrayAccess("b", 0), 42))
    ), Map.empty)

    println("")
    test(new Memory(List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null))))))))), List(
      Assert(EQ(Call("length", List("list")), 2))
    ), mapOfPrograms(lengthProgram))

    println("")
    test(new Memory(List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null))))))))), List(
      Assign("list", Call("reverse", List("list"))),
      Assert(EQ(FieldAccess("list", "value"), IntConstant(2)))
    ), mapOfPrograms(reverseProgram))

    println("")
    test(new Memory(List(("a1" -> IntArray(0, List(3, 2, 4, 5, 1).toArray)), ("a2" -> IntArray(1, Nil.toArray)), ("a3" -> IntArray(2, List(42).toArray)))), List(
      Call("selectionSort", List("a1")),
      Call("checkSorted", List("a1")),
      Call("selectionSort", List("a2")),
      Call("checkSorted", List("a2")),
      Call("selectionSort", List("a3")),
      Call("checkSorted", List("a3"))
    ), mapOfPrograms(selectionSortProgram, checkSortedProgram))

    println("")
    test(new Memory, List(
      Assert(EQ(Call("fact", List(5)), 120))
    ), mapOfPrograms(factProgram))
 
    // Test unknowns in conditions.  Should return ERROR.
    println("")
    test(new Memory, List(
      If(UnseenExpr(), List(Assert(false)), Nil, List(Assert(false)))
    ), Map.empty, Some((m, h) => h match { case _: Unseen => ErrorConstant }))

  }

  def testIteratorExecute() {
    val iteratorExecutor = new IteratorExecutor(Map.empty, printer)
    val stmts = List(
      Assign("x", 42),
      Assign("i", 0),
      Loop(LT("i", 2), List(Assign("i", Plus("i", 1)))),
      Assign("y", 42)
    )
    val mem = iteratorExecutor.executeStmts(new Memory, stmts)._2
    while (iteratorExecutor.hasNext) {
      println(printer.stringOfMemory(mem))
      println(iteratorExecutor.getNext)
      iteratorExecutor.executeNext(mem)
    }
  }

  def testCompiler() {

    def test(text: String): List[Stmt] = {
      println("\nTesting:\n" + text)
      val result = parse(text)
      println("Got:\n" + result +" or\n" + printer.stringOfStmts(result))
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

  def testGraphviz() {

    val graphviz = new GraphvizHelper

    def test(stmts: List[Stmt]) {
      val runtime = Runtime.getRuntime()
      val result = graphviz.toGraphvizString(stmts)
      println(result)
      val p = runtime.exec("dot -Tpng -o tmp.png")
      val out = new java.io.PrintStream(p.getOutputStream())
      out.print(result)
      out.close()
      p.waitFor()
      runtime.exec("xv tmp.png").waitFor()
      //(new java.io.File("tmp.png")).delete()
      println(result)
    }

    test(List(
      //Assign("x", Plus("y", 1))
      //If(GT("x", "y"), List("x"), List(), List("y"))
      Conditional(NE("cur", Null), List(Assign("cur", FieldAccess("cur", "next")))),
      GT("cur", FieldAccess("cur", "next"))
    ))

  }

  def testSynthesize() {

    def test(trace: Trace, printHelpers: PartialFunction[String, Value => String] = Map.empty, precondition: Option[Map[String, Value] => Boolean] = None, postcondition: Option[(Map[String, Value], Map[String, Value], Value) => Boolean] = None, objectComparators: Map[String, (Value, Value) => Int] = Map.empty, fieldLayouts: Map[String, List[List[String]]] = Map.empty, objectLayouts: Map[String, ObjectLayout] = Map.empty) {
      val printer = new Printer(printHelpers, false)
      //println("Program:\n" + printer.stringOfTrace(trace))
      try {
	val result = synthesize(trace, makeSynthesizerFromTrace(trace, printHelpers, precondition = precondition, postcondition = postcondition, objectComparators = objectComparators) _, trace.functions, trace.objectTypes, objectComparators, fieldLayouts, objectLayouts)
	println("Result:\n" + printer.stringOfProgram(result))
      } catch {
	case e => e.printStackTrace
      }
    }

    def stringOfList(v: Value, seen: Set[Int] = Set[Int]()): String = v match {
      case Null => "null"
      case Object(id, _, fields) => 
	if (seen contains id)
	  printer.stringOfValue(fields("value"))
	else
	  printer.stringOfValue(fields("value")) + " -> " + stringOfList(fields("next"), seen + id)
    }
    val listPrintHelpers: PartialFunction[String, Value => String] = (s: String) => s match {
      case "Node" => v => "List(" + stringOfList(v) + ")"
    }

    def makeNode(id: Int, value: Int, next: Value): Value = Object(id, "Node", HashMap.empty ++ List(("value" -> value), ("next" -> next)))

    /*test(new Trace("test1", UnitType, List(("x", 42), ("y", 21), ("z", 5)), Map.empty, Map.empty, List(
      Assign("a", 42),
      Assign("b", 5)
    )))

    println("")
    test(new Trace("values", UnitType, List(("a", 42), ("b", 41)), Map.empty, Map.empty, List(
      42
    )))

    println("")
    test(new Trace("max1", UnitType, List(("x", 42), ("y", 5)), Map.empty, Map.empty, List(
      Conditional(GE(42, 5), List(42))
    )))

    println("")
    test(new Trace("max2", UnitType, List(("x", 42), ("y", 5)), Map.empty, Map.empty, List(
      Conditional(GT(42, 5), List(42))
    )))

    println("")
    test(new Trace("arraytest", UnitType, List(("a", IntArray(0, List(5, 42, 137) toArray))), Map.empty, Map.empty, List(
      Assume(GE(ArrayLength("a"), 3)),
      Assign("x", 5),  // a(0)
      Assign("y", 3),  // (a.length)
      Assign(IntArrayAccess("a", 2), 2)  // 2
    )))

    println("")
    test(new Trace("two_step", UnitType, List(("a", true), ("b", false)), Map.empty, Map.empty, List(
      Assign("x", true)  // Answer whichever has two possibilities to get a second trace
    )))

    println("")
    test(new Trace("object", UnitType, List(("a", 42), ("b", 2), ("o", Object(0, "Foo", new HashMap + ("f" -> IntConstant(42))))), Map.empty, Map.empty ++ List(("Foo", List(("f", IntType)))), List(
      Assume(NE("o", Null)),
      Assign("x", 42),  // o.f
      Assign(FieldAccess("o", "f"), 2)  // b
    )))

    println("")
    test(new Trace("object2", UnitType, List(("o", Object(0, "Foo", new HashMap ++ List(("f" -> Object(1, "Bar", new HashMap + ("g" -> Object(2, "Baz", new HashMap + ("x" -> 0))))), ("h" -> 0))))), Map.empty, List(("Foo", List(("h", IntType), ("f", ObjectType("Bar")))), ("Bar", List(("g", ObjectType("Baz")))), ("Baz", List(("x", IntType)))) toMap, List(
      Assume(And(And(NE("o", Null), NE(FieldAccess("o", "f"), Null)), NE(FieldAccess(FieldAccess("o", "f"), "g"), Null))),
      Assign("p", FieldAccess("o", "f")),
      Assign(FieldAccess(FieldAccess("p", "g"), "x"), 2)
    )))

    println("")
    test(new Trace("object3", UnitType, List(("o", Object(0, "Foo", new HashMap + ("f" -> Object(1, "Bar", new HashMap ++ List(("g" -> Object(2, "Baz", new HashMap + ("x" -> 137))), ("x" -> 42))))))), Map.empty, List(("Foo", List(("f", ObjectType("Bar")))), ("Bar", List(("x", IntType), ("g", ObjectType("Baz")))), ("Baz", List(("x", IntType), ("h", IntType)))) toMap, List(
      Assume(And(And(NE("o", Null), NE(FieldAccess("o", "f"), Null)), NE(FieldAccess(FieldAccess("o", "f"), "g"), Null))),
      Assign("y", 42),
      Assign("z", 137)
    )))

    println("")
    test(new Trace("loop0", UnitType, List(("x", 42), ("y", 137)), Map.empty, Map.empty, List(
      Iterate(List(
	(LT(137, 42), List())
      ))
    )))

    println("")
    test(new Trace("loop_condition", UnitType, List(("max", 2)), Map.empty, Map.empty, List(
      Assign("i", 0),
      Iterate(List(
	(LT("i", "max"), List(Assign("i", 1))),
	(LT("i", "max"), List(Assign("i", 2))),
	(LT("i", "max"), List())
      ))
    )))

    println("")
    test(new Trace("if_condition", UnitType, List(("x", 42), ("y", 18)), Map.empty, Map.empty, List(
      Conditional(LT(42, 18), List(18))  // should be min
    )))

    println("")
    test(new Trace("loop1", UnitType, List(("max", 3)), Map.empty, Map.empty, List(
      Assign("sum", 0),
      Assign("i", 0),
      Iterate(List(
	(LT("i", "max"), List(Assign("sum", 0), Assign("i", 1))),
	(LT("i", "max"), List(Assign("sum", 1), Assign("i", 2))),
	(LT("i", "max"), List(Assign("sum", 3), Assign("i", 3))),
	(LT("i", "max"), List())
      ))
    )))

    println("")
    test(new Trace("array1", UnitType, List(("a", IntArray(0, List(-5, -5, -5, -5, -5, -5, -5, 42, 137) toArray)), ("i", 7), ("j", 8)), Map.empty, Map.empty, List(
      Assume(GE(ArrayLength("a"), 9)),
      Assume(And(GE("i", 0), LT("i", ArrayLength("a")))),
      Assume(And(GE("j", 0), LT("j", ArrayLength("a")))),
      LT(42, 137)
    )))

    println("")
    test(new Trace("selectionSort", UnitType, List(("a", IntArray(0, List(42, 17, 137) toArray))), Map.empty, Map.empty, List(
      Assign("i", 0),  // i := 0
      Iterate(List(
	(LT(0, 2), List(  // i < a.length - 1
	  Assign("min", 0),  // min := i
	  Assign("j", 1),  // j := i + 1
	  Iterate(List(
	    (LT(1, 3), List(Conditional(LT(17, 42), List(Assign("min", 1))), Assign("j", 2))),  // a(j) < a(min), min := j
	    (LT(2, 3), List(Conditional(LT(137, 17), List()), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  Assign("tmp", 42),  // tmp := a(i)
	  Assign(IntArrayAccess("a", "i"), 17),  // a(i) := a(min)
	  Assign(IntArrayAccess("a", "min"), 42),  // a(min) := tmp
	  Assign("i", 1)
	)),
	(LT(1, 2), List(
	  Assign("min", 1),
	  Assign("j", 2),
	  Iterate(List(
	    (LT(2, 3), List(Conditional(LT(137, 42), List()), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  Assign("tmp", 42),  // tmp := a(i)
	  Assign(IntArrayAccess("a", "i"), 42),
	  Assign(IntArrayAccess("a", "min"), 42),
	  Assign("i", 2)
	)),
	(LT(2, 2), List())
      ))
    )))

    println("")
    test(new Trace("object_ids", UnitType, List(("o0", Object(0, "Foo", new HashMap + ("f" -> IntConstant(42)))), ("o1", Object(1, "Foo", new HashMap + ("f" -> IntConstant(42))))), Map.empty, Map.empty ++ List(("Foo", List(("f", IntType)))), List(
      Assume(And(NE("o0", Null), NE("o1", Null))),
      Assign("x", ObjectID(0)),
      Assign("x", ObjectID(1))
    )))

    println("")
    test(new Trace("circular_objects", UnitType, List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null)))))))), Map.empty, Map.empty + ("Node" -> List(("value", IntType), ("next", ObjectType("Node")))), List(
      Assume(And(NE("list", Null), NE(FieldAccess("list", "next"), Null))),
      Assign(FieldAccess(FieldAccess("list", "next"), "next"), ObjectID(1)),
      "list"
    )), listPrintHelpers, None, None, listComparator, listFieldLayout, listLayout)

    println("")
    test(new Trace("rev_list", UnitType, List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null)))))))), Map.empty, listTypes, List(
      Assign("cur", ObjectID(1)),
      Assign("prev", Null),
      Iterate(List(
	(NE(ObjectID(1), Null), List(
	  Assign("next", ObjectID(2)),
	  Assign(FieldAccess("cur", "next"), Null),
	  Assign("prev", ObjectID(1)),
	  Assign("cur", ObjectID(2))
	)),
	(NE(ObjectID(2), Null), List(
	  Assign("next", Null),
	  Assign(FieldAccess("cur", "next"), ObjectID(1)),
	  Assign("prev", ObjectID(2)),
	  Assign("cur", Null)
	)),
	(NE(Null, Null), List())
      )),
      ObjectID(2)
    )), listPrintHelpers, None, None, listComparator, listFieldLayout, listLayout)

    println("")
    test(new Trace("average_list", UnitType, List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 42), ("next" ->  Object(2, "Node", HashMap.empty ++ List(("value" -> 17), ("next" -> Null)))))))), Map.empty, listTypes, List(
      Assume(NE("list", Null)),
      Assign("sum", 0),
      Assign("count", 0),
      Assign("cur", ObjectID(1)),
      Iterate(List(
	(NE(ObjectID(1), Null), List(
	  Assign("sum", 42),
	  Assign("count", 1),
	  Assign("cur", ObjectID(2))
	)),
	(NE(ObjectID(2), Null), List(
	  Assign("sum", 42 + 17),
	  Assign("count", 2),
	  Assign("cur", Null)
	)),
	(NE(Null, Null), List())
      )),
      Div("sum", "count")
    )), listPrintHelpers, None, None, listComparator, listFieldLayout, listLayout)

    println("")
    test(new Trace("array_zero", IntType, List(("a", IntArray(0, List(42, 137) toArray)), ("x", 13)), Map.empty, Map.empty, List(
      Assume(GT(ArrayLength("a"), 0)),
      55
    )))

    println("")
    test(new Trace("find1", UnitType, List(("target", 42), ("a", IntArray(0, List(8, 11, 42) toArray))), Map.empty, Map.empty, List(
      Assign("i", 0),
      Iterate(List(
	(LT(0, 3), List(
	  Conditional(EQ(8, 42), List(Assign("i", 1)))
	)),
	(LT(1, 3), List(
	  Conditional(EQ(11, 42), List(Assign("i", 2)))
	)),
	(LT(2, 3), List(
	  Conditional(EQ(42, 42), List(Break))
	))
      )),
      "i"
    )))

    println("")
    test(new Trace("find2", UnitType, List(("target", 42), ("a", IntArray(0, List(8, 11, 42) toArray))), Map.empty, Map.empty, List(
      Assign("i", 0),
      Iterate(List(
	(LT(0, 3), List(
	  Conditional(EQ(8, 42), List()),
	  Assign("i", 1)
	)),
	(LT(1, 3), List(
	  Conditional(EQ(11, 42), List()),
	  Assign("i", 2)
	)),
	(LT(2, 3), List(
	  Conditional(EQ(42, 42), List(Break))
	))
      )),
      "i"
    )))

    println("")
    test(new Trace("find3", UnitType, List(("target", 42), ("a", IntArray(0, List(8, 11, 42) toArray))), Map.empty, Map.empty, List(
      Assign("found", false),
      Assign("i", 0),
      Iterate(List(
	(LT(0, 3), List(
	  Conditional(EQ(8, 42), List()),
	  Assign("i", 1)
	)),
	(LT(1, 3), List(
	  Conditional(EQ(11, 42), List()),
	  Assign("i", 2)
	)),
	(LT(2, 3), List(
	  Conditional(EQ(42, 42), List(Assign("found", true), Break))
	))
      )),
      "found"
    )))

    println("")
    test(new Trace("intersect", UnitType, List(("a1", IntArray(0, List(8, 42, 137) toArray)), ("a2", IntArray(1, List(42, 17, 8) toArray))), mapOfPrograms(containsProgram), Map.empty, List(
      UnorderedStmts(List(
	Assign("count", 0),
	Assign("i", 0)
      )),
      Iterate(List(
	(LT(0, 3), List(
	  Assign("j", 0),
	  Iterate(List(
	    (LT(0, 3), List(
	      Conditional(EQ(8, 42), List()),
	      Assign("j", 1)
	    )),
	    (LT(1, 3), List(
	      Conditional(EQ(8, 17), List()),
	      Assign("j", 2)
	    )),
	    (LT(2, 3), List(
	      Conditional(EQ(8, 8), List(Assign("count", 1), Break))
	    ))
	  )),
	  Assign("i", 1)
	)),
	(LT(1, 3), List(
	  Assign("j", 0),
	  Iterate(List(
	    (LT(0, 3), List(
	      Conditional(EQ(42, 42), List(Assign("count", 2), Break))
	    ))
	  )),
	  Assign("i", 2)
	)),
	(LT(2, 3), List(
	  Assign("j", 0),
	  Iterate(List(
	    (LT(0, 3), List(
	      Conditional(EQ(137, 42), List()),
	      Assign("j", 1)
	    )),
	    (LT(1, 3), List(
	      Conditional(EQ(137, 17), List()),
	      Assign("j", 2)
	    )),
	    (LT(2, 3), List(
	      Conditional(EQ(137, 8), List()),
	      Assign("j", 3)
	    )),
	    (LT(3, 3), List())
	  )),
	  Assign("i", 3)
	)),
	(LT(3, 3), List())
      )),
      2
    )))

    println("")
    test(new Trace("call1", UnitType, Nil, mapOfPrograms(answerProgram, timesthreeProgram), Map.empty, List(
      Assign("y", 126),
      Assign("x", 42)
    )))

    println("")
    test(new Trace("array_equality", UnitType, List(("a", IntArray(0, List(42, 137) toArray))), Map.empty, Map.empty, List(
      Assign("b", "a"),
      EQ("a", "b")
    )))

    println("")
    test(new Trace("selectionSortSwap", UnitType, List(("a", IntArray(0, List(42, 17, 137) toArray))), mapOfPrograms(swapProgram), Map.empty, List(
      Assign("i", 0),  // i := 0
      Iterate(List(
	(LT(0, 2), List(  // i < a.length - 1
	  Assign("min", 0),  // min := i
	  Assign("j", 1),  // j := i + 1
	  Iterate(List(
	    (LT(1, 3), List(Conditional(LT(17, 42), List(Assign("min", 1))), Assign("j", 2))),  // a(j) < a(min), min := j
	    (LT(2, 3), List(Conditional(LT(137, 17), List()), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  Call("swap", List("a", 0, 1)),  // swap(a, i, min)
	  Assign("i", 1)
	)),
	(LT(1, 2), List(
	  Assign("min", 1),
	  Assign("j", 2),
	  Iterate(List(
	    (LT(2, 3), List(Conditional(LT(137, 42), List()), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  Call("swap", List("a", 1, 1)),  //. swap(a, i, min)
	  Assign("i", 2)
	)),
	(LT(2, 2), List())
      ))
    )))

    println("")
    test(new Trace("call2", UnitType, List(("x", 5), ("y", 5)), mapOfPrograms(timesthreeProgram), Map.empty, List(
      Assign("z", 15)
    )))

    println("")
    test(new Trace("call3", UnitType, List(("x", 5), ("y", 5)), mapOfPrograms(timesthreeProgram), Map.empty, List(
      15
    )))

    println("")
    test(new Trace("call4", UnitType, List(("a", IntArray(0, List(17, 42) toArray)), ("x", 0), ("y", 1)), mapOfPrograms(swapProgram), Map.empty, List(
      Assume(And(And(GE("x", 0), GE("y", 0)), And(GT(ArrayLength("a"), "x"), GT(ArrayLength("a"), "y")))),
      Call("swap", List("a", 0, 1))
    )))

    println("")
    test(new Trace("selectionSort2", UnitType, List(("a", IntArray(0, List(137, 17, 42) toArray))), mapOfPrograms(swapProgram), Map.empty, List(
      Assign("i", 0),  // i := 0
      Iterate(List(
	(LT(0, 2), List(  // i < a.length - 1
	  Assign("min", 0),  // min := i
	  Assign("j", 1),  // j := i + 1
	  Iterate(List(
	    (LT(1, 3), List(Conditional(LT(17, 137), List(Assign("min", 1))), Assign("j", 2))),  // a(j) < a(min), min := j
	    (LT(2, 3), List(Conditional(LT(42, 17), List()), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  Call("swap", List("a", 0, 1)),  // swap(a, i, min)
	  Assign("i", 1)
	)),
	(LT(1, 2), List(
	  Assign("min", 1),
	  Assign("j", 2),
	  Iterate(List(
	    (LT(2, 3), List(Conditional(LT(42, 137), List(Assign("min", 2))), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  Call("swap", List("a", 1, 2)),  // swap(a, i, min)
	  Assign("i", 2)
	)),
	(LT(2, 2), List())
      ))
    )))

    println("")
    test(new Trace("novar", UnitType, List(("x", 2)), mapOfPrograms(swapProgram), Map.empty, List(
      2  // Try giving "j" or something that doesn't exist.
    )))

    println("")
    test(new Trace("inTest", UnitType, List(("a", IntArray(0, List(137, 17, 42) toArray))), mapOfPrograms(swapProgram), Map.empty, List(
      Iterate(List(
	(Assign("i", 0), List(  // i < a.length
	  Assign(IntArrayAccess("a", 0), 0)
	)),
	(Assign("i", 1), List(  // i < a.length
	  Assign(IntArrayAccess("a", 1), 0)
	)),
	(Assign("i", 2), List(  // i < a.length
	  Assign(IntArrayAccess("a", 2), 0)
	))
      ))
    )))

    println("")
    test(new Trace("selectionSortForLoop", UnitType, List(("a", IntArray(0, List(137, 17, 42) toArray))), mapOfPrograms(swapProgram), Map.empty, List(
      Iterate(List(
	(Assign("i", 0), List(  // i < a.length - 1
	  Assign("min", 0),  // min := i
	  Iterate(List(
	    (Assign("j", 1), List(Conditional(LT(17, 137), List(Assign("min", 1))))),  // a(j) < a(min), min := j
	    (Assign("j", 2), List(Conditional(LT(42, 17), List())))
	  )),
	  Call("swap", List("a", 0, 1))  // swap(a, i, min)
	)),
	(Assign("i", 1), List(
	  Assign("min", 1),
	  Iterate(List(
	    (Assign("j", 2), List(Conditional(LT(42, 137), List(Assign("min", 2)))))
	  )),
	  Call("swap", List("a", 1, 2))  // swap(a, i, min)
	))
      ))
    )))

    println("")
    test(new Trace("findLoop", UnitType, List(("target", 42), ("a", IntArray(0, List(8, 11, 42, 137) toArray))), Map.empty, Map.empty, List(
      Iterate(List(
	(Assign("i", 0), List(
	  Conditional(EQ(8, 42), List())
	)),
	(Assign("i", 1), List(
	  Conditional(EQ(11, 42), List())
	)),
	(Assign("i", 2), List(
	  Conditional(EQ(42, 42), List(Break))
	))
      ))
    )))

    // println("")
    // test(new Trace("intersectForLoop", UnitType, List(("a1", IntArray(0, List(8, 42, 137) toArray)), ("a2", IntArray(1, List(42, 137, 17) toArray))), Map.empty, Map.empty, List(
    //   Assign("count", LiteralExpr(0)),
    //   Iterate(List(
    // 	(Assign("i", 0), List(
    // 	  Iterate(List(
    // 	    (Assign("j", 0), List(
    // 	      Conditional(EQ(8, 42), List())
    // 	    )),
    // 	    (Assign("j", 1), List(
    // 	      Conditional(EQ(8, 137), List())
    // 	    )),
    // 	    (Assign("j", 2), List(
    // 	      Conditional(EQ(8, 17), List())
    // 	    ))
    // 	  ))
    // 	)),
    // 	(Assign("i", 1), List(
    // 	  Iterate(List(
    // 	    (Assign("j", 0), List(
    // 	      Conditional(EQ(42, 42), List(Assign("count", 1), Break))
    // 	    ))
    // 	  ))
    // 	)),
    // 	(Assign("i", 2), List(
    // 	  Iterate(List(
    // 	    (Assign("j", 0), List(
    // 	      Conditional(EQ(137, 42), List())
    // 	    )),
    // 	    (Assign("j", 1), List(
    // 	      Conditional(EQ(137, 137), List(Assign("count", 2), Break))
    // 	    ))
    // 	  ))
    // 	))
    //   )),
    //   2
    // )))

    println("")
    test(new Trace("literals", UnitType, List(("target", 42), ("a", IntArray(0, List(8, 11, 42, 137) toArray))), Map.empty, Map.empty, List(
      LiteralAction(Assign("i", 0)),
      //Conditional(EQ(LiteralExpr("target"), LiteralExpr(42)), Nil),
      Iterate(List(
	(LiteralExpr(LT("i", ArrayLength("a"))), List(
	  LiteralAction(Assign("i", Plus("i", 1)))
	)),
	(LiteralExpr(LT("i", ArrayLength("a"))), List(
	  LiteralAction(Assign("i", Plus("i", 1)))
	)),
	(LiteralExpr(LT("i", ArrayLength("a"))), List(
	  LiteralAction(Assign("i", Plus("i", 1)))
	)),
	(LiteralExpr(LT("i", ArrayLength("a"))), List(
	  LiteralAction(Assign("i", Plus("i", 1)))
	)),
	(LiteralExpr(LT("i", ArrayLength("a"))), List(
	))
      ))
    )))

    println("")
    test(new Trace("negation", UnitType, List(("a" -> true), ("b" -> false)), Map.empty, Map.empty, List(
      true
    )))

    println("")
    test(new Trace("unseen", UnitType, List(("x" -> 7), ("y" -> 42)), Map.empty, Map.empty, List(
      Println(StringConstant("For unseen hole, use same as this conditional (x := y, y := x+1), then ensure the second one could be either y+1 or x+1.")),
      Conditional(LT(7, 42), List(
	Assign("x", "y"),
	Assign("y", Plus("x", 1))
      )),
      Assert(EQ("y", Plus("x", 1)))
    )))

    println("")
    test(new Trace("arrayCloning", UnitType, List(("a", IntArray(0, List(8, 11, 42, 137) toArray))), Map.empty, Map.empty, List(
      Assume(GT(ArrayLength("a"), 0)),
      Assign("b", "a"),
      Assign(IntArrayAccess("a", 0), LiteralExpr(13)),
      Println(StringConstant("The next line should be a[0] or b[0]")),
      13  
    )))

    println("")
    test(new Trace("unordered1", UnitType, List(("a" -> 42), ("b" -> 137), ("c" -> 41)), Map.empty, Map.empty, List(
      UnorderedStmts(List(
	Assign("x", 42),
	Assign("y", 137)
      ))
    )))

    println("")
    test(new Trace("rev_list_with_unordered", UnitType, List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null)))))))), Map.empty, listTypes, List(
      Assign("cur", ObjectID(1)),
      Assign("prev", Null),
      Iterate(List(
	(NE(ObjectID(1), Null), List(
	  UnorderedStmts(List(
	    Assign(FieldAccess("cur", "next"), Null),
	    Assign("prev", ObjectID(1)),
	    Assign("cur", ObjectID(2))
	  ))
	)),
	(NE(ObjectID(2), Null), List(
	  UnorderedStmts(List(
	    Assign(FieldAccess("cur", "next"), ObjectID(1)),
	    Assign("prev", ObjectID(2)),
	    Assign("cur", Null)
	  ))
	)),
	(NE(Null, Null), List())
      )),
      ObjectID(2)
    )), listPrintHelpers, None, None, listComparator, listFieldLayout, listLayout)

    println("")
    test(new Trace("selectionSort2WithUnordered", UnitType, List(("a", IntArray(0, List(137, 17, 42) toArray))), Map.empty, Map.empty, List(
      Assign("i", 0),  // i := 0
      Iterate(List(
	(LT(0, 2), List(  // i < a.length - 1
	  Assign("min", 0),  // min := i
	  Assign("j", 1),  // j := i + 1
	  Iterate(List(
	    (LT(1, 3), List(Conditional(LT(17, 137), List(Assign("min", 1))), Assign("j", 2))),  // a(j) < a(min), min := j
	    (LT(2, 3), List(Conditional(LT(42, 17), List()), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  UnorderedStmts(List(
	    Assign(IntArrayAccess("a", 0), IntArrayAccess("a", 1)),
	    Assign(IntArrayAccess("a", 1), IntArrayAccess("a", 0))
	  )),
	  Assign("i", 1)
	)),
	(LT(1, 2), List(
	  Assign("min", 1),
	  Assign("j", 2),
	  Iterate(List(
	    (LT(2, 3), List(Conditional(LT(42, 137), List(Assign("min", 2))), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  UnorderedStmts(List(
	    Assign(IntArrayAccess("a", 1), IntArrayAccess("a", 2)),
	    Assign(IntArrayAccess("a", 2), IntArrayAccess("a", 1))
	  )),
	  Assign("i", 2)
	)),
	(LT(2, 2), List())
      ))
    )))

    println("")
    test(new Trace("snapshot1", UnitType, List(("a" -> 42), ("b" -> 137)), Map.empty, Map.empty, List(
      Snapshot(new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(137))))),
      42  // Can be a or x.
    )))

    println("")
    test(new Trace("snapshot2", UnitType, List(("max" -> 3)), Map.empty, Map.empty, List(
      Assign("sum", LiteralExpr(0)),
      Assign("i", LiteralExpr(0)),
      Iterate(List(
	(LT(0, 3), List(Snapshot(new Memory(List(("i" -> IntConstant(1)), ("sum" -> IntConstant(0)), ("max" -> IntConstant(3))))))),
	(LT(1, 3), List(Snapshot(new Memory(List(("i" -> IntConstant(2)), ("sum" -> IntConstant(1)), ("max" -> IntConstant(3))))))),
	(LT(2, 3), List(Snapshot(new Memory(List(("i" -> IntConstant(3)), ("sum" -> IntConstant(3)), ("max" -> IntConstant(3))))))),
	(LT(3, 3), Nil)
      ))
    )))

    println("")
    test(new Trace("snapshot3", UnitType, List(("max" -> 3), ("foo" -> 42), ("bar" -> 42)), Map.empty, Map.empty, List(
      Assume(And(NE("foo", 0), NE("bar", 0))),
      Assign("baz", LiteralExpr(0)),
      Iterate(List(
	(LT(0, 3), List(Snapshot(new Memory(List(("baz" -> IntConstant(42)), ("max" -> IntConstant(3)), ("foo" -> IntConstant(42)), ("bar" -> IntConstant(42))))))),
	(LT(1, 3), List(Snapshot(new Memory(List(("baz" -> IntConstant(84)), ("max" -> IntConstant(3)), ("foo" -> IntConstant(42)), ("bar" -> IntConstant(42))))))),
	(LT(2, 3), List(Snapshot(new Memory(List(("baz" -> IntConstant(126)), ("max" -> IntConstant(3)), ("foo" -> IntConstant(42)), ("bar" -> IntConstant(42))))))),
	(LT(3, 3), Nil)
      ))
    )))

    println("")
    test(new Trace("rev_list_snapshot", UnitType, List(("list" -> Object(1, "Node", HashMap.empty ++ List(("value" -> 1), ("next" -> Object(2, "Node", HashMap.empty ++ List(("value" -> 2), ("next" -> Null)))))))), Map.empty, listTypes, List(
      Assign("cur", ObjectID(1)),
      Assign("prev", LiteralExpr(Null)),
      Iterate(List(
	(NE(ObjectID(1), Null), List(
	  Snapshot(new Memory(List(("list" -> makeNode(1, 1, Null)), ("prev" -> makeNode(1, 1, Null)), ("cur" -> makeNode(2, 2, Null)))))
	)),
	(NE(ObjectID(2), Null), List(
	  Snapshot(new Memory(List(("list" -> makeNode(1, 1, Null)), ("prev" -> makeNode(2, 2, makeNode(1, 1, Null))), ("cur" -> Null))))
	)),
	(NE(Null, Null), List())
      )),
      ObjectID(2)
    )), listPrintHelpers, None, None, listComparator, listFieldLayout, listLayout)

    println("")
    test(new Trace("snapshot4", UnitType, List(("a", IntArray(0, List(137, 17, 11) toArray)), ("target" -> 42)), Map.empty, Map.empty, List(
      Iterate(List(
	(Assign("i", 0), List(
	  Snapshot(new Memory(List(("i" -> IntConstant(0)), ("target" -> IntConstant(42)), ("a" -> IntArray(0, List(42, 17, 11) toArray)))))
	)),
	(Assign("i", 1), List(
	  Snapshot(new Memory(List(("i" -> IntConstant(1)), ("target" -> IntConstant(42)), ("a" -> IntArray(0, List(42, 42, 11) toArray)))))
	)),
	(Assign("i", 2), List(
	  Snapshot(new Memory(List(("i" -> IntConstant(2)), ("target" -> IntConstant(42)), ("a" -> IntArray(0, List(42, 42, 42) toArray)))))
	))
      ))
    )))

    println("")
    test(new Trace("snapshot5", UnitType, List(("in", 42), ("a", IntArray(0, List(137, 17, 11) toArray)), ("list" -> makeNode(1, 46, makeNode(2, 50, Null)))), Map.empty, listTypes, List(
      Assume(EQ(ArrayLength("a"), 3)),
      Assume(And(And(NE("list", Null), NE(FieldAccess("list", "next"), Null)), EQ(FieldAccess(FieldAccess("list", "next"), "next"), Null))),
      Snapshot(new Memory(List(("in" -> IntConstant(42)), ("x" -> IntConstant(137)), ("y" -> IntConstant(17)), ("a" -> IntArray(0, List(42, 42, 42) toArray)), ("list" -> makeNode(2, 50, makeNode(1, 46, Null))))))
    )), fieldLayouts = listFieldLayout, objectLayouts = listLayout)

    println("")
    test(new Trace("snapshot6", UnitType, List(("target", 42), ("a", IntArray(0, List(0, 1, 2) toArray))), Map.empty, Map.empty, List(
      Assume(EQ(ArrayLength("a"), 3)),
      Snapshot(new Memory(List(("target" -> IntConstant(42)), ("a" -> IntArray(0, List(0, 42, 2) toArray)))))
    )))

    println("")
    test(new Trace("selectionSortWithCorrectnessCondition", UnitType, List(("a", IntArray(0, List(42, 17, 137) toArray))), mapOfPrograms(checkSortedProgram), Map.empty, List(
      Assign("i", 0),  // i := 0
      Iterate(List(
	(LT(0, 2), List(  // i < a.length - 1
	  Assign("min", 0),  // min := i
	  Assign("j", 1),  // j := i + 1
	  Iterate(List(
	    (LT(1, 3), List(Conditional(LT(17, 42), List(Assign("min", 1))), Assign("j", 2))),  // a(j) < a(min), min := j
	    (LT(2, 3), List(Conditional(LT(137, 17), List()), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  Assign("tmp", 42),  // tmp := a(i)
	  Assign(IntArrayAccess("a", "i"), 17),  // a(i) := a(min)
	  Assign(IntArrayAccess("a", "min"), 42),  // a(min) := tmp
	  Assign("i", 1)
	)),
	(LT(1, 2), List(
	  Assign("min", 1),
	  Assign("j", 2),
	  Iterate(List(
	    (LT(2, 3), List(Conditional(LT(137, 42), List()), Assign("j", 3))),
	    (LT(3, 3), List())
	  )),
	  Assign("tmp", 42),  // tmp := a(i)
	  Assign(IntArrayAccess("a", "i"), 42),
	  Assign(IntArrayAccess("a", "min"), 42),
	  Assign("i", 2)
	)),
	(LT(2, 2), List())
      )),
      LiteralExpr(Call("checkSorted", List("a")))
    )))

    println("")
    test(new Trace("testHoleEquality", UnitType, List(("a" -> 42), ("b" -> 42), ("c" -> 137)), Map.empty, Map.empty, List(
      Println(StringConstant("Must be x := b.")),
      Assign("x", 42),
      Assert(NE("x", "a")),
      Assign("x", 137),
      Println(StringConstant("Can be x := a or x := b.")),
      Assign("x", 42)
    )))

    // Should only explore three paths, not four.
    println("")
    test(new Trace("testAbortingLoops", UnitType, List(("a" -> 42), ("b" -> 42), ("c" -> 137)), Map.empty, Map.empty, List(
      Iterate(List((LT(42, 42), Nil))),
      Assign("x", 42),
      Assert(NE("x", "a"))
    )))

    // Should explore zero paths.
    println("")
    test(new Trace("testUnknownsInLoops", UnitType, List(("a" -> 42), ("b" -> 42), ("c" -> 137)), Map.empty, Map.empty, List(
      Assign("i", LiteralExpr(0)),
      Iterate(List(
	(LiteralExpr(LT("i", 1)), List(
	  Println(StringConstant("Must be x := b")),
	  Assign("x", 42),
	  Assert(NE("x", "a")),
	  Conditional(LiteralExpr(LT("c", 10)), Nil),
	  Println(StringConstant("Can be x := a or x := b")),
	  Assign("x", 42),
	  LiteralAction(Assign("i", Plus("i", 1)))
	 )),
	(LiteralExpr(LT("i", 1)), Nil)
      ))
    )))

    println("")
    test(new Trace("testHoleEquality", UnitType, List(("a" -> 42), ("b" -> 42), ("c" -> 137)), Map.empty, Map.empty, List(
      Conditional(LiteralExpr(LT("a", "b")), List(
	Println(StringConstant("Should be able to prune to just x := b even though the other branch is unseen.")),
	Assign("x", 42),
	Assert(NE("x", "a"))
      ))
    )))

    // This is proof that pruning can help us after we learn more about a seen hole (that is, we don't want to stop pruning after we've found all unseen holes).
    println("")
    test(new Trace("two_step_pruning", UnitType, List(("a" -> 42), ("b" -> 42), ("c" -> false)), Map.empty, Map.empty, List(
      UnorderedStmts(List(
	Assign("x", 42),
	Assign("y", 42)
      )),
      Println(StringConstant("On input when c is true, always set x:=a and y:=b and set y:=b on unseen path.  We should ask only three queries on the first trace and none on the second as we prune the remaining x:=.")),
      Conditional(LiteralExpr("c"), List(
	Assign("x", 42)
      )),
      Assert(And(Or(EQ("x", "a"), EQ("y", "a")), Or(EQ("x", "b"), EQ("y", "b"))))
    )))

    println("")
    test(new Trace("testPrinting", UnitType, List(("a" -> 42), ("b" -> 42)), Map.empty, Map.empty, List(
      Println(StringConstant("*****before")),
      Assign("x", 42),
      Println(StringConstant("*****after"))
    )))

    println("")
    test(new Trace("testLoopPruning", UnitType, List(("a" -> 42), ("b" -> 142), ("u0a" -> 17), ("u0b" -> 17), ("u1a" -> 137), ("u1b" -> 137), ("u2a" -> 1337), ("u2b" -> 1337)), Map.empty, Map.empty, List(
      Assign("i", LiteralExpr(0)),
      Iterate(List(
	(LiteralExpr(LT("i", 1)), List(
	  Assign("shouldPrune", 137),
	  Assert(EQ("shouldPrune", "u1a")),
	  Conditional(LiteralExpr(LT("a", "b")), List(
	    Println(StringConstant("You should not see me the first time through.")),
	    Assign("shouldNotPrune1", 17),
	    Assert(EQ("shouldNotPrune1", "u0a"))
	  )),
	  Conditional(LiteralExpr(GE("a", "b")), Nil),
	  Assign("shouldNotPrune2", 1337),
	  Assert(EQ("shouldNotPrune2", "u2a")),
	  Assign("i", LiteralExpr(Plus("i", 1)))
	)),
	(LiteralExpr(LT("i", 1)), Nil)
      ))
    )))

    println("")
    test(new Trace("testLoopPruning2", UnitType, List(("a" -> 42), ("b" -> 142), ("ua" -> 137), ("ub" -> 137)), Map.empty, Map.empty, List(
      Assign("i", LiteralExpr(0)),
      Iterate(List(
	(LiteralExpr(LT("i", 2)), List(
	  Conditional(LiteralExpr(EQ("i", 0)), List(
	    Assign("shouldPrune", 137),
	    Assert(EQ("shouldPrune", "ua")),
	    Conditional(LiteralExpr(GE("a", "b")), Nil)
	  )),
	  Assign("i", LiteralExpr(Plus("i", 1)))
	)),
	(LiteralExpr(LT("i", 2)), List(
	  Conditional(LiteralExpr(EQ("i", 0)), Nil),
	  Assign("i", LiteralExpr(Plus("i", 1)))
	)),
	(LiteralExpr(LT("i", 2)), Nil)
      ))
    )))

    // When comparing two unseen statements, we prefer the one that opens up another unseen statement.
    println("")
    test(new Trace("testComparingUnseenStmtsForInputGeneration", UnitType, List(("a" -> 42), ("b" -> 42)), Map.empty, Map.empty, List(
      Conditional(LiteralExpr(LE("a", "b")), List(
	Println(StringConstant("You should see me the first time through.")),
	Conditional(EQ("a", "b"), List(
	  Println(StringConstant("Should ask top hole first."))
	)),
	Conditional(NE("a", "b"), Nil)
      ))
    )))

    // When comparing two unseen statements, we prefer the one that opens up a possibilities hole.
    println("")
    test(new Trace("testComparingUnseenStmtsForInputGeneration2", UnitType, List(("a" -> 42), ("b" -> 42), ("b1", true), ("b2", false)), Map.empty, Map.empty, List(
      Conditional(LiteralExpr(LE("a", "b")), List(
	Println(StringConstant("You should see me the first time through.")),
	Conditional(EQ("a", "b"), List(
	  Println(StringConstant("Should ask top hole first."))
	)),
	Assign("x", true),
	Assert(EQ("x", Or("b1", "b2")))
      ))
    )))*/

    def maxPost(args: Map[String, Value], rMap: Map[String, Value], r: Value): Boolean = {
      def toInt(v: Value) = v.asInstanceOf[IntConstant].n
      val rv = toInt(r)
      val x = toInt(args("x"))
      val y = toInt(args("y"))
      rv >= y && rv >= y && (rv == x || rv == y)
    }
    println("")
    test(new Trace("inferConditionalMax", UnitType, List(("x", 1), ("y", 0)), Map.empty, Map.empty, List(
      1
    )), postcondition = Some(maxPost))

  }

}
