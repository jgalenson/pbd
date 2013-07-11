package graphprog.test

object TestExecution {

  import graphprog.lang.AST._
  import graphprog.lang.{ Executor, Printer, IteratorExecutor }
  import graphprog.Controller._
  import graphprog.Utils._
  import graphprog.lang.Compiler._
  import graphprog.synthesis.Synthesis._
  import scala.collection.mutable.HashMap
  import graphprog.Controller.ObjectLayout
  import TestCommon._

  def main(args: Array[String]) {
    parseCommandLine(args)
    testExecute()
    testIteratorExecute()
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
	case e: Throwable =>
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
    ), Map.empty, Some((m, h) => h match { case _: Unseen => ErrorConstant case _ => throw new IllegalArgumentException }))

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
}
