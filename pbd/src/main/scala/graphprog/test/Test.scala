package graphprog.test

object Test {

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
    val options = parseCommandLine(args)
    //testGraphviz()
    testSynthesize(options)
  }

  val printer = new Printer(Map[String, Value => String](), false)

  /*def testGraphviz() {

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

  }*/

  def testSynthesize(options: Options) {

    def test(trace: Trace, printHelpers: PartialFunction[String, Value => String] = Map.empty, precondition: Option[Map[String, Value] => Boolean] = None, postcondition: Option[(Map[String, Value], Map[String, Value], Value) => Boolean] = None, objectComparators: Map[String, (Value, Value) => Int] = Map.empty, fieldLayouts: Map[String, List[List[String]]] = Map.empty, objectLayouts: Map[String, ObjectLayout] = Map.empty) {
      val printer = new Printer(printHelpers, false)
      //println("Program:\n" + printer.stringOfTrace(trace))
      try {
	val result = synthesize(trace, makeSynthesizerFromTrace(trace, printHelpers, precondition = precondition, postcondition = postcondition, objectComparators = objectComparators) _, trace.functions, trace.objectTypes, objectComparators, fieldLayouts, objectLayouts, options)
	println("Result:\n" + printer.stringOfProgram(result))
      } catch {
	case e: Throwable => e.printStackTrace
      }
    }

    val listPrintHelpers: PartialFunction[String, Value => String] = (s: String) => s match {
      case "Node" => v => "List(" + stringOfList(v, printer) + ")"
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
    test(new Trace("arraytest", UnitType, List(("a", makeIntArray(0, List(5, 42, 137) toArray))), Map.empty, Map.empty, List(
      Assume(GE(ArrayLength("a"), 3)),
      Assign("x", 5),  // a(0)
      Assign("y", 3),  // (a.length)
      Assign(ArrayAccess("a", 2), 2)  // 2
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
    test(new Trace("array1", UnitType, List(("a", makeIntArray(0, List(-5, -5, -5, -5, -5, -5, -5, 42, 137) toArray)), ("i", 7), ("j", 8)), Map.empty, Map.empty, List(
      Assume(GE(ArrayLength("a"), 9)),
      Assume(And(GE("i", 0), LT("i", ArrayLength("a")))),
      Assume(And(GE("j", 0), LT("j", ArrayLength("a")))),
      LT(42, 137)
    )))

    println("")
    test(new Trace("selectionSort", UnitType, List(("a", makeIntArray(0, List(42, 17, 137) toArray))), Map.empty, Map.empty, List(
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
	  Assign(ArrayAccess("a", "i"), 17),  // a(i) := a(min)
	  Assign(ArrayAccess("a", "min"), 42),  // a(min) := tmp
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
	  Assign(ArrayAccess("a", "i"), 42),
	  Assign(ArrayAccess("a", "min"), 42),
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
    test(new Trace("array_zero", IntType, List(("a", makeIntArray(0, List(42, 137) toArray)), ("x", 13)), Map.empty, Map.empty, List(
      Assume(GT(ArrayLength("a"), 0)),
      55
    )))

    println("")
    test(new Trace("find1", UnitType, List(("target", 42), ("a", makeIntArray(0, List(8, 11, 42) toArray))), Map.empty, Map.empty, List(
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
    test(new Trace("find2", UnitType, List(("target", 42), ("a", makeIntArray(0, List(8, 11, 42) toArray))), Map.empty, Map.empty, List(
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
    test(new Trace("find3", UnitType, List(("target", 42), ("a", makeIntArray(0, List(8, 11, 42) toArray))), Map.empty, Map.empty, List(
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
    test(new Trace("intersect", UnitType, List(("a1", makeIntArray(0, List(8, 42, 137) toArray)), ("a2", makeIntArray(1, List(42, 17, 8) toArray))), mapOfPrograms(containsProgram), Map.empty, List(
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
    test(new Trace("array_equality", UnitType, List(("a", makeIntArray(0, List(42, 137) toArray))), Map.empty, Map.empty, List(
      Assign("b", "a"),
      EQ("a", "b")
    )))

    println("")
    test(new Trace("selectionSortSwap", UnitType, List(("a", makeIntArray(0, List(42, 17, 137) toArray))), mapOfPrograms(swapProgram), Map.empty, List(
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
    test(new Trace("call4", UnitType, List(("a", makeIntArray(0, List(17, 42) toArray)), ("x", 0), ("y", 1)), mapOfPrograms(swapProgram), Map.empty, List(
      Assume(And(And(GE("x", 0), GE("y", 0)), And(GT(ArrayLength("a"), "x"), GT(ArrayLength("a"), "y")))),
      Call("swap", List("a", 0, 1))
    )))

    println("")
    test(new Trace("selectionSort2", UnitType, List(("a", makeIntArray(0, List(137, 17, 42) toArray))), mapOfPrograms(swapProgram), Map.empty, List(
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
    test(new Trace("inTest", UnitType, List(("a", makeIntArray(0, List(137, 17, 42) toArray))), mapOfPrograms(swapProgram), Map.empty, List(
      Iterate(List(
	(Assign("i", 0), List(  // i < a.length
	  Assign(ArrayAccess("a", 0), 0)
	)),
	(Assign("i", 1), List(  // i < a.length
	  Assign(ArrayAccess("a", 1), 0)
	)),
	(Assign("i", 2), List(  // i < a.length
	  Assign(ArrayAccess("a", 2), 0)
	))
      ))
    )))

    println("")
    test(new Trace("selectionSortForLoop", UnitType, List(("a", makeIntArray(0, List(137, 17, 42) toArray))), mapOfPrograms(swapProgram), Map.empty, List(
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
    test(new Trace("findLoop", UnitType, List(("target", 42), ("a", makeIntArray(0, List(8, 11, 42, 137) toArray))), Map.empty, Map.empty, List(
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
    // test(new Trace("intersectForLoop", UnitType, List(("a1", makeIntArray(0, List(8, 42, 137) toArray)), ("a2", makeIntArray(1, List(42, 137, 17) toArray))), Map.empty, Map.empty, List(
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
    test(new Trace("literals", UnitType, List(("target", 42), ("a", makeIntArray(0, List(8, 11, 42, 137) toArray))), Map.empty, Map.empty, List(
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
    test(new Trace("arrayCloning", UnitType, List(("a", makeIntArray(0, List(8, 11, 42, 137) toArray))), Map.empty, Map.empty, List(
      Assume(GT(ArrayLength("a"), 0)),
      Assign("b", "a"),
      Assign(ArrayAccess("a", 0), LiteralExpr(13)),
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
    test(new Trace("selectionSort2WithUnordered", UnitType, List(("a", makeIntArray(0, List(137, 17, 42) toArray))), Map.empty, Map.empty, List(
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
	    Assign(ArrayAccess("a", 0), ArrayAccess("a", 1)),
	    Assign(ArrayAccess("a", 1), ArrayAccess("a", 0))
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
	    Assign(ArrayAccess("a", 1), ArrayAccess("a", 2)),
	    Assign(ArrayAccess("a", 2), ArrayAccess("a", 1))
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
    test(new Trace("snapshot4", UnitType, List(("a", makeIntArray(0, List(137, 17, 11) toArray)), ("target" -> 42)), Map.empty, Map.empty, List(
      Iterate(List(
	(Assign("i", 0), List(
	  Snapshot(new Memory(List(("i" -> IntConstant(0)), ("target" -> IntConstant(42)), ("a" -> makeIntArray(0, List(42, 17, 11) toArray)))))
	)),
	(Assign("i", 1), List(
	  Snapshot(new Memory(List(("i" -> IntConstant(1)), ("target" -> IntConstant(42)), ("a" -> makeIntArray(0, List(42, 42, 11) toArray)))))
	)),
	(Assign("i", 2), List(
	  Snapshot(new Memory(List(("i" -> IntConstant(2)), ("target" -> IntConstant(42)), ("a" -> makeIntArray(0, List(42, 42, 42) toArray)))))
	))
      ))
    )))

    println("")
    test(new Trace("snapshot5", UnitType, List(("in", 42), ("a", makeIntArray(0, List(137, 17, 11) toArray)), ("list" -> makeNode(1, 46, makeNode(2, 50, Null)))), Map.empty, listTypes, List(
      Assume(EQ(ArrayLength("a"), 3)),
      Assume(And(And(NE("list", Null), NE(FieldAccess("list", "next"), Null)), EQ(FieldAccess(FieldAccess("list", "next"), "next"), Null))),
      Snapshot(new Memory(List(("in" -> IntConstant(42)), ("x" -> IntConstant(137)), ("y" -> IntConstant(17)), ("a" -> makeIntArray(0, List(42, 42, 42) toArray)), ("list" -> makeNode(2, 50, makeNode(1, 46, Null))))))
    )), fieldLayouts = listFieldLayout, objectLayouts = listLayout)

    println("")
    test(new Trace("snapshot6", UnitType, List(("target", 42), ("a", makeIntArray(0, List(0, 1, 2) toArray))), Map.empty, Map.empty, List(
      Assume(EQ(ArrayLength("a"), 3)),
      Snapshot(new Memory(List(("target" -> IntConstant(42)), ("a" -> makeIntArray(0, List(0, 42, 2) toArray)))))
    )))

    println("")
    test(new Trace("selectionSortWithCorrectnessCondition", UnitType, List(("a", makeIntArray(0, List(42, 17, 137) toArray))), mapOfPrograms(checkSortedProgram), Map.empty, List(
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
	  Assign(ArrayAccess("a", "i"), 17),  // a(i) := a(min)
	  Assign(ArrayAccess("a", "min"), 42),  // a(min) := tmp
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
	  Assign(ArrayAccess("a", "i"), 42),
	  Assign(ArrayAccess("a", "min"), 42),
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
