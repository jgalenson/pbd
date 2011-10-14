package graphprog.test

object GuiTest {

  import graphprog.Controller
  import graphprog.Controller._
  import graphprog.lang.AST._
  import graphprog.synthesis.Synthesis._
  import graphprog.Utils._
  import scala.collection.immutable.{ Map => IMap }
  import scala.collection.mutable.Map
  import graphprog.Controller.ObjectLayout
  import TestCommon._

  val printer = new graphprog.lang.Printer(Map[String, Value => String](), false)

  def mapOfPrograms(programs: Program*): IMap[String, Program] = programs map { p => (p.name, p) } toMap

  def main(args: Array[String]) {
    val options = parseCommandLine(args)
    //simpleTest(options)
    //bigListTest(options)
    //emptyObjectAndArrayTest(options)
    //manyVarsTest(options)
    //getActionTest(options)
    //getTraceTest(options)
    synthesizeTest(options)
  }

  def simpleTest(options: Options) {
    val controller = new Controller(makeSynthesizer("", UnitType, Nil, IMap.empty, IMap.empty, objectComparators = listComparator), IMap.empty, IMap.empty, listComparator, listFieldLayout, listLayout, options)
    val arr = IntArray(0, List(42, 17, 137).toArray)
    val rec = Object(4, "Rec", Map.empty[String, Value] + ("me" -> Null))
    rec.fields("me") = rec
    val mem = new Memory(List(("x" -> IntConstant(42)),
			      ("pair" -> Object(0, "IntPair", Map.empty[String, Value] ++ List(("x" -> IntConstant(42)), ("y" -> IntConstant(137))))),
			      ("myArr" -> Object(1, "MyArr", Map.empty[String, Value] ++ List(("arr" -> IntArray(1, List(1, 2, 3, 4, 5).toArray)), ("size" -> IntConstant(5))))),
			      ("list" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(3, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))),
			      ("a2" -> arr),
			      ("rec" -> rec)
			     ))
    mem.enterScope
    mem += "a" -> arr
    mem += "z" -> true
    println(printer.stringOfMemory(mem))
    controller.updateDisplay(mem, Nil, Some(Null))
    readLine("Press Enter to update the display.")
    //Thread.sleep(2000)
    mem.exitScope
    mem += ("ping" -> 42)
    mem += ("x" -> 424242)
    mem("a2").asInstanceOf[IntArray].array(1) = 424242
    mem.getObject(3).get.fields("value") = 424242
    mem += ("a2" -> IntArray(2, List(42).toArray))
    mem.getObject(1).get.fields("arr") = arr
    mem.getObject(3).get.fields("next") = mem.getObject(2).get
    mem += "pair" -> Null
    mem += "newA" -> IntArray(3, List(42, 17, 137).toArray)
    println("Updating")
    println(printer.stringOfMemory(mem))
    controller.updateDisplay(mem, Nil, Some(Null))
  }

  def bigListTest(options: Options) {
    val controller = new Controller(makeSynthesizer("", UnitType, Nil, IMap.empty, IMap.empty, objectComparators = listComparator), IMap.empty, IMap.empty, listComparator, listFieldLayout, listLayout, options)

    var id = 1
    def getID(): Int = { val n = id; id += 1; n }
    def makeList(n: Int): Value = n match {
      case 0 => Null
      case n => Object(getID(), "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(n)), ("next" -> makeList(n - 1))))
    }

    val mem = new Memory(List(("l1" -> makeList(5)), ("l2" -> makeList(9)), ("l3" -> makeList(17))))

    controller.updateDisplay(mem, Nil, Some(Null))
  }

  def emptyObjectAndArrayTest(options: Options) {
    val controller = new Controller(makeSynthesizer("", UnitType, Nil, IMap.empty, IMap.empty), IMap.empty, IMap.empty, IMap.empty, IMap.empty, IMap.empty, options)

    val mem = new Memory(List(("o" -> Object(0, "Empty", Map.empty)), ("a" -> IntArray(0, Nil.toArray))))

    controller.updateDisplay(mem, Nil, Some(Null))
  }

  def manyVarsTest(options: Options) {
    val controller = new Controller(makeSynthesizer("", UnitType, Nil, IMap.empty, IMap.empty), mapOfPrograms(answerProgram, factProgram), IMap.empty, IMap.empty, IMap.empty, IMap.empty, options)

    val mem = new Memory(List(("a" -> IntConstant(1)), ("b" -> IntConstant(2)), ("c" -> IntConstant(3)), ("d" -> IntConstant(4)), ("e" -> IntConstant(5)), ("f" -> IntConstant(6)), ("g" -> IntConstant(7)), ("h" -> IntConstant(8)), ("i" -> IntConstant(9)), ("j" -> IntConstant(10)), ("k" -> IntConstant(11)), ("l" -> IntConstant(12)), ("m" -> IntConstant(12)), ("n" -> IntConstant(13))))

    controller.updateDisplay(mem, Nil, Some(Null))
  }

  def getActionTest(options: Options) {

    def test(mem: Memory, possibilityMaker: Memory => List[Action], functions: IMap[String, Program]) {
      val controller = new Controller(makeSynthesizer("", UnitType, Nil, IMap.empty, IMap.empty, objectComparators = listComparator), functions, IMap.empty, listComparator, listFieldLayout, listLayout, options)
      val possibilities = possibilityMaker(mem)
      println("Possibilities are " + iterableToString(possibilities, " or ", { s: Stmt => printer.stringOfStmt(s) }))
      controller.updateDisplay(mem, Nil, Some(Null))
      val actions = controller.getActions(possibilities, false).asInstanceOf[Actions].actions
      println("Got " + iterableToString(actions, " or ", (a: Action) => printer.stringOfAction(a)))
      controller.cleanup()
    }

    test(new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(5)), ("z" -> IntConstant(137)))), _ => List("x", "y"), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(42)), ("a" -> IntArray(0, List(5, 42, 137).toArray)))), mem => List("x", IntArrayAccess(mem.getArray(0).get, 1)), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(42)), ("o" -> Object(0, "Obj", Map.empty ++ List(("foo" -> IntConstant(42)), ("bar" -> IntConstant(11))))))), mem => List("x", FieldAccess(mem.getObject(0).get, "foo")), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))))), mem => List("list", "cur"), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))))), mem => List(mem.getObject(1).get, mem.getObject(2).get), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(5)), ("z" -> IntConstant(137)))), _ => List("x", IntConstant(0)), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(42)), ("a" -> IntArray(0, List(5, 42, 137).toArray)))), mem => List("x", ArrayLength(mem.getArray(0).get)), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(0)), ("y" -> IntConstant(42)), ("z" -> IntConstant(137)))), _ => List(Assign("x", "y"), Assign("x", "z")), IMap.empty)

    test(new Memory(List(("y" -> IntConstant(42)), ("z" -> IntConstant(137)))), _ => List(Assign("x", "y"), Assign("x", "z")), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(0)), ("o" -> Object(1, "Obj", Map.empty[String, Value] ++ List(("value" -> IntConstant(42)), ("next" -> Null)))), ("a" -> IntArray(1, List(13, 42, 137).toArray)))), mem => List(Assign("x", FieldAccess(mem.getObject(1).get, "value")), Assign("x", IntArrayAccess(mem.getArray(1).get, 1))), IMap.empty)

    test(new Memory(List(("o" -> Object(1, "Obj", Map.empty[String, Value] ++ List(("value" -> IntConstant(0))))), ("x" -> IntConstant(42)), ("y" -> IntConstant(137)))), mem => List(Assign(FieldAccess(mem.getObject(1).get, "value"), "x"), Assign(FieldAccess(mem.getObject(1).get, "value"), "y")), IMap.empty)

    test(new Memory(List(("a" -> IntArray(1, List(13, 42, 137).toArray)), ("x" -> IntConstant(42)), ("y" -> IntConstant(137)))), mem => List(Assign(IntArrayAccess(mem.getArray(1).get, 1), "x"), Assign(IntArrayAccess(mem.getArray(1).get, 1), "y")), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))))), mem => List(Assign("x", mem.getObject(1).get), Assign("x", mem.getObject(2).get)), IMap.empty)

    test(new Memory(List(("a1" -> IntArray(0, List(1, 2).toArray)), ("a2" -> IntArray(1, List(3, 4).toArray)))), mem => List(Assign("a3", mem.getArray(0).get), Assign("a3", mem.getArray(1).get)), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(5)), ("y" -> IntConstant(7)))), mem => List(Call("answer", Nil), Call("fact", List("x")), Call("sum", List("x", "y"))), mapOfPrograms(answerProgram, factProgram, sumProgram))

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))))), mem => List(Call("length", List(mem.getObject(1).get)), Call("length", List(mem.getObject(2).get))), mapOfPrograms(lengthProgram))

    test(new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(5)), ("z" -> IntConstant(137)))), _ => List(Plus("x", "y"), "x"), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))))), mem => List("list", FieldAccess("list", "next")), IMap.empty)

    test({ val mem = new Memory(List(("o1" -> Object(0, "Obj", Map.empty ++ List(("foo" -> IntConstant(42)), ("bar" -> IntConstant(11))))), ("o3" -> Null))); mem += ("o2" -> mem.getObject(0).get) }, mem => List("o1", "o2", "o3"), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))))), mem => List(Assign("p", "list"), Assign("p", FieldAccess("list", "next"))), IMap.empty)

    test({ val mem = new Memory(List(("o1" -> Object(0, "Obj", Map.empty ++ List(("foo" -> IntConstant(42)), ("bar" -> IntConstant(11))))), ("o3" -> Null))); mem += ("o2" -> mem.getObject(0).get) }, mem => List(Assign("p", "o1"), Assign("p", "o2"), Assign("p", "o3")), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(5)), ("z" -> IntConstant(137)))), _ => List("x", IntConstant(0), IntConstant(1), Plus(42, -42)), IMap.empty)

    test(new Memory(List(("xr" -> IntConstant(42)), ("yr" -> IntConstant(137)))), _ => List(Assign("x", "xr"), Assign("y", "yr")), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(137)), ("z" -> IntConstant(15)))), _ => List(Assign("x", "x"), Assign("y", "y")), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(137)), ("z" -> IntConstant(25)))), _ => List(Assign("x", "y"), Assign("y", "x")), IMap.empty)

    test(new Memory(List(("a" -> IntArray(1, List(13, 42, 137).toArray)))), mem => List(Assign(IntArrayAccess(mem.getArray(1).get, 0), IntArrayAccess(mem.getArray(1).get, 1)), Assign(IntArrayAccess(mem.getArray(1).get, 0), IntArrayAccess(mem.getArray(1).get, 0))), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))))), mem => List(Assign("n", Call("length", List("list"))), Assign("n", 2)), mapOfPrograms(lengthProgram))

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))), ("nullvar" -> Null))), mem => List(Assign("p", "nullvar"), Assign("p", FieldAccess("cur", "next")), Assign("p", Null)), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))), ("nullvar" -> Null))), mem => List("nullvar", FieldAccess("cur", "next"), Null), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))))), mem => List(mem.getObject(2).get, FieldAccess(mem.getObject(2).get, "next")), IMap.empty)

    test(new Memory(List(("list" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("cur" -> Object(2, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null)))))), mem => List(Assign("x", mem.getObject(2).get), Assign("x", FieldAccess(mem.getObject(2).get, "next"))), IMap.empty)

    test(new Memory(List(("x" -> IntConstant(42)))), _ => List(Assign("l1", "x"), Assign("l2", "x")), IMap.empty)

    // Test long (wrapped) tooltip
    test(new Memory(List()), _ => List(Assign("x", IntConstant(0)), Assign("x", Plus(42, -42)), Assign("x", Plus(4242, -4242)), Assign("x", Plus(424242, -424242)), Assign("x", Plus(101010, -101010)), Assign("x", Plus(Plus(424242, -424242), Plus(101010, -101010))), Assign("x", Plus(Plus(424242, -424242), Plus(-101010, 101010))), Assign("x", Plus(Plus(-424242, 424242), Plus(101010, -101010))), Assign("x", 42)), IMap.empty)

    // Test ordering of new possibilities.
    test(new Memory(Nil), _ => List(IntConstant(0), IntConstant(1)), IMap.empty)
    test(new Memory(Nil), _ => List(IntConstant(1), IntConstant(0)), IMap.empty)

  }

  def getTraceTest(options: Options) {

    def test(mem: Memory, functions: IMap[String, Program], objectTypes: IMap[String, List[(String, Type)]], objectComparators: IMap[String, (Value, Value) => Int], fieldLayouts: IMap[String, List[List[String]]], objectLayouts: IMap[String, ObjectLayout]) {
      val controller = new Controller(makeSynthesizer("", UnitType, Nil, IMap.empty, objectTypes, objectComparators = objectComparators), functions, objectTypes, objectComparators, fieldLayouts, objectLayouts, options)
      val unseen = UnseenStmt()
      controller.updateDisplay(mem, List(unseen), Some(unseen))
      controller.getStmtTrace(mem, false) match {
	case StmtInfo((actions, stmts, memory)) =>
	  println("Actions:\n" + printer.stringOfStmts(actions))
	  println("Stmts:\n" + printer.stringOfStmts(stmts))
	  println("Mem: " + printer.stringOfMemory(memory))
	case o => println(o)
      }
      controller.cleanup()
    }

    test(new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(101010)), ("z" -> IntConstant(137)), ("list" -> Object(0, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(1)), ("next" -> Object(1, "Node", Map.empty[String, Value] ++ List(("value" -> IntConstant(2)), ("next" -> Null))))))), ("a" -> IntArray(0, List(137, 42, 5).toArray)), ("b1" -> BooleanConstant(true)), ("b2" -> BooleanConstant(false)))), mapOfPrograms(answerProgram, factProgram, sumProgram, lengthProgram, reverseProgram, selectionSortProgram, swapProgram), listTypes, listComparator, listFieldLayout, listLayout)

  }

  def synthesizeTest(options: Options) {

    def test(name: String, typ: Type, inputs: List[(String, Value)], functions: IMap[String, Program], objectTypes: IMap[String, List[(String, Type)]], postcondition: Option[(IMap[String, Value], IMap[String, Value], Value) => Boolean], objectComparators: IMap[String, (Value, Value) => Int], fieldLayouts: IMap[String, List[List[String]]], objectLayouts: IMap[String, ObjectLayout]) {
      try {
	val result = synthesize((new Memory(inputs)).toIterator.toList, makeSynthesizer(name, typ, graphprog.lang.Typer.typeOfInputs(inputs), functions, objectTypes, postcondition = postcondition, objectComparators = objectComparators) _, functions, objectTypes, objectComparators, fieldLayouts, objectLayouts, options)
	println("Result:\n" + printer.stringOfProgram(result))
      } catch {
	case e => e.printStackTrace
      }
    }

    //test("test1", UnitType, List(("a" -> IntArray(0, /*List(137, 42, 5, 11, 18, 42, 101010)*/List(42, 17, 137).toArray))), mapOfPrograms(swapProgram), IMap.empty, None, IMap.empty, IMap.empty, IMap.empty)

    test("selectionSort", UnitType, List(("a" -> IntArray(0, List(137, 42, 5, 11, 18, 42, 101010).toArray))), mapOfPrograms(swapProgram), IMap.empty, Some(arrayAIsSorted), IMap.empty, IMap.empty, IMap.empty)
    //test("selectionSort", UnitType, List(("a" -> IntArray(0, List(42, 137, 5, 11, 18, 42, 101010).toArray))), mapOfPrograms(swapProgram), IMap.empty, Some(arrayAIsSorted), IMap.empty, IMap.empty, IMap.empty)

    def knapsackWeakPost(args: IMap[String, Value], resMap: IMap[String, Value], rv: Value): Boolean = {
      val items = args("items").asInstanceOf[IntArray].array
      val nums = args("result").asInstanceOf[IntArray].array
      val max = args("max").asInstanceOf[IntConstant].n
      assert(items.size == nums.size)
      items.zip(nums).foldLeft(0){ (acc, cur) => acc + cur._1 * cur._2 } <= max
    }
    //test("knapsack", ArrayType(IntType), List(("items" -> IntArray(0, List(215, 275, 335, 355, 420, 580).toArray)), ("max" -> IntConstant(1505)), ("result" -> IntArray(1, Array.fill(1505)(0)))), IMap.empty, IMap.empty, Some(knapsackWeakPost), IMap.empty, IMap.empty, IMap.empty)

  }

}
