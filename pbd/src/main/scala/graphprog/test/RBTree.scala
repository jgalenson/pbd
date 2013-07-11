package graphprog.test

object RBTree {

  import graphprog.lang.AST._
  import graphprog.lang.{ Executor, Memory, Printer }
  import graphprog.Controller._
  import graphprog.Controller
  import graphprog.Utils._
  import graphprog.synthesis.Synthesis._
  import scala.collection.mutable.HashMap
  import scala.util.Random.{nextInt, nextBoolean, nextFloat, shuffle}
  import TestCommon._
  import annotation.tailrec

  def main(args: Array[String]) {
    val options = parseCommandLine(args)
    //showRandomTree(15)
    //testExecute()
    synthesizeLeftRotate(options)
    //synthesizeTreeInsert(options)
    //synthesizeRBInsert(options)
  }

  // Red is 0, Black is 1.  -1 is undefined for non-RB trees.
  def makeNode(id: Int, v: Int, c: StringConstant, l: Value, r: Value): Object = Object(id, "Node", HashMap.empty ++ List(("value" -> v), ("color" -> c), ("left" -> l), ("right" -> r)))
  def makeNode(id: Int, v: Int, l: Value, r: Value): Object = Object(id, "Node", HashMap.empty ++ List(("value" -> v), ("left" -> l), ("right" -> r)))
  def makeNode(v: Int, c: StringConstant, l: Value, r: Value): Object = makeNode(v, v, c, l, r)
  def makeNode(v: Int, c: StringConstant): Object = makeNode(v, c, Null, Null)
  def makeTree(id: Int, root: Value): Object = Object(id, "Tree", HashMap.empty + ("root" -> root))
  val RED = StringConstant("red")
  val BLACK = StringConstant("black")
  val UNK = StringConstant("unknown")

  def stringOfNode(tree: Value): String = {
    val seen = scala.collection.mutable.Set[Int]()
    def recurse(tree: Value): (String, String) = tree match {
      case Null => ("null", "")
      case Object(id, _, fields) => 
	if (seen contains id)
	  return ("!!LOOP(" + id + ")!!", "")
	seen += id
	val (lShort, lLong) = recurse(fields("left"))
	val (rShort, rLong) = recurse(fields("right"))
	val colorString = if (fields contains "color") " (" + fields("color").asInstanceOf[StringConstant].s + ") " else " "
	(printer.stringOfValue(fields("value")), printer.stringOfValue(fields("value")) + "(" + id + ")" + colorString + "-> " + lShort + ", " + rShort + (if (lLong == "") "" else "; " + lLong) + (if (rLong == "") "" else "; " + rLong))
    }
    val s = recurse(tree)._2
    if (s == "") "null" else s
  }
  def stringOfTree(tree: Object): String = "id=" + tree.id + " root = " + stringOfNode(tree.fields("root"))
  def setParentPointers(node: Value, parent: Value): Value = node match {
    case Null => node
    case Object(_, _, fields) =>
      fields += ("parent" -> parent)
      setParentPointers(fields("left"), node)
      setParentPointers(fields("right"), node)
      node
  }
  object TreeGen {
    val NULL_PROBABILITY = 0.4
    val MAX_HEIGHT = 5
    var objectID = 1
    def getObjectID(): Int = { var id = objectID; objectID += 1; id }
    def randomColor() = if (nextBoolean()) RED else BLACK
    def genRandomTree(height: Int): Value = {
      if (height >= MAX_HEIGHT || nextFloat() < NULL_PROBABILITY)
	return Null
      val id = getObjectID()
      makeNode(id, id, randomColor(), genRandomTree(height + 1), genRandomTree(height + 1))
    }
    def genBinaryTree(height: Int, min: Int, max: Int): Value = {
      if (height >= MAX_HEIGHT || nextFloat() < NULL_PROBABILITY || min > max)
	return Null
      val id = getObjectID()
      val v = nextBoundedInt(min, max)
      makeNode(id, v, genBinaryTree(height + 1, min, v - 1), genBinaryTree(height + 1, v + 1, max))
    }
    def genRandomTree(): Object = makeTree(0, setParentPointers(genRandomTree(0), Null))
    def genBinaryTree(): Object = makeTree(0, setParentPointers(genBinaryTree(0, 0, 100), Null))
    def genRedBlackTree(maxNumElems: Int): Object = {
      val executor = new Executor(allPrograms, printer)
      var tree = emptyTree
      val size = maxNumElems//if (maxNumElems == 0) 0 else nextInt(maxNumElems)
      val elems = shuffle((1 to 2 * size).toList).take(size)
      var id = 1
      for (elem <- elems) {
	val newNode = setParentPointers(makeNode(id, elem, UNK, Null, Null), Null)
	tree = executor.executeStmts(new Memory(List(("tree" -> tree), ("x" -> newNode))), List(Call("rbInsert", List("tree", "x"))))._2("tree").asInstanceOf[Object]
	id += 1
      }
      tree
    }
  }
  import TreeGen.{genRandomTree, genBinaryTree, genRedBlackTree}
  def getNodes(node: Value): List[Object] = node match {
    case Null => Nil
    case o @ Object(_, _, fields) => o :: (getNodes(fields("left")) ++ getNodes(fields("right")))
  }

  def checkRedBlackInvariant(tree: Value): Boolean = {
    def check(tree: Value, seen: Set[Int]): Int = tree match {
      case Null => 1
      case Object(id, _, fields) =>
	if (seen contains id)
	  -1
	val newSeen = seen + id
	val l = check(fields("left"), newSeen)
	val r = check(fields("right"), newSeen)
	if (l == -1 || r == -1)
	  -1
	else if (l != r)
	  -1
	else if (fields("color") == RED) {
	  def isRed(v: Value) = v match { case Null => false case Object(_, _, fields) => fields("color") == RED }
	  if (isRed(fields("left")) || isRed(fields("right")))
	    -1
	  else
	    l
	} else
	  l + 1
    }
    check(tree, Set.empty) != -1
  }

  val printHelpers: PartialFunction[String, Value => String] = (s: String) => s match {
    case "Tree" => v => "Tree(" + stringOfTree(v.asInstanceOf[Object]) + ")"
    case "Node" => v => "Node(" + stringOfNode(v) + ")"
  }

  val printer = new Printer(printHelpers, false)

  def test(trace: Trace, generator: Option[Double => List[(String, Value)]], fieldLayouts: Map[String, List[List[String]]], options: Options) {
    try {
      val result = synthesize(trace, makeSynthesizerFromTrace(trace, printHelpers, generator, None, None, treeComparator) _, trace.functions, trace.objectTypes, treeComparator, fieldLayouts, treeLayout, options)
      println("Result:\n" + printer.stringOfProgram(result))
    } catch {
      case e: Throwable => e.printStackTrace
    }
  }
  def test(name: String, typ: Type, inputs: List[(String, Value)], generator: Option[Double => List[(String, Value)]], precondition: Option[Map[String, Value] => Boolean], postcondition: Option[(Map[String, Value], Map[String, Value], Value) => Boolean], functions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], fieldLayouts: Map[String, List[List[String]]], options: Options) {
    try {
      val result = synthesize(inputs, makeSynthesizer(name, typ, graphprog.lang.Typer.typeOfInputs(inputs), functions, objectTypes, printHelpers, generator, precondition, postcondition, treeComparator) _, functions, objectTypes, treeComparator, fieldLayouts, treeLayout, options)
      println("Result:\n" + printer.stringOfProgram(result))
    } catch {
      case e: Throwable => e.printStackTrace
    }
  }

  val simpleLeftTree = makeTree(0, setParentPointers(makeNode(1, 1, BLACK, makeNode(2, 2, BLACK, Null, makeNode(3, 3, RED, Null, Null)), makeNode(4, 4, BLACK, Null, Null)), Null))
  val simpleRightTree = makeTree(0, setParentPointers(makeNode(1, 1, BLACK, makeNode(3, 3, BLACK, makeNode(2, 2, RED, Null, Null), Null), makeNode(4, 4, BLACK, Null, Null)), Null))
  val simpleNotRBTree = makeTree(0, setParentPointers(makeNode(1, 1, RED, makeNode(2, 2, RED, Null, makeNode(3, 3, RED, Null, Null)), makeNode(4, 4, RED, Null, Null)), Null))
  val fullLeftTree = makeTree(0, setParentPointers(makeNode(1, 1, Null, makeNode(3, 3, makeNode(2, 2, Null, Null), makeNode(5, 5, makeNode(4, 4, Null, Null), makeNode(6, 6, Null, Null)))), Null))
  val simpleBinaryTree = makeTree(0, setParentPointers(makeNode(12, 12, makeNode(5, 5, makeNode(2, 2, Null, Null), makeNode(9, 9, Null, Null)), makeNode(18, 18, makeNode(15, 15, Null, makeNode(17, 17, Null, Null)), makeNode(19, 19, Null, Null))), Null))
  val emptyTree = makeTree(0, Null)
  val simpleRBTree = makeTree(0, setParentPointers(makeNode(11, BLACK, makeNode(2, RED, makeNode(1, BLACK), makeNode(7, BLACK, makeNode(5, RED, Null, Null), makeNode(8, RED))), makeNode(14, BLACK, Null, makeNode(15, RED))), Null))  // CLR p269

  def testExecute() {

    def testExec(memory: Memory, stmts: List[Stmt], functions: Map[String, Program]) {
      println("Testing:\n" + printer.stringOfStmts(stmts))
      val (result, finalMemory) = (new Executor(functions, printer, shouldPrint = true)).executeStmts(memory, stmts)
      println("Result: " + printer.stringOfValue(result) + " with memory " + printer.stringOfMemory(finalMemory))
    }

    println("Left tree: " + stringOfTree(simpleLeftTree))
    testExec(new Memory(List(("leftTree" -> simpleLeftTree))), List(
      Call("leftRotate", List("leftTree", ObjectID(2)))
    ), allPrograms)

    println("Right tree: " + stringOfTree(simpleRightTree))
    testExec(new Memory(List(("rightTree" -> simpleRightTree))), List(
      Call("rightRotate", List("rightTree", ObjectID(3)))
    ), allPrograms)

    testExec(new Memory(List(("leftTree" -> simpleLeftTree))), List(
      Call("checkRedBlackInvariant", List(FieldAccess("leftTree", "root")))
    ), allPrograms)

    testExec(new Memory(List(("rightTree" -> simpleRightTree))), List(
      Call("checkRedBlackInvariant", List(FieldAccess("rightTree", "root")))
    ), allPrograms)

    testExec(new Memory(List(("notRBTree" -> simpleNotRBTree))), List(
      Call("checkRedBlackInvariant", List(FieldAccess("notRBTree", "root")))
    ), allPrograms)

    testExec(new Memory(List(("simpleBinaryTree" -> simpleBinaryTree), ("z" -> setParentPointers(makeNode(13, 13, Null, Null), Null)), ("z2" -> setParentPointers(makeNode(10, 10, Null, Null), Null)))), List(
      Call("treeInsert", List("simpleBinaryTree", "z")),
      Call("treeInsert", List("simpleBinaryTree", "z2"))
    ), allPrograms)

    testExec(new Memory(List(("tree" -> emptyTree), ("x" -> setParentPointers(makeNode(13, 13, Null, Null), Null)))), List(
      Call("treeInsert", List("tree", "x"))
    ), allPrograms)

    testExec(new Memory(List(("tree" -> simpleRBTree), ("x" -> setParentPointers(makeNode(4, 4, Null, Null), Null)))), List(
      Call("treeInsert", List("tree", "x"))
    ), allPrograms)

    println("RBTree: " + stringOfTree(simpleRBTree))
    println("New node: " + stringOfNode(setParentPointers(makeNode(4, UNK), Null)))
    testExec(new Memory(List(("tree" -> simpleRBTree), ("x" -> setParentPointers(makeNode(4, UNK), Null)))), List(
      Call("rbInsert", List("tree", "x")),
      Call("checkRedBlackInvariant", List(FieldAccess("tree", "root")))
    ), allPrograms)

  }

  def synthesizeLeftRotate(options: Options) {

    val leftRotateGenerator = Some( (_: Double) => {
      @tailrec def tryGen(): (Object, Object) = {
	val tree = genBinaryTree()//genRandomTree()
	val candidateNodes = getNodes(tree.fields("root")) filter { _.fields("right") != Null  }
	if (candidateNodes.isEmpty) tryGen() else (tree, randomElement(candidateNodes))
      }
      val (tree, x) = tryGen()
      List(("tree" -> tree), ("x" -> x))
    })
    val leftRotateFilter = Some( (args: Map[String, Value]) => {
      val x = args("x")
      x != Null && x.asInstanceOf[Object].fields("right") != Null  //  I don't need to ensure that tree is non-null since my generator function ensure that.
    })
    def leftRotatePostcondition(args: Map[String, Value], resMap: Map[String, Value], rv: Value): Boolean = {
      val postTree = resMap("tree").asInstanceOf[Object].fields("root")
      val preList = treeToList(args("tree").asInstanceOf[Object].fields("root"))
      val postList = treeToList(postTree)
      checkTreeInvariant(postTree) && preList == postList
    }

    val tree = fullLeftTree
    val x = tree.fields("root").asInstanceOf[Object].fields("right")
    println(stringOfTree(tree))
    println("x = " + x)
    /*test(new Trace("leftRotate", UnitType, List(("tree" -> tree), ("x" -> x)), mapOfPrograms(checkTreeInvariantProgram), btreeTypes, List(
      Assume(And(NE("x", Null), NE(FieldAccess("x", "right"), Null))),
      Assign("y", FieldAccess("x", "right")),
      Assign(FieldAccess("x", "right"), FieldAccess("y", "left")),
      Conditional(NE(FieldAccess("y", "left"), LiteralExpr(Null)), List(
	Assign(FieldAccess(FieldAccess("y", "left"), "parent"), "x")
      )),
      Conditional(EQ(FieldAccess("x", "parent"), LiteralExpr(Null)), List(
	Conditional(EQ(FieldAccess(FieldAccess("x", "parent"), "right"), "x"), List(
	  Assign(FieldAccess(FieldAccess("x", "parent"), "right"), "y")
	))
      )),
      Assign(FieldAccess("y", "parent"), FieldAccess("x", "parent")),
      Assign(FieldAccess("y", "left"), "x"),
      Assign(FieldAccess("x", "parent"), "y"),
      LiteralExpr(Call("checkTreeInvariant", List(FieldAccess("tree", "root"))))
    )), leftRotateGenerator, btreeFieldLayout, options)*/
    test("leftRotate", UnitType, List(("tree" -> tree), ("x" -> x)), leftRotateGenerator, leftRotateFilter, Some(leftRotatePostcondition), mapOfPrograms(checkTreeInvariantProgram), btreeTypes, btreeFieldLayout, options)

  }

  def synthesizeTreeInsert(options: Options) {

    val treeInsertGenerator = Some((_: Double) => {
      val tree = genBinaryTree()
      val allNodes = getNodes(tree.fields("root"))
      val allValues = allNodes.map{ o => o.fields("value").asInstanceOf[IntConstant].n }.toSet
      val v = if (allNodes.isEmpty) nextBoundedInt(0, 100) else randomElement(((allValues.min - 1) to (allValues.max + 1)).filter{ n => !allValues.contains(n) })
      val z = setParentPointers(makeNode(if (allNodes.isEmpty) 1 else allNodes.map{ o => o.id }.max + 1, v, Null, Null), Null)
      List(("tree" -> tree), ("z" -> z))
    })
    val treeInsertFilter = Some( (args: Map[String, Value]) => {
      args("tree") != Null && args("z") != Null
    })
    def treeInsertPostcondition(args: Map[String, Value], resMap: Map[String, Value], rv: Value): Boolean = {
      val postTree = resMap("tree").asInstanceOf[Object].fields("root")
      val preList = treeToList(args("tree").asInstanceOf[Object].fields("root"))
      val postList = treeToList(postTree)
      checkTreeInvariant(postTree) && preList != postList && postList.isDefined && postList.forall{ l => holdsOverIterable(l, (n1: Int, n2: Int) => n1 <= n2) }
    }

    val tree = simpleBinaryTree
    val z = setParentPointers(makeNode(13, 13, Null, Null), Null)
    println(stringOfTree(tree))
    println("z = " + z)
    /*test(new Trace("treeInsert", UnitType, List(("tree" -> tree), ("z" -> z)), mapOfPrograms(checkTreeInvariantProgram), btreeTypes, List(
      Assign("y", LiteralExpr(Null)),
      Assign("x", FieldAccess("tree", "root")),
      Iterate(List(
	(NE("x", LiteralExpr(Null)), List(
	  Assign("y", "x"),
	  Conditional(LT(FieldAccess("z", "value"), FieldAccess("x", "value")), List(Assign("x", FieldAccess("x", "right"))))
	)),
	(NE("x", LiteralExpr(Null)), List(
	  Assign("y", "x"),
	  Conditional(LT(FieldAccess("z", "value"), FieldAccess("x", "value")), List(Assign("x", FieldAccess("x", "left"))))
	)),
	(NE("x", LiteralExpr(Null)), List(
	  Assign("y", "x"),
	  Conditional(LT(FieldAccess("z", "value"), FieldAccess("x", "value")), List(Assign("x", FieldAccess("x", "left"))))
	)),
	(NE("x", LiteralExpr(Null)), Nil)
      )),
      Assign(FieldAccess("z", "parent"), "y"),
      Conditional(EQ("y", LiteralExpr(Null)), List(
	Conditional(LT(FieldAccess("z", "value"), FieldAccess("y", "value")), List(Assign(FieldAccess("y", "left"), "z")))
      )),
      LiteralExpr(Call("checkTreeInvariant", List(FieldAccess("tree", "root"))))
    )), treeInsertGenerator, btreeFieldLayout, options)*/
    test("treeInsert", UnitType, List(("tree" -> tree), ("z" -> z)), treeInsertGenerator, treeInsertFilter, Some(treeInsertPostcondition), mapOfPrograms(checkTreeInvariantProgram), btreeTypes, btreeFieldLayout, options)

  }

  def synthesizeRBInsert(options: Options) {

    val rbInsertGenerator = Some((size: Double) => {
      val tree = genRedBlackTree((size * 20).toInt)
      val allValues = getNodes(tree.fields("root")).map{ o => o.fields("value").asInstanceOf[IntConstant].n }.toSet
      val v = if (allValues.isEmpty) nextBoundedInt(0, 100) else randomElement(((allValues.min - 1) to (allValues.max + 1)).filter{ n => !allValues.contains(n) })
      val x = setParentPointers(makeNode(allValues.size + 1, v, UNK, Null, Null), Null)
      List(("tree", tree), ("x" -> x))
    })

    val tree = simpleRBTree
    val x = setParentPointers(makeNode(4, 4, UNK, Null, Null), Null)
    println(stringOfTree(tree))
    println("x = " + stringOfNode(x))
    test(new Trace("rbInsert", UnitType, List(("tree" -> tree), ("x" -> x)), mapOfPrograms(treeInsertProgram, leftRotateProgram, rightRotateProgram, grandparentProgram, checkTreeInvariantProgram, checkRedBlackInvariantProgram), rbtreeTypes, List(
      Assign("red", LiteralExpr(RED)),
      Assign("black", LiteralExpr(BLACK)),
      Call("treeInsert", List("tree", "x")),
      Assign(FieldAccess("x", "color"), "red"),
      Iterate(List(
	(And(NE("x", FieldAccess("tree", "root")), EQ(FieldAccess(FieldAccess("x", "parent"), "color"), "red")), List(
	  Assign("isLeftCase", EQ(FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "left"), FieldAccess("x", "parent"))),
	  Assign("y", LiteralExpr(Null)),
	  Conditional(LiteralExpr("isLeftCase"), List(Assign("y", FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "right")))),
	  //Conditional(EQ(FieldAccess("y", "color"), "red"), List(
	  Conditional(And(LiteralExpr(NE("y", Null)), EQ(FieldAccess("y", "color"), "red")), List(
	    Assign(FieldAccess(FieldAccess("x", "parent"), "color"), "black"),
	    Assign(FieldAccess("y", "color"), "black"),
	    Assign(FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "color"), "red"),
	    Assign("x", FieldAccess(FieldAccess("x", "parent"), "parent"))
	  ))
	)),
	(And(NE("x", FieldAccess("tree", "root")), EQ(FieldAccess(FieldAccess("x", "parent"), "color"), "red")), List(
	  Assign("isLeftCase", EQ(FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "left"), FieldAccess("x", "parent"))),
	  Assign("y", LiteralExpr(Null)),
	  Conditional(LiteralExpr("isLeftCase"), List(Assign("y", FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "right")))),
	  //Conditional(EQ(FieldAccess("y", "color"), "red"), List(
	  Conditional(And(LiteralExpr(NE("y", Null)), EQ(FieldAccess("y", "color"), "red")), List(
	    Conditional(And(LiteralExpr("isLeftCase"), EQ("x", FieldAccess(FieldAccess("x", "parent"), "right"))), List(
	      Assign("x", FieldAccess("x", "parent")),
	      Call("leftRotate", List("tree", "x"))
	    )),
	    Conditional(And(LiteralExpr(Not("isLeftCase")), EQ("x", FieldAccess(FieldAccess("x", "parent"), "left"))), Nil),
	    Assign(FieldAccess(FieldAccess("x", "parent"), "color"), "black"),
	    Assign(FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "color"), "red"),
	    Conditional(LiteralExpr("isLeftCase"), List(
	      Call("rightRotate", List("tree", FieldAccess(FieldAccess("x", "parent"), "parent")))
	    ))
	  ))
	)),
	(And(NE("x", FieldAccess("tree", "root")), EQ(FieldAccess(FieldAccess("x", "parent"), "color"), "red")), Nil)
      )),
      Assign(FieldAccess(FieldAccess("tree", "root"), "color"), "black"),
      LiteralExpr(Call("checkTreeInvariant", List(FieldAccess("tree", "root")))),
      LiteralExpr(Call("checkRedBlackInvariant", List(FieldAccess("tree", "root"))))
    )), rbInsertGenerator, rbtreeFieldLayout, options)

  }
  
  val leftRotateProgram = Program("leftRotate", UnitType, List(("tree", ObjectType("Tree")), ("x", ObjectType("Node"))), Map.empty, btreeTypes, List(
      Assume(And(NE("tree", Null), And(NE("x", Null), NE(FieldAccess("x", "right"), Null)))),
      Assign("y", FieldAccess("x", "right")),
      Assign(FieldAccess("x", "right"), FieldAccess("y", "left")),
      If(NE(FieldAccess("y", "left"), Null), List(Assign(FieldAccess(FieldAccess("y", "left"), "parent"), "x")), Nil, Nil),
      If(EQ(FieldAccess("x", "parent"), Null), 
	List(Assign(FieldAccess("tree", "root"), "y")
      ), Nil, List(
	If(EQ(FieldAccess(FieldAccess("x", "parent"), "left"), "x"), List(
	  Assign(FieldAccess(FieldAccess("x", "parent"), "left"), "y")
	), Nil, List(
	  Assign(FieldAccess(FieldAccess("x", "parent"), "right"), "y")
	))
      )),
      Assign(FieldAccess("y", "parent"), FieldAccess("x", "parent")),
      Assign(FieldAccess("y", "left"), "x"),
      Assign(FieldAccess("x", "parent"), "y"),
      UnitConstant
  ))
  val rightRotateProgram = Program("rightRotate", UnitType, List(("tree", ObjectType("Tree")), ("y", ObjectType("Node"))), Map.empty, btreeTypes, List(
      Assume(And(NE("tree", Null), And(NE("y", Null), NE(FieldAccess("y", "left"), Null)))),
      Assign("x", FieldAccess("y", "left")),
      Assign(FieldAccess("y", "left"), FieldAccess("x", "right")),
      If(NE(FieldAccess("x", "right"), Null), List(Assign(FieldAccess(FieldAccess("x", "right"), "parent"), "y")), Nil, Nil),
      If(EQ(FieldAccess("y", "parent"), Null), 
	List(Assign(FieldAccess("tree", "root"), "x")
      ), Nil, List(
	If(EQ(FieldAccess(FieldAccess("y", "parent"), "left"), "y"), List(
	  Assign(FieldAccess(FieldAccess("y", "parent"), "left"), "x")
	), Nil, List(
	  Assign(FieldAccess(FieldAccess("y", "parent"), "right"), "x")
	))
      )),
      Assign(FieldAccess("x", "parent"), FieldAccess("y", "parent")),
      Assign(FieldAccess("x", "right"), "y"),
      Assign(FieldAccess("y", "parent"), "x"),
      UnitConstant
  ))
  val checkRedBlackInvariantProgram = Program("checkRedBlackInvariant", UnitType, List(("node", ObjectType("Node"))), Map.empty, rbtreeTypes, List(
    If(EQ("node", Null), List(1), Nil, List(
      Assign("l", Call("checkRedBlackInvariant", List(FieldAccess("node", "left")))),
      Assign("r", Call("checkRedBlackInvariant", List(FieldAccess("node", "right")))),
      Assert(EQ("l", "r")),
      If(EQ(FieldAccess("node", "color"), RED), List(
	Assert(Or(EQ(FieldAccess("node", "left"), Null), EQ(FieldAccess(FieldAccess("node", "left"), "color"), BLACK))),
	Assert(Or(EQ(FieldAccess("node", "right"), Null), EQ(FieldAccess(FieldAccess("node", "right"), "color"), BLACK))),
	"l"
      ), Nil, List(
	Plus("l", 1)
      ))
    ))
  ))
  val checkTreeInvariantProgram = Program("checkTreeInvariant", UnitType, List(("node", ObjectType("Node"))), Map.empty, btreeTypes, List(
    If(EQ("node", Null), List(UnitConstant), Nil, List(
      If(NE(FieldAccess("node", "left"), Null), List(Assert(And(LT(FieldAccess(FieldAccess("node", "left"), "value"), FieldAccess("node", "value")), EQ("node", FieldAccess(FieldAccess("node", "left"), "parent"))))), Nil, Nil),
      If(NE(FieldAccess("node", "right"), Null), List(Assert(And(GT(FieldAccess(FieldAccess("node", "right"), "value"), FieldAccess("node", "value")), EQ("node", FieldAccess(FieldAccess("node", "right"), "parent"))))), Nil, Nil),
      Call("checkTreeInvariant", List(FieldAccess("node", "left"))),
      Call("checkTreeInvariant", List(FieldAccess("node", "right")))
    ))
  ))
  val treeInsertProgram = Program("treeInsert", UnitType, List(("tree", ObjectType("Tree")), ("z", ObjectType("Node"))), Map.empty, btreeTypes, List(
    Assume(And(NE("tree", Null), NE("z", Null))),
    Assign("y", Null),
    Assign("x", FieldAccess("tree", "root")),
    Loop(NE("x", Null), List(
	Assign("y", "x"),
	If(LT(FieldAccess("z", "value"), FieldAccess("x", "value")), List(Assign("x", FieldAccess("x", "left"))), Nil, List(Assign("x", FieldAccess("x", "right"))))
    )),
    Assign(FieldAccess("z", "parent"), "y"),
    If(EQ("y", Null), List(
      Assign(FieldAccess("tree", "root"), "z")
    ), Nil, List(
      If(LT(FieldAccess("z", "value"), FieldAccess("y", "value")), List(Assign(FieldAccess("y", "left"), "z")), Nil, List(Assign(FieldAccess("y", "right"), "z")))
    )),
    UnitConstant
  ))
  val rbInsertProgram = Program("rbInsert", UnitType, List(("tree", ObjectType("Tree")), ("x", ObjectType("Node"))), mapOfPrograms(treeInsertProgram, leftRotateProgram, rightRotateProgram), rbtreeTypes, List(
    Assume(NE("tree", Null)),
    Assign("red", LiteralExpr(RED)),
    Assign("black", LiteralExpr(BLACK)),
    Call("treeInsert", List("tree", "x")),
    Assign(FieldAccess("x", "color"), "red"),
    Loop(And(NE("x", FieldAccess("tree", "root")), EQ(FieldAccess(FieldAccess("x", "parent"), "color"), "red")), List(
      Assign("isLeftCase", EQ(FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "left"), FieldAccess("x", "parent"))),
      Assign("y", Null),
      If("isLeftCase", List(Assign("y", FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "right"))), Nil, List(Assign("y", FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "left")))),
      //If(EQ(FieldAccess("y", "color"), "red"), List(
      If(And(NE("y", Null), EQ(FieldAccess("y", "color"), "red")), List(
	Assign(FieldAccess(FieldAccess("x", "parent"), "color"), "black"),
	Assign(FieldAccess("y", "color"), "black"),
	Assign(FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "color"), "red"),
	Assign("x", FieldAccess(FieldAccess("x", "parent"), "parent"))
      ), Nil, List(
	If(And("isLeftCase", EQ("x", FieldAccess(FieldAccess("x", "parent"), "right"))), List(
	  Assign("x", FieldAccess("x", "parent")),
	  Call("leftRotate", List("tree", "x"))
	), Nil, Nil),
	If(And(Not("isLeftCase"), EQ("x", FieldAccess(FieldAccess("x", "parent"), "left"))), List(
	  Assign("x", FieldAccess("x", "parent")),
	  Call("rightRotate", List("tree", "x"))
	), Nil, Nil),
	Assign(FieldAccess(FieldAccess("x", "parent"), "color"), "black"),
	Assign(FieldAccess(FieldAccess(FieldAccess("x", "parent"), "parent"), "color"), "red"),
	If("isLeftCase", List(
	  Call("rightRotate", List("tree", FieldAccess(FieldAccess("x", "parent"), "parent")))
	), Nil, List(
	  Call("leftRotate", List("tree", FieldAccess(FieldAccess("x", "parent"), "parent")))
	))
      ))
    )),
    Assign(FieldAccess(FieldAccess("tree", "root"), "color"), "black"),
    UnitConstant
  ))
  val grandparentProgram = Program("grandparent", ObjectType("Node"), List(("x", ObjectType("Node"))), Map.empty, btreeTypes, List(
    Assume(And(NE("x", Null), NE(FieldAccess("x", "parent"), Null))),
    FieldAccess(FieldAccess("x", "parent"), "parent")
  ))

  val allPrograms = Map.empty ++ List(("leftRotate" -> leftRotateProgram), ("rightRotate" -> rightRotateProgram), ("checkRedBlackInvariant" -> checkRedBlackInvariantProgram), ("checkTreeInvariant" -> checkTreeInvariantProgram), ("treeInsert" -> treeInsertProgram), ("rbInsert" -> rbInsertProgram), ("grandparent" -> grandparentProgram))

  def showRandomTree(size: Int, options: Options) {
    val controller = new Controller(makeSynthesizer("", UnitType, Nil, Map.empty, Map.empty, objectComparators = treeComparator), Map.empty, Map.empty, treeComparator, rbtreeFieldLayout, treeLayout, options)
    val mem = new Memory(List("tree" -> genRedBlackTree(size)))
    controller.updateDisplay(mem, Nil, Some(Null))
    controller.getStmtTrace(mem, false)
  }

}
