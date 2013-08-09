package pbd.test

protected[test] object TestCommon {

  import pbd.lang.AST._
  import pbd.lang.Printer
  import pbd.Utils._
  import pbd.Controller.Options
  import scala.annotation.tailrec
  import scala.language.implicitConversions

  implicit def string2Var(s: String) = Var(s)
  implicit def int2IntConstant(n: Int) = IntConstant(n)
  implicit def boolean2BooleanConstant(b: Boolean) = BooleanConstant(b)

  val swapProgram = Program("swap", UnitType, List(("a", ArrayType(IntType)), ("i1", IntType), ("i2", IntType)), Map.empty, Map.empty, List(Assign("tmp", ArrayAccess("a", "i1")), Assign(ArrayAccess("a", "i1"), ArrayAccess("a", "i2")), Assign(ArrayAccess("a", "i2"), "tmp"), UnitConstant))
  val answerProgram = Program("answer", IntType, Nil, Map.empty, Map.empty, List(42))
  val timesthreeProgram = Program("timesthree", IntType, List(("x", IntType)), Map.empty, Map.empty, List(Times("x", 3)))
  val fibProgram = Program("fib", IntType, List(("n", IntType)), Map.empty, Map.empty, List(If(LT("n", 2), List("n"), Nil, List(Plus(Call("fib", List(Minus("n", 1))), Call("fib", List(Minus("n", 2))))))))
  val factProgram = Program("fact", IntType, List(("n", IntType)), Map.empty, Map.empty, List(If(LE("n", 1), List(1), Nil, List(Times("n", Call("fact", List(Minus("n", 1))))))))
  val sumProgram = Program("sum", IntType, List(("x", IntType), ("y", IntType)), Map.empty, Map.empty, List(Plus("x", "y")))
  val checkSortedProgram = Program("checkSorted", UnitType, List(("a", ArrayType(IntType))), Map.empty, Map.empty, List( Loop(In("i", Until(0, Minus(ArrayLength("a"), 1))), List(Assert(LE(ArrayAccess("a", "i"), ArrayAccess("a", Plus("i", 1)))))) ))
  val containsProgram = Program("contains", BooleanType, List(("a", ArrayType(IntType)), ("x", IntType)), Map.empty, Map.empty, List( Assign("found", false), Loop(In("i", Until(0, ArrayLength("a"))), List(If(EQ(ArrayAccess("a", "i"), "x"), List(Assign("found", true), Break), Nil, Nil))), "found" ))
  val lengthProgram = Program("length", IntType, List(("list", ObjectType("Node"))), Map.empty, Map.empty, List( If(EQ("list", Null), List(0), Nil, List(Plus(Call("length", List(FieldAccess("list", "next"))), 1))) ))
  val reverseProgram = Program("reverse", ObjectType("Node"), List(("list", ObjectType("Node"))), Map.empty, Map.empty, List( Assign("cur", "list"), Assign("prev", Null), Loop(NE("cur", Null), List(UnorderedStmts(List(Assign(FieldAccess("cur", "next"), "prev"), Assign("cur", FieldAccess("cur", "next")), Assign("prev", "cur"))))), "prev" ))
  val selectionSortProgram = Program("selectionSort", UnitType, List(("a", ArrayType(IntType))), mapOfPrograms(swapProgram), Map.empty, List( Loop(In("i", Until(0, Minus(ArrayLength("a"), 1))), List(Assign("min", "i"), Loop(In("j", Until(Plus("i", 1), ArrayLength("a"))), List(If(LT(ArrayAccess("a", "j"), ArrayAccess("a", "min")), List(Assign("min", "j")), Nil, Nil))), Call("swap", List("a", "i", "min")))) ))

  def mapOfPrograms(programs: Program*): Map[String, Program] = programs.map{ p => (p.name, p) }.toMap

  val listTypes = Map.empty + ("Node" -> List(("value", IntType), ("next", ObjectType("Node"))))
  val btreeTypes = Map.empty ++ List(("Node" -> List(("value", IntType), ("left", ObjectType("Node")), ("right", ObjectType("Node")), ("parent", ObjectType("Node")))), ("Tree" -> List(("root", ObjectType("Node")))))
  val rbtreeTypes = Map.empty ++ List(("Node" -> List(("value", IntType), ("color", StringType), ("left", ObjectType("Node")), ("right", ObjectType("Node")), ("parent", ObjectType("Node")))), ("Tree" -> List(("root", ObjectType("Node")))), ("Color" -> List(("color", IntType))))

  val listFieldLayout = Map.empty + ("Node" -> List(List("value", "next")))
  val btreeFieldLayout = Map.empty + ("Node" -> List(List("parent"), List("value"), List("left", "right")))
  val rbtreeFieldLayout = Map.empty + ("Node" -> List(List("parent"), List("value"), List("color"), List("left", "right")))

  def stringOfList(v: Value, printer: Printer, seen: Set[Int] = Set[Int]()): String = v match {
    case Null => "null"
    case Object(id, _, fields) => 
      if (seen contains id)
	printer.stringOfValue(fields("value"))
      else
	printer.stringOfValue(fields("value")) + " -> " + stringOfList(fields("next"), printer, seen + id)
  }

  def layoutList(list: Object, widthFn: Value => Int, heightFn: Value => Int, spacing: Int): Iterable[(Object, (Int, Int))] = {
    val nodeWidth = widthFn(list)
    def doLayout(list: Value, curX: Int): List[(Object, (Int, Int))] = (list: @unchecked) match {
      case Null => Nil
      case list @ Object(_, _, fields) =>
	(list -> ((curX, 0))) :: doLayout(list.fields("next"), curX + nodeWidth + spacing)
    }
    doLayout(list, 0)
  }

  /**
   * Lay out a binary tree.
   * Adapted from "Tidy Drawings of Trees" by Wetherell and Shannon (modified Algorithm 3).
   */
  def layoutBinaryTree(tree: Object, widthFn: Value => Int, heightFn: Value => Int, spacing: Int): Iterable[(Object, (Int, Int))] = {
    import math.{ max, min }
    import java.util.Arrays
    import scala.collection.mutable.Map
    if (tree == Null)
      return Nil
    val (nodeWidth, nodeHeight) = (widthFn(tree), heightFn(tree))
    val xOffset = nodeWidth + spacing
    val positions = Map.empty[Object, (Int, Int)]
    val modifiers = Map.empty[Object, Int]
    val treeHeight = {
      def getTreeHeight(n: Value): Int = (n: @unchecked) match {
	case Null => 0
	case Object(_, _, fields) => max(getTreeHeight(fields("left")), getTreeHeight(fields("right"))) + 1
      }
      getTreeHeight(tree)
    }
    val modifier = Array.fill(treeHeight + 1)(0)
    val nextPos = Array.fill(treeHeight + 1)(0)
    def firstPass(node: Value, curHeight: Int): Unit = (node: @unchecked) match {
      case Null =>
      case node @ Object(_, _, fields) =>
	val (left, right) = (fields("left"), fields("right"))
	firstPass(left, curHeight + 1)
	firstPass(right, curHeight + 1)
	val place = (left, right) match {
	  case (Null, Null) => nextPos(curHeight)
	  case (Null, r: Object) => positions(r)._1 - xOffset
	  case (l: Object, Null) => positions(l)._1 + xOffset
	  case (l: Object, r: Object) => (positions(l)._1 + positions(r)._1) / 2
	}
	modifier(curHeight) = max(modifier(curHeight), nextPos(curHeight) - place)
	val curX = (left, right) match {
	  case (Null, Null) => place
	  case _ => place + modifier(curHeight)
	}
	positions += node -> (curX, -1)
	nextPos(curHeight) = curX + 2 * xOffset
	modifiers += node -> modifier(curHeight)
    }
    def secondPass(node: Value, curHeight: Int, modifierSum: Int, isRight: Boolean): Unit = (node: @unchecked) match {
      case Null =>
      case node @ Object(_, _, fields) =>
	val (left, right) = (fields("left"), fields("right"))
	val nextModifierSum = modifierSum + modifiers(node)
	secondPass(left, curHeight + 1, nextModifierSum, false)
	val curX = max(max(min(nextPos(curHeight), positions(node)._1 + modifierSum), left match { case l: Object => positions(l)._1 + xOffset case Null => Int.MinValue }), if (isRight) positions(fields("parent").asInstanceOf[Object])._1 + xOffset else Int.MinValue)
	nextPos(curHeight) = curX + 2 * xOffset
	val curY = curHeight * (nodeHeight + spacing)
	positions += node -> (curX, curY)
	secondPass(right, curHeight + 1, nextModifierSum, true)
    }
    firstPass(tree, 0)
    Arrays.fill(nextPos, 0)
    secondPass(tree, 0, 0, false)
    positions
  }

  val listLayout = scala.collection.immutable.Map.empty + ("Node" -> (layoutList _))
  val treeLayout = scala.collection.immutable.Map.empty + ("Node" -> (layoutBinaryTree _))

  def compareLists(l1: Value, l2: Value): Int = {
    @tailrec def numNodesInList(l: Value, seen: Set[Int], count: Int): Int = l match {
      case Null => count
      case Object(id, _, fields) =>
	if (seen contains id)
	  count
	else
	  numNodesInList(fields("next"), seen + id, count + 1)
    }
    numNodesInList(l1, Set.empty, 0) - numNodesInList(l2, Set.empty, 0)
  }

  def compareBinaryTrees(t1: Value, t2: Value): Int = {
    def numNodesInTree(t: Value, seen: Set[Int]): Int = t match {
      case Null => 0
      case Object(id, _, fields) =>
	if (seen contains id)
	  0
	else {
	  val newSeen = seen + id
	  numNodesInTree(fields("left"), newSeen) + numNodesInTree(fields("right"), newSeen) + 1
	}
    }
    numNodesInTree(t1, Set.empty) - numNodesInTree(t2, Set.empty)
  }
  def compareBinaryTreesTree(t1: Value, t2: Value): Int = (t1, t2) match {
    case (Null, Null) => 0
    case (Null, _) => -1
    case (_, Null) => 1
    case (Object(_, _, f1), Object(_, _, f2)) => compareBinaryTrees(f1("root"), f2("root"))
  }

  val listComparator = Map.empty + ("Node" -> (compareLists _))
  val treeComparator = Map.empty ++ List(("Node" -> (compareBinaryTrees _)), ("Tree" -> (compareBinaryTreesTree _)))

  def intArrayIsSorted(arrName: String)(args: Map[String, Value], resMap: Map[String, Value], rv: Value): Boolean = {
    val array = resMap(arrName).asInstanceOf[ArrayValue].array.map{ n => n.asInstanceOf[IntConstant].n }
    holdsOverIterable(array, (n1: Int, n2: Int) => n1 <= n2)
  }

  def treeToList(tree: Value): Option[List[Int]] = {
    def toList(tree: Value, seen: Set[Int]): Option[List[Int]] = tree match {
      case Null => Some(Nil)
      case Object(id, _, fields) =>
	if (seen contains id)
	  None
	else {
	  val newSeen = seen + id
	  (toList(fields("left"), newSeen), toList(fields("right"), newSeen)) match {
	    case (Some(l), Some(r)) => Some(l ++ List(fields("value").asInstanceOf[IntConstant].n) ++ r)
	    case _ => None
	  }
	}
    }
    toList(tree, Set.empty)
  }

  def checkTreeInvariant(tree: Value): Boolean = {
    val seen = scala.collection.mutable.Set.empty[Int]
    def helper(tree: Value, parent: Value): Boolean = tree match {
      case Null => true
      case Object(id, _, fields) =>
	if (seen contains id)
	  return false
	if (fields("parent") != parent)
	  return false
	seen += id
	helper(fields("left"), tree) && helper(fields("right"), tree)
    }
    helper(tree, Null)
  }

  def parseCommandLine(args: Array[String]): Options = {
    import scala.util.Random.{ setSeed, nextLong }
    def showUsage() {
      println("<prog> [--seed N] [--help]")
      println("  --seed N   Sets the random seed used to generate test cases")
      println("  --dump-backup-data <file>   Dumps backup information that can be used to restore after a crash")
      println("  --load-backup-data <file>   Loads backup information from a file")
      println("  --help     Displays this help text")
    }
    var seedSet = false
    def setRandomSeed(seed: Long) {
      println("Setting random seed to " + seed)
      seedSet = true
      setSeed(seed)
    }
    var dumpBackupData: Option[String] = None
    var loadBackupData: Option[String] = None
    var extraOptions = scala.collection.mutable.ListBuffer.empty[String]
    var i = 0
    while (i < args.length) {
      if (args(i) == "--help") {
        showUsage()
        System.exit(1)
      } else if (args(i) == "--seed" && i + 1 < args.length) {
	setRandomSeed(args(i+1).toLong)
	i += 2
      } else if (args(i) == "--dump-backup-data" && i + 1 < args.length) {
	dumpBackupData = Some(args(i + 1))
	i += 2
      } else if (args(i) == "--load-backup-data" && i + 1 < args.length) {
	loadBackupData = Some(args(i + 1))
	i += 2
      } else {
        extraOptions += args(i)
	i += 1
      }
    }
    if (!seedSet)
      setRandomSeed(nextLong())
    new Options(dumpBackupData, loadBackupData, extraOptions.toList)
  }

  protected[test] def makeIntArray(id: Int, elems: Iterable[Int]): ArrayValue = ArrayValue(id, elems.map{ n => IntConstant(n) }.toArray, IntType)

}
