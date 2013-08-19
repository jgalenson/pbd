package pbd.test

object Graph {

  import pbd.Controller
  import pbd.Controller._
  import pbd.lang.AST._
  import pbd.lang.Printer
  import pbd.synthesis.Synthesis._
  import pbd.Utils._
  import TestCommon._
  import scala.collection.mutable.{ Map => MMap }

  def main(args: Array[String]) {
    val options = parseCommandLine(args)
    testGraph(options)
    testDSW(options)
  }

  val graphTypes = Map.empty ++ List(("Graph" -> List("nodes" -> ArrayType(ObjectType("Node")))), ("Node" -> List(("value", IntType), ("visited", BooleanType), ("index", IntType), ("children", ArrayType(ObjectType("Node"))))))

  private def getObjArr(node: Object, name: String): Array[Value] = node.fields(name).asInstanceOf[ArrayValue].array

  def makeGraph(allChildren: Iterable[(Int, Iterable[Int])]): Object = {
    assert(allChildren.map{ _._1 }.toList.distinct == allChildren.map{ _._1 })
    val nodes = allChildren.zipWithIndex.map{ case ((value, children), id) => (value, Object(id + 2, "Node", MMap.empty ++ List(("value" -> value), ("visited" -> BooleanConstant(false)), ("index" -> IntConstant(0)), ("children" -> ArrayValue(allChildren.size + id + 2, { for (_ <- 0 until children.size) yield Null }.toArray, ObjectType("Node")))))) }.toMap
    allChildren.foreach{ case (value, children) => {
      val childArr = getObjArr(nodes(value), "children")
      children.zipWithIndex.foreach{ case (child, i) => childArr(i) = nodes(child) }
    } }
    Object(0, "Graph", MMap.empty + ("nodes" -> ArrayValue(1, nodes.values.toArray, ObjectType("Node"))))
  }

  def stringOfNode(node: Value): String = node match {
    case Null => "null"
    case node @ Object(id, _, fields) => printer.stringOfValue(fields("value")) + "(" + id + "), " + printer.stringOfValue(fields("visited")) + "," + printer.stringOfValue(fields("index")) + " -> [" + iterableToString(getObjArr(node, "children").map{ case Null => "null" case Object(id, _, fields) => printer.stringOfValue(fields("value")) + "(" + id + ")" }, ", ") + "](" + fields("children").asInstanceOf[ArrayValue].id + ")"
  }
  def stringOfGraph(graph: Value): String = {
    /*def findNodes(nodes: Map[Int, Object], node: Value): Map[Int, Object] = node match {
      case Null => nodes
      case node @ Object(id, _, fields) =>
	if (nodes.contains(id))
	  return nodes
	getChildArr(node).foldLeft(nodes + (id -> node))(findNodes)
    }
    iterableToString(findNodes(Map.empty[Int, Object], node).values.map(stringOfNode), "; ")*/
    graph match {
      case Null => "null"
      case graph @ Object(_, _, fields) => iterableToString(getObjArr(graph, "nodes").map(stringOfNode), ";  ")
    }
  }

  val printHelpers: PartialFunction[String, Value => String] = (s: String) => s match {
    case "Graph" => v => "Graph(" + stringOfGraph(v) + ")"
    case "Node" => v => "Node(" + stringOfNode(v) + ")"
  }

  val printer = new Printer(printHelpers, false)

  def layoutNode(node: Object, widthFn: Value => Int, heightFn: Value => Int, spacing: Int): Iterable[(Object, (Int, Int))] = {
    val seen = MMap.empty[Object, (Int, Int)]
    def doLayout(node: Value, curX: Int, curY: Int): Unit = (node: @unchecked) match {
      case Null => 
      case node @ Object(_, _, fields) =>
	if (seen.contains(node))
	  return
	seen += (node -> ((curX, curY)))
	getObjArr(node, "children").zipWithIndex.foreach{ case (child, i) => doLayout(child, curX + widthFn(node) + spacing, curY + i * (heightFn(node) + spacing)) }
    }
    doLayout(node, 0, 0)
    seen
  }

  def nodesReachableFrom(seen: Set[Object], t: Value): Set[Object] = t match {
    case o: Object if !seen.contains(o) => getObjArr(o, "children").foldLeft(seen + o)(nodesReachableFrom)
    case _ => seen
  }

  def compareGraphNodes(t1: Value, t2: Value): Int = {
    nodesReachableFrom(Set.empty, t1).size - nodesReachableFrom(Set.empty, t2).size
  }
  def compareGraph(t1: Value, t2: Value): Int = (t1, t2) match {
    case (Null, Null) => 0
    case (Null, _) => -1
    case (_, Null) => 1
    case (o1: Object, o2: Object) => getObjArr(o1, "nodes").length - getObjArr(o2, "nodes").length
  }

  val graphComparator = Map.empty ++ List(("Node" -> (compareGraphNodes _)), ("Tree" -> (compareGraph _)))

  val graphLayout = scala.collection.immutable.Map.empty ++ List(("Node" -> (layoutNode _)))

  val graphGenerator = Some((sizeWeight: Double) => {
    import scala.util.Random.{nextInt, nextBoolean, nextFloat, shuffle}
    val size = Math.max(1, (10 * sizeWeight).toInt)
    val elems = shuffle((0 to 2 * size).toList).take(size)
    val graph = makeGraph(elems.map{ elem => (elem, shuffle(elems).take(nextInt(size))) })
    List(("tree" -> graph), ("x" -> shuffle(getObjArr(graph, "nodes").toList).head))
  })

  def testGraph(options: Options) {
    val list = makeGraph(List((0, List(1)), (1, List(2)), (2, Nil)))
    val circle = makeGraph(List((0, List(1)), (1, List(2)), (2, List(0))))
    val fan = makeGraph(List((0, List(1, 2)), (1, List(3, 4)), (2, List(5, 6)), (3, Nil), (4, Nil), (5, Nil), (6, Nil)))

    println("List:\n" + stringOfGraph(list))
    println("Circle:\n" + stringOfGraph(circle))
    println("Fan:\n" + stringOfGraph(fan))
  }

  def testDSW(options: Options) {

    val list = makeGraph(List((0, List(1)), (1, Nil)))


    val fan = makeGraph(List((0, List(1, 2)), (1, List(3, 4)), (2, List(5, 6)), (3, Nil), (4, Nil), (5, Nil), (6, Nil)))

    def test(name: String, typ: Type, inputs: List[(String, Value)], generator: Option[Double => List[(String, Value)]], precondition: Option[Map[String, Value] => Boolean], postcondition: Option[(Map[String, Value], Map[String, Value], Value) => Boolean], functions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], options: Options) {
      try {
	val result = synthesize(inputs, makeSynthesizer(name, typ, pbd.lang.Typer.typeOfInputs(inputs), functions, objectTypes, printHelpers, generator, precondition, postcondition, graphComparator) _, functions, objectTypes, graphComparator, Map.empty[String, List[List[String]]], graphLayout, options)
	println("Result:\n" + printer.stringOfProgram(result))
      } catch {
	case e: Throwable => e.printStackTrace
      }
    }

    def dswPostcondition(args: Map[String, Value], resMap: Map[String, Value], rv: Value): Boolean = {
      val argNodes = getObjArr(args("tree").asInstanceOf[Object], "nodes")
      val resNodes = getObjArr(resMap("tree").asInstanceOf[Object], "nodes")
      nodesReachableFrom(Set.empty, resMap("x")).forall{ _.asInstanceOf[Object].fields("visited").asInstanceOf[BooleanConstant].b } &&
      argNodes.zip(resNodes).forall{ case (o1 @ Object(id1, _, f1), o2 @ Object(id2, _, f2)) => id1 == id2 && f1("value") == f2("value") && getObjArr(o1, "children").toList == getObjArr(o2, "children").toList case _ => false }
    }
    
    val tree = list
    test("DSW", UnitType, List(("tree" -> tree), ("x" -> getObjArr(tree, "nodes")(0))), graphGenerator, None, Some(dswPostcondition), Map.empty, graphTypes, options)
    
  }

}
