package pbd.test

object TestSynthesis {

  import scala.collection.immutable.{ Map => IMap }
  import scala.collection.mutable.{ Map => MMap }
  import pbd.lang.AST._
  import pbd.lang.{ Executor, Memory, Printer, Typer }
  import pbd.synthesis.CodeGenerator
  import pbd.synthesis.Synthesis.makeSynthesizerFromTrace
  import pbd.test.TestCommon._
  import pbd.Controller.{ Options, synthesize }
  import pbd.Utils._

  def main(args: Array[String]) {
    val options = parseCommandLine(args)
    //testOrdering(options)
    //testMultipleMemories(options)
    //testTiming(options)
    //testCurMem(options)
    testGreaterDepth(options)
  }

  private val printer = new Printer(Map.empty, true)
  private val executor = new Executor(Map.empty, printer)
  private val typer = new Typer(Map.empty, Map.empty)
  private val codeGenerator = new CodeGenerator(IMap.empty, printer, executor, typer, MMap.empty)

  def stringOfStmts(xs: Iterable[Stmt]): String = iterableToString(xs, ", ", (s: Stmt) => printer.stringOfStmt(s))

  def testOrdering(options: Options) {
    assert(stringOfStmts(codeGenerator.genAllExprs(List((1, new Memory(List(("x" -> IntConstant(1)), ("y" -> IntConstant(1)))))), 1, None)) == "x, y, 1, y / x, x / y, x * y, x * x, y * y")
    assert(stringOfStmts(codeGenerator.genAllExprs(List((1, new Memory(List(("z" -> IntConstant(1)), ("y" -> IntConstant(1)))))), 1, None)) == "y, 1, z / y, y / z, y * z, z, z * z, y * y")
    assert(stringOfStmts(codeGenerator.genAllExprs(List((42, new Memory(List(("a" -> makeIntArray(0, List(42))), ("i" -> IntConstant(0)))))), 1, None)) == "42, a[0], a[i]")
    assert(stringOfStmts(codeGenerator.genAllExprs(List((42, new Memory(List(("z" -> makeIntArray(0, List(42))), ("i" -> IntConstant(0)))))), 1, None)) == "42, z[0], z[i]")
  }

  def testMultipleMemories(options: Options) {
    println(stringOfStmts(codeGenerator.genAllExprs(List((1, new Memory(List(("x" -> IntConstant(1)), ("y" -> IntConstant(1))))), (42, new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(137)))))), 1, None)))
  }

  def testTiming(options: Options) {
    println(stringOfStmts(time(codeGenerator.genAllExprs(List((1, new Memory(List(("a" -> IntConstant(11)), ("b" -> IntConstant(42)), ("c" -> IntConstant(137)), ("d" -> IntConstant(4242)))))), 3, None))))
  }

  def testCurMem(options: Options) {
    println(stringOfStmts(time(codeGenerator.genAllExprs(List((14, new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(3)))))), 3, Some(new Memory(List(("x" -> IntConstant(137)), ("y" -> IntConstant(0)))))))))
  }

  def testGreaterDepth(options: Options) {

    def makeNode(id: Int, v: Int, n: Value): Object = Object(id, "Node", MMap.empty[String, Value] ++ List(("value" -> IntConstant(v)), ("next" -> n)))
    def next(o: Value): Value = o match  {
      case Object(_, _, fields) => fields("next")
      case _ => throw new RuntimeException
    }
    def value(o: Value): Int = o match  {
      case Object(_, _, fields) => fields("value").asInstanceOf[IntConstant].n
      case _ => throw new RuntimeException
    }
    def sizePrecondition(minSize: Int)(args: IMap[String, Value]): Boolean = {
      def length(l: Value, seen: Set[Int]): Int = l match {
	case Null => 0
	case Object(id, _, fields) => if (seen.contains(id)) -1 else length(fields("next"), seen + id) + 1
      }
      length(args("l"), Set.empty) >= minSize
    }
    
    // Find more expressions to get l.next.next.value.
    val l1 = makeNode(0, 42, makeNode(1, 42, makeNode(2, 42, makeNode(3, 42, Null))))
    val trace1 = new Trace("third", ObjectType("node"), List(("l" -> l1), ("x" -> 137)), Map.empty, listTypes, List(Assign("x", IntConstant(42))))
    val result1 = synthesize(trace1, makeSynthesizerFromTrace(trace1, precondition = Some(sizePrecondition(4)), objectComparators = listComparator) _, trace1.functions, trace1.objectTypes, listComparator, listFieldLayout, listLayout, options)
    println("Result:\n" + printer.stringOfProgram(result1))
    
    // Finx more exprs on first line to get l.next.next.value + l.next.value
    def valuePostcondition(args: Map[String, Value], resMap: Map[String, Value], rv: Value): Boolean = rv match {
      case IntConstant(rv) => rv == (value(next(next(args("l")))) + value(next(args("l"))))
      case _ => false
    }
    val l2 = makeNode(0, -42, makeNode(1, 137, makeNode(2, 42, makeNode(3, 1337, Null))))
    val trace2 = new Trace("third", IntType, List(("l" -> l2), ("x" -> 137)), Map.empty, listTypes, List(Assign("y", 42), Assign("z", 137), LiteralExpr(Plus("y", "z"))))
    val result2 = synthesize(trace2, makeSynthesizerFromTrace(trace2, precondition = Some(sizePrecondition(4)), postcondition = Some(valuePostcondition), objectComparators = listComparator) _, trace2.functions, trace2.objectTypes, listComparator, listFieldLayout, listLayout, options)
    println("Result:\n" + printer.stringOfProgram(result2))

    // Finding more expressions might make it search l.next.next, which works for first memory but crashes in current one.
    val l3 = makeNode(0, 42, makeNode(1, 42, makeNode(2, 42, makeNode(3, 42, Null))))
    val trace3 = new Trace("third", ObjectType("node"), List(("l" -> l3), ("x" -> 137)), Map.empty, listTypes, List(Assign("x", IntConstant(42))))
    val result3 = synthesize(trace3, makeSynthesizerFromTrace(trace3, precondition = Some(sizePrecondition(1)), objectComparators = listComparator) _, trace3.functions, trace3.objectTypes, listComparator, listFieldLayout, listLayout, options)
    println("Result:\n" + printer.stringOfProgram(result3))

  }
  
}
