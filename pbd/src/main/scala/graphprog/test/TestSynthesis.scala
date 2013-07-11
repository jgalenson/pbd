package graphprog.test

object TestSynthesis {

  import scala.collection.immutable.{ Map => IMap }
  import graphprog.lang.AST._
  import graphprog.lang.{ Executor, Printer, Typer }
  import graphprog.synthesis.CodeGenerator
  import graphprog.test.TestCommon._
  import graphprog.Controller.Options
  import graphprog.Utils._

  def main(args: Array[String]) {
    val options = parseCommandLine(args)
    //testOrdering(options)
    //testMultipleMemories(options)
    testTiming(options)
  }

  private val printer = new Printer(Map.empty, true)
  private val executor = new Executor(Map.empty, printer)
  private val typer = new Typer(Map.empty, Map.empty)
  private val codeGenerator = new CodeGenerator(IMap.empty, printer, executor, typer)

  def stringOfStmts(xs: Iterable[Stmt]): String = iterableToString(xs, ", ", (s: Stmt) => printer.stringOfStmt(s))

  def testOrdering(options: Options) {
    assert(stringOfStmts(codeGenerator.genAllExprs(List((1, new Memory(List(("x" -> IntConstant(1)), ("y" -> IntConstant(1)))))), 1)) == "x, y, 1, y / x, x / y, x * y, x * x, y * y")
    assert(stringOfStmts(codeGenerator.genAllExprs(List((1, new Memory(List(("z" -> IntConstant(1)), ("y" -> IntConstant(1)))))), 1)) == "y, 1, z / y, y / z, y * z, z, z * z, y * y")
    assert(stringOfStmts(codeGenerator.genAllExprs(List((42, new Memory(List(("a" -> IntArray(0, List(42).toArray)), ("i" -> IntConstant(0)))))), 1)) == "42, a[0], a[i]")
    assert(stringOfStmts(codeGenerator.genAllExprs(List((42, new Memory(List(("z" -> IntArray(0, List(42).toArray)), ("i" -> IntConstant(0)))))), 1)) == "42, z[0], z[i]")
  }

  def testMultipleMemories(options: Options) {
    println(stringOfStmts(codeGenerator.genAllExprs(List((1, new Memory(List(("x" -> IntConstant(1)), ("y" -> IntConstant(1))))), (42, new Memory(List(("x" -> IntConstant(42)), ("y" -> IntConstant(137)))))), 1)))
  }

  def testTiming(options: Options) {
    println(stringOfStmts(time(codeGenerator.genAllExprs(List((1, new Memory(List(("a" -> IntConstant(11)), ("b" -> IntConstant(42)), ("c" -> IntConstant(137)), ("d" -> IntConstant(4242)))))), 3))))
  }
  
}
