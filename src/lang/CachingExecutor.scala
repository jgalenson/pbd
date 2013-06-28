package graphprog.lang

import AST._
import ASTUtils._

class CachingExecutor(private val functions: Map[String, Program], private val printer: Printer, private val holeHandler: (Memory, Hole) => Stmt = Executor.errorOnHole, private val shouldPrint: Boolean = false) extends Executor(functions, printer, holeHandler, shouldPrint) {

  import scala.collection.mutable.{ HashMap => MHashMap, Map => MMap, ListBuffer }

  private val equivalences = MHashMap.empty[(Memory, Expr), Value]
  //private var misses = 0
  //private var lookups = 0

  override def eval(memory: Memory, e: Expr): Value = {
    //println("Hit rate: " + ((lookups - misses) / misses.toDouble))
    //lookups += 1
    equivalences.getOrElseUpdate((memory, e), { /*misses += 1;*/ super.eval(memory, e) })
  }

}
