package graphprog.synthesis

import graphprog.lang.AST._

object SynthesisUtils {

  import graphprog.lang.{ Executor, Memory }
  import graphprog.lang.ASTUtils._

  protected[synthesis] def yieldEquivalentResults(memoryPre: Memory, cur: Stmt, targetOutput: Value, targetMemoryPost: Memory, executor: Executor): Boolean = {
    val (curResult, curMemoryPost) = executor.execute(memoryPre, cur)
    areEquivalent(curResult, targetOutput, curMemoryPost, targetMemoryPost)
  }
  protected[synthesis] def yieldEquivalentResults(memory: Memory, cur: Stmt, targetStmt: Stmt, executor: Executor): Boolean = {
    val (curResult, curMemoryPost) = executor.execute(memory, cur)
    val (targetResult, targetMemoryPost) = executor.execute(memory, targetStmt)
    areEquivalent(curResult, targetResult, curMemoryPost, targetMemoryPost)
  }

 protected[synthesis] def possibilitiesToExpr[T <: Stmt](possibilities: Iterable[T], noneFn: => T): T = {
    val numPossibilities = possibilities.size
    if (numPossibilities == 0)
      noneFn
    else if (numPossibilities == 1)
      possibilities.head
    else
      PossibilitiesHole(possibilities.toList).asInstanceOf[T]
  }
  protected[synthesis]  def possibilitiesToStmt(hole: PossibilitiesHole, possibilities: Iterable[Stmt]): Stmt = {
    if (possibilities.size == hole.possibilities.size)
      hole
    else
      possibilitiesToExpr(possibilities, throw new SolverError("No possibilities remaining for hole " + hole))
  }

  /* Exception class */

  protected[synthesis] class SolverError(msg: String) extends RuntimeException {
    override def toString: String = "SolverError: " + msg
  }

}
