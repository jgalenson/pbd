package pbd.lang

import AST._
import ASTUtils._

class CachingExecutor(private val functions: Map[String, Program], private val printer: Printer, private val holeHandler: (Memory, Hole) => Stmt = Executor.errorOnHole, private val shouldPrint: Boolean = false) extends Executor(functions, printer, holeHandler, shouldPrint) {

  import scala.collection.mutable.{ HashMap => MHashMap }

  private val equivalences = MHashMap.empty[(Memory, Expr), (Option[Memory], Value)]
  //private val equivalences = new ConcurrentHashMap[(Memory, Expr), Value]
  //private var misses = 0
  //private var lookups = 0

  override def eval(memory: Memory, e: Expr): Value = {
    //println("Hit rate: " + ((lookups - misses) / lookups.toDouble))
    //lookups += 1
    equivalences.get((memory, e)) match {
      case Some((mOpt, v)) =>
	mOpt.foreach{ m => memory.cloneFrom(m) }
        v match {  // We have to use the current memory's version of the result if it is in the heap.
	  case ArrayValue(id, _, _) => memory.getArray(id).get
	  case Object(id, _, _) => memory.getObject(id).get
	  case v => v
	}
      case None => 
	//misses += 1
	val initMem = memory.clone
	val result = super.eval(memory, e)  // This must come before the next line so that we get side effects to memory before cloning it.
	equivalences += ((initMem, e) -> (if (memoriesAreEqual(memory, initMem)) None else Some(memory.clone), result))
	result
    }
    /*val key = (memory, e)
    val resultOpt = equivalences.get(key)
    if (resultOpt != null)
      resultOpt
    else {
      val newResult = super.eval(memory, e)
      equivalences.put(key, newResult)
      newResult
    }*/
  }

}
