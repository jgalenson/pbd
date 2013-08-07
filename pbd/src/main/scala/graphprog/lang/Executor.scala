package graphprog.lang

import AST._
import ASTUtils._
import graphprog.Utils._
import scala.annotation.tailrec

class Executor(private val functions: Map[String, Program], private val printer: Printer, private val holeHandler: (Memory, Hole) => Stmt = Executor.errorOnHole, private val shouldPrint: Boolean = false) extends Serializable {

  import Executor.ExecuteError
  import scala.collection.immutable.Map
  import scala.collection.mutable.{ Set => MSet }

  protected def exec(memory: Memory, s: Stmt): Value = {
    //println("Executing " + printer.stringOfStmt(s) + " with memory " + printer.stringOfMemory(memory))
    s match {
      case h: Hole => exec(memory, holeHandler(memory, h))
      case l: TLiteral[_] => exec(memory, l.l)
      case e: Expr => eval(memory, e)
      case Assign(l, r) =>
        val v = eval(memory, r)
	if (v == ErrorConstant)
	  return v
	//println("Updating memory: " + printer.stringOfExpr(l) + " -> " + v)
	l match {
          case Var(n) => memory += (n -> v)
          case ArrayAccess(a, iExpr) =>
	    val arrayObj = eval(memory, a)
	    if (!arrayObj.isInstanceOf[ArrayValue])
	      return ErrorConstant
	    val array = arrayObj.asInstanceOf[ArrayValue].array
	    val i = evalInt(memory, iExpr)
	    if (i < 0 || i >= array.length)
	      return ErrorConstant
	    array(i) = v
	  case FieldAccess(o, field) =>
	    val obj = eval(memory, o)
	    if (!obj.isInstanceOf[Object])
	      return ErrorConstant
	    val fields = obj.asInstanceOf[Object].fields
	    if (!fields.contains(field))
	      throw new ExecuteError(s, "Object " + printer.stringOfExpr(o) + " with value " + printer.stringOfValue(eval(memory, o)) + " does not contain field " + field + " but has only " + fields)
	    fields += (field -> v)
        }
	v
      case If(condition, thenBranch, elseIfPaths, elseBranch) => 
	def executeBody(body: List[Stmt]): Value = {
	  memory.enterScope()
	  val result = execStmts(memory, body)
	  memory.exitScope()
	  result
	}
	val elseCondition = Not((condition :: (elseIfPaths map { _._1 })) reduceLeft { (acc, cur) => Or(acc, cur) })
	val allPaths = ((condition, thenBranch) :: elseIfPaths) :+ ((elseCondition, elseBranch))
	val curPaths = allPaths dropWhile { path => !path._1.isInstanceOf[Hole] && !evalBoolean(memory, path._1) }
	val path = curPaths.head
	if (path._1.isInstanceOf[Hole]) {
	  def holeHelper(curPaths: List[(Expr, List[Stmt])]): Value = curPaths match {
	    case Nil => execStmts(memory, elseBranch)
	    case path :: rest =>
	      val c = exec(memory, holeHandler(memory, path._1.asInstanceOf[Hole]))
	      if (isErrorOrFailure(c))
		return c
	      val cBool = c.asInstanceOf[BooleanConstant].b
	      if (cBool)
		executeBody(path._2)
	      else
		holeHelper(rest dropWhile { path => !path._1.isInstanceOf[Hole] && !evalBoolean(memory, path._1) })
	  }
	  holeHelper(curPaths dropRight 1)  // Ignore else since we don't need to evaluate its condition
	} else
	  executeBody(path._2)
      case Assume(condition) =>
        if (evalBoolean(memory, condition)) UnitConstant else AssumeFailed
      case Assert(condition) =>
        if (evalBoolean(memory, condition)) UnitConstant else AssertFailed
      case Conditional(condition, body) => 
	memory.enterScope()
	val result = execStmts(memory, body)  // A Conditional shows the original condition, even if it is false on this trace, so just execute.
	memory.exitScope()
	result
      case l @ Loop(condition, body) =>
	memory.enterScope()
	val result = doLoop(memory, l)
	memory.exitScope()
	result
      case Iterate(iterations) => 
	@tailrec def runIterate(iterations: List[(Action, List[Action])]): Value = iterations match {
	  case Nil => UnitConstant
	  case (condition, body) :: rest =>
	    val result = exec(memory, condition)
            if (isErrorOrFailure(result))
	      return result
	    else if (result.isInstanceOf[BooleanConstant] && !result.asInstanceOf[BooleanConstant].b && !body.isEmpty)
	      return ErrorConstant
	    else {
	      val v = execStmts(memory, body)
	      if (isErrorOrFailure(v))
		v
	      else if (v == BreakHit)
		UnitConstant
	      else
		runIterate(rest)
	    }
	}
	memory.enterScope()
	val result = runIterate(iterations)
	memory.exitScope()
	result
      case Break => BreakHit
      case Println(s) => 
	if (shouldPrint)
	  println(s.s)
	UnitConstant
      case UnorderedStmts(stmts) =>
	val newMemories = stmts map { a => val (v, m) = execute(memory, a); if (v == BreakHit) return ErrorConstant else if (isErrorOrFailure(v)) return v else m }
	val modifications = newMemories map { newMemory => diffMemories(memory, newMemory) }  // TODO-optimization: I'm recomputing memory.getObjectsAndArrays().toSet here
	// Combine results and ensure that there are not multiple writes to the same location.
	val (modVars, modFields, modArrays) = modifications.foldLeft((Map[String, Value](), Map[(Int, String), Value](), Map[(Int, Int), Value]())) { case ((accVars, accFields, accModArrs), (curVars, curFields, curModArrs)) => {
	  if (!accVars.keys.toSet.intersect(curVars.keys.toSet).isEmpty || !accFields.keys.toSet.intersect(curFields.keys.toSet).isEmpty || !accModArrs.keys.toSet.intersect(curModArrs.keys.toSet).isEmpty)
	    return ErrorConstant
	  (accVars ++ curVars, accFields ++ curFields, accModArrs ++ curModArrs)
	}}
	val (objects, arrays) = memory.getObjectsAndArrays()
	// Update memory with the result of the unordered statements.
	def getRealValue(v: Value) = v match {
	  case Object(id, _, _) => objects(id)
	  case ArrayValue(id, _, _) => arrays(id)
	  case _ => v
	}
	modFields foreach { case ((id, field), value) => objects(id).fields += (field -> getRealValue(value)) }
	modArrays foreach { case ((id, index), value) => arrays(id).array(index) = value }
	modVars foreach { t => memory += (t._1 -> getRealValue(t._2)) }
	UnitConstant
      case Snapshot(snapshotMemory) =>
	import scala.collection.mutable.{ Map => MMap }
	def cloneMap[T1, T2](m1: MMap[T1, T2], m2: MMap[T1, T2]) {
	  m1.clear()
	  m1 ++= m2
	}
	val oldMemory = memory.mem.clone
	memory.mem.clear
	oldMemory.reverse.foreach{ m => memory.mem.push(MMap[String, Value]() ++ (m.map{ kv => (kv._1, snapshotMemory(kv._1)) })) }
	snapshotMemory.keys.filter{ k => !memory.contains(k) }.foreach{ k => memory += (k -> snapshotMemory(k)) }  // Add in new variables from the snapshot.
	UnitConstant
      case UnknownJoinIf(_, _) => throw new ExecuteError(s, "Cannot execute: " + s)
    }
  }
  protected def doLoop(memory: Memory, l: Loop): Value = {
    @tailrec def runLoop(): Value = {
      val result = exec(memory, l.condition)
      if (isErrorOrFailure(result))
	result
      else if (result.isInstanceOf[IntConstant] || result.asInstanceOf[BooleanConstant].b) {
	val v = doLoopBody(memory, l)
	if (isErrorOrFailure(v))
	  v
	else if (v == BreakHit)
	  UnitConstant
	else
	  runLoop()
      } else
	UnitConstant
    }
    runLoop()
  }
  protected def doLoopBody(memory: Memory, l: Loop): Value = execStmts(memory, l.body)
  protected def eval(memory: Memory, e: Expr): Value = {
    //println("Evaluating " + printer.stringOfExpr(e) + " with memory " + printer.stringOfMemory(memory))
    def handleIntComparison(l: Expr, r: Expr, op: (Int, Int) => Boolean): Value = {
      val lhs = eval(memory, l)
      val rhs = eval(memory, r)
      if (!lhs.isInstanceOf[IntConstant])
        throw new ExecuteError(e, "Operand " + printer.stringOfExpr(l) + " is not int but is " + printer.stringOfExpr(lhs))
      if (!rhs.isInstanceOf[IntConstant])
        throw new ExecuteError(e, "Operand " + printer.stringOfExpr(r) + " is not int but is " + printer.stringOfExpr(rhs))
      BooleanConstant(op(lhs.asInstanceOf[IntConstant].n, rhs.asInstanceOf[IntConstant].n))
    }
    def handleIntArithmetic(l: Expr, r: Expr, op: (Int, Int) => Int): Value = {
      val lhs = eval(memory, l)
      val rhs = eval(memory, r)
      if (!lhs.isInstanceOf[IntConstant])
        throw new ExecuteError(e, "Operand " + printer.stringOfExpr(l) + " is not int but is " + printer.stringOfExpr(lhs))
      if (!rhs.isInstanceOf[IntConstant])
        throw new ExecuteError(e, "Operand " + printer.stringOfExpr(r) + " is not int but is " + printer.stringOfExpr(rhs))
      IntConstant(op(lhs.asInstanceOf[IntConstant].n, rhs.asInstanceOf[IntConstant].n))
    }
    def handleCheckingEquality(l: Expr, r: Expr, op: Boolean => Boolean): BooleanConstant = (eval(memory, l), eval(memory, r)) match {
      case (x, y) if isErrorOrFailure(x) || isErrorOrFailure(y) => throw new ExecuteError(e, "Trying to check equality or disequality of " + printer.stringOfExpr(l) + " (" + printer.stringOfExpr(x) + ") and " + printer.stringOfExpr(r) + " (" + printer.stringOfExpr(y) + ") and at least one is an error or a failure.")
      case (x, y) => BooleanConstant(op(areEqual(x, y, false, false)))
    }
    def handleEquality(l: Expr, r: Expr): Value = handleCheckingEquality(l, r, b => b)
    def handleDisequality(l: Expr, r: Expr): Value = handleCheckingEquality(l, r, b => !b)
    e match {
      case h: Hole => exec(memory, holeHandler(memory, h))
      case l: TLiteralExpr[_] => eval(memory, l.l)
      case v: Value => getValueFromMemory(v, memory)  // Use the value from the current memory, as this one could be from an old memory.
      case Var(n) =>
        if (!memory.contains(n))
          throw new ExecuteError(e, "Variable does not exist.")
	memory(n)
      case ArrayAccess(a, iExpr) =>
	val arrayObj = eval(memory, a)
	if (!arrayObj.isInstanceOf[ArrayValue])
	  return ErrorConstant
        val array = arrayObj.asInstanceOf[ArrayValue].array
	val i = evalInt(memory, iExpr)
	if (i < 0 || i >= array.length)
	  ErrorConstant
	else
          array(i)
      case FieldAccess(obj, field) =>
	val o = eval(memory, obj)
	if (!o.isInstanceOf[Object])
	  ErrorConstant
        else {
	  val fields = o.asInstanceOf[Object].fields
          if (fields contains field)
	    fields(field)
          else
	    throw new ExecuteError(e, "Object " + printer.stringOfExpr(obj) + " with value " + printer.stringOfValue(eval(memory, obj)) + " does not contain field " + field + " but has only " + fields)
	}
      case ArrayLength(e) =>
	val a = eval(memory, e)
	if (!a.isInstanceOf[ArrayValue])
	  ErrorConstant
	else
	  IntConstant(a.asInstanceOf[ArrayValue].array.length)
      case ObjectID(id) =>
	val oOpt = memory.getObject(id)
	if (oOpt.isEmpty)
	  throw new ExecuteError(e, "There is no object with id " + id.toString + ".")
	oOpt.get
      case ArrayID(id) =>
	val aOpt = memory.getArray(id)
	if (aOpt.isEmpty)
	  throw new ExecuteError(e, "There is no array with id " + id.toString + ".")
	aOpt.get
      case Call(name, args) => 
	val target = functions(name)
	val actuals = (target.inputs map { _._1 }) zip (args map { e => eval(memory, e) })
	executeProgram(target, actuals, false)._1
      case In(v, range) =>
	val name = v.name
	if (evalBoolean(memory, LT(if (range.isInclusive) range.max else Minus(range.max, IntConstant(1)), range.min)))
	  BooleanConstant(false)
	else if (!memory.contains(name))
	  exec(memory, Assign(v, range.min))
	else if (evalBoolean(memory, EQ(v, if (range.isInclusive) range.max else Minus(range.max, IntConstant(1)))))
	  BooleanConstant(false)
	else
	  exec(memory, Assign(v, Plus(v, IntConstant(1))))
      case r: Range =>
	val min = evalInt(memory, r.min)
	val max = evalInt(memory, r.max)
	val range = if (r.isInclusive) min to max else min until max
	ArrayValue(Int.MinValue, range.toArray.map{ n => IntConstant(n) }, IntType)  // TODO-bug: min value might be used
      case EQ(l, r) => handleEquality(l, r)
      case NE(l, r) => handleDisequality(l, r)
      case LT(l, r) => handleIntComparison(l, r, _ < _)
      case LE(l, r) => handleIntComparison(l, r, _ <= _)
      case GT(l, r) => handleIntComparison(l, r, _ > _)
      case GE(l, r) => handleIntComparison(l, r, _ >= _)
      case And(l, r) => BooleanConstant(evalBoolean(memory, l) && evalBoolean(memory, r))
      case Or(l, r) => BooleanConstant(evalBoolean(memory, l) || evalBoolean(memory, r))
      case Not(e) => eval(memory, e) match { case BooleanConstant(b) => BooleanConstant(!b) }
      case Plus(l, r) => handleIntArithmetic(l, r, _ + _)
      case Minus(l, r) => handleIntArithmetic(l, r, _ - _)
      case Times(l, r) => handleIntArithmetic(l, r, _ * _)
      case Div(l, r) => 
	val rVal = eval(memory, r)
	if (!rVal.isInstanceOf[IntConstant] || rVal.asInstanceOf[IntConstant].n == 0)
	  ErrorConstant
	else
	  handleIntArithmetic(l, rVal, _ / _)
    }
  }
  private def evalBoolean(memory: Memory, e: Expr): Boolean = eval(memory, e).asInstanceOf[BooleanConstant].b
  private def evalInt(memory: Memory, e: Expr): Int = eval(memory, e).asInstanceOf[IntConstant].n
  protected[graphprog] def execute(memory: Memory, s: Stmt): (Value, Memory) = {
    val clonedMemory = memory.clone
    (exec(clonedMemory, s), clonedMemory)
  }
  protected[graphprog] def evaluate(memory: Memory, s: Stmt): Value = execute(memory, s)._1
  protected[graphprog] def evaluateBoolean(memory: Memory, s: Stmt): Boolean = evaluate(memory, s).asInstanceOf[BooleanConstant].b
  protected[graphprog] def evaluateInt(memory: Memory, e: Expr): Int = evaluate(memory, e).asInstanceOf[IntConstant].n

  /* Execute a list of statements and return the result and final memory. */
  protected def execStmts(memory: Memory, stmts: List[Stmt]): Value = {
    if (java.lang.Thread.interrupted())
      throw new InterruptedException
    stmts.foldLeft(UnitConstant: Value) { (prev, s) => if (isErrorOrFailure(prev) || prev == BreakHit) prev else exec(memory, s) }
  }
  protected[graphprog] def executeStmts(memory: Memory, stmts: List[Stmt]): (Value, Memory) = {
    val clonedMemory = memory.clone
    (execStmts(clonedMemory, stmts), clonedMemory)
  }
  protected[graphprog] def evaluateStmts(memory: Memory, stmts: List[Stmt]): Value = executeStmts(memory, stmts)._1

  protected[graphprog] def executeProgram(program: Program, inputs: List[(String, Value)], cloneMemory: Boolean): (Value, Memory) = {
    val inputMem = new Memory(inputs)
    val mem = if (cloneMemory) inputMem.clone else inputMem
    (if (program.functions.eq(functions) || (program.functions.isEmpty && functions.size == 1 && functions.head._2.eq(program)))
      execStmts(mem, program.stmts)
    else {  // TODO-optimization: Could try to avoid the extra allocations here, perhaps by always using transitive closure of functions.
      assert(functions contains program.name)
      val newFunctions = program.functions + (program.name -> functions(program.name))
      (new Executor(newFunctions, printer, holeHandler, shouldPrint)).execStmts(mem, program.stmts)
    }, mem)
  }

}


import scala.collection.mutable.Stack

class IteratorExecutor private (private var iterator: Stack[Stmt], private val functions: Map[String, Program], private val printer: Printer, private val holeHandler: (Memory, Hole) => Stmt) extends Executor(functions, printer, holeHandler) {

  def this(functions: Map[String, Program], printer: Printer, holeHandler: (Memory, Hole) => Stmt = Executor.errorOnHole) = this(Stack.empty[Stmt], functions, printer, holeHandler)

  def hasNext: Boolean = iterator.nonEmpty

  def getNext: Stmt = iterator.top

  def getNextOpt: Option[Stmt] = if (hasNext) Some(iterator.top) else None

  def executeNext(memory: Memory): Value = exec(memory, iterator.pop)

  def skipNext() = iterator.pop

  override def clone: IteratorExecutor = new IteratorExecutor(iterator.clone, functions, printer, holeHandler)

  override def doLoop(memory: Memory, l: Loop): Value = {
    val result = exec(memory, l.condition)
    if (isErrorOrFailure(result))
      result
    else if (result.isInstanceOf[IntConstant] || result.asInstanceOf[BooleanConstant].b) {
      iterator pushAll (l :: l.body.reverse)  // TODO/FIXME: This doesn't work with breaks or errors.
      UnitConstant
    } else
      UnitConstant
  }

  override def execStmts(memory: Memory, stmts: List[Stmt]): Value = {
    iterator pushAll stmts.reverse
    UnitConstant
  }

  // We need to execute calls "atomically" since otherwise we would pick up the call to execStmts but use our memory, which doesn't haev the parameters.
  override def executeProgram(program: Program, inputs: List[(String, Value)], cloneMemory: Boolean): (Value, Memory) = (new Executor(functions, printer, holeHandler)).executeProgram(program, inputs, cloneMemory)

}

object Executor {

  private class ExecuteError(s: Stmt, msg: String) extends RuntimeException {
    override def toString: String = "ExecuteError(" + (new Printer(Map[String, Value => String](), false)).stringOfStmt(s) + ", " + msg + ")"
  }

  protected[lang] def errorOnHole(memory: Memory, hole: Hole): Nothing = throw new ExecuteError(hole.asInstanceOf[Stmt], "I'm trying to execute a hole when there shouldn't be a hole.")

  protected[graphprog] def simpleHoleHandler(executor: Executor)(memory: Memory, hole: Hole): Stmt = hole match {
    case PossibilitiesHole(possibilities) => 
      val results = possibilities flatMap { s => try { val (v, m) = executor.execute(memory, s); if (v == ErrorConstant) Nil else List((s, v, m)) } catch { case _: Throwable => Nil } }  // TODO: I shouldn't need the catch here: all errors that can arise should return ErrorConstants in execute.  Same in findFirstNewRandomInput, in findBest*, in fillHoles.genExpr, and in simpleInputPruning.
      if (results.size == 0)
	ErrorConstant
      else if (results.size == possibilities.size && holdsOverIterable(results, (x: (Stmt, Value, Memory), y: (Stmt, Value, Memory)) => areEquivalent(x._2, y._2, x._3, y._3)))
	results.head._1
      else
	ErrorConstant
    case _: Unseen => ErrorConstant
    case _: EvidenceHole => throw new ExecuteError(hole.asInstanceOf[Stmt], "Cannot handle evidence hole")
  }

  protected[graphprog] class InterruptedException extends FastException

}
