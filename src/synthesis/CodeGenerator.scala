package graphprog.synthesis

import graphprog.lang.AST._
import graphprog.lang.{ Executor, Printer, Typer }
import scala.collection.immutable.{ Map => IMap }

protected[synthesis] class CodeGenerator(private val functions: IMap[String, Program], private val shortPrinter: Printer, private val defaultExecutor: Executor, private val typer: Typer) {

  import graphprog.Utils._
  import graphprog.lang.ASTUtils._
  import scala.annotation.tailrec
  import scala.collection.mutable.{ HashMap => MHashMap, Map => MMap, ListBuffer }
  import CodeGenerator._
  import SynthesisUtils._

  // TODO-cleanup: Ugly.
  private def genAllExprs(evidence: Iterable[(Action, Memory)], maxDepth: Int, checker: Option[(Expr, Action, Memory) => Boolean] = None): Iterable[Expr] = {
    if (evidence.head._1.isInstanceOf[LiteralExpr]) {  // TODO: This should probably be in fillHoles once I have it recursing on itself for +,<,etc.
      assert(holdsOverIterable(evidence, (x: (Action, Memory), y: (Action, Memory)) => x._1 == y._1))
      return List(evidence.head._1.asInstanceOf[LiteralExpr].e)
    }
    val targetType = typer.typeOfAction(evidence.head._1, evidence.head._2)
    val memory = evidence.head._2  // We only use this to get the type of a variable, so we don't care which memory we get, as all should have the same type.
    val vars = memory.keys map { s => Var(s) }
    def genAllExprsRec(depth: Int): List[Expr] = {
      def pairs[T1, T2](l1: List[T1], l2: List[T2]): List[(T1, T2)] = for (e1 <- l1; e2 <- l2) yield (e1, e2)
      def canBeSameType(t1: Type, t2: Type): Boolean = (t1, t2) match {
	case (ObjectType(n1), ObjectType(n2)) => n1 == n2 || n1 == "null" || n2 == "null"  // I somtimes call this with t2 == targetType, which would be null when I want something non-null, so if either is null, accept it
	case (_, _) => t1 == t2
      }
      def exprHasType(e: Expr, t: Type): Boolean = canBeSameType(typer.typeOfExpr(e, memory), t)
      if (depth > maxDepth)
	return Nil
      val constants = (targetType, depth) match {
	case (BooleanType, 0) => List(BooleanConstant(true), BooleanConstant(false))
	case (IntType, 0) => List(IntConstant(0), IntConstant(1), IntConstant(2))
	case (_: ObjectType, 0) => List(Null)
	case (_, _) => List(IntConstant(1), IntConstant(2), BooleanConstant(true), BooleanConstant(false), Null)
      }
      val curVariables = if (depth == 0) vars filter { v => exprHasType(v, targetType) } else vars
      val nextLevel = genAllExprsRec(depth + 1)
      val binaryOps = pairs(nextLevel, nextLevel) flatMap { t => t match {
	// Reduce the number of possibilities by ignoring duplicates, unnecessary ops, etc.
	case (e, IntConstant(1)) if !e.isInstanceOf[IntConstant] && typer.typeOfExpr(e, memory) == IntType && (targetType == IntType || depth > 0) => List(Plus(e, IntConstant(1)), Minus(e, IntConstant(1)))
	case (IntConstant(n1), IntConstant(n2)) if n1 == n2 => Nil
	case (Var(n1), Var(n2)) if n1 == n2 && typer.typeOfValue(memory(n1)) == IntType && typer.typeOfValue(memory(n2)) == IntType && (targetType == IntType || depth > 0) => List(Times(t._1, t._2))
	case (IntConstant(_), _) => Nil  // Prefer the other direction
	case (e1, e2) if  (targetType == IntType || depth > 0) && typer.typeOfExpr(e1, memory) == IntType && typer.typeOfExpr(e2, memory) == IntType => (if (e2.isInstanceOf[IntConstant] || shortPrinter.stringOfExpr(e1) < shortPrinter.stringOfExpr(e2)) List(Plus(t._1, t._2)) else Nil) ++ (if (e2.isInstanceOf[IntConstant] || shortPrinter.stringOfExpr(e1) <= shortPrinter.stringOfExpr(e2)) List(Times(t._1, t._2)) else Nil) ++ (if (e1 != e2) List(Minus(t._1, t._2)) else Nil) ++ (if (e1 != e2 && evidence.forall{ case (_, memory) => defaultExecutor.evaluate(memory, Div(t._1, t._2)) != ErrorConstant }) List(Div(t._1, t._2)) else Nil)
	case (e1, e2) if targetType == BooleanType && typer.typeOfExpr(e1, memory) == IntType && typer.typeOfExpr(e2, memory) == IntType && shortPrinter.stringOfExpr(e1) < shortPrinter.stringOfExpr(e2) => List(EQ(t._1, t._2), NE(t._1, t._2), LT(t._1, t._2), LE(t._1, t._2), GT(t._1, t._2), GE(t._1, t._2))
	case (e1, e2) if targetType == BooleanType && typer.typeOfExpr(e1, memory) == BooleanType && typer.typeOfExpr(e2, memory) == BooleanType && !e1.isInstanceOf[BooleanConstant] && !e2.isInstanceOf[BooleanConstant] && shortPrinter.stringOfExpr(e1) < shortPrinter.stringOfExpr(e2) => List(And(t._1, t._2), Or(t._1, t._2))
	case (e1, e2) if (targetType == IntType || depth > 0) && typer.typeOfExpr(e1, memory).isInstanceOf[ArrayType] && typer.typeOfExpr(e2, memory) == IntType => if (evidence forall { case (_, memory) => val r = defaultExecutor.evaluateInt(memory, e2); r >= 0 && r < defaultExecutor.evaluate(memory, e1).asInstanceOf[IntArray].array.length }) List(IntArrayAccess(e1, e2)) else Nil
	case (e1, e2) if targetType == BooleanType && typer.typeOfExpr(e1, memory).isInstanceOf[ObjectType] && typer.typeOfExpr(e2, memory).isInstanceOf[ObjectType] && canBeSameType(typer.typeOfExpr(e1, memory), typer.typeOfExpr(e2, memory)) && shortPrinter.stringOfExpr(e1) < shortPrinter.stringOfExpr(e2) => List(EQ(e1, e2), NE(e1, e2))
	case (e1, e2) if targetType == BooleanType && typer.typeOfExpr(e1, memory) == StringType && typer.typeOfExpr(e2, memory) == StringType && shortPrinter.stringOfExpr(e1) <= shortPrinter.stringOfExpr(e2) => List(EQ(e1, e2), NE(e1, e2))
	case _ => Nil
      }}
      val curParts = if (depth == maxDepth) vars else nextLevel
      val calls = functions.values filter { x => depth > 0 || canBeSameType(x.typ, targetType) } flatMap { p => {
	val actualsPossibilities = p.inputs map { t => curParts filter { e => exprHasType(e, t._2) } }
	val allArgs = actualsPossibilities.foldLeft(List[List[Expr]](Nil)){ (acc, cur) => for (a <- acc; c <- cur) yield a :+ c }
	allArgs map { Call(p.name, _) }
      }}
      val extras = (curParts flatMap { e => defaultExecutor.evaluate(memory, e) match {
	case IntArray(_, a) if (depth > 0 || targetType == IntType) && !e.isInstanceOf[Range] => List(ArrayLength(e)) ++ (if (depth < maxDepth) List(IntArrayAccess(e, IntConstant(0))) else Nil)
	case Object(_, _, f) => f filter { f => depth > 0 || canBeSameType(typer.typeOfValue(f._2), targetType) } map { s => FieldAccess(e, s._1) }
	case BooleanConstant(b) if targetType == BooleanType && depth < maxDepth && !e.isInstanceOf[BooleanConstant] => List(Not(e))  // Ensure that negating uses a depth.
	case _ => Nil
      }})
      val possibilities = (constants ++ curVariables ++ binaryOps ++ calls ++ extras) filter { e => evidence forall { case (_, memory) => val v = defaultExecutor.evaluate(memory, e); !isErrorOrFailure(v) } }
      if (depth == 0) possibilities filter hasCorrectForm(evidence.map{ _._1 }) else possibilities
    }
    // TODO/FIXME: Improve this.  Also, I could do this check before generating the possibilities and use it to guide them (e.g. I don't need a search if they give me osmething unambiguous like a[i] < x+y, and if they give me a[5] I only need to fill the 5 hole, not the a[] part).
    def hasCorrectForm(evidence: Iterable[Action])(e: Expr): Boolean = {
      def hasCorrectForm(evidence: Expr, e: Expr): Boolean = (evidence, e) match {
	//case (Null, e) => e == Null  // TODO: Do I really want this?
	case (_: Value, _) | (_: ObjectID, _) | (_: ArrayID, _) => true
	case (Var(n1), Var(n2)) => n1 == n2
	case (IntArrayAccess(a1, e1), IntArrayAccess(a2, e2)) => hasCorrectForm(a1, a2) && hasCorrectForm(e1, e2)
	case (FieldAccess(o1, f1), FieldAccess(o2, f2)) => f1 == f2 && hasCorrectForm(o1, o2)
	case (ArrayLength(a1), ArrayLength(a2)) => hasCorrectForm(a1, a2)
	case (Call(n1, a1), Call(n2, a2)) => n1 == n2 && a1.size == a2.size && a1.zip(a2).forall{ as => hasCorrectForm(as._1, as._2) }
	case (In(n1, r1), In(n2, r2)) => hasCorrectForm(n1, n2) && hasCorrectForm(r1, r2)
	case (To(min1, max1), To(min2, max2)) => hasCorrectForm(min1, min2) && hasCorrectForm(max1, max2)
	case (Until(min1, max1), Until(min2, max2)) => hasCorrectForm(min1, min2) && hasCorrectForm(max1, max2)
	case (b1: BinaryOp, b2: BinaryOp) => hasCorrectForm(b1.lhs, b2.lhs) && hasCorrectForm(b1.rhs, b2.rhs)
	case (Not(c1), Not(c2)) => hasCorrectForm(c1, c2)
	case _ => false
      }
      evidence.forall{ evidence => hasCorrectForm(evidence.asInstanceOf[Expr], e) }
    }
    val exprs = genAllExprsRec(0)
    if (checker.isEmpty)
      getValidChoices(exprs, evidence)
    else
      exprs filter { e => evidence forall { case (a, m) => checker.get(e, a, m) } }
  }

  /* Returns all of the given exprs that meet all the evidence.
   * Caches the executed results of the evidence to avoid recomputing it.
   * TODO-optimization: store evidence result and memory in the EvidenceHole itself.
   */ 
  private def getValidChoices(exprs: Iterable[Expr], evidence: Iterable[(Action, Memory)]): Iterable[Expr] = {
    val fullEvidence = evidence map { case (action, memory) => val (result, memAfter) = defaultExecutor.execute(memory, action); (memory, result, memAfter) }
    val goodExprs = exprs filter { e => fullEvidence forall { case (memBefore, result, memAfter) => try { yieldEquivalentResults(memBefore, e, result, memAfter, defaultExecutor) } catch { case _ => false } }}
    if (evidence.size > 0 && evidence.forall{ _._1.isInstanceOf[Call] } && holdsOverIterable(evidence, (x: (Action, Memory), y: (Action, Memory)) => (x._1, y._1) match { case (Call(n1, _), Call(n2, _)) => n1 == n2 case _ => throw new RuntimeException })) {  // TODO: This shouldn't be needed once I add expression holes.
      val functionName = evidence.head._1.asInstanceOf[Call].name
      goodExprs filter { _ match { case Call(n1, _) => n1 == functionName case _ => false }}
    } else
      goodExprs
  }

  private def genExpr(evidence: Iterable[(Action, Memory)], maxDepth: Int): Iterable[Expr] = {
    def binaryOpHelper(constructor: (Expr, Expr) => Expr, isCommutative: Boolean): Iterable[Expr] = {
      val x = evidence collect { case (b: BinaryOp, m) => ((b.lhs, m), (b.rhs, m)) } unzip
      val leftExprs = genExpr(x._1, maxDepth)
      val rightExprs = genExpr(x._2, maxDepth)
      val choices = for (l <- leftExprs; r <- rightExprs if l != r) yield constructor(l, r)
      val unaryEvidence = evidence filter { _._1.isInstanceOf[BooleanConstant] }
      val finalChoices = getValidChoices(choices, unaryEvidence)
      if (!isCommutative)
	finalChoices
      else  // Keep only one of (a, b) and (b, a)
	finalChoices.foldLeft((Set[Expr](), Set[Expr]())){ case ((choices, reversed), cur) => (cur: @unchecked) match { case c: Comparison => if (choices.contains(c) || reversed.contains(c)) (choices, reversed) else (choices + c, reversed + constructor(c.rhs, c.lhs)) } }._1.toList
    }
    evidence.collectFirst{ case (c: Comparison, _) => c } match {
      case Some(EQ(_, _)) => binaryOpHelper(EQ(_, _), true)
      case Some(NE(_, _)) => binaryOpHelper(NE(_, _), true)
      case Some(LT(_, _)) => binaryOpHelper(LT(_, _), false)
      case Some(LE(_, _)) => binaryOpHelper(LE(_, _), false)
      case Some(GT(_, _)) => binaryOpHelper(GT(_, _), false)
      case Some(GE(_, _)) => binaryOpHelper(GE(_, _), false)
      case Some(And(_, _)) => binaryOpHelper(And(_, _), true)
      case Some(Or(_, _)) => binaryOpHelper(Or(_, _), true)
      case None => genAllExprs(evidence, maxDepth)
    }
  }
  private def holeFiller[T <: Stmt](stmt: Stmt, evidence: Iterable[(Action, Memory)], depth: Int, generator: (Iterable[(Action, Memory)], Int) => Iterable[T]): T = {
    var possibilities = generator(evidence, depth)
    possibilitiesToExpr(possibilities, {
      if (depth < MAX_EXPR_DEPTH)
	holeFiller(stmt, evidence, depth + 1, generator)
      else
	throw new SolverError("Could not fill hole " + shortPrinter.stringOfStmt(stmt) + " at depth " + depth) with FastException
    })
  }
  protected[synthesis] def fillExprHole(expr: Expr, depth: Int = INITIAL_EXPR_DEPTH): Expr = expr match {
    case ExprEvidenceHole(evidence) => holeFiller(expr, evidence, depth, genExpr)
    case _ => expr
  }
  protected[synthesis] def fillHoles(stmts: List[Stmt], isPartialTrace: Boolean, depth: Int = INITIAL_EXPR_DEPTH): List[Stmt] = {
    def genStmt(evidence: Iterable[(Action, Memory)], maxDepth: Int): Iterable[Stmt] = evidence.head._1 match {
      case _: Expr => genExpr(evidence, maxDepth)
      case Assign(l, _) =>
	val assignEvidence = evidence map { case (a: Assign, m) => (a, m) case s => throw new RuntimeException("Unexpected stmt: " + s) }
	if (holdsOverIterable(assignEvidence map { case (Assign(l, _), _) => l }, ((x: LVal, y: LVal) => x == y)) && (l match { case FieldAccess(ObjectID(_), _) | IntArrayAccess(ArrayID(_), _) => false case _ => true })) {  // TODO: I should really check l thoroughly, not just at the first level like this.
	  val exprEvidence = assignEvidence map { case (Assign(_, r), m) => (r, m) }
	  val allExprs = genExpr(exprEvidence, maxDepth) filter { _ != l }
	  allExprs map { Assign(l, _) }
	} else {
	  assert(holdsOverIterable(assignEvidence map { _._1 }, (x: Action, y: Action) => (x, y) match { case (FieldAccess(_, f1), FieldAccess(_, f2)) => f1 == f2 case _ => true }))
	  val leftEvidence = assignEvidence map { case (Assign(FieldAccess(l, _), _), m) => (l, m) case (Assign(l, _), m) => (l, m) }
	  val leftExprs = genExpr(leftEvidence, maxDepth) collect { case l: LVal => l }
	  val rightEvidence = assignEvidence map { case (Assign(_, r), m) => (r, m) }
	  val rightExprs = genExpr(rightEvidence, maxDepth)
	  val field = assignEvidence.head._1 match { case Assign(FieldAccess(_, f), _) => Some(f) case _ => None }
	  for (l <- leftExprs; r <- rightExprs if l != r) yield field match { case Some(f) => Assign(FieldAccess(l, f), r) case None => Assign(l, r) }
	}
    }
    def genLoopCondition(evidence: Iterable[(Action, Memory)], depth: Int): Iterable[Stmt] = {
      def handleForLoop(v: Var, evidence: Iterable[(Action, Memory)]): Iterable[Stmt] = {
	val name = v.name
	val assigns = evidence flatMap { case (Assign(_, r), m) => List((r, m)) case (i @ In(Var(n), r), m) => val res = defaultExecutor.execute(m, i); if (res._1.isInstanceOf[BooleanConstant]) Nil else if (m.contains(n)) List((IntConstant(m(n).asInstanceOf[IntConstant].n + 1), m)) else if (res._2 contains name) List((r.min, m)) else Nil case (Break, _) => Nil }
	val exprs = {
	  def minChecker(e: Expr, a: Action, m: Memory): Boolean = defaultExecutor.evaluateBoolean(m, if (m contains name) LT(e, a.asInstanceOf[Expr]) else EQ(e, a.asInstanceOf[Expr]))
	  val mins = genAllExprs(assigns, depth, Some(minChecker))
	  def maxChecker(isInclusive: Boolean)(e: Expr, a: Action, m: Memory): Boolean = defaultExecutor.evaluateBoolean(m, if (isInclusive) GE(e, a.asInstanceOf[Expr]) else GT(e, a.asInstanceOf[Expr]))
	  val inMaxs = genAllExprs(assigns, depth, Some(maxChecker(true)))
	  val exMaxs = genAllExprs(assigns, depth, Some(maxChecker(false)))
	  (for (min <- mins; max <- inMaxs) yield To(min, max)) ++ (for (min <- mins; max <- exMaxs) yield Until(min, max))
	}
	val iterationCheckMemories = {
	  def getMemories(evidence: Iterable[(Action, Memory)]): List[(Memory, Option[Int])] = {
	    @tailrec def finishIteration(evidence: Iterable[(Action, Memory)], numIterations: Int): (Option[Int], Iterable[(Action, Memory)]) = evidence match {
	      case Nil => (None, Nil)
	      case (Break, m) :: rest => (Some(numIterations), rest)
	      case (_, m) :: rest => 
		if (m contains name)
		  finishIteration(rest, numIterations + 1)
		else
		  (None, evidence)
	    }
	    def callGetMemories(m: Memory, rest: Iterable[(Action, Memory)]): List[(Memory, Option[Int])] = {
	      assert(!m.contains(name))
	      val (right, newRest) = finishIteration(rest, 1)
	      (m, right) :: getMemories(newRest)
	    }
	    evidence match {
	      case Nil => Nil
	      case(Assign(_, _), m) :: rest => callGetMemories(m, rest)
	      case(In(_, _), m) :: rest => callGetMemories(m, rest)
	    }
	  }
	  getMemories(evidence)
	}
	def numIterations(r: Range): Int = iterationCheckMemories.map { 
	  case (m, None) => defaultExecutor.evaluateInt(m, ArrayLength(r))
	  case (_, Some(size)) => size
	}.sum
	val finalExprs = if (isPartialTrace) exprs else exprs filter { case r: Range => try { numIterations(r) == assigns.size } catch { case _ => false } }  // If isPartialTrace is true, we might see only the first iteration of a loop with more than one iteration, so we cannot check that we have the right number of iterations.
	finalExprs map { In(v, _) }
      }
      (evidence.head._1: @unchecked) match {
	case Assign(v: Var, _) => handleForLoop(v, evidence)
	case In(v: Var, _) => handleForLoop(v, evidence)
	case _: Expr => genExpr(evidence, depth)
      }
    }
    def fillStmtHole(stmt: Stmt, depth: Int, isLoopCondition: Boolean): Stmt = stmt match {
      case e: Expr => fillExprHole(e, depth)
      case StmtEvidenceHole(evidence) => holeFiller(stmt, evidence, depth, if (isLoopCondition) genLoopCondition else genStmt)
      case If(c, t, ei, e) => If(fillExprHole(c, depth), fillHoles(t, isPartialTrace, depth), ei map { b => (b._1, fillHoles(b._2, isPartialTrace, depth)) }, fillHoles(e, isPartialTrace, depth))
      case Loop(condition, body) => Loop(fillStmtHole(condition, depth, true), fillHoles(body, isPartialTrace, depth))
      case UnorderedStmts(s) => UnorderedStmts(fillHoles(s, isPartialTrace, depth))
      case _ => stmt
    }
    stmts map { s => fillStmtHole(s, depth, false) }
  }

}

object CodeGenerator {

  // Initial depth to check expressions.
  private val INITIAL_EXPR_DEPTH = 1

  // Maximum depth to check expressions.
  private val MAX_EXPR_DEPTH = 2

}
