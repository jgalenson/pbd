package graphprog.synthesis

import graphprog.lang.AST._
import graphprog.lang.{ Executor, Printer, Typer, CachingExecutor }
import scala.collection.immutable.{ Map => IMap }

protected[synthesis] class CodeGenerator(private val functions: IMap[String, Program], private val shortPrinter: Printer, private val defaultExecutor: Executor, private val typer: Typer) {

  import graphprog.Utils._
  import graphprog.lang.ASTUtils._
  import scala.annotation.tailrec
  import scala.collection.mutable.{ HashMap => MHashMap, Map => MMap, ListBuffer, Set => MSet, HashSet => MHashSet }
  import CodeGenerator._
  import SynthesisUtils._

  // TODO-cleanup: Ugly.
  protected[graphprog] def genAllExprs(evidence: Iterable[(Action, Memory)], maxDepth: Int, checker: Option[(Expr, Action, Memory) => Boolean] = None): Iterable[Expr] = {
    if (evidence.head._1.isInstanceOf[LiteralExpr]) {  // TODO: This should probably be in fillHoles once I have it recursing on itself for +,<,etc.
      assert(holdsOverIterable(evidence, (x: (Action, Memory), y: (Action, Memory)) => x._1 == y._1))
      return List(evidence.head._1.asInstanceOf[LiteralExpr].e)
    }
    val cachingExecutor = new CachingExecutor(functions, shortPrinter)
    def makeCalls(name: String, actualsPossibilities: Iterable[Iterable[Expr]]): Iterable[Call] = {
      val allArgs = actualsPossibilities.foldLeft(List[List[Expr]](Nil)){ (acc, cur) => for (a <- acc; c <- cur) yield a :+ c }
      allArgs map { Call(name, _) }
    }
    def genExprs(): (Iterable[Expr], MMap[Expr, MSet[Expr]]) = {
      def canBeSameType(t1: Type, t2: Type): Boolean = (t1, t2) match {
	case (ObjectType(n1), ObjectType(n2)) => n1 == n2 || n1 == "null" || n2 == "null"  // I somtimes call this with t2 == targetType, which would be null when I want something non-null, so if either is null, accept it
	case (_, _) => t1 == t2
      }
      def exprHasType(e: Expr, t: Type, memory: Memory): Boolean = canBeSameType(typer.typeOfExpr(e, memory), t)
      val equivalences = MHashMap.empty[Memory, MHashMap[Result, ListBuffer[Expr]]]
      def getResult(e: Expr, memory: Memory, result: (Value, Memory)): Result = if (e.isInstanceOf[Call] && result._2 != memory) SideEffect((memory, result._2), result._1) else result._1
      def pairs(l1: Iterable[Expr], l2: Iterable[Expr], memory: Memory): Iterable[(Expr, Expr)] = for (e1 <- l1; e2 <- l2; e2b = if (e1 != e2) e2 else equivalences(memory)(getResult(e2, memory, cachingExecutor.execute(memory, e2))).find{ _ != e1 }.getOrElse{ e2 }; reorder = e1 == e2 && shortPrinter.stringOfExpr(e1) > shortPrinter.stringOfExpr(e2b)) yield if (!reorder) (e1, e2b) else (e2b, e1)
      def getRepresentatives(memory: Memory): Iterable[Expr] = equivalences.getOrElse(memory, MMap.empty).values.map{ _.head }
      def addExpr(memory: Memory, expr: Expr, result: Result) = equivalences.getOrElseUpdate(memory, MHashMap.empty).getOrElseUpdate(result, ListBuffer.empty) += expr
      def genExprsRec(depth: Int) {
	if (depth > maxDepth)
	  return
	evidence.groupBy{ _._2 }.foreach{ case (memory, evidence) => {
	  val targetType = typer.typeOfAction(evidence.head._1, memory)
	  val constants = List(Null)
	  val vars = memory.keys map { s => Var(s) }
	  val curVariables = if (depth == maxDepth) vars filter { v => exprHasType(v, targetType, memory) } else vars
	  val nextLevel = getRepresentatives(memory)
	  //println("Memory: " + memory)
	  //println("Depth " + depth + "/" + maxDepth + " next level: " + iterableToString(nextLevel, ", ", (e: Expr) => shortPrinter.stringOfExpr(e)))
	  val binaryOps = pairs(nextLevel, nextLevel, memory).flatMap{ t => t match {
	    // Reduce the number of possibilities by ignoring duplicates, unnecessary ops, etc.
	    case (Var(n1), Var(n2)) if n1 == n2 && typer.typeOfValue(memory(n1)) == IntType && typer.typeOfValue(memory(n2)) == IntType && (targetType == IntType || depth < maxDepth) => List(Times(t._1, t._2))
	    case (e1, e2) if  (targetType == IntType || depth < maxDepth) && typer.typeOfExpr(e1, memory) == IntType && typer.typeOfExpr(e2, memory) == IntType => (if (shortPrinter.stringOfExpr(e1) < shortPrinter.stringOfExpr(e2)) List(Plus(t._1, t._2)) else Nil) ++ (if (shortPrinter.stringOfExpr(e1) <= shortPrinter.stringOfExpr(e2)) List(Times(t._1, t._2)) else Nil) ++ (if (e1 != e2) List(Minus(t._1, t._2)) else Nil) ++ (if (e1 != e2 && evidence.forall{ case (_, memory) => cachingExecutor.evaluate(memory, Div(t._1, t._2)) != ErrorConstant }) List(Div(t._1, t._2)) else Nil)
	    case (e1, e2) if targetType == BooleanType && typer.typeOfExpr(e1, memory) == IntType && typer.typeOfExpr(e2, memory) == IntType && shortPrinter.stringOfExpr(e1) < shortPrinter.stringOfExpr(e2) => List(EQ(t._1, t._2), NE(t._1, t._2), LT(t._1, t._2), LE(t._1, t._2), GT(t._1, t._2), GE(t._1, t._2))
	    case (e1, e2) if targetType == BooleanType && typer.typeOfExpr(e1, memory) == BooleanType && typer.typeOfExpr(e2, memory) == BooleanType && shortPrinter.stringOfExpr(e1) < shortPrinter.stringOfExpr(e2) => List(And(t._1, t._2), Or(t._1, t._2))
	    case (e1, e2) if (targetType == IntType || depth < maxDepth) && typer.typeOfExpr(e1, memory).isInstanceOf[ArrayType] && typer.typeOfExpr(e2, memory) == IntType => if (evidence forall { case (_, memory) => val r = cachingExecutor.evaluateInt(memory, e2); r >= 0 && r < cachingExecutor.evaluate(memory, e1).asInstanceOf[IntArray].array.length }) List(IntArrayAccess(e1, e2)) else Nil
	    case (e1, e2) if targetType == BooleanType && typer.typeOfExpr(e1, memory).isInstanceOf[ObjectType] && typer.typeOfExpr(e2, memory).isInstanceOf[ObjectType] && canBeSameType(typer.typeOfExpr(e1, memory), typer.typeOfExpr(e2, memory)) && shortPrinter.stringOfExpr(e1) < shortPrinter.stringOfExpr(e2) => List(EQ(e1, e2), NE(e1, e2))
	    case (e1, e2) if targetType == BooleanType && typer.typeOfExpr(e1, memory) == StringType && typer.typeOfExpr(e2, memory) == StringType && shortPrinter.stringOfExpr(e1) <= shortPrinter.stringOfExpr(e2) => List(EQ(e1, e2), NE(e1, e2))
	    case _ => Nil
	  }}
	  val calls = functions.values.filter{ x => depth < maxDepth || canBeSameType(x.typ, targetType) }.flatMap{ p => {
	    val actualsPossibilities = p.inputs map { t => nextLevel filter { e => exprHasType(e, t._2, memory) } }
	    makeCalls(p.name, actualsPossibilities)
	  }}
	  val extras = nextLevel.flatMap{ e => cachingExecutor.evaluate(memory, e) match {
	    case IntConstant(n) if targetType == IntType || depth < maxDepth => List(Plus(e, IntConstant(1)), Minus(e, IntConstant(1)), Times(e, IntConstant(2)), Div(e, IntConstant(2)))
	    case IntConstant(n) if targetType == BooleanType || depth < maxDepth => List(LT(e, IntConstant(0)), GT(e, IntConstant(0)))
	    case IntArray(_, a) if (depth < maxDepth || targetType == IntType) && !e.isInstanceOf[Range] => List(ArrayLength(e)) ++ (if (depth > 0) List(IntArrayAccess(e, IntConstant(0))) else Nil)
	    case Object(_, _, f) => f filter { f => depth < maxDepth || canBeSameType(typer.typeOfValue(f._2), targetType) } map { s => FieldAccess(e, s._1) }
	    case BooleanConstant(b) if targetType == BooleanType && depth > 0 && !e.isInstanceOf[BooleanConstant] => List(Not(e))  // Ensure that negating uses a depth.
	    case _ => Nil
	  }}
	  val possibilities = constants ++ curVariables ++ binaryOps ++ calls ++ extras
	  //println("Depth " + depth + "/" + maxDepth + " poss: " + iterableToString(possibilities, ", ", (e: Expr) => shortPrinter.stringOfExpr(e)))
	  possibilities.filter{ e => getDepth(e) == depth }.foreach{ e => cachingExecutor.execute(memory, e) match {
	    case result @ (value, newMem) if !isErrorOrFailure(value) => addExpr(memory, e, getResult(e, memory, result))
	    case _ => 
	  } }
	  //println("Equivalences: " + iterableToString(equivalences(memory), ", ", (kv: (Result, ListBuffer[Expr])) => { kv._1 match { case v: Value => soe(v) case SideEffect(ms, v) => kv._1.toString } } + " -> {" + iterableToString(kv._2, ", ", (e: Expr) => soe(e)) + "}"))
	} }
	genExprsRec(depth + 1)
      }
      genExprsRec(0)  // TODO: This is a bit slow and could be optimized.
      //def soe(e: Expr): String = shortPrinter.stringOfExpr(e)
      val finalEquivMap = {
	val combinedEquivs = MHashMap.empty[Expr, MSet[Expr]]
	val allClasses = MHashSet.empty[MSet[Expr]] ++ equivalences.values.flatMap{ _.values.map{ MHashSet.empty[Expr] ++ _ } }
	//println("All classes: " + iterableToString(allClasses, ", ", (cls: MSet[Expr]) => "{" + iterableToString(cls, ", ", (e: Expr) => soe(e)) + "}"))
	allClasses.foreach{ curClass => curClass.foreach{ expr => combinedEquivs += (expr -> combinedEquivs.getOrElse(expr, curClass).intersect(curClass)) } }  // TODO: This is a bit slow and could be optimized.
	combinedEquivs
      }
      //println("Pre equivalences: " + iterableToString(equivalences, ", ", (me: (Memory, MHashMap[Result, ListBuffer[Expr]])) => me._1 + " -> " + iterableToString(me._2, ", ", (kv: (Result, ListBuffer[Expr])) => { kv._1 match { case v: Value => soe(v) case SideEffect(ms, v) => kv._1.toString } } + " -> {" + iterableToString(kv._2, ", ", (e: Expr) => soe(e)) + "}")))
      //println("Post equivalences: " + iterableToString(finalEquivMap, ", ", (kv: (Expr, MSet[Expr])) => soe(kv._1) + " -> {" + iterableToString(kv._2, ", ", (e: Expr) => soe(e)) + "}"))
      val demonstrations = evidence.collect{ case (v: Value, _) => v }.toSet
      val candidates = demonstrations ++ finalEquivMap.values.toSet.map{ (cls: MSet[Expr]) => cls.head }  // TODO: This is a bit slow and could be optimized.
      (candidates, finalEquivMap)
    }
    def expandEquivalences(validExprs: Iterable[Expr], equivalences: MMap[Expr, MSet[Expr]]): Iterable[Expr] = {
      val newlyExpanded = MSet.empty[Expr]
      def isUsefulInfix(infix: BinaryOp): Boolean = infix match {
	case Plus(l, r) => !l.isInstanceOf[Value] && ((r.isInstanceOf[Value] && r == IntConstant(1)) || shortPrinter.stringOfExpr(l) < shortPrinter.stringOfExpr(r))
	case Times(l, r) => !l.isInstanceOf[Value] && ((r.isInstanceOf[Value] && r == IntConstant(2)) || shortPrinter.stringOfExpr(l) <= shortPrinter.stringOfExpr(r))
	case Minus(l, r) => !l.isInstanceOf[Value] && ((r.isInstanceOf[Value] && r == IntConstant(1)) || shortPrinter.stringOfExpr(l) != shortPrinter.stringOfExpr(r))
	case Div(l, r) => !l.isInstanceOf[Value] && ((r.isInstanceOf[Value] && r == IntConstant(2)) || shortPrinter.stringOfExpr(l) != shortPrinter.stringOfExpr(r))
	case _ => shortPrinter.stringOfExpr(infix.lhs) < shortPrinter.stringOfExpr(infix.rhs)
      }
      def expandRec(expr: Expr): Iterable[Expr] = {
	if (newlyExpanded.contains(expr))
	  return equivalences(expr)
	newlyExpanded += expr
	val curDepth = getDepth(expr)
	val curEquivalences = equivalences.getOrElseUpdate(expr, MSet.empty[Expr] + expr)
	curEquivalences ++= { expr match {
	  case _: Value | Var(_) | ObjectID(_) | ArrayID(_) | LiteralExpr(_) => Nil
	  case op: BinaryOp =>
	    { for (l <- expandRec(op.lhs);
		   if (getDepth(l) < curDepth);
		   r <- expandRec(op.rhs);
		   if (getDepth(r) < curDepth))
	      yield { op match {
		case EQ(_, _) => EQ(l, r)
		case NE(_, _) => NE(l, r)
		case LT(_, _) => LT(l, r)
		case LE(_, _) => LE(l, r)
		case GT(_, _) => GT(l, r)
		case GE(_, _) => GE(l, r)
		case And(_, _) => And(l, r)
		case Or(_, _) => Or(l, r)
		case Plus(_, _) => Plus(l, r)
		case Minus(_, _) => Minus(l, r)
		case Times(_, _) => Times(l, r)
		case Div(_, _) => Div(l, r)
	      } } }.filter(isUsefulInfix)
	  case Not(e) =>
	    for (e <- expandRec(e))
	      yield Not(e)
	  case IntArrayAccess(a, i) =>
	    for (a <- expandRec(a);
		 i <- expandRec(i))
	      yield IntArrayAccess(a, i)
	  case FieldAccess(o, f) =>
	    for (o <- expandRec(o))
	      yield FieldAccess(o, f)
	  case In(n, r) =>
	    for (r <- expandRec(r))
	      yield In(n, r.asInstanceOf[Range])
	  case r: Range =>
	    for (min <- expandRec(r.min);
		 max <- expandRec(r.max))
	      yield { r match {
		case To(_, _) => To(min, max)
		case Until(_, _) => Until(min, max)
	      } }
	  case Call(name, args) =>
	    makeCalls(name, args.map(expandRec))
	  case _ => Nil
	} }
	curEquivalences
      }
      val candidates = validExprs.flatMap{ e => equivalences.getOrElse(e, Set(e)).toSet }.toSet  // We need to expand all of the equivalent expressions since some will have different forms.
      //println("Candidates: {" + iterableToString(candidates, ", ", (e: Expr) => soe(e)) + "}")
      candidates.flatMap(expandRec).toSet
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
    def getDepth(e: Expr): Int = {
      def max2(e1: Expr, e2: Expr): Int = Math.max(getDepth(e1), getDepth(e2))
      def maxN(nums: List[Expr]): Int = nums.map(getDepth).reduce(Math.max)//{ (x, y) => Math.max(x, y) }
      def isDoubleInfix(e: Expr): Boolean = e match {  // Heurstically avoid things with top infixes near the top-level.
	case op: BinaryOp => op.lhs.isInstanceOf[BinaryOp] || op.rhs.isInstanceOf[BinaryOp]
	case _ => false
      }
      { e match {
	case _: Value | Var(_) | ObjectID(_) | ArrayID(_) => 0
	case IntArrayAccess(a, i) => max2(a, i) + 1
	case FieldAccess(o,_) => getDepth(o) + 1
	case ArrayLength(e) => getDepth(e) + 1
	case Call(_, args) => maxN(args) + 1
	case In(_, r) => getDepth(r) + 1
	case r: Range => max2(r.min, r.max) + 1
	case op: BinaryOp => max2(op.lhs, op.rhs) + 1
	case Not(e) => getDepth(e) + 1
	case LiteralExpr(e) => getDepth(e)
      } } + { if (isDoubleInfix(e)) 1 else 0 }
    }
    //def soe(e: Expr): String = shortPrinter.stringOfExpr(e)
    //def som(m: Memory): String = shortPrinter.stringOfMemory(m)
    //println("\nEvidence: " + shortPrinter.stringOfStmt(StmtEvidenceHole(evidence.toList)))
    val (exprs, equivalences) = genExprs()
    //println("Exprs: {" + iterableToString(exprs, ", ", (e: Expr) => soe(e)) + "}")
    //println("Equivalences: " + iterableToString(equivalences, ", ", (kv: (Expr, MSet[Expr])) => soe(kv._1) + " -> {" + iterableToString(kv._2, ", ", (e: Expr) => soe(e)) + "}"))
    val validExprs = 
      if (checker.isEmpty)
	getValidChoices(exprs, evidence, cachingExecutor)
      else
	exprs filter { e => evidence forall { case (a, m) => checker.get(e, a, m) } }
    //println("Valid exprs: {" + iterableToString(validExprs, ", ", (e: Expr) => soe(e)) + "}")
    val allExprs = expandEquivalences(validExprs, equivalences).filter{ e => getDepth(e) <= maxDepth }.filter(hasCorrectForm(evidence.map{ _._1 }))
    //println("Final exprs: {" + iterableToString(allExprs, ", ", (e: Expr) => soe(e)) + "}")
    allExprs
  }

  /* Returns all of the given exprs that meet all the evidence.
   * Caches the executed results of the evidence to avoid recomputing it.
   * TODO-optimization: store evidence result and memory in the EvidenceHole itself.
   */ 
  private def getValidChoices(exprs: Iterable[Expr], evidence: Iterable[(Action, Memory)], executor: Executor = defaultExecutor): Iterable[Expr] = {
    val fullEvidence = evidence map { case (action, memory) => val (result, memAfter) = executor.execute(memory, action); (memory, result, memAfter) }
    val goodExprs = exprs filter { e => fullEvidence forall { case (memBefore, result, memAfter) => try { yieldEquivalentResults(memBefore, e, result, memAfter, executor) } catch { case _ => false } }}
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
  private val INITIAL_EXPR_DEPTH = 2

  // Maximum depth to check expressions.
  private val MAX_EXPR_DEPTH = 2

}
