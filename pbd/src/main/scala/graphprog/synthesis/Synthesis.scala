package graphprog.synthesis

import graphprog.lang.AST._
import graphprog.Controller
import scala.collection.immutable.{ Map => IMap }

// The postcondition takes (initial arguments, memory at end of program, return value).  Comparing initial and final values may cause problems as they have the same ids.
class Synthesis(private val controller: Controller, name: String, typ: Type, private val inputTypes: List[(String, Type)], private val functions: IMap[String, Program], private val objectTypes: IMap[String, List[(String, Type)]], private val printHelpers: PartialFunction[String, Value => String], private val generator: Option[Double => List[(String, Value)]], private val precondition: Option[IMap[String, Value] => Boolean], private val postcondition: Option[(IMap[String, Value], IMap[String, Value], Value) => Boolean], private val objectComparators: Map[String, (Value, Value) => Int]) extends Serializable {

  import graphprog.lang.{ Executor, Memory, Printer, Typer, IteratorExecutor }
  import graphprog.lang.ASTUtils._
  import graphprog.lang.Executor.simpleHoleHandler
  import graphprog.Controller._
  import graphprog.Utils._
  import scala.collection.mutable.{ Map, Set => MSet, ListBuffer }
  import scala.annotation.tailrec
  import scala.collection.{ Map => TMap }
  import Synthesis._
  import SynthesisUtils._

  /* Constructors */

  def this(controller: Controller, trace: Trace, printHelpers: PartialFunction[String, Value => String] = Map.empty, generator: Option[Double => List[(String, Value)]] = None, precondition: Option[IMap[String, Value] => Boolean] = None, postcondition: Option[(IMap[String, Value], IMap[String, Value], Value) => Boolean] = None, objectComparators: Map[String, (Value, Value) => Int] = Map.empty) = this(controller, trace.name, trace.typ, graphprog.lang.Typer.typeOfInputs(trace.inputs), trace.functions, trace.objectTypes, printHelpers, generator, precondition, postcondition, objectComparators)

  /* IVars */

  private val longPrinter = new Printer(printHelpers, true)
  private val shortPrinter = new Printer(printHelpers, false)
  private val defaultExecutor = new Executor(functions, longPrinter)
  private val typer = new Typer(functions, objectTypes)
  
  private var allInputs = List.empty[List[(String, Value)]]  // TODO: This should be a val ListBuffer, but with that when I load backed-up data, I can't add to this.
  private val finishedInputs = ListBuffer.empty[List[(String, Value)]]
  private val origHoles = Map.empty[Stmt, PossibilitiesHole]
  private val enteredActions = Map.empty[Stmt, ListBuffer[(List[Action], Memory)]]
  private val lastSearchDepth = Map.empty[Stmt, Int]
  //private val conditionEvidence = Map.empty[UnseenExpr, List[(Value, Memory)]]
  private var breakpoints = List.empty[Breakpoint]
  private var breakpointsToAdd = List.empty[Breakpoint]
  private var breakpointsToRemove = List.empty[Stmt]

  private val codeGenerator = new CodeGenerator(functions, shortPrinter, defaultExecutor, typer, enteredActions)

  private var numUnseensFilled = 0
  private var numDisambiguations = 0
  private var numCodeFixes = 0

  /* Checking for equality and other helpers */

  private def executeProgram(executor: Executor, input: List[(String, Value)], stmts: List[Stmt]): (Value, Memory) = executor.executeStmts(new Memory(input), stmts)

  /* Algorithms */

  private def genProgramFromCompleteTraces(actions: List[Action], memory: Memory, loops: TMap[Iterate, Loop]): List[Stmt] = {
    //traces foreach { t => println(utils.stringOfTrace(t)) }
    def genProgramFromCompleteTracesRec(ast: List[Stmt], traces: List[(List[Action], Memory)]): List[Stmt] = {
      //println(iterableToString(traces, " and ", (t: (List[Action], Memory)) => "[" + utils.stringOfStmts(t._1, t._2) + "]") + ".")
      if (traces.isEmpty)
	return ast :+ UnseenStmt()
      if (traces.head._1.isEmpty)
	return ast
      val heads = traces map { t => (t._1.head, t._2) }
      val curNode = heads.head._1 match {
	case Conditional(_, _) => 
	  val conditionalHeads = heads map { case (c: Conditional, m) => (c, m) case _ => throw new RuntimeException }
	  val conditions = conditionalHeads map { case (Conditional(c, _), m) => (c, m) }
	  val paths = conditionalHeads partition { case (Conditional(cond, _), memory) => defaultExecutor.evaluateBoolean(memory, cond) }
	  val true_branch = paths._1 map { case (Conditional(_, body), memory) => (body, memory) }
	  val false_branch = paths._2 map { case (Conditional(_, body), memory) => (body, memory) }
	  If(ExprEvidenceHole(conditions), genProgramFromCompleteTracesRec(Nil, true_branch), Nil, genProgramFromCompleteTracesRec(Nil, false_branch))
	case i: Iterate if loops contains i => loops(i)
	case Iterate(_) =>
	  val allIterations = heads flatMap { case (Iterate(i), m) => { val as = i map { t => t._1 :: t._2 }; as zip as.scanLeft(m){ (curMem, curIter) => defaultExecutor.executeStmts(curMem, curIter)._2 } } case _ => throw new RuntimeException }
	  val conditionals = allIterations map { case (c :: b, m) => (List(c), m) case _ => throw new RuntimeException }
	  val bodies = allIterations flatMap { case (c :: b, m) => if (b.isEmpty) Nil else List((b, defaultExecutor.execute(m, c)._2)) case _ => throw new RuntimeException }
	  val newConditionals = {  // Add a Break to the conditional if it's a for loop so we know we broke out.
	    if (conditionals.head._1.head.isInstanceOf[Assign])
	      allIterations.map{ case (c :: b, m) => ((List(c), m), defaultExecutor.executeStmts(defaultExecutor.execute(m, c)._2, b)) case _ => throw new RuntimeException }.flatMap{ case ((c, m1), (BreakHit, m2)) => List((c, m1), (List(Break), m2)) case ((c, m), _) => List((c, m)) }
	    else
	      conditionals
	  }
	  Loop(genProgramFromCompleteTracesRec(Nil, newConditionals).head, genProgramFromCompleteTracesRec(Nil, bodies))
	case Assert(_) | Assume(_) | Println(_) => heads.head._1  // TODO: Is this right?
	case Break => assert(heads forall { _._1 == Break }); return ast :+ Break
	case LiteralAction(a) => assert(holdsOverIterable(heads, (x: (Action, Memory), y: (Action, Memory)) => x._1 == y._1)); a
	case LiteralExpr(e) => assert(holdsOverIterable(heads, (x: (Action, Memory), y: (Action, Memory)) => x._1 == y._1)); e
	case UnorderedStmts(_) => 
	  val bodies = heads map { case (UnorderedStmts(s), m) => s.asInstanceOf[List[Action]] map { a => (List(a), m) } case _ => throw new RuntimeException }
	  UnorderedStmts(bodies.transpose flatMap { x => genProgramFromCompleteTracesRec(Nil, x) })
	case Snapshot(_) =>
	  val changes = heads map { case (Snapshot(sm), om) => diffMemories(om, sm) case _ => throw new RuntimeException }
	  // Add in dummy assignments for variables that were assigned sometimes but not others.
	  var (_, varLHS, _, _) = changes.foldLeft((true, Set[String](), Set[(Int, String)](), Set[(Int, Int)]())) { case ((isFirst, accVars, accFields, accModArrs), (curVars, curFields, curModArrs)) => {
	    assert(heads.size == 1 || (curFields.size <= 1 && curModArrs.size <= 1 && (isFirst || ((accFields.size > 0) == (curFields.size == 1) && (accModArrs.size > 0) == (curModArrs.size == 1)))))  // TODO: I currently allow snapshots in loops to write to at most one field/array.  This is artificial, but removing it is difficult, as it is not obvious which assignments from different iterations work together.
	    (false, accVars ++ curVars.keys.toSet, accFields ++ curFields.keys.toSet, accModArrs ++ curModArrs.keys.toSet)
	  }}
	  val fullChanges = changes map { case (vars, fields, arrs) => (varLHS map { n => if (vars contains n) (n, vars(n)) else (n, Var(n)) }, fields map { case (k, v) => (k, v) }, arrs map { case (k, v) => (k, IntConstant(v)) }) }  // Note that we combine variable assignments but not fields/arrays.
	  def getRealExpr(e: Expr): Expr = e match {
	    case Object(id, _, _) => ObjectID(id)  // Use the current version of the object in case other changes have been made to it.
	    case _ => e
	  }
	  // Convert to UnorderedStmts and recurse on those
	  val stmts = fullChanges map { case (vars, fields, modArrs) => UnorderedStmts((vars.map{ case (n, v) => Assign(Var(n), getRealExpr(v)) } ++ fields.map { case ((id, f), v) => Assign(FieldAccess(ObjectID(id), f), getRealExpr(v)) } ++ modArrs.map{ case ((id, i), v) => Assign(IntArrayAccess(ArrayID(id), IntConstant(i)), v) }).toList) }
	  return genProgramFromCompleteTracesRec(ast, stmts.zip(traces).map{ case (s, (_ :: rest, m)) => (s :: rest, m) case _ => throw new RuntimeException })
	case _ => StmtEvidenceHole(heads)
      }
      val rest = traces flatMap { case (a :: as, m) => val v = defaultExecutor.execute(m, a); if (v._1 == BreakHit) Nil else List((as, v._2)) case _ => throw new RuntimeException }  // TODO-optimization: I've already executed them at least once if they're conditionals or iterates.
      genProgramFromCompleteTracesRec(ast :+ curNode, rest)
    }
    genProgramFromCompleteTracesRec(Nil, List((actions, memory)))
  }

  /* Input generation */

  private def genRandomInput(bounds: (Int, Int, Int, Int)): List[(String, Value)] = {
    import scala.util.Random.{nextInt, nextBoolean, nextFloat}
    val (_, l, u, arraySize) = bounds
    var id = 0
    def getID(): Int = { var cur = id; id += 1; cur }
    def genRandom(inputs: List[(String, Type)]): List[(String, Value)] = inputs map { t => (t._1, t._2 match {
      case IntType => IntConstant(nextBoundedInt(l, u))
      case BooleanType => BooleanConstant(nextBoolean())
      case ArrayType(IntType) => IntArray(getID(), (0 until nextInt(arraySize)).map{ _ => nextBoundedInt(l, u) }.toArray)
      case ObjectType(typ) => if (nextFloat() < NULL_PROBABILITY) Null else Object(getID(), typ, Map.empty ++ genRandom(objectTypes(typ)))
      case ArrayType(_) => throw new IllegalArgumentException("Cannot handle non-integer arrays.")
    })}
    genRandom(inputTypes)
  }

  private def findFirstRandomInput(inputSize: Double, successCond: Option[List[(String, Value)] => Boolean]): Option[List[(String, Value)]] = generator match {
    case Some(generator) =>
      // Try 0.1, 0.2, ..., 0.9 in increasing order of their distance to inputSize without wrapping.
      // If inputSize >= 0.5 we prefer smaller numbers, otherwise we prefer larger numbers.
      // E.g. inputSize = 0.3 yields 0.3, 0.4, 0.2, 0.5, 0.1, 0.6, 0.0, 0.7, 0.8, 0.9.
      val maxInputs = EXPLORATION_BOUNDS.foldLeft(0){ (acc, cur) => acc + cur._1 }
      val sizes = {
	val start = math.round(inputSize * 10)
	(0 until 10).sortWith{ (x, y) => val xDiff = math.abs(x - start); val yDiff = math.abs(y - start); if (xDiff < yDiff) true else if (xDiff > yDiff) false else if (inputSize >= 0.5) x < y else y < x }.map{ _ / 10.0 }
      }
      for (i <- 0 until maxInputs) {
	val size = sizes((i / maxInputs.toDouble * 10).toInt)
	val input = generator(size)
	if (successCond match { case Some(c) => c(input) case None => true })
	  return Some(input)
      }
      None
    case None =>
      val bounds = {  // Order bounds based on inputSize.
	if (inputSize <= 1/3.0)
	  EXPLORATION_BOUNDS
	else if (inputSize <= 2/3.0)
	  EXPLORATION_BOUNDS(1) :: EXPLORATION_BOUNDS(0) :: List(EXPLORATION_BOUNDS(2))
	else
	  EXPLORATION_BOUNDS.reverse
      }
      precondition match {
	case None => Some(genRandomInput(bounds.head))
	case Some(precondition) => 
	  for (bounds <- bounds; _ <- 0 until bounds._1) {
	    val input = genRandomInput(bounds)
	    if (precondition(input.toMap) && (successCond match { case Some(c) => c(input) case None => true }))
	      return Some(input)
	  }
	  None
      }
  }

  val simpleHoleHandlerExecutor = new Executor(functions, longPrinter, simpleHoleHandler(defaultExecutor))

  /**
   * Finds the first random input that helps us.
   * @param inputSize A number in [0, 1] representing the size of the input to
   * generate.  Numbers closer to 0 are smaller.
   */
  private def findFirstNewRandomInput(code: List[Stmt], inputSize: Double): Option[List[(String, Value)]] = {
    def tryInput(input: List[(String, Value)]): Boolean = try { executeProgram(simpleHoleHandlerExecutor, input, code)._1 == ErrorConstant } catch { case _: Throwable => true } // We clone the memory so we don't mutate the original input.
    findFirstRandomInput(inputSize, Some(i => tryInput(i)))
  }

  /**
   * Helper that finds the best random input according to the given functions.
   * @param runFn Runs the given input and returns some information.
   * @param compareFn Compares the returned info from different inputs
   * and chooses the best.  <0 means we prefer the first, >0 the second.
   * It must be a total ordering.
   * @param useFn Whether we should use the input that generated the
   * given information or return none to represent that nothing was found.
   */
  private def findBestRandomInputHelper[T](runFn: List[(String, Value)] => T, compareFn: (T, T) => Int, useFn: T => Boolean): Option[List[(String, Value)]] = {
    val inputs: Seq[List[(String, Value)]] = generator match {
      case Some(generator) =>
	val numInputs = EXPLORATION_BOUNDS.foldLeft(0){ (acc, cur) => acc + cur._1 }
	(0 until numInputs).map{ i => generator(i / numInputs.toDouble) }
      case None =>
	val randomInputs = for (bounds <- EXPLORATION_BOUNDS; _ <- 0 until bounds._1) yield genRandomInput(bounds)
	precondition match {
	  case None => randomInputs
	  case Some(precondition) => randomInputs.filter{ i => precondition(i.toMap) }
	}
    }
    findBestRandomInputHelper(inputs, runFn, compareFn, useFn)
  }
  private def findBestRandomInputHelper[T](inputs: Seq[List[(String, Value)]], runFn: List[(String, Value)] => T, compareFn: (T, T) => Int, useFn: T => Boolean): Option[List[(String, Value)]] = {
    //println(({ val r = inputs.map{ input => runFn(input) }.sortWith{ (x, y) => compareFn(x, y) < 0 }; r.tail.takeWhile{ x => compareFn(r.head, x) == 0 }.size } + 1) + " best input(s).")
    //println(iterableToString(inputs.map{ input => (input, runFn(input)) }.sortWith{ (x, y) => compareFn(x._2, y._2) < 0 }, "\n", (t: (List[(String, Value)], T)) => shortPrinter.stringOfInputs(t._1, ", ") + " -> " + t._2.toString))
    if (inputs.isEmpty)
      return None
    val bestInput = inputs.map{ input => (input, runFn(input)) }.reduceLeft{ (acc, cur) => if (compareFn(cur._2, acc._2) < 0) cur else acc }  // Prefer the earlier elements in the list
    if (useFn(bestInput._2))
      Some(bestInput._1)
    else
      None
  }

  /**
   * Finds the best random input.  See the comment below for compareFn for the definition of best.
   */
  private def findBestRandomInput(code: List[Stmt], preferredInput: Option[List[(String, Value)]]): Option[List[(String, Value)]] = {
    // Stores the initial input values, the hole where we diverged, and the distinct values at that divergence.
    case class FirstQuestionHole(input: Iterable[Value], hole: Hole, values: List[Value]) extends Value with IsErrorOrFailure {
      override def toString: String = iterableToString(input, ", ", (v: Value) => shortPrinter.stringOfValue(v)) + " -> " + shortPrinter.stringOfHole(hole) + " with " + values.size  + " values."
    }
    /**
     * Runs the program with the given input and records information about the first diverging hole.
     */
    def runFn(input: List[(String, Value)]): Option[FirstQuestionHole] = {
      def holeHandler(input: List[Value])(memory: Memory, hole: Hole): Stmt = hole match {
	case PossibilitiesHole(possibilities) => 
	  val results = possibilities flatMap { s => try { val (v, m) = defaultExecutor.execute(memory, s); if (v == ErrorConstant) Nil else List((s, v, m)) } catch { case _: Throwable => Nil } }
          if (results.size == 0)
	    FirstQuestionHole(input, hole, Nil)
          else if (results.size == possibilities.size && holdsOverIterable(results, (x: (Stmt, Value, Memory), y: (Stmt, Value, Memory)) => areEquivalent(x._2, y._2, x._3, y._3)))
	    results.head._1
	  else
	    FirstQuestionHole(input, hole, results.foldLeft(List[Value]()){ (acc, cur) => if (acc.find{ v => areEqual(cur._2, v, true, true) }.isDefined) acc else cur._2 :: acc })  // List the unique values.
	case _: Unseen => FirstQuestionHole(input, hole, Nil)
	case _: EvidenceHole => throw new IllegalArgumentException(hole.toString)
      }
      val executor = new Executor(functions, longPrinter, holeHandler(input.map{ _._2 }))
      executeProgram(executor, input, code)._1 match {
	case r: FirstQuestionHole => Some(r)
	case _ => None
      }
    }
    /**
     * Compares two inputs.  Returns <0 if x is smaller than y, >0 if it
     * is larger, and 0 if they are the same size.  We define smaller as follows.
     * - For integers, whichever is smaller (or positive if they have the same absolute value).
     * - For arrays, if one is a smaller size, we return it.  Otherwise, we return the one with the smaller sum of absolute values.
     * - Null is smaller than a non-null object.
     * - For two objects, we recursively compare their fields.  But if those fields are themselves objects, we do not recurse again but simply consider any two non-null fields as the same size.
     * - For multiple things (the list of initial inputs or fields), we recursively compare each pair.  If one has more smaller
     * objects and arrays, we return it.  Otherwise, we return the on with more smaller integers.
     */
    // TODO: Potentially I should modify this to not prefer things that can be constants (e.g. 0, 1, 2) since they can lead to more questions.
    def compareInputs(doSimpleObjectCheck: Boolean)(x: Iterable[Value], y: Iterable[Value]): Int = {
      def normalize(n: Int): Int = if (n < 0) -1 else if (n > 0) 1 else 0
      def sumArray(a: Array[Int]): Int = a.foldLeft(0){ (acc, cur) => acc + math.abs(cur) }
      def sortFields(f: Map[String, Value]): Iterable[Value] = f.toList.sortBy{ _._1 }.map{ _._2 }
      def defaultCompareObjects(o1: Object, o2: Object): Int = {
	def getObjects(v: Value, objects: Set[Int]): Set[Int] = v match {
	  case Object(id, _, f) if !objects.contains(id) => f.values.foldLeft(objects + id){ (acc, cur) => getObjects(cur, acc) }
	  case _ => objects
	}
	if (doSimpleObjectCheck)
	  0
	else {
	  val diff = getObjects(o1, Set.empty[Int]).size - getObjects(o2, Set.empty[Int]).size
	  normalize(if (diff != 0) diff else compareInputs(true)(sortFields(o1.fields), sortFields(o2.fields)))
	}
      }
      val scores = x.zip(y).map{ t => (t, t match {
	case (BooleanConstant(_), BooleanConstant(_)) => 0
	case (IntConstant(n1), IntConstant(n2)) =>
	  val diff = normalize(math.abs(n1) - math.abs(n2))
	  if (diff != 0)
	    diff
	  else  // Prefer positive numbers over negative numbers.
	    normalize(n2 - n1)
	case (StringConstant(s1), StringConstant(s2)) => s1.size - s2.size
	case (IntArray(_, a1), IntArray(_, a2)) => normalize(if (a1.size != a2.size) a1.size - a2.size else sumArray(a1) - sumArray(a2))
	case (Null, Null) => 0
	case (Null, Object(_, _, _)) => -1
	case (Object(_, _, _), Null) => 1
	case (o1 @ Object(_, t1, _), o2 @ Object(_, t2, _)) if t1 == t2 && objectComparators.contains(t1) => objectComparators(t1)(o1, o2)
	case (o1: Object, o2: Object) => defaultCompareObjects(o1, o2)
      }) }
      val (simple, complicated) = scores.partition{ t => t._1._1.isInstanceOf[BooleanConstant] || t._1._1.isInstanceOf[IntConstant] }
      val complicatedSum = complicated.map{ _._2 }.sum
      if (complicatedSum != 0)
	complicatedSum
      else
	simple.map{ _._2 }.sum
    }
    /**
     * Orders two unseen statements with the following algorithm.
     * - If one happens-before the other, return that.
     * - Otherwise, if removing one would allow us to prune more holes, return that.
     * - Otherwise, if removing one would open more unseen statements, return that.
     */
    def orderUnseens(h1: Unseen, h2: Unseen): Int = {
      // Replaces the given hole with UnitConstant.
      def removeHole(target: Hole): List[Stmt] = {
	def removeHoleFromStmts(stmts: List[Stmt]): List[Stmt] = {
	  def removeHoleFromStmt(stmt: Stmt): Stmt = stmt match {
	    case h if h.eq(target) => UnitConstant
	    case If(c, t, ei, e) => If(removeHoleFromStmt(c).asInstanceOf[Expr], removeHoleFromStmts(t), ei.map{ p => (removeHoleFromStmt(p._1).asInstanceOf[Expr], removeHoleFromStmts(p._2)) }, removeHoleFromStmts(e))
	    case Loop(c, b) => Loop(removeHoleFromStmt(c), removeHoleFromStmts(b))
	    case UnorderedStmts(s) => UnorderedStmts(removeHoleFromStmts(s))
	    case s => s
	  }
	  stmts map removeHoleFromStmt
	}
	removeHoleFromStmts(code)
      }
      // Compute happens-before relation.
      def orderHoles(stmts: List[Stmt]): Int = {
	def orderHoleInStmt(stmt: Stmt): Int = stmt match {
	  case h: Unseen if h eq h1 => -1
	  case h: Unseen if h eq h2 => 1
	  case If(c, t, ei, e) =>
	    val condition = orderHoleInStmt(c)
	    if (condition != 0)
	      condition
	    else {
	      val r = (t :: e :: ei.map{ x => x._1 :: x._2 }).map(orderHoles)
	      if (r.contains(-1) && r.contains(1)) {  // Try removing the two holes.
		def getSizes(h: Hole): (Int, Int) = { val (before, first, _) = classifyHoles(removeHole(h)); (before.size, first.size) }
		val (beforeH1, firstH1) = getSizes(h1)
		val (beforeH2, firstH2) = getSizes(h2)
		if (beforeH1 != beforeH2)
		  beforeH2 - beforeH1
		else
		  firstH2 - firstH1
	      } else if (r contains -1)
		-1
	      else if (r contains 1)
		1
	      else
		0
	    }
	  case Loop(c, b) => orderHoles(c :: b)
	  case UnorderedStmts(s) => orderHoles(s)
	  case _ => 0
	}
	stmts.foldLeft(0){ (prev, cur) => if (prev != 0) prev else orderHoleInStmt(cur) }
      }
      orderHoles(code)
    }
    /**
     * Compares two results using the following rules.
     * - If one distinguishes between some possibilities and the other does not, choose the one that does.
     * - Otherwise, compare the first hole they distinguish (as it is the only one we know for certain).
     * -- If one is an unseen statement and the other is not, choose the unseen statement.
     * -- If both are possibility holes, choose the one that has the smallest ratio of possibilities to distinct values (the expected number of possibilities after the user answers) or the one that has no distinct values.
     * --- If both have the same ratio, choose the "smaller" one (see compareInputs).
     * -- If both are different unseen statements, choose the one that happens-before the other (see orderUnseens for details).
     * -- If both are the same unseen statement, choose the "smaller" input.
     */
    def compareFn(inputComparator: (Iterable[Value], Iterable[Value]) => Int)(x: Option[FirstQuestionHole], y: Option[FirstQuestionHole]): Int = (x, y) match {
      case (None, None) => 0
      case (None, Some(_)) => 1
      case (Some(_), None) => -1
      case (Some(FirstQuestionHole(i1, h1, v1)), Some(FirstQuestionHole(i2, h2, v2))) => ((i1, h1, v1), (i2, h2, v2)) match {
	case ((i1, PossibilitiesHole(p1), v1), (i2, PossibilitiesHole(p2), v2)) => 
	  if (v1.isEmpty && v2.isEmpty)
	    return 0
	  else if (v1.isEmpty)
	    return -1
	  else if (v2.isEmpty)
	    return 1
	  val (r1, r2) = (p1.size / v1.size.toDouble, p2.size / v2.size.toDouble)
	  if (r1 < r2)
	    -1
	  else if (r1 > r2)
	    1
	  else
	    inputComparator(i1, i2)
	case ((i1, h1: Unseen, _), (i2, h2: Unseen, _)) => if (h1 eq h2) inputComparator(i1, i2) else orderUnseens(h1, h2)
	case ((_, _: Unseen, _), _) => -1
	case (_, (_, _: Unseen, _)) => 1
      }
    }
    def useFn(found: Option[FirstQuestionHole]): Boolean = found.isDefined
    val bestInput = findBestRandomInputHelper(runFn, compareFn(compareInputs(false)), useFn)
    findBestRandomInputHelper(preferredInput.toList ++ bestInput.toList, runFn, compareFn( (_, _) => 0 ), useFn)  // The helper prefers elements earlier in the list.
  }

  @tailrec private def getNextInput(code: List[Stmt], preferredInput: Option[List[(String, Value)]]): (List[Stmt], Option[List[(String, Value)]]) = {
    if (isComplete(code))
      return (code, None)
    val inputs = findBestRandomInput(code, preferredInput)
    if (inputs.isEmpty)
      return (code, None)
    val (prunedStmts, shouldContinueWithInput) = simpleInputPruning(code, inputs.get)
    if (shouldContinueWithInput)
      (prunedStmts, inputs)
    else
      getNextInput(prunedStmts, None)
  }

  private case class FixCode(reason: String, curStmt: Option[Stmt]) extends RuntimeException with FastException
  private case class PruneCode(curStmts: List[Stmt]) extends RuntimeException with FastException
  private case class FixedCode(curStmt: Option[Stmt], newCode: CodeInfo) extends RuntimeException with FastException
  private case class SkipTrace(info: EndTrace, newStmts: IMap[Stmt, Stmt], newBlocks: IMap[Stmt, List[Stmt]]) extends RuntimeException with FastException
  private case class FoundMoreExpressions(curStmt: Stmt) extends RuntimeException with FastException
  // TODO: Remove asInstanceOfs
  // We might have isFixing == true and failingStmt == None, for instance when there is no correct path on an input but we don't crash on a single statement (from long pruning).
  private def executeWithHelpFromUser(memory: Memory, origStmts: List[Stmt], pruneAfterUnseen: Boolean, amFixing: Boolean, failingStmt: Option[Stmt], otherBranch: Option[(Stmt, UnknownJoinIf)] = None): (List[Action], List[Stmt], Memory) = {
    def updateDisplay(memory: Memory, curStmt: Option[Stmt], newStmts: IMap[Stmt, Stmt], newBlocks: IMap[Stmt, List[Stmt]], layoutObjs: Boolean = true) = {
      val code = getNewStmts(origStmts, newStmts, newBlocks)
      val displayCode = otherBranch match {  // Show the unknown join to the user.
	case Some((target, UnknownJoinIf(i, _))) => addBlock(code, (Some(target), None), s => UnknownJoinIf(i, s))
	case None => code
      }
      val actualBreakpoints = breakpoints map { breakpoint => newStmts.get(breakpoint.line) match {
	case Some(newStmt) => refreshBreakpointLine(breakpoint, newStmt)
	case None => breakpoint
      } }
      controller.updateDisplay(memory, displayCode, curStmt, layoutObjs, actualBreakpoints, failingStmt)
    }
    var continue = false  // Whether the user has selected to continue.
    var foundMoreExpressions = false
    def doFixStep(memory: Memory, curStmt: Option[Stmt], newStmts: IMap[Stmt, Stmt], newBlocks: IMap[Stmt, List[Stmt]], diffInfo: Option[(Memory, Stmt, Value)]): Boolean = {
      assert(amFixing)
      (diffInfo, continue) match {
	case (Some(_), true) => // The user pressed continue and there's only one possibility, so execute it.
	case _ =>
	  //continue = false  // TODO: Should we continue in this case or not?
	  updateDisplay(memory, curStmt, newStmts, newBlocks, false)
	  controller.doFixStep(diffInfo, canDiverge = !otherBranch.isDefined) match {
	    case Step => // Do nothing, which accepts the current choice.
	    case Continue => continue = true
	    case c: CodeInfo => throw new FixedCode(curStmt, c)
	    case EndConditional => throw new RuntimeException
	    case e: EndTrace => throw new SkipTrace(e, newStmts, newBlocks)
	    case FindMoreExpressions => return true
	  }
      }
      false
    }
    var pruneBeforeNextDisambiguation = false
    def executeWithHelpFromUserHelper(memory: Memory, stmts: List[Stmt], newStmts: IMap[Stmt, Stmt], newBlocks: IMap[Stmt, List[Stmt]], indent: String, printFn: String => Unit = print): ((Memory, List[Action], IMap[Stmt, Stmt], IMap[Stmt, List[Stmt]]), Boolean) = {
      // Parse a string, retrying if the user gives us an illegal string.
      /*def parse(inputFn: => String, failFn: => List[Action], indent: String): List[Action] = {
	try {
	  graphprog.lang.Compiler.parse(inputFn)
	} catch {
	  case _ =>
	    println(indent + "The action(s) you entered do not seem to be legal.  Please try again.")
	    failFn
	}
      }
      def getTraceFromUser(indent: String): List[Action] = {
	@tailrec def getLines(acc: String = ""): String = readLine(indent) match {
	  case "" => acc
	  case s => getLines(acc + (if (acc == "") "" else "\n") + s)
	}
	parse(getLines(), getTraceFromUser(indent), indent)
      }
      def getActionFromUser(possibilities: List[Stmt], indent: String, prefix: String = ""): Action = {
	val pattern = """:(-?\d+)""".r
	val input = readLine(indent + prefix)
	val stmt = input match {
	  case pattern(index) if index.toInt < possibilities.size && index.toInt >= -possibilities.size =>
	    val i = index.toInt
	    val action = if (i >= 0) possibilities(i) else possibilities(possibilities.size + i)
	    println(indent + input + " is " + longPrinter.stringOfStmt(action))
	    action.asInstanceOf[Action]
	  case s => parse(prefix + s, List(getActionFromUser(possibilities, indent, prefix)), indent).head
	}
	stmt
      }*/
      def noprint(s: String) = ()
      def myprint(s: String) = printFn(indent + s)
      def myprintln(s: String) = printFn(indent + s + "\n")
      stmts.foldLeft(((memory, List[Action](), newStmts, newBlocks), false)){ case (((memory, trace, newStmts, newBlocks), breakHit), curStmt) => {
	def conditionHelper(memory: Memory, condition: Stmt, newStmts: IMap[Stmt, Stmt], newBlocks: IMap[Stmt, List[Stmt]]): (Action, IMap[Stmt, Stmt], IMap[Stmt, List[Stmt]], Boolean, Memory) = {
	  val ((conditionMemory, conditionActions, newerStmts, newerBlocks), _) = executeWithHelpFromUserHelper(memory, List(condition), newStmts, newBlocks, indent, noprint)
	  val conditionExpr = conditionActions.head.asInstanceOf[Expr]
	  val conditionResult = defaultExecutor.evaluate(memory, conditionExpr)
	  println(indent + "cond (" + shortPrinter.stringOfExpr(conditionExpr) + ") is " + shortPrinter.stringOfValue(conditionResult))
	  (conditionExpr, newerStmts, newerBlocks, conditionResult.isInstanceOf[IntConstant] || conditionResult.asInstanceOf[BooleanConstant].b, conditionMemory)
	}
	if (breakHit) 
	  ((memory, trace, newStmts, newBlocks), breakHit)
	else if (newBlocks.contains(curStmt))
	  executeWithHelpFromUserHelper(memory, newBlocks(curStmt), newStmts, newBlocks, indent, noprint)
	else {
	  val actualCurStmt = newStmts.getOrElse(curStmt, curStmt)
	  //println("Executing " + shortPrinter.stringOfStmt(actualCurStmt))
	  def updateDisplayShort(layoutObjs: Boolean = true) = updateDisplay(memory, Some(actualCurStmt), newStmts, newBlocks, layoutObjs)
	  def doFixStepShort(diffInfo: Option[(Memory, Stmt, Value)]) {
	    if (doFixStep(memory, Some(actualCurStmt), newStmts, newBlocks, diffInfo)) {
	      val newHole = findMoreExpressions()
	      controller.hideFixingGui()  // We might have had the step GUI but need to show possibilities GUI, so this clears the old stuff.
	      origHoles.getOrElse(curStmt, curStmt) match {
		case origHole: PossibilitiesHole =>
		  origHoles -= curStmt
		  origHoles += (newHole -> origHole)
		case _ =>
	      }
	      throw new FoundMoreExpressions(newHole)
	    }
	  }
	  // Do a new search for the current statement at a depth one larger than before.
	  def findMoreExpressions(): PossibilitiesHole = {
	    val origStmt = origHoles.getOrElse(curStmt, curStmt)
	    val lastDepth = lastSearchDepth.getOrElse(origStmt, CodeGenerator.INITIAL_EXPR_DEPTH)
	    enteredActions.get(origStmt) match {  // Get all the actions/memories the user has given us for this statement.
	      case Some(enteredActions) => codeGenerator.fillHoles(List(StmtEvidenceHole(enteredActions.flatMap{ case (as, m) => as.map{ (_, m) } }.toList)), false, Some(memory), lastDepth + 1) match {
		case List(newHole: PossibilitiesHole) =>
		  println(indent + "Went from " + shortPrinter.stringOfStmt(curStmt) + " to " + shortPrinter.stringOfStmt(newHole))
		  lastSearchDepth += (origStmt -> (lastDepth + 1))
		  foundMoreExpressions = true
		  newHole
		case _ => throw new RuntimeException
	      }
	      case None => throw new RuntimeException
	    }
	  }
	  // Handle breakpoints
	  breakpointsToAdd foreach { breakpoint => {
	    val origStmts = newStmts.collect{ case (k, v) if v eq breakpoint.line => k }.toList
	    breakpoints :+= { (origStmts: @unchecked) match {
	      case Nil => breakpoint
	      case origStmt :: Nil => refreshBreakpointLine(breakpoint, origStmt)
	    } }
	  } }
	  breakpointsToAdd = Nil
	  breakpointsToRemove foreach { line => {
	    val origStmts = newStmts.collect{ case (k, v) if v eq line => k }.toList
	    val origStmt = (origStmts: @unchecked) match {
	      case Nil => line
	      case origStmt :: Nil => origStmt
	    }
	    breakpoints = breakpoints filterNot { _.line eq origStmt }
	  } }
	  breakpointsToRemove = Nil
	  if (breakpoints exists { _ match {
	    case NormalBreakpoint(s) => curStmt eq s
	    case ConditionalBreakpoint(s, c) => curStmt.eq(s) && (try { defaultExecutor.evaluateBoolean(memory, c) } catch { case _ => updateDisplayShort(false); controller.displayMessage("Evaluation of this breakpoint's condition crashed."); true })  // TODO: Is this how we want to handle this case?
	  } })
	    continue = false
	  // See if we're at the point where we need to step through the already-seen branch of a conditional.
	  otherBranch match {
	    case Some((targetStmt, uif)) if targetStmt.eq(actualCurStmt) =>  // I don't need to compare memories since all previous times at this point I've taken the same branch (the original one).
	      assert(amFixing)
	      updateDisplay(memory, Some(actualCurStmt), newStmts, newBlocks, false)
	      controller.insertConditionalAtPoint(getNewStmts(origStmts, newStmts, newBlocks), uif, stmts.dropWhile{ _.ne(curStmt) }.map{ s => newStmts.getOrElse(s, s) }) match {
		case c: CodeInfo => throw new FixedCode(None, c)
		case e: EndTrace => throw new SkipTrace(e, newStmts, newBlocks)
	      }
	    case _ =>
	  }
	  // Handle the actual statement
	  def handleStmt(actualCurStmt: Stmt): ((Memory, List[Action], IMap[Stmt, Stmt], IMap[Stmt, List[Stmt]]), Boolean) = (actualCurStmt: @unchecked) match {
	    case curHole @ PossibilitiesHole(possibilities) =>
	      def updateHoleMaps(newStmt: Stmt, actions: List[Action], userEntered: Boolean) = origHoles.getOrElse(curStmt, curStmt) match {
		case origHole: PossibilitiesHole => 
		  if (userEntered)
		    enteredActions.getOrElseUpdate(origHole, ListBuffer.empty) += ((actions, memory))
		  if (newStmt != curStmt) {
		    assert(actualCurStmt == curStmt || (origHoles.contains(actualCurStmt) && !origHoles.contains(curStmt)), actualCurStmt + "  " + curStmt + "  " + origHoles)
		    origHoles -= actualCurStmt
		    origHoles += (newStmt -> origHole)
		  }
		case _ =>
	      }
	      // Filter out things that are illegal and cause errors
	      val newPossibilities = possibilities filter { p => try { val v = defaultExecutor.evaluate(memory, p); !isErrorOrFailure(v) } catch { case _ => false } }
	      if (newPossibilities.isEmpty)
		doFixStepShort(None)  // TODO: If newPossibilities is empty, get this trace and generate a new hole from all the evidence with depth+1?  Requires that I combine evidence and possibilities holes.
	      // If all possibilities yield the same result, use it.
	      val (firstResult, firstPossMemory) = defaultExecutor.execute(memory, newPossibilities.head)
	      if (newPossibilities.tail forall { p => yieldEquivalentResults(memory, p, firstResult, firstPossMemory, defaultExecutor) }) {
		val action = (newPossibilities.head: @unchecked) match {  // TODO: Change top-level hole to assign with hole inside it to remove this?
		  case c @ Call(name, _) =>
		    myprintln("Call to " + name + " got " + firstResult)
		    c  // We must return a call and not just the value so we can re-execute it later when it is a possibility.  We choose an arbitrary call because they call get the same result
		  case i: In =>
		    myprintln(shortPrinter.stringOfExpr(firstResult))
		    i  // We must return the actual in and not the result so it can get executed later, as in call above.
		  case e: Expr => 
		    myprintln(longPrinter.stringOfExpr(firstResult))
		    firstResult
		  case Assign(l, _) =>
		    myprintln(shortPrinter.stringOfExpr(l) + " := " + longPrinter.stringOfValue(firstResult))
		    Assign(l, firstResult)
		}
		if (amFixing)
		  doFixStepShort(Some((firstPossMemory, newPossibilities.head, firstResult)))
		val newStmt = possibilitiesToStmt(curHole, newPossibilities)
		updateHoleMaps(newStmt, newPossibilities map { _.asInstanceOf[Action] }, false)
		((firstPossMemory, trace :+ action, newStmts + (curStmt -> newStmt), newBlocks), false)
	      } else {
		if (pruneBeforeNextDisambiguation)
		  throw new PruneCode(getNewStmts(origStmts, newStmts, newBlocks))
		updateDisplayShort(!amFixing)
		val holeString = "Hole(" + newPossibilities.foldLeft(("", 0)){ case ((acc, i), cur) => (acc + (if (acc == "") "" else " or ") + "(" + i.toString + ") " + shortPrinter.stringOfStmt(cur), i + 1) }._1 + ")"
		println(indent + Console.RED + "**" + Console.RESET + "Please finish statement: " + holeString)
		println(indent + "Memory is: " + longPrinter.stringOfMemory(memory))
		// Get the current action from the user, retrying if they give us something we are not expecting (e.g. make a typo).
		/*def getActionText(isFirstTry: Boolean): (List[Action], Value, Memory) = {
		  // TODO: Incomplete printing help (fill in as needed).
		  if (isFirstTry)
		    print(indent + "Possibilities are: ")
		  val action = (newPossibilities.head: @unchecked) match {
		    case Call(n, _) if functions(n).typ == UnitType =>  // For calls, print the call itself, not the result.
		      if (isFirstTry)
			println(iterableToString(newPossibilities, " or ", { s: Stmt => shortPrinter.stringOfStmt(s) }) + ".")
		      getActionFromUser(newPossibilities, indent)
		    case In(v, _) =>
		      if (isFirstTry)
			println(iterableToString(newPossibilities, " or ", { s: Stmt => shortPrinter.stringOfStmt(defaultExecutor.evaluate(memory, s)) }) + ".")
		      val prefix = shortPrinter.stringOfExpr(v) + " in "
		      getActionFromUser(newPossibilities, indent, prefix)
		    case _: Expr =>
		      if (isFirstTry)
			println(iterableToString(newPossibilities, " or ", { s: Stmt => shortPrinter.stringOfStmt(defaultExecutor.evaluate(memory, s)) }) + ".")
		      getActionFromUser(newPossibilities, indent)
		    case Assign(l, _) =>
		      if (isFirstTry)
			println(iterableToString(newPossibilities.asInstanceOf[List[Assign]], " or ", { a: Assign => shortPrinter.stringOfStmt(Assign(a.lhs, defaultExecutor.evaluate(memory, a.rhs))) }) + ".")
		      val prefix =
			if (holdsOverIterable(newPossibilities map { case Assign(l, _) => l case _ => throw new RuntimeException }, ((x: LVal, y: LVal) => x == y)))
			  shortPrinter.stringOfExpr(l) + " := "
			else
			  ""
		      getActionFromUser(newPossibilities, indent, prefix)
		  }
		  try {
		    val (actionResult, actionMemory) = defaultExecutor.execute(memory, action)
		    if (newPossibilities exists { p => yieldEquivalentResults(memory, p, actionResult, actionMemory, defaultExecutor) })
		      return (List(action), actionResult, actionMemory)
		    else {
		      println(indent + "You entered something that does not correspond to one of our possibilities.  This is either because your program is too complicated for us or because you made a typo.  Please try again.")
		      getActionText(false)
		    }
		  } catch {  // Catch if they entered something that causes a crash (e.g. a typo that gets interpreted as a nonexistent variable).
		    case _ =>
		      println(indent + "You entered something illegal.  Please try again.")
		      getActionText(false)
		  }
		}*/
		// Gets the current action from the user via the GUI.
		def getActionGUI(newPossibilities: List[Stmt]): (List[Stmt], List[Action], Value, Memory) = {
		  val actions = controller.getActions(newPossibilities.asInstanceOf[List[Action]], amFixing)
		  (actions: @unchecked) match {
		    case Actions(actions) => 
		      val (result, newMem) = defaultExecutor.execute(memory, actions.head)
		      println(indent + shortPrinter.stringOfValue(result))
		      (newPossibilities, actions, result, newMem)  // We return actions for the action and not actions.head because actions.head could be wrong (e.g. could be x < y when we want a < b, and this would give us wrong values).
		    case Fix if amFixing => controller.getFixInfo() match {
		      case code: CodeInfo => throw new FixedCode(Some(actualCurStmt), code)
		      case e: EndTrace => throw new SkipTrace(e, newStmts, newBlocks)
		      case x => throw new IllegalArgumentException(x.toString)
		    }
		    case Fix if !amFixing => throw new FixCode("you asked to change it", None)
		    case e: EndTrace => throw new SkipTrace(e, newStmts, newBlocks)
		    case FindMoreExpressions =>  // The user asked us to increase the search depth.
		      val newStmt = findMoreExpressions()
		      updateDisplay(memory, Some(newStmt), newStmts + (curStmt -> newStmt), newBlocks, false)
		      getActionGUI(newStmt.possibilities.asInstanceOf[List[Action]])
		  }
		}
		//val (actions, curResult, newMemory) = getActionText(true)
		val (newerPossibilities, actions, curResult, newMemory) = getActionGUI(newPossibilities)
		// Filter out possibilities ruled illegal by this new action (which will reduce the possibilities in the next iteration).
		val newStmt = possibilitiesToStmt(curHole, newerPossibilities filter { p => yieldEquivalentResults(memory, p, curResult, newMemory, defaultExecutor) })
		//println("Changed " + shortPrinter.stringOfStmt(curStmt) + " to " + shortPrinter.stringOfStmt(newStmt))
		numDisambiguations += 1
		updateHoleMaps(newStmt, actions, true)
		//continue = false  // TODO: Should we continue in this case or not?
		((newMemory, trace :+ curResult, newStmts + (curStmt -> newStmt), newBlocks), false)
	      }
	    case unseen: Unseen =>
	      updateDisplayShort()
	      println(indent + Console.RED + "**" + Console.RESET + "We have not seen this path before.  Please finish the trace.")
	      /*def getTraceText(): (Memory, List[Action], List[Stmt]) = {
		val actions = getTraceFromUser(indent)
		val (holes, newMemory) = actions.foldLeft((List[Stmt](), memory)){ case ((stmts, memory), cur) => (stmts :+ StmtEvidenceHole(List((cur, memory))), defaultExecutor.execute(memory, cur)._2) }
		val curStmts = codeGenerator.fillHoles(holes, false)
		(newMemory, actions, curStmts)
	      }*/
	      def getTraceGUI(): (Memory, List[Action], List[Stmt]) = {
		def getTrace[T](getter: Option[T]): T = getter match {
		  case Some(r) => r
		  case None => throw new FixCode("you asked to change it", None)
		}
		val canFix = !amFixing && (origStmts.size > 1 || origStmts.head != actualCurStmt)
		val (actions, curStmts, newMemory) = unseen match {
		  case _: UnseenStmt => controller.getStmtTrace(memory, canFix) match {
		    case StmtInfo(s) => s
		    case Fix => throw new FixCode("you asked to change it", None)
		    case e: EndTrace => throw new SkipTrace(e, newStmts, newBlocks)
		  }
		  case _: UnseenExpr => controller.getExprTrace(memory, canFix) match {
		    case ExprInfo((entered, code, m)) => (List(entered), List(code), m)
		    case Fix => throw new FixCode("you asked to change it", None)
		    case e: EndTrace => throw new SkipTrace(e, newStmts, newBlocks)
		  }
		}
		println(shortPrinter.stringOfStmts(actions, indent))
		(newMemory, actions, curStmts)
	      }
	      //val (newMemory, actions, curStmts) = getTraceText()
	      val (newMemory, actions, curStmts) = getTraceGUI()
	      val finalCurStmts = curStmts/*(unseen, curStmts) match {
		case (unseen: UnseenExpr, condition :: Nil) => conditionEvidence.get(unseen) match {
		  case Some(evidence) =>
		    conditionEvidence -= unseen
		    List(condition match {
		      case PossibilitiesHole(possibilities) =>
			println(iterableToString(evidence, ", ", (e: (Value, Memory)) => shortPrinter.stringOfValue(e._1) + " @ " + shortPrinter.stringOfMemory(e._2)))
			val newCondition = possibilitiesToExpr(getValidChoices(possibilities.map{ _.asInstanceOf[Expr] }, evidence), throw new SolverError("Pruned conditional " + shortPrinter.stringOfStmt(condition) + " too far"))
			println("***** Went from " + shortPrinter.stringOfStmt(condition) + " to " + shortPrinter.stringOfStmt(newCondition))
			newCondition
		      case _ => println("a");condition
		    })
		  case _ => curStmts
		}
		case _ => curStmts
	      }*/
	      numUnseensFilled += 1
	      if (pruneAfterUnseen)  // TODO: It would be nice to not disable this pruning when synthesizing the code for a loop from its first iteration.  But then it's not obvious how to generate inputs (since I don't have the full program).
		pruneBeforeNextDisambiguation = true
	      ((newMemory, trace ++ actions, newStmts, newBlocks + (curStmt -> finalCurStmts)), false)
	    case _: Expr | Assert(_) | Assume(_) | Println(_) | Assign(_, _) => 
	      val printStmt = actualCurStmt match {
		case Assign(l, r) => Assign(l, defaultExecutor.evaluate(memory, r))  // Print the executed assignment.
		case _ => actualCurStmt
	      }
	      myprintln(shortPrinter.stringOfStmt(printStmt))
	      val newMemoryOpt = {
		val resOpt = try { Some(defaultExecutor.execute(memory, actualCurStmt)) } catch { case _ if amFixing => None }
		resOpt match {
		  case Some((v, m)) => 
		    if (amFixing)
		      doFixStepShort(Some((m, actualCurStmt, v)))
		    Some(m)
		  case None =>
		    doFixStepShort(None)
		    None
		}
	      }
	      ((newMemoryOpt.get, trace :+ actualCurStmt.asInstanceOf[Action], newStmts, newBlocks), false)
	    case If(condition, thenBranch, _, elseBranch) =>   // TODO: Does not work for else if branches.
	      val (conditionAction, newerStmts, newerBlocks, conditionResult, conditionMemory) = conditionHelper(memory, condition, newStmts, newBlocks)
	      val body = if (conditionResult) thenBranch else elseBranch
	      val ((newMemory, actions, newestStmts, newestBlocks), breakHit) = executeWithHelpFromUserHelper(conditionMemory, body, newerStmts, newerBlocks, indent + "  ", printFn)
	      ((newMemory, trace :+ Conditional(conditionAction.asInstanceOf[Expr], actions), newestStmts, newestBlocks), breakHit)
	    case Loop(condition, body) =>
	      def handleLoop(memory: Memory, newStmts: IMap[Stmt, Stmt], newBlocks: IMap[Stmt, List[Stmt]], breakHit: Boolean): (Memory, List[(Action, List[Action])], IMap[Stmt, Stmt], IMap[Stmt, List[Stmt]], Boolean) = {
		val (conditionAction, newerStmts, newerBlocks, conditionResult, conditionMemory) = conditionHelper(memory, condition, newStmts, newBlocks)
		if (!conditionResult || breakHit)
		  return (conditionMemory, List((conditionAction, Nil)), newerStmts, newerBlocks, breakHit)
		val ((newMemory, curIter, newestStmts, newestBlocks), newBreakHit) = executeWithHelpFromUserHelper(conditionMemory, body, newerStmts, newerBlocks, indent + "  ", printFn)
		// Recurse for the next iteration
		val (finalMemory, restIter, finalStmts, finalBlocks, _) = handleLoop(newMemory, newestStmts, newestBlocks, newBreakHit)
		(finalMemory, (conditionAction, curIter) :: restIter, finalStmts, finalBlocks, false)
	      }
	      val (newMemory, actions, newerStmts, newerBlocks, _) = handleLoop(memory, newStmts, newBlocks, false)
	      ((newMemory, trace :+ Iterate(actions), newerStmts, newerBlocks), false)
	    case Break => 
	      myprintln("break")
	      ((memory, trace :+ Break, newStmts, newBlocks), true)
	    case UnorderedStmts(stmts) =>
	      myprintln("unordered")
	      val result = stmts map { s => executeWithHelpFromUserHelper(memory, List(s), newStmts, newBlocks, indent + "  ", printFn)._1 }
	      val actions = result flatMap { _._2 }
	      val actionStmt = UnorderedStmts(actions)
	      val newMemory = {  // We cannot simply execute actionStmt, since it might, for example, have a possibilities hole with two different LHS.  So we manually combine the memories.
		val clonedMem = memory.clone
		val (objs, arrs) = clonedMem.getObjectsAndArrays()  // We have to call this before we start modifications as things can become orphaned.
		val diffs = result map { _._1 } map { m => diffMemories(memory, m) }
		diffs.foldLeft(clonedMem){ case (acc, (newVars, modObjs, modArrs)) => {
		  newVars foreach { acc += _ }
		  modObjs foreach { case ((id, f), v) => objs(id).fields(f) = v }
		  modArrs foreach { case ((id, i), v) => arrs(id).array(i) = v }
		  acc
		} }
	      }
	      // We manually combine the new statements and keep only things that are different from what we knew before this unordered stmt.
	      val newerStmts = result.map{ _._3 }.foldLeft(newStmts){ (acc, cur) => cur.foldLeft(acc){ (acc, kv) => if (!acc.contains(kv._1) || newStmts(kv._1) != kv._2) acc + kv else acc } }
	      val newerBlocks = result.map{ _._4 }.foldLeft(newBlocks){ (acc, cur) => cur.foldLeft(acc){ (acc, kv) => if (!acc.contains(kv._1) || newBlocks(kv._1) != kv._2) acc + kv else acc } }
	      ((newMemory, trace :+ actionStmt, newerStmts, newerBlocks), false)
	  }
	  // TODO: I should get rid of this method and just put the try/catch around all of handleStmt itself.
	  def doHandleStmt(actualCurStmt: Stmt): ((Memory, List[Action], IMap[Stmt, Stmt], IMap[Stmt, List[Stmt]]), Boolean) = try {
	    handleStmt(actualCurStmt)
	  } catch {
	    case FoundMoreExpressions(newStmt) => doHandleStmt(newStmt)
	  }
	  doHandleStmt(actualCurStmt)
	}
      }}
    }
    val (finalMem, actions, newStmts, newBlocks) = executeWithHelpFromUserHelper(memory, origStmts, IMap.empty, IMap.empty, "")._1
    if (amFixing && !foundMoreExpressions)
      doFixStep(finalMem, None, newStmts, newBlocks, None)
    (actions, getNewStmts(origStmts, newStmts, newBlocks), finalMem)
  }
  protected[graphprog] def executeLoopWithHelpFromUser(memory: Memory, origStmts: List[Stmt], pruneAfterUnseen: Boolean): LoopIntermediateInfo = {
    try {
      StmtInfo(executeWithHelpFromUser(memory, origStmts, pruneAfterUnseen, false, None))
    } catch {
      case SkipTrace(e: EndTrace, _, _) => e
    }
  }
  private def getTraceWithHelpFromUser(code: List[Stmt], inputs: List[(String, Value)], pruneAfterUnseen: Boolean, amFixing: Boolean, failingStmt: Option[Stmt], otherBranch: Option[(Stmt, UnknownJoinIf)] = None): List[Stmt] = {
    controller.getOptions().dumpBackupData match {
      case Some(filename) => dumpBackupData(filename, controller, code)
      case None =>
    }
    allInputs :+= inputs  // This might add duplicate inputs (when we re-do one to find a join) but comparing inputs for equality is a pain, since they're from different executions and so we can't just compare by ids.
    controller.clearScreen()
    breakpoints = Nil
    breakpointsToAdd = Nil
    breakpointsToRemove = Nil
    println("We need another example to help us find your program.  " + getHoleInfo(code))
    println("Please help us finish this trace.  We currently have the following program:\n" + longPrinter.stringOfProgram(Program(name, typ, inputTypes, functions, objectTypes, code)))
    print(longPrinter.stringOfTrace(Trace(name, typ, inputs, functions, objectTypes, Nil)))
    def recurse(newCode: => List[Stmt], reason: String): List[Stmt] = {  // newCode is passed by need so we can print the abort before executing it
      println("Aborting trace to " + reason + ".  We'll continue with this or another trace if necessary when this finishes.")
      val (newerCode, newInput) = getNextInput(newCode, Some(inputs))
      newInput match {
	case Some(newInput) => return getTraceWithHelpFromUser(newerCode, newInput, pruneAfterUnseen, amFixing, failingStmt, otherBranch)
	case None => return newerCode
      }
    }
    try {
      val mem = new Memory(inputs)
      if (amFixing) {
	assert(breakpoints.isEmpty)
	controller.updateDisplay(mem, code, None, true, Nil, failingStmt)
      }
      val newCode = executeWithHelpFromUser(mem, code, pruneAfterUnseen, amFixing, failingStmt, otherBranch)._2
      println("Thank you for giving us this trace.  We'll get to work now.")
      finishedInputs += inputs
      newCode
    } catch {
      case FixCode(reason, curStmt) => recurse(fixCode(code, reason, inputs, curStmt), "fix the code")
      case PruneCode(curStmts) => recurse(prunePossibilities(curStmts), "prune the code")
      case FixedCode(curStmt, newCode) => (curStmt, newCode.code) match {
	case (Some(realCurStmt), List(uif: UnknownJoinIf)) => allInputs.find{ input => advanceIteratorExecutorToPoint(code, curStmt, input, None).hasNext } match {
	  case Some(newInput) =>  // We found no legal join points before, so we re-execute the original branch we saw to find the exact join.
	    println("Aborting trace to fill a conditional.  We'll continue with this or another trace if necessary when this finishes.")
	    controller.displayMessage("Aborting trace to fill a conditional.  We'll continue with this or another trace if necessary when this finishes.")
	    val newerCode = getTraceWithHelpFromUser(code, newInput, pruneAfterUnseen, amFixing, None, Some((realCurStmt, uif)))
	    prune(newerCode, 0, Some(inputs)).getOrElse{ newerCode }  // If this input has no successful path, the pruning will continue it.  If it has a successful path but needs disambiguation, we drop it and try to find something else.
	  case None => throw new SolverError("Cannot find previous input that brings me to a branch of a conditional I've already seen.")
	}
	case _ =>
	  println("Got new code.")
	  newCode.code  // TODO/FIXME: Instead continue with trace?
      }
      case SkipTrace(EndTrace(sameInput, saveChanges), newStmts, newBlocks) =>
	println((if (sameInput) "Restarting" else "Aborting") + " current trace and " + (if (saveChanges) "saving" else "discarding") + " changes.")
	val nextCode =
	  if (saveChanges)
	    getNewStmts(code, newStmts, newBlocks)
	  else
	    code
	val (finalCode, newInput) =
	  if (sameInput)
	    (nextCode, Some(inputs))
	  else
	    getNextInput(nextCode, None)
	newInput match {
	  case Some(newInput) => getTraceWithHelpFromUser(finalCode, newInput, pruneAfterUnseen, amFixing, if (sameInput) failingStmt else None, otherBranch)
	  case None => finalCode
	}
    }
  }

  // Be careful to not create new things unless we need them, since that breaks reference equality.
  def getNewStmts(oldStmts: List[Stmt], newStmts: PartialFunction[Stmt, Stmt], newBlocks: PartialFunction[Stmt, List[Stmt]]): List[Stmt] = {
    def getNewExpr(e: Expr): Expr = singleton(getNewStmt(e)).asInstanceOf[Expr]
    def getNewStmts(s: List[Stmt]): List[Stmt] = {
      val newStmts = s flatMap getNewStmt
      if (s.size == newStmts.size && s.zip(newStmts).forall{ t => t._1 eq t._2 })
	s
      else
	newStmts
    }
    def getNewStmt(s: Stmt): List[Stmt] = s match {
      case _ if newStmts isDefinedAt s => List(newStmts(s))
      case _ if newBlocks isDefinedAt s => getNewStmts(newBlocks(s))
      case If(c, t, ei, e) =>
	val newIf = If(getNewExpr(c), getNewStmts(t), ei.map{ b => (getNewExpr(b._1), getNewStmts(b._2)) }, getNewStmts(e))
	if (newIf.condition.eq(c) && newIf.thenBranch.eq(t) && newIf.elseBranch.eq(e) && newIf.elseIfPaths.zip(ei).forall{ t => t._1._1.eq(t._2._1) && t._1._2.eq(t._2._2) })
	  List(s)
	else
	  List(newIf)
      case Loop(c, b) =>
	val newLoop = Loop(singleton(getNewStmt(c)), getNewStmts(b))
	if (newLoop.condition.eq(c) && newLoop.body.eq(b))
	  List(s)
	else
	  List(newLoop)
      case UnorderedStmts(stmts) =>
	val newStmts = getNewStmts(stmts)
	if (newStmts eq stmts)
	  List(s)
	else
	  List(UnorderedStmts(newStmts))
      case _ => List(s)
    }
    getNewStmts(oldStmts)
  }

  /**
   * Checks whether a program is complete, i.e. has no holes.
   */
  private def isComplete(stmts: List[Stmt]): Boolean = {
    def isCompleteStmt(stmt: Stmt): Boolean = stmt match {
      case _: Hole => false
      case If(c, t, ei, e) => isCompleteStmt(c) && isComplete(t) && isComplete(e) && ei.forall{ t => isComplete(t._2) }
      case Loop(c, b) => isCompleteStmt(c) && isComplete(b)
      case UnorderedStmts(s) => isComplete(s)
      case _ => true
    }
    stmts forall isCompleteStmt
  }

  /**
   * Returns a string with statistics about the holes in the
   * program.
   */
  private def getHoleInfo(code: List[Stmt]): String = {
    def getHoles(stmts: List[Stmt]): List[Hole] = {
      def getHoleInStmt(stmt: Stmt): List[Hole] = stmt match {
	case h: Hole => List(h)
	case If(c, t, ei, e) => getHoleInStmt(c) ++ getHoles(t) ++ getHoles(e) ++ ei.flatMap{ t => getHoles(t._2) }
	case Loop(c, b) => getHoleInStmt(c) ++ getHoles(b)
	case UnorderedStmts(s) => getHoles(s)
	case _ => Nil
      }
      stmts flatMap getHoleInStmt
    }
    val holes = getHoles(code)
    val numUnseen = holes.filter{ case _: Unseen => true case _ => false }.size
    val possibilities = holes collect { case PossibilitiesHole(p) => p.size }
    val variants = possibilities.foldLeft(1){ _ * _ }
    "This program has " + numUnseen + " unseen " + pluralize("statement", "statements", numUnseen) + " and " + possibilities.size + " possibility " + pluralize("hole", "holes", possibilities.size) + " with " + possibilities.sum + " total possibilities representing " + variants + " variant " + pluralize("program", "programs", variants) + "."
  }

  // TODO: Really, for this use I want "all holes whose first occurence always precedes those of unseen stmts on the given input".  That would let me prune extra holes (e.g. on rbInsert when we don't enter the loop, I could prune the final tree.root.color assignment, which I currently can't do here but can do with an automatic interactive trace).
  /**
   * Returns a tuple whose first element contains holes whose first occurrence always precedes those of all unseen stmts,
   * whose second element contains unseen holes that are the first unseen hole on some path,
   * and whose third element contains holes whose first occurrence can follow those of an unseen statement.
   * Note that this is probably not precise.  But if any elements that should be in the first part are accidentally
   * put in the third, then we just cannot prune them.  And if any elements that should be in the third part are
   * put in the first, then we should remove them later in the pruning process.
   */
  private def classifyHoles(l: List[Stmt]): (List[PossibilitiesHole], List[Unseen], List[Hole]) = {
    /**
     * For these functions, the second and third elements of the tuple are as above.  The first is as
     * the first above but separates holes that are not inside the body of a conditional from those that are.
     */
    type InnerType = ((List[PossibilitiesHole], List[PossibilitiesHole]), List[Unseen], List[Hole], Boolean)
    def combiner(x: InnerType, y: InnerType): InnerType = ((x._1._1 ++ y._1._1, x._1._2 ++ y._1._2), x._2 ++ y._2, x._3 ++ y._3, x._4 || y._4)
    def getList(l: List[Stmt], seenUnseen: Boolean, isInLoop: Boolean): InnerType = {
      def getStmt(acc: InnerType, s: Stmt, isInLoop: Boolean): InnerType = {
	val cur = s match {
	  case h: PossibilitiesHole => if (acc._4) ((Nil, Nil), Nil, List(h), false) else ((List(h), Nil), Nil, Nil, false)
	  case h: Unseen => 
	    if (isInLoop)  // When we see an unseen statement inside a loop, mark that everything before it in a condition could occur after it.  Note the short circuit since we modify acc.
	      return ((acc._1._1, Nil), List(h), acc._1._2 ++ acc._3, true)
	    else
	      ((Nil, Nil), List(h), Nil, true)
	  case If(c, t, ei, e) => 
	    val condition = getList(List(c), acc._4, isInLoop)
	    val bodies = (t :: e :: ei.map { t => t._1 :: t._2 }).map{ x => getList(x, acc._4, isInLoop) }.reduceLeft(combiner)
	    val hasUnseen = condition._4 || bodies._4
	    val result = ((condition._1._1, condition._1._2 ++ bodies._1._1 ++ bodies._1._2), condition._2 ++ bodies._2, condition._3 ++ bodies._3, hasUnseen)  // Mark what happened in the bodies as being inside a conditional, but do not so mark the original condition.
	    if (hasUnseen && isInLoop)  // When this if contains an unseen statement and is in a loop, mark that everything that came before the if and was in a conditional could occur after an unseeen statement.  Note the short circuit since we modify acc.
	      return ((acc._1._1 ++ result._1._1, result._1._2), acc._2 ++ result._2, acc._1._2 ++ acc._3 ++ result._3, true)
	    else if (condition._4)
	      ((condition._1._1, condition._1._2), condition._2 ++ bodies._2, condition._3 ++ bodies._1._1 ++ bodies._1._2 ++ bodies._3, hasUnseen)
	    else
	      result
	  case Loop(c, b) =>
	    val condition = getStmt(acc, c, isInLoop)
	    val body = getList(b, acc._4, true)
	    combiner(condition, body)
	  case UnorderedStmts(s) => getList(s, acc._4, isInLoop)
	  case _ => ((Nil, Nil), Nil, Nil, false)
	}
	if (acc._4)  // If we've already seen an unseen statement, mark what we just saw as following it.
	  (acc._1, acc._2, acc._3 ++ cur._1._1 ++ cur._1._2 ++ cur._2 ++ cur._3, true)
	else
	  combiner(acc, cur)
      }
      l.foldLeft(((List[PossibilitiesHole](), List[PossibilitiesHole]()), List[Unseen](), List[Hole](), seenUnseen)){ (acc, cur) => getStmt(acc, cur, isInLoop) }
    }
    val (before, first, after, _) = getList(l, false, false)
    (before._1 ++ before._2, first, after)
  }

  // TODO/FIXME: I should really also show these input/output pairs to the user and ask if they're correct.  For example, if we don't have a postcondition, this might be very necessary.
  private def checkProgram(code: List[Stmt]): Option[(List[(String, Value)], Boolean)] = {
    /*@tailrec */def doCheck(curRound: Int): Option[(List[(String, Value)], Boolean)] = {
      if (curRound == NUM_FINAL_CHECKS)
	None
      else {
	findFirstRandomInput(curRound / NUM_FINAL_CHECKS.toDouble, None) match {
	  case None => None
	  case inputOpt @ Some(input) =>
	    val (result, resMem) = try { executeProgram(simpleHoleHandlerExecutor, input, code) } catch { case _: Throwable => return Some((input, true)) }
	    if (isErrorOrFailure(result))
	      return Some((input, true))
	    postcondition match {
	      case Some(p) if !p(input.toMap, resMem.toMap, result) => return Some((input, false))
	      case _ => return doCheck(curRound + 1)
	    }
	}
      }
    }
    doCheck(0)
  }

  // TODO: Improve implementation by looking at the exprs themselves.  This is just a hack.
  private def guessHole(h: PossibilitiesHole): Stmt = h.possibilities.reduceLeft{ (x, y) => if (shortPrinter.stringOfStmt(x).size <= shortPrinter.stringOfStmt(y).size) x else y }

  // isPartialTrace: Whether or not this sequence of actions can end in the middle of a trace (e.g. with only the first iteration of a loop that in truth has more than one iteration.).
  protected[graphprog] def genProgramAndFillHoles(memory: Memory, actions: List[Action], isPartialTrace: Boolean, loops: TMap[Iterate, Loop]): List[Stmt] = {
    //println(shortPrinter.stringOfStmts(actions))
    val stmts = genProgramFromCompleteTraces(actions, memory, loops)
    //println(shortPrinter.stringOfStmts(stmts))
    val filledStmts = codeGenerator.fillHoles(stmts, isPartialTrace)
    //println(shortPrinter.stringOfStmts(filledStmts))
    filledStmts
  }
  protected[graphprog] def genProgramAndFillHoles(memory: Memory, expr: Expr): Expr = codeGenerator.fillExprHole(ExprEvidenceHole(List((expr, memory))))

  /* Main synthesis methods. */

  protected[graphprog] def synthesize(initialTrace: Trace): Program = {
    println(shortPrinter.stringOfStmts(initialTrace.actions))
    allInputs :+= initialTrace.inputs
    val stmts = genProgramAndFillHoles(new Memory(initialTrace.inputs), initialTrace.actions, false, IMap.empty)
    synthesizeCode(stmts)
  }
  protected[graphprog] def synthesizeCode(stmts: List[Stmt]): Program = {
    @tailrec def synthesizeRec(code: List[Stmt]): (List[Stmt], Boolean) = {
      val prunedCode = prunePossibilities(code)
      val (furtherPrunedCode, inputs) = getNextInput(prunedCode, None)
      val complete = isComplete(furtherPrunedCode)
      if (complete || inputs.isEmpty) {
	checkProgram(furtherPrunedCode) match {
	  case None => (furtherPrunedCode, complete)
	  case Some((i, true)) => synthesizeRec(getTraceWithHelpFromUser(furtherPrunedCode, i, true, false, None))
	  case Some((i, false)) => synthesizeRec(fixCode(furtherPrunedCode, "the displayed input fails the correctness condition", i, None))
	}
      } else
	synthesizeRec(getTraceWithHelpFromUser(furtherPrunedCode, inputs.get, true, false, None))
    }
    println("Initial statements:\n" + shortPrinter.stringOfStmts(stmts))
    val (code, isFinished) = synthesizeRec(stmts)
    controller.clearDisplay(code)
    val numTraces = allInputs.size
    numUnseensFilled -= 1
    val numQueries = numDisambiguations + numUnseensFilled
    println(Console.RED + "***" + Console.RESET + "Asked " + numQueries + " " + pluralize("query", "queries", numQueries) + " (" + numDisambiguations + " disambiguation and " + numUnseensFilled + " unseen)" + " in " + numTraces + " " + pluralize("trace", "traces", numTraces) + " (" + allInputs.toSet.size + " unique) with " + numCodeFixes + " " + pluralize("fix", "fixes", numCodeFixes) + ".")
    for (input <- allInputs)
      println(longPrinter.stringOfInputs(input, ";"))
    // TODO: Handle this case better.  Should I display program with holes or the guessed one?
    val finalProgram = Program(name, typ, inputTypes, functions, objectTypes, code)
    if (isFinished) {
      controller.clearDisplay(code)
      controller.displayMessage("Here is the complete program.")
      finalProgram
    } else {
      val guessedStmts = getNewStmts(code, _ match { case h: PossibilitiesHole => guessHole(h) }, IMap.empty)
      println("Guessing:\n" + longPrinter.stringOfStmts(guessedStmts))
      controller.clearDisplay(guessedStmts)
      controller.displayMessage("Here is the program.")
      throw new SolverError("Unable to find a random input that will help us on the following program.\n" + getHoleInfo(code) + "\n" + longPrinter.stringOfProgram(finalProgram)) with FastException
    }
  }
  def synthesize(input: List[(String, Value)]): Program = {
    val stmts = getTraceWithHelpFromUser(List(UnseenStmt()), input, false, false, None)
    synthesizeCode(stmts)
  }

  /**
   * Prunes the given program.  The basic algorithm is to generate an input,
   * explore all paths with that input, and remove possibilities that never
   * have successful runs.  The complications are that
   * - we must treat unseen statements as successful and cannot prune holes
   * that follow them
   * - we can only prune holes that we see on all successful runs, as
   * otherwise it's possible that the only desired run is one that does
   * not touch this hole, and we do not want to prune based on undesired
   * runs.
   * Note that this function can be very slow, as in the worse case it must
   * explore every path through the program, but there are many optimizations
   * that speed it up in practice.
   */
  private def prunePossibilities(code: List[Stmt]): List[Stmt] = {
    @tailrec def pruneLoop(code: List[Stmt], curRound: Int): List[Stmt] = {
      if (curRound == NUM_PRUNING_ROUNDS || isComplete(code))
	code
      else {
	prune(code, curRound / NUM_PRUNING_ROUNDS.toDouble, None) match {
	  case Some(newCode) => pruneLoop(newCode, curRound + 1)
	  case None => code
	}
      }
    }
    // First, do some fast input pruning to try to reduce the space of the input size, and then do slower full pruning, then do some fast input pruning again to take advantage of any new possibilities the full pruning might have pruned.
    doInputPruning(pruneLoop(doInputPruning(code), 0))
  }

  private def doInputPruning(code: List[Stmt]) = (0 until NUM_PRUNING_ROUNDS).foldLeft(code){ (code, i) => val input = findFirstNewRandomInput(code, i / NUM_PRUNING_ROUNDS.toDouble); if (input.isDefined) simpleInputPruning(code, input.get)._1 else code }

    // Returns None if it cannot prune the program and there is no point in trying again (e.g. it cannot generate a good input).
    private def prune(code: List[Stmt], progress: Double, inputOpt: Option[List[(String, Value)]]): Option[List[Stmt]] = {
      import scala.collection.mutable.HashSet
      case object AbortOnUnknown extends Value with IsErrorOrFailure
      case object TimeoutValue extends Value with IsErrorOrFailure
      // Get an input that (a) does not fail the precondition and (b) differentiates between at least one possibility.
      val input = inputOpt.getOrElse{ findFirstNewRandomInput(code, progress).getOrElse{ return None } }
      // Do some (fast) simple input pruning, which if it works can greatly reduce the search space.
      val prunedCode = simpleInputPruning(code, input)._1
      val newPossibilitiesMap = {
	var legalHoles = classifyHoles(prunedCode)._1.toSet
	//println("Initial legal holes: " + iterableToString(legalHoles, ", ", (h: PossibilitiesHole) => shortPrinter.stringOfHole(h)))
	if (legalHoles.isEmpty)
	  return None
	//println("Beginning pruning with input: " + shortPrinter.stringOfInputs(input, ".  "))
	val successfulChoices = Map[PossibilitiesHole, MSet[Stmt]]()
	val path = ListBuffer[(PossibilitiesHole, ListBuffer[List[Stmt]])]()
	val curHolesSeen = MSet.empty[PossibilitiesHole]
	var numPaths = 0
	var numSuccessfulPaths = 0
	def holeHandler(memory: Memory, hole: Hole): Stmt = {
	  // Group the possibilities into equivalence classes
	  def getEquivalences(possibilities: Iterable[Stmt]): ListBuffer[List[Stmt]] = {
	    val goods = ListBuffer.empty[(Value, Memory, ListBuffer[Stmt])]
	    val fails = ListBuffer.empty[Stmt]
	    possibilities.foreach{ cur => {
	      try {
		val (pRes, pMem) = defaultExecutor.execute(memory, cur)
		goods.find{ s => areEquivalent(pRes, s._1, pMem, s._2) } match {
		  case Some(s) => s._3 += cur
		  case None => goods += ((pRes, pMem, ListBuffer[Stmt](cur)))
		}
	      } catch {
		case _: Throwable => fails += cur  // Put failing possibilities together, since they could be in a loop and made failing by something that comes after them.
	      }
	    } }
	    val all = goods.map{ _._3.toList }
	    if (fails.nonEmpty)  // Don't add fails if it is empty or we get tons of bogus paths and slowdown.
	      all += fails.toList
	    all
          }
	  if (Thread.currentThread().isInterrupted())  // Manually check for interruption and timeout.  This won't catch infinite loops with no holes, though.
	    throw new java.util.concurrent.TimeoutException
	  hole match {
	    case h @ PossibilitiesHole(possibilities) =>
	      val result = path.find{ h == _._1 } match {
		case None =>
	          val equivalences = getEquivalences(possibilities)
		  path += (h -> equivalences)
		  equivalences.head.head
		case Some(v @ (_, groups)) =>
		  if (curHolesSeen contains h) {  // If this is the first time we've seen this hole on this path but we've seen it on another path (since we have a group for it), there's no need to split the current group, since this is the first time we've seen it on the path.
		    val newEquivalences = getEquivalences(groups.remove(0))  // Split the current equivalence class to handle loops and recursion.
		    groups prependAll newEquivalences
		  }
		  groups.head.head
	      }
	      //println(shortPrinter.stringOfStmt(h) + "  -->  " + shortPrinter.stringOfStmt(result))
	      curHolesSeen += h
	      result
	    case _: Unseen => AbortOnUnknown  // Stop searching when we hit an unseen statement.
	    case _: EvidenceHole => throw new IllegalArgumentException(hole.toString)
	  }
	}
	val executor = new Executor(functions, longPrinter, holeHandler) {
	  override def doLoopBody(memory: Memory, l: Loop): Value = {  // Do a simple check for a loop with no chanegs to memory and do a fast timeout if we're in one.
	    val initMem = memory.clone
	    val v = super.doLoopBody(memory, l)
	    if (memoriesAreEqual(memory, initMem))
	      TimeoutValue
	    else
	      v
	  }
	}
	def programSucceeded(result: Value, resMap: IMap[String, Value]): Boolean = !isErrorOrFailure(result) && (postcondition match { case Some(p) => p(input.toMap, resMap, result) case _ => true })
	//val startTime = System.currentTimeMillis()
	// Returns (has at least one path that was successful or hit an unseen stmt, can prune)
	@tailrec def explorePossibilitySpace(): (Boolean, Boolean) = {
	  //println("Exploring: " + path)
	  curHolesSeen.clear()
	  val result = executeWithTimeout(executeProgram(executor, input, prunedCode), TIMEOUT)
	  //println("Explored: " + iterableToString(path, ", ", (t: (PossibilitiesHole, ListBuffer[List[Stmt]])) => "{" + iterableToString(t._2, ",", (t: List[Stmt]) => "{" + iterableToString(t, ",", (s: Stmt) => shortPrinter.stringOfStmt(s)) + "}") + "}") + " and got " + result)
	  numPaths += 1
	  result match {
	    case NormalResult((result, resMem)) if result == AbortOnUnknown || programSucceeded(result, resMem.toMap) =>
	      //println("Successful path")
	      numSuccessfulPaths += 1
	      // Filter out holes that we didn't see on this run.  We can't prune them since this run could be the only success for this input.
	      legalHoles = legalHoles intersect path.map{ _._1 }.toSet
	      // Mark each statement chosen on a successful path.  But we only mark legal holes to save effort, since we can't prune the rest.
	      path foreach { case (h, goods) if legalHoles.contains(h) => successfulChoices.getOrElseUpdate(h, HashSet[Stmt]()) ++= goods.head case _ => () }
	      // Optimizations: stop the search if we cannot possibly eliminate anything else.
	      if (legalHoles.isEmpty)
		return (true, false)
	      if (legalHoles.forall{ h => successfulChoices.contains(h) && successfulChoices(h).size == h.possibilities.size })
		return (true, false)
	    //case Timeout => println("Timeout on path " + iterableToString(path, ", ", (t: (PossibilitiesHole, ListBuffer[List[Stmt]])) => shortPrinter.stringOfStmts(t._2(0))))
	    // Note that I'm counting executions that timeout as failing which isn't sound but hopefully won't be a problem.
	    case _ => ()
	  }
	  @tailrec def tryToBacktrack() {
	    if (!path.isEmpty) {
	      val (hole, groups) = path.remove(path.size - 1)
	      groups.remove(0)
	      if (groups.nonEmpty)
		path += (hole -> groups)
	      else
		tryToBacktrack()
	    }
	  }
	  // Optimization: if this path uses a known-successful possibility for each legal hole, then we do not need to search through all possible values for non-legal holes on the similar path as doing so cannot help us.  So we prune the non-legal holes at the end and backtrack on the last legal hole.
	  // This optimization is very important: it drastically speeds things up e.g. on leftRotate.
	  if (legalHoles.forall{ h => path.find{ h == _._1 } match { case Some((_, groups)) => successfulChoices.get(h) match { case Some(good) => groups.head.forall { s => good contains s } case None => false } case None => false } })
	    while (!path.isEmpty && !legalHoles.contains(path.last._1))
	      path.remove(path.size - 1)
	  tryToBacktrack()
	  if (!path.isEmpty)
	    explorePossibilitySpace()
	  else
	    (numSuccessfulPaths > 0, true)
	}
	val (hasSuccessfulPath, canPrune) = explorePossibilitySpace()
	//println("Explored " + numPaths + " paths")
	//println("Explored " + numPaths + " paths in " + (new java.text.SimpleDateFormat("mm:ss.S")).format(new java.util.Date(System.currentTimeMillis() - startTime)))
	if (!hasSuccessfulPath) {
	  val newerCode = doInputPruning(prunedCode)  // First try to do input pruning, as if it finds something that needs a fix, it's a crash, so we're guaranteed no disambiguation questions before it, while this input might have disambiguation questions.
	  if (newerCode == prunedCode)
	    return Some(fixCode(prunedCode, "the program has no successful paths on this input", input, None))
	  else
	    return Some(newerCode)
	} else if (canPrune)
	  successfulChoices.filterKeys{ h => legalHoles contains h }.toMap.mapValues{ _.toSet }
	else
	  IMap[PossibilitiesHole, Set[Stmt]]()
      }
      //println(newPossibilitiesMap)
      Some(updateHoles(prunedCode, newPossibilitiesMap, "full"))
    }

  /**
   * Prunes the given program by executing it on the given input as far as we
   * can (until we get to a hole that splits into more than one direction) and
   * removes impossible possibilities (e.g. ones that cause a crash) on holes
   * we have seen.  Note that this is very fast, as it mostly just executes
   * the program.
   */
  private def simpleInputPruning(code: List[Stmt], input: List[(String, Value)]): (List[Stmt], Boolean) = {
    //println("Beginning simple input pruning with input " + shortPrinter.stringOfInputs(input, ".  "))
    case object UnableToContinue extends Value with IsErrorOrFailure
    case object UnseenHit extends Value with IsErrorOrFailure
    case class ErrorHit(hole: Stmt) extends Value with IsErrorOrFailure
    val newPossibilitiesMap = Map[PossibilitiesHole, List[Stmt]]()
    def holeHandler(memory: Memory, hole: Hole): Stmt = hole match {
      case hole @ PossibilitiesHole(p) =>
	val possibilities = newPossibilitiesMap.getOrElse(hole, p)
	val results = possibilities flatMap { s => try { val (v, m) = defaultExecutor.execute(memory, s); if (isErrorOrFailure(v)) Nil else List((s, v, m)) } catch { case _: Throwable => Nil } }
        if (results.size == 0)
	  return ErrorHit(hole)
	if (results.size < possibilities.size)
	  newPossibilitiesMap += (hole -> results.map{ _._1 })
        if (holdsOverIterable(results, (x: (Stmt, Value, Memory), y: (Stmt, Value, Memory)) => areEquivalent(x._2, y._2, x._3, y._3)))
	  results.head._1
	else
	  UnableToContinue
      case _: Unseen => UnseenHit
      case _: EvidenceHole => throw new IllegalArgumentException(hole.toString)
    }
    val executor = new Executor(functions, longPrinter, holeHandler)
    val (result, resMem) = try { executeProgram(executor, input, code) } catch { case _: Throwable => (ErrorConstant, new Memory(input)) }
    val errorOrFailure = isErrorOrFailure(result)
    if (result != UnseenHit && result != UnableToContinue && (errorOrFailure || (postcondition match { case Some(p) => !p(input.toMap, resMem.toMap, result) case _ => false }))) {
      val (reason, stmt) = result match {
	case ErrorHit(h) => ("it fails on the displayed input", Some(h))
	case _ => ("the displayed input fails", None)
      }
      simpleInputPruning(fixCode(code, reason, input, stmt), input)
    } else if (newPossibilitiesMap.isEmpty)
      (code, errorOrFailure)
    else
      (updateHoles(code, newPossibilitiesMap.toMap.mapValues{ _.toSet }, "fast"), errorOrFailure)
  }

  /**
   * Modifies the given program by updating holes in the given map.
   * newPossibilitiesMap: Map from hole to possibilities.  If a hole is mapped
   * to multiple possibilities, we replace the hole with a hole using the new
   * possibilities.  If there is only one possibility, with replace the whole
   * with it.
   */
  private def updateHoles(code: List[Stmt], newPossibilitiesMap: IMap[PossibilitiesHole, Set[Stmt]], typ: String): List[Stmt] = {
    if (newPossibilitiesMap.isEmpty)
      return code
    def pruneList(l: List[Stmt]): List[Stmt] = {
      def pruneExpr(e: Expr): Expr = pruneStmt(e).asInstanceOf[Expr]
      def pruneStmt(s: Stmt): Stmt = s match {
	case h @ PossibilitiesHole(p) if newPossibilitiesMap.contains(h) =>
	  val successful = newPossibilitiesMap(h)
	  val newPossibilities = p filter { s => successful contains s }
	  if (newPossibilities.size < p.size) {
	    val newStmt = possibilitiesToExpr(newPossibilities, throw new SolverError("All possibilities pruned for hole " + h))
	    origHoles += (newStmt -> origHoles.getOrElse(h, h))
	    origHoles -= h
	    println("Pruned (" + typ + ") hole " + shortPrinter.stringOfHole(h) + " to " + shortPrinter.stringOfStmt(newStmt))
	    newStmt
	  } else
	    h
	case If(c, t, ei, e) => If(pruneExpr(c), pruneList(t), ei map { t => (pruneExpr(t._1), pruneList(t._2)) }, pruneList(e))
	case Loop(c, b) => Loop(pruneStmt(c), pruneList(b))
	case UnorderedStmts(s) => UnorderedStmts(pruneList(s))
	case _ => s
      }
      l map pruneStmt
    }
    pruneList(code)
  }

  /* Inferring conditionals */

  private def fixCode(code: List[Stmt], reason: String, input: List[(String, Value)], failingStmt: Option[Stmt]): List[Stmt] = {
    println(Console.RED + "**" + Console.RESET + "Please fix the program because " + reason + ".")
    // TODO/FIXME: Call resetPruning here?
    controller.clearScreen()
    controller.updateDisplay(new Memory(input), code, None, true, Nil, failingStmt)
    controller.displayMessage("The current program is not complete because " + reason + ".  Please fix it so that we can continue.")
    numCodeFixes += 1
    val fixedStmts = getTraceWithHelpFromUser(code, input, true, true, failingStmt)
    println("Got fixed code:\n" + shortPrinter.stringOfStmts(fixedStmts, "  "))
    prunePossibilities(fixedStmts)
  }

  // Fix the condition.  We do this by re-reunning each input we've already seen on the new program and remembering the memory each time we see the condition.
  protected[graphprog] def getCondition(code: List[Stmt], oldCondition: Expr, firstPossibleJoinStmt: Option[Stmt], branch: Boolean): Expr = oldCondition match {
    case curHole @ PossibilitiesHole(possibilities) =>
      val unseen = UnseenExpr()
      val codeWithUnseen = addBlock(code, (firstPossibleJoinStmt, None), s => unseen)
      val evidence = ListBuffer.empty[(Value, Memory)]
      def holeHandler(memory: Memory, hole: Hole): Stmt = hole match {
	case hole @ PossibilitiesHole(p) =>
	  val results = p flatMap { s => try { val (v, m) = defaultExecutor.execute(memory, s); if (isErrorOrFailure(v)) Nil else List((s, v, m)) } catch { case _: Throwable => Nil } }
	  assert(holdsOverIterable(results, (x: (Stmt, Value, Memory), y: (Stmt, Value, Memory)) => areEquivalent(x._2, y._2, x._3, y._3)))
	  results.head._1
	case _: UnseenExpr if hole eq unseen =>
	  val v = BooleanConstant(!branch)
	  evidence += ((v, memory.clone))  // We clone the memory because the rest of the execution could leave scopes and remove variables.
	  ErrorConstant
      }
      val executor = new Executor(functions, longPrinter, holeHandler)
      finishedInputs foreach { i => executeProgram(executor, i, codeWithUnseen) }
      val newCondition = possibilitiesToStmt(curHole, evidence.foldLeft(possibilities){ case (curPossibilities, (v, m)) => curPossibilities filter { p => yieldEquivalentResults(m, p, v, defaultExecutor) } }).asInstanceOf[Expr]
      newCondition match {
	case p: PossibilitiesHole =>
	  origHoles += p -> p
	  enteredActions += (p -> evidence.map{ case (v, m) => (List(v), m) })
	case _ =>
      }
      newCondition
    case _ => oldCondition
  }

  protected[graphprog] def resetPruning(code: List[Stmt]): List[Stmt] = {
    // Fix pruning.  For anything that was a hole at the beginning, replace it with that original hole and then re-run all entered user actions to remove possibilities.  This has the effect of undoing pruning and then removing anything we would have removed through user interaction.
    val holeMap = origHoles.map{ case (curStmt, origHole) => curStmt -> possibilitiesToStmt(origHole, enteredActions.getOrElse(origHole, ListBuffer.empty[(List[Action], Memory)]).foldLeft(origHole.possibilities){ case (acc, (actions, mem)) => acc filter { p => actions exists { a => yieldEquivalentResults(mem, p, a, defaultExecutor) } } }) }.toMap
    holeMap foreach { case (curStmt, newStmt) => { val prevHole = origHoles.remove(curStmt).get; if (newStmt match { case PossibilitiesHole(p) => p.size != prevHole.possibilities.size case _ => true }) origHoles += (newStmt -> prevHole) } }
    getNewStmts(code, holeMap, IMap.empty)
  }

  // firstPossibleJoinStmt is the "smallest" thing, e.g. it is the condition not the if.  I have the real if in the caller (see ASTUtils.getOwningStmt), but the iteratorExecutor needs the smaller one anyway.  I could combine these for some efficiency, but who cares.
  protected[graphprog] def findLegalJoinPoints(code: List[Stmt], firstPossibleJoinStmt: Option[Stmt], memAtFirstPossibleJoinStmt: Memory, memAtJoin: Memory, actionsAfterJoin: List[Action]): (Option[Stmt], List[Stmt]) = {
    val parents = getParents(code)

    // Move the IteratorExecutor to the first potential join statement.
    val iteratorExecutor = advanceIteratorExecutorToPoint(code, firstPossibleJoinStmt, allInputs.last, Some(memAtFirstPossibleJoinStmt))
    assert(iteratorExecutor.hasNext)
    val realFirstPossibleJoinStmt = iteratorExecutor.getNextOpt
    val firstPossibleJoinStmtParent = realFirstPossibleJoinStmt.map{ realFirstPossibleJoinStmt => parents(realFirstPossibleJoinStmt) }.getOrElse(None)

    // Finds (first stmt after potential join, iterator) for all potential joins.
    val legalIterators = {
      @tailrec def getLegalIterators(legalIterators: List[(Stmt, IteratorExecutor)]): List[(Stmt, IteratorExecutor)] = {
	val newLegalIterators = legalIterators :+ ((iteratorExecutor.getNext, iteratorExecutor.clone))
	val curParent = parents(iteratorExecutor.getNext)
	iteratorExecutor.skipNext()
	if (iteratorExecutor.hasNext && (parents(iteratorExecutor.getNext).eq(firstPossibleJoinStmtParent) || curParent.eq(firstPossibleJoinStmtParent)))  // We can go one beyond firstPossibleJoinStmtParent, which represents the conditional covering the whole block.
	  getLegalIterators(newLegalIterators)
	else
	  newLegalIterators
      }
      getLegalIterators(Nil)
    }
    println(legalIterators.size + " potential joins:\n" + shortPrinter.stringOfStmts(legalIterators.map{ _._1 }, "  "))

    // Finds the potential joins that match the actions we've seen after the join.
    val legalJoins = legalIterators filter { case (firstStmtAfterJoin, iterator) => {
      val mem = memAtJoin.clone
      def checkIterator(actionsAfterJoin: List[Action]): Boolean = actionsAfterJoin match {
	case Nil => true
	case cur :: rest => 
	  iterator.getNext match {
	    case PossibilitiesHole(possibilities) =>
	      if (!possibilities.exists{ p => yieldEquivalentResults(mem, cur, p, defaultExecutor) })  // TODO: Check in more depth?
		return false
	    case next =>
	      if (!(try { yieldEquivalentResults(mem, cur, next, defaultExecutor) } catch { case _ => false }))
		return false
	  }
	  checkIterator(rest)
      }
      checkIterator(actionsAfterJoin)
    } } map { _._1 }

    (realFirstPossibleJoinStmt, legalJoins)
  }
  private def advanceIteratorExecutorToPoint(code: List[Stmt], target: Option[Stmt], input: List[(String, Value)], targetMem: Option[Memory]): IteratorExecutor = {
    val iteratorExecutor = new IteratorExecutor(functions, shortPrinter, simpleHoleHandler(defaultExecutor))
    val mem = iteratorExecutor.executeStmts(new Memory(input), code)._2
    target foreach { target => {
      // What I get as firstPossibleJoinStmt can be a condition, so I need to turn it into the containing statement in those cases.
      def isRightStmt(cur: Stmt) = cur match {
	case If(c, _, _, _) => c eq target
	case Loop(c, _) => c eq target
	case _ => cur eq target
      }
      while (iteratorExecutor.hasNext && !(isRightStmt(iteratorExecutor.getNext) && (targetMem match { case Some(targetMem) => memoriesAreEqual(mem, targetMem) case None => true })))
	iteratorExecutor.executeNext(mem)
    } }
    iteratorExecutor
  }

  protected[graphprog] def addBreakpoint(breakpoint: Breakpoint) = {
    breakpointsToAdd :+= breakpoint
    breakpointsToRemove = breakpointsToRemove filterNot { _ eq breakpoint.line }  // Make sure the add takes precedence over any previous removes.
  }

  protected[graphprog] def removeBreakpoint(line: Stmt) = {
    breakpointsToRemove :+= line
    breakpointsToAdd = breakpointsToAdd filterNot { _.line eq line }  // Make sure the remove takes precedence over any previous adds.
  }

  private def refreshBreakpointLine(breakpoint: Breakpoint, newLine: Stmt): Breakpoint = breakpoint match {
    case _: NormalBreakpoint => NormalBreakpoint(newLine)
    case ConditionalBreakpoint(_, c) => ConditionalBreakpoint(newLine, c)
  }

}

object Synthesis {

  def makeSynthesizer(name: String, typ: Type, inputTypes: List[(String, Type)], functions: IMap[String, Program], objectTypes: IMap[String, List[(String, Type)]], printHelpers: PartialFunction[String, Value => String] = Map.empty, generator: Option[Double => List[(String, Value)]] = None, precondition: Option[IMap[String, Value] => Boolean] = None, postcondition: Option[(IMap[String, Value], IMap[String, Value], Value) => Boolean] = None, objectComparators: Map[String, (Value, Value) => Int] = Map.empty)(controller: Controller): Synthesis = new Synthesis(controller, name, typ, inputTypes, functions, objectTypes, printHelpers, generator, precondition, postcondition, objectComparators)
  def makeSynthesizerFromTrace(trace: Trace, printHelpers: PartialFunction[String, Value => String] = Map.empty, generator: Option[Double => List[(String, Value)]] = None, precondition: Option[IMap[String, Value] => Boolean] = None, postcondition: Option[(IMap[String, Value], IMap[String, Value], Value) => Boolean] = None, objectComparators: Map[String, (Value, Value) => Int] = Map.empty)(controller: Controller): Synthesis = makeSynthesizer(trace.name, trace.typ, graphprog.lang.Typer.typeOfInputs(trace.inputs), trace.functions, trace.objectTypes, printHelpers, generator, precondition, postcondition, objectComparators)(controller)

  /* Constants */

  // Bounds for generating random inputs: (number of inputs of this size to try, min integer, max integer, max array size).
  private val EXPLORATION_BOUNDS = List((20, 0, 30, 5), (10, -50, 50, 10), (10, -100, 100, 20))
  // Probability we set an object to null.
  private val NULL_PROBABILITY = 0.25
  // Number of pruning rounds.
  private val NUM_PRUNING_ROUNDS = 20
  // Timeout in ms when running programs during pruning.
  private val TIMEOUT = 200
  // Number of inputs to try when we have a final program to try to ensure that we're not missing a conditional.
  private val NUM_FINAL_CHECKS = 20

}
