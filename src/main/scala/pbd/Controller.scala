package pbd

import synthesis.Synthesis
import lang.AST.{ Action, Program, Trace, Value, Stmt, Type, Object, Iterate, Loop, Expr, Primitive, UnseenStmt }
import lang.Memory
import gui.SynthesisGUI._
import scala.concurrent.SyncVar
import java.util.concurrent.Semaphore
import Controller._
import scala.collection.immutable.Map
import scala.collection.{ Map => TMap }
import Utils._

/**
 * The Controller is responsible for letting the synthesizer and the gui communicate.
 */
protected[pbd] class Controller(private val synthesisCreator: Controller => Synthesis, private val helperFunctions: Map[String, Program], private val objectTypes: Map[String, List[(String, Type)]], private val objectComparators: Map[String, (Value, Value) => Int], private val fieldLayouts: Map[String, List[List[String]]], private val objectLayouts: Map[String, ObjectLayout], @transient private var options: Options) extends Serializable {

  // The last state we displayed.
  @transient private var lastState: Option[(Memory, List[Stmt], Option[Stmt])] = None
  // Variables used for blocking communication between the synthesizer and the gui.
  private val actionsVar = new SyncVar[ActionsInfo]
  private val stmtTraceVar = new SyncVar[StmtTraceIntermediateInfo]
  private val exprTraceVar = new SyncVar[ExprTraceIntermediateInfo]
  private val fixInfo = new SyncVar[FixInfo]

  private val synthesizer = synthesisCreator(this)
  @transient private var gui = makeGUI(this, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts)  // We need to define this last since its creation triggers a paint, which calls getMemory, which needs memChan.

  def synthesize(input: List[(String, Value)]): Program = synthesizer.synthesize(input)
  def synthesize(trace: Trace): Program = synthesizer.synthesize(trace)

  /**
   * Updates the GUI to display the current memory and code.
   */
  def updateDisplay(memory: Memory, stmts: List[Stmt], curStmt: Option[Stmt], layoutObjs: Boolean = true, breakpoints: List[Breakpoint] = Nil, failingStmt: Option[Stmt] = None) = {
    lastState = Some((memory, stmts, curStmt))
    invokeAndWait{ gui.updateDisplay(Some(memory.clone), stmts, curStmt, layoutObjs, breakpoints, failingStmt) }  // Important: we clone the memory since the GUI operates on its data directly.
  }

  /**
   * Clears the display.
   */
  def clearDisplay(stmts: List[Stmt]) = invokeAndWait{ gui.updateDisplay(None, stmts, None, false, Nil, None) }

  /**
   * Shows the user a list of possible actions and lets him choose some.
   * Note that the user can also do other things through the controls.
   */ 
  def getActions(possibilities: List[Action], amFixing: Boolean): ActionsInfo = {
    invokeAndWait{ gui.getActions(possibilities, amFixing) }
    actionsVar.take
  }

  /**
   * Gets statement(s) from the user.
   */ 
  def getStmtTrace(memory: Memory, canFix: Boolean, isConditional: Boolean = false): StmtTraceFinalInfo = {
    invokeLater{ gui.getStmtTrace(memory, canFix, isConditional) }
    stmtTraceVar.take match {
      case StmtIntermediateInfo((actions, loops, newMemory)) =>
	// TODO/FIXME: Does this really guarantee that I wake up the last waiter rather than a random one?  If I end up changing this, probably integrate SynthesisGUI.depth into that.
	val stmts = synthesizer.genProgramAndFillHoles(memory, actions, false, loops)
	StmtInfo((actions, stmts, newMemory))
      case Fix => Fix
      case e: EndTrace => e
    }
  }

  /*
   * Gets an expression from the user.
   */
  def getExprTrace(memory: Memory, canFix: Boolean): ExprTraceFinalInfo = {
    invokeLater{ gui.getExprTrace(canFix) }
    exprTraceVar.take match {
      case ExprIntermediateInfo((enteredExpr, newMemory)) =>
	val exprCode = synthesizer.genProgramAndFillHoles(memory, enteredExpr)
	ExprInfo((enteredExpr, exprCode, newMemory))
      case Fix => Fix
      case e: EndTrace => e
    }
  }

  /*
   * Shows the user the given memory diff and lets him walk through it or
   * fix the program, e.g., by adding a conditional.
   */
  def doFixStep(diffInfo: Option[(Memory, Stmt, Value)], amInConditional: Boolean = false, canDiverge: Boolean = true): FixInfo = {
    val newDiffInfo = diffInfo map { case (mem, stmt, value) => (mem, (stmt, value) match {
      case (_: Expr, p: Primitive) => Some(p)  // Let's only show the value if the current statement is an expression that returns a primitive.  We don't want, e.g., assign results or objects.
      case _ => None
    }) }
    invokeLater{ gui.doFixStep(newDiffInfo, amInConditional, canDiverge) }
    getFixInfo()
  }

  /**
   * Gets the user to demonstrate a condition and then the new body of the conditional.
   * Returns a function that, given the actions executed since the conditional ended, finds the legal join points.
   * TODO/FIXME: Use manually-executed actionsAfterJoin to prune corresponding PossibilityHoles, if any (test on sort: I join on j:=j+1, which should prune j:=min+1).
   */
  def insertConditionalAtPoint(): ConditionalInfo = {
    import pbd.lang.{ Executor, Printer }
    import pbd.lang.AST.{ If, UnseenExpr, UnknownJoinIf, BooleanConstant }
    import pbd.lang.ASTUtils.{ addBlock, getOwningStmt }
    val (initMem, code, initStmt) = lastState.get
    val realInitStmt = initStmt map { initStmt => getOwningStmt(code, initStmt) }
    val printer = new Printer(Map[String, Value => String](), true)

    val unseenPred = UnseenExpr()
    invokeLater{ gui.setCode(addBlock(code, (realInitStmt, None), s => UnknownJoinIf(If(unseenPred, List(UnseenStmt()), Nil, List(UnseenStmt())), s)), Some(unseenPred)) }
    val (predAction, predStmt, predMem) = getExprTrace(initMem.clone, false) match {
      case ExprInfo(i) => i
      case e: EndTrace => return e
      case Fix => throw new RuntimeException
    }
    val branch = (new Executor(helperFunctions, printer)).evaluateBoolean(initMem, predAction)
    val newPredStmt = synthesizer.getCondition(code, predStmt, realInitStmt, branch)

    val unseenBody = UnseenStmt()
    invokeLater{ gui.setCode(addBlock(code, (realInitStmt, None), s => UnknownJoinIf(if (branch) If(newPredStmt, List(unseenBody), Nil, List(UnseenStmt())) else If(newPredStmt, List(UnseenStmt()), Nil, List(unseenBody)), s)), Some(unseenBody)) }
    val (newBranchActions, newBranch, joinMem) = getStmtTrace(predMem, false, true) match {
      case StmtInfo(i) => i
      case e: EndTrace => return e
      case Fix => throw new RuntimeException
    }

    invokeLater{ gui.setCode(addBlock(code, (realInitStmt, None), s => UnknownJoinIf(if (branch) If(newPredStmt, newBranch, Nil, List(UnseenStmt())) else If(newPredStmt, List(UnseenStmt()), Nil, newBranch), s)), None) }
    JoinFinderInfo(joinMem, (actionsAfterJoin: List[Action]) => {
      val (lastExecutedStmt, legalJoins) = synthesizer.findLegalJoinPoints(code, initStmt, initMem, joinMem, actionsAfterJoin)
      println(legalJoins.size + " legal " + pluralize("join", "joins", legalJoins.size) + ":" + (if (legalJoins.nonEmpty) "\n" + (new Printer(Map[String, Value => String](), true)).stringOfStmts(legalJoins, "  ") else ""))
      legalJoins match {
	case joinStmt :: Nil =>
	  val newCode = addBlock(code, (lastExecutedStmt, Some(joinStmt)), s => if (branch) If(newPredStmt, newBranch, Nil, s) else If(newPredStmt, s, Nil, newBranch))
	  println("New code:\n" + (new Printer(Map[String, Value => String](), true)).stringOfStmts(newCode, "  "))
	  Some(newCode)
	case Nil => Some(List(UnknownJoinIf(if (branch) If(newPredStmt, newBranch, Nil, List(UnseenStmt())) else If(newPredStmt, List(UnseenStmt()), Nil, newBranch), Nil)))
	case _ => None
      }
    })
  }
  /**
   * Called in the case where in an earlier attempt to find a join we had no legal places, so we aborted and tried the other branch.  We've seen that one before, though, and followers is a superset of what it can contain.
   */
  def insertConditionalAtPoint(code: List[Stmt], uif: pbd.lang.AST.UnknownJoinIf, followers: List[Stmt]): JoinInfo = {
    import pbd.lang.{ Executor, Printer }
    import pbd.lang.AST.{ If, PossibilitiesHole, UnknownJoinIf, Not }
    import pbd.lang.ASTUtils.{ addBlock, getOwningStmt }
    import pbd.lang.Executor.simpleHoleHandler
    val (initMem, uifCode, initStmt) = lastState.get  // The code here has the UnknownJoinIf in it, so we use the user-given one without it.
    val realInitStmt = initStmt map { initStmt => getOwningStmt(code, initStmt) }
    val printer = new Printer(Map[String, Value => String](), true)
    val normalExecutor = new Executor(helperFunctions, printer)
    val holeExecutor = new Executor(helperFunctions, printer, simpleHoleHandler(normalExecutor))

    val (branch, cond, oldBody, unseen) = uif.known match {
      case If(c, b, _, List(u: UnseenStmt)) => (true, c, b, u)
      case If(c, List(u: UnseenStmt), _, b) => (false, c, b, u)
      case _ => throw new RuntimeException
    }
    invokeLater{ gui.setCode(uifCode, Some(unseen)) }
    displayMessage("There must be a conditional at this point.  Please demonstrate the body, marking where the conditional ends.")

    def getCode(firstStmtAfterBlock: Option[Stmt]): CodeInfo = CodeInfo(addBlock(code, (Some(followers.head), firstStmtAfterBlock), s => if (branch) If(cond, oldBody, Nil, s) else If(cond, s, Nil, oldBody)))
    // Walk through the followers, showing the user what they are and asking whether to continue or end the conditional
    followers.foldLeft((List[Stmt](), initMem.clone)){ case ((prevStmts, curMem), curStmt) => {
      val unseenBody = UnseenStmt()
      updateDisplay(curMem, addBlock(code, (realInitStmt, None), s => UnknownJoinIf(if (branch) If(cond, oldBody, Nil, prevStmts :+ unseenBody) else If(cond, prevStmts :+ unseenBody, Nil, oldBody), s.drop(prevStmts.size))), Some(unseenBody), false)
      val (v, m) = holeExecutor.execute(curMem, curStmt)
      // FIXME: This (and code that gets legal joins in synthesis) fails when a stmt is a conditional with a hole for the condition.  In Synthesis we can't execute it so we think it's an illegal join while here we don't show a diff.  Example random seed (currently): 6987549502241748574.
      doFixStep(Some((m, curStmt, v)), true, false) match {
	case EndConditional => return getCode(Some(curStmt))
	case Step => (prevStmts :+ curStmt, m)
	case e: EndTrace => return e
	case _ => throw new RuntimeException
      }
    } }
    return getCode(None)
  }
  def getFixInfo(): FixInfo = fixInfo.take
  def hideFixingGui() = invokeLater{ gui.hideFixingGui() }

  // Communicate bween the synthesizer and the gui.
  def setActions(actions: ActionsInfo) = actionsVar put actions
  def setStmtTrace(trace: StmtTraceIntermediateInfo) = stmtTraceVar put trace
  def setExprTrace(expr: ExprTraceIntermediateInfo) = exprTraceVar put expr
  def setFixInfo(info: FixInfo) = fixInfo put info

  /**
   * Synthesizes a loop given its first iteration and then walks through it.
   * ActionsToPoint is all the actions that from initialMemory to the end of
   * the first iteration of this loop with a marker marking the current location.
   */
  def synthesizeLoop(initialMemory: Memory, firstIteration: Iterate, loops: TMap[Iterate, Loop], curMemory: Memory, actionsToPoint: List[Stmt], numBlocksToMark: Int): LoopFinalInfo = {
    import pbd.lang.AST.Marker
    import pbd.lang.ASTUtils.{ getNewStmts, getParents }
    // Synthesize and prune code for the loop.
    val codeToPoint = synthesizer.genProgramAndFillHoles(initialMemory, actionsToPoint.asInstanceOf[List[Action]], true, loops)
    val marker = Marker()
    val codeToPointWithUnseens = {  // Adds unseens where necessary for pruning.
      val parents = getParents(codeToPoint)
      val blocksToMark = scala.collection.mutable.Set.empty[Stmt]
      def getMarkerParents(s: Stmt, numBlocksToMark: Int) {
	if (numBlocksToMark > 0) {
	  val parent = parents(s).get
	  blocksToMark += parent
	  getMarkerParents(parent, numBlocksToMark - 1)
	}
      }
      getMarkerParents(marker, numBlocksToMark)
      getNewStmts(codeToPoint, Map.empty, (s: Stmt) => s match { case s if blocksToMark.contains(s) => blocksToMark -= s; List(s, UnseenStmt()) })
    }
    val prunedCodeToPointWithUnseens = synthesizer.prunePossibilities(codeToPointWithUnseens, false)
    val curLoop = getParents(prunedCodeToPointWithUnseens)(marker) match { case Some(Loop(c, b)) if b.last == marker => Loop(c, b.dropRight(1)) case s => throw new RuntimeException(s.toString) }  // Get the newly-pruned loop.
    // Continue executing further iterations of the loop if necessary.
    firstIteration match {
      case Iterate(List((_, Nil))) => LoopInfo((curMemory, firstIteration, curLoop.asInstanceOf[Loop]))  // If the first iteration is empty, do not execute the loop.
      case _ =>
	val (allIterations, loop, finalMem) = ((firstIteration, synthesizer.executeLoopWithHelpFromUser(curMemory, curLoop, false)): @unchecked) match {
	  case (Iterate(i1 :: Nil), StmtInfo((Iterate(irest) :: Nil, (l: Loop) :: Nil, m))) => (Iterate(i1 :: irest), l, m)
	  case (_, e: EndTrace) => return e
	}
      LoopInfo((finalMem, allIterations, loop))
    }
  }

  /**
   * Skips the current trace.
   */
  def skipTrace(queryType: QueryType, sameInput: Boolean, saveChanges: Boolean) {
    clearScreen()
    val ender = EndTrace(sameInput, saveChanges)
    queryType match {
      case Actions => setActions(ender)
      case StmtTrace => setStmtTrace(ender)
      case ExprTrace => setExprTrace(ender)
      case FixType => setFixInfo(ender)
    }
  }

  /**
   * Add/remove breakpoints.
   */
  def addBreakpoint(breakpoint: Breakpoint) = synthesizer.addBreakpoint(breakpoint)
  def removeBreakpoint(line: Stmt) = synthesizer.removeBreakpoint(line)

  /**
   * Display a graphical message to the suer.
   */
  def displayMessage(msg: String) = gui.displayMessage(msg)

  def getOptions(): Options = options

  /**
   * Clear the screen.
   */
  def clearScreen() = invokeLater { gui.clear() }

  def cleanup() = gui.dispose()

  /*
   * Serialization methods.
   * These next two methods control how the Controller is serialized.
   * We need to manually recreate the GUI after deserializing the Controller.
   */
  private def writeObject(out: java.io.ObjectOutputStream) {
    out.defaultWriteObject()
  }

  private def readObject(in: java.io.ObjectInputStream) {
    in.defaultReadObject()
    gui = makeGUI(this, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts)
  }

}

object Controller {

  /**
   * The type of the function the user can supply to manually lay out objects of certain types.
   * Parameter 1: The object to be laid out.
   * Parameter 2,3: Functions to compute the width and height of values.
   * Parameter 4: Minimum amount of space to leave between things.
   * Return: A list of objects and their new coordinates.
   * TODO: Currently, this is called on every object of this type.  For trees, we would only need to call it on the head, but we cannot avoid it for lists.  I could let the user pass a function telling when to call it (e.g. only when parent is null for trees).
   * TODO: This should allow us to layout arrays as well.
   */
  type ObjectLayout = (Object, (Value => Int), (Value => Int), Int) => Iterable[(Object, (Int, Int))]

  def synthesize(trace: Trace, synthesisCreator: Controller => Synthesis, helperFunctions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], objectComparators: Map[String, (Value, Value) => Int], fieldLayouts: Map[String, List[List[String]]], objectLayouts: Map[String, ObjectLayout], options: Options): Program = synthesize(controller => controller.synthesize(trace), synthesisCreator, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts, options)
  def synthesize(inputs: List[(String, Value)], synthesisCreator: Controller => Synthesis, helperFunctions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], objectComparators: Map[String, (Value, Value) => Int], fieldLayouts: Map[String, List[List[String]]], objectLayouts: Map[String, ObjectLayout], options: Options): Program = synthesize(controller => controller.synthesize(inputs), synthesisCreator, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts, options)
  private def synthesize(action: Controller => Program, synthesisCreator: Controller => Synthesis, helperFunctions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], objectComparators: Map[String, (Value, Value) => Int], fieldLayouts: Map[String, List[List[String]]], objectLayouts: Map[String, ObjectLayout], options: Options): Program = {
    options.loadBackupData match {
      case Some(filename) =>  // Load in the stored data and continue computation from that point.
	val (controller, code) = loadBackupData(filename)
	controller.options = options  // Use the current options.
	try {
	  controller.synthesizer.synthesizeCode(code)
	} finally {
	  controller.cleanup()
	}
      case None =>
	val controller = new Controller(synthesisCreator, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts, options)
	try {
	  action(controller)
	} finally {
	  controller.cleanup()
	}
    }
  }

  /*
   * Utility methods that handle serialization of our state.
   * TODO: Improve handling of serialization.  Some fields are marked vars (e.g., options, gui in Controller ).  Some things are serialized that don't need to be (e.g. printer, executors, typer in Synthesis).
   */

  protected[pbd] def dumpBackupData(filename: String, controller: Controller, curCode: List[Stmt]) {
    import java.io.{ File, FileOutputStream, ObjectOutputStream }
    val out = new ObjectOutputStream(new FileOutputStream(filename))
    out.writeObject(controller)
    out.writeObject(curCode)
    out.close()
  }

  private def loadBackupData(filename: String): (Controller, List[Stmt]) = {
    import java.io.{ File, FileInputStream, ObjectInputStream }
    val in = new ObjectInputStream(new FileInputStream(filename))
    val controller = in.readObject().asInstanceOf[Controller]
    val code = in.readObject().asInstanceOf[List[Stmt]]
    in.close()
    (controller, code)
  }

  /**
   * Types for communication.
   * The two intermediate types are the result directly returned from the GUI
   * while the non-intermediate versions are the real data we want returned.
   */
  protected[pbd] sealed trait ActionsInfo
  protected[pbd] sealed trait StmtTraceIntermediateInfo
  protected[pbd] sealed trait StmtTraceFinalInfo
  protected[pbd] sealed trait ExprTraceIntermediateInfo
  protected[pbd] sealed trait ExprTraceFinalInfo
  protected[pbd] sealed trait FixInfo  // The different things the user can do when we're in fix/debug mode.
  protected[pbd] sealed trait ConditionalInfo
  protected[pbd] sealed trait JoinInfo
  protected[pbd] sealed trait LoopIntermediateInfo
  protected[pbd] sealed trait LoopFinalInfo
  protected[pbd] case class Actions(actions: List[Action]) extends ActionsInfo
  protected[pbd] case class StmtIntermediateInfo(stmtInfo: (List[Action], TMap[Iterate, Loop], Memory)) extends StmtTraceIntermediateInfo
  protected[pbd] case class StmtInfo(stmtInfo: (List[Action], List[Stmt], Memory)) extends StmtTraceFinalInfo with LoopIntermediateInfo
  protected[pbd] case class ExprIntermediateInfo(exprInfo: (Expr, Memory)) extends ExprTraceIntermediateInfo
  protected[pbd] case class ExprInfo(exprInfo: (Expr, Expr, Memory)) extends ExprTraceFinalInfo
  protected[pbd] case class CodeInfo(code: List[Stmt]) extends FixInfo with JoinInfo
  protected[pbd] case object Fix extends ActionsInfo with StmtTraceIntermediateInfo with StmtTraceFinalInfo with ExprTraceIntermediateInfo with ExprTraceFinalInfo
  protected[pbd] case object Step extends FixInfo
  protected[pbd] case object Continue extends FixInfo
  protected[pbd] case object EndConditional extends FixInfo
  protected[pbd] case class EndTrace(sameInput: Boolean, saveChanges: Boolean) extends ActionsInfo with StmtTraceIntermediateInfo with StmtTraceFinalInfo with ExprTraceIntermediateInfo with ExprTraceFinalInfo with FixInfo with ConditionalInfo with JoinInfo with LoopIntermediateInfo with LoopFinalInfo
  protected[pbd] case class JoinFinderInfo(memory: Memory, joinFinder: List[Action] => Option[List[Stmt]]) extends ConditionalInfo
  protected[pbd] case class LoopInfo(info: (Memory, Iterate, Loop)) extends LoopFinalInfo
  protected[pbd] case object FindMoreExpressions extends ActionsInfo with FixInfo

  protected[pbd] sealed abstract class QueryType
  protected[pbd] case object Actions extends QueryType
  protected[pbd] case object StmtTrace extends QueryType
  protected[pbd] case object ExprTrace extends QueryType
  protected[pbd] case object FixType extends QueryType

  protected[pbd] abstract class Breakpoint { val line: Stmt }
  protected[pbd] case class NormalBreakpoint(line: Stmt) extends Breakpoint
  protected[pbd] case class ConditionalBreakpoint(line: Stmt, condition: Expr) extends Breakpoint

  class Options(val dumpBackupData: Option[String], val loadBackupData: Option[String], val extraArgs: List[String])

}
