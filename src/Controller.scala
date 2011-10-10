package graphprog

import synthesis.Synthesis
import lang.AST.{ Action, Memory, Program, Trace, Value, Stmt, Type, Object, Iterate, Loop, Expr, Primitive }
import gui.SynthesisGUI._
import scala.concurrent.SyncVar
import java.util.concurrent.Semaphore
import Controller._
import scala.collection.immutable.Map
import scala.collection.{ Map => TMap }
import Utils._

protected[graphprog] class Controller(private val synthesisCreator: Controller => Synthesis, private val helperFunctions: Map[String, Program], private val objectTypes: Map[String, List[(String, Type)]], private val objectComparators: Map[String, (Value, Value) => Int], private val fieldLayouts: Map[String, List[List[String]]], private val objectLayouts: Map[String, ObjectLayout]) {

  protected var lastState: Option[(Memory, List[Stmt], Option[Stmt])] = None
  protected val actionsVar = new SingleUseSyncVar[Option[List[Action]]]
  protected val stmtTraceVar = new SingleUseSyncVar[Option[(List[Action], TMap[Iterate, Loop], Memory)]]
  protected val exprTraceVar = new SingleUseSyncVar[Option[(Expr, Memory)]]
  protected val fixInfo = new SingleUseSyncVar[FixInfo]

  protected val synthesizer = synthesisCreator(this)
  protected val gui = makeGUI(this, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts)  // We need to define this last since its creation triggers a paint, which calls getMemory, which needs memChan.

  def synthesize(input: List[(String, Value)]): Program = synthesizer.synthesize(input)
  def synthesize(trace: Trace): Program = synthesizer.synthesize(trace)

  def updateDisplay(memory: Memory, stmts: List[Stmt], curStmt: Option[Stmt], layoutObjs: Boolean = true) = {
    lastState = Some((memory, stmts, curStmt))
    invokeAndWait{ gui.updateDisplay(Some(memory.clone), stmts, curStmt, layoutObjs) }  // Important: we clone the memory since the GUI operates on its data directly.
  }
  def clearDisplay(stmts: List[Stmt]) = invokeAndWait{ gui.updateDisplay(None, stmts, None, false) }

  def getActions(possibilities: List[Action], amFixing: Boolean): Option[List[Action]] = {
    invokeAndWait{ gui.getActions(possibilities, amFixing) }
    actionsVar.get
  }

  def getStmtTrace(memory: Memory, canFix: Boolean, isConditional: Boolean = false): Option[(List[Action], List[Stmt], Memory)] = {
    invokeLater{ gui.getStmtTrace(memory, canFix, isConditional) }
    stmtTraceVar.get map { case (actions, loops, newMemory) => {
	// TODO/FIXME: Does this really guarantee that I wake up the last waiter rather than a random one?  If I end up changing this, probably integrate SynthesisGUI.depth into that.
	val stmts = synthesizer.genProgramAndFillHoles(memory, actions, false, loops)
      (actions, stmts, newMemory)
    } }
  }
  def getExprTrace(memory: Memory, canFix: Boolean): Option[(Expr, Expr, Memory)] = {
    invokeLater{ gui.getExprTrace(canFix) }
    exprTraceVar.get map { case (enteredExpr, newMemory) => {
      val exprCode = synthesizer.genProgramAndFillHoles(memory, enteredExpr)
      (enteredExpr, exprCode, newMemory)
    } }
  }

  def doFixStep(diffInfo: Option[(Memory, Stmt, Value)], amInConditional: Boolean = false, canDiverge: Boolean = true): FixInfo = {
    val newDiffInfo = diffInfo map { case (mem, stmt, value) => (mem, (stmt, value) match {
      case (_: Expr, p: Primitive) => Some(p)  // Let's only show the value if the current statement is an expression that returns a primitive.  We don't want, e.g., assign results or objects.
      case _ => None
    }) }
    invokeLater{ gui.doFixStep(newDiffInfo, amInConditional, canDiverge) }
    getFixInfo()
  }
  // Returns a function that, given the actions executed since the conditional ended, finds the legal join points.
  def insertConditionalAtPoint(): (Memory, List[Action] => Option[List[Stmt]]) = {
    import graphprog.lang.{ Executor, Printer }
    import graphprog.lang.AST.{ If, UnseenExpr, UnseenStmt, UnknownJoinIf, BooleanConstant }
    import graphprog.lang.ASTUtils.{ addBlock, getOwningStmt }
    val (initMem, code, initStmt) = lastState.get
    val realInitStmt = initStmt map { initStmt => getOwningStmt(code, initStmt) }
    val printer = new Printer(Map[String, Value => String](), true)

    val unseenPred = UnseenExpr()
    invokeLater{ gui.setCode(addBlock(code, (realInitStmt, None), s => UnknownJoinIf(If(unseenPred, List(UnseenStmt()), Nil, List(UnseenStmt())), s)), Some(unseenPred)) }
    val (predAction, predStmt, predMem) = getExprTrace(initMem.clone, false).get
    val branch = (new Executor(helperFunctions, printer)).evaluateBoolean(initMem, predAction)
    val newPredStmt = synthesizer.getCondition(code, predStmt, realInitStmt, branch)

    val unseenBody = UnseenStmt()
    invokeLater{ gui.setCode(addBlock(code, (realInitStmt, None), s => UnknownJoinIf(if (branch) If(newPredStmt, List(unseenBody), Nil, List(UnseenStmt())) else If(newPredStmt, List(UnseenStmt()), Nil, List(unseenBody)), s)), Some(unseenBody)) }
    val (newBranchActions, newBranch, joinMem) = getStmtTrace(predMem, false, true).get
    invokeLater{ gui.setCode(addBlock(code, (realInitStmt, None), s => UnknownJoinIf(if (branch) If(newPredStmt, newBranch, Nil, List(UnseenStmt())) else If(newPredStmt, List(UnseenStmt()), Nil, newBranch), s)), None) }
    (joinMem, (actionsAfterJoin: List[Action]) => {
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
  // Called in the case where in an earlier attempt to find a join we had no legal places, so we aborted and tried the other branch.  We've seen that one before, though, and followers is a superset of what it can contain.
  def insertConditionalAtPoint(code: List[Stmt], uif: graphprog.lang.AST.UnknownJoinIf, followers: List[Stmt]): List[Stmt] = {
    import graphprog.lang.{ Executor, Printer }
    import graphprog.lang.AST.{ If, UnseenExpr, UnseenStmt, PossibilitiesHole, UnknownJoinIf, Not }
    import graphprog.lang.ASTUtils.{ addBlock, getOwningStmt }
    import graphprog.lang.Executor.simpleHoleHandler
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

    def getCode(firstStmtAfterBlock: Option[Stmt]): List[Stmt] = addBlock(code, (Some(followers.head), firstStmtAfterBlock), s => if (branch) If(cond, oldBody, Nil, s) else If(cond, s, Nil, oldBody))
    // Walk through the followers, showing the user what they are and asking whether to continue or end the conditional
    followers.foldLeft((List[Stmt](), initMem.clone)){ case ((prevStmts, curMem), curStmt) => {
      val unseenBody = UnseenStmt()
      updateDisplay(curMem, addBlock(code, (realInitStmt, None), s => UnknownJoinIf(if (branch) If(cond, oldBody, Nil, prevStmts :+ unseenBody) else If(cond, prevStmts :+ unseenBody, Nil, oldBody), s.drop(prevStmts.size))), Some(unseenBody), false)
      val (v, m) = holeExecutor.execute(curMem, curStmt)
      // FIXME: This (and code that gets legal joins in synthesis) fails when a stmt is a conditional with a hole for the condition.  In Synthesis we can't execute it so we think it's an illegal join while here we don't show a diff.  Example random seed (currently): 6987549502241748574.
      doFixStep(Some((m, curStmt, v)), true, false) match {
	case EndConditional => return getCode(Some(curStmt))
	case Step => (prevStmts :+ curStmt, m)
	case _ => throw new RuntimeException
      }
    } }
    return getCode(None)
  }
  def getFixInfo(): FixInfo = fixInfo.get

  def setActions(actions: Option[List[Action]]) = actionsVar set actions
  def setStmtTrace(trace: Option[(List[Action], TMap[Iterate, Loop], Memory)]) = stmtTraceVar set trace
  def setExprTrace(expr: Option[(Expr, Memory)]) = exprTraceVar set expr
  def setFixInfo(info: FixInfo) = fixInfo set info

  // TODO/FIXME: I should do pruning here after genProgramAndFillHoles but before executeWithHelpFromUser.  That might reduce the num of questions I ask for later iterations.  But for that, I need to have access to the entire program up to this point.  Canvas' Tracer has the current unseen part, but I don't have everything before it.  Once I modify executeWithHelpFromUser to keep the whole program, I can have that.  Note that I can also add pruning to places inside executeWithHelpFromUser, perhaps after I get an unseen statement.
  def synthesizeLoop(initialMemory: Memory, firstIteration: Iterate, loops: TMap[Iterate, Loop], curMemory: Memory): (Memory, Iterate, Loop) = {
    val stmts = synthesizer.genProgramAndFillHoles(initialMemory, List(firstIteration), true, loops)
    firstIteration match {
      case Iterate(List((_, Nil))) => (curMemory, firstIteration, singleton(stmts).asInstanceOf[Loop])  // If the first iteration is empty, do not execute the loop.
      case _ =>
	val (allIterations, loop, finalMem) = ((firstIteration, synthesizer.executeWithHelpFromUser(curMemory, stmts, false, false)): @unchecked) match {
	  case (Iterate(i1 :: Nil), (Iterate(irest) :: Nil, (l: Loop) :: Nil, m)) => (Iterate(i1 :: irest), l, m)
	}
      (finalMem, allIterations, loop)
    }
  }

  def displayMessage(msg: String) = gui.displayMessage(msg)

  def clearScreen() = gui.clear()

  def cleanup() = gui.dispose()

}

private class SingleUseSyncVar[T] extends SyncVar[T] {
  override def get = synchronized {
    val x = super.get
    unset
    x
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
   */
  type ObjectLayout = (Object, (Value => Int), (Value => Int), Int) => Iterable[(Object, (Int, Int))]

  def synthesize(trace: Trace, synthesisCreator: Controller => Synthesis, helperFunctions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], objectComparators: Map[String, (Value, Value) => Int], fieldLayouts: Map[String, List[List[String]]], objectLayouts: Map[String, ObjectLayout]): Program = {
    val controller = new Controller(synthesisCreator, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts)
    try {
      controller.synthesize(trace)
    } finally {
      controller.cleanup()
    }
  }
  def synthesize(inputs: List[(String, Value)], synthesisCreator: Controller => Synthesis, helperFunctions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], objectComparators: Map[String, (Value, Value) => Int], fieldLayouts: Map[String, List[List[String]]], objectLayouts: Map[String, ObjectLayout]): Program = {
    val controller = new Controller(synthesisCreator, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts)
    try {
      controller.synthesize(inputs)
    } finally {
      controller.cleanup()
    }
  }

  // The possible results of user actions when we're in fixing/debug walkthrough mode.
  protected[graphprog] sealed abstract class FixInfo
  protected[graphprog] case class Code(code: List[Stmt]) extends FixInfo
  protected[graphprog] case object Step extends FixInfo
  protected[graphprog] case object Continue extends FixInfo
  protected[graphprog] case object EndConditional extends FixInfo

}
