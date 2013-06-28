package graphprog.gui

import java.awt.{ BorderLayout, Dimension }
import java.awt.event.{ WindowAdapter, WindowEvent }
import javax.swing.{ JFrame, UIManager, WindowConstants, JLabel, JSplitPane, JScrollPane, BorderFactory, JOptionPane }
import graphprog.gui._
import SynthesisGUI._
import graphprog.Controller
import graphprog.Controller._
import graphprog.lang.AST.{ Program, Type, Primitive, Value }
import graphprog.Controller.ObjectLayout
import scala.collection.{ Map => TMap }

class SynthesisGUI private (private val controller: Controller, private val helperFunctions: Map[String, Program], private val objectTypes: Map[String, List[(String, Type)]], private val objectComparators: Map[String, (Value, Value) => Int], private val fieldLayouts: Map[String, List[List[String]]], private val objectLayouts: Map[String, ObjectLayout]) extends JFrame(TITLE) {

  import graphprog.Utils._
  import graphprog.lang.AST.{ Action, Memory, Value, Stmt, Iterate, Loop, If, UnseenStmt, Expr }

  private val canvas = new Canvas(this, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts)
  private val controls = new graphprog.gui.controls.Controls(this, helperFunctions.values)
  private val statusBar = new JLabel(" ")
  private val code = new Code(this)

  private var depth = 0

  // GUI layout

  setupGUI()

  private def setupGUI() {
    setLayout(new BorderLayout)
    UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName())
    javax.swing.ToolTipManager.sharedInstance().setDismissDelay(Integer.MAX_VALUE)  // Without this the tooltips in the Code pane go away after a few seconds.
    setPreferredSize(new Dimension(WIDTH, HEIGHT))
    canvas.setPreferredSize(new Dimension((WIDTH * CANVAS_PERCENTAGE).toInt, HEIGHT - controls.getHeight() - statusBar.getHeight()))

    setJMenuBar(controls.getMenu())
    val codePane = new JScrollPane(code)
    codePane.setBorder(BorderFactory.createTitledBorder("Code"));
    val splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, canvas, codePane)
    splitPane.setOneTouchExpandable(true)
    splitPane.setDividerLocation((CANVAS_PERCENTAGE * WIDTH).toInt)  // Use an absolute value not a percentage since it's not visible yet.
    add(splitPane, BorderLayout.CENTER)
    add(statusBar, BorderLayout.SOUTH)
    add(controls.getToolbar(), BorderLayout.NORTH)

    setupWindow()
  }

  private def setupWindow() {
    setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE)
    addWindowListener(new WindowAdapter() {
      override def windowClosing(event: WindowEvent) {
	doExit()
      }
    })
    pack()
    setVisible(true)
  }

  protected[gui] def doExit() = {
    dispose()
    System.exit(0)
  }

  protected[gui] def setStatusBarText(msg: String) = statusBar.setText(msg)
  protected[gui] def emptyStatusBarText() = statusBar.setText(" ")

  protected[gui] def addPrimVarToCanvas(name: String) = canvas.addPrimVar(name)
  protected[gui] def addPointerToCanvas(name: String) = canvas.addPointer(name)
  protected[gui] def addPrimToCanvas(p: Primitive) = canvas.addPrim(p)
  protected[gui] def addActionToCanvas(a: Action, shouldDoExpr: Boolean) = canvas.addAction(a, shouldDoExpr)

  protected[gui] def addCallToCanvas(c: Callable) = canvas.addCall(c)

  protected[gui] def startUnordered() = canvas.startUnordered()
  protected[gui] def startSnapshot() = canvas.startSnapshot()
  protected[gui] def startConditional() = canvas.startConditional()
  protected[gui] def finishBlock() = canvas.finishBlock()
  protected[gui] def startLoop() = canvas.startLoop()
  protected[gui] def finishIteration() = canvas.finishIteration()

  protected[gui] def conditionSetOrUnset(given: Boolean) = controls.conditionSetOrUnset(given)
  protected[gui] def showTraceControls() = controls.showTraceControls()
  protected[gui] def hideTraceControls() = controls.hideTraceControls()

  // Communication logic

  def updateDisplay(memoryOpt: Option[Memory], stmts: List[Stmt], curStmt: Option[Stmt], layoutObjs: Boolean, breakpoints: List[Breakpoint] = Nil, failingStmt: Option[Stmt]) {
    memoryOpt match {
      case Some(memory) => canvas.updateDisplayWithMemory(memory, layoutObjs)
      case None => canvas.clear()
    }
    setCode(stmts, curStmt, None, breakpoints, failingStmt)
    repaint()
  }

  def getActions(possibilities: List[Action], amFixing: Boolean) {
    canvas.setPossibilities(possibilities)
    controls.showHoleControls(!amFixing && depth == 0)
    if (amFixing)
      controls.showFixingControls(false, false, true)
    repaint()
  }

  protected[gui] def setActions(actions: ActionsInfo) {
    controls.hideHoleControls()
    repaint()  // Repaint after we finish the selection to, e.g., remove the hilighting
    controller.setActions(actions)
  }
  protected[gui] def setNoAction() {
    canvas.clear()
    emptyStatusBarText()
    setActions(Fix)
  }

  def getStmtTrace(memory: Memory, canFix: Boolean, isConditional: Boolean) {
    controls.startTraceMode(false, canFix && depth == 0, isConditional, false)
    canvas.startStmtTraceMode(memory)
    repaint()
  }
  def getExprTrace(canFix: Boolean) {
    controls.startTraceMode(true, canFix && depth == 0, false, false)
    canvas.startExprTraceMode()
    repaint()
  }

  // This is called from the Menu, so I do not need to call hideTraceControls.
  protected[gui] def finishStmtTrace() {
    val (actions, loops, mem) = canvas.finishStmtTraceMode()
    finishStmtTrace(StmtIntermediateInfo((actions, loops, mem)))
    repaint()
  }
  protected[gui] def setTraceExpr(e: Expr, m: Memory) {
    controls.finishExprTraceMode()
    controller.setExprTrace(ExprIntermediateInfo((e, m)))
  }
  protected[gui] def setNoTrace(isExpr: Boolean) {
    canvas.finishTraceMode()
    if (isExpr)
      controller.setExprTrace(Fix)
    else
      finishStmtTrace(Fix)
    repaint()
  }
  protected[gui] def finishStmtTrace(result: StmtTraceIntermediateInfo) {
    hideTraceControls()  // This gets called from Menu, but we have to call this to notify Toolbar.
    controls.discardAllEdits()
    controller.setStmtTrace(result)
  }

  def doFixStep(diffInfo: Option[(Memory, Option[Primitive])], amInConditional: Boolean, canDiverge: Boolean) = diffInfo match {
    case Some((diffMemory, valueOpt)) =>
      controls.showFixingControls(true, amInConditional, canDiverge)
      canvas.showMemoryDiff(diffMemory, valueOpt)
    case None => insertConditionalAtPoint()
  }
  protected[gui] def step() {
    hideFixingGui()
    controller.setFixInfo(Step)
  }
  protected[gui] def continue() {
    hideFixingGui()
    controller.setFixInfo(Continue)
  }
  protected[gui] def insertConditionalAtPoint() {
    if (canvas.isQueryMode()) {
      canvas.leaveQueryMode()
      controls.hideHoleControls()
      controller.setActions(Fix)
    }
    hideFixingGui()
    showMessage(this, "There must be a conditional at this point.  Please demonstrate the guard and then the body, marking where the conditional ends.", "Insert a conditional")
    invokeOffSwingThread(controller.insertConditionalAtPoint(), (result: ConditionalInfo) => result match {
      case JoinFinderInfo(mem, joinFinder) => 
	controls.startTraceMode(false, false, false, true)
	canvas.startJoinGuessMode(mem, joinFinder)
	repaint()
      case e: EndTrace => controller.setFixInfo(e)
    })
  }
  // Called when we've found the join point for a conditional.
  protected[gui] def finishFixing(code: List[Stmt]) {
    controls.finishStmtTraceMode()
    controller.setFixInfo(CodeInfo(code))
  }
  // Called when the user marks that a conditional has ended (but we don't necessarily know the join point yet).
  protected[gui] def endConditional() {
    hideFixingGui()
    controller.setFixInfo(EndConditional)
  }
  private def hideFixingGui() {
    canvas.hideMemoryDiff()
    controls.hideFixingControls()
  }

  def setCode(stmts: List[Stmt], curStmt: Option[Stmt], replacementStmts: Option[Iterable[Stmt]] = None, breakpoints: List[Breakpoint] = Nil, failingStmt: Option[Stmt] = None) = code.setCode(stmts, curStmt, replacementStmts, breakpoints, failingStmt)

  protected[gui] def setCurrentStmts(stmts: Iterable[Stmt]) = code.showCode(Some(stmts))

  protected[gui] def layoutObjects() = canvas.layoutObjects()

  protected[gui] def synthesizeLoop(initialMemory: Memory, loop: Iterate, loops: TMap[Iterate, Loop], curMemory: Memory): LoopFinalInfo = {
    depth += 1
    controls.discardAllEdits()  // TODO: I probably shouldn't call this off the Swing thread like this.
    val result = controller.synthesizeLoop(initialMemory, loop, loops, curMemory)
    depth -= 1
    result
  }

  protected[gui] def getCode() = code.getCode()

  protected[gui] def skipTrace(queryType: QueryType, sameInput: Boolean, saveChanges: Boolean) {
    queryType match {
      case Actions => controls.hideHoleControls()
      case ExprTrace => controls.finishExprTraceMode()
      case StmtTrace => 
	hideTraceControls()
	controls.discardAllEdits()
      case FixType => controls.hideFixingControls()
    }
    controller.skipTrace(queryType, sameInput, saveChanges)
  }

  protected[gui] def addBreakpoint(breakpoint: Breakpoint) = controller.addBreakpoint(breakpoint)

  protected[gui] def removeBreakpoint(line: Stmt) = controller.removeBreakpoint(line)

  protected[gui] def addEdit(e: javax.swing.undo.UndoableEdit) = controls.addEdit(e)

  def displayMessage(msg: String) = showMessage(this, msg, msg)
  def displayMessage(msg: String, title: String) = showMessage(this, msg, title)

  def clear() = canvas.clear()

}

object SynthesisGUI {

  private val TITLE = "Synthesis GUI"
  private val WIDTH = 1200
  private val HEIGHT = 1160
  private val CANVAS_PERCENTAGE = .75

  // we need to initialize the gui on the Swing thread, so we mark its constructor as private and call this instead.
  def makeGUI(controller: Controller, helperFunctions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], objectComparators: Map[String, (Value, Value) => Int], fieldLayouts: Map[String, List[List[String]]], objectLayouts: Map[String, ObjectLayout]): SynthesisGUI = {
    val waiter = new scala.concurrent.SyncVar[SynthesisGUI]
    javax.swing.SwingUtilities.invokeLater(new Runnable() {
      def run() = waiter.set(new SynthesisGUI(controller, helperFunctions, objectTypes, objectComparators, fieldLayouts, objectLayouts))
    })
    waiter.get
  }

  def showError(owner: java.awt.Component, error: String) = JOptionPane.showMessageDialog(owner, error, error, JOptionPane.ERROR_MESSAGE)
  def showMessage(owner: java.awt.Component, msg: String, title: String) = JOptionPane.showMessageDialog(owner, msg, title, JOptionPane.INFORMATION_MESSAGE)
  def showInputDialog(gui: SynthesisGUI, msg: String): Option[String] = JOptionPane.showInputDialog(gui, msg) match {
    case null => None
    case s => Some(s)
  }

}