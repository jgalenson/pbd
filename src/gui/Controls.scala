package graphprog.gui.controls

import java.awt.event.{ ActionEvent, ActionListener, KeyEvent }
import javax.swing.{ JMenu, JMenuBar, JMenuItem, KeyStroke, JOptionPane, JButton, JLabel, JTextField, JPanel, Box }
import graphprog.lang.AST.Program
import graphprog.lang.Compiler.parseOpt
import graphprog.gui.{ Prog, BinaryOp, UnaryOp }
import graphprog.gui.SynthesisGUI
import graphprog.Utils._

private class Menu(private val synthesisGUI: SynthesisGUI, private val controls: Controls, private val functions: Iterable[Program]) extends JMenuBar {

  import Controls._

  private val trace = new JMenu("Trace")
  private val undo = new JMenuItem("Undo")
  private val redo = new JMenuItem("Redo")
  private val addPrim = new JMenuItem("Add primitive")
  private val addPointer = new JMenuItem("Add pointer")
  private val finishTrace = new JMenuItem("Finish Trace")
  private val startUnordered = new JMenuItem("Start unordered")
  private val endUnordered = new JMenuItem("End unordered block")
  private val startSnapshot = new JMenuItem("Start snapshot")
  private val endSnapshot = new JMenuItem("End snapshot")
  private val startConditional = new JMenuItem("Start conditional")
  private val endConditional = new JMenuItem("End conditional")
  private val startLoop = new JMenuItem("Start loop")
  private val endIteration = new JMenuItem("End iteration")
  private def starters = List(startUnordered, startSnapshot, startConditional, startLoop)
  private def enders = List(endUnordered, endSnapshot, endConditional, endIteration)
  private val hole = new JMenu("Hole")
  private val fixProgramFromTrace = new JMenuItem("Fix program")
  private val fixProgramFromHole = new JMenuItem("Fix program")
  private val fixProgram = new JMenu("Fix program")
  private val insertConditionalFromHole = new JMenuItem("Insert conditional")
  private val steper = new JMenuItem("Step")
  private val continuer = new JMenuItem("Continue")
  private val insertConditional = new JMenuItem("Insert conditional")
  private val endConditionalWhenFixing = new JMenuItem("End conditional")

  addFileMenu()
  addTraceMenu()
  addHoleMenu()
  addFixProgramMenu()

  private def addFileMenu() {
    val file = setupControl(new JMenu("File"), this, KeyEvent.VK_F)

    setupControl(new JMenuItem("Quit"), file, _ => synthesisGUI.doExit(), KeyEvent.VK_Q).setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Q, ActionEvent.CTRL_MASK))
  }

  private def addTraceMenu() {
    trace.setMnemonic(KeyEvent.VK_T)

    import graphprog.lang.AST.{ IntConstant, BooleanConstant }

    setupControl(new JMenuItem("Re-layout objects"), trace, _ => synthesisGUI.layoutObjects(), KeyEvent.VK_R)

    trace.addSeparator()

    setupControl(undo, trace, _ => controls.undo(), KeyEvent.VK_U).setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Z, ActionEvent.CTRL_MASK))
    undo.setEnabled(false)

    setupControl(redo, trace, _ => controls.redo(), KeyEvent.VK_R).setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Y, ActionEvent.CTRL_MASK))
    redo.setEnabled(false)

    trace.addSeparator()

    setupControl(addPrim, trace, _ => showInputDialog(synthesisGUI, "Enter the primitive's name.") foreach { n => synthesisGUI.addPrimVarToCanvas(n) }, KeyEvent.VK_M)

    setupControl(addPointer, trace, _ => showInputDialog(synthesisGUI, "Enter the pointer's name.") foreach { n => synthesisGUI.addPointerToCanvas(n) }, KeyEvent.VK_P)

    setupControl(new JMenuItem("Add int"), trace, _ => showInputDialog(synthesisGUI, "Enter an integer.") foreach { n => synthesisGUI.addPrimToCanvas(IntConstant(n.toInt)) }, KeyEvent.VK_I)

    val addBoolean = setupControl(new JMenu("Add boolean"), trace, KeyEvent.VK_O)
    List(true, false) foreach { b => setupControl(new JMenuItem(b.toString), addBoolean, _ => synthesisGUI.addPrimToCanvas(BooleanConstant(b))) }

    val addBuiltin = setupControl(new JMenu("Add builtin"), trace, KeyEvent.VK_B)
    builtins foreach { op => setupControl(new JMenuItem(op.name), addBuiltin, _ => synthesisGUI.addCallToCanvas(op)) }

    val addCall = setupControl(new JMenu("Add call"), trace, KeyEvent.VK_A)
    functions foreach { p => setupControl(new JMenuItem(p.name), addCall, _ => synthesisGUI.addCallToCanvas(Prog(p))) }
    addCall.setEnabled(functions.nonEmpty)

    setupControl(new JMenuItem("Add expression"), trace, _ => showInputDialog(synthesisGUI, "Enter an expression.") foreach { s => controls.addActionIfValid(s) }, KeyEvent.VK_X)

    trace.addSeparator()

    setupControl(startUnordered, trace, _ => controls.startBlock(Unordered), KeyEvent.VK_U)
    setupControl(endUnordered, trace, _ => controls.endBlock(), KeyEvent.VK_E)

    setupControl(startSnapshot, trace, _ => controls.startBlock(Snapshot), KeyEvent.VK_S)
    setupControl(endSnapshot, trace, _ => controls.endBlock(), KeyEvent.VK_E)

    setupControl(startConditional, trace, _ => controls.startBlock(Conditional(false)), KeyEvent.VK_C)
    setupControl(endConditional, trace, _ => controls.endBlock(), KeyEvent.VK_E)

    setupControl(startLoop, trace, _ => controls.startBlock(Loop(false)), KeyEvent.VK_L)
    setupControl(endIteration, trace, _ => controls.endBlock(), KeyEvent.VK_E)

    trace.addSeparator()

    setupControl(fixProgramFromTrace, trace, _ => controls.setNoTrace())

    trace.addSeparator()

    setupControl(finishTrace, trace, _ => controls.endBlock(), KeyEvent.VK_F)

    trace.setEnabled(false)
    add(trace)
  }

  def addHoleMenu() {
    hole.setMnemonic(KeyEvent.VK_H)

    setupControl(fixProgramFromHole, hole, _ => synthesisGUI.setNoAction())

    setupControl(insertConditionalFromHole, hole, _ => synthesisGUI.insertConditionalAtPoint(), KeyEvent.VK_I)

    hole.setEnabled(false)
    add(hole)
  }

  def addFixProgramMenu() {
    fixProgram.setMnemonic(KeyEvent.VK_F)

    setupControl(steper, fixProgram, _ => synthesisGUI.step(), KeyEvent.VK_S)

    setupControl(continuer, fixProgram, _ => synthesisGUI.continue(), KeyEvent.VK_C)

    setupControl(insertConditional, fixProgram, _ => synthesisGUI.insertConditionalAtPoint(), KeyEvent.VK_I)

    setupControl(endConditionalWhenFixing, fixProgram, _ => synthesisGUI.endConditional(), KeyEvent.VK_E)

    fixProgram.setEnabled(false)
    add(fixProgram)
  }

  def showTraceMenu() = trace.setEnabled(true)
  def hideTraceMenu() = trace.setEnabled(false)
  def showHoleMenu() = hole.setEnabled(true)
  def hideHoleMenu() = hole.setEnabled(false)
  def enableDisableFixProgramStarters(flag: Boolean) {
    fixProgramFromTrace.setEnabled(flag)
    fixProgramFromHole.setEnabled(flag)
  }
  def showFixProgram(canContinue: Boolean, amInConditional: Boolean) {
    fixProgram.setEnabled(true)
    steper.setEnabled(canContinue)
    continuer.setEnabled(canContinue && !amInConditional)  // We need the user to mark the end of the conditional, so don't let them continue.
    insertConditionalFromHole.setEnabled(!amInConditional)
    insertConditional.setEnabled(!amInConditional)
    endConditionalWhenFixing.setEnabled(amInConditional)
  }
  def hideFixProgram() {
    fixProgram.setEnabled(false)
    insertConditionalFromHole.setEnabled(false)
  }

  def conditionSetOrUnset(curBlock: Block, given: Boolean) {
    starters.foreach{ _.setEnabled(given) }
    ender(curBlock).setEnabled(given)
  }

  private def ender(block: Block): JMenuItem = block match {
    case _: Trace => finishTrace
    case Unordered => endUnordered
    case Snapshot => endSnapshot
    case Conditional(_) => endConditional
    case Loop(_) => endIteration
  }
  private def newCurBlock(block: Block) = block match {
    case Trace(isExpr, _, isConditional) =>
      starters.foreach{ _.setEnabled(!isExpr) }
      enders.foreach{ _.setEnabled(false) }
      finishTrace.setEnabled(!isExpr)
      List(addPrim, addPointer).foreach{ _.setEnabled(!isExpr) }
      controls.showTraceControls()
      if (isConditional)
	finishTrace.setLabel("Finish conditional")
      else
	finishTrace.setLabel("Finish Trace")
    case Unordered => startUnordered.setEnabled(false)
    case Snapshot => starters.foreach{ _.setEnabled(false) }
    case b: BlockWithCondition =>
      if (!b.seenCondition) {
	starters.foreach{ _.setEnabled(false) }
	ender(block).setEnabled(false)
      }
  }
  protected[controls] def startBlock(block: Block) {
    val end = ender(block)
    enders.foreach{ e => if (e eq end) e.setEnabled(true) else e.setEnabled(false) }
    finishTrace.setEnabled(false)
    newCurBlock(block)
  }
  protected[controls] def endBlock(curBlock: Block, nextBlock: Option[Block]) {
    starters.foreach{ _.setEnabled(true) }
    ender(curBlock).setEnabled(false)
    nextBlock foreach { block => {
      newCurBlock(block)
      ender(block).setEnabled(true)
    } }
  }

  def refreshUndoRedo(undoManager: javax.swing.undo.UndoManager) {
    undo.setEnabled(undoManager.canUndo())
    if (undo.isEnabled())
      undo.setText(undoManager.getUndoPresentationName())
    else
      undo.setText("Undo")
    redo.setEnabled(undoManager.canRedo())
    if (redo.isEnabled())
      redo.setText(undoManager.getRedoPresentationName())
    else
      redo.setText("Redo")
  }

}

private class Toolbar(private val synthesisGUI: SynthesisGUI, private val controls: Controls, private val functions: Iterable[Program]) extends JPanel {

  import Controls._

  private val ender = new JButton("End trace")
  private val stepButton = new JButton("Step")
  private val continueButton = new JButton("Continue")
  private val insertConditionalButton = new JButton("Insert conditional")
  private val endConditionalButton = new JButton("End conditional")

  private val traceBox = makeTraceToolbar()
  private val fixProgramBox = makeFixProgramToolbar()
  private val emptyBox = makeEmptyBox()

  private var shown = emptyBox  // Prevents losing focus in the textbox by removing it and instantly re-adding it.

  add(emptyBox)

  private def makeTraceToolbar(): Box = {
    val box = Box.createHorizontalBox()

    box.add(new JLabel("Add expression: "))

    val exprInput = new JTextField
    exprInput.addActionListener(new ActionListener() {
      def actionPerformed(e: ActionEvent) = { controls.addActionIfValid(exprInput.getText()); exprInput.setText("") }
    })
    exprInput.setPreferredSize(new java.awt.Dimension(150, 20))
    box.add(exprInput)

    box.add(Box.createHorizontalStrut(5))

    setupControl(new JButton("Add expression"), box, _ => { controls.addActionIfValid(exprInput.getText()); exprInput.setText("") })

    box.add(Box.createHorizontalStrut(10))

    setupControl(ender, box, _ => controls.endBlock())

    box
  }

  private def makeFixProgramToolbar(): Box = {
    val box = Box.createHorizontalBox()

    setupControl(stepButton, box, _ => synthesisGUI.step())

    box.add(Box.createHorizontalStrut(10))

    setupControl(continueButton, box, _ => synthesisGUI.continue())

    box.add(Box.createHorizontalStrut(10))

    setupControl(insertConditionalButton, box, _ => synthesisGUI.insertConditionalAtPoint())

    setupControl(endConditionalButton, box, _ => synthesisGUI.endConditional())

    box
  }

  private def makeEmptyBox(): Box = {
    val emptyBox = Box.createHorizontalBox()
    emptyBox.setPreferredSize(traceBox.getPreferredSize())
    emptyBox
  }
  
  def showTraceToolbar() = showToolbar(traceBox)
  def showFixProgramToolbar(canContinue: Boolean, amInConditional: Boolean) {
    stepButton.setEnabled(canContinue)
    continueButton.setEnabled(canContinue && !amInConditional)  // We need the user to mark the end of the conditional, so don't let them continue.
    insertConditionalButton.setEnabled(!amInConditional)
    endConditionalButton.setEnabled(amInConditional)
    showToolbar(fixProgramBox)
  }
  def emptyToolbar() = showToolbar(emptyBox)
  private def showToolbar(box: Box) {
    if (shown != box) {
      remove(shown)
      add(box)
      shown = box
      validate()
      repaint()
    }
  }

  def nextBlock(block: Option[Block]) = block match {
    case None => ender.setEnabled(false)
    case Some(b) =>
      b match {
	case Trace(true, _, _) => ender.setEnabled(false)
	case _ => ender.setEnabled(true)
      }
      b match {
	case Trace(_, _, false) => ender.setLabel("Finish trace")
	case Trace(_, _, true) => ender.setLabel("End conditional")
	case Unordered => ender.setLabel("End unordered")
	case Snapshot => ender.setLabel("End snapshot")
	case Conditional(_) => ender.setLabel("End conditional")
	case Loop(_) => ender.setLabel("End iteration")
      }
  }

}

protected[gui] class Controls(private val synthesisGUI: SynthesisGUI, private val functions: Iterable[Program]) {

  import Controls._
  import javax.swing.undo.{ UndoableEdit, UndoManager, AbstractUndoableEdit }

  private val menu = new Menu(synthesisGUI, this, functions)
  private val toolbar = new Toolbar(synthesisGUI, this, functions)

  private val curBlocks = new scala.collection.mutable.Stack[Block]
  private val undoManager = new UndoManager

  def startTraceMode(isExpr: Boolean, allowFixing: Boolean, isConditional: Boolean) {
    startBlock(Trace(isExpr, allowFixing, isConditional))
  }
  def finishExprTraceMode() = {
    assert(curBlocks.headOption match { case Some(Trace(true, _, _)) => true case _ => false })
    endBlock()
  }
  def finishStmtTraceMode() = {
    assert(curBlocks.headOption match { case Some(Trace(false, _, _)) => true case _ => false })
    endBlock(true)
  }
  def showTraceControls() {
    menu.enableDisableFixProgramStarters(curBlocks.collect{ case Trace(_, allowFixing, _) => allowFixing }.head)
    menu.showTraceMenu()
    toolbar.showTraceToolbar()
  }
  def hideTraceControls() {
    menu.hideTraceMenu()
    toolbar.emptyToolbar()
  }
  def conditionSetOrUnset(given: Boolean) = {
    curBlocks.push((curBlocks.pop: @unchecked) match {
      case Conditional(g) if given != g => Conditional(given)
      case Loop(g) if given != g => Loop(given)
    })
    menu.conditionSetOrUnset(curBlocks.head, given)
  }
  def showHoleControls(allowFixing: Boolean) {
    menu.showHoleMenu()
    menu.enableDisableFixProgramStarters(allowFixing)
  }
  def hideHoleControls() = menu.hideHoleMenu()
  def showFixingControls(canContinue: Boolean, amInConditional: Boolean) {
    menu.showFixProgram(canContinue, amInConditional)
    toolbar.showFixProgramToolbar(canContinue, amInConditional)
  }
  def hideFixingControls() {
    menu.hideFixProgram()
    toolbar.emptyToolbar()
  }

  def setNoTrace() {
    synthesisGUI.setNoTrace(curBlocks.collect{ case Trace(isExpr, true, _) => isExpr }.head)
  }

  def addEdit(e: UndoableEdit) {
    undoManager.addEdit(e)
    menu.refreshUndoRedo(undoManager)
  }
  def undo() {
    undoManager.undo()
    menu.refreshUndoRedo(undoManager)
  }
  def redo() {
    undoManager.redo()
    menu.refreshUndoRedo(undoManager)
  }
  def discardAllEdits() {
    undoManager.discardAllEdits()
    menu.refreshUndoRedo(undoManager)
  }

  def getMenu(): JMenuBar = menu
  def getToolbar(): JPanel = toolbar
  def getHeight(): Int = menu.getHeight() + toolbar.getHeight()

  private def addBlock(block: Block) {
    curBlocks push block
    menu.startBlock(block)
    toolbar.nextBlock(Some(block))
  }
  protected[controls] def startBlock(block: Block) {
    def doStart(f: => Unit) {
      undoManager.addEdit(new StartBlockEdit(block))
      f
    }
    addBlock(block)
    block match {
      case Unordered => doStart(synthesisGUI.startUnordered())
      case Snapshot => doStart(synthesisGUI.startSnapshot())
      case Conditional(false) => doStart(synthesisGUI.startConditional())
      case Loop(false) => doStart(synthesisGUI.startLoop())
      case _: Trace =>
    }
  }
  private def removeBlock(): Block = {
    val curBlock = curBlocks.pop
    val nextBlock = curBlocks.headOption
    menu.endBlock(curBlock, nextBlock)
    toolbar.nextBlock(nextBlock)
    curBlocks.headOption match {
      case None => hideTraceControls()
      case Some(_) => showTraceControls()
    }
    curBlock match {
      case _: Trace => hideTraceControls()  // We need this since we could be synthesizing a loop and get a possibilities question.  When we finish the loop, Canvas will ensure that the trace menu is enabled.
      case _ =>
    }
    curBlock
  }
  protected[controls] def endBlock(guiAlreadyEnded: Boolean = false) {
    def doEnd(curBlock: Block) {
      undoManager.addEdit(new EndBlockEdit(curBlock))
      synthesisGUI.finishBlock()
    }
    val curBlock = removeBlock()
    curBlock match {
      case Trace(isExpr, _, _) => 
	if (!isExpr && !guiAlreadyEnded)
	  synthesisGUI.finishStmtTrace()  // ExprTrace is ended by Canvas, not Controls
      case Loop(true) => synthesisGUI.finishIteration()
      case _ => doEnd(curBlock)
    }
  }
  protected[controls] def addActionIfValid(str: String, shouldDoExpr: Boolean = true) {
    def isLegalStart(newBlock: Block) = curBlocks.headOption match {
      case Some(curBlock) => curBlock match {
	case Trace(isExpr, _, _) => !isExpr
	case Unordered => newBlock != Unordered
	case Snapshot => false
	case b: BlockWithCondition => b.seenCondition
      }
      case None => false
    }
    def isLegalEnd() = curBlocks.headOption match {
      case Some(curBlock) => curBlock match {
	case b: BlockWithCondition if !b.seenCondition => false
	case _ => true
      }
      case None => false
    }
    def tryStartBlock(newBlock: Block) {
      if (isLegalStart(newBlock))
	startBlock(newBlock)
      else
	SynthesisGUI.showError(synthesisGUI, "Cannot start block: " + newBlock)
    }
    val conditionalPattern = """:conditional(?: (.*))?""".r
    val loopPattern = """:loop(?: (.*))?""".r
    def addAction(str: String) = str match {
      case ":unordered" => tryStartBlock(Unordered)
      case ":snapshot" => tryStartBlock(Snapshot)
      case conditionalPattern(rest) =>
	tryStartBlock(Conditional(false))
	if (rest != null)
	  addActionIfValid(rest, true)
      case loopPattern(rest) =>
	tryStartBlock(Loop(false))
	if (rest != null)
	  addActionIfValid(rest, true)
      case ":end" =>
	if (isLegalEnd())
	  endBlock()
	else
	  SynthesisGUI.showError(synthesisGUI, "Cannot end block")
      case _ => parseOpt(str) match {
	case Some(a :: Nil) => synthesisGUI.addActionToCanvas(a, shouldDoExpr)
	case None => SynthesisGUI.showError(synthesisGUI, "Please enter a valid expression.")
	case r => assert(false, str + " got " + r)
      }
    }
    str.split(";") foreach { s => addAction(s.trim()) }
  }

  private abstract class BlockEdit(block: Block) extends AbstractUndoableEdit {
    protected var childEdit: Option[UndoableEdit] = None
    override def canUndo() = childEdit.isDefined
    override def canRedo() = childEdit.isDefined
    override def addEdit(other: UndoableEdit): Boolean = {
      val canAdd = childEdit.isEmpty
      if (canAdd)
	childEdit = Some(other)
      canAdd
    }
  }
  private class StartBlockEdit(block: Block) extends BlockEdit(block) {
    override def getPresentationName(): String = "start " + block.toString
    override def undo() {
      assert(curBlocks.top == block)
      removeBlock()
      childEdit.get.undo()
    }
    override def redo(){
      addBlock(block)
      childEdit.get.redo()
    }
  }
  private class EndBlockEdit(block: Block) extends BlockEdit(block) {
    override def getPresentationName(): String = "finish " + block.toString
    override def undo(){
      addBlock(block)
      childEdit.get.undo()
    }
    override def redo() {
      assert(curBlocks.top == block)
      removeBlock()
      childEdit.get.redo()
    }
  }

}

private object Controls {

  import graphprog.lang.AST.{ Plus, Minus, Times, Div, EQ, NE, LT, LE, GT, GE, And, Or, Not, Var, IntType, BooleanType, GenericType, Action }

  val builtins = List(BinaryOp("+", (l, r) => Plus(l, r), (IntType, IntType)),
		      BinaryOp("-", (l, r) => Minus(l, r), (IntType, IntType)),
		      BinaryOp("*", (l, r) => Times(l, r), (IntType, IntType)),
		      BinaryOp("/", (l, r) => Div(l, r), (IntType, IntType)),
		      BinaryOp("=", (l, r) => EQ(l, r), (GenericType, GenericType)),
		      BinaryOp("!=", (l, r) => NE(l, r), (GenericType, GenericType)),
		      BinaryOp("<", (l, r) => LT(l, r), (IntType, IntType)),
		      BinaryOp("<=", (l, r) => LE(l, r), (IntType, IntType)),
		      BinaryOp(">", (l, r) => GT(l, r), (IntType, IntType)),
		      BinaryOp(">=", (l, r) => GE(l, r), (IntType, IntType)),
		      BinaryOp("&&", (l, r) => And(l, r), (BooleanType, BooleanType)),
		      BinaryOp("||", (l, r) => Or(l, r), (BooleanType, BooleanType)),
		      UnaryOp("!", b => Not(b), BooleanType))

  abstract class Block
  case class Trace(isExpr: Boolean, allowFixing: Boolean, isConditional: Boolean) extends Block
  case object Unordered extends Block {
    override def toString: String = "unordered"
  }
  case object Snapshot extends Block {
    override def toString: String = "snapshot"
  }
  abstract class BlockWithCondition extends Block { val seenCondition: Boolean }
  case class Conditional(seenCondition: Boolean) extends BlockWithCondition {
    override def toString: String = "conditional"
  }
  case class Loop(seenCondition: Boolean) extends BlockWithCondition {
    override def toString: String = "iteration"
  }

  def showInputDialog(gui: SynthesisGUI, msg: String): Option[String] = JOptionPane.showInputDialog(gui, msg) match {
    case null => None
    case s => Some(s)
  }

}
