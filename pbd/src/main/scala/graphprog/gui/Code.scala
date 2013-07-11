package graphprog.gui

import java.awt.Color
import javax.swing.{ JList, DefaultListModel, DefaultListCellRenderer, ListCellRenderer }
import Code._

protected[gui] class Code private (private val synthesisGUI: SynthesisGUI, private val model: DefaultListModel[ListData]) extends JList[ListData](model) {

  import graphprog.lang.AST.{ Stmt, Value, If }
  import graphprog.lang.Printer
  import graphprog.Utils._
  import graphprog.Controller.{ Breakpoint, NormalBreakpoint, ConditionalBreakpoint }

  private var elems: List[ListData] = Nil

  private var stmts: List[Stmt] = Nil
  private var curStmt: Option[Stmt] = None
  private var replacedStmts: List[Stmt] = Nil
  private var failingStmt: Option[Stmt] = None
  private var breakpoints: List[Breakpoint] = Nil

  private val printer = new Printer(Map.empty, true)

  def this(synthesisGUI: SynthesisGUI) = this(synthesisGUI, new DefaultListModel)

  private def init() {
    setCellRenderer(new ListCellRenderer[ListData] {
      import java.awt.Component
      import javax.swing._
      val realRenderer = new DefaultListCellRenderer()
      def getListCellRendererComponent(list: JList[_ <: ListData], value: ListData, index: Int, isSelected: Boolean, cellHasFocus: Boolean): Component = {
	val comp = realRenderer.asInstanceOf[ListCellRenderer[ListData]].getListCellRendererComponent(list, value, index, isSelected, cellHasFocus)
	realRenderer.setText("<html>" + value.displayStr + "</html>")
	return comp
      }
    })

    import java.awt.event.{ MouseAdapter, MouseEvent }
    addMouseListener(new MouseAdapter {
      import javax.swing.{ JPopupMenu, JMenuItem }
      import graphprog.lang.Compiler.parseOpt
      import graphprog.gui.SynthesisGUI.{ showInputDialog, showError }
      import graphprog.lang.AST.Expr

      private var cur: Option[ListData] = None

      private val popupMenu = new JPopupMenu
      setupControl(new JMenuItem("Add breakpoint"), popupMenu, _ => addBreakpoint(NormalBreakpoint(cur.get.stmt)))
      setupControl(new JMenuItem("Add conditional breakpoint"), popupMenu, _ => addConditionalBreakpoint())
      private val removeBreakpoint = new JMenuItem("Remove breakpoint")
      setupControl(removeBreakpoint, popupMenu, _ => removeBreakpoint(cur.get.stmt))

      private def addConditionalBreakpoint() {
	showInputDialog(synthesisGUI, "Enter condition") foreach { str => parseOpt(str) match {
	  case Some((c: Expr) :: Nil) => addBreakpoint(ConditionalBreakpoint(cur.get.stmt, c))
	  case _ => showError(synthesisGUI, "Please enter a single expression.")
	} }
      }

      private def addBreakpoint(breakpoint: Breakpoint) {
	breakpoints :+= breakpoint  // Add it to our list since otherwise we might not get notified of it immediately.
	synthesisGUI.addBreakpoint(breakpoint)
      }

      private def removeBreakpoint(line: Stmt) {
	breakpoints = breakpoints filterNot {_.line eq line }  // Remove it from our list since otherwise we might not get notified immediately.
	synthesisGUI.removeBreakpoint(line)
      }

      override def mousePressed(e: MouseEvent) = maybeShowPopup(e)
      override def mouseReleased(e: MouseEvent) = maybeShowPopup(e)
      private def maybeShowPopup(e: MouseEvent) {
	if (e.isPopupTrigger()) {
	  val curIndex = getIndexAtPoint(e.getPoint())
	  curIndex match {
	    case Some(i) => setSelectedIndex(i)
	    case None => clearSelection()
	  }
	  cur = curIndex map { i => elems(i) }
	  cur match {
	    case Some(cur) =>
	      removeBreakpoint.setEnabled(breakpoints.exists{ _.line eq cur.stmt })
	      popupMenu.show(e.getComponent(), e.getX(), e.getY())
	    case _ =>
	  }
	}
      }
    })
  }
  init()

  private def getIndexAtPoint(point: java.awt.Point): Option[Int] = {
    val index = locationToIndex(point)
    if (getCellBounds(index, index).contains(point))  // Without this anything below the last element will get the last element.
      Some(index)
    else
      None
  }

  override def getToolTipText(e: java.awt.event.MouseEvent): String = getIndexAtPoint(e.getPoint()).map{ i => elems(i).tooltipStr.getOrElse(null) }.getOrElse(null)

  def setCode(stmts: List[Stmt], curStmt: Option[Stmt], replacementStmts: Option[Iterable[Stmt]] = None, breakpoints: List[Breakpoint] = Nil, failingStmt: Option[Stmt] = None) = {
    this.stmts = stmts
    this.curStmt = curStmt
    this.failingStmt = failingStmt
    this.breakpoints = breakpoints
    showCode(replacementStmts)
  }

  // TODO: This code is ugly.  Clean it up and combine similar parts.
  def showCode(replacementStmts: Option[Iterable[Stmt]]) = {
    import graphprog.lang.AST.{ Conditional, Iterate, If, Loop, UnorderedStmts, Action, Expr, Unseen, PossibilitiesHole, UnknownJoinIf }
    import graphprog.lang.Printer.prettyStringOfStmt
    replacedStmts = (curStmt, replacementStmts) match {
      case (Some(curStmt), Some(replacementStmts)) =>
	def replaceAction(a: Action): List[Action] = a match {
	  case a if a eq curStmt => replacementStmts.toList.asInstanceOf[List[Action]]
	  case Conditional(c, b) => List(Conditional(c, replaceActions(b)))
	  case Iterate(is) => List(Iterate(is map { i => (i._1, replaceActions(i._2)) }))
	  case _ => List(a)
	}
	def replaceStmt(s: Stmt): List[Stmt] = s match {
	  case a: Action => replaceAction(a)
	  case s if s eq curStmt => replacementStmts.toList
	  case If(c, b, ei, e) => List(If(c, replaceStmts(b), ei map { p => (p._1, replaceStmts(p._2)) }, replaceStmts(e)))
	  case UnknownJoinIf(i, u) => List(UnknownJoinIf(singleton(replaceStmt(i)).asInstanceOf[If], replaceStmts(u)))
	  case Loop(c, b) => List(Loop(c, replaceStmts(b)))
	  case _ => List(s)
	}
	def replaceActions(as: List[Action]): List[Action] = as flatMap replaceAction
	def replaceStmts(ss: List[Stmt]): List[Stmt] = ss flatMap replaceStmt
	replaceStmts(stmts)
      case _ => stmts
    }
    def addStmts(s: Iterable[Stmt], parent: Option[Stmt], indent: String, isCurrent: Boolean, isFailing: Boolean): List[ListData] = {
      def addStmt(s: Stmt, parent: Option[Stmt], indent: String, isCurrent: Boolean, isFailing: Boolean): List[ListData] = {
	def doStmt(isCurrent: Boolean, isFailing: Boolean): List[ListData] = {
	  def colorify(s: String, color: String): String = "<font color='" + color + "'>" + s + "</font>"
	  def makeElem(s: Stmt, isExecutable: Boolean, displayString: String, hoverString: Option[String] = None, sanitize: Boolean = true): ListData = {
	    def htmlize(s: String): String = {
	      val sanitizedStr = if (sanitize) sanitizeHTML(s) else s
	      if (isCurrent) colorify(sanitizedStr, CUR_COLOR) else if (isFailing) colorify(sanitizedStr, FAILING_COLOR) else sanitizedStr
	    }
	    ListData(s, parent, htmlize(displayString), hoverString.map{ _.trim() }, isExecutable)
	  }
	  def pathHelper(prefix: String, s: Stmt, c: Option[Stmt], b: List[Stmt], indent: String = indent): List[ListData] = {
	    def stringOfCondition(s: Stmt, stringMaker: Stmt => String, htmlize: Boolean): String = {
	      val str = if (htmlize) sanitizeHTML(stringMaker(s)) else stringMaker(s)
	      (curStmt, replacementStmts) match {
		case (Some(curStmt), None) if s eq curStmt => colorify(str, CUR_COLOR)
		case _ => str
	      }
	    }
	    val body = addStmts(b, Some(s), indent + "  ", isCurrent, isFailing)
	    def getStartString(stringMaker: Stmt => String, htmlize: Boolean) = {
	      val space = if (htmlize) "&nbsp;" else " "
	      (if (htmlize) sanitizeHTML(indent + prefix) else indent + prefix) + (c match {
		case Some(c) => space + "(" + stringOfCondition(c, stringMaker, htmlize) + ")"
		case None => ""
	      }) + (body.size match {
		case 0 => space + ";"
		case 1 => ""
		case n => space + "{"
	      })
	    }
	    val noEnd = makeElem(s, c.isDefined, getStartString(c => prettyStringOfStmt(c, printer), true), c.collect{ case p: PossibilitiesHole => getStartString(c => printer.stringOfStmt(c), false) }, false) :: body
	    if (body.size > 1)
	      noEnd :+ makeElem(s, false, indent + "}")
	    else
	      noEnd
	  }
	  s match {
	    case Conditional(c, b) => pathHelper("cond", s, Some(c), b)
	    case Iterate(is) => (makeElem(s, false, indent + "iterate {") :: is.flatMap{ i => pathHelper("iteration", s, Some(i._1), i._2, indent + "  ") }) :+ makeElem(s, false, indent + "}")
	    case If(c, b, ei, e) => pathHelper("if", s, Some(c), b) ++ ei.flatMap{ p => pathHelper("else if", s, Some(p._1), p._2) } ++ (if (e.nonEmpty) pathHelper("else", s, None, e) else Nil)
	    case UnknownJoinIf(i, u) => addStmt(i, parent, indent, isCurrent, isFailing) ++ (if (u.nonEmpty) pathHelper("unknown", s, None, u) else Nil)
	    case Loop(c, b) => pathHelper("loop", s, Some(c), b)
	    case UnorderedStmts(stmts) => pathHelper("unordered", s, None, stmts)
	    case s => List(makeElem(s, true, indent + prettyStringOfStmt(s, printer), if (s.isInstanceOf[PossibilitiesHole]) Some(printer.stringOfStmt(s)) else None))
	  }
	}
	def isTargetStmt(s: Stmt, target: Option[Stmt]) = target match {
	  case Some(t) => s eq t
	  case None => false
	}
	(curStmt, replacementStmts) match {
	  case (Some(curStmt), Some(replacementStmts)) if s.eq(curStmt) => addStmts(replacementStmts, parent, indent, true, isTargetStmt(s, failingStmt))
	  case _ => doStmt(isCurrent || isTargetStmt(s, curStmt), isFailing || isTargetStmt(s, failingStmt))
	}
      }
      s.flatMap{ s => addStmt(s, parent, indent, isCurrent, isFailing) }.toList
    }
    val items = addStmts(stmts, None, "", false, false)
    def coalesceElses(l: List[ListData]): List[ListData] = l match {
      case x :: y :: rest => (x.displayStr, y.displayStr) match {
	case (s1: String, s2: String) if s1.matches("(?:&nbsp;)*}") && s2.startsWith("else") => (x copy (displayStr = (s1 + " " + s2))) :: coalesceElses(rest)  // TODO: Probably won't work for elses with non-zero indent.
	case _ => x :: coalesceElses(y :: rest)
      }
      case _ => l
    }
    elems = coalesceElses(items)
    model.clear()
    elems foreach { x => model.addElement(x) }
  }

  def getCode(): (List[Stmt], Option[Stmt]) = (stmts, curStmt)

  private def sanitizeHTML(s: String) = s.replaceAll(" ", "&nbsp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;")

}

private object Code {

  val CUR_COLOR = "blue"
  val FAILING_COLOR = "red"

  import graphprog.lang.AST.Stmt

  case class ListData(stmt: Stmt, parent: Option[Stmt], displayStr: String, tooltipStr: Option[String], isExecutable: Boolean)

}
