package graphprog.gui

import java.awt.{ Color, Graphics, Graphics2D, Rectangle }
import javax.swing.{ JPanel }
import scala.collection.mutable.{ Map, Set, ListBuffer }
import scala.collection.immutable.{ Map => IMap, Set => ISet }
import Canvas._
import Shape._
import graphprog.lang.AST.{ Program, Type, Value }
import graphprog.Utils._
import graphprog.Controller._
import scala.collection.{ Map => TMap }

// TODO: Improve layout.  Maybe remove code from createShape and instead add a new function that movies things that have been created (and call it after creating all of them).
protected[gui] class Canvas(private val gui: SynthesisGUI, private val helperFunctions: IMap[String, Program], private val objectTypes: IMap[String, List[(String, Type)]], private val objectComparators: IMap[String, (Value, Value) => Int], private val fieldLayouts: IMap[String, List[List[String]]], private val objectLayouts: IMap[String, ObjectLayout]) extends JPanel {

  import graphprog.lang.AST.{ Action, IntArray, IntConstant, Null, Object, Primitive, Value, Assign, Var => ASTVar, Call, HeapValue, Expr, Stmt, Iterate, Loop, BooleanConstant }
  import graphprog.lang.{ Printer, Executor, Typer, Memory }
  import java.awt.event.{ MouseAdapter, MouseEvent, MouseMotionAdapter, MouseWheelListener, MouseWheelEvent }
  import scala.annotation.tailrec

  private val variables = Map.empty[String, Var]
  private val objects = Map.empty[Int, Obj]
  private val arrays = Map.empty[Int, IntArr]
  private val nulls = ListBuffer.empty[NullShape]
  private def toplevelShapes = variables.valuesIterator ++ objects.valuesIterator ++ arrays.valuesIterator ++ newDiffShapes.toIterator ++ nulls.toIterator ++ modeShapes ++ (held match {
    case Mutation(s) => Iterator.single(s)
    case _ => Iterator.empty
  })
  private def modeShapes: Iterator[Shape] = mode match {
    case SelectQuery(_, _, newShapes) => newShapes.toIterator
    case AssignQuery(_, _, _, _, newShapes, _) => newShapes.toIterator
    case trace: Trace => trace.newShapes.toIterator
    case _ => Iterator.empty
  }
  private def modeArrows: Iterator[Arrow] = mode match {
    case AssignQuery(_, _, _, _, _, newArrows) => newArrows.keys.toIterator
    case _ => Iterator.empty
  }
  private def modeArrowsAndShapes: Iterator[(Arrow, (Shape, Shape))] = mode match {
    case AssignQuery(_, _, _, _, _, newArrows) => newArrows.toIterator
    case _ => Iterator.empty
  }
  private def getHeapShape(value: HeapValue): HeapObject = value match {
    case IntArray(id, _) => arrays(id)
    case Object(id, _, _) => objects(id)
    case Null => nulls.head
  }
  private val fields = Map.empty[Int, Map[String, Field]]
  private val arrElems = Map.empty[Int, List[IntArrAccess]]
  private val arrLens = Map.empty[Int, ArrLen]
  private def getChildren(shape: Shape): Iterable[Shape] = shape match {
    case Obj(Object(id, _, _), _, _, _, _) => fields(id).values
    case IntArr(IntArray(id, _), _, _, _, _) => arrLens(id) :: arrElems(id)
    case _ => Nil
  }
  private def allShapes = toplevelShapes.toList flatMap { shape => getChildren(shape) ++ List(shape) }

  // IVars for tracking what mode we're in (e.g. just observing memory, answering a query, etc).
  private trait InteractionMode
  private case object Observer extends InteractionMode
  private abstract class QueryMode extends InteractionMode
  private case class SelectQuery(possibilitiesSet: ISet[Shape], possibilitiesMap: IMap[Shape, List[Action]], newShapes: ISet[Shape]) extends QueryMode
  private case class AssignQuery(possibilities: IMap[Shape, IMap[Shape, List[Action]]], lefts: ISet[Shape], rights: ISet[Shape], rightMap: IMap[Shape, ISet[Shape]], newShapes: ISet[Shape], newArrows: IMap[Arrow, (Shape, Shape)]) extends QueryMode
  private abstract class Trace extends InteractionMode { val newShapes: Set[Shape] }
  private case class StmtTrace(actions: ListBuffer[Action], var curBlocks: List[TraceBlock], loops: Map[Iterate, Loop], newShapes: Set[Shape], var initMem: Memory, joinFinder: Option[(List[Action] => Option[List[Stmt]])]) extends Trace  // curBlocks has inner blocks at the beginning, initMem is  clone of memory after finishing the previous statement.
  private case class ExprTrace(newShapes: Set[Shape]) extends Trace  // Currently only for boolean expressions: see comment in doExpr.  This would be easy to change if necessary (probably just add type as ivar).
  private var mode: InteractionMode = Observer
  private abstract class TraceBlock
  private case class UnorderedTrace(s: ListBuffer[Action]) extends TraceBlock
  private case object SnapshotTrace extends TraceBlock
  private case class ConditionalTrace(var condition: Option[Expr], body: ListBuffer[Action]) extends TraceBlock
  private case class LoopTrace(var condition: Option[Action], body: ListBuffer[Action], initialMemory: Memory) extends TraceBlock

  private val newDiffShapes = Set.empty[Shape]
  private val diffShapes = Set.empty[Shape]
  private val diffArrows = Set.empty[Arrow]
  private val diffArrowMap = Map.empty[Pointer, List[Arrow]]
  private val oldDiffArrows = Set.empty[Arrow]
  private val diffOriginalVals = Set.empty[() => Unit]

  private val printer = new Printer(Map[String, Value => String](), true)
  private val executor = new Executor(helperFunctions, printer)
  private val typer = new Typer(helperFunctions, objectTypes)

  // IVars for mouse movement
  private var (startX, startY) = (0, 0)  // starting position for snapping back.
  private var (lastX, lastY) = (0, 0)  // Store the last location so we can do relative movement since we don't know where in the shape the mouse is.
  // Info for dragging
  private trait HeldShape {
    def isSomething(): Boolean = this != NoHeld
    def forShape(f: Shape => Unit) = this match {
      case Movement(shape) => f(shape)
      case Mutation(shape) => f(shape)
      case _ =>
    }
    def forArrow(f: Arrow => Unit) = this match {
      case FlyingArrow(arrow) => f(arrow)
      case _ =>
    }
  }
  private trait NonMutation extends HeldShape
  private case object NoHeld extends NonMutation
  private case class Movement(shape: Shape) extends NonMutation
  private case class Mutation(shape: Shadow) extends HeldShape
  private case class FlyingArrow(arrow: Arrow) extends HeldShape
  private var held: HeldShape = NoHeld
  // We store this so we can redraw all arrows pointing to the shape the user is moving.
  private val pointees = Map.empty[Option[Shape], Set[Arrow]]
  private def getArrowsTo(shape: Shape): Iterable[Arrow] = {
    def arrowsToShape(shape: Shape) = pointees.getOrElse(Some(shape), Nil.asInstanceOf[Iterable[Arrow]])
    arrowsToShape(shape) ++ modeShapes.toList.flatMap(arrowsToShape) ++ modeArrowsAndShapes.collect{ case (a, (_, d)) if d eq shape => a }
  }
  private def getArrowsFrom(shape: Shape): Iterable[Arrow] = (shape match {
    case p @ Pointer(_, a, _, _, _, _) => a :: diffArrowMap.getOrElse(p, Nil)
    case call: FuncCall => call.getAllArrows()
    case c: Child[_, _] => getArrowsFrom(c.child)
    case _ => Nil
  }) ++ modeArrowsAndShapes.collect{ case (a, (s, _)) if s eq shape => a }
  private val arrowSources = Map.empty[Arrow, Shape]
  private def arrows = pointees.flatMap{ kv => kv._2 }
  // IVars for tooltip
  private var tooltip: Option[Tooltip] = None
  // IVars for hovering over Calls
  private var hoveringCall: Option[FuncCall] = None

  // Initialize the Canvas and set an iVar needed for tooltips.
  private val (tooltipListener, callHoverListener) = setup()

  private def setup(): (MouseMotionAdapter, MouseMotionAdapter) = {
    setBackground(Color.WHITE)

    // Mouse/shape movement code
    def moveShapeAndRepaint(shape: Shape, dx: Int, dy: Int) = mutateAndDoubleRepaint(shape, moveShape(shape, dx, dy, getChildren, getArrowsTo, getArrowsFrom))
    def moveArrowAndRepaint(arrow: Arrow, mover: Arrow => Unit) {
      val initialBounds = boundsOfArrow(arrow)
      mover(arrow)
      smartRepaintBounds(List(initialBounds, boundsOfArrow(arrow)))
    }
    def getBounds(held: HeldShape): List[Rectangle] = (held, mode) match {
      case (Mutation(heldCopy @ Shadow(heldOrig, _, _)), AssignQuery(possibilitiesMap, lefts, rights, rightMap, _, newArrows)) =>
	val invalidLefts = lefts -- rightMap(heldOrig)  // These change from red to black (things that cannot be assigned this).
	val invalidRights = rights -- rightMap(heldOrig) - heldOrig  // These change from green to black.
	val doubleLefts = rights.filter{ rhs => possibilitiesMap.contains(rhs) && possibilitiesMap(rhs).contains(heldOrig) }  // These change from green to red (things that are on some RHS and this LHS).
	val arrowEndpoints = newArrows.flatMap{ case (_, (s, d)) => List(s, d) }
	(List(heldCopy, heldOrig) ++ invalidLefts ++ invalidRights ++ doubleLefts ++ arrowEndpoints).map(boundsOfShape _)
      case (Mutation(heldCopy @ Shadow(heldOrig, _, _)), mode: Trace) =>
	List(boundsOfShape(heldCopy), boundsOfShape(heldOrig)) ++ allShapes.filter{ shape => canReceive(shape, heldOrig, mode) }.map(boundsOfShape)
      case (FlyingArrow(arrow), mode: Trace) =>
	val source = arrowSources(arrow)
	allShapes.filter{ shape => canReceive(source, shape, mode) }.map(boundsOfShape)  // I deal with repainting the arrow's bounds in the caller.
      case _ => Nil
    }
    // Repaint parts of the screen if necessary when the user presses or releases the mouse.  Called with the held value (i.e. the shape if the mouse was released).
    def changeHeld(newHeld: HeldShape, x: Int, y: Int, oldBounds: Option[List[Rectangle]] = None) {
      if (newHeld.isSomething()) {
	startX = x
	startY = y
	lastX = x
	lastY = y
      }
      val oldHeld = held
      held = newHeld
      smartRepaintBounds(getBounds(oldHeld) ++ getBounds(newHeld) ++ oldBounds.getOrElse(Nil))
    }
    def removeTooltip(t: Tooltip) {
      tooltip = None
      smartRepaint(boundsOfShape(t))
    }
    def findLegalInnerShape(x: Int, y: Int, legalShapes: ISet[Shape]): Option[Shape] = findInnerShape(x, y, legalShapes) match {
      case Some(c: Child[_, _]) => Some(if (legalShapes contains c) c else c.parent)
      case s => s
    }
    // TODO-low: Use Swing tooltips.  See JComponent.getToolTip{Location,Text} versions that take mouseEvents.  Canvas can implement those to return the location/string, and this can simply set them into an ivar.  Unfortunately, those currently seem to fail, probably due to xmonad/Java not liking each other.
    val tooltipListener = new MouseMotionAdapter() {
      override def mouseMoved(e: MouseEvent) {
	assert (held == NoHeld)
	val (x, y) = (e.getX(), e.getY())
	val (validShapes, validArrows, shapeActionFn, arrowActionFn) = (mode: @unchecked) match {
	  case SelectQuery(s, m, _) => (s, IMap.empty[Arrow, Set[(Shape, Shape)]], (s: Shape) => m(s), (a: Arrow) => List.empty[Action])
	  case AssignQuery(m, lSet, rSet, r, _, newArrows) => (lSet ++ rSet, newArrows, (s: Shape) => ((if (lSet.contains(s)) m(s).values.flatten.toList else Nil) ++ (if (rSet.contains(s)) r(s).flatMap{ l => m(l)(s) }.toList else Nil)).distinct, (a: Arrow) => newArrows(a) match { case (l, r) => m(l)(r) })
	}
	def addTooltip(sa: Either[Shape, Arrow]) {
	  val g = e.getComponent().getGraphics()
	  val msgs = (sa match {
	    case Left(s) => shapeActionFn(s)
	    case Right(a) => arrowActionFn(a)
	  }).map{ a => printer.stringOfAction(a) }.foldLeft(List[String]()){ case (revLines, cur) => revLines match {
	    case Nil => List(cur)
	    case curLine :: rest =>
	      val next = curLine + " or " + cur
	      if (x + stringWidth(g, next) <= getWidth())
		next :: rest
	      else
		("or " + cur) :: revLines
	  } }.reverse
	  val t = Tooltip(msgs, sa match { case Left(s) => s case Right(a) => null }, x, y + TOOLTIP_VOFFSET, msgs.map{ s => stringWidth(g, s) }.max, msgs.map{ s => heightOfString(s, g) }.sum)
	  tooltip = Some(t)
	  smartRepaint(boundsOfShape(t))
	}
	(tooltip, findLegalInnerShape(x, y, validShapes), findArrowBodies(x, y, validArrows.keys)) match {
	  case (Some(t), Some(s), _) if (t.shape eq s) => moveShapeAndRepaint(t, x - t.x, y - t.y + TOOLTIP_VOFFSET)
	  case (Some(t), Some(s), _) =>
	    removeTooltip(t)
	    addTooltip(Left(s))
	  case (Some(t), None, arrows) if arrows.nonEmpty =>
	    removeTooltip(t)
	    addTooltip(Right(arrows.head))
	  case (Some(t), None, _) => removeTooltip(t)
	  case (None, Some(s), _) if validShapes.contains(s) => addTooltip(Left(s))
	  case (None, None, arrows) if arrows.nonEmpty => addTooltip(Right(arrows.head))
	  case _ =>
	}
      }
    }
    def addTooltipListener() = mode match {
      case _: SelectQuery | _: AssignQuery => addMouseMotionListener(tooltipListener)
      case _ =>
    }
    def hoverOverCall(call: FuncCall) {
      unhoverCall()
      hoveringCall = Some(call)
      call.isHovering = true
      call.getAllArrows.foreach{ a => a.isFlying = true }
      smartRepaintBounds(getAllBounds(call))
    }
    val callHoverListener = new MouseMotionAdapter() {
      override def mouseMoved(e: MouseEvent) {
	val (x, y) = (e.getX(), e.getY())
	val calls = modeShapes.filter{ _.isInstanceOf[FuncCall] }
	(hoveringCall, findShape(x, y, calls)) match {
	  case (None, Some(call @ FuncCall(_, _, _, _, _, _, _, _, _, false))) => hoverOverCall(call)
	  case (Some(call), None) => unhoverCall()
	  case _ =>
	}
      }
    }
    def possibilitySelected(actions: List[Action]) {
      gui.setActions(Actions(actions))
      leaveQueryMode()
    }
    def snapBackArrow(arrow: Arrow, x: Int, y: Int) = {
      if (arrow.target.isEmpty)
	moveArrowAndRepaint(arrow, a => { val src = arrowSources(a); a.srcX = src.x; a.srcY = src.y; a.dstX = src.x + src.width; a.dstY = src.y + src.height })  // Reset a null arrow.
      else
	moveArrowAndRepaint(arrow, arrow => { arrow.dstX += startX - x; arrow.dstY += startY - y })  // Snap back the arrow.
    }
    // TODO: Ideally I would probably use a key listener rather than mouse wheel.
    val arrowSwitcherListener = new MouseWheelListener() {
      override def mouseWheelMoved(e: MouseWheelEvent) {
	val allArrows = findArrows(lastX, lastY)
	if (allArrows.size > 1) {
	  val notches = e.getWheelRotation()
	  val oldArrow = held.asInstanceOf[FlyingArrow].arrow
	  val newArrow = allArrows((allArrows.indexOf(oldArrow) + notches + allArrows.size) % allArrows.size)  // Add allArrows.size to avoid crashing when you keep scrolling up (and get to 0 - 1 % n).
	  assert(newArrow != oldArrow)
	  val (x, y) = (e.getX(), e.getY())
	  oldArrow.isFlying = false
	  snapBackArrow(oldArrow, x, y)
	  newArrow.isFlying = true
	  smartRepaint(boundsOfArrow(newArrow))
	  changeHeld(FlyingArrow(newArrow), x, y)
	}
      }
    }
    addMouseListener(new MouseAdapter() {
      override def mousePressed(e: MouseEvent) {
	if (e.getButton() != MouseEvent.BUTTON1)
	  return
	val (x, y) = (e.getX(), e.getY())
	val newHeld = (mode, e.isAltDown()) match {
	  case (AssignQuery(_, _, rights, _, _, _), false) => findLegalInnerShape(x, y, rights) match {
	    case Some(s) if rights.contains(s) => Mutation(Shadow(s, s.x, s.y))
	    case _ => NoHeld
	  }
	  case (_: Trace, false) => findArrows(x, y) match {
	    case a :: _ if mode.isInstanceOf[StmtTrace] =>
	      a match {  // Move the null arrow so it starts from the center of its owning pointer.
		case Arrow(_, None, srcX, srcY, dstX, dstY, _) => moveArrowAndRepaint(a, a => { a.srcX = srcX + (dstX - srcX) / 2; a.srcY = srcY + (dstY - srcY) / 2; a.dstX = x; a.dstY = y })
		case _ => smartRepaint(boundsOfArrow(a))
	      }
	      a.isFlying = true
	      addMouseWheelListener(arrowSwitcherListener)
	      FlyingArrow(a)
	    case _ => findInnerShape(x, y) match {
	      case Some(s) => Mutation(Shadow(s, s.x, s.y))
	      case None => NoHeld
	    }
	  }
	  case (_, true) => findShape(x, y) match {
	    case Some(s) => Movement(s)
	    case None => NoHeld
	  }
	  case _ => NoHeld
	}
	changeHeld(newHeld, x, y)
	tooltip foreach { t => removeTooltip(t) }
	removeMouseMotionListener(tooltipListener)
      }
      override def mouseReleased(e: MouseEvent) {
	if (e.getButton() != MouseEvent.BUTTON1)
	  return
	val (x, y) = (e.getX(), e.getY())
	def snapBack(shape: Shape) = moveShapeAndRepaint(shape, startX - x, startY - y)
	val origBounds = getBounds(held)  // We need to precompute this, since if something used to point to null and then gets assigned to something, we lose that it could be assigned to anything before.
	if (x != startX || y != startY) {  // Only fire for releases when the mouse has moved; mouseClicked handles the other case.
	  (held, mode) match {
	    case (Mutation(Shadow(held, _, _)), AssignQuery(possibilitiesMap, _, _, rightMap, _, _)) => findShape(x, y, rightMap(held)) match {
	      case Some(receiver) if possibilitiesMap(receiver).contains(held) => possibilitySelected(possibilitiesMap(receiver)(held))
	      case _ =>
	    }
	    case (Mutation(heldCopy @ Shadow(heldOrig, _, _)), mode: Trace) =>
	      findInnerShape(x, y) match {
		case Some(call @ FuncCall(c, _, None, _, _, x, y, w, h, _)) if canReceive(call, heldOrig, mode) =>
		  val target = heldOrig match {
		    case Pointer(_, Arrow(_, target, _, _, _, _, _), _, _, _, _) => target
		    case s => Some(s)
		  }
		  call.argArrows :+= makeCallArrow(x, y, w, c.numInputs, target, call.argArrows.size, pointees)
		  if (call.argArrows.size == c.numInputs)
		    doCall(call, x, y, w, h)
		  call.str = makeCallString(c, call.argArrows.toList.map{ a => shapeToExpr(a.target) }, call.result, printer)
		  hoverOverCall(call)
		  updateWidthAndHeight(call, true, e.getComponent.getGraphics())
		case Some(shape) if canReceive(shape, heldOrig, mode) && mode.isInstanceOf[StmtTrace] => doAssignment(mode.asInstanceOf[StmtTrace], shape, heldOrig)
		case _ =>
	      }
	    case (FlyingArrow(arrow), curMode: StmtTrace) =>
	      findShape(x, y) match {
		case Some(shape: HeapObject) if canReceive(arrowSources(arrow), shape, curMode) => doAssignment(curMode, arrowSources(arrow), shape)
		case _ => snapBackArrow(arrow, x, y)
	      }
	      arrow.isFlying = false
	      removeMouseWheelListener(arrowSwitcherListener)
	    case _ =>
	  }
	  held forShape { held => {
	    if (findShapes(held).size > 1 || isOffscreen(held.x, held.y, held.width, held.height))
	      snapBack(held)
	  }}
	} else
	  held forArrow { _.isFlying = false }
	changeHeld(NoHeld, x, y, Some(origBounds))
	addTooltipListener()
      }
      override def mouseClicked(e: MouseEvent) {
	if (e.getButton() != MouseEvent.BUTTON1)
	  return
	mode match {
	  case SelectQuery(possibilitiesSet, possibilitiesMap, _) => findLegalInnerShape(e.getX(), e.getY(), possibilitiesSet) foreach { selected => possibilitySelected(possibilitiesMap(selected)) }
	  case AssignQuery(possibilitiesMap, lefts, rights, _, _, newArrows) =>
	    val shapeClicked = 
	      if (lefts.size == 1) {
		val shapes = findLegalInnerShape(e.getX(), e.getY(), rights)
		shapes foreach { selected => possibilitySelected(possibilitiesMap.head._2(selected)) }  // Allow users to simply click on the rhs when there is only one lhs.
		shapes.isDefined
	      } else if (rights.size == 1) {
		val shapes = findLegalInnerShape(e.getX(), e.getY(), lefts)
		shapes foreach { selected => possibilitySelected(possibilitiesMap(selected).head._2) }  // Allow users to simply click on the lhs when there is only one rhs.
		shapes.isDefined
	      } else
		false
	    if (!shapeClicked)
	      findArrowBodies(e.getX(), e.getY(), newArrows.keys).headOption match {
		case Some(arrow) =>
		  val (l, r) = newArrows(arrow)
		  possibilitySelected(possibilitiesMap(l)(r))
		case None =>
	      }
	  case mode: Trace => findInnerShape(e.getX(), e.getY(), toplevelShapes ++ modeShapes) foreach { shape => doExpr(mode, shape) }
	  case _ =>
	}
      }
    })
    addMouseMotionListener(new MouseMotionAdapter() {
      override def mouseDragged(e: MouseEvent) {
	if (held.isSomething()) {
	  val (x, y) = (e.getX(), e.getY())
	  held forShape { held => moveShapeAndRepaint(held, x - lastX, y - lastY) }
	  held forArrow { arrow => moveArrowAndRepaint(arrow, arrow => { arrow.dstX += x - lastX; arrow.dstY += y -  lastY }) }
	  lastX = x
	  lastY = y
	}
      }
    })
    (tooltipListener, callHoverListener)
  }

  private def smartRepaint(bounds: Rectangle) {
    bounds.grow(1, 1)
    repaint(bounds)
  }
  private def smartRepaintBounds(bounds: Iterable[Rectangle]) {
    if (bounds.nonEmpty)
      smartRepaint(bounds.reduceLeft{ (acc, cur) => acc.union(cur) })
  }
  // Does an action and repaints with the bounds before and after the action was executed.
  private def mutateAndDoubleRepaint[T <: Shape](shape: T, f: => Unit, getSecondBounds: Boolean = true) {
    val initialBounds = getAllBounds(shape)
    f
    val finalBounds = if (getSecondBounds) getAllBounds(shape) else Nil
    smartRepaintBounds(initialBounds ++ finalBounds)
  }
  private def boundsOfArrow(a: Arrow): Rectangle = {
    def boundsOfArrowToCoords(srcX: Int, srcY: Int, srcW: Int, srcH: Int, dstX: Int, dstY: Int, dstW: Int, dstH: Int): Rectangle = {
      val left = math.min(srcX, dstX)
      val top = math.min(srcY, dstY)
      val right = math.max(srcX + srcW, dstX + dstW)
      val bottom = math.max(srcY + srcH, dstY + dstH)
      new Rectangle(left - ARROWHEAD_SIZE, top - ARROWHEAD_SIZE, right - left + 2 * ARROWHEAD_SIZE, bottom - top + 2 * ARROWHEAD_SIZE)
    }
    boundsOfArrowToCoords(a.srcX, a.srcY, 0, 0, a.dstX, a.dstY, 0, 0)
  }
  private def getAllBounds(shape: Shape): Iterable[Rectangle] = List(boundsOfShape(shape)) ++ getArrowsTo(shape).map(boundsOfArrow) ++ (shape match {
    case src @ Pointer(_, a, _, _, _, _) => List(boundsOfArrow(a))
    case shape @ IntArr(IntArray(id, _), _, _, _, _) => (arrLens(id) :: arrElems(id)).flatMap{ f => getAllBounds(f.child) }  // We check the children since calls might point to them.
    case shape @ Obj(Object(id, _, fs), _, _, _, _) => fields(id).values.flatMap{ f => getAllBounds(f.child) ++ getArrowsFrom(f).map(boundsOfArrow) }  // We check the children since some might be pointers with arrows.
    case call @ FuncCall(_, _, _, _, _, _, _, _, _, true) => call.getAllArrows().map{ arrow => boundsOfArrow(arrow) }
    case c: Child[_, _] => getAllBounds(c.parent)
    case _ => Nil
  }) ++ getArrowsFrom(shape).map(boundsOfArrow)
  private def canReceive(lhs: Shape, rhs: Shape, mode: Trace): Boolean = {
    def isUnfinishedCall(s: Shape) = s match {
      case FuncCall(_, _, None, _, _, _, _, _, _, _) => true
      case _ => false
    }
    mode match {
      case mode: StmtTrace => mode.curBlocks match {
	case ConditionalTrace(None, _) :: _ => isUnfinishedCall(lhs)  // We need an expression (not an assignment) for the condition, so we can only drag to calls.
	case LoopTrace(None, _, _) :: _ => isUnfinishedCall(lhs) || (lhs.isInstanceOf[Var] && typer.typeOfValue(shapeToValue(rhs)) == graphprog.lang.AST.IntType)  // Lop conditions can be integer assignments.
	case _ => shapesCanReceive(lhs, rhs, typer, false)
      }
      case ExprTrace(_) => shapesCanReceive(lhs, rhs, typer, true)
    }
  }
  private def unhoverCall() = hoveringCall foreach { call => mutateAndDoubleRepaint(call, {
    hoveringCall = None
    call.isHovering = false
    call.getAllArrows().foreach{ a => a.isFlying = false }
  }) }
  private def doTraceAction(a: Action, mode: Trace) = {
    def removeAllNewShapes() {
      mode.newShapes.foreach{ _ match {
	case call: FuncCall => 
	  call.getAllArrows().foreach{ a => pointees(a.target) -= a }
	  unhoverCall()
	case _ =>
      }}
      val bounds = mode.newShapes.flatMap{ s => getAllBounds(s) }
      mode.newShapes.clear
      smartRepaintBounds(bounds)
    }
    removeAllNewShapes()
    (mode, a) match {
      case (mode: StmtTrace, a: Action) =>
	val oldMem = mode.initMem
	addActionToTraceBlock(a, mode)
	setGuiCurrentStmts(mode)
	mode.initMem = makeMemory().clone
	gui.addEdit(new ActionDoneEdit(a, oldMem, mode.initMem))
	if (mode.joinFinder.isDefined)
	  findJoin(mode)
      case (_: ExprTrace, e: Expr) => finishExprTraceMode(e)
      case _ => throw new IllegalArgumentException
    }
  }
  private def doExpr(mode: Trace, shape: Shape) {
    val isLegalExpr = mode match {
      case mode: StmtTrace => mode.curBlocks match {
	case ConditionalTrace(None, _) :: _ => typer.canAssign(graphprog.lang.AST.BooleanType, shapeToValue(shape))  // If we are waiting for a condition, only allow boolean exprs.
	case LoopTrace(None, _, _) :: _ => typer.canAssign(graphprog.lang.AST.BooleanType, shapeToValue(shape))  // Loop conditions must be boolean expressions (or integer assignments, but that's a release, not a click).
	case _ => true
      }
      case ExprTrace(_) => typer.canAssign(graphprog.lang.AST.BooleanType, shapeToValue(shape))  // If we are waiting for an expression, only allow boolean exprs.  TODO: Or should I allow any expression?  I currently only use this to fill in conditions, but in the future I could conceivably use it for other things.
    }
    if (isLegalExpr)
      doTraceAction(shapeToExpr(shape), mode)
  }
  private def doAssignment(mode: StmtTrace, lhs: Shape, rhs: Shape) {
    lhs match {
      case v: Var if !variables.contains(v.name) => variables += v.name -> v
      case _ =>
    }
    doTraceAction(assign(lhs, rhs, pointees), mode)
    updateWidthAndHeight(lhs, true, getGraphics())
  }
  private def doCall(call: FuncCall, x: Int, y: Int, w: Int, h: Int) {
    val (result, newMem) = executor.execute(makeMemory(), shapeToExpr(call))
    call.result = Some(result)
    val resultHeapShape = result match { case h: HeapValue => Some(getHeapShape(h)) case _ => None }
    resultHeapShape foreach { result => call.resultArrow = Some(makeCallResultArrow(x, y, w, h, Some(result), pointees)) }
    // TODO/FIXME: Because of this, if I finish a call but click on something else, I get in an inconsistent state.
    updateShapes(getGraphics(), newMem, resultHeapShape.map{ shape => (shape, result) })
    repaint()
  }
  // We do not pass curAction by need, even though we don't always need it, because computing it can have side effects that we need (e.g. assign).
  private def addActionToTraceBlock(curAction: Action, mode: StmtTrace) = mode.curBlocks match {
    case Nil => mode.actions += curAction
    case b :: _ => b match {
      case UnorderedTrace(s) => s += curAction
      case SnapshotTrace =>
      case c @ ConditionalTrace(None, _) if curAction.isInstanceOf[Expr] =>
	gui.conditionSetOrUnset(true)
	c.condition = Some(curAction.asInstanceOf[Expr])
      case ConditionalTrace(None, _) => assert(false)
      case ConditionalTrace(Some(_), body) => body += curAction
      case l @ LoopTrace(None, _, _) =>
	gui.conditionSetOrUnset(true)
	l.condition = Some(curAction)
	executor.evaluate(makeMemory(), curAction) match {  // If the loop condition is false, immediately end the iteration.
	  case BooleanConstant(false) => finishIteration()
	  case _ =>
	}
      case LoopTrace(Some(_), body, _) => body += curAction
    }
  }
  private def removeTopActionFromTraceBlock(mode: StmtTrace) = (mode.curBlocks: @unchecked) match {
    case Nil if mode.actions.nonEmpty => mode.actions.remove(mode.actions.size - 1)
    case b :: _ => (b: @unchecked) match {
      case UnorderedTrace(s) => s.remove(s.size - 1)
      case SnapshotTrace =>
      case c @ ConditionalTrace(Some(e), body) if body.isEmpty =>
	c.condition = None
	gui.conditionSetOrUnset(false)
	e
      case ConditionalTrace(Some(_), body) => body.remove(body.size - 1)
      case l @ LoopTrace(Some(e), body, _) if body.isEmpty =>
	l.condition = None
	gui.conditionSetOrUnset(false)
	e
      case LoopTrace(Some(_), body, _) => body.remove(body.size - 1)
    }
  }
  // Generates the AST Action from the given block.  If extraAction is defined, use it as the last action in this block.
  private def blockToAction(block: TraceBlock, extraAction: Option[Action]): Action = {
    import graphprog.lang.AST.{ UnorderedStmts, Snapshot, Conditional, UnseenExpr, UnseenStmt }
    block match {
      case UnorderedTrace(s) => UnorderedStmts(s.toList ++ extraAction.toList)
      case SnapshotTrace => Snapshot(makeMemory())
      case ConditionalTrace(None, b) => assert(b.isEmpty); assert(extraAction.isDefined && extraAction.get.isInstanceOf[UnseenExpr]); Conditional(extraAction.get.asInstanceOf[Expr], List(UnseenStmt()))
      case ConditionalTrace(Some(s), b) => Conditional(s, b.toList ++ extraAction.toList)
      case LoopTrace(None, b, _) => assert(b.isEmpty); assert(extraAction.isDefined && extraAction.get.isInstanceOf[UnseenExpr]); Iterate(List((extraAction.get, List(UnseenStmt()))))
      case LoopTrace(Some(s), b, _) => Iterate(List((s, b.toList ++ extraAction.toList)))
    }
  }
  // If markCurStmt is true, we put an UnseenExpr as the current/final statement.
  private def getTraceModeActions(mode: StmtTrace, markCurStmt: Boolean): List[Action] = mode.actions.toList ++ mode.curBlocks.foldLeft(if (markCurStmt) Some(graphprog.lang.AST.UnseenExpr(): Action) else None){ (acc, cur) => Some(blockToAction(cur, acc)) }.toList
  private def setGuiCurrentStmts(mode: StmtTrace) = gui.setCurrentStmts(getTraceModeActions(mode, true))

  override def paintComponent(g: Graphics) {
    super.paintComponent(g)
    val g2d = g.asInstanceOf[Graphics2D]
    val drawShapes = toplevelShapes ++ newDiffShapes.toIterator ++ tooltip.toIterator
    drawShapes.foreach{ shape => draw(g2d, shape, getChildren, colorer, arrowColorer) }
    diffArrows.foreach{ arrow => { drawArrow(g2d, arrow, arrowColorer) } }
    modeArrows.foreach{ arrow => { drawArrow(g2d, arrow, arrowColorer) } }
  }

  /**
   * Updates the display to correspond to a new memory.  Removes shapes
   * for things that are gone, creates shapes for new things, and updates
   * the information for existing things whose value has changed.
   */
  def updateDisplayWithMemory(mem: Memory, layoutObjs: Boolean): Unit = updateDisplayWithMemory(getGraphics().asInstanceOf[Graphics2D], mem, layoutObjs)
  private def updateDisplayWithMemory(g: Graphics2D, mem: Memory, layoutObjs: Boolean): Unit = {
    val vars = mem.toIterator.toList
    // Remove orphans.  We do this first to free up space in which to place new shapes.
    variables.keySet.--(vars.map{ _._1 }.toSet).foreach{ name => removeShape(variables(name)) }
    val (curObjects, curArrays) = mem.getObjectsAndArrays
    objects.keySet.--(curObjects.keySet).foreach{ id => removeShape(objects(id)) }
    arrays.keySet.--(curArrays.keySet).foreach{ id => removeShape(arrays(id)) }
    if (nulls.isEmpty) {  // We create null before anything else since things might point to it.
      val (w, h) = (NULL_WIDTH, NULL_HEIGHT)
      val (x, y) = findLocation(getWidth() - OBJECT_SPACING, getHeight() - OBJECT_SPACING, w, h, false)
      nulls += makeNull(x, y, w, h)
    }
    // Create new shapes.
    vars.foreach{ case (name, value) => variables.getOrElseUpdate(name, createVarShape(g, name, value, OBJECT_SPACING, OBJECT_SPACING, true)) }
    // Update existing shapes.
    updateShapes(g, mem, Nil)
    // Layout objects nicely.
    if (layoutObjs)
      useUserObjectLayout(objects.values.toSet, g)
    // Place nulls nicely.
    nulls foreach { n => {
      val (newX, newY) = findLocation(OBJECT_SPACING, OBJECT_SPACING, NULL_WIDTH, NULL_HEIGHT, true)
      moveShape(n, newX - n.x, newY - n.y, getChildren, getArrowsTo, getArrowsFrom)
    } }
  }
  def removeShape(shape: Shape): Unit = shape match {
    case Prim(name, _, _, _, _, _) => variables.remove(name)
    case p @ Pointer(name, a: Arrow, _, _, _, _) =>
      variables.remove(name)
      removeArrow(a)
    case shape @ Obj(Object(id, _, fs), _, _, _, _) =>
      fields(id) foreach { kv => removeShape(kv._2) }
      objects -= id
      fields -= id
      pointees -= Some(shape)
    case shape @ IntArr(IntArray(id, _), _, _, _, _) =>
      arrays -= id
      arrElems -= id
      arrLens -= id
      pointees -= Some(shape)
    case Field(f, _) => removeShape(f)
    case _ => throw new IllegalArgumentException(shape.toString)
  }
  def removeArrow(a: Arrow) {
    if (pointees contains a.target)
      pointees(a.target) -= a
    arrowSources -= a
  }
  // Create new shapes.
  private def createVarShape(g: Graphics, name: String, value: Value, x: Int, y: Int, canMove: Boolean = false): Var = {
    val (w, h) = (widthOfVar(name, value, g), heightOfVar(name, value, g))
    val (newX, newY) = if (canMove) findLocation(x, y, w, h, true) else (x, y)
    value match {
      case p: Primitive => Prim(name, Some(p), newX, newY, w, h)
      case a: IntArray => createPointer(name, Some(createArrShape(g, a, newX + w + OBJECT_SPACING, newY)), newX, newY, w, h)
      case o: Object => createPointer(name, Some(createObjShape(g, o, newX + w + OBJECT_SPACING, newY)), newX, newY, w, h)
      case Null => createPointer(name, None, newX, newY, w, h)
    }
  }
  private def createPointer(name: String, target: Option[HeapObject], x: Int, y: Int, w: Int, h: Int): Pointer = {
    val arrow = makeArrow(x, y, w, h, target)
    val pointer = Pointer(name, arrow, x, y, w, h)
    addArrow(arrow, pointer)
    pointer
  }
  private def addArrow(arrow: Arrow, pointer: Pointer) {
    pointees.getOrElseUpdate(arrow.target, Set()) += arrow
    arrowSources += arrow -> pointer
  }
  private def createArrShape(g: Graphics, array: IntArray, x: Int, y: Int): IntArr = arrays.getOrElseUpdate(array.id, {
    val (w, h) = (widthOfVal(array, g, fieldLayouts), heightOfVal(array, g, fieldLayouts))
    val (newX, newY) = findLocation(x, y, w, h, false)
    val aShape = IntArr(array, newX, newY, w, h)
    val childShapes = array.array.foldLeft((List[IntArrAccess](), 0, newX)){ case ((acc, i, curX), n) => {
      val cur = IntConstant(n)
      val curShape = IntArrAccess(makeMVal(cur, curX, newY, widthOfVal(cur, g, fieldLayouts), heightOfVal(cur, g, fieldLayouts)), i, aShape)
      (curShape :: acc, i + 1, curX + curShape.width)
    }}._1.reverse
    arrElems += array.id -> childShapes
    val len = IntConstant(array.array.length)
    val lenY = if (array.array.isEmpty) newY else newY + heightOfVal(childShapes.head.child.data, g, fieldLayouts)
    val lenShape = ArrLen(IVal(len, newX, lenY, w, heightOfVal(len, g, fieldLayouts)), aShape)
    arrLens += array.id -> lenShape
    aShape
  })
  private def createObjShape(g: Graphics, obj: Object, x: Int, y: Int): Obj = {
    if (objects contains obj.id)  // We can't use getOrElseUpdate like in the array case because we need to separate object and field creation for cyclic objects.
      return objects(obj.id)
    val (w, h) = (widthOfVal(obj, g, fieldLayouts), heightOfVal(obj, g, fieldLayouts))
    val oShape = {
      val (newX, newY) = findLocation(x, y, w, h, false)
      Obj(obj, newX, newY, w, h)
    }
    objects += obj.id -> oShape
    val fieldMap = Map.empty[String, Field]
    fields += obj.id -> fieldMap
    obj.fields.foldLeft(oShape.y){ case (y, (name, value)) => {
      val curY = y + FIELD_PADDING
      val varShape = createVarShape(g, name, value, oShape.x + (oShape.width - Shape.widthOfVar(name, value, g)) / 2, curY)
      val curShape = Field(varShape, oShape)
      varShape match {
	case Pointer(_, a, _, _, _, _) => arrowSources += a -> curShape
	case _ =>
      }
      fieldMap += name -> curShape
      curY + curShape.height
    }}
    useUserFieldLayout(oShape, g)
    oShape
  }
  // Update existing shapes.
  private def updateShapes(g: Graphics, memory: Memory, extraShapes: Iterable[(Shape, Value)]): Unit = {
    val updated = Set.empty[Shape]
    def updateShape(shape: Shape, value: Value, updateWH: Boolean = true): Unit = {
      if (updated contains shape)
	return
      updated += shape
      (shape, value) match {
	case (v: MVal, p: Primitive) => v.data = p
	case (prim: Prim, p: Primitive) => prim.data = Some(p)
	case (p @ Pointer(_, a @ Arrow(_, oldTarget, _, _, _, _, _), _, _, _, _), _) =>
	  val newTarget = value match {  // It might point to something new, which we have to create.
	    case a @ IntArray(id, _) => Some(arrays.getOrElse(id, createArrShape(g, a, p.x + p.width + OBJECT_SPACING, p.y)))
	    case o @ Object(id, _, _) => Some(objects.getOrElse(id, createObjShape(g, o, p.x + p.width + OBJECT_SPACING, p.y)))
	    case Null => None
	  }
	  if (oldTarget != newTarget) {
	    if (pointees contains oldTarget)
	      pointees(oldTarget) -= a
	    pointees.getOrElseUpdate(newTarget, Set.empty) += a
	    updateArrow(a, p.x, p.y, p.width, p.height, newTarget)
	  }
	  newTarget.foreach{ newTarget => updateShape(newTarget, value) }
	case (IntArr(IntArray(id1, array1), _, _, _, _), IntArray(id2, array2)) =>
	  assert(id1 == id2)
	  for (i <- 0 until array2.length)  // As below in the object case, we need to freshen the shape's data, since executing a call in trace mode makes a copy of the array.
	    array1(i) = array2(i)
	  arrElems(id1).zip(array1).foreach{ case (shape, value) => updateShape(shape, IntConstant(value)) }
	case (Obj(Object(id1, _, f1), _, _, _, _), Object(id2, _, f2)) =>
	  assert(id1 == id2)
	  f2.foreach{ kv => f1 += kv._1 -> (kv._2 match { case Object(id, _, _) => assert(objects contains id, id + ", " + iterableToString(objects, "; ", (kv: (Int, Obj)) => kv._1 + " -> " + printer.stringOfValue(kv._2.data))); objects(id).data case IntArray(id, _) => arrays(id).data case v => v }) }  // We copy the object's fields into the shape so the shape is fresh.  We need this since executing calls in trace mode produces a cloned object distinct and newer than the shape's object.  But note that we cannot copy over f2's values directly since they might refer to cloned objects and arrays.  In this case, we make sure to use our version.
	  f2.foreach{ kv => updateShape(fields(id1)(kv._1), kv._2) }  // This must be f2 and not f1, since f1's rhs are ours, which might not have their changes.
	case (c: Child[_, _], _) => updateShape(c.child, value, false)
	case (_: NullShape, Null) =>
	case _ => throw new RuntimeException
      }
      if (updateWH)
	updateWidthAndHeight(shape, false, g)
    }
    (memory.toIterator.toList.map{ nv => (variables(nv._1), nv._2) } ++ extraShapes).foreach{ sv => updateShape(sv._1, sv._2) }
  }

  /**
   * (Re-)Lays out an object's fields according to the specification
   * given by the user.  The specification is given as a matrix of fields.
   * E.g.
   * [["parent"],
   *  ["value"],
   *  ["color"],
   *  ["left", "right"]]
   */
  private def useUserFieldLayout(obj: Obj, g: Graphics) {
    fieldLayouts.get(obj.data.typ).foreach{ layout => {
      val curFields = fields(obj.data.id)
      assert(curFields.size == layout.flatten.size && layout.flatten.forall{ f => curFields.contains(f) })  // Ensure that the layout is well-formed.
      // Change the width and height of the object.
      if (curFields.nonEmpty) {
	obj.width = widthOfVal(obj.data, g, fieldLayouts)
	obj.height = heightOfVal(obj.data, g, fieldLayouts)
      }
      //Layout all rows.
      layout.foldLeft(obj.y + FIELD_PADDING){ (rowY, row) => {
	val rowFields = row.map{ f => curFields(f) }
	// Center this row horizontally within the object and center each field vertically within its row.
	val rowWidth = row.map{ f => widthOfVar(f, obj.data.fields(f), g) + FIELD_PADDING }.sum + FIELD_PADDING
	val rowStartX = obj.x + (obj.width - rowWidth) / 2 + FIELD_PADDING
	val rowHeight = row.map{ f => heightOfVar(f, obj.data.fields(f), g) }.max
	// Layout individual row.
	rowFields.foldLeft(rowStartX) { (rowX, field) => {
	  field.x = rowX
	  field.y = rowY + (rowHeight - field.height) / 2
	  field.x + field.width + FIELD_PADDING
	}}
	rowFields.map{ f => f.y + f.height }.max + FIELD_PADDING
      }}
    }}
  }
  /**
   * Lays out an object.  See the comment about the ObjectLayout type in Controller.scala.
   * We re-layout objects that were illegally placed.
   */
  private def useUserObjectLayout(allObjs: ISet[Obj], g: Graphics) {
    // Adjusts shapes by moving them down-right until they are not overlapping and then moving them up-left as far as possible.
    def shiftObjects(objs: Iterable[Obj], existingShapes: Iterable[Shape]) {
      def moveObjs(dx: Int, dy: Int) = objs.foreach{ o => moveShape(o, dx, dy, getChildren, getArrowsTo, getArrowsFrom) }
      // Move the objects up or left while they are legally placed.
      @tailrec def moveObjsUpLeft(dx: Int, dy: Int) {
	val newBounds = objs.map{ o => val r = boundsOfShape(o); r.translate(dx, dy); r }
	if (newBounds.forall{ b => b.x >= OBJECT_SPACING && b.y >= OBJECT_SPACING && findShapesNear(b.x, b.y, b.width, b.height, existingShapes).isEmpty }) {
	  moveObjs(dx, dy)
	  moveObjsUpLeft(dx, dy)
	} else if (newBounds.forall{ b => findShapesNear(b.x, b.y, b.width, b.height, existingShapes).isEmpty }) {
	  val (newdx, newdy) = (math.max(dx, OBJECT_SPACING - objs.map{ _.x }.min), math.max(dy, OBJECT_SPACING - objs.map{ _.y }.min))
	  moveObjs(newdx, newdy)
	}
      }
      // Move the objects down and right until they are all legally placed.
      @tailrec def moveObjsDownRight() {
	val ds = objs.flatMap{ o => findShapesNear(o.x, o.y, o.width, o.height, existingShapes).map{ s => (s.x + s.width + OBJECT_SPACING - o.x, s.y + s.height + OBJECT_SPACING - o.y) } }
	if (ds.nonEmpty) {
	  val (dx, dy) = ds.reduceLeft{ (acc, cur) => (math.min(acc._1, cur._1), math.min(acc._2, cur._2)) }
	  val (dxShapes, dyShapes) = (objs.flatMap{ o => findShapesNear(o.x + dx, o.y, o.width, o.height, existingShapes) }, objs.flatMap{ o => findShapesNear(o.x, o.y + dy, o.width, o.height, existingShapes) })
	  // Move whichever way will bring us to a legal place or the smaller direction.
	  if ((dxShapes.isEmpty && dyShapes.nonEmpty) || (dxShapes.nonEmpty && dyShapes.nonEmpty && dx <= dy))
	    moveObjs(dx, 0)
	  else
	    moveObjs(0, dy)
	  moveObjsDownRight()
	}
      }
      if (objs.nonEmpty) {  // This can be called when objs is empty (if we can't lay anything out), and in that case moveObjsUpLeft would infinite loop, so guard against it here.
	moveObjsDownRight()
	moveObjsUpLeft(-OBJECT_SPACING, 0)
	moveObjsUpLeft(0, -OBJECT_SPACING)
      }
    }
    val layableObjs = allObjs.filter{ o => objectLayouts contains o.data.typ }
    val (widthFn, heightFn) = ((v: Value) => widthOfVal(v, g, fieldLayouts), (v: Value) => heightOfVal(v, g, fieldLayouts))
    // TODO-lowish: I can use objectComparators, if applicable, to sort rather than laying each thing out.
    val layoutInfos = layableObjs.map{ o => (o, try { objectLayouts(o.data.typ)(o.data, widthFn, heightFn, OBJECT_SPACING) } catch { case _: Throwable => Nil }) }.toMap  // We might be in the middle of a trace with inconsistent objects, so the layout call could fail.
    @tailrec def doLayouts(shapesToLayout: ISet[Obj], secondTrys: ISet[Int]) {
      if (shapesToLayout.isEmpty)  // We've placed all the shapes, so return
	return
      val availableShapes = toplevelShapes.toSet -- shapesToLayout
      val curObjects = {
	// Pick the shape to layout next by (a) preferring things we have placed illegaly before (e.g. subtrees) and (b) preferring things that let us place more shapes (e.g. the root of a tree).
	val (oShape, objectLayoutInfo) = shapesToLayout.map{ o => (o, layoutInfos(o)) }.reduceLeft{ (acc, cur) => ((acc, cur), (secondTrys.contains(acc._1.data.id), secondTrys.contains(cur._1.data.id))) match {
	  case (_, (true, false)) => acc
	  case (_, (false, true)) => cur
	  case _ if cur._2.size > acc._2.size => cur
	  case _ if acc._2.size > cur._2.size => acc
	  case _ if cur._1.data.id < acc._1.data.id => cur
	  case _ => acc
	} }
	val obj = oShape.data
	val objLayoutInfo = objectLayoutInfo.map{ case (o, l) => (objects(o.id), l) }
	// If we're placing the shape for the first time, start at the top-left and move down.  If we've placed before, try to place near where it should be.
	val (minX, minY) = if (secondTrys.contains(oShape.data.id)) findLocation(oShape.x, oShape.y, oShape.width, oShape.height, false, availableShapes) else (OBJECT_SPACING, OBJECT_SPACING)
	val positions = objLayoutInfo.map{ case (o, (x, y)) => (o, (minX + x, minY + y)) }
	// Move the object (if this is an illegal place, we are just storing the location and will move it later)
	positions.foreach{ case (o, (x, y)) => moveShape(o, x - o.x, y - o.y, getChildren, getArrowsTo, getArrowsFrom) }
	positions.map{ _._1 }.toSet	
      }
      val existingShapes = availableShapes -- curObjects
      shiftObjects(curObjects, existingShapes)  // Shift the shapes we just placed to be in the right place.
      val (placed, illegal) = curObjects.foldLeft((ISet.empty[Obj], ISet.empty[Obj])){ case ((placed, illegal), o) => {
	if (isOffscreen(o.x, o.y, o.width, o.height) || findShapes(boundsOfShape(o), existingShapes ++ placed).nonEmpty)
	  (placed, illegal + o)
	else
	  (placed + o, illegal)
      }}
      val nextShapesToLayout = (shapesToLayout ++ illegal) -- placed
      if (nextShapesToLayout != shapesToLayout)
	doLayouts(nextShapesToLayout, secondTrys ++ illegal.map{ _.data.id })
      else  // We're stuck, so place the remaining shapes somewhere legal.  Otherwise we'll infinite loop.
	shapesToLayout.foldLeft(List[Shape]()){ (acc, cur) => {
	  val (x, y) = findLocation(cur.x, cur.y, cur.width, cur.height, false, availableShapes ++ acc)
	  moveShape(cur, x - cur.x, y - cur.y, getChildren, getArrowsTo, getArrowsFrom)
	  cur :: acc
	}}
    }
    doLayouts(layableObjs, ISet.empty)
  }

  private def updateWidthAndHeight(shape: Shape, updateParent: Boolean, g: Graphics) {
    def updateWidthAndHeightHelper(shape: Shape, changeXY: Boolean) {
      def updateWH(w: Int, h: Int) {
	if (changeXY) {
	  shape.x = shape.x - (w - shape.width) / 2
	  shape.y = shape.y - (h - shape.height) / 2
	}
	shape.width = w
	shape.height = h
      }
      (shape: @unchecked) match {
	case v: Val => updateWH(widthOfVal(v.data, g, fieldLayouts), heightOfVal(v.data, g, fieldLayouts))
	case Prim(name, Some(data), _, _, _, _) => updateWH(widthOfVar(name, data, g), heightOfVar(name, data, g))
	case Pointer(name, a @ Arrow(_, target, _, _, _, _, _), _, _, _, _) => 
	  val data = shapeToValue(target)
	  updateWH(widthOfVar(name, data, g), heightOfVar(name, data, g))
	  updateArrow(a, shape.x, shape.y, shape.width, shape.height, target)
	case shape @ IntArr(a @ IntArray(id, _), _, _, _, _) =>
	  updateWH(widthOfVal(a, g, fieldLayouts), heightOfVal(a, g, fieldLayouts))
	  val len = arrLens(id)
	  len.x = shape.x
	  len.width = shape.width
	  val elems = arrElems(id)
	  elems.foldLeft(shape.x){ (curX, e) => {
	    e.x = curX
	    e.x + e.width
	  }}
	  getArrowsTo(shape).foreach{ a => updateArrow(a, a.srcX, a.srcY, 0, 0, a.target) }
	case shape @ Obj(o, _, _, w, h) =>
	  val (newWidth, newHeight) = (widthOfVal(o, g, fieldLayouts), heightOfVal(o, g, fieldLayouts))
	  if (newWidth != w || newHeight != h) {
	    updateWH(newWidth, newHeight)
	    useUserFieldLayout(shape, g)  // If the object's size has changed, we need to re-lay out its fields.
	    fields(o.id).values.foreach{ f => updateWidthAndHeightHelper(f.child, true) }  // if the object's size has changed, we need to update its fields.
	    getArrowsTo(shape).foreach{ a => updateArrow(a, a.srcX, a.srcY, 0, 0, a.target) }
	  }
	case c: Child[_, _] =>
	  updateWidthAndHeightHelper(c.child, c.isInstanceOf[Field])
	  if (updateParent)
	    updateWidthAndHeightHelper(c.parent, false)
	case FuncCall(p, argArrows, _, resultArrow, str, _, _, _, _, _) =>
	  updateWH(widthOfString(str, g), heightOfString(str, g))
	  argArrows.zipWithIndex.foreach{ case (arrow, i) => {
	    arrow.srcX = getCallArrowX(shape.x, shape.width, p.numInputs, i)
	    arrow.srcY = shape.y
	  }}
	  resultArrow.foreach { resultArrow => {
	    resultArrow.srcX = shape.x + shape.width / 2
	    resultArrow.srcY = shape.y + shape.height
	  }}
	case _: NullShape =>
      }
    }
    mutateAndDoubleRepaint(shape, updateWidthAndHeightHelper(shape, false))
  }
  
  /**
   * Try find a place to layout a shape with the given width and height
   * starting at the given default location.
   * For now, this algorithm simply moves it left or down until it finds an open spot.
   */
  private def findLocation(origX: Int, origY: Int, w: Int, h: Int, isVariable: Boolean, shapes: Iterable[Shape] = toplevelShapes.toList): (Int, Int) = {
    import math.{ max, min }
    def myIsOffscreen(x: Int, y: Int, w: Int, h: Int) = isOffscreen(x, y, w, h) && w < getWidth() && h < getHeight()  // If the object has no chance of fitting onscreen, just place it.
    def findLocHelper(origX: Int, origY: Int): Option[(Int, Int)] = {
      @tailrec def findLocRec(x: Int, y: Int): (Int, Int) = findShapesNear(x, y, w, h, shapes) match {
	case Nil => (x, y)
	case l => 
	  val newX = l.foldLeft(Int.MaxValue){ (acc, cur) => min(acc, cur.x + cur.width) } + OBJECT_SPACING
	  val newY = l.foldLeft(Int.MaxValue){ (acc, cur) => min(acc, cur.y + cur.height) } + OBJECT_SPACING
	  if (isVariable || newY - origY <= newX - origX) findLocRec(x, newY) else findLocRec(newX, y)
      }
      if (myIsOffscreen(origX, origY, w, h))
	None
      else {
	val (newX, newY) = findLocRec(origX, if (isVariable) origY else max(OBJECT_SPACING, origY - h / 2))  // Center the new shape vertically with the given y if it's not a variable.
	if (myIsOffscreen(newX, newY, w, h)) None else Some((newX, newY))
      }
    }
    def randomPlacer(): Option[(Int, Int)] = {
      import scala.util.Random._
      val (screenWidth, screenHeight) = (getWidth(), getHeight())
      def doRandomPlacement(n: Int): Option[(Int, Int)] = {
	if (n < 0)
	  None
	else {
	  val (x, y) = (nextInt(screenWidth), nextInt(screenHeight))
	  if (myIsOffscreen(x, y, w, h) || findShapesNear(x, y, w, h, shapes).nonEmpty) doRandomPlacement(n - 1) else Some((x, y))
	}
      }
      doRandomPlacement(100)
    }
    (findLocHelper(origX, origY) orElse
     findLocHelper(origX + OBJECT_SPACING, OBJECT_SPACING) orElse
     findLocHelper(OBJECT_SPACING, origY + OBJECT_SPACING) orElse
     findLocHelper(getWidth() / 2, OBJECT_SPACING) orElse
     findLocHelper(OBJECT_SPACING, getHeight() / 2) orElse
     randomPlacer() orElse
     (throw new java.lang.RuntimeException("I cannot place a shape."))).get
  }
  private def findShapesNear(x: Int, y: Int, w: Int, h: Int, shapes: Iterable[Shape] = toplevelShapes.toList): List[Shape] = findShapes(new Rectangle(x - OBJECT_SPACING / 2, y - OBJECT_SPACING / 2, w + OBJECT_SPACING, h + OBJECT_SPACING), shapes)
  private def findShapes(s: Shape): List[Shape] = findShapes(boundsOfShape(s))
  private def findShapes(r: Rectangle, shapes: Iterable[Shape] = toplevelShapes.toList): List[Shape] = shapes.filter{ s => boundsOfShape(s).intersects(r) }.toList
  private def findShape[T <: Shape](x: Int, y: Int, shapes: TraversableOnce[T] = toplevelShapes): Option[T] = shapes.find{ s => boundsOfShape(s).contains(x, y) }
  private def findInnerShape(x: Int, y: Int, shapes: TraversableOnce[Shape] = toplevelShapes): Option[Shape] = findShape(x, y, shapes) match {
    case None => None
    case Some(s) => findShape(x, y, getChildren(s) ++ List(s))
  }
  private def findArrows(x: Int, y: Int): List[Arrow] = {
    import math._
    def arrowIsClicked(a: Arrow): Boolean = {
      def dist(x1: Int, y1: Int, x2: Int, y2: Int) = sqrt(pow(x1 - x2, 2) + pow(y1 - y2, 2))
      def arrowPointIsClicked(arrowX: Int, arrowY: Int): Boolean = dist(arrowX, arrowY, x, y) <= 5
      a match {
	case Arrow(_, None, srcX, srcY, dstX, dstY, _) => arrowPointIsClicked(srcX, srcY) || arrowPointIsClicked(dstX, dstY)
	case Arrow(_, _, _, _, dstX, dstY, _) => arrowPointIsClicked(dstX, dstY)
      }
    }
    // This function tries to help us pick the best arrow based on the angle from the mouse, but it's not perfect.  So rather than the commented code below, which uses only this, we use all of them and only use this to sort the arrows.
    def arrowAngle(a: Arrow): Double = {
      def angle(oX: Int, oY: Int, x1: Int, y1: Int, x2: Int, y2: Int): Double = {
	val a1 = atan2(oY - y1, oX - x1) - atan2(oY - y2, oX - x2)
	val a2 = atan2(y1 - oY, x1 - oX) - atan2(y2 - oY, x2 - oX)
	def evener(a: Double) = abs(if (a < -Pi) a + Pi else if (a > Pi) a - Pi else a)
	min(evener(a1), evener(a2))
      }
      angle(a.srcX, a.srcY, a.dstX, a.dstY, x, y)
    }
    //arrows.collect{ case a if arrowIsClicked(a) => (a, arrowAngle(a)) }.foldLeft(List[(Arrow, Double)]()){ (acc, cur) => if (acc.isEmpty || cur._2 < acc.head._2) List(cur) else if (acc.nonEmpty && cur._2 == acc.head._2) acc :+ cur else acc }.map{ _._1 }
    arrows.filter(arrowIsClicked).toList.sortBy{ a => arrowAngle(a) }
  }
  private def findArrowBodies(x: Int, y: Int, arrows: Iterable[Arrow]): List[Arrow] = {
    import math._
    def distanceFromArrow(a: Arrow): Int = {
      val minX = min(a.srcX, a.dstX)
      val maxX = max(a.srcX, a.dstX)
      val minY = min(a.srcY, a.dstY)
      val maxY = max(a.srcY, a.dstY)
      if (x < minX - 5 || x > maxX + 5 || y < minY - 5 || y > maxY + 5)
	return Int.MinValue
      val yOffset = ((x - minX).toDouble / (maxX - minX)) * (maxY - minY)
      val targetY = if ((a.srcX <= a.dstX && a.srcY <= a.dstY) || (a.srcX >= a.dstX && a.srcY >= a.dstY)) minY + yOffset else maxY - yOffset
	
      return abs(y.toDouble - targetY).toInt
    }
    arrows.map{ a: Arrow => (a, distanceFromArrow(a)) }.filter{ case (_, d) => d >= 0 && d <= 5 }.toList.sortBy{ _._2 }.map{ _._1 }
  }
  private def boundsOfShape(s: Shape): Rectangle = new Rectangle(s.x, s.y, s.width, s.height)

  private def isOffscreen(x: Int, y: Int, w: Int, h: Int): Boolean = x < 0 || x + w > getWidth() || y < 0 || y + h > getHeight()

  // TODO: Sort newly-created shapes so that they always appear in the same order (e.g. so we can't have two questions with the same answers with the orders reversed, e.g. true above false then false above true).
  def setPossibilities(possibilities: List[Action]): Unit = setPossibilities(possibilities, makeMemory(), getGraphics().asInstanceOf[Graphics2D])
  private def setPossibilities(possibilities: List[Action], mem: Memory, g: Graphics2D): Unit = {
    import graphprog.lang.AST.{ Expr, IntArrayAccess, FieldAccess, ArrayLength, Call, LVal }
    val newModeVars = Map.empty[String, Var]
    val newPrimitives = Map.empty[Primitive, Shape]
    val newCalls = Map.empty[(String, List[Expr]), Shape]
    def newShapes = newModeVars.values ++ newPrimitives.values ++ newCalls.values
    def getShape(e: Expr, isLHS: Boolean): Shape = {
      def handleVar(s: Shape): Shape = s match {
	case Pointer(_, Arrow(_, Some(target), _, _, _, _, _), _, _, _, _) if !isLHS => target
	case Field(Pointer(_, Arrow(_, Some(target), _, _, _, _, _), _, _, _, _), _) if !isLHS => target
	case _ => s
      }
      // TODO-low: Implement In/To/Until.  Not that I care.
      e match {
	case cur: Primitive =>
	  val (w, h) = (widthOfVal(cur, g, fieldLayouts), heightOfVal(cur, g, fieldLayouts))
	  val (x, y) = findLocation(OBJECT_SPACING, OBJECT_SPACING, w, h, true, toplevelShapes.toList ++ newShapes)
	  newPrimitives.getOrElseUpdate(cur, IVal(cur, x, y, w, h))
	case Object(id, _, _) =>
	  assert(objects contains id)
	  objects(id)
	case IntArray(id, _) =>
	  assert(arrays contains id)
	  arrays(id)
	case ASTVar(name) =>
	  if (isLHS)
	    variables.getOrElse(name, newModeVars.getOrElseUpdate(name, {  
	      val (w, h) = (Shape.DEFAULT_WIDTH, heightOfVar(name, IntConstant(0), g))
	      val (x, y) = findLocation(OBJECT_SPACING, OBJECT_SPACING, w, h, true, toplevelShapes.toList ++ newShapes)
	      Prim(name, None, x, y, w, h)
	    }))
	  else {
	    assert(variables contains name, variables.toString + " does not contain " + name)
	    handleVar(variables(name))
	  }
	case IntArrayAccess(IntArray(id, _), IntConstant(index)) =>
	  assert(arrays contains id)
	  arrElems(id)(index)
	case FieldAccess(Object(id, _, _), field) =>
	  assert(objects contains id)
	  handleVar(fields(id)(field))
	case ArrayLength(IntArray(id, _)) =>
	  assert(arrays contains id)
	  arrLens(id)
	case Call(name, args) =>
	  val evaledArgs = args map { e => partiallyEvaluateExpr(e) }
	  newCalls.getOrElseUpdate((name, evaledArgs), {
	    val prog = Prog(helperFunctions(name))
	    val result = executor.evaluate(mem, e)
	    val str = makeCallString(prog, args, Some(result), printer)
	    val argShapes = evaledArgs.map{ e => getShape(e, isLHS) }
	    val (w, h) = (widthOfString(str, g), heightOfString(str, g))
	    val (x, y) = findLocation(OBJECT_SPACING, OBJECT_SPACING, w, h, true, toplevelShapes.toList ++ newShapes ++ argShapes)
	    val (argArrows, resultArrow) = makeCallArrows(argShapes, result, x, y, w, h)
	    FuncCall(prog, argArrows, Some(result), resultArrow, str, x, y, w, h, false)
	  })
	case Null => nulls.head
	// Partial evaluation
	case e => getShape(partiallyEvaluateExpr(e), isLHS)
      }
    }
    /*def partiallyEvaluateAction(a: Action): Action = a match {
      case Assign(l, r) => Assign(partiallyEvaluateExpr(l).asInstanceOf[LVal], partiallyEvaluateExpr(r))
      case e: Expr => partiallyEvaluateExpr(e)
    }*/
    def partiallyEvaluateExpr(e: Expr): Expr = e match {
      case IntArrayAccess(array, index) => IntArrayAccess(executor.evaluate(mem, array), executor.evaluate(mem, index))
      case FieldAccess(obj, field) =>
	val o = executor.evaluate(mem, obj)
	assert(o.isInstanceOf[Object])
	FieldAccess(o, field)
      case ArrayLength(e) => ArrayLength(executor.evaluate(mem, e))
      case v: ASTVar => v
      case Call(name, args) => Call(name, args.map{ e => partiallyEvaluateExpr(e) })
      case e => executor.evaluate(mem, e)
    }
    possibilities.head match {
      case _: Expr =>
	val possibilitiesMap = possibilities.foldLeft(IMap.empty[Shape, List[Action]]){ case (acc, cur: Expr) => {
	  val curShape = getShape(cur, false)
	  acc + (curShape -> (cur :: acc.getOrElse(curShape, Nil)))
	} case _ => throw new RuntimeException }
	val possibilitiesSet = possibilitiesMap.keySet.toSet
	mode = SelectQuery(possibilitiesSet, possibilitiesMap, newShapes.toSet)
      case _: Assign =>
	def shapeToPointer(s: Shape): Option[Pointer] = s match {
	  case p: Pointer => Some(p)
	  case c: Child[_, _] => shapeToPointer(c.child)
	  case _ => None
	}
	def shapeToPointee(s: Shape): Shape = s match {
	  case Pointer(_, Arrow(_, None, _, _, _, _, _), _, _, _, _) => nulls.head
	  case Pointer(_, Arrow(_, Some(target), _, _, _, _, _), _, _, _, _) => shapeToPointee(target)
	  case c: Child[_, _] => shapeToPointee(c.child)
	  case _ => s
	}
	val shapesToArrow = Map.empty[(Shape, Shape), Arrow]
	val (possibilitiesMap, rightMap, arrows) = possibilities.foldLeft((IMap.empty[Shape, IMap[Shape, List[Action]]], IMap.empty[Shape, ISet[Shape]], IMap.empty[Arrow, (Shape, Shape)])){ case ((accl, accr, arrows), cur @ Assign(lhs, rhs)) => {
	  val lhsShape = getShape(lhs, true)
	  val rhsShape = getShape(rhs, false)
	  val newArrows = shapeToPointer(lhsShape).map{ p => {
	    val p = shapeToPointer(lhsShape).get
	    val target = shapeToPointee(rhsShape)
	    shapesToArrow.get((p, target)) match {
	      case Some(a: Arrow) => arrows
	      case None => 
		val arrow = makeArrow(p.x, p.y, p.width, p.height, Some(target))
		addArrow(arrow, p)
		shapesToArrow += ((p, target) -> arrow)
		arrows + (arrow -> (lhsShape, rhsShape))
	    }
	  } }.getOrElse(arrows)
	  val leftInnerMap = accl.getOrElse(lhsShape, IMap.empty[Shape, List[Action]])
	  (accl + (lhsShape -> (leftInnerMap + (rhsShape -> (cur :: leftInnerMap.getOrElse(rhsShape, Nil))))), accr + (rhsShape -> (accr.getOrElse(rhsShape, ISet.empty[Shape]) + lhsShape)), newArrows)
	} case _ => throw new RuntimeException }
	val lefts = possibilitiesMap.keySet.toSet
	val rights = possibilitiesMap.values.foldLeft(ISet.empty[Shape]){ (acc, cur) => acc ++ cur.keySet }
	mode = AssignQuery(possibilitiesMap, lefts, rights, rightMap, newShapes.toSet, arrows)
      case e => throw new IllegalArgumentException(e.toString)
    }
    addMouseMotionListener(tooltipListener)
    addMouseMotionListener(callHoverListener)
    gui.setStatusBarText("Please choose " + iterableToString(possibilities, " or ", (a: Action) => printer.stringOfAction(a)) + ".")
  }
  def leaveQueryMode() {
    mode = Observer
    removeMouseMotionListener(tooltipListener)
    removeMouseMotionListener(callHoverListener)
    gui.emptyStatusBarText()
  }

  private def makeCallArrows(argShapes: List[Shape], result: Value, x: Int, y: Int, w: Int, h: Int): (List[Arrow], Option[Arrow]) = {
    val argArrows = argShapes.zipWithIndex.map{ case (s, i) => makeCallArrow(x, y, w, argShapes.size, Some(s), i, pointees) }
    val resultArrow = result match {
      case result: HeapValue => Some(makeCallResultArrow(x, y, w, h, Some(getHeapShape(result)), pointees))
      case _ => None
    }
    (argArrows, resultArrow)
  }

  private val colorer: PartialFunction[Shape, Color] = shape => { (held, mode) match {
    case (Mutation(heldCopy @ Shadow(heldOrig, _, _)), _) if shape.eq(heldOrig) || shape.eq(heldCopy) => SHADOW_COLOR
    case (_, SelectQuery(possibilities, _, _)) if possibilities.contains(shape) => POSSIBILITY_COLOR
    case (Mutation(Shadow(held, _, _)), AssignQuery(possibilitiesMap, lefts, _, _, _, _)) if lefts.contains(shape) && possibilitiesMap(shape).contains(held) => RECEIVER_COLOR  // If we're holding a rhs, only color red the things that can receive it.
    case (_: NonMutation, AssignQuery(possibilitiesMap, lefts, _, _, _, _)) if lefts.contains(shape) => RECEIVER_COLOR
    case (_: NonMutation, AssignQuery(_, _, rights, _, _, _)) if rights.contains(shape) => POSSIBILITY_COLOR
    case (Mutation(Shadow(held, _, _)), mode: Trace) if canReceive(shape, held, mode) => RECEIVER_COLOR
    case (FlyingArrow(arrow), mode: Trace) if shape.isInstanceOf[HeapObject] && canReceive(arrowSources(arrow), shape, mode) => RECEIVER_COLOR
    case (_, _) if diffShapes.contains(shape) || newDiffShapes.contains(shape) => NEW_DIFF_COLOR
  }}
  private val arrowColorer: PartialFunction[Arrow, Color] = arrow => (arrow, mode) match {
    case (Arrow(_, _, _, _, _, _, true), _) => SHADOW_COLOR
    case (a: Arrow, _) if diffArrows.contains(a) => NEW_DIFF_COLOR
    case (a: Arrow, _) if oldDiffArrows.contains(a) => OLD_DIFF_COLOR
    case (a: Arrow, AssignQuery(_, _, _, _, _, arrows)) if arrows.contains(a) => POSSIBILITY_COLOR
  }

  def startStmtTraceMode(memory: Memory) {
    mode = StmtTrace(ListBuffer.empty, Nil, Map.empty, Set.empty, memory.clone, None)
    gui.setStatusBarText("Please give a trace.")
    addMouseMotionListener(callHoverListener)
  }
  def startExprTraceMode() {
    mode = ExprTrace(Set.empty)
    gui.setStatusBarText("Please give an expression.")
    addMouseMotionListener(callHoverListener)
  }

  def finishStmtTraceMode(): (List[Action], TMap[Iterate, Loop], Memory) = {
    val curMode = mode.asInstanceOf[StmtTrace]
    val actions = getTraceModeActions(curMode, false)
    finishTraceMode()
    (actions, curMode.loops, makeMemory())
  }
  private def finishExprTraceMode(e: Expr) {
    gui.setTraceExpr(e, makeMemory())
    finishTraceMode()
  }
  def finishTraceMode() {
    removeMouseMotionListener(callHoverListener)
    mode = Observer
    gui.emptyStatusBarText()
  }

  def makeMemory(): Memory = new Memory(variables.valuesIterator.map{ v => getBinding(v) })

  def addPrimVar(name: String, extraShapes: Iterable[Shape] = Nil) = addVar(name, g => {
    val (w, h) = (widthOfVar(name, IntConstant(0), g), heightOfVar(name, IntConstant(0), g))
    val (x, y) = findLocation(OBJECT_SPACING, OBJECT_SPACING, w, h, true, toplevelShapes.toList ++ extraShapes)
    Prim(name, None, x, y, w, h)
  } )
  def addPointer(name: String, extraShapes: Iterable[Shape] = Nil) = addVar(name, { g => {
    val (w, h) = (widthOfVar(name, Null, g), heightOfVar(name, Null, g))
    val (x, y) = findLocation(OBJECT_SPACING, OBJECT_SPACING, w, h, true, toplevelShapes.toList ++ extraShapes)
    createPointer(name, None, x, y, w, h)
  } })
  def addPrim(p: Primitive) = addShape(makePrim(p, Nil))
  private def makePrim(p: Primitive, extraShapes: Iterable[Shape])(g: Graphics): Shape = {
    val (w, h) = (widthOfVal(p, g, fieldLayouts), heightOfVal(p, g, fieldLayouts))
    val (x, y) = findLocation(OBJECT_SPACING, OBJECT_SPACING, w, h, true, toplevelShapes.toList ++ extraShapes)
    IVal(p, x, y, w, h)
  }
  def addCall(c: Callable) = addShape{ g => {
    val result = c match { case Prog(p) if (p.inputs.isEmpty) => Some(executor.evaluate(makeMemory(), Call(p.name, Nil))) case op: ConcreteOp => Some(executor.evaluate(makeMemory(), op.e)) case _ => None }
    val str = makeCallString(c, Nil, result, printer)
    val (w, h) = (widthOfString(str, g), heightOfString(str, g))
    val (x, y) = findLocation(OBJECT_SPACING, OBJECT_SPACING, w, h, true)
    FuncCall(c, Nil, result, None, str, x, y, w, h, false)  // It can't have a result arrow since it can only have a result if it hsa zero arguments, in which case no objects are accessible.
  } }
  private def addVar(name: String, shapeCreator: Graphics => Shape): Option[Shape] = {
    if (variables.contains(name) || mode.asInstanceOf[Trace].newShapes.exists{ _ match { case v: Var if v.name == name => true case _ => false } }) {
      SynthesisGUI.showError(gui, "Variable " + name + " already exists.")
      None
    } else
      Some(addShape(shapeCreator))
  }
  private def addShape[T <: Shape](shapeCreator: Graphics => T): T = {
    val newShape = shapeCreator(getGraphics())
    mode.asInstanceOf[Trace].newShapes += newShape
    smartRepaint(boundsOfShape(newShape))
    newShape
  }

  // TODO/FIXME: Allow giving possibilities.
  // TODO/FIXME: Here (and in AST and friends) add ++ so I can increment vars more easily and without using a constant 1 that could be a standin.
  // TODO: I currently do exprs by default (see Control.scala).  Should I really do that?
  def addAction(a: Action, shouldDoExpr: Boolean): Boolean = {
    import graphprog.lang.AST.{ BinaryOp, Not, IntArrayAccess, FieldAccess, ArrayLength, ObjectID, ArrayID, Range, In }
    case class IllegalAction(msg: String) extends RuntimeException
    val curMode = mode.asInstanceOf[Trace]
    val curNewShapes = Set.empty[Shape]
    var shouldDo = shouldDoExpr
    def addAction(createNewPrim: Boolean)(a: Action): Shape = {
      def addCallable(c: ConcreteOp, args: List[Expr]) = addShape{ g => {
	val result = executor.evaluate(makeMemory(), c.e)
	val str = makeCallString(c, args, Some(result), printer)
	val argShapes = args map addAction(createNewPrim)
	val g = getGraphics()
	val (w, h) = (widthOfString(str, g), heightOfString(str, g))
        val (x, y) = findLocation(OBJECT_SPACING, OBJECT_SPACING, w, h, true, toplevelShapes.toList ++ argShapes ++ curNewShapes)
        val (argArrows, resultArrow) = makeCallArrows(argShapes, result, x, y, w, h)
	FuncCall(c, argArrows, Some(result), resultArrow, str, x, y, w, h, false)
      } }
      def addAndReturnShape(s: Shape): Shape = { curNewShapes += s; s }
      a match {
	case Null => nulls.head
	case ASTVar(n) if variables contains n => variables(n)
	case ASTVar(n) => curMode.newShapes.find{ _ match { case v: Var if v.name == n => true case _ => false } }.get
	case IntArrayAccess(a, i) => arrElems(shapeToValue(addAction(createNewPrim)(a)).asInstanceOf[IntArray].id)(shapeToValue(addAction(false)(i)).asInstanceOf[IntConstant].n)
	case FieldAccess(o, f) => fields(shapeToValue(addAction(createNewPrim)(o)).asInstanceOf[Object].id)(f)
	case ArrayLength(a) => arrLens(shapeToValue(addAction(createNewPrim)(a)).asInstanceOf[IntArray].id)
	case p: Primitive => if (createNewPrim) addAndReturnShape(makePrim(p, curNewShapes)(getGraphics())) else makePrim(p, curNewShapes)(getGraphics())
	case c @ Call(n, a) if helperFunctions.contains(n) =>
	  val s = addCallable(ConcreteCall(c), a)
	  doCall(s, s.x, s.y, s.width, s.height)
	  s
	case e: BinaryOp => addCallable(ConcreteBinaryOp(e), List(e.lhs, e.rhs))
	case e: Not => addCallable(ConcreteUnaryOp(e), List(e.c))
	case Assign(l, r) if curMode.isInstanceOf[StmtTrace] =>
	  val lhsExists = l match {
	    case ASTVar(n) => variables.contains(n) || curMode.newShapes.exists{ _ match { case v: Var if v.name == n => true case _ => false } }
	    case _ => true  // TODO: I should actually check this too, although if I don't I just get a different error anyway....
	  }
	  if (lhsExists && !typer.canAssign(l, r, makeMemory()))
	    throw new IllegalAction(printer.stringOfAction(a) + ": lhs and rhs have different types.")
	  val rShape = addAction(false)(r)
	  val lShape = l match {
	    case ASTVar(n) if !lhsExists => (if (shapeToValue(rShape).isInstanceOf[HeapValue]) addPointer(n, curNewShapes) else addPrimVar(n, curNewShapes)).get
	    case _ => addAction(false)(l)
	  }
	  doAssignment(curMode.asInstanceOf[StmtTrace], lShape, rShape)
	  shouldDo = false
	  lShape
	case ObjectID(id) => objects(id)
	case ArrayID(id) => arrays(id)
	//case r: Range => addCallable(ConcreteBinaryOp(r), List(r.min, r.max))  // TODO/FIXME: This doesn't work since evaluate(range) returns an array.  Maybe make a RangeVal thing?
	//case i @ In(n, r) => addCallable(ConcreteBinaryOp(i), List(n, r))
	case _ => throw new RuntimeException
      }
    }
    try {
      val shape = addAction(!shouldDo)(a)
      if (shouldDo)
	doExpr(curMode, shape)
      curMode.newShapes ++= curNewShapes
      smartRepaintBounds(curNewShapes flatMap getAllBounds)
      true
    } catch {
      case e: Throwable =>
	e.printStackTrace()
	val msg = e match {
	  case IllegalAction(msg) => msg
	  case _ => "Illegal action " + printer.stringOfAction(a)
	}
	SynthesisGUI.showError(gui, msg)
	false
    }
  }

  def layoutObjects() {
    val g = getGraphics()
    useUserObjectLayout(objects.values.toSet, getGraphics())
    repaint()
  }

  def startUnordered() = startBlock(UnorderedTrace(ListBuffer.empty))
  def startSnapshot() = startBlock(SnapshotTrace)
  def startConditional() = startBlock(ConditionalTrace(None, ListBuffer.empty))
  def startLoop() = startBlock(LoopTrace(None, ListBuffer.empty, makeMemory().clone))  // We clone the memory since we need the initial memory before any changes, and the gui directly modifies the objects and arrays.
  private def startBlock(curBlock: TraceBlock) {
    addBlock(curBlock)
    gui.addEdit(new StartBlockEdit(curBlock))
  }
  private def addBlock(curBlock: TraceBlock) {
    val curMode = mode.asInstanceOf[StmtTrace]
    curMode.curBlocks ::= curBlock
    setGuiCurrentStmts(curMode)
  }

  def finishBlock() {
    val block = removeBlock()
    gui.addEdit(new FinishBlockEdit(block))
  }
  private def removeBlock(): TraceBlock = {
    val curMode = mode.asInstanceOf[StmtTrace]
    val block = (curMode.curBlocks: @unchecked) match {
      case curBlock :: rest =>
	curMode.curBlocks = rest
	addActionToTraceBlock(blockToAction(curBlock, None), curMode)
	curBlock
    }
    setGuiCurrentStmts(curMode)
    block
  }

  def finishIteration() {
    val curMode = mode.asInstanceOf[StmtTrace]
    val (curBlock, restBlocks) = (curMode.curBlocks: @unchecked) match {
      case (i: LoopTrace) :: r => (i, r)
    }
    val curCode = gui.getCode()
    mode = Observer
    gui.hideTraceControls()
    // TODO/FIXME: Add the ability to do LiteralExpr/Stmt.  By default it's off, but it should be selectable.
    // TODO/FIXME: Investigate why we ask so many more queries (GuiTest selectionSort vs. Test selectionSortSwap).  Part is that we don't give as much (Test gives the second full iteration and the third condition).  We also don't do initial pruning before the second trace.  Is there more to it?  Can we regain some of this?  selectionSortSwap in Test takes about 6 queries.  GuiTest with same array asks, on the first trace, 5 in the inner loop, 5 on outer loop, then 9 afterwards.  Part of this is due to the fact that we get fewer details after the first iteration: Test will give i<a.length form every iteration, GuiTest will give it for the first iteration but true/false after that, which has less information.
    invokeOffSwingThread[LoopFinalInfo, Unit]({
      gui.synthesizeLoop(curBlock.initialMemory, blockToAction(curBlock, None).asInstanceOf[Iterate], curMode.loops, makeMemory())  //  We need the memory before executing any actions in the loop.
    }, _ match {
      case LoopInfo((finalMem, iterate, loop)) =>
	mode = curMode
	curMode.curBlocks = restBlocks
	curMode.loops += iterate -> loop
	addActionToTraceBlock(iterate, curMode)
	gui.setCode(curCode._1, curCode._2, Some(getTraceModeActions(curMode, true)))
	gui.showTraceControls()
	// Update memory with the results from later iterations of the loop and repaint to see it on the screen.
	updateDisplayWithMemory(getGraphics().asInstanceOf[Graphics2D], finalMem, true)
	repaint()
      case e: EndTrace =>
	finishTraceMode()
	gui.finishStmtTrace(e)
      })
  }

  def showMemoryDiff(newMemory: Memory, exprValue: Option[Primitive]) {
    val (newVars, modObjs, modArrs) = graphprog.lang.ASTUtils.diffMemories(makeMemory(), newMemory)
    def addDiffArrow(a: Arrow, p: Pointer, pointerOwnsArrow: Boolean) {
      diffArrows += a
      if (!pointerOwnsArrow)
	diffArrowMap += (p -> (a :: diffArrowMap.getOrElse(p, Nil)))
    }
    def updateShape(s: Shape, v: Value) {
      def updateShape(s: Shape, v: Value, origShape: Shape): Unit = s match {
	case p @ Prim(_, data, _, _, _, _) =>
	  diffOriginalVals += (() => p.data = data)
	  p.data = Some(v.asInstanceOf[Primitive])
	  diffShapes += origShape
	case s @ MVal(_, data, _, _, _, _) =>
	  diffOriginalVals += (() => s.data = data)
	  s.data = v.asInstanceOf[Primitive]
	  diffShapes += origShape
	case p: Pointer =>
	  val target = (v: @unchecked) match {
	    case Null => None
	    case h: HeapValue => Some(getHeapShape(h))
	  }
	  val arrow = makeArrow(p.x, p.y, p.width, p.height, target)
	  addArrow(arrow, p)
	  addDiffArrow(arrow, p, false)
	  oldDiffArrows += p.arrow
	case c: Child[_, _] => updateShape(c.child, v, c)
	case s => throw new IllegalArgumentException(s.toString)
      }
      updateShape(s, v, s)
    }
    newVars foreach { case (n, v) => variables.get(n) match { 
      case Some(s) => updateShape(s, v)
      case None =>
	val newShape = createVarShape(getGraphics(), n, v, OBJECT_SPACING, OBJECT_SPACING, true)
	newDiffShapes += newShape
	newShape match {
	  case p: Pointer => addDiffArrow(p.arrow, p, true)
	  case _ =>
	}
    } }
    modObjs foreach { case ((id, f), v) => updateShape(fields(id)(f), v) }
    modArrs foreach { case ((id, i), v) => updateShape(arrElems(id)(i), IntConstant(v)) }
    exprValue foreach { p => newDiffShapes += makePrim(p, Nil)(getGraphics()) }
    repaint()
  }
  def hideMemoryDiff() {
    diffShapes.clear()
    diffOriginalVals.foreach{ _() }
    diffOriginalVals.clear()
    newDiffShapes.filterNot{ _.isInstanceOf[IVal] }.foreach(removeShape)  // makePrim returns an IVal and removeShape can't handle it.  But all I need to do is remove it from newDiffShapes, which the next line does.
    newDiffShapes.clear()
    diffArrows.foreach(removeArrow)
    diffArrows.clear()
    diffArrowMap.clear()
    oldDiffArrows.clear()
    repaint()
  }

  // In this mode, called after ending a new conditional branch, we get actions from the user, and after each check to see if we have <= 1 legal join point.
  def startJoinGuessMode(memory: Memory, joinFinder: List[Action] => Option[List[Stmt]]) {
    startStmtTraceMode(memory)
    val curMode = StmtTrace(ListBuffer.empty, Nil, Map.empty, Set.empty, memory.clone, Some((joinFinder)))
    mode = curMode
    findJoin(curMode)  // We might alreayd know where the join point must be.
  }

  private def findJoin(mode: StmtTrace) {
    val actions = getTraceModeActions(mode, false)
    mode.joinFinder.get(actions) match {
      case Some(newCode) => gui.finishFixing(newCode)
      case _ =>
    }
  }

  def isObserverMode(): Boolean = mode == Observer
  def isQueryMode(): Boolean = mode.isInstanceOf[QueryMode]

  // TODO/FIXME: Add more types of undos.  I currently don't allow undoing end iteration; should I?  Can I easily allow undo moving?  If so, I can probably remove the boolean from updateDisplay that blocks re-layout on undo/redo.
  private class ActionDoneEdit(action: Action, oldMem: Memory, newMem: Memory) extends javax.swing.undo.AbstractUndoableEdit {
    private lazy val name = printer.stringOfAction(action)
    override def canUndo() = true
    override def canRedo() = true
    override def getPresentationName(): String = name
    private def undoOrRedo(m: Memory, f: StmtTrace => Unit) {
      val curMode = mode.asInstanceOf[StmtTrace]
      curMode.initMem = m
      updateDisplayWithMemory(getGraphics().asInstanceOf[Graphics2D], m, false)
      f(curMode)
      setGuiCurrentStmts(curMode)
      gui.repaint()
    }
    override def undo() = undoOrRedo(oldMem, curMode => removeTopActionFromTraceBlock(curMode))
    override def redo() = undoOrRedo(newMem, curMode => addActionToTraceBlock(action, curMode))
  }
  private class StartBlockEdit(block: TraceBlock) extends javax.swing.undo.AbstractUndoableEdit {
    override def canUndo() = true
    override def canRedo() = true
    override def undo() {
      val curMode = mode.asInstanceOf[StmtTrace]
      curMode.curBlocks = curMode.curBlocks.tail
      setGuiCurrentStmts(curMode)
    }
    override def redo() = addBlock(block)
  }
  private class FinishBlockEdit(block: TraceBlock) extends javax.swing.undo.AbstractUndoableEdit {
    override def canUndo() = true
    override def canRedo() = true
    override def undo() {
      val curMode = mode.asInstanceOf[StmtTrace]
      removeTopActionFromTraceBlock(curMode)
      addBlock(block)
      setGuiCurrentStmts(curMode)
    }
    override def redo() = removeBlock()
  }

  def clear() {
    variables.clear
    objects.clear
    arrays.clear
    fields.clear
    arrElems.clear
    arrLens.clear
    pointees.clear
    arrowSources.clear
    nulls.clear
    held = NoHeld
    tooltip = None
    hoveringCall = None
    mode = Observer
    removeMouseMotionListener(tooltipListener)
    removeMouseMotionListener(callHoverListener)
    hideMemoryDiff()
  }

}

private object Canvas {

  val POSSIBILITY_COLOR = Color.GREEN
  val RECEIVER_COLOR = Color.RED
  val SHADOW_COLOR = Color.ORANGE//new Color(255, 220, 0)  // Dark yellow (the default is too hard to see).
  val OLD_DIFF_COLOR = Color.RED
  val NEW_DIFF_COLOR = Color.BLUE
  val TOOLTIP_VOFFSET = 15

}
