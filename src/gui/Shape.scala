package graphprog.gui

import java.awt.{ Color, Font, Graphics2D, Rectangle, Graphics, BasicStroke }
import Shape._
import graphprog.lang.AST.{ Null, Object, Primitive, IntArray, IntConstant, Value, Program, Expr, Var => ASTVar, LVal, Call, Assign, Action, FieldAccess, IntArrayAccess, ArrayLength, ObjectID, ArrayID, HeapValue, Type, PrimitiveType }
import graphprog.lang.ASTUtils.stringOfPrimitive
import graphprog.lang.{ Typer, Printer }
import graphprog.Utils._
import scala.collection.mutable.{ Map, Set, ListBuffer }
import scala.collection.immutable.{ Map => IMap }

// TODO: Separate out location (x,y,w,h) from data?
// TODO: Think of a way to clean up Arrow?
// TODO: Fix ids: IVal might neet it if we can have multiples with the same val.
sealed abstract class Shape {
  var x: Int
  var y: Int
  var width: Int
  var height: Int
}
sealed abstract class HeapObject extends Shape
case class NullShape(id: Int, var x: Int, var y: Int, var width: Int, var height: Int) extends HeapObject{
  override def equals(o: Any) = o match { case NullShape(id2, _, _, _, _) => id == id2 case _ => false }  // Nulls need an id since all their other fields can change.
  override def hashCode: Int = id.hashCode
}
sealed abstract class Var extends Shape {
  val name: String
  override def hashCode: Int = name.hashCode  // All the other fields can change.
}
sealed abstract class Val extends Shape {
  def data: Primitive
}
case class MVal(id: Int, var data: Primitive, var x: Int, var y: Int, var width: Int, var height: Int) extends Val {
  override def hashCode: Int = id.hashCode  // All the other fields can change.
}
case class IVal(data: Primitive, var x: Int, var y: Int, var width: Int, var height: Int) extends Val {
  override def hashCode: Int = data.hashCode  // All the other fields can change.
}
case class Prim(name: String, var data: Option[Primitive], var x: Int, var y: Int, var width: Int, var height: Int) extends Var
case class Pointer(name: String, arrow: Arrow, var x: Int, var y: Int, var width: Int, var height: Int) extends Var
case class IntArr(data: IntArray, var x: Int, var y: Int, var width: Int, var height: Int) extends HeapObject {
  override def hashCode: Int = data.hashCode  // We need to avoid loops for circular structures
}
case class Obj(data: Object, var x: Int, var y: Int, var width: Int, var height: Int) extends HeapObject {
  override def hashCode: Int = data.hashCode  // We need to avoid loops for circular structures
}

sealed abstract class Child[T1 <: Shape,T2 <: Shape] extends Shape {
  val child: T1
  val parent: T2
  def x = child.x
  def x_=(newX: Int) = child.x = newX
  def y = child.y
  def y_=(newY: Int) = child.y = newY
  def width = child.width
  def width_=(newWidth: Int) = child.width = newWidth
  def height = child.height
  def height_=(newHeight: Int) = child.height = newHeight
  override def hashCode: Int = child.hashCode
}
case class Field(child: Var, parent: Obj) extends Child[Var, Obj]
case class IntArrAccess(child: MVal, index: Int, parent: IntArr) extends Child[MVal, IntArr]
case class ArrLen(child: IVal, parent: IntArr) extends Child[IVal, IntArr]

sealed abstract class Callable {
  def numInputs: Int
}
case class Prog(prog: Program) extends Callable {
  def numInputs: Int = prog.inputs.size
}
sealed abstract class Op extends Callable {
  val name: String
  def getArgTypes(): List[Type]
}
case class UnaryOp(name: String, op: Expr => Expr, argType: Type) extends Op {
  def getArgTypes(): List[Type] = List(argType)
  def numInputs: Int = 1
}
case class BinaryOp(name: String, op: (Expr, Expr) => Expr, argTypes: (Type, Type)) extends Op {
  def getArgTypes(): List[Type] = List(argTypes._1, argTypes._2)
  def numInputs: Int = 2
}
sealed abstract class ConcreteOp extends Callable {
  val e: Expr
}
case class ConcreteUnaryOp(e: Expr) extends ConcreteOp {
  def numInputs: Int = 1
}
case class ConcreteBinaryOp(e: Expr) extends ConcreteOp {
  def numInputs: Int = 2
}
case class ConcreteCall(e: Call) extends ConcreteOp {
  def numInputs: Int = e.args.size
}
case class FuncCall(func: Callable, var argArrows: List[Arrow], var result: Option[Value], var resultArrow: Option[Arrow], var str: String, var x: Int, var y: Int, var width: Int, var height: Int, var isHovering: Boolean) extends Shape {
  def getAllArrows(): Iterable[Arrow] = argArrows ++ resultArrow.toList
  override def hashCode: Int = func.hashCode  // Other fields can change.
}

case class Shadow(data: Shape, var x: Int, var y: Int) extends Shape {
  def width = data.width
  def width_=(newWidth: Int) = data.width = newWidth
  def height = data.height
  def height_=(newHeight: Int) = data.height = newHeight
}
case class Tooltip(msgs: List[String], shape: Shape, var x: Int, var y: Int, var width: Int, var height: Int) extends Shape

case class Arrow(id: Int, var target: Option[Shape], var srcX: Int, var srcY: Int, var dstX: Int, var dstY: Int, var isFlying: Boolean) {
  override def equals(o: Any) = o match { case Arrow(id2, _, _, _, _, _, _) => id == id2 case _ => false }  // Arrows need an id since all their other fields can change.
  override def hashCode: Int = id.hashCode
}

protected[gui] object Shape {

  import scala.annotation.tailrec

  val DEFAULT_WIDTH = 20
  val DEFAULT_HEIGHT = 20
  private val FONT_SIZE = 12
  private val FONT = new Font("Dialog", Font.PLAIN, FONT_SIZE)
  private val TEXT_PADDING = 2
  val ARROWHEAD_SIZE = 7
  val FIELD_PADDING = 5
  private val DEFAULT_COLOR = Color.BLACK
  private val TOOLTIP_COLOR = new Color(Color.YELLOW.getRed(), Color.YELLOW.getGreen(), Color.YELLOW.getBlue(), 192)
  val NULL_WIDTH = 16
  val NULL_HEIGHT = 6
  val OBJECT_SPACING = 40

  private var lastID = -1

  def draw(g: Graphics2D, shape: Shape, getChildren: Shape => Iterable[Shape], colorer: PartialFunction[Shape, Color], arrowColorer: PartialFunction[Arrow, Color], isShadow: Boolean = false, parent: Option[Shape] = None): Unit = {
    def doRect(x: Int, y: Int, w: Int, h: Int) {
      val oldStroke = g.getStroke()
      if (!isShadow && (colorer.isDefinedAt(shape) || (parent.isDefined && colorer.isDefinedAt(parent.get))))
	g.setStroke(new BasicStroke(2))
      g.drawRect(x, y, w, h)
      g.setStroke(oldStroke)
    }
    def drawTextCentered(str: String, x: Int, y: Int, width: Int, height: Int) {
      val fm = g.getFontMetrics()
      val left = x + (width - fm.stringWidth(str)) / 2
      val bottom = y + height / 2 - (fm.getAscent() + fm.getDescent()) / 2 + fm.getAscent()
      g.drawString(str, left.toFloat, bottom.toFloat)
    }
    def drawTextBelow(str: String, x: Int, y: Int, width: Int, height: Int) {
      val fm = g.getFontMetrics()
      val left = x + (width - fm.stringWidth(str)) / 2
      val bottom = y + height + fm.getAscent()
      g.drawString(str, left.toFloat, bottom.toFloat)
    }
    def drawTextLeft(str: String, x: Int, y: Int, height: Int) {
      val fm = g.getFontMetrics()
      val left = x
      val bottom = y + height / 2 - (fm.getAscent() + fm.getDescent()) / 2 + fm.getAscent()
      g.drawString(str, left.toFloat, bottom.toFloat)
    }
    def drawCentered(str: String, x: Int, y: Int, w: Int, h: Int) {
      doRect(x, y, w, h)
      g.setColor(DEFAULT_COLOR)
      g.setFont(FONT)
      drawTextCentered(str, x, y, w, h)
    }
    val curColor = (colorer.orElse((shape: Shape) => shape match { case _ => DEFAULT_COLOR }))(shape)
    if (parent.isEmpty && !isShadow)
      g.setColor(curColor)
    shape match {
      case v: Val => drawCentered(stringOfPrimitive(v.data), v.x, v.y, v.width, v.height)
      case Prim(name, data, x, y, w, _) =>
	doRect(x, y, w, DEFAULT_HEIGHT)
	g.setColor(DEFAULT_COLOR)
	g.setFont(FONT)
	data foreach { data => drawTextCentered(stringOfPrimitive(data), x, y, w, DEFAULT_HEIGHT) }
	drawTextBelow(name, x, y, w, DEFAULT_HEIGHT)
      case src @ Pointer(name, arrow, x, y, w, h) =>
	drawCentered(name, x, y, w, h)
	if (!isShadow)
	  drawArrow(g, arrow, arrowColorer)
      case IntArr(_, x, y, w, h) =>
	doRect(x, y, w, h)
	getChildren(shape).foreach{ e => draw(g, e, getChildren, colorer, arrowColorer, isShadow) }
      case Obj(Object(id, _, fs), x, y, w, h) =>
	doRect(x, y, w, h)
	g.setColor(DEFAULT_COLOR)
	getChildren(shape).foreach{ f => draw(g, f, getChildren, colorer, arrowColorer, isShadow) }
      case call @ FuncCall(_, _, _, _, str, x, y, w, h, isHovering) =>
	drawCentered(str, x, y, w, h)
	if (isHovering && !isShadow)
	  call.getAllArrows().foreach{ a => drawArrow(g, a, arrowColorer) }
      case Shadow(shape, x, y) =>
	val shadowG = g.create().asInstanceOf[Graphics2D]
	shadowG.translate(x - shape.x, y - shape.y)
	draw(shadowG, shape, getChildren, colorer, arrowColorer, isShadow = true)
      case t @ Tooltip(msgs, _, x, y, w, h) =>
	doRect(x, y, w, h)
	g.setColor(TOOLTIP_COLOR)
	g.fillRect(x, y, w, h)
	g.setColor(curColor)
	msgs.foldLeft(y){ (y, msg) => {
	  val h = heightOfString(msg, g)
	  drawTextLeft(msg, x + TEXT_PADDING, y, h)
	  y + h
	}}
      case ArrLen(IVal(len, x, y, w, h), _) => drawCentered("length: " + stringOfPrimitive(len), x, y, w, h)
      case c: Child[_, _] => draw(g, c.child, getChildren, colorer, arrowColorer, isShadow, parent = Some(c))
      case NullShape(_, x, y, w, h) =>
	g.drawLine(x, y, x + w, y)
	g.drawLine(x + 2, y + h / 2, x + w - 2, y + h / 2)
	g.drawLine(x + 4, y + h, x + w - 4, y + h)
    }
  }

  /* Based on the second-to-last answer from http://mathforum.org/library/drmath/view/54146.html. */
  def drawArrow(g: Graphics2D, a: Arrow, arrowColorer: PartialFunction[Arrow, Color]): Unit = {
    val oldStroke = g.getStroke()
    if (arrowColorer.isDefinedAt(a)) {
      g.setColor(arrowColorer(a))
      g.setStroke(new BasicStroke(2))
    }
    val (srcX, srcY, dstX, dstY) = (a.srcX, a.srcY, a.dstX, a.dstY)
    val deltaX = dstX - srcX
    val deltaY = dstY - srcY
    val len = math.sqrt(deltaX * deltaX + deltaY * deltaY)
    val constant = ARROWHEAD_SIZE / (math.sqrt(2) * len)
    g.drawLine(srcX, srcY, dstX, dstY)
    g.setStroke(oldStroke)
    if (a.target.isDefined || a.isFlying) {
      g.drawLine(dstX - ((deltaX - deltaY) * constant).toInt, dstY - ((deltaY + deltaX) * constant).toInt, dstX, dstY)
      g.drawLine(dstX - ((deltaX + deltaY) * constant).toInt, dstY - ((deltaY - deltaX) * constant).toInt, dstX, dstY)
    }
  }

  def makeNull(x: Int, y: Int, w: Int, h: Int): NullShape = {
    lastID += 1
    NullShape(lastID, x, y, w, h)
  }

  def makeMVal(data: Primitive, x: Int, y: Int, w: Int, h: Int): MVal = {
    lastID += 1
    MVal(lastID, data, x, y, w, h)
  }

  def makeArrow(srcX: Int, srcY: Int, srcW: Int, srcH: Int, dst: Option[Shape]): Arrow = {
    lastID += 1
    dst match {
      case None => Arrow(lastID, dst, srcX, srcY, srcX + srcW, srcY + srcH, false)
      case Some(target) => Arrow(lastID, dst, srcX + srcW / 2, srcY + srcH / 2, getArrowDst(srcX + srcW / 2, target.x, target.width), getArrowDst(srcY + srcH / 2, target.y, target.height), false)
    }
  }
  def updateArrow(a: Arrow, srcX: Int, srcY: Int, srcW: Int, srcH: Int, newTarget: Option[Shape]) = {
    a.target = newTarget
    newTarget match {
      case None => a.srcX = srcX; a.srcY = srcY; a.dstX = srcX + srcW; a.dstY = srcY + srcH
      case Some(target) => a.srcX = srcX + srcW / 2; a.srcY = srcY + srcH / 2; a.dstX = getArrowDst(a.srcX, target.x, target.width); a.dstY = getArrowDst(a.srcY, target.y, target.height)
    }
  }
  private def getArrowDst(src: Int, dst: Int, wh: Int): Int = if (src <= dst + wh / 2) dst else dst + wh

  def widthOfVar(name: String, value: Value, g: Graphics): Int = value match {
    case p: Primitive => math.max(DEFAULT_WIDTH, math.max(stringWidth(g, name), stringWidth(g, stringOfPrimitive(p))))
    case _: IntArray | _: Object | Null => math.max(DEFAULT_WIDTH, stringWidth(g, name))
  }
  def widthOfVal(value: Value, g: Graphics, fieldLayouts: IMap[String, List[List[String]]]): Int = value match {
    case p: Primitive => widthOfString(stringOfPrimitive(p), g)
    case IntArray(_, array) => math.max(array.map{ v => widthOfVal(IntConstant(v), g, fieldLayouts) }.sum, widthOfString("length: " + array.length, g))
    case Object(_, _, fields) if fields.isEmpty => DEFAULT_WIDTH
    case Object(_, typ, fields) if fieldLayouts.contains(typ) => fieldLayouts(typ).map{ _.map{ f => widthOfVar(f, fields(f), g) + FIELD_PADDING }.sum }.max + FIELD_PADDING
    case Object(_, _, fields) => fields.map{ f => widthOfVar(f._1, f._2, g) }.max + 2 * FIELD_PADDING
  }
  def widthOfProgram(p: Program, g: Graphics): Int = widthOfString(p.name, g)
  def widthOfString(s: String, g: Graphics): Int = math.max(DEFAULT_WIDTH, stringWidth(g, s))

  def heightOfVar(name: String, value: Value, g: Graphics): Int = value match {
    case _: Primitive => DEFAULT_HEIGHT + g.getFontMetrics.getAscent() + g.getFontMetrics.getDescent()
    case _: IntArray | _: Object | Null => DEFAULT_HEIGHT
  }
  def heightOfVal(value: Value, g: Graphics, fieldLayouts: IMap[String, List[List[String]]]): Int = value match {
    case p: Primitive => heightOfString(stringOfPrimitive(p), g)
    case IntArray(_, array) => (if (array.size > 0) heightOfString("1", g) else 0) + heightOfString(array.length.toString, g)
    case Object(_, _, fields) if fields.isEmpty => DEFAULT_HEIGHT
    case Object(_, typ, fields) if fieldLayouts.contains(typ) => fieldLayouts(typ).map{ _.map{ f => heightOfVar(f, fields(f), g) }.max + FIELD_PADDING }.sum + FIELD_PADDING
    case Object(_, _, fields) if fields.nonEmpty => fields.foldLeft(FIELD_PADDING){ (acc, cur) => acc + heightOfVar(cur._1, cur._2, g) + FIELD_PADDING }
  }
  def heightOfProgram(p: Program, g: Graphics): Int = heightOfString(p.name, g)
  def heightOfString(s: String, g: Graphics): Int = DEFAULT_HEIGHT

  def stringWidth(g: Graphics, s: String): Int = g.getFontMetrics().stringWidth(s) + 2 * TEXT_PADDING

  def moveShape(shape: Shape, dx: Int, dy: Int, getChildren: Shape => Iterable[Shape], getArrowsTo: Shape => Iterable[Arrow], getArrowsFrom: Shape => Iterable[Arrow]): Unit = {
    getChildren(shape).foreach{ e => moveShape(e, dx, dy, getChildren, getArrowsTo, getArrowsFrom) }
    shape.x += dx
    shape.y += dy
    getArrowsFrom(shape).foreach{ a => a match {
      case Arrow(_, None, _, _, _, _, _) => a.srcX += dx; a.srcY += dy; a.dstX += dx; a.dstY += dy
      case Arrow(_, Some(dst), srcX, srcY, _, _, _) => updateArrow(a, srcX + dx, srcY + dy, 0, 0, a.target)
    }}
    getArrowsTo(shape).foreach{ a => updateArrow(a, a.srcX, a.srcY, 0, 0, a.target) }
  }

  def shapesCanReceive(lhs: Shape, rhs: Shape, typer: Typer, isExpr: Boolean): Boolean = {
    if (!shapeToValue.isDefinedAt(rhs))
      return false
    def canReceive(lhs: Shape): Boolean = lhs match {
      case MVal(_, data, _, _, _, _) => !isExpr && typer.canAssign(data, shapeToValue(rhs))
      case Prim(_, Some(data), _, _, _, _) => !isExpr && typer.canAssign(data, shapeToValue(rhs))
      case Prim(_, None, _, _, _, _) => !isExpr && typer.typeOfValue(shapeToValue(rhs)).isInstanceOf[PrimitiveType]
      case Pointer(_, Arrow(_, target, _, _, _, _, _), _, _, _, _) => !isExpr && typer.canAssign(shapeToValue(target), shapeToValue(rhs))
      case Field(f, _) => !isExpr && canReceive(f)
      case IntArrAccess(e, _, _) => !isExpr && canReceive(e)
      case FuncCall(Prog(prog), argArrows, None, _, _, _, _, _, _, _) if argArrows.size < prog.inputs.size => typer.canAssign(prog.inputs(argArrows.size)._2, shapeToValue(rhs))
      case FuncCall(_: BinaryOp, List(a), None, _, _, _, _, _, _, _) => typer.canAssign(shapeToValue(a.target), shapeToValue(rhs))  // Binary ops can be generic (like =), so use the type of the lhs if we have it.
      case FuncCall(op: Op, argArrows, None, _, _, _, _, _, _, _) if argArrows.size < op.numInputs => typer.canAssign(op.getArgTypes()(argArrows.size), shapeToValue(rhs))
      case _ => false
    }
    canReceive(lhs)
  }

  def assign(lhs: Shape, rhs: Shape, pointees: Map[Option[Shape], Set[Arrow]]): Action = {
    // Update the gui with the result of the assignment
    def updateGUIWithAssignment(lhs: Shape, rhs: Shape): Unit = {
      @tailrec def getPrimitive(shape: Shape): Primitive = (shape: @unchecked) match {
	case v: Val => v.data
	case Prim(_, Some(data), _, _, _, _) => data
	case c: Child[_, _] => getPrimitive(c.child)
	case FuncCall(_, _, Some(result), _, _, _, _, _, _, _) => result.asInstanceOf[Primitive]
      }
      lhs match {
	case v: MVal => v.data = getPrimitive(rhs)
	case p: Prim => p.data = Some(getPrimitive(rhs))
	case Pointer(_, a @ Arrow(_, oldTarget, _, _, _, _, _), x, y, w, h) =>
	  val newTarget = (rhs: @unchecked) match {
	    case _: NullShape => None
	    case s: HeapObject => Some(s)
	    case Pointer(_, Arrow(_, target, _, _, _, _, _), _, _, _, _) => target
	    case Field(Pointer(_, Arrow(_, target, _, _, _, _, _), _, _, _, _), _) => target
	    case FuncCall(_, _, _, Some(Arrow(_, target @ Some(_: HeapObject), _, _, _, _, _)), _, _, _, _, _, _) => target
	  }
	  updateArrow(a, x, y, w, h, newTarget)
	  if (pointees.contains(oldTarget))
	    pointees(oldTarget) -= a
	  pointees.getOrElseUpdate(newTarget, Set.empty) += a
	case Field(field, Obj(Object(_, _, fields), _, _, _, _)) =>
	  fields(field.name) = shapeToValue(rhs)
	  updateGUIWithAssignment(field, rhs)
	case IntArrAccess(e, i, IntArr(IntArray(_, array), _, _, _, _)) =>
	  array(i) = shapeToValue(rhs).asInstanceOf[IntConstant].n
	  updateGUIWithAssignment(e, rhs)
      }
    }
    updateGUIWithAssignment(lhs, rhs)
    // Return the Action representing it.
    Assign(shapeToLVal(lhs), shapeToExpr(rhs))
  }

  def getBinding(v: Var): (String, Value) = v.name -> ((v: @unchecked) match {
    case Prim(_, Some(data), _, _, _, _) => data
    case Pointer(_, Arrow(_, target, _, _, _, _, _), _, _, _, _) => shapeToValue(target)
  })

  def shapeToValue(shape: Option[Shape]): Value = shape match {
    case None => Null
    case Some(s) => shapeToValue(s)
  }
  val shapeToValue: PartialFunction[Shape, Value] = {
    case _: NullShape => Null
    case v: Val => v.data
    case Prim(_, Some(d), _, _, _, _) => d
    case Pointer(_, Arrow(_, target, _, _, _, _, _), _, _, _, _) => shapeToValue(target)
    case IntArr(arr, _, _, _, _) => arr
    case Obj(o, _, _, _, _) => o
    case c: Child[_, _] => shapeToValue(c.child)
    case FuncCall(_, _, Some(result), _, _, _, _, _, _, _) => result
  }
  def shapeToExpr(shape: Option[Shape]): Expr = shape match {
    case None => Null
    case Some(s) => shapeToExpr(s)
  }
  def shapeToExpr(shape: Shape): Expr = shape match {
    case ArrLen(_, IntArr(a, _, _, _, _)) => ArrayLength(a)
    case FuncCall(Prog(f), argArrows, _, _, _, _, _, _, _, _) if argArrows.size == f.inputs.size => Call(f.name, argArrows.map{ a => shapeToExpr(a.target) }.toList)
    case FuncCall(UnaryOp(_, op, _), List(a), _, _, _, _, _, _, _, _) => op(shapeToExpr(a.target))
    case FuncCall(BinaryOp(_, op, _), List(a1, a2), _, _, _, _, _, _, _, _) => op(shapeToExpr(a1.target), shapeToExpr(a2.target))
    case FuncCall(op: ConcreteOp, _, _, _, _, _, _, _, _, _) => op.e
    case IntArr(IntArray(id, _), _, _, _, _) => ArrayID(id)
    case Obj(Object(id, _, _), _, _, _, _) => ObjectID(id)  // If we returned the object directly, executing a call would modify the object directly.
    case _ => (shapeToLVal orElse shapeToValue)(shape)
  }
  private val shapeToLVal: PartialFunction[Shape, LVal] = {
    case v: Var => ASTVar(v.name)
    case Field(field, Obj(Object(id, _, _), _, _, _, _)) => FieldAccess(ObjectID(id), field.name)  // As above in shapeToExpr, we return a reference to the object and not the object itself since it is only a copy of the real object in the synthesizer.
    case IntArrAccess(_, i, IntArr(IntArray(id, _), _, _, _, _)) => IntArrayAccess(ArrayID(id), IntConstant(i))
  }

  def makeCallArrow(x: Int, y: Int, w: Int, numArgs: Int, target: Option[Shape], i: Int, pointees: Map[Option[Shape], Set[Arrow]]): Arrow = {
    val arrow = makeArrow(getCallArrowX(x, w, numArgs, i), y, 0, 0, target)
    pointees.getOrElseUpdate(target, Set.empty) += arrow
    arrow
  }
  def getCallArrowX(x: Int, w: Int, numArgs: Int, i: Int): Int = (x + ((i + 1).toFloat / (numArgs + 1)) * w).toInt

  def makeCallResultArrow(x: Int, y: Int, w: Int, h: Int, target: Option[Shape], pointees: Map[Option[Shape], Set[Arrow]]): Arrow = {
    val arrow = makeArrow(x + w / 2, y + h, 0, 0, target)
    pointees.getOrElseUpdate(target, Set.empty) += arrow
    arrow
  }

  def makeCallString(c: Callable, args: List[Expr], result: Option[Value], printer: Printer): String = {
    def stringOfOptExpr[T <: Expr](e: Option[T]): String = e match { case Some(e) => printer.stringOfExpr(e) case None => "?" }
    val fullArgs = args.map{ x => Some(x) }.padTo(c.numInputs, None)
    c match {
      case Prog(prog) => prog.name + "(" + iterableToString(fullArgs, ", ", stringOfOptExpr) + ") = " + stringOfOptExpr(result)
      case UnaryOp(name, _, _) => name + stringOfOptExpr(fullArgs(0)) + " = " + stringOfOptExpr(result)
      case BinaryOp(name, _, _) => stringOfOptExpr(fullArgs(0)) + " " + name + " " + stringOfOptExpr(fullArgs(1)) + " = " + stringOfOptExpr(result)
      case op: ConcreteOp => assert(args.size == op.numInputs && result.isDefined); printer.stringOfExpr(op.e) + " = " + printer.stringOfExpr(result.get)
    }
  }

}
