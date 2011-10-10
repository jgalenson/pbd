package graphprog.lang

object AST {

  import scala.collection.mutable.{ Map => MMap, HashMap => MHashMap, Stack }

  // TODO: Arrays are borked: I hardcode IntArray in many places (including in access).
  sealed trait Type
  sealed trait PrimitiveType extends Type
  case object ErrorType extends Type
  case object UnitType extends PrimitiveType
  case object IntType extends PrimitiveType
  case object BooleanType extends PrimitiveType
  case object StringType extends PrimitiveType
  sealed trait HeapType extends Type
  case class ArrayType(t: Type) extends HeapType
  case class ObjectType(name: String) extends HeapType
  case object GenericType extends Type

  trait Value extends Expr
  trait IsErrorOrFailure
  case object ErrorConstant extends Value with IsErrorOrFailure
  case object AssumeFailed extends Value with IsErrorOrFailure
  case object AssertFailed extends Value with IsErrorOrFailure
  case object BreakHit extends Value
  case object UnitConstant extends Value
  sealed trait Primitive extends Value
  case class IntConstant(n: Int) extends Primitive
  case class BooleanConstant(b: Boolean) extends Primitive
  case class StringConstant(s: String) extends Primitive
  sealed trait HeapValue extends Value
  case class IntArray(id: Int, array: Array[Int]) extends HeapValue {
    override def equals(o: Any) = o match { case IntArray(id2, _) => id == id2 case _ => false }
    override def hashCode: Int = id.hashCode
  }
  case class Object(id: Int, typ: String, fields: MMap[String, Value]) extends HeapValue {
    override def equals(o: Any) = o match { case Object(id2, _, _) => id == id2 case _ => false }
    override def hashCode: Int = id.hashCode
    override def toString: String = typ + "(" + id.toString + ")"  // Needed so toString of circular objects doesn't infinite loop.
  }
  case object Null extends HeapValue

  sealed trait Expr extends Action
  sealed trait LVal extends Expr
  case class Var(name: String) extends LVal
  case class IntArrayAccess(array: Expr, index: Expr) extends LVal
  case class FieldAccess(obj: Expr, field: String) extends LVal
  case class ArrayLength(e: Expr) extends Expr
  case class ObjectID(id: Int) extends Expr
  case class ArrayID(id: Int) extends Expr
  case class Call(name: String, args: List[Expr]) extends Expr  // Call a complete/known function.
  case class In(name: Var, range: Range) extends Expr
  sealed abstract class Range(val isInclusive: Boolean) extends Expr { val min: Expr; val max: Expr }
  case class To(min: Expr, max: Expr) extends Range(true)
  case class Until(min: Expr, max: Expr) extends Range(false)
  sealed abstract class BinaryOp extends Expr { val lhs: Expr; val rhs: Expr }
  sealed abstract class Comparison extends BinaryOp { val lhs: Expr; val rhs: Expr }
  case class EQ(lhs: Expr, rhs: Expr) extends Comparison
  case class NE(lhs: Expr, rhs: Expr) extends Comparison
  case class LT(lhs: Expr, rhs: Expr) extends Comparison
  case class LE(lhs: Expr, rhs: Expr) extends Comparison
  case class GT(lhs: Expr, rhs: Expr) extends Comparison
  case class GE(lhs: Expr, rhs: Expr) extends Comparison
  case class And(lhs: Expr, rhs: Expr) extends Comparison
  case class Or(lhs: Expr, rhs: Expr) extends Comparison
  case class Not(c: Expr) extends Expr
  sealed abstract class Arithmetic extends BinaryOp { val lhs: Expr; val rhs: Expr }
  case class Plus(lhs: Expr, rhs: Expr) extends Arithmetic
  case class Minus(lhs: Expr, rhs: Expr) extends Arithmetic
  case class Times(lhs: Expr, rhs: Expr) extends Arithmetic
  case class Div(lhs: Expr, rhs: Expr) extends Arithmetic

  sealed trait Action extends Stmt
  case class Conditional(condition: Expr, body: List[Action]) extends Action

  sealed trait Hole
  case class ExprEvidenceHole(evidence: List[(Expr, Memory)]) extends Expr with Hole
  case class StmtEvidenceHole(evidence: List[(Action, Memory)]) extends Stmt with Hole
  case class PossibilitiesHole(possibilities: List[Stmt]) extends Expr with Hole {
    override def equals(o: Any) = o match { case o: AnyRef => this eq o case _ => false }  // Compare holes by reference so two holes that look the same are not equal (needed for pruning).
  }
  sealed trait Unseen extends Hole {
    override def equals(o: Any) = o match { case o: AnyRef => this eq o case _ => false }  // Compare holes by reference so two holes that look the same are not equal (needed for mapping different Unseens to different actual statements).
  }
  case class UnseenExpr extends Expr with Unseen
  case class UnseenStmt extends Action with Unseen

  sealed trait Stmt
  case class Assign(lhs: LVal, rhs: Expr) extends Action
  case class If(condition: Expr, thenBranch: List[Stmt], elseIfPaths: List[(Expr, List[Stmt])], elseBranch: List[Stmt]) extends Stmt
  case class Assume(condition: Expr) extends Action
  case class Assert(condition: Expr) extends Action
  case class Loop(condition: Stmt, body: List[Stmt]) extends Stmt
  case class Iterate(iterations: List[(Action, List[Action])]) extends Action
  case object Break extends Action
  case class Println(s: StringConstant) extends Action

  case class LiteralAction(a: Action) extends Action
  case class LiteralExpr(e: Expr) extends Expr

  case class UnorderedStmts(s: List[Stmt]) extends Action
  case class Snapshot(memory: Memory) extends Action

  sealed trait Synthetic
  case class UnknownJoinIf(known: If, unknown: List[Stmt]) extends Stmt with Synthetic

  case class Program(name: String, typ: Type, inputs: List[(String, Type)], functions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], stmts: List[Stmt])
  case class Trace(name: String, typ: Type, inputs: List[(String, Value)], functions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], actions: List[Action])

  /* Helper classes */

  class Memory(val mem: Stack[MMap[String, Value]]) {

    def this(m: MMap[String, Value]) = this(Stack[MMap[String, Value]](m))
    def this(l: TraversableOnce[(String, Value)]) = this(MHashMap.empty ++ l)
    def this() = this(MHashMap[String, Value]())

    def +=(kv: (String, Value)): Memory = {
      mem.find{ _ contains kv._1 } match {
	case Some(m) => m(kv._1) = kv._2
	case None => mem.top += kv
      }
      this
    }
    def apply(key: String): Value = mem.find{ _ contains key }.get(key)
    def contains(key: String): Boolean = mem.find{ _ contains key}.isDefined
    protected[graphprog] def enterScope: Unit = mem push MMap[String, Value]()
    protected[graphprog] def exitScope: Unit = mem pop
    def keys: Iterable[String] = mem flatMap { _.keys }
    override def clone: Memory = {
      val (objects, arrays) = getObjectsAndArrays()
      val clonedObjects = MHashMap.empty ++ (objects mapValues { o => Object(o.id, o.typ, new MHashMap[String, Value]) })  // Note that this needs to be a mutable map not an immutable map or updates to its fields do not stick
      val clonedArrays = MHashMap.empty ++ (arrays mapValues { a => IntArray(a.id, a.array.clone) })
      def myclone(v: Value): Value = v match {
	case IntArray(id, _) => clonedArrays(id)
	case Object(id, _, _) => clonedObjects(id)
	case _ => v
      }
      clonedObjects.values foreach { clone => clone.fields ++= objects(clone.id).fields.map { t => (t._1 -> myclone(t._2)) } }
      val newMemory = Stack[MMap[String, Value]]()
      mem.reverse.foreach { m => newMemory push (MMap.empty ++ m.mapValues(myclone)) }
      new Memory(newMemory)
    }
    def getObject(id: Int): Option[Object] = getObjectsAndArrays()._1.get(id)  // TODO-optimization: We could speed this (and getArray) up by not calling getObjectsAndArrays() and constructing the whole maps.
    def getArray(id: Int): Option[IntArray] = getObjectsAndArrays()._2.get(id)

    def getObjectsAndArrays(): (MMap[Int, Object], MMap[Int, IntArray]) = {
      val objects = new MHashMap[Int, Object]
      val arrays = new MHashMap[Int, IntArray]
      def getObjectAndArray(v: Value): Unit = v match {
	case a: IntArray => arrays += (a.id -> a)
	case o @ Object(id, _, fields) =>
	  if (!objects.contains(id)) {
	    objects += (id -> o)
	    getObjectsAndArrays(fields.values)
	  }
	case _ => ()
      }
      def getObjectsAndArrays(values: Iterable[Value]) = values foreach getObjectAndArray
      getObjectsAndArrays(mem flatMap { _.values })
      (objects, arrays)
    }

    def toIterator: Iterator[(String, Value)] = mem.foldLeft(Iterator.apply[(String, Value)]()){ (acc, cur) => acc ++ cur.toIterator }
    def toMap: Map[String, Value] = toIterator.toMap

  }

}
