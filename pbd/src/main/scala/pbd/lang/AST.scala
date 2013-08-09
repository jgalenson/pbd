package pbd.lang

object AST {

  import scala.collection.mutable.{ Map => MMap }

  sealed trait Type
  sealed trait PrimitiveType extends Type
  case object ErrorType extends Type
  case object UnitType extends PrimitiveType
  case object IntType extends PrimitiveType
  case object BooleanType extends PrimitiveType
  case object StringType extends PrimitiveType
  sealed trait HeapType extends Type
  case class ArrayType(t: Type) extends HeapType
  //We use name based typing, not structural
  case class ObjectType(name: String) extends HeapType
  case object GenericType extends Type

  trait Result
  trait Value extends Expr with Result
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
  case class ArrayValue(id: Int, array: Array[Value], elemType: Type) extends HeapValue {
    override def equals(o: Any) = o match { case ArrayValue(id2, _, _) => id == id2 case _ => false }
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
  case class ArrayAccess(array: Expr, index: Expr) extends LVal
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
  sealed trait EvidenceHole extends Hole
  case class ExprEvidenceHole(evidence: List[(Expr, Memory)]) extends Expr with EvidenceHole
  case class StmtEvidenceHole(evidence: List[(Action, Memory)]) extends Stmt with EvidenceHole
  case class PossibilitiesHole(possibilities: List[Stmt]) extends Expr with Hole {
    override def equals(o: Any) = o match { case o: AnyRef => this eq o case _ => false }  // Compare holes by reference so two holes that look the same are not equal (needed for pruning).
  }
  sealed trait Unseen extends Hole {
    override def equals(o: Any) = o match { case o: AnyRef => this eq o case _ => false }  // Compare holes by reference so two holes that look the same are not equal (needed for mapping different Unseens to different actual statements).
  }
  case class UnseenExpr() extends Expr with Unseen
  case class UnseenStmt() extends Action with Unseen

  sealed trait Stmt
  case class Assign(lhs: LVal, rhs: Expr) extends Action
  case class If(condition: Expr, thenBranch: List[Stmt], elseIfPaths: List[(Expr, List[Stmt])], elseBranch: List[Stmt]) extends Stmt
  case class Assume(condition: Expr) extends Action
  case class Assert(condition: Expr) extends Action
  case class Loop(condition: Stmt, body: List[Stmt]) extends Stmt
  case class Iterate(iterations: List[(Action, List[Action])]) extends Action
  case object Break extends Action
  case class Println(s: StringConstant) extends Action

  sealed trait TLiteral[T <: Action] { val l: T }
  sealed trait TLiteralExpr[T <: Expr] extends TLiteral[Expr] { val l: T }
  case class LiteralAction(l: Action) extends Action with TLiteral[Action]
  case class LiteralExpr(l: Expr) extends Expr with TLiteralExpr[Expr]

  case class UnorderedStmts(s: List[Stmt]) extends Action
  case class Snapshot(memory: Memory) extends Action

  sealed trait Synthetic
  case class UnknownJoinIf(known: If, unknown: List[Stmt]) extends Stmt with Synthetic

  case class Program(name: String, typ: Type, inputs: List[(String, Type)], functions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], stmts: List[Stmt])
  case class Trace(name: String, typ: Type, inputs: List[(String, Value)], functions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], actions: List[Action])

  /* Helper classes */

  case class SideEffect(effect: (Memory, Memory), value: Value) extends Result

}
