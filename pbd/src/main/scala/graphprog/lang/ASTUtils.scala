package graphprog.lang

import AST._
import graphprog.Utils._

protected[graphprog] class Printer(helpers: PartialFunction[String, Value => String], short: Boolean) extends Serializable {

  import scala.collection.immutable.Map
  import scala.collection.immutable.Set
  import graphprog.lang.Memory

  private def stringOfType(t: Type): String = t match {
    case ErrorType => "ERROR"
    case UnitType => "Unit"
    case IntType => "Int"
    case BooleanType => "Boolean"
    case StringType => "String"
    case ArrayType(t) => "Array[" + stringOfType(t) + "]"
    case ObjectType(name) => name
    case GenericType => "?"
  }
  protected[graphprog] def stringOfValue(v: Value, seen: Set[Object] = Set.empty): String = v match {
    case p: Primitive => ASTUtils.stringOfPrimitive(p)
    case ErrorConstant => "ERROR"
    case AssumeFailed => "assume failed"
    case AssertFailed => "assert failed"
    case BreakHit => "break hit"
    case UnitConstant => "()"
    case IntArray(_, array) => "Array(" + iterableToString(array, ",") + ")"
    case o @ Object(id, t, m) => 
      if (helpers isDefinedAt t)
	helpers(t)(v)
      else {
	t + "(" + id.toString + ")" + (if (short || seen(o)) "" else "(" + iterableToString(m, ", ", (kv: (String, Value)) => kv._1 + " -> " + stringOfValue(kv._2, seen + o)) + ")")  // Avoid infinite loops on circular objects
      }
    case Null => "null"
  }
  protected[graphprog] def stringOfExpr(e: Expr): String = {
    // Helper so that we use parenthses to show precedence.
    def stringOfOperand(o: Expr): String = o match {
      case _: BinaryOp => "(" + stringOfExpr(o) + ")"
      case _ => stringOfExpr(o)
    }
    e match {
      case v: Value => stringOfValue(v)
      case h: Hole => stringOfHole(h)
      case Var(name) => name
      case IntArrayAccess(array, index) => stringOfExpr(array) + "[" + stringOfExpr(index) + "]"
      case FieldAccess(obj, field) => stringOfExpr(obj) + "." + field
      case ArrayLength(e) => stringOfExpr(e) + ".length"
      case ObjectID(id) => "ObjectID(" + id.toString + ")"
      case ArrayID(id) => "ArrayID(" + id.toString + ")"
      case Call(name, args) => name + "(" + iterableToString(args, ", ", (e: Expr) => stringOfExpr(e)) + ")"
      case In(name, range) => stringOfExpr(name) + " in " + stringOfExpr(range)
      case To(min, max) => stringOfExpr(min) + " to " + stringOfExpr(max)
      case Until(min, max) => stringOfExpr(min) + " until " + stringOfExpr(max)
      case c: Comparison => stringOfExpr(c.lhs) + Printer.getComparisonSeparator(c) + stringOfExpr(c.rhs)
      case Not(e) => "!" + stringOfOperand(e)
      case Plus(lhs, rhs) => stringOfOperand(lhs) + " + " + stringOfOperand(rhs)
      case Minus(lhs, rhs) => stringOfOperand(lhs) + " - " + stringOfOperand(rhs)
      case Times(lhs, rhs) => stringOfOperand(lhs) + " * " + stringOfOperand(rhs)
      case Div(lhs, rhs) => stringOfOperand(lhs) + " / " + stringOfOperand(rhs)
      case LiteralExpr(e) => "LiteralExpr(" + stringOfExpr(e) + ")"
    }
  }
  private def stringOfBody(b: List[Stmt], indent: String = "") = b match {
    case Nil => " ;"
    case s :: Nil => "\n" + stringOfStmt(s, indent + "  ")
    case _ => " {\n" + stringOfStmts(b, indent + "  ") + "\n" + indent + "}"
  }
  private def stringOfPath(c: Action, b: List[Stmt], prefix: String, indent: String = ""): String = prefix + " (" + stringOfAction(c) + ")" + stringOfBody(b, indent)
  protected[graphprog] def stringOfAction(a: Action, indent: String = ""): String = a match {
    case e: Expr => stringOfExpr(e)
    case h: Hole => stringOfHole(h)
    case Assign(lhs, rhs) => stringOfExpr(lhs) + " := " + stringOfExpr(rhs)
    case Assume(c) => "assume(" + stringOfExpr(c) + ")"
    case Assert(c) => "assert(" + stringOfExpr(c) + ")"
    case Conditional(c, body) => stringOfPath(c, body, "cond", indent)
    case Iterate(iterations) => "iterate {" + iterableToString(iterations, "\n", (actions: (Action, List[Action])) => indent + "  " + stringOfPath(actions._1, actions._2, "iteration", indent + "  "), "\n") + "\n" + indent + "}"
    case Break => "break"
    case Println(s) => "println(" + stringOfValue(s) + ")"
    case LiteralAction(a) => "LiteralAction(" + stringOfAction(a, indent) + ")"
    case UnorderedStmts(s) => "unordered" + stringOfBody(s, indent)
    case Snapshot(m) => "snapshot " + stringOfMemory(m)
  }
  protected[graphprog] def stringOfHole(h: Hole) = h match {
    case ExprEvidenceHole(evidence) => "Hole(" + iterableToString(evidence, " and ", { t: (Action, Memory) => stringOfAction(t._1, "") + " with " + stringOfMemory(t._2) }) + ")"
    case StmtEvidenceHole(evidence) => "Hole(" + iterableToString(evidence, " and ", { t: (Action, Memory) => stringOfAction(t._1, "") + " with " + stringOfMemory(t._2) }) + ")"
    case PossibilitiesHole(possibilities) => "Hole(" + iterableToString(possibilities, " or ", { s: Stmt => stringOfStmt(s, "") }) + ")"
    case _: Unseen => "?"
  }
  protected[graphprog] def stringOfStmt(s: Stmt, indent: String = ""): String = indent + (s match {
    case a: Action => stringOfAction(a, indent)
    case h: Hole => stringOfHole(h)
    case If(condition, thenBranch, elseIfPaths, elseBranch) =>
      val s = stringOfPath(condition, thenBranch, "if", indent) + (if (!elseIfPaths.isEmpty) "\n" else "") + iterableToString(elseIfPaths, "\n", { p: (Expr, List[Stmt]) => stringOfPath(p._1, p._2, "else if", indent) }) + (if (elseBranch.size > 0) "\n" + indent + "else" + stringOfBody(elseBranch, indent) else "")
      s.replaceAll("}\nelse", "} else")
    case Loop(condition, body) => "loop (" + stringOfStmt(condition, "") + ")" + stringOfBody(body, indent)
    case UnknownJoinIf(i, u) => 
      val s = stringOfStmt(i, indent) + (if (u.nonEmpty) "\n" + indent + "unknown" + stringOfBody(u, indent) else "")
      s.replaceAll("}\nunknown", "} unknown")
  })
  protected[graphprog] def stringOfStmts(stmts: Iterable[Stmt], indent: String = ""): String = iterableToString(stmts, "\n", { s: Stmt => stringOfStmt(s, indent) })
  protected[graphprog] def stringOfInputs(inputs: List[(String, Value)], sep: String) = iterableToString(inputs, sep, { t: (String, Value) => "input " + t._1 + " -> " + stringOfValue(t._2) })
  protected[graphprog] def stringOfProgram(program: Program): String = "def " + program.name + "(" + iterableToString(program.inputs, ", ", { i: (String, Type) => "input " + i._1 + ": " + stringOfType(i._2) }) + ") {\n" + stringOfStmts(program.stmts, "  ") + "\n}"
  protected[graphprog] def stringOfTrace(trace: Trace): String = "name " + trace.name + "\n" + stringOfInputs(trace.inputs, "\n") + "\n" + stringOfStmts(trace.actions)
  protected[graphprog] def stringOfMemory(memory: Memory): String = "Mem(" + iterableToString(memory.keys, ", ", (key: String) => key + " -> " + stringOfValue(memory(key))) + ")"

}

protected[graphprog] object Printer {

  def prettyStringOfStmt(s: Stmt, printer: Printer): String = {
    def prettyStringOfPossibilities(ss: List[Stmt]): String = ss.head match {
	case _: Assign => prettyString(ss.collect{ case Assign(l, _) => l }) + " := " + prettyString(ss.collect{ case Assign(_, r) => r })
	case c: Comparison => prettyString(ss.collect{ case c: Comparison => c.lhs }) + getComparisonSeparator(c) + prettyString(ss.collect{ case c: Comparison => c.rhs })
	case Call(n1, a1) if ss.tail.forall{ case Call(n2, a2) => n1 == n2 && a1.size == a2.size case _ => false } => n1 + "(" + iterableToString(ss.collect{ case Call(_, a) => a }.transpose, ", ", (as: List[Expr]) => prettyString(as)) + ")"
	case _ => prettyString(ss)
    }
    def prettyString(es: List[Stmt]): String = {
      assert(es.nonEmpty)
      val uniques = es.toSet
      if (uniques.size == 1)
	printer.stringOfStmt(uniques.head)
      else  // TODO: Which of these should I use?
	"{" + uniques.map{ s => printer.stringOfStmt(s) }.reduceLeft{ (x, y) => if (x.size <= y.size) x else y } + ", " + (uniques.size - 1) + " more}"
	//"{" + iterableToString(uniques, ", ", (s: Stmt) => printer.stringOfStmt(s)) + "}"
	//uniques.size + " possibilities"
    }
    s match {
      case PossibilitiesHole(possibilities) if possibilities.nonEmpty => prettyStringOfPossibilities(possibilities)
      case _ => printer.stringOfStmt(s)
    }
  }

  private def getComparisonSeparator(c: Comparison): String = c match {
    case EQ(_, _) => " = "
    case NE(_, _) => " != "
    case LT(_, _) => " < "
    case LE(_, _) => " <= "
    case GT(_, _) => " > "
    case GE(_, _) => " >= "
    case And(_, _) => " && "
    case Or(_, _) => " || "
  }

}

protected[graphprog] class Typer(functions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]]) extends Serializable {

  protected[graphprog] def typeOfValue(v: Value): Type = Typer.typeOfValue(v)
  protected[graphprog] def typeOfExpr(e: Expr, memory: Memory): Type = e match {
    case Var(name) => typeOfValue(memory(name))
    case FieldAccess(o, f) => objectTypes(typeOfExpr(o, memory).asInstanceOf[ObjectType].name).toMap.get(f).get
    case ObjectID(id) => typeOfValue(memory.getObject(id).get)
    case ArrayID(id) => typeOfValue(memory.getArray(id).get)
    case LiteralExpr(e) => typeOfExpr(e, memory)
    case _ => typeOfExprNoMemory(e)
  }
  private def typeOfExprNoMemory(e: Expr): Type = e match {
    case v: Value => typeOfValue(v)
    case IntArrayAccess(_, _) => IntType
    case ArrayLength(_) => IntType
    case Call(name, _) => functions(name).typ
    case In(_, range) => IntType
    case r: Range => ArrayType(IntType)
    case c: Comparison => BooleanType
    case Not(_) => BooleanType
    case a: Arithmetic => IntType
    case s => throw new IllegalArgumentException("Cannot get the type of stmt " + s + " without memory.")
  }
  protected[graphprog] def typeOfAction(a: Action, memory: Memory): Type = a match {
    case e: Expr => typeOfExpr(e, memory)
    case Assign(_, rhs) => typeOfExpr(rhs, memory)
    case Assume(_) => UnitType
    case Assert(_) => UnitType
    case Conditional(_, _) => UnitType
    case Iterate(_) => UnitType
    case Break => UnitType
    case Println(_) => UnitType
    case LiteralAction(a) => typeOfAction(a, memory)
    case UnorderedStmts(_) => UnitType
    case Snapshot(_) => UnitType
    case UnseenStmt() => throw new IllegalArgumentException("Cannot get type of UnseenStmt")
  }
  private def typeOfStmt(s: Stmt, memory: Memory): Type = s match {
    case a: Action => typeOfAction(a, memory)
    case If(_, _, _, _) | UnknownJoinIf(_, _) => UnitType
    case Loop(_, _) => UnitType
    case StmtEvidenceHole(_) => throw new IllegalArgumentException("Cannot get type of " + s)
  }

  protected[graphprog] def canAssign(lhs: Expr, rhs: Expr): Boolean = {
    canAssignTypes(typeOfExprNoMemory(lhs), typeOfExprNoMemory(rhs))
  }
  protected[graphprog] def canAssign(lhs: Type, rhs: Expr): Boolean = {
    canAssignTypes(lhs, typeOfExprNoMemory(rhs))
  }
  protected[graphprog] def canAssign(lhs: Expr, rhs: Expr, memory: Memory): Boolean = {
    canAssignTypes(typeOfExpr(lhs, memory), typeOfExpr(rhs, memory))
  }
  private def canAssignTypes(l: Type, r: Type): Boolean = (l, r) match {
    case (IntType, IntType) => true
    case (BooleanType, BooleanType) => true
    case (StringType, StringType) => true
    case (ArrayType(t1), ArrayType(t2)) => canAssignTypes(t1, t2)
    case (ObjectType(o1), ObjectType(o2)) => o1 == o2 || o1 == "null" || o2 == "null"
    case (GenericType, _) => true
    case _ => false
  }

}

protected[graphprog] object Typer {

  def typeOfValue(v: Value): Type = v match {
    case ErrorConstant => ErrorType
    case UnitConstant => UnitType
    case IntArray(_, _) => ArrayType(IntType)
    case IntConstant(_) => IntType
    case BooleanConstant(_) => BooleanType
    case StringConstant(_) => StringType
    case Object(_, t, _) => ObjectType(t)
    case Null => ObjectType("null")
  }

  def typeOfInputs(inputs: List[(String, Value)]): List[(String, Type)] = inputs.map{ t => (t._1, typeOfValue(t._2)) }

}

/*protected[graphprog] class GraphvizHelper {

  protected[graphprog] def toGraphvizString(stmts: List[Stmt]): String = {
    import scala.collection.mutable.ListBuffer
    var defines = new ListBuffer[(String, String)]
    var uuidCounter = 0
    def name(oldName: String): String = {
      def uuid: String = {
	val s = uuidCounter.toString
	uuidCounter += 1
	s
      }
      var newName = "\"" + oldName + "_" + uuid + "\""
      defines += ((newName, oldName))
      newName
    }
    def arrow(top: String, bottom: String): String = top + " -> " + bottom
    def arrows(top: String, bottoms: String*): String = iterableToString(bottoms, "\n", (s: String) => arrow(top, s))
    def valueToGraphviz(v: Value): String = v match {
      case ErrorConstant => name("Error")
      case AssumeFailed => name("Assume Failed")
      case AssertFailed => name("Assert Failed")
      case BreakHit => name("Break Hit")
      case UnitConstant => name("()")
      case IntArray(_, array) => arrows(name("IntArray"), array map { n => name(n.toString) }: _*)
      case IntConstant(n) => name(n.toString)
      case BooleanConstant(b) => name(b.toString)
      case StringConstant(s) => name(s)
      case Object(id, t, m) => arrows(name(t + " " + id.toString), m.toList map { kv => name("." + kv._1 + " = " + kv._2) }: _*)
      case Null => name("null")
    }
    def exprToGraphviz(e: Expr): String = e match {
      case v: Value => valueToGraphviz(v)
      case h: Hole => holeToGraphviz(h)
      case Var(v) => arrow(name("Var"), name(v))
      case IntArrayAccess(a, index) => arrows(name("IntArrayAccess"), exprToGraphviz(a), exprToGraphviz(index)) 
      case FieldAccess(obj, field) => arrows(name("FieldAccess"), exprToGraphviz(obj), name(field))
      case ArrayLength(e) => arrow(name("ArrayLength"), exprToGraphviz(e))
      case ObjectID(id) => name("Object " + id)
      case ArrayID(id) => name("Array " + id)
      case Call(fn, args) => arrows(name("Call"), name(fn), arrows("Args", args map exprToGraphviz: _*))
      case In(varname, range) => arrows(name("Range"), exprToGraphviz(varname), exprToGraphviz(range))
      case To(min, max) => arrows(name("To"), exprToGraphviz(min), exprToGraphviz(max))
      case Until(min, max) => arrows(name("Until"), exprToGraphviz(min), exprToGraphviz(max))
      case EQ(lhs, rhs) => arrows(name("="), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case NE(lhs, rhs) => arrows(name("!="), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case LT(lhs, rhs) => arrows(name("<"), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case LE(lhs, rhs) => arrows(name("<="), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case GT(lhs, rhs) => arrows(name(">"), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case GE(lhs, rhs) => arrows(name(">="), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case And(lhs, rhs) => arrows(name("&&"), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case Or(lhs, rhs) => arrows(name("||"), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case Not(e) => "!(" + arrow(name("!"), exprToGraphviz(e))
      case Plus(lhs, rhs) => arrows(name("+"), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case Minus(lhs, rhs) => arrows(name("-"), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case Times(lhs, rhs) => arrows(name("*"), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case Div(lhs, rhs) => arrows(name("/"), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case LiteralExpr(e) => arrow(name("LiteralExpr"), exprToGraphviz(e))
    }
    def actionToGraphviz(a: Action): String = a match {
      case e: Expr => exprToGraphviz(e)
      case Assign(lhs, rhs) => arrows(name(":="), exprToGraphviz(lhs), exprToGraphviz(rhs))
      case Assume(c) => arrow(name("Assume"), exprToGraphviz(c))
      case Assert(c) => arrow(name("Assert"), exprToGraphviz(c))
      case Conditional(c, body) => arrows(name("Conditional"), exprToGraphviz(c), stmtsToGraphviz(body))
      case Iterate(iterations) => arrows(name("Iterate"), iterations map { iteration => arrows(name("Iteration"), actionToGraphviz(iteration._1), stmtsToGraphviz(iteration._2)) }: _*)
      case Break => name("Break")
      case Println(s) => arrow(name("Println"), valueToGraphviz(s))
      case LiteralAction(a) => arrow(name("LiteralAction"), actionToGraphviz(a))
      case UnorderedStmts(s) => arrows("UnorderedStmts", s map { s => stmtToGraphviz(s) }: _*)
      case Snapshot(m) => name("Snapshot")
    }
    def holeToGraphviz(h: Hole): String = h match {
      case ExprEvidenceHole(evidence) => arrows(name("EvidenceHole"), evidence map { t => actionToGraphviz(t._1) }: _*)
      case StmtEvidenceHole(evidence) => arrows(name("EvidenceHole"), evidence map { t => actionToGraphviz(t._1) }: _*)
      case PossibilitiesHole(possibilities) => arrows(name("PossibilitiesHole"), possibilities map stmtToGraphviz: _*)
      case _: Unseen => name("?")
    }
    def stmtToGraphviz(s: Stmt): String = s match {
      case a: Action => actionToGraphviz(a)
      case h: Hole => holeToGraphviz(h)
      case If(condition, thenBranch, elseIfPaths, elseBranch) => arrows(name("If"), ((((condition, thenBranch) :: elseIfPaths) map { (b: (Expr, List[Stmt])) => arrows(name("Branch"), exprToGraphviz(b._1), stmtsToGraphviz(b._2)) }) :+ arrow(name("else"), stmtsToGraphviz(elseBranch))): _*)
      case Loop(condition, body) => arrows(name("Loop"), stmtToGraphviz(condition), stmtsToGraphviz(body))
    }
    def stmtsToGraphviz(stmts: List[Stmt]): String = stmts match {
      case Nil => ""
      case s :: Nil => stmtToGraphviz(s)
      case x :: xs => arrows(name("StmtBlock"), stmts map stmtToGraphviz: _*)
    }
    val main = stmtsToGraphviz(stmts)
    val labels = iterableToString(defines, "\n ", (t: (String, String)) => t._1 + " [label=\"" + t._2 + "\"]", " ")
    "digraph G {" + ("\n" + main).replaceAll("\n", "\n ") + "\n" + labels + "\n}"
  }

}*/

object ASTUtils {

  import scala.collection.mutable.{ Set => MSet }

  protected[graphprog] def stringOfPrimitive(p: Primitive): String = p match {
    case IntConstant(n) => n.toString
    case BooleanConstant(b) => b.toString
    case StringConstant(s) => "\"" + s + "\""
  }

  protected[graphprog] def isErrorOrFailure(v: Value): Boolean = v.isInstanceOf[IsErrorOrFailure]

  /**
   * Checks whether two values are equal.
   * Note that we create copies of objects whenever we clone memory,
   * so we must compare them by their ids, not with ==, and we must
   * compare arrays deeply.
   * Also note that the set of seen objects (used to prevent
   * infinite recursion) only stores whether we've started to compare
   * two objects, not what the result is.  So be sure not to reuse it
   * when you care about the result.  We only reuse it since we abort
   * whenever we hit a false.
   */
  protected[graphprog] def areEqual(v1: Value, v2: Value, checkFields: Boolean, checkArrays: Boolean, seenObjectIDs: MSet[(Int, Int)] = MSet[(Int, Int)]()): Boolean = (v1, v2) match {
    case (Object(id1, _, f1), Object(id2, _, f2)) => id1 == id2 && (!checkFields || seenObjectIDs.contains((id1, id2)) || mapsAreEqual(f1, f2, (x: Value, y: Value) => areEqual(x, y, checkFields, checkArrays, seenObjectIDs += ((id1, id2)))))
    case (IntArray(id1, a1), IntArray(id2, a2)) => id1 == id2 && (!checkArrays || (a1.length == a2.length && a1.toList == a2.toList))
    case (_, _) => v1 == v2
  }

  private def mapsAreEqual[T1, T2](m1: scala.collection.Map[T1, T2], m2: scala.collection.Map[T1, T2], eq: (T2, T2) => Boolean): Boolean = m1.size == m2.size && m1.forall{ kv => m2.contains(kv._1) && eq(kv._2, m2(kv._1)) }

  protected[graphprog] def memoriesAreEqual(m1: Memory, m2: Memory, seenObjectIDs: MSet[(Int, Int)] = MSet[(Int, Int)]()): Boolean = {
    m1.mem.size == m2.mem.size && m1.mem.zip(m2.mem).forall{ case (m1, m2) => mapsAreEqual(m1, m2, (x: Value, y: Value) => areEqual(x, y, true, true, seenObjectIDs)) }
  }

  protected[graphprog] def areEquivalent(v1: Value, v2: Value, m1: Memory, m2: Memory): Boolean = {
    val seenObjectIDs = MSet[(Int, Int)]()  // Reuse the set of seen objects for efficiency
    areEqual(v1, v2, true, true, seenObjectIDs) && memoriesAreEqual(m1, m2, seenObjectIDs)
  }

  protected[graphprog] def getParents(code: List[Stmt]): Map[Stmt, Option[Stmt]] = {
    def getParentsForStmts(code: List[Stmt], parent: Option[Stmt], acc: Map[Stmt, Option[Stmt]]): Map[Stmt, Option[Stmt]] = {
      def getParentsForStmt(cur: Stmt, parent: Option[Stmt], acc: Map[Stmt, Option[Stmt]]): Map[Stmt, Option[Stmt]] = (cur match {
	case If(c, t, ei, e) => getParentsForStmts(e, Some(cur), getParentsForStmts(t, Some(cur), getParentsForStmt(c, Some(cur), acc)))  // Doesn't work with else ifs
	case Loop(c, b) => getParentsForStmts(b, Some(cur), getParentsForStmt(c, Some(cur), acc))
	case UnorderedStmts(s) => getParentsForStmts(s, Some(cur), acc)
	case _ => acc
      }) + (cur -> parent)
      code.foldLeft(acc){ (acc, cur) => getParentsForStmt(cur, parent, acc) }
    }
    getParentsForStmts(code, None, Map.empty) 
  }

  protected[graphprog] def diffMemories(memory: Memory, newMemory: Memory): (Map[String, Value], Map[(Int, String), Value], Map[(Int, Int), Int]) = {
    // TODO-bug: I should really track all assigns here.  If we execute an assignment that assigns to the current value, I don't currently catch that.
    val oldKeySet = memory.keys.toSet
    val (oldObjectMap, oldArrayMap) = memory.getObjectsAndArrays()
    val oldObjectIDs = oldObjectMap.keys.toSet
    val oldArrayIDs = oldArrayMap.keys.toSet
    val newKeySet = newMemory.keys.toSet
    val (newObjectMap, newArrayMap) = newMemory.getObjectsAndArrays()
    val newObjectIDs = newObjectMap.keys.toSet
    val newArrayIDs = newArrayMap.keys.toSet
    val newVars = newKeySet diff oldKeySet map { key => (key, newMemory(key)) }
    val modifiedVars = newKeySet.intersect(oldKeySet).collect{ case n: String if !areEqual(memory(n), newMemory(n), false, false) => (n, newMemory(n)) }
    val modifiedObjects = newObjectIDs intersect oldObjectIDs flatMap { id => {
      val oldFields = oldObjectMap(id).fields
      val newFields = newObjectMap(id).fields
      assert(newFields.keys.toSet == oldFields.keys.toSet)
      oldFields.keys flatMap { field => {
	val oldValue = oldFields(field)
	val newValue = newFields(field)
	if (areEqual(oldValue, newValue, false, false))
	  Nil
	else
	  List(((id, field), newValue))
      }}
    }}
    val modifiedArrays = newArrayIDs intersect oldArrayIDs flatMap { id => {
      val oldArray = oldArrayMap(id).array
      val newArray = newArrayMap(id).array
      assert(newArray.size == oldArray.size)
      oldArray.zip(newArray).zipWithIndex collect { case ((o, n), i) if o != n => ((id, i), n) }
    }}
    ((newVars ++ modifiedVars).toMap, modifiedObjects.toMap, modifiedArrays.toMap)
  }

  // blockMarker stores (first stmt in block, first stmt after block), which has already determined to be legal.  If the two statements are the same, the block is empty.
  protected[graphprog] def addBlock(code: List[Stmt], blockMarker: (Option[Stmt], Option[Stmt]), blockMaker: List[Stmt] => Stmt): List[Stmt] = blockMarker._1 match {
    case Some(firstInBlock) =>
      var replaced = false
      def replaceStmt(s: Stmt) = s match {
	case If(c, b, ei, e) => If(c, replaceStmts(b), ei map { p => (p._1, replaceStmts(p._2)) }, replaceStmts(e))
	case Loop(c, b) => Loop(c, replaceStmts(b))
	case UnorderedStmts(s) => UnorderedStmts(replaceStmts(s))
	case _ => s
      }
      def replaceStmts(ss: List[Stmt]): List[Stmt] = {
	val firstIndex = ss indexWhere { _ eq firstInBlock }
	if (firstIndex == -1)
	  return ss map replaceStmt
	replaced = true
	val (pre, rest) = ss splitAt firstIndex
	blockMarker._2 match {
	  case Some(firstAfterBlock) if firstInBlock eq firstAfterBlock => pre ++ (blockMaker(Nil) :: rest)
	  case Some(firstAfterBlock) if ss exists { _ eq firstAfterBlock } =>
	    val afterIndex = ss indexWhere { _ eq firstAfterBlock }
	    val (mid, post) = rest splitAt (afterIndex - firstIndex)
	    pre ++ (blockMaker(mid) :: post)
	  case _ => pre :+ blockMaker(rest)
	}
      }
      val newCode = replaceStmts(code)
      assert(replaced)
      newCode
    case None => code :+ blockMaker(Nil)
  }

  // If the parameter is a condition, gets the statement that owns it.
  // The call to getParents is inefficient, but who cares.
  protected[graphprog] def getOwningStmt(code: List[Stmt], s: Stmt): Stmt = getParents(code)(s) match {
    case Some(p) => p match {
      case If(c, _, _, _) if c eq s => p
      case Loop(c, _) if c eq s => p
      case _ => s
    }
    case None => s
  }

  protected[graphprog] def copyBinaryOp(op: BinaryOp, newLeft: Expr, newRight: Expr): BinaryOp = op match {
    case EQ(_, _) => EQ(newLeft, newRight)
    case NE(_, _) => NE(newLeft, newRight)
    case LT(_, _) => LT(newLeft, newRight)
    case LE(_, _) => LE(newLeft, newRight)
    case GT(_, _) => GT(newLeft, newRight)
    case GE(_, _) => GE(newLeft, newRight)
    case And(_, _) => And(newLeft, newRight)
    case Or(_, _) => Or(newLeft, newRight)
    case Plus(_, _) => Plus(newLeft, newRight)
    case Minus(_, _) => Minus(newLeft, newRight)
    case Times(_, _) => Times(newLeft, newRight)
    case Div(_, _) => Div(newLeft, newRight)
  }

  protected[graphprog] def copyRange(r: Range, newMin: Expr, newMax: Expr): Range = r match {
    case To(_, _) => To(newMin, newMax)
    case Until(_, _) => Until(newMin, newMax)
  }

}
