package graphprog.lang

object Compiler {
  import scala.collection.mutable.{ Map => MMap, HashMap => MHashMap, Stack }
  import AST._
  import scala.util.parsing.combinator._

  // TODO: Missing array literals, if/conditional, loop/iterate, arith disambiguation, array length
  private object TraceCompiler extends JavaTokenParsers with PackratParsers {

    override val whiteSpace = """[ \t]+""".r

    def bool = """true|false""".r

    def identifier = """[a-zA-Z][a-zA-Z0-9_]*""".r

    lazy val value: PackratParser[Value] = 
      wholeNumber ^^ { case n => IntConstant(n.toInt) } |
      bool ^^ { case b => BooleanConstant(b.toBoolean) } |
      """null""".r ^^ { case _ => Null } |
      "\"" ~ """[^\"]*""".r ~ "\"" ^^ { case _~s~_ => StringConstant(s.toString) }

    lazy val obj: PackratParser[ObjectID] =
      "ObjectID(" ~ wholeNumber ~ ")" ^^ { case _~id~_ => ObjectID(id.toInt) }

    lazy val lval: PackratParser[LVal] =
      lval ~ "[" ~ expr ~ "]" ^^ { case a~_~i~_ => ArrayAccess(a, i) } |  // TODO-bug: lval here, below, and in length should be expr
      lval ~ "." ~ identifier ^^ { case o~_~f => FieldAccess(o, f) } |
      identifier ^^ { case s => Var(s.toString) }

    lazy val comparison: PackratParser[Comparison] =
      expr ~ "=" ~ expr ^^ { case l~_~r => EQ(l, r) } |
      expr ~ "!" ~ "=" ~ expr ^^ { case l~_~_~r => NE(l, r) } |
      expr ~ "<" ~ expr ^^ { case l~_~r => LT(l, r) } |
      expr ~ "<=" ~ expr ^^ { case l~_~r => LE(l, r) } |
      expr ~ ">" ~ expr ^^ { case l~_~r => GT(l, r) } |
      expr ~ ">=" ~ expr ^^ { case l~_~r => GE(l, r) } |
      expr ~ "&&" ~ expr ^^ { case l~_~r => And(l, r) } |
      expr ~ "||" ~ expr ^^ { case l~_~r => Or(l, r) }

    lazy val not: PackratParser[Not] =
      "!" ~ expr ^^ { case _~e => Not(e) }

    lazy val arithmetic: PackratParser[Arithmetic] =
      expr ~ "+" ~ expr ^^ { case l~_~r => Plus(l, r) } |
      expr ~ "-" ~ expr ^^ { case l~_~r => Minus(l, r) } |
      expr ~ "*" ~ expr ^^ { case l~_~r => Times(l, r) } |
      expr ~ "/" ~ expr ^^ { case l~_~r => Div(l, r) }

    lazy val call: PackratParser[Call] =
      identifier ~ "(" ~ repsep(expr, ",") ~ ")" ^^ { case n~_~a~_ => Call(n, a) }

    lazy val range: PackratParser[Range] = 
      expr ~ "to" ~ expr ^^ { case min~_~max => To(min, max) } |
      expr ~ "until" ~ expr ^^ { case min~_~max => Until(min, max) }

    lazy val in: PackratParser[In] =
      identifier ~ "in" ~ range ^^ { case v~_~r => In(Var(v), r) }

    lazy val length: PackratParser[ArrayLength] =
      identifier ~ "." ~ "length" ^^ { case a~_~_ => ArrayLength(Var(a)) }
    
    lazy val expr: PackratParser[Expr] =
      arithmetic | comparison | not | value | in | range | length | obj | call | lval |  // Order and | not ||| matter here, and value must preceed lval to recognize true/false.
      "(" ~ expr ~ ")" ^^ { case _~e~_ => e }

    lazy val action: PackratParser[Action] =
      lval ~ ":=" ~ expr ^^ { case l~_~r => Assign(l, r) } |
      expr 

    lazy val actionList: PackratParser[List[Action]] =
      repsep(action, "\n")


    lazy val field_def: PackratParser[String] = 
      "field" ~ identifier ~ ":" ~ identifier ^^ { case _ => "a field" }

    lazy val field_list: PackratParser[String] = 
      repsep(field_def, ";") ~ opt(";") ^^ { case _ => "a group of fields"}
      
      
    lazy val class_def: PackratParser[ObjectType] =
      "class" ~ identifier ~"{" ~ repsep(field_list, "\n") ~ "}" ^^ { case _ => ObjectType("") } // MMap.empty[String, Value]) }

    lazy val classList: PackratParser[List[Type]] = 
      repsep(class_def, "\n") ^^ { case _ => List[ObjectType]()}

    def parse(text: String) = parseAll(actionList, text)

    def parseClasses(text: String) = parseAll(classList, text)

  }

  protected[graphprog] def parse(text: String): List[Action] = {
    TraceCompiler.parse(text).get
  }
  protected[graphprog] def parseClasses(text: String): List[Type] = {
    TraceCompiler.parseClasses(text).get
  }

  protected[graphprog] def parseOpt(text: String): Option[List[Action]] = {
    TraceCompiler.parse(text) match {
      case TraceCompiler.Success(r, _) => Some(r)
      case _ => None
    }
  }

}
