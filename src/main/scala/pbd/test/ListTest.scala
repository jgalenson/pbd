package pbd.test

object ListTest {

  import pbd.Controller._
  import pbd.lang.AST._
  import pbd.lang.Printer
  import pbd.synthesis.Synthesis._
  import TestCommon._

  def main(args: Array[String]) {
    val options = parseCommandLine(args)
    testList(options)
  }

  val printHelpers: PartialFunction[String, Value => String] = (s: String) => s match {
    case "Node" => v => "List(" + stringOfList(v.asInstanceOf[Object], printer) + ")"
  }

  val printer = new Printer(printHelpers, false)

  def test(name: String, typ: Type, inputs: List[(String, Value)], generator: Option[Double => List[(String, Value)]], precondition: Option[Map[String, Value] => Boolean], postcondition: Option[(Map[String, Value], Map[String, Value], Value) => Boolean], functions: Map[String, Program], objectTypes: Map[String, List[(String, Type)]], options: Options) {
    try {
      val result = synthesize(inputs, makeSynthesizer(name, typ, pbd.lang.Typer.typeOfInputs(inputs), functions, objectTypes, printHelpers, generator, precondition, postcondition, listComparator) _, functions, objectTypes, listComparator, listFieldLayout, listLayout, options)
      println("Result:\n" + printer.stringOfProgram(result))
    } catch {
      case e: Throwable => e.printStackTrace
    }
  }

  private def testList(options: Options) {

    def revListPostcondition(args: Map[String, Value], resMap: Map[String, Value], rv: Value): Boolean = {
      val argList = args("list")
      val resList = rv
      listToList(resList) == listToList(argList).map{ _.reverse }
    }

    val listMaker = new ListMaker
    test("revList", UnitType, List(("list" -> listMaker.makeList(1))), None, None, Some(revListPostcondition), Map.empty, listTypes, options)
  }

}
