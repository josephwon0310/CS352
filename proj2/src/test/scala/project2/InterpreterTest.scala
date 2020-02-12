package project2

import org.scalatest._

class InterpretTest extends FunSuite {
  import Language._

  def testInterpreter(ast: Exp, res: Int) = {
    val interpreter = new StackInterpreter

    assert(res == interpreter.run(ast), "Interpreter does not return the correct value")
  }

  test("arithm") {
    testInterpreter(Lit(-21), -21)
    testInterpreter(Prim("-", Lit(10), Lit(2)), 8)
    testInterpreter(Unary("-", Lit(10)), -10)
  }

  test("let") {
    testInterpreter(Let("x", Lit(10), Ref("x")), 10)
  }

  test("vardec") {
    testInterpreter(VarDec("x", Lit(30), Prim("+", Ref("x"), Lit(20))), 50)
  }

  test("varassign") {
    testInterpreter(VarDec("x", Lit(5), VarAssign("x", Prim("-", Ref("x"), Lit(15)))), -10)
  }

  test("if") {
    testInterpreter(If(Cond(">", Lit(3), Lit(1)), Lit(10), Lit(5)), 10)
    testInterpreter(If(Cond("==", Lit(1), Lit(2)), Lit(1), Lit(2)), 2)
  }

}
