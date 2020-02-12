package project2

import org.scalatest._
import java.io.{ByteArrayOutputStream, PrintWriter}

// Define the stream method
trait TestOutput {
  import Language._

  val out = new ByteArrayOutputStream
  val pOut = new PrintWriter(out, true)
  def stream = pOut
  def emitCode(ast: Exp): Unit

  def code(ast: Exp) = {
    emitCode(ast)
    out.toString.stripLineEnd
  }
}

class CompilerTest extends FunSuite {
  import Language._

  def runner(src: String, gData: Map[Char,Int] = Map()) = new ASMRunner(src, gData)

  def testCompiler(ast: Exp, res: Int) = {
    val interpreter = new X86Compiler with TestOutput

    val code = interpreter.code(ast)
    val asm = runner(code)

    assert(asm.assemble == 0, "Code generated couldn't be assembled")
    assert(asm.run == res, "Invalid result")
  }


  test("arithm") {
    testCompiler(Lit(-21), -21)
    testCompiler(Prim("-", Lit(10), Lit(2)), 8)
    testCompiler(Unary("-", Lit(10)), -10)
  }

  test("let") {
    testCompiler(Let("x", Lit(10), Ref("x")), 10) 
  }

  test("vardec") {
    testCompiler(VarDec("x", Lit(30), Prim("+", Ref("x"), Lit(20))), 50) 
  }

  test("varassign") {
    testCompiler(VarDec("x", Lit(5), VarAssign("x", Prim("-", Ref("x"), Lit(15)))), -10)
  }

  test("if") {
    testCompiler(If(Cond(">", Lit(3), Lit(1)), Lit(10), Lit(5)), 10) 
    testCompiler(If(Cond("==", Lit(1), Lit(2)), Lit(1), Lit(2)), 2)
  }
}
