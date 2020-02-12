package project1

import java.io._
import org.scalatest._

// Define the stream method
trait TestOutput {
  val out = new ByteArrayOutputStream
  val pOut = new PrintWriter(out, true)
  def stream = pOut
  def emitCode(ast: Exp): Unit

  def code(ast: Exp) = {
    emitCode(ast)
    out.toString.stripLineEnd
  }
}

class StackGeneratorTest extends FunSuite {

  def runner(src: String, gData: Map[Char,Int] = Map()) = new ASMRunner(src, gData)

  // Function Helper for StackASMGenerator
  def testStackASMGenerator(ast: Exp, res: Int) = {
    val gen = new StackASMGenerator with TestOutput

    val code = gen.code(ast)
    val asm = runner(code)

    assert(asm.assemble == 0, "Code generated couldn't be assembled")
    assert(asm.run == res, "Invalid result")
  }

  test("SingleDigit") {
    testStackASMGenerator(Lit(2), 2)
  }

  // TODO more tests
  test("PlusTest1") {
    testStackASMGenerator(Plus(Lit(2), Lit(1)), 3)
  }

  test("PlusTest2") {
    testStackASMGenerator(Plus(Lit(0), Lit(9)), 9)
  }

  test("PlusTest3") {
    testStackASMGenerator(Plus(Lit(0), Lit(0)), 0)
  }

  test("MinusTest1") {
    testStackASMGenerator(Minus(Lit(3), Lit(1)), 2)
  }

  test("MinusTest2") {
    testStackASMGenerator(Minus(Lit(5), Lit(9)), -4)
  }

  test("MinusTest3") {
    testStackASMGenerator(Minus(Lit(0), Lit(0)), 0)
  }

  test("MulTest1") {
    testStackASMGenerator(Times(Lit(0), Lit(9)), 0)
  }

  test("MulTest2") {
    testStackASMGenerator(Times(Lit(5), Lit(7)), 35)
  }

}

class RegGeneratorTest extends FunSuite {

  def runner(src: String, gData: Map[Char,Int] = Map()) = new ASMRunner(src, gData)

  // Function Helper for StackASMGenerator
  def testRegASMGenerator(ast: Exp, res: Int) = {
    val gen = new RegASMGenerator with TestOutput

    val code = gen.code(ast)
    val asm = runner(code)

    assert(asm.assemble == 0, "Code generated couldn't be assembled")
    assert(asm.run == res, "Invalid result")
  }

  test("SingleDigit") {
    testRegASMGenerator(Lit(2), 2)
  }

  // TODO more tests
}
