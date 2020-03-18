package miniscala

import BitTwiddling.bitsToIntMSBF
import miniscala.{ SymbolicCPSTreeModule => H }
import miniscala.{ SymbolicCPSTreeModuleLow => L }

/**
 * Value-representation phase for the CPS language. Translates a tree
 * with high-level values (blocks, integers, booleans, unit) and
 * corresponding primitives to one with low-level values (blocks
 * and integers only) and corresponding primitives.
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 */

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree =
    transform(tree)(Map.empty)

  val unitLit = bitsToIntMSBF(0, 0, 1, 0)
  val optimized = false

  private def transform(tree: H.Tree)
                       (implicit worker: Map[Symbol, (Symbol, Seq[Symbol])])
      : L.Tree = tree match {

    // Literals
    case H.LetL(name, IntLit(value), body) =>
      //print("!!!")
      L.LetL(name, (value << 1) | 1, transform(body)) //LSB of intLit is 1
    case H.LetL(name, CharLit(value), body) =>
      L.LetL(name, (value << 3) | bitsToIntMSBF(1, 1, 0), transform(body)) //LSB of charLit is 110
    case H.LetL(name, UnitLit, body) =>
      L.LetL(name, unitLit, transform(body))
    case H.LetL(name, BooleanLit(value), body) =>
      val boolLit = if (value) bitsToIntMSBF(1, 1, 0, 1, 0)
                    else bitsToIntMSBF(0, 1, 0, 1, 0) //LSB of boolLit is 1010
      L.LetL(name, boolLit, transform(body))

    // TODO: Add missing literals

    // *************** Primitives ***********************
    // Make sure you implement all possible primitives
    // (defined in MiniScalaPrimitives.scala)
    //
    // Integer primitives
    case H.LetP(name, MiniScalaIntAdd, args, body) =>
      tempLetP(CPSAdd, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSSub, Seq(r, c1), transform(body))
        } 
      }
    case H.LetP(name, MiniScalaIntSub, args, body) =>
      tempLetP(CPSSub, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSAdd, Seq(r, c1), transform(body)) 
        }
      }
    case H.LetP(name, MiniScalaIntMul, Seq(n, m), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(n, c1)) { nm1 =>
          tempLetP(CPSArithShiftR, Seq(m, c1)) { mar1 => 
            tempLetP(CPSMul, Seq(nm1, mar1)) { r =>
              L.LetP(name, CPSAdd, Seq(r, c1), transform(body))
            }
          }
        }
      }
    case H.LetP(name, MiniScalaIntDiv, Seq(n, m), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(n, c1)) {nm1 =>
          tempLetP(CPSArithShiftR, Seq(m, c1)) {mar1 => 
            tempLetP(CPSDiv, Seq(nm1, mar1)) { r =>
              L.LetP(name, CPSAdd, Seq(r, c1), transform(body))
            }
          }
        }
      }
    case H.LetP(name, MiniScalaIntMod, Seq(n,m), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(n, c1)) { nm1 => 
          tempLetP(CPSSub, Seq(m, c1)) { mm1 =>
            tempLetP(CPSMod, Seq(nm1, mm1)) { r =>
              L.LetP(name, CPSAdd, Seq(r, c1), transform(body))
            }
          }
        }
      }
    case H.LetP(name, MiniScalaIntArithShiftLeft, Seq(n, m), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(n, c1)) { nm1 =>
          tempLetP(CPSArithShiftR, Seq(m, c1)) { mar1 =>
            tempLetP(CPSArithShiftL, Seq(nm1, mar1)) { r =>
              L.LetP(name, CPSAdd, Seq(r, c1), transform(body))
            }
          }
        }
      }
    case H.LetP(name, MiniScalaIntArithShiftRight, Seq(n, m), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(n, c1)) { nm1 =>
          tempLetP(CPSArithShiftR, Seq(m, c1)) { mar1 =>
            tempLetP(CPSArithShiftR, Seq(nm1, mar1)) { r =>
              L.LetP(name, CPSAdd, Seq(r, c1), transform(body))
            }
          }
        }
      }
    case H.LetP(name, MiniScalaIntBitwiseAnd, Seq(n, m), body) =>
      L.LetP(name, CPSAnd, Seq(n, m), transform(body))
    case H.LetP(name, MiniScalaIntBitwiseOr, Seq(n, m), body) =>
      L.LetP(name, CPSOr, Seq(n, m), transform(body))
    case H.LetP(name, MiniScalaIntBitwiseXOr, Seq(n, m), body) =>
      tempLetP(CPSXOr, Seq(n, m)) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSAdd, Seq(r, c1), transform(body))
        }
      }

    // TODO: Add missing integer primitives

    // Block primitives
    // TODO: Add block primitives
    case H.LetP(name, MiniScalaBlockAlloc(k), Seq(n1), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(n1, c1)) { t1 =>
          L.LetP(name, CPSBlockAlloc(k), Seq(t1), transform(body))
        }
      }
    case H.LetP(name, MiniScalaBlockTag, args, body) => //tag n1
      tempLetL(1) { c1 =>
        tempLetP(CPSBlockTag, args) { t1 => 
          tempLetP(CPSArithShiftL, Seq(t1, c1)) {t2 =>
            L.LetP(name, CPSAdd, Seq(t2, c1), transform(body))
          }
        }
      }
    case H.LetP(name, MiniScalaBlockGet, Seq(blockv, i), body) => //ith block
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(i, c1)) { iar1 =>
          L.LetP(name, CPSBlockGet, Seq(blockv, iar1), transform(body))
        }
      }
    case H.LetP(name, MiniScalaBlockSet, Seq(v, i, o), body) => //set ith block to o
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(i, c1)) { i_ut =>
          tempLetP(CPSBlockSet, Seq(v, i_ut, o)) { set =>
            L.LetL(name, unitLit, transform(body))
          }
        }
      }
    case H.LetP(name, MiniScalaBlockLength, blockv, body) => //get length of blockv
      tempLetL(1) { c1 =>
        tempLetP(CPSBlockLength, blockv) { length =>
          tempLetP(CPSArithShiftL, Seq(length, c1)) { t1 =>
            L.LetP(name, CPSAdd, Seq(t1, c1), transform(body))
          }
        }
      }

    // Conversion primitives int->char/char->int
    // TODO
    case H.LetP(name, MiniScalaCharToInt, Seq(n1), body) =>
      tempLetL(2) { c2 =>
        L.LetP(name, CPSArithShiftR, Seq(n1, c2), transform(body))
      }

    case H.LetP(name, MiniScalaIntToChar, Seq(n1), body) =>
      tempLetL(2) { c2 =>
        tempLetP(CPSArithShiftL, Seq(n1, c2)) { t1 =>
          L.LetP(name, CPSAdd, Seq(t1, c2), transform(body))
        }
      }

    // IO primitives
    // TODO
    case H.LetP(name, MiniScalaByteRead, _, body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSByteRead, Seq()) { t1 =>
          tempLetP(CPSArithShiftL, Seq(t1, c1)) { t2 =>
            L.LetP(name, CPSAdd, Seq(t2, c1), transform(body))
          }
        }
      }
    
    case H.LetP(name, MiniScalaByteWrite, Seq(v), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(v, c1)) { var1 => 
          tempLetP(CPSByteWrite, Seq(var1)) { _ =>
            L.LetL(name, unitLit, transform(body))
          }
        }
      }

    // Other primitives
    // TODO
    case H.LetP(name, MiniScalaId, args, body) =>
      L.LetP(name, CPSId, args, transform(body))

    // Continuations nodes (LetC, AppC)
    // TODO
    case H.LetC(conts, body) =>
      var cntList = Seq[L.CntDef]()
      for (c <- conts) {
        cntList = cntList :+ L.CntDef(c.name, c.args, transform(c.body))
      }
      L.LetC(cntList, transform(body))

    case H.AppC(cont, args) =>
      L.AppC(cont, args)
    // Functions nodes (LetF, AppF)
    // TODO
    case H.LetF(funs, body) =>
      var workers = Seq[L.FunDef]()
      val funNames = funs map(f => f.name)
      val wkrfv = funs map(f => (Symbol.fresh(s"${f.name}_wrkr"), freeVariables(f)(Map.empty).toSeq))
      //make workers
      (funs zip wkrfv).foreach {
        case ((fun @ H.FunDef(name, retC, args, body)), (w_name, w_fv)) =>
          var FVs = Seq[Symbol]()
          val env = Symbol.fresh(s"${name}_env")
          for (v <- w_fv) { FVs = FVs :+ Symbol.fresh(s"${v}") }
          val inner = transform(fun.body) subst Substitution(name +: w_fv, env +: FVs)
          val worker_body = wrap(FVs.zipWithIndex, inner) {
            case((free_v, i), inner) =>
              tempLetL(i + 1) { i =>
                L.LetP(free_v, CPSBlockGet, Seq(env, i), inner)
              }
          }
          workers = workers :+ L.FunDef(w_name, retC, env +: args, worker_body)
      }
      //blocksets
      val zipped = funNames zip wkrfv
      val inner = transform(body)
      val blockSets = wrap(zipped, inner) {
        case ((fName, (w_name, w_fv)), inner) =>
          //each blocksets
          tempLetL(0) { zero =>
            tempLetP(CPSBlockSet, Seq(fName, zero, w_name)) { _ =>
              wrap(w_fv.zipWithIndex, inner) {
                case ((fv, i), inner) =>
                  tempLetL(i + 1) { i =>
                    tempLetP(CPSBlockSet, Seq(fName, i, fv)) { _ =>  inner }
                  }
              }
            }
          }
      }
      val fbody = wrap(zipped, blockSets) {
        case ((fName, (_, w_fv)), inner) =>
          tempLetL(w_fv.length + 1) { size =>
            L.LetP(fName, CPSBlockAlloc(BlockTag.Function.id), Seq(size), inner)
          }
      }
      L.LetF(workers, fbody)

    case H.AppF(fun, retC, args) =>
      tempLetL(0) { zero =>
        tempLetP(CPSBlockGet, Seq(fun, zero)) { f =>
          L.AppF(f, retC, fun +: args)
        }
      }

    // ********************* Conditionnals ***********************
    // Type tests
    case H.If(MiniScalaBlockP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(0, 0), thenC, elseC)
    case H.If(MiniScalaIntP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1), thenC, elseC)
    case H.If(MiniScalaCharP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1,1,0), thenC, elseC)
    case H.If(MiniScalaBoolP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1,0,1,0), thenC, elseC)
    case H.If(MiniScalaUnitP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(0,0,1,0), thenC, elseC)
    // TODO: add missing cases

    // Test primitives (<, >, ==, ...)
    // TODO
    case H.If(MiniScalaIntLt, args, thenC, elseC) =>
      L.If(CPSLt, args, thenC, elseC)
    case H.If(MiniScalaIntLe, args, thenC, elseC) =>
      L.If(CPSLe, args, thenC, elseC)
    case H.If(MiniScalaEq, args, thenC, elseC) =>
      L.If(CPSEq, args, thenC, elseC)
    case H.If(MiniScalaNe, args, thenC, elseC) =>
      L.If(CPSNe, args, thenC, elseC)
    case H.If(MiniScalaIntGe, args, thenC, elseC) =>
      L.If(CPSGe, args, thenC, elseC)
    case H.If(MiniScalaIntGt, args, thenC, elseC) =>
      L.If(CPSGt, args, thenC, elseC)

    // Halt case
    // TODO
    case H.Halt(arg) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(arg, c1)) {t1 =>
          L.Halt(t1)
        }
      }
  }

  /*
   * Auxilary function.
   *
   * Example:
   *  // assuming we have a function with symbol f and the return continuation is rc:
   *
   *  val names = Seq("first", "second")
   *  val values = Seq(42, 112)
   *  val inner = L.AppF(f, rc, names)
   *  val res = wrap(names zip values , inner) {
   *    case ((n, v), inner) => L.LetL(n, v, inner)
   *  }
   *
   *  // res is going to be the following L.Tree
   *  L.LetL("first", 42,
   *    L.LetL("second", 112,
   *      L.AppF(f, rc, Seq("first", "second"))
   *    )
   *  )
   */
  private def wrap[T](args: Seq[T], inner: L.Tree)(createLayer: (T, L.Tree) => L.Tree) = {
    def addLayers(args: Seq[T]): L.Tree = args match {
      case h +: t => createLayer(h, addLayers(t))
      case _ => inner
    }
    addLayers(args)
  }

  private def freeVariables(tree: H.Tree)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] = tree match {
    case H.LetL(name, _, body) =>
      freeVariables(body) - name
    case H.LetP(name, _, args, body) =>
      freeVariables(body) - name ++ args
    // TODO: add missing cases
    case H.LetC(cnts, body) =>
      var cfv = Set[Symbol]()
      cnts.foreach {
        case c @ H.CntDef(name, args, body) =>
          cfv = cfv ++ (freeVariables(c) -- args.toSet)
      }
      freeVariables(body) ++ cfv
    case H.LetF(funs, body) =>
      val funNames = funs map (f => f.name)
      var fvs = Set[Symbol]()
      funs.foreach{
        case f @ H.FunDef(name, retC, args, body) =>
          fvs = fvs ++ (freeVariables(f) -- args.toSet)
      }
      freeVariables(body) ++ fvs -- funNames
    case H.AppC(_, args) =>
      args.toSet
    case H.AppF(fun, _, args) =>
      Set(fun) ++ args.toSet
    case H.If(_, args, _, _) =>
      args.toSet
  }

  private def freeVariables(cnt: H.CntDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(cnt.body) -- cnt.args

  private def freeVariables(fun: H.FunDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(fun.body) - fun.name -- fun.args

  // Tree builders

  /**
   * Call body with a fresh name, and wraps its resulting tree in one
   * that binds the fresh name to the given literal value.
   */
  private def tempLetL(v: Int)(body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetL(tempSym, v, body(tempSym))
  }

  /**
   * Call body with a fresh name, and wraps its resulting tree in one
   * that binds the fresh name to the result of applying the given
   * primitive to the given arguments.
   */
  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Name])
                      (body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }

  /**
   * Generate an If tree to check whether the least-significant bits
   * of the value bound to the given name are equal to those passed as
   * argument. The generated If tree will apply continuation tC if it
   * is the case, and eC otherwise. The bits should be ordered with
   * the most-significant one first (e.g. the list (1,1,0) represents
   * the decimal value 6).
   */
  private def ifEqLSB(arg: L.Name, bits: Seq[Int], tC: L.Name, eC: L.Name)
      : L.Tree =
    tempLetL(bitsToIntMSBF(bits map { b => 1 } : _*)) { mask =>
      tempLetP(CPSAnd, Seq(arg, mask)) { masked =>
        tempLetL(bitsToIntMSBF(bits : _*)) { value =>
          L.If(CPSEq, Seq(masked, value), tC, eC) } } }
}
