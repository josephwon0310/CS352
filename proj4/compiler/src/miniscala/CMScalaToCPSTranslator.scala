package miniscala

import miniscala.{ SymbolicCMScalaTreeModule => S }
import miniscala.{ SymbolicCPSTreeModule => C }

object CMScalaToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    nonTail(tree){_ =>
      val z = Symbol.fresh("c0")
      C.LetL(z, IntLit(0), C.Halt(z))
    }(Set.empty)
  }

  private def nonTail(tree: S.Tree)(ctx: Symbol=>C.Tree)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {
      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
            C.LetP(name, MiniScalaId, Seq(v), nonTail(body)(ctx)))

      // TODO: complete the following cases and add the missing ones.

      case S.Lit(value) =>
        val n = Symbol.fresh("n")
        C.LetL(n, value, ctx(n))
      
      case S.VarDec(name, _, value, body) =>
        val s = Symbol.fresh("s")
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        C.LetL(s, IntLit(1), 
          C.LetP(name, MiniScalaBlockAlloc(BlockTag.Variable.id), Seq(s),
            C.LetL(z, IntLit(0),
            nonTail(value)(v =>
              C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), nonTail(body)(ctx)(mut + name))))))

      case S.VarAssign(name, value) =>
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        C.LetL(z, IntLit(0),
          nonTail(value)(v => 
            C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), ctx(v))))

      case S.LetRec(funs, body) =>
        var funDefList = Seq[miniscala.SymbolicCPSTreeModule.FunDef]()
        for (f <- funs) {
          var argList = Seq[miniscala.Symbol]()
          for (arg <- f.args) {
            argList :+ arg.name
          }
          val c = Symbol.fresh("c")
          funDefList :+ C.FunDef(f.name, c, argList, tail(f.body, c))
        }
        C.LetF(funDefList, nonTail(body)(ctx))

      case S.App(fun, _, args) =>
        val r = Symbol.fresh("r")
        nonTail(fun)(v =>
          nonTail_*(args)(vs =>
            tempLetC("c", Seq(r), ctx(r))(cBody => C.AppF(v, cBody, vs))))

      // Reference of an immutable variable
      case S.Ref(name) if !mut(name) =>
        ctx(name)

      // Reference of an mutable variable
      case S.Ref(name) => // if mut(name) =>
        val z = Symbol.fresh("z")
        val v = Symbol.fresh("v")
        C.LetL(z, IntLit(0), 
          C.LetP(v, MiniScalaBlockGet, Seq(name, z), ctx(v)))

      case S.If(cond @ S.Prim(_, args), tB, eB) if cond.isInstanceOf[S.Prim] =>
        var r = Symbol.fresh("r")
        tempLetC("c", Seq(r), ctx(r))(c =>
          tempLetC("ct", Seq(), nonTail(tB)(v_2 => C.AppC(/*Sym*/, v_2)))(ctb =>
            tempLetC("cf", Seq(), nonTail(eB)(v_3 => C.AppC(/*Sym*/, v_3)))(ceb =>
              nonTail_*(args)(vs =>
                //If(cond: TestPrimitive, args: Seq[Name], thenC: Name, elseC: Name)
                C.If(cond, vs, ctb, ceb)
            ))))

      case S.If(cond, tB, eB) =>
        val r = Symbol.fresh("r")
        val f = Symbol.fresh("f")
        tempLetC("c", Seq(r), ctx(r))(c =>
          tempLetC("ct", Seq(), nonTail(tB)(v_2 => C.AppC(/*Sym*/, v_2)))(ctb =>
            tempLetC("cf", Seq(), nonTail(eB)(v_3 => C.AppC(/*Sym*/, v_3)))(ceb =>
              C.LetL(f, BooleanLit(false),
                    nonTail(cond)(v_1 =>
                              //TODO
                                  C.If()))
            ))))

      //Prim(op: Primitive, args: List[Tree])
      //logical
      case S.Prim(op:MiniScalaTestPrimitive, _) =>
        ???
      case S.Prim(op:MiniScalaValuePrimitive, _) =>
        ???

    }
  }
  
  // nonTail_* takes a sequence of S.Tree, and a continuation that takes a
  // sequence of symbols.  The sequence of symbols in the continuation
  // represents the transformed result of `trees`.  This is particularly useful
  // for the App case in nonTail.
  private def nonTail_*(trees: Seq[S.Tree])(ctx: Seq[Symbol]=>C.Tree)(implicit mut: Set[Symbol]): C.Tree =
    trees match {
      case Seq() => 
        ctx(Seq())
      case t +: ts =>
        nonTail(t)(tSym => nonTail_*(ts)(tSyms => ctx(tSym +: tSyms)))
    }

  private def tail(tree: S.Tree, c: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {
      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
          C.LetP(name, MiniScalaId, Seq(v), tail(body, c)))
      


      // TODO: add the missing cases.
    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    def litToCont(l: CMScalaLiteral): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {
      case S.If(condE, S.Lit(tl), S.Lit(fl)) =>
        cond(condE, litToCont(tl), litToCont(fl))

      // TODO add missing cases

      case S.Prim(p: MiniScalaTestPrimitive, args) =>
        nonTail_*(args)(as => C.If(p, as, trueC, falseC))

      case other =>
        nonTail(other)(o =>
          nonTail(S.Lit(BooleanLit(false)))(n =>
            C.If(MiniScalaNe, Seq(o, n), trueC, falseC)))
    }
  }

  // Helper function for defining a continuation.
  // Example:
  // tempLetC("c", Seq(r), ctx(r))(k => App(f, k, as))
  private def tempLetC(cName: String, args: Seq[C.Name], cBody: C.Tree)
                      (body: C.Name=>C.Tree): C.Tree = {
    val cSym = Symbol.fresh(cName)
    C.LetC(Seq(C.CntDef(cSym, args, cBody)), body(cSym))
  }
}
