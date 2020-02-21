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
            argList = argList :+ arg.name
          }
          val c = Symbol.fresh("c")
          funDefList = funDefList:+ C.FunDef(f.name, c, argList, tail(f.body, c))
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

      case S.While(condi, lbody, body) =>
        val loop = Symbol.fresh("loop")
        val d = Symbol.fresh("d")
        val loop_d = Symbol.fresh("d")
        C.LetC(Seq(C.CntDef(loop, Seq(loop_d),
          tempLetC("c", Seq(), nonTail(body)(ctx))(c1 =>
            tempLetC("ct", Seq(), tail(lbody, loop))(ct =>
              cond(condi, ct, c1))))),
                C.LetL(d, UnitLit, C.AppC(loop, Seq(d))))


      case S.If(S.Prim(op:MiniScalaTestPrimitive, args), tB, eB) =>
        //print("!!")
        var r = Symbol.fresh("r")
        tempLetC("C", Seq(r), ctx(r))(c =>
          tempLetC("ct", Seq(), tail(tB, c))(ctb =>
            tempLetC("cf", Seq(), tail(eB, c))(ceb =>
              nonTail_*(args)(vs =>
                //If(cond: TestPrimitive, args: Seq[Name], thenC: Name, elseC: Name)
                C.If(op, vs, ctb, ceb)))))

      case S.If(condi, tB, eB) =>
        var r = Symbol.fresh("r")
        tempLetC("C", Seq(r), ctx(r))(c =>
          tempLetC("ct", Seq(), tail(tB, c))(ctb =>
            tempLetC("cf", Seq(), tail(eB, c))(ceb => 
              cond(condi, ctb, ceb))))


      //Prim(op: Primitive, args: List[Tree])
      //logical
      case cond @ S.Prim(op:MiniScalaTestPrimitive, _) =>
        nonTail(S.If(cond, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx)

      case S.Prim(op:MiniScalaValuePrimitive, args) =>
        val sym = Symbol.fresh("v")
        nonTail_*(args)(ags => C.LetP(sym, op, ags, ctx(sym)))

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
      
      case S.Lit(value) =>
        val n = Symbol.fresh("n")
        C.LetL(n, value, C.AppC(c, Seq(n)))

      case S.VarDec(name, _, value, body) =>
        val s = Symbol.fresh("s")
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        C.LetL(s, IntLit(1),
          C.LetP(name, MiniScalaBlockAlloc(BlockTag.Variable.id), Seq(s),
            C.LetL(z, IntLit(0), nonTail(value)(v =>
              C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), tail(body, c)(mut+name))))))

      case S.VarAssign(name, value) =>
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        C.LetL(z, IntLit(0),
          nonTail(value)(v => 
            C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), C.AppC(c, Seq(v)))))

      case S.LetRec(funs, body) =>
        var funDefList = Seq[miniscala.SymbolicCPSTreeModule.FunDef]()
        for (f <- funs) {
          var argList = Seq[miniscala.Symbol]()
          for (arg <- f.args) {
            argList = argList :+ arg.name
          }
          val c = Symbol.fresh("c")
          funDefList = funDefList :+ C.FunDef(f.name, c, argList, tail(f.body, c))
        }
        C.LetF(funDefList, tail(body, c))
      
      case S.App(fun, _, args) =>
        val r = Symbol.fresh("r")
        nonTail(fun)(v =>
          nonTail_*(args)(vs =>
            C.AppF(v, c, vs)))
      
      case S.Ref(name) if !mut(name) =>
        C.AppC(c, Seq(name))
      
      case S.Ref(name) =>
        val z = Symbol.fresh("z")
        val v = Symbol.fresh("v")
        C.LetL(z, IntLit(0), 
          C.LetP(v, MiniScalaBlockGet, Seq(name, z), C.AppC(c, Seq(v))))
      
      case S.While(condi, lbody, body) =>
        val loop = Symbol.fresh("loop")
        val loop_d = Symbol.fresh("d")
        val d = Symbol.fresh("d")
        C.LetC(Seq(C.CntDef(loop, Seq(loop_d),
          tempLetC("c", Seq(), tail(body, c))(c1 =>
            tempLetC("ct", Seq(), tail(lbody, loop))(ct =>
              cond(condi, ct, c1))))),
                C.LetL(d, UnitLit, C.AppC(loop, Seq(d))))

      case cond @ S.Prim(op: MiniScalaTestPrimitive, _) =>
        tail(S.If(cond, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))), c)
      
      case S.Prim(op: MiniScalaValuePrimitive, args) =>
        val sym = Symbol.fresh("v")
        nonTail_*(args)(ags => C.LetP(sym, op, ags, C.AppC(c, Seq(sym))))
      
      case S.If(condi, tB, eB) =>
        val r = Symbol.fresh("r")
        tempLetC("c", Seq(r), C.AppC(c, Seq(r)))(cont =>
          tempLetC("ct", Seq(), tail(tB, c))(ct =>
            tempLetC("cf", Seq(), tail(eB, c))(cf =>
              cond(condi, ct, cf))))


      // TODO: add the missing cases.
    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    def litToCont(l: CMScalaLiteral): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {
      //example
      // [[if(e_1) false else true]]_C ct cf =
      //  [[e_1]]_C cf ct
      case S.If(condE, S.Lit(tl), S.Lit(fl)) => 
        cond(condE, litToCont(tl), litToCont(fl))

      // TODO add missing cases
      case S.If(condE, S.Lit(tl), eB) => 
        tempLetC("ac", Seq(), cond(eB, trueC, falseC))(ac =>
          cond(condE, litToCont(tl), ac))

      case S.If(condE, tl, S.Lit(eB)) =>
        tempLetC("ac", Seq(), cond(tl, trueC, falseC))(ac =>
          cond(condE, ac, litToCont(eB)))

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