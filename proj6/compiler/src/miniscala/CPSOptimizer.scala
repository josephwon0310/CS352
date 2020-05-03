package miniscala

import scala.collection.mutable.{ Map => MutableMap }

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  def apply(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = (size(simplifiedTree) * 1.5).toInt
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  /* Counts how many times a symbol is encountered as an applied function,
   * and how many as a value
   */
  private case class Count(applied: Int = 0, asValue: Int = 0)

  /* Local state of the optimization
   * Note: To update the state, use the with* methods
   */
  private case class State(
    /* How many times a symbol is encountered in the Tree. Note: The
     * census for the whole program gets calculated once in the
     * beginning, and passed to the initial state.
     */
    census: Map[Name, Count],
    // Name substitution that needs to be applied to the current tree
    subst: Substitution[Name] = Substitution.empty,
    // Names that have a constant value
    lEnv: Map[Name, Literal] = Map.empty,
    // The inverse of lEnv
    lInvEnv: Map[Literal, Name] = Map.empty,
    // A known block mapped to its tag and length
    bEnv: Map[Name, (Literal, Name)] = Map.empty,
    // ((p, args) -> n2) is included in eInvEnv iff n2 == p(args)
    // Note: useful for common-subexpression elimination
    eInvEnv: Map[(ValuePrimitive, Seq[Name]), Name] = Map.empty,
    // Continuations that will be inlined
    cEnv: Map[Name, CntDef] = Map.empty,
    // Functions that will be inlined
    fEnv: Map[Name, FunDef] = Map.empty) {

    // Checks whether a symbol is dead in the current state
    def dead(s: Name): Boolean =
      census get s map (_ == Count(applied = 0, asValue = 0)) getOrElse true
    // Checks whether a symbols is applied exactly once as a function
    // in the current State, and never used as a value
    def appliedOnce(s: Name): Boolean =
      census get s map (_ == Count(applied = 1, asValue = 0)) getOrElse false

    // Addas a substitution to the state
    def withSubst(from: Name, to: Name): State =
      copy(subst = subst + (from -> to))
    // Adds a Seq of substitutions to the state
    def withSubst(from: Seq[Name], to: Seq[Name]): State =
      copy(subst = subst ++ (from zip to))

    // Adds a constant to the State
    def withLit(name: Name, value: Literal) =
      copy(lEnv = lEnv + (name -> value), lInvEnv = lInvEnv + (value -> name))
    // Adds a block to the state
    def withBlock(name: Name, tag: Literal, size: Name) =
      copy(bEnv = bEnv + (name -> (tag, size)))
    // Adds a primitive assignment to the state
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Name]) =
      copy(eInvEnv = eInvEnv + ((prim, args) -> name))
    // Adds an inlinable continuation to the state
    def withCnt(cnt: CntDef) =
      copy(cEnv = cEnv + (cnt.name -> cnt))
    // Adds a Seq of inlinable continuations to the state
    def withCnts(cnts: Seq[CntDef]) =
      (this /: cnts) (_.withCnt(_))
    // Adds an inlinable function to the state
    def withFun(fun: FunDef) =
      copy(fEnv = fEnv + (fun.name -> fun))
    // Adds a Seq of inlinable functions to the state
    def withFuns(funs: Seq[FunDef]) =
      (this /: funs) (_.withFun(_))
    /*
     * The same state, with emply inverse environments.
     * Use this when entering a new FunDef, because assigned Name's may
     * come out of scope during hoisting.
     */
    def withEmptyInvEnvs =
      copy(lInvEnv = Map.empty, eInvEnv = Map.empty)
  }

  // Shrinking optimizations
  private def shrink(tree: Tree): Tree = {
    def shrinkT(tree: Tree)(implicit s: State): Tree = tree match {
      case LetL(n, l, e) =>
          //dead code
          if (s.dead(n))
            shrinkT(e)
          //CSE
          else if (s.lInvEnv.contains(l))
            shrinkT(e.subst(Substitution.apply[Symbol](n, s.lInvEnv(l))))
          else 
            LetL(n, l, shrinkT(e)(s.withLit(n, l)))

      case LetP(n, p, args, e) =>
        //dead code
        if (s.dead(n) && !impure(p))
          shrinkT(e)
        //constant folding + CSE
        else if (!impure(p) && !unstable(p)) {
          if (s.eInvEnv.contains((p, args))) {
            shrinkT(e subst Substitution.apply[Symbol](n, s.eInvEnv((p, args))))
          }
          //constang folding + neutral/absorb
          else if (args.length == 2) {
            //===== check foldable =====
            var foldable = true
            var lits = Seq[Literal]()
            for (a <- args) {
                if(!(s.lEnv.get(a).isDefined)) foldable = false
            }
            // Constant Folding
            if(foldable){
              for (a <- args) {
                lits = lits :+ s.lEnv(a)
              }
              shrinkT(LetL(n, vEvaluator((p, lits)), e))
            }
            //Left neutral/absorb
            else if (s.lEnv.get(args(0)).isDefined) {
              if (leftNeutral.contains((s.lEnv(args(0)), p))) {
                val n_state = s.withSubst(n, args(1))
                shrinkT(e.subst(n_state.subst))(n_state)
              }
              else if (leftAbsorbing.contains((s.lEnv(args(0)), p))) {
                val n_state = s.withSubst(n, args(0))
                shrinkT(e.subst(n_state.subst))(n_state)
              }
              else LetP(n, p, args, shrinkT(e)(s.withExp(n, p, args)))
            }
            //Right neutral/absorb
            else if (s.lEnv.get(args(1)).isDefined) {
              if (rightNeutral.contains((p, s.lEnv(args(1))))) {
                val n_state = s.withSubst(n, args(0))
                shrinkT(e.subst(n_state.subst))(n_state)
              }
              else if (rightAbsorbing.contains((p, s.lEnv(args(1))))) {
                val n_state = s.withSubst(n, args(1))
                shrinkT(e.subst(n_state.subst))(n_state)
              }
              else LetP(n, p, args, shrinkT(e)(s.withExp(n, p, args)))
            }
            //same arg reduce
            else if (args(0) == args(1) && sameArgReduce.isDefinedAt(p)) {
              shrinkT(LetL(n, sameArgReduce(p), e))
            }
            else LetP(n, p, args, shrinkT(e)(s.withExp(n, p, args)))
          }
          else LetP(n, p, args, shrinkT(e)(s.withExp(n, p, args)))
        }

        else LetP(n, p, args, shrinkT(e)(s.withExp(n, p, args)))

      case LetF(funs, body) if funs.exists(fun => s.dead(fun.name)) =>
        var n_funs = Seq[FunDef]()
        var inlinable_funs = Seq[FunDef]()
        funs.foreach {
          case f @ _ =>
            if (!(s.dead(f.name))) n_funs = n_funs :+ f
            if (s.appliedOnce(f.name)) inlinable_funs = inlinable_funs :+ f
        }
        if (n_funs.length > 0)
          LetF(n_funs, shrinkT(body)(s.withFuns(inlinable_funs)))
        else
          shrinkT(body)(s.withFuns(inlinable_funs))

      case LetC(cnts, body) if cnts.exists(cnt => s.dead(cnt.name)) =>
        var n_cnts = Seq[CntDef]()
        var inlinable_cnts = Seq[CntDef]()
        cnts.foreach {
          case c @ _ =>
            if (!(s.dead(c.name))) n_cnts = n_cnts :+ c
            if (s.appliedOnce(c.name)) inlinable_cnts = inlinable_cnts :+ c
        }
        if (n_cnts.length > 0)
          LetC(n_cnts, shrinkT(body)(s.withCnts(inlinable_cnts)))
        else
          shrinkT(body)(s.withCnts(inlinable_cnts))

      case If(cond, args, ct, cf) =>
          var lits = Seq[Literal](); //literal for each arg
          var foldable = true
          args.foreach {
            case a @ _ =>
              lits = lits :+ s.lEnv(a)
              if(!(s.lEnv.get(a).isDefined)) foldable = false
          }
          if (args(0) == args(1)) {
            if (sameArgReduceC(cond)) shrinkT(AppC(ct, Seq[Name]()))
            else shrinkT(AppC(cf, Seq[Name]()))
          }
          else if (foldable) {
            if (cEvaluator.isDefinedAt((cond, lits))) {
              if (cEvaluator(cond, lits)) shrinkT(AppC(ct, Seq[Name]()))
              else shrinkT(AppC(ct, Seq[Name]()))
            }
            else If(cond, args, ct, cf)
          }
          else If(cond, args, ct, cf)

      case _ =>
        // TODO
        tree
    }

    shrinkT(tree)(State(census(tree)))
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = Stream.iterate((0, tree), fibonacci.length) { case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {
        case LetL(n, l, e) => LetL(n, l, inlineT(e)(s.withLit(n, l)))

        case LetP(n, p, args, e) => LetP(n, p, args, inlineT(e)(s.withExp(n, p, args)))

        case LetF(funs, body) =>
          var notdead = Seq[FunDef]()
          var n_funs = Seq[FunDef]()
          var inlinable_funs = Seq[FunDef]()
          funs.foreach {
            case f @ _ =>
              if (!(s.dead(f.name))) notdead = notdead :+ f
          }
          notdead.foreach {
            case f @ _ => n_funs = n_funs :+ FunDef(f.name, f.retC, f.args, inlineT(f.body))
          }
          n_funs.foreach {
            case f @ _ =>
              if (size(f.body) <= funLimit) inlinable_funs = inlinable_funs :+ f
          }
          LetF(n_funs, inlineT(body)(s.withFuns(inlinable_funs)))
          
        case LetC(cnts, body) =>
          var notdead = Seq[CntDef]()
          var n_cnts = Seq[CntDef]()
          var inlinable_cnts = Seq[CntDef]()
          cnts.foreach {
            case c @ _ =>
              if(!(s.dead(c.name))) notdead = notdead :+ c
          }
          notdead.foreach {
            case c @ _ => n_cnts = n_cnts :+ CntDef(c.name, c.args, inlineT(c.body))
          }
          n_cnts.foreach {
            case c @ _ =>
              if (size(c.body) <= cntLimit) inlinable_cnts = inlinable_cnts :+ c
          }
          LetC(n_cnts, inlineT(body)(s.withCnts(n_cnts)))          

        case AppF(funName, retC, args) =>
          if (s.fEnv.contains(funName)) {
            val fun_def = s.fEnv(funName)
            var n_state = s.withSubst(fun_def.retC, retC)
            n_state = n_state.withSubst(fun_def.args, args)
            fun_def.body.subst(n_state.subst)
          }
          else AppF(funName, retC, args)

        case AppC(cName, args) =>
          if (s.cEnv.contains(cName)) {
            val cnt_def = s.cEnv(cName)
            var n_state = s.withSubst(cnt_def.args, args)
            cnt_def.body.subst(n_state.subst)
          }
          else AppC(cName, args)
        case _ =>
          // TODO
          tree
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]()
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(applied = currCount.applied + 1)
      rhs remove symbol foreach addToCensus
    }

    def incValUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(asValue = currCount.asValue + 1)
      rhs remove symbol foreach addToCensus
    }

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetL(_, _, body) =>
        addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUse; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def sameLen(formalArgs: Seq[Name], actualArgs: Seq[Name]): Boolean =
    formalArgs.length == actualArgs.length

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetL(_, _, body) => size(body) + 1
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  // Returns whether a ValuePrimitive has side-effects
  protected val impure: ValuePrimitive => Boolean
  // Returns whether different applications of a ValuePrimivite on the
  // same arguments may yield different results
  protected val unstable: ValuePrimitive => Boolean
  // Extracts the tag from a block allocation primitive
  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  // Returns true for the block tag primitive
  protected val blockTag: ValuePrimitive
  // Returns true for the block length primitive
  protected val blockLength: ValuePrimitive
  // Returns true for the identity primitive
  protected val identity: ValuePrimitive

  // ValuePrimitives with their left-neutral elements
  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-neutral elements
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with their left-absorbing elements
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-absorbing elements
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with the value equal arguments reduce to
  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal]
  // TestPrimitives with the (boolean) value equal arguments reduce to
  protected val sameArgReduceC: TestPrimitive => Boolean
  // An evaluator for ValuePrimitives
  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  // An evaluator for TestPrimitives
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(MiniScalaBlockSet, MiniScalaByteRead, MiniScalaByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    // TODO : done!
    case MiniScalaBlockAlloc(_) => true
    case MiniScalaBlockGet => true
    case MiniScalaByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case MiniScalaBlockAlloc(tag) => IntLit(tag)
  }
  protected val blockTag: ValuePrimitive = MiniScalaBlockTag
  protected val blockLength: ValuePrimitive = MiniScalaBlockLength

  protected val identity: ValuePrimitive = MiniScalaId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((IntLit(0), MiniScalaIntAdd), 
        (IntLit(1), MiniScalaIntMul), 
        (IntLit(~0), MiniScalaIntBitwiseAnd), 
        (IntLit(0), MiniScalaIntBitwiseOr), 
        (IntLit(0), MiniScalaIntBitwiseXOr)) // TODO
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((MiniScalaIntAdd, IntLit(0)), 
        (MiniScalaIntSub, IntLit(0)), 
        (MiniScalaIntMul, IntLit(1)), 
        (MiniScalaIntDiv, IntLit(1)),
        (MiniScalaIntArithShiftLeft, IntLit(0)), 
        (MiniScalaIntArithShiftRight, IntLit(0)),
        (MiniScalaIntBitwiseAnd, IntLit(~0)), 
        (MiniScalaIntBitwiseOr, IntLit(0)), 
        (MiniScalaIntBitwiseXOr, IntLit(0))) // TODO

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((IntLit(0), MiniScalaIntMul), 
        (IntLit(0), MiniScalaIntBitwiseAnd), 
        (IntLit(~0), MiniScalaIntBitwiseOr),
        (IntLit(0), MiniScalaIntArithShiftLeft),
        (IntLit(0), MiniScalaIntArithShiftRight)) // TODO
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((MiniScalaIntMul, IntLit(0)), 
        (MiniScalaIntBitwiseAnd, IntLit(0)), 
        (MiniScalaIntBitwiseOr, IntLit(~0))) // TODO

  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal] =
    Map(MiniScalaIntSub -> IntLit(0), 
        MiniScalaIntDiv -> IntLit(1), 
        MiniScalaIntMod -> IntLit(0), 
        MiniScalaIntBitwiseXOr -> IntLit(0)) // TODO

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case MiniScalaIntLe | MiniScalaIntGe | MiniScalaEq => true
    case MiniScalaIntLt | MiniScalaIntGt | MiniScalaNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (MiniScalaIntAdd, Seq(IntLit(x), IntLit(y))) => IntLit(x + y)
    // TODO
    case (MiniScalaIntSub, Seq(IntLit(x), IntLit(y))) => IntLit(x - y)
    case (MiniScalaIntMul, Seq(IntLit(x), IntLit(y))) => IntLit(x * y)
    case (MiniScalaIntDiv, Seq(IntLit(x), IntLit(y))) if (y != 0) => IntLit(Math.floorDiv(x, y))
    case (MiniScalaIntMod, Seq(IntLit(x), IntLit(y))) if (y != 0) => IntLit(Math.floorMod(x, y))

    case (MiniScalaIntArithShiftLeft, Seq(IntLit(x), IntLit(y))) => IntLit(x << y)
    case (MiniScalaIntArithShiftRight, Seq(IntLit(x), IntLit(y))) => IntLit(x >> y)
    case (MiniScalaIntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => IntLit(x & y)
    case (MiniScalaIntBitwiseOr, Seq(IntLit(x), IntLit(y))) => IntLit(x | y)
    case (MiniScalaIntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => IntLit(x ^ y)
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {

    case (MiniScalaIntP, Seq(IntLit(_))) => true
    case (MiniScalaIntP, _) => false
    case (MiniScalaCharP, Seq(CharLit(_))) => true
    case (MiniScalaCharP, _) => false
    case (MiniScalaBoolP, Seq(BooleanLit(_))) => true
    case (MiniScalaBoolP, _) => false
    case (MiniScalaUnitP, Seq(UnitLit)) => true
    case (MiniScalaUnitP, _) => false
    case (MiniScalaEq, Seq(IntLit(x), IntLit(y))) => x == y
    case (MiniScalaNe, Seq(IntLit(x), IntLit(y))) => x != y
    case (MiniScalaIntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (MiniScalaIntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (MiniScalaIntGt, Seq(IntLit(x), IntLit(y))) => x > y
    case (MiniScalaIntGe, Seq(IntLit(x), IntLit(y))) => x >= y
    case (MiniScalaEq, Seq(BooleanLit(x), BooleanLit(y))) => x == y
    case (MiniScalaNe, Seq(BooleanLit(x), BooleanLit(y))) => x != y
    // TODO
  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.Tree => SymbolicCPSTreeModuleLow.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(CPSBlockSet, CPSByteRead, CPSByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(_) | CPSBlockGet | CPSByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case CPSBlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = CPSBlockTag
  protected val blockLength: ValuePrimitive = CPSBlockLength

  protected val identity: ValuePrimitive = CPSId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSAdd), (1, CPSMul), (~0, CPSAnd), (0, CPSOr), (0, CPSXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((CPSAdd, 0), (CPSSub, 0), (CPSMul, 1), (CPSDiv, 1),
        (CPSArithShiftL, 0), (CPSArithShiftR, 0),
        (CPSAnd, ~0), (CPSOr, 0), (CPSXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSMul), (0, CPSAnd), (~0, CPSOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((CPSMul, 0), (CPSAnd, 0), (CPSOr, ~0))

  protected val sameArgReduce: Map[ValuePrimitive, Literal] =
    Map(CPSSub -> 0, CPSDiv -> 1, CPSMod -> 0, CPSXOr -> 0)

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case CPSLe | CPSGe | CPSEq => true
    case CPSLt | CPSGt | CPSNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (CPSAdd, Seq(x, y)) => x + y
    case (CPSSub, Seq(x, y)) => x - y
    case (CPSMul, Seq(x, y)) => x * y
    case (CPSDiv, Seq(x, y)) if (y != 0) => Math.floorDiv(x, y)
    case (CPSMod, Seq(x, y)) if (y != 0) => Math.floorMod(x, y)

    case (CPSArithShiftL, Seq(x, y)) => x << y
    case (CPSArithShiftR, Seq(x, y)) => x >> y
    case (CPSAnd, Seq(x, y)) => x & y
    case (CPSOr, Seq(x, y)) => x | y
    case (CPSXOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {

    case (CPSLt, Seq(x, y)) => x < y
    case (CPSLe, Seq(x, y)) => x <= y
    case (CPSEq, Seq(x, y)) => x == y
    case (CPSNe, Seq(x, y)) => x != y
    case (CPSGe, Seq(x, y)) => x >= y
    case (CPSGt, Seq(x, y)) => x > y
  }
}
