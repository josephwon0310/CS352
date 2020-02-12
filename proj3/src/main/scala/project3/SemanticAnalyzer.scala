package project3

class SemanticAnalyzer(parser: Parser) extends Reporter with BugReporter {
  import Language._

  /*
   * Primitive functions that do not need to be defined or declared.
   */
  val primitives = Map[String,(Boolean,Type)](
      "getchar" -> (false, FunType(List(), IntType)),
      "putchar" -> (false, FunType(List(("", IntType)), UnitType))
    )

  /*
   * Define an empty state for the Semantic Analyzer.
   *
   * NOTE:
   *   val env = new Env
   *
   *   env("hello") is equivalent to env.apply("hello")
   */
  class Env {
    def apply(name: String): Option[Type] = None
    def isVar(name: String) = false
  }

  /*
   * Env that keeps track of variables defined.
   * The map stores true if the variable is mutable,
   * false otherwise and its type.
   */
  case class TypeEnv(
    vars: Map[String,(Boolean, Type)] = primitives,
    outer: Env = new Env) extends Env {

    /*
     * Return true if the variable is already defined
     * in this scope
     */
    def isDefined(name: String) = vars.contains(name)

    /*
     * Make a copy of this object and add a mutable variable 'name'
     */
    def withVar(name: String, tp: Type): TypeEnv = {
      copy(vars = vars + (name -> (true, tp)))
    }

    /*
     * Make a copy of this object and add an immutable variable 'name'
     */
    def withVal(name: String, tp: Type): TypeEnv = {
      copy(vars = vars + (name -> (false, tp)))
    }

    /*
     * Make a copy of this object and add in the list of immutable variables.
     */
    def withVals(list: List[(String,Type)]): TypeEnv = {
      copy(vars = vars ++ (list map { t => (t._1, (false, t._2)) }).toMap)
    }

    /*
     * Return true if 'name' is a mutable variable defined in this scope
     * or in the outer scope.
     */
    override def isVar(name: String) = vars.get(name) match {
      case None => outer.isVar(name)
      case Some((mut, _)) => mut
    }

    /*
     * Return the Type if the variable 'name' is an option.
     * i.e. Some(tp) if the variable exists or None if it doesn't
     */
    override def apply(name: String): Option[Type] = vars.get(name) match {
      case Some((_, tp)) => Some(tp)
      case None => outer(name)
    }
  }

  // Error reporting
  var numError = 0
  def error(msg: String, pos: Position): Unit = {
    numError += 1
    parser.error(msg, pos)
  }

  // Warning reporting
  var numWarning = 0
  def warn(msg: String, pos: Position): Unit = {
    numWarning += 1
    parser.warn(msg, pos)
  }

  /*
   * Return a fresh name if a new variable needs to be defined
   */
  var next = 0
  def freshName(pref: String = "x") = {
    next += 1
    s"${pref}_$next"
  }

  /*
   * Auxiliary functions. May be useful.
   */
  def getName(arg: Any): String = arg match {
    case Arg(name, _, _) => name
    case FunDef(name, _, _, _) =>  name
    case _ => BUG(s"Don't know how to extract name from $arg")
  }

  def getPos(arg: Any): Position = arg match {
    case Arg(_, _, pos) => pos
    case fd@FunDef(_, _, _, _) => fd.pos
    case _ => BUG(s"Don't know how to extract position from $arg")
  }

  def checkDuplicateNames(args: List[Any]): Boolean = args match {
    case h::t =>
      val name = getName(h)
      val (dup, other) = t partition { arg => name == getName(arg) }
      dup foreach { arg =>
        error(s"$name is already defined", getPos(arg))
      }
      checkDuplicateNames(other) || dup.length > 0
    case Nil => false
  }

  def funType(args: List[Arg], rtp: Type): FunType = {
    FunType(args map { arg => (arg.name, arg.tp) }, rtp)
  }

  def listArgType(size: Int, tp: Type) = List.fill(size)(("", tp))

  /**
   * Run the Semantic Analyzer on the given AST.
   *
   * Print out the number of warnings and errors found, if any.
   * Return the AST with types resolved and the number of warnings
   * and errors.
   *
   * NOTE: we want our main program to return an Int!
   */
  def run(exp: Exp) = {
    numError = 0
    val nexp = typeCheck(exp, IntType)(TypeEnv())
    if (numWarning > 0)
      System.err.println(s"""$numWarning warning${if (numWarning != 1) "s" else ""} found""")
    if (numError > 0)
      System.err.println(s"""$numError error${if (numError != 1) "s" else ""} found""")

    (nexp, numWarning, numError)
  }

  // List of valid infix operators
  val isBOperator   = Set("==","!=","<=",">=","<",">")
  val isIntOperator   = Set("+","-","*","/")

  /*
   * Returns the type of the binary operator 'op'. See case "+" for an example
   * TODO: implement the remaining binary operators for typeBinOperator
   */
  def typeBinOperator(op: String)(pos: Position) = op match {
    case "+" => FunType(List(("", IntType), ("", IntType)), IntType)
    case "-" => FunType(List(("", IntType), ("", IntType)), IntType)
    case "*" => FunType(List(("", IntType), ("", IntType)), IntType)
    case "/" => FunType(List(("", IntType), ("", IntType)), IntType)
    case "==" => FunType(List(("", IntType), ("", IntType)), BooleanType)
    case "!=" => FunType(List(("", IntType), ("", IntType)), BooleanType)
    case "<=" => FunType(List(("", IntType), ("", IntType)), BooleanType)
    case ">=" => FunType(List(("", IntType), ("", IntType)), BooleanType)
    case "<" => FunType(List(("", IntType), ("", IntType)), BooleanType)
    case ">" => FunType(List(("", IntType), ("", IntType)), BooleanType)
    case _ =>
      error("undefined binary operator", pos)
      UnknownType
  }

  // List of valid unary operators
  val isIntUnOperator   = Set("+","-")

  /*
   * Returns the type of the unary operator 'op'
   * TODO: implement typeUnOperator
   */
  def typeUnOperator(op: String)(pos: Position) = op match {
    case "+" => FunType(List(("", IntType)), IntType)
    case "-" => FunType(List(("", IntType)), IntType)
    case _ =>
      error(s"undefined unary operator", pos)
      UnknownType
  }

  /*
   * Returns the type of the ternary operator 'op'
   * TODO: implement typeTerOperator
   * operators: block-set
   */
  def typeTerOperator(op: String)(pos: Position) = op match {
    case _ =>
      error(s"undefined ternary operator", pos)
      UnknownType
  }
  /*
   * Return the type of the operator 'op' with arity 'arity'
   */
  def typeOperator(op: String, arity: Int)(pos: Position): Type = arity match {
    case 3 => typeTerOperator(op)(pos)
    case 2 => typeBinOperator(op)(pos)
    case 1 => typeUnOperator(op)(pos)
    case _ =>
      error(s"undefined operator", pos)
      UnknownType
  }

  /*
   * Check if 'tp' conforms to 'pt' and return the more precise type.
   * The result needs to be well formed.
   *
   * TODO: implement the case of function type.
   */
  def typeConforms(tp: Type, pt: Type)(env: TypeEnv, pos: Position): Type = (tp, pt) match {
    case (_, _) if tp == pt => 
      typeWellFormed(tp)(env, pos)
    case (_, UnknownType) => 
      typeWellFormed(tp)(env, pos)  // tp <: Any
    case (UnknownType, _) =>       
      typeWellFormed(pt)(env, pos)  // for function arguments
    case (FunType(args1, rtp1), FunType(args2, rtp2)) if args1.length == args2.length => 
      FunType(typeConform(args1, args2)(env, pos), typeConforms(rtp1, rtp2)(env, pos))
    case (ArrayType(tp), ArrayType(pt)) =>  
      ArrayType(typeConforms(tp, pt)(env, pos))
    case _ =>
      error(s"type mismatch;\nfound   : $tp\nexpected: $pt", pos); pt
  }

  /*
   * Auxiliary function used to check function type argument conformity.
   *
   * The function is verifying that 'tp' elements number n conforms
   * to 'pt' element number n. It returns the list of precise types
   * returned by each invocation to typeConforms
   */
  def typeConform(tp: List[(String, Type)], pt: List[(String,Type)])(env: TypeEnv, pos: Position): List[(String, Type)] = {
    if (tp.length != pt.length) BUG("length of list does not match")

    (tp zip pt) map { case ((arg1, tp1), (arg2, tp2)) =>
      (if (tp1 != UnknownType) arg1 
       else arg2, typeConforms(tp1, tp2)(env, pos))
    }
  }

  /*
   * Verify that the type 'tp' is well formed. i.e there is no
   * UnknownType.
   */
  def typeWellFormed(tp: Type)(env: TypeEnv, pos: Position)(implicit forFunction: Boolean=false): Type = tp match {
    case FunType(args, rte) =>
      FunType(args map { case (n, tp) => 
        (n, typeWellFormed(tp)(env, pos)) 
      }, typeWellFormed(rte)(env, pos)(true))
    case ArrayType(tp) => ArrayType(typeWellFormed(tp)(env, pos))
    case UnknownType =>
        if (forFunction) {
          //println(tp)
          error("malformed type: function return types must be explicit if function is used recursively or in other functions' bodies", pos) 
        }
        else error("malformed type", pos)
        UnknownType
    case _ => tp
  }


  /*
   * typeCheck takes an expression and an expected type (which may be UnknownType).
   * This is done via calling the typeInfer and typeConforms
   * functions (details below), and finally returning the original
   * expression with all typing information resolved.
   *
   * typeInfer uses the inference rules seen during the lectures
   * to discover the type of an expression. As a reminder, the rules we saw can be
   * found in lectures 5 and 6.
   *
   * TODO: Remove the ??? and add the correct implementation.
   * The code must follow the inference rules seen during the lectures.
   *
   * The errors/warnings check that you had to implement for project 2
   * should be already implemented. However, there are new variables
   * introduced that need to be check for duplicate (function name,
   * variables names). We defined the rules for function semantic in
   * lecture 5.
   */
  def typeCheck(exp: Exp, pt: Type)(env: TypeEnv): Exp = {
    val nexp = typeInfer(exp, pt)(env)
    // println("==typecheck==")
    // print("exp: ")
    // println(exp)
    // print("pt: ")
    // println(pt)
    // print("exp type: ")
    // println(nexp.tp)

    val rnexpType = typeConforms(nexp.tp, pt)(env, exp.pos)
    nexp.withType(rnexpType)
  }

  def typeInfer(exp: Exp, pt: Type)(env: TypeEnv): Exp = exp match {
    case Lit(_: Int) => 
      exp.withType(IntType)
    case Lit(_: Boolean) => exp.withType(BooleanType)

    //TODO WEIRD AF
    // case Lit(x: String) => 
    //   print(x)
    //   exp.withType(BooleanType)
    case Lit(_: Unit) => exp.withType(UnitType)
    case Prim("block-set", args) =>
      val narr = typeCheck(args(0), ArrayType(pt))(env)
      val nindex = typeCheck(args(1), IntType)(env)
      val nval = typeCheck(args(2), pt)(env)
      Prim("block-set", List(narr, nindex, nval)).withType(UnitType)
    case Prim(op, args) =>
      typeOperator(op, args.length)(exp.pos) match {
        // case IntType =>
        //   val tp1 = typeCheck(args(0), IntType)(env)
        //   IntType
        case FunType(atps, rtp) =>
          // println(args)
          // println(atps)
          var nargs = List[Exp]()
          for (arg <- args) {
            var narg = typeCheck(arg, arg.tp)(env)
            nargs = nargs :+ narg
          }

          // val tp1 = typeCheck(args(0), IntType)(env)
          // val tp2 = typeCheck(args(1), IntType)(env)
          Prim(op, nargs).withType(rtp)

        case UnknownType => exp.withType(UnknownType)
        case _ => BUG("operator's type needs to be FunType")
      }
    case Let(x, tp, rhs, body) =>
      if (env.isDefined(x))
        warn("reuse of variable name", exp.pos)
      val nrhs = typeCheck(rhs, tp)(env)
      val nbody = typeCheck(body, pt)(env.withVal(x, nrhs.tp))
      Let(x, nrhs.tp, nrhs, nbody).withType(nbody.tp) 
    case Ref(x) =>
      env(x) match {
        case Some(tp) => // Remember to check that the type taken from the environment is welformed
            // if (!env.isDefined(x))
            //     error("undeclared variable", exp.pos)
            val new_tp = typeWellFormed(tp)(env, exp.pos)
            exp.withType(new_tp)
        case _ =>
          error("undefined identifier", exp.pos)
          exp.withType(UnknownType)
      }
    case If(cond, tBranch, eBranch) =>
      // Hint: type check the else branch before the then branch.
      val ncond = typeCheck(cond, BooleanType)(env)
      val neb = typeCheck(eBranch, pt)(env)
      val ntb = typeCheck(tBranch, neb.tp)(env)
      //typeConforms(neb.tp, ntb.tp)(env, exp.pos)

      If(ncond,ntb,neb).withType(neb.tp)

    case VarDec(x, tp, rhs, body) =>
      if (env.isDefined(x))
        warn("reuse of variable name", exp.pos)
      
      val nrhs = typeCheck(rhs, tp)(env)
      val nbody = typeCheck(body, pt)(env.withVar(x, nrhs.tp))
      VarDec(x, nrhs.tp, nrhs, nbody).withType(nbody.tp)

    case VarAssign(x, rhs) =>
      val xtp = if (!env.isDefined(x)) {
        error("undefined identifier", exp.pos)
        UnknownType
      } else {
        if (!env.isVar(x))
          error("reassignment to val", exp.pos)
        env(x).get
      }

      val nrhs = typeCheck(rhs, xtp)(env)
      
      /* Because of syntactic sugar, a variable assignment 
       * statement can be accepted as an expression
       * of type Unit. In this case, we will modify
       * the AST and store the assignment value into
       * a "dummy" variable and return the Unit Literal.
       *
       * For example,
       *
       * If(..., VarAssign("x", Lit(1)), Lit(()))
       *
       * requires the two branches of the If to be of the same
       * type, in this case, Unit. Therefore the "then" branch
       * will need to be modified to have the correct type.
       * Without changing the semantics!
       */
       //TODO THIS HAS TO CHANGE
      pt match {
        case UnitType =>
          //VarAssign(x, nrhs).withType(UnitType)
          Let(freshName(), nrhs.tp, VarAssign(x, nrhs).withType(UnitType), Lit(()))
          //Let("DUMMY", UnitType, VarAssign(x, reass), Lit(()))
        case _ => 
          VarAssign(x, nrhs).withType(nrhs.tp)
      }

    case While(cond, lbody, body) => 
      val ncond = typeCheck(cond, BooleanType)(env)
      val nlbody = typeCheck(lbody, UnitType)(env)
      val nbody = typeCheck(body, pt)(env)
      While(ncond,nlbody, nbody).withType(nbody.tp)

    case FunDef(fname, args, rtp, fbody) => 
      //TODO FIND OUT HOW TO ADD ARGS to Function environment
      checkDuplicateNames(args)
      var nargs = List[(String, Type)]()
      for (arg <- args) {
        nargs = nargs :+ (arg.name, arg.tp)
      }
      var nfbody = typeCheck(fbody, rtp)(env.withVals(nargs))
      FunDef(fname, args, nfbody.tp, nfbody).withType(pt)

    case LetRec(funs, body) =>
      checkDuplicateNames(funs)
      var nenv = env
      funs.size match {
        // TODO modify to handle general case
        case 0 =>
          val nbody = typeCheck(body, pt)(nenv)
          LetRec(Nil, nbody).withType(nbody.tp)
        case _ =>
          var nfuns = List[Exp]()
          
          var envvars = List[(String,Type)]()
          for (fun <- funs) {
            var asfun = fun.asInstanceOf[FunDef]
            envvars = (getName(fun), funType(asfun.args, asfun.rtp)) :: envvars
          }
          nenv = nenv.withVals(envvars)

          // for (fun <- funs) {
          //   var asfun = fun.asInstanceOf[FunDef]
          //   var nargs = List[(String, Type)]()
          //   for (arg <- asfun.args) {
          //     nargs = (arg.name, arg.tp) :: nargs
          //   }
          //   val nfbody = typeCheck(asfun.fbody, asfun.rtp)(env.withVals(nargs))
          //   val tptp = funType(asfun.args, nfbody.tp)
          //   val nfun = typeCheck(fun, tptp)(nenv)
          //   nenv = nenv.withVal(getName(fun), funType(asfun.args, asfun.rtp))
          //   nfuns = nfun :: nfuns
          // }

          //Double check
          var nfuns2 = List[Exp]()
          var nargs = List[(String, Type)]()
          for (fun <- funs) {
            val asfun = fun.asInstanceOf[FunDef]
            for (arg <- asfun.args) {
              nargs = (arg.name, arg.tp) :: nargs
            }
            val nfbody = typeCheck(asfun.fbody, asfun.rtp)(nenv.withVals(nargs))
            val funtp = funType(asfun.args, nfbody.tp)
            nenv = nenv.withVal(getName(fun), funtp)
            val nfun = typeCheck(fun, funtp)(nenv)
            nfuns2 = nfun :: nfuns2
          }

          val nbody = typeCheck(body, pt)(nenv)

          LetRec(nfuns2, nbody).withType(nbody.tp)
      }
    case App(fun, args) =>
      // TODO Check fun type
      
      val nFun: Exp = typeCheck(fun, fun.tp)(env)
      
      // Handling some errors
      val ftp = nFun.tp match {
        case ftp@FunType(fargs, _) if fargs.length == args.length =>
          ftp
        case ftp@FunType(fargs, rtp) if fargs.length < args.length =>
          error(s"too many arguments for method: ($fargs)$rtp", exp.pos)
          FunType(fargs ++ List.fill(args.length - fargs.length)(("", UnknownType)), rtp)
        case ftp@FunType(fargs, rtp) =>
          error(s"not enough arguments for method: ($fargs)$rtp", exp.pos)
          ftp
        case ArrayType(tp) =>
          FunType(List(("", IntType)), tp)
        case tp =>

          error(s"$tp does not take paramters", exp.pos)
          FunType(List.fill(args.length)(("", UnknownType)), pt)
      }

      // TODO: Check arguments type
      var nargs = List[Exp]()
      for (arg <- args) {
        var narg = typeCheck(arg, arg.tp)(env)
        nargs = narg :: nargs
      }

      // Transform some function applications into primitives on arrays.
      nFun.tp match {
        case ArrayType(tp) =>
          Prim("block-get", List(nFun, nargs.head)).withType(tp)
        case _ => App(nFun, nargs).withType(ftp.rtp)
      }
    case ArrayDec(size: Exp, etp: Type) => 
      // TODO: Check array declaration
      // Note that etp is the type of elements
      val nsize = typeCheck(size, IntType)(env)
      ArrayDec(nsize, etp).withType(ArrayType(etp))
    case _ =>
      BUG(s"malformed expresstion $exp")
  }
}
