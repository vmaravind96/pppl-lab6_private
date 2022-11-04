package jsy.student

import jsy.util.options.SetBool
import jsy.lab6.Lab6Like
import jsy.lab6.ast._
import jsy.util.DoWith

object Lab6 extends jsy.util.JsyApplication with Lab6Like {
  /*
   * CSCI 3155: Lab 6
   * Reference Implementation
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*** Exercises with Continuations ***/

  def foldLeftAndThen[A,B](t: Tree)(z: A)(f: (A,Int) => A)(sc: A => B): B = {
    def loop(acc: A, t: Tree)(sc: A => B): B = t match {
      case Empty => sc(acc)
      case Node(l, d, r) => loop(acc, l) { acc => loop(f(acc,d), r)(sc) }
    }
    loop(z, t)(sc)
  }

  def dfs[A](t: Tree)(f: Int => Boolean)(sc: List[Int] => A)(fc: () => A): A = {
    def loop(path: List[Int], t: Tree)(fc: () => A): A = t match {
      case Empty => fc()
      case Node(_, d, _) if f(d) => sc(d :: path)
      case Node(l, d, r) => loop(d :: path, l) { () => loop(d :: path, r)(fc) }
    }
    loop(Nil, t)(fc)
  }

  /*** Regular Expression Parsing ***/

  /* We define a recursive decent parser for regular expressions in
   * RegExprParser.
   * 
   * We derive RegExprParser from Parsers in the Scala library to make
   * use of it's handing of input (Input) and parsing results
   * (ParseResult).
   * 
   * The Parsers trait is actually a general purpose combinator parser
   * library that we will not use.
   * 
   * Grammar
   * 
   *   re ::= union
   *   union ::= intersect {| intersect}
   *   intersect ::= concat {& concat}
   *   concat ::= not {not}
   *   not ::= ~ not | star
   *   star ::= atom {*|+|?}
   *   atom ::= ! | # | c | . | ( re )
   * 
   */
  object REParser extends REParserLike {
    /* The following items are the relevant pieces inherited from Parsers
     * 
     * type Input = Reader[Elem]
     * sealed abstract class ParseResult[+T] {
     *   val next: Input
     *   def map[U](f: T => U): ParseResult[U]
     * }
     * case class Success[+T](result: T, next: Input) extends ParseResult[T]
     * case class Failure(next: Input) extends ParseResult[Nothing]
     */

    def re(next: Input): ParseResult[RegExpr] = union(next)

    def union(next: Input): ParseResult[RegExpr] = intersect(next) match {
      case Success(r, next) => {
        def unions(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next)
          else (next.first, next.rest) match {
            case ('|', next) => intersect(next) match {
              case Success(r, next) => unions(RUnion(acc, r), next)
              case _ => Failure("expected intersect", next)
            }
            case _ => Success(acc, next)
          }
        unions(r, next)
      }
      case _ => Failure("expected intersect", next)
    }

    def intersect(next: Input): ParseResult[RegExpr] = concat(next) match {
      case Success(r, next) => {
        def intersects(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next)
          else (next.first, next.rest) match {
            case ('&', next) => concat(next) match {
              case Success(r, next) => intersects(RIntersect(acc, r), next)
              case _ => Failure("expected concat", next)
            }
            case _ => Success(acc, next)
          }
        intersects(r, next)
      }
      case _ => Failure("expected concat", next)
    }

    def concat(next: Input): ParseResult[RegExpr] = not(next) match {
      case Success(r, next) => {
        def concats(acc: RegExpr, next: Input): ParseResult[RegExpr] = not(next) match {
          case Success(r, next) => concats(RConcat(acc, r), next)
          case _ => Success(acc, next)
        }
        concats(r, next)
      }
      case _ => Failure("expected not", next)
    }

    def not(next: Input): ParseResult[RegExpr] = (next.first, next.rest) match {
      case ('~', next) => not(next) map RNeg
      case _ => star(next)
    }

    def star(next: Input): ParseResult[RegExpr] = atom(next) match {
      case Success(r, next) => {
        def stars(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next)
          else (next.first, next.rest) match {
            case ('*', next) => stars(RStar(acc), next)
            case ('+', next) => stars(RPlus(acc), next)
            case ('?', next) => stars(ROption(acc), next)
            case _ => Success(acc, next)
          }
        stars(r, next)
      }
      case _ => Failure("expected atom", next)
    }

    /* This set is useful to check if a Char is/is not a regular expression
       meta-language character.  Use delimiters.contains(c) for a Char c. */
    val delimiters = Set('|', '&', '~', '*', '+', '?', '!', '#', '.', '(', ')')

    def atom(next: Input): ParseResult[RegExpr] =
      if (next.atEnd) Failure("expected atom", next)
      else (next.first, next.rest) match {
        case ('!', next) => Success(RNoString, next)
        case ('#', next) => Success(REmptyString, next)
        case ('.', next) => Success(RAnyChar, next)
        case ('(', next) => re(next) match {
          case Success(r, next) => (next.first, next.rest) match {
            case (')', next) => Success(r, next)
            case _ => Failure("unmatched (", next)
          }
          case fail => fail
        }
        case (c, next) if (!delimiters.contains(c)) => Success(RSingle(c), next)
        case _ => Failure("expected atom", next)
      }
  }


  /*** Regular Expression Matching ***/

  /** Tests whether a prefix of chars matches the regular expression re.
    *
    * @param re a regular expression
    * @param chars a sequence of characters
    * @param sc the success continuation
    * @return if there is a prefix match, then sc is called with the remainder of chars that has yet to be matched. That is, the success continuation sc captures “what to do next if a prefix of chars successfully matches re; if a failure to match is discovered, then false is returned directly.
    */
  def test(re: RegExpr, chars: List[Char])(sc: List[Char] => Boolean): Boolean = (re, chars) match {
    /* Basic Operators */
    case (RNoString, _) => false
    case (REmptyString, _) => sc(chars)
    case (RSingle(_), Nil) => false
    case (RSingle(c1), c2 :: t) => c1 == c2 && sc(t)
    case (RConcat(re1, re2), _) => test(re1, chars) { chars1 => test(re2, chars1)(sc) }
    case (RUnion(re1, re2), _) => test(re1, chars)(sc) || test(re2, chars)(sc)
    case (RStar(re1), _) =>
      sc(chars) ||
        test(re1, chars) { chars1 => chars != chars1 && test(RStar(re1), chars1)(sc) }

    /* Extended Operators */
    case (RAnyChar, Nil) => false
    case (RAnyChar, _ :: t) => sc(t)
    case (RPlus(re1), _) => test(RConcat(re1, RStar(re1)), chars)(sc)
    case (ROption(re1), _) => test(RUnion(REmptyString, re1), chars)(sc)

    /***** Extra Credit Cases *****/
    case (RIntersect(re1, re2), _) =>
      test(re1, chars) { chars1 => test(re2, chars) { chars2 => chars1 == chars2 && sc(chars2) } }
    case (RNeg(re1), _) => {
      /* Try every splitting of chars.  Could perhaps be made more elegant.  We also
       * should use a more efficient structure for the splitting (because we use :+). */
      def negtest(chars1: List[Char], chars2: List[Char]): Boolean = {
        def trynext() = chars2 match {
          case Nil => false
          case h2 :: t2 => negtest(chars1 :+ h2, t2)
        }
        (!test(re1, chars1) { r => r.isEmpty } && sc(chars2)) || trynext()
      }
      negtest(Nil, chars)
    }
  }

  def retest(re: RegExpr, s: String): Boolean = test(re, s.toList) { chars => chars.isEmpty }


  /*******************************/
  /*** JavaScripty Interpreter ***/
  /*******************************/

  /* This part is optional for fun and extra credit.
   *
   * If you want your own complete JavaScripty interpreter, you can copy your
   * Lab 5 interpreter here and extend it for the Lab 6 constructs.
   */

  /*** Type Inference ***/

  def typeof(env: TEnv, e: Expr): Typ = ???

  /*** Step ***/

  def substitute(e: Expr, v: Expr, x: String): Expr = ???
  def step(e: Expr): DoWith[Mem,Expr] = ???

  /*** Lower ***/

  def lower(e: Expr): Expr = e

///  /*** Helper: mapFirst to DoWith ***/
///
///  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
///  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match {
///    case Nil => doreturn( Nil )
///    case h :: t => f(h) match {
///      case None =>
///        mapFirstWith(f)(t) map { tp => h :: tp }
///      /* for (tp <- mapFirstWith(f)(t)) yield h :: tp */
///      case Some(withhp) =>
///        withhp map { hp => hp :: t }
///      /* for (hp <- withhp) yield hp :: t */
///    }
///  }
///
///  /*** Transformation ***/
///
///  /* Transformation visitor. */
///  /*
///  def transformVisitor[Env](visitant: (Env => Expr => Expr) => Env => PartialFunction[Expr, Expr])(env: Env)(e: Expr): Expr = {
///    def loop(env: Env)(e: Expr): Expr = {
///      val tr: Expr => Expr = loop(env)
///      val f = visitant(loop)(env).orElse[Expr,Expr] {
///        case Var(_) | N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
///        case Print(e1) => Print(tr(e1))
///        case Unary(uop, e1) => Unary(uop, tr(e1))
///        case Binary(bop, e1, e2) => Binary(bop, tr(e1), tr(e2))
///        case If(e1, e2, e3) => If(tr(e1), tr(e2), tr(e3))
///        case Decl(mut, y, e1, e2) => Decl(mut, y, tr(e1), tr(e2))
///        case Function(p, paramse, retty, e1) => Function(p, paramse, retty, tr(e1))
///        case Call(e1, args) => Call(tr(e1), args map tr)
///        case Obj(fields) => Obj(fields mapValues tr)
///        case GetField(e1, f) => GetField(tr(e1), f)
///        case Assign(e1, e2) => Assign(tr(e1), tr(e2))
///        case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, tr(e1))
///        /***** Begin Regular Expressions Extension *****/
///        case RE(_) => e
///        case RuntimeCall(f, args) => RuntimeCall(f, args map tr)
///        /***** End Regular Expressions Extension *****/
///      }
///      f(e)
///    }
///    loop(env)(e)
///  }
///
///  def transformVisitorSimple(visitant: (Expr => Expr) => PartialFunction[Expr, Expr])(e: Expr): Expr = {
///    def myvisitant(tr: Unit => Expr => Expr): Unit => PartialFunction[Expr,Expr] = { _ => visitant(tr()) }
///    transformVisitor[Unit](myvisitant)()(e)
///  }
///
///  def transformTypVisitor[Env](visitant: (Env => Typ => Typ) => Env => PartialFunction[Typ, Typ])(env: Env)(t: Typ): Typ = {
///    def loop(env: Env)(t: Typ): Typ = {
///      val tr: Typ => Typ = loop(env)
///      val f = visitant(loop)(env).orElse[Typ,Typ] {
///        case TNumber | TBool | TString | TUndefined | TNull | TVar(_) => t
///        case TFunction(paramse, rt) =>
///          val paramsep = paramse.fold(
///           { params => Left(params map { case (x,t) => (x,tr(t)) }) },
///           { case (mode,x,t) => Right((mode,x,tr(t))) }
///          )
///          TFunction(paramsep, tr(rt))
///        case TObj(fields) => TObj(fields mapValues tr)
///        case TInterface(tvar, t1) => TInterface(tvar, tr(t1))
///        /***** Begin Regular Expressions Extension *****/
///        case TRegExp => t
///        /***** End Regular Expressions Extension *****/
///      }
///      f(t)
///    }
///    loop(env)(t)
///  }
///
///  def transformTypVisitorSimple(visitant: (Typ => Typ) => PartialFunction[Typ, Typ])(t: Typ): Typ = {
///    def myvisitant(tr: Unit => Typ => Typ): Unit => PartialFunction[Typ,Typ] = { _ => visitant(tr()) }
///    transformTypVisitor[Unit](myvisitant)()(t)
///  }
///
///  /* Substitute in type t replacing uses of type variable tvar with type tp */
///  def typSubstitute(t: Typ, tp: Typ, tvar: String): Typ = {
///    def subst(tr: Typ => Typ): PartialFunction[Typ,Typ] = {
///      case TVar(tvarp) => if (tvar == tvarp) tp else t
///      case TInterface(tvarp, t1) =>
///        if (tvar == tvarp) t // tvar shadowed by tvarp
///        else TInterface(tvarp, tr(t1))
///    }
///    transformTypVisitorSimple(subst)(t)
///  }
///
///  /* Substitute in an expression e all uses of type variable tvar with type tp */
///  def typSubstituteExpr(tp: Typ, tvar: String, e: Expr): Expr = {
///    def tysubst(t: Typ): Typ = typSubstitute(t, tp, tvar)
///    def subst(tr: Expr => Expr): PartialFunction[Expr, Expr] = {
///      case Unary(Cast(t), e1) => Unary(Cast(tysubst(t)), tr(e1))
///      case Function(p, paramse, retty, e1) =>
///        val paramsep = paramse.fold(
///        { params => Left(params map { case (x,t) => (x,tysubst(t)) }) },
///        { case (mode,x,t) => Right((mode,x,tysubst(t))) }
///        )
///        Function(p, paramsep, retty map tysubst, tr(e1))
///      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException
///    }
///    transformVisitorSimple(subst)(e)
///  }
///  */
///
///  /*** Casting ***/
///
///  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
///    case (TNull, TObj(_)) => true
///    case (_, _) if (t1 == t2) => true
///    case (TObj(fields1), TObj(fields2)) => {
///      (fields2 forall { case (f2, t2) => fields1.get(f2) match { case Some(t1) => t1 == t2 case None => false } }) ||
///        (fields1 forall { case (f2, t2) => fields2.get(f2) match { case Some(t1) => t1 == t2 case None => false } })
///    }
///    /*case (TInterface(tvar, t1p), _) => castOk(typSubstitute(t1p, t1, tvar), t2)
///    case (_, TInterface(tvar, t2p)) => castOk(t1, typSubstitute(t2p, t2, tvar))*/
///    case _ => false
///  }
///
///  /*** Type Inference ***/
///
///  def hasFunctionTyp(t: Typ): Boolean = t match {
///    case TFunction(_, _) => true
///    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
///    case _ => false
///  }
///
///  def mut(m: PMode): Mutability = m match {
///    case PName => MConst
///    case PVar | PRef => MVar
///  }
///
///  def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ = {
///    def typ(e1: Expr) = typeInfer(env, e1)
///    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)
///    def check[T](e1: Expr)(cases: PartialFunction[Typ,T]): T = {
///      val errpfun: PartialFunction[Typ,T] = { case tgot => err(tgot, e1) }
///      (cases orElse errpfun)(typ(e1))
///    }
///
///    e match {
///      /***** Begin Regular Expressions Extension *****/
///      case RE(_) => TRegExp
///      case Call(GetField(e1, "test"), List(e2)) => typ(e1) match {
///        case TRegExp => typ(e2) match {
///          case TString => TBool
///          case tgot => err(tgot, e2)
///        }
///        case tgot => err(tgot, e1)
///      }
///      /***** End Regular Expressions Extension *****/
///
///      case Print(e1) => typ(e1); TUndefined
///      case N(_) => TNumber
///      case B(_) => TBool
///      case Undefined => TUndefined
///      case S(_) => TString
///      case Var(x) =>
///        val (_, t) = env(x)
///        t
///      case Unary(Neg, e1) => check(e1){
///        case TNumber => TNumber
///      }
///      case Unary(Not, e1) => check(e1){
///        case TBool => TBool
///      }
///      case Binary(Plus, e1, e2) => check(e1){
///        case TNumber => check(e2){ case TNumber => TNumber }
///        case TString => check(e2){ case TString => TString }
///      }
///      case Binary(Minus|Times|Div, e1, e2) => check(e1){
///        case TNumber => check(e2){ case TNumber => TNumber }
///      }
///      case Binary(Eq|Ne, e1, e2) => check(e1){
///        case t1 if !hasFunctionTyp(t1) => check(e2){ case t2 if (t1 == t2) => TBool }
///      }
///      case Binary(Lt|Le|Gt|Ge, e1, e2) => check(e1){
///        case TNumber => check(e2){ case TNumber => TBool }
///        case TString => check(e2){ case TString => TBool }
///      }
///      case Binary(And|Or, e1, e2) => check(e1){
///        case TBool => check(e2){ case TBool => TBool }
///      }
///      case Binary(Seq, e1, e2) => typ(e1); typ(e2)
///      case If(e1, e2, e3) => check(e1){
///        case TBool => check(e2){
///          case t2 => check(e3){ case t3 if (t2 == t3) => t2 }
///        }
///      }
///
///      case Obj(fields) => TObj(fields map { case (f,t) => (f, typ(t)) })
///      case GetField(e1, f) => check(e1){
///        case tgot @ TObj(tfields) => tfields.getOrElse(f, err(tgot, e1))
///      }
///
///      case Decl(mut, x, e1, e2) => typeInfer(env + (x -> (mut, typ(e1))), e2)
///
///      case Function(p, paramse, tann, e1) => {
///        // Bind to env1 an environment that extends env with an appropriate binding if
///        // the function is potentially recursive.
///        val env1 = (p, tann) match {
///          case (Some(f), Some(rt)) =>
///            val tprime = TFunction(paramse, rt)
///            env + (f -> (MConst, tprime))
///          case (None, _) => env
///          case _ => err(TUndefined, e1)
///        }
///        // Bind to env2 an environment that extends env1 with the parameters.
///        val env2 = paramse match {
///          case Left(params) => params.foldLeft(env1){ case (acc, (x,t)) => acc + (x -> (MConst, t)) }
///          case Right((mode,x,t)) => env1 + (x -> (mut(mode), t))
///        }
///        // Infer the type of the function body
///        val t1 = typeInfer(env2, e1)
///        tann foreach { rt => if (rt != t1) err(t1, e1) };
///        TFunction(paramse, t1)
///      }
///
///      case Call(e1, args) => check(e1){
///        case TFunction(Left(params), tret) if (params.length == args.length) => {
///          (params, args).zipped.foreach {
///            case ((_, tparami),ei) => check(ei){
///              case ti if (ti == tparami) => ()
///            }
///          }
///          tret
///        }
///        case tgot @ TFunction(Right((mode,_,tparam)), tret) => {
///          args match {
///            case earg :: Nil => check(earg){
///              case targ if (targ == tparam  && (mode != PRef || isLExpr(earg))) => ()
///            }
///            case _ => err(tgot, e1)
///          }
///          tret
///        }
///      }
///
///      case Assign(Var(x), e1) =>
///        val t1 = typ(e1)
///        env.get(x) match {
///          case Some((MVar, t)) if (t1 == t) => t1
///          case _ => err(t1, e1)
///        }
///      case Assign(GetField(e1, f), e2) => check(e1){
///        case TObj(fields) =>
///          val t2 = typ(e2)
///          fields.get(f) match {
///            case Some(t) if (t2 == t) => t2
///            case _ => err(t2, e2)
///          }
///      }
///      case Assign(_, _) => err(TUndefined, e)
///
///      case Null => TNull
///
///      case Unary(Cast(t), e1) => check(e1) {
///        case t1 if (castOk(t1, t)) => t
///        case t1 =>
///          /* println("Casting to: " + t) */
///          err(t1, e1)
///      }
///
///      /* Should not match: non-source expressions or should have been removed */
///      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
///    }
///  }
///
///  /*** Small-Step Interpreter ***/
///
///  /* Do the operation for an inequality. */
///  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
///    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
///    ((v1, v2): @unchecked) match {
///      case (S(s1), S(s2)) =>
///        (bop: @unchecked) match {
///          case Lt => s1 < s2
///          case Le => s1 <= s2
///          case Gt => s1 > s2
///          case Ge => s1 >= s2
///        }
///      case (N(n1), N(n2)) =>
///        (bop: @unchecked) match {
///          case Lt => n1 < n2
///          case Le => n1 <= n2
///          case Gt => n1 > n2
///          case Ge => n1 >= n2
///        }
///    }
///  }
///
///  /* Capture-avoiding substitution in e replacing variables x with esub. */
///  def substitute(e: Expr, esub: Expr, x: String): Expr = {
///    def subst(e: Expr): Expr = substitute(e, esub, x)
///    val ep = avoidCapture(freeVars(esub), e)
///    ep match {
///      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => ep
///      case Print(e1) => Print(subst(e1))
///      case Unary(uop, e1) => Unary(uop, subst(e1))
///      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
///      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
///      case Var(y) => if (x == y) esub else e
///      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
///      case Function(p, paramse, retty, e1) =>
///        if (
///          p == Some(x) ||
///            paramse.fold(
///            { params => params exists { case (y,_) => x == y } },
///            { case (_,y,_) => x == y }
///            )
///        ) e
///        else Function(p, paramse, retty, subst(e1))
///      case Call(e1, args) => Call(subst(e1), args map subst)
///      case Obj(fields) => Obj(fields map { case (fi,ei) => (fi, subst(ei)) })
///      case GetField(e1, f) => GetField(subst(e1), f)
///      case Assign(e1, e2) => Assign(subst(e1), subst(e2))
///      case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, subst(e1))
///
///      /***** Begin Regular Expressions Extension *****/
///      case RE(_) => e
///      case RuntimeCall(f, args) => RuntimeCall(f, args map subst)
///      /***** End Regular Expression Extension *****/
///    }
///  }
///
///  /* A small-step transition. */
///  def step(e: Expr): DoWith[Mem, Expr] = {
///    require(!isValue(e), s"stepping on a value: ${e}")
///
///    /*** Helpers for Call ***/
///
///    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))
///
///    /* Check whether or not the argument expression is ready to be applied. */
///    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
///      case PVar => isValue(arg)
///      case PName => true
///      case PRef => isLValue(arg)
///    }
///
///    /*** Body ***/
///    e match {
///      /***** Begin Regular Expressions Extension *****/
///      /* Do Rule */
///      case Call(GetField(RE(re), "test"), List(S(s))) => doreturn( B(retest(re,s)) )
///      /* Search Rule */
///      case Call(e1 @ GetField(RE(re), "test"), List(e2)) =>
///        step(e2) map { e2p => Call(e1, List(e2p)) }
///      /* RuntimeCall Search Rule. */
///      case RuntimeCall(f, args) =>
///        mapFirstWith(stepIfNotValue)(args) map { argsp => RuntimeCall(f, argsp) }
///      /***** End Regular Expressions Extension *****/
///
///      /* Base Cases: Do Rules */
///      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
///      case Unary(Neg, N(n1)) => doreturn( N(- n1) )
///      case Unary(Not, B(b1)) => doreturn( B(! b1) )
///      case Binary(Seq, v1, e2) if isValue(v1) => doreturn( e2 )
///      case Binary(Plus, S(s1), S(s2)) => doreturn( S(s1 + s2) )
///      case Binary(Plus, N(n1), N(n2)) => doreturn( N(n1 + n2) )
///      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(inequalityVal(bop, v1, v2)) )
///      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 == v2) )
///      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 != v2) )
///      case Binary(And, B(b1), e2) => doreturn( if (b1) e2 else B(false) )
///      case Binary(Or, B(b1), e2) => doreturn( if (b1) B(true) else e2 )
///      case Binary(Minus, N(n1), N(n2)) => doreturn( N(n1 - n2) )
///      case Binary(Times, N(n1), N(n2)) => doreturn( N(n1 * n2) )
///      case Binary(Div, N(n1), N(n2)) => doreturn( N(n1 / n2) )
///      case If(B(b1), e2, e3) => doreturn( if (b1) e2 else e3 )
///      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) => memalloc(e)
///      case GetField(a @ A(_), f) =>
///        doget map { m =>
///          val vopt = m.get(a) flatMap {
///            case Obj(fields) => fields.get(f)
///            case _ => None
///          }
///          vopt.getOrElse(throw StuckError(e))
///        }
///      /*
///      for (m <- doget) yield {
///        val vopt = for {
///          Obj(fields) <- m.get(a)
///          v <- fields.get(f)
///        } yield v
///        vopt.getOrElse(throw StuckError(e))
///      }
///      */
///
///      case Decl(MConst, x, v1, e2) if isValue(v1) => doreturn( substitute(e2, v1, x) )
///      case Decl(MVar, x, v1, e2) if isValue(v1) =>
///        memalloc(v1) map { a => substitute(e2, Unary(Deref, a), x) }
///      /* for (a <- Mem.alloc(v1)) yield substitute(e2, Unary(Deref, a), x) */
///
///      case Unary(Deref, a @ A(_)) =>
///        doget map { m => m(a) }
///      /* for (m <- doget) yield m(a) */
///
///      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
///        domodify { (m: Mem) => m + (a -> v) } map { _ => v }
///      /* for (_ <- domodify { (m: Mem) => m + (a -> v) }) yield v */
///
///      case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
///        domodify { (m: Mem) =>
///          val fields = m.get(a) match {
///            case Some(Obj(fields)) if (fields.contains(f)) => fields
///            case _ => throw StuckError(e)
///          }
///          m + (a -> Obj(fields + (f -> v)))
///        } map {
///          _ => v
///        }
///
///      case Call(v1, args) if isValue(v1) =>
///        def substfun(e1: Expr, p: Option[String]): Expr = p match {
///          case None => e1
///          case Some(x) => substitute(e1, v1, x)
///        }
///        (v1, args) match {
///          /* DoCall, DoCallRec */
///          case (Function(p, Left(params), _, e1), _) if (args forall isValue) => {
///            val e1p = (params, args).zipped.foldRight(e1){
///              case (((xi, _),vi), acc) => substitute(acc, vi, xi)
///            }
///            doreturn( substfun(e1p, p) )
///          }
///          case (Function(p, Right((mode,x,_)), _, e1), earg :: Nil) if argApplyable(mode, earg) => mode match {
///            /* DoCallName, DoCallRecName, DoCallRef, DoCallRecRef */
///            case PName | PRef => doreturn( substfun(substitute(e1, earg, x), p) )
///            /* DoCallVar, DoCallRecVar */
///            case PVar => memalloc(earg) map { a => substfun(substitute(e1, Unary(Deref, a), x), p) }
///          }
///          /* SearchCall2 */
///          case (Function(_, Left(_), _, _), args) => mapFirstWith(stepIfNotValue)(args) map { argsp => Call(v1, argsp) }
///          /* SearchCallVar, SearchCallRef */
///          case (Function(_, Right(_), _, _), earg :: Nil) => step(earg) map { eargp => Call(v1, eargp :: Nil) }
///          case _ => throw StuckError(e)
///        }
///
///      case Unary(Cast(t), Null) => t match {
///        case TObj(_) | TInterface(_, TObj(_)) => doreturn( Null )
///        case _ => throw StuckError(e)
///      }
///      case Unary(Cast(t), a @ A(_)) => doget map { m =>
///        m.get(a) match {
///          case Some(Obj(fields)) => t match {
///            case TObj(fieldst) if fieldst forall { case (fi, _) => fields.contains(fi) } => a
///            case TInterface(_, TObj(fieldst)) if fieldst forall { case (fi, _) => fields.contains(fi) } => a
///            case _ => throw DynamicTypeError(e)
///          }
///          case _ => throw StuckError(e)
///        }
///      }
///      case Unary(Cast(_), v1) if isValue(v1) => doreturn( v1 )
///
///      /* Base Cases: Error Rules */
///      case Unary(Deref, Null) | GetField(Null, _) | Assign(Unary(Deref, Null), _) | Assign(GetField(Null, _), _) => throw NullDereferenceError(e)
///
///      /* Inductive Cases: Search Rules */
///      case Print(e1) =>
///        step(e1) map { e1p => Print(e1p) }
///      /* for (e1p <- step(e1)) yield Print(e1p) */
///      case Unary(uop, e1) =>
///        step(e1) map { e1p => Unary(uop, e1p) }
///      /* for (e1p <- step(e1)) yield Unary(uop, e1p) */
///      case Binary(bop, v1, e2) if isValue(v1) =>
///        step(e2) map { e2p => Binary(bop, v1, e2p) }
///      /* for (e2p <- step(e2)) yield Binary(bop, v1, e2p) */
///      case Binary(bop, e1, e2) =>
///        step(e1) map { e1p => Binary(bop, e1p, e2) }
///      /* for (e1p <- step(e1)) yield Binary(bop, e1p, e2) */
///      case If(e1, e2, e3) =>
///        step(e1) map { e1p => If(e1p, e2, e3) }
///      /* for (e1p <- step(e1)) yield If(e1p, e2, e3) */
///      case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
///        case Some((fi,ei)) =>
///          step(ei) map { eip => Obj(fields + (fi -> eip)) }
///        /* for (eip <- step(ei)) yield Obj(fields + (fi -> eip)) */
///        case None => throw StuckError(e)
///      }
///      case GetField(e1, f) =>
///        step(e1) map { e1p => GetField(e1p, f) }
///      /* for (e1p <- step(e1)) yield GetField(e1p, f) */
///
///      case Decl(mut, x, e1, e2) =>
///        step(e1) map { e1p => Decl(mut, x, e1p, e2) }
///      /* for (e1p <- step(e1)) yield Decl(mut, x, e1p, e2) */
///      case Assign(e1, e2) if (isLValue(e1)) =>
///        step(e2) map { e2p => Assign(e1, e2p) }
///      /* for (e2p <- step(e2)) yield Assign(e1, e2p) */
///      case Assign(e1, e2) =>
///        step(e1) map { e1p => Assign(e1p, e2) }
///      /* for (e1p <- step(e1)) yield Assign(e1p, e2) */
///
///      case Call(e1, args) =>
///        step(e1) map { e1p => Call(e1p, args) }
///      /* for (e1p <- step(e1)) yield Call(e1p, args) */
///
///      /* Everything else is a stuck error. */
///      case _ => throw StuckError(e)
///    }
///  }
///
///  /*** Extra Credit: Lowering: Remove Interface Declarations ***/
///
///  def removeInterfaceDecl(e: Expr): Expr = ??? /*{
///    type Env = Map[String, Typ]
///    def removeFromTyp(env: Env, t: Typ): Typ = {
///      def tyrm(tr: Env => Typ => Typ)(env: Env): PartialFunction[Typ,Typ] = {
///        case TVar(tvar) => env.getOrElse(tvar, throw new IllegalArgumentException("Unknown type name %s.".format(tvar)))
///        /* Should never match because introduced in this pass. */
///        case TInterface(_, _) => throw new IllegalArgumentException("Gremlins: Encountered TInterface in removeInterfaceDecl.")
///      }
///      transformTypVisitor(tyrm)(env)(t)
///    }
///    def loop(env: Map[String, Typ], e: Expr): Expr = {
///      def tyrm(t: Typ): Typ = removeFromTyp(env, t)
///      def rm(e: Expr): Expr = loop(env, e)
///      val r =
///        e match {
///          case Unary(Cast(t), e1) => Unary(Cast(tyrm(t)), rm(e1))
///          case Function(p, paramse, retty, e1) =>
///            val paramsep = paramse.fold(
///            { params => Left(params map { case (x, t) => (x, tyrm(t)) }) },
///            { case (mode,x,t) => Right(mode,x,tyrm(t)) }
///            )
///            Function(p, paramsep, retty map tyrm, rm(e1))
///          case InterfaceDecl(tvar, t, e1) =>
///            val tp = TInterface(tvar, removeFromTyp(env + (tvar -> TVar(tvar)), t))
///            loop(env + (tvar ->tp), e1)
///          /* Pass through cases. */
///          case Var(_) | N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
///          case Print(e1) => Print(rm(e1))
///          case Unary(uop, e1) => Unary(uop, rm(e1))
///          case Binary(bop, e1, e2) => Binary(bop, rm(e1), rm(e2))
///          case If(e1, e2, e3) => If(rm(e1), rm(e2), rm(e3))
///          case Decl(mut, y, e1, e2) => Decl(mut, y, rm(e1), rm(e2))
///          case Call(e1, args) => Call(rm(e1), args map rm)
///          case Obj(fields) => Obj(fields map { case (f, e) => (f, rm(e)) })
///          case GetField(e1, f) => GetField(rm(e1), f)
///          case Assign(e1, e2) => Assign(rm(e1), rm(e2))
///          /***** Begin Regular Expressions Extension *****/
///          case RE(_) => e
///          case RuntimeCall(f, args) => RuntimeCall(f, args map rm)
///          /***** End Regular Expressions Extension *****/
///        }
///      /* Patch up positions for error messages. */
///      e match {
///        case InterfaceDecl(_, _, _) => r
///        case _ => r setPos e.pos
///      }
///    }
///    loop(Map.empty, e)
///  }*/
///
///  /***************************/
///  /*** External Interfaces ***/
///  /***************************/
///
///  var useReferenceRegExprParser = false // set to true to use the reference parser
///
///  this.flagOptions = this.flagOptions ++ List(
///    ("ref-reparser", SetBool(b => useReferenceRegExprParser = b, Some(b => useReferenceRegExprParser == b)), "using the reference regular expression parser")
///  )
///
///  // Select the parser to use based on the useReferenceRegExprParser flag
///  def parser: JsyParser =
///    if (useReferenceRegExprParser) new JsyParser else new JsyParser(REParser.parse)
///
///  //this.debug = true // comment this out or set to false if you don't want print debugging information
///  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
///
///  def inferType(e: Expr): Typ = {
///    if (debug) {
///      println("------------------------------------------------------------")
///      println("Type checking: %s ...".format(e))
///    }
///    val t = typeInfer(Map.empty, e)
///    if (debug) {
///      println("Type: " + pretty(t))
///    }
///    t
///  }
///
///  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging.
///
///  case class TerminationError(e: Expr) extends Exception {
///    override def toString = JsyParser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
///  }
///
///  def iterateStep(e: Expr): Expr = {
///    require(closed(e), "input Expr to iterateStep is not closed: free variables: %s".format(freeVars(e)))
///    def loop(e: Expr, n: Int): DoWith[Mem, Expr] =
///      if (Some(n) == maxSteps) throw TerminationError(e)
///      else if (isValue(e)) doreturn(e)
///      else {
///        for {
///          m <- doget[Mem]
///          _ = if (debug) {
///            println("Step %s:%n  %s%n  %s".format(n, m, e))
///          }
///          ep <- step(e)
///          epp <- loop(ep, n + 1)
///        } yield
///        epp
///      }
///    if (debug) {
///      println("------------------------------------------------------------")
///      println("Evaluating with step ...")
///    }
///    val (m, v) = loop(e, 0)(memempty)
///    if (debug) {
///      println("Result:%n  %s%n  %s".format(m, v))
///    }
///    v
///  }
///
///  // Convenience to pass in a jsy expression as a string.
///  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(parser.parse(s)))
///
///  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
///
///  // Interface for main
///  def processFile(file: java.io.File) {
///    if (debug) {
///      println("============================================================")
///      println("File: " + file.getName)
///      println("Parsing ...")
///    }
///
///    val expr =
///      handle(None: Option[Expr]) {
///        Some {
///          parser.parseFile(file)
///        }
///      } getOrElse {
///        return
///      }
///
///    val exprlowered =
///      handle(None: Option[Expr]) {
///        Some {
///          removeInterfaceDecl(expr)
///        }
///      } getOrElse {
///        return
///      }
///
///    val welltyped = handle(false) {
///      println("# Type checking ...")
///      val t = inferType(exprlowered)
///      println("## " + pretty(t))
///      true
///    }
///    if (!welltyped) return
///
///    handle() {
///      println("# Stepping ...")
///      def loop(e: Expr, n: Int): DoWith[Mem, Expr] =
///        if (Some(n) == maxSteps) throw TerminationError(e)
///        else if (isValue(e)) doreturn(e)
///        else {
///          for {
///            m <- doget[Mem]
///            _ = println("## %4d:%n##  %s%n##  %s".format(n, m, e))
///            ep <- step(e)
///            epp <- loop(ep, n + 1)
///          } yield
///          epp
///        }
///      val (m, v) = loop(exprlowered, 0)(memempty)
///      println("## %s%n%s".format(m, pretty(v)))
///    }
///  }

}