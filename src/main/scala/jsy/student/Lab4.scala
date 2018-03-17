package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser

  /*
   * CSCI 3155: Lab 4
   * Kathryn Gray
   *
   * Partner: Alexander Urbanski
   * Collaborators: Kyle Helmick
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

  /* Collections and Higher-Order Functions */

  /* Lists */

  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if(h1==h2)  compressRec(t1) else h1::compressRec(t1)
  }

  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) =>  if (acc == Nil || h != acc.head) h :: acc
    else acc
  }

  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match{
      case None => h :: mapFirst(t)(f)
      case Some(x) => x :: t
    }
  }

  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => (l,d,r) match{
        case (Empty, db, Empty) => f(acc,db)
        case (Empty, db, rb) => f(loop(acc,rb),db)
        case (lb,db,_) => f(loop(acc,lb),db)
      } //  f(z,d)  Want in-order f(f(....))
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      (acc,d) => acc match{
        case (false, _) => (false,None)
        case (true, m) => m match {
          case None => (true,Some(d))
          case Some(x) => if(x > d) (true,Some(d)) else (false,None)
        }
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env(x)//if(env.contains(x)) env(x) else err(TUndefined,Var(x))
      case Decl(_, x, e1, e2) =>
        val t1=typeof(env, e1)
        //update env with t1 for x
        val newenv = env + (x->t1)
        typeof(newenv, e2)
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(Eq|Ne, e1, e2) => (typeof(env,e1),typeof(env,e2)) match {
        case (l,t) if ((l==t) && !hasFunctionTyp(l)) => TBool
        case (tgot @ TFunction(_,_), _)  => err(tgot,e1)
        case (_,tgot) => err(tgot,e2)
      }

      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(And|Or, e1, e2) =>
        (typeof(env,e1),typeof(env,e2)) match {
          case (TBool, TBool) => TBool
          case (tgot, _) => err(tgot, e1)
          case (_, tgot) => err(tgot, e2)
        }
      case Binary(Seq, e1, e2) =>
        typeof(env,e1)
        typeof(env, e2)

      case If(e1, e2, e3) => if (typeof(env,e1)!=TBool) err(typeof(env,e1),e1)
      else (typeof(env,e2),typeof(env,e3)) match {
        case (l,t) if (l==t) => l
        //case (tgot, _) if (tgot==TFunction) => err(tgot,e2)
        case (_,tgot) => err(tgot,e3)
      }
      //Changed before passing less test cases: Source -> K
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          case (None, t) => env
          case (Some(pp), Some(t)) => env + (pp->TFunction(params, t))
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1){(accenv,t) => t match {
          case (s,MTyp(_,ty)) => accenv + (s -> ty)
        }
        }
        // Infer the type of the function body
        val t1 = typeof(env2, e1)
        // Check with the possibly annotated return type
        tann match{
          case(Some(t)) => if(t==t1) TFunction(params, t) else err(t1,e1)
          case(None) => TFunction(params, t1)
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            case ((varname, mtype), e) => val etype = typeof(env,e)
              if (mtype.t != etype) throw err(etype,e)
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.mapValues(value => typeof(env,value)))
      case GetField(e1, f) =>
        val t=typeof(env,e1)
        t match{
          case TObj(fields) => fields.get(f) match{
            case Some(tau) => tau
            case None => err(t,e1)
          }
          case _ => err(t, e1)
        }
    }
  }


  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1),S(s2)) => bop match {
        case Lt => s1<s2
        case Le => s1<=s2
        case Gt => s1>s2
        case Ge => s1>=s2
        case _ => ???
      }
      case (N(x),N(y)) => bop match{
        case Lt => x<y
        case Le => x<=y
        case Gt => x>y
        case Ge => x>=y
        case _ => ???
      }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(expr) => loop(expr, n+1)
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
      /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, substitute(e1,esub,x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1,esub,x), substitute(e2,esub,x))
      case If(e1, e2, e3) => If(substitute(e1,esub,x),substitute(e2,esub,x),substitute(e3,esub,x))
      case Var(y) => if(y==x) esub else Var(y)
      case Decl(mode, y, e1, e2) =>
        if(x==y) Decl(mode, y, substitute(e1,esub,x), e2)
        else Decl(mode, y, substitute(e1,esub,x), substitute(e2,esub,x))
      /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) =>
        p match {
          case Some(fname) if(fname == x) => e
          case _ => if (params.exists{case (pname, ptype) => pname==x}) e
          else Function(p, params, tann, substitute(e1,esub,x))//cry
        }
      /*if (freeVars(e).contains(x)) {
        Function(p, params, tann, substitute(e1, esub, x))
      }
      else e*/
      case Call(e1, args) =>
        val newe1 = substitute(e1,esub,x)
        val newargs = args.map(a=>substitute(a,esub,x))
        Call(newe1, newargs)
      /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.mapValues(value => substitute(value,esub,x)))
      case GetField(e1, f) => if(x!=f) GetField(substitute(e1,esub,x),f) else e
    }
    //Changed before passing less test cases: source -> class
    val fvs = freeVars(esub)
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    subst(rename(e)(fresh))
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))
        //Changed before passing less test cases: source -> class
        case Unary(uop, e1) => Unary(uop, ren(env,e1))
        case Binary(bop, e1, e2) => Binary(bop, ren(env,e1), ren(env,e2))
        case If(e1, e2, e3) => If(ren(env,e1),ren(env,e2),ren(env,e3))
        case Var(y) =>
          if (env.contains(y)) Var(env(y)) else Var(y)
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          Decl(mode, yp, ren(env,e1), ren(env+(y->yp), e2))

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => (None, env)
            case Some(x) =>
              val m=fresh(x)
              (Some(m),env+(x->m))
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            case ((paramname,paramtype),(params, envp)) =>
              val pfresh = fresh(paramname)
              ((pfresh,paramtype) :: params, extend(env,paramname, pfresh))
          }
          Function(pp, paramsp, retty, ren(envpp,e1))
        }
        case Call(e1, args) => {
         val renamedArgs = args.foldRight(Nil: List[(Expr)]) {
           case (d, acc) => ren(env, d) :: acc
         }
         Call(ren(env, e1), renamedArgs)
       }
        case Obj(fields) => Obj(fields.mapValues(value => ren(env,value)))
        case GetField(e1, f) =>
          e1 match {
            case Obj(fields) => fields.get(f) match {
              case Some(fe) => ren(env,fe)
              case None =>  Undefined
            }
            case _ => ???
          }
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => !isValue(e)
    case MName => false
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      /***** Cases needing adapting from Lab 3.*/

      //DO Neg and Not
      case Unary(uop, x) if isValue(x) => (uop,x) match{
        case (Neg,N(x)) => N(-x)
        case (Not,B(x)) => B(!x)
      }
      /***** More cases here */
      //Do Seq
      case Binary(Seq, v1,e2) if(isValue(v1)) => e2
      //Do And and Or
      case Binary(bop @(And | Or), B(b), v2) => (bop, B(b), v2) match{
        case (And, B(b1), e2) => if(b1) e2 else B(false)
        case (Or, B(b1), e2) => if(!b1) e2 else B(true)
      }
      //Do Arith
      case Binary(bop, v1, v2) if (isValue(v1) && isValue(v2)) => (bop, v1, v2) match {
        case (Plus, N(n1), N(n2)) => N(n1+n2)
        case (Plus, S(s1), S(s2)) => S(s1+s2)
        case (Minus, N(n1), N(n2)) => N(n1- n2)
        case (Div, N(n1), N(n2))  => N(n1/n2)
        case (Times, N(n1), N(n2)) => N (n1 * n2)
        case (bopie@(Lt | Le | Gt | Ge), v1, v2) => B(inequalityVal (bopie, v1, v2) )
        case (Eq, vb1,vb2) => B(vb1==vb2)
        case (Ne, vb1, vb2) => B(vb1!=vb2)
      }
      //Do If
      case If(B(b), e2, e3) => if(b==true) e2 else e3
      //Do Call
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            //((pname, Mtyp(mode, type)),arg)
            val reducable = pazip.foldRight(false){
              (p, acc) => p match {
                case ((pname, pmode), ar) => acc || isRedex(pmode.m, ar)
              }
            }
            if (!reducable) {
              val e1p = pazip.foldRight(e1) {
                case(((pname,_), ar), end) => substitute(end,ar,pname)
              }
              p match {
                //Do Call
                case None => e1p
                //Do Call Rec
                case Some(x1) => substitute(e1p,v1,x1)
              }
            }
            else {
              //Search Call 2
              val pazipp = mapFirst(pazip) {
                p => p match{
                  case ((pname, pmode), ar) =>
                    if(isRedex(pmode.m,ar)) Some(((pname, pmode),step(ar)))
                  else None
                }
              }
              val unzipped = pazipp.unzip
              step(Call(v1, unzipped._2))
            }
          }
          case _ => throw StuckError(e)
        }
        //Do Decl and Search Decl
      case Decl(mode, y, e1, e2) =>
        //Do Decl
        if(!isRedex(mode, e1)) substitute(e2,e1,y)
        //Search Decl
        else  Decl(mode,y,step(e1),e2)
      /***** New cases for Lab 4. */
      //Do Get Field and Search Get Field
      case GetField(obj,f) => {
        if (isValue(obj)) {
          obj match {
            //Do Get Field
            case Obj(fields) => fields.get(f) match {
              case Some(tau) => tau
              case None => throw StuckError(e)
            }
            case _ => throw StuckError(e)
          }
        }
        //Search Get Field
        else GetField(step(obj), f)
        //case notobj => GetField(step(notobj),f)
      }
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      /***** Cases from Lab 3. */
      //Search Unary
      case Unary(uop, x) => Unary(uop, step(x))
      //Search Binary 1 and 2
      case Binary(bop, v1, v2) => if(!isValue(v1)) Binary(bop,step(v1),v2)
      else Binary(bop,v1,step(v2))
      //Search If
      case If(e1,e2,e3) => If(step(e1), e2, e3)
      /***** More cases here */
      /***** Cases needing adapting from Lab 3 */
      //Search Call 2
      //case Call(v1 @ Function(_, _, _, _), args) => val newargs= args.map(value=>step(value)); Call(v1, newargs)
      //Search Call 1
      case Call(e1, args) if !isValue(e1) => Call(step(e1),args)
      /***** New cases for Lab 4. */
      //Search Object
      case Obj(fields) => { //Obj(fields.mapValues(value => step(value)))//Obj(fields.find((fname, fval)=> if(!isRedex(fval) step(fval))))
        val l = fields.toList
        val newfield = mapFirst(l){ case (f, ei) =>  if(isValue(ei)) None
        else Some((f,step(ei)))}.toMap
        Obj(newfield)
      }
      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}


