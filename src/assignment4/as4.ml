(*
 * Created by atuladhar on 03/12/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment.
 * Name: Anwesh Tuladhar
 *)

(** Import as3 to utilise the definition on DiMLazy datatypes, expressions and sub function. *)
use "as3.ml";

(** Defined an exception Stuck. Raised when no further steps can be taken 
    during evaluation of an expression.
  *)
exception Stuck;

(** Type checker for DiMLazy expressions. 
  * @param expr => the expression to be type checked
  * @returns => option of datatype typ. The NONE option is returned iff the expression is ill typed.
  *)
fun tc expr = 
  let 
    (** Look for the given variable within the given context 
      * @param var => the variable to search for
      * @param contexts => list of pairs of varName and varType in current context.
      * @returns => option of dataype typ representing the type of var.
                 => NONE if the variable is not found in the given context.
      *)
    fun lookupVar (var:string) nil = NONE
      | lookupVar var ((varName, varType)::contexts) = 
          if var = varName then SOME varType else lookupVar var contexts;

    (** Type check the given expression within the context provided.
      * @param expr => the expression to be type checked.
      * @param context => the context within which to type check expr. The context is initialised to nil
          and is augmented by new variables only by the expression FunExpr.
      * @returns => option of datatype typ. The NONE option is returned iff the expression is ill typed.
      *)
    fun typeExpr TrueExpr _ = SOME Bool
      | typeExpr FalseExpr _ = SOME Bool
      | typeExpr (IntExpr(_)) _ = SOME Int
      | typeExpr (PlusExpr(l, r)) context = 
          if (typeExpr l context) = SOME Int andalso (typeExpr r context) = SOME Int then
            SOME Int
          else 
            NONE
      | typeExpr (LessExpr(l, r)) context = 
          if (typeExpr l context) = SOME Int andalso (typeExpr r context) = SOME Int then
            SOME Bool
          else 
            NONE
      | typeExpr (IfExpr(condition, thenBranch, elseBranch)) context = 
          if (typeExpr condition context) = SOME(Bool) then
            let 
              val typeOfThen = typeExpr thenBranch context
            in 
              if typeOfThen = (typeExpr elseBranch context) then
                typeOfThen
              else
                NONE
            end
          else
            NONE
      | typeExpr (VarExpr(v)) context = 
          lookupVar v context

      | typeExpr (FunExpr(funName, paramName, paramType, returnType, body)) context = 
          let 
            val funPair = (funName, Arrow(paramType, returnType));
            val paramPair = (paramName, paramType);
            val currentContext = funPair::paramPair::context
          in
            case typeExpr body currentContext of
              SOME(t) => 
                if t = returnType then
                  SOME(#2(funPair))
                else 
                  NONE
              | NONE => NONE 
          end
      | typeExpr (ApplyExpr(func, arg)) context = 
          case typeExpr func context of
            SOME(Arrow(paramType, returnType)) =>
              if (typeExpr arg context) = SOME(paramType) then
                SOME returnType
              else NONE
            | SOME(_) => NONE 
            | NONE => NONE

  in 
    typeExpr expr nil
  end;

(** An interpreter for DiMLazy. The evaluation strategy followed is Call By Name (CBN) and 
  * evaluation direction is right to left.
  * @param expr => the expression to be evaluated
  * @returns => the final value expression.
  * @throws => Exception Stuck iff the evaluation is ill-typed and hence diverges.
  *)
fun eval expr = 
  let 
    (** Performs the beta addtion step.
      * @param x => integer value of left IntExpr
      * @param y => integer value of right IntExpr
      * @returns => the IntExpr representing the arithmetic sum of x and y
      *)
    fun betaAdd (IntExpr(x)) (IntExpr(y)) = IntExpr(x + y)
      | betaAdd _ _ = raise Stuck;
    
    (** Performs the beta less than step.
      * @param x, y => integer value of left and right IntExpr respectively
      * @returns => the Bool expr representing the result of x < y
      *)
    fun betaLess (IntExpr(x)) (IntExpr(y)) = if x < y then TrueExpr else FalseExpr
      | betaLess _ _ = raise Stuck;

    (** Performs the beta step of if-then-else expression.
      * @param bool => Bool expr after evaluating the condition of the if-then-else expr
      * @returns => the thenBranch expr if bool is TrueExpr
                 => the elseBranch expr if bool is False Expr
      * @throws => Stuck otherwise
      *)
    fun betaIfThenElse TrueExpr thenBranch _ = thenBranch
      | betaIfThenElse FalseExpr _ elseBranch = elseBranch
      | betaIfThenElse _ _ _ = raise Stuck;

    (** Performs the beta step of apply expression.
      * @param f => The FunExpr to be applied
      * @param arg => The argument supplied to FunExpr
      * @returns => The expression body of FunExpr after applying capture avoiding substitution:
          [arg/paramName, f/funName]body
      *)
    fun betaApply (f as FunExpr(funName, paramName, paramType, returnType, body)) arg = 
          (sub arg paramName (sub f funName body) )
      | betaApply _ _ = raise Stuck;

    (** Performs type check for the given expression.
      * @param e=> The expression to type check
      * @returns => true if e is well-typed
                 => false otherwise
      *)
    fun isTypeSafe e = 
      case tc e of 
        SOME _ => true
        | NONE => false;

    (** Performs the search steps when evaluating the expressions
      * @param expr => The current expression to be evaluated
      * @returns => The result of evaluating the expression.
      * @throws => Exception Stuck iff the evaluation is ill-typed and hence diverges.
      *)
    fun searchRule (t as TrueExpr) = t
      | searchRule (f as FalseExpr) = f
      | searchRule (n as IntExpr(_)) = n
      | searchRule (func as FunExpr(_,_,_,_,_)) = func
      | searchRule (v as VarExpr(_)) = raise Stuck  (* Variable is not considered a value. *)
      | searchRule (pe as PlusExpr(l, r)) = 
          let 
            val rval = searchRule r;
            val lval = searchRule l
          in 
            betaAdd lval rval
          end
      | searchRule (le as LessExpr(l, r)) = 
          let 
            val rval = searchRule r;
            val lval = searchRule l
          in 
            betaLess lval rval
          end
      | searchRule (ie as IfExpr(condition, thenBranch, elseBranch)) = 
          let
            val condBool = searchRule condition
          in
            searchRule (betaIfThenElse condBool thenBranch elseBranch)
          end
      | searchRule (ae as ApplyExpr(func, arg)) = 
          let 
            val newExpr = betaApply func arg
          in
            (*if isTypeSafe newExpr then searchRule newExpr else raise Stuck*)
            searchRule newExpr
          end
  in
    searchRule expr
  end;


val t = TrueExpr;
val f = FalseExpr;
val i = IntExpr(3);
val v = VarExpr("variable");
val p = PlusExpr(VarExpr("a"), VarExpr("b"));
val p1 = PlusExpr(IntExpr(3), IntExpr(4));
val l = LessExpr(VarExpr("a"), VarExpr("b"));
val l1 = LessExpr(IntExpr(3), IntExpr(4));
val ifSimple = IfExpr(TrueExpr, IntExpr(2), IntExpr(3));


val ifBad = IfExpr(TrueExpr, IntExpr(2), TrueExpr);


val ifBad1 = IfExpr(IntExpr(1), TrueExpr, FalseExpr);
val ifExp = IfExpr(LessExpr(VarExpr("a"), IntExpr(5)), 
  PlusExpr(VarExpr("a"), IntExpr(10)), PlusExpr(IntExpr(5), IntExpr(10)));
val funExp = FunExpr("f", "a", Int, Int, ifExp);
val applyFunExp1 = ApplyExpr(funExp, IntExpr(3));
val applyFunExp2 = ApplyExpr(funExp, IntExpr(7));
val funExp1 = FunExpr("f", "unused", Int, Int, ifSimple);


val funExp2 = FunExpr("f", "a", Int, Int, ifBad);   


(*Evaluates even if not typesafe as condition always true.*)
val ifForFun = IfExpr(LessExpr(VarExpr("a"), IntExpr(5)), VarExpr("a"), IntExpr(5));  (*returns 5 or less*)
val funExp3 = FunExpr("f", "a", Int, Int, ifForFun);
val applyFunExp3 = ApplyExpr(funExp3, IntExpr(99));
val applyFunExp3_1 = ApplyExpr(funExp3, IntExpr(2));
val funIdentity = FunExpr("f", "a", Int, Int, VarExpr("a"));
val applyIdentity1 = ApplyExpr(funIdentity, funExp3);
val applyIdentity2 = ApplyExpr(funIdentity, TrueExpr);

val sumBody = IfExpr(
  LessExpr(
    VarExpr("x"),
    IntExpr(2)
  ), 
  IntExpr(1), 
  PlusExpr(
    VarExpr("x"),
    ApplyExpr(
      VarExpr("sum"),
      PlusExpr(
        VarExpr("x"),
        IntExpr(~1)
      )
    )
  )
)

val sum = FunExpr("sum", "x", Int, Int, sumBody);
val applySum = ApplyExpr(sum, IntExpr(10)); (*Sum = 55*)

val sumOf10 = FunExpr("f", "unused", Int, Int, applySum);
val applyUnusedBadArg = ApplyExpr(sumOf10, LessExpr(TrueExpr, FalseExpr));    (*Shows Call By Name evaluation strategy*)

val cbnEval = PlusExpr(VarExpr("bad"), ApplyExpr(sum, IntExpr(10))); (*Can be verified by using print*)
(*val applyCBN = ApplyExpr(cbnEval, VarExpr("BAD"));*)


val f2 = ApplyExpr(FunExpr("loop", "x", Int, Int, ApplyExpr(VarExpr("loop"), VarExpr("x"))), IntExpr(5));   (*Infinite loop*)
val f3 =  FunExpr(
            "f", "x", Int, Int, 
            PlusExpr(
              VarExpr("x"),   (*false*)
              ApplyExpr(  (*false*)
                FunExpr("f", "x", Int, Int,  (*false*)
                  PlusExpr( (*false orelse true = true*)
                    ApplyExpr(
                      FunExpr("f", "z", Int, Int,   (*false*)
                        ApplyExpr(VarExpr("f"), VarExpr("x"))
                      ), 
                      ApplyExpr(VarExpr("f"), VarExpr("x")) (*true*)
                    ), 
                    (*VarExpr("z"))*) (*Free variable = ill typed.*)
                    IntExpr(99)) (*Free variable = ill typed.*)
                ),
                ApplyExpr(
                  VarExpr("f"), 
                  VarExpr("x")
                )
              )
            )
          );

val applyF3 = ApplyExpr(f3, IntExpr(3)); (*Stuck as free variable = ill typed*)

val f4 = FunExpr(
          "f", "x", Int, Int, 
          PlusExpr(
            VarExpr("x"),
            VarExpr("y")
          )
        );
val f5 = FunExpr(
          "f", "z", Int, Int, 
          PlusExpr(
            VarExpr("z"),
            VarExpr("y")
          )
        );

val f6 = FunExpr(
          "f", "x" , Int, Bool, 
          ApplyExpr(
            FunExpr(
              "f", "x", Bool, Bool, 
              ApplyExpr(VarExpr("f"), VarExpr("x"))
            ),
            IntExpr(5)
          )
        );

val f7 = FunExpr(
          "f", "x" , Int, Bool, 
          ApplyExpr(VarExpr("f"), VarExpr("x"))
        );







































