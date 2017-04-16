(*
 * Created by atuladhar on 04/15/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment.
 * Name: Anwesh Tuladhar
 *)

(** Import diMLazy-Au to utilise the definition on DiMLazy datatypes, expressions and sub function. *)
use "diMLazy-Au.sml";

(** Type checker for DiMLazy expressions. 
  * @param expr => the expression to be type checked
  * @returns => option of datatype typ. The NONE option is returned iff the expression is ill typed.
  *)
fun tc expr = 
  let 
    (*fun subT tVar rType Bool = Bool
      | subT tVar rType Int = Int
      | subT tVar rType (vType as Var(_)) = vType
      | subT tVar rType (Arrow(argType, returnType)) = 
          Arrow((sub tVar rType argType), (sub tVar rType returnType))
      | subT tVar rType (Prod(t1, t2)) = 
          Prod((sub tVar rType t1), (sub tVar rType t2))
      | subT tVar rType (Sum(t1, t2)) = 
          Sum((sub tVar rType t1), (sub tVar rType t2))
      | subT tVar rType (recType as Rec(t, tBody)) = recType;*)

    fun unroll rType Bool = Bool
      | unroll rType Int = Int
      | unroll rType Unit = Unit
      | unroll rType (vType as Var(t)) = rType
      | unroll rType (Arrow(argType, returnType)) = 
          Arrow((unroll rType argType), (unroll rType returnType))
      | unroll rType (Prod(t1, t2)) = 
          Prod((unroll rType t1), (unroll rType t2))
      | unroll rType (Sum(t1, t2)) = 
          Sum((unroll rType t1), (unroll rType t2))
(*todo: check case for recursive type. Should be ok if maximally rolled.*)
      | unroll rType (recType as Rec(t, tBody)) = tBody;

    fun subT tVar eType Bool = Bool
      | subT tVar eType Int = Int
      | subT _ _ Unit = Unit
      | subT tVar eType (vType as Var(_)) = vType
      | subT tVar eType (Arrow(argType, returnType)) = 
          Arrow((subT tVar eType argType), (subT tVar eType returnType))
      | subT tVar eType (Prod(t1, t2)) = 
          Prod((subT tVar eType t1), (subT tVar eType t2))
      | subT tVar eType (Sum(t1, t2)) = 
          Sum((subT tVar eType t1), (subT tVar eType t2))
      | subT tVar eType (recType as Rec(t, tBody)) = 
          if eType = (unroll recType tBody) then
            tVar
          else 
            Rec(t, (subT tVar eType tBody));
          (*(
            case unroll recType tBody of 
              eType => tVar
              | _ => 
                  Rec(t, (subT tVar eType tBody))
          )*)


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
          (
            case typeExpr func context of
            SOME(Arrow(paramType, returnType)) =>
              if (typeExpr arg context) = SOME(paramType) then
                SOME returnType
              else NONE
            | SOME(_) => NONE 
            | NONE => NONE
          )

      | typeExpr UnitExpr _ = SOME Unit
      | typeExpr (PairExpr(e1, e2)) context = 
          let
            val t1 = typeExpr e1 context
            val t2 = typeExpr e2 context
          in
            case t1 of 
              SOME(tt1) =>
                (
                  case t2 of 
                    SOME(tt2) => 
                      SOME(Prod(tt1, tt2))
                    | NONE => NONE
                )
              | NONE => NONE
          end
      | typeExpr (FstExpr(pair)) context = 
          (
            case typeExpr pair context of 
            SOME(Prod(fst, _)) => SOME(fst)
            | _ => NONE
          )
      | typeExpr (SndExpr(pair)) context =
          (
            case typeExpr pair context of
              SOME(Prod(_, snd)) => SOME(snd)
              | _ => NONE
          )
      | typeExpr (SumExpr(side, e, t as Sum(l, r))) context =
          let 
            val eType = typeExpr e context
          in
            (
              case side of 
                Left => 
                  (
                    case eType of 
                      SOME(l) => SOME(t)
                      | _ => NONE
                  )
                | Right =>
                  (
                    case eType of
                      SOME(r) => SOME(t)
                      | _ => NONE
                  )
            )
          end
      | typeExpr (CaseExpr(e, x, e1, y, e2)) context =
          (case typeExpr e context of
              SOME(Sum(l, r)) => 
                let 
                  val e1Context = (x, l)::context
                  val e2Context = (y, r)::context
                  val e1Type = typeExpr e1 e1Context
                  val e2Type = typeExpr e2 e2Context
                in
                  case e2Type of
                    SOME(t2) => 
                      (
                        case e1Type of 
                        SOME(t1) => if t1 = t2 then SOME(t1) else NONE
                        | NONE => NONE
                      )
                    | NONE => NONE
                end
              | _ => NONE
          )

      | typeExpr (RollExpr(e)) context = 
          let 
            val eType = typeExpr e context
          in 
            case eType of
              SOME(et) =>
                (*SOME(subT (Var("t")) et et)*)
                SOME(Rec("t", subT (Var("t")) et et))
              | NONE => NONE
          end
      | typeExpr (UnrollExpr(e)) context = 
          let 
            val eType = typeExpr e context
          in
            case eType of 
              SOME(rType as Rec(t, tBody)) =>
                SOME(unroll rType tBody)
              | _ => (print("HEREEE\n\n");
                NONE)
          end

      | typeExpr other _ = NONE
  in 
    typeExpr expr nil
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







































