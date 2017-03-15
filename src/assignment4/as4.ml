(*
 * Created by atuladhar on 03/12/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment.
 * Name: Anwesh Tuladhar
 *)

use "as3_with_test.ml";

exception Stuck;
exception NotFinished;

fun tc expr = 
  let 
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
          #2 (foldl (fn ((varName, varType), (isSome, optionType)) => 
              if v = varName andalso not isSome then (true, SOME varType) 
              else (isSome, optionType)
            ) 
            (false, NONE) 
            (context)
          )
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

(*fun eval expr = 
  let 
    fun betaAdd (IntExpr(x)) (IntExpr(y)) = IntExpr(x + y)
      | betaAdd _ _ = raise Stuck;

    fun betaLess (IntExpr(x)) (IntExpr(y)) = if x < y then TrueExpr else FalseExpr
      | betaLess _ _ = raise Stuck;

    fun betaIfThenElse TrueExpr thenBranch _ = thenBranch
      | betaIfThenElse FalseExpr _ elseBranch = elseBranch
      | betaIfThenElse _ _ _ = raise Stuck;

    fun betaApply (f as FunExpr(funName, paramName, paramType, returnType, body)) expr = 
          ((sub f paramName body) handle 
            Capture => raise Stuck)
      | betaApply _ _ = raise Stuck;

    fun isTypeSafe e = 
      case tc e of 
        SOME _ => true
        | NONE => false;

    fun searchRule (t as TrueExpr) = t
      | searchRule (f as FalseExpr) = f
      | searchRule (n as IntExpr(_)) = n
      | searchRule (func as FunExpr(_,_,_,_,_)) = func
      | searchRule (v as VarExpr(_)) = raise Stuck
      | searchRule (pe as PlusExpr(l, r)) = 
          let 
            val rval = if isTypeSafe r then searchRule r else raise Stuck;
            val lval = if isTypeSafe l then searchRule l else raise Stuck
          in 
            betaAdd lval rval
          end
      | searchRule (le as LessExpr(l, r)) = 
          let 
            val rval = if isTypeSafe r then searchRule r else raise Stuck;
            val lval = if isTypeSafe l then searchRule r else raise Stuck
          in 
            betaLess lval rval
          end
      | searchRule (ie as IfExpr(condition, thenBranch, elseBranch)) = 
          let
            val condBool = if isTypeSafe condition then searchRule condition else raise Stuck
          in
            searchRule (betaIfThenElse condBool thenBranch elseBranch)
          end
      | searchRule (ae as ApplyExpr(func, arg)) = 
          let 
            val newExpr = if isTypeSafe func then betaApply func arg else raise Stuck
          in
            searchRule newExpr
          end
  in
    searchRule expr
  end;*)

fun eval expr = 
  let 
    fun betaAdd (IntExpr(x)) (IntExpr(y)) = IntExpr(x + y)
      | betaAdd _ _ = raise Stuck;

    fun betaLess (IntExpr(x)) (IntExpr(y)) = if x < y then TrueExpr else FalseExpr
      | betaLess _ _ = raise Stuck;

    fun betaIfThenElse TrueExpr thenBranch _ = thenBranch
      | betaIfThenElse FalseExpr _ elseBranch = elseBranch
      | betaIfThenElse _ _ _ = raise Stuck;

    fun betaApply (f as FunExpr(funName, paramName, paramType, returnType, body)) arg = 
         (* ((sub f paramName body) handle 
            Capture => raise Stuck)*)
          (sub arg paramName (sub f funName body) )
            (*handle Capture => raise Stuck)*)
      | betaApply _ _ = raise Stuck;

    fun isTypeSafe e = 
      case tc e of 
        SOME _ => true
        | NONE => false;

    fun searchRule (t as TrueExpr) = t
      | searchRule (f as FalseExpr) = f
      | searchRule (n as IntExpr(_)) = n
      | searchRule (func as FunExpr(_,_,_,_,_)) = func
      | searchRule (v as VarExpr(_)) = raise Stuck
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
            (*val newExpr = if isTypeSafe func then betaApply func arg else raise Stuck*)
          in
            if isTypeSafe newExpr then searchRule newExpr else raise Stuck
          end
      (*| searchRule _ = raise NotFinished;*)
  in
    searchRule expr
  end;









































