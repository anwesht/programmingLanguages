(*
 * Created by atuladhar on 03/12/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment.
 * Name: Anwesh Tuladhar
 *)

use "as3_with_test.ml";

(*fun tc expr = 
  let 
    fun typeExpr TrueExpr _ = SOME Bool
      | typeExpr FalseExpr _ = SOME Bool
      | typeExpr (IntExpr(_)) _ = SOME Int
      | typeExpr (PlusExpr(l, r)) context = 
          if (typeExpr l context) = SOME Int andalso (typeExpr r context) = SOME Int then
            SOME Int
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

      | typeExpr _ _ = NONE;
  in 
    typeExpr expr nil
  end;*)

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
            val funPair = (funName, Arrow(paramType, returnType))
            val paramPair = (paramName, paramType)
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



