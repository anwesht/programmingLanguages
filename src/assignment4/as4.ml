(*
 * Created by atuladhar on 03/12/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment.
 * Name: Anwesh Tuladhar
 *)

use "as3_with_test.ml";

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
  end;