use "as6.ml";

(*case tc t1 of
  SOME(Unit) => print ("t1 Success!!! :) \n")
  | _ => print ("t1 Failure! :( \n") ;

case tc t2 of
  SOME(Unit) => print ("t1 Success!!! :) \n")
  | _ => print ("t1 Failure! :( \n") ;
*)

fun test func id expr expected = 
  if (func expr) = expected then
    print (id^" Success!!! :) \n")
  else print (id^" Failure! :( \n") ;


val t1 = UnitExpr;
val t2 = PairExpr(IntExpr(1), PairExpr(IntExpr(2), IntExpr(3)));
val t3 = FstExpr(t2);
val t4 = SndExpr(t2);
val t5 = SumExpr(Right, 
            PairExpr(IntExpr(5), IntExpr(6)),
            Sum(Int, Prod(Int, Int)));
val t6 = SumExpr(Left, 
            IntExpr(5),
            Sum(Int, Bool));
val t7 = SumExpr(Right, 
            IntExpr(5),
            Sum(Int, Bool));
val t8 = CaseExpr(t5, "x", TrueExpr, "y", FalseExpr);
val t9 = CaseExpr(t5,
                  "z1",
                  IntExpr(88),
                  "z2",
                  SndExpr(VarExpr("z2"))
                 );
val t10 = SumExpr(Right, 
            PairExpr(IntExpr(5), IntExpr(6)),
            Sum(Int, Bool));

val tRoll = RollExpr(
              SumExpr(
                Right, 
                PairExpr(
                  FstExpr(VarExpr("nonempty")),
                  SndExpr(VarExpr("Ls"))),
                uType)
              );

val funVar = FunExpr("f", 
  "x",
  Prod(Int, Var("t")),
  Int, 
  IntExpr(4));

print("************************");
print("Testing Type Checker\n");
print("************************");
test tc "e1" e1 (SOME (Arrow (Sum (Unit,Prod (Int,Int)),Sum (Prod (Int,Int),Unit))));
test tc "e2" e2 (SOME (Sum (Unit,Prod (Int,Int))));
test tc "e3" e3 (SOME(Int));
test tc "e4" e4 (SOME
                (Arrow(
                  Rec ("t",Sum (Unit,Prod (Int,Var "t"))),
                  Rec ("t",Sum (Unit,Prod (Int,Var "t"))))));
test tc "e5" e5 (SOME (Rec ("t",Sum (Unit,Prod (Int,Var "t")))));
test tc "e6" e6 (SOME (Rec ("t",Sum (Unit,Prod (Int,Var "t")))));

test tc "t1" t1 (SOME(Unit));
test tc "t2" t2 (SOME(Prod (Int,Prod (Int,Int))));
test tc "t3" t3 (SOME(Int));
test tc "t4" t4 (SOME(Prod(Int, Int)));
test tc "t5" t5 (SOME(Sum (Int,Prod (Int,Int))));
test tc "t6" t6 (SOME(Sum (Int,Bool)));
test tc "t7" t7 NONE;
test tc "t8" t8 (SOME(Bool));
test tc "t9" t9 (SOME(Int));
test tc "t10" t10 NONE;

test tc "tRoll" tRoll NONE;
test tc "funVar" funVar NONE;

(*Test isVal*)
print("************************");
print("Testing function isVal\n");
print("************************");

test isVal "e1" e1 true;
test isVal "e2" e2 false;
test isVal "e3" e3 false;
test isVal "e4" e4 true;
test isVal "e5" e5 false;
test isVal "e6" e6 false;
test isVal "t1" t1 true;
test isVal "t2" t2 false;
test isVal "t3" t3 false;
test isVal "t4" t4 false;
test isVal "t5" t5 false;
test isVal "t6" t6 false;
test isVal "t7" t7 false;
test isVal "t8" t8 false;
test isVal "t9" t9 false;
test isVal "t10" t10 false;
test isVal "tRoll" tRoll false;
test isVal "funVar" funVar true;

(*Test isVal*)
print("************************");
print("Testing function decompose\n");
print("************************");

test decompose "e2" e2 (SumCtxt (Right,PairCtxt2 (Hole,IntExpr 6),Sum (Unit,Prod (Int,Int))),
                        IfExpr (FalseExpr,IntExpr 4,IntExpr 5)) ;









