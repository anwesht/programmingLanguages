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
  else print ("______________\n"^id^" Failure! :( \n______________\n") ;

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

val ite_int = IfExpr (FalseExpr,IntExpr 4,IntExpr 5);
val pe1 = PlusExpr(IntExpr(3), IntExpr(4));
val pe2 = PlusExpr(ite_int, IntExpr(4));
val pe3 = PlusExpr(IntExpr(3), ite_int);

val lt1 = LessExpr(IntExpr(3), IntExpr(4));
val lt2 = LessExpr(ite_int, IntExpr(4));
val lt3 = LessExpr(IntExpr(3), ite_int);

val ite1 = IfExpr (TrueExpr,IntExpr 4,IntExpr 5);
val ite2 = IfExpr (lt1,IntExpr 4,IntExpr 5);
val ite3 = IfExpr (lt2,IntExpr 4,IntExpr 5);
val ite4 = IfExpr (lt3,IntExpr 4,IntExpr 5);

val var = VarExpr("x");

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
val ifApplySum = IfExpr (lt1,sum,sum);

test decompose "pe1" pe1 (Hole, pe1);
test decompose "pe2" pe2 (PlusCtxt2 (Hole,4), ite_int);
test decompose "pe3" pe3 (PlusCtxt1 (IntExpr 3,Hole), ite_int);

test decompose "lt1" lt1 (Hole, lt1);
test decompose "lt2" lt2 (LessCtxt2 (Hole,4), ite_int);
test decompose "lt3" lt3 (LessCtxt1 (IntExpr 3,Hole), ite_int);

test decompose "ite1" ite1 (Hole, ite1);
test decompose "ite2" ite2 (IfCtxt (Hole,IntExpr 4,IntExpr 5),lt1);
test decompose "ite3" ite3 (IfCtxt (LessCtxt2 (Hole,4),IntExpr 4,IntExpr 5), ite_int);
test decompose "ite4" ite4 (IfCtxt (LessCtxt1 (IntExpr 3,Hole),IntExpr 4,IntExpr 5), ite_int);

(*test decompose "sum" sum ("Stuck as function is a value");*)
test decompose "applySum" applySum (Hole,
   ApplyExpr
     (FunExpr
        ("sum","x",Int,Int,
         IfExpr
           (LessExpr (VarExpr "x",IntExpr 2),IntExpr 1,
            PlusExpr
              (VarExpr "x",
               ApplyExpr (VarExpr "sum",PlusExpr (VarExpr "x",IntExpr ~1))))),
      IntExpr 10));

test decompose "ifApplySum" ifApplySum (IfCtxt
     (Hole,
      FunExpr
        ("sum","x",Int,Int,
         IfExpr
           (LessExpr (VarExpr "x",IntExpr 2),IntExpr 1,
            PlusExpr
              (VarExpr "x",
               ApplyExpr (VarExpr "sum",PlusExpr (VarExpr "x",IntExpr ~1))))),
      FunExpr
        ("sum","x",Int,Int,
         IfExpr
           (LessExpr (VarExpr "x",IntExpr 2),IntExpr 1,
            PlusExpr
              (VarExpr "x",
               ApplyExpr (VarExpr "sum",PlusExpr (VarExpr "x",IntExpr ~1)))))),
   LessExpr (IntExpr 3,IntExpr 4));


test decompose "e2" e2 (SumCtxt (Right,PairCtxt2 (Hole,IntExpr 6),Sum (Unit,Prod (Int,Int))),
                        ite_int) ;

val e2_d = decompose e2;
val e2_f = fill (#1 e2_d) (#2 e2_d);
e2_f = e2;


test bigStep "bigStep e5" e5 (RollExpr
    (SumExpr
       (Right,
        PairExpr
          (IntExpr 2,
           RollExpr
             (SumExpr
                (Right,
                 PairExpr
                   (IntExpr 3,
                    RollExpr
                      (SumExpr
                         (Right,
                          PairExpr
                            (IntExpr 4,
                             RollExpr
                               (SumExpr
                                  (Left,UnitExpr,
                                   Sum
                                     (Unit,
                                      Prod
                                        (Int,
                                         Rec
                                           ("t",Sum (Unit,Prod (Int,Var "t")))))))),
                          Sum
                            (Unit,
                             Prod
                               (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))))),
                 Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))))),
        Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t"))))))));

test bigStep "bigStep e6" e6 (RollExpr
    (SumExpr
       (Right,
        PairExpr
          (IntExpr 4,
           RollExpr
             (SumExpr
                (Right,
                 PairExpr
                   (IntExpr 3,
                    RollExpr
                      (SumExpr
                         (Right,
                          PairExpr
                            (IntExpr 2,
                             RollExpr
                               (SumExpr
                                  (Left,UnitExpr,
                                   Sum
                                     (Unit,
                                      Prod
                                        (Int,
                                         Rec
                                           ("t",Sum (Unit,Prod (Int,Var "t")))))))),
                          Sum
                            (Unit,
                             Prod
                               (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))))),
                 Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))))),
        Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t"))))))));

(* Define rType (rolled-list type) to represent mu t.unit+(int*t) *)
val rType = Rec("t",Sum(Unit,Prod(Int,Var("t"))));

(* Define uType (unrolled-list type) to represent unit+(int* mu t.unit+(int*t)) *)
val uType = Sum(Unit,Prod(Int,Rec("t",Sum(Unit,Prod(Int,Var("t"))))));
(*
val rLLType = Rec("tt", Sum(Unit, Prod(rType, Var("tt"))));
val uLLType = Sum(Unit, Prod(Sum(Unit, Prod(Int,Rec("t",Sum(Unit,Prod(Int,Var("t")))))), 
      Rec("tt", Sum(Unit + (Prod(Int,Rec("t",Sum(Unit,Prod(Int,Var("t"))))))))));


val intList1 = 
  RollExpr(
    SumExpr(Right,
            PairExpr(
              IntExpr(2),
              RollExpr(
                SumExpr(Right,
                        PairExpr(
                          IntExpr(3),
                          RollExpr(
                            SumExpr(Right,
                                    PairExpr(
                                      IntExpr(4),
                                      RollExpr(
                                        SumExpr(Left,UnitExpr,uType))),
                                    uType))),
                        uType))),
            uType));

val intList2 = 
  RollExpr(
    SumExpr(Right,
            PairExpr(
              IntExpr(5),
              RollExpr(
                SumExpr(Right,
                        PairExpr(
                          IntExpr(6),
                          RollExpr(
                            SumExpr(Left,UnitExpr,uType))),
                        uType))),
            uType));

val intListList = 
  RollExpr(
    SumExpr(Right, 
            PairExpr(
              intList1,
              RollExpr(SumExpr(Right,
                      PairExpr(
                        intList2,
                        RollExpr(
                          SumExpr(Left,UnitExpr,uType))),
                      uLLType))),
            uLLType));*)


