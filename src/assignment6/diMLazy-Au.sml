(* This file defines several diMLazy-Au datatypes and some example expressions. *)

(* diMLazy-Au types *)
datatype typ = Bool | Int | Arrow of typ * typ | Unit
             | Prod of typ * typ | Sum of typ * typ
             | Var of string | Rec of string * typ; (* Var and Rec are grad level *)

datatype side = Left | Right;

(* diMLazy-Au expressions *)
datatype expr = TrueExpr | FalseExpr | IntExpr of int
 | PlusExpr of expr*expr | LessExpr of expr*expr
 | IfExpr of expr*expr*expr (* i.e., IfExpr(condition, thenBranch, elseBranch) *)
 | VarExpr of string | ApplyExpr of expr*expr (* i.e., ApplyExpr(fun, arg) *)
 | FunExpr of string*string*typ*typ*expr
 (* i.e., FunExpr(functionName, parameterName, parameterType, returnType, body) *)
 | UnitExpr | PairExpr of expr*expr
 | FstExpr of expr (* selects first element of a pair *) | SndExpr of expr
 | SumExpr of side*expr*typ
 (* e.g., "(inl 5):int+unit" would be SumExpr(Left,IntExpr(5),Sum(Int,Unit)) *)
 | CaseExpr of expr*string*expr*string*expr
 (* e.g., "case e of (inl x=>e1 | inr y=>e2)" would be CaseExpr(e,x,e1,y,e2) *)
 | RollExpr of expr | UnrollExpr of expr; (* RollExpr and UnrollExpr are grad level *)

(* Additional datatypes and exception, to help define evaluation of diMLazy-Au expressions *)

datatype ctxt = Hole | PlusCtxt1 of expr*ctxt | PlusCtxt2 of ctxt*int
 | LessCtxt1 of expr*ctxt | LessCtxt2 of ctxt*int
 | IfCtxt of ctxt*expr*expr  | ApplyCtxt of ctxt*expr
 | PairCtxt1 of expr*ctxt | PairCtxt2 of ctxt*expr (* where expr is a value *)
 | FstCtxt of ctxt | SndCtxt of ctxt | SumCtxt of side*ctxt*typ
 | CaseCtxt of ctxt*string*expr*string*expr
 | RollCtxt of ctxt | UnrollCtxt of ctxt;

exception Stuck;


(* The remainder of this file contains example diMLazy-Au expressions *)

(* Tell SML/NJ to print these expressions in detail *)
Control.Print.printDepth := 30;

(* Define e1 to represent:
   fun f(x:unit+(int*int)):(int*int)+unit =
     case x of inl x1=> (inr x1):(int*int)+unit
             | inr x2=> (inl (x2.snd,x2.fst)):(int*int)+unit
*)
val e1 = let val t1 = Sum(Unit,Prod(Int,Int))
             val t2 = Sum(Prod(Int,Int),Unit)
         in
           FunExpr("f","x",t1,t2,
             CaseExpr(VarExpr("x"),
                      "x1",
                      SumExpr(Right,VarExpr("x1"),t2),
                      "x2",
                      SumExpr(Left, PairExpr(SndExpr(VarExpr("x2")),
                                             FstExpr(VarExpr("x2"))), 
                              t2)))
         end;

(* Define e2 to represent:
   (inr (if false then 4 else 5, 6)):unit+(int*int)
*)
val e2 = SumExpr(Right, 
                 PairExpr(IfExpr(FalseExpr,IntExpr(4),IntExpr(5)),IntExpr(6)),
                 Sum(Unit,Prod(Int,Int)));

(* Define e3 to represent:
   case e1(e2) of inl z1=> z1.snd end
                | inr z2=> 88
*)
val e3 = CaseExpr(ApplyExpr(e1,e2),
                  "z1",
                  SndExpr(VarExpr("z1")),
                  "z2",
                  IntExpr(88));

(* Define rType (rolled-list type) to represent mu t.unit+(int*t) *)
val rType = Rec("t",Sum(Unit,Prod(Int,Var("t"))));

(* Define uType (unrolled-list type) to represent unit+(int* mu t.unit+(int*t)) *)
val uType = Sum(Unit,Prod(Int,Rec("t",Sum(Unit,Prod(Int,Var("t"))))));

val vType = Sum (Unit,Prod (Int,Rec ("t1",Sum (Unit,Prod (Int,Var "t1")))));

(* Define e4 to represent:
   fun reverse(L:rType):rType =
     (fun revDiffLists(Ls:rType*rType):rType =
        case unroll(Ls.fst)
          of inl empty => Ls.snd
           | inr nonempty => revDiffLists(nonempty.snd,
                                          roll((inr(nonempty.fst,Ls.snd)):uType)
     )
     (L, roll((inl ()):uType))
   ---
   With ML's syntactic sugar, we could write e4 as:
   fun reverse(L) = 
     let fun revDiffLists(nil,done)=done
           | revDiffLists(x::xs,done)=revDiffLists(xs, x::done)
     in revDiffLists(L,nil)
     end
*)

val argExpr = PairExpr(SndExpr(VarExpr("nonempty")),
                           RollExpr(SumExpr(Right, 
                                            PairExpr(FstExpr(VarExpr("nonempty")),
                                                     SndExpr(VarExpr("Ls"))),
                                            uType)))
    val lastBody = ApplyExpr(VarExpr("revDiffLists"),argExpr)
    val rDLBody = CaseExpr(UnrollExpr(FstExpr(VarExpr("Ls"))),
                           "empty", SndExpr(VarExpr("Ls")),
                           "nonempty",lastBody)
    val f1 = FunExpr("revDiffLists","Ls",Prod(rType,rType),rType,rDLBody)

val e4 =
  let
    val argExpr = PairExpr(SndExpr(VarExpr("nonempty")),
                           RollExpr(SumExpr(Right, 
                                            PairExpr(FstExpr(VarExpr("nonempty")),
                                                     SndExpr(VarExpr("Ls"))),
                                            uType)))
    val lastBody = ApplyExpr(VarExpr("revDiffLists"),argExpr)
    val rDLBody = CaseExpr(UnrollExpr(FstExpr(VarExpr("Ls"))),
                           "empty", SndExpr(VarExpr("Ls")),
                           "nonempty",lastBody)
    val f1 = FunExpr("revDiffLists","Ls",Prod(rType,rType),rType,rDLBody)
    val e = PairExpr(VarExpr("L"),RollExpr(SumExpr(Left,UnitExpr,uType)))
  in
    FunExpr("reverse","L",rType,rType,ApplyExpr(f1,e)) 
  end;

val g =
  let
    val argExpr = PairExpr(SndExpr(VarExpr("nonempty")),
                           RollExpr(SumExpr(Right, 
                                            PairExpr(FstExpr(VarExpr("nonempty")),
                                                     SndExpr(VarExpr("Ls"))),
                                            uType)))
    val arg = SndExpr(VarExpr("nonempty"))
    val lastBody = ApplyExpr(VarExpr("revDiffLists"),arg)
    val rDLBody = CaseExpr(UnrollExpr(VarExpr("Ls")),
                           "empty", VarExpr("Ls"),
                           "nonempty",lastBody)
    val f1 = FunExpr("revDiffLists","Ls",rType,rType,rDLBody)
    val e = VarExpr("L")
  in
    FunExpr("reverse","L",rType,rType,ApplyExpr(f1,e)) 
  end;

val e4_1 =
  let
    val etest = RollExpr
          (SumExpr
             (Left,UnitExpr,
              Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))));
    val etest2 = RollExpr(
        SumExpr(Right,
                PairExpr(
                  IntExpr(4),
                  RollExpr(
                    SumExpr(Left,UnitExpr,uType))),
                uType));

    val epair = PairExpr(etest,RollExpr(SumExpr(Left,UnitExpr,uType)))
    val epair2 = PairExpr(etest2,RollExpr(SumExpr(Left,UnitExpr,uType)))

    val argExpr = PairExpr(SndExpr(VarExpr("nonempty")),
                           RollExpr(SumExpr(Right, 
                                            PairExpr(FstExpr(VarExpr("nonempty")),
                                                     SndExpr(VarExpr("Ls"))),
                                            uType)))
    (*val lastBody = ApplyExpr(VarExpr("revDiffLists"),argExpr)*)
    (*val lastBody = SndExpr(VarExpr("nonempty"))*)
    (*val lastBody = argExpr*)
    (*val lastBody = CaseExpr(UnrollExpr(FstExpr(argExpr)),
                           "empty", SndExpr(argExpr),
                            "nonempty", VarExpr("revDiffLists"))*)
    (*val lastBody = ApplyExpr(VarExpr("revDiffLists"), epair2)*)
    (*val lastBody = VarExpr("revDiffLists")*)
    val lastBody = SndExpr(VarExpr("nonempty"))

    val rDLBody = CaseExpr(UnrollExpr(FstExpr(VarExpr("Ls"))),
                           "empty", SndExpr(VarExpr("Ls")),
                           "nonempty",lastBody)
    val f1 = FunExpr("revDiffLists","Ls",Prod(rType,rType),rType,rDLBody)
    val e = PairExpr(VarExpr("L"),RollExpr(SumExpr(Left,UnitExpr,uType)))
  in
    FunExpr("reverse","L",rType,rType,ApplyExpr(f1,e)) 
  end;

(* Define e5 to represent 2::3::4::nil, or in diMLazy-Au:
   roll( (inr(2,
              roll( (inr(3,
                         roll( (inr (4, 
                                     roll( (inl ()):uType )
                                    )
                               ):uType
                             )
                        )
                     ):uType
                  )
             )
         ):uType
       )
*)
val e5 = 
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

val e5_1 = RollExpr
          (SumExpr
             (Left,UnitExpr,
              Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))));

val e5_2 = 
      RollExpr(
        SumExpr(Right,
                PairExpr(
                  IntExpr(4),
                  RollExpr(
                    SumExpr(Left,UnitExpr,uType))),
                uType));

val e5_3 =       
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
                uType));

val uTypeAlt = Sum(Unit,Prod(Int,Rec("tv_1",Sum(Unit,Prod(Int,Var("tv_1"))))));

val e5Alt = 
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
                                        SumExpr(Left,UnitExpr,uTypeAlt))),
                                    uType))),
                        uTypeAlt))),
            uType));

(* Define e6 to represent e4(e5) *)
val e6 = ApplyExpr(e4,e5);
val e6_1 = ApplyExpr(e4_1,e5_2);

val pair1 =  PairExpr
    (RollExpr
       (SumExpr
          (Right,
           PairExpr
             (IntExpr 4,
              RollExpr
                (SumExpr
                   (Left,UnitExpr,
                    Sum
                      (Unit,
                       Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))))),
           Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t"))))))),
     RollExpr
       (SumExpr
          (Right,
           PairExpr
             (IntExpr 3,
              RollExpr
                (SumExpr
                   (Left,UnitExpr,
                    Sum
                      (Unit,
                       Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))))),
           Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t"))))))));

val u = UnrollExpr(FstExpr(pair1));

val pair2 = PairExpr
    (e5_3
      ,
     RollExpr
       (SumExpr
          (Right,
           PairExpr
             (IntExpr 3,
              RollExpr
                (SumExpr
                   (Left,UnitExpr,
                    Sum
                      (Unit,
                       Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t")))))))),
           Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t"))))))));
  val argExpr = PairExpr(SndExpr(VarExpr("nonempty")),
                           RollExpr(SumExpr(Right, 
                                            PairExpr(FstExpr(VarExpr("nonempty")),
                                                     SndExpr(VarExpr("Ls"))),
                                            uType)))
    (*val lastBody = ApplyExpr(VarExpr("revDiffLists"),argExpr)*)
    (*val lastBody = SndExpr(VarExpr("nonempty"))*)
    val lastBody = argExpr
    val rDLBody = CaseExpr(UnrollExpr(FstExpr(VarExpr("Ls"))),
                           "empty", SndExpr(VarExpr("Ls")),
                           "nonempty",lastBody)
    val f1 = FunExpr("revDiffLists","Ls",Prod(rType,rType),rType,rDLBody)
    val e = PairExpr(e5,RollExpr(SumExpr(Left,UnitExpr,uType)))

val testing = ApplyExpr(f1, pair2);


(*val rLLType = Rec("tt", Sum(Unit, Prod(rType, Var("tt"))));*)

val uLLType = 
  Sum(
    Unit, 
    Prod(
      Sum(
        Unit, 
        Prod(
          Int,
          Rec("t",Sum(Unit,Prod(Int,Var("t")))))
        ), 
      Rec("tt", 
        Sum(
          Unit, (
            Prod(
              Sum(
                Unit, 
                Prod(Int,Rec("t",Sum(Unit,Prod(Int,Var("t")))))
                ),
              Var("tt")))))));

(*val rType = Rec("t",Sum(Unit,Prod(Int,Var("t"))));*)

val uLLAlt = 
  Sum(
    Unit, 
    Prod(
      rType
      , 
      Rec("tt", 
        Sum(
          Unit, (
            Prod(
              rType,
              Var("tt")))))));

val rLLType = 
  (Rec
    ("tv_0",
      Sum
        (Unit,
        Prod
          (Sum (Unit,Prod (Int,Rec ("t",Sum (Unit,Prod (Int,Var "t"))))),
            Var "tv_0"))))
(*val uLLType = Sum(Unit, Prod(Sum(Unit, Prod(Int,Rec("t",Sum(Unit,Prod(Int,Var("t")))))), 
      Rec("t", Sum(Unit, (Prod(
        Sum(Unit, Prod(Int,Rec("t",Sum(Unit,Prod(Int,Var("t")))))),
        Var("t")))))));*)
        (*(Int, Rec("t", Sum(Unit, Prod(Int, Var("tt"))))))))));*)
      (*Rec("tt", Sum(Unit, (Prod(Int, Rec("t", Sum(Unit, Prod(Int, Var("tt"))))))))));*)


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

val unitLL = 
  RollExpr(
    SumExpr(
      Left,
      UnitExpr, 
      uLLType ))

val unitAlt = 
  RollExpr(
    SumExpr(
      Left,
      UnitExpr, 
      uLLAlt ))

val iLL = 
  RollExpr(
    SumExpr(
      Right,
      PairExpr(
        e5_2,
        unitLL),
      uLLType))

val iLLAlt = 
  RollExpr(
    SumExpr(
      Right,
      PairExpr(
        e5_2,
        unitAlt),
      uLLAlt))

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
            uLLType));

val illExpand = 
  RollExpr(
    SumExpr(
      Right,
      PairExpr(
        
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
                  uType))
         ,

        RollExpr(
          SumExpr(
            Left,
            UnitExpr, 
            uLLAlt ))

        ),
      uLLAlt))

  val typeofe = (Prod(Rec ("tttt",Sum (Unit,Prod (Int,Var "tttt"))),
        Rec ("tttt",Sum (Unit,Prod (Int,Var "tttt")))));

val typeofrev = Prod
             (Rec ("t",Sum (Unit,Prod (Int,Var "t"))),
              Rec ("t",Sum (Unit,Prod (Int,Var "t"))));