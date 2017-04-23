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
    (*fun unroll rType Bool = Bool
      | unroll rType Int = Int
      | unroll rType Unit = Unit
      | unroll rType (vType as Var(t)) = rType
      | unroll rType (Arrow(argType, returnType)) = 
          Arrow((unroll rType argType), (unroll rType returnType))
      | unroll rType (Prod(t1, t2)) = 
          Prod((unroll rType t1), (unroll rType t2))
      | unroll rType (Sum(t1, t2)) = 
          Sum((unroll rType t1), (unroll rType t2))
      | unroll rType (recType as Rec(t, tBody)) = tBody;*)

    fun unroll _ _ Bool = Bool
      | unroll _ _ Int = Int
      | unroll _ _ Unit = Unit
      (*| unroll rType (vType as Var(t)) = rType*)
      | unroll rType tVar (vType as Var(t)) = 
          if tVar = t then rType else vType 
      | unroll rType tVar (Arrow(argType, returnType)) = 
          Arrow((unroll rType tVar argType), (unroll rType tVar returnType))
      | unroll rType tVar (Prod(t1, t2)) = 
          Prod((unroll rType tVar t1), (unroll rType tVar t2))
      | unroll rType tVar (Sum(t1, t2)) = 
          Sum((unroll rType tVar t1), (unroll rType tVar t2))
(*todo: check case for recursive type. Should be ok if maximally rolled???*)
      (*| unroll rType tVar (recType as Rec(t, tBody)) = tBody;*)
      | unroll rType tVar (recType as Rec(t, tBody)) = unroll rType tVar tBody;

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
          if eType = (unroll recType t tBody) then
            (print("replacing with tvar. \n"); tVar)
          else 
            (print("not replacing with tvar.\n"); Rec(t, (subT tVar eType tBody))) ;

      (*fun findPair t nil = NONE
        | findPair t (to, tn)::ts = if t = to then SOME tn else findPair t ts*)

      fun findPair t nil varList count = 
            let val newt = "tv_"^Int.toString(count)
            in (newt, (t, newt)::varList, count+1)
            end
        | findPair t ((to, tn)::ts) varList count = 
            if t = to then (tn, varList, count) else findPair t ts varList count

      fun alphaConvert Bool varList count = (Bool, varList, count)
        | alphaConvert Int varList count = (Int, varList, count)
        | alphaConvert Unit varList count = (Unit, varList, count)
        | alphaConvert (Var(t)) varList count = 
            let val (newt, newVarList, newCount) = findPair t varList varList count
            in (Var(newt), newVarList, newCount)
            end
            (*case findPair t of 
              SOME tn => (Var(tn), varList, count)
              | NONE => ("tv_"^Int.toString(count), (t, tn)::varList, count+1)*)
        | alphaConvert (Arrow(argType, returnType)) varList count = 
            let 
              val (newReturnType, newVarList, newCount) = alphaConvert returnType varList count
              val (newArg, newVarList, newCount) = alphaConvert argType newVarList newCount
            in 
              (Arrow(newArg, newReturnType), newVarList, newCount)
            end

        | alphaConvert (Prod(t1, t2)) varList count = 
            let 
              val (newt1, newVarList, newCount) = alphaConvert t1 varList count
              val (newt2, newVarList, newCount) = alphaConvert t2 newVarList newCount
            in 
              (Prod(newt1, newt2), newVarList, newCount)
            end
        | alphaConvert (Sum (t1, t2)) varList count = 
            let 
              val (newt1, newVarList, newCount) = alphaConvert t1 varList count
              val (newt2, newVarList, newCount) = alphaConvert t2 newVarList newCount
            in 
              (Sum(newt1, newt2), newVarList, newCount)
            end        
        | alphaConvert (Rec(t, tBody)) varList count = 
            let 
              val (newt, newVarList, newCount) = findPair t varList varList count
              val (aTBody, newVarList, newCount) = alphaConvert tBody newVarList newCount
            in (Rec(newt, aTBody), newVarList, newCount)
            end

      fun isAlphaEquivalent e1 e2 =  
        let 
          val (ae1, varList, count) = alphaConvert e1 nil 0
          val (ae2, varList, count) = alphaConvert e1 varList count
        in 
          if ae1 = ae2 then true else false
        end
          




    (*fun findAndSubT eType Bool = Bool
      | findAndSubT eType Int = Int
      | findAndSubT _ _ Unit = Unit
      | findAndSubT eType (vType as Var(_)) = vType
      | findAndSubT eType (Arrow(argType, returnType)) = 
          Arrow((findAndSubT eType argType), (findAndSubT eType returnType))
      | findAndSubT eType (Prod(t1, t2)) = 
          Prod((findAndSubT eType t1), (findAndSubT eType t2))
      | findAndSubT eType (Sum(t1, t2)) = 
          Sum((findAndSubT eType t1), (findAndSubT eType t2))
      | findAndSubT eType (recType as Rec(t, tBody)) = 
          if eType = (unroll recType tBody) then
           
          else 
            Rec(t, (findAndSubT eType tBody));*)

    (** Look for the given variable within the given context 
      * @param var => the variable to search for
      * @param contexts => list of pairs of varName and varType in current context.
      * @returns => option of dataype typ representing the type of var.
                 => NONE if the variable is not found in the given context.
      *)
    fun lookupVar (var:string) nil = NONE
      | lookupVar var ((varName, varType)::contexts) = 
          if var = varName then SOME varType else lookupVar var contexts;

    fun lookupTypeVar (var:string) nil = false
      | lookupTypeVar var (varName::typeContexts) = 
          if var = varName then true else lookupTypeVar var typeContexts;

    fun isValidType t = 
      let
        fun isValid Bool _ = true
          | isValid Int _ = true
          | isValid Unit _ = true
          | isValid (Arrow(argType, returnType)) typeContext = 
            (isValid argType typeContext) andalso (isValid returnType typeContext)
          | isValid (Prod(t1, t2)) typeContext = 
            (isValid t1 typeContext) andalso (isValid t2 typeContext)
          | isValid (Sum(t1, t2)) typeContext = 
            (isValid t1 typeContext) andalso (isValid t2 typeContext)
          | isValid (Var(t)) typeContext = 
            lookupTypeVar t typeContext
          | isValid (Rec(t, tType)) typeContext =
            isValid tType (t::typeContext)
      in
        isValid t nil
      end;
    
    (** Type check the given expression within the context provided.
      * @param expr => the expression to be type checked.
      * @param context => the context within which to type check expr. The context is initialised to nil
          and is augmented by new variables only by the expression FunExpr.
      * @returns => option of datatype typ. The NONE option is returned iff the expression is ill typed.
      *)
    fun typeExpr TrueExpr _ varCount = (SOME Bool, varCount)
      | typeExpr FalseExpr _ varCount = (SOME Bool, varCount)
      | typeExpr (IntExpr(_)) _ varCount = (SOME Int, varCount)
      | typeExpr (PlusExpr(l, r)) context varCount = 
          let 
            val (tl, newCount) = (typeExpr l context varCount)
            val (tr, newCount) = (typeExpr r context newCount)
          in 
            if  tl = SOME Int andalso tr = SOME Int then
              (SOME Int, newCount)
            else 
              (NONE, newCount)
          end
      | typeExpr (LessExpr(l, r)) context varCount = 
          let 
            val (tl, newCount) = (typeExpr l context varCount)
            val (tr, newCount) = (typeExpr r context newCount)
          in 
            if tl = SOME Int andalso tr = SOME Int then
              (SOME Bool, newCount)
            else 
              (NONE, newCount)
          end
      | typeExpr (IfExpr(condition, thenBranch, elseBranch)) context varCount= 
          let 
            val (tcond, newCount) = typeExpr condition context varCount
          in
            if tcond = SOME Bool then
              let 
                val (typeOfThen, newCount) = typeExpr thenBranch context newCount
                val (typeOfElse, newCount) = typeExpr elseBranch context newCount
              in 
                if typeOfThen = typeOfElse then (typeOfThen, newCount)
                else (NONE, newCount)
              end
            else
              (NONE, newCount)
          end
      | typeExpr (VarExpr(v)) context varCount= 
          (lookupVar v context, varCount)

      | typeExpr (FunExpr(funName, paramName, paramType, returnType, body)) context varCount = 
          if isValidType paramType andalso isValidType returnType then
            let 
              val funPair = (funName, Arrow(paramType, returnType));
              val paramPair = (paramName, paramType);
              val currentContext = funPair::paramPair::context
              val (tBody, newCount) = typeExpr body currentContext varCount
            in
              case tBody of
                SOME(t) => 
                  (*if t = returnType then (SOME(#2(funPair)), newCount)*)
                  if isAlphaEquivalent t returnType then (SOME(#2(funPair)), newCount)
                  else (NONE, newCount)
                | NONE => (NONE, newCount)
            end
          else (NONE, varCount)
      | typeExpr (ApplyExpr(func, arg)) context varCount =
          let
             val (tfunc, newCount) = typeExpr func context varCount
             val (targ, newCount) = typeExpr arg context newCount
          in
            case tfunc of
              SOME(Arrow(paramType, returnType)) =>
                (*if targ = SOME paramType then (SOME returnType, newCount)*)
                (case targ of 
                  SOME(t) => 
                    if isAlphaEquivalent t paramType then (SOME returnType, newCount)
                    else (NONE, newCount)
                  | NONE => (NONE, newCount))
              | _ => (NONE, newCount)
          end

      | typeExpr UnitExpr _ varCount = (SOME Unit, varCount)
      | typeExpr (PairExpr(e1, e2)) context varCount = 
          let
            val (t1, newCount) = typeExpr e1 context varCount
            val (t2, newCount) = typeExpr e2 context newCount
          in
            case t1 of 
              SOME(tt1) =>
                (
                  case t2 of 
                    SOME(tt2) => 
                      (SOME(Prod(tt1, tt2)), newCount)
                    | NONE => (NONE, newCount)
                )
              | NONE => (NONE, newCount)
          end
      | typeExpr (FstExpr(pair)) context varCount= 
          let 
            val (tpair, newCount) = typeExpr pair context varCount
          in
            case tpair of 
              SOME(Prod(fst, _)) => (SOME(fst), newCount)
              | _ => (NONE, newCount)
          end
      | typeExpr (SndExpr(pair)) context varCount =
          let 
            val (tpair, newCount) = typeExpr pair context varCount
          in
            case tpair of 
                SOME(Prod(_, snd)) => (SOME(snd), newCount)
                | _ => (NONE, newCount)
          end
       (*| typeExpr (SumExpr(side, e, t as Sum(l, r))) context varCount =
          if isValidType l andalso isValidType r then
            let 
              val (eType, newCount) = typeExpr e context varCount
            in

              case side of 
                    Left => 
                      if eType = SOME l then (SOME t, newCount)
                      else (print("none in inject left\n");(NONE, newCount))
                    | Right =>
                      if eType = SOME r then (SOME t, newCount)
                      else (print("none in inject right\n");(NONE, newCount))
            end
          else (NONE, varCount)*)
      | typeExpr (SumExpr(side, e, t as Sum(l, r))) context varCount =
          if isValidType l andalso isValidType r then
            let 
              val (eType, newCount) = typeExpr e context varCount
            in
              case eType of 
                SOME(et) => 
                  ( 
                    case side of 
                      Left => 
                        if isAlphaEquivalent et l then (SOME t, newCount)
                        else (print("none in inject left\n");(NONE, newCount))
                      | Right =>
                        if isAlphaEquivalent et r then (SOME t, newCount)
                        else (print("none in inject right\n");(NONE, newCount))
                  )
                | NONE => (NONE, newCount)
            end
          else (NONE, varCount)

      | typeExpr (CaseExpr(e, x, e1, y, e2)) context varCount =
          let 
            val (te, newCount) = typeExpr e context varCount
          in
            case te of
              SOME(Sum(l, r)) => 
                let 
                  val e1Context = (x, l)::context
                  val e2Context = (y, r)::context
                  val (e1Type, newCount) = typeExpr e1 e1Context newCount
                  val (e2Type, newCount) = typeExpr e2 e2Context newCount
                in
                  if e1Type = e2Type then (e1Type, newCount)
                  else (NONE, newCount)
                end
              | _ => (NONE, newCount)
          end
      | typeExpr (RollExpr(e)) context varCount = 
          let 
            val (eType, newCount) = typeExpr e context varCount
            val tVar = "tv_"^Int.toString(newCount)
          in 
            case eType of
              SOME(et) =>
              (*todo: This is not Complete!!!*)
                (*(SOME(Rec("t", subT (Var("t")) et et)), newCount)*)
                (*(SOME(Rec("t22", subT (Var("t22")) et et)), newCount)*)
                (SOME(Rec(tVar, subT (Var(tVar)) et et)), newCount+1)
              | NONE => (NONE, newCount)
          end
      | typeExpr (UnrollExpr(e)) context varCount = 
          let 
            val (eType, newCount) = typeExpr e context varCount
          in
            case eType of 
              SOME(rType as Rec(t, tBody)) =>
                (SOME(unroll rType t tBody), newCount)
              | _ => (NONE, newCount)
          end

      | typeExpr other _ varCount = (NONE, varCount);

    (*fun findTVarFor et = *)

  in 
    #1 (typeExpr expr nil 0)
  end;


fun isVal TrueExpr = true
  | isVal FalseExpr = true
  | isVal (IntExpr(_)) = true
  | isVal (FunExpr(_,_,_,_,_)) = true
  | isVal UnitExpr = true
  | isVal (RollExpr(e)) = isVal e
  | isVal (SumExpr(_, e, _)) = isVal e
  | isVal (PairExpr(e1, e2)) = isVal e1 andalso isVal e2
  | isVal _ = false;

fun decompose e = 
  let 
    fun dig TrueExpr = raise Stuck     (*(Hole, f)*)
      | dig FalseExpr = raise Stuck    (*(Hole, f)*)
      | dig UnitExpr = raise Stuck
      | dig (IntExpr(_)) = raise Stuck   (*(Hole, n)*)
      | dig (VarExpr(_)) = raise Stuck
      | dig (FunExpr(_,_,_,_,_)) = raise Stuck
      | dig (SumExpr(Left, e, t)) = 
          let val (ctxt, betaE) = dig e
          in (SumCtxt(Left, ctxt, t), betaE)
          end
      | dig (SumExpr(Right, e, t)) = 
          let val (ctxt, betaE) = dig e
          in (SumCtxt(Right, ctxt, t), betaE)
          end
      | dig (PairExpr(e1, e2)) = 
          if isVal e2 then
            let val (ctxt, betaE) = dig e1
            in (PairCtxt2(ctxt, e2), betaE)
            end
          else 
            let val (ctxt, betaE) = dig e2
            in (PairCtxt1(e1, ctxt), betaE)
            end
      | dig (pe as PlusExpr(IntExpr(_), IntExpr(_))) = (Hole, pe) 
      | dig (PlusExpr(l, IntExpr(i))) = 
          let val (ctxt, betaE) = dig l
          in (PlusCtxt2(ctxt, i), betaE)
          end
      | dig (pe as PlusExpr(l, r)) = 
          let val (ctxt, betaE) = dig r
          in (PlusCtxt1(l, ctxt), betaE)
          end 
      | dig (le as LessExpr(IntExpr(_), IntExpr(_))) = (Hole, le) 
      | dig (LessExpr(l, IntExpr(i))) = 
          let val (ctxt, betaE) = dig l
          in (LessCtxt2(ctxt, i), betaE)
          end
      | dig (le as LessExpr(l, r)) = 
          let val (ctxt, betaE) = dig r
          in (LessCtxt1(l, ctxt), betaE)
          end 
      | dig (ite as IfExpr(TrueExpr, _, _)) = (Hole, ite) 
      | dig (ite as IfExpr(FalseExpr, _, _)) = (Hole, ite)
      | dig (ite as IfExpr(condition, thenBranch, elseBranch)) = 
          let val (ctxt, betaE) = dig condition
          in (IfCtxt(ctxt, thenBranch, elseBranch), betaE)
          end 
      | dig (ae as ApplyExpr(FunExpr(_,_,_,_,_), arg)) = (Hole, ae)
      | dig (ApplyExpr(func, arg)) = 
          let val (ctxt, betaE) = dig func
          in (ApplyCtxt(ctxt, arg), betaE)
          end  

      | dig (fst as FstExpr(PairExpr(_, _))) = (Hole, fst)
      | dig (FstExpr(pair)) =  
          let val (ctxt, betaE) = dig pair
          in (FstCtxt(ctxt), betaE)
          end
      | dig (snd as SndExpr(PairExpr(_, _))) = (Hole, snd)
      | dig (SndExpr(pair)) =  
          let val (ctxt, betaE) = dig pair
          in (SndCtxt(ctxt), betaE)
          end
      | dig (ce as CaseExpr(SumExpr(_,_,_), _,_,_,_)) = (Hole, ce)
      | dig (ce as CaseExpr(e, x1, e1, x2, e2)) = 
          let val (ctxt, betaE) = dig e
          in (CaseCtxt(ctxt, x1, e1, x2, e2), betaE)
          end
      | dig (RollExpr(e)) = (*Roll of a value will be stuck*)
          let val (ctxt, betaE) = dig e
          in (RollCtxt(ctxt), betaE)
          end      
      (*| dig (ue as UnrollExpr(RollExpr(_))) = (print("dig unroll hole\n"); (Hole, ue))*)
      | dig (ue as UnrollExpr(r as RollExpr(e))) = 
            if isVal e then (Hole, ue)
            else 
              let val (ctxt, betaE) = dig r
              in (UnrollCtxt(ctxt), betaE)
              end
      | dig (UnrollExpr(e)) = 
          let val (ctxt, betaE) = dig e
          in (UnrollCtxt(ctxt), betaE)
          end;
  in
    dig e
  end;

fun fill Hole e = e
  | fill (PlusCtxt1(l, ctxt)) e = PlusExpr(l, fill ctxt e) 
  | fill (PlusCtxt2(ctxt, r)) e = PlusExpr(fill ctxt e, IntExpr(r)) 
  | fill (LessCtxt1(l, ctxt)) e = LessExpr(l, fill ctxt e)
  | fill (LessCtxt2(ctxt, r)) e = LessExpr(fill ctxt e, IntExpr(r))
  | fill (IfCtxt(ctxt, tb, eb)) e = IfExpr(fill ctxt e, tb, eb)
  | fill (ApplyCtxt(ctxt, arg)) e = ApplyExpr(fill ctxt e, arg)
  | fill (PairCtxt1(e1, ctxt)) e = PairExpr(e1, fill ctxt e)
  | fill (PairCtxt2(ctxt, e2)) e = PairExpr(fill ctxt e, e2)
  | fill (FstCtxt(ctxt)) e = FstExpr(fill ctxt e)
  | fill (SndCtxt(ctxt)) e = SndExpr(fill ctxt e)
  | fill (SumCtxt(side, ctxt, typ)) e = SumExpr(side, fill ctxt e, typ)
  | fill (CaseCtxt(ctxt, x1, e1, x2, e2)) e = CaseExpr(fill ctxt e, x1, e1, x2, e2)
  | fill (RollCtxt(ctxt)) e = RollExpr(fill ctxt e)
  | fill (UnrollCtxt(ctxt)) e = UnrollExpr(fill ctxt e)

fun beta e =
  let
    fun sub (e:expr) x TrueExpr = TrueExpr
      | sub e x FalseExpr = FalseExpr
      | sub e x UnitExpr = UnitExpr
      | sub e x (ie as IntExpr(_)) = ie
      | sub e x (ve as VarExpr(v)) = if x=v then e else ve
      | sub e x (PlusExpr(left, right)) = PlusExpr((sub e x left), (sub e x right))
      | sub e x (LessExpr(left, right)) = LessExpr((sub e x left), (sub e x right))
      | sub e x (IfExpr(condition, thenBranch, elseBranch)) = 
          IfExpr((sub e x condition), (sub e x thenBranch), (sub e x elseBranch))
      | sub e x (ApplyExpr(function, argument)) = ApplyExpr((sub e x function), (sub e x argument))
      | sub e x (fe as FunExpr(functionName, parameterName, parameterType, returnType, body)) = 
          if (functionName = x orelse parameterName = x) then fe
          else 
            FunExpr(functionName, parameterName, parameterType, returnType, 
              (sub e x body)
            )
      | sub e x (PairExpr(e1, e2)) = PairExpr(sub e x e1, sub e x e2)
      | sub e x (FstExpr(expr)) = FstExpr(sub e x expr)
      | sub e x (SndExpr(expr)) = SndExpr(sub e x expr)
      | sub e x (SumExpr(side, expr, typ)) = SumExpr(side, sub e x expr, typ)
      | sub e x (CaseExpr(expr, x1, e1, x2, e2)) = 
          let 
            val subbedE = sub e x expr
            val subbedE1 = if x = x1 then e1 else sub e x e1
            val subbedE2 = if x = x2 then e2 else sub e x e2 
          in CaseExpr(subbedE, x1, subbedE1, x2, subbedE2)
          end
      | sub e x (RollExpr(expr)) = RollExpr(sub e x expr)
      | sub e x (UnrollExpr(expr)) = UnrollExpr(sub e x expr);

    fun betaStep (PlusExpr(IntExpr(l), IntExpr(r))) = IntExpr(l + r)
      | betaStep (LessExpr(IntExpr(l), IntExpr(r))) = if l < r then TrueExpr else FalseExpr
      | betaStep (IfExpr(TrueExpr, thenBranch, _)) = thenBranch
      | betaStep (IfExpr(FalseExpr, _, elseBranch)) = elseBranch
      | betaStep (ApplyExpr(f as FunExpr(funName, paramName, paramType, returnType, body), arg)) = 
          if funName = paramName then raise Stuck
          else (sub arg paramName (sub f funName body) )
      | betaStep (FstExpr(PairExpr(fst, _))) = fst
      | betaStep (SndExpr(PairExpr(_, snd))) = snd
      | betaStep (CaseExpr(SumExpr(Left, e, _), x1, e1,_,_)) = sub e x1 e1
      | betaStep (CaseExpr(SumExpr(Right, e, _), _,_, x2, e2)) = sub e x2 e2
      | betaStep (UnrollExpr(RollExpr(e))) = e
      | betaStep _ = raise Stuck
  in
    betaStep e
  end

fun smallStep e = 
  let   
    val (ctxt, betaE) = decompose e
    val betaSteppedE = beta betaE
  in 
    fill ctxt betaSteppedE
  end

fun bigStep e =
  let 
    val next = if not (isVal e ) then smallStep e else e
  in 
    if not (isVal next) then bigStep next else next
  end



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