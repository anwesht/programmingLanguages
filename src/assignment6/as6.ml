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
    (** Finds the mapping from old t to new t.*)
    fun findPair (t:string) nil varList count = 
          let val newt = "tv_"^Int.toString(count)
          in (newt, (t, newt)::varList, count+1)
          end
      | findPair t ((to, tn)::ts) varList count = 
          if t = to then (tn, varList, count) else findPair t ts varList count

    (** Renames type variables *)
    fun alphaConvert Bool varList count = (Bool, varList, count)
      | alphaConvert Int varList count = (Int, varList, count)
      | alphaConvert Unit varList count = (Unit, varList, count)
      | alphaConvert (Var(t)) varList count = 
          let val (newt, newVarList, newCount) = findPair t varList varList count
          in (Var(newt), newVarList, newCount)
          end
      | alphaConvert (Arrow(argType, returnType)) varList count = 
          let 
            val (newReturnType, newVarList, newCount) = alphaConvert returnType varList count
            val (newArg, newVarList, newCount) = alphaConvert argType varList count
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

    (** Checks for alpha equivalence of two types by alpha converting them to a fresh third variable.*)
    fun isAlphaEquivalent (e1:typ) (e2:typ) =  
      let 
        val (ae1, varList, count) = alphaConvert e1 nil 0
        val (ae2, varList, count) = alphaConvert e2 nil 0
      in 
        if ae1 = ae2 then true
        else false
      end;

    (** wrapper for isAlphaEquivalent*)
    fun isAlphaEquivalent1 (SOME(e1)) (SOME(e2)) = isAlphaEquivalent e1 e2 
      | isAlphaEquivalent1 _ _ = false

    (** Unrolls a rolled type.*)
    fun unroll _ _ Bool = Bool
      | unroll _ _ Int = Int
      | unroll _ _ Unit = Unit
      | unroll rType tVar (vType as Var(t)) = 
          if tVar = t then rType else vType 
      | unroll rType tVar (Arrow(argType, returnType)) = 
          Arrow((unroll rType tVar argType), (unroll rType tVar returnType))
      | unroll rType tVar (Prod(t1, t2)) = 
          Prod((unroll rType tVar t1), (unroll rType tVar t2))
      | unroll rType tVar (Sum(t1, t2)) = 
          Sum((unroll rType tVar t1), (unroll rType tVar t2))
      | unroll rType tVar (recType as Rec(t, tBody)) = recType;

    (** Performs a substitution of Var for expression e if a is alpha equivalent to eType*)
    fun maximalSub eType varType Bool = Bool
      | maximalSub eType varType Int = Int
      | maximalSub eType varType (Arrow(argType, returnType)) = 
          Arrow(maximalSub eType varType argType, maximalSub eType varType returnType)
      | maximalSub eType varType Unit = Unit
      | maximalSub eType varType (Prod(t1, t2)) = 
          Prod(maximalSub eType varType t1, maximalSub eType varType t2)
      | maximalSub eType varType (Sum(t1, t2)) = 
          Sum(maximalSub eType varType t1, maximalSub eType varType t2)
      | maximalSub eType varType (v as Var(t)) = v
      | maximalSub eType varType (rType as Rec(t, tBody)) = 
          let 
            val unrolled = unroll rType t tBody
          in 
            if isAlphaEquivalent eType unrolled then varType
            else rType
          end

    (** Look for the given variable within the given context 
      * @param var => the variable to search for
      * @param contexts => list of pairs of varName and varType in current context.
      * @returns => option of dataype typ representing the type of var.
                 => NONE if the variable is not found in the given context.
      *)
    fun lookupVar (var:string) nil = NONE
      | lookupVar var ((varName, varType)::contexts) = 
          if var = varName then SOME varType else lookupVar var contexts;

    (** Similar to lookupVar. Looks for type variables.*)
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
          and is augmented by new variables by expressions FunExpr and CaseExpr.
      * @param count => keeps track of the number of typevariables.
      * @returns => option of datatype typ. The NONE option is returned iff the expression is ill typed.
      *)
    fun typeExpr TrueExpr _ varContext varCount = (SOME Bool, varCount)
      | typeExpr FalseExpr _ varContext varCount = (SOME Bool, varCount)
      | typeExpr (IntExpr(_)) _ varContext varCount = (SOME Int, varCount)
      | typeExpr (PlusExpr(l, r)) context varContext varCount = 
          let 
            val (tl, newCount) = (typeExpr l context varContext varCount)
            val (tr, newCount) = (typeExpr r context varContext newCount)
          in 
            if  tl = SOME Int andalso tr = SOME Int then
              (SOME Int, newCount)
            else 
              (NONE, newCount)
          end
      | typeExpr (LessExpr(l, r)) context varContext varCount = 
          let 
            val (tl, newCount) = (typeExpr l context varContext varCount)
            val (tr, newCount) = (typeExpr r context varContext newCount)
          in 
            if tl = SOME Int andalso tr = SOME Int then
              (SOME Bool, newCount)
            else 
              (NONE, newCount)
          end
      | typeExpr (IfExpr(condition, thenBranch, elseBranch)) context varContext varCount = 
          let 
            val (tcond, newCount) = typeExpr condition context varContext varCount
          in
            if tcond = SOME Bool then
              let 
                val (typeOfThen, newCount) = typeExpr thenBranch context varContext newCount
                val (typeOfElse, newCount) = typeExpr elseBranch context varContext newCount
              in 
                if isAlphaEquivalent1 typeOfThen typeOfElse then (typeOfThen, newCount)
                else (NONE, newCount)
              end
            else
              (NONE, newCount)
          end
      | typeExpr (VarExpr(v)) context varContext varCount = 
          (lookupVar v context, varCount)

      | typeExpr (FunExpr(funName, paramName, paramType, returnType, body)) context varContext varCount = 
          if isValidType paramType andalso isValidType returnType then
            let 
              val funPair = (funName, Arrow(paramType, returnType));
              val paramPair = (paramName, paramType);
              val currentContext = funPair::paramPair::context
              val (tBody, newCount) = typeExpr body currentContext varContext varCount
            in
              case tBody of
                SOME(t) => 
                  if isAlphaEquivalent t returnType then (SOME(#2(funPair)), newCount)
                  else (NONE, newCount)
                | NONE => (NONE, newCount)
            end
          else (NONE, varCount)
      | typeExpr (ApplyExpr(func, arg)) context varContext varCount =
          let
             val (tfunc, newCount) = typeExpr func context varContext varCount
             val (targ, newCount) = typeExpr arg context varContext newCount
          in
            case tfunc of
              SOME(Arrow(paramType, returnType)) =>
                (case targ of 
                  SOME(t) => 
                    if isAlphaEquivalent t paramType then (SOME returnType, newCount)
                    else (SOME t, newCount)
                  | NONE => (NONE, newCount))
              | _ => (NONE, newCount)
          end

      | typeExpr UnitExpr _ varContext varCount = (SOME Unit, varCount)
      | typeExpr (PairExpr(e1, e2)) context varContext varCount = 
          let
            val (t1, newCount) = typeExpr e1 context varContext varCount
            val (t2, newCount) = typeExpr e2 context varContext newCount
          in
            case t1 of 
              SOME(tt1) =>
                (
                  case t2 of 
                    SOME(tt2) => 
                      if isAlphaEquivalent tt1 tt2 then (SOME(Prod(tt1, tt1)), newCount)
                      else (SOME(Prod(tt1, tt2)), newCount)
                    | NONE => (NONE, newCount)
                )
              | NONE => (NONE, newCount)
          end
      | typeExpr (FstExpr(pair)) context varContext varCount = 
          let 
            val (tpair, newCount) = typeExpr pair context varContext varCount
          in
            case tpair of 
              SOME(Prod(fst, _)) => (SOME(fst), newCount)
              | _ => (NONE, newCount)
          end
      | typeExpr (SndExpr(pair)) context varContext varCount =
          let 
            val (tpair, newCount) = typeExpr pair context varContext varCount
          in
            case tpair of 
                SOME(Prod(_, snd)) => (SOME(snd), newCount)
                | _ => (NONE, newCount)
          end
      | typeExpr (SumExpr(side, e, t as Sum(l, r))) context varContext varCount =
          if isValidType l andalso isValidType r then
            let 
              val (eType, newCount) = typeExpr e context varContext varCount
            in
              case eType of 
                SOME(et) => 
                  ( 
                    case side of 
                      Left => 
                        if isAlphaEquivalent et l then (SOME t, newCount)
                        else (NONE, newCount)
                      | Right =>
                        if isAlphaEquivalent et r then (SOME t, newCount)
                        else (NONE, newCount)
                  )
                | NONE => (NONE, newCount)
            end
          else (NONE, varCount)

      | typeExpr (CaseExpr(e, x, e1, y, e2)) context varContext varCount =
          let 
            val (te, newCount) = typeExpr e context varContext varCount
          in
            case te of
              SOME(Sum(l, r)) => 
                let 
                  val e1Context = (x, l)::context
                  val e2Context = (y, r)::context
                  val (e1Type, newCount) = typeExpr e1 e1Context varContext newCount
                  val (e2Type, newCount) = typeExpr e2 e2Context varContext newCount
                in
                  if isAlphaEquivalent1 e1Type e2Type then (e1Type, newCount)
                  else (NONE, newCount)
                end
              | _ => (NONE, newCount)
          end
      | typeExpr (RollExpr(e)) context varContext varCount = 
          let 
            val (eType, newCount) = typeExpr e context varContext varCount
            val tVar = "tv_"^Int.toString(newCount)
          in 
            case eType of
              SOME(et) =>
                (SOME(Rec(tVar, maximalSub et (Var(tVar)) et)), newCount+1)
              | NONE => (NONE, newCount)
          end
      | typeExpr (UnrollExpr(e)) context varContext varCount = 
          let 
            val (eType, newCount) = typeExpr e context varContext varCount
          in
            case eType of 
              SOME(rType as Rec(t, tBody)) =>
                (SOME(unroll rType t tBody), newCount)
              | _ => (NONE, newCount)
          end;
  in 
    #1 (typeExpr expr nil nil 0)
  end;


(** Returns true iff the given expression is a value.
  * @param e => the expression to check
  * @returns => boolean
  *)
fun isVal TrueExpr = true
  | isVal FalseExpr = true
  | isVal (IntExpr(_)) = true
  | isVal (FunExpr(_,_,_,_,_)) = true
  | isVal UnitExpr = true
  | isVal (RollExpr(e)) = isVal e
  | isVal (SumExpr(_, e, _)) = isVal e
  | isVal (PairExpr(e1, e2)) = isVal e1 andalso isVal e2
  | isVal _ = false;

(** Introduces an evaluation context such that e = E[e'] 
    and e' can take a beta step.
  * @param e => expression to be decomposed.
  * @returns (E, e') => E = evaluation context
                     => e' = redex
  * @throws => exception Stuck if e' cannot be found.
  *)
fun decompose TrueExpr = raise Stuck 
  | decompose FalseExpr = raise Stuck
  | decompose UnitExpr = raise Stuck
  | decompose (IntExpr(_)) = raise Stuck   
  | decompose (VarExpr(_)) = raise Stuck
  | decompose (FunExpr(_,_,_,_,_)) = raise Stuck
  | decompose (SumExpr(Left, e, t)) = 
      let val (ctxt, betaE) = decompose e
      in (SumCtxt(Left, ctxt, t), betaE)
      end
  | decompose (SumExpr(Right, e, t)) = 
      let val (ctxt, betaE) = decompose e
      in (SumCtxt(Right, ctxt, t), betaE)
      end
  | decompose (PairExpr(e1, e2)) = 
      if isVal e2 then
        let val (ctxt, betaE) = decompose e1
        in (PairCtxt2(ctxt, e2), betaE)
        end
      else 
        let val (ctxt, betaE) = decompose e2
        in (PairCtxt1(e1, ctxt), betaE)
        end
  | decompose (pe as PlusExpr(IntExpr(_), IntExpr(_))) = (Hole, pe) 
  | decompose (PlusExpr(l, IntExpr(i))) = 
      let val (ctxt, betaE) = decompose l
      in (PlusCtxt2(ctxt, i), betaE)
      end
  | decompose (pe as PlusExpr(l, r)) = 
      let val (ctxt, betaE) = decompose r
      in (PlusCtxt1(l, ctxt), betaE)
      end 
  | decompose (le as LessExpr(IntExpr(_), IntExpr(_))) = (Hole, le) 
  | decompose (LessExpr(l, IntExpr(i))) = 
      let val (ctxt, betaE) = decompose l
      in (LessCtxt2(ctxt, i), betaE)
      end
  | decompose (le as LessExpr(l, r)) = 
      let val (ctxt, betaE) = decompose r
      in (LessCtxt1(l, ctxt), betaE)
      end 
  | decompose (ite as IfExpr(TrueExpr, _, _)) = (Hole, ite) 
  | decompose (ite as IfExpr(FalseExpr, _, _)) = (Hole, ite)
  | decompose (ite as IfExpr(condition, thenBranch, elseBranch)) = 
      let val (ctxt, betaE) = decompose condition
      in (IfCtxt(ctxt, thenBranch, elseBranch), betaE)
      end 
  | decompose (ae as ApplyExpr(FunExpr(_,_,_,_,_), arg)) = (Hole, ae)
  | decompose (ApplyExpr(func, arg)) = 
      let val (ctxt, betaE) = decompose func
      in (ApplyCtxt(ctxt, arg), betaE)
      end  
  | decompose (fst as FstExpr(PairExpr(_, _))) = (Hole, fst)
  | decompose (FstExpr(pair)) =  
      let val (ctxt, betaE) = decompose pair
      in (FstCtxt(ctxt), betaE)
      end
  | decompose (snd as SndExpr(PairExpr(_, _))) = (Hole, snd)
  | decompose (SndExpr(pair)) =  
      let val (ctxt, betaE) = decompose pair
      in (SndCtxt(ctxt), betaE)
      end
  | decompose (ce as CaseExpr(SumExpr(_,_,_), _,_,_,_)) = (Hole, ce)
  | decompose (ce as CaseExpr(e, x1, e1, x2, e2)) = 
      let val (ctxt, betaE) = decompose e
      in (CaseCtxt(ctxt, x1, e1, x2, e2), betaE)
      end
  | decompose (RollExpr(e)) =
      let val (ctxt, betaE) = decompose e
      in (RollCtxt(ctxt), betaE)
      end      
  | decompose (ue as UnrollExpr(r as RollExpr(e))) = 
        if isVal e then (Hole, ue)
        else 
          let val (ctxt, betaE) = decompose r
          in (UnrollCtxt(ctxt), betaE)
          end
  | decompose (UnrollExpr(e)) = 
      let val (ctxt, betaE) = decompose e
      in (UnrollCtxt(ctxt), betaE)
      end;

(** Replaces the hole in an evaluation context with the expression e.
  * @param ctxt => The evaluation context whose hole is to be filled.
  * @param e => The expression with which to fill the hole.
  * @returns => E[e]
  *)
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

(** Perform Beta step of e. 
  * @param e => expression to beta step
  * @returns => e' = expression after beta stepping e. e' can be a value
  * @throws => Exception Stuck if e cannot beta step 
  *)
fun beta e =
  let
    (** Implements [e/x]e' *)
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

    (** Implements the beta stepping of e. *)
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

(** Takes an expression e, decomposes it to find the execution context, 
    takes a single beta step and returns the execution context filled with
    beta stepped expression. 
  * @param e => expression to step
  * @returns => e after taking a step
  * @throws => Exception Stuck if no step is possible.
  *)
fun smallStep e = 
  let   
    val (ctxt, betaE) = decompose e
    val betaSteppedE = beta betaE
  in 
    fill ctxt betaSteppedE
  end

(** Fully evaluates an expression e i.e. takes small steps as long as it is possible.
  * @param e => expression to evaluate
  * @returns => fully evaluated expression
  * @throws => Exception Stuck 
  *)
fun bigStep e =
  let 
    val next = if not (isVal e ) then smallStep e else e
  in 
    if not (isVal next) then bigStep next else next
  end