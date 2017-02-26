(*
 * Created by atuladhar on 02/21/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment.
 * Name: Anwesh Tuladhar
 *)

datatype typ = Bool | Int | Arrow of typ * typ;

datatype expr = TrueExpr | FalseExpr | IntExpr of int
    | PlusExpr of expr * expr | LessExpr of expr * expr
    | IfExpr of expr * expr * expr
    | VarExpr of string
    | ApplyExpr of expr * expr
    | FunExpr of string * string * typ * typ * expr;

exception Capture;

(*fun isFV expr var = 
  let 
    fun getVarList TrueExpr  vList = vList
      | getVarList FalseExpr vList = vList
      | getVarList (IntExpr(_)) vList = vList
      | getVarList (VarExpr(v)) vList = v::vList
      | getVarList (PlusExpr(left, right)) vList = (getVarList left vList) @ (getVarList right vList)
      | getVarList (LessExpr(left, right)) vList = (getVarList left vList) @ (getVarList right vList)
      | getVarList (IfExpr(condition, thenBranch, elseBranch)) vList = (getVarList condition vList) @ (getVarList thenBranch vList) @ (getVarList elseBranch vList)
      | getVarList (ApplyExpr(function, argument)) vList = (getVarList function vList) @ (getVarList argument vList)
      | getVarList (FunExpr(functionName, parameterName, parameterType, returnType, body)) vList = functionName::parameterName::(getVarList body vList);

    fun checkFV _ nil vCount= vCount < 2
      | checkFV var (v::vs) 0 = 
        if v=var then checkFV var vs 1
        else checkFV var vs 0
      | checkFV (var:string) (v::vs) 1 = 
        if v=var then false
        else checkFV var vs 1
      | checkFV _ _ _ = false;
  in 
    checkFV var (getVarList expr nil) 0
  end;*)

fun isFV TrueExpr _ = false
  | isFV FalseExpr  _ = false
  | isFV (IntExpr(_)) _ = false
  | isFV (VarExpr(v)) var = v=var
  | isFV (PlusExpr(left, right)) var = (isFV left var) orelse (isFV right var)
  | isFV (LessExpr(left, right)) var = (isFV left var) orelse (isFV right var)
  | isFV (IfExpr(condition, thenBranch, elseBranch)) var = 
      (isFV condition var) orelse (isFV thenBranch var) orelse (isFV elseBranch var)
  | isFV (ApplyExpr(function, argument))  var = (isFV function var) orelse  (isFV argument var)
  | isFV (FunExpr(functionName, parameterName, parameterType, returnType, body)) var = 
      ((isFV body var) andalso var <> functionName andalso  var <> parameterName);

fun sub (e:expr) x TrueExpr = TrueExpr
  | sub e x FalseExpr = FalseExpr
  | sub e x (ie as IntExpr(_)) = ie
  | sub e x (ve as VarExpr(v)) = if x=v then e else ve
  | sub e x (PlusExpr(left, right)) = PlusExpr((sub e x left), (sub e x right))
  | sub e x (LessExpr(left, right)) = LessExpr((sub e x left), (sub e x right))
  | sub e x (IfExpr(condition, thenBranch, elseBranch)) = 
      IfExpr((sub e x condition), (sub e x thenBranch), (sub e x elseBranch))
  | sub e x (ApplyExpr(function, argument)) = ApplyExpr((sub e x function), (sub e x argument))
  | sub e x (fe as FunExpr(functionName, parameterName, parameterType, returnType, body)) = 
      if (functionName = x orelse parameterName = x) then fe
      else if (not (isFV e functionName) andalso not (isFV e parameterName)) then
        FunExpr(functionName, parameterName, parameterType, returnType, 
          (sub e x body)
        )
      else raise Capture;

(*fun uniquifyVars expr = 
  let     
    fun uniquify TrueExpr _ = TrueExpr
      | uniquify FalseExpr _ = FalseExpr
      | uniquify (ie as IntExpr(_)) _ = ie
      | uniquify (ve as VarExpr(_)) _ = ve
      | uniquify (PlusExpr(left, right)) count = PlusExpr((sub e x left), (sub e x right))
      | uniquify (LessExpr(left, right)) count = LessExpr((sub e x left), (sub e x right))
      | uniquify (IfExpr(condition, thenBranch, elseBranch)) count = 
          IfExpr((sub e x condition), (sub e x thenBranch), (sub e x elseBranch))
      | uniquify (ApplyExpr(function, argument)) count = ApplyExpr((sub e x function), (sub e x argument))
      | uniquify (fe as FunExpr(functionName, parameterName, parameterType, returnType, body)) count = 
          if (functionName = x orelse parameterName = x) then fe
          else if (not (isFV e functionName) andalso not (isFV e parameterName)) then
            FunExpr(functionName, parameterName, parameterType, returnType, 
              (sub e x body)
            )
          else raise Capture;
  in 
    uniquify expr 101
  end;*)
      
fun uniquifyVars expr = 
  let
    fun uniquify TrueExpr inScope count = (TrueExpr, count)
      | uniquify FalseExpr inScope count = (FalseExpr, count)
      | uniquify (ie as IntExpr(_)) inScope count = (ie, count)
      | uniquify (VarExpr(v)) inScope count = 
          let 
            (*fun rename (v:string) inScope count = *)
              (*if #1(#1 (inScope)) = v then
                #2(#1 (inScope))
              else if #1(#2 (inScope)) = v then
                #2(#2 (inScope))
              else "var_"^Int.toString(count)*)
              
                (*val (newVar, newCount, _) = foldl (fn ((old, new), (newVar, nc, isInScope)) => 
                  if v = old andalso not isInScope then (new, nc, true) 
                  else if isInScope then (newVar, nc, isInScope) 
                  else (newVar, nc+1, isInScope)
                ) 
                (("var_"^Int.toString(count)), count, false) 
                (inScope)*)
                val (newVar, isInScope) = foldl (fn ((old, new), (newVar, iis)) => 
                  (*if v = old andalso not isInScope then (new, true) else (newVar, isInScope)*)
                  if v = old andalso not iis then (new, true) 
                  else (newVar, iis)
                ) 
                (("var_"^Int.toString(count)), false) 
                (inScope)
              
          in 
            (*(VarExpr(rename v inScope count), count+1)*)
            (VarExpr(newVar), if isInScope then count else count+1)
          end
      | uniquify (PlusExpr(left, right)) inScope count =
          let 
            val (leftVal, leftCount) = uniquify left inScope count
            val (rightVal, rightCount) = uniquify right inScope leftCount
          in
            (*(PlusExpr(leftVal, right), count)*)
            (PlusExpr(leftVal, rightVal), rightCount)
          end
      | uniquify (LessExpr(left, right)) inScope count = 
          let 
            val (leftVal, leftCount) = uniquify left inScope count
            val (rightVal, rightCount) = uniquify right inScope leftCount
          in
            (LessExpr(leftVal, rightVal), rightCount)
          end
      | uniquify (IfExpr(condition, thenBranch, elseBranch)) inScope count =
          let 
            val (condVal, condCount) = uniquify condition inScope count
            val (thenVal, thenCount) = uniquify thenBranch inScope condCount
            val (elseVal, elseCount) = uniquify elseBranch inScope thenCount
          in
            (IfExpr(condVal, thenVal, elseVal), elseCount)
          end
      | uniquify (ApplyExpr(function, argument)) inScope count = 
          let 
            val (funVal, funCount) = uniquify function inScope count
            val (argVal, argCount) = uniquify argument inScope funCount
          in
            (ApplyExpr(funVal, argVal), argCount)
          end
      | uniquify (fe as FunExpr(functionName, parameterName, parameterType, returnType, body)) inScope count = 
          let 
            (*val currentScopeList = ((functionName, "fun"^"_"^Int.toString(count)), (parameterName, "var"^"_"^Int.toString(count)))*)
            val funPair = (functionName, "fun"^"_"^Int.toString(count))
            val paramPair = (parameterName, "var"^"_"^Int.toString(count))

            fun isIn _ nil = false
              | isIn (x:string) ((y,_)::ys) = x=y orelse isIn x ys;

            fun augmentScope nil currentScope = currentScope
              | augmentScope ((p as (old, _))::xs) currentScope = 
                  if isIn old currentScope then 
                    augmentScope xs currentScope
                  else 
                    augmentScope xs (p::currentScope);

            val currentScope = augmentScope inScope [funPair, paramPair]
            val (newBody, bodyCount) = uniquify body currentScope (count+1)
            (*val (newBody, bodyCount) = uniquify body [funPair, paramPair] (count+1)*)
          in 
            ( FunExpr(
                #2 funPair,
                #2 paramPair,
                parameterType,
                returnType,
                newBody
              ),
              bodyCount
            )
          end
  in 
    #1(uniquify expr nil 1)
  end;


fun printExpr TrueExpr  = print("true ")
  | printExpr FalseExpr = print("false ")
  | printExpr (IntExpr(i)) = print(Int.toString(i)^" ")
  | printExpr (VarExpr(v)) = print(v)
  | printExpr (PlusExpr(left, right)) = (printExpr(left); print(" + "); printExpr(right))
  | printExpr (LessExpr(left, right)) = (printExpr(left); print(" < "); printExpr(right))
  | printExpr (IfExpr(condition, thenBranch, elseBranch)) = 
    (
      print("if ");
      printExpr(condition); 
      print(" then \n\t");
      printExpr(thenBranch);
      print("\n else \n\t");
      printExpr(elseBranch)
    )
  | printExpr (ApplyExpr(function, argument)) = (printExpr(function); print( "( "); printExpr(argument); print(")"))
  | printExpr (FunExpr(functionName, parameterName, parameterType, returnType, body)) =
      (
        print("\n(fun "^functionName^" ("^parameterName^") = \n\t");
        printExpr(body);
        print("\n)\n")
      );




(*fun f(x) = (x + (fun g (y) = (fun h (za) = h(y)))(g(y) + z)(f(x)));*)
val t = TrueExpr;
val f = FalseExpr;
val i = IntExpr(3);
val v = VarExpr("variable");
val p = PlusExpr(VarExpr("a"), VarExpr("b"));
val l = LessExpr(VarExpr("a"), VarExpr("b"));
val ifExp = IfExpr(LessExpr(VarExpr("a"), IntExpr(5)), PlusExpr(VarExpr("a"), IntExpr(5)), PlusExpr(VarExpr("b"), IntExpr(2)));
val funExp = FunExpr("f", "a", Int, Int, ifExp);

val f1 = FunExpr("loop", "x", Int, Int, ApplyExpr(VarExpr("loop"), VarExpr("x")));
val f2 = ApplyExpr(FunExpr("loop", "x", Int, Int, ApplyExpr(VarExpr("loop"), VarExpr("x"))), IntExpr(5));
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
                    VarExpr("z")) (*false*)
                ),
                ApplyExpr(
                  VarExpr("f"), 
                  VarExpr("x")
                )
              )
            )
          );

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



