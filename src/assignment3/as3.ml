(*
 * Created by atuladhar on 02/21/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment.
 * Name: Anwesh Tuladhar
 *)

(** Declaration of DataTypes for the language. *)
datatype typ = Bool | Int | Arrow of typ * typ;

(** Declaration of  expr types for the language. *)
datatype expr = TrueExpr | FalseExpr | IntExpr of int
    | PlusExpr of expr * expr | LessExpr of expr * expr
    | IfExpr of expr * expr * expr
    | VarExpr of string
    | ApplyExpr of expr * expr
    | FunExpr of string * string * typ * typ * expr;

(** Declaration of Capture Exception*)
exception Capture;

(** Checks whether a given variable is free or not in the provided expression.
  * @param var => The name of the variable for which the check is performed.
  * @param e => the expression in which to check if the variable is free.
  * @returns => true iff var is a free variable in e.
  *)
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

(** Performs the substitution [e/x]e'.
  * @param e => the expression with which to replace all free x's in e'
  * @param x => string representing the variable which is to be replaced in e'
  * @param e' => The expression in which the substitution is to be done.
  * @returns => The expression e' with e replacing all free x's in e'.
  * @throws => Capture expression when a substitution cannot be performed.
  *)
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
      
(** Finds the alpha-equivalent expression with neutral and uniquely named variables.
  * @param expr => the expression for which alpha-equivalent expression is to be found.
  *)
fun uniquifyVars expr = 
  let
    (** Renamees variables based on current scope.
      * @param expr = Input expression in which to rename variables.
      * @param inScope = (string*string) list 
          => where first string is the original name and the second string is the new name.
          => each time a FunExpr is encountered, the inScope list is augmented with the current scope.
          => each time VarExpr is encountered, the variable name is searched for in the inScope list. 
            If found, the corresponding renamed varName is used 
            Else a new neutral and unique name is provided using the count.
      * @param count = integer value to keep track of the number of variables and functions.
      * @returns => (expr*int) => where expr is the same as the input expression but with renamed variables
          and int is the new count after renaming all the variables in that expression.
      *)
    fun uniquify TrueExpr inScope count = (TrueExpr, count)
      | uniquify FalseExpr inScope count = (FalseExpr, count)
      | uniquify (ie as IntExpr(_)) inScope count = (ie, count)
      | uniquify (VarExpr(v)) inScope count = 
          let 
            val (newVar, isInScope) = foldl (fn ((old, new), (newVar, iis)) => 
              if v = old andalso not iis then (new, true) 
              else (newVar, iis)
            ) 
            (("var_"^Int.toString(count)), false) 
            (inScope)
          in 
            (VarExpr(newVar), if isInScope then count else count+1)
          end
      | uniquify (PlusExpr(left, right)) inScope count =
          let 
            val (leftVal, leftCount) = uniquify left inScope count
            val (rightVal, rightCount) = uniquify right inScope leftCount
          in
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
            fun isIn _ nil = false
              | isIn (x:string) ((y,_)::ys) = x=y orelse isIn x ys;

            fun augmentScope nil currentScope = currentScope
              | augmentScope ((p as (old, _))::xs) currentScope = 
                  if isIn old currentScope then 
                    augmentScope xs currentScope
                  else 
                    augmentScope xs (p::currentScope);

            val funPair = (functionName, "fun"^"_"^Int.toString(count))
            val paramPair = (parameterName, "var"^"_"^Int.toString(count))
            val currentScope = augmentScope inScope [funPair, paramPair]
            val (newBody, bodyCount) = uniquify body currentScope (count+1)
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



