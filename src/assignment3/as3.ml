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



