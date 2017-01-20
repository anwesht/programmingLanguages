(*
 * Created by atuladhar on 01/19/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment
 * Name: Anwesh Tuladhar
 *)

(** Prints the polynomial in human readable form.
  * @param P => int list list representation of the polynomial
  *)
fun printxy(P) = 
  let 
    (** Prints the formatted value of the coeficient 
      * @param c => coefficient
      * @param isFirst: bool => Flag to check for first position
      *)
    fun printCoef(0, _) = print("")
      | printCoef(1, true) = print(Int.toString(1))
      | printCoef(~1, true) = (
          print (" -");
          print(Int.toString(1))
        ) 
      | printCoef(1, false) = print(" + ")
      | printCoef(~1, false) = print (" -")   
      | printCoef(c: int, true) = (
          if c<0 then (
            print (" - ");
            print(Int.toString(~1*c))
          )  
          else ( 
            print(Int.toString(c))
          )
        )
      | printCoef(c: int, false) = (
          if c<0 then (
            print (" - ");
            print(Int.toString(~1*c))
          )  
          else ( 
            print(" + ");
            print(Int.toString(c))
          )
      );

    (** print x then the y part of the polynomial
      * @param x::xs => polynomial in x = inner int list
      * @param e => exponent of x
      * @param y => string representing the y portion of the polynomial
      *)
    fun print_xWithy(nil, e, y:string) = print("")
      | print_xWithy(x::xs, 0, y:string) = (
          if x=0 then (
            print("")
          )
          else (
            if y<>"" then printCoef(x, false)
            else printCoef(x, true);
            print(y)
          );
          print_xWithy(xs, 1, y)
        )
      | print_xWithy(x::xs, 1, y:string) = (
          printCoef(x, false);
          if x=0 then (
            print("")
          )
          else (
            print("x");
            print(y)
          );
          print_xWithy(xs, 2, y)         
        ) 
      | print_xWithy(x::xs, e, y:string) = (
          if x=0 then (
            print("")
          )
          else (
            printCoef(x, false);
            print("x"); 
            print("^"); 
            print(Int.toString(e));
            print(y)
          ); 
          
          print_xWithy(xs, e+1, y)
        );

    (** Evaluates the y portion of the polynomial and calls print_xWithy *)
    fun print_xy(nil, ey) = (
          if ey=0 then print(Int.toString(0))
          else  print("")
        )
      | print_xy(y::ys, 0) = (
          print_xWithy(y, 0, "");
          print_xy(ys, 1) 
        )
      | print_xy(y::ys, 1) = (
          print_xWithy(y, 0, "y");
          print_xy(ys, 2)
        )
      | print_xy(y::ys, ey) = (
          print_xWithy(y, 0, "y^"^Int.toString(ey));
          print_xy(ys, ey+1)
        )
  in 
    print_xy(P, 0);
    print("\n")
  end;
    

(** Evaluates the value of the polynomial, given the values of x and y
  * @param P => int list list representation of polynomial in x and y
  * @param xVal => value of x
  * @param yVal => value of y
  *)
fun evalxy(P, xVal, yVal) = 
  let 
    fun evalPower(base, 0) = 1
      | evalPower(base, exp) = base * evalPower(base, exp - 1); 
  
    fun eval_xWithy(nil, _, _, _) = 0
      | eval_xWithy(x::xs, xVal, expX, yVal) = 
        (x * evalPower(xVal, expX) * yVal) + eval_xWithy(xs, xVal, expX+1, yVal);

    fun eval_xy(nil, _, _, _) = 0
      | eval_xy(xy::xys, xVal, yVal, expY) = 
        eval_xWithy(xy, xVal, 0, evalPower(yVal, expY)) + eval_xy(xys, xVal, yVal, expY+1)
  in 
    eval_xy(P, xVal, yVal, 0)
  end;
  
(** Evaluates the sum of two polynomials in x and y
  * @param P => int list list representation of the first polynomial in x and y
  * @param Q => int list list representation of the second polynomial in x and y
  *)
fun paddxy(P, nil) = P
  | paddxy(nil, Q) = Q
  | paddxy(p::ps, q::qs) = 
    let 
      (** Helper function to sum the inner int lists *)
      fun paddx(P, nil) = P
      | paddx(nil, Q) = Q
      | paddx((p:int)::ps, q::qs) = (p + q)::paddx(ps, qs);
    in 
      (** Recursively sum corresponding values of two polynomials *)
      paddx(p, q)::paddxy(ps, qs)
    end;

(** Evaluates the multiplication of two polynomials in x and y
  * @param P => int list list representation of the first polynomial in x and y
  * @param Q => int list list representation of the second polynomial in x and y
  *)
fun multxy(nil, _) = nil
  | multxy(xy::xys, mult) = 
    let
      (** Helper function to multiply the inner int list with a scalar
        * @param x::xs => int list (inner)
        * @param mult => the scalar value
        *)
      fun multx(nil, _) = nil
        | multx(x::xs, mult) = (x * mult)::multx(xs, mult)
    in
      (* Multiply the head of the list (i.e. innerlist) with the scalar
        and construct the int list list*)
      multx(xy, mult)::multxy(xys, mult)
    end

(** Evaluates the multiplication of two polynomials in x and y
  * @param P => int list list representation of the first polynomial in x and y
  * @param Q => int list list representation of the second polynomial in x and y
  *)
fun pmultxy(_, nil) = nil
  | pmultxy(nil, _) = nil
  | pmultxy(P, q::qs) = 
    let 
      (** Helper function to multiply the inner int lists.
        * PQ = P*q + qs*x ==> qs*x is obtained by shifting to the right
        *)
      fun pmult(P, nil) = nil
        | pmult(P, q::qs) = padd(smult(P, q), 0::pmult(P, qs));

      (** Helper function to multiply the first polynomial in x and y 
        * with an inner list.
        * @param P => int list list (polynomial in x and y)
        * @param q => int list (the inner int list)  
        *)
      fun pmultx(P, nil) = P
        | pmultx(nil, _) = nil
        | pmultx((p:int list)::ps, q: int list) = 
        (** Construct the intermediate product of polynomial P with the coefficient and x variable.
          * This represents => P * q, where q = inner int list
          *)
        pmult(p, q)::pmultx(ps, q);
    in
      (** pmultx(P, q) returns P * q i.e. P * (only x part)
        * Shifting to the right represents the multiplication by y.
        *)
      paddxy(pmultx(P, q), nil::pmultxy(P, qs))
    end;
