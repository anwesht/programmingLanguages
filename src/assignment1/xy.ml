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
    (** Returns the formatted value of the coefficient 
      * @param c => coefficient
      * @param isFirst: bool => Flag to check for first position
      *)
    fun printCoef(0, _, _) = ""
      | printCoef(1, true, _) = "1"
      | printCoef(~1, true, _) = " -1"
      | printCoef(1, false, 0) = ""
      | printCoef(1, false, _) = " + "
      | printCoef(~1, false, _) = " -"
      | printCoef(c: int, true, _) = (
          if c < 0 then " -"^Int.toString(~1 * c)
          else Int.toString(c)
        )
      | printCoef(c: int, false, 0) = (
          if c < 0 then " - "^Int.toString(~1 * c)
          else Int.toString(c)
        )
      | printCoef(c: int, false, _) = (
          if c < 0 then " - "^Int.toString(~1 * c)
          else " + "^Int.toString(c)
        )

    (** Concat x then the y part of the polynomial
      * @param x::xs => polynomial in x = inner int list
      * @param e => exponent of x
      * @param y => string representing the y portion of the polynomial
      * @param out => the output string 
      *)
    fun print_xWithy(nil, _, _, out) = out
      | print_xWithy(x::xs, 0, y:string, out) = (
          if x=0 then print_xWithy(xs, 1, y, out)
          else 
            if y<>"" then print_xWithy(xs, 1, y, out@[printCoef(x, false, length out)]@[y])
            else print_xWithy(xs, 1, y, out@[printCoef(x, true, length out)]@[y])
        )
      | print_xWithy(x::xs, 1, y:string, out) = (
          if x=0 then print_xWithy(xs, 2, y, out)  
          else print_xWithy(xs, 2, y, out@[printCoef(x, false, length out)]@["x", y])
        ) 
      | print_xWithy(x::xs, e, y:string, out) = (
          if x=0 then print_xWithy(xs, e+1, y, out)
          else 
            print_xWithy(xs, e+1, y, out@[printCoef(x, false, length out)]@["x", "^", Int.toString(e), y])
        );

    (** Evaluates the y portion of the polynomial and calls print_xWithy 
      * @param y::ys => polynomial in x and y
      * @param ey => exponent of y
      *)
    fun print_xy(nil, ey, out: string list) = (
          if length out = 0 then [Int.toString(0)]
          else  out
        )
      | print_xy(y::ys, 0, out: string list) = (
          print_xy(ys, 1, out@print_xWithy(y, 0, "", nil)) 
        )
      | print_xy(y::ys, 1, out: string list) = (
          print_xy(ys, 2, out@print_xWithy(y, 0, "y", nil))
        )
      | print_xy(y::ys, ey, out: string list) = (
          print_xy(ys, ey+1, out@print_xWithy(y, 0, "y^"^Int.toString(ey), nil))
        )

    (** Prints the contents of a string list *)
    fun printList(nil) = print("\n")
      | printList(x::xs: string list) = (
        print(x);
        printList(xs)
      )
  in 
    printList(print_xy(P, 0, nil))
  end;
    

(** Evaluates the value of the polynomial, given the values of x and y
  * @param P => int list list representation of polynomial in x and y
  * @param xVal => value of x
  * @param yVal => value of y
  *)
fun evalxy(P, xVal, yVal) = 
  let 
    (** Evaluate base^exp *)
    fun evalPower(base, 0) = 1
      | evalPower(base, exp) = base * evalPower(base, exp - 1); 
    
    (** Evaluate: (coefficients * x * y) *)
    fun eval_xWithy(nil, _, _, _) = 0
      | eval_xWithy(x::xs, xVal, expX, yVal) = 
        (x * evalPower(xVal, expX) * yVal) + eval_xWithy(xs, xVal, expX+1, yVal);

    (** Evaluate the polynomial in x and y
      * @param xy::xys => polynomial in x and y
      * @param xVal => value of x
      * @param yVal => value of y
      * @param expY => the exponent of y
      *)
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
      (** Helper function to add the inner int list*)
      fun addxx(P, nil) = P
        | addxx(nil, Q) = Q
        | addxx(P: int list as p::ps, Q: int list as q::qs) = (p + q)::addxx(ps, qs);

      (** helper function to multiply inner int list with a scalar *)
      fun multxs(nil, q) = nil
        | multxs(P: int list as p::ps, q: int) = (p * q)::multxs(ps, q);

      (** Helper function to multiply the inner int lists.
        * @param P => int list (inner int list of P)
        * @param Q => int list (inner int list of Q)
        * PQ = P*q + qs*x ==> qs*x is obtained by shifting to the right
        *)
      fun multxx(P: int list, nil) = nil
        | multxx(P: int list, Q: int list as q::qs) = addxx(multxs(P, q), 0::multxx(P, qs));

      (** Helper function to multiply the first polynomial in x and y 
        * with an inner list.
        * @param P => int list list (polynomial in x and y)
        * @param q => int list (the inner int list)  
        *)
      fun pmultx(P, nil) = P
        | pmultx(nil, _) = nil
        | pmultx(P: int list list as p::ps, q: int list) = 
        (** Construct the intermediate product of polynomial P with the coefficient and x variable.
          * This represents => P * q, where q = inner int list
          *)
        multxx(p, q)::pmultx(ps, q);
    in
      (** pmultx(P, q) returns P * q i.e. P * (only x part)
        * Shifting to the right represents the multiplication by y.
        *)
      paddxy(pmultx(P, q), nil::pmultxy(P, qs))
    end;