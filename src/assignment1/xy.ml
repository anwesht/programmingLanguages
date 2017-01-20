fun printxy(P) = 
  let 
    fun printCoef(0, _) = print("")
      | printCoef(1, true) = print(Int.toString(1))
      | printCoef(~1, true) = (
          print (" - ");
          print(Int.toString(1))
        ) 
      | printCoef(1, false) = print(" + ")
      | printCoef(~1, false) = print (" - ")   
      | printCoef(c: int, true) = (
          if c<0 then (
            print (" -");
            print(Int.toString(~1*c))
          )  
          else ( 
            print(Int.toString(c))
          )
        )
      | printCoef(c: int, false) = (
          if c<0 then (
            print (" -");
            print(Int.toString(~1*c))
          )  
          else ( 
            print(" + ");
            print(Int.toString(c))
          )
      );

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
    
(*fun evalxy(P, x, y) = 
  let 
    fun padd(P, nil) = P
      | padd(nil, Q) = Q
      | padd((p:int)::ps, q::qs) = (p + q)::padd(ps, qs);
    
    fun smult(nil, q) = nil
      | smult((p:int)::ps, q) = (p * q)::smult(ps, q);

    fun pmult(P, nil) = nil
      | pmult(P, q::qs) = padd(smult(P, q), 0::pmult(P, qs));*)

fun evalx(P, xVal) = 
  let 
    fun evalPower(base, 0) = 1
      | evalPower(base, exp) = base * evalPower(base, exp - 1); 
  
    fun eval_x(nil, _, _) = 0
      | eval_x(x::xs, xVal, exp) = (x * evalPower(xVal, exp)) + eval_x(xs, xVal, exp+1);
  in 
    eval_x(P, xVal, 0)
  end;

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
  

(*fun paddx(P, nil) = P
      | paddx(nil, Q) = Q
      | paddx((p:int)::ps, q::qs) = (p + q)::paddx(ps, qs);
*)
fun paddxy(P, nil) = P
  | paddxy(nil, Q) = Q
  | paddxy(p::ps, q::qs) = 
    let 
      fun paddx(P, nil) = P
      | paddx(nil, Q) = Q
      | paddx((p:int)::ps, q::qs) = (p + q)::paddx(ps, qs);
    in 
      paddx(p, q)::paddxy(ps, qs)
    end;
    
(*fun smult(nil, q) = nil
      | smult((p:int)::ps, q) = (p * q)::smult(ps, q);*)

fun multxy(nil, _) = nil
  | multxy(xy::xys, mult) = 
    let
      fun multx(nil, _) = nil
        | multx(x::xs, mult) = (x * mult)::multx(xs, mult)
    in
      multx(xy, mult)::multxy(xys, mult)
    end


(*fun pmult(P, nil) = nil
  | pmult(P, q::qs) = 
      paddxy(multxy(P, q), 0::pmult(P, qs))*)

(*-----------------------------------------------*)
fun padd(P, nil) = P
  | padd(nil, Q) = Q
  | padd((p:int)::ps, q::qs) = (p + q)::padd(ps, qs);

(*smult(P, q) multiplies polynomial P by scalar q*)
fun smult(nil, q) = nil
  | smult((p:int)::ps, q) = (p * q)::smult(ps, q);

(*pmult(P, Q) produces PQ
    To multiply a polynomial by x, we "shift" the terms right by
    inserting an element 0 in front of the list that represents
    PS.
*)
fun pmult(P, nil) = nil
  | pmult(P, q::qs) = padd(smult(P, q), 0::pmult(P, qs));

(*-----------------------------------------------*)

(*fun pmultxy(P, nil) = P
  | pmultxy(nil, Q) = Q
  (*| pmultxy(p::ps, q::qs) = paddxy(pmult(p, q), nil::pmultxy(P, qs));*)
  | pmultxy(p::ps, q::qs) = pmult(p, q)::*)

(*[] :: []*)
(*fun multAllPWithq(p::ps, q) = pmult(p, q)::multAllPWithq(ps, q)*)

(*fun pmultxy(P, nil) = P
  | pmultxy(nil, Q) = Q
  | pmultxy(P as p::ps, q::qs) = multAllPWithq(P, q)::pmultxy(ps, qs)
*)

(*fun pmultxy(P, nil) = P
  | pmultxy(nil, Q) = Q
  | pmultxy(p::ps, q::qs) = 
      pmult(p, q), nil::pmultxy(ps, q)*)

fun pmultx(P, nil) = P
  | pmultx(nil, _) = nil
  | pmultx((p:int list)::ps, q: int list) = 
      pmult(p, q)::pmultx(ps, q)

(*fun pmultxy(P, nil) = P
  | pmultxy(nil, Q) = Q
  | pmultxy(P, q::qs) = nil@pmultx(P, q)@pmultxy(P, qs);*)
  (*| pmultxy(P as p::ps, q::qs) = nil@pmultx(P, q)::pmultxy(P, qs)*)

(*fun pmultxy(P, nil) = P
  | pmultxy(nil, Q) = Q
  | pmultxy(P, q::qs) = paddxy(nil@pmultx(P, q), pmultxy(P, qs));*)

(*fun pmultxy(P, nil) = P
  | pmultxy(nil, Q) = Q
  | pmultxy(P, q::qs) = paddxy(pmultx(P, q), nil::pmultxy(P, qs));*)

fun pmultxy(P, nil) = nil
  | pmultxy(P, q::qs) = paddxy(pmultx(P, q), nil::pmultxy(P, qs));























