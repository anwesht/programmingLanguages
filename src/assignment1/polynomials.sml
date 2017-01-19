(*From the book*)
(*padd(P, Q) produces the polynomial sum P + Q*)
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

fun printCoef(0) = print("")
  | printCoef(c: int) = (
      if c<0 then (
        print ("-");
        print(Int.toString(~1*c))
      )  
      else ( 
        print("+");
        print(Int.toString(c))
      )
  );

fun printCoef(0, _) = print("")
  | printCoef(1, 0) = print(Int.toString(1))
  | printCoef(~1, 0) = (
      print ("-");
      print(Int.toString(1))
    ) 
  | printCoef(1, _) = print("+")
  | printCoef(~1, _) = print ("-")   
  | printCoef(c: int, _) = (
      if c<0 then (
        print ("-");
        print(Int.toString(~1*c))
      )  
      else ( 
        print("+");
        print(Int.toString(c))
      )
  );

fun printx(nil, c) = (
      if c=0 then print(Int.toString(0))
      else  print("");
      print("\n")
    )
  | printx(x::xs, 0) = (
      (*print(Int.toString(x)); *)
      printCoef(x, 0);
      printx(xs, 1)
    )
  | printx(x::xs, 1) = (
      (*print(Int.toString(x)); *)
      printCoef(x, 1);
      print("x"); printx(xs, 2)
    ) 
  | printx(x::xs, e) = (
      (*print(Int.toString(x));*)
      if x=0 then 
        print("")
      else (
        printCoef(x, e);
        print("x"); 
        print("^"); 
        print(Int.toString(e))
      ); 
      printx(xs, e+1)
    );







