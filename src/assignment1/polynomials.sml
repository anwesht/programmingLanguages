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

fun printx(nil, _) = print(Int.toString(0))
    | printx(x::xs, 0) = (
        print(Int.toString(x)); 
        printx(xs, 1)
        )
    | printx(x::xs, 1) = (
        print(Int.toString(x)); 
        print("x"); printx(xs, 2)
        ) 
    | printx(x::xs, e) = (
        print(Int.toString(x));
        print("x"); 
        print("^"); 
        print(Int.toString(e)); 
        printx(xs, e+1));
