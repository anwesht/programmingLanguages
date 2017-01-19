fun printxy(P) = 
  let 
    fun printCoef(0, _) = print("")
      | printCoef(1, 0) = print(Int.toString(1))
      | printCoef(~1, 0) = (
          print (" - ");
          print(Int.toString(1))
        ) 
      | printCoef(1, _) = print(" + ")
      | printCoef(~1, _) = print (" - ")   
      | printCoef(c: int, 0) = (
          if c<0 then (
            print (" -");
            print(Int.toString(~1*c))
          )  
          else ( 
            print(Int.toString(c))
          )
        )
      | printCoef(c: int, _) = (
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
          printCoef(x, 0);
          if x=0 then (
            print("")
          )
          else (
            print(y)
          );
          print_xWithy(xs, 1, y)
        )
      | print_xWithy(x::xs, 1, y:string) = (
          printCoef(x, 1);
          if x=0 then (
            print("")
            (*print(y)*)
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
            (*print(y)*)
          )
          else (
            printCoef(x, e);
            print("x"); 
            print("^"); 
            print(Int.toString(e));
            print(y)
          ); 
          
          print_xWithy(xs, e+1, y)
        );

    fun print_xy(nil, ey) = (
          if ey=0 then print(Int.toString(0))
          else  print("");
          print("\n")
        )
      | print_xy(y::ys, 0) = (
          (*print("HERE:::");*)
          print_xWithy(y, 0, "");
          print_xy(ys, 1) 
        )
      | print_xy(y::ys, 1) = (
          (*print("ey = 1");*)
          print_xWithy(y, 0, "y");
          print_xy(ys, 2)
        )
      | print_xy(y::ys, ey) = (
          print_xWithy(y, 0, "y^"^Int.toString(ey));
          print_xy(ys, ey+1)
        )
  in 
    print_xy(P, 0)
  end;
    

    






