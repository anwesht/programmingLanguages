fun mul nil _ = nil
  | mul _ 0 = nil
  | mul P s = 
      map (fn (x) => x * s ) (P) 
      ;

fun multxy nil _ = nil
  | multxy _ 0 = nil
  | multxy P s = 
      map (fn (xs) => 
        map (fn (x) => x * s) (xs)) (P)
    ; 

(*fun eval nil _ = nil
  | eval _ 0 = nil
  | eval xy::xys xVal = 
      map (fn (x) => (x, xVal)) (P)
      ;*)
      (*foldr (fn (xCoef, seed) => )*)
      (*map (fn (xCoef, seed) => xCoef * seed ) (xVal) (P)*)
      (*foldl (fn (xCoef, seed) => xCoef * seed ) (xVal) (P)*)
(*fun eval nil _ = nil
  | eval _ 0 = nil
  | eval P xVal = 
      map (fn (x) => (x, xVal)) (P) 
      ;
*)

fun eval nil _ = 0
  | eval _ 0 = 0
  | eval P xVal = 
      #1 (foldl (fn (xCoef, (sum, xValue)) => 
          (*val s = sum + xCoef * (if xValue > 0 then xValue else 1);*)
          (sum + xCoef * (if xValue > 0 then xValue else 1), (if xValue > 0 then xValue else 1) * xVal)
        
      ) ((0, 0)) (P)) 
      ;

(* A function that will multiply given number with the seed.
 * *)