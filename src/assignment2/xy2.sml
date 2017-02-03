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

(*fun evalx nil _ = 0
  | evalx _ 0 = 0
  | evalx P xVal = 
      #1 (foldl (fn (xCoef, (sum, xValue)) => 
          (sum + xCoef * (if xValue > 0 then xValue else 1), (if xValue > 0 then xValue else 1) * xVal)
      ) ((0, 0)) (P)) 
      ;*)

fun evalx nil _ = 0
  | evalx _ 0 = 0
  | evalx P xVal = 
      #1 (foldl (
        fn (xCoef, (sum, xValue)) => 
          (sum + xCoef * (if xValue = 0 then 1 else xValue), (if xValue = 0 then 1 else xValue) * xVal)
      ) ((0, 0)) (P)) 
      ;

(*fun eval nil _ _= 0
  | eval P xVal yVal = 
      #1 (foldl (fn (xList, (total, yValue)) => 
        ((total + (#1 (foldl (
                fn (xCoef, (sum, xValue)) => 
                  (sum + xCoef * (if xValue = 0 then 1 else xValue), (if xValue = 0 then 1 else xValue) * xVal)
                ) ((0, 0)) (map (fn x => x * (if yValue = 0 then 1 else yValue)) (xList)) 
              )
            )
          ), ((if yValue = 0 then 1 else yValue) * yVal)
        )
      ) (0, 0) (P))
      ;*)

fun eval nil _ _= 0
  (*| eval _ 0 _ = 0*)
  | eval P xVal yVal = 
      #1 (foldl (fn (xList, (total, yValue)) => (
        print(Int.toString(total)^"\n");
        ((total + (#1 (foldl (
                fn (xCoef, (sum, xValue)) => 
                  (sum + xCoef * (if xValue = 0 then 1 else xValue), ((if xValue = 0 then 1 else xValue) * xVal))
                ) ((0, 0)) (map (fn x => x * (if yValue = 0 then 1 else yValue)) (xList)) 
              )
            )
          ), ((if yValue = 0 then 1 else yValue) * yVal)
        )
        )
      ) (0, 0) (P))
      ;

val p = [[1], [0,~2,0,0,3], [],[],[], [], [~5, 0, 7]];
val q = [[~1], [~1]];
(* A function that will multiply given number with the seed.
 * *)