(*
 * Created by atuladhar on 02/02/17.
 * Pledge: I pledge my Honor that I have not cheated, and will not cheat, on this assignment.
 * Name: Anwesh Tuladhar
 *)

(** Multiplies polynomial in x and y with a scalar s.
  * @param P => polynomial in x and y => int list list
  * @param s => scalar multiplier => int
  *)
fun multxy nil _ = nil
  | multxy _ 0 = nil
  | multxy P s = 
      map (fn (xs) => 
        map (fn (x) => x * s) (xs)) (P)
    ; 

(** Evaluates the value of polynomial in x and y.
  * 1. Fold left through the polynomial P with seed value = a tuple (total and yValue)
  * 2. For each inner int list => folds left again where the value of x is plugged into the equation.
  * 3. The result is multiplied by yValue in the outer fold to get the value with both x and y plugged in.  
  * @param P => polynomial to evaluate.
  * @param xVal => value of x
  * @param yVal => value of y
  * @returns => P(xVal, yVal)
  *)
fun evalxy P xVal yVal = 
      #1 (foldl (fn (xList, (total, yValue)) => (
        ((total + (#1 (foldl (
                fn (xCoef, (sum, xValue)) => 
                  (sum + xCoef * xValue, xValue * xVal)
                ) ((0, 1)) (map (fn x => x * yValue) (xList)) 
              )
            )
          ), yValue * yVal)
        )
        
      ) (0, 1) (P))
      ;

(** Adds two polynomials in x and y.
  * 1. Create a tuple with the corresponding coefficients of polynomials P and Q paired together:
       The longer of the two polynomial int list list is folded left, with the other one as the seed value.
       This is done for both the outer and inner lists, corresponding to y and x respectively.
  * 2. The tuple list is folded left to add the pair of coefficients, creating a new list representing the
       sum of P and Q.
  * @param P => first polynomial to add
  * @param Q => second polynomial to add
  * @returns => int list list representing P + Q
  *)
fun paddxy P Q = 
  foldl (fn ((pp, qq), sumXY) => 
    ((foldl (
          fn (tup, sumxList) => (#1 tup + #2 tup)::sumxList
        ) (nil) (
            #2 (foldl (
              fn  (px, (nil, tupleList)) => (nil, (px, 0)::tupleList)
                | (px, (qx::qxs, tupleList)) => (qxs, (px, qx)::tupleList) 
              ) ((if length qq < length pp then qq else pp, nil)) (if length qq < length pp then pp else qq))
            )
      )::sumXY)) (nil)  (#2 (foldl (
              fn  (pxy, (nil, tupleListList)) => (nil, (pxy, [])::tupleListList)
                | (pxy, (qxy::qxys, tupleListList)) => (qxys, (pxy, qxy)::tupleListList) 
            ) ((if length Q < length P then Q else P, nil)) (if length Q < length P then P else Q)
        )
      )  
      ;  

(** Multiple two polynomials in x and y
  * pxList = inner int list of P.
    fullQList = int list list of Q
    fullPQMultList = result list
  * qxList = inner int list of Q
    pMultList = result of multiplying int list of P * int list of Q
  * Multiplication is carried out as follows:
        => pxList * fullQlist[0] + pxList * []::fullQList[1] + ...
  * The same approach is taken for multiplication of each inner list
  *)
fun pmultxy P Q = 
  #2 ((foldl (
      fn(pxList, (fullQList, fullPQMultList)) =>
      (** Shifting fullQList to the right represents multiplication by y
        * paddxy => pMultqFullList = pMultqFullList + pxList * qxList
        *)
        ([]::fullQList, paddxy    
            (foldr (
              fn (qxList, pMultqFullList) => 
                ((#2 (foldl (
                        fn (px, (qList, qMultList)) => 
                          (** Shifting qList to the right represents multiplication by x *)
                          (0::qList, (
                            foldl (
                              fn (tup, sumxList) => (#1 tup + #2 tup)::sumxList
                            ) (nil) (
                              #2 (foldl (
                                fn  (px, (nil, tupleList)) => (nil, (px, 0)::tupleList)
                                  | (px, (qx::qxs, tupleList)) => (qxs, (px, qx)::tupleList) 
                                ) (qMultList, nil) (map (fn qx => px*qx) (qList))
                              )
                            )))
                      ) ((pxList, nil)) (qxList))
                )::pMultqFullList)
              ) (nil) (fullQList)
            ) ( fullPQMultList)
            )
          )
        )
        ((Q, nil)) (P)
      )
;