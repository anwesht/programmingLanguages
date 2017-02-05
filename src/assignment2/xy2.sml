fun multxy nil _ = nil
  | multxy _ 0 = nil
  | multxy P s = 
      map (fn (xs) => 
        map (fn (x) => x * s) (xs)) (P)
    ; 

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

fun pmultxy P Q = 
  #2 ((foldl (
      fn(pxList, (fullQList, fullPQMultList)) =>
        ([]::fullQList, paddxy
            (foldr (
              fn (qxList, pMultqFullList) => 
                ((#2 (foldl (
                        fn (px, (qList, qMultList)) => 
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

val p = [[1], [0,~2,0,0,3], [],[],[], [], [~5, 0, 7]];
val q = [[~1], [~1]];
val t1 = [1,2,3];
val t2 = [4,5,6];
val tt1 = [[1,2], [3,4]];
val tt2 = [[5,6], [7,8], [9,10]];