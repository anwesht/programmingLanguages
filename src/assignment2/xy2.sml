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

fun evalx nil _ = 0
  | evalx _ 0 = 0
  | evalx P xVal = 
      #1 (foldl (
        fn (xCoef, (sum, xValue)) => 
          (sum + xCoef * (if xValue = 0 then 1 else xValue), (if xValue = 0 then 1 else xValue) * xVal)
      ) ((0, 0)) (P)) 
      ;

fun evalxy nil _ _= 0
  | evalxy _ 0 0 = 0
  | evalxy (xy::xys) xVal 0 = 
      #1 (foldl (
        fn (xCoef, (sum, xValue)) => 
          (sum + xCoef * (if xValue = 0 then 1 else xValue), (if xValue = 0 then 1 else xValue) * xVal)
      ) ((0, 0)) (xy)) 
  | evalxy P 0 yVal = 
      #1 (foldl (
        fn (nil, (total, yValue)) => (total, ((if yValue = 0 then 1 else yValue) * yVal))
          | (x::_, (total, yValue)) => (
            print(Int.toString(total)^"\n");
            ((total + (x * (if yValue = 0 then 1 else yValue))), ((if yValue = 0 then 1 else yValue) * yVal))
          )
      ) (0, 0) (P))
  | evalxy P xVal yVal = 
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

(*working inner multiple*)
(*fun pmultx P Q = 
      #2 (foldl (
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
      ) ((Q, nil)) (P))

      *)


fun pmultxy P Q = 
  #2 (foldl (
      fn(pxList, (fullQList, fullPQMultList)) =>
        (*([]::fullQList, (paddxy(SOMETHING, LIST OF LISTS p_part Multiplying FULL Q LIST)))*)
        (*([]::fullQList, (paddxy(fullPQMultList, *)
        (nil::fullQList, 
            (foldl (
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
                      (*) ((Q, nil)) (P))*)
                      ) ((qxList, nil)) (pxList))
                )::pMultqFullList)
              ) (nil) (fullQList)
            ) 
          )
        )
        ((Q, nil)) (P)
      )
;
      
      (*foldl (
          fn (tup, sumxList) => (#1 tup + #2 tup)::sumxList
        ) (nil) (
            #2 (foldl (
              fn  (px, (nil, tupleList)) => (nil, (px, 0)::tupleList)
                | (px, (qx::qxs, tupleList)) => (qxs, (px, qx)::tupleList) 
              ) (qList, nil)) (map (fn qx => px*qx) (qList))
            )*)
            




val p = [[1], [0,~2,0,0,3], [],[],[], [], [~5, 0, 7]];
val q = [[~1], [~1]];
val t1 = [1,2,3];
val t2 = [4,5,6];
val tt1 = [[1,2], [3,4]];
val tt2 = [[5,6], [7,8], [9,10]];
(* A function that will multiply given number with the seed.
 * *)