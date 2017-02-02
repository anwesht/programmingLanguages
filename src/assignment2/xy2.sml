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