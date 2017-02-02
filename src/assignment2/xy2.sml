fun multxy nil _ = nil
  | multxy _ 0 = nil
  | multxy P s = 
      map (fn (x) => x * s ) (P) 
      ; 