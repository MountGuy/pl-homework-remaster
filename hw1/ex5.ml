type nat =
    ZERO 
  | SUCC of nat

let rec natadd(m, n) = 
  match n with
  | ZERO -> m
  | SUCC n' -> SUCC(natadd(m, n'))
and natmul(m, n) = 
  match n with
  | ZERO -> ZERO
  | SUCC n' -> natadd(natmul(m, n'), m)