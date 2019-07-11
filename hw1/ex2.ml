let rec prod (f, i, k) =
  if(k <= 0) then 1.0
  else prod(f, i, k - 1) *. f(i, k)

let rec sumprod (f, n, k) =
    if(n <= 0) then 0.0
    else sumprod(f, n - 1, k) +. prod(f, n, k)

