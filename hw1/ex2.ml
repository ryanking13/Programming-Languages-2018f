let rec prod ((m, n, k): (int * int -> float) * int * int): float =
    if k < 1 then   
        1.0
    else if k = 1 then
        m(n, 1)
    else
        m(n, k) *. prod(m, n, k-1)

let rec sumprod ((m, n, k): (int * int -> float) * int * int): float =
    if n < 1 then
        0.0
    else if n = 1 then
        prod (m, 1, k)
    else
        prod (m, n, k) +. sumprod(m, n-1, k)


