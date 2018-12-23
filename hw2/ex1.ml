exception FreeVariable
type exp = X
         | INT of int
         | REAL of float
         | ADD of exp * exp
         | SUB of exp * exp
         | MUL of exp * exp
         | DIV of exp * exp
         | SIGMA of exp * exp * exp
         | INTEGRAL of exp * exp * exp

let rec process ((n, exp): (float * exp)): float =
    match exp with
    | X -> n
    | INT i -> float_of_int i
    | REAL f -> f
    | ADD (e1, e2) -> process (n, e1) +. process (n, e2)
    | SUB (e1, e2) -> process (n, e1) -. process (n, e2)
    | MUL (e1, e2) -> process (n, e1) *. process (n, e2)
    | DIV (e1, e2) -> process (n, e1) /. process (n, e2)
    | SIGMA (e1, e2, e3) -> sigma (calculate e1, calculate e2, e3)
    | INTEGRAL (e1, e2, e3) -> integral (calculate e1, calculate e2, e3)
    
and sigma ((a, b, e): (float * float * exp)): float =
    let ai = int_of_float a in
    let bi = int_of_float b in
    if ai > bi then
        0.0
    else if ai = bi then
        process(a, e)
    else
        process(a, e) +. sigma (a +. 1.0, b, e)

and integral ((a, b, e): (float * float * exp)): float =

    if a > b then
        -1.0 *. integral(b, a, e)
    else if b -. a >= 0.1 then  
        process(a, e) *. 0.1 +. integral(a +. 0.1, b, e)
    else
        0.0

and calculate (exp: exp): float =
    match exp with
    | X -> raise FreeVariable
    | INT i -> float_of_int i
    | REAL f -> f
    | ADD (e1, e2) -> calculate e1 +. calculate e2
    | SUB (e1, e2) -> calculate e1 -. calculate e2
    | MUL (e1, e2) -> calculate e1 *. calculate e2
    | DIV (e1, e2) -> calculate e1 /. calculate e2
    | SIGMA (e1, e2, e3) -> sigma (calculate e1, calculate e2, e3)
    | INTEGRAL (e1, e2, e3) -> integral (calculate e1, calculate e2, e3)