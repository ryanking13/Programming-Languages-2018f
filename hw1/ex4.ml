type formula = TRUE
             | FALSE
             | NOT of formula
             | ANDALSO of formula * formula
             | ORELSE of formula * formula
             | IMPLY of formula * formula
             | LESS of expr * expr

and expr = NUM of int
         | PLUS of expr * expr
         | MINUS of expr * expr

let rec eval_expr (e: expr): int =
    match e with
    | NUM e1 -> e1
    | PLUS (e1, e2) ->
        (
            eval_expr e1 + eval_expr e2
        )
    | MINUS (e1, e2) ->
        (
            eval_expr e1 - eval_expr e2
        )


let rec eval (formula: formula): bool =
    match formula with
    | TRUE -> true
    | FALSE -> false
    | NOT f' ->
        (if eval f' = true then false else true)
    | ANDALSO (f', g') ->
        (
            let _f = eval f' in
            let _g = eval g' in
            if _f = true && _g = true then true
            else false
        )
    | ORELSE (f', g') ->
        (
            let _f = eval f' in
            let _g = eval g' in
            if _f = false && _g = false then false
            else true
        )
    | IMPLY (f', g') ->
        (
            let _f = eval f' in
            let _g = eval g' in
            if _f = true && _g = false then false
            else true
        )
    | LESS (e1, e2) ->
        (
            if eval_expr e1 < eval_expr e2 then true
            else false
        )