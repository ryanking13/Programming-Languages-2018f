exception InvalidArgument

type ae = CONST of int
        | VAR of string
        | POWER of string * int
        | TIMES of ae list
        | SUM of ae list

let rec diff ((expr, var): (ae * string)): ae =

    match expr with
    | CONST i -> CONST 0
    | VAR s ->
        (
            if s = var then
                CONST 1
            else
                CONST 0
        )
    | POWER (s, i) ->
        (
            if s = var then
                TIMES ([CONST i; POWER (s, i-1)])
            else
                CONST 0
        )
    | TIMES (l) ->
        (
            match l with
            | [] -> raise InvalidArgument
            (* | head::left -> SUM ([TIMES ( diff(head, var)::left ); TIMES([head; diff((TIMES left), var)])]) *)
            | head::left ->
                (
                    if List.length left = 0 then
                        diff(head, var)
                    else
                        SUM ([TIMES ( diff(head, var)::left ); TIMES([head; diff((TIMES left), var)])])
                ) 
        )
    | SUM (l) ->
        (
            match l with
            | [] -> raise InvalidArgument
            (* | head::left -> SUM([diff(head, var); diff(SUM left, var)]) *)
            | head::left ->
                (
                    if List.length left = 0 then
                        diff(head, var)
                    else
                        SUM([diff(head, var); diff(SUM left, var)])
                )
        )

