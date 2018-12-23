type nat = ZERO | SUCC of nat

let rec natadd ((n1, n2): (nat * nat)): nat =
    match n1 with
    | ZERO ->
        (match n2 with
            | ZERO -> ZERO
            | SUCC n2' -> n2
        )
    | SUCC n1' ->
        (match n2 with
            | ZERO -> n1
            | SUCC n2' -> SUCC (natadd (n1, n2'))
        )

let rec natmul ((n1, n2): (nat * nat)): nat =
    match n1 with
    | ZERO ->
        (match n2 with
            | ZERO -> ZERO
            | SUCC n2' -> ZERO
        )
    | SUCC n1' ->
        (match n2 with
            | ZERO -> ZERO
            | SUCC n2' -> natadd (n1, natmul(n1, n2'))
        )