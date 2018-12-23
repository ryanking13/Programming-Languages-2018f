module type Queue =
    sig
        type element
        type queue
        exception EMPTY_Q
        val emptyQ: queue
        val enQ: queue * element -> queue
        val deQ: queue -> element * queue
    end

module IntListQ =
    struct
        type element = int list
        type queue = ((int list) list * (int list) list)
        exception EMPTY_Q
        let emptyQ = ([], [])
        let enQ ((q, e): (queue * element)): queue =
            match q with
            | (q1, q2) -> (e::q1, q2)
        let deQ (q: queue): (element * queue) =

            let rec reverse_list (list, accum) = 
                match list with
                | [] -> accum
                | head::list' -> reverse_list (list', head::accum)
            in

            match q with
            | ([], []) -> raise EMPTY_Q
            | (q1, []) ->
                (
                    let rq1' = reverse_list(q1, []) in
                    match rq1' with
                    | [] -> raise EMPTY_Q
                    | head::q1' -> (head, ([], q1'))
                )
            | (q1, head::q2) -> (head, (q1, q2))
    end

(* module ValidIntListQ = (IntListQ : Queue) *)