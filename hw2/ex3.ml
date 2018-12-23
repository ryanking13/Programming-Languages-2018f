exception EmptyHeap 

type heap = EMPTY | NODE of rank * value * heap * heap
and rank = int
and value = int

let rank (h: heap): rank =
    match h with 
    | EMPTY -> -1 
    | NODE(r,_,_,_) -> r 

let shake ((x,lh,rh):(value * heap * heap)): heap = 
    if (rank lh) >= (rank rh) 
    then NODE(rank rh+1, x, lh, rh)
    else NODE(rank lh+1, x, rh, lh) 

let findMin (h: heap): value =
    match h with 
    | EMPTY -> raise EmptyHeap 
    | NODE(_,x,_,_) -> x 

let rec merge ((lh, rh): (heap * heap)): heap =
    match lh with
    | EMPTY -> rh
    | NODE(lr, lx, llh, lrh) ->
        (
            match rh with
            | EMPTY -> lh 
            | NODE (rr, rx, rlh, rrh) ->
                (
                    if lx <= rx then
                        shake(lx, llh, merge(lrh, rh))
                    else
                        shake(rx, rlh, merge(lh, rrh))
                )
        )

let insert ((x,h): (value * heap)): heap =
    merge(h, NODE(0,x,EMPTY,EMPTY)) 

let deleteMin (h: heap): heap =
    match h with 
    | EMPTY -> raise EmptyHeap 
    | NODE(_,x,lh,rh) -> merge (lh,rh) 