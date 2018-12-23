type require = id * (cond list)
and cond
    = Items of gift list
    | Same of id
    | Common of cond * cond
    | Except of cond * gift list
and gift = int
and id = A | B | C | D | E

exception Invalid
type giftmap = id * (gift list)

let string_of_list string_of_elem ls =
  "[" ^ (String.concat "; " (List.map string_of_elem ls)) ^ "]"

let string_of_id x =
  match x with
  A -> "A" | B -> "B" | C -> "C" | D -> "D" | E -> "E"

let string_of_id_tuple string_of_e (x, e) =
  Printf.sprintf "%s: %s" (string_of_id x) (string_of_e e)

let string_of_int_list = string_of_list string_of_int

let string_of_sum_list string_of_elem l =
  l |> List.map string_of_elem |> String.concat " + "

let string_of_id_tuple_list string_of_elem itl =
  "\n  " ^ (List.map (string_of_id_tuple string_of_elem) itl |> String.concat "\n  ") ^ "\n"

let string_of_shoppingList =
  string_of_id_tuple_list string_of_int_list


let shoppingList (rlist: require list): giftmap list =
    let rec get_cond_list (rlist: require list) (id: id): cond list =
        match rlist with
        | [] -> []
        | (id', l')::rlist' -> if id' = id then l' else get_cond_list rlist' id
    in

    let rec get_gmap (glist: giftmap list) (id: id): gift list =
        match glist with
        | [] -> raise Invalid
        | (id', l')::glist' -> if id' = id then l' else get_gmap glist' id
    in

    let rec update_gmap_list (glist: giftmap list) (id: id) (l: gift list): giftmap list =
        match glist with
        | [] -> raise Invalid
        | (id', l')::glist' -> if id' = id then (id, l)::glist' else (id', l')::(update_gmap_list glist' id l)
    in

    let rec common l1 l2 l =
        match l1 with
        | [] -> l
        | h::t -> if (List.mem h l2) then (common t l2 (h::l)) else (common t l2 l)
    in

    let rec except l1 l2 l =
        match l1 with
        | [] -> l
        | h::t -> if (List.mem h l2) then (except t l2 l) else (except t l2 (h::l))
    in

    let compare a b: int =
        if a > b then 1
        else if a = b then 0
        else -1
    in

    let rec eval_cond (glist: giftmap list) (cond: cond): gift list =
        match cond with
        | Items l -> l
        | Same id -> get_gmap glist id
        | Common (c1, c2) -> common (eval_cond glist c1) (eval_cond glist c2) []
        | Except (c, l) -> except (eval_cond glist c) l []
    in

    let rec eval_conds (glist: giftmap list) (clist: cond list) (l: (gift list) list): (gift list) list =
        match clist with
        | [] -> l
        | cond::clist' -> eval_conds glist clist' ((eval_cond glist cond)::l)
    in

    let rec check_id (glist: giftmap list) (rlist: require list) (id: id): giftmap list =
        let clist = get_cond_list rlist id in
        let evaled_cond = eval_conds glist clist [] in
        let sorted = List.sort_uniq compare (List.concat evaled_cond) in
        update_gmap_list glist id sorted
    in

    let rec check_all_ids (glist: giftmap list) (rlist: require list) (ids: id list): giftmap list =
        match ids with
        | [] -> glist
        | id::ids' -> check_all_ids (check_id glist rlist id) rlist ids'
    in

    let rec check_all_ids_ (glist: giftmap list) (rlist: require list) (ids: id list) (left: id list): giftmap list =
        match left with
        | [] -> glist
        | id::left' -> check_all_ids_ (check_all_ids glist rlist ids) rlist ids left'
    in

    let ids = [A; B; C; D; E;] in
    let glist = [(A, []); (B, []); (C, []); (D, []); (E, []);] in

    check_all_ids_ glist rlist ids ids
    