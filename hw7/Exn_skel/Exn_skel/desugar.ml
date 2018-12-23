(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 *)

open Xexp

let count = ref 0 

let new_name () = 
  let _ = count := !count +1 in
  "#x_" ^ (string_of_int !count)

type handler = (int * xexp) list

(* let rec se e = 
    match e with
    | Num n -> Printf.sprintf "Num %d" n
    | Var s -> Printf.sprintf "Var %s" s
    | Fn (x, e1) -> Printf.sprintf "Fn ( %s, %s )" x (se e1)
    | App (e1, e2) -> Printf.sprintf "App ( %s, %s )" (se e1) (se e2)
    | If (e1, e2, e3) -> Printf.sprintf "If ( %s, %s, %s )" (se e1) (se e2) (se e3)
    | Equal (e1, e2) -> Printf.sprintf "( %s = %s )" (se e1) (se e2)
    | Raise (e1) -> Printf.sprintf "Raise %s" (se e1)
    | Handle (e1, n, e2) -> Printf.sprintf "Handle ( %s, %d, %s )" (se e1) n (se e2)

let show e =
    let _ = print_endline ("::" ^ (se e)) in
    e *)


let rec alpha_conv exp subst = 
  match exp with
  | Num n -> Num n
  | Var x -> (try Var (List.assoc x subst) with Not_found -> Var x)
  | Fn (x, e) ->
    let x' = new_name () in
    let subst' = (x, x') :: subst in
    Fn (x', alpha_conv e subst')
  | App (e1, e2) -> App (alpha_conv e1 subst, alpha_conv e2 subst)
  | If (e1, e2, e3) -> 
    If (alpha_conv e1 subst, alpha_conv e2 subst, alpha_conv e3 subst)
  | Equal (e1, e2) -> Equal (alpha_conv e1 subst, alpha_conv e2 subst)
  | Raise e1 -> Raise (alpha_conv e1 subst)
  | Handle (e1, n, e2) -> Handle (alpha_conv e1 subst, n, alpha_conv e2 subst)


let empty_handler = fun x -> Num 201812

let append (n, e) handler =
    let new_handler exp =
        If (Equal (exp, Num n), e, handler exp)
    in new_handler

(* TODO : Implement this function *)
let removeExn : xexp -> xexp = fun e ->

    let vh = new_name() in
    let vi = new_name()  in
    let empty_handler = Fn (vh, Num 201812) in
    let identity = Fn (vi, Var vi) in

    let rec cps e =
        let k = new_name() in
        let handler = new_name() in
        match e with
        | Num n -> Fn (handler, Fn (k, App (Var k, Num n)))
        | Var x -> Fn (handler, Fn (k, App (Var k, Var x)))
        | Fn (x, e1) -> Fn (handler, Fn (k, App (Var k, Fn (x, cps e1))))
        | App (e1, e2) ->
            let v1 = new_name () in
            let v2 = new_name () in
            Fn (handler,
                Fn (k, 
                    App (App(cps e1, Var handler), 
                         Fn (v1, 
                             App (App(cps e2, Var handler), 
                                  Fn (v2,
                                      App (App (App (Var v1, Var v2), Var handler),
                                           Var k
                                          )
                                     )
                                 )
                            )
                        )
                    )
                )
        | If (e1, e2, e3) ->
            let v1 = new_name () in
            let v2 = new_name () in
            let v3 = new_name () in
            Fn (handler,
                Fn (k,
                    App (App(cps e1, Var handler),
                        Fn (v1,
                            If (Var v1,
                                App (App(cps e2, Var handler),
                                    Fn (v2,
                                        App (Var k, Var v2)
                                        )
                                    ),
                                App (App(cps e3, Var handler),
                                    Fn (v3,
                                        App (Var k, Var v3)
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
        | Equal (e1, e2) ->
          let v1 = new_name () in
          let v2 = new_name () in
          Fn (handler,
              Fn (k, 
                  App (App(cps e1, Var handler), 
                      Fn (v1, 
                          App (App(cps e2, Var handler), 
                              Fn (v2, 
                                  App (Var k, Equal (Var v1, Var v2))
                                  )
                              )
                          )
                      )
                  )
              )
        | Raise e1 ->
            Fn (handler,
                Fn (k,
                    App (App (cps e1, Var handler), Var handler)
                    )
                )
        | Handle (e1, n, e2) ->
            let v = new_name() in

            let handle = App (App (cps e2, Var handler), Var k) in
            let throw = App (Var handler, Var v) in
            let check_raise = Fn (v, If (Equal (Var v, Num n), handle, throw)) in
            Fn (handler,
              Fn (k,
                  App (App (cps e1, check_raise), Var k)
                  )
              )
    in
  
    App (App (cps (alpha_conv e []), empty_handler), identity)