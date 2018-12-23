(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton
 *)

open M

type var = string

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  | TWrite of var (* TInt TBool TString *)
  | TEq of var (* TInt TBool TString TLoc *)
  (* Modify, or add more if needed *)

type typ_scheme =
  | SimpleTyp of typ 
  | GenTyp of (typ list * typ)

type typ_env = (M.id * typ_scheme) list

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> typ list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TVar v -> [TVar v]
  | TWrite v -> [TWrite v]
  | TEq v -> [TEq v]

let ftv_of_scheme : typ_scheme -> typ list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas 

let ftv_of_env : typ_env -> typ list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv_of_env tyenv in
  let typ_ftv = ftv_of_typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

(* let rec se exp =
  match exp with
  | M.CONST (M.S _) -> print_endline "STRING"; exp
  | M.CONST (M.B _) -> print_endline "BOOL"; exp
  | M.CONST (M.N _) -> print_endline "INT"; exp
  | M.VAR x -> print_endline ("VAR " ^ x); exp
  | M.APP _ -> print_endline ("APP"); exp
  | M.FN (x, e) -> print_endline ("-----"); print_endline ("FN " ^ x); se e; print_endline("-----"); exp
  | M.LET _ -> print_endline ("LET"); exp
  | M.IF _ -> print_endline ("IF"); exp
  | M.BOP _ -> print_endline ("BOP"); exp
  | M.READ -> print_endline ("READ"); exp
  | M.WRITE e -> print_endline ("WRITE"); exp
  | M.MALLOC _ -> print_endline ("MALLOC"); exp
  | M.ASSIGN (e1, e2) -> print_endline ("ASSIGN"); exp
  | M.BANG e -> print_endline ("BANG"); exp
  | M.PAIR (e1, e2) -> print_endline ("PAIR"); exp
  | M.SEQ (e1, e2) -> print_endline ("SEQ"); exp
  | M.FST e -> print_endline ("FST"); exp
  | M.SND e -> print_endline ("SND"); exp *)

(* let rec st t =
  match t with
  | TInt -> print_endline "- TINT"; t
  | TBool -> print_endline "- TBOOL"; t
  | TString -> print_endline "- TSTRING"; t
  | TPair (t1, t2) -> print_endline "- TPAIR"; st t1; st t2; t
  | TLoc _ -> print_endline "- TLOC"; t
  | TFun (t1, t2) -> print_endline "- TFUN"; st t1; st t2; t
  | TVar x -> print_endline ("- TVAR " ^ x); t
  | TWrite x -> print_endline ("- TWRITE " ^ x); t
  | TEq x -> print_endline ("- TEq " ^ x); t *)

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
    | TWrite x' -> if (x = x') then t else t'
    | TEq x' -> if (x = x') then t else t'
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
    let _alphas =
      List.map (
        fun a -> (
          match a with
          | TVar x -> x
          | TWrite x -> x
          | TEq x -> x
          | _ -> raise (M.TypeError "[SUBST_SCHEME] var/write/eq must be given")
        )
      ) alphas
    in
    (* let betas = List.map (fun _ -> new_var()) alphas in *)
    let betas = List.map (
        fun b -> (
          match b with
            | TVar x -> TVar (new_var())
            | TWrite x -> TWrite (new_var())
            | TEq x -> TEq (new_var())
            | _ -> raise (M.TypeError "[SUBST_SCHEME] var/write/eq must be given")
        )
      ) alphas
    in
    let s' =
      List.fold_left2
        (fun acc_subst alpha beta -> make_subst alpha beta @@ acc_subst)
        empty_subst _alphas betas
    in
    GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

(* TODO : Implement this function *)
let check : M.exp -> M.typ = fun exp ->
    let rec expansive exp =
      match exp with
      | M.CONST _ -> false
      | M.VAR _ -> false
      | M.FN _ -> false
      | M.APP _ -> true
      | M.LET (d, e2) ->
        (
          match d with
          | M.VAL (x, e1) -> expansive e1 || expansive e2
          | M.REC (f, x, e1) -> expansive e2
        )
      | M.IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3
      | M.BOP (op, e1, e2) -> expansive e1 || expansive e2
      | M.READ -> false
      | M.WRITE e -> expansive e 
      | M.MALLOC _ -> true
      | M.ASSIGN (e1, e2) -> expansive e1 || expansive e2
      | M.BANG e -> expansive e
      | M.PAIR (e1, e2) -> expansive e1 || expansive e2
      | M.SEQ (e1, e2) -> expansive e1 || expansive e2
      | M.FST e -> expansive e
      | M.SND e -> expansive e
    in

    let rec duplicate t x =
      match t with
      | TInt -> false
      | TBool -> false
      | TString -> false
      | TLoc t -> duplicate t x
      | TVar a -> if a = x then true else false
      | TPair (t1, t2) -> duplicate t1 x || duplicate t2 x
      | TFun (t1, t2) -> duplicate t1 x || duplicate t2 x
      | TEq a -> if a = x then true else false
      | TWrite a -> if a = x then true else false
    in

    let rec unify (t1, t2) =
      match (t1, t2) with
      | (TInt, TInt) | (TBool, TBool) | (TString, TString) -> empty_subst
      | (TLoc t1', TLoc t2') -> unify (t1', t2')
      | (TVar x1, TVar x2) when x1 = x2 -> empty_subst
      | (t1, TVar x) ->
        if duplicate t1 x then raise (M.TypeError "[UNIFY] Duplicate var")
        else make_subst x t1
      | (TVar x, t2) ->
        if duplicate t2 x then raise (M.TypeError "[UNIFY] Duplicate var")
        else make_subst x t2
      | (TPair (t11, t12), TPair (t21, t22)) ->
        let s = unify (t11, t21) in
        let s' = unify (s t12, s t22) in
        s' @@ s
      | (TFun (t11, t12), TFun (t21, t22)) ->
        let s = unify (t11, t21) in
        let s' = unify (s t12, s t22) in
        s' @@ s
      | (TEq x1, TEq x2) when x1 = x2 -> empty_subst
      | (TEq x, t2) ->
        if duplicate t2 x then raise (M.TypeError "[UNIFY] Duplicate var")
        else 
        (
          match t2 with
          | TInt | TBool | TString -> make_subst x t2
          | TLoc t -> make_subst x t2
          | TWrite x' | TEq x' -> make_subst x t2
          | _ -> (* st t2; *) raise (M.TypeError "[UNIFY] TEq failed")
        )
      | (t1, TEq x) ->
        if duplicate t1 x then raise (M.TypeError "[UNIFY] Duplicate var")
        else
        (
          match t1 with
          | TInt | TBool | TString -> make_subst x t1
          | TLoc t -> make_subst x t1
          | TWrite x' | TEq x' -> make_subst x t1
          | _ -> (* st t1; *) raise (M.TypeError "[UNIFY] TEq failed")
        )
      | (TWrite x1, TWrite x2) when x1 = x2 -> empty_subst
      | (TWrite x, t2) ->
        if duplicate t2 x then raise (M.TypeError "[UNIFY] Duplicate var")
        else
        (
          match t2 with
          | TInt | TBool | TString -> make_subst x t2
          | TWrite x' -> make_subst x t2
          | _ -> (* st t2; *) raise (M.TypeError "[UNIFY] TWrite failed")
        )
      | (t1, TWrite x) ->
        if duplicate t1 x then raise (M.TypeError "[UNIFY] Duplicate var")
        else
        (
          match t1 with
          | TInt | TBool | TString -> make_subst x t1
          | TWrite x' -> make_subst x t1
          | _ -> (* st t1; *) raise (M.TypeError "[UNIFY] TWrite failed")
        )
      | _ -> (* (st t1); (st t2); *) raise (M.TypeError "[UNIFY] unexpected behavior")
    in
    
    let rec m (env, exp, t) =
      match exp with
      | M.CONST c -> (match c with | M.S _ -> unify (TString, t) | M.N _ -> unify (TInt, t) | M.B _ -> unify (TBool, t))
      | M.VAR x ->
        let t' = List.assoc x env in
        (
          match t' with
          | SimpleTyp t'' -> unify (t'', t)
          | GenTyp (alphas, t'') ->
            let _alphas =
              List.map (
                fun a -> (
                  match a with
                  | TVar x -> x
                  | TWrite x -> x
                  | TEq x -> x
                  | _ -> raise (M.TypeError "[SUBST_SCHEME] var/write/eq must be given")
                )
              ) alphas
            in
            (* let betas = List.map (fun _ -> new_var()) alphas in *)
            let betas = List.map (
                fun b -> (
                  match b with
                    | TVar x -> TVar (new_var())
                    | TWrite x -> TWrite (new_var())
                    | TEq x -> TEq (new_var())
                    | _ -> raise (M.TypeError "[SUBST_SCHEME] var/write/eq must be given")
                )
              ) alphas
            in
            let s' =
              List.fold_left2
                (fun acc_subst alpha beta -> make_subst alpha beta @@ acc_subst)
                empty_subst _alphas betas
            in
            unify(s' t'', t)
        )
      | M.FN (x, e) ->
        let x1 = TVar (new_var()) in
        let x2 = TVar (new_var()) in
        let s = unify(TFun (x1, x2), t) in
        let env' = subst_env s env in
        let s' = m ((x, SimpleTyp (s x1))::env', e, s x2) in
        s' @@ s
      | M.APP (e1, e2) ->
        let x1 = TVar (new_var()) in
        let s = m (env, e1, TFun (x1, t)) in
        let env' = subst_env s env in
        let s' = m (env', e2, s x1) in
        s' @@ s
      | M.LET (d, e2) ->
        (
          match d with
          | M.VAL (x, e1) ->
            let x1 = TVar (new_var()) in
            let s = m (env, e1, x1) in
            let env' = subst_env s env in
            if expansive e1 then
              let s' = m ((x, SimpleTyp (s x1))::env', e2, s t) in
              s' @@ s
            else
              let s' = m ((x, generalize env' (s x1))::env', e2, s t) in
              s' @@ s
          | M.REC (f, x, e1) ->
            let x1 = TVar (new_var()) in
            let s = m ((f, SimpleTyp x1)::env, M.FN (x, e1), x1) in
            let env' = subst_env s env in
            let s' = m ((f, generalize env' (s x1))::env', e2, s t) in
            s' @@ s
        )
      | M.IF (e1, e2, e3) ->
        let s = m (env, e1, TBool) in
        let env' = subst_env s env in
        let s' = m (env', e2, s t) in
        let env'' = subst_env s' env' in
        let s'' = m (env'', e3, (s' @@ s) t) in
        s'' @@ s' @@ s
      | M.BOP (op, e1, e2) ->
        (
          match op with
          | M.ADD | M.SUB ->
            let s = unify(TInt, t) in
            let env' = subst_env s env in
            let s' = m (env', e1, TInt) in
            let env'' = subst_env s' env' in
            let s'' = m (env'', e2, TInt) in
            s'' @@ s' @@ s
          | M.AND | M.OR ->
            let s = unify(TBool, t) in
            let env' = subst_env s env in
            let s' = m (env', e1, TBool) in
            let env'' = subst_env s' env' in
            let s'' = m (env'', e2, TBool) in
            s'' @@ s' @@ s
          | M.EQ ->
(*             let x1 = TVar (new_var()) in
            let x2 = TVar (new_var()) in
            let s = unify(TBool, t) in
            let env' = subst_env s env in
            let s' = unify(x1, x2) in
            let env'' = subst_env s' env' in
            let s'' = m (env'', e1, s' x1) in
            let env''' = subst_env s'' env'' in
            let s''' = m (env''', e2, s'' x2) in
            s''' @@ s'' @@ s' @@ s *)
            let x1 = TEq (new_var()) in
            let s = unify(TBool, t) in
            let env' = subst_env s env in
            let s' = m (env', e1, s x1) in
            let env'' = subst_env s' env' in
            let s'' = m (env'', e2, (s' @@ s) x1) in
            s'' @@ s' @@ s
        )
      | M.READ -> unify (TInt, t)
      | M.WRITE e ->
        (* let x1 = TVar (new_var()) in *)
        let x1 = TWrite (new_var()) in
        let s = unify(x1, t) in
        let env' = subst_env s env in
        let s' = m (env', e, s t) in
        s' @@ s
      | M.MALLOC e ->
        let x1 = TVar (new_var()) in
        let s = unify(t, TLoc x1) in
        let env' = subst_env s env in
        let s' = m (env', e, s x1) in
        s' @@ s 
      | M.ASSIGN (e1, e2) ->
        let x1 = TVar (new_var()) in
        let s = unify(t, x1) in
        let env' = subst_env s env in
        let s' = m (env', e1, s (TLoc x1)) in
        let env'' = subst_env s' env' in
        let s'' = m (env'', e2, (s' @@ s) t) in
        s'' @@ s' @@ s
      | M.BANG e ->
        let x1 = TVar (new_var()) in
        let s = unify(x1, t) in
        let env' = subst_env s env in
        let s' = m (env', e, s (TLoc x1)) in
        s' @@ s
      | M.PAIR (e1, e2) ->
        let x1 = TVar (new_var()) in
        let x2 = TVar (new_var()) in
        let s = unify(TPair (x1, x2), t) in
        let env' = subst_env s env in
        let s' = m (env', e1, s x1) in
        let env'' = subst_env s' env' in
        let s'' = m (subst_env s' env'', e2, (s' @@ s) x2) in
        s'' @@ s' @@ s
      | M.SEQ (e1, e2) ->
        let x1 = TVar (new_var()) in
        let s = m (env, e1, x1) in
        let env' = subst_env s env in
        let s' = m (env', e2, s t) in
        s' @@ s
      | M.FST e ->
        let x1 = TVar (new_var()) in
        let x2 = TVar (new_var()) in
        let s = unify (x1, t) in
        let env' = subst_env s env in
        let s' = m (env', e, s (TPair (x1, x2))) in
        s' @@ s
      | M.SND e ->
        let x1 = TVar (new_var()) in
        let x2 = TVar (new_var()) in
        let s = unify (x2, t) in
        let env' = subst_env s env in
        let s' = m (env', e, s (TPair (x1, x2))) in
        s' @@ s
    in

    let rec toMType t =
      match t with
      | TInt -> M.TyInt
      | TBool -> M.TyBool
      | TString -> M.TyString
      | TPair (t1, t2) -> M.TyPair (toMType t1, toMType t2)
      | TLoc t -> M.TyLoc (toMType t)
      | TFun (t1, t2) -> raise (M.TypeError ("TyArrow"))
      | TVar v -> raise (M.TypeError ("Free variable: " ^ v))
      | _ -> raise (M.TypeError "Invalid")
    in

    (* let emptyEnv = (fun x -> raise (M.TypeError ("unbound id: " ^ x))) in *)
    let x = TVar (new_var ()) in
    let s = m ([], exp, x) in
    toMType (s x)
  (* raise (M.TypeError "Type Checker Unimplemented") *)
