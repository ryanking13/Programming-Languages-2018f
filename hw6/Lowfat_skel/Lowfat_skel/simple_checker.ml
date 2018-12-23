(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton Code
 *)

open M
open Pp

type var = string

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  (* Modify, or add more if needed *)

let rec s_t (env, typ) =
    match typ with
    | TInt -> print_endline "int"; (env, typ)
    | TBool -> print_endline "bool"; (env, typ)
    | TString -> print_endline "string"; (env, typ)
    | TPair (t1, t2) ->
      let _ = print_endline "pair" in
      let _ = s_t (env, t1) in
      let _ = s_t (env, t2); in 
      (env, typ)
    | TLoc t -> print_endline "loc"; (env, typ)
    | TFun (t1, t2) ->
      let _ = print_endline "fun" in
      let _ = s_t (env, t1) in
      let _ = s_t (env, t2) in
      (env, typ)
    | TVar v -> print_endline ("var: " ^ v); (env, typ)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

(* TODO : Implement this function *)
let check : M.exp -> M.types = fun exp ->
    let rec subst_env subst env =
      List.map (fun (x, t) -> (x, subst t)) env
    in
    let rec unify (t1, t2) =
      match (t1, t2) with
      | (TInt, TInt) | (TBool, TBool) | (TString, TString) -> empty_subst
      | (TLoc t1', TLoc t2') -> unify (t1', t2')
      | (TVar x, t2) -> make_subst x t2
      | (t1, TVar x) -> make_subst x t1
      | (TPair (t11, t12), TPair (t21, t22)) ->
        let s = unify (t11, t21) in
        let s' = unify (s t12, s t22) in
        s @@ s'
      | (TFun (t11, t12), TFun (t21, t22)) ->
        let s = unify (t11, t21) in
        let s' = unify (s t12, s t22) in
        s @@ s'
      | _ -> raise (M.TypeError "[UNIFY] unexpected behavior")
    in

    let rec m (env, exp, t) =
      match exp with
      | M.CONST c -> (match c with | M.S _ -> unify (TString, t) | M.N _ -> unify (TInt, t) | M.B _ -> unify (TBool, t))
      | M.VAR x ->
        let t' = List.assoc (TVar x) env in
        unify (t, t')
      | M.FN (x, e) ->
        let x1 = TVar (new_var()) in
        let x2 = TVar (new_var()) in
        let s = unify(TFun (x1, x2), t) in
        let env' = subst_env s env in
        let s' = m ( (TVar x, s x1)::env', e, s x2) in
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
            let s' = m ((TVar x, s x1)::env', e2, s t) in
            s' @@ s
          | M.REC (f, x, e1) ->
            let x1 = TVar (new_var()) in
            let x2 = TVar (new_var()) in
            let s = unify(x1, x2) in
            let env' = subst_env s env in
            let s' = m ((TVar f, x2)::env, M.FN(x, e1), x1) in
            let env'' = subst_env s' env' in
            let s'' = m ((TVar f, s' x1)::env'', e2, s' t) in
            s'' @@ s' @@ s
        )
      | M.IF (e1, e2, e3) ->
        let x1 = TVar (new_var()) in
        let s = m (env, e1, TBool) in
        let env' = subst_env s env in
        let s' = unify(x1, t) in
        let env'' = subst_env s' env' in
        let s'' = m (env'', e2, s' x1) in
        let env''' = subst_env s'' env'' in
        let s''' = m (env''', e3, s'' t) in
        s''' @@ s'' @@ s' @@ s
      | M.BOP (op, e1, e2) ->
        (
          match op with
          | M.ADD | M.SUB ->
            let s = unify(TInt, t) in
            let env' = subst_env s env in
            let s' = m (env', e1, s t) in
            let env'' = subst_env s' env' in
            let s'' = m (env'', e2, s' t) in
            s'' @@ s' @@ s
          | M.AND | M.OR ->
            let s = unify(TBool, t) in
            let env' = subst_env s env in
            let s' = m (env', e1, s t) in
            let env'' = subst_env s' env' in
            let s'' = m (env'', e2, s' t) in
            s'' @@ s' @@ s
          | M.EQ ->
            let x1 = TVar (new_var()) in
            let x2 = TVar (new_var()) in
            let s = unify(TBool, t) in
            let env' = subst_env s env in
            let s' = unify(x1, x2) in
            let env'' = subst_env s' env' in
            let s'' = m (env'', e1, s' x1) in
            let env''' = subst_env s'' env'' in
            let s''' = m (env''', e2, s'' x2) in
            s''' @@ s'' @@ s' @@ s
        )
      | M.READ -> unify (TInt, t)
      | M.WRITE e ->
        let x1 = TVar (new_var()) in
        let s = unify(x1, t) in
        let env' = subst_env s env in
        let s' = m (env', e, s x1) in
        s' @@ s
      | M.MALLOC e ->
        let x1 = TVar (new_var()) in
        let s = unify(TLoc x1, t) in
        let env' = subst_env s env in
        let s' = m (env', e, s x1) in
        s' @@ s 
      | M.ASSIGN (e1, e2) ->
        let x1 = TVar (new_var()) in
        let s = unify(x1, t) in
        let env' = subst_env s env in
        let s' = m (env', e1, s (TLoc x1)) in
        let env'' = subst_env s' env' in
        let s'' = m (env'', e2, s' t) in
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
        let env'' = subst_env s env' in
        let s'' = m (subst_env s' env'', e2, s x2) in
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
      | TFun (t1, t2) -> M.TyArrow (toMType t1, toMType t2)
      | TVar v -> raise (M.TypeError ("Free variable: " ^ v))
    in

    (* let emptyEnv = (fun x -> raise (M.TypeError ("unbound id: " ^ x))) in *)
    let x = TVar (new_var ()) in
    let s = m ([], exp, x) in
    toMType (s x)
  (* raise (M.TypeError "Type Checker Unimplemented") *)