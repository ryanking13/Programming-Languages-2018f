(*
 * SNU 4190.310 Programming Languages 2018 Fall
 *  K- Interpreter Skeleton Code
 *)

(* Location Signature *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M (Loc.base,[])

  let rec replace_nth = fun l n c -> 
    match l with
    | h::t -> if n = 1 then c :: t else h :: (replace_nth t (n - 1) c)
    | [] -> raise Not_allocated

  let load (M (boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V v -> v 
    | U -> raise Not_initialized

  let store (M (boundary,storage)) loc content =
    M (boundary, replace_nth storage (Loc.diff boundary loc) (V content))

  let alloc (M (boundary,storage)) = 
    (boundary, M (Loc.increase boundary 1, U :: storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E (fun x -> raise Not_bound)
  let lookup (E (env)) id = env id
  let bind (E (env)) id loc = E (fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module K : KMINUS =
struct
  exception Error of string

  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp

  type program = exp

  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v =
    match v with
    | Num n -> n
    | _ -> raise (Error "TypeError : not int")

  let value_bool v =
    match v with
    | Bool b -> b
    | _ -> raise (Error "TypeError : not bool")

  let value_unit v =
    match v with
    | Unit -> ()
    | _ -> raise (Error "TypeError : not unit")

  let value_record v =
    match v with
    | Record r -> r
    | _ -> raise (Error "TypeError : not record")

  let lookup_env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "TypeError : not addr")) 
    with Env.Not_bound -> raise (Error "Unbound")

  let lookup_env_proc e f =
    try
      (match Env.lookup e f with
      | Addr _ -> raise (Error "TypeError : not proc") 
      | Proc (id_list, exp, env) -> (id_list, exp, env))
    with Env.Not_bound -> raise (Error "Unbound")

  let rec eval mem env e =
    match e with
    | READ x -> 
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      (v, Mem.store mem l v)
    | WRITE e ->
      let (v, mem') = eval mem env e in
      let n = value_int v in
      let _ = print_endline (string_of_int n) in
      (v, mem')
    | LETV (x, e1, e2) ->
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | ASSIGN (x, e) ->
      let (v, mem') = eval mem env e in
      let l = lookup_env_loc env x in
      (v, Mem.store mem' l v)
    | TRUE -> (Bool true, mem)
    | FALSE -> (Bool false, mem)
    | UNIT -> (Unit, mem)
    | NUM n -> (Num n, mem)
    | VAR i -> (Mem.load mem (lookup_env_loc env i), mem)
    | ADD (e1, e2) ->
        let (v', mem') = eval mem env e1 in
        let (v'', mem'') = eval mem' env e2 in
        let vi' = value_int v' in
        let vi'' = value_int v'' in
        (Num (vi' + vi''), mem'')
    | SUB (e1, e2) ->
        let (v', mem') = eval mem env e1 in
        let (v'', mem'') = eval mem' env e2 in
        let vi' = value_int v' in
        let vi'' = value_int v'' in
        (Num (vi' - vi''), mem'')
    | MUL (e1, e2) ->
        let (v', mem') = eval mem env e1 in
        let (v'', mem'') = eval mem' env e2 in
        let vi' = value_int v' in
        let vi'' = value_int v'' in
        (Num (vi' * vi''), mem'')    
    | DIV (e1, e2) ->
        let (v', mem') = eval mem env e1 in
        let (v'', mem'') = eval mem' env e2 in
        let vi' = value_int v' in
        let vi'' = value_int v'' in
        (Num (vi' / vi''), mem'')
    | EQUAL (e1, e2) ->
        let (v', mem') = eval mem env e1 in
        let (v'', mem'') = eval mem' env e2 in
        (match v' with
            | Num n ->
                (match v'' with
                    | Num n' -> (Bool (n = n'), mem'')
                    | _ -> (Bool false, mem'')
                )
            | Bool b ->
                (match v'' with
                    | Bool b' -> (Bool (b = b'), mem'')
                    | _ -> (Bool false, mem'')
                )
            | Unit ->
                (match v'' with
                    | Unit -> (Bool true, mem'')
                    | _ -> (Bool false, mem'')
                )
            | Record r -> (Bool false, mem'')
        )
    | LESS (e1, e2) ->
        let (v', mem') = eval mem env e1 in
        let (v'', mem'') = eval mem' env e2 in
        let vi' = value_int v' in
        let vi'' = value_int v'' in
        (Bool (vi' < vi''), mem'')
    | NOT (e) ->
        let (v', mem') = eval mem env e in
        let vb' = value_bool v' in
        (Bool (not vb'), mem')
    | SEQ (e1, e2) ->
        let (v', mem') = eval mem env e1 in
        let (v'', mem'') = eval mem' env e2 in
        (v'', mem'')
    | IF (e1, e2, e3) ->
        let (v', mem') = eval mem env e1 in
        let vb' = value_bool v' in
        (match vb' with
            | true -> eval mem' env e2
            | false -> eval mem' env e3
        )
    | WHILE (e1, e2) ->
        let check m e =
            let (v', m') = eval !m env e in
            value_bool v'
        in
        let _m = mem in
        let m = ref _m in
        let v = ref Unit in
        let _ =
            while (check m e1) do
                let (v', m') = eval !m env e2 in
                m := m'; v := v'
            done
        in
        (!v, !m)
    | LETF (id, params, e1, e2) ->
        eval mem (Env.bind env id (Proc (params, e1, env))) e2 
    | CALLV (id, params) ->
        (* exp list to value list *)
        let rec eval_params mem env params evaled_params =
            (match params with
                | h::t ->
                    let (v, mem') = eval mem env h in 
                    eval_params mem' env t (v::evaled_params)
                | [] -> (mem, env, evaled_params)
            )
        in

        let rec replace_params mem env id_list params =
            (match id_list with
                | ih::it -> 
                    (match params with
                        | ph::pt ->
                            let (l, mem') = Mem.alloc mem in
                            replace_params (Mem.store mem' l ph) (Env.bind env ih (Addr l)) it pt
                        | [] -> raise (Error "InvalidArg")
                    )
                | [] -> (mem, env)
            )
        in

        let (id_list, exp, proc_env) = lookup_env_proc env id in
        let (mem', env', params') = eval_params mem env params [] in
        if List.length id_list != List.length params' then raise (Error "InvalidArg")
        else (
            let params_rev' = List.rev params' in
            let (mem'', proc_env') = replace_params mem' proc_env id_list params_rev' in
            eval mem'' (Env.bind proc_env' id (Proc (id_list, exp, proc_env))) exp
        )

    | CALLR (id, params) ->
        (* id list to loc list *)
        let rec eval_params env params evaled_params =
            (match params with
                | h::t ->
                    let l = Env.lookup env h in 
                    eval_params env t (l::evaled_params)
                | [] -> (env, evaled_params)
            )
        in

        let rec replace_params env id_list params =
            (match id_list with
                | ih::it -> 
                    (match params with
                        | ph::pt ->
                            replace_params (Env.bind env ih ph) it pt
                        | [] -> raise (Error "InvalidArg")
                    )
                | [] -> env
            )
        in

        let (id_list, exp, proc_env) = lookup_env_proc env id in
        let (env', params') = eval_params env params [] in
        if List.length id_list != List.length params' then raise (Error "InvalidArg")
        else (
            let params_rev' = List.rev params' in
            let proc_env' = replace_params proc_env id_list params_rev' in
            eval mem (Env.bind proc_env' id (Proc (id_list, exp, proc_env))) exp
        )      
    | RECORD (id_exp_map) ->
        (* alloc: id * exp list to id * Loc.t list *)
        let rec alloc mem map =
            (match map with
            | (id, e)::t ->
                let (v, mem') = eval mem env e in
                let (l, mem'') = Mem.alloc mem' in
                let mem''' = (Mem.store mem'' l v) in
                let (map', mem'''') = alloc mem''' t in
                ((id, l)::map', mem'''')
            | [] -> ([], mem))
        in
        (* gen_record: (id * Loc.t list) -> id -> Loc.t *)
        let rec gen_record map _id =
            match map with
            | (id, l)::t -> if id = _id then l else gen_record t _id 
            | [] -> raise (Error "Unbound")
        in

        (match id_exp_map with
        | [] -> (Unit, mem)
        | _ ->
            let (id_loc_map, mem') = alloc mem id_exp_map in
            let ret = gen_record id_loc_map in
            (Record ret, mem')
        )
    | FIELD (e, id) ->
        let (v, mem') = eval mem env e in
        let record = value_record v in
        let loc = record id in
        let v = Mem.load mem' loc in
        (v, mem')
    | ASSIGNF (e1, id, e2) ->
        let (v, mem') = eval mem env e1 in
        let (v', mem'') = eval mem' env e2 in
        let record = value_record v in
        let loc = record id in
        let mem''' = Mem.store mem'' loc v' in
        (v', mem''')

  let run (mem, env, pgm) = 
    let (v, _ ) = eval mem env pgm in
    v
end