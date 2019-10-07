(*
 * SNU 4190.310 Programming Languages 2017 Fall
 *  K- Interpreter Skeleton Code
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
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
    | NUM n -> Num n, mem
    | TRUE -> Bool true, mem
    | FALSE -> Bool false, mem
    | UNIT -> Unit, mem
    | VAR x -> (Mem.load mem (lookup_env_loc env x)), mem
    | ADD (e1, e2) 
    | SUB (e1, e2) 
    | MUL (e1, e2) 
    | DIV (e1, e2) 
    | EQUAL (e1, e2)
    | LESS (e1, e2) ->
      let v1, mem' = eval mem env e1 in
      let v2, mem'' = eval mem' env e2 in
      (
        match e with
        | ADD _ -> Num (value_int v1 + value_int v2), mem''
        | SUB _ -> Num (value_int v1 - value_int v2), mem''
        | MUL _ -> Num (value_int v1 * value_int v2), mem''
        | DIV _ -> Num (value_int v1 / value_int v2), mem''
        | EQUAL _ -> 
        (
          match v1, v2 with
          | Num n1, Num n2 -> Bool (n1 = n2), mem''
          | Bool b1, Bool b2 -> Bool (b1 = b2), mem''
          | Unit, Unit -> Bool true, mem''
          | _ -> Bool false, mem''
        )
        | LESS _ -> Bool (value_int v1 < value_int v2), mem''
        | _ -> raise (Error "Impossible case")
      )
    | NOT e ->
      let v, mem' = eval mem env e in
      Bool (not(value_bool v)), mem'
    | SEQ (e1, e2) ->
      let _, mem' = eval mem env e1 in
      eval mem' env e2
    | IF (e1, e2, e3) ->
      let v, mem' = eval mem env e1 in
      if value_bool v
      then eval mem' env e2
      else eval mem' env e3
    | WHILE (e1, e2) ->
      let v, mem' = eval mem env e1 in
      if value_bool v
      then let _, mem'' = eval mem' env e2 in
        eval mem'' env (WHILE (e1, e2))
      else Unit, mem'
    | LETV (x, e1, e2) ->
      let v, mem' = eval mem env e1 in
      let l, mem'' = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | LETF (f, par_list, e1, e2) ->
      eval mem (Env.bind env f (Proc (par_list, e1, env))) e2
    | CALLV (f, exp_list) ->
      let x_list, e', env' = lookup_env_proc env f in
      let _ = if List.length exp_list != List.length x_list then raise (Error "InvalidArg") in
      let fold (env_acc, mem_acc) x exp =
        let v, m' = eval mem_acc env exp in
        let l, m'' = Mem.alloc m' in
        Env.bind env_acc x (Addr l), Mem.store m'' l v in
      let env'', mem'' = List.fold_left2 fold (env', mem) x_list exp_list in
      let env''' = Env.bind env'' f (Proc (x_list, e', env')) in
      eval mem'' env''' e'
    | CALLR (f, y_list) ->
      let x_list, e, env' = lookup_env_proc env f in
      let _ = if List.length x_list != List.length y_list then raise (Error "InvalidArg") in
      let fold env_acc x y = Env.bind env_acc x (Addr (lookup_env_loc env y)) in
      let env'' = List.fold_left2 fold env' x_list y_list in
      let env''' = Env.bind env'' f (Proc (x_list, e, env')) in
      eval mem env''' e
    | RECORD id_exp_list ->
      if List.length id_exp_list = 0 then Unit, mem else
      let fold (mem_acc, rec_acc) (id, exp) =
        let v, m = eval mem_acc env exp in
        let l, m' = Mem.alloc m in
        Mem.store m' l v, fun r -> if r = id then l else rec_acc r in
      let mem', r = List.fold_left fold (mem, fun x -> raise (Error "Unbound")) id_exp_list in
      Record r, mem'
    | FIELD (e, x) ->
      let r, mem' = eval mem env e in
      Mem.load mem' (value_record r x), mem'
    | ASSIGN (x, e) ->
      let v, mem' = eval mem env e in
      let l = lookup_env_loc env x in
      v, Mem.store mem' l v
    | ASSIGNF (e1, x, e2) ->
      let r, mem' = eval mem env e1 in
      let v, mem'' = eval mem' env e2 in
      v, Mem.store mem'' (value_record r x) v
    | READ x ->
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      v, Mem.store mem l v
    | WRITE e ->
      let v, mem' = eval mem env e in
      let _ = Printf.printf "%d\n" (value_int v) in
      v, mem'

  let run (mem, env, pgm) =
    let v, _  = eval mem env pgm in
    v
end
