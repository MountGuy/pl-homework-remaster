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

type typ_env = var -> typ

type equ = typ * typ

let (@+) tenv (var, typ) = fun x -> if x = var then typ else tenv x

let empty_tenv = fun x -> raise (M.TypeError "Wrong access of type environment")

let rec make_equ exp tenv =
  match exp with
  | M.CONST c -> (
    match c with
    | M.N i -> TInt, []
    | M.B b -> TBool, []
    | M.S s -> TString, []
  )
  | M.VAR x -> tenv x, []
  | M.FN (x, e) ->
    let v1 = new_var() in
    let t1 = TVar v1 in
    let t2, equs = make_equ e (tenv @+ (x, t1)) in
    TFun (t1, t2), equs
  | M.APP (e1, e2) ->
    let t1, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 tenv in
    let t3 = TVar (new_var()) in
    t3, equs1 @ equs2 @ [TFun (t2, t3), t1]
  | M.LET (M.VAL (x, e1), e2) ->
    let t1, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 (tenv @+ (x, t1)) in
    t2, equs1 @ equs2
  | M.LET (M.REC (f, x, body), e) ->
    let t1 = TVar (new_var()) in
    let t2 = TVar (new_var()) in
    let t3, equs3 = make_equ body ((tenv @+ (x, t1)) @+ (f, TFun (t1, t2))) in
    let t4, equs4 = make_equ e (tenv @+ (f, TFun (t1, t2))) in
    t4, equs3 @ equs4 @ [t2, t3]
  | M.IF (e1, e2, e3) ->
    let t1, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 tenv in
    let t3, equs3 = make_equ e3 tenv in
    t2, equs1 @ equs2 @ equs3 @ [t1, TBool; t2, t3]
  | M.BOP (M.ADD, e1, e2)
  | M.BOP (M.SUB, e1, e2) ->
    let t1, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 tenv in
    TInt, equs1 @ equs2 @ [t1, TInt; t2, TInt]
  | M.BOP (M.EQ, e1, e2) ->
    let t1, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 tenv in
    TBool, equs1 @ equs2 @ [t1, t2]
  | M.BOP (M.AND, e1, e2)
  | M.BOP (M.OR, e1, e2) ->
    let t1, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 tenv in
    TBool, equs1 @ equs2 @ [t1, TBool; t2, TBool]
  | M.READ -> TInt, []
  | M.WRITE e -> make_equ e tenv
  | M.MALLOC e ->
    let t, equs = make_equ e tenv in
    TLoc t, equs
  | M.ASSIGN (e1, e2) ->
    let t1, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 tenv in
    t2, equs1 @ equs2 @ [TLoc t2, t1]
  | M.BANG e ->
    let t, equs = make_equ e tenv in
    let t1 = TVar (new_var()) in
    t1, equs @ [t, TLoc t1]
  | M.SEQ (e1, e2) ->
    let _, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 tenv in
    t2, equs1 @ equs2
  | M.PAIR (e1, e2) ->
    let t1, equs1 = make_equ e1 tenv in
    let t2, equs2 = make_equ e2 tenv in
    TPair (t1, t2), equs1 @ equs2
  | M.FST e ->
    let t, equs = make_equ e tenv in
    let t1 = TVar (new_var()) in
    let t2 = TVar (new_var()) in
    t1, equs @ [t, TPair (t1, t2)]
  | M.SND e ->
    let t, equs = make_equ e tenv in
    let t1 = TVar (new_var()) in
    let t2 = TVar (new_var()) in
    t2, equs @ [t, TPair (t1, t2)]

let rec app_sol typ_sol x typ =
  match typ with
  | TInt
  | TBool
  | TString -> typ
  | TPair (t1, t2) -> TPair (app_sol typ_sol x t1, app_sol typ_sol x t2)
  | TLoc t -> TLoc (app_sol typ_sol x t)
  | TFun (t1, t2) -> TFun (app_sol typ_sol x t1, app_sol typ_sol x t2)
  | TVar t -> if t = x then typ_sol else TVar t

let rec solve_equ equs =
  match equs with
  | equ :: equ_tail ->
  (
    match equ with
    | TInt, TInt
    | TBool, TBool
    | TString, TString -> solve_equ equ_tail
    | typ, TVar v
    | TVar v, typ ->
      let equ_tail' = List.map (fun (t1, t2) -> (app_sol typ v t1, app_sol typ v t2)) equ_tail in
      (v, typ) :: (solve_equ equ_tail')
    | TPair (t1f, t1s), TPair (t2f, t2s) -> solve_equ ([t1f, t2f; t1s, t2s] @ equ_tail)
    | TFun (t1x, t1f), TFun (t2x, t2f) -> solve_equ ([t1x, t2x; t1f, t2f] @ equ_tail)
    | TLoc (t1), TLoc (t2) -> solve_equ ([t1, t2] @ equ_tail)
    | _ -> raise (M.TypeError "Invalid expression")
  )
  | [] -> []

(* TODO : Implement this function *)
let check : M.exp -> M.types = fun exp ->
  let t, equs = make_equ exp empty_tenv in
  let sols = solve_equ equs in

  let rec remove_var typ sols =
    match sols with
    | [] -> typ
    | (v, t) :: sol_tail -> remove_var (app_sol t v typ) sol_tail in
  let t' = remove_var t sols in

  let rec tvar_to_m_typ t =
    match t with
    | TInt -> M.TyInt
    | TBool -> M.TyBool
    | TString -> M.TyString
    | TPair (t1, t2) -> M.TyPair (tvar_to_m_typ t1, tvar_to_m_typ t2)
    | TLoc t -> M.TyLoc (tvar_to_m_typ t)
    | TFun (t1, t2) -> M.TyArrow (tvar_to_m_typ t1, tvar_to_m_typ t2)
    | _ -> raise (M.TypeError "Invalid expression") in
  tvar_to_m_typ t'