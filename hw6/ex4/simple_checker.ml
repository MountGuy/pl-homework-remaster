(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton Code
 *)

open M
open Pp

type var = string

let count = ref 0 

let new_var () = 
  let _ = count := !count + 1 in
  "x_" ^ (string_of_int !count)

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  | TEVar of var
  | TWVar of var
  (* Modify, or add more if needed *)

let (@+) (var, typ) tenv = fun x -> if x = var then typ else tenv x

let empty_subst = fun t -> t

let make_subst = fun x t ->
  let rec subs t' =
    match t' with
    | TVar x' | TEVar x' | TWVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TInt | TBool | TString -> t'
  in subs

let (@@) s s' = (fun t -> s (s' t)) (* substitution composition *)

let rec typ_has_x typ x =
  match typ with
  | TWVar v | TEVar v | TVar v -> v = x 
  | TInt | TBool | TString -> false
  | TPair (t1, t2) | TFun (t1, t2) -> typ_has_x t1 x || typ_has_x t2 x
  | TLoc t -> typ_has_x t x

let rec unify typ1 typ2 =
  match typ1, typ2 with
  | TInt, TInt | TBool, TBool | TString, TString -> empty_subst
  | TWVar v, TInt | TWVar v, TBool | TWVar v, TString | TWVar v, TWVar _ 
  | TEVar v, TInt | TEVar v, TBool | TEVar v, TString | TEVar v, TWVar _ 
  | TVar v, TWVar _ | TEVar v, TEVar _ | TVar v, TEVar _ | TVar v, TVar _ -> make_subst v typ2
  | TInt, TWVar v | TBool, TWVar v | TString, TWVar v 
  | TInt, TEVar v | TBool, TEVar v | TString, TEVar v
  | TWVar _, TEVar v | TWVar _, TVar v | TEVar _, TVar v -> make_subst v typ1
  | TEVar v, TLoc typ | TLoc typ, TEVar v ->
    if typ_has_x typ v then raise (M.TypeError "unify2") else make_subst v (TLoc typ) 
  | TVar v, typ | typ, TVar v ->
    if typ_has_x typ v then raise (M.TypeError "unify2") else make_subst v typ
  | TPair (t1, t2), TPair (t1', t2')
  | TFun (t1, t2), TFun (t1', t2') ->
    let s = unify t1 t1' in
    let s' = unify (s t2) (s t2') in
    s' @@ s
  | TLoc l1, TLoc l2 -> unify l1 l2
  | _ -> raise (M.TypeError "unify3")

let rec w tenv exp =
  match exp with
  | M.CONST (M.N _) -> empty_subst, TInt
  | M.CONST (M.B _) -> empty_subst, TBool
  | M.CONST (M.S _) -> empty_subst, TString
  | M.VAR x -> empty_subst, (tenv x)
  | M.FN (x, e) -> 
    let beta = TVar (new_var()) in
    let s1, t1 = w ((x, beta) @+ tenv) e in
    s1, TFun (s1 beta, t1)
  | M.APP (e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2, t2 = w (s1 @@ tenv) e2 in
    let beta = TVar(new_var()) in
    let s3 = unify (s2 t1) (TFun (t2, beta)) in
    s3 @@ s2 @@ s1, s3 beta
  | M.LET (M.VAL (x, e1), e2) ->
    let s1, t1 = w tenv e1 in
    let s2, t2 = w ((x, t1) @+ (s1 @@ tenv)) e2 in
    s2 @@ s1, t2
  | M.LET (M.REC (f, x, e1), e2) ->
    let beta = TVar(new_var()) in
    let s1, t1 = w ((f, beta) @+ tenv) (M.FN(x, e1)) in
    let s2 = unify (s1 beta) t1 in
    let s3, t3 = w ((f, (s2 t1)) @+ tenv) e2 in
    s3 @@ s2 @@ s1, t3
  | M.IF (e1, e2, e3) ->
    let s1, t1 = w tenv e1 in
    let s2 = unify t1 TBool in
    let s3, t3 = w ((s2 @@ s1) @@ tenv) e2 in
    let s4, t4 = w ((s3 @@ s2 @@ s1) @@ tenv) e3 in
    let s5 = unify (s4 t3) t4 in
    s5 @@ s4 @@ s3 @@ s2 @@ s1, (s5 t4)
  | M.BOP (M.ADD, e1, e2)
  | M.BOP (M.SUB, e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2 = unify TInt t1 in
    let s3, t3 = w ((s2 @@ s1) @@ tenv) e2 in
    let s4 = unify TInt t3 in
    s4 @@ s3 @@ s2 @@ s1, TInt
  | M.BOP (M.EQ, e1, e2) ->
    let s1, t1 = w tenv e1 in
    let beta = TEVar(new_var()) in
    let s2 = unify beta t1 in
    let s3, t3 = w ((s2 @@ s1) @@ tenv) e2 in
    let s4 = unify ((s3 @@ s2) beta) t3 in
    s4 @@ s3 @@ s2 @@ s1, TBool
  | M.BOP (M.AND, e1, e2)
  | M.BOP (M.OR, e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2 = unify TBool t1 in
    let s3, t3 = w ((s2 @@ s1) @@ tenv) e2 in
    let s4 = unify TBool t3 in
    s4 @@ s3 @@ s2 @@ s1, TBool
  | M.READ -> empty_subst, TInt
  | M.WRITE e ->
    let beta = TWVar(new_var()) in
    let s1, t1 = w tenv e in
    let s2 = unify t1 beta in
    s2 @@ s1, s2 beta
  | M.MALLOC e ->
    let s1, t1 = w tenv e in
    s1, TLoc t1
  | M.ASSIGN (e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2, t2 = w (s1 @@ tenv) e2 in
    let s3 = unify (s2 t1) (TLoc t2) in
    s3 @@ s2 @@ s1, s3 t2
  | M.BANG e ->
    let beta = TVar(new_var()) in
    let s1, t1 = w tenv e in
    let s2 = unify t1 (TLoc beta) in
    s2 @@ s1, s2 beta
  | M.SEQ (e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2, t2 = w (s1 @@ tenv) e2 in
    s2 @@ s1, t2
  | M.PAIR (e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2, t2 = w (s1 @@ tenv) e2 in
    s2 @@ s1, TPair(s2 t1, t2)
  | M.FST e ->
    let tf = TVar(new_var()) in
    let ts = TVar(new_var()) in
    let s1, t1 = w tenv e in
    let s2 = unify t1 (TPair(tf, ts)) in
    s2 @@ s1, s2 tf
  | M.SND e ->
    let tf = TVar(new_var()) in
    let ts = TVar(new_var()) in
    let s1, t1 = w tenv e in
    let s2 = unify t1 (TPair(tf, ts)) in
    s2 @@ s1, s2 ts

(* TODO : Implement this function *)
let check : M.exp -> M.types = fun exp ->
  let s, typ = w (fun x -> (TVar x)) exp in
  let rec tvar_to_m_typ t =
    match t with
    | TInt -> M.TyInt
    | TBool -> M.TyBool
    | TString -> M.TyString
    | TPair (t1, t2) -> M.TyPair (tvar_to_m_typ t1, tvar_to_m_typ t2)
    | TLoc t -> M.TyLoc (tvar_to_m_typ t)
    | TFun (t1, t2) -> M.TyArrow (tvar_to_m_typ t1, tvar_to_m_typ t2)
    | _ -> raise (M.TypeError "Invalid expression") in
  tvar_to_m_typ typ