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
  | TFun of typ * typ
  | TLoc of typ
  | TVar of var
  | TEVar of var
  | TWVar of var

type typ_scheme =
  | SimpleTyp of typ
  | GenTyp of (var list * typ)

type typ_env = (M.id * typ_scheme) list

let get_scheme tenv x = List.assoc x tenv

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

let rec ftv_of_typ : typ -> var list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2)
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TVar v | TEVar v | TWVar v -> [v]

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas

let ftv_of_env : typ_env -> var list = fun tyenv ->
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

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' =
    match t' with
    | TVar x' | TEVar x' | TWVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TInt | TBool | TString -> t'
  in subs

let (@@) s s' = (fun t -> s (s' t)) (* substitution composition *)

let rec change_var : var -> var -> typ -> typ = fun x y t ->
  match t with
    | TVar x' -> if (x = x') then TVar y else t
    | TEVar x' -> if (x = x') then TEVar y else t
    | TWVar x' -> if (x = x') then TWVar y else t
    | TPair (t1, t2) -> TPair (change_var x y t1, change_var x y t2)
    | TFun (t1, t2) -> TFun (change_var x y t1, change_var x y t2)
    | TLoc t' -> TLoc (change_var x y t')
    | TInt | TBool | TString -> t

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* s (\all a.t) = \all b.s{a->b}t  (where b is new variable) *)
    let betas = List.map (fun _ -> new_var()) alphas in
    let t' = List.fold_left2 (fun acc_typ alpha beta -> change_var alpha beta acc_typ) t alphas betas in 
    GenTyp (betas, subs t')

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

let instantize tyscm =
  match subst_scheme empty_subst tyscm with
  | SimpleTyp t -> t
  | GenTyp (_, t) -> t

let rec expansive exp =
  match exp with
  | M.CONST _ | M.VAR _ | M.FN   _ -> false
  | M.APP _ | M.READ | M.MALLOC _ -> true
  | M.LET (M.REC _, e) | M.WRITE e | M.BANG e | M.FST e | M.SND e -> expansive e
  | M.LET (M.VAL (_, e1), e2)
  | M.BOP (_, e1, e2)
  | M.ASSIGN (e1, e2)
  | M.SEQ (e1, e2)
  | M.PAIR (e1, e2) -> expansive e1 || expansive e2
  | M.IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3

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
  | M.VAR x -> 
    let x_scheme = List.assoc x tenv in
    empty_subst, (instantize x_scheme)
  | M.FN (x, e) -> 
    let beta = TVar (new_var()) in
    let s1, t1 = w ([x, SimpleTyp beta] @ tenv) e in
    s1, TFun (s1 beta, t1)
  | M.APP (e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2, t2 = w (subst_env s1 tenv) e2 in
    let beta = TVar(new_var()) in
    let s3 = unify (s2 t1) (TFun (t2, beta)) in
    s3 @@ s2 @@ s1, s3 beta
  | M.LET (M.VAL (x, e1), e2) ->
    let s1, t1 = w tenv e1 in
    let sche_t1 = if expansive e1 then SimpleTyp t1 else generalize (subst_env s1 tenv) t1 in
    let s2, t2 = w ([x, sche_t1] @ (subst_env s1 tenv)) e2 in
    s2 @@ s1, t2
  | M.LET (M.REC (f, x, e1), e2) ->
    let beta = TVar(new_var()) in
    let s1, t1 = w ([f, SimpleTyp beta] @ tenv) (M.FN(x, e1)) in
    let s2 = unify (s1 beta) t1 in
    let s3, t3 = w ([f, generalize (subst_env (s2 @@ s1) tenv) (s2 t1)] @ tenv) e2 in
    s3 @@ s2 @@ s1, t3
  | M.IF (e1, e2, e3) ->
    let s1, t1 = w tenv e1 in
    let s2 = unify t1 TBool in
    let s3, t3 = w (subst_env (s2 @@ s1) tenv) e2 in
    let s4, t4 = w (subst_env (s3 @@ s2 @@ s1) tenv) e3 in
    let s5 = unify (s4 t3) t4 in
    s5 @@ s4 @@ s3 @@ s2 @@ s1, (s5 t4)
  | M.BOP (M.ADD, e1, e2)
  | M.BOP (M.SUB, e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2 = unify TInt t1 in
    let s3, t3 = w (subst_env (s2 @@ s1) tenv) e2 in
    let s4 = unify TInt t3 in
    s4 @@ s3 @@ s2 @@ s1, TInt
  | M.BOP (M.EQ, e1, e2) ->
    let s1, t1 = w tenv e1 in
    let beta = TEVar(new_var()) in
    let s2 = unify beta t1 in
    let s3, t3 = w (subst_env (s2 @@ s1) tenv) e2 in
    let s4 = unify ((s3 @@ s2) beta) t3 in
    s4 @@ s3 @@ s2 @@ s1, TBool
  | M.BOP (M.AND, e1, e2)
  | M.BOP (M.OR, e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2 = unify TBool t1 in
    let s3, t3 = w (subst_env (s2 @@ s1) tenv) e2 in
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
    let s2, t2 = w (subst_env s1 tenv) e2 in
    let s3 = unify (s2 t1) (TLoc t2) in
    s3 @@ s2 @@ s1, s3 t2
  | M.BANG e ->
    let beta = TVar(new_var()) in
    let s1, t1 = w tenv e in
    let s2 = unify t1 (TLoc beta) in
    s2 @@ s1, s2 beta
  | M.SEQ (e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2, t2 = w (subst_env s1 tenv) e2 in
    s2 @@ s1, t2
  | M.PAIR (e1, e2) ->
    let s1, t1 = w tenv e1 in
    let s2, t2 = w (subst_env s1 tenv) e2 in
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

let check : M.exp -> M.typ = fun exp ->
  let s, t = w [] exp in
  let rec typ_to_mtyp typ =
    match typ with
    | TInt -> M.TyInt
    | TBool -> M.TyBool
    | TString -> M.TyString
    | TPair (t1, t2) -> M.TyPair(typ_to_mtyp t1, typ_to_mtyp t2)
    | TLoc t -> M.TyLoc(typ_to_mtyp t)
    | _ -> raise (M.TypeError "typ to m typ") in
  typ_to_mtyp t