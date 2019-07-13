type treasure = StarBox | NameBox of string
type key = Bar | Node of key * key
type map = 
    End of treasure
  | Branch of map * map
  | Guide of string * map

type key_var = 
    BAR 
  | VAR of string 
  | NODE of key_var * key_var
type key_equ = key_var * key_var

exception IMPOSSIBLE

let count = ref 0
  
let new_var () =
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

let rec union var_set1 var_set2 =
  match var_set1 with
  | [] -> var_set2
  | var :: var_tail ->
    let union_var = union var_tail var_set2 in
    if List.exists (fun x -> x = var) union_var then union_var else var :: union_var

let rec get_equ map =
  match map with
  | End treasure ->
  (
    match treasure with
    | StarBox -> (BAR, [], ["*"], ["*"])
    | NameBox str -> 
      (VAR str, [], [str], [str])
  )
  | Branch (map1, map2) ->
    let key1, equs1, boxes1, vars1 = get_equ map1 in
    let key2, equs2, boxes2, vars2 = get_equ map2 in
    let beta = new_var() in
    let vars = union vars1 (union [beta] vars2) in
    (VAR beta, (((NODE(key2, (VAR beta))), key1) :: equs1 @ equs2), (union boxes1 boxes2), vars )
  | Guide (str, map) ->
    let (key, equs, boxes, vars) = get_equ map in
    (NODE((VAR str), key)), equs, boxes, vars

let rec is_const key_var =
  match key_var with
  | BAR -> true
  | NODE (key_var1, key_var2) -> (is_const key_var1) && (is_const key_var2)
  | _ -> false

let rec key_var_to_key key_var =
  match key_var with
  | BAR -> Bar
  | NODE (key_var1, key_var2) -> Node(key_var_to_key key_var1, key_var_to_key key_var2)
  | _ -> raise IMPOSSIBLE

let rec app_to_var var x x_value =
  match var with
  | BAR -> BAR
  | VAR y -> if x = y then x_value else (VAR y)
  | NODE (v1, v2) -> NODE(app_to_var v1 x x_value, app_to_var v2 x x_value)

let rec solve equs =
  match equs with
  | [] -> []
  | equ :: equ_tail ->
    let lhs, rhs = equ in
    (
      match lhs with
      | BAR ->
      (
        match rhs with
        | BAR -> solve equ_tail
        | VAR x ->
          let equs' = List.map (fun (l,r) -> (app_to_var l x BAR), (app_to_var r x BAR)) equ_tail in
          (x, BAR) :: (solve equs')
        | NODE _ -> raise IMPOSSIBLE
      )
      | VAR x ->
      (
        match rhs with
        | BAR ->
          let equs' = List.map (fun (l,r) -> (app_to_var l x BAR), (app_to_var r x BAR)) equ_tail in
          (x, BAR) :: (solve equs')
        | VAR y ->
          if x = y then solve equ_tail else
          let equs' = List.map (fun (l,r) -> (app_to_var l x (VAR y)), (app_to_var r x (VAR y))) equ_tail in
          (x, (VAR y)) :: (solve equs')
        | NODE (left, right) ->
          let equs' = List.map (fun (l,r) -> (app_to_var l x (NODE (left, right))), (app_to_var r x (NODE (left, right)))) equ_tail in
          (x, (NODE (left, right))) :: (solve equs')
      )
      | NODE (left, right) ->
      (
        match rhs with
        | BAR -> raise IMPOSSIBLE
        | VAR x ->
          let equs' = List.map (fun (l,r) -> (app_to_var l x (NODE (left, right))), (app_to_var r x (NODE (left, right)))) equ_tail in
          (x, (NODE (left, right))) :: (solve equs')
        | NODE (left', right') ->
          solve ((left, left') :: (right, right') :: equ_tail)
      )
    )

let rec remove_free_var vars sol =
  match vars with
  | [] -> sol
  | var :: var_tail ->
    if List.exists (fun (x,_) -> x = var) sol 
    then remove_free_var var_tail sol 
    else
    (
      let sol' = List.map (fun (x, y) -> (x, app_to_var y var BAR)) sol in
      remove_free_var var_tail ((var, BAR) :: sol') 
    )

let rec remove_var var sol =
  match var with
  | BAR -> (BAR, false)
  | VAR x -> 
    let _, value = List.find (fun (y,_) -> y = x) sol in
    if is_const value then (value, true) else (var, false)
  | NODE (var1, var2) ->
    let var1', bool1 = remove_var var1 sol in
    let var2', bool2 = remove_var var2 sol in
    (NODE(var1', var2')), bool1 || bool2

let rec refine_sol sol =
  let map (x, var) =
  (
    let var', bool = remove_var var sol in
    (x, var'), bool
  ) in
  let sol', bools = List.split (List.map map sol) in
  if List.exists (fun x -> x) bools then refine_sol sol' else sol'

let rec pick_keys boxes sol =
  match boxes with
  | [] -> []
  | box :: box_tail ->
    if box = "*" 
    then union [Bar] (pick_keys box_tail sol) 
    else 
      let _, key = (List.find (fun (x,_) -> x = box) sol) in
      union (pick_keys box_tail sol) [key_var_to_key key]

let getReady map =
  let _, equs, boxes, vars = get_equ map in
  pick_keys boxes (refine_sol (remove_free_var vars (solve equs)))