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

let rec key_2_string key =
  match key with
  | BAR -> "-"
  | VAR x -> x
  | NODE (key1, key2) -> "(" ^ (key_2_string key1) ^ ", " ^ (key_2_string key2) ^ ")"

let print_equ equ =
  List.map (fun (x, y) -> print_endline(key_2_string x ^ " = " ^ key_2_string y)) equ

let print_sol sol =
  List.map (fun (x, y) -> print_endline( "VAR" ^ x ^ " = " ^ key_2_string y)) sol

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
    | StarBox -> (BAR, [], ["*"])
    | NameBox str -> 
      (VAR str, [], [str])
  )
  | Branch (map1, map2) ->
    let key1, equs1, boxes1= get_equ map1 in
    let key2, equs2, boxes2= get_equ map2 in
    let beta = new_var() in
    (VAR beta, (((NODE(key2, (VAR beta))), key1) :: equs1 @ equs2), (union boxes1 boxes2))
  | Guide (str, map) ->
    let (key, equs, boxes) = get_equ map in
    (NODE((VAR str), key)), equs, boxes

let rec app_to_var var x x_value =
  match var with
  | BAR -> BAR
  | VAR y -> if x = y then x_value else (VAR y)
  | NODE (v1, v2) -> NODE(app_to_var v1 x x_value, app_to_var v2 x x_value)

let rec keyv_has_x keyv x =
  match keyv with
  | BAR -> false
  | VAR y -> x = y
  | NODE (keyv1, keyv2) -> keyv_has_x keyv1 x || keyv_has_x keyv2 x

let rec solve : (key_var * key_var) list -> (string * key_var) list -> (string * key_var) list = fun equs sol ->
  match equs with
  | [] -> sol
  | equ :: equ_tail ->
    (
      match equ with
      | BAR , BAR -> solve equ_tail sol
      | VAR x, VAR y ->
        if x = y then solve equ_tail sol else
        let equs' = List.map (fun (l,r) -> (app_to_var l x (VAR y)), (app_to_var r x (VAR y))) equ_tail in
        let sol' = List.map (fun (l,r) -> (l , (app_to_var r x (VAR y)))) sol in
        solve equs' ((x, VAR y) :: sol')
      | key, VAR x
      | VAR x, key ->
        if keyv_has_x key x then raise IMPOSSIBLE else 
        let equs' = List.map (fun (l,r) -> (app_to_var l x key), (app_to_var r x key)) equ_tail in
        let sol' = List.map (fun (l,r) -> (l, (app_to_var r x key))) sol in 
        solve equs' ((x, key) :: sol')
      | BAR,  NODE _
      | NODE _, BAR -> raise IMPOSSIBLE
      | NODE (left, right), NODE (left', right') ->
        solve ((left, left') :: (right, right') :: equ_tail) sol
    )

let rec remove_free_var key =
  match key with
  | BAR -> Bar
  | VAR _ -> Bar
  | NODE (key1, key2) -> Node (remove_free_var key1, remove_free_var key2)

let getReady map =
  let _, equs, boxes = get_equ map in
  let solution = ("*", BAR) :: (solve equs []) in  
  let keys = List.map (fun x ->  match List.assoc_opt x solution with | None -> (Bar) | Some r -> remove_free_var r) boxes in
  List.sort_uniq compare keys