type treasure = StarBox | NameBox of string
type key = Bar | Node of key * key
type map = 
    End of treasure
  | Branch of map * map
  | Guide of string * map
exception IMPOSSIBLE

type key_var = 
    BAR 
  | VAR of string 
  | NODE of key_var * key_var

let rec make_subst x keyv =
  let rec subs keyv' =
    match keyv' with
    | BAR -> BAR
    | VAR x' -> if x = x' then keyv else keyv'
    | NODE (keyv1, keyv2) -> NODE (subs keyv1, subs keyv2) in
  subs

let (@@) sub1 sub2 = (fun keyv -> sub1 (sub2 keyv))

let rec keyv_has_x keyv x =
  match keyv with
  | BAR -> false
  | NODE (keyv1, keyv2) -> keyv_has_x keyv1 x || keyv_has_x keyv2 x
  | VAR x' -> x = x'

let rec unify keyv1 keyv2 =
  match keyv1, keyv2 with
  | BAR, BAR -> fun x -> x
  | VAR x1, VAR x2 -> make_subst x1 keyv2
  | VAR x, keyv | keyv, VAR x ->
    if keyv_has_x keyv x then raise IMPOSSIBLE else make_subst x keyv
  | NODE (keyv1, keyv2), NODE (keyv1', keyv2') ->
    let s1 = unify keyv1 keyv1' in
    let s2 = unify (s1 keyv2) (s1 keyv2') in
    s2 @@ s1
  | _ -> raise IMPOSSIBLE

let rec solve map subs count =
  match map with
  | End StarBox -> subs, BAR, [VAR "*"], count
  | End NameBox x -> subs, subs (VAR x), [VAR x], count
  | Branch (map1, map2) ->
    let s1, keyv1, boxes1, count' = solve map1 subs count in
    let s2, keyv2, boxes2, count'' = solve map2 s1 count' in
    let beta = VAR ("x_" ^ (string_of_int count'')) in
    let s3 = unify (s2 keyv1) (NODE (keyv2, beta)) in
    s3 @@ s2, s3 beta, boxes1 @ boxes2, count'' + 1
  | Guide (x, map') ->
    let s, keyv, boxes, count' = solve map' subs count in
    s, NODE (s (VAR x), keyv), boxes, count'

let getReady map =
  let s, keyv, boxes, _ = solve map (fun x -> x) 0 in
  let x_keys = List.map (fun k -> k, s k) boxes in
  let sol = List.fold_left (fun sub (x, keyv) -> (unify x (sub keyv)) @@ sub) (fun x -> x) x_keys in
  let keys = List.map (fun x -> sol x) boxes in
  let rec keyv_to_key keyv =
    match keyv with
    | BAR | VAR _ -> Bar
    | NODE (keyv1, keyv2) -> Node (keyv_to_key keyv1, keyv_to_key keyv2) in
  List.sort_uniq compare (List.map keyv_to_key keys)e