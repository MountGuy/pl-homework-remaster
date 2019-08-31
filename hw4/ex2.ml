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

let count = ref 0
let new_var () =
  let _ = count := !count + 1 in
  "x_" ^ (string_of_int !count)
  
let union set1 set2 =
  let set1' = List.filter (fun v -> not (List.mem v set2)) set1 in
  set1' @ set2

let empty_subst = fun x -> x

let rec make_subst x keyv =
  let rec subs keyv' =
    match keyv' with
    | BAR -> BAR
    | VAR x' -> if x = x' then keyv else keyv'
    | NODE (keyv1, keyv2) -> NODE (subs keyv1, subs keyv2)
    in subs

let (@@) sub1 sub2 = (fun keyv -> sub1 (sub2 keyv))

let keyv_has_x keyv x =
  let rec keyv_has_x' keyv x =
    match keyv with
    | BAR -> false
    | NODE (keyv1, keyv2) -> keyv_has_x' keyv1 x || keyv_has_x' keyv2 x
    | VAR x' -> x = x' in
  match keyv with
  | VAR _ -> false
  | _ -> keyv_has_x' keyv x

let rec unify keyv1 keyv2 =
  match keyv1, keyv2 with
  | BAR, BAR -> empty_subst
  | VAR x, keyv | keyv, VAR x ->
    if keyv_has_x keyv x then raise IMPOSSIBLE else make_subst x keyv
  | NODE (keyv1, keyv2), NODE (keyv1', keyv2') ->
    let s1 = unify keyv1 keyv1' in
    let s2 = unify (s1 keyv2) (s1 keyv2') in
    s2 @@ s1
  | _ -> raise IMPOSSIBLE

let rec solve map subs =
  match map with
  | End StarBox -> subs, BAR, ["*"]
  | End NameBox x -> subs, subs (VAR x), [x]
  | Branch (map1, map2) ->
    let s1, keyv1, boxes1 = solve map1 subs in
    let s2, keyv2, boxes2 = solve map2 s1 in
    let beta = VAR (new_var()) in
    let s3 = unify (s2 keyv1) (NODE(keyv2, beta)) in
    s3 @@ s2, s3 beta, union boxes1 boxes2
  | Guide (x, map') ->
    let s, keyv, boxes = solve map' subs in
    s, NODE (s (VAR x), keyv), boxes

let getReady map =
  let s, keyv, boxes = solve map empty_subst in
  let x_keys = List.map (fun x -> VAR x, s (VAR x)) boxes in
  let s' = List.fold_left (fun sub (x, keyv) -> (unify x (sub keyv)) @@ sub) empty_subst x_keys in
  let keys = List.map (fun x -> s' (VAR x)) boxes in
  let rec keyv_to_key keyv =
    match keyv with
    | BAR | VAR _ -> Bar
    | NODE (keyv1, keyv2) -> Node(keyv_to_key keyv1, keyv_to_key keyv2) in
  let rec compare_key key1 key2 =
    match key1, key2 with
    | Bar, Bar -> 0
    | Node (k1, k2), Node (k1', k2') -> (compare_key k1 k1') * 100 + (compare_key k2 k2')
    | Bar, Node _ -> 1 
    | Node _, Bar -> -1 in
  List.sort_uniq compare_key (List.map keyv_to_key keys)