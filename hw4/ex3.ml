type require = id * (cond list)
and cond = 
    Items of gift list
  | Same of id
  | Common of cond * cond
  | Except of cond * gift list
and gift = int
and id = A | B | C | D | E

let union gifts1 gifts2 = 
  let gifts1' = List.filter (fun x -> not(List.mem x gifts2)) gifts1 in
  List.sort_uniq compare (gifts1' @ gifts2)

let rec con_g gl con =
  match con with
  | Items g -> g
  | Same id -> List.assoc id gl
  | Common (c1, c2) -> List.filter (fun x -> List.mem x (con_g gl c2)) (con_g gl c1)
  | Except (c, g) -> List.filter (fun x -> not(List.mem x g)) (con_g gl c)

let rec cons_g gl cons = List.fold_left (fun gl_acc con -> union (con_g gl con) gl_acc) [] cons

let rec update_gl gl reqs =
  let next_gl = List.map (fun (id, cons) -> (id, (cons_g gl cons))) reqs in
  if not(gl = next_gl) then update_gl next_gl reqs else next_gl

let shoppingList reqs =
  let empty_list = [(A,[]); (B,[]); (C,[]); (D,[]); (E,[])] in
  let reqs' = List.map (fun (x, _) -> match List.assoc_opt x reqs with | None -> (x, []) | Some r -> (x, r)) empty_list in
  update_gl empty_list reqs'