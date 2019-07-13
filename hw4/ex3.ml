type require = id * (cond list)
and cond = 
    Items of gift list
  | Same of id
  | Common of cond * cond
  | Except of cond * gift list
and gift = int
and id = A | B | C | D | E

let gifts_of_id gifts_list id =
  if List.exists (fun (x, _) -> x = id) gifts_list then
    let _, list = List.find (fun (x,_) -> x = id) gifts_list in
    list
  else
    [] 

let rec union gifts1 gifts2 = 
  match gifts1 with
  | [] -> gifts2
  | gift :: gift_tail ->
    let union_list = union gift_tail gifts2 in
    if List.exists (fun x -> x = gift) union_list then union_list else gift :: union_list

let rec common gifts1 gifts2 =
  match gifts1 with
  | [] -> []
  | gift :: gift_tail ->
    let common_list = common gift_tail gifts2 in
    if List.exists (fun x -> x = gift) gifts2 then gift :: common_list else common_list

let rec except gifts1 gifts2 =
  match gifts1 with
  | [] -> []
  | gift :: gift_tail ->
    let except_list = except gift_tail gifts2 in
    if List.exists (fun x -> x = gift) gifts2 then except_list else gift :: except_list

let equal gifts1 gifts2 =
  (except gifts1 gifts2 = []) && (except gifts2 gifts1 = [])

let rec gift_of_cond gifts_list cond =
  match cond with
  | Items gifts -> gifts
  | Same id -> gifts_of_id gifts_list id
  | Common (con1, con2) -> common (gift_of_cond gifts_list con1) (gift_of_cond gifts_list con2)
  | Except (con, gifts) -> except (gift_of_cond gifts_list con) gifts

let rec gift_of_conds gifts_list conds =
  match conds with
  | [] -> []
  | cond :: cond_tail -> union (gift_of_cond gifts_list cond) (gift_of_conds gifts_list cond_tail)

let rec update_gifts_list gifts_list req_list =
  let next_gifts_list = List.map (fun (id, conds) -> (id, (gift_of_conds gifts_list conds))) req_list in
  let is_equal = List.map (fun (id, gifts) -> equal gifts (gifts_of_id gifts_list id)) next_gifts_list in
  if List.exists (fun x -> not(x)) is_equal 
    then update_gifts_list next_gifts_list req_list 
    else next_gifts_list

let shoppingList req_list =
  let initial_list = [(A,[]); (B,[]); (C,[]); (D,[]); (E,[])] in
  let raw_list = update_gifts_list initial_list req_list in
  let sorted_list = List.map (fun (id, list) -> (id, List.sort (fun x y -> x - y) list)) raw_list in
  List.map (fun (id, _) -> id, (gifts_of_id sorted_list id) ) initial_list