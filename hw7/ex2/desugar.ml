(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 *)

open Xexp

let count = ref 0

let new_name () = 
  let _ = count := !count + 1 in
  "x_" ^ (string_of_int !count)

let rec alpha_conv exp subst = 
  match exp with
  | Num n -> Num n
  | Var x -> (try Var (List.assoc x subst) with Not_found -> Var x)
  | Fn (x, e) ->
    let x' = new_name () in
    let subst' = (x, x') :: subst in
    Fn (x', alpha_conv e subst')
  | App (e1, e2) -> App (alpha_conv e1 subst, alpha_conv e2 subst)
  | If (e1, e2, e3) -> If (alpha_conv e1 subst, alpha_conv e2 subst, alpha_conv e3 subst)
  | Equal (e1, e2) -> Equal (alpha_conv e1 subst, alpha_conv e2 subst)
  | Raise e -> Raise (alpha_conv e subst)
  | Handle (e1, n, e2) -> Handle (alpha_conv e1 subst, n, alpha_conv e2 subst)

(* TODO : Implement this function *)

let app_k_h e ek eh = App(App(e, ek), eh)
let fn_k_h e k h = Fn(k, Fn(h, e))

let rec removeExn' e =
  let k = new_name() in
  let h = new_name() in
  match e with
  | Num n -> fn_k_h (App(Var k, Num n)) k h
  | Var x -> fn_k_h (App(Var k, Var x)) k h
  | Fn (x, e) -> fn_k_h (App(Var k, Fn(x, removeExn' e))) k h
  | App (e1, e2) ->
    let f = new_name() in
    let v = new_name() in
    fn_k_h (
      app_k_h (removeExn' e1)
      (Fn (f, app_k_h (removeExn' e2)
              (Fn(v, app_k_h (App(Var f, Var v)) (Var k) (Var h)))
              (Var h)
          )
      )
      (Var h)
    ) k h
  | If (e1, e2, e3) ->
    let v = new_name() in
    fn_k_h (app_k_h (removeExn' e1)
                    (Fn(v, If(Var v,
                             (app_k_h (removeExn' e2) (Var k) (Var h)),
                             (app_k_h (removeExn' e3) (Var k) (Var h)))))
                    (Var h)
            ) k h
  | Equal (e1, e2) ->
    let left = new_name() in
    let right = new_name() in
    fn_k_h (app_k_h (removeExn' e1)
                    (Fn(left, app_k_h (removeExn' e2)
                                      (Fn(right, App(Var k, (Equal (Var left, Var right)))))
                                      (Var h)))
                    (Var h)
            ) k h
  | Raise e -> fn_k_h (app_k_h (removeExn' e) (Var h) (Var h)) k h
  | Handle (e1, n, e2) ->
    let v = new_name() in
    fn_k_h (app_k_h (removeExn' e1) (Var k) (Fn(v, If(Equal(Var v, Num n), app_k_h (removeExn' e2) (Var k) (Var h), App(Var h, Var v))))) k h

let removeExn : xexp -> xexp = fun e ->
  let e' = alpha_conv e [] in
  let no_exept = removeExn' e' in
  let x = new_name() in
  app_k_h no_exept (Fn(x, Var x)) (Fn(x, Num 201812))
