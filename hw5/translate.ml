(*
 * SNU 4190.310 Programming Languages 
 * K-- to SM5 translator skeleton code
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)

open K
open Sm5
module Translator = struct

  (* TODO : complete this function  *)
  let rec trans : K.program -> Sm5.command = function
    | K.NUM i -> [Sm5.PUSH (Sm5.Val (Sm5.Z i))]
    | K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
    | K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
    | K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))]
    | K.VAR x -> [Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.ADD (e1, e2) -> trans e1 @ trans e2 @ [Sm5.ADD]
    | K.SUB (e1, e2) -> trans e1 @ trans e2 @ [Sm5.SUB]
    | K.MUL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.MUL]
    | K.DIV (e1, e2) -> trans e1 @ trans e2 @ [Sm5.DIV]
    | K.EQUAL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.EQ]
    | K.LESS (e1, e2) -> trans e1 @ trans e2 @ [Sm5.LESS]
    | K.NOT e -> trans e @ [Sm5.NOT]
    | K.ASSIGN (x, e) -> trans e @ [Sm5.PUSH (Sm5.Id x); Sm5.STORE; Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.SEQ (e1, e2) -> trans e1 @ [Sm5.POP] @ trans e2
    | K.IF (e1, e2, e3) -> trans e1 @ [Sm5.JTR (trans e2, trans e3)]
    | K.WHILE (e1, e2) -> trans (K.LETF("#while", "#1", K.IF(e1, K.SEQ(e2, K.CALLV("#while", K.NUM 1)), K.UNIT), K.CALLV("#while", K.NUM 1)))
    | K.FOR (x, e1, e2, e3) ->
      trans
      (
        K.LETV("#start", e1, 
        K.LETV("#end", e2, 
        K.LETF("#for", "#i", 
          K.IF(K.LESS(K.VAR "#end", K.VAR "#i"),
            K.UNIT,
            K.SEQ(K.ASSIGN(x, K.VAR "#i"),
            K.SEQ(e3, K.CALLV("#for", K.ADD(K.NUM 1, K.VAR "#i"))))),
        K.CALLV("#for", K.VAR "#start")))))
    | K.LETV (x, e1, e2) ->
      trans e1 @ [Sm5.MALLOC; Sm5.BIND x; Sm5.PUSH (Sm5.Id x); Sm5.STORE] @
      trans e2 @ [Sm5.UNBIND; Sm5.POP]
    | K.LETF (f, x, e1, e2) ->
      [
        Sm5.PUSH (Sm5.Fn (x, [Sm5.BIND f] @ trans e1));
        Sm5.BIND f;
      ] @
      trans e2 @
      [
        Sm5.UNBIND;
        Sm5.POP
      ]
    | K.CALLV (f, e) ->
      [
        Sm5.PUSH (Sm5.Id f);
        Sm5.PUSH (Sm5.Id f)
      ] @
      trans e @
      [
        Sm5.MALLOC;
        Sm5.CALL
      ]
    | K.CALLR (f, x) ->
      [
        Sm5.PUSH (Sm5.Id f);
        Sm5.PUSH (Sm5.Id f);
        Sm5.PUSH (Sm5.Id x);
        Sm5.LOAD;
        Sm5.PUSH (Sm5.Id x);
        Sm5.CALL
      ]
    | K.READ x -> [Sm5.GET; Sm5.PUSH (Sm5.Id x); Sm5.STORE; Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.WRITE e ->
      trans e @ 
      [
        Sm5.MALLOC;
        Sm5.BIND "#buffer";
        Sm5.PUSH (Sm5.Id "#buffer");
        Sm5.STORE;
        Sm5.PUSH (Sm5.Id "#buffer");
        Sm5.LOAD;
        Sm5.PUT;
        Sm5.PUSH (Sm5.Id "#buffer");
        Sm5.LOAD;
        Sm5.UNBIND;
        Sm5.POP
        ]

end
