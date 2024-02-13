(*
This module implements a (consservative) apartness check: Given two (open)
expression (typically reduction rules LHSs), are they definitely apart.
*)

open Util.Source
open Ast

(* Looks at an expression of type list from the back and chops off all
   known _elements_, followed by the list of all list expressions.
   Returns it all in reverse order.
 *)
let rec to_snoc_list (e : exp) : exp list * exp list = match e.it with
  | ListE es -> List.rev es, []
  | CatE (e1, e2) ->
    let tailelems2, listelems2 = to_snoc_list e2 in
    if listelems2 = []
    (* Second list is fully known? Can look at first list *)
    then let tailelems1, listelems1 = to_snoc_list e1 in
         tailelems2 @ tailelems1, listelems1
    (* Second list has unknown elements, have to stop there *)
    else tailelems2, listelems2 @ [e1]
  | _ -> [], [e]

(* We assume the expressions to be of the same type; for ill-typed inputs
   no guarantees are made. *)
let rec apart (e1 : exp) (e2: exp) : bool =
  if Eq.eq_exp e1 e2 then false else
  (*
  (fun b -> if not b then Printf.eprintf "apart\n  %s\n  %s\n  %b\n" (Print.string_of_exp e1) (Print.string_of_exp e2) b; b)
  *)
  (match e1.it, e2.it with
  (* A literal is never a literal of other type *)
  | NatE n1, NatE n2 -> not (n1 = n2)
  | BoolE b1, BoolE b2 -> not (b1 = b2)
  | TextE t1, TextE t2 -> not (t1 = t2)
  | CaseE (a1, exp1), CaseE (a2, exp2) ->
    not (a1 = a2) || apart exp1 exp2
  | TupE es1, TupE es2 when List.length es1 = List.length es2 ->
    List.exists2 apart es1 es2
  | (CatE _ | ListE _), (CatE _ | ListE _) ->
    list_exp_apart e1 e2
  | SubE (e1, _, _), SubE (e2, _, _) -> apart e1 e2
  | MixE (mixop1, e1), MixE (mixop2, e2) ->
    not (mixop1 = mixop2) || apart e1 e2
  (* We do not know anything about variables and functions *)
  | _ , _ -> false (* conservative *)
  )

(* Two list expressions are apart if either their manifest tail elements are apart *)
and list_exp_apart e1 e2 = snoc_list_apart (to_snoc_list e1) (to_snoc_list e2)

and snoc_list_apart (tailelems1, listelems1) (tailelems2, listelems2) =
  match tailelems1, listelems1, tailelems2, listelems2 with
  (* If the heads are apart, the lists are apart *)
  | e1 :: e1s, _, e2 :: e2s, _ -> apart e1 e2 || snoc_list_apart (e1s, listelems1) (e2s, listelems2)
  (* If one list is definitely empty and the other list definitely isn't *)
  | [], [], _ :: _, _ -> false
  | _ :: _, _, [], [] -> false
  (* Else, can't tell *)
  | _, _, _, _ -> false

