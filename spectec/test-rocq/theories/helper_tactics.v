From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.

(***

These are some tactics that are very useful when doing type soundness.

You should be able to notice that some of these tactics are directly taken from
WasmCert, as they work essentially the same. 

***)

Ltac decomp :=
repeat lazymatch goal with
	| H: _ /\ _ |- _ => 
		destruct H
end.


(** Similar to [set (name := term)], but introduce an equality instead of a local definition. **)
Ltac set_eq name term :=
  set (name := term);
  have: name = term; [
      reflexivity
    | clearbody name ].

Ltac is_variable x cont1 cont2 :=
	match tt with
	| _ =>
		(* Sorry for the hack.
		Only a variable be cleared.
		Local definitions are not considered variables by this tactic. *)
		(exfalso; clear - x; assert_fails clearbody x; fail 1) || cont2
	| _ => cont1
	end.

(** The first step is to name each parameter of the predicate. **)
Ltac gen_ind_pre H :=
  let rec aux v :=
    lazymatch v with
    | ?f ?x =>
      let only_do_if_ok_direct t cont :=
        lazymatch t with
        | Type => idtac

        | _ => cont tt
        end in
      let t := type of x in
      only_do_if_ok_direct t ltac:(fun _ =>
        let t :=
          match t with
          | _ _ => t
          | ?t => eval unfold t in t
          | _ => t
          end in
        only_do_if_ok_direct t ltac:(fun _ =>
          let x' :=
            let rec get_name x :=
              match x with
              | ?f _ => get_name f
              | _ => fresh x
              | _ => fresh "x"
              end in
            get_name x in
          move: H;
          set_eq x' x;
          let E := fresh "E" x' in
          move=> E H));
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** Then, each of the associated parameters can be generalised. **)
Ltac gen_ind_gen H :=
  let rec try_generalize t :=
    lazymatch t with
    | ?f ?x => try_generalize f; try_generalize x
    | ?x => is_variable x ltac:(generalize dependent x) ltac:(idtac)
    | _ => fail "unable to generalize" t
    end in
  let rec aux v :=
    lazymatch v with
    | ?f ?x => 
    lazymatch goal with
      | _ : x = ?y |- _ => try_generalize y
      | _ => fail "unexpected term" v
      end;
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** After the induction, one can inverse them again (and do some cleaning). **)
Ltac gen_ind_post :=
  repeat lazymatch goal with
  | |- _ = _ -> _ => inversion 1
  | |- _ -> _ => intro
  end;
  repeat lazymatch goal with
  | H: True |- _ => clear H
  | H: ?x = ?x |- _ => clear H
  end.

(** Wrapping every part of the generalised induction together. **)
Ltac gen_ind H :=
  gen_ind_pre H;
  gen_ind_gen H;
  induction H;
  gen_ind_post.

(** Similar to [gen_ind H; subst], but cleaning just a little bit more. **)
Ltac gen_ind_subst H :=
  gen_ind H;
  subst;
  gen_ind_post.

(*
Ltac admin_instrs_ok_dependent_ind H :=
let Ht := type of H in
lazymatch Ht with
| Admin_instrs_ok ?s ?C ?es ?tf =>
	let s2 := fresh "s2" in
	let C2 := fresh "C2" in
	let es2 := fresh "es2" in
	let tf2 := fresh "tf2" in
	remember s as s2 eqn:Hrems;
	remember C as C2 eqn:HremC;
	remember es as es2 eqn:Hremes;
	remember tf as tf2 eqn:Hremtf;
	generalize dependent Hrems;
	generalize dependent HremC;
	generalize dependent Hremtf;
	generalize dependent s; generalize dependent C;
	generalize dependent tf;
	induction H
end.
*)

Ltac removeinst2 H :=
    let H1 := fresh "HLength" in
    eapply length_app_both_nil in H as H1; eauto;
    rewrite H1 in H; rewrite <- app_right_nil in H.

Ltac removeinstSimpler H :=
	let H1 := fresh "HLength" in
	eapply length_app_nil in H as H1; eauto;
	rewrite H1 in H; rewrite <- app_right_nil in H.

Lemma list_cons_eq : forall {A : Type} (x y : A) (xs ys : seq A),
  [x] ++ xs = [y] ++ ys -> x = y /\ xs = ys.
Proof.
  move => A x y xs ys H.
  injection H as H.
  by split.
Qed.

Lemma list_rcons_eq : forall {A : Type} (xs ys : seq A) (x y: A),
  xs ++ [x] = ys ++ [y] ->
  xs = ys /\ x = y.
Proof.
	move => A xs ys x y H.
	have Hsizeeq : size xs = size ys.
    {
	  rewrite !cats1 in H.
	  apply (f_equal size) in H.
	  rewrite !size_rcons in H.
	  by injection H as H. }
	split.
	- apply (f_equal (take (size xs))) in H.
	  rewrite !take_cat !Hsizeeq !ltnn !subnn !take0 in H.
	  by rewrite !cats0 in H.
	- apply (f_equal (drop (size xs))) in H.
	  rewrite !drop_cat !Hsizeeq !ltnn !subnn !drop0 in H.
	  by inversion H.
Qed.

Ltac destruct_list_eq_right H :=
  match type of H with
  (* Case 1: Extract from right xs ++ [x] = ys ++ [y] *)
  | @eq (seq _) (?xs ++ [?x]) (?ys ++ [?y]) =>
    let H0 := fresh H "_body" in
    let H1 := fresh H "_tail" in
    move: (list_rcons_eq _ _ _ _ H) => [H0 H1];
    clear H
  (* Case 3: Nil from right xs ++ [x] = [y] *)
  | @eq (seq _) (?xs ++ [?x]) ([?y]) =>
	rewrite -(cat0s [y]) in H; destruct_list_eq_right H
  (* Case 5: Nil from right [x] = ys ++ [y] *)
  | @eq (seq _) ([?x]) (?ys ++ ?[y]) =>
	symmetry in H; destruct_list_eq_right H
  | _ => idtac
  end.

Ltac destruct_list_eq_left H :=
  match type of H with
  (* Case 2: Extract from left [x] ++ xs = [y] ++ ys *)
  | @eq (seq _) ([?x] ++ ?xs) ([?y] ++ ?ys) =>
    let H0 := fresh H "_body" in
    let H1 := fresh H "_head" in
    move: (list_cons_eq _ _ _ _ H) => [H1 H0]; clear H
  (* Case 4: Nil from left [x] ++ xs = [y] *)
  | @eq (seq _) ([?x] ++ ?xs) ([?y]) =>
  rewrite -(cats0 [y]) in H; destruct_list_eq_left H
  (* Case 6: Nil from left [x] = [y] ++ ys *)
  | @eq (seq _) ([?x]) ([?y] ++ ?ys) =>
  symmetry in H; destruct_list_eq_left H
  | _ => idtac
  end.

Ltac repeat_cat_assoc_right H :=
  repeat rewrite (catA) in H.

Ltac repeat_cat_assoc_left H :=
  repeat rewrite -(catA) in H.

Ltac rewrite_cons_cat H :=
  match type of H with
  | @eq (seq _) (?x :: ?xs) (?y :: ?ys) =>
    rewrite -[x :: xs]cat1s in H;
    rewrite -[y :: ys]cat1s in H
  | @eq (seq _) (?x :: ?xs) (_) =>
    rewrite -[x :: xs]cat1s in H
  | @eq (seq _) (_) (?y :: ?ys) =>
    rewrite -[y :: ys]cat1s in H
  | _ => idtac
  end.

Ltac discriminate_empty_list H :=
  match type of H with
  | [] = [_] =>
    discriminate H
  | [_] = [] =>
    discriminate H
  | _ => idtac
  end.

Ltac destruct_empty_list H :=
  match type of H with
  | [] = ?a ++ ?b =>
    let H1 := fresh H in
    let H2 := fresh H in
    apply empty_append in H as [H1 H2];
    clear H;
    destruct_empty_list H1;
    destruct_empty_list H2
  | _ = [] =>
    symmetry in H; destruct_empty_list H
  | [] = [_] =>
    discriminate H
  | _ => idtac
  end.

Ltac destruct_list_eq H :=
  try (rewrite !app_cat in H);
  try destruct_empty_list H;
  (* Try destruct from right *)
  try (repeat_cat_assoc_right H;
  destruct_list_eq_right H);
  (* Try destruct from left *)
  try (rewrite_cons_cat H;
  repeat_cat_assoc_left H;
  destruct_list_eq_left H);
  try destruct_empty_list H.

Ltac destruct_functypes :=
    repeat match goal with
    | v_ft: functype |- _ =>
		let v_ft1 := fresh v_ft in
		let v_ft2 := fresh v_ft in
        destruct v_ft as [[v_ft1] [v_ft2]]
    end.

Ltac destruct_disjunctions :=
	repeat match goal with
	| H: ?x \/ ?y |- _ =>
		let H1 := fresh H in
		let H2 := fresh H in
		destruct H as [H1 | H2]
	| _ : _ |- _ => idtac
	end.

Ltac eq_to_prop :=
  repeat match goal with
  (* | H : is_true (_ == _) = true |- _ =>
    move/eqP in H *)
  | H : is_true (_ == _) |- _ =>
    move/eqP in H
  | H : is_true (_ != _) |- _ =>
    move/negbTE in H;
    move/eqP in H
  | H : is_true (_ || _) |- _ =>
    move/orP in H
  | H : is_true (_ && _) |- _ =>
    move/andP in H
  | H : _ |- is_true (_ == _) =>
    apply/eqP
  end.