From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
Import ListNotations.
From MetaSpectec Require Import syntax.
From HB Require Import structures.

Inductive option_forall {T : Type} (P : (T -> Prop)) : option T -> Prop :=
	| opt_none : option_forall P None
  | opt_some : forall x,
    P x ->
    option_forall P (Some x)
.

Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : seq X) (ys : seq Y) : seq Z :=
	seq.map (fun '(x, y) => f x y) (seq.zip xs ys).

Definition slice {A : Type} (i j : nat) (l : list A) : list A :=
  firstn (j - i) (skipn i l).

(* PRE: i < size l *)
Definition update {A : Type} (l : list A) (i : nat) (x : A) : list A :=
  set_nth x l i x.

Definition update_slice {A : Type} (l : list A) (i : nat) (j : nat) (xs : list A) : list A :=
  let idx_lst := iota i (j - i) in
  foldl (fun acc '(idx, x) => update acc idx x) l (zip idx_lst xs)
.

Definition is_plaintyp (t : il_typ) : bool :=
  match t with
  | VarT _ _ => false
  | _ => true
  end
.

Lemma eq_dec_Equality_axiom :
  forall (T : Type) (eq_dec : forall (x y : T), decidable (x = y)),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in Equality.axiom eqb.
Proof.
  move=> T eq_dec eqb x y. rewrite /eqb.
  case: (eq_dec x y); by [apply: ReflectT | apply: ReflectF].
Qed.

Definition atom_eq_dec : forall (v1 v2 : atom),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decide equality. Defined.

Definition atom_eqb (v1 v2 : atom) : bool :=
	is_left(atom_eq_dec v1 v2).
Definition eqatomP : Equality.axiom (atom_eqb) :=
	eq_dec_Equality_axiom (atom) (atom_eq_dec).

HB.instance Definition _ := hasDecEq.Build (atom) (eqatomP).

Definition mixop_eq_dec : forall (v1 v2 : mixop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decide equality. Defined.

Definition mixop_eqb (v1 v2 : mixop) : bool :=
	is_left(mixop_eq_dec v1 v2).
Definition eqmixopP : Equality.axiom (mixop_eqb) :=
	eq_dec_Equality_axiom (mixop) (mixop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (mixop) (eqmixopP).


