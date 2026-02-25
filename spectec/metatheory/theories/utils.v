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

Definition opt_to_lst {X : Type} (x : option X) : list X :=
  match x with
  | Some a => [a]
  | None => []
  end
.

(* PRE: size xs <= 1 *)
Definition lst_to_opt {X : Type} (xs : list X) : option X :=
  match xs with
  | [] => None
  | [x] => Some x
  (* Should not happen *)
  | _ => None
  end
.

Definition option_map {X Y : Type} (f : X -> Y) (x_opt : option X) : option Y :=
  match x_opt with
  | Some x => Some (f x)
  | None => None
  end
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

Fixpoint disjoint {X : eqType} (xs : list X) : bool :=
  match xs with
  | [] => true
  | x :: xs => negb (x \in xs) && disjoint xs
  end
.

Definition same_size {X : Type} (xss : list (list X)) : bool :=
  match xss with
  | [] => true
  | [_] => true
  | xs :: xss' => seq.all (fun xs' => size xs == size xs') xss'
  end
.

(* PRE: all lists in xss are of same size *)
Fixpoint transpose_helper {X : Type} (xss : list (list X)) (n : nat) : list (list X) :=
  match n with
  | O => []
  | S n' =>
    let heads := (List.flat_map (fun xs => 
      match xs with
      | [] => []
      | x :: xs' => [x]
      end
    ) xss) in
    heads :: transpose_helper (List.map behead xss) n'
  end
.

Definition transpose {X : Type} (xss : list (list X)) : list (list X) :=
  match xss with
  | [] => []
  | (xs :: xss') => transpose_helper xss (size xs)
  end
.

Definition list_mapi {X Y : Type} (f : nat -> X -> Y) (xs : list X) : list Y :=
  let idxs := iota 0 (size xs) in
  List.map (fun '(i, x) => f i x) (zip idxs xs)
.

Inductive List_Forall3 {A B C: Type} (R : A -> B -> C -> Prop): seq A -> seq B -> seq C -> Prop :=
	| Forall3_nil : List_Forall3 R nil nil nil
	| Forall3_cons : forall x y z l l' l'',
		R x y z -> List_Forall3 R l l' l'' -> List_Forall3 R (x :: l) (y :: l') (z :: l'').

Definition list_map3 {A B C D: Type} (f : A -> B -> C -> D) (xs : seq A) (ys : seq B) (zs : seq C) : seq D :=
	seq.map (fun '(x, (y, z)) => f x y z) (seq.zip xs (seq.zip ys zs)).

Definition atomtyp (x : typfield) : atom * il_typ :=
  match x with
  | (a, _, t, _) => (a, t)
  end
.

Definition atomtyps (xs : list typfield) : list (atom * il_typ) :=
  List.map atomtyp xs.

(* Decidable equality axiom *)

Lemma eq_dec_Equality_axiom :
  forall (T : Type) (eq_dec : forall (x y : T), decidable (x = y)),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in Equality.axiom eqb.
Proof.
  move=> T eq_dec eqb x y. rewrite /eqb.
  case: (eq_dec x y); by [apply: ReflectT | apply: ReflectF].
Qed.

(* Decidable equality for atoms *)

Definition atom_eq_dec : forall (v1 v2 : atom),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decide equality. Defined.

Definition atom_eqb (v1 v2 : atom) : bool :=
	is_left(atom_eq_dec v1 v2).
Definition eqatomP : Equality.axiom (atom_eqb) :=
	eq_dec_Equality_axiom (atom) (atom_eq_dec).

HB.instance Definition _ := hasDecEq.Build (atom) (eqatomP).

(* Decidable equality for mixops *)

Definition mixop_eq_dec : forall (v1 v2 : mixop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decide equality. Defined.

Definition mixop_eqb (v1 v2 : mixop) : bool :=
	is_left(mixop_eq_dec v1 v2).
Definition eqmixopP : Equality.axiom (mixop_eqb) :=
	eq_dec_Equality_axiom (mixop) (mixop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (mixop) (eqmixopP).


