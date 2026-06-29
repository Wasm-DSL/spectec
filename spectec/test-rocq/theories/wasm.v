(* Imported Code *)
From Stdlib Require Import String List Unicode.Utf8 Reals.
From mathcomp Require Import all_ssreflect all_algebra.
From HB Require Import structures.
From RecordUpdate Require Import RecordSet.
Declare Scope wasm_scope.

Class Inhabited (T: Type) := { default_val : T }.

Definition lookup_total {T: Type} {_: Inhabited T} (l: seq T) (n: nat) : T :=
	seq.nth default_val l n.

Definition the {T : Type} {_ : Inhabited T} (arg : option T) : T :=
	match arg with
		| None => default_val
		| Some v => v
	end.

Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : seq X) (ys : seq Y) : seq Z :=
	seq.map (fun '(x, y) => f x y) (seq.zip xs ys).

Definition option_zipWith {α β γ: Type} (f: α -> β -> γ) (x: option α) (y: option β): option γ := 
	match x, y with
		| Some x, Some y => Some (f x y)
		| _, _ => None
	end.

Fixpoint list_update {α: Type} (l: seq α) (n: nat) (y: α): seq α :=
	match l, n with
		| nil, _ => nil
		| x :: l', O => y :: l'
		| x :: l', S n => x :: list_update l' n y
	end.

Definition option_append {α: Type} (x y: option α) : option α :=
	match x with
		| Some _ => x
		| None => y
	end.

Definition option_map {α β : Type} (f : α -> β) (x : option α) : option β :=
	match x with
		| Some x => Some (f x)
		| _ => None
	end.

Fixpoint list_update_func {α: Type} (l: seq α) (n: nat) (y: α -> α): seq α :=
	match l, n with
		| nil, _ => nil
		| x :: l', O => (y x) :: l'
		| x :: l', S n => x :: list_update_func l' n y
	end.

Fixpoint list_slice {α: Type} (l: seq α) (i: nat) (j: nat): seq α :=
	match l, i, j with
		| nil, _, _ => nil
		| x :: l', O, O => nil
		| x :: l', S n, O => nil
		| x :: l', O, S m => x :: list_slice l' 0 m
		| x :: l', S n, m => list_slice l' n m
	end.

Fixpoint list_slice_update {α: Type} (l: seq α) (i: nat) (j: nat) (update_l: seq α): seq α :=
	match l, i, j, update_l with
		| nil, _, _, _ => nil
		| l', _, _, nil => l'
		| x :: l', O, O, _ => nil
		| x :: l', S n, O, _ => nil
		| x :: l', O, S m, y :: u_l' => y :: list_slice_update l' 0 m u_l'
		| x :: l', S n, m, _ => x :: list_slice_update l' n m update_l
	end.

Definition list_extend {α: Type} (l: seq α) (y: α): seq α :=
	y :: l.

Definition option_map3 {A B C D: Type} (f: A -> B -> C -> D) (x: option A) (y: option B) (z: option C): option D :=
	match x, y, z with
		| Some x, Some y, Some z => Some (f x y z)
		| _, _, _ => None
	end.

Definition list_map3 {A B C D: Type} (f : A -> B -> C -> D) (xs : seq A) (ys : seq B) (zs : seq C) : seq D :=
	seq.map (fun '(x, (y, z)) => f x y z) (seq.zip xs (seq.zip ys zs)).

Inductive List_Forall3 {A B C: Type} (R : A -> B -> C -> Prop): seq A -> seq B -> seq C -> Prop :=
	| Forall3_nil : List_Forall3 R nil nil nil
	| Forall3_cons : forall x y z l l' l'',
		R x y z -> List_Forall3 R l l' l'' -> List_Forall3 R (x :: l) (y :: l') (z :: l'').

Inductive Foralli_help {X : Type} (f : nat -> X -> Prop) : nat -> list X -> Prop :=
	| Foralli_nil : forall n, Foralli_help f n nil
	| Foralli_cons : forall x l n,
	f n x -> Foralli_help f (n + 1) l -> Foralli_help f n (x::l).

Definition List_Foralli {X : Type} (f : nat -> X -> Prop) (xs : list X) : Prop :=
	Foralli_help f 0 xs.

Definition holds_upto (P : nat -> Prop) (n : nat) :=
	Forall P (iota 0 n).

Class Append (α: Type) := _append : α -> α -> α.

Infix "@@" := _append (right associativity, at level 60) : wasm_scope.

Global Instance Append_List_ {α: Type}: Append (seq α) := { _append l1 l2 := seq.cat l1 l2 }.

Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.

Global Instance Append_nat : Append (nat) := { _append n1 n2 := n1 + n2}.

Global Instance Inh_unit : Inhabited unit := { default_val := tt }.

Global Instance Inh_nat : Inhabited nat := { default_val := O }.

Global Instance Inh_list {T: Type} : Inhabited (seq T) := { default_val := nil }.

Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.

Global Instance Inh_int : Inhabited int := { default_val := 0 }.

Global Instance Inh_rat : Inhabited rat := { default_val := 0 }.

Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.

Global Instance Inh_type : Inhabited Type := { default_val := nat }.

Definition option_to_list {T: Type} (arg : option T) : seq T :=
	match arg with
		| None => nil
		| Some a => a :: nil
	end.

Coercion option_to_list: option >-> seq.

Definition int_to_nat (i : int) : nat :=
	match i with
		| Posz n => n
		| Negz n => 0
	end.

Definition rat_to_int (r : rat) : int :=
	((numq r) %/ (denq r))%Z.

Definition rat_to_nat (r : rat) : nat :=
	int_to_nat (rat_to_int r).

Coercion int_to_nat : int >-> nat.

Coercion ratz : int >-> rat.

Coercion rat_to_int : rat >-> int.

Coercion rat_to_nat : rat >-> nat.

Create HintDb eq_dec_db.

Ltac decidable_equality_step :=
  do [ by eauto with eq_dec_db | decide equality ].

Lemma eq_dec_Equality_axiom :
  forall (T : Type) (eq_dec : forall (x y : T), decidable (x = y)),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in Equality.axiom eqb.
Proof.
  move=> T eq_dec eqb x y. rewrite /eqb.
  case: (eq_dec x y); by [apply: ReflectT | apply: ReflectF].
Qed.

Class Coercion (A B : Type) := { coerce : A -> B }.

Notation "x ':>' B" := (coerce (A:=_) (B:=B) x)
(at level 70, right associativity).

Definition option_coerce {A B : Type} `{Coercion A B} (a_opt : option A): option B :=
	match a_opt with
		| Some a => Some (coerce a)
		| None => None
	end.

Definition list_coerce {A B : Type} `{Coercion A B} (a_list : seq A): seq B :=
	[seq (coerce a) | a <- a_list].

Definition id_coerce {A : Type} (a : A) : A := a.

Definition transitive_coerce {A B C : Type} `{Coercion A B} `{Coercion B C} (a : A): C :=
	coerce (coerce a).

Definition total_coerce {A B: Type} `{Coercion A (option B)} {_ : Inhabited B} (a : A): B :=
	the (coerce a).

Global Instance option_coercion (A B : Type) {_: Coercion A B}: Coercion (option A) (option B) := { coerce := option_coerce }.

Global Instance list_coercion (A B : Type) {_: Coercion A B}: Coercion (seq A) (seq B) := { coerce := list_coerce }.

Global Instance id_coercion (A : Type): Coercion A A := { coerce := id_coerce }.

Global Instance transitive_coercion (A B C : Type) `{Coercion A B} `{Coercion B C}: Coercion A C := { coerce := transitive_coerce }.

Global Instance total_coercion (A B : Type) `{Coercion A (option B)} {_ : Inhabited B}: Coercion A B := { coerce := total_coerce}.

Notation "| x |" := (seq.size x) (at level 60).
Notation "!( x )" := (the x) (at level 60).
Notation "x '[|' a '|]'" := (lookup_total x a) (at level 10).

Lemma eqb_eq {T : eqType} (x y : T) :
	x == y -> x = y.
Proof. by move/eqP. Qed.

Hint Resolve eqb_eq : core.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.

(* Generated Code *)
(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.14-162.17 *)
Inductive r_MUT : Type :=
	| MUT : r_MUT.

Global Instance Inhabited__r_MUT : Inhabited (r_MUT) := { default_val := MUT }.

Definition r_MUT_eq_dec : forall (v1 v2 : r_MUT),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition r_MUT_eqb (v1 v2 : r_MUT) : bool :=
	is_left(r_MUT_eq_dec v1 v2).
Definition eqr_MUTP : Equality.axiom (r_MUT_eqb) :=
	eq_dec_Equality_axiom (r_MUT) (r_MUT_eq_dec).

HB.instance Definition _ := hasDecEq.Build (r_MUT) (eqr_MUTP).
Hint Resolve r_MUT_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:7.1-7.15 *)
Definition res_N : Type := nat.

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:8.1-8.15 *)
Definition M : Type := nat.

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:9.1-9.15 *)
Definition n : Type := nat.

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:10.1-10.15 *)
Definition m : Type := nat.

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:15.1-15.14 *)
Definition Ki : nat := 1024.

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:21.1-21.25 *)
Definition min (res_nat : nat) (nat_0 : nat) : nat :=
	match res_nat, nat_0 return nat with
		| i, j => (if (i <= j)%N then i else j)
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:25.1-25.21 *)
Inductive fun_sum : (seq nat) -> nat -> Prop :=
	| fun_sum_case_0 : fun_sum [:: ] 0
	| fun_sum_case_1 : forall (v_n : nat) (n'_lst : (seq n)) (var_0 : nat), 
		(fun_sum n'_lst var_0) ->
		fun_sum ([::v_n] ++ n'_lst) (v_n + var_0)%N.

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:32.1-32.58 *)
Definition opt_ (X : eqType) (var_0_lst : (seq X)) : (option (option X)) :=
	match X, var_0_lst return (option (option X)) with
		| X, [:: ] => (Some None)
		| X, [::w] => (Some (Some w))
		| X, x1 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:36.1-36.45 *)
Definition list_ (X : eqType) (var_0_opt : (option X)) : (seq X) :=
	match X, var_0_opt return (seq X) with
		| X, None => [:: ]
		| X, (Some w) => [::w]
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:40.1-40.86 *)
Fixpoint concat_ (X : eqType) (var_0_lst_lst : (seq (seq X))) : (seq X) :=
	match X, var_0_lst_lst return (seq X) with
		| X, [:: ] => [:: ]
		| X, (w_lst :: w'_lst_lst) => (w_lst ++ (concat_ X w'_lst_lst))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:44.1-44.39 *)
Axiom inv_concat_ : forall (X : eqType) (var_0_lst : (seq X)), (seq (seq X)).

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.46 *)
Fixpoint setproduct2_ (X : eqType) (X_0 : X) (var_0_lst_lst : (seq (seq X))) : (seq (seq X)) :=
	match X, X_0, var_0_lst_lst return (seq (seq X)) with
		| X, w_1, [:: ] => [:: ]
		| X, w_1, (w'_lst :: w_lst_lst) => ([::([::w_1] ++ w'_lst)] ++ (setproduct2_ X w_1 w_lst_lst))
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.47 *)
Fixpoint setproduct1_ (X : eqType) (var_0_lst : (seq X)) (var_1_lst_lst : (seq (seq X))) : (seq (seq X)) :=
	match X, var_0_lst, var_1_lst_lst return (seq (seq X)) with
		| X, [:: ], w_lst_lst => [:: ]
		| X, (w_1 :: w'_lst), w_lst_lst => ((setproduct2_ X w_1 w_lst_lst) ++ (setproduct1_ X w'_lst w_lst_lst))
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:49.1-49.84 *)
Fixpoint setproduct_ (X : eqType) (var_0_lst_lst : (seq (seq X))) : (seq (seq X)) :=
	match X, var_0_lst_lst return (seq (seq X)) with
		| X, [:: ] => [::[:: ]]
		| X, (w_1_lst :: w_lst_lst) => (setproduct1_ X w_1_lst (setproduct_ X w_lst_lst))
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:60.1-60.78 *)
Fixpoint disjoint_ (X : eqType) (var_0_lst : (seq X)) : bool :=
	match X, var_0_lst return bool with
		| X, [:: ] => true
		| X, (w :: w'_lst) => ((negb (w \in w'_lst)) && (disjoint_ X w'_lst))
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
Inductive res_list (X : Type) : Type :=
	| mk_list (X_lst : (seq X)) : res_list X.

Global Instance Inhabited__res_list (X : Type) : Inhabited (res_list X) := { default_val := mk_list X default_val }.

(* FIXME - No clear way to do decidable equality *)
Definition res_list_eq_dec : forall (X : Type) (v1 v2 : res_list X),
  {v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition res_list_eqb (X : Type) (v1 v2 : res_list X) : bool :=
	is_left(res_list_eq_dec X v1 v2).
Definition eqres_listP (X : Type) : Equality.axiom (res_list_eqb X) :=
	eq_dec_Equality_axiom (res_list X) (res_list_eq_dec X).

HB.instance Definition _ (X : Type) := hasDecEq.Build (res_list X) (eqres_listP X).
Hint Resolve res_list_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
Definition proj_list_0 (X : eqType) (x : (res_list X)) : ((seq X)) :=
	match X, x return ((seq X)) with
		| X, (mk_list v_X_list_0) => (v_X_list_0)
	end.

Global Instance proj_list_0_coercion (X : eqType) : Coercion (res_list X) ((seq X)) := { coerce := proj_list_0 X }.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36 *)
Inductive bit : Type :=
	| mk_bit (i : nat) : bit.

Global Instance Inhabited__bit : Inhabited (bit) := { default_val := mk_bit default_val }.

Definition bit_eq_dec : forall (v1 v2 : bit),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition bit_eqb (v1 v2 : bit) : bool :=
	is_left(bit_eq_dec v1 v2).
Definition eqbitP : Equality.axiom (bit_eqb) :=
	eq_dec_Equality_axiom (bit) (bit_eq_dec).

HB.instance Definition _ := hasDecEq.Build (bit) (eqbitP).
Hint Resolve bit_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.8-15.11 *)
Inductive wf_bit : bit -> Prop :=
	| bit_case_0 : forall (i : nat), 
		((i == 0) || (i == 1)) ->
		wf_bit (mk_bit i).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
Inductive byte : Type :=
	| mk_byte (i : nat) : byte.

Global Instance Inhabited__byte : Inhabited (byte) := { default_val := mk_byte default_val }.

Definition byte_eq_dec : forall (v1 v2 : byte),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition byte_eqb (v1 v2 : byte) : bool :=
	is_left(byte_eq_dec v1 v2).
Definition eqbyteP : Equality.axiom (byte_eqb) :=
	eq_dec_Equality_axiom (byte) (byte_eq_dec).

HB.instance Definition _ := hasDecEq.Build (byte) (eqbyteP).
Hint Resolve byte_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
Definition proj_byte_0 (x : byte) : (nat) :=
	match x return (nat) with
		| (mk_byte v_num_0) => (v_num_0)
	end.

Global Instance proj_byte_0_coercion : Coercion byte (nat) := { coerce := proj_byte_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.8-16.12 *)
Inductive wf_byte : byte -> Prop :=
	| byte_case_0 : forall (i : nat), 
		((i >= 0)%N && (i <= 255)%N) ->
		wf_byte (mk_byte i).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
Inductive uN : Type :=
	| mk_uN (i : nat) : uN.

Global Instance Inhabited__uN : Inhabited (uN) := { default_val := mk_uN default_val }.

Definition uN_eq_dec : forall (v1 v2 : uN),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition uN_eqb (v1 v2 : uN) : bool :=
	is_left(uN_eq_dec v1 v2).
Definition equNP : Equality.axiom (uN_eqb) :=
	eq_dec_Equality_axiom (uN) (uN_eq_dec).

HB.instance Definition _ := hasDecEq.Build (uN) (equNP).
Hint Resolve uN_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
Definition proj_uN_0 (x : uN) : (nat) :=
	match x return (nat) with
		| (mk_uN v_num_0) => (v_num_0)
	end.

Global Instance proj_uN_0_coercion : Coercion uN (nat) := { coerce := proj_uN_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.8-18.11 *)
Inductive wf_uN : res_N -> uN -> Prop :=
	| uN_case_0 : forall (v_N : res_N) (i : nat), 
		((i >= 0)%N && (i <= ((((2 ^ v_N)%N : int) - (1 : int))%Z : nat))%N) ->
		wf_uN v_N (mk_uN i).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
Inductive sN : Type :=
	| mk_sN (i : int) : sN.

Global Instance Inhabited__sN : Inhabited (sN) := { default_val := mk_sN default_val }.

Definition sN_eq_dec : forall (v1 v2 : sN),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition sN_eqb (v1 v2 : sN) : bool :=
	is_left(sN_eq_dec v1 v2).
Definition eqsNP : Equality.axiom (sN_eqb) :=
	eq_dec_Equality_axiom (sN) (sN_eq_dec).

HB.instance Definition _ := hasDecEq.Build (sN) (eqsNP).
Hint Resolve sN_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
Definition proj_sN_0 (x : sN) : (int) :=
	match x return (int) with
		| (mk_sN v_num_0) => (v_num_0)
	end.

Global Instance proj_sN_0_coercion : Coercion sN (int) := { coerce := proj_sN_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.8-20.11 *)
Inductive wf_sN : res_N -> sN -> Prop :=
	| sN_case_0 : forall (v_N : res_N) (i : int), 
		((((i >= (0 - ((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : int))%Z)%Z && (i <= (0 - (1 : int))%Z)%Z) || (i == (0 : int))) || ((i >= ((1 : int))%Z)%Z && (i <= (((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : int) - (1 : int))%Z)%Z)) ->
		wf_sN v_N (mk_sN i).

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:22.1-23.8 *)
Definition iN : Type := uN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:25.1-25.18 *)
Definition u8 : Type := uN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:26.1-26.20 *)
Definition u16 : Type := uN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:27.1-27.20 *)
Definition u31 : Type := uN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:28.1-28.20 *)
Definition u32 : Type := uN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:29.1-29.20 *)
Definition u64 : Type := uN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:30.1-30.20 *)
Definition s33 : Type := sN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:31.1-31.20 *)
Definition i32 : Type := iN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:32.1-32.20 *)
Definition i64 : Type := iN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:33.1-33.22 *)
Definition i128 : Type := iN.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:40.1-40.35 *)
Definition signif (v_N : res_N) : (option nat) :=
	match v_N return (option nat) with
		| 32 => (Some 23)
		| 64 => (Some 52)
		| x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:44.1-44.34 *)
Definition expon (v_N : res_N) : (option nat) :=
	match v_N return (option nat) with
		| 32 => (Some 8)
		| 64 => (Some 11)
		| x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:48.1-48.30 *)
Definition fun_M (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (!((signif v_N)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:51.1-51.30 *)
Definition E (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (!((expon v_N)))
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:58.1-58.30 *)
Definition exp : Type := int.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.1-63.84 *)
Inductive fNmag : Type :=
	| NORM (v_m : m) (v_exp : exp) : fNmag
	| SUBNORM (v_m : m) : fNmag
	| INF : fNmag
	| NAN (v_m : m) : fNmag.

Global Instance Inhabited__fNmag : Inhabited (fNmag) := { default_val := NORM default_val default_val }.

Definition fNmag_eq_dec : forall (v1 v2 : fNmag),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition fNmag_eqb (v1 v2 : fNmag) : bool :=
	is_left(fNmag_eq_dec v1 v2).
Definition eqfNmagP : Equality.axiom (fNmag_eqb) :=
	eq_dec_Equality_axiom (fNmag) (fNmag_eq_dec).

HB.instance Definition _ := hasDecEq.Build (fNmag) (eqfNmagP).
Hint Resolve fNmag_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.8-59.14 *)
Inductive wf_fNmag : res_N -> fNmag -> Prop :=
	| fNmag_case_0 : forall (v_N : res_N) (v_m : m) (v_exp : exp), 
		((v_m < (2 ^ (fun_M v_N))%N)%N && ((((2 : int) - ((2 ^ ((((E v_N) : int) - (1 : int))%Z : nat))%N : int))%Z <= v_exp)%Z && (v_exp <= (((2 ^ ((((E v_N) : int) - (1 : int))%Z : nat))%N : int) - (1 : int))%Z)%Z)) ->
		wf_fNmag v_N (NORM v_m v_exp)
	| fNmag_case_1 : forall (v_N : res_N) (v_exp : exp) (v_m : m), 
		((v_m < (2 ^ (fun_M v_N))%N)%N && (((2 : int) - ((2 ^ ((((E v_N) : int) - (1 : int))%Z : nat))%N : int))%Z == v_exp)) ->
		wf_fNmag v_N (SUBNORM v_m)
	| fNmag_case_2 : forall (v_N : res_N), wf_fNmag v_N INF
	| fNmag_case_3 : forall (v_N : res_N) (v_m : m), 
		((1 <= v_m)%N && (v_m < (2 ^ (fun_M v_N))%N)%N) ->
		wf_fNmag v_N (NAN v_m).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.1-56.35 *)
Inductive fN : Type :=
	| POS (_ : fNmag) : fN
	| NEG (_ : fNmag) : fN.

Global Instance Inhabited__fN : Inhabited (fN) := { default_val := POS default_val }.

Definition fN_eq_dec : forall (v1 v2 : fN),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition fN_eqb (v1 v2 : fN) : bool :=
	is_left(fN_eq_dec v1 v2).
Definition eqfNP : Equality.axiom (fN_eqb) :=
	eq_dec_Equality_axiom (fN) (fN_eq_dec).

HB.instance Definition _ := hasDecEq.Build (fN) (eqfNP).
Hint Resolve fN_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.8-54.11 *)
Inductive wf_fN : res_N -> fN -> Prop :=
	| fN_case_0 : forall (v_N : res_N) (var_0 : fNmag), 
		(wf_fNmag v_N var_0) ->
		wf_fN v_N (POS var_0)
	| fN_case_1 : forall (v_N : res_N) (var_0 : fNmag), 
		(wf_fNmag v_N var_0) ->
		wf_fN v_N (NEG var_0).

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:65.1-65.20 *)
Definition f32 : Type := fN.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:66.1-66.20 *)
Definition f64 : Type := fN.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.1-68.39 *)
Definition fzero (v_N : res_N) : fN :=
	match v_N return fN with
		| v_N => (POS (SUBNORM 0))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.6-68.12 *)
Lemma fzero_is_wf : forall (v_N : res_N) (ret_val : fN),
	(ret_val == (fzero v_N)) ->
	(wf_fN v_N ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.1-71.39 *)
Definition fone (v_N : res_N) : fN :=
	match v_N return fN with
		| v_N => (POS (NORM 1 (0 : int)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.6-71.11 *)
Lemma fone_is_wf : forall (v_N : res_N) (ret_val : fN),
	(ret_val == (fone v_N)) ->
	(wf_fN v_N ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:74.1-74.21 *)
Definition canon_ (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (2 ^ ((((!((signif v_N))) : int) - (1 : int))%Z : nat))%N
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:80.1-81.8 *)
Definition vN : Type := iN.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 *)
Inductive char : Type :=
	| mk_char (i : nat) : char.

Global Instance Inhabited__char : Inhabited (char) := { default_val := mk_char default_val }.

Definition char_eq_dec : forall (v1 v2 : char),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition char_eqb (v1 v2 : char) : bool :=
	is_left(char_eq_dec v1 v2).
Definition eqcharP : Equality.axiom (char_eqb) :=
	eq_dec_Equality_axiom (char) (char_eq_dec).

HB.instance Definition _ := hasDecEq.Build (char) (eqcharP).
Hint Resolve char_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 *)
Definition proj_char_0 (x : char) : (nat) :=
	match x return (nat) with
		| (mk_char v_num_0) => (v_num_0)
	end.

Global Instance proj_char_0_coercion : Coercion char (nat) := { coerce := proj_char_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.8-88.12 *)
Inductive wf_char : char -> Prop :=
	| char_case_0 : forall (i : nat), 
		(((i >= 0)%N && (i <= 55295)%N) || ((i >= 57344)%N && (i <= 1114111)%N)) ->
		wf_char (mk_char i).

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25 *)
Inductive fun_utf8 : (seq char) -> (seq byte) -> Prop :=
	| fun_utf8_case_0 : forall (ch : char) (b : byte), 
		(((ch :> nat) < 128)%N && ((mk_byte (ch :> (nat))) == b)) ->
		(wf_byte (mk_byte (ch :> (nat)))) ->
		fun_utf8 [::ch] [::b]
	| fun_utf8_case_1 : forall (ch : char) (b_1 : byte) (b_2 : byte), 
		(((128 <= (ch :> nat))%N && ((ch :> nat) < 2048)%N) && ((ch :> nat) == (((2 ^ 6)%N * ((((b_1 :> nat) : int) - (192 : int))%Z : nat))%N + ((((b_2 :> nat) : int) - (128 : int))%Z : nat))%N)) ->
		fun_utf8 [::ch] [::b_1; b_2]
	| fun_utf8_case_2 : forall (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte), 
		((((2048 <= (ch :> nat))%N && ((ch :> nat) < 55296)%N) || ((57344 <= (ch :> nat))%N && ((ch :> nat) < 65536)%N)) && ((ch :> nat) == ((((2 ^ 12)%N * ((((b_1 :> nat) : int) - (224 : int))%Z : nat))%N + ((2 ^ 6)%N * ((((b_2 :> nat) : int) - (128 : int))%Z : nat))%N)%N + ((((b_3 :> nat) : int) - (128 : int))%Z : nat))%N)) ->
		fun_utf8 [::ch] [::b_1; b_2; b_3]
	| fun_utf8_case_3 : forall (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) (b_4 : byte), 
		(((65536 <= (ch :> nat))%N && ((ch :> nat) < 69632)%N) && ((ch :> nat) == (((((2 ^ 18)%N * ((((b_1 :> nat) : int) - (240 : int))%Z : nat))%N + ((2 ^ 12)%N * ((((b_2 :> nat) : int) - (128 : int))%Z : nat))%N)%N + ((2 ^ 6)%N * ((((b_3 :> nat) : int) - (128 : int))%Z : nat))%N)%N + ((((b_4 :> nat) : int) - (128 : int))%Z : nat))%N)) ->
		fun_utf8 [::ch] [::b_1; b_2; b_3; b_4]
	| fun_utf8_case_4 : forall (ch_lst : (seq char)) (var_0_lst : (seq (seq byte))), 
		((|var_0_lst|) == (|ch_lst|)) ->
		List.Forall2 (fun (var_0 : (seq byte)) (ch : char) => (fun_utf8 [::ch] var_0)) var_0_lst ch_lst ->
		fun_utf8 ch_lst (concat_ byte var_0_lst).

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25 *)
Lemma utf8_is_wf : forall (var_0_lst : (seq char)) (ret_val_lst : (seq byte)) (var_0 : (seq byte)),
	(fun_utf8 var_0_lst var_0) ->
	List.Forall (fun (var_0 : char) => (wf_char var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.
Proof. Admitted.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 *)
Inductive name : Type :=
	| mk_name (char_lst : (seq char)) : name.

Global Instance Inhabited__name : Inhabited (name) := { default_val := mk_name default_val }.

Definition name_eq_dec : forall (v1 v2 : name),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition name_eqb (v1 v2 : name) : bool :=
	is_left(name_eq_dec v1 v2).
Definition eqnameP : Equality.axiom (name_eqb) :=
	eq_dec_Equality_axiom (name) (name_eq_dec).

HB.instance Definition _ := hasDecEq.Build (name) (eqnameP).
Hint Resolve name_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 *)
Definition proj_name_0 (x : name) : ((seq char)) :=
	match x return ((seq char)) with
		| (mk_name v_char_list_0) => (v_char_list_0)
	end.

Global Instance proj_name_0_coercion : Coercion name ((seq char)) := { coerce := proj_name_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.8-92.12 *)
Inductive wf_name : name -> Prop :=
	| name_case_0 : forall (char_lst : (seq char)) (var_0 : (seq byte)), 
		(fun_utf8 char_lst var_0) ->
		List.Forall (fun (v_char : char) => (wf_char v_char)) char_lst ->
		((|var_0|) < (2 ^ 32)%N)%N ->
		wf_name (mk_name char_lst).

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:101.1-101.36 *)
Definition idx : Type := u32.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:102.1-102.44 *)
Definition laneidx : Type := u8.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:104.1-104.45 *)
Definition typeidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:105.1-105.49 *)
Definition funcidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:106.1-106.49 *)
Definition globalidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:107.1-107.47 *)
Definition tableidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:108.1-108.46 *)
Definition memidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:109.1-109.45 *)
Definition elemidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:110.1-110.45 *)
Definition dataidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:111.1-111.47 *)
Definition labelidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:112.1-112.47 *)
Definition localidx : Type := idx.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:126.1-127.26 *)
Inductive numtype : Type :=
	| I32 : numtype
	| I64 : numtype
	| F32 : numtype
	| F64 : numtype.

Global Instance Inhabited__numtype : Inhabited (numtype) := { default_val := I32 }.

Definition numtype_eq_dec : forall (v1 v2 : numtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition numtype_eqb (v1 v2 : numtype) : bool :=
	is_left(numtype_eq_dec v1 v2).
Definition eqnumtypeP : Equality.axiom (numtype_eqb) :=
	eq_dec_Equality_axiom (numtype) (numtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (numtype) (eqnumtypeP).
Hint Resolve numtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:129.1-130.9 *)
Inductive vectype : Type :=
	| V128 : vectype.

Global Instance Inhabited__vectype : Inhabited (vectype) := { default_val := V128 }.

Definition vectype_eq_dec : forall (v1 v2 : vectype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vectype_eqb (v1 v2 : vectype) : bool :=
	is_left(vectype_eq_dec v1 v2).
Definition eqvectypeP : Equality.axiom (vectype_eqb) :=
	eq_dec_Equality_axiom (vectype) (vectype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vectype) (eqvectypeP).
Hint Resolve vectype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:132.1-133.22 *)
Inductive consttype : Type :=
	| consttype_I32 : consttype
	| consttype_I64 : consttype
	| consttype_F32 : consttype
	| consttype_F64 : consttype
	| consttype_V128 : consttype.

Global Instance Inhabited__consttype : Inhabited (consttype) := { default_val := consttype_I32 }.

Definition consttype_eq_dec : forall (v1 v2 : consttype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition consttype_eqb (v1 v2 : consttype) : bool :=
	is_left(consttype_eq_dec v1 v2).
Definition eqconsttypeP : Equality.axiom (consttype_eqb) :=
	eq_dec_Equality_axiom (consttype) (consttype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (consttype) (eqconsttypeP).
Hint Resolve consttype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:135.1-136.24 *)
Inductive reftype : Type :=
	| FUNCREF : reftype
	| EXTERNREF : reftype.

Global Instance Inhabited__reftype : Inhabited (reftype) := { default_val := FUNCREF }.

Definition reftype_eq_dec : forall (v1 v2 : reftype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition reftype_eqb (v1 v2 : reftype) : bool :=
	is_left(reftype_eq_dec v1 v2).
Definition eqreftypeP : Equality.axiom (reftype_eqb) :=
	eq_dec_Equality_axiom (reftype) (reftype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (reftype) (eqreftypeP).
Hint Resolve reftype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:138.1-139.38 *)
Inductive valtype : Type :=
	| valtype_I32 : valtype
	| valtype_I64 : valtype
	| valtype_F32 : valtype
	| valtype_F64 : valtype
	| valtype_V128 : valtype
	| valtype_FUNCREF : valtype
	| valtype_EXTERNREF : valtype
	| BOT : valtype.

Global Instance Inhabited__valtype : Inhabited (valtype) := { default_val := valtype_I32 }.

Definition valtype_eq_dec : forall (v1 v2 : valtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition valtype_eqb (v1 v2 : valtype) : bool :=
	is_left(valtype_eq_dec v1 v2).
Definition eqvaltypeP : Equality.axiom (valtype_eqb) :=
	eq_dec_Equality_axiom (valtype) (valtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (valtype) (eqvaltypeP).
Hint Resolve valtype_eq_dec : eq_dec_db.

(* Auxiliary Definition at:  *)
Definition valtype_numtype (var_0 : numtype) : valtype :=
	match var_0 return valtype with
		| I32 => valtype_I32
		| I64 => valtype_I64
		| F32 => valtype_F32
		| F64 => valtype_F64
	end.

(* Auxiliary Definition at:  *)
Definition valtype_reftype (var_0 : reftype) : valtype :=
	match var_0 return valtype with
		| FUNCREF => valtype_FUNCREF
		| EXTERNREF => valtype_EXTERNREF
	end.

(* Auxiliary Definition at:  *)
Definition valtype_vectype (var_0 : vectype) : valtype :=
	match var_0 return valtype with
		| V128 => valtype_V128
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:141.1-141.38 *)
Inductive Inn : Type :=
	| Inn_I32 : Inn
	| Inn_I64 : Inn.

Global Instance Inhabited__Inn : Inhabited (Inn) := { default_val := Inn_I32 }.

Definition Inn_eq_dec : forall (v1 v2 : Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Inn_eqb (v1 v2 : Inn) : bool :=
	is_left(Inn_eq_dec v1 v2).
Definition eqInnP : Equality.axiom (Inn_eqb) :=
	eq_dec_Equality_axiom (Inn) (Inn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Inn) (eqInnP).
Hint Resolve Inn_eq_dec : eq_dec_db.

(* Auxiliary Definition at:  *)
Definition numtype_Inn (var_0 : Inn) : numtype :=
	match var_0 return numtype with
		| Inn_I32 => I32
		| Inn_I64 => I64
	end.

(* Auxiliary Definition at:  *)
Definition valtype_Inn (var_0 : Inn) : valtype :=
	match var_0 return valtype with
		| Inn_I32 => valtype_I32
		| Inn_I64 => valtype_I64
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:142.1-142.38 *)
Inductive Fnn : Type :=
	| Fnn_F32 : Fnn
	| Fnn_F64 : Fnn.

Global Instance Inhabited__Fnn : Inhabited (Fnn) := { default_val := Fnn_F32 }.

Definition Fnn_eq_dec : forall (v1 v2 : Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Fnn_eqb (v1 v2 : Fnn) : bool :=
	is_left(Fnn_eq_dec v1 v2).
Definition eqFnnP : Equality.axiom (Fnn_eqb) :=
	eq_dec_Equality_axiom (Fnn) (Fnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Fnn) (eqFnnP).
Hint Resolve Fnn_eq_dec : eq_dec_db.

(* Auxiliary Definition at:  *)
Definition numtype_Fnn (var_0 : Fnn) : numtype :=
	match var_0 return numtype with
		| Fnn_F32 => F32
		| Fnn_F64 => F64
	end.

(* Auxiliary Definition at:  *)
Definition valtype_Fnn (var_0 : Fnn) : valtype :=
	match var_0 return valtype with
		| Fnn_F32 => valtype_F32
		| Fnn_F64 => valtype_F64
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:143.1-143.36 *)
Definition Vnn : Type := vectype.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:146.1-147.16 *)
Definition resulttype : Type := (res_list valtype).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:152.1-152.52 *)
Inductive packtype : Type :=
	| I8 : packtype
	| I16 : packtype.

Global Instance Inhabited__packtype : Inhabited (packtype) := { default_val := I8 }.

Definition packtype_eq_dec : forall (v1 v2 : packtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition packtype_eqb (v1 v2 : packtype) : bool :=
	is_left(packtype_eq_dec v1 v2).
Definition eqpacktypeP : Equality.axiom (packtype_eqb) :=
	eq_dec_Equality_axiom (packtype) (packtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (packtype) (eqpacktypeP).
Hint Resolve packtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:153.1-153.60 *)
Inductive lanetype : Type :=
	| lanetype_I32 : lanetype
	| lanetype_I64 : lanetype
	| lanetype_F32 : lanetype
	| lanetype_F64 : lanetype
	| lanetype_I8 : lanetype
	| lanetype_I16 : lanetype.

Global Instance Inhabited__lanetype : Inhabited (lanetype) := { default_val := lanetype_I32 }.

Definition lanetype_eq_dec : forall (v1 v2 : lanetype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition lanetype_eqb (v1 v2 : lanetype) : bool :=
	is_left(lanetype_eq_dec v1 v2).
Definition eqlanetypeP : Equality.axiom (lanetype_eqb) :=
	eq_dec_Equality_axiom (lanetype) (lanetype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (lanetype) (eqlanetypeP).
Hint Resolve lanetype_eq_dec : eq_dec_db.

(* Auxiliary Definition at:  *)
Definition lanetype_Fnn (var_0 : Fnn) : lanetype :=
	match var_0 return lanetype with
		| Fnn_F32 => lanetype_F32
		| Fnn_F64 => lanetype_F64
	end.

(* Auxiliary Definition at:  *)
Definition lanetype_Inn (var_0 : Inn) : lanetype :=
	match var_0 return lanetype with
		| Inn_I32 => lanetype_I32
		| Inn_I64 => lanetype_I64
	end.

(* Auxiliary Definition at:  *)
Definition lanetype_numtype (var_0 : numtype) : lanetype :=
	match var_0 return lanetype with
		| I32 => lanetype_I32
		| I64 => lanetype_I64
		| F32 => lanetype_F32
		| F64 => lanetype_F64
	end.

(* Auxiliary Definition at:  *)
Definition lanetype_packtype (var_0 : packtype) : lanetype :=
	match var_0 return lanetype with
		| I8 => lanetype_I8
		| I16 => lanetype_I16
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:155.1-155.37 *)
Definition Pnn : Type := packtype.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:156.1-156.38 *)
Inductive Jnn : Type :=
	| Jnn_I32 : Jnn
	| Jnn_I64 : Jnn
	| Jnn_I8 : Jnn
	| Jnn_I16 : Jnn.

Global Instance Inhabited__Jnn : Inhabited (Jnn) := { default_val := Jnn_I32 }.

Definition Jnn_eq_dec : forall (v1 v2 : Jnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Jnn_eqb (v1 v2 : Jnn) : bool :=
	is_left(Jnn_eq_dec v1 v2).
Definition eqJnnP : Equality.axiom (Jnn_eqb) :=
	eq_dec_Equality_axiom (Jnn) (Jnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Jnn) (eqJnnP).
Hint Resolve Jnn_eq_dec : eq_dec_db.

(* Auxiliary Definition at:  *)
Definition lanetype_Jnn (var_0 : Jnn) : lanetype :=
	match var_0 return lanetype with
		| Jnn_I32 => lanetype_I32
		| Jnn_I64 => lanetype_I64
		| Jnn_I8 => lanetype_I8
		| Jnn_I16 => lanetype_I16
	end.

(* Auxiliary Definition at:  *)
Definition Jnn_packtype (var_0 : packtype) : Jnn :=
	match var_0 return Jnn with
		| I8 => Jnn_I8
		| I16 => Jnn_I16
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:157.1-157.37 *)
Definition Lnn : Type := lanetype.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.1-162.18 *)
Definition mut : Type := (option r_MUT).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.1-165.17 *)
Inductive limits : Type :=
	| mk_limits (v_u32 : u32) (u32_opt : (option u32)) : limits.

Global Instance Inhabited__limits : Inhabited (limits) := { default_val := mk_limits default_val default_val }.

Definition limits_eq_dec : forall (v1 v2 : limits),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition limits_eqb (v1 v2 : limits) : bool :=
	is_left(limits_eq_dec v1 v2).
Definition eqlimitsP : Equality.axiom (limits_eqb) :=
	eq_dec_Equality_axiom (limits) (limits_eq_dec).

HB.instance Definition _ := hasDecEq.Build (limits) (eqlimitsP).
Hint Resolve limits_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.8-164.14 *)
Inductive wf_limits : limits -> Prop :=
	| limits_case_0 : forall (v_u32 : u32) (u32_opt : (option u32)), 
		(wf_uN 32 v_u32) ->
		wf_limits (mk_limits v_u32 u32_opt).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:167.1-168.14 *)
Inductive globaltype : Type :=
	| mk_globaltype (v_mut : mut) (v_valtype : valtype) : globaltype.

Global Instance Inhabited__globaltype : Inhabited (globaltype) := { default_val := mk_globaltype default_val default_val }.

Definition globaltype_eq_dec : forall (v1 v2 : globaltype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globaltype_eqb (v1 v2 : globaltype) : bool :=
	is_left(globaltype_eq_dec v1 v2).
Definition eqglobaltypeP : Equality.axiom (globaltype_eqb) :=
	eq_dec_Equality_axiom (globaltype) (globaltype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globaltype) (eqglobaltypeP).
Hint Resolve globaltype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:169.1-170.27 *)
Inductive functype : Type :=
	| mk_functype (v_resulttype : resulttype) (v_resulttype : resulttype) : functype.

Global Instance Inhabited__functype : Inhabited (functype) := { default_val := mk_functype default_val default_val }.

Definition functype_eq_dec : forall (v1 v2 : functype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition functype_eqb (v1 v2 : functype) : bool :=
	is_left(functype_eq_dec v1 v2).
Definition eqfunctypeP : Equality.axiom (functype_eqb) :=
	eq_dec_Equality_axiom (functype) (functype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (functype) (eqfunctypeP).
Hint Resolve functype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.1-172.17 *)
Inductive tabletype : Type :=
	| mk_tabletype (v_limits : limits) (v_reftype : reftype) : tabletype.

Global Instance Inhabited__tabletype : Inhabited (tabletype) := { default_val := mk_tabletype default_val default_val }.

Definition tabletype_eq_dec : forall (v1 v2 : tabletype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tabletype_eqb (v1 v2 : tabletype) : bool :=
	is_left(tabletype_eq_dec v1 v2).
Definition eqtabletypeP : Equality.axiom (tabletype_eqb) :=
	eq_dec_Equality_axiom (tabletype) (tabletype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tabletype) (eqtabletypeP).
Hint Resolve tabletype_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.8-171.17 *)
Inductive wf_tabletype : tabletype -> Prop :=
	| tabletype_case_0 : forall (v_limits : limits) (v_reftype : reftype), 
		(wf_limits v_limits) ->
		wf_tabletype (mk_tabletype v_limits v_reftype).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.1-174.14 *)
Inductive memtype : Type :=
	| PAGE (v_limits : limits) : memtype.

Global Instance Inhabited__memtype : Inhabited (memtype) := { default_val := PAGE default_val }.

Definition memtype_eq_dec : forall (v1 v2 : memtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memtype_eqb (v1 v2 : memtype) : bool :=
	is_left(memtype_eq_dec v1 v2).
Definition eqmemtypeP : Equality.axiom (memtype_eqb) :=
	eq_dec_Equality_axiom (memtype) (memtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memtype) (eqmemtypeP).
Hint Resolve memtype_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.8-173.15 *)
Inductive wf_memtype : memtype -> Prop :=
	| memtype_case_0 : forall (v_limits : limits), 
		(wf_limits v_limits) ->
		wf_memtype (PAGE v_limits).

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:175.1-176.10 *)
Definition elemtype : Type := reftype.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:177.1-178.5 *)
Inductive datatype : Type :=
	| OK : datatype.

Global Instance Inhabited__datatype : Inhabited (datatype) := { default_val := OK }.

Definition datatype_eq_dec : forall (v1 v2 : datatype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition datatype_eqb (v1 v2 : datatype) : bool :=
	is_left(datatype_eq_dec v1 v2).
Definition eqdatatypeP : Equality.axiom (datatype_eqb) :=
	eq_dec_Equality_axiom (datatype) (datatype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (datatype) (eqdatatypeP).
Hint Resolve datatype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.1-180.70 *)
Inductive externtype : Type :=
	| FUNC (v_functype : functype) : externtype
	| GLOBAL (v_globaltype : globaltype) : externtype
	| TABLE (v_tabletype : tabletype) : externtype
	| MEM (v_memtype : memtype) : externtype.

Global Instance Inhabited__externtype : Inhabited (externtype) := { default_val := FUNC default_val }.

Definition externtype_eq_dec : forall (v1 v2 : externtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition externtype_eqb (v1 v2 : externtype) : bool :=
	is_left(externtype_eq_dec v1 v2).
Definition eqexterntypeP : Equality.axiom (externtype_eqb) :=
	eq_dec_Equality_axiom (externtype) (externtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (externtype) (eqexterntypeP).
Hint Resolve externtype_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.8-179.18 *)
Inductive wf_externtype : externtype -> Prop :=
	| externtype_case_0 : forall (v_functype : functype), wf_externtype (FUNC v_functype)
	| externtype_case_1 : forall (v_globaltype : globaltype), wf_externtype (GLOBAL v_globaltype)
	| externtype_case_2 : forall (v_tabletype : tabletype), 
		(wf_tabletype v_tabletype) ->
		wf_externtype (TABLE v_tabletype)
	| externtype_case_3 : forall (v_memtype : memtype), 
		(wf_memtype v_memtype) ->
		wf_externtype (MEM v_memtype).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.1-318.60 *)
Inductive dim : Type :=
	| mk_dim (i : nat) : dim.

Global Instance Inhabited__dim : Inhabited (dim) := { default_val := mk_dim default_val }.

Definition dim_eq_dec : forall (v1 v2 : dim),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition dim_eqb (v1 v2 : dim) : bool :=
	is_left(dim_eq_dec v1 v2).
Definition eqdimP : Equality.axiom (dim_eqb) :=
	eq_dec_Equality_axiom (dim) (dim_eq_dec).

HB.instance Definition _ := hasDecEq.Build (dim) (eqdimP).
Hint Resolve dim_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.1-318.60 *)
Definition proj_dim_0 (x : dim) : (nat) :=
	match x return (nat) with
		| (mk_dim v_num_0) => (v_num_0)
	end.

Global Instance proj_dim_0_coercion : Coercion dim (nat) := { coerce := proj_dim_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.8-318.11 *)
Inductive wf_dim : dim -> Prop :=
	| dim_case_0 : forall (i : nat), 
		(((((i == 1) || (i == 2)) || (i == 4)) || (i == 8)) || (i == 16)) ->
		wf_dim (mk_dim i).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:319.1-319.69 *)
Inductive shape : Type :=
	| X (v_lanetype : lanetype) (v_dim : dim) : shape.

Global Instance Inhabited__shape : Inhabited (shape) := { default_val := X default_val default_val }.

Definition shape_eq_dec : forall (v1 v2 : shape),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition shape_eqb (v1 v2 : shape) : bool :=
	is_left(shape_eq_dec v1 v2).
Definition eqshapeP : Equality.axiom (shape_eqb) :=
	eq_dec_Equality_axiom (shape) (shape_eq_dec).

HB.instance Definition _ := hasDecEq.Build (shape) (eqshapeP).
Hint Resolve shape_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:319.8-319.13 *)
Inductive wf_shape : shape -> Prop :=
	| shape_case_0 : forall (v_lanetype : lanetype) (v_dim : dim), 
		(wf_dim v_dim) ->
		wf_shape (X v_lanetype v_dim).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:206.1-206.32 *)
Definition fun_lanetype (v_shape : shape) : lanetype :=
	match v_shape return lanetype with
		| (X v_Lnn (mk_dim v_N)) => v_Lnn
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:208.1-208.59 *)
Definition res_size (v_valtype : valtype) : (option nat) :=
	match v_valtype return (option nat) with
		| valtype_I32 => (Some 32)
		| valtype_I64 => (Some 64)
		| valtype_F32 => (Some 32)
		| valtype_F64 => (Some 64)
		| valtype_V128 => (Some 128)
		| x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 *)
Definition psize (v_packtype : packtype) : nat :=
	match v_packtype return nat with
		| I8 => 8
		| I16 => 16
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.45 *)
Definition lsize (v_lanetype : lanetype) : nat :=
	match v_lanetype return nat with
		| lanetype_I32 => (!((res_size (valtype_numtype I32))))
		| lanetype_I64 => (!((res_size (valtype_numtype I64))))
		| lanetype_F32 => (!((res_size (valtype_numtype F32))))
		| lanetype_F64 => (!((res_size (valtype_numtype F64))))
		| lanetype_I8 => (psize I8)
		| lanetype_I16 => (psize I16)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 *)
Definition isize (v_Inn : Inn) : nat :=
	match v_Inn return nat with
		| v_Inn => (!((res_size (valtype_Inn v_Inn))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 *)
Definition jsize (v_Jnn : Jnn) : nat :=
	match v_Jnn return nat with
		| v_Jnn => (lsize (lanetype_Jnn v_Jnn))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:213.1-213.70 *)
Definition fsize (v_Fnn : Fnn) : nat :=
	match v_Fnn return nat with
		| v_Fnn => (!((res_size (valtype_Fnn v_Fnn))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:231.1-231.63 *)
Definition sizenn (v_numtype : numtype) : nat :=
	match v_numtype return nat with
		| nt => (!((res_size (valtype_numtype nt))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:232.1-232.63 *)
Definition sizenn1 (v_numtype : numtype) : nat :=
	match v_numtype return nat with
		| nt => (!((res_size (valtype_numtype nt))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:233.1-233.63 *)
Definition sizenn2 (v_numtype : numtype) : nat :=
	match v_numtype return nat with
		| nt => (!((res_size (valtype_numtype nt))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:238.1-238.63 *)
Definition lsizenn (v_lanetype : lanetype) : nat :=
	match v_lanetype return nat with
		| lt => (lsize lt)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:239.1-239.63 *)
Definition lsizenn1 (v_lanetype : lanetype) : nat :=
	match v_lanetype return nat with
		| lt => (lsize lt)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:240.1-240.63 *)
Definition lsizenn2 (v_lanetype : lanetype) : nat :=
	match v_lanetype return nat with
		| lt => (lsize lt)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.40 *)
Definition inv_isize (res_nat : nat) : (option Inn) :=
	match res_nat return (option Inn) with
		| 32 => (Some Inn_I32)
		| 64 => (Some Inn_I64)
		| x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:246.1-246.40 *)
Definition inv_jsize (res_nat : nat) : (option Jnn) :=
	match res_nat return (option Jnn) with
		| 8 => (Some Jnn_I8)
		| 16 => (Some Jnn_I16)
		| 32 => (Some Jnn_I32)
		| 64 => (Some Jnn_I64)
		| x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:247.1-247.40 *)
Definition inv_fsize (res_nat : nat) : (option Fnn) :=
	match res_nat return (option Fnn) with
		| 32 => (Some Fnn_F32)
		| 64 => (Some Fnn_F64)
		| x0 => None
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
Inductive num_ : Type :=
	| mk_num__0 (v_Inn : Inn) (var_x : iN) : num_
	| mk_num__1 (v_Fnn : Fnn) (var_x : fN) : num_.

Global Instance Inhabited__num_ : Inhabited (num_) := { default_val := mk_num__0 default_val default_val }.

Definition num__eq_dec : forall (v1 v2 : num_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition num__eqb (v1 v2 : num_) : bool :=
	is_left(num__eq_dec v1 v2).
Definition eqnum_P : Equality.axiom (num__eqb) :=
	eq_dec_Equality_axiom (num_) (num__eq_dec).

HB.instance Definition _ := hasDecEq.Build (num_) (eqnum_P).
Hint Resolve num__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.8-259.13 *)
Inductive wf_num_ : numtype -> num_ -> Prop :=
	| num__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : iN), 
		((res_size (valtype_Inn v_Inn)) != None) ->
		(wf_uN (!((res_size (valtype_Inn v_Inn)))) var_x) ->
		(v_numtype == (numtype_Inn v_Inn)) ->
		wf_num_ v_numtype (mk_num__0 v_Inn var_x)
	| num__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : fN), 
		(wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x) ->
		(v_numtype == (numtype_Fnn v_Fnn)) ->
		wf_num_ v_numtype (mk_num__1 v_Fnn var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
Definition proj_num__0 (var_x : num_) : (option iN) :=
	match var_x return (option iN) with
		| (mk_num__0 v_Inn var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
Definition proj_num__1 (var_x : num_) : (option fN) :=
	match var_x return (option fN) with
		| (mk_num__1 v_Fnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:263.1-263.36 *)
Definition pack_ : Type := iN.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
Inductive lane_ : Type :=
	| mk_lane__0 (v_numtype : numtype) (var_x : num_) : lane_
	| mk_lane__1 (v_packtype : packtype) (var_x : pack_) : lane_
	| mk_lane__2 (v_Jnn : Jnn) (var_x : iN) : lane_.

Global Instance Inhabited__lane_ : Inhabited (lane_) := { default_val := mk_lane__0 default_val default_val }.

Definition lane__eq_dec : forall (v1 v2 : lane_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition lane__eqb (v1 v2 : lane_) : bool :=
	is_left(lane__eq_dec v1 v2).
Definition eqlane_P : Equality.axiom (lane__eqb) :=
	eq_dec_Equality_axiom (lane_) (lane__eq_dec).

HB.instance Definition _ := hasDecEq.Build (lane_) (eqlane_P).
Hint Resolve lane__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.8-265.14 *)
Inductive wf_lane_ : lanetype -> lane_ -> Prop :=
	| lane__case_0 : forall (v_lanetype : lanetype) (v_numtype : numtype) (var_x : num_), 
		(wf_num_ v_numtype var_x) ->
		(v_lanetype == (lanetype_numtype v_numtype)) ->
		wf_lane_ v_lanetype (mk_lane__0 v_numtype var_x)
	| lane__case_1 : forall (v_lanetype : lanetype) (v_packtype : packtype) (var_x : pack_), 
		(wf_uN (psize v_packtype) var_x) ->
		(v_lanetype == (lanetype_packtype v_packtype)) ->
		wf_lane_ v_lanetype (mk_lane__1 v_packtype var_x)
	| lane__case_2 : forall (v_lanetype : lanetype) (v_Jnn : Jnn) (var_x : iN), 
		(wf_uN (lsize (lanetype_Jnn v_Jnn)) var_x) ->
		(v_lanetype == (lanetype_Jnn v_Jnn)) ->
		wf_lane_ v_lanetype (mk_lane__2 v_Jnn var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
Definition proj_lane__0 (var_x : lane_) : (option num_) :=
	match var_x return (option num_) with
		| (mk_lane__0 v_numtype var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
Definition proj_lane__1 (var_x : lane_) : (option pack_) :=
	match var_x return (option pack_) with
		| (mk_lane__1 v_packtype var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
Definition proj_lane__2 (var_x : lane_) : (option iN) :=
	match var_x return (option iN) with
		| (mk_lane__2 v_Jnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:270.1-270.34 *)
Definition vec_ : Type := vN.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.1-272.35 *)
Definition fun_zero (v_numtype : numtype) : num_ :=
	match v_numtype return num_ with
		| I32 => (mk_num__0 Inn_I32 (mk_uN 0))
		| I64 => (mk_num__0 Inn_I64 (mk_uN 0))
		| F32 => (mk_num__1 Fnn_F32 (fzero (!((res_size (valtype_Fnn Fnn_F32))))))
		| F64 => (mk_num__1 Fnn_F64 (fzero (!((res_size (valtype_Fnn Fnn_F64))))))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.6-272.11 *)
Lemma zero_is_wf : forall (v_numtype : numtype) (ret_val : num_),
	(ret_val == (fun_zero v_numtype)) ->
	(wf_num_ v_numtype ret_val).
Proof. Admitted.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:279.1-279.42 *)
Inductive sx : Type :=
	| U : sx
	| res_S : sx.

Global Instance Inhabited__sx : Inhabited (sx) := { default_val := U }.

Definition sx_eq_dec : forall (v1 v2 : sx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition sx_eqb (v1 v2 : sx) : bool :=
	is_left(sx_eq_dec v1 v2).
Definition eqsxP : Equality.axiom (sx_eqb) :=
	eq_dec_Equality_axiom (sx) (sx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (sx) (eqsxP).
Hint Resolve sx_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 *)
Inductive sz : Type :=
	| mk_sz (i : nat) : sz.

Global Instance Inhabited__sz : Inhabited (sz) := { default_val := mk_sz default_val }.

Definition sz_eq_dec : forall (v1 v2 : sz),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition sz_eqb (v1 v2 : sz) : bool :=
	is_left(sz_eq_dec v1 v2).
Definition eqszP : Equality.axiom (sz_eqb) :=
	eq_dec_Equality_axiom (sz) (sz_eq_dec).

HB.instance Definition _ := hasDecEq.Build (sz) (eqszP).
Hint Resolve sz_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 *)
Definition proj_sz_0 (x : sz) : (nat) :=
	match x return (nat) with
		| (mk_sz v_num_0) => (v_num_0)
	end.

Global Instance proj_sz_0_coercion : Coercion sz (nat) := { coerce := proj_sz_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.8-280.10 *)
Inductive wf_sz : sz -> Prop :=
	| sz_case_0 : forall (i : nat), 
		((((i == 8) || (i == 16)) || (i == 32)) || (i == 64)) ->
		wf_sz (mk_sz i).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
Inductive unop_Inn : Type :=
	| CLZ : unop_Inn
	| CTZ : unop_Inn
	| POPCNT : unop_Inn
	| EXTEND (v_n : n) : unop_Inn.

Global Instance Inhabited__unop_Inn : Inhabited (unop_Inn) := { default_val := CLZ }.

Definition unop_Inn_eq_dec : forall (v1 v2 : unop_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition unop_Inn_eqb (v1 v2 : unop_Inn) : bool :=
	is_left(unop_Inn_eq_dec v1 v2).
Definition equnop_InnP : Equality.axiom (unop_Inn_eqb) :=
	eq_dec_Equality_axiom (unop_Inn) (unop_Inn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (unop_Inn) (equnop_InnP).
Hint Resolve unop_Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
Inductive unop_Fnn : Type :=
	| ABS : unop_Fnn
	| unop_Fnn_NEG : unop_Fnn
	| SQRT : unop_Fnn
	| CEIL : unop_Fnn
	| FLOOR : unop_Fnn
	| TRUNC : unop_Fnn
	| NEAREST : unop_Fnn.

Global Instance Inhabited__unop_Fnn : Inhabited (unop_Fnn) := { default_val := ABS }.

Definition unop_Fnn_eq_dec : forall (v1 v2 : unop_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition unop_Fnn_eqb (v1 v2 : unop_Fnn) : bool :=
	is_left(unop_Fnn_eq_dec v1 v2).
Definition equnop_FnnP : Equality.axiom (unop_Fnn_eqb) :=
	eq_dec_Equality_axiom (unop_Fnn) (unop_Fnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (unop_Fnn) (equnop_FnnP).
Hint Resolve unop_Fnn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
Inductive unop_ : Type :=
	| mk_unop__0 (v_Inn : Inn) (var_x : unop_Inn) : unop_
	| mk_unop__1 (v_Fnn : Fnn) (var_x : unop_Fnn) : unop_.

Global Instance Inhabited__unop_ : Inhabited (unop_) := { default_val := mk_unop__0 default_val default_val }.

Definition unop__eq_dec : forall (v1 v2 : unop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition unop__eqb (v1 v2 : unop_) : bool :=
	is_left(unop__eq_dec v1 v2).
Definition equnop_P : Equality.axiom (unop__eqb) :=
	eq_dec_Equality_axiom (unop_) (unop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (unop_) (equnop_P).
Hint Resolve unop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.8-282.14 *)
Inductive wf_unop_ : numtype -> unop_ -> Prop :=
	| unop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : unop_Inn), 
		(v_numtype == (numtype_Inn v_Inn)) ->
		wf_unop_ v_numtype (mk_unop__0 v_Inn var_x)
	| unop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : unop_Fnn), 
		(v_numtype == (numtype_Fnn v_Fnn)) ->
		wf_unop_ v_numtype (mk_unop__1 v_Fnn var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
Definition proj_unop__0 (var_x : unop_) : (option unop_Inn) :=
	match var_x return (option unop_Inn) with
		| (mk_unop__0 v_Inn var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
Definition proj_unop__1 (var_x : unop_) : (option unop_Fnn) :=
	match var_x return (option unop_Fnn) with
		| (mk_unop__1 v_Fnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
Inductive binop_Inn : Type :=
	| ADD : binop_Inn
	| SUB : binop_Inn
	| MUL : binop_Inn
	| DIV (v_sx : sx) : binop_Inn
	| REM (v_sx : sx) : binop_Inn
	| AND : binop_Inn
	| OR : binop_Inn
	| XOR : binop_Inn
	| SHL : binop_Inn
	| SHR (v_sx : sx) : binop_Inn
	| ROTL : binop_Inn
	| ROTR : binop_Inn.

Global Instance Inhabited__binop_Inn : Inhabited (binop_Inn) := { default_val := ADD }.

Definition binop_Inn_eq_dec : forall (v1 v2 : binop_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition binop_Inn_eqb (v1 v2 : binop_Inn) : bool :=
	is_left(binop_Inn_eq_dec v1 v2).
Definition eqbinop_InnP : Equality.axiom (binop_Inn_eqb) :=
	eq_dec_Equality_axiom (binop_Inn) (binop_Inn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (binop_Inn) (eqbinop_InnP).
Hint Resolve binop_Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
Inductive binop_Fnn : Type :=
	| binop_Fnn_ADD : binop_Fnn
	| binop_Fnn_SUB : binop_Fnn
	| binop_Fnn_MUL : binop_Fnn
	| binop_Fnn_DIV : binop_Fnn
	| MIN : binop_Fnn
	| MAX : binop_Fnn
	| COPYSIGN : binop_Fnn.

Global Instance Inhabited__binop_Fnn : Inhabited (binop_Fnn) := { default_val := binop_Fnn_ADD }.

Definition binop_Fnn_eq_dec : forall (v1 v2 : binop_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition binop_Fnn_eqb (v1 v2 : binop_Fnn) : bool :=
	is_left(binop_Fnn_eq_dec v1 v2).
Definition eqbinop_FnnP : Equality.axiom (binop_Fnn_eqb) :=
	eq_dec_Equality_axiom (binop_Fnn) (binop_Fnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (binop_Fnn) (eqbinop_FnnP).
Hint Resolve binop_Fnn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
Inductive binop_ : Type :=
	| mk_binop__0 (v_Inn : Inn) (var_x : binop_Inn) : binop_
	| mk_binop__1 (v_Fnn : Fnn) (var_x : binop_Fnn) : binop_.

Global Instance Inhabited__binop_ : Inhabited (binop_) := { default_val := mk_binop__0 default_val default_val }.

Definition binop__eq_dec : forall (v1 v2 : binop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition binop__eqb (v1 v2 : binop_) : bool :=
	is_left(binop__eq_dec v1 v2).
Definition eqbinop_P : Equality.axiom (binop__eqb) :=
	eq_dec_Equality_axiom (binop_) (binop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (binop_) (eqbinop_P).
Hint Resolve binop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.8-286.15 *)
Inductive wf_binop_ : numtype -> binop_ -> Prop :=
	| binop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : binop_Inn), 
		(v_numtype == (numtype_Inn v_Inn)) ->
		wf_binop_ v_numtype (mk_binop__0 v_Inn var_x)
	| binop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : binop_Fnn), 
		(v_numtype == (numtype_Fnn v_Fnn)) ->
		wf_binop_ v_numtype (mk_binop__1 v_Fnn var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
Definition proj_binop__0 (var_x : binop_) : (option binop_Inn) :=
	match var_x return (option binop_Inn) with
		| (mk_binop__0 v_Inn var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
Definition proj_binop__1 (var_x : binop_) : (option binop_Fnn) :=
	match var_x return (option binop_Fnn) with
		| (mk_binop__1 v_Fnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
Inductive testop_Inn : Type :=
	| EQZ : testop_Inn.

Global Instance Inhabited__testop_Inn : Inhabited (testop_Inn) := { default_val := EQZ }.

Definition testop_Inn_eq_dec : forall (v1 v2 : testop_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition testop_Inn_eqb (v1 v2 : testop_Inn) : bool :=
	is_left(testop_Inn_eq_dec v1 v2).
Definition eqtestop_InnP : Equality.axiom (testop_Inn_eqb) :=
	eq_dec_Equality_axiom (testop_Inn) (testop_Inn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (testop_Inn) (eqtestop_InnP).
Hint Resolve testop_Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
Inductive testop_ : Type :=
	| mk_testop__0 (v_Inn : Inn) (var_x : testop_Inn) : testop_.

Global Instance Inhabited__testop_ : Inhabited (testop_) := { default_val := mk_testop__0 default_val default_val }.

Definition testop__eq_dec : forall (v1 v2 : testop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition testop__eqb (v1 v2 : testop_) : bool :=
	is_left(testop__eq_dec v1 v2).
Definition eqtestop_P : Equality.axiom (testop__eqb) :=
	eq_dec_Equality_axiom (testop_) (testop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (testop_) (eqtestop_P).
Hint Resolve testop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.8-293.16 *)
Inductive wf_testop_ : numtype -> testop_ -> Prop :=
	| testop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : testop_Inn), 
		(v_numtype == (numtype_Inn v_Inn)) ->
		wf_testop_ v_numtype (mk_testop__0 v_Inn var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
Definition proj_testop__0 (var_x : testop_) : testop_Inn :=
	match var_x return testop_Inn with
		| (mk_testop__0 v_Inn var_x) => var_x
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
Inductive relop_Inn : Type :=
	| EQ : relop_Inn
	| NE : relop_Inn
	| LT (v_sx : sx) : relop_Inn
	| GT (v_sx : sx) : relop_Inn
	| LE (v_sx : sx) : relop_Inn
	| GE (v_sx : sx) : relop_Inn.

Global Instance Inhabited__relop_Inn : Inhabited (relop_Inn) := { default_val := EQ }.

Definition relop_Inn_eq_dec : forall (v1 v2 : relop_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition relop_Inn_eqb (v1 v2 : relop_Inn) : bool :=
	is_left(relop_Inn_eq_dec v1 v2).
Definition eqrelop_InnP : Equality.axiom (relop_Inn_eqb) :=
	eq_dec_Equality_axiom (relop_Inn) (relop_Inn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (relop_Inn) (eqrelop_InnP).
Hint Resolve relop_Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
Inductive relop_Fnn : Type :=
	| relop_Fnn_EQ : relop_Fnn
	| relop_Fnn_NE : relop_Fnn
	| relop_Fnn_LT : relop_Fnn
	| relop_Fnn_GT : relop_Fnn
	| relop_Fnn_LE : relop_Fnn
	| relop_Fnn_GE : relop_Fnn.

Global Instance Inhabited__relop_Fnn : Inhabited (relop_Fnn) := { default_val := relop_Fnn_EQ }.

Definition relop_Fnn_eq_dec : forall (v1 v2 : relop_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition relop_Fnn_eqb (v1 v2 : relop_Fnn) : bool :=
	is_left(relop_Fnn_eq_dec v1 v2).
Definition eqrelop_FnnP : Equality.axiom (relop_Fnn_eqb) :=
	eq_dec_Equality_axiom (relop_Fnn) (relop_Fnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (relop_Fnn) (eqrelop_FnnP).
Hint Resolve relop_Fnn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
Inductive relop_ : Type :=
	| mk_relop__0 (v_Inn : Inn) (var_x : relop_Inn) : relop_
	| mk_relop__1 (v_Fnn : Fnn) (var_x : relop_Fnn) : relop_.

Global Instance Inhabited__relop_ : Inhabited (relop_) := { default_val := mk_relop__0 default_val default_val }.

Definition relop__eq_dec : forall (v1 v2 : relop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition relop__eqb (v1 v2 : relop_) : bool :=
	is_left(relop__eq_dec v1 v2).
Definition eqrelop_P : Equality.axiom (relop__eqb) :=
	eq_dec_Equality_axiom (relop_) (relop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (relop_) (eqrelop_P).
Hint Resolve relop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.8-297.15 *)
Inductive wf_relop_ : numtype -> relop_ -> Prop :=
	| relop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : relop_Inn), 
		(v_numtype == (numtype_Inn v_Inn)) ->
		wf_relop_ v_numtype (mk_relop__0 v_Inn var_x)
	| relop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : relop_Fnn), 
		(v_numtype == (numtype_Fnn v_Fnn)) ->
		wf_relop_ v_numtype (mk_relop__1 v_Fnn var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
Definition proj_relop__0 (var_x : relop_) : (option relop_Inn) :=
	match var_x return (option relop_Inn) with
		| (mk_relop__0 v_Inn var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
Definition proj_relop__1 (var_x : relop_) : (option relop_Fnn) :=
	match var_x return (option relop_Fnn) with
		| (mk_relop__1 v_Fnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-313.16 *)
Inductive cvtop : Type :=
	| cvtop_EXTEND (v_sx : sx) : cvtop
	| WRAP : cvtop
	| CONVERT (v_sx : sx) : cvtop
	| cvtop_TRUNC (v_sx : sx) : cvtop
	| TRUNC_SAT (v_sx : sx) : cvtop
	| PROMOTE : cvtop
	| DEMOTE : cvtop
	| REINTERPRET : cvtop.

Global Instance Inhabited__cvtop : Inhabited (cvtop) := { default_val := cvtop_EXTEND default_val }.

Definition cvtop_eq_dec : forall (v1 v2 : cvtop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition cvtop_eqb (v1 v2 : cvtop) : bool :=
	is_left(cvtop_eq_dec v1 v2).
Definition eqcvtopP : Equality.axiom (cvtop_eqb) :=
	eq_dec_Equality_axiom (cvtop) (cvtop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (cvtop) (eqcvtopP).
Hint Resolve cvtop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:320.1-320.69 *)
Inductive ishape : Type :=
	| ishape_X (v_Jnn : Jnn) (v_dim : dim) : ishape.

Global Instance Inhabited__ishape : Inhabited (ishape) := { default_val := ishape_X default_val default_val }.

Definition ishape_eq_dec : forall (v1 v2 : ishape),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition ishape_eqb (v1 v2 : ishape) : bool :=
	is_left(ishape_eq_dec v1 v2).
Definition eqishapeP : Equality.axiom (ishape_eqb) :=
	eq_dec_Equality_axiom (ishape) (ishape_eq_dec).

HB.instance Definition _ := hasDecEq.Build (ishape) (eqishapeP).
Hint Resolve ishape_eq_dec : eq_dec_db.

(* Auxiliary Definition at:  *)
Definition shape_ishape (var_0 : ishape) : shape :=
	match var_0 return shape with
		| (ishape_X x0 x1) => (X (lanetype_Jnn x0) x1)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:320.8-320.14 *)
Inductive wf_ishape : ishape -> Prop :=
	| ishape_case_0 : forall (v_Jnn : Jnn) (v_dim : dim), 
		(wf_dim v_dim) ->
		wf_ishape (ishape_X v_Jnn v_dim).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:321.1-321.69 *)
Inductive fshape : Type :=
	| fshape_X (v_Fnn : Fnn) (v_dim : dim) : fshape.

Global Instance Inhabited__fshape : Inhabited (fshape) := { default_val := fshape_X default_val default_val }.

Definition fshape_eq_dec : forall (v1 v2 : fshape),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition fshape_eqb (v1 v2 : fshape) : bool :=
	is_left(fshape_eq_dec v1 v2).
Definition eqfshapeP : Equality.axiom (fshape_eqb) :=
	eq_dec_Equality_axiom (fshape) (fshape_eq_dec).

HB.instance Definition _ := hasDecEq.Build (fshape) (eqfshapeP).
Hint Resolve fshape_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:321.8-321.14 *)
Inductive wf_fshape : fshape -> Prop :=
	| fshape_case_0 : forall (v_Fnn : Fnn) (v_dim : dim), 
		(wf_dim v_dim) ->
		wf_fshape (fshape_X v_Fnn v_dim).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:322.1-322.69 *)
Inductive pshape : Type :=
	| pshape_X (v_Pnn : Pnn) (v_dim : dim) : pshape.

Global Instance Inhabited__pshape : Inhabited (pshape) := { default_val := pshape_X default_val default_val }.

Definition pshape_eq_dec : forall (v1 v2 : pshape),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition pshape_eqb (v1 v2 : pshape) : bool :=
	is_left(pshape_eq_dec v1 v2).
Definition eqpshapeP : Equality.axiom (pshape_eqb) :=
	eq_dec_Equality_axiom (pshape) (pshape_eq_dec).

HB.instance Definition _ := hasDecEq.Build (pshape) (eqpshapeP).
Hint Resolve pshape_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:322.8-322.14 *)
Inductive wf_pshape : pshape -> Prop :=
	| pshape_case_0 : forall (v_Pnn : Pnn) (v_dim : dim), 
		(wf_dim v_dim) ->
		wf_pshape (pshape_X v_Pnn v_dim).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.1-324.22 *)
Definition fun_dim (v_shape : shape) : dim :=
	match v_shape return dim with
		| (X v_Lnn (mk_dim v_N)) => (mk_dim v_N)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.6-324.10 *)
Lemma dim_is_wf : forall (v_shape : shape) (ret_val : dim),
	(wf_shape v_shape) ->
	(ret_val == (fun_dim v_shape)) ->
	(wf_dim ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.1-325.41 *)
Definition shsize (v_shape : shape) : nat :=
	match v_shape return nat with
		| (X v_Lnn (mk_dim v_N)) => ((lsize v_Lnn) * v_N)%N
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:327.1-327.20 *)
Inductive vvunop : Type :=
	| NOT : vvunop.

Global Instance Inhabited__vvunop : Inhabited (vvunop) := { default_val := NOT }.

Definition vvunop_eq_dec : forall (v1 v2 : vvunop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vvunop_eqb (v1 v2 : vvunop) : bool :=
	is_left(vvunop_eq_dec v1 v2).
Definition eqvvunopP : Equality.axiom (vvunop_eqb) :=
	eq_dec_Equality_axiom (vvunop) (vvunop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vvunop) (eqvvunopP).
Hint Resolve vvunop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:328.1-328.41 *)
Inductive vvbinop : Type :=
	| vvbinop_AND : vvbinop
	| ANDNOT : vvbinop
	| vvbinop_OR : vvbinop
	| vvbinop_XOR : vvbinop.

Global Instance Inhabited__vvbinop : Inhabited (vvbinop) := { default_val := vvbinop_AND }.

Definition vvbinop_eq_dec : forall (v1 v2 : vvbinop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vvbinop_eqb (v1 v2 : vvbinop) : bool :=
	is_left(vvbinop_eq_dec v1 v2).
Definition eqvvbinopP : Equality.axiom (vvbinop_eqb) :=
	eq_dec_Equality_axiom (vvbinop) (vvbinop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vvbinop) (eqvvbinopP).
Hint Resolve vvbinop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:329.1-329.28 *)
Inductive vvternop : Type :=
	| BITSELECT : vvternop.

Global Instance Inhabited__vvternop : Inhabited (vvternop) := { default_val := BITSELECT }.

Definition vvternop_eq_dec : forall (v1 v2 : vvternop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vvternop_eqb (v1 v2 : vvternop) : bool :=
	is_left(vvternop_eq_dec v1 v2).
Definition eqvvternopP : Equality.axiom (vvternop_eqb) :=
	eq_dec_Equality_axiom (vvternop) (vvternop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vvternop) (eqvvternopP).
Hint Resolve vvternop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:330.1-330.27 *)
Inductive vvtestop : Type :=
	| ANY_TRUE : vvtestop.

Global Instance Inhabited__vvtestop : Inhabited (vvtestop) := { default_val := ANY_TRUE }.

Definition vvtestop_eq_dec : forall (v1 v2 : vvtestop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vvtestop_eqb (v1 v2 : vvtestop) : bool :=
	is_left(vvtestop_eq_dec v1 v2).
Definition eqvvtestopP : Equality.axiom (vvtestop_eqb) :=
	eq_dec_Equality_axiom (vvtestop) (vvtestop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vvtestop) (eqvvtestopP).
Hint Resolve vvtestop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
Inductive vunop_Jnn_N : Type :=
	| vunop_Jnn_N_ABS : vunop_Jnn_N
	| vunop_Jnn_N_NEG : vunop_Jnn_N
	| vunop_Jnn_N_POPCNT : vunop_Jnn_N.

Global Instance Inhabited__vunop_Jnn_N : Inhabited (vunop_Jnn_N) := { default_val := vunop_Jnn_N_ABS }.

Definition vunop_Jnn_N_eq_dec : forall (v1 v2 : vunop_Jnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vunop_Jnn_N_eqb (v1 v2 : vunop_Jnn_N) : bool :=
	is_left(vunop_Jnn_N_eq_dec v1 v2).
Definition eqvunop_Jnn_NP : Equality.axiom (vunop_Jnn_N_eqb) :=
	eq_dec_Equality_axiom (vunop_Jnn_N) (vunop_Jnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vunop_Jnn_N) (eqvunop_Jnn_NP).
Hint Resolve vunop_Jnn_N_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.8-332.15 *)
Inductive wf_vunop_Jnn_N : Jnn -> res_N -> vunop_Jnn_N -> Prop :=
	| vunop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : res_N), wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_ABS
	| vunop_Jnn_N_case_1 : forall (v_Jnn : Jnn) (v_N : res_N), wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_NEG
	| vunop_Jnn_N_case_2 : forall (v_Jnn : Jnn) (v_N : res_N), 
		(v_Jnn == Jnn_I8) ->
		wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_POPCNT.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
Inductive vunop_Fnn_N : Type :=
	| vunop_Fnn_N_ABS : vunop_Fnn_N
	| vunop_Fnn_N_NEG : vunop_Fnn_N
	| vunop_Fnn_N_SQRT : vunop_Fnn_N
	| vunop_Fnn_N_CEIL : vunop_Fnn_N
	| vunop_Fnn_N_FLOOR : vunop_Fnn_N
	| vunop_Fnn_N_TRUNC : vunop_Fnn_N
	| vunop_Fnn_N_NEAREST : vunop_Fnn_N.

Global Instance Inhabited__vunop_Fnn_N : Inhabited (vunop_Fnn_N) := { default_val := vunop_Fnn_N_ABS }.

Definition vunop_Fnn_N_eq_dec : forall (v1 v2 : vunop_Fnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vunop_Fnn_N_eqb (v1 v2 : vunop_Fnn_N) : bool :=
	is_left(vunop_Fnn_N_eq_dec v1 v2).
Definition eqvunop_Fnn_NP : Equality.axiom (vunop_Fnn_N_eqb) :=
	eq_dec_Equality_axiom (vunop_Fnn_N) (vunop_Fnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vunop_Fnn_N) (eqvunop_Fnn_NP).
Hint Resolve vunop_Fnn_N_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
Inductive vunop_ : Type :=
	| mk_vunop__0 (v_Jnn : Jnn) (v_N : res_N) (var_x : vunop_Jnn_N) : vunop_
	| mk_vunop__1 (v_Fnn : Fnn) (v_N : res_N) (var_x : vunop_Fnn_N) : vunop_.

Global Instance Inhabited__vunop_ : Inhabited (vunop_) := { default_val := mk_vunop__0 default_val default_val default_val }.

Definition vunop__eq_dec : forall (v1 v2 : vunop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vunop__eqb (v1 v2 : vunop_) : bool :=
	is_left(vunop__eq_dec v1 v2).
Definition eqvunop_P : Equality.axiom (vunop__eqb) :=
	eq_dec_Equality_axiom (vunop_) (vunop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (vunop_) (eqvunop_P).
Hint Resolve vunop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.8-332.15 *)
Inductive wf_vunop_ : shape -> vunop_ -> Prop :=
	| vunop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_N : res_N) (var_x : vunop_Jnn_N), 
		(wf_vunop_Jnn_N v_Jnn v_N var_x) ->
		(v_shape == (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		wf_vunop_ v_shape (mk_vunop__0 v_Jnn v_N var_x)
	| vunop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_N : res_N) (var_x : vunop_Fnn_N), 
		(v_shape == (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) ->
		wf_vunop_ v_shape (mk_vunop__1 v_Fnn v_N var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
Definition proj_vunop__0 (var_x : vunop_) : (option vunop_Jnn_N) :=
	match var_x return (option vunop_Jnn_N) with
		| (mk_vunop__0 v_Jnn v_N var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
Definition proj_vunop__1 (var_x : vunop_) : (option vunop_Fnn_N) :=
	match var_x return (option vunop_Fnn_N) with
		| (mk_vunop__1 v_Fnn v_N var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
Inductive vbinop_Jnn_N : Type :=
	| vbinop_Jnn_N_ADD : vbinop_Jnn_N
	| vbinop_Jnn_N_SUB : vbinop_Jnn_N
	| ADD_SAT (v_sx : sx) : vbinop_Jnn_N
	| SUB_SAT (v_sx : sx) : vbinop_Jnn_N
	| vbinop_Jnn_N_MUL : vbinop_Jnn_N
	| AVGRU : vbinop_Jnn_N
	| Q15MULR_SATS : vbinop_Jnn_N
	| vbinop_Jnn_N_MIN (v_sx : sx) : vbinop_Jnn_N
	| vbinop_Jnn_N_MAX (v_sx : sx) : vbinop_Jnn_N.

Global Instance Inhabited__vbinop_Jnn_N : Inhabited (vbinop_Jnn_N) := { default_val := vbinop_Jnn_N_ADD }.

Definition vbinop_Jnn_N_eq_dec : forall (v1 v2 : vbinop_Jnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vbinop_Jnn_N_eqb (v1 v2 : vbinop_Jnn_N) : bool :=
	is_left(vbinop_Jnn_N_eq_dec v1 v2).
Definition eqvbinop_Jnn_NP : Equality.axiom (vbinop_Jnn_N_eqb) :=
	eq_dec_Equality_axiom (vbinop_Jnn_N) (vbinop_Jnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vbinop_Jnn_N) (eqvbinop_Jnn_NP).
Hint Resolve vbinop_Jnn_N_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.16 *)
Inductive wf_vbinop_Jnn_N : Jnn -> res_N -> vbinop_Jnn_N -> Prop :=
	| vbinop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : res_N), wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_ADD
	| vbinop_Jnn_N_case_1 : forall (v_Jnn : Jnn) (v_N : res_N), wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_SUB
	| vbinop_Jnn_N_case_2 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 16)%N ->
		wf_vbinop_Jnn_N v_Jnn v_N (ADD_SAT v_sx)
	| vbinop_Jnn_N_case_3 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 16)%N ->
		wf_vbinop_Jnn_N v_Jnn v_N (SUB_SAT v_sx)
	| vbinop_Jnn_N_case_4 : forall (v_Jnn : Jnn) (v_N : res_N), 
		((lsizenn (lanetype_Jnn v_Jnn)) >= 16)%N ->
		wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_MUL
	| vbinop_Jnn_N_case_5 : forall (v_Jnn : Jnn) (v_N : res_N), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 16)%N ->
		wf_vbinop_Jnn_N v_Jnn v_N AVGRU
	| vbinop_Jnn_N_case_6 : forall (v_Jnn : Jnn) (v_N : res_N), 
		((lsizenn (lanetype_Jnn v_Jnn)) == 16) ->
		wf_vbinop_Jnn_N v_Jnn v_N Q15MULR_SATS
	| vbinop_Jnn_N_case_7 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 32)%N ->
		wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N_MIN v_sx)
	| vbinop_Jnn_N_case_8 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 32)%N ->
		wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N_MAX v_sx).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
Inductive vbinop_Fnn_N : Type :=
	| vbinop_Fnn_N_ADD : vbinop_Fnn_N
	| vbinop_Fnn_N_SUB : vbinop_Fnn_N
	| vbinop_Fnn_N_MUL : vbinop_Fnn_N
	| vbinop_Fnn_N_DIV : vbinop_Fnn_N
	| vbinop_Fnn_N_MIN : vbinop_Fnn_N
	| vbinop_Fnn_N_MAX : vbinop_Fnn_N
	| PMIN : vbinop_Fnn_N
	| PMAX : vbinop_Fnn_N.

Global Instance Inhabited__vbinop_Fnn_N : Inhabited (vbinop_Fnn_N) := { default_val := vbinop_Fnn_N_ADD }.

Definition vbinop_Fnn_N_eq_dec : forall (v1 v2 : vbinop_Fnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vbinop_Fnn_N_eqb (v1 v2 : vbinop_Fnn_N) : bool :=
	is_left(vbinop_Fnn_N_eq_dec v1 v2).
Definition eqvbinop_Fnn_NP : Equality.axiom (vbinop_Fnn_N_eqb) :=
	eq_dec_Equality_axiom (vbinop_Fnn_N) (vbinop_Fnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vbinop_Fnn_N) (eqvbinop_Fnn_NP).
Hint Resolve vbinop_Fnn_N_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
Inductive vbinop_ : Type :=
	| mk_vbinop__0 (v_Jnn : Jnn) (v_N : res_N) (var_x : vbinop_Jnn_N) : vbinop_
	| mk_vbinop__1 (v_Fnn : Fnn) (v_N : res_N) (var_x : vbinop_Fnn_N) : vbinop_.

Global Instance Inhabited__vbinop_ : Inhabited (vbinop_) := { default_val := mk_vbinop__0 default_val default_val default_val }.

Definition vbinop__eq_dec : forall (v1 v2 : vbinop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vbinop__eqb (v1 v2 : vbinop_) : bool :=
	is_left(vbinop__eq_dec v1 v2).
Definition eqvbinop_P : Equality.axiom (vbinop__eqb) :=
	eq_dec_Equality_axiom (vbinop_) (vbinop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (vbinop_) (eqvbinop_P).
Hint Resolve vbinop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.16 *)
Inductive wf_vbinop_ : shape -> vbinop_ -> Prop :=
	| vbinop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_N : res_N) (var_x : vbinop_Jnn_N), 
		(wf_vbinop_Jnn_N v_Jnn v_N var_x) ->
		(v_shape == (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		wf_vbinop_ v_shape (mk_vbinop__0 v_Jnn v_N var_x)
	| vbinop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_N : res_N) (var_x : vbinop_Fnn_N), 
		(v_shape == (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) ->
		wf_vbinop_ v_shape (mk_vbinop__1 v_Fnn v_N var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
Definition proj_vbinop__0 (var_x : vbinop_) : (option vbinop_Jnn_N) :=
	match var_x return (option vbinop_Jnn_N) with
		| (mk_vbinop__0 v_Jnn v_N var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
Definition proj_vbinop__1 (var_x : vbinop_) : (option vbinop_Fnn_N) :=
	match var_x return (option vbinop_Fnn_N) with
		| (mk_vbinop__1 v_Fnn v_N var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 *)
Inductive vtestop_Jnn_N : Type :=
	| ALL_TRUE : vtestop_Jnn_N.

Global Instance Inhabited__vtestop_Jnn_N : Inhabited (vtestop_Jnn_N) := { default_val := ALL_TRUE }.

Definition vtestop_Jnn_N_eq_dec : forall (v1 v2 : vtestop_Jnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vtestop_Jnn_N_eqb (v1 v2 : vtestop_Jnn_N) : bool :=
	is_left(vtestop_Jnn_N_eq_dec v1 v2).
Definition eqvtestop_Jnn_NP : Equality.axiom (vtestop_Jnn_N_eqb) :=
	eq_dec_Equality_axiom (vtestop_Jnn_N) (vtestop_Jnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vtestop_Jnn_N) (eqvtestop_Jnn_NP).
Hint Resolve vtestop_Jnn_N_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 *)
Inductive vtestop_ : Type :=
	| mk_vtestop__0 (v_Jnn : Jnn) (v_N : res_N) (var_x : vtestop_Jnn_N) : vtestop_.

Global Instance Inhabited__vtestop_ : Inhabited (vtestop_) := { default_val := mk_vtestop__0 default_val default_val default_val }.

Definition vtestop__eq_dec : forall (v1 v2 : vtestop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vtestop__eqb (v1 v2 : vtestop_) : bool :=
	is_left(vtestop__eq_dec v1 v2).
Definition eqvtestop_P : Equality.axiom (vtestop__eqb) :=
	eq_dec_Equality_axiom (vtestop_) (vtestop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (vtestop_) (eqvtestop_P).
Hint Resolve vtestop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.8-350.17 *)
Inductive wf_vtestop_ : shape -> vtestop_ -> Prop :=
	| vtestop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_N : res_N) (var_x : vtestop_Jnn_N), 
		(v_shape == (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		wf_vtestop_ v_shape (mk_vtestop__0 v_Jnn v_N var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 *)
Definition proj_vtestop__0 (var_x : vtestop_) : vtestop_Jnn_N :=
	match var_x return vtestop_Jnn_N with
		| (mk_vtestop__0 v_Jnn v_N var_x) => var_x
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
Inductive vrelop_Jnn_N : Type :=
	| vrelop_Jnn_N_EQ : vrelop_Jnn_N
	| vrelop_Jnn_N_NE : vrelop_Jnn_N
	| vrelop_Jnn_N_LT (v_sx : sx) : vrelop_Jnn_N
	| vrelop_Jnn_N_GT (v_sx : sx) : vrelop_Jnn_N
	| vrelop_Jnn_N_LE (v_sx : sx) : vrelop_Jnn_N
	| vrelop_Jnn_N_GE (v_sx : sx) : vrelop_Jnn_N.

Global Instance Inhabited__vrelop_Jnn_N : Inhabited (vrelop_Jnn_N) := { default_val := vrelop_Jnn_N_EQ }.

Definition vrelop_Jnn_N_eq_dec : forall (v1 v2 : vrelop_Jnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vrelop_Jnn_N_eqb (v1 v2 : vrelop_Jnn_N) : bool :=
	is_left(vrelop_Jnn_N_eq_dec v1 v2).
Definition eqvrelop_Jnn_NP : Equality.axiom (vrelop_Jnn_N_eqb) :=
	eq_dec_Equality_axiom (vrelop_Jnn_N) (vrelop_Jnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vrelop_Jnn_N) (eqvrelop_Jnn_NP).
Hint Resolve vrelop_Jnn_N_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.8-354.16 *)
Inductive wf_vrelop_Jnn_N : Jnn -> res_N -> vrelop_Jnn_N -> Prop :=
	| vrelop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : res_N), wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N_EQ
	| vrelop_Jnn_N_case_1 : forall (v_Jnn : Jnn) (v_N : res_N), wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N_NE
	| vrelop_Jnn_N_case_2 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		(((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == res_S)) ->
		wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_LT v_sx)
	| vrelop_Jnn_N_case_3 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		(((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == res_S)) ->
		wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_GT v_sx)
	| vrelop_Jnn_N_case_4 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		(((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == res_S)) ->
		wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_LE v_sx)
	| vrelop_Jnn_N_case_5 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		(((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == res_S)) ->
		wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_GE v_sx).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
Inductive vrelop_Fnn_N : Type :=
	| vrelop_Fnn_N_EQ : vrelop_Fnn_N
	| vrelop_Fnn_N_NE : vrelop_Fnn_N
	| vrelop_Fnn_N_LT : vrelop_Fnn_N
	| vrelop_Fnn_N_GT : vrelop_Fnn_N
	| vrelop_Fnn_N_LE : vrelop_Fnn_N
	| vrelop_Fnn_N_GE : vrelop_Fnn_N.

Global Instance Inhabited__vrelop_Fnn_N : Inhabited (vrelop_Fnn_N) := { default_val := vrelop_Fnn_N_EQ }.

Definition vrelop_Fnn_N_eq_dec : forall (v1 v2 : vrelop_Fnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vrelop_Fnn_N_eqb (v1 v2 : vrelop_Fnn_N) : bool :=
	is_left(vrelop_Fnn_N_eq_dec v1 v2).
Definition eqvrelop_Fnn_NP : Equality.axiom (vrelop_Fnn_N_eqb) :=
	eq_dec_Equality_axiom (vrelop_Fnn_N) (vrelop_Fnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vrelop_Fnn_N) (eqvrelop_Fnn_NP).
Hint Resolve vrelop_Fnn_N_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
Inductive vrelop_ : Type :=
	| mk_vrelop__0 (v_Jnn : Jnn) (v_N : res_N) (var_x : vrelop_Jnn_N) : vrelop_
	| mk_vrelop__1 (v_Fnn : Fnn) (v_N : res_N) (var_x : vrelop_Fnn_N) : vrelop_.

Global Instance Inhabited__vrelop_ : Inhabited (vrelop_) := { default_val := mk_vrelop__0 default_val default_val default_val }.

Definition vrelop__eq_dec : forall (v1 v2 : vrelop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vrelop__eqb (v1 v2 : vrelop_) : bool :=
	is_left(vrelop__eq_dec v1 v2).
Definition eqvrelop_P : Equality.axiom (vrelop__eqb) :=
	eq_dec_Equality_axiom (vrelop_) (vrelop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (vrelop_) (eqvrelop_P).
Hint Resolve vrelop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.8-354.16 *)
Inductive wf_vrelop_ : shape -> vrelop_ -> Prop :=
	| vrelop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_N : res_N) (var_x : vrelop_Jnn_N), 
		(wf_vrelop_Jnn_N v_Jnn v_N var_x) ->
		(v_shape == (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		wf_vrelop_ v_shape (mk_vrelop__0 v_Jnn v_N var_x)
	| vrelop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_N : res_N) (var_x : vrelop_Fnn_N), 
		(v_shape == (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) ->
		wf_vrelop_ v_shape (mk_vrelop__1 v_Fnn v_N var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
Definition proj_vrelop__0 (var_x : vrelop_) : (option vrelop_Jnn_N) :=
	match var_x return (option vrelop_Jnn_N) with
		| (mk_vrelop__0 v_Jnn v_N var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
Definition proj_vrelop__1 (var_x : vrelop_) : (option vrelop_Fnn_N) :=
	match var_x return (option vrelop_Fnn_N) with
		| (mk_vrelop__1 v_Fnn v_N var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:362.1-362.48 *)
Inductive half : Type :=
	| LOW : half
	| HIGH : half.

Global Instance Inhabited__half : Inhabited (half) := { default_val := LOW }.

Definition half_eq_dec : forall (v1 v2 : half),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition half_eqb (v1 v2 : half) : bool :=
	is_left(half_eq_dec v1 v2).
Definition eqhalfP : Equality.axiom (half_eqb) :=
	eq_dec_Equality_axiom (half) (half_eq_dec).

HB.instance Definition _ := hasDecEq.Build (half) (eqhalfP).
Hint Resolve half_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:363.1-363.19 *)
Inductive zero : Type :=
	| ZERO : zero.

Global Instance Inhabited__zero : Inhabited (zero) := { default_val := ZERO }.

Definition zero_eq_dec : forall (v1 v2 : zero),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition zero_eqb (v1 v2 : zero) : bool :=
	is_left(zero_eq_dec v1 v2).
Definition eqzeroP : Equality.axiom (zero_eqb) :=
	eq_dec_Equality_axiom (zero) (zero_eq_dec).

HB.instance Definition _ := hasDecEq.Build (zero) (eqzeroP).
Hint Resolve zero_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:365.1-365.99 *)
Inductive vcvtop : Type :=
	| vcvtop_EXTEND (v_half : half) (v_sx : sx) : vcvtop
	| vcvtop_TRUNC_SAT (v_sx : sx) (zero_opt : (option zero)) : vcvtop
	| vcvtop_CONVERT (half_opt : (option half)) (v_sx : sx) : vcvtop
	| vcvtop_DEMOTE (v_zero : zero) : vcvtop
	| PROMOTELOW : vcvtop.

Global Instance Inhabited__vcvtop : Inhabited (vcvtop) := { default_val := vcvtop_EXTEND default_val default_val }.

Definition vcvtop_eq_dec : forall (v1 v2 : vcvtop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vcvtop_eqb (v1 v2 : vcvtop) : bool :=
	is_left(vcvtop_eq_dec v1 v2).
Definition eqvcvtopP : Equality.axiom (vcvtop_eqb) :=
	eq_dec_Equality_axiom (vcvtop) (vcvtop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vcvtop) (eqvcvtopP).
Hint Resolve vcvtop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 *)
Inductive vshiftop_Jnn_N : Type :=
	| vshiftop_Jnn_N_SHL : vshiftop_Jnn_N
	| vshiftop_Jnn_N_SHR (v_sx : sx) : vshiftop_Jnn_N.

Global Instance Inhabited__vshiftop_Jnn_N : Inhabited (vshiftop_Jnn_N) := { default_val := vshiftop_Jnn_N_SHL }.

Definition vshiftop_Jnn_N_eq_dec : forall (v1 v2 : vshiftop_Jnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vshiftop_Jnn_N_eqb (v1 v2 : vshiftop_Jnn_N) : bool :=
	is_left(vshiftop_Jnn_N_eq_dec v1 v2).
Definition eqvshiftop_Jnn_NP : Equality.axiom (vshiftop_Jnn_N_eqb) :=
	eq_dec_Equality_axiom (vshiftop_Jnn_N) (vshiftop_Jnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vshiftop_Jnn_N) (eqvshiftop_Jnn_NP).
Hint Resolve vshiftop_Jnn_N_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 *)
Inductive vshiftop_ : Type :=
	| mk_vshiftop__0 (v_Jnn : Jnn) (v_N : res_N) (var_x : vshiftop_Jnn_N) : vshiftop_.

Global Instance Inhabited__vshiftop_ : Inhabited (vshiftop_) := { default_val := mk_vshiftop__0 default_val default_val default_val }.

Definition vshiftop__eq_dec : forall (v1 v2 : vshiftop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vshiftop__eqb (v1 v2 : vshiftop_) : bool :=
	is_left(vshiftop__eq_dec v1 v2).
Definition eqvshiftop_P : Equality.axiom (vshiftop__eqb) :=
	eq_dec_Equality_axiom (vshiftop_) (vshiftop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (vshiftop_) (eqvshiftop_P).
Hint Resolve vshiftop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.8-367.18 *)
Inductive wf_vshiftop_ : ishape -> vshiftop_ -> Prop :=
	| vshiftop__case_0 : forall (v_ishape : ishape) (v_Jnn : Jnn) (v_N : res_N) (var_x : vshiftop_Jnn_N), 
		(v_ishape == (ishape_X v_Jnn (mk_dim v_N))) ->
		wf_vshiftop_ v_ishape (mk_vshiftop__0 v_Jnn v_N var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 *)
Definition proj_vshiftop__0 (var_x : vshiftop_) : vshiftop_Jnn_N :=
	match var_x return vshiftop_Jnn_N with
		| (mk_vshiftop__0 v_Jnn v_N var_x) => var_x
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 *)
Inductive vextunop_Jnn_N : Type :=
	| EXTADD_PAIRWISE (v_sx : sx) : vextunop_Jnn_N.

Global Instance Inhabited__vextunop_Jnn_N : Inhabited (vextunop_Jnn_N) := { default_val := EXTADD_PAIRWISE default_val }.

Definition vextunop_Jnn_N_eq_dec : forall (v1 v2 : vextunop_Jnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vextunop_Jnn_N_eqb (v1 v2 : vextunop_Jnn_N) : bool :=
	is_left(vextunop_Jnn_N_eq_dec v1 v2).
Definition eqvextunop_Jnn_NP : Equality.axiom (vextunop_Jnn_N_eqb) :=
	eq_dec_Equality_axiom (vextunop_Jnn_N) (vextunop_Jnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vextunop_Jnn_N) (eqvextunop_Jnn_NP).
Hint Resolve vextunop_Jnn_N_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.8-370.18 *)
Inductive wf_vextunop_Jnn_N : Jnn -> res_N -> vextunop_Jnn_N -> Prop :=
	| vextunop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		((16 <= (lsizenn (lanetype_Jnn v_Jnn)))%N && ((lsizenn (lanetype_Jnn v_Jnn)) <= 32)%N) ->
		wf_vextunop_Jnn_N v_Jnn v_N (EXTADD_PAIRWISE v_sx).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 *)
Inductive vextunop_ : Type :=
	| mk_vextunop__0 (v_Jnn : Jnn) (v_N : res_N) (var_x : vextunop_Jnn_N) : vextunop_.

Global Instance Inhabited__vextunop_ : Inhabited (vextunop_) := { default_val := mk_vextunop__0 default_val default_val default_val }.

Definition vextunop__eq_dec : forall (v1 v2 : vextunop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vextunop__eqb (v1 v2 : vextunop_) : bool :=
	is_left(vextunop__eq_dec v1 v2).
Definition eqvextunop_P : Equality.axiom (vextunop__eqb) :=
	eq_dec_Equality_axiom (vextunop_) (vextunop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (vextunop_) (eqvextunop_P).
Hint Resolve vextunop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.8-370.18 *)
Inductive wf_vextunop_ : ishape -> vextunop_ -> Prop :=
	| vextunop__case_0 : forall (v_ishape : ishape) (v_Jnn : Jnn) (v_N : res_N) (var_x : vextunop_Jnn_N), 
		(wf_vextunop_Jnn_N v_Jnn v_N var_x) ->
		(v_ishape == (ishape_X v_Jnn (mk_dim v_N))) ->
		wf_vextunop_ v_ishape (mk_vextunop__0 v_Jnn v_N var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 *)
Definition proj_vextunop__0 (var_x : vextunop_) : vextunop_Jnn_N :=
	match var_x return vextunop_Jnn_N with
		| (mk_vextunop__0 v_Jnn v_N var_x) => var_x
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 *)
Inductive vextbinop_Jnn_N : Type :=
	| EXTMUL (v_half : half) (v_sx : sx) : vextbinop_Jnn_N
	| DOTS : vextbinop_Jnn_N.

Global Instance Inhabited__vextbinop_Jnn_N : Inhabited (vextbinop_Jnn_N) := { default_val := EXTMUL default_val default_val }.

Definition vextbinop_Jnn_N_eq_dec : forall (v1 v2 : vextbinop_Jnn_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vextbinop_Jnn_N_eqb (v1 v2 : vextbinop_Jnn_N) : bool :=
	is_left(vextbinop_Jnn_N_eq_dec v1 v2).
Definition eqvextbinop_Jnn_NP : Equality.axiom (vextbinop_Jnn_N_eqb) :=
	eq_dec_Equality_axiom (vextbinop_Jnn_N) (vextbinop_Jnn_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vextbinop_Jnn_N) (eqvextbinop_Jnn_NP).
Hint Resolve vextbinop_Jnn_N_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.8-373.19 *)
Inductive wf_vextbinop_Jnn_N : Jnn -> res_N -> vextbinop_Jnn_N -> Prop :=
	| vextbinop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : res_N) (v_half : half) (v_sx : sx), wf_vextbinop_Jnn_N v_Jnn v_N (EXTMUL v_half v_sx)
	| vextbinop_Jnn_N_case_1 : forall (v_Jnn : Jnn) (v_N : res_N), 
		((lsizenn (lanetype_Jnn v_Jnn)) == 32) ->
		wf_vextbinop_Jnn_N v_Jnn v_N DOTS.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 *)
Inductive vextbinop_ : Type :=
	| mk_vextbinop__0 (v_Jnn : Jnn) (v_N : res_N) (var_x : vextbinop_Jnn_N) : vextbinop_.

Global Instance Inhabited__vextbinop_ : Inhabited (vextbinop_) := { default_val := mk_vextbinop__0 default_val default_val default_val }.

Definition vextbinop__eq_dec : forall (v1 v2 : vextbinop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vextbinop__eqb (v1 v2 : vextbinop_) : bool :=
	is_left(vextbinop__eq_dec v1 v2).
Definition eqvextbinop_P : Equality.axiom (vextbinop__eqb) :=
	eq_dec_Equality_axiom (vextbinop_) (vextbinop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (vextbinop_) (eqvextbinop_P).
Hint Resolve vextbinop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.8-373.19 *)
Inductive wf_vextbinop_ : ishape -> vextbinop_ -> Prop :=
	| vextbinop__case_0 : forall (v_ishape : ishape) (v_Jnn : Jnn) (v_N : res_N) (var_x : vextbinop_Jnn_N), 
		(wf_vextbinop_Jnn_N v_Jnn v_N var_x) ->
		(v_ishape == (ishape_X v_Jnn (mk_dim v_N))) ->
		wf_vextbinop_ v_ishape (mk_vextbinop__0 v_Jnn v_N var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 *)
Definition proj_vextbinop__0 (var_x : vextbinop_) : vextbinop_Jnn_N :=
	match var_x return vextbinop_Jnn_N with
		| (mk_vextbinop__0 v_Jnn v_N var_x) => var_x
	end.

(* Record Creation Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.1-381.69 *)
Record memarg := MKmemarg
{	ALIGN : u32
;	OFFSET : u32
}.

Global Instance Inhabited_memarg : Inhabited (memarg) := 
{default_val := {|
	ALIGN := default_val;
	OFFSET := default_val|} }.

Definition _append_memarg (arg1 arg2 : (memarg)) :=
{|
	ALIGN := arg1.(ALIGN); (* FIXME - Non-trivial append *)
	OFFSET := arg1.(OFFSET); (* FIXME - Non-trivial append *)
|}.

Global Instance Append_memarg : Append memarg := { _append arg1 arg2 := _append_memarg arg1 arg2 }.

#[export] Instance eta__memarg : Settable _ := settable! MKmemarg <ALIGN;OFFSET>.

Definition memarg_eq_dec : forall (v1 v2 : memarg),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memarg_eqb (v1 v2 : memarg) : bool :=
	is_left(memarg_eq_dec v1 v2).
Definition eqmemargP : Equality.axiom (memarg_eqb) :=
	eq_dec_Equality_axiom (memarg) (memarg_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memarg) (eqmemargP).
Hint Resolve memarg_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.8-381.14 *)
Inductive wf_memarg : memarg -> Prop :=
	| memarg_case_ : forall (var_0 : u32) (var_1 : u32), 
		(wf_uN 32 var_0) ->
		(wf_uN 32 var_1) ->
		wf_memarg {| ALIGN := var_0; OFFSET := var_1 |}.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 *)
Inductive loadop_Inn : Type :=
	| mk_loadop_Inn (v_sz : sz) (v_sx : sx) : loadop_Inn.

Global Instance Inhabited__loadop_Inn : Inhabited (loadop_Inn) := { default_val := mk_loadop_Inn default_val default_val }.

Definition loadop_Inn_eq_dec : forall (v1 v2 : loadop_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition loadop_Inn_eqb (v1 v2 : loadop_Inn) : bool :=
	is_left(loadop_Inn_eq_dec v1 v2).
Definition eqloadop_InnP : Equality.axiom (loadop_Inn_eqb) :=
	eq_dec_Equality_axiom (loadop_Inn) (loadop_Inn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (loadop_Inn) (eqloadop_InnP).
Hint Resolve loadop_Inn_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.8-385.16 *)
Inductive wf_loadop_Inn : Inn -> loadop_Inn -> Prop :=
	| loadop_Inn_case_0 : forall (v_Inn : Inn) (v_sz : sz) (v_sx : sx), 
		(wf_sz v_sz) ->
		((v_sz :> nat) < (sizenn (numtype_Inn v_Inn)))%N ->
		wf_loadop_Inn v_Inn (mk_loadop_Inn v_sz v_sx).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 *)
Inductive loadop_ : Type :=
	| mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_.

Global Instance Inhabited__loadop_ : Inhabited (loadop_) := { default_val := mk_loadop__0 default_val default_val }.

Definition loadop__eq_dec : forall (v1 v2 : loadop_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition loadop__eqb (v1 v2 : loadop_) : bool :=
	is_left(loadop__eq_dec v1 v2).
Definition eqloadop_P : Equality.axiom (loadop__eqb) :=
	eq_dec_Equality_axiom (loadop_) (loadop__eq_dec).

HB.instance Definition _ := hasDecEq.Build (loadop_) (eqloadop_P).
Hint Resolve loadop__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.8-385.16 *)
Inductive wf_loadop_ : numtype -> loadop_ -> Prop :=
	| loadop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : loadop_Inn), 
		(wf_loadop_Inn v_Inn var_x) ->
		(v_numtype == (numtype_Inn v_Inn)) ->
		wf_loadop_ v_numtype (mk_loadop__0 v_Inn var_x).

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 *)
Definition proj_loadop__0 (var_x : loadop_) : loadop_Inn :=
	match var_x return loadop_Inn with
		| (mk_loadop__0 v_Inn var_x) => var_x
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:388.1-391.46 *)
Inductive vloadop : Type :=
	| SHAPEX_ (_ : nat) (_ : nat) (v_sx : sx) : vloadop
	| SPLAT (_ : nat) : vloadop
	| vloadop_ZERO (_ : nat) : vloadop.

Global Instance Inhabited__vloadop : Inhabited (vloadop) := { default_val := SHAPEX_ default_val default_val default_val }.

Definition vloadop_eq_dec : forall (v1 v2 : vloadop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vloadop_eqb (v1 v2 : vloadop) : bool :=
	is_left(vloadop_eq_dec v1 v2).
Definition eqvloadopP : Equality.axiom (vloadop_eqb) :=
	eq_dec_Equality_axiom (vloadop) (vloadop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vloadop) (eqvloadopP).
Hint Resolve vloadop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:398.1-400.17 *)
Inductive blocktype : Type :=
	| _RESULT (valtype_opt : (option valtype)) : blocktype
	| _IDX (v_typeidx : typeidx) : blocktype.

Global Instance Inhabited__blocktype : Inhabited (blocktype) := { default_val := _RESULT default_val }.

Definition blocktype_eq_dec : forall (v1 v2 : blocktype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition blocktype_eqb (v1 v2 : blocktype) : bool :=
	is_left(blocktype_eq_dec v1 v2).
Definition eqblocktypeP : Equality.axiom (blocktype_eqb) :=
	eq_dec_Equality_axiom (blocktype) (blocktype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (blocktype) (eqblocktypeP).
Hint Resolve blocktype_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:398.8-398.17 *)
Inductive wf_blocktype : blocktype -> Prop :=
	| blocktype_case_0 : forall (valtype_opt : (option valtype)), wf_blocktype (_RESULT valtype_opt)
	| blocktype_case_1 : forall (v_typeidx : typeidx), 
		(wf_uN 32 v_typeidx) ->
		wf_blocktype (_IDX v_typeidx).

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
Inductive instr : Type :=
	| NOP : instr
	| UNREACHABLE : instr
	| DROP : instr
	| SELECT (valtype_lst_opt : (option (seq valtype))) : instr
	| BLOCK (v_blocktype : blocktype) (instr_lst : (seq instr)) : instr
	| LOOP (v_blocktype : blocktype) (instr_lst : (seq instr)) : instr
	| IFELSE (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst : (seq instr)) : instr
	| BR (v_labelidx : labelidx) : instr
	| BR_IF (v_labelidx : labelidx) : instr
	| BR_TABLE (labelidx_lst : (seq labelidx)) (v_labelidx : labelidx) : instr
	| CALL (v_funcidx : funcidx) : instr
	| CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : instr
	| RETURN : instr
	| CONST (v_numtype : numtype) (_ : num_) : instr
	| UNOP (v_numtype : numtype) (_ : unop_) : instr
	| BINOP (v_numtype : numtype) (_ : binop_) : instr
	| TESTOP (v_numtype : numtype) (_ : testop_) : instr
	| RELOP (v_numtype : numtype) (_ : relop_) : instr
	| CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop) : instr
	| instr_EXTEND (v_numtype : numtype) (v_n : n) : instr
	| VCONST (v_vectype : vectype) (_ : vec_) : instr
	| VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : instr
	| VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : instr
	| VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : instr
	| VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : instr
	| VUNOP (v_shape : shape) (_ : vunop_) : instr
	| VBINOP (v_shape : shape) (_ : vbinop_) : instr
	| VTESTOP (v_shape : shape) (_ : vtestop_) : instr
	| VRELOP (v_shape : shape) (_ : vrelop_) : instr
	| VSHIFTOP (v_ishape : ishape) (_ : vshiftop_) : instr
	| VBITMASK (v_ishape : ishape) : instr
	| VSWIZZLE (v_ishape : ishape) : instr
	| VSHUFFLE (v_ishape : ishape) (laneidx_lst : (seq laneidx)) : instr
	| VSPLAT (v_shape : shape) : instr
	| VEXTRACT_LANE (v_shape : shape) (sx_opt : (option sx)) (v_laneidx : laneidx) : instr
	| VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : instr
	| VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextunop_) : instr
	| VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextbinop_) : instr
	| VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : instr
	| VCVTOP (v_shape : shape) (v_shape : shape) (v_vcvtop : vcvtop) : instr
	| REF_NULL (v_reftype : reftype) : instr
	| REF_FUNC (v_funcidx : funcidx) : instr
	| REF_IS_NULL : instr
	| LOCAL_GET (v_localidx : localidx) : instr
	| LOCAL_SET (v_localidx : localidx) : instr
	| LOCAL_TEE (v_localidx : localidx) : instr
	| GLOBAL_GET (v_globalidx : globalidx) : instr
	| GLOBAL_SET (v_globalidx : globalidx) : instr
	| TABLE_GET (v_tableidx : tableidx) : instr
	| TABLE_SET (v_tableidx : tableidx) : instr
	| TABLE_SIZE (v_tableidx : tableidx) : instr
	| TABLE_GROW (v_tableidx : tableidx) : instr
	| TABLE_FILL (v_tableidx : tableidx) : instr
	| TABLE_COPY (v_tableidx : tableidx) (v_tableidx : tableidx) : instr
	| TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : instr
	| ELEM_DROP (v_elemidx : elemidx) : instr
	| LOAD (v_numtype : numtype) (_ : (option loadop_)) (v_memarg : memarg) : instr
	| STORE (v_numtype : numtype) (sz_opt : (option sz)) (v_memarg : memarg) : instr
	| VLOAD (v_vectype : vectype) (vloadop_opt : (option vloadop)) (v_memarg : memarg) : instr
	| VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : instr
	| VSTORE (v_vectype : vectype) (v_memarg : memarg) : instr
	| VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : instr
	| MEMORY_SIZE : instr
	| MEMORY_GROW : instr
	| MEMORY_FILL : instr
	| MEMORY_COPY : instr
	| MEMORY_INIT (v_dataidx : dataidx) : instr
	| DATA_DROP (v_dataidx : dataidx) : instr.

Global Instance Inhabited__instr : Inhabited (instr) := { default_val := NOP }.

Fixpoint instr_eq_dec (v1 v2 : instr) {struct v1} :
  {v1 = v2} + {v1 <> v2}.
Proof. decide equality; do ? decidable_equality_step. Defined.

Definition instr_eqb (v1 v2 : instr) : bool :=
	is_left(instr_eq_dec v1 v2).
Definition eqinstrP : Equality.axiom (instr_eqb) :=
	eq_dec_Equality_axiom (instr) (instr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (instr) (eqinstrP).
Hint Resolve instr_eq_dec : eq_dec_db.

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
Inductive wf_instr : instr -> Prop :=
	| instr_case_0 : wf_instr NOP
	| instr_case_1 : wf_instr UNREACHABLE
	| instr_case_2 : wf_instr DROP
	| instr_case_3 : forall (valtype_lst_opt : (option (seq valtype))), wf_instr (SELECT valtype_lst_opt)
	| instr_case_4 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)), 
		(wf_blocktype v_blocktype) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		wf_instr (BLOCK v_blocktype instr_lst)
	| instr_case_5 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)), 
		(wf_blocktype v_blocktype) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		wf_instr (LOOP v_blocktype instr_lst)
	| instr_case_6 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst_0_lst : (seq instr)), 
		(wf_blocktype v_blocktype) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		List.Forall (fun (instr_lst_0 : instr) => (wf_instr instr_lst_0)) instr_lst_0_lst ->
		wf_instr (IFELSE v_blocktype instr_lst instr_lst_0_lst)
	| instr_case_7 : forall (v_labelidx : labelidx), 
		(wf_uN 32 v_labelidx) ->
		wf_instr (BR v_labelidx)
	| instr_case_8 : forall (v_labelidx : labelidx), 
		(wf_uN 32 v_labelidx) ->
		wf_instr (BR_IF v_labelidx)
	| instr_case_9 : forall (labelidx_lst : (seq labelidx)) (v_labelidx : labelidx), 
		List.Forall (fun (v_labelidx : labelidx) => (wf_uN 32 v_labelidx)) labelidx_lst ->
		(wf_uN 32 v_labelidx) ->
		wf_instr (BR_TABLE labelidx_lst v_labelidx)
	| instr_case_10 : forall (v_funcidx : funcidx), 
		(wf_uN 32 v_funcidx) ->
		wf_instr (CALL v_funcidx)
	| instr_case_11 : forall (v_tableidx : tableidx) (v_typeidx : typeidx), 
		(wf_uN 32 v_tableidx) ->
		(wf_uN 32 v_typeidx) ->
		wf_instr (CALL_INDIRECT v_tableidx v_typeidx)
	| instr_case_12 : wf_instr RETURN
	| instr_case_13 : forall (v_numtype : numtype) (var_0 : num_), 
		(wf_num_ v_numtype var_0) ->
		wf_instr (CONST v_numtype var_0)
	| instr_case_14 : forall (v_numtype : numtype) (var_0 : unop_), 
		(wf_unop_ v_numtype var_0) ->
		wf_instr (UNOP v_numtype var_0)
	| instr_case_15 : forall (v_numtype : numtype) (var_0 : binop_), 
		(wf_binop_ v_numtype var_0) ->
		wf_instr (BINOP v_numtype var_0)
	| instr_case_16 : forall (v_numtype : numtype) (var_0 : testop_), 
		(wf_testop_ v_numtype var_0) ->
		wf_instr (TESTOP v_numtype var_0)
	| instr_case_17 : forall (v_numtype : numtype) (var_0 : relop_), 
		(wf_relop_ v_numtype var_0) ->
		wf_instr (RELOP v_numtype var_0)
	| instr_case_18 : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop), 
		(numtype_1 != numtype_2) ->
		wf_instr (CVTOP numtype_1 numtype_2 v_cvtop)
	| instr_case_19 : forall (v_numtype : numtype) (v_n : n), wf_instr (instr_EXTEND v_numtype v_n)
	| instr_case_20 : forall (v_vectype : vectype) (var_0 : vec_), 
		((res_size (valtype_vectype v_vectype)) != None) ->
		(wf_uN (!((res_size (valtype_vectype v_vectype)))) var_0) ->
		wf_instr (VCONST v_vectype var_0)
	| instr_case_21 : forall (v_vectype : vectype) (v_vvunop : vvunop), wf_instr (VVUNOP v_vectype v_vvunop)
	| instr_case_22 : forall (v_vectype : vectype) (v_vvbinop : vvbinop), wf_instr (VVBINOP v_vectype v_vvbinop)
	| instr_case_23 : forall (v_vectype : vectype) (v_vvternop : vvternop), wf_instr (VVTERNOP v_vectype v_vvternop)
	| instr_case_24 : forall (v_vectype : vectype) (v_vvtestop : vvtestop), wf_instr (VVTESTOP v_vectype v_vvtestop)
	| instr_case_25 : forall (v_shape : shape) (var_0 : vunop_), 
		(wf_shape v_shape) ->
		(wf_vunop_ v_shape var_0) ->
		wf_instr (VUNOP v_shape var_0)
	| instr_case_26 : forall (v_shape : shape) (var_0 : vbinop_), 
		(wf_shape v_shape) ->
		(wf_vbinop_ v_shape var_0) ->
		wf_instr (VBINOP v_shape var_0)
	| instr_case_27 : forall (v_shape : shape) (var_0 : vtestop_), 
		(wf_shape v_shape) ->
		(wf_vtestop_ v_shape var_0) ->
		wf_instr (VTESTOP v_shape var_0)
	| instr_case_28 : forall (v_shape : shape) (var_0 : vrelop_), 
		(wf_shape v_shape) ->
		(wf_vrelop_ v_shape var_0) ->
		wf_instr (VRELOP v_shape var_0)
	| instr_case_29 : forall (v_ishape : ishape) (var_0 : vshiftop_), 
		(wf_ishape v_ishape) ->
		(wf_vshiftop_ v_ishape var_0) ->
		wf_instr (VSHIFTOP v_ishape var_0)
	| instr_case_30 : forall (v_ishape : ishape), 
		(wf_ishape v_ishape) ->
		wf_instr (VBITMASK v_ishape)
	| instr_case_31 : forall (v_ishape : ishape), 
		(wf_ishape v_ishape) ->
		(v_ishape == (ishape_X Jnn_I8 (mk_dim 16))) ->
		wf_instr (VSWIZZLE v_ishape)
	| instr_case_32 : forall (v_ishape : ishape) (laneidx_lst : (seq laneidx)), 
		(wf_ishape v_ishape) ->
		List.Forall (fun (v_laneidx : laneidx) => (wf_uN 8 v_laneidx)) laneidx_lst ->
		((v_ishape == (ishape_X Jnn_I8 (mk_dim 16))) && ((|laneidx_lst|) == 16)) ->
		wf_instr (VSHUFFLE v_ishape laneidx_lst)
	| instr_case_33 : forall (v_shape : shape), 
		(wf_shape v_shape) ->
		wf_instr (VSPLAT v_shape)
	| instr_case_34 : forall (v_numtype : numtype) (v_shape : shape) (sx_opt : (option sx)) (v_laneidx : laneidx), 
		(wf_shape v_shape) ->
		(wf_uN 8 v_laneidx) ->
		(((fun_lanetype v_shape) == (lanetype_numtype v_numtype)) <-> (sx_opt == None)) ->
		wf_instr (VEXTRACT_LANE v_shape sx_opt v_laneidx)
	| instr_case_35 : forall (v_shape : shape) (v_laneidx : laneidx), 
		(wf_shape v_shape) ->
		(wf_uN 8 v_laneidx) ->
		wf_instr (VREPLACE_LANE v_shape v_laneidx)
	| instr_case_36 : forall (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextunop_), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(wf_vextunop_ ishape_1 var_0) ->
		((lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))%N) ->
		wf_instr (VEXTUNOP ishape_1 ishape_2 var_0)
	| instr_case_37 : forall (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextbinop_), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(wf_vextbinop_ ishape_1 var_0) ->
		((lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))%N) ->
		wf_instr (VEXTBINOP ishape_1 ishape_2 var_0)
	| instr_case_38 : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(((lsize (fun_lanetype (shape_ishape ishape_2))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))%N) && ((2 * (lsize (fun_lanetype (shape_ishape ishape_1))))%N <= 32)%N) ->
		wf_instr (VNARROW ishape_1 ishape_2 v_sx)
	| instr_case_39 : forall (v_shape : shape) (shape_0 : shape) (v_vcvtop : vcvtop), 
		(wf_shape v_shape) ->
		(wf_shape shape_0) ->
		wf_instr (VCVTOP v_shape shape_0 v_vcvtop)
	| instr_case_40 : forall (v_reftype : reftype), wf_instr (REF_NULL v_reftype)
	| instr_case_41 : forall (v_funcidx : funcidx), 
		(wf_uN 32 v_funcidx) ->
		wf_instr (REF_FUNC v_funcidx)
	| instr_case_42 : wf_instr REF_IS_NULL
	| instr_case_43 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_instr (LOCAL_GET v_localidx)
	| instr_case_44 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_instr (LOCAL_SET v_localidx)
	| instr_case_45 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_instr (LOCAL_TEE v_localidx)
	| instr_case_46 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_instr (GLOBAL_GET v_globalidx)
	| instr_case_47 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_instr (GLOBAL_SET v_globalidx)
	| instr_case_48 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_instr (TABLE_GET v_tableidx)
	| instr_case_49 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_instr (TABLE_SET v_tableidx)
	| instr_case_50 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_instr (TABLE_SIZE v_tableidx)
	| instr_case_51 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_instr (TABLE_GROW v_tableidx)
	| instr_case_52 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_instr (TABLE_FILL v_tableidx)
	| instr_case_53 : forall (v_tableidx : tableidx) (tableidx_0 : tableidx), 
		(wf_uN 32 v_tableidx) ->
		(wf_uN 32 tableidx_0) ->
		wf_instr (TABLE_COPY v_tableidx tableidx_0)
	| instr_case_54 : forall (v_tableidx : tableidx) (v_elemidx : elemidx), 
		(wf_uN 32 v_tableidx) ->
		(wf_uN 32 v_elemidx) ->
		wf_instr (TABLE_INIT v_tableidx v_elemidx)
	| instr_case_55 : forall (v_elemidx : elemidx), 
		(wf_uN 32 v_elemidx) ->
		wf_instr (ELEM_DROP v_elemidx)
	| instr_case_56 : forall (v_numtype : numtype) (var_0_opt : (option loadop_)) (v_memarg : memarg), 
		List.Forall (fun (var_0 : loadop_) => (wf_loadop_ v_numtype var_0)) (option_to_list var_0_opt) ->
		(wf_memarg v_memarg) ->
		wf_instr (LOAD v_numtype var_0_opt v_memarg)
	| instr_case_57 : forall (Inn_opt : (option Inn)) (numtype_opt : (option numtype)) (v_numtype : numtype) (sz_opt : (option sz)) (v_memarg : memarg), 
		List.Forall (fun (v_sz : sz) => (wf_sz v_sz)) (option_to_list sz_opt) ->
		(wf_memarg v_memarg) ->
		((Inn_opt == None) <-> (numtype_opt == None)) ->
		((Inn_opt == None) <-> (sz_opt == None)) ->
		List_Forall3 (fun (v_Inn : Inn) (v_numtype : numtype) (v_sz : sz) => ((v_numtype == (numtype_Inn v_Inn)) && ((v_sz :> nat) < (sizenn (numtype_Inn v_Inn)))%N)) (option_to_list Inn_opt) (option_to_list numtype_opt) (option_to_list sz_opt) ->
		wf_instr (STORE v_numtype sz_opt v_memarg)
	| instr_case_58 : forall (v_vectype : vectype) (vloadop_opt : (option vloadop)) (v_memarg : memarg), 
		(wf_memarg v_memarg) ->
		wf_instr (VLOAD v_vectype vloadop_opt v_memarg)
	| instr_case_59 : forall (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx), 
		(wf_sz v_sz) ->
		(wf_memarg v_memarg) ->
		(wf_uN 8 v_laneidx) ->
		wf_instr (VLOAD_LANE v_vectype v_sz v_memarg v_laneidx)
	| instr_case_60 : forall (v_vectype : vectype) (v_memarg : memarg), 
		(wf_memarg v_memarg) ->
		wf_instr (VSTORE v_vectype v_memarg)
	| instr_case_61 : forall (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx), 
		(wf_sz v_sz) ->
		(wf_memarg v_memarg) ->
		(wf_uN 8 v_laneidx) ->
		wf_instr (VSTORE_LANE v_vectype v_sz v_memarg v_laneidx)
	| instr_case_62 : wf_instr MEMORY_SIZE
	| instr_case_63 : wf_instr MEMORY_GROW
	| instr_case_64 : wf_instr MEMORY_FILL
	| instr_case_65 : wf_instr MEMORY_COPY
	| instr_case_66 : forall (v_dataidx : dataidx), 
		(wf_uN 32 v_dataidx) ->
		wf_instr (MEMORY_INIT v_dataidx)
	| instr_case_67 : forall (v_dataidx : dataidx), 
		(wf_uN 32 v_dataidx) ->
		wf_instr (DATA_DROP v_dataidx).

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:523.1-524.9 *)
Definition expr : Type := (seq instr).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:536.1-536.59 *)
Inductive elemmode : Type :=
	| ACTIVE (v_tableidx : tableidx) (v_expr : expr) : elemmode
	| PASSIVE : elemmode
	| DECLARE : elemmode.

Global Instance Inhabited__elemmode : Inhabited (elemmode) := { default_val := ACTIVE default_val default_val }.

Definition elemmode_eq_dec : forall (v1 v2 : elemmode),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elemmode_eqb (v1 v2 : elemmode) : bool :=
	is_left(elemmode_eq_dec v1 v2).
Definition eqelemmodeP : Equality.axiom (elemmode_eqb) :=
	eq_dec_Equality_axiom (elemmode) (elemmode_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elemmode) (eqelemmodeP).
Hint Resolve elemmode_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:536.8-536.16 *)
Inductive wf_elemmode : elemmode -> Prop :=
	| elemmode_case_0 : forall (v_tableidx : tableidx) (v_expr : expr), 
		(wf_uN 32 v_tableidx) ->
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		wf_elemmode (ACTIVE v_tableidx v_expr)
	| elemmode_case_1 : wf_elemmode PASSIVE
	| elemmode_case_2 : wf_elemmode DECLARE.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:537.1-537.47 *)
Inductive datamode : Type :=
	| datamode_ACTIVE (v_memidx : memidx) (v_expr : expr) : datamode
	| datamode_PASSIVE : datamode.

Global Instance Inhabited__datamode : Inhabited (datamode) := { default_val := datamode_ACTIVE default_val default_val }.

Definition datamode_eq_dec : forall (v1 v2 : datamode),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition datamode_eqb (v1 v2 : datamode) : bool :=
	is_left(datamode_eq_dec v1 v2).
Definition eqdatamodeP : Equality.axiom (datamode_eqb) :=
	eq_dec_Equality_axiom (datamode) (datamode_eq_dec).

HB.instance Definition _ := hasDecEq.Build (datamode) (eqdatamodeP).
Hint Resolve datamode_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:537.8-537.16 *)
Inductive wf_datamode : datamode -> Prop :=
	| datamode_case_0 : forall (v_memidx : memidx) (v_expr : expr), 
		(wf_uN 32 v_memidx) ->
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		wf_datamode (datamode_ACTIVE v_memidx v_expr)
	| datamode_case_1 : wf_datamode datamode_PASSIVE.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:539.1-540.16 *)
Inductive type : Type :=
	| TYPE (v_functype : functype) : type.

Global Instance Inhabited__type : Inhabited (type) := { default_val := TYPE default_val }.

Definition type_eq_dec : forall (v1 v2 : type),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition type_eqb (v1 v2 : type) : bool :=
	is_left(type_eq_dec v1 v2).
Definition eqtypeP : Equality.axiom (type_eqb) :=
	eq_dec_Equality_axiom (type) (type_eq_dec).

HB.instance Definition _ := hasDecEq.Build (type) (eqtypeP).
Hint Resolve type_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:541.1-542.16 *)
Inductive local : Type :=
	| LOCAL (v_valtype : valtype) : local.

Global Instance Inhabited__local : Inhabited (local) := { default_val := LOCAL default_val }.

Definition local_eq_dec : forall (v1 v2 : local),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition local_eqb (v1 v2 : local) : bool :=
	is_left(local_eq_dec v1 v2).
Definition eqlocalP : Equality.axiom (local_eqb) :=
	eq_dec_Equality_axiom (local) (local_eq_dec).

HB.instance Definition _ := hasDecEq.Build (local) (eqlocalP).
Hint Resolve local_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:543.1-544.27 *)
Inductive func : Type :=
	| func_FUNC (v_typeidx : typeidx) (local_lst : (seq local)) (v_expr : expr) : func.

Global Instance Inhabited__func : Inhabited (func) := { default_val := func_FUNC default_val default_val default_val }.

Definition func_eq_dec : forall (v1 v2 : func),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition func_eqb (v1 v2 : func) : bool :=
	is_left(func_eq_dec v1 v2).
Definition eqfuncP : Equality.axiom (func_eqb) :=
	eq_dec_Equality_axiom (func) (func_eq_dec).

HB.instance Definition _ := hasDecEq.Build (func) (eqfuncP).
Hint Resolve func_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:543.8-543.12 *)
Inductive wf_func : func -> Prop :=
	| func_case_0 : forall (v_typeidx : typeidx) (local_lst : (seq local)) (v_expr : expr), 
		(wf_uN 32 v_typeidx) ->
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		wf_func (func_FUNC v_typeidx local_lst v_expr).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:545.1-546.25 *)
Inductive global : Type :=
	| global_GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global.

Global Instance Inhabited__global : Inhabited (global) := { default_val := global_GLOBAL default_val default_val }.

Definition global_eq_dec : forall (v1 v2 : global),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition global_eqb (v1 v2 : global) : bool :=
	is_left(global_eq_dec v1 v2).
Definition eqglobalP : Equality.axiom (global_eqb) :=
	eq_dec_Equality_axiom (global) (global_eq_dec).

HB.instance Definition _ := hasDecEq.Build (global) (eqglobalP).
Hint Resolve global_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:545.8-545.14 *)
Inductive wf_global : global -> Prop :=
	| global_case_0 : forall (v_globaltype : globaltype) (v_expr : expr), 
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		wf_global (global_GLOBAL v_globaltype v_expr).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:547.1-548.18 *)
Inductive table : Type :=
	| table_TABLE (v_tabletype : tabletype) : table.

Global Instance Inhabited__table : Inhabited (table) := { default_val := table_TABLE default_val }.

Definition table_eq_dec : forall (v1 v2 : table),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition table_eqb (v1 v2 : table) : bool :=
	is_left(table_eq_dec v1 v2).
Definition eqtableP : Equality.axiom (table_eqb) :=
	eq_dec_Equality_axiom (table) (table_eq_dec).

HB.instance Definition _ := hasDecEq.Build (table) (eqtableP).
Hint Resolve table_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:547.8-547.13 *)
Inductive wf_table : table -> Prop :=
	| table_case_0 : forall (v_tabletype : tabletype), 
		(wf_tabletype v_tabletype) ->
		wf_table (table_TABLE v_tabletype).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:549.1-550.17 *)
Inductive mem : Type :=
	| MEMORY (v_memtype : memtype) : mem.

Global Instance Inhabited__mem : Inhabited (mem) := { default_val := MEMORY default_val }.

Definition mem_eq_dec : forall (v1 v2 : mem),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition mem_eqb (v1 v2 : mem) : bool :=
	is_left(mem_eq_dec v1 v2).
Definition eqmemP : Equality.axiom (mem_eqb) :=
	eq_dec_Equality_axiom (mem) (mem_eq_dec).

HB.instance Definition _ := hasDecEq.Build (mem) (eqmemP).
Hint Resolve mem_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:549.8-549.11 *)
Inductive wf_mem : mem -> Prop :=
	| mem_case_0 : forall (v_memtype : memtype), 
		(wf_memtype v_memtype) ->
		wf_mem (MEMORY v_memtype).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.1-552.30 *)
Inductive elem : Type :=
	| ELEM (v_reftype : reftype) (expr_lst : (seq expr)) (v_elemmode : elemmode) : elem.

Global Instance Inhabited__elem : Inhabited (elem) := { default_val := ELEM default_val default_val default_val }.

Definition elem_eq_dec : forall (v1 v2 : elem),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elem_eqb (v1 v2 : elem) : bool :=
	is_left(elem_eq_dec v1 v2).
Definition eqelemP : Equality.axiom (elem_eqb) :=
	eq_dec_Equality_axiom (elem) (elem_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elem) (eqelemP).
Hint Resolve elem_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.8-551.12 *)
Inductive wf_elem : elem -> Prop :=
	| elem_case_0 : forall (v_reftype : reftype) (expr_lst : (seq expr)) (v_elemmode : elemmode), 
		List.Forall (fun (v_expr : expr) => List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr) expr_lst ->
		(wf_elemmode v_elemmode) ->
		wf_elem (ELEM v_reftype expr_lst v_elemmode).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:553.1-554.22 *)
Inductive data : Type :=
	| DATA (byte_lst : (seq byte)) (v_datamode : datamode) : data.

Global Instance Inhabited__data : Inhabited (data) := { default_val := DATA default_val default_val }.

Definition data_eq_dec : forall (v1 v2 : data),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition data_eqb (v1 v2 : data) : bool :=
	is_left(data_eq_dec v1 v2).
Definition eqdataP : Equality.axiom (data_eqb) :=
	eq_dec_Equality_axiom (data) (data_eq_dec).

HB.instance Definition _ := hasDecEq.Build (data) (eqdataP).
Hint Resolve data_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:553.8-553.12 *)
Inductive wf_data : data -> Prop :=
	| data_case_0 : forall (byte_lst : (seq byte)) (v_datamode : datamode), 
		List.Forall (fun (v_byte : byte) => (wf_byte v_byte)) byte_lst ->
		(wf_datamode v_datamode) ->
		wf_data (DATA byte_lst v_datamode).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:555.1-556.16 *)
Inductive start : Type :=
	| START (v_funcidx : funcidx) : start.

Global Instance Inhabited__start : Inhabited (start) := { default_val := START default_val }.

Definition start_eq_dec : forall (v1 v2 : start),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition start_eqb (v1 v2 : start) : bool :=
	is_left(start_eq_dec v1 v2).
Definition eqstartP : Equality.axiom (start_eqb) :=
	eq_dec_Equality_axiom (start) (start_eq_dec).

HB.instance Definition _ := hasDecEq.Build (start) (eqstartP).
Hint Resolve start_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:555.8-555.13 *)
Inductive wf_start : start -> Prop :=
	| start_case_0 : forall (v_funcidx : funcidx), 
		(wf_uN 32 v_funcidx) ->
		wf_start (START v_funcidx).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.1-559.66 *)
Inductive externidx : Type :=
	| externidx_FUNC (v_funcidx : funcidx) : externidx
	| externidx_GLOBAL (v_globalidx : globalidx) : externidx
	| externidx_TABLE (v_tableidx : tableidx) : externidx
	| externidx_MEM (v_memidx : memidx) : externidx.

Global Instance Inhabited__externidx : Inhabited (externidx) := { default_val := externidx_FUNC default_val }.

Definition externidx_eq_dec : forall (v1 v2 : externidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition externidx_eqb (v1 v2 : externidx) : bool :=
	is_left(externidx_eq_dec v1 v2).
Definition eqexternidxP : Equality.axiom (externidx_eqb) :=
	eq_dec_Equality_axiom (externidx) (externidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (externidx) (eqexternidxP).
Hint Resolve externidx_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.8-558.17 *)
Inductive wf_externidx : externidx -> Prop :=
	| externidx_case_0 : forall (v_funcidx : funcidx), 
		(wf_uN 32 v_funcidx) ->
		wf_externidx (externidx_FUNC v_funcidx)
	| externidx_case_1 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_externidx (externidx_GLOBAL v_globalidx)
	| externidx_case_2 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_externidx (externidx_TABLE v_tableidx)
	| externidx_case_3 : forall (v_memidx : memidx), 
		(wf_uN 32 v_memidx) ->
		wf_externidx (externidx_MEM v_memidx).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.1-561.24 *)
Inductive export : Type :=
	| EXPORT (v_name : name) (v_externidx : externidx) : export.

Global Instance Inhabited__export : Inhabited (export) := { default_val := EXPORT default_val default_val }.

Definition export_eq_dec : forall (v1 v2 : export),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition export_eqb (v1 v2 : export) : bool :=
	is_left(export_eq_dec v1 v2).
Definition eqexportP : Equality.axiom (export_eqb) :=
	eq_dec_Equality_axiom (export) (export_eq_dec).

HB.instance Definition _ := hasDecEq.Build (export) (eqexportP).
Hint Resolve export_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.8-560.14 *)
Inductive wf_export : export -> Prop :=
	| export_case_0 : forall (v_name : name) (v_externidx : externidx), 
		(wf_name v_name) ->
		(wf_externidx v_externidx) ->
		wf_export (EXPORT v_name v_externidx).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:562.1-563.30 *)
Inductive import : Type :=
	| IMPORT (v_name : name) (v_name : name) (v_externtype : externtype) : import.

Global Instance Inhabited__import : Inhabited (import) := { default_val := IMPORT default_val default_val default_val }.

Definition import_eq_dec : forall (v1 v2 : import),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition import_eqb (v1 v2 : import) : bool :=
	is_left(import_eq_dec v1 v2).
Definition eqimportP : Equality.axiom (import_eqb) :=
	eq_dec_Equality_axiom (import) (import_eq_dec).

HB.instance Definition _ := hasDecEq.Build (import) (eqimportP).
Hint Resolve import_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:562.8-562.14 *)
Inductive wf_import : import -> Prop :=
	| import_case_0 : forall (v_name : name) (name_0 : name) (v_externtype : externtype), 
		(wf_name v_name) ->
		(wf_name name_0) ->
		(wf_externtype v_externtype) ->
		wf_import (IMPORT v_name name_0 v_externtype).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.1-566.76 *)
Inductive module : Type :=
	| MODULE (type_lst : (seq type)) (import_lst : (seq import)) (func_lst : (seq func)) (global_lst : (seq global)) (table_lst : (seq table)) (mem_lst : (seq mem)) (elem_lst : (seq elem)) (data_lst : (seq data)) (start_opt : (option start)) (export_lst : (seq export)) : module.

Global Instance Inhabited__module : Inhabited (module) := { default_val := MODULE default_val default_val default_val default_val default_val default_val default_val default_val default_val default_val }.

Definition module_eq_dec : forall (v1 v2 : module),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition module_eqb (v1 v2 : module) : bool :=
	is_left(module_eq_dec v1 v2).
Definition eqmoduleP : Equality.axiom (module_eqb) :=
	eq_dec_Equality_axiom (module) (module_eq_dec).

HB.instance Definition _ := hasDecEq.Build (module) (eqmoduleP).
Hint Resolve module_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.8-565.14 *)
Inductive wf_module : module -> Prop :=
	| module_case_0 : forall (type_lst : (seq type)) (import_lst : (seq import)) (func_lst : (seq func)) (global_lst : (seq global)) (table_lst : (seq table)) (mem_lst : (seq mem)) (elem_lst : (seq elem)) (data_lst : (seq data)) (start_opt : (option start)) (export_lst : (seq export)), 
		List.Forall (fun (v_import : import) => (wf_import v_import)) import_lst ->
		List.Forall (fun (v_func : func) => (wf_func v_func)) func_lst ->
		List.Forall (fun (v_global : global) => (wf_global v_global)) global_lst ->
		List.Forall (fun (v_table : table) => (wf_table v_table)) table_lst ->
		List.Forall (fun (v_mem : mem) => (wf_mem v_mem)) mem_lst ->
		List.Forall (fun (v_elem : elem) => (wf_elem v_elem)) elem_lst ->
		List.Forall (fun (v_data : data) => (wf_data v_data)) data_lst ->
		List.Forall (fun (v_start : start) => (wf_start v_start)) (option_to_list start_opt) ->
		List.Forall (fun (v_export : export) => (wf_export v_export)) export_lst ->
		wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst).

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
Inductive fun_concat_bytes : (seq (seq byte)) -> (seq byte) -> Prop :=
	| fun_concat_bytes_case_0 : fun_concat_bytes [:: ] [:: ]
	| fun_concat_bytes_case_1 : forall (b_lst : (seq byte)) (b'_lst_lst : (seq (seq byte))) (var_0 : (seq byte)), 
		(fun_concat_bytes b'_lst_lst var_0) ->
		fun_concat_bytes ([::b_lst] ++ b'_lst_lst) (b_lst ++ var_0).

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
Lemma concat_bytes_is_wf : forall (var_0_lst_lst : (seq (seq byte))) (ret_val_lst : (seq byte)) (var_0 : (seq byte)),
	(fun_concat_bytes var_0_lst_lst var_0) ->
	List.Forall (fun (var_0_lst : (seq byte)) => List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst) var_0_lst_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:28.1-28.32 *)
Definition unpack (v_lanetype : lanetype) : numtype :=
	match v_lanetype return numtype with
		| lanetype_I32 => I32
		| lanetype_I64 => I64
		| lanetype_F32 => F32
		| lanetype_F64 => F64
		| lanetype_I8 => I32
		| lanetype_I16 => I32
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:44.1-44.54 *)
Definition shunpack (v_shape : shape) : numtype :=
	match v_shape return numtype with
		| (X v_Lnn (mk_dim v_N)) => (unpack v_Lnn)
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64 *)
Inductive fun_funcsxt : (seq externtype) -> (seq functype) -> Prop :=
	| fun_funcsxt_case_0 : fun_funcsxt [:: ] [:: ]
	| fun_funcsxt_case_1 : forall (ft : functype) (xt_lst : (seq externtype)) (var_0 : (seq functype)), 
		(fun_funcsxt xt_lst var_0) ->
		fun_funcsxt ([::(FUNC ft)] ++ xt_lst) ([::ft] ++ var_0)
	| fun_funcsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq functype)), 
		(fun_funcsxt xt_lst var_0) ->
		fun_funcsxt ([::v_externtype] ++ xt_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66 *)
Inductive fun_globalsxt : (seq externtype) -> (seq globaltype) -> Prop :=
	| fun_globalsxt_case_0 : fun_globalsxt [:: ] [:: ]
	| fun_globalsxt_case_1 : forall (gt : globaltype) (xt_lst : (seq externtype)) (var_0 : (seq globaltype)), 
		(fun_globalsxt xt_lst var_0) ->
		fun_globalsxt ([::(GLOBAL gt)] ++ xt_lst) ([::gt] ++ var_0)
	| fun_globalsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq globaltype)), 
		(fun_globalsxt xt_lst var_0) ->
		fun_globalsxt ([::v_externtype] ++ xt_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
Inductive fun_tablesxt : (seq externtype) -> (seq tabletype) -> Prop :=
	| fun_tablesxt_case_0 : fun_tablesxt [:: ] [:: ]
	| fun_tablesxt_case_1 : forall (res_tt : tabletype) (xt_lst : (seq externtype)) (var_0 : (seq tabletype)), 
		(fun_tablesxt xt_lst var_0) ->
		fun_tablesxt ([::(TABLE res_tt)] ++ xt_lst) ([::res_tt] ++ var_0)
	| fun_tablesxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq tabletype)), 
		(fun_tablesxt xt_lst var_0) ->
		fun_tablesxt ([::v_externtype] ++ xt_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
Lemma tablesxt_is_wf : forall (var_0_lst : (seq externtype)) (ret_val_lst : (seq tabletype)) (var_0 : (seq tabletype)),
	(fun_tablesxt var_0_lst var_0) ->
	List.Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : tabletype) => (wf_tabletype ret_val)) ret_val_lst.
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
Inductive fun_memsxt : (seq externtype) -> (seq memtype) -> Prop :=
	| fun_memsxt_case_0 : fun_memsxt [:: ] [:: ]
	| fun_memsxt_case_1 : forall (mt : memtype) (xt_lst : (seq externtype)) (var_0 : (seq memtype)), 
		(fun_memsxt xt_lst var_0) ->
		fun_memsxt ([::(MEM mt)] ++ xt_lst) ([::mt] ++ var_0)
	| fun_memsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq memtype)), 
		(fun_memsxt xt_lst var_0) ->
		fun_memsxt ([::v_externtype] ++ xt_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
Lemma memsxt_is_wf : forall (var_0_lst : (seq externtype)) (ret_val_lst : (seq memtype)) (var_0 : (seq memtype)),
	(fun_memsxt var_0_lst var_0) ->
	List.Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : memtype) => (wf_memtype ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61 *)
Definition dataidx_instr (v_instr : instr) : (seq dataidx) :=
	match v_instr return (seq dataidx) with
		| (MEMORY_INIT x) => [::x]
		| (DATA_DROP x) => [::x]
		| res_in => [:: ]
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.6-80.20 *)
Lemma dataidx_instr_is_wf : forall (v_instr : instr) (ret_val_lst : (seq dataidx)),
	(wf_instr v_instr) ->
	(ret_val_lst == (dataidx_instr v_instr)) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32 ret_val)) ret_val_lst.
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
Inductive fun_dataidx_instrs : (seq instr) -> (seq dataidx) -> Prop :=
	| fun_dataidx_instrs_case_0 : fun_dataidx_instrs [:: ] [:: ]
	| fun_dataidx_instrs_case_1 : forall (v_instr : instr) (instr'_lst : (seq instr)) (var_0 : (seq dataidx)), 
		(fun_dataidx_instrs instr'_lst var_0) ->
		fun_dataidx_instrs ([::v_instr] ++ instr'_lst) ((dataidx_instr v_instr) ++ var_0).

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
Lemma dataidx_instrs_is_wf : forall (var_0_lst : (seq instr)) (ret_val_lst : (seq dataidx)) (var_0 : (seq dataidx)),
	(fun_dataidx_instrs var_0_lst var_0) ->
	List.Forall (fun (var_0 : instr) => (wf_instr var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32 ret_val)) ret_val_lst.
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
Inductive fun_dataidx_expr : expr -> (seq dataidx) -> Prop :=
	| fun_dataidx_expr_case_0 : forall (in_lst : (seq instr)) (var_0 : (seq dataidx)), 
		(fun_dataidx_instrs in_lst var_0) ->
		fun_dataidx_expr in_lst var_0.

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
Lemma dataidx_expr_is_wf : forall (v_expr : expr) (ret_val_lst : (seq dataidx)) (var_0 : (seq dataidx)),
	(fun_dataidx_expr v_expr var_0) ->
	List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32 ret_val)) ret_val_lst.
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
Inductive fun_dataidx_func : func -> (seq dataidx) -> Prop :=
	| fun_dataidx_func_case_0 : forall (x : uN) (loc_lst : (seq local)) (e : (seq instr)) (var_0 : (seq dataidx)), 
		(fun_dataidx_expr e var_0) ->
		fun_dataidx_func (func_FUNC x loc_lst e) var_0.

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
Lemma dataidx_func_is_wf : forall (v_func : func) (ret_val_lst : (seq dataidx)) (var_0 : (seq dataidx)),
	(fun_dataidx_func v_func var_0) ->
	(wf_func v_func) ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32 ret_val)) ret_val_lst.
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
Inductive fun_dataidx_funcs : (seq func) -> (seq dataidx) -> Prop :=
	| fun_dataidx_funcs_case_0 : fun_dataidx_funcs [:: ] [:: ]
	| fun_dataidx_funcs_case_1 : forall (v_func : func) (func'_lst : (seq func)) (var_1 : (seq dataidx)) (var_0 : (seq dataidx)), 
		(fun_dataidx_funcs func'_lst var_1) ->
		(fun_dataidx_func v_func var_0) ->
		fun_dataidx_funcs ([::v_func] ++ func'_lst) (var_0 ++ var_1).

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
Lemma dataidx_funcs_is_wf : forall (var_0_lst : (seq func)) (ret_val_lst : (seq dataidx)) (var_0 : (seq dataidx)),
	(fun_dataidx_funcs var_0_lst var_0) ->
	List.Forall (fun (var_0 : func) => (wf_func var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32 ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35 *)
Definition memarg0 : memarg := {| ALIGN := (mk_uN 0); OFFSET := (mk_uN 0) |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.6-106.13 *)
Lemma memarg0_is_wf : forall (ret_val : memarg),
	(ret_val == (memarg0 )) ->
	(wf_memarg ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41 *)
Axiom s33_to_u32 : forall (v_s33 : s33), u32.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.6-7.17 *)
Lemma s33_to_u32_is_wf : forall (v_s33 : s33) (ret_val : u32),
	(wf_sN 33 v_s33) ->
	(ret_val == (s33_to_u32 v_s33)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22 *)
Definition res_bool (v_bool : bool) : nat :=
	match v_bool return nat with
		| false => 0
		| true => 1
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23 *)
Axiom truncz : forall (res_rat : rat), int.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:20.6-20.14 *)
Inductive fun_signed_ : res_N -> nat -> int -> Prop :=
	| fun_signed__case_0 : forall (v_N : nat) (i : nat), 
		(i < (2 ^ (((v_N : int) - (1 : int))%Z : nat))%N)%N ->
		fun_signed_ v_N i (i : int)
	| fun_signed__case_1 : forall (v_N : nat) (i : nat), 
		(((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N <= i)%N && (i < (2 ^ v_N)%N)%N) ->
		fun_signed_ v_N i ((i : int) - ((2 ^ v_N)%N : int))%Z.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:24.6-24.18 *)
Inductive fun_inv_signed_ : res_N -> int -> nat -> Prop :=
	| fun_inv_signed__case_0 : forall (v_N : nat) (i : int), 
		(((0 : int) <= i)%Z && (i < ((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : int))%Z) ->
		fun_inv_signed_ v_N i (i : nat)
	| fun_inv_signed__case_1 : forall (v_N : nat) (i : int), 
		(((0 - ((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : int))%Z <= i)%Z && (i < (0 : int))%Z) ->
		fun_inv_signed_ v_N i ((i + ((2 ^ v_N)%N : int))%Z : nat).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61 *)
Definition sat_u_ (v_N : res_N) (res_int : int) : nat :=
	match v_N, res_int return nat with
		| v_N, i => (if (i < (0 : int))%Z then 0 else (if (i > (((2 ^ v_N)%N : int) - (1 : int))%Z)%Z then ((((2 ^ v_N)%N : int) - (1 : int))%Z : nat) else (i : nat)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61 *)
Definition sat_s_ (v_N : res_N) (res_int : int) : int :=
	match v_N, res_int return int with
		| v_N, i => (if (i < (0 - ((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : int))%Z)%Z then (0 - ((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : int))%Z else (if (i > (((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : int) - (1 : int))%Z)%Z then (((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : int) - (1 : int))%Z else i))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89 *)
Axiom extend__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.6-56.15 *)
Lemma extend___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN) (ret_val : iN),
	(wf_uN v_M v_iN) ->
	(ret_val == (extend__ v_M v_N v_sx v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30 *)
Axiom fabs_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.6-224.12 *)
Lemma fabs__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fabs_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31 *)
Axiom fceil_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.6-227.13 *)
Lemma fceil__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fceil_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32 *)
Axiom ffloor_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.6-228.14 *)
Lemma ffloor__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (ffloor_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34 *)
Axiom fnearest_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.6-230.16 *)
Lemma fnearest__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fnearest_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30 *)
Axiom fneg_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.6-225.12 *)
Lemma fneg__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fneg_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31 *)
Axiom fsqrt_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.6-226.13 *)
Lemma fsqrt__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fsqrt_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32 *)
Axiom ftrunc_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.6-229.14 *)
Lemma ftrunc__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (ftrunc_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29 *)
Axiom iclz_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.6-120.12 *)
Lemma iclz__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (iclz_ v_N v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29 *)
Axiom ictz_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.6-121.12 *)
Lemma ictz__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (ictz_ v_N v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32 *)
Axiom ipopcnt_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.6-122.15 *)
Lemma ipopcnt__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (ipopcnt_ v_N v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33 *)
Axiom wrap__ : forall (v_M : M) (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.6-55.13 *)
Lemma wrap___is_wf : forall (v_M : M) (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_M v_iN) ->
	(ret_val == (wrap__ v_M v_N v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
Definition fun_unop_ (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) : (seq num_) :=
	match v_numtype, v_unop_, v_num_ return (seq num_) with
		| I32, (mk_unop__0 Inn_I32 CLZ), (mk_num__0 Inn_I32 v_iN) => [::(mk_num__0 Inn_I32 (iclz_ (sizenn (numtype_Inn Inn_I32)) v_iN))]
		| I64, (mk_unop__0 Inn_I64 CLZ), (mk_num__0 Inn_I64 v_iN) => [::(mk_num__0 Inn_I64 (iclz_ (sizenn (numtype_Inn Inn_I64)) v_iN))]
		| I32, (mk_unop__0 Inn_I32 CTZ), (mk_num__0 Inn_I32 v_iN) => [::(mk_num__0 Inn_I32 (ictz_ (sizenn (numtype_Inn Inn_I32)) v_iN))]
		| I64, (mk_unop__0 Inn_I64 CTZ), (mk_num__0 Inn_I64 v_iN) => [::(mk_num__0 Inn_I64 (ictz_ (sizenn (numtype_Inn Inn_I64)) v_iN))]
		| I32, (mk_unop__0 Inn_I32 POPCNT), (mk_num__0 Inn_I32 v_iN) => [::(mk_num__0 Inn_I32 (ipopcnt_ (sizenn (numtype_Inn Inn_I32)) v_iN))]
		| I64, (mk_unop__0 Inn_I64 POPCNT), (mk_num__0 Inn_I64 v_iN) => [::(mk_num__0 Inn_I64 (ipopcnt_ (sizenn (numtype_Inn Inn_I64)) v_iN))]
		| I32, (mk_unop__0 Inn_I32 (EXTEND v_M)), (mk_num__0 Inn_I32 v_iN) => [::(mk_num__0 Inn_I32 (extend__ v_M (sizenn (numtype_Inn Inn_I32)) res_S (wrap__ (sizenn (numtype_Inn Inn_I32)) v_M v_iN)))]
		| I64, (mk_unop__0 Inn_I64 (EXTEND v_M)), (mk_num__0 Inn_I64 v_iN) => [::(mk_num__0 Inn_I64 (extend__ v_M (sizenn (numtype_Inn Inn_I64)) res_S (wrap__ (sizenn (numtype_Inn Inn_I64)) v_M v_iN)))]
		| F32, (mk_unop__1 Fnn_F32 ABS), (mk_num__1 Fnn_F32 v_fN) => (seq.map (fun (iter_0_1 : fN) => (mk_num__1 Fnn_F32 iter_0_1)) (fabs_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
		| F64, (mk_unop__1 Fnn_F64 ABS), (mk_num__1 Fnn_F64 v_fN) => (seq.map (fun (iter_0_2 : fN) => (mk_num__1 Fnn_F64 iter_0_2)) (fabs_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
		| F32, (mk_unop__1 Fnn_F32 unop_Fnn_NEG), (mk_num__1 Fnn_F32 v_fN) => (seq.map (fun (iter_0_3 : fN) => (mk_num__1 Fnn_F32 iter_0_3)) (fneg_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
		| F64, (mk_unop__1 Fnn_F64 unop_Fnn_NEG), (mk_num__1 Fnn_F64 v_fN) => (seq.map (fun (iter_0_4 : fN) => (mk_num__1 Fnn_F64 iter_0_4)) (fneg_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
		| F32, (mk_unop__1 Fnn_F32 SQRT), (mk_num__1 Fnn_F32 v_fN) => (seq.map (fun (iter_0_5 : fN) => (mk_num__1 Fnn_F32 iter_0_5)) (fsqrt_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
		| F64, (mk_unop__1 Fnn_F64 SQRT), (mk_num__1 Fnn_F64 v_fN) => (seq.map (fun (iter_0_6 : fN) => (mk_num__1 Fnn_F64 iter_0_6)) (fsqrt_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
		| F32, (mk_unop__1 Fnn_F32 CEIL), (mk_num__1 Fnn_F32 v_fN) => (seq.map (fun (iter_0_7 : fN) => (mk_num__1 Fnn_F32 iter_0_7)) (fceil_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
		| F64, (mk_unop__1 Fnn_F64 CEIL), (mk_num__1 Fnn_F64 v_fN) => (seq.map (fun (iter_0_8 : fN) => (mk_num__1 Fnn_F64 iter_0_8)) (fceil_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
		| F32, (mk_unop__1 Fnn_F32 FLOOR), (mk_num__1 Fnn_F32 v_fN) => (seq.map (fun (iter_0_9 : fN) => (mk_num__1 Fnn_F32 iter_0_9)) (ffloor_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
		| F64, (mk_unop__1 Fnn_F64 FLOOR), (mk_num__1 Fnn_F64 v_fN) => (seq.map (fun (iter_0_10 : fN) => (mk_num__1 Fnn_F64 iter_0_10)) (ffloor_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
		| F32, (mk_unop__1 Fnn_F32 TRUNC), (mk_num__1 Fnn_F32 v_fN) => (seq.map (fun (iter_0_11 : fN) => (mk_num__1 Fnn_F32 iter_0_11)) (ftrunc_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
		| F64, (mk_unop__1 Fnn_F64 TRUNC), (mk_num__1 Fnn_F64 v_fN) => (seq.map (fun (iter_0_12 : fN) => (mk_num__1 Fnn_F64 iter_0_12)) (ftrunc_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
		| F32, (mk_unop__1 Fnn_F32 NEAREST), (mk_num__1 Fnn_F32 v_fN) => (seq.map (fun (iter_0_13 : fN) => (mk_num__1 Fnn_F32 iter_0_13)) (fnearest_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
		| F64, (mk_unop__1 Fnn_F64 NEAREST), (mk_num__1 Fnn_F64 v_fN) => (seq.map (fun (iter_0_14 : fN) => (mk_num__1 Fnn_F64 iter_0_14)) (fnearest_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
		| _, _, _ => default_val
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 *)
Lemma unop__is_wf : forall (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) (ret_val_lst : (seq num_)),
	(wf_unop_ v_numtype v_unop_) ->
	(wf_num_ v_numtype v_num_) ->
	(ret_val_lst == (fun_unop_ v_numtype v_unop_ v_num_)) ->
	List.Forall (fun (ret_val : num_) => (wf_num_ v_numtype ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37 *)
Axiom fadd_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.6-215.12 *)
Lemma fadd__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fadd_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42 *)
Axiom fcopysign_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.6-223.17 *)
Lemma fcopysign__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fcopysign_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37 *)
Axiom fdiv_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.6-218.12 *)
Lemma fdiv__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fdiv_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37 *)
Axiom fmax_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.6-220.12 *)
Lemma fmax__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fmax_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37 *)
Axiom fmin_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.6-219.12 *)
Lemma fmin__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fmin_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37 *)
Axiom fmul_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.6-217.12 *)
Lemma fmul__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fmul_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37 *)
Axiom fsub_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.6-216.12 *)
Lemma fsub__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fsub_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36 *)
Definition iadd_ (v_N : res_N) (v_iN : iN) (iN_0 : iN) : iN :=
	match v_N, v_iN, iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN (((i_1 :> nat) + (i_2 :> nat))%N mod (2 ^ v_N)%N)%N)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.6-105.12 *)
Lemma iadd__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iadd_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36 *)
Axiom iand_ : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.6-112.12 *)
Lemma iand__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iand_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 *)
Inductive fun_idiv_ : res_N -> sx -> iN -> iN -> (option iN) -> Prop :=
	| fun_idiv__case_0 : forall (v_N : nat) (i_1 : uN), fun_idiv_ v_N U i_1 (mk_uN 0) None
	| fun_idiv__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_idiv_ v_N U i_1 i_2 (Some (mk_uN ((truncz (((i_1 :> nat) : rat) / ((i_2 :> nat) : rat))%Q) : nat)))
	| fun_idiv__case_2 : forall (v_N : nat) (i_1 : uN), fun_idiv_ v_N res_S i_1 (mk_uN 0) None
	| fun_idiv__case_3 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : int) (var_0 : int), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		(((var_0 : rat) / (var_1 : rat))%Q == ((2 ^ (((v_N : int) - (1 : int))%Z : nat))%N : rat)) ->
		fun_idiv_ v_N res_S i_1 i_2 None
	| fun_idiv__case_4 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_2 : int) (var_1 : int) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_2) ->
		(fun_signed_ v_N (i_1 :> nat) var_1) ->
		(fun_inv_signed_ v_N (truncz ((var_1 : rat) / (var_2 : rat))%Q) var_0) ->
		fun_idiv_ v_N res_S i_1 i_2 (Some (mk_uN var_0)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 *)
Lemma idiv__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : (option iN)) (var_0 : (option iN)),
	(fun_idiv_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val_opt == var_0) ->
	List.Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (option_to_list ret_val_opt).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36 *)
Definition imul_ (v_N : res_N) (v_iN : iN) (iN_0 : iN) : iN :=
	match v_N, v_iN, iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN (((i_1 :> nat) * (i_2 :> nat))%N mod (2 ^ v_N)%N)%N)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.6-107.12 *)
Lemma imul__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (imul_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35 *)
Axiom ior_ : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.6-114.11 *)
Lemma ior__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ior_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
Inductive fun_irem_ : res_N -> sx -> iN -> iN -> (option iN) -> Prop :=
	| fun_irem__case_0 : forall (v_N : nat) (i_1 : uN), fun_irem_ v_N U i_1 (mk_uN 0) None
	| fun_irem__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_irem_ v_N U i_1 i_2 (Some (mk_uN ((((i_1 :> nat) : int) - (((i_2 :> nat) * ((truncz (((i_1 :> nat) : rat) / ((i_2 :> nat) : rat))%Q) : nat))%N : int))%Z : nat)))
	| fun_irem__case_2 : forall (v_N : nat) (i_1 : uN), fun_irem_ v_N res_S i_1 (mk_uN 0) None
	| fun_irem__case_3 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (j_1 : int) (j_2 : int) (var_2 : int) (var_1 : int) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_2) ->
		(fun_signed_ v_N (i_1 :> nat) var_1) ->
		(fun_inv_signed_ v_N (j_1 - (j_2 * (truncz ((j_1 : rat) / (j_2 : rat))%Q))%Z)%Z var_0) ->
		((j_1 == var_1) && (j_2 == var_2)) ->
		fun_irem_ v_N res_S i_1 i_2 (Some (mk_uN var_0)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
Lemma irem__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : (option iN)) (var_0 : (option iN)),
	(fun_irem_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val_opt == var_0) ->
	List.Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (option_to_list ret_val_opt).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37 *)
Axiom irotl_ : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.6-118.13 *)
Lemma irotl__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (irotl_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37 *)
Axiom irotr_ : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.6-119.13 *)
Lemma irotr__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (irotr_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.1-116.34 *)
Axiom ishl_ : forall (v_N : res_N) (v_iN : iN) (v_u32 : u32), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.6-116.12 *)
Lemma ishl__is_wf : forall (v_N : res_N) (v_iN : iN) (v_u32 : u32) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN 32 v_u32) ->
	(ret_val == (ishl_ v_N v_iN v_u32)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.1-117.74 *)
Axiom ishr_ : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (v_u32 : u32), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.6-117.12 *)
Lemma ishr__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN 32 v_u32) ->
	(ret_val == (ishr_ v_N v_sx v_iN v_u32)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36 *)
Definition isub_ (v_N : res_N) (v_iN : iN) (iN_0 : iN) : iN :=
	match v_N, v_iN, iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN ((((((2 ^ v_N)%N + (i_1 :> nat))%N : int) - ((i_2 :> nat) : int))%Z mod ((2 ^ v_N)%N : int))%Z : nat))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.6-106.12 *)
Lemma isub__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (isub_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36 *)
Axiom ixor_ : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.6-115.12 *)
Lemma ixor__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ixor_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 *)
Inductive fun_binop_ : numtype -> binop_ -> num_ -> num_ -> (seq num_) -> Prop :=
	| fun_binop__case_0 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 ADD) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (iadd_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_1 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 ADD) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (iadd_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_2 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 SUB) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (isub_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_3 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 SUB) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (isub_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_4 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 MUL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (imul_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_5 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 MUL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (imul_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_idiv_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 (DIV v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (list_ num_ (option_map (fun (iter_0_15 : iN) => (mk_num__0 Inn_I32 iter_0_15)) var_0))
	| fun_binop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_idiv_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 (DIV v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (list_ num_ (option_map (fun (iter_0_16 : iN) => (mk_num__0 Inn_I64 iter_0_16)) var_0))
	| fun_binop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_irem_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 (REM v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (list_ num_ (option_map (fun (iter_0_17 : iN) => (mk_num__0 Inn_I32 iter_0_17)) var_0))
	| fun_binop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_irem_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 (REM v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (list_ num_ (option_map (fun (iter_0_18 : iN) => (mk_num__0 Inn_I64 iter_0_18)) var_0))
	| fun_binop__case_10 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 AND) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (iand_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_11 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 AND) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (iand_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_12 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 OR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (ior_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_13 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 OR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (ior_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_14 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 XOR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (ixor_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_15 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 XOR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (ixor_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_16 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 SHL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (ishl_ (sizenn (numtype_Inn Inn_I32)) iN_1 (mk_uN (iN_2 :> (nat)))))]
	| fun_binop__case_17 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 SHL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (ishl_ (sizenn (numtype_Inn Inn_I64)) iN_1 (mk_uN (iN_2 :> (nat)))))]
	| fun_binop__case_18 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 (SHR v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (ishr_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 (mk_uN (iN_2 :> (nat)))))]
	| fun_binop__case_19 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 (SHR v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (ishr_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 (mk_uN (iN_2 :> (nat)))))]
	| fun_binop__case_20 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 ROTL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (irotl_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_21 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 ROTL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (irotl_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_22 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I32 (mk_binop__0 Inn_I32 ROTR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (irotr_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_23 : forall (iN_1 : uN) (iN_2 : uN), fun_binop_ I64 (mk_binop__0 Inn_I64 ROTR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (irotr_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_24 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_ADD) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_19 : fN) => (mk_num__1 Fnn_F32 iter_0_19)) (fadd_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_25 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_ADD) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_20 : fN) => (mk_num__1 Fnn_F64 iter_0_20)) (fadd_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_26 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_SUB) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_21 : fN) => (mk_num__1 Fnn_F32 iter_0_21)) (fsub_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_27 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_SUB) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_22 : fN) => (mk_num__1 Fnn_F64 iter_0_22)) (fsub_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_28 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_MUL) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_23 : fN) => (mk_num__1 Fnn_F32 iter_0_23)) (fmul_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_29 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_24 : fN) => (mk_num__1 Fnn_F64 iter_0_24)) (fmul_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_30 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_DIV) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_25 : fN) => (mk_num__1 Fnn_F32 iter_0_25)) (fdiv_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_31 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_DIV) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_26 : fN) => (mk_num__1 Fnn_F64 iter_0_26)) (fdiv_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_32 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F32 (mk_binop__1 Fnn_F32 MIN) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_27 : fN) => (mk_num__1 Fnn_F32 iter_0_27)) (fmin_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_33 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F64 (mk_binop__1 Fnn_F64 MIN) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_28 : fN) => (mk_num__1 Fnn_F64 iter_0_28)) (fmin_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_34 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F32 (mk_binop__1 Fnn_F32 MAX) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_29 : fN) => (mk_num__1 Fnn_F32 iter_0_29)) (fmax_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_35 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F64 (mk_binop__1 Fnn_F64 MAX) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_30 : fN) => (mk_num__1 Fnn_F64 iter_0_30)) (fmax_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_36 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F32 (mk_binop__1 Fnn_F32 COPYSIGN) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_31 : fN) => (mk_num__1 Fnn_F32 iter_0_31)) (fcopysign_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_37 : forall (fN_1 : fN) (fN_2 : fN), fun_binop_ F64 (mk_binop__1 Fnn_F64 COPYSIGN) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_32 : fN) => (mk_num__1 Fnn_F64 iter_0_32)) (fcopysign_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 *)
Lemma binop__is_wf : forall (v_numtype : numtype) (v_binop_ : binop_) (v_num_ : num_) (num__0 : num_) (ret_val_lst : (seq num_)) (var_0 : (seq num_)),
	(fun_binop_ v_numtype v_binop_ v_num_ num__0 var_0) ->
	(wf_binop_ v_numtype v_binop_) ->
	(wf_num_ v_numtype v_num_) ->
	(wf_num_ v_numtype num__0) ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : num_) => (wf_num_ v_numtype ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27 *)
Definition ieqz_ (v_N : res_N) (v_iN : iN) : u32 :=
	match v_N, v_iN return u32 with
		| v_N, i_1 => (mk_uN (res_bool ((i_1 :> nat) == 0)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.6-123.12 *)
Lemma ieqz__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : u32),
	(wf_uN v_N v_iN) ->
	(ret_val == (ieqz_ v_N v_iN)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.1-49.32 *)
Definition fun_testop_ (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) : num_ :=
	match v_numtype, v_testop_, v_num_ return num_ with
		| I32, (mk_testop__0 Inn_I32 EQZ), (mk_num__0 Inn_I32 v_iN) => (mk_num__0 Inn_I32 (ieqz_ (sizenn (numtype_Inn Inn_I32)) v_iN))
		| I64, (mk_testop__0 Inn_I64 EQZ), (mk_num__0 Inn_I64 v_iN) => (mk_num__0 Inn_I32 (ieqz_ (sizenn (numtype_Inn Inn_I64)) v_iN))
		| _, _, _ => default_val
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 *)
Lemma testop__is_wf : forall (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) (ret_val : num_),
	(wf_testop_ v_numtype v_testop_) ->
	(wf_num_ v_numtype v_num_) ->
	(ret_val == (fun_testop_ v_numtype v_testop_ v_num_)) ->
	(wf_num_ I32 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33 *)
Axiom feq_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), u32.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.6-231.11 *)
Lemma feq__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (feq_ v_N v_fN fN_0)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33 *)
Axiom fge_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), u32.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.6-236.11 *)
Lemma fge__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (fge_ v_N v_fN fN_0)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33 *)
Axiom fgt_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), u32.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.6-234.11 *)
Lemma fgt__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (fgt_ v_N v_fN fN_0)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33 *)
Axiom fle_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), u32.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.6-235.11 *)
Lemma fle__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (fle_ v_N v_fN fN_0)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33 *)
Axiom flt_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), u32.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.6-233.11 *)
Lemma flt__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (flt_ v_N v_fN fN_0)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33 *)
Axiom fne_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), u32.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.6-232.11 *)
Lemma fne__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (fne_ v_N v_fN fN_0)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33 *)
Definition ieq_ (v_N : res_N) (v_iN : iN) (iN_0 : iN) : u32 :=
	match v_N, v_iN, iN_0 return u32 with
		| v_N, i_1, i_2 => (mk_uN (res_bool (i_1 == i_2)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.6-125.11 *)
Lemma ieq__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : u32),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ieq_ v_N v_iN iN_0)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
Inductive fun_ige_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ige__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ige_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) >= (i_2 :> nat))%N))
	| fun_ige__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : int) (var_0 : int), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ige_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 >= var_1)%Z)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
Lemma ige__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32),
	(fun_ige_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
Inductive fun_igt_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_igt__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_igt_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) > (i_2 :> nat))%N))
	| fun_igt__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : int) (var_0 : int), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_igt_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 > var_1)%Z)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
Lemma igt__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32),
	(fun_igt_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
Inductive fun_ile_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ile__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ile_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) <= (i_2 :> nat))%N))
	| fun_ile__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : int) (var_0 : int), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ile_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 <= var_1)%Z)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
Lemma ile__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32),
	(fun_ile_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
Inductive fun_ilt_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ilt__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ilt_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) < (i_2 :> nat))%N))
	| fun_ilt__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : int) (var_0 : int), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ilt_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 < var_1)%Z)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
Lemma ilt__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32),
	(fun_ilt_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33 *)
Definition ine_ (v_N : res_N) (v_iN : iN) (iN_0 : iN) : u32 :=
	match v_N, v_iN, iN_0 return u32 with
		| v_N, i_1, i_2 => (mk_uN (res_bool (i_1 != i_2)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.6-126.11 *)
Lemma ine__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : u32),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ine_ v_N v_iN iN_0)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
Inductive fun_relop_ : numtype -> relop_ -> num_ -> num_ -> num_ -> Prop :=
	| fun_relop__case_0 : forall (iN_1 : uN) (iN_2 : uN), fun_relop_ I32 (mk_relop__0 Inn_I32 EQ) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 (ieq_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))
	| fun_relop__case_1 : forall (iN_1 : uN) (iN_2 : uN), fun_relop_ I64 (mk_relop__0 Inn_I64 EQ) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 (ieq_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))
	| fun_relop__case_2 : forall (iN_1 : uN) (iN_2 : uN), fun_relop_ I32 (mk_relop__0 Inn_I32 NE) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 (ine_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))
	| fun_relop__case_3 : forall (iN_1 : uN) (iN_2 : uN), fun_relop_ I64 (mk_relop__0 Inn_I64 NE) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 (ine_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))
	| fun_relop__case_4 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ilt_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (LT v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_5 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ilt_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (LT v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_igt_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (GT v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_igt_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (GT v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ile_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (LE v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ile_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (LE v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_10 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ige_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (GE v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_11 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ige_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (GE v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_12 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_EQ) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (feq_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_13 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_EQ) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (feq_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_14 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_NE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fne_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_15 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_NE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fne_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_16 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_LT) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (flt_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_17 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_LT) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (flt_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_18 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_GT) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fgt_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_19 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_GT) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fgt_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_20 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_LE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fle_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_21 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_LE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fle_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_22 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_GE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fge_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_23 : forall (fN_1 : fN) (fN_2 : fN), fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_GE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fge_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
Lemma relop__is_wf : forall (v_numtype : numtype) (v_relop_ : relop_) (v_num_ : num_) (num__0 : num_) (ret_val : num_) (var_0 : num_),
	(fun_relop_ v_numtype v_relop_ v_num_ num__0 var_0) ->
	(wf_relop_ v_numtype v_relop_) ->
	(wf_num_ v_numtype v_num_) ->
	(wf_num_ v_numtype num__0) ->
	(ret_val == var_0) ->
	(wf_num_ I32 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90 *)
Axiom convert__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN), fN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.6-61.16 *)
Lemma convert___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN) (ret_val : fN),
	(wf_uN v_M v_iN) ->
	(ret_val == (convert__ v_M v_N v_sx v_iN)) ->
	(wf_fN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36 *)
Axiom demote__ : forall (v_M : M) (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.6-59.15 *)
Lemma demote___is_wf : forall (v_M : M) (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_M v_fN) ->
	(ret_val_lst == (demote__ v_M v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37 *)
Axiom promote__ : forall (v_M : M) (v_N : res_N) (v_fN : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.6-60.16 *)
Lemma promote___is_wf : forall (v_M : M) (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_M v_fN) ->
	(ret_val_lst == (promote__ v_M v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76 *)
Axiom reinterpret__ : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_), num_.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.6-63.20 *)
Lemma reinterpret___is_wf : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) (ret_val : num_),
	(wf_num_ numtype_1 v_num_) ->
	(ret_val == (reinterpret__ numtype_1 numtype_2 v_num_)) ->
	(wf_num_ numtype_2 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88 *)
Axiom trunc__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN), (option iN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.6-57.14 *)
Lemma trunc___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN) (ret_val_opt : (option iN)),
	(wf_fN v_M v_fN) ->
	(ret_val_opt == (trunc__ v_M v_N v_sx v_fN)) ->
	List.Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (option_to_list ret_val_opt).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93 *)
Axiom trunc_sat__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN), (option iN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.6-58.18 *)
Lemma trunc_sat___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN) (ret_val_opt : (option iN)),
	(wf_fN v_M v_fN) ->
	(ret_val_opt == (trunc_sat__ v_M v_N v_sx v_fN)) ->
	List.Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (option_to_list ret_val_opt).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
Inductive fun_cvtop__ : numtype -> numtype -> cvtop -> num_ -> (seq num_) -> Prop :=
	| fun_cvtop___case_0 : forall (v_sx : sx) (iN_1 : uN), fun_cvtop__ I32 I32 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I32 iN_1) [::(mk_num__0 Inn_I32 (extend__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))]
	| fun_cvtop___case_1 : forall (v_sx : sx) (iN_1 : uN), fun_cvtop__ I64 I32 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I64 iN_1) [::(mk_num__0 Inn_I32 (extend__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))]
	| fun_cvtop___case_2 : forall (v_sx : sx) (iN_1 : uN), fun_cvtop__ I32 I64 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I32 iN_1) [::(mk_num__0 Inn_I64 (extend__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))]
	| fun_cvtop___case_3 : forall (v_sx : sx) (iN_1 : uN), fun_cvtop__ I64 I64 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I64 iN_1) [::(mk_num__0 Inn_I64 (extend__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))]
	| fun_cvtop___case_4 : forall (iN_1 : uN), fun_cvtop__ I32 I32 WRAP (mk_num__0 Inn_I32 iN_1) [::(mk_num__0 Inn_I32 (wrap__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))]
	| fun_cvtop___case_5 : forall (iN_1 : uN), fun_cvtop__ I64 I32 WRAP (mk_num__0 Inn_I64 iN_1) [::(mk_num__0 Inn_I32 (wrap__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))]
	| fun_cvtop___case_6 : forall (iN_1 : uN), fun_cvtop__ I32 I64 WRAP (mk_num__0 Inn_I32 iN_1) [::(mk_num__0 Inn_I64 (wrap__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))]
	| fun_cvtop___case_7 : forall (iN_1 : uN), fun_cvtop__ I64 I64 WRAP (mk_num__0 Inn_I64 iN_1) [::(mk_num__0 Inn_I64 (wrap__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))]
	| fun_cvtop___case_8 : forall (v_sx : sx) (fN_1 : fN), fun_cvtop__ F32 I32 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F32 fN_1) (list_ num_ (option_map (fun (iter_0_33 : iN) => (mk_num__0 Inn_I32 iter_0_33)) (trunc__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))
	| fun_cvtop___case_9 : forall (v_sx : sx) (fN_1 : fN), fun_cvtop__ F64 I32 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F64 fN_1) (list_ num_ (option_map (fun (iter_0_34 : iN) => (mk_num__0 Inn_I32 iter_0_34)) (trunc__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))
	| fun_cvtop___case_10 : forall (v_sx : sx) (fN_1 : fN), fun_cvtop__ F32 I64 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F32 fN_1) (list_ num_ (option_map (fun (iter_0_35 : iN) => (mk_num__0 Inn_I64 iter_0_35)) (trunc__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))
	| fun_cvtop___case_11 : forall (v_sx : sx) (fN_1 : fN), fun_cvtop__ F64 I64 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F64 fN_1) (list_ num_ (option_map (fun (iter_0_36 : iN) => (mk_num__0 Inn_I64 iter_0_36)) (trunc__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))
	| fun_cvtop___case_12 : forall (v_sx : sx) (fN_1 : fN), fun_cvtop__ F32 I32 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F32 fN_1) (list_ num_ (option_map (fun (iter_0_37 : iN) => (mk_num__0 Inn_I32 iter_0_37)) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))
	| fun_cvtop___case_13 : forall (v_sx : sx) (fN_1 : fN), fun_cvtop__ F64 I32 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F64 fN_1) (list_ num_ (option_map (fun (iter_0_38 : iN) => (mk_num__0 Inn_I32 iter_0_38)) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))
	| fun_cvtop___case_14 : forall (v_sx : sx) (fN_1 : fN), fun_cvtop__ F32 I64 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F32 fN_1) (list_ num_ (option_map (fun (iter_0_39 : iN) => (mk_num__0 Inn_I64 iter_0_39)) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))
	| fun_cvtop___case_15 : forall (v_sx : sx) (fN_1 : fN), fun_cvtop__ F64 I64 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F64 fN_1) (list_ num_ (option_map (fun (iter_0_40 : iN) => (mk_num__0 Inn_I64 iter_0_40)) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))
	| fun_cvtop___case_16 : forall (v_sx : sx) (iN_1 : uN), fun_cvtop__ I32 F32 (CONVERT v_sx) (mk_num__0 Inn_I32 iN_1) [::(mk_num__1 Fnn_F32 (convert__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))]
	| fun_cvtop___case_17 : forall (v_sx : sx) (iN_1 : uN), fun_cvtop__ I64 F32 (CONVERT v_sx) (mk_num__0 Inn_I64 iN_1) [::(mk_num__1 Fnn_F32 (convert__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))]
	| fun_cvtop___case_18 : forall (v_sx : sx) (iN_1 : uN), fun_cvtop__ I32 F64 (CONVERT v_sx) (mk_num__0 Inn_I32 iN_1) [::(mk_num__1 Fnn_F64 (convert__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))]
	| fun_cvtop___case_19 : forall (v_sx : sx) (iN_1 : uN), fun_cvtop__ I64 F64 (CONVERT v_sx) (mk_num__0 Inn_I64 iN_1) [::(mk_num__1 Fnn_F64 (convert__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))]
	| fun_cvtop___case_20 : forall (fN_1 : fN), fun_cvtop__ F32 F32 PROMOTE (mk_num__1 Fnn_F32 fN_1) (seq.map (fun (iter_0_41 : fN) => (mk_num__1 Fnn_F32 iter_0_41)) (promote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))
	| fun_cvtop___case_21 : forall (fN_1 : fN), fun_cvtop__ F64 F32 PROMOTE (mk_num__1 Fnn_F64 fN_1) (seq.map (fun (iter_0_42 : fN) => (mk_num__1 Fnn_F32 iter_0_42)) (promote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))
	| fun_cvtop___case_22 : forall (fN_1 : fN), fun_cvtop__ F32 F64 PROMOTE (mk_num__1 Fnn_F32 fN_1) (seq.map (fun (iter_0_43 : fN) => (mk_num__1 Fnn_F64 iter_0_43)) (promote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))
	| fun_cvtop___case_23 : forall (fN_1 : fN), fun_cvtop__ F64 F64 PROMOTE (mk_num__1 Fnn_F64 fN_1) (seq.map (fun (iter_0_44 : fN) => (mk_num__1 Fnn_F64 iter_0_44)) (promote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))
	| fun_cvtop___case_24 : forall (fN_1 : fN), fun_cvtop__ F32 F32 DEMOTE (mk_num__1 Fnn_F32 fN_1) (seq.map (fun (iter_0_45 : fN) => (mk_num__1 Fnn_F32 iter_0_45)) (demote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))
	| fun_cvtop___case_25 : forall (fN_1 : fN), fun_cvtop__ F64 F32 DEMOTE (mk_num__1 Fnn_F64 fN_1) (seq.map (fun (iter_0_46 : fN) => (mk_num__1 Fnn_F32 iter_0_46)) (demote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))
	| fun_cvtop___case_26 : forall (fN_1 : fN), fun_cvtop__ F32 F64 DEMOTE (mk_num__1 Fnn_F32 fN_1) (seq.map (fun (iter_0_47 : fN) => (mk_num__1 Fnn_F64 iter_0_47)) (demote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))
	| fun_cvtop___case_27 : forall (fN_1 : fN), fun_cvtop__ F64 F64 DEMOTE (mk_num__1 Fnn_F64 fN_1) (seq.map (fun (iter_0_48 : fN) => (mk_num__1 Fnn_F64 iter_0_48)) (demote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))
	| fun_cvtop___case_28 : forall (iN_1 : uN), 
		((res_size (valtype_Inn Inn_I32)) != None) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((!((res_size (valtype_Inn Inn_I32)))) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		fun_cvtop__ I32 F32 REINTERPRET (mk_num__0 Inn_I32 iN_1) [::(reinterpret__ (numtype_Inn Inn_I32) (numtype_Fnn Fnn_F32) (mk_num__0 Inn_I32 iN_1))]
	| fun_cvtop___case_29 : forall (iN_1 : uN), 
		((res_size (valtype_Inn Inn_I64)) != None) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((!((res_size (valtype_Inn Inn_I64)))) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		fun_cvtop__ I64 F32 REINTERPRET (mk_num__0 Inn_I64 iN_1) [::(reinterpret__ (numtype_Inn Inn_I64) (numtype_Fnn Fnn_F32) (mk_num__0 Inn_I64 iN_1))]
	| fun_cvtop___case_30 : forall (iN_1 : uN), 
		((res_size (valtype_Inn Inn_I32)) != None) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((!((res_size (valtype_Inn Inn_I32)))) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		fun_cvtop__ I32 F64 REINTERPRET (mk_num__0 Inn_I32 iN_1) [::(reinterpret__ (numtype_Inn Inn_I32) (numtype_Fnn Fnn_F64) (mk_num__0 Inn_I32 iN_1))]
	| fun_cvtop___case_31 : forall (iN_1 : uN), 
		((res_size (valtype_Inn Inn_I64)) != None) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((!((res_size (valtype_Inn Inn_I64)))) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		fun_cvtop__ I64 F64 REINTERPRET (mk_num__0 Inn_I64 iN_1) [::(reinterpret__ (numtype_Inn Inn_I64) (numtype_Fnn Fnn_F64) (mk_num__0 Inn_I64 iN_1))]
	| fun_cvtop___case_32 : forall (fN_1 : fN), 
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((res_size (valtype_Inn Inn_I32)) != None) ->
		((!((res_size (valtype_Fnn Fnn_F32)))) == (!((res_size (valtype_Inn Inn_I32))))) ->
		fun_cvtop__ F32 I32 REINTERPRET (mk_num__1 Fnn_F32 fN_1) [::(reinterpret__ (numtype_Fnn Fnn_F32) (numtype_Inn Inn_I32) (mk_num__1 Fnn_F32 fN_1))]
	| fun_cvtop___case_33 : forall (fN_1 : fN), 
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((res_size (valtype_Inn Inn_I32)) != None) ->
		((!((res_size (valtype_Fnn Fnn_F64)))) == (!((res_size (valtype_Inn Inn_I32))))) ->
		fun_cvtop__ F64 I32 REINTERPRET (mk_num__1 Fnn_F64 fN_1) [::(reinterpret__ (numtype_Fnn Fnn_F64) (numtype_Inn Inn_I32) (mk_num__1 Fnn_F64 fN_1))]
	| fun_cvtop___case_34 : forall (fN_1 : fN), 
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((res_size (valtype_Inn Inn_I64)) != None) ->
		((!((res_size (valtype_Fnn Fnn_F32)))) == (!((res_size (valtype_Inn Inn_I64))))) ->
		fun_cvtop__ F32 I64 REINTERPRET (mk_num__1 Fnn_F32 fN_1) [::(reinterpret__ (numtype_Fnn Fnn_F32) (numtype_Inn Inn_I64) (mk_num__1 Fnn_F32 fN_1))]
	| fun_cvtop___case_35 : forall (fN_1 : fN), 
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((res_size (valtype_Inn Inn_I64)) != None) ->
		((!((res_size (valtype_Fnn Fnn_F64)))) == (!((res_size (valtype_Inn Inn_I64))))) ->
		fun_cvtop__ F64 I64 REINTERPRET (mk_num__1 Fnn_F64 fN_1) [::(reinterpret__ (numtype_Fnn Fnn_F64) (numtype_Inn Inn_I64) (mk_num__1 Fnn_F64 fN_1))].

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
Lemma cvtop___is_wf : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop) (v_num_ : num_) (ret_val_lst : (seq num_)) (var_0 : (seq num_)),
	(fun_cvtop__ numtype_1 numtype_2 v_cvtop v_num_ var_0) ->
	(wf_num_ numtype_1 v_num_) ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : num_) => (wf_num_ numtype_2 ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87 *)
Axiom narrow__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.6-62.15 *)
Lemma narrow___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN) (ret_val : iN),
	(wf_uN v_M v_iN) ->
	(ret_val == (narrow__ v_M v_N v_sx v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 *)
Axiom ibits_ : forall (v_N : res_N) (v_iN : iN), (seq bit).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.6-76.13 *)
Lemma ibits__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val_lst : (seq bit)),
	(wf_uN v_N v_iN) ->
	(ret_val_lst == (ibits_ v_N v_iN)) ->
	List.Forall (fun (ret_val : bit) => (wf_bit ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102 *)
Axiom fbits_ : forall (v_N : res_N) (v_fN : fN), (seq bit).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.6-77.13 *)
Lemma fbits__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq bit)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fbits_ v_N v_fN)) ->
	List.Forall (fun (ret_val : bit) => (wf_bit ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103 *)
Axiom ibytes_ : forall (v_N : res_N) (v_iN : iN), (seq byte).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.6-78.14 *)
Lemma ibytes__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val_lst : (seq byte)),
	(wf_uN v_N v_iN) ->
	(ret_val_lst == (ibytes_ v_N v_iN)) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103 *)
Axiom fbytes_ : forall (v_N : res_N) (v_fN : fN), (seq byte).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.6-79.14 *)
Lemma fbytes__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq byte)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fbytes_ v_N v_fN)) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103 *)
Axiom nbytes_ : forall (v_numtype : numtype) (v_num_ : num_), (seq byte).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.6-80.14 *)
Lemma nbytes__is_wf : forall (v_numtype : numtype) (v_num_ : num_) (ret_val_lst : (seq byte)),
	(wf_num_ v_numtype v_num_) ->
	(ret_val_lst == (nbytes_ v_numtype v_num_)) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103 *)
Axiom vbytes_ : forall (v_vectype : vectype) (v_vec_ : vec_), (seq byte).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.6-81.14 *)
Lemma vbytes__is_wf : forall (v_vectype : vectype) (v_vec_ : vec_) (ret_val_lst : (seq byte)),
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) v_vec_) ->
	(ret_val_lst == (vbytes_ v_vectype v_vec_)) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 *)
Axiom inv_ibits_ : forall (v_N : res_N) (var_0_lst : (seq bit)), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.6-83.17 *)
Lemma inv_ibits__is_wf : forall (v_N : res_N) (var_0_lst : (seq bit)) (ret_val : iN),
	List.Forall (fun (var_0 : bit) => (wf_bit var_0)) var_0_lst ->
	(ret_val == (inv_ibits_ v_N var_0_lst)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 *)
Axiom inv_fbits_ : forall (v_N : res_N) (var_0_lst : (seq bit)), fN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.6-84.17 *)
Lemma inv_fbits__is_wf : forall (v_N : res_N) (var_0_lst : (seq bit)) (ret_val : fN),
	List.Forall (fun (var_0 : bit) => (wf_bit var_0)) var_0_lst ->
	(ret_val == (inv_fbits_ v_N var_0_lst)) ->
	(wf_fN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86 *)
Axiom inv_ibytes_ : forall (v_N : res_N) (var_0_lst : (seq byte)), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.6-85.18 *)
Lemma inv_ibytes__is_wf : forall (v_N : res_N) (var_0_lst : (seq byte)) (ret_val : iN),
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (inv_ibytes_ v_N var_0_lst)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86 *)
Axiom inv_fbytes_ : forall (v_N : res_N) (var_0_lst : (seq byte)), fN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.6-86.18 *)
Lemma inv_fbytes__is_wf : forall (v_N : res_N) (var_0_lst : (seq byte)) (ret_val : fN),
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (inv_fbytes_ v_N var_0_lst)) ->
	(wf_fN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84 *)
Axiom inv_nbytes_ : forall (v_numtype : numtype) (var_0_lst : (seq byte)), num_.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.6-87.18 *)
Lemma inv_nbytes__is_wf : forall (v_numtype : numtype) (var_0_lst : (seq byte)) (ret_val : num_),
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (inv_nbytes_ v_numtype var_0_lst)) ->
	(wf_num_ v_numtype ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84 *)
Axiom inv_vbytes_ : forall (v_vectype : vectype) (var_0_lst : (seq byte)), vec_.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.6-88.18 *)
Lemma inv_vbytes__is_wf : forall (v_vectype : vectype) (var_0_lst : (seq byte)) (ret_val : vec_),
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (inv_vbytes_ v_vectype var_0_lst)) ->
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29 *)
Axiom inot_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.6-110.12 *)
Lemma inot__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (inot_ v_N v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29 *)
Axiom irev_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.6-111.12 *)
Lemma irev__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (irev_ v_N v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39 *)
Axiom iandnot_ : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.6-113.15 *)
Lemma iandnot__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iandnot_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27 *)
Definition inez_ (v_N : res_N) (v_iN : iN) : u32 :=
	match v_N, v_iN return u32 with
		| v_N, i_1 => (mk_uN (res_bool ((i_1 :> nat) != 0)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.6-124.12 *)
Lemma inez__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : u32),
	(wf_uN v_N v_iN) ->
	(ret_val == (inez_ v_N v_iN)) ->
	(wf_uN 32 ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49 *)
Axiom ibitselect_ : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.6-131.18 *)
Lemma ibitselect__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(wf_uN v_N iN_1) ->
	(ret_val == (ibitselect_ v_N v_iN iN_0 iN_1)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29 *)
Definition ineg_ (v_N : res_N) (v_iN : iN) : iN :=
	match v_N, v_iN return iN with
		| v_N, i_1 => (mk_uN (((((2 ^ v_N)%N : int) - ((i_1 :> nat) : int))%Z mod ((2 ^ v_N)%N : int))%Z : nat))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.6-133.12 *)
Lemma ineg__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (ineg_ v_N v_iN)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
Inductive fun_iabs_ : res_N -> iN -> iN -> Prop :=
	| fun_iabs__case_0 : forall (v_N : nat) (i_1 : uN) (var_0 : int), 
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_iabs_ v_N i_1 (if (var_0 >= (0 : int))%Z then i_1 else (ineg_ v_N i_1)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
Lemma iabs__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN) (var_0 : iN),
	(fun_iabs_ v_N v_iN var_0) ->
	(wf_uN v_N v_iN) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
Inductive fun_imin_ : res_N -> sx -> iN -> iN -> iN -> Prop :=
	| fun_imin__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), 
		((i_1 :> nat) <= (i_2 :> nat))%N ->
		fun_imin_ v_N U i_1 i_2 i_1
	| fun_imin__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), 
		((i_1 :> nat) > (i_2 :> nat))%N ->
		fun_imin_ v_N U i_1 i_2 i_2
	| fun_imin__case_2 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : int) (var_0 : int), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_imin_ v_N res_S i_1 i_2 (if (var_0 <= var_1)%Z then i_1 else i_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
Lemma imin__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN),
	(fun_imin_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
Inductive fun_imax_ : res_N -> sx -> iN -> iN -> iN -> Prop :=
	| fun_imax__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), 
		((i_1 :> nat) >= (i_2 :> nat))%N ->
		fun_imax_ v_N U i_1 i_2 i_1
	| fun_imax__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), 
		((i_1 :> nat) < (i_2 :> nat))%N ->
		fun_imax_ v_N U i_1 i_2 i_2
	| fun_imax__case_2 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : int) (var_0 : int), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_imax_ v_N res_S i_1 i_2 (if (var_0 >= var_1)%Z then i_1 else i_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
Lemma imax__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN),
	(fun_imax_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
Inductive fun_iadd_sat_ : res_N -> sx -> iN -> iN -> iN -> Prop :=
	| fun_iadd_sat__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_iadd_sat_ v_N U i_1 i_2 (mk_uN (sat_u_ v_N (((i_1 :> nat) + (i_2 :> nat))%N : int)))
	| fun_iadd_sat__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_2 : int) (var_1 : int) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_2) ->
		(fun_signed_ v_N (i_1 :> nat) var_1) ->
		(fun_inv_signed_ v_N (sat_s_ v_N (var_1 + var_2)%Z) var_0) ->
		fun_iadd_sat_ v_N res_S i_1 i_2 (mk_uN var_0).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
Lemma iadd_sat__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN),
	(fun_iadd_sat_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
Inductive fun_isub_sat_ : res_N -> sx -> iN -> iN -> iN -> Prop :=
	| fun_isub_sat__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_isub_sat_ v_N U i_1 i_2 (mk_uN (sat_u_ v_N (((i_1 :> nat) : int) - ((i_2 :> nat) : int))%Z))
	| fun_isub_sat__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_2 : int) (var_1 : int) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_2) ->
		(fun_signed_ v_N (i_1 :> nat) var_1) ->
		(fun_inv_signed_ v_N (sat_s_ v_N (var_1 - var_2)%Z) var_0) ->
		fun_isub_sat_ v_N res_S i_1 i_2 (mk_uN var_0).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
Lemma isub_sat__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN),
	(fun_isub_sat_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82 *)
Axiom iavgr_ : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.6-138.13 *)
Lemma iavgr__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iavgr_ v_N v_sx v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90 *)
Axiom iq15mulr_sat_ : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.6-139.20 *)
Lemma iq15mulr_sat__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iq15mulr_sat_ v_N v_sx v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38 *)
Axiom fpmin_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.6-221.13 *)
Lemma fpmin__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fpmin_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38 *)
Axiom fpmax_ : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.6-222.13 *)
Lemma fpmax__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fpmax_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27 *)
Definition packnum_ (v_lanetype : lanetype) (v_num_ : num_) : lane_ :=
	match v_lanetype, v_num_ return lane_ with
		| lanetype_I32, c => (mk_lane__0 I32 c)
		| lanetype_I64, c => (mk_lane__0 I64 c)
		| lanetype_F32, c => (mk_lane__0 F32 c)
		| lanetype_F64, c => (mk_lane__0 F64 c)
		| lanetype_I8, (mk_num__0 Inn_I32 c) => (mk_lane__1 I8 (wrap__ (!((res_size (valtype_numtype (unpack (lanetype_packtype I8)))))) (psize I8) c))
		| lanetype_I16, (mk_num__0 Inn_I32 c) => (mk_lane__1 I16 (wrap__ (!((res_size (valtype_numtype (unpack (lanetype_packtype I16)))))) (psize I16) c))
		| _, _ => default_val
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.6-323.15 *)
Lemma packnum__is_wf : forall (v_lanetype : lanetype) (v_num_ : num_) (ret_val : lane_),
	(wf_num_ (unpack v_lanetype) v_num_) ->
	(ret_val == (packnum_ v_lanetype v_num_)) ->
	(wf_lane_ v_lanetype ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.1-329.29 *)
Definition unpacknum_ (v_lanetype : lanetype) (v_lane_ : lane_) : num_ :=
	match v_lanetype, v_lane_ return num_ with
		| lanetype_I32, (mk_lane__0 I32 c) => c
		| lanetype_I64, (mk_lane__0 I64 c) => c
		| lanetype_F32, (mk_lane__0 F32 c) => c
		| lanetype_F64, (mk_lane__0 F64 c) => c
		| lanetype_I8, (mk_lane__1 I8 c) => (mk_num__0 Inn_I32 (extend__ (psize I8) (!((res_size (valtype_numtype (unpack (lanetype_packtype I8)))))) U c))
		| lanetype_I16, (mk_lane__1 I16 c) => (mk_num__0 Inn_I32 (extend__ (psize I16) (!((res_size (valtype_numtype (unpack (lanetype_packtype I16)))))) U c))
		| _, _ => default_val
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.6-328.17 *)
Lemma unpacknum__is_wf : forall (v_lanetype : lanetype) (v_lane_ : lane_) (ret_val : num_),
	(wf_lane_ v_lanetype v_lane_) ->
	(ret_val == (unpacknum_ v_lanetype v_lane_)) ->
	(wf_num_ (unpack v_lanetype) ret_val).
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.1-336.84 *)
Axiom lanes_ : forall (v_shape : shape) (v_vec_ : vec_), (seq lane_).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.6-336.13 *)
Lemma lanes__is_wf : forall (v_shape : shape) (v_vec_ : vec_) (ret_val_lst : (seq lane_)),
	(wf_shape v_shape) ->
	(wf_uN 128 v_vec_) ->
	(ret_val_lst == (lanes_ v_shape v_vec_)) ->
	List.Forall (fun (ret_val : lane_) => (wf_lane_ (fun_lanetype v_shape) ret_val)) ret_val_lst.
Proof. Admitted.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.1-340.36 *)
Axiom inv_lanes_ : forall (v_shape : shape) (var_0_lst : (seq lane_)), vec_.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.6-339.17 *)
Lemma inv_lanes__is_wf : forall (v_shape : shape) (var_0_lst : (seq lane_)) (ret_val : vec_),
	(wf_shape v_shape) ->
	List.Forall (fun (var_0 : lane_) => (wf_lane_ (fun_lanetype v_shape) var_0)) var_0_lst ->
	(ret_val == (inv_lanes_ v_shape var_0_lst)) ->
	(wf_uN 128 ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:343.1-343.28 *)
Definition zeroop (v_vcvtop : vcvtop) : (option zero) :=
	match v_vcvtop return (option zero) with
		| (vcvtop_EXTEND v_half v_sx) => None
		| (vcvtop_CONVERT half_opt v_sx) => None
		| (vcvtop_TRUNC_SAT v_sx zero_opt) => zero_opt
		| (vcvtop_DEMOTE v_zero) => (Some v_zero)
		| PROMOTELOW => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:350.1-350.28 *)
Definition halfop (v_vcvtop : vcvtop) : (option half) :=
	match v_vcvtop return (option half) with
		| (vcvtop_EXTEND v_half v_sx) => (Some v_half)
		| (vcvtop_CONVERT half_opt v_sx) => half_opt
		| (vcvtop_TRUNC_SAT v_sx zero_opt) => None
		| (vcvtop_DEMOTE v_zero) => None
		| PROMOTELOW => (Some LOW)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:357.1-357.32 *)
Definition fun_half (v_half : half) (res_nat : nat) (nat_0 : nat) : nat :=
	match v_half, res_nat, nat_0 return nat with
		| LOW, i, j => i
		| HIGH, i, j => j
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.1-363.28 *)
Definition vvunop_ (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) : vec_ :=
	match v_vectype, v_vvunop, v_vec_ return vec_ with
		| V128, NOT, v128 => (inot_ (!((res_size valtype_V128))) v128)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.6-362.14 *)
Lemma vvunop__is_wf : forall (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) (ret_val : vec_),
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) v_vec_) ->
	(ret_val == (vvunop_ v_vectype v_vvunop v_vec_)) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.1-365.31 *)
Definition vvbinop_ (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) : vec_ :=
	match v_vectype, v_vvbinop, v_vec_, vec__0 return vec_ with
		| V128, vvbinop_AND, v128_1, v128_2 => (iand_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, ANDNOT, v128_1, v128_2 => (iandnot_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, vvbinop_OR, v128_1, v128_2 => (ior_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, vvbinop_XOR, v128_1, v128_2 => (ixor_ (!((res_size valtype_V128))) v128_1 v128_2)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.6-364.15 *)
Lemma vvbinop__is_wf : forall (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_),
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) v_vec_) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) vec__0) ->
	(ret_val == (vvbinop_ v_vectype v_vvbinop v_vec_ vec__0)) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.1-367.34 *)
Definition vvternop_ (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) : vec_ :=
	match v_vectype, v_vvternop, v_vec_, vec__0, vec__1 return vec_ with
		| V128, BITSELECT, v128_1, v128_2, v128_3 => (ibitselect_ (!((res_size valtype_V128))) v128_1 v128_2 v128_3)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.6-366.16 *)
Lemma vvternop__is_wf : forall (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val : vec_),
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) v_vec_) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) vec__0) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) vec__1) ->
	(ret_val == (vvternop_ v_vectype v_vvternop v_vec_ vec__0 vec__1)) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 *)
Inductive fun_vunop_ : shape -> vunop_ -> vec_ -> (seq vec_) -> Prop :=
	| fun_vunop__case_0 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_3 : lane_) => ((proj_lane__2 lane_1_3) != None)) lane_1_lst ->
		List.Forall2 (fun (var_1 : uN) (lane_1_3 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_3))) var_1)) var_1_lst lane_1_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_2 : lane_) => ((proj_lane__2 lane_1_2) != None)) lane_1_lst ->
		List.Forall2 (fun (var_0 : uN) (lane_1_2 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_2))) var_0)) var_0_lst lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_ABS) v128_1 [::v128]
	| fun_vunop__case_1 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_6 : lane_) => ((proj_lane__2 lane_1_6) != None)) lane_1_lst ->
		List.Forall2 (fun (var_1 : uN) (lane_1_6 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_6))) var_1)) var_1_lst lane_1_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_5 : lane_) => ((proj_lane__2 lane_1_5) != None)) lane_1_lst ->
		List.Forall2 (fun (var_0 : uN) (lane_1_5 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_5))) var_0)) var_0_lst lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_ABS) v128_1 [::v128]
	| fun_vunop__case_2 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_9 : lane_) => ((proj_lane__2 lane_1_9) != None)) lane_1_lst ->
		List.Forall2 (fun (var_1 : uN) (lane_1_9 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_9))) var_1)) var_1_lst lane_1_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_8 : lane_) => ((proj_lane__2 lane_1_8) != None)) lane_1_lst ->
		List.Forall2 (fun (var_0 : uN) (lane_1_8 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_8))) var_0)) var_0_lst lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_ABS) v128_1 [::v128]
	| fun_vunop__case_3 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_12 : lane_) => ((proj_lane__2 lane_1_12) != None)) lane_1_lst ->
		List.Forall2 (fun (var_1 : uN) (lane_1_12 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_12))) var_1)) var_1_lst lane_1_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_11 : lane_) => ((proj_lane__2 lane_1_11) != None)) lane_1_lst ->
		List.Forall2 (fun (var_0 : uN) (lane_1_11 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_11))) var_0)) var_0_lst lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_ABS) v128_1 [::v128]
	| fun_vunop__case_4 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_14 : lane_) => ((proj_lane__2 lane_1_14) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_1_14 : lane_) => (mk_lane__2 Jnn_I32 (ineg_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_14)))))) lane_1_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_15 : lane_) => ((proj_lane__2 lane_1_15) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_15 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (ineg_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_15))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_NEG) v128_1 [::v128]
	| fun_vunop__case_5 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_17 : lane_) => ((proj_lane__2 lane_1_17) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_1_17 : lane_) => (mk_lane__2 Jnn_I64 (ineg_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_17)))))) lane_1_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_18 : lane_) => ((proj_lane__2 lane_1_18) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_18 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (ineg_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_18))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_NEG) v128_1 [::v128]
	| fun_vunop__case_6 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_20 : lane_) => ((proj_lane__2 lane_1_20) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_1_20 : lane_) => (mk_lane__2 Jnn_I8 (ineg_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_20)))))) lane_1_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_21 : lane_) => ((proj_lane__2 lane_1_21) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_21 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (ineg_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_21))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_NEG) v128_1 [::v128]
	| fun_vunop__case_7 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_23 : lane_) => ((proj_lane__2 lane_1_23) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_1_23 : lane_) => (mk_lane__2 Jnn_I16 (ineg_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_23)))))) lane_1_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_24 : lane_) => ((proj_lane__2 lane_1_24) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_24 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (ineg_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_24))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_NEG) v128_1 [::v128]
	| fun_vunop__case_8 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_26 : lane_) => ((proj_lane__2 lane_1_26) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_1_26 : lane_) => (mk_lane__2 Jnn_I32 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_26)))))) lane_1_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_27 : lane_) => ((proj_lane__2 lane_1_27) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_27 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_27))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_POPCNT) v128_1 [::v128]
	| fun_vunop__case_9 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_29 : lane_) => ((proj_lane__2 lane_1_29) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_1_29 : lane_) => (mk_lane__2 Jnn_I64 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_29)))))) lane_1_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_30 : lane_) => ((proj_lane__2 lane_1_30) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_30 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_30))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_POPCNT) v128_1 [::v128]
	| fun_vunop__case_10 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_32 : lane_) => ((proj_lane__2 lane_1_32) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_1_32 : lane_) => (mk_lane__2 Jnn_I8 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_32)))))) lane_1_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_33 : lane_) => ((proj_lane__2 lane_1_33) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_33 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_33))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_POPCNT) v128_1 [::v128]
	| fun_vunop__case_11 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_35 : lane_) => ((proj_lane__2 lane_1_35) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_1_35 : lane_) => (mk_lane__2 Jnn_I16 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_35)))))) lane_1_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_36 : lane_) => ((proj_lane__2 lane_1_36) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_36 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_36))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_POPCNT) v128_1 [::v128]
	| fun_vunop__case_12 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_38 : lane_) => (seq.map (fun (iter_0_49 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_49))) (fabs_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_38))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_2 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_2)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_39 : lane_) => List.Forall (fun (iter_0_50 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_50)))) (fabs_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_39)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_ABS) v128_1 v128_lst
	| fun_vunop__case_13 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_41 : lane_) => (seq.map (fun (iter_0_51 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_51))) (fabs_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_41))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_4 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_4)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_42 : lane_) => List.Forall (fun (iter_0_52 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_52)))) (fabs_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_42)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_ABS) v128_1 v128_lst
	| fun_vunop__case_14 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_44 : lane_) => (seq.map (fun (iter_0_53 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_53))) (fneg_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_44))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_6 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_6)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_45 : lane_) => List.Forall (fun (iter_0_54 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_54)))) (fneg_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_45)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_NEG) v128_1 v128_lst
	| fun_vunop__case_15 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_47 : lane_) => (seq.map (fun (iter_0_55 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_55))) (fneg_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_47))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_8 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_8)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_48 : lane_) => List.Forall (fun (iter_0_56 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_56)))) (fneg_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_48)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_NEG) v128_1 v128_lst
	| fun_vunop__case_16 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_50 : lane_) => (seq.map (fun (iter_0_57 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_57))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_50))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_10 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_10)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_51 : lane_) => List.Forall (fun (iter_0_58 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_58)))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_51)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_SQRT) v128_1 v128_lst
	| fun_vunop__case_17 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_53 : lane_) => (seq.map (fun (iter_0_59 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_59))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_53))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_12 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_12)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_54 : lane_) => List.Forall (fun (iter_0_60 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_60)))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_54)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_SQRT) v128_1 v128_lst
	| fun_vunop__case_18 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_56 : lane_) => (seq.map (fun (iter_0_61 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_61))) (fceil_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_56))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_14 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_14)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_57 : lane_) => List.Forall (fun (iter_0_62 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_62)))) (fceil_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_57)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_CEIL) v128_1 v128_lst
	| fun_vunop__case_19 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_59 : lane_) => (seq.map (fun (iter_0_63 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_63))) (fceil_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_59))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_16 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_16)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_60 : lane_) => List.Forall (fun (iter_0_64 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_64)))) (fceil_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_60)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_CEIL) v128_1 v128_lst
	| fun_vunop__case_20 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_62 : lane_) => (seq.map (fun (iter_0_65 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_65))) (ffloor_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_62))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_18 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_18)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_63 : lane_) => List.Forall (fun (iter_0_66 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_66)))) (ffloor_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_63)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_FLOOR) v128_1 v128_lst
	| fun_vunop__case_21 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_65 : lane_) => (seq.map (fun (iter_0_67 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_67))) (ffloor_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_65))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_20 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_20)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_66 : lane_) => List.Forall (fun (iter_0_68 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_68)))) (ffloor_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_66)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_FLOOR) v128_1 v128_lst
	| fun_vunop__case_22 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_68 : lane_) => (seq.map (fun (iter_0_69 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_69))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_68))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_22 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_22)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_69 : lane_) => List.Forall (fun (iter_0_70 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_70)))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_69)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_TRUNC) v128_1 v128_lst
	| fun_vunop__case_23 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_71 : lane_) => (seq.map (fun (iter_0_71 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_71))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_71))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_24 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_24)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_72 : lane_) => List.Forall (fun (iter_0_72 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_72)))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_72)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_TRUNC) v128_1 v128_lst
	| fun_vunop__case_24 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_74 : lane_) => (seq.map (fun (iter_0_73 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_73))) (fnearest_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_74))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_26 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_26)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_75 : lane_) => List.Forall (fun (iter_0_74 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_74)))) (fnearest_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_75)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_NEAREST) v128_1 v128_lst
	| fun_vunop__case_25 : forall (v_M : nat) (v128_1 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_77 : lane_) => (seq.map (fun (iter_0_75 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_75))) (fnearest_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_77))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_28 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_28)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		List.Forall (fun (lane_1_78 : lane_) => List.Forall (fun (iter_0_76 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_76)))) (fnearest_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_78)))))))) lane_1_lst ->
		(v_M == M_0) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_NEAREST) v128_1 v128_lst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 *)
Lemma vunop__is_wf : forall (v_shape : shape) (v_vunop_ : vunop_) (v_vec_ : vec_) (ret_val_lst : (seq vec_)) (var_0 : (seq vec_)),
	(fun_vunop_ v_shape v_vunop_ v_vec_ var_0) ->
	(wf_shape v_shape) ->
	(wf_vunop_ v_shape v_vunop_) ->
	(wf_uN 128 v_vec_) ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst.
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 *)
Inductive fun_vbinop_ : shape -> vbinop_ -> vec_ -> vec_ -> (seq vec_) -> Prop :=
	| fun_vbinop__case_0 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_80 : lane_) => ((proj_lane__2 lane_1_80) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_2 : lane_) => ((proj_lane__2 lane_2_2) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_80 : lane_) (lane_2_2 : lane_) => (mk_lane__2 Jnn_I32 (iadd_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_80))) (!((proj_lane__2 lane_2_2)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_81 : lane_) => ((proj_lane__2 lane_1_81) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_3 : lane_) => ((proj_lane__2 lane_2_3) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_81 : lane_) (lane_2_3 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iadd_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_81))) (!((proj_lane__2 lane_2_3))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [::v128]
	| fun_vbinop__case_1 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_83 : lane_) => ((proj_lane__2 lane_1_83) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_5 : lane_) => ((proj_lane__2 lane_2_5) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_83 : lane_) (lane_2_5 : lane_) => (mk_lane__2 Jnn_I64 (iadd_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_83))) (!((proj_lane__2 lane_2_5)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_84 : lane_) => ((proj_lane__2 lane_1_84) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_6 : lane_) => ((proj_lane__2 lane_2_6) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_84 : lane_) (lane_2_6 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iadd_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_84))) (!((proj_lane__2 lane_2_6))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [::v128]
	| fun_vbinop__case_2 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_86 : lane_) => ((proj_lane__2 lane_1_86) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_8 : lane_) => ((proj_lane__2 lane_2_8) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_86 : lane_) (lane_2_8 : lane_) => (mk_lane__2 Jnn_I8 (iadd_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_86))) (!((proj_lane__2 lane_2_8)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_87 : lane_) => ((proj_lane__2 lane_1_87) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_9 : lane_) => ((proj_lane__2 lane_2_9) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_87 : lane_) (lane_2_9 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iadd_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_87))) (!((proj_lane__2 lane_2_9))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [::v128]
	| fun_vbinop__case_3 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_89 : lane_) => ((proj_lane__2 lane_1_89) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_11 : lane_) => ((proj_lane__2 lane_2_11) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_89 : lane_) (lane_2_11 : lane_) => (mk_lane__2 Jnn_I16 (iadd_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_89))) (!((proj_lane__2 lane_2_11)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_90 : lane_) => ((proj_lane__2 lane_1_90) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_12 : lane_) => ((proj_lane__2 lane_2_12) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_90 : lane_) (lane_2_12 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iadd_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_90))) (!((proj_lane__2 lane_2_12))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [::v128]
	| fun_vbinop__case_4 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_92 : lane_) => ((proj_lane__2 lane_1_92) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_14 : lane_) => ((proj_lane__2 lane_2_14) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_92 : lane_) (lane_2_14 : lane_) => (mk_lane__2 Jnn_I32 (isub_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_92))) (!((proj_lane__2 lane_2_14)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_93 : lane_) => ((proj_lane__2 lane_1_93) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_15 : lane_) => ((proj_lane__2 lane_2_15) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_93 : lane_) (lane_2_15 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (isub_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_93))) (!((proj_lane__2 lane_2_15))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [::v128]
	| fun_vbinop__case_5 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_95 : lane_) => ((proj_lane__2 lane_1_95) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_17 : lane_) => ((proj_lane__2 lane_2_17) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_95 : lane_) (lane_2_17 : lane_) => (mk_lane__2 Jnn_I64 (isub_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_95))) (!((proj_lane__2 lane_2_17)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_96 : lane_) => ((proj_lane__2 lane_1_96) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_18 : lane_) => ((proj_lane__2 lane_2_18) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_96 : lane_) (lane_2_18 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (isub_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_96))) (!((proj_lane__2 lane_2_18))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [::v128]
	| fun_vbinop__case_6 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_98 : lane_) => ((proj_lane__2 lane_1_98) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_20 : lane_) => ((proj_lane__2 lane_2_20) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_98 : lane_) (lane_2_20 : lane_) => (mk_lane__2 Jnn_I8 (isub_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_98))) (!((proj_lane__2 lane_2_20)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_99 : lane_) => ((proj_lane__2 lane_1_99) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_21 : lane_) => ((proj_lane__2 lane_2_21) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_99 : lane_) (lane_2_21 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (isub_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_99))) (!((proj_lane__2 lane_2_21))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [::v128]
	| fun_vbinop__case_7 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_101 : lane_) => ((proj_lane__2 lane_1_101) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_23 : lane_) => ((proj_lane__2 lane_2_23) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_101 : lane_) (lane_2_23 : lane_) => (mk_lane__2 Jnn_I16 (isub_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_101))) (!((proj_lane__2 lane_2_23)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_102 : lane_) => ((proj_lane__2 lane_1_102) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_24 : lane_) => ((proj_lane__2 lane_2_24) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_102 : lane_) (lane_2_24 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (isub_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_102))) (!((proj_lane__2 lane_2_24))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [::v128]
	| fun_vbinop__case_8 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_105 : lane_) => ((proj_lane__2 lane_1_105) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_27 : lane_) => ((proj_lane__2 lane_2_27) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_105 : lane_) (lane_2_27 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_105))) (!((proj_lane__2 lane_2_27))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_104 : lane_) => ((proj_lane__2 lane_1_104) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_26 : lane_) => ((proj_lane__2 lane_2_26) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_104 : lane_) (lane_2_26 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_104))) (!((proj_lane__2 lane_2_26))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_9 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_108 : lane_) => ((proj_lane__2 lane_1_108) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_30 : lane_) => ((proj_lane__2 lane_2_30) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_108 : lane_) (lane_2_30 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_108))) (!((proj_lane__2 lane_2_30))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_107 : lane_) => ((proj_lane__2 lane_1_107) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_29 : lane_) => ((proj_lane__2 lane_2_29) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_107 : lane_) (lane_2_29 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_107))) (!((proj_lane__2 lane_2_29))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_10 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_111 : lane_) => ((proj_lane__2 lane_1_111) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_33 : lane_) => ((proj_lane__2 lane_2_33) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_111 : lane_) (lane_2_33 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_111))) (!((proj_lane__2 lane_2_33))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_110 : lane_) => ((proj_lane__2 lane_1_110) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_32 : lane_) => ((proj_lane__2 lane_2_32) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_110 : lane_) (lane_2_32 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_110))) (!((proj_lane__2 lane_2_32))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_11 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_114 : lane_) => ((proj_lane__2 lane_1_114) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_36 : lane_) => ((proj_lane__2 lane_2_36) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_114 : lane_) (lane_2_36 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_114))) (!((proj_lane__2 lane_2_36))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_113 : lane_) => ((proj_lane__2 lane_1_113) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_35 : lane_) => ((proj_lane__2 lane_2_35) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_113 : lane_) (lane_2_35 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_113))) (!((proj_lane__2 lane_2_35))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_12 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_117 : lane_) => ((proj_lane__2 lane_1_117) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_39 : lane_) => ((proj_lane__2 lane_2_39) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_117 : lane_) (lane_2_39 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_117))) (!((proj_lane__2 lane_2_39))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_116 : lane_) => ((proj_lane__2 lane_1_116) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_38 : lane_) => ((proj_lane__2 lane_2_38) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_116 : lane_) (lane_2_38 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_116))) (!((proj_lane__2 lane_2_38))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_13 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_120 : lane_) => ((proj_lane__2 lane_1_120) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_42 : lane_) => ((proj_lane__2 lane_2_42) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_120 : lane_) (lane_2_42 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_120))) (!((proj_lane__2 lane_2_42))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_119 : lane_) => ((proj_lane__2 lane_1_119) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_41 : lane_) => ((proj_lane__2 lane_2_41) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_119 : lane_) (lane_2_41 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_119))) (!((proj_lane__2 lane_2_41))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_14 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_123 : lane_) => ((proj_lane__2 lane_1_123) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_45 : lane_) => ((proj_lane__2 lane_2_45) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_123 : lane_) (lane_2_45 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_123))) (!((proj_lane__2 lane_2_45))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_122 : lane_) => ((proj_lane__2 lane_1_122) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_44 : lane_) => ((proj_lane__2 lane_2_44) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_122 : lane_) (lane_2_44 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_122))) (!((proj_lane__2 lane_2_44))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_15 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_126 : lane_) => ((proj_lane__2 lane_1_126) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_48 : lane_) => ((proj_lane__2 lane_2_48) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_126 : lane_) (lane_2_48 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_126))) (!((proj_lane__2 lane_2_48))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_125 : lane_) => ((proj_lane__2 lane_1_125) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_47 : lane_) => ((proj_lane__2 lane_2_47) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_125 : lane_) (lane_2_47 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_125))) (!((proj_lane__2 lane_2_47))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_16 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_129 : lane_) => ((proj_lane__2 lane_1_129) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_51 : lane_) => ((proj_lane__2 lane_2_51) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_129 : lane_) (lane_2_51 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_129))) (!((proj_lane__2 lane_2_51))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_128 : lane_) => ((proj_lane__2 lane_1_128) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_50 : lane_) => ((proj_lane__2 lane_2_50) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_128 : lane_) (lane_2_50 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_128))) (!((proj_lane__2 lane_2_50))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_17 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_132 : lane_) => ((proj_lane__2 lane_1_132) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_54 : lane_) => ((proj_lane__2 lane_2_54) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_132 : lane_) (lane_2_54 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_132))) (!((proj_lane__2 lane_2_54))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_131 : lane_) => ((proj_lane__2 lane_1_131) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_53 : lane_) => ((proj_lane__2 lane_2_53) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_131 : lane_) (lane_2_53 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_131))) (!((proj_lane__2 lane_2_53))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_18 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_135 : lane_) => ((proj_lane__2 lane_1_135) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_57 : lane_) => ((proj_lane__2 lane_2_57) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_135 : lane_) (lane_2_57 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_135))) (!((proj_lane__2 lane_2_57))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_134 : lane_) => ((proj_lane__2 lane_1_134) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_56 : lane_) => ((proj_lane__2 lane_2_56) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_134 : lane_) (lane_2_56 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_134))) (!((proj_lane__2 lane_2_56))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_19 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_138 : lane_) => ((proj_lane__2 lane_1_138) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_60 : lane_) => ((proj_lane__2 lane_2_60) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_138 : lane_) (lane_2_60 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_138))) (!((proj_lane__2 lane_2_60))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_137 : lane_) => ((proj_lane__2 lane_1_137) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_59 : lane_) => ((proj_lane__2 lane_2_59) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_137 : lane_) (lane_2_59 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_137))) (!((proj_lane__2 lane_2_59))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_20 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_141 : lane_) => ((proj_lane__2 lane_1_141) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_63 : lane_) => ((proj_lane__2 lane_2_63) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_141 : lane_) (lane_2_63 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_141))) (!((proj_lane__2 lane_2_63))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_140 : lane_) => ((proj_lane__2 lane_1_140) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_62 : lane_) => ((proj_lane__2 lane_2_62) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_140 : lane_) (lane_2_62 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_140))) (!((proj_lane__2 lane_2_62))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_21 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_144 : lane_) => ((proj_lane__2 lane_1_144) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_66 : lane_) => ((proj_lane__2 lane_2_66) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_144 : lane_) (lane_2_66 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_144))) (!((proj_lane__2 lane_2_66))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_143 : lane_) => ((proj_lane__2 lane_1_143) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_65 : lane_) => ((proj_lane__2 lane_2_65) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_143 : lane_) (lane_2_65 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_143))) (!((proj_lane__2 lane_2_65))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_22 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_147 : lane_) => ((proj_lane__2 lane_1_147) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_69 : lane_) => ((proj_lane__2 lane_2_69) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_147 : lane_) (lane_2_69 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_147))) (!((proj_lane__2 lane_2_69))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_146 : lane_) => ((proj_lane__2 lane_1_146) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_68 : lane_) => ((proj_lane__2 lane_2_68) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_146 : lane_) (lane_2_68 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_146))) (!((proj_lane__2 lane_2_68))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_23 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_150 : lane_) => ((proj_lane__2 lane_1_150) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_72 : lane_) => ((proj_lane__2 lane_2_72) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_150 : lane_) (lane_2_72 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_150))) (!((proj_lane__2 lane_2_72))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_149 : lane_) => ((proj_lane__2 lane_1_149) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_71 : lane_) => ((proj_lane__2 lane_2_71) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_149 : lane_) (lane_2_71 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_149))) (!((proj_lane__2 lane_2_71))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_0 : uN) => (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_24 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_152 : lane_) => ((proj_lane__2 lane_1_152) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_74 : lane_) => ((proj_lane__2 lane_2_74) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_152 : lane_) (lane_2_74 : lane_) => (mk_lane__2 Jnn_I32 (imul_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_152))) (!((proj_lane__2 lane_2_74)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_153 : lane_) => ((proj_lane__2 lane_1_153) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_75 : lane_) => ((proj_lane__2 lane_2_75) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_153 : lane_) (lane_2_75 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (imul_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_153))) (!((proj_lane__2 lane_2_75))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [::v128]
	| fun_vbinop__case_25 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_155 : lane_) => ((proj_lane__2 lane_1_155) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_77 : lane_) => ((proj_lane__2 lane_2_77) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_155 : lane_) (lane_2_77 : lane_) => (mk_lane__2 Jnn_I64 (imul_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_155))) (!((proj_lane__2 lane_2_77)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_156 : lane_) => ((proj_lane__2 lane_1_156) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_78 : lane_) => ((proj_lane__2 lane_2_78) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_156 : lane_) (lane_2_78 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (imul_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_156))) (!((proj_lane__2 lane_2_78))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [::v128]
	| fun_vbinop__case_26 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_158 : lane_) => ((proj_lane__2 lane_1_158) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_80 : lane_) => ((proj_lane__2 lane_2_80) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_158 : lane_) (lane_2_80 : lane_) => (mk_lane__2 Jnn_I8 (imul_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_158))) (!((proj_lane__2 lane_2_80)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_159 : lane_) => ((proj_lane__2 lane_1_159) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_81 : lane_) => ((proj_lane__2 lane_2_81) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_159 : lane_) (lane_2_81 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (imul_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_159))) (!((proj_lane__2 lane_2_81))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [::v128]
	| fun_vbinop__case_27 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_161 : lane_) => ((proj_lane__2 lane_1_161) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_83 : lane_) => ((proj_lane__2 lane_2_83) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_161 : lane_) (lane_2_83 : lane_) => (mk_lane__2 Jnn_I16 (imul_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_161))) (!((proj_lane__2 lane_2_83)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_162 : lane_) => ((proj_lane__2 lane_1_162) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_84 : lane_) => ((proj_lane__2 lane_2_84) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_162 : lane_) (lane_2_84 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (imul_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_162))) (!((proj_lane__2 lane_2_84))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [::v128]
	| fun_vbinop__case_28 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_164 : lane_) => ((proj_lane__2 lane_1_164) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_86 : lane_) => ((proj_lane__2 lane_2_86) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_164 : lane_) (lane_2_86 : lane_) => (mk_lane__2 Jnn_I32 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I32)) U (!((proj_lane__2 lane_1_164))) (!((proj_lane__2 lane_2_86)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_165 : lane_) => ((proj_lane__2 lane_1_165) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_87 : lane_) => ((proj_lane__2 lane_2_87) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_165 : lane_) (lane_2_87 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I32)) U (!((proj_lane__2 lane_1_165))) (!((proj_lane__2 lane_2_87))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 AVGRU) v128_1 v128_2 [::v128]
	| fun_vbinop__case_29 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_167 : lane_) => ((proj_lane__2 lane_1_167) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_89 : lane_) => ((proj_lane__2 lane_2_89) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_167 : lane_) (lane_2_89 : lane_) => (mk_lane__2 Jnn_I64 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I64)) U (!((proj_lane__2 lane_1_167))) (!((proj_lane__2 lane_2_89)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_168 : lane_) => ((proj_lane__2 lane_1_168) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_90 : lane_) => ((proj_lane__2 lane_2_90) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_168 : lane_) (lane_2_90 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I64)) U (!((proj_lane__2 lane_1_168))) (!((proj_lane__2 lane_2_90))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 AVGRU) v128_1 v128_2 [::v128]
	| fun_vbinop__case_30 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_170 : lane_) => ((proj_lane__2 lane_1_170) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_92 : lane_) => ((proj_lane__2 lane_2_92) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_170 : lane_) (lane_2_92 : lane_) => (mk_lane__2 Jnn_I8 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I8)) U (!((proj_lane__2 lane_1_170))) (!((proj_lane__2 lane_2_92)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_171 : lane_) => ((proj_lane__2 lane_1_171) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_93 : lane_) => ((proj_lane__2 lane_2_93) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_171 : lane_) (lane_2_93 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I8)) U (!((proj_lane__2 lane_1_171))) (!((proj_lane__2 lane_2_93))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 AVGRU) v128_1 v128_2 [::v128]
	| fun_vbinop__case_31 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_173 : lane_) => ((proj_lane__2 lane_1_173) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_95 : lane_) => ((proj_lane__2 lane_2_95) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_173 : lane_) (lane_2_95 : lane_) => (mk_lane__2 Jnn_I16 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I16)) U (!((proj_lane__2 lane_1_173))) (!((proj_lane__2 lane_2_95)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_174 : lane_) => ((proj_lane__2 lane_1_174) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_96 : lane_) => ((proj_lane__2 lane_2_96) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_174 : lane_) (lane_2_96 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I16)) U (!((proj_lane__2 lane_1_174))) (!((proj_lane__2 lane_2_96))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 AVGRU) v128_1 v128_2 [::v128]
	| fun_vbinop__case_32 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_176 : lane_) => ((proj_lane__2 lane_1_176) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_98 : lane_) => ((proj_lane__2 lane_2_98) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_176 : lane_) (lane_2_98 : lane_) => (mk_lane__2 Jnn_I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) res_S (!((proj_lane__2 lane_1_176))) (!((proj_lane__2 lane_2_98)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_177 : lane_) => ((proj_lane__2 lane_1_177) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_99 : lane_) => ((proj_lane__2 lane_2_99) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_177 : lane_) (lane_2_99 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) res_S (!((proj_lane__2 lane_1_177))) (!((proj_lane__2 lane_2_99))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 Q15MULR_SATS) v128_1 v128_2 [::v128]
	| fun_vbinop__case_33 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_179 : lane_) => ((proj_lane__2 lane_1_179) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_101 : lane_) => ((proj_lane__2 lane_2_101) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_179 : lane_) (lane_2_101 : lane_) => (mk_lane__2 Jnn_I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) res_S (!((proj_lane__2 lane_1_179))) (!((proj_lane__2 lane_2_101)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_180 : lane_) => ((proj_lane__2 lane_1_180) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_102 : lane_) => ((proj_lane__2 lane_2_102) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_180 : lane_) (lane_2_102 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) res_S (!((proj_lane__2 lane_1_180))) (!((proj_lane__2 lane_2_102))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 Q15MULR_SATS) v128_1 v128_2 [::v128]
	| fun_vbinop__case_34 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_182 : lane_) => ((proj_lane__2 lane_1_182) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_104 : lane_) => ((proj_lane__2 lane_2_104) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_182 : lane_) (lane_2_104 : lane_) => (mk_lane__2 Jnn_I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) res_S (!((proj_lane__2 lane_1_182))) (!((proj_lane__2 lane_2_104)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_183 : lane_) => ((proj_lane__2 lane_1_183) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_105 : lane_) => ((proj_lane__2 lane_2_105) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_183 : lane_) (lane_2_105 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) res_S (!((proj_lane__2 lane_1_183))) (!((proj_lane__2 lane_2_105))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 Q15MULR_SATS) v128_1 v128_2 [::v128]
	| fun_vbinop__case_35 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_185 : lane_) => ((proj_lane__2 lane_1_185) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_107 : lane_) => ((proj_lane__2 lane_2_107) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_185 : lane_) (lane_2_107 : lane_) => (mk_lane__2 Jnn_I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) res_S (!((proj_lane__2 lane_1_185))) (!((proj_lane__2 lane_2_107)))))) lane_1_lst lane_2_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_186 : lane_) => ((proj_lane__2 lane_1_186) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_108 : lane_) => ((proj_lane__2 lane_2_108) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_186 : lane_) (lane_2_108 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) res_S (!((proj_lane__2 lane_1_186))) (!((proj_lane__2 lane_2_108))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 Q15MULR_SATS) v128_1 v128_2 [::v128]
	| fun_vbinop__case_36 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_188 : lane_) (lane_2_110 : lane_) => (seq.map (fun (iter_0_77 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_77))) (fadd_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_188)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_110))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_30 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_30)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_189 : lane_) (lane_2_111 : lane_) => List.Forall (fun (iter_0_78 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_78)))) (fadd_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_189)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_111)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_ADD) v128_1 v128_2 v128_lst
	| fun_vbinop__case_37 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_191 : lane_) (lane_2_113 : lane_) => (seq.map (fun (iter_0_79 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_79))) (fadd_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_191)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_113))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_32 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_32)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_192 : lane_) (lane_2_114 : lane_) => List.Forall (fun (iter_0_80 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_80)))) (fadd_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_192)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_114)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_ADD) v128_1 v128_2 v128_lst
	| fun_vbinop__case_38 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_194 : lane_) (lane_2_116 : lane_) => (seq.map (fun (iter_0_81 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_81))) (fsub_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_194)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_116))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_34 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_34)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_195 : lane_) (lane_2_117 : lane_) => List.Forall (fun (iter_0_82 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_82)))) (fsub_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_195)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_117)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_SUB) v128_1 v128_2 v128_lst
	| fun_vbinop__case_39 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_197 : lane_) (lane_2_119 : lane_) => (seq.map (fun (iter_0_83 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_83))) (fsub_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_197)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_119))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_36 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_36)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_198 : lane_) (lane_2_120 : lane_) => List.Forall (fun (iter_0_84 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_84)))) (fsub_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_198)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_120)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_SUB) v128_1 v128_2 v128_lst
	| fun_vbinop__case_40 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_200 : lane_) (lane_2_122 : lane_) => (seq.map (fun (iter_0_85 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_85))) (fmul_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_200)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_122))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_38 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_38)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_201 : lane_) (lane_2_123 : lane_) => List.Forall (fun (iter_0_86 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_86)))) (fmul_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_201)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_123)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MUL) v128_1 v128_2 v128_lst
	| fun_vbinop__case_41 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_203 : lane_) (lane_2_125 : lane_) => (seq.map (fun (iter_0_87 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_87))) (fmul_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_203)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_125))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_40 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_40)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_204 : lane_) (lane_2_126 : lane_) => List.Forall (fun (iter_0_88 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_88)))) (fmul_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_204)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_126)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MUL) v128_1 v128_2 v128_lst
	| fun_vbinop__case_42 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_206 : lane_) (lane_2_128 : lane_) => (seq.map (fun (iter_0_89 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_89))) (fdiv_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_206)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_128))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_42 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_42)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_207 : lane_) (lane_2_129 : lane_) => List.Forall (fun (iter_0_90 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_90)))) (fdiv_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_207)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_129)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_DIV) v128_1 v128_2 v128_lst
	| fun_vbinop__case_43 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_209 : lane_) (lane_2_131 : lane_) => (seq.map (fun (iter_0_91 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_91))) (fdiv_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_209)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_131))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_44 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_44)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_210 : lane_) (lane_2_132 : lane_) => List.Forall (fun (iter_0_92 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_92)))) (fdiv_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_210)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_132)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_DIV) v128_1 v128_2 v128_lst
	| fun_vbinop__case_44 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_212 : lane_) (lane_2_134 : lane_) => (seq.map (fun (iter_0_93 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_93))) (fmin_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_212)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_134))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_46 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_46)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_213 : lane_) (lane_2_135 : lane_) => List.Forall (fun (iter_0_94 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_94)))) (fmin_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_213)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_135)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MIN) v128_1 v128_2 v128_lst
	| fun_vbinop__case_45 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_215 : lane_) (lane_2_137 : lane_) => (seq.map (fun (iter_0_95 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_95))) (fmin_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_215)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_137))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_48 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_48)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_216 : lane_) (lane_2_138 : lane_) => List.Forall (fun (iter_0_96 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_96)))) (fmin_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_216)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_138)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MIN) v128_1 v128_2 v128_lst
	| fun_vbinop__case_46 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_218 : lane_) (lane_2_140 : lane_) => (seq.map (fun (iter_0_97 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_97))) (fmax_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_218)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_140))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_50 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_50)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_219 : lane_) (lane_2_141 : lane_) => List.Forall (fun (iter_0_98 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_98)))) (fmax_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_219)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_141)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MAX) v128_1 v128_2 v128_lst
	| fun_vbinop__case_47 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_221 : lane_) (lane_2_143 : lane_) => (seq.map (fun (iter_0_99 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_99))) (fmax_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_221)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_143))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_52 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_52)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_222 : lane_) (lane_2_144 : lane_) => List.Forall (fun (iter_0_100 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_100)))) (fmax_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_222)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_144)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MAX) v128_1 v128_2 v128_lst
	| fun_vbinop__case_48 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_224 : lane_) (lane_2_146 : lane_) => (seq.map (fun (iter_0_101 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_101))) (fpmin_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_224)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_146))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_54 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_54)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_225 : lane_) (lane_2_147 : lane_) => List.Forall (fun (iter_0_102 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_102)))) (fpmin_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_225)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_147)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 PMIN) v128_1 v128_2 v128_lst
	| fun_vbinop__case_49 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_227 : lane_) (lane_2_149 : lane_) => (seq.map (fun (iter_0_103 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_103))) (fpmin_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_227)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_149))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_56 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_56)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_228 : lane_) (lane_2_150 : lane_) => List.Forall (fun (iter_0_104 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_104)))) (fpmin_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_228)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_150)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 PMIN) v128_1 v128_2 v128_lst
	| fun_vbinop__case_50 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_230 : lane_) (lane_2_152 : lane_) => (seq.map (fun (iter_0_105 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_105))) (fpmax_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_230)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_152))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_58 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_58)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_231 : lane_) (lane_2_153 : lane_) => List.Forall (fun (iter_0_106 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_106)))) (fpmax_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_231)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_153)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 PMAX) v128_1 v128_2 v128_lst
	| fun_vbinop__case_51 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))) (v128_lst : (seq vec_)), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_233 : lane_) (lane_2_155 : lane_) => (seq.map (fun (iter_0_107 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_107))) (fpmax_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_233)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_155))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_60 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_60)) lane_lst_lst)) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_234 : lane_) (lane_2_156 : lane_) => List.Forall (fun (iter_0_108 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_108)))) (fpmax_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_234)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_156)))))))) lane_1_lst lane_2_lst ->
		(v_M == M_0) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 PMAX) v128_1 v128_2 v128_lst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 *)
Lemma vbinop__is_wf : forall (v_shape : shape) (v_vbinop_ : vbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : (seq vec_)) (var_0 : (seq vec_)),
	(fun_vbinop_ v_shape v_vbinop_ v_vec_ vec__0 var_0) ->
	(wf_shape v_shape) ->
	(wf_vbinop_ v_shape v_vbinop_) ->
	(wf_uN 128 v_vec_) ->
	(wf_uN 128 vec__0) ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst.
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
Inductive fun_vrelop_ : shape -> vrelop_ -> vec_ -> vec_ -> vec_ -> Prop :=
	| fun_vrelop__case_0 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_236 : lane_) => ((proj_lane__2 lane_1_236) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_158 : lane_) => ((proj_lane__2 lane_2_158) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_236 : lane_) (lane_2_158 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_236))) (!((proj_lane__2 lane_2_158)))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_2 : iN) => (mk_lane__2 Jnn_I32 lane_3_2)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_237 : lane_) => ((proj_lane__2 lane_1_237) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_159 : lane_) => ((proj_lane__2 lane_2_159) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_237 : lane_) (lane_2_159 : lane_) => (wf_uN 1 (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_237))) (!((proj_lane__2 lane_2_159)))) :> (nat))))) lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_3_3 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_3))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_1 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_239 : lane_) => ((proj_lane__2 lane_1_239) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_161 : lane_) => ((proj_lane__2 lane_2_161) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_239 : lane_) (lane_2_161 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_239))) (!((proj_lane__2 lane_2_161)))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_5 : iN) => (mk_lane__2 Jnn_I64 lane_3_5)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_240 : lane_) => ((proj_lane__2 lane_1_240) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_162 : lane_) => ((proj_lane__2 lane_2_162) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_240 : lane_) (lane_2_162 : lane_) => (wf_uN 1 (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_240))) (!((proj_lane__2 lane_2_162)))) :> (nat))))) lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_3_6 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_6))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_2 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_242 : lane_) => ((proj_lane__2 lane_1_242) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_164 : lane_) => ((proj_lane__2 lane_2_164) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_242 : lane_) (lane_2_164 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_242))) (!((proj_lane__2 lane_2_164)))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_8 : iN) => (mk_lane__2 Jnn_I8 lane_3_8)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_243 : lane_) => ((proj_lane__2 lane_1_243) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_165 : lane_) => ((proj_lane__2 lane_2_165) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_243 : lane_) (lane_2_165 : lane_) => (wf_uN 1 (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_243))) (!((proj_lane__2 lane_2_165)))) :> (nat))))) lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_3_9 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_9))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_3 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_245 : lane_) => ((proj_lane__2 lane_1_245) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_167 : lane_) => ((proj_lane__2 lane_2_167) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_245 : lane_) (lane_2_167 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_245))) (!((proj_lane__2 lane_2_167)))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_11 : iN) => (mk_lane__2 Jnn_I16 lane_3_11)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_246 : lane_) => ((proj_lane__2 lane_1_246) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_168 : lane_) => ((proj_lane__2 lane_2_168) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_246 : lane_) (lane_2_168 : lane_) => (wf_uN 1 (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_246))) (!((proj_lane__2 lane_2_168)))) :> (nat))))) lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_3_12 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_12))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_4 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_248 : lane_) => ((proj_lane__2 lane_1_248) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_170 : lane_) => ((proj_lane__2 lane_2_170) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_248 : lane_) (lane_2_170 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_248))) (!((proj_lane__2 lane_2_170)))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_14 : iN) => (mk_lane__2 Jnn_I32 lane_3_14)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_249 : lane_) => ((proj_lane__2 lane_1_249) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_171 : lane_) => ((proj_lane__2 lane_2_171) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_249 : lane_) (lane_2_171 : lane_) => (wf_uN 1 (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_249))) (!((proj_lane__2 lane_2_171)))) :> (nat))))) lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_3_15 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_15))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_5 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_251 : lane_) => ((proj_lane__2 lane_1_251) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_173 : lane_) => ((proj_lane__2 lane_2_173) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_251 : lane_) (lane_2_173 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_251))) (!((proj_lane__2 lane_2_173)))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_17 : iN) => (mk_lane__2 Jnn_I64 lane_3_17)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_252 : lane_) => ((proj_lane__2 lane_1_252) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_174 : lane_) => ((proj_lane__2 lane_2_174) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_252 : lane_) (lane_2_174 : lane_) => (wf_uN 1 (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_252))) (!((proj_lane__2 lane_2_174)))) :> (nat))))) lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_3_18 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_18))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_6 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_254 : lane_) => ((proj_lane__2 lane_1_254) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_176 : lane_) => ((proj_lane__2 lane_2_176) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_254 : lane_) (lane_2_176 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_254))) (!((proj_lane__2 lane_2_176)))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_20 : iN) => (mk_lane__2 Jnn_I8 lane_3_20)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_255 : lane_) => ((proj_lane__2 lane_1_255) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_177 : lane_) => ((proj_lane__2 lane_2_177) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_255 : lane_) (lane_2_177 : lane_) => (wf_uN 1 (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_255))) (!((proj_lane__2 lane_2_177)))) :> (nat))))) lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_3_21 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_21))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_7 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_257 : lane_) => ((proj_lane__2 lane_1_257) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_179 : lane_) => ((proj_lane__2 lane_2_179) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_257 : lane_) (lane_2_179 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_257))) (!((proj_lane__2 lane_2_179)))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_23 : iN) => (mk_lane__2 Jnn_I16 lane_3_23)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_258 : lane_) => ((proj_lane__2 lane_1_258) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_180 : lane_) => ((proj_lane__2 lane_2_180) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_258 : lane_) (lane_2_180 : lane_) => (wf_uN 1 (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_258))) (!((proj_lane__2 lane_2_180)))) :> (nat))))) lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_3_24 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_24))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_8 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_261 : lane_) => ((proj_lane__2 lane_1_261) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_183 : lane_) => ((proj_lane__2 lane_2_183) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_261 : lane_) (lane_2_183 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_261))) (!((proj_lane__2 lane_2_183))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_260 : lane_) => ((proj_lane__2 lane_1_260) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_182 : lane_) => ((proj_lane__2 lane_2_182) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_260 : lane_) (lane_2_182 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_260))) (!((proj_lane__2 lane_2_182))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_26 : iN) => (mk_lane__2 Jnn_I32 lane_3_26)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_27 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_27))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_9 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_264 : lane_) => ((proj_lane__2 lane_1_264) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_186 : lane_) => ((proj_lane__2 lane_2_186) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_264 : lane_) (lane_2_186 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_264))) (!((proj_lane__2 lane_2_186))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_263 : lane_) => ((proj_lane__2 lane_1_263) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_185 : lane_) => ((proj_lane__2 lane_2_185) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_263 : lane_) (lane_2_185 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_263))) (!((proj_lane__2 lane_2_185))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_29 : iN) => (mk_lane__2 Jnn_I64 lane_3_29)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_30 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_30))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_10 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_267 : lane_) => ((proj_lane__2 lane_1_267) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_189 : lane_) => ((proj_lane__2 lane_2_189) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_267 : lane_) (lane_2_189 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_267))) (!((proj_lane__2 lane_2_189))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_266 : lane_) => ((proj_lane__2 lane_1_266) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_188 : lane_) => ((proj_lane__2 lane_2_188) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_266 : lane_) (lane_2_188 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_266))) (!((proj_lane__2 lane_2_188))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_32 : iN) => (mk_lane__2 Jnn_I8 lane_3_32)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_33 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_33))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_11 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_270 : lane_) => ((proj_lane__2 lane_1_270) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_192 : lane_) => ((proj_lane__2 lane_2_192) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_270 : lane_) (lane_2_192 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_270))) (!((proj_lane__2 lane_2_192))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_269 : lane_) => ((proj_lane__2 lane_1_269) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_191 : lane_) => ((proj_lane__2 lane_2_191) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_269 : lane_) (lane_2_191 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_269))) (!((proj_lane__2 lane_2_191))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_35 : iN) => (mk_lane__2 Jnn_I16 lane_3_35)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_36 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_36))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_12 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_273 : lane_) => ((proj_lane__2 lane_1_273) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_195 : lane_) => ((proj_lane__2 lane_2_195) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_273 : lane_) (lane_2_195 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_273))) (!((proj_lane__2 lane_2_195))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_272 : lane_) => ((proj_lane__2 lane_1_272) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_194 : lane_) => ((proj_lane__2 lane_2_194) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_272 : lane_) (lane_2_194 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_272))) (!((proj_lane__2 lane_2_194))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_38 : iN) => (mk_lane__2 Jnn_I32 lane_3_38)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_39 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_39))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_13 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_276 : lane_) => ((proj_lane__2 lane_1_276) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_198 : lane_) => ((proj_lane__2 lane_2_198) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_276 : lane_) (lane_2_198 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_276))) (!((proj_lane__2 lane_2_198))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_275 : lane_) => ((proj_lane__2 lane_1_275) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_197 : lane_) => ((proj_lane__2 lane_2_197) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_275 : lane_) (lane_2_197 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_275))) (!((proj_lane__2 lane_2_197))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_41 : iN) => (mk_lane__2 Jnn_I64 lane_3_41)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_42 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_42))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_14 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_279 : lane_) => ((proj_lane__2 lane_1_279) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_201 : lane_) => ((proj_lane__2 lane_2_201) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_279 : lane_) (lane_2_201 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_279))) (!((proj_lane__2 lane_2_201))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_278 : lane_) => ((proj_lane__2 lane_1_278) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_200 : lane_) => ((proj_lane__2 lane_2_200) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_278 : lane_) (lane_2_200 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_278))) (!((proj_lane__2 lane_2_200))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_44 : iN) => (mk_lane__2 Jnn_I8 lane_3_44)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_45 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_45))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_15 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_282 : lane_) => ((proj_lane__2 lane_1_282) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_204 : lane_) => ((proj_lane__2 lane_2_204) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_282 : lane_) (lane_2_204 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_282))) (!((proj_lane__2 lane_2_204))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_281 : lane_) => ((proj_lane__2 lane_1_281) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_203 : lane_) => ((proj_lane__2 lane_2_203) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_281 : lane_) (lane_2_203 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_281))) (!((proj_lane__2 lane_2_203))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_47 : iN) => (mk_lane__2 Jnn_I16 lane_3_47)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_48 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_48))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_16 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_285 : lane_) => ((proj_lane__2 lane_1_285) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_207 : lane_) => ((proj_lane__2 lane_2_207) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_285 : lane_) (lane_2_207 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_285))) (!((proj_lane__2 lane_2_207))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_284 : lane_) => ((proj_lane__2 lane_1_284) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_206 : lane_) => ((proj_lane__2 lane_2_206) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_284 : lane_) (lane_2_206 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_284))) (!((proj_lane__2 lane_2_206))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_50 : iN) => (mk_lane__2 Jnn_I32 lane_3_50)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_51 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_51))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_17 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_288 : lane_) => ((proj_lane__2 lane_1_288) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_210 : lane_) => ((proj_lane__2 lane_2_210) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_288 : lane_) (lane_2_210 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_288))) (!((proj_lane__2 lane_2_210))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_287 : lane_) => ((proj_lane__2 lane_1_287) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_209 : lane_) => ((proj_lane__2 lane_2_209) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_287 : lane_) (lane_2_209 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_287))) (!((proj_lane__2 lane_2_209))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_53 : iN) => (mk_lane__2 Jnn_I64 lane_3_53)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_54 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_54))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_18 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_291 : lane_) => ((proj_lane__2 lane_1_291) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_213 : lane_) => ((proj_lane__2 lane_2_213) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_291 : lane_) (lane_2_213 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_291))) (!((proj_lane__2 lane_2_213))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_290 : lane_) => ((proj_lane__2 lane_1_290) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_212 : lane_) => ((proj_lane__2 lane_2_212) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_290 : lane_) (lane_2_212 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_290))) (!((proj_lane__2 lane_2_212))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_56 : iN) => (mk_lane__2 Jnn_I8 lane_3_56)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_57 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_57))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_19 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_294 : lane_) => ((proj_lane__2 lane_1_294) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_216 : lane_) => ((proj_lane__2 lane_2_216) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_294 : lane_) (lane_2_216 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_294))) (!((proj_lane__2 lane_2_216))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_293 : lane_) => ((proj_lane__2 lane_1_293) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_215 : lane_) => ((proj_lane__2 lane_2_215) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_293 : lane_) (lane_2_215 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_293))) (!((proj_lane__2 lane_2_215))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_59 : iN) => (mk_lane__2 Jnn_I16 lane_3_59)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_60 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_60))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_20 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_297 : lane_) => ((proj_lane__2 lane_1_297) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_219 : lane_) => ((proj_lane__2 lane_2_219) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_297 : lane_) (lane_2_219 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_297))) (!((proj_lane__2 lane_2_219))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_296 : lane_) => ((proj_lane__2 lane_1_296) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_218 : lane_) => ((proj_lane__2 lane_2_218) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_296 : lane_) (lane_2_218 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_296))) (!((proj_lane__2 lane_2_218))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_62 : iN) => (mk_lane__2 Jnn_I32 lane_3_62)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_63 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_63))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_21 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_300 : lane_) => ((proj_lane__2 lane_1_300) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_222 : lane_) => ((proj_lane__2 lane_2_222) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_300 : lane_) (lane_2_222 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_300))) (!((proj_lane__2 lane_2_222))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_299 : lane_) => ((proj_lane__2 lane_1_299) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_221 : lane_) => ((proj_lane__2 lane_2_221) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_299 : lane_) (lane_2_221 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_299))) (!((proj_lane__2 lane_2_221))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_65 : iN) => (mk_lane__2 Jnn_I64 lane_3_65)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_66 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_66))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_22 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_303 : lane_) => ((proj_lane__2 lane_1_303) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_225 : lane_) => ((proj_lane__2 lane_2_225) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_303 : lane_) (lane_2_225 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_303))) (!((proj_lane__2 lane_2_225))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_302 : lane_) => ((proj_lane__2 lane_1_302) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_224 : lane_) => ((proj_lane__2 lane_2_224) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_302 : lane_) (lane_2_224 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_302))) (!((proj_lane__2 lane_2_224))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_68 : iN) => (mk_lane__2 Jnn_I8 lane_3_68)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_69 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_69))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_23 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_306 : lane_) => ((proj_lane__2 lane_1_306) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_228 : lane_) => ((proj_lane__2 lane_2_228) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_306 : lane_) (lane_2_228 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_306))) (!((proj_lane__2 lane_2_228))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_305 : lane_) => ((proj_lane__2 lane_1_305) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_227 : lane_) => ((proj_lane__2 lane_2_227) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_305 : lane_) (lane_2_227 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_305))) (!((proj_lane__2 lane_2_227))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN (var_0 :> (nat))))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_71 : iN) => (mk_lane__2 Jnn_I16 lane_3_71)) lane_3_lst))) ->
		(wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ->
		List.Forall (fun (var_1 : uN) => (wf_uN 1 (mk_uN (var_1 :> (nat))))) var_1_lst ->
		List.Forall (fun (lane_3_72 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_72))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_24 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_308 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_308)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_308 : lane_) => ((proj_lane__0 lane_1_308) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_230 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_230)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_230 : lane_) => ((proj_lane__0 lane_2_230) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_308 : lane_) (lane_2_230 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((feq_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_308)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_230))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_74 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_74 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_309 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_309)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_309 : lane_) => ((proj_lane__0 lane_1_309) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_231 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_231)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_231 : lane_) => ((proj_lane__0 lane_2_231) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_309 : lane_) (lane_2_231 : lane_) => (wf_uN 1 (mk_uN ((feq_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_309)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_231))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_75 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_75 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_25 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_311 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_311)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_311 : lane_) => ((proj_lane__0 lane_1_311) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_233 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_233)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_233 : lane_) => ((proj_lane__0 lane_2_233) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_311 : lane_) (lane_2_233 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((feq_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_311)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_233))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_77 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_77 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_312 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_312)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_312 : lane_) => ((proj_lane__0 lane_1_312) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_234 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_234)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_234 : lane_) => ((proj_lane__0 lane_2_234) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_312 : lane_) (lane_2_234 : lane_) => (wf_uN 1 (mk_uN ((feq_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_312)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_234))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_78 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_78 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_26 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_314 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_314)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_314 : lane_) => ((proj_lane__0 lane_1_314) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_236 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_236)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_236 : lane_) => ((proj_lane__0 lane_2_236) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_314 : lane_) (lane_2_236 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((fne_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_314)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_236))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_80 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_80 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_315 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_315)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_315 : lane_) => ((proj_lane__0 lane_1_315) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_237 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_237)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_237 : lane_) => ((proj_lane__0 lane_2_237) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_315 : lane_) (lane_2_237 : lane_) => (wf_uN 1 (mk_uN ((fne_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_315)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_237))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_81 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_81 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_27 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_317 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_317)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_317 : lane_) => ((proj_lane__0 lane_1_317) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_239 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_239)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_239 : lane_) => ((proj_lane__0 lane_2_239) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_317 : lane_) (lane_2_239 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((fne_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_317)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_239))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_83 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_83 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_318 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_318)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_318 : lane_) => ((proj_lane__0 lane_1_318) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_240 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_240)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_240 : lane_) => ((proj_lane__0 lane_2_240) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_318 : lane_) (lane_2_240 : lane_) => (wf_uN 1 (mk_uN ((fne_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_318)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_240))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_84 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_84 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_28 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_320 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_320)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_320 : lane_) => ((proj_lane__0 lane_1_320) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_242 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_242)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_242 : lane_) => ((proj_lane__0 lane_2_242) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_320 : lane_) (lane_2_242 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((flt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_320)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_242))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_86 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_86 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_321 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_321)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_321 : lane_) => ((proj_lane__0 lane_1_321) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_243 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_243)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_243 : lane_) => ((proj_lane__0 lane_2_243) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_321 : lane_) (lane_2_243 : lane_) => (wf_uN 1 (mk_uN ((flt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_321)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_243))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_87 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_87 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_LT) v128_1 v128_2 v128
	| fun_vrelop__case_29 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_323 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_323)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_323 : lane_) => ((proj_lane__0 lane_1_323) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_245 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_245)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_245 : lane_) => ((proj_lane__0 lane_2_245) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_323 : lane_) (lane_2_245 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((flt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_323)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_245))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_89 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_89 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_324 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_324)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_324 : lane_) => ((proj_lane__0 lane_1_324) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_246 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_246)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_246 : lane_) => ((proj_lane__0 lane_2_246) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_324 : lane_) (lane_2_246 : lane_) => (wf_uN 1 (mk_uN ((flt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_324)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_246))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_90 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_90 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_LT) v128_1 v128_2 v128
	| fun_vrelop__case_30 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_326 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_326)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_326 : lane_) => ((proj_lane__0 lane_1_326) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_248 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_248)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_248 : lane_) => ((proj_lane__0 lane_2_248) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_326 : lane_) (lane_2_248 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((fgt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_326)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_248))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_92 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_92 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_327 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_327)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_327 : lane_) => ((proj_lane__0 lane_1_327) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_249 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_249)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_249 : lane_) => ((proj_lane__0 lane_2_249) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_327 : lane_) (lane_2_249 : lane_) => (wf_uN 1 (mk_uN ((fgt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_327)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_249))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_93 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_93 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_GT) v128_1 v128_2 v128
	| fun_vrelop__case_31 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_329 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_329)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_329 : lane_) => ((proj_lane__0 lane_1_329) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_251 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_251)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_251 : lane_) => ((proj_lane__0 lane_2_251) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_329 : lane_) (lane_2_251 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((fgt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_329)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_251))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_95 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_95 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_330 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_330)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_330 : lane_) => ((proj_lane__0 lane_1_330) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_252 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_252)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_252 : lane_) => ((proj_lane__0 lane_2_252) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_330 : lane_) (lane_2_252 : lane_) => (wf_uN 1 (mk_uN ((fgt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_330)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_252))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_96 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_96 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_GT) v128_1 v128_2 v128
	| fun_vrelop__case_32 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_332 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_332)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_332 : lane_) => ((proj_lane__0 lane_1_332) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_254 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_254)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_254 : lane_) => ((proj_lane__0 lane_2_254) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_332 : lane_) (lane_2_254 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((fle_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_332)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_254))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_98 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_98 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_333 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_333)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_333 : lane_) => ((proj_lane__0 lane_1_333) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_255 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_255)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_255 : lane_) => ((proj_lane__0 lane_2_255) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_333 : lane_) (lane_2_255 : lane_) => (wf_uN 1 (mk_uN ((fle_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_333)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_255))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_99 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_99 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_LE) v128_1 v128_2 v128
	| fun_vrelop__case_33 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_335 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_335)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_335 : lane_) => ((proj_lane__0 lane_1_335) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_257 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_257)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_257 : lane_) => ((proj_lane__0 lane_2_257) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_335 : lane_) (lane_2_257 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((fle_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_335)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_257))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_101 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_101 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_336 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_336)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_336 : lane_) => ((proj_lane__0 lane_1_336) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_258 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_258)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_258 : lane_) => ((proj_lane__0 lane_2_258) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_336 : lane_) (lane_2_258 : lane_) => (wf_uN 1 (mk_uN ((fle_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_336)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_258))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_102 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_102 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_LE) v128_1 v128_2 v128
	| fun_vrelop__case_34 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_338 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_338)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_338 : lane_) => ((proj_lane__0 lane_1_338) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_260 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_260)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_260 : lane_) => ((proj_lane__0 lane_2_260) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_338 : lane_) (lane_2_260 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((fge_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_338)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_260))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_104 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_104 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_339 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_339)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_339 : lane_) => ((proj_lane__0 lane_1_339) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_261 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_261)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_261 : lane_) => ((proj_lane__0 lane_2_261) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_339 : lane_) (lane_2_261 : lane_) => (wf_uN 1 (mk_uN ((fge_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_339)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_261))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_105 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_105 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_GE) v128_1 v128_2 v128
	| fun_vrelop__case_35 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : nat) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v128 : vec_), 
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_341 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_341)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_341 : lane_) => ((proj_lane__0 lane_1_341) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_263 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_263)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_263 : lane_) => ((proj_lane__0 lane_2_263) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_341 : lane_) (lane_2_263 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((fge_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_341)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_263))))))) :> (nat))))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_107 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_107 :> (nat)))))) lane_3_lst))) ->
		(wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_342 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_342)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_342 : lane_) => ((proj_lane__0 lane_1_342) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_264 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_264)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_264 : lane_) => ((proj_lane__0 lane_2_264) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_342 : lane_) (lane_2_264 : lane_) => (wf_uN 1 (mk_uN ((fge_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_342)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_264))))))) :> (nat))))) lane_1_lst lane_2_lst ->
		(wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ->
		List.Forall (fun (lane_3_108 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_108 :> (nat))))))) lane_3_lst ->
		(v_M == M_0) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_GE) v128_1 v128_2 v128.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
Lemma vrelop__is_wf : forall (v_shape : shape) (v_vrelop_ : vrelop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_),
	(fun_vrelop_ v_shape v_vrelop_ v_vec_ vec__0 var_0) ->
	(wf_shape v_shape) ->
	(wf_vrelop_ v_shape v_vrelop_) ->
	(wf_uN 128 v_vec_) ->
	(wf_uN 128 vec__0) ->
	(ret_val == var_0) ->
	(wf_uN 128 ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
Definition vcvtop__ (shape_1 : shape) (shape_2 : shape) (v_vcvtop : vcvtop) (v_lane_ : lane_) : (seq lane_) :=
	match shape_1, shape_2, v_vcvtop, v_lane_ return (seq lane_) with
		| (X lanetype_I32 (mk_dim M_1)), (X lanetype_I32 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I32 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I32 iN_2)]
		| (X lanetype_I64 (mk_dim M_1)), (X lanetype_I32 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I64 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I32 iN_2)]
		| (X lanetype_I8 (mk_dim M_1)), (X lanetype_I32 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I8 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I32 iN_2)]
		| (X lanetype_I16 (mk_dim M_1)), (X lanetype_I32 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I16 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I32 iN_2)]
		| (X lanetype_I32 (mk_dim M_1)), (X lanetype_I64 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I32 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I64 iN_2)]
		| (X lanetype_I64 (mk_dim M_1)), (X lanetype_I64 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I64 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I64 iN_2)]
		| (X lanetype_I8 (mk_dim M_1)), (X lanetype_I64 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I8 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I64 iN_2)]
		| (X lanetype_I16 (mk_dim M_1)), (X lanetype_I64 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I16 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I64 iN_2)]
		| (X lanetype_I32 (mk_dim M_1)), (X lanetype_I8 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I32 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I8 iN_2)]
		| (X lanetype_I64 (mk_dim M_1)), (X lanetype_I8 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I64 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I8 iN_2)]
		| (X lanetype_I8 (mk_dim M_1)), (X lanetype_I8 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I8 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I8 iN_2)]
		| (X lanetype_I16 (mk_dim M_1)), (X lanetype_I8 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I16 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I8 iN_2)]
		| (X lanetype_I32 (mk_dim M_1)), (X lanetype_I16 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I32 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I16 iN_2)]
		| (X lanetype_I64 (mk_dim M_1)), (X lanetype_I16 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I64 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I16 iN_2)]
		| (X lanetype_I8 (mk_dim M_1)), (X lanetype_I16 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I8 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I16 iN_2)]
		| (X lanetype_I16 (mk_dim M_1)), (X lanetype_I16 (mk_dim M_2)), (vcvtop_EXTEND v_half v_sx), (mk_lane__2 Jnn_I16 iN_1) => 
			let iN_2 := (extend__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1) in 
			[::(mk_lane__2 Jnn_I16 iN_2)]
		| (X lanetype_I32 (mk_dim M_1)), (X lanetype_F32 (mk_dim M_2)), (vcvtop_CONVERT half_opt v_sx), (mk_lane__2 Jnn_I32 iN_1) => 
			let fN_2 := (convert__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1) in 
			[::(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]
		| (X lanetype_I64 (mk_dim M_1)), (X lanetype_F32 (mk_dim M_2)), (vcvtop_CONVERT half_opt v_sx), (mk_lane__2 Jnn_I64 iN_1) => 
			let fN_2 := (convert__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1) in 
			[::(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]
		| (X lanetype_I8 (mk_dim M_1)), (X lanetype_F32 (mk_dim M_2)), (vcvtop_CONVERT half_opt v_sx), (mk_lane__2 Jnn_I8 iN_1) => 
			let fN_2 := (convert__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1) in 
			[::(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]
		| (X lanetype_I16 (mk_dim M_1)), (X lanetype_F32 (mk_dim M_2)), (vcvtop_CONVERT half_opt v_sx), (mk_lane__2 Jnn_I16 iN_1) => 
			let fN_2 := (convert__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1) in 
			[::(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]
		| (X lanetype_I32 (mk_dim M_1)), (X lanetype_F64 (mk_dim M_2)), (vcvtop_CONVERT half_opt v_sx), (mk_lane__2 Jnn_I32 iN_1) => 
			let fN_2 := (convert__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1) in 
			[::(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]
		| (X lanetype_I64 (mk_dim M_1)), (X lanetype_F64 (mk_dim M_2)), (vcvtop_CONVERT half_opt v_sx), (mk_lane__2 Jnn_I64 iN_1) => 
			let fN_2 := (convert__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1) in 
			[::(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]
		| (X lanetype_I8 (mk_dim M_1)), (X lanetype_F64 (mk_dim M_2)), (vcvtop_CONVERT half_opt v_sx), (mk_lane__2 Jnn_I8 iN_1) => 
			let fN_2 := (convert__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1) in 
			[::(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]
		| (X lanetype_I16 (mk_dim M_1)), (X lanetype_F64 (mk_dim M_2)), (vcvtop_CONVERT half_opt v_sx), (mk_lane__2 Jnn_I16 iN_1) => 
			let fN_2 := (convert__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1) in 
			[::(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]
		| (X lanetype_F32 (mk_dim M_1)), (X lanetype_I32 (mk_dim M_2)), (vcvtop_TRUNC_SAT v_sx zero_opt), (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) => 
			let iN_2_opt := (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1) in 
			(list_ lane_ (option_map (fun (iN_2_2 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_2))) iN_2_opt))
		| (X lanetype_F32 (mk_dim M_1)), (X lanetype_I64 (mk_dim M_2)), (vcvtop_TRUNC_SAT v_sx zero_opt), (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) => 
			let iN_2_opt := (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1) in 
			(list_ lane_ (option_map (fun (iN_2_4 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_4))) iN_2_opt))
		| (X lanetype_F64 (mk_dim M_1)), (X lanetype_I32 (mk_dim M_2)), (vcvtop_TRUNC_SAT v_sx zero_opt), (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) => 
			let iN_2_opt := (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1) in 
			(list_ lane_ (option_map (fun (iN_2_6 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_6))) iN_2_opt))
		| (X lanetype_F64 (mk_dim M_1)), (X lanetype_I64 (mk_dim M_2)), (vcvtop_TRUNC_SAT v_sx zero_opt), (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) => 
			let iN_2_opt := (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1) in 
			(list_ lane_ (option_map (fun (iN_2_8 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_8))) iN_2_opt))
		| (X lanetype_F32 (mk_dim M_1)), (X lanetype_F32 (mk_dim M_2)), (vcvtop_DEMOTE ZERO), (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) => 
			let fN_2_lst := (demote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) in 
			(seq.map (fun (fN_2_2 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_2))) fN_2_lst)
		| (X lanetype_F32 (mk_dim M_1)), (X lanetype_F64 (mk_dim M_2)), (vcvtop_DEMOTE ZERO), (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) => 
			let fN_2_lst := (demote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) in 
			(seq.map (fun (fN_2_4 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_4))) fN_2_lst)
		| (X lanetype_F64 (mk_dim M_1)), (X lanetype_F32 (mk_dim M_2)), (vcvtop_DEMOTE ZERO), (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) => 
			let fN_2_lst := (demote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) in 
			(seq.map (fun (fN_2_6 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_6))) fN_2_lst)
		| (X lanetype_F64 (mk_dim M_1)), (X lanetype_F64 (mk_dim M_2)), (vcvtop_DEMOTE ZERO), (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) => 
			let fN_2_lst := (demote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) in 
			(seq.map (fun (fN_2_8 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_8))) fN_2_lst)
		| (X lanetype_F32 (mk_dim M_1)), (X lanetype_F32 (mk_dim M_2)), PROMOTELOW, (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) => 
			let fN_2_lst := (promote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) in 
			(seq.map (fun (fN_2_10 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_10))) fN_2_lst)
		| (X lanetype_F32 (mk_dim M_1)), (X lanetype_F64 (mk_dim M_2)), PROMOTELOW, (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) => 
			let fN_2_lst := (promote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) in 
			(seq.map (fun (fN_2_12 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_12))) fN_2_lst)
		| (X lanetype_F64 (mk_dim M_1)), (X lanetype_F32 (mk_dim M_2)), PROMOTELOW, (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) => 
			let fN_2_lst := (promote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) in 
			(seq.map (fun (fN_2_14 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_14))) fN_2_lst)
		| (X lanetype_F64 (mk_dim M_1)), (X lanetype_F64 (mk_dim M_2)), PROMOTELOW, (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) => 
			let fN_2_lst := (promote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) in 
			(seq.map (fun (fN_2_16 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_16))) fN_2_lst)
		| _, _, _, _ => default_val
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.15 *)
Lemma vcvtop___is_wf : forall (shape_1 : shape) (shape_2 : shape) (v_vcvtop : vcvtop) (v_lane_ : lane_) (ret_val_lst : (seq lane_)),
	(wf_shape shape_1) ->
	(wf_shape shape_2) ->
	(wf_lane_ (fun_lanetype shape_1) v_lane_) ->
	(ret_val_lst == (vcvtop__ shape_1 shape_2 v_vcvtop v_lane_)) ->
	List.Forall (fun (ret_val : lane_) => (wf_lane_ (fun_lanetype shape_2) ret_val)) ret_val_lst.
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 *)
Inductive fun_vextunop__ : ishape -> ishape -> vextunop_ -> vec_ -> vec_ -> Prop :=
	| fun_vextunop___case_0 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)) (M_1_0 : nat) (ci_lst : (seq lane_)) (c : vec_), 
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_2 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2)))) != None)) ci_lst ->
		List.Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_1 : iN) (cj_2_1 : iN) => [::cj_1_1; cj_2_1]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_2 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_2 : iN) (cj_2_2 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_2 cj_2_2)))) cj_1_lst cj_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_3 : iN) (cj_2_3 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_3 cj_2_3))))) cj_1_lst cj_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextunop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_1 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)) (M_1_0 : nat) (ci_lst : (seq lane_)) (c : vec_), 
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_4 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_4)))) != None)) ci_lst ->
		List.Forall (fun (ci_4 : lane_) => ((proj_lane__0 ci_4) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_4 : iN) (cj_2_4 : iN) => [::cj_1_4; cj_2_4]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_4 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_4)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_5 : iN) (cj_2_5 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_5 cj_2_5)))) cj_1_lst cj_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_6 : iN) (cj_2_6 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_6 cj_2_6))))) cj_1_lst cj_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextunop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_2 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)) (M_1_0 : nat) (ci_lst : (seq lane_)) (c : vec_), 
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_6 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_6)))) != None)) ci_lst ->
		List.Forall (fun (ci_6 : lane_) => ((proj_lane__0 ci_6) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_7 : iN) (cj_2_7 : iN) => [::cj_1_7; cj_2_7]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_6 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_6)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_8 : iN) (cj_2_8 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_8 cj_2_8)))) cj_1_lst cj_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_9 : iN) (cj_2_9 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_9 cj_2_9))))) cj_1_lst cj_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextunop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_3 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)) (M_1_0 : nat) (ci_lst : (seq lane_)) (c : vec_), 
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_8 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_8)))) != None)) ci_lst ->
		List.Forall (fun (ci_8 : lane_) => ((proj_lane__0 ci_8) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_10 : iN) (cj_2_10 : iN) => [::cj_1_10; cj_2_10]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_8 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_8)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_11 : iN) (cj_2_11 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_11 cj_2_11)))) cj_1_lst cj_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_12 : iN) (cj_2_12 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_12 cj_2_12))))) cj_1_lst cj_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextunop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 *)
Lemma vextunop___is_wf : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop_ : vextunop_) (v_vec_ : vec_) (ret_val : vec_) (var_0 : vec_),
	(fun_vextunop__ ishape_1 ishape_2 v_vextunop_ v_vec_ var_0) ->
	(wf_ishape ishape_1) ->
	(wf_ishape ishape_2) ->
	(wf_vextunop_ ishape_1 v_vextunop_) ->
	(wf_uN 128 v_vec_) ->
	(ret_val == var_0) ->
	(wf_uN 128 ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 *)
Inductive fun_vextbinop__ : ishape -> ishape -> vextbinop_ -> vec_ -> vec_ -> vec_ -> Prop :=
	| fun_vextbinop___case_0 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : nat) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (c : vec_), 
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_2 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_2)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_2 : lane_) => ((proj_lane__0 ci_1_2) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_2 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_2)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_2 : lane_) => ((proj_lane__0 ci_2_2) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (ci_1_2 : lane_) (ci_2_2 : lane_) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_2))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_2))))))))))) ci_1_lst ci_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ->
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_3 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_3)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_3 : lane_) => ((proj_lane__0 ci_1_3) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_3 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_3)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_3 : lane_) => ((proj_lane__0 ci_2_3) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_3 : lane_) (ci_2_3 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_3))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_3)))))))))))) ci_1_lst ci_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_1 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : nat) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (c : vec_), 
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_5 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_5)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_5 : lane_) => ((proj_lane__0 ci_1_5) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_5 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_5)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_5 : lane_) => ((proj_lane__0 ci_2_5) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (ci_1_5 : lane_) (ci_2_5 : lane_) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_5))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_5))))))))))) ci_1_lst ci_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ->
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_6 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_6)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_6 : lane_) => ((proj_lane__0 ci_1_6) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_6 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_6)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_6 : lane_) => ((proj_lane__0 ci_2_6) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_6 : lane_) (ci_2_6 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_6))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_6)))))))))))) ci_1_lst ci_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_2 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : nat) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (c : vec_), 
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_8 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_8)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_8 : lane_) => ((proj_lane__0 ci_1_8) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_8 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_8)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_8 : lane_) => ((proj_lane__0 ci_2_8) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (ci_1_8 : lane_) (ci_2_8 : lane_) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_8))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_8))))))))))) ci_1_lst ci_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ->
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_9 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_9)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_9 : lane_) => ((proj_lane__0 ci_1_9) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_9 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_9)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_9 : lane_) => ((proj_lane__0 ci_2_9) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_9 : lane_) (ci_2_9 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_9))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_9)))))))))))) ci_1_lst ci_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_3 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : nat) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (c : vec_), 
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_11 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_11)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_11 : lane_) => ((proj_lane__0 ci_1_11) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_11 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_11)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_11 : lane_) => ((proj_lane__0 ci_2_11) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (ci_1_11 : lane_) (ci_2_11 : lane_) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_11))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_11))))))))))) ci_1_lst ci_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ->
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_12 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_12)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_12 : lane_) => ((proj_lane__0 ci_1_12) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_12 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_12)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_12 : lane_) => ((proj_lane__0 ci_2_12) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_12 : lane_) (ci_2_12 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_12))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_12)))))))))))) ci_1_lst ci_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_4 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)) (M_1_0 : nat) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (c : vec_), 
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_14 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_14)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_14 : lane_) => ((proj_lane__0 ci_1_14) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_14 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_14)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_14 : lane_) => ((proj_lane__0 ci_2_14) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_13 : iN) (cj_2_13 : iN) => [::cj_1_13; cj_2_13]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_14 : lane_) (ci_2_14 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_14))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_14))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_14 : iN) (cj_2_14 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_14 cj_2_14)))) cj_1_lst cj_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_15 : iN) (cj_2_15 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_15 cj_2_15))))) cj_1_lst cj_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 DOTS) c_1 c_2 c
	| fun_vextbinop___case_5 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)) (M_1_0 : nat) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (c : vec_), 
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_16 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_16)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_16 : lane_) => ((proj_lane__0 ci_1_16) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_16 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_16)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_16 : lane_) => ((proj_lane__0 ci_2_16) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_16 : iN) (cj_2_16 : iN) => [::cj_1_16; cj_2_16]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_16 : lane_) (ci_2_16 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_16))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_16))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_17 : iN) (cj_2_17 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_17 cj_2_17)))) cj_1_lst cj_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_18 : iN) (cj_2_18 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_18 cj_2_18))))) cj_1_lst cj_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 DOTS) c_1 c_2 c
	| fun_vextbinop___case_6 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)) (M_1_0 : nat) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (c : vec_), 
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_18 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_18)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_18 : lane_) => ((proj_lane__0 ci_1_18) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_18 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_18)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_18 : lane_) => ((proj_lane__0 ci_2_18) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_19 : iN) (cj_2_19 : iN) => [::cj_1_19; cj_2_19]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_18 : lane_) (ci_2_18 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_18))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_18))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_20 : iN) (cj_2_20 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_20 cj_2_20)))) cj_1_lst cj_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_21 : iN) (cj_2_21 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_21 cj_2_21))))) cj_1_lst cj_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 DOTS) c_1 c_2 c
	| fun_vextbinop___case_7 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)) (M_1_0 : nat) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (c : vec_), 
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_20 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_20)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_20 : lane_) => ((proj_lane__0 ci_1_20) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_20 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_20)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_20 : lane_) => ((proj_lane__0 ci_2_20) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_22 : iN) (cj_2_22 : iN) => [::cj_1_22; cj_2_22]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_20 : lane_) (ci_2_20 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_20))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_20))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_23 : iN) (cj_2_23 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_23 cj_2_23)))) cj_1_lst cj_2_lst))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ->
		(wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_24 : iN) (cj_2_24 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_24 cj_2_24))))) cj_1_lst cj_2_lst ->
		(M_1 == M_1_0) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 DOTS) c_1 c_2 c.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 *)
Lemma vextbinop___is_wf : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop_ : vextbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_),
	(fun_vextbinop__ ishape_1 ishape_2 v_vextbinop_ v_vec_ vec__0 var_0) ->
	(wf_ishape ishape_1) ->
	(wf_ishape ishape_2) ->
	(wf_vextbinop_ ishape_1 v_vextbinop_) ->
	(wf_uN 128 v_vec_) ->
	(wf_uN 128 vec__0) ->
	(ret_val == var_0) ->
	(wf_uN 128 ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 *)
Inductive fun_vshiftop_ : ishape -> vshiftop_ -> lane_ -> u32 -> lane_ -> Prop :=
	| fun_vshiftop__case_0 : forall (v_Jnn : Jnn) (v_M : nat) (lane : uN) (v_n : nat) (Jnn_1 : Jnn) (Jnn_0 : Jnn) (M_0 : nat), 
		(v_Jnn == Jnn_1) ->
		(v_Jnn == Jnn_0) ->
		(v_M == M_0) ->
		fun_vshiftop_ (ishape_X v_Jnn (mk_dim v_M)) (mk_vshiftop__0 Jnn_0 M_0 vshiftop_Jnn_N_SHL) (mk_lane__2 Jnn_1 lane) (mk_uN v_n) (mk_lane__2 v_Jnn (ishl_ (lsizenn (lanetype_Jnn v_Jnn)) lane (mk_uN v_n)))
	| fun_vshiftop__case_1 : forall (v_Jnn : Jnn) (v_M : nat) (v_sx : sx) (lane : uN) (v_n : nat) (Jnn_1 : Jnn) (Jnn_0 : Jnn) (M_0 : nat), 
		(v_Jnn == Jnn_1) ->
		(v_Jnn == Jnn_0) ->
		(v_M == M_0) ->
		fun_vshiftop_ (ishape_X v_Jnn (mk_dim v_M)) (mk_vshiftop__0 Jnn_0 M_0 (vshiftop_Jnn_N_SHR v_sx)) (mk_lane__2 Jnn_1 lane) (mk_uN v_n) (mk_lane__2 v_Jnn (ishr_ (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (mk_uN v_n))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 *)
Lemma vshiftop__is_wf : forall (v_ishape : ishape) (v_vshiftop_ : vshiftop_) (v_lane_ : lane_) (v_u32 : u32) (ret_val : lane_) (var_0 : lane_),
	(fun_vshiftop_ v_ishape v_vshiftop_ v_lane_ v_u32 var_0) ->
	(wf_ishape v_ishape) ->
	(wf_vshiftop_ v_ishape v_vshiftop_) ->
	(wf_lane_ (fun_lanetype (shape_ishape v_ishape)) v_lane_) ->
	(wf_uN 32 v_u32) ->
	(ret_val == var_0) ->
	(wf_lane_ (fun_lanetype (shape_ishape v_ishape)) ret_val).
Proof. Admitted.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:5.1-5.39 *)
Definition addr : Type := nat.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:6.1-6.53 *)
Definition funcaddr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:7.1-7.53 *)
Definition globaladdr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:8.1-8.51 *)
Definition tableaddr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:9.1-9.50 *)
Definition memaddr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:10.1-10.49 *)
Definition elemaddr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:11.1-11.49 *)
Definition dataaddr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:12.1-12.49 *)
Definition hostaddr : Type := addr.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:25.1-26.70 *)
Inductive externaddr : Type :=
	| externaddr_FUNC (v_funcaddr : funcaddr) : externaddr
	| externaddr_GLOBAL (v_globaladdr : globaladdr) : externaddr
	| externaddr_TABLE (v_tableaddr : tableaddr) : externaddr
	| externaddr_MEM (v_memaddr : memaddr) : externaddr.

Global Instance Inhabited__externaddr : Inhabited (externaddr) := { default_val := externaddr_FUNC default_val }.

Definition externaddr_eq_dec : forall (v1 v2 : externaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition externaddr_eqb (v1 v2 : externaddr) : bool :=
	is_left(externaddr_eq_dec v1 v2).
Definition eqexternaddrP : Equality.axiom (externaddr_eqb) :=
	eq_dec_Equality_axiom (externaddr) (externaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (externaddr) (eqexternaddrP).
Hint Resolve externaddr_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.1-38.62 *)
Inductive num : Type :=
	| num_CONST (v_numtype : numtype) (_ : num_) : num.

Global Instance Inhabited__num : Inhabited (num) := { default_val := num_CONST default_val default_val }.

Definition num_eq_dec : forall (v1 v2 : num),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition num_eqb (v1 v2 : num) : bool :=
	is_left(num_eq_dec v1 v2).
Definition eqnumP : Equality.axiom (num_eqb) :=
	eq_dec_Equality_axiom (num) (num_eq_dec).

HB.instance Definition _ := hasDecEq.Build (num) (eqnumP).
Hint Resolve num_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.8-37.11 *)
Inductive wf_num : num -> Prop :=
	| num_case_0 : forall (v_numtype : numtype) (var_0 : num_), 
		(wf_num_ v_numtype var_0) ->
		wf_num (num_CONST v_numtype var_0).

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.1-40.62 *)
Inductive vec : Type :=
	| vec_VCONST (v_vectype : vectype) (_ : vec_) : vec.

Global Instance Inhabited__vec : Inhabited (vec) := { default_val := vec_VCONST default_val default_val }.

Definition vec_eq_dec : forall (v1 v2 : vec),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vec_eqb (v1 v2 : vec) : bool :=
	is_left(vec_eq_dec v1 v2).
Definition eqvecP : Equality.axiom (vec_eqb) :=
	eq_dec_Equality_axiom (vec) (vec_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vec) (eqvecP).
Hint Resolve vec_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.8-39.11 *)
Inductive wf_vec : vec -> Prop :=
	| vec_case_0 : forall (v_vectype : vectype) (var_0 : vec_), 
		((res_size (valtype_vectype v_vectype)) != None) ->
		(wf_uN (!((res_size (valtype_vectype v_vectype)))) var_0) ->
		wf_vec (vec_VCONST v_vectype var_0).

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:41.1-42.71 *)
Inductive ref : Type :=
	| ref_REF_NULL (v_reftype : reftype) : ref
	| REF_FUNC_ADDR (v_funcaddr : funcaddr) : ref
	| REF_HOST_ADDR (v_hostaddr : hostaddr) : ref.

Global Instance Inhabited__ref : Inhabited (ref) := { default_val := ref_REF_NULL default_val }.

Definition ref_eq_dec : forall (v1 v2 : ref),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition ref_eqb (v1 v2 : ref) : bool :=
	is_left(ref_eq_dec v1 v2).
Definition eqrefP : Equality.axiom (ref_eqb) :=
	eq_dec_Equality_axiom (ref) (ref_eq_dec).

HB.instance Definition _ := hasDecEq.Build (ref) (eqrefP).
Hint Resolve ref_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.1-44.20 *)
Inductive val : Type :=
	| val_CONST (v_numtype : numtype) (_ : num_) : val
	| val_VCONST (v_vectype : vectype) (_ : vec_) : val
	| val_REF_NULL (v_reftype : reftype) : val
	| val_REF_FUNC_ADDR (v_funcaddr : funcaddr) : val
	| val_REF_HOST_ADDR (v_hostaddr : hostaddr) : val.

Global Instance Inhabited__val : Inhabited (val) := { default_val := val_CONST default_val default_val }.

Definition val_eq_dec : forall (v1 v2 : val),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition val_eqb (v1 v2 : val) : bool :=
	is_left(val_eq_dec v1 v2).
Definition eqvalP : Equality.axiom (val_eqb) :=
	eq_dec_Equality_axiom (val) (val_eq_dec).

HB.instance Definition _ := hasDecEq.Build (val) (eqvalP).
Hint Resolve val_eq_dec : eq_dec_db.

(* Auxiliary Definition at:  *)
Definition val_ref (var_0 : ref) : val :=
	match var_0 return val with
		| (ref_REF_NULL x0) => (val_REF_NULL x0)
		| (REF_FUNC_ADDR x0) => (val_REF_FUNC_ADDR x0)
		| (REF_HOST_ADDR x0) => (val_REF_HOST_ADDR x0)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.8-43.11 *)
Inductive wf_val : val -> Prop :=
	| val_case_0 : forall (v_numtype : numtype) (var_0 : num_), 
		(wf_num_ v_numtype var_0) ->
		wf_val (val_CONST v_numtype var_0)
	| val_case_1 : forall (v_vectype : vectype) (var_0 : vec_), 
		((res_size (valtype_vectype v_vectype)) != None) ->
		(wf_uN (!((res_size (valtype_vectype v_vectype)))) var_0) ->
		wf_val (val_VCONST v_vectype var_0)
	| val_case_2 : forall (v_reftype : reftype), wf_val (val_REF_NULL v_reftype)
	| val_case_3 : forall (v_funcaddr : funcaddr), wf_val (val_REF_FUNC_ADDR v_funcaddr)
	| val_case_4 : forall (v_hostaddr : hostaddr), wf_val (val_REF_HOST_ADDR v_hostaddr).

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.1-47.22 *)
Inductive result : Type :=
	| _VALS (val_lst : (seq val)) : result
	| TRAP : result.

Global Instance Inhabited__result : Inhabited (result) := { default_val := _VALS default_val }.

Definition result_eq_dec : forall (v1 v2 : result),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition result_eqb (v1 v2 : result) : bool :=
	is_left(result_eq_dec v1 v2).
Definition eqresultP : Equality.axiom (result_eqb) :=
	eq_dec_Equality_axiom (result) (result_eq_dec).

HB.instance Definition _ := hasDecEq.Build (result) (eqresultP).
Hint Resolve result_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.8-46.14 *)
Inductive wf_result : result -> Prop :=
	| result_case_0 : forall (val_lst : (seq val)), 
		List.Forall (fun (v_val : val) => (wf_val v_val)) val_lst ->
		wf_result (_VALS val_lst)
	| result_case_1 : wf_result TRAP.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.1-80.22 *)
Record exportinst := MKexportinst
{	NAME : name
;	ADDR : externaddr
}.

Global Instance Inhabited_exportinst : Inhabited (exportinst) := 
{default_val := {|
	NAME := default_val;
	ADDR := default_val|} }.

Definition _append_exportinst (arg1 arg2 : (exportinst)) :=
{|
	NAME := arg1.(NAME); (* FIXME - Non-trivial append *)
	ADDR := arg1.(ADDR); (* FIXME - Non-trivial append *)
|}.

Global Instance Append_exportinst : Append exportinst := { _append arg1 arg2 := _append_exportinst arg1 arg2 }.

#[export] Instance eta__exportinst : Settable _ := settable! MKexportinst <NAME;ADDR>.

Definition exportinst_eq_dec : forall (v1 v2 : exportinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition exportinst_eqb (v1 v2 : exportinst) : bool :=
	is_left(exportinst_eq_dec v1 v2).
Definition eqexportinstP : Equality.axiom (exportinst_eqb) :=
	eq_dec_Equality_axiom (exportinst) (exportinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (exportinst) (eqexportinstP).
Hint Resolve exportinst_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.8-78.18 *)
Inductive wf_exportinst : exportinst -> Prop :=
	| exportinst_case_ : forall (var_0 : name) (var_1 : externaddr), 
		(wf_name var_0) ->
		wf_exportinst {| NAME := var_0; ADDR := var_1 |}.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.1-90.26 *)
Record moduleinst := MKmoduleinst
{	TYPES : (seq functype)
;	FUNCS : (seq funcaddr)
;	GLOBALS : (seq globaladdr)
;	TABLES : (seq tableaddr)
;	MEMS : (seq memaddr)
;	ELEMS : (seq elemaddr)
;	DATAS : (seq dataaddr)
;	EXPORTS : (seq exportinst)
}.

Global Instance Inhabited_moduleinst : Inhabited (moduleinst) := 
{default_val := {|
	TYPES := default_val;
	FUNCS := default_val;
	GLOBALS := default_val;
	TABLES := default_val;
	MEMS := default_val;
	ELEMS := default_val;
	DATAS := default_val;
	EXPORTS := default_val|} }.

Definition _append_moduleinst (arg1 arg2 : (moduleinst)) :=
{|
	TYPES := arg1.(TYPES) @@ arg2.(TYPES);
	FUNCS := arg1.(FUNCS) @@ arg2.(FUNCS);
	GLOBALS := arg1.(GLOBALS) @@ arg2.(GLOBALS);
	TABLES := arg1.(TABLES) @@ arg2.(TABLES);
	MEMS := arg1.(MEMS) @@ arg2.(MEMS);
	ELEMS := arg1.(ELEMS) @@ arg2.(ELEMS);
	DATAS := arg1.(DATAS) @@ arg2.(DATAS);
	EXPORTS := arg1.(EXPORTS) @@ arg2.(EXPORTS);
|}.

Global Instance Append_moduleinst : Append moduleinst := { _append arg1 arg2 := _append_moduleinst arg1 arg2 }.

#[export] Instance eta__moduleinst : Settable _ := settable! MKmoduleinst <TYPES;FUNCS;GLOBALS;TABLES;MEMS;ELEMS;DATAS;EXPORTS>.

Definition moduleinst_eq_dec : forall (v1 v2 : moduleinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition moduleinst_eqb (v1 v2 : moduleinst) : bool :=
	is_left(moduleinst_eq_dec v1 v2).
Definition eqmoduleinstP : Equality.axiom (moduleinst_eqb) :=
	eq_dec_Equality_axiom (moduleinst) (moduleinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (moduleinst) (eqmoduleinstP).
Hint Resolve moduleinst_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.8-82.18 *)
Inductive wf_moduleinst : moduleinst -> Prop :=
	| moduleinst_case_ : forall (var_0_lst : (seq functype)) (var_1_lst : (seq funcaddr)) (var_2_lst : (seq globaladdr)) (var_3_lst : (seq tableaddr)) (var_4_lst : (seq memaddr)) (var_5_lst : (seq elemaddr)) (var_6_lst : (seq dataaddr)) (var_7_lst : (seq exportinst)), 
		List.Forall (fun (var_7 : exportinst) => (wf_exportinst var_7)) var_7_lst ->
		wf_moduleinst {| TYPES := var_0_lst; FUNCS := var_1_lst; GLOBALS := var_2_lst; TABLES := var_3_lst; MEMS := var_4_lst; ELEMS := var_5_lst; DATAS := var_6_lst; EXPORTS := var_7_lst |}.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.1-63.16 *)
Record funcinst := MKfuncinst
{	funcinst_TYPE : functype
;	funcinst_MODULE : moduleinst
;	CODE : func
}.

Global Instance Inhabited_funcinst : Inhabited (funcinst) := 
{default_val := {|
	funcinst_TYPE := default_val;
	funcinst_MODULE := default_val;
	CODE := default_val|} }.

Definition _append_funcinst (arg1 arg2 : (funcinst)) :=
{|
	funcinst_TYPE := arg1.(funcinst_TYPE); (* FIXME - Non-trivial append *)
	funcinst_MODULE := arg1.(funcinst_MODULE) @@ arg2.(funcinst_MODULE);
	CODE := arg1.(CODE); (* FIXME - Non-trivial append *)
|}.

Global Instance Append_funcinst : Append funcinst := { _append arg1 arg2 := _append_funcinst arg1 arg2 }.

#[export] Instance eta__funcinst : Settable _ := settable! MKfuncinst <funcinst_TYPE;funcinst_MODULE;CODE>.

Definition funcinst_eq_dec : forall (v1 v2 : funcinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition funcinst_eqb (v1 v2 : funcinst) : bool :=
	is_left(funcinst_eq_dec v1 v2).
Definition eqfuncinstP : Equality.axiom (funcinst_eqb) :=
	eq_dec_Equality_axiom (funcinst) (funcinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (funcinst) (eqfuncinstP).
Hint Resolve funcinst_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.8-60.16 *)
Inductive wf_funcinst : funcinst -> Prop :=
	| funcinst_case_ : forall (var_0 : functype) (var_1 : moduleinst) (var_2 : func), 
		(wf_moduleinst var_1) ->
		(wf_func var_2) ->
		wf_funcinst {| funcinst_TYPE := var_0; funcinst_MODULE := var_1; CODE := var_2 |}.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.1-66.16 *)
Record globalinst := MKglobalinst
{	globalinst_TYPE : globaltype
;	VALUE : val
}.

Global Instance Inhabited_globalinst : Inhabited (globalinst) := 
{default_val := {|
	globalinst_TYPE := default_val;
	VALUE := default_val|} }.

Definition _append_globalinst (arg1 arg2 : (globalinst)) :=
{|
	globalinst_TYPE := arg1.(globalinst_TYPE); (* FIXME - Non-trivial append *)
	VALUE := arg1.(VALUE); (* FIXME - Non-trivial append *)
|}.

Global Instance Append_globalinst : Append globalinst := { _append arg1 arg2 := _append_globalinst arg1 arg2 }.

#[export] Instance eta__globalinst : Settable _ := settable! MKglobalinst <globalinst_TYPE;VALUE>.

Definition globalinst_eq_dec : forall (v1 v2 : globalinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globalinst_eqb (v1 v2 : globalinst) : bool :=
	is_left(globalinst_eq_dec v1 v2).
Definition eqglobalinstP : Equality.axiom (globalinst_eqb) :=
	eq_dec_Equality_axiom (globalinst) (globalinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globalinst) (eqglobalinstP).
Hint Resolve globalinst_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.8-64.18 *)
Inductive wf_globalinst : globalinst -> Prop :=
	| globalinst_case_ : forall (var_0 : globaltype) (var_1 : val), 
		(wf_val var_1) ->
		wf_globalinst {| globalinst_TYPE := var_0; VALUE := var_1 |}.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.1-69.16 *)
Record tableinst := MKtableinst
{	tableinst_TYPE : tabletype
;	REFS : (seq ref)
}.

Global Instance Inhabited_tableinst : Inhabited (tableinst) := 
{default_val := {|
	tableinst_TYPE := default_val;
	REFS := default_val|} }.

Definition _append_tableinst (arg1 arg2 : (tableinst)) :=
{|
	tableinst_TYPE := arg1.(tableinst_TYPE); (* FIXME - Non-trivial append *)
	REFS := arg1.(REFS) @@ arg2.(REFS);
|}.

Global Instance Append_tableinst : Append tableinst := { _append arg1 arg2 := _append_tableinst arg1 arg2 }.

#[export] Instance eta__tableinst : Settable _ := settable! MKtableinst <tableinst_TYPE;REFS>.

Definition tableinst_eq_dec : forall (v1 v2 : tableinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tableinst_eqb (v1 v2 : tableinst) : bool :=
	is_left(tableinst_eq_dec v1 v2).
Definition eqtableinstP : Equality.axiom (tableinst_eqb) :=
	eq_dec_Equality_axiom (tableinst) (tableinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tableinst) (eqtableinstP).
Hint Resolve tableinst_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.8-67.17 *)
Inductive wf_tableinst : tableinst -> Prop :=
	| tableinst_case_ : forall (var_0 : tabletype) (var_1_lst : (seq ref)), 
		(wf_tabletype var_0) ->
		wf_tableinst {| tableinst_TYPE := var_0; REFS := var_1_lst |}.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.1-72.18 *)
Record meminst := MKmeminst
{	meminst_TYPE : memtype
;	BYTES : (seq byte)
}.

Global Instance Inhabited_meminst : Inhabited (meminst) := 
{default_val := {|
	meminst_TYPE := default_val;
	BYTES := default_val|} }.

Definition _append_meminst (arg1 arg2 : (meminst)) :=
{|
	meminst_TYPE := arg1.(meminst_TYPE); (* FIXME - Non-trivial append *)
	BYTES := arg1.(BYTES) @@ arg2.(BYTES);
|}.

Global Instance Append_meminst : Append meminst := { _append arg1 arg2 := _append_meminst arg1 arg2 }.

#[export] Instance eta__meminst : Settable _ := settable! MKmeminst <meminst_TYPE;BYTES>.

Definition meminst_eq_dec : forall (v1 v2 : meminst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition meminst_eqb (v1 v2 : meminst) : bool :=
	is_left(meminst_eq_dec v1 v2).
Definition eqmeminstP : Equality.axiom (meminst_eqb) :=
	eq_dec_Equality_axiom (meminst) (meminst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (meminst) (eqmeminstP).
Hint Resolve meminst_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.8-70.15 *)
Inductive wf_meminst : meminst -> Prop :=
	| meminst_case_ : forall (var_0 : memtype) (var_1_lst : (seq byte)), 
		(wf_memtype var_0) ->
		List.Forall (fun (var_1 : byte) => (wf_byte var_1)) var_1_lst ->
		wf_meminst {| meminst_TYPE := var_0; BYTES := var_1_lst |}.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:73.1-75.16 *)
Record eleminst := MKeleminst
{	eleminst_TYPE : elemtype
;	eleminst_REFS : (seq ref)
}.

Global Instance Inhabited_eleminst : Inhabited (eleminst) := 
{default_val := {|
	eleminst_TYPE := default_val;
	eleminst_REFS := default_val|} }.

Definition _append_eleminst (arg1 arg2 : (eleminst)) :=
{|
	eleminst_TYPE := arg1.(eleminst_TYPE); (* FIXME - Non-trivial append *)
	eleminst_REFS := arg1.(eleminst_REFS) @@ arg2.(eleminst_REFS);
|}.

Global Instance Append_eleminst : Append eleminst := { _append arg1 arg2 := _append_eleminst arg1 arg2 }.

#[export] Instance eta__eleminst : Settable _ := settable! MKeleminst <eleminst_TYPE;eleminst_REFS>.

Definition eleminst_eq_dec : forall (v1 v2 : eleminst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition eleminst_eqb (v1 v2 : eleminst) : bool :=
	is_left(eleminst_eq_dec v1 v2).
Definition eqeleminstP : Equality.axiom (eleminst_eqb) :=
	eq_dec_Equality_axiom (eleminst) (eleminst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (eleminst) (eqeleminstP).
Hint Resolve eleminst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.1-77.18 *)
Record datainst := MKdatainst
{	datainst_BYTES : (seq byte)
}.

Global Instance Inhabited_datainst : Inhabited (datainst) := 
{default_val := {|
	datainst_BYTES := default_val|} }.

Definition _append_datainst (arg1 arg2 : (datainst)) :=
{|
	datainst_BYTES := arg1.(datainst_BYTES) @@ arg2.(datainst_BYTES);
|}.

Global Instance Append_datainst : Append datainst := { _append arg1 arg2 := _append_datainst arg1 arg2 }.

#[export] Instance eta__datainst : Settable _ := settable! MKdatainst <datainst_BYTES>.

Definition datainst_eq_dec : forall (v1 v2 : datainst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition datainst_eqb (v1 v2 : datainst) : bool :=
	is_left(datainst_eq_dec v1 v2).
Definition eqdatainstP : Equality.axiom (datainst_eqb) :=
	eq_dec_Equality_axiom (datainst) (datainst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (datainst) (eqdatainstP).
Hint Resolve datainst_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.8-76.16 *)
Inductive wf_datainst : datainst -> Prop :=
	| datainst_case_ : forall (var_0_lst : (seq byte)), 
		List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
		wf_datainst {| datainst_BYTES := var_0_lst |}.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.1-110.22 *)
Record store := MKstore
{	store_FUNCS : (seq funcinst)
;	store_GLOBALS : (seq globalinst)
;	store_TABLES : (seq tableinst)
;	store_MEMS : (seq meminst)
;	store_ELEMS : (seq eleminst)
;	store_DATAS : (seq datainst)
}.

Global Instance Inhabited_store : Inhabited (store) := 
{default_val := {|
	store_FUNCS := default_val;
	store_GLOBALS := default_val;
	store_TABLES := default_val;
	store_MEMS := default_val;
	store_ELEMS := default_val;
	store_DATAS := default_val|} }.

Definition _append_store (arg1 arg2 : (store)) :=
{|
	store_FUNCS := arg1.(store_FUNCS) @@ arg2.(store_FUNCS);
	store_GLOBALS := arg1.(store_GLOBALS) @@ arg2.(store_GLOBALS);
	store_TABLES := arg1.(store_TABLES) @@ arg2.(store_TABLES);
	store_MEMS := arg1.(store_MEMS) @@ arg2.(store_MEMS);
	store_ELEMS := arg1.(store_ELEMS) @@ arg2.(store_ELEMS);
	store_DATAS := arg1.(store_DATAS) @@ arg2.(store_DATAS);
|}.

Global Instance Append_store : Append store := { _append arg1 arg2 := _append_store arg1 arg2 }.

#[export] Instance eta__store : Settable _ := settable! MKstore <store_FUNCS;store_GLOBALS;store_TABLES;store_MEMS;store_ELEMS;store_DATAS>.

Definition store_eq_dec : forall (v1 v2 : store),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition store_eqb (v1 v2 : store) : bool :=
	is_left(store_eq_dec v1 v2).
Definition eqstoreP : Equality.axiom (store_eqb) :=
	eq_dec_Equality_axiom (store) (store_eq_dec).

HB.instance Definition _ := hasDecEq.Build (store) (eqstoreP).
Hint Resolve store_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.8-104.13 *)
Inductive wf_store : store -> Prop :=
	| store_case_ : forall (var_0_lst : (seq funcinst)) (var_1_lst : (seq globalinst)) (var_2_lst : (seq tableinst)) (var_3_lst : (seq meminst)) (var_4_lst : (seq eleminst)) (var_5_lst : (seq datainst)), 
		List.Forall (fun (var_0 : funcinst) => (wf_funcinst var_0)) var_0_lst ->
		List.Forall (fun (var_1 : globalinst) => (wf_globalinst var_1)) var_1_lst ->
		List.Forall (fun (var_2 : tableinst) => (wf_tableinst var_2)) var_2_lst ->
		List.Forall (fun (var_3 : meminst) => (wf_meminst var_3)) var_3_lst ->
		List.Forall (fun (var_5 : datainst) => (wf_datainst var_5)) var_5_lst ->
		wf_store {| store_FUNCS := var_0_lst; store_GLOBALS := var_1_lst; store_TABLES := var_2_lst; store_MEMS := var_3_lst; store_ELEMS := var_4_lst; store_DATAS := var_5_lst |}.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.1-114.24 *)
Record frame := MKframe
{	LOCALS : (seq val)
;	frame_MODULE : moduleinst
}.

Global Instance Inhabited_frame : Inhabited (frame) := 
{default_val := {|
	LOCALS := default_val;
	frame_MODULE := default_val|} }.

Definition _append_frame (arg1 arg2 : (frame)) :=
{|
	LOCALS := arg1.(LOCALS) @@ arg2.(LOCALS);
	frame_MODULE := arg1.(frame_MODULE) @@ arg2.(frame_MODULE);
|}.

Global Instance Append_frame : Append frame := { _append arg1 arg2 := _append_frame arg1 arg2 }.

#[export] Instance eta__frame : Settable _ := settable! MKframe <LOCALS;frame_MODULE>.

Definition frame_eq_dec : forall (v1 v2 : frame),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition frame_eqb (v1 v2 : frame) : bool :=
	is_left(frame_eq_dec v1 v2).
Definition eqframeP : Equality.axiom (frame_eqb) :=
	eq_dec_Equality_axiom (frame) (frame_eq_dec).

HB.instance Definition _ := hasDecEq.Build (frame) (eqframeP).
Hint Resolve frame_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.8-112.13 *)
Inductive wf_frame : frame -> Prop :=
	| frame_case_ : forall (var_0_lst : (seq val)) (var_1 : moduleinst), 
		List.Forall (fun (var_0 : val) => (wf_val var_0)) var_0_lst ->
		(wf_moduleinst var_1) ->
		wf_frame {| LOCALS := var_0_lst; frame_MODULE := var_1 |}.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.1-116.47 *)
Inductive state : Type :=
	| mk_state (v_store : store) (v_frame : frame) : state.

Global Instance Inhabited__state : Inhabited (state) := { default_val := mk_state default_val default_val }.

Definition state_eq_dec : forall (v1 v2 : state),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition state_eqb (v1 v2 : state) : bool :=
	is_left(state_eq_dec v1 v2).
Definition eqstateP : Equality.axiom (state_eqb) :=
	eq_dec_Equality_axiom (state) (state_eq_dec).

HB.instance Definition _ := hasDecEq.Build (state) (eqstateP).
Hint Resolve state_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.8-116.13 *)
Inductive wf_state : state -> Prop :=
	| state_case_0 : forall (v_store : store) (v_frame : frame), 
		(wf_store v_store) ->
		(wf_frame v_frame) ->
		wf_state (mk_state v_store v_frame).

(* Mutual Recursion at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
Inductive admininstr : Type :=
	| admininstr_NOP : admininstr
	| admininstr_UNREACHABLE : admininstr
	| admininstr_DROP : admininstr
	| admininstr_SELECT (valtype_lst_opt : (option (seq valtype))) : admininstr
	| admininstr_BLOCK (v_blocktype : blocktype) (instr_lst : (seq instr)) : admininstr
	| admininstr_LOOP (v_blocktype : blocktype) (instr_lst : (seq instr)) : admininstr
	| admininstr_IFELSE (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst : (seq instr)) : admininstr
	| admininstr_BR (v_labelidx : labelidx) : admininstr
	| admininstr_BR_IF (v_labelidx : labelidx) : admininstr
	| admininstr_BR_TABLE (labelidx_lst : (seq labelidx)) (v_labelidx : labelidx) : admininstr
	| admininstr_CALL (v_funcidx : funcidx) : admininstr
	| admininstr_CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : admininstr
	| admininstr_RETURN : admininstr
	| admininstr_CONST (v_numtype : numtype) (_ : num_) : admininstr
	| admininstr_UNOP (v_numtype : numtype) (_ : unop_) : admininstr
	| admininstr_BINOP (v_numtype : numtype) (_ : binop_) : admininstr
	| admininstr_TESTOP (v_numtype : numtype) (_ : testop_) : admininstr
	| admininstr_RELOP (v_numtype : numtype) (_ : relop_) : admininstr
	| admininstr_CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop) : admininstr
	| admininstr_EXTEND (v_numtype : numtype) (v_n : n) : admininstr
	| admininstr_VCONST (v_vectype : vectype) (_ : vec_) : admininstr
	| admininstr_VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : admininstr
	| admininstr_VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : admininstr
	| admininstr_VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : admininstr
	| admininstr_VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : admininstr
	| admininstr_VUNOP (v_shape : shape) (_ : vunop_) : admininstr
	| admininstr_VBINOP (v_shape : shape) (_ : vbinop_) : admininstr
	| admininstr_VTESTOP (v_shape : shape) (_ : vtestop_) : admininstr
	| admininstr_VRELOP (v_shape : shape) (_ : vrelop_) : admininstr
	| admininstr_VSHIFTOP (v_ishape : ishape) (_ : vshiftop_) : admininstr
	| admininstr_VBITMASK (v_ishape : ishape) : admininstr
	| admininstr_VSWIZZLE (v_ishape : ishape) : admininstr
	| admininstr_VSHUFFLE (v_ishape : ishape) (laneidx_lst : (seq laneidx)) : admininstr
	| admininstr_VSPLAT (v_shape : shape) : admininstr
	| admininstr_VEXTRACT_LANE (v_shape : shape) (sx_opt : (option sx)) (v_laneidx : laneidx) : admininstr
	| admininstr_VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : admininstr
	| admininstr_VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextunop_) : admininstr
	| admininstr_VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextbinop_) : admininstr
	| admininstr_VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : admininstr
	| admininstr_VCVTOP (v_shape : shape) (v_shape : shape) (v_vcvtop : vcvtop) : admininstr
	| admininstr_REF_NULL (v_reftype : reftype) : admininstr
	| admininstr_REF_FUNC (v_funcidx : funcidx) : admininstr
	| admininstr_REF_IS_NULL : admininstr
	| admininstr_LOCAL_GET (v_localidx : localidx) : admininstr
	| admininstr_LOCAL_SET (v_localidx : localidx) : admininstr
	| admininstr_LOCAL_TEE (v_localidx : localidx) : admininstr
	| admininstr_GLOBAL_GET (v_globalidx : globalidx) : admininstr
	| admininstr_GLOBAL_SET (v_globalidx : globalidx) : admininstr
	| admininstr_TABLE_GET (v_tableidx : tableidx) : admininstr
	| admininstr_TABLE_SET (v_tableidx : tableidx) : admininstr
	| admininstr_TABLE_SIZE (v_tableidx : tableidx) : admininstr
	| admininstr_TABLE_GROW (v_tableidx : tableidx) : admininstr
	| admininstr_TABLE_FILL (v_tableidx : tableidx) : admininstr
	| admininstr_TABLE_COPY (v_tableidx : tableidx) (v_tableidx : tableidx) : admininstr
	| admininstr_TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : admininstr
	| admininstr_ELEM_DROP (v_elemidx : elemidx) : admininstr
	| admininstr_LOAD (v_numtype : numtype) (_ : (option loadop_)) (v_memarg : memarg) : admininstr
	| admininstr_STORE (v_numtype : numtype) (sz_opt : (option sz)) (v_memarg : memarg) : admininstr
	| admininstr_VLOAD (v_vectype : vectype) (vloadop_opt : (option vloadop)) (v_memarg : memarg) : admininstr
	| admininstr_VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : admininstr
	| admininstr_VSTORE (v_vectype : vectype) (v_memarg : memarg) : admininstr
	| admininstr_VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : admininstr
	| admininstr_MEMORY_SIZE : admininstr
	| admininstr_MEMORY_GROW : admininstr
	| admininstr_MEMORY_FILL : admininstr
	| admininstr_MEMORY_COPY : admininstr
	| admininstr_MEMORY_INIT (v_dataidx : dataidx) : admininstr
	| admininstr_DATA_DROP (v_dataidx : dataidx) : admininstr
	| admininstr_REF_FUNC_ADDR (v_funcaddr : funcaddr) : admininstr
	| admininstr_REF_HOST_ADDR (v_hostaddr : hostaddr) : admininstr
	| CALL_ADDR (v_funcaddr : funcaddr) : admininstr
	| LABEL_ (v_n : n) (instr_lst : (seq instr)) (admininstr_lst : (seq admininstr)) : admininstr
	| FRAME_ (v_n : n) (v_frame : frame) (admininstr_lst : (seq admininstr)) : admininstr
	| admininstr_TRAP : admininstr.

Global Instance Inhabited__admininstr : Inhabited (admininstr) := { default_val := admininstr_NOP }.

Fixpoint admininstr_eq_dec (v1 v2 : admininstr) {struct v1} :
  {v1 = v2} + {v1 <> v2}.
Proof. decide equality; do ? decidable_equality_step. Defined.

Definition admininstr_eqb (v1 v2 : admininstr) : bool :=
	is_left(admininstr_eq_dec v1 v2).
Definition eqadmininstrP : Equality.axiom (admininstr_eqb) :=
	eq_dec_Equality_axiom (admininstr) (admininstr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (admininstr) (eqadmininstrP).
Hint Resolve admininstr_eq_dec : eq_dec_db.

(* Auxiliary Definition at:  *)
Definition admininstr_instr (var_0 : instr) : admininstr :=
	match var_0 return admininstr with
		| NOP => admininstr_NOP
		| UNREACHABLE => admininstr_UNREACHABLE
		| DROP => admininstr_DROP
		| (SELECT x0) => (admininstr_SELECT x0)
		| (BLOCK x0 x1) => (admininstr_BLOCK x0 x1)
		| (LOOP x0 x1) => (admininstr_LOOP x0 x1)
		| (IFELSE x0 x1 x2) => (admininstr_IFELSE x0 x1 x2)
		| (BR x0) => (admininstr_BR x0)
		| (BR_IF x0) => (admininstr_BR_IF x0)
		| (BR_TABLE x0 x1) => (admininstr_BR_TABLE x0 x1)
		| (CALL x0) => (admininstr_CALL x0)
		| (CALL_INDIRECT x0 x1) => (admininstr_CALL_INDIRECT x0 x1)
		| RETURN => admininstr_RETURN
		| (CONST x0 x1) => (admininstr_CONST x0 x1)
		| (UNOP x0 x1) => (admininstr_UNOP x0 x1)
		| (BINOP x0 x1) => (admininstr_BINOP x0 x1)
		| (TESTOP x0 x1) => (admininstr_TESTOP x0 x1)
		| (RELOP x0 x1) => (admininstr_RELOP x0 x1)
		| (CVTOP x0 x1 x2) => (admininstr_CVTOP x0 x1 x2)
		| (instr_EXTEND x0 x1) => (admininstr_EXTEND x0 x1)
		| (VCONST x0 x1) => (admininstr_VCONST x0 x1)
		| (VVUNOP x0 x1) => (admininstr_VVUNOP x0 x1)
		| (VVBINOP x0 x1) => (admininstr_VVBINOP x0 x1)
		| (VVTERNOP x0 x1) => (admininstr_VVTERNOP x0 x1)
		| (VVTESTOP x0 x1) => (admininstr_VVTESTOP x0 x1)
		| (VUNOP x0 x1) => (admininstr_VUNOP x0 x1)
		| (VBINOP x0 x1) => (admininstr_VBINOP x0 x1)
		| (VTESTOP x0 x1) => (admininstr_VTESTOP x0 x1)
		| (VRELOP x0 x1) => (admininstr_VRELOP x0 x1)
		| (VSHIFTOP x0 x1) => (admininstr_VSHIFTOP x0 x1)
		| (VBITMASK x0) => (admininstr_VBITMASK x0)
		| (VSWIZZLE x0) => (admininstr_VSWIZZLE x0)
		| (VSHUFFLE x0 x1) => (admininstr_VSHUFFLE x0 x1)
		| (VSPLAT x0) => (admininstr_VSPLAT x0)
		| (VEXTRACT_LANE x0 x1 x2) => (admininstr_VEXTRACT_LANE x0 x1 x2)
		| (VREPLACE_LANE x0 x1) => (admininstr_VREPLACE_LANE x0 x1)
		| (VEXTUNOP x0 x1 x2) => (admininstr_VEXTUNOP x0 x1 x2)
		| (VEXTBINOP x0 x1 x2) => (admininstr_VEXTBINOP x0 x1 x2)
		| (VNARROW x0 x1 x2) => (admininstr_VNARROW x0 x1 x2)
		| (VCVTOP x0 x1 x2) => (admininstr_VCVTOP x0 x1 x2)
		| (REF_NULL x0) => (admininstr_REF_NULL x0)
		| (REF_FUNC x0) => (admininstr_REF_FUNC x0)
		| REF_IS_NULL => admininstr_REF_IS_NULL
		| (LOCAL_GET x0) => (admininstr_LOCAL_GET x0)
		| (LOCAL_SET x0) => (admininstr_LOCAL_SET x0)
		| (LOCAL_TEE x0) => (admininstr_LOCAL_TEE x0)
		| (GLOBAL_GET x0) => (admininstr_GLOBAL_GET x0)
		| (GLOBAL_SET x0) => (admininstr_GLOBAL_SET x0)
		| (TABLE_GET x0) => (admininstr_TABLE_GET x0)
		| (TABLE_SET x0) => (admininstr_TABLE_SET x0)
		| (TABLE_SIZE x0) => (admininstr_TABLE_SIZE x0)
		| (TABLE_GROW x0) => (admininstr_TABLE_GROW x0)
		| (TABLE_FILL x0) => (admininstr_TABLE_FILL x0)
		| (TABLE_COPY x0 x1) => (admininstr_TABLE_COPY x0 x1)
		| (TABLE_INIT x0 x1) => (admininstr_TABLE_INIT x0 x1)
		| (ELEM_DROP x0) => (admininstr_ELEM_DROP x0)
		| (LOAD x0 x1 x2) => (admininstr_LOAD x0 x1 x2)
		| (STORE x0 x1 x2) => (admininstr_STORE x0 x1 x2)
		| (VLOAD x0 x1 x2) => (admininstr_VLOAD x0 x1 x2)
		| (VLOAD_LANE x0 x1 x2 x3) => (admininstr_VLOAD_LANE x0 x1 x2 x3)
		| (VSTORE x0 x1) => (admininstr_VSTORE x0 x1)
		| (VSTORE_LANE x0 x1 x2 x3) => (admininstr_VSTORE_LANE x0 x1 x2 x3)
		| MEMORY_SIZE => admininstr_MEMORY_SIZE
		| MEMORY_GROW => admininstr_MEMORY_GROW
		| MEMORY_FILL => admininstr_MEMORY_FILL
		| MEMORY_COPY => admininstr_MEMORY_COPY
		| (MEMORY_INIT x0) => (admininstr_MEMORY_INIT x0)
		| (DATA_DROP x0) => (admininstr_DATA_DROP x0)
	end.

(* Auxiliary Definition at:  *)
Definition admininstr_ref (var_0 : ref) : admininstr :=
	match var_0 return admininstr with
		| (ref_REF_NULL x0) => (admininstr_REF_NULL x0)
		| (REF_FUNC_ADDR x0) => (admininstr_REF_FUNC_ADDR x0)
		| (REF_HOST_ADDR x0) => (admininstr_REF_HOST_ADDR x0)
	end.

(* Auxiliary Definition at:  *)
Definition admininstr_val (var_0 : val) : admininstr :=
	match var_0 return admininstr with
		| (val_CONST x0 x1) => (admininstr_CONST x0 x1)
		| (val_VCONST x0 x1) => (admininstr_VCONST x0 x1)
		| (val_REF_NULL x0) => (admininstr_REF_NULL x0)
		| (val_REF_FUNC_ADDR x0) => (admininstr_REF_FUNC_ADDR x0)
		| (val_REF_HOST_ADDR x0) => (admininstr_REF_HOST_ADDR x0)
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
Inductive wf_admininstr : admininstr -> Prop :=
	| admininstr_case_0 : wf_admininstr admininstr_NOP
	| admininstr_case_1 : wf_admininstr admininstr_UNREACHABLE
	| admininstr_case_2 : wf_admininstr admininstr_DROP
	| admininstr_case_3 : forall (valtype_lst_opt : (option (seq valtype))), wf_admininstr (admininstr_SELECT valtype_lst_opt)
	| admininstr_case_4 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)), 
		(wf_blocktype v_blocktype) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		wf_admininstr (admininstr_BLOCK v_blocktype instr_lst)
	| admininstr_case_5 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)), 
		(wf_blocktype v_blocktype) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		wf_admininstr (admininstr_LOOP v_blocktype instr_lst)
	| admininstr_case_6 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst_0_lst : (seq instr)), 
		(wf_blocktype v_blocktype) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		List.Forall (fun (instr_lst_0 : instr) => (wf_instr instr_lst_0)) instr_lst_0_lst ->
		wf_admininstr (admininstr_IFELSE v_blocktype instr_lst instr_lst_0_lst)
	| admininstr_case_7 : forall (v_labelidx : labelidx), 
		(wf_uN 32 v_labelidx) ->
		wf_admininstr (admininstr_BR v_labelidx)
	| admininstr_case_8 : forall (v_labelidx : labelidx), 
		(wf_uN 32 v_labelidx) ->
		wf_admininstr (admininstr_BR_IF v_labelidx)
	| admininstr_case_9 : forall (labelidx_lst : (seq labelidx)) (v_labelidx : labelidx), 
		List.Forall (fun (v_labelidx : labelidx) => (wf_uN 32 v_labelidx)) labelidx_lst ->
		(wf_uN 32 v_labelidx) ->
		wf_admininstr (admininstr_BR_TABLE labelidx_lst v_labelidx)
	| admininstr_case_10 : forall (v_funcidx : funcidx), 
		(wf_uN 32 v_funcidx) ->
		wf_admininstr (admininstr_CALL v_funcidx)
	| admininstr_case_11 : forall (v_tableidx : tableidx) (v_typeidx : typeidx), 
		(wf_uN 32 v_tableidx) ->
		(wf_uN 32 v_typeidx) ->
		wf_admininstr (admininstr_CALL_INDIRECT v_tableidx v_typeidx)
	| admininstr_case_12 : wf_admininstr admininstr_RETURN
	| admininstr_case_13 : forall (v_numtype : numtype) (var_0 : num_), 
		(wf_num_ v_numtype var_0) ->
		wf_admininstr (admininstr_CONST v_numtype var_0)
	| admininstr_case_14 : forall (v_numtype : numtype) (var_0 : unop_), 
		(wf_unop_ v_numtype var_0) ->
		wf_admininstr (admininstr_UNOP v_numtype var_0)
	| admininstr_case_15 : forall (v_numtype : numtype) (var_0 : binop_), 
		(wf_binop_ v_numtype var_0) ->
		wf_admininstr (admininstr_BINOP v_numtype var_0)
	| admininstr_case_16 : forall (v_numtype : numtype) (var_0 : testop_), 
		(wf_testop_ v_numtype var_0) ->
		wf_admininstr (admininstr_TESTOP v_numtype var_0)
	| admininstr_case_17 : forall (v_numtype : numtype) (var_0 : relop_), 
		(wf_relop_ v_numtype var_0) ->
		wf_admininstr (admininstr_RELOP v_numtype var_0)
	| admininstr_case_18 : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop), 
		(numtype_1 != numtype_2) ->
		wf_admininstr (admininstr_CVTOP numtype_1 numtype_2 v_cvtop)
	| admininstr_case_19 : forall (v_numtype : numtype) (v_n : n), wf_admininstr (admininstr_EXTEND v_numtype v_n)
	| admininstr_case_20 : forall (v_vectype : vectype) (var_0 : vec_), 
		((res_size (valtype_vectype v_vectype)) != None) ->
		(wf_uN (!((res_size (valtype_vectype v_vectype)))) var_0) ->
		wf_admininstr (admininstr_VCONST v_vectype var_0)
	| admininstr_case_21 : forall (v_vectype : vectype) (v_vvunop : vvunop), wf_admininstr (admininstr_VVUNOP v_vectype v_vvunop)
	| admininstr_case_22 : forall (v_vectype : vectype) (v_vvbinop : vvbinop), wf_admininstr (admininstr_VVBINOP v_vectype v_vvbinop)
	| admininstr_case_23 : forall (v_vectype : vectype) (v_vvternop : vvternop), wf_admininstr (admininstr_VVTERNOP v_vectype v_vvternop)
	| admininstr_case_24 : forall (v_vectype : vectype) (v_vvtestop : vvtestop), wf_admininstr (admininstr_VVTESTOP v_vectype v_vvtestop)
	| admininstr_case_25 : forall (v_shape : shape) (var_0 : vunop_), 
		(wf_shape v_shape) ->
		(wf_vunop_ v_shape var_0) ->
		wf_admininstr (admininstr_VUNOP v_shape var_0)
	| admininstr_case_26 : forall (v_shape : shape) (var_0 : vbinop_), 
		(wf_shape v_shape) ->
		(wf_vbinop_ v_shape var_0) ->
		wf_admininstr (admininstr_VBINOP v_shape var_0)
	| admininstr_case_27 : forall (v_shape : shape) (var_0 : vtestop_), 
		(wf_shape v_shape) ->
		(wf_vtestop_ v_shape var_0) ->
		wf_admininstr (admininstr_VTESTOP v_shape var_0)
	| admininstr_case_28 : forall (v_shape : shape) (var_0 : vrelop_), 
		(wf_shape v_shape) ->
		(wf_vrelop_ v_shape var_0) ->
		wf_admininstr (admininstr_VRELOP v_shape var_0)
	| admininstr_case_29 : forall (v_ishape : ishape) (var_0 : vshiftop_), 
		(wf_ishape v_ishape) ->
		(wf_vshiftop_ v_ishape var_0) ->
		wf_admininstr (admininstr_VSHIFTOP v_ishape var_0)
	| admininstr_case_30 : forall (v_ishape : ishape), 
		(wf_ishape v_ishape) ->
		wf_admininstr (admininstr_VBITMASK v_ishape)
	| admininstr_case_31 : forall (v_ishape : ishape), 
		(wf_ishape v_ishape) ->
		(v_ishape == (ishape_X Jnn_I8 (mk_dim 16))) ->
		wf_admininstr (admininstr_VSWIZZLE v_ishape)
	| admininstr_case_32 : forall (v_ishape : ishape) (laneidx_lst : (seq laneidx)), 
		(wf_ishape v_ishape) ->
		List.Forall (fun (v_laneidx : laneidx) => (wf_uN 8 v_laneidx)) laneidx_lst ->
		((v_ishape == (ishape_X Jnn_I8 (mk_dim 16))) && ((|laneidx_lst|) == 16)) ->
		wf_admininstr (admininstr_VSHUFFLE v_ishape laneidx_lst)
	| admininstr_case_33 : forall (v_shape : shape), 
		(wf_shape v_shape) ->
		wf_admininstr (admininstr_VSPLAT v_shape)
	| admininstr_case_34 : forall (v_numtype : numtype) (v_shape : shape) (sx_opt : (option sx)) (v_laneidx : laneidx), 
		(wf_shape v_shape) ->
		(wf_uN 8 v_laneidx) ->
		(((fun_lanetype v_shape) == (lanetype_numtype v_numtype)) <-> (sx_opt == None)) ->
		wf_admininstr (admininstr_VEXTRACT_LANE v_shape sx_opt v_laneidx)
	| admininstr_case_35 : forall (v_shape : shape) (v_laneidx : laneidx), 
		(wf_shape v_shape) ->
		(wf_uN 8 v_laneidx) ->
		wf_admininstr (admininstr_VREPLACE_LANE v_shape v_laneidx)
	| admininstr_case_36 : forall (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextunop_), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(wf_vextunop_ ishape_1 var_0) ->
		((lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))%N) ->
		wf_admininstr (admininstr_VEXTUNOP ishape_1 ishape_2 var_0)
	| admininstr_case_37 : forall (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextbinop_), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(wf_vextbinop_ ishape_1 var_0) ->
		((lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))%N) ->
		wf_admininstr (admininstr_VEXTBINOP ishape_1 ishape_2 var_0)
	| admininstr_case_38 : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(((lsize (fun_lanetype (shape_ishape ishape_2))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))%N) && ((2 * (lsize (fun_lanetype (shape_ishape ishape_1))))%N <= 32)%N) ->
		wf_admininstr (admininstr_VNARROW ishape_1 ishape_2 v_sx)
	| admininstr_case_39 : forall (v_shape : shape) (shape_0 : shape) (v_vcvtop : vcvtop), 
		(wf_shape v_shape) ->
		(wf_shape shape_0) ->
		wf_admininstr (admininstr_VCVTOP v_shape shape_0 v_vcvtop)
	| admininstr_case_40 : forall (v_reftype : reftype), wf_admininstr (admininstr_REF_NULL v_reftype)
	| admininstr_case_41 : forall (v_funcidx : funcidx), 
		(wf_uN 32 v_funcidx) ->
		wf_admininstr (admininstr_REF_FUNC v_funcidx)
	| admininstr_case_42 : wf_admininstr admininstr_REF_IS_NULL
	| admininstr_case_43 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_admininstr (admininstr_LOCAL_GET v_localidx)
	| admininstr_case_44 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_admininstr (admininstr_LOCAL_SET v_localidx)
	| admininstr_case_45 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_admininstr (admininstr_LOCAL_TEE v_localidx)
	| admininstr_case_46 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_admininstr (admininstr_GLOBAL_GET v_globalidx)
	| admininstr_case_47 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_admininstr (admininstr_GLOBAL_SET v_globalidx)
	| admininstr_case_48 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_admininstr (admininstr_TABLE_GET v_tableidx)
	| admininstr_case_49 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_admininstr (admininstr_TABLE_SET v_tableidx)
	| admininstr_case_50 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_admininstr (admininstr_TABLE_SIZE v_tableidx)
	| admininstr_case_51 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_admininstr (admininstr_TABLE_GROW v_tableidx)
	| admininstr_case_52 : forall (v_tableidx : tableidx), 
		(wf_uN 32 v_tableidx) ->
		wf_admininstr (admininstr_TABLE_FILL v_tableidx)
	| admininstr_case_53 : forall (v_tableidx : tableidx) (tableidx_0 : tableidx), 
		(wf_uN 32 v_tableidx) ->
		(wf_uN 32 tableidx_0) ->
		wf_admininstr (admininstr_TABLE_COPY v_tableidx tableidx_0)
	| admininstr_case_54 : forall (v_tableidx : tableidx) (v_elemidx : elemidx), 
		(wf_uN 32 v_tableidx) ->
		(wf_uN 32 v_elemidx) ->
		wf_admininstr (admininstr_TABLE_INIT v_tableidx v_elemidx)
	| admininstr_case_55 : forall (v_elemidx : elemidx), 
		(wf_uN 32 v_elemidx) ->
		wf_admininstr (admininstr_ELEM_DROP v_elemidx)
	| admininstr_case_56 : forall (v_numtype : numtype) (var_0_opt : (option loadop_)) (v_memarg : memarg), 
		List.Forall (fun (var_0 : loadop_) => (wf_loadop_ v_numtype var_0)) (option_to_list var_0_opt) ->
		(wf_memarg v_memarg) ->
		wf_admininstr (admininstr_LOAD v_numtype var_0_opt v_memarg)
	| admininstr_case_57 : forall (Inn_opt : (option Inn)) (numtype_opt : (option numtype)) (v_numtype : numtype) (sz_opt : (option sz)) (v_memarg : memarg), 
		List.Forall (fun (v_sz : sz) => (wf_sz v_sz)) (option_to_list sz_opt) ->
		(wf_memarg v_memarg) ->
		((Inn_opt == None) <-> (numtype_opt == None)) ->
		((Inn_opt == None) <-> (sz_opt == None)) ->
		List_Forall3 (fun (v_Inn : Inn) (v_numtype : numtype) (v_sz : sz) => ((v_numtype == (numtype_Inn v_Inn)) && ((v_sz :> nat) < (sizenn (numtype_Inn v_Inn)))%N)) (option_to_list Inn_opt) (option_to_list numtype_opt) (option_to_list sz_opt) ->
		wf_admininstr (admininstr_STORE v_numtype sz_opt v_memarg)
	| admininstr_case_58 : forall (v_vectype : vectype) (vloadop_opt : (option vloadop)) (v_memarg : memarg), 
		(wf_memarg v_memarg) ->
		wf_admininstr (admininstr_VLOAD v_vectype vloadop_opt v_memarg)
	| admininstr_case_59 : forall (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx), 
		(wf_sz v_sz) ->
		(wf_memarg v_memarg) ->
		(wf_uN 8 v_laneidx) ->
		wf_admininstr (admininstr_VLOAD_LANE v_vectype v_sz v_memarg v_laneidx)
	| admininstr_case_60 : forall (v_vectype : vectype) (v_memarg : memarg), 
		(wf_memarg v_memarg) ->
		wf_admininstr (admininstr_VSTORE v_vectype v_memarg)
	| admininstr_case_61 : forall (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx), 
		(wf_sz v_sz) ->
		(wf_memarg v_memarg) ->
		(wf_uN 8 v_laneidx) ->
		wf_admininstr (admininstr_VSTORE_LANE v_vectype v_sz v_memarg v_laneidx)
	| admininstr_case_62 : wf_admininstr admininstr_MEMORY_SIZE
	| admininstr_case_63 : wf_admininstr admininstr_MEMORY_GROW
	| admininstr_case_64 : wf_admininstr admininstr_MEMORY_FILL
	| admininstr_case_65 : wf_admininstr admininstr_MEMORY_COPY
	| admininstr_case_66 : forall (v_dataidx : dataidx), 
		(wf_uN 32 v_dataidx) ->
		wf_admininstr (admininstr_MEMORY_INIT v_dataidx)
	| admininstr_case_67 : forall (v_dataidx : dataidx), 
		(wf_uN 32 v_dataidx) ->
		wf_admininstr (admininstr_DATA_DROP v_dataidx)
	| admininstr_case_68 : forall (v_funcaddr : funcaddr), wf_admininstr (admininstr_REF_FUNC_ADDR v_funcaddr)
	| admininstr_case_69 : forall (v_hostaddr : hostaddr), wf_admininstr (admininstr_REF_HOST_ADDR v_hostaddr)
	| admininstr_case_70 : forall (v_funcaddr : funcaddr), wf_admininstr (CALL_ADDR v_funcaddr)
	| admininstr_case_71 : forall (v_n : n) (instr_lst : (seq instr)) (admininstr_lst : (seq admininstr)), 
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		wf_admininstr (LABEL_ v_n instr_lst admininstr_lst)
	| admininstr_case_72 : forall (v_n : n) (v_frame : frame) (admininstr_lst : (seq admininstr)), 
		(wf_frame v_frame) ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		wf_admininstr (FRAME_ v_n v_frame admininstr_lst)
	| admininstr_case_73 : wf_admininstr admininstr_TRAP.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.1-117.62 *)
Inductive config : Type :=
	| mk_config (v_state : state) (admininstr_lst : (seq admininstr)) : config.

Global Instance Inhabited__config : Inhabited (config) := { default_val := mk_config default_val default_val }.

Definition config_eq_dec : forall (v1 v2 : config),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition config_eqb (v1 v2 : config) : bool :=
	is_left(config_eq_dec v1 v2).
Definition eqconfigP : Equality.axiom (config_eqb) :=
	eq_dec_Equality_axiom (config) (config_eq_dec).

HB.instance Definition _ := hasDecEq.Build (config) (eqconfigP).
Hint Resolve config_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.8-117.14 *)
Inductive wf_config : config -> Prop :=
	| config_case_0 : forall (v_state : state) (admininstr_lst : (seq admininstr)), 
		(wf_state v_state) ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		wf_config (mk_config v_state admininstr_lst).

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.1-7.43 *)
Definition default_ (v_valtype : valtype) : (option val) :=
	match v_valtype return (option val) with
		| valtype_I32 => (Some (val_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))
		| valtype_I64 => (Some (val_CONST I64 (mk_num__0 Inn_I64 (mk_uN 0))))
		| valtype_F32 => (Some (val_CONST F32 (mk_num__1 Fnn_F32 (fzero 32))))
		| valtype_F64 => (Some (val_CONST F64 (mk_num__1 Fnn_F64 (fzero 64))))
		| valtype_V128 => (Some (val_VCONST V128 (mk_uN 0)))
		| valtype_FUNCREF => (Some (val_REF_NULL FUNCREF))
		| valtype_EXTERNREF => (Some (val_REF_NULL EXTERNREF))
		| x0 => None
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.6-7.15 *)
Lemma default__is_wf : forall (v_valtype : valtype) (ret_val : val),
	((default_ v_valtype) != None) ->
	(ret_val == (!((default_ v_valtype)))) ->
	(wf_val ret_val).
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63 *)
Inductive fun_funcsxa : (seq externaddr) -> (seq funcaddr) -> Prop :=
	| fun_funcsxa_case_0 : fun_funcsxa [:: ] [:: ]
	| fun_funcsxa_case_1 : forall (fa : nat) (xv_lst : (seq externaddr)) (var_0 : (seq funcaddr)), 
		(fun_funcsxa xv_lst var_0) ->
		fun_funcsxa ([::(externaddr_FUNC fa)] ++ xv_lst) ([::fa] ++ var_0)
	| fun_funcsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (seq externaddr)) (var_0 : (seq funcaddr)), 
		(fun_funcsxa xv_lst var_0) ->
		fun_funcsxa ([::v_externaddr] ++ xv_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65 *)
Inductive fun_globalsxa : (seq externaddr) -> (seq globaladdr) -> Prop :=
	| fun_globalsxa_case_0 : fun_globalsxa [:: ] [:: ]
	| fun_globalsxa_case_1 : forall (ga : nat) (xv_lst : (seq externaddr)) (var_0 : (seq globaladdr)), 
		(fun_globalsxa xv_lst var_0) ->
		fun_globalsxa ([::(externaddr_GLOBAL ga)] ++ xv_lst) ([::ga] ++ var_0)
	| fun_globalsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (seq externaddr)) (var_0 : (seq globaladdr)), 
		(fun_globalsxa xv_lst var_0) ->
		fun_globalsxa ([::v_externaddr] ++ xv_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64 *)
Inductive fun_tablesxa : (seq externaddr) -> (seq tableaddr) -> Prop :=
	| fun_tablesxa_case_0 : fun_tablesxa [:: ] [:: ]
	| fun_tablesxa_case_1 : forall (ta : nat) (xv_lst : (seq externaddr)) (var_0 : (seq tableaddr)), 
		(fun_tablesxa xv_lst var_0) ->
		fun_tablesxa ([::(externaddr_TABLE ta)] ++ xv_lst) ([::ta] ++ var_0)
	| fun_tablesxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (seq externaddr)) (var_0 : (seq tableaddr)), 
		(fun_tablesxa xv_lst var_0) ->
		fun_tablesxa ([::v_externaddr] ++ xv_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62 *)
Inductive fun_memsxa : (seq externaddr) -> (seq memaddr) -> Prop :=
	| fun_memsxa_case_0 : fun_memsxa [:: ] [:: ]
	| fun_memsxa_case_1 : forall (ma : nat) (xv_lst : (seq externaddr)) (var_0 : (seq memaddr)), 
		(fun_memsxa xv_lst var_0) ->
		fun_memsxa ([::(externaddr_MEM ma)] ++ xv_lst) ([::ma] ++ var_0)
	| fun_memsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (seq externaddr)) (var_0 : (seq memaddr)), 
		(fun_memsxa xv_lst var_0) ->
		fun_memsxa ([::v_externaddr] ++ xv_lst) var_0.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.1-48.57 *)
Definition fun_store (v_state : state) : store :=
	match v_state return store with
		| (mk_state s f) => s
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.6-48.12 *)
Lemma store_is_wf : forall (v_state : state) (ret_val : store),
	(wf_state v_state) ->
	(ret_val == (fun_store v_state)) ->
	(wf_store ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57 *)
Definition fun_frame (v_state : state) : frame :=
	match v_state return frame with
		| (mk_state s f) => f
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.6-49.12 *)
Lemma frame_is_wf : forall (v_state : state) (ret_val : frame),
	(wf_state v_state) ->
	(ret_val == (fun_frame v_state)) ->
	(wf_frame ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:55.1-55.64 *)
Definition fun_funcaddr (v_state : state) : (seq funcaddr) :=
	match v_state return (seq funcaddr) with
		| (mk_state s f) => (FUNCS (frame_MODULE f))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.1-58.57 *)
Definition fun_funcinst (v_state : state) : (seq funcinst) :=
	match v_state return (seq funcinst) with
		| (mk_state s f) => (store_FUNCS s)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.6-58.15 *)
Lemma funcinst_is_wf : forall (v_state : state) (ret_val_lst : (seq funcinst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_funcinst v_state)) ->
	List.Forall (fun (ret_val : funcinst) => (wf_funcinst ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59 *)
Definition fun_globalinst (v_state : state) : (seq globalinst) :=
	match v_state return (seq globalinst) with
		| (mk_state s f) => (store_GLOBALS s)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.6-59.17 *)
Lemma globalinst_is_wf : forall (v_state : state) (ret_val_lst : (seq globalinst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_globalinst v_state)) ->
	List.Forall (fun (ret_val : globalinst) => (wf_globalinst ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58 *)
Definition fun_tableinst (v_state : state) : (seq tableinst) :=
	match v_state return (seq tableinst) with
		| (mk_state s f) => (store_TABLES s)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.6-60.16 *)
Lemma tableinst_is_wf : forall (v_state : state) (ret_val_lst : (seq tableinst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_tableinst v_state)) ->
	List.Forall (fun (ret_val : tableinst) => (wf_tableinst ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56 *)
Definition fun_meminst (v_state : state) : (seq meminst) :=
	match v_state return (seq meminst) with
		| (mk_state s f) => (store_MEMS s)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.6-61.14 *)
Lemma meminst_is_wf : forall (v_state : state) (ret_val_lst : (seq meminst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_meminst v_state)) ->
	List.Forall (fun (ret_val : meminst) => (wf_meminst ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:62.1-62.57 *)
Definition fun_eleminst (v_state : state) : (seq eleminst) :=
	match v_state return (seq eleminst) with
		| (mk_state s f) => (store_ELEMS s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.1-63.57 *)
Definition fun_datainst (v_state : state) : (seq datainst) :=
	match v_state return (seq datainst) with
		| (mk_state s f) => (store_DATAS s)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.6-63.15 *)
Lemma datainst_is_wf : forall (v_state : state) (ret_val_lst : (seq datainst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_datainst v_state)) ->
	List.Forall (fun (ret_val : datainst) => (wf_datainst ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58 *)
Definition fun_moduleinst (v_state : state) : moduleinst :=
	match v_state return moduleinst with
		| (mk_state s f) => (frame_MODULE f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.6-64.17 *)
Lemma moduleinst_is_wf : forall (v_state : state) (ret_val : moduleinst),
	(wf_state v_state) ->
	(ret_val == (fun_moduleinst v_state)) ->
	(wf_moduleinst ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:74.1-74.66 *)
Definition fun_type (v_state : state) (v_typeidx : typeidx) : functype :=
	match v_state, v_typeidx return functype with
		| (mk_state s f), x => ((TYPES (frame_MODULE f))[| (x :> nat) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.1-75.66 *)
Definition fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
	match v_state, v_funcidx return funcinst with
		| (mk_state s f), x => ((store_FUNCS s)[| ((FUNCS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.6-75.11 *)
Lemma func_is_wf : forall (v_state : state) (v_funcidx : funcidx) (ret_val : funcinst),
	(wf_state v_state) ->
	(wf_uN 32 v_funcidx) ->
	(ret_val == (fun_func v_state v_funcidx)) ->
	(wf_funcinst ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68 *)
Definition fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
	match v_state, v_globalidx return globalinst with
		| (mk_state s f), x => ((store_GLOBALS s)[| ((GLOBALS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.6-76.13 *)
Lemma global_is_wf : forall (v_state : state) (v_globalidx : globalidx) (ret_val : globalinst),
	(wf_state v_state) ->
	(wf_uN 32 v_globalidx) ->
	(ret_val == (fun_global v_state v_globalidx)) ->
	(wf_globalinst ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67 *)
Definition fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
	match v_state, v_tableidx return tableinst with
		| (mk_state s f), x => ((store_TABLES s)[| ((TABLES (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.6-77.12 *)
Lemma table_is_wf : forall (v_state : state) (v_tableidx : tableidx) (ret_val : tableinst),
	(wf_state v_state) ->
	(wf_uN 32 v_tableidx) ->
	(ret_val == (fun_table v_state v_tableidx)) ->
	(wf_tableinst ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65 *)
Definition fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
	match v_state, v_memidx return meminst with
		| (mk_state s f), x => ((store_MEMS s)[| ((MEMS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.6-78.10 *)
Lemma mem_is_wf : forall (v_state : state) (v_memidx : memidx) (ret_val : meminst),
	(wf_state v_state) ->
	(wf_uN 32 v_memidx) ->
	(ret_val == (fun_mem v_state v_memidx)) ->
	(wf_meminst ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:79.1-79.66 *)
Definition fun_elem (v_state : state) (v_tableidx : tableidx) : eleminst :=
	match v_state, v_tableidx return eleminst with
		| (mk_state s f), x => ((store_ELEMS s)[| ((ELEMS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.1-80.66 *)
Definition fun_data (v_state : state) (v_dataidx : dataidx) : datainst :=
	match v_state, v_dataidx return datainst with
		| (mk_state s f), x => ((store_DATAS s)[| ((DATAS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.6-80.11 *)
Lemma data_is_wf : forall (v_state : state) (v_dataidx : dataidx) (ret_val : datainst),
	(wf_state v_state) ->
	(wf_uN 32 v_dataidx) ->
	(ret_val == (fun_data v_state v_dataidx)) ->
	(wf_datainst ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67 *)
Definition fun_local (v_state : state) (v_localidx : localidx) : val :=
	match v_state, v_localidx return val with
		| (mk_state s f), x => ((LOCALS f)[| (x :> nat) |])
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.6-81.12 *)
Lemma local_is_wf : forall (v_state : state) (v_localidx : localidx) (ret_val : val),
	(wf_state v_state) ->
	(wf_uN 32 v_localidx) ->
	(ret_val == (fun_local v_state v_localidx)) ->
	(wf_val ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89 *)
Definition with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
	match v_state, v_localidx, v_val return state with
		| (mk_state s f), x, v => (mk_state s (f <| LOCALS := (list_update_func (LOCALS f) (x :> nat) (fun (_ : val) => v)) |>))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.6-95.17 *)
Lemma with_local_is_wf : forall (v_state : state) (v_localidx : localidx) (v_val : val) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32 v_localidx) ->
	(wf_val v_val) ->
	(ret_val == (with_local v_state v_localidx v_val)) ->
	(wf_state ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96 *)
Definition with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
	match v_state, v_globalidx, v_val return state with
		| (mk_state s f), x, v => (mk_state (s <| store_GLOBALS := (list_update_func (store_GLOBALS s) ((GLOBALS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : globalinst) => (var_1 <| VALUE := v |>))) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.6-96.18 *)
Lemma with_global_is_wf : forall (v_state : state) (v_globalidx : globalidx) (v_val : val) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32 v_globalidx) ->
	(wf_val v_val) ->
	(ret_val == (with_global v_state v_globalidx v_val)) ->
	(wf_state ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97 *)
Definition with_table (v_state : state) (v_tableidx : tableidx) (res_nat : nat) (v_ref : ref) : state :=
	match v_state, v_tableidx, res_nat, v_ref return state with
		| (mk_state s f), x, i, r => (mk_state (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : tableinst) => (var_1 <| REFS := (list_update_func (REFS var_1) i (fun (_ : ref) => r)) |>))) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.6-97.17 *)
Lemma with_table_is_wf : forall (v_state : state) (v_tableidx : tableidx) (res_nat : nat) (v_ref : ref) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32 v_tableidx) ->
	(ret_val == (with_table v_state v_tableidx res_nat v_ref)) ->
	(wf_state ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89 *)
Definition with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
	match v_state, v_tableidx, v_tableinst return state with
		| (mk_state s f), x, ti => (mk_state (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f))[| (x :> nat) |]) (fun (_ : tableinst) => ti)) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.6-98.21 *)
Lemma with_tableinst_is_wf : forall (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32 v_tableidx) ->
	(wf_tableinst v_tableinst) ->
	(ret_val == (with_tableinst v_state v_tableidx v_tableinst)) ->
	(wf_state ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100 *)
Definition with_mem (v_state : state) (v_memidx : memidx) (res_nat : nat) (nat_0 : nat) (var_0_lst : (seq byte)) : state :=
	match v_state, v_memidx, res_nat, nat_0, var_0_lst return state with
		| (mk_state s f), x, i, j, b_lst => (mk_state (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (BYTES var_1) i j b_lst) |>))) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.6-99.15 *)
Lemma with_mem_is_wf : forall (v_state : state) (v_memidx : memidx) (res_nat : nat) (nat_0 : nat) (var_0_lst : (seq byte)) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32 v_memidx) ->
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (with_mem v_state v_memidx res_nat nat_0 var_0_lst)) ->
	(wf_state ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87 *)
Definition with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
	match v_state, v_memidx, v_meminst return state with
		| (mk_state s f), x, mi => (mk_state (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f))[| (x :> nat) |]) (fun (_ : meminst) => mi)) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.6-100.19 *)
Lemma with_meminst_is_wf : forall (v_state : state) (v_memidx : memidx) (v_meminst : meminst) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32 v_memidx) ->
	(wf_meminst v_meminst) ->
	(ret_val == (with_meminst v_state v_memidx v_meminst)) ->
	(wf_state ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93 *)
Definition with_elem (v_state : state) (v_elemidx : elemidx) (var_0_lst : (seq ref)) : state :=
	match v_state, v_elemidx, var_0_lst return state with
		| (mk_state s f), x, r_lst => (mk_state (s <| store_ELEMS := (list_update_func (store_ELEMS s) ((ELEMS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : eleminst) => (var_1 <| eleminst_REFS := r_lst |>))) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.6-101.16 *)
Lemma with_elem_is_wf : forall (v_state : state) (v_elemidx : elemidx) (var_0_lst : (seq ref)) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32 v_elemidx) ->
	(ret_val == (with_elem v_state v_elemidx var_0_lst)) ->
	(wf_state ret_val).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94 *)
Definition with_data (v_state : state) (v_dataidx : dataidx) (var_0_lst : (seq byte)) : state :=
	match v_state, v_dataidx, var_0_lst return state with
		| (mk_state s f), x, b_lst => (mk_state (s <| store_DATAS := (list_update_func (store_DATAS s) ((DATAS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : datainst) => (var_1 <| datainst_BYTES := b_lst |>))) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.6-102.16 *)
Lemma with_data_is_wf : forall (v_state : state) (v_dataidx : dataidx) (var_0_lst : (seq byte)) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32 v_dataidx) ->
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (with_data v_state v_dataidx var_0_lst)) ->
	(wf_state ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
Inductive fun_growtable_before_fun_growtable_case_1 : tableinst -> nat -> ref -> Prop :=
	| fun_growtable_case_0 : forall (ti : tableinst) (v_n : nat) (r : ref) (ti' : tableinst) (i : u32) (j_opt : (option u32)) (rt : reftype) (r'_lst : (seq ref)) (i' : nat), 
		({| tableinst_TYPE := (mk_tabletype (mk_limits i j_opt) rt); REFS := r'_lst |} == ti) ->
		(i' == ((|r'_lst|) + v_n)%N) ->
		List.Forall (fun (j_2 : u32) => (i' <= (j_2 :> nat))%N) (option_to_list j_opt) ->
		(ti' == {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN i') j_opt) rt); REFS := (r'_lst ++ (List.repeat r v_n)) |}) ->
		(wf_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits i j_opt) rt); REFS := r'_lst |}) ->
		(wf_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN i') j_opt) rt); REFS := (r'_lst ++ (List.repeat r v_n)) |}) ->
		fun_growtable_before_fun_growtable_case_1 ti v_n r.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
Inductive fun_growtable : tableinst -> nat -> ref -> (option tableinst) -> Prop :=
	| fun_growtable__fun_growtable_case_0 : forall (ti : tableinst) (v_n : nat) (r : ref) (ti' : tableinst) (i : u32) (j_opt : (option u32)) (rt : reftype) (r'_lst : (seq ref)) (i' : nat), 
		({| tableinst_TYPE := (mk_tabletype (mk_limits i j_opt) rt); REFS := r'_lst |} == ti) ->
		(i' == ((|r'_lst|) + v_n)%N) ->
		List.Forall (fun (j_2 : u32) => (i' <= (j_2 :> nat))%N) (option_to_list j_opt) ->
		(ti' == {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN i') j_opt) rt); REFS := (r'_lst ++ (List.repeat r v_n)) |}) ->
		(wf_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits i j_opt) rt); REFS := r'_lst |}) ->
		(wf_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN i') j_opt) rt); REFS := (r'_lst ++ (List.repeat r v_n)) |}) ->
		fun_growtable ti v_n r (Some ti')
	| fun_growtable_case_1 : forall (x0 : tableinst) (x1 : nat) (x2 : ref), 
		(~(fun_growtable_before_fun_growtable_case_1 x0 x1 x2)) ->
		fun_growtable x0 x1 x2 None.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
Lemma growtable_is_wf : forall (v_tableinst : tableinst) (res_nat : nat) (v_ref : ref) (ret_val : tableinst) (var_0 : (option tableinst)),
	(fun_growtable v_tableinst res_nat v_ref var_0) ->
	(wf_tableinst v_tableinst) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_tableinst ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
Inductive fun_growmemory_before_fun_growmemory_case_1 : meminst -> nat -> Prop :=
	| fun_growmemory_case_0 : forall (mi : meminst) (v_n : nat) (mi' : meminst) (i : u32) (j_opt : (option u32)) (b_lst : (seq byte)) (i' : rat), 
		({| meminst_TYPE := (PAGE (mk_limits i j_opt)); BYTES := b_lst |} == mi) ->
		(i' == ((((|b_lst|) : rat) / ((64 * (Ki ))%N : rat))%Q + (v_n : rat))%Q) ->
		List.Forall (fun (j_7 : u32) => (i' <= ((j_7 :> nat) : rat))%Q) (option_to_list j_opt) ->
		(mi' == {| meminst_TYPE := (PAGE (mk_limits (mk_uN (i' : nat)) j_opt)); BYTES := (b_lst ++ (List.repeat (mk_byte 0) (v_n * (64 * (Ki ))%N)%N)) |}) ->
		(wf_meminst {| meminst_TYPE := (PAGE (mk_limits i j_opt)); BYTES := b_lst |}) ->
		(wf_meminst {| meminst_TYPE := (PAGE (mk_limits (mk_uN (i' : nat)) j_opt)); BYTES := (b_lst ++ (List.repeat (mk_byte 0) (v_n * (64 * (Ki ))%N)%N)) |}) ->
		fun_growmemory_before_fun_growmemory_case_1 mi v_n.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
Inductive fun_growmemory : meminst -> nat -> (option meminst) -> Prop :=
	| fun_growmemory__fun_growmemory_case_0 : forall (mi : meminst) (v_n : nat) (mi' : meminst) (i : u32) (j_opt : (option u32)) (b_lst : (seq byte)) (i' : rat), 
		({| meminst_TYPE := (PAGE (mk_limits i j_opt)); BYTES := b_lst |} == mi) ->
		(i' == ((((|b_lst|) : rat) / ((64 * (Ki ))%N : rat))%Q + (v_n : rat))%Q) ->
		List.Forall (fun (j_7 : u32) => (i' <= ((j_7 :> nat) : rat))%Q) (option_to_list j_opt) ->
		(mi' == {| meminst_TYPE := (PAGE (mk_limits (mk_uN (i' : nat)) j_opt)); BYTES := (b_lst ++ (List.repeat (mk_byte 0) (v_n * (64 * (Ki ))%N)%N)) |}) ->
		(wf_meminst {| meminst_TYPE := (PAGE (mk_limits i j_opt)); BYTES := b_lst |}) ->
		(wf_meminst {| meminst_TYPE := (PAGE (mk_limits (mk_uN (i' : nat)) j_opt)); BYTES := (b_lst ++ (List.repeat (mk_byte 0) (v_n * (64 * (Ki ))%N)%N)) |}) ->
		fun_growmemory mi v_n (Some mi')
	| fun_growmemory_case_1 : forall (x0 : meminst) (x1 : nat), 
		(~(fun_growmemory_before_fun_growmemory_case_1 x0 x1)) ->
		fun_growmemory x0 x1 None.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
Lemma growmemory_is_wf : forall (v_meminst : meminst) (res_nat : nat) (ret_val : meminst) (var_0 : (option meminst)),
	(fun_growmemory v_meminst res_nat var_0) ->
	(wf_meminst v_meminst) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_meminst ret_val).
Proof. Admitted.

(* Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 *)
Record context := MKcontext
{	context_TYPES : (seq functype)
;	context_FUNCS : (seq functype)
;	context_GLOBALS : (seq globaltype)
;	context_TABLES : (seq tabletype)
;	context_MEMS : (seq memtype)
;	context_ELEMS : (seq elemtype)
;	context_DATAS : (seq datatype)
;	context_LOCALS : (seq valtype)
;	LABELS : (seq resulttype)
;	context_RETURN : (option resulttype)
}.

Global Instance Inhabited_context : Inhabited (context) := 
{default_val := {|
	context_TYPES := default_val;
	context_FUNCS := default_val;
	context_GLOBALS := default_val;
	context_TABLES := default_val;
	context_MEMS := default_val;
	context_ELEMS := default_val;
	context_DATAS := default_val;
	context_LOCALS := default_val;
	LABELS := default_val;
	context_RETURN := default_val|} }.

Definition _append_context (arg1 arg2 : (context)) :=
{|
	context_TYPES := arg1.(context_TYPES) @@ arg2.(context_TYPES);
	context_FUNCS := arg1.(context_FUNCS) @@ arg2.(context_FUNCS);
	context_GLOBALS := arg1.(context_GLOBALS) @@ arg2.(context_GLOBALS);
	context_TABLES := arg1.(context_TABLES) @@ arg2.(context_TABLES);
	context_MEMS := arg1.(context_MEMS) @@ arg2.(context_MEMS);
	context_ELEMS := arg1.(context_ELEMS) @@ arg2.(context_ELEMS);
	context_DATAS := arg1.(context_DATAS) @@ arg2.(context_DATAS);
	context_LOCALS := arg1.(context_LOCALS) @@ arg2.(context_LOCALS);
	LABELS := arg1.(LABELS) @@ arg2.(LABELS);
	context_RETURN := arg1.(context_RETURN) @@ arg2.(context_RETURN);
|}.

Global Instance Append_context : Append context := { _append arg1 arg2 := _append_context arg1 arg2 }.

#[export] Instance eta__context : Settable _ := settable! MKcontext <context_TYPES;context_FUNCS;context_GLOBALS;context_TABLES;context_MEMS;context_ELEMS;context_DATAS;context_LOCALS;LABELS;context_RETURN>.

Definition context_eq_dec : forall (v1 v2 : context),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition context_eqb (v1 v2 : context) : bool :=
	is_left(context_eq_dec v1 v2).
Definition eqcontextP : Equality.axiom (context_eqb) :=
	eq_dec_Equality_axiom (context) (context_eq_dec).

HB.instance Definition _ := hasDecEq.Build (context) (eqcontextP).
Hint Resolve context_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:5.8-5.15 *)
Inductive wf_context : context -> Prop :=
	| context_case_ : forall (var_0_lst : (seq functype)) (var_1_lst : (seq functype)) (var_2_lst : (seq globaltype)) (var_3_lst : (seq tabletype)) (var_4_lst : (seq memtype)) (var_5_lst : (seq elemtype)) (var_6_lst : (seq datatype)) (var_7_lst : (seq valtype)) (var_8_lst : (seq resulttype)) (var_9_opt : (option resulttype)), 
		List.Forall (fun (var_3 : tabletype) => (wf_tabletype var_3)) var_3_lst ->
		List.Forall (fun (var_4 : memtype) => (wf_memtype var_4)) var_4_lst ->
		wf_context {| context_TYPES := var_0_lst; context_FUNCS := var_1_lst; context_GLOBALS := var_2_lst; context_TABLES := var_3_lst; context_MEMS := var_4_lst; context_ELEMS := var_5_lst; context_DATAS := var_6_lst; context_LOCALS := var_7_lst; LABELS := var_8_lst; context_RETURN := var_9_opt |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:19.1-19.66 *)
Inductive Limits_ok : limits -> nat -> Prop :=
	| mk_Limits_ok : forall (v_n : n) (m_opt : (option m)) (k : nat), 
		(v_n <= k)%N ->
		List.Forall (fun (v_m : nat) => ((v_n <= v_m)%N && (v_m <= k)%N)) (option_to_list m_opt) ->
		(wf_limits (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))) ->
		Limits_ok (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) k.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:20.1-20.64 *)
Inductive Functype_ok : functype -> Prop :=
	| mk_Functype_ok : forall (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), Functype_ok (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:21.1-21.66 *)
Inductive Globaltype_ok : globaltype -> Prop :=
	| mk_Globaltype_ok : forall (t : valtype), Globaltype_ok (mk_globaltype (Some MUT) t).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:22.1-22.65 *)
Inductive Tabletype_ok : tabletype -> Prop :=
	| mk_Tabletype_ok : forall (v_limits : limits) (v_reftype : reftype), 
		(Limits_ok v_limits ((((2 ^ 32)%N : int) - (1 : int))%Z : nat)) ->
		(wf_tabletype (mk_tabletype v_limits v_reftype)) ->
		Tabletype_ok (mk_tabletype v_limits v_reftype).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:23.1-23.63 *)
Inductive Memtype_ok : memtype -> Prop :=
	| mk_Memtype_ok : forall (v_limits : limits), 
		(Limits_ok v_limits (2 ^ 16)%N) ->
		(wf_memtype (PAGE v_limits)) ->
		Memtype_ok (PAGE v_limits).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:24.1-24.66 *)
Inductive Externtype_ok : externtype -> Prop :=
	| Externtype_ok__func : forall (v_functype : functype), 
		(Functype_ok v_functype) ->
		(wf_externtype (FUNC v_functype)) ->
		Externtype_ok (FUNC v_functype)
	| Externtype_ok__global : forall (v_globaltype : globaltype), 
		(Globaltype_ok v_globaltype) ->
		(wf_externtype (GLOBAL v_globaltype)) ->
		Externtype_ok (GLOBAL v_globaltype)
	| Externtype_ok__table : forall (v_tabletype : tabletype), 
		(Tabletype_ok v_tabletype) ->
		(wf_externtype (TABLE v_tabletype)) ->
		Externtype_ok (TABLE v_tabletype)
	| Externtype_ok__mem : forall (v_memtype : memtype), 
		(Memtype_ok v_memtype) ->
		(wf_externtype (MEM v_memtype)) ->
		Externtype_ok (MEM v_memtype).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:71.1-71.69 *)
Inductive Valtype_sub : valtype -> valtype -> Prop :=
	| refl : forall (t : valtype), Valtype_sub t t
	| bot : forall (t : valtype), Valtype_sub BOT t.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:72.1-72.76 *)
Inductive Resulttype_sub : resulttype -> resulttype -> Prop :=
	| mk_Resulttype_sub : forall (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((|t_1_lst|) == (|t_2_lst|)) ->
		List.Forall2 (fun (t_1 : valtype) (t_2 : valtype) => (Valtype_sub t_1 t_2)) t_1_lst t_2_lst ->
		Resulttype_sub (mk_list _ t_1_lst) (mk_list _ t_2_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:87.1-87.75 *)
Inductive Limits_sub : limits -> limits -> Prop :=
	| mk_Limits_sub : forall (n_11 : n) (n_12 : n) (n_21 : n) (n_22 : n), 
		(n_11 >= n_21)%N ->
		(n_12 <= n_22)%N ->
		(wf_limits (mk_limits (mk_uN n_11) (Some (mk_uN n_12)))) ->
		(wf_limits (mk_limits (mk_uN n_21) (Some (mk_uN n_22)))) ->
		Limits_sub (mk_limits (mk_uN n_11) (Some (mk_uN n_12))) (mk_limits (mk_uN n_21) (Some (mk_uN n_22))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:88.1-88.73 *)
Inductive Functype_sub : functype -> functype -> Prop :=
	| mk_Functype_sub : forall (ft : functype), Functype_sub ft ft.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:89.1-89.75 *)
Inductive Globaltype_sub : globaltype -> globaltype -> Prop :=
	| mk_Globaltype_sub : forall (gt : globaltype), Globaltype_sub gt gt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:90.1-90.74 *)
Inductive Tabletype_sub : tabletype -> tabletype -> Prop :=
	| mk_Tabletype_sub : forall (lim_1 : limits) (rt : reftype) (lim_2 : limits), 
		(Limits_sub lim_1 lim_2) ->
		(wf_tabletype (mk_tabletype lim_1 rt)) ->
		(wf_tabletype (mk_tabletype lim_2 rt)) ->
		Tabletype_sub (mk_tabletype lim_1 rt) (mk_tabletype lim_2 rt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:91.1-91.72 *)
Inductive Memtype_sub : memtype -> memtype -> Prop :=
	| mk_Memtype_sub : forall (lim_1 : limits) (lim_2 : limits), 
		(Limits_sub lim_1 lim_2) ->
		(wf_memtype (PAGE lim_1)) ->
		(wf_memtype (PAGE lim_2)) ->
		Memtype_sub (PAGE lim_1) (PAGE lim_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:92.1-92.75 *)
Inductive Externtype_sub : externtype -> externtype -> Prop :=
	| Externtype_sub__func : forall (ft_1 : functype) (ft_2 : functype), 
		(Functype_sub ft_1 ft_2) ->
		(wf_externtype (FUNC ft_1)) ->
		(wf_externtype (FUNC ft_2)) ->
		Externtype_sub (FUNC ft_1) (FUNC ft_2)
	| Externtype_sub__global : forall (gt_1 : globaltype) (gt_2 : globaltype), 
		(Globaltype_sub gt_1 gt_2) ->
		(wf_externtype (GLOBAL gt_1)) ->
		(wf_externtype (GLOBAL gt_2)) ->
		Externtype_sub (GLOBAL gt_1) (GLOBAL gt_2)
	| Externtype_sub__table : forall (tt_1 : tabletype) (tt_2 : tabletype), 
		(Tabletype_sub tt_1 tt_2) ->
		(wf_externtype (TABLE tt_1)) ->
		(wf_externtype (TABLE tt_2)) ->
		Externtype_sub (TABLE tt_1) (TABLE tt_2)
	| Externtype_sub__mem : forall (mt_1 : memtype) (mt_2 : memtype), 
		(Memtype_sub mt_1 mt_2) ->
		(wf_externtype (MEM mt_1)) ->
		(wf_externtype (MEM mt_2)) ->
		Externtype_sub (MEM mt_1) (MEM mt_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:198.1-198.76 *)
Inductive Blocktype_ok : context -> blocktype -> functype -> Prop :=
	| Blocktype_ok__valtype : forall (C : context) (valtype_opt : (option valtype)), 
		(wf_context C) ->
		(wf_blocktype (_RESULT valtype_opt)) ->
		Blocktype_ok C (_RESULT valtype_opt) (mk_functype (mk_list _ [:: ]) (mk_list _ (option_to_list valtype_opt)))
	| Blocktype_ok__typeidx : forall (C : context) (v_typeidx : typeidx) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((v_typeidx :> nat) < (|(context_TYPES C)|))%N ->
		(((context_TYPES C)[| (v_typeidx :> nat) |]) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_context C) ->
		(wf_blocktype (_IDX v_typeidx)) ->
		Blocktype_ok C (_IDX v_typeidx) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)).

(* Mutual Recursion at: ../specification/wasm-2.0/6-typing.spectec:137.1-138.65 *)
Inductive Instr_ok : context -> instr -> functype -> Prop :=
	| nop : forall (C : context), 
		(wf_context C) ->
		(wf_instr NOP) ->
		Instr_ok C NOP (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| unreachable : forall (C : context) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(wf_context C) ->
		(wf_instr UNREACHABLE) ->
		Instr_ok C UNREACHABLE (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| drop : forall (C : context) (t : valtype), 
		(wf_context C) ->
		(wf_instr DROP) ->
		Instr_ok C DROP (mk_functype (mk_list _ [::t]) (mk_list _ [:: ]))
	| select_expl : forall (C : context) (t : valtype), 
		(wf_context C) ->
		(wf_instr (SELECT (Some [::t]))) ->
		Instr_ok C (SELECT (Some [::t])) (mk_functype (mk_list _ [::t; t; valtype_I32]) (mk_list _ [::t]))
	| select_impl : forall (C : context) (t : valtype) (t' : valtype) (v_numtype : numtype) (v_vectype : vectype), 
		(Valtype_sub t t') ->
		((t' == (valtype_numtype v_numtype)) || (t' == (valtype_vectype v_vectype))) ->
		(wf_context C) ->
		(wf_instr (SELECT None)) ->
		Instr_ok C (SELECT None) (mk_functype (mk_list _ [::t; t; valtype_I32]) (mk_list _ [::t]))
	| block : forall (C : context) (bt : blocktype) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Blocktype_ok C bt (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := None |} @@ C) instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_context C) ->
		(wf_instr (BLOCK bt instr_lst)) ->
		(wf_context {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := None |}) ->
		Instr_ok C (BLOCK bt instr_lst) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| loop : forall (C : context) (bt : blocktype) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Blocktype_ok C bt (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_1_lst)]; context_RETURN := None |} @@ C) instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_context C) ->
		(wf_instr (LOOP bt instr_lst)) ->
		(wf_context {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_1_lst)]; context_RETURN := None |}) ->
		Instr_ok C (LOOP bt instr_lst) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| res_if : forall (C : context) (bt : blocktype) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Blocktype_ok C bt (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := None |} @@ C) instr_1_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := None |} @@ C) instr_2_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_context C) ->
		(wf_instr (IFELSE bt instr_1_lst instr_2_lst)) ->
		(wf_context {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := None |}) ->
		Instr_ok C (IFELSE bt instr_1_lst instr_2_lst) (mk_functype (mk_list _ (t_1_lst ++ [::valtype_I32])) (mk_list _ t_2_lst))
	| br : forall (C : context) (l : labelidx) (t_1_lst : (seq valtype)) (t_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((l :> nat) < (|(LABELS C)|))%N ->
		((proj_list_0 valtype ((LABELS C)[| (l :> nat) |])) == t_lst) ->
		(wf_context C) ->
		(wf_instr (BR l)) ->
		Instr_ok C (BR l) (mk_functype (mk_list _ (t_1_lst ++ t_lst)) (mk_list _ t_2_lst))
	| br_if : forall (C : context) (l : labelidx) (t_lst : (seq valtype)), 
		((l :> nat) < (|(LABELS C)|))%N ->
		((proj_list_0 valtype ((LABELS C)[| (l :> nat) |])) == t_lst) ->
		(wf_context C) ->
		(wf_instr (BR_IF l)) ->
		Instr_ok C (BR_IF l) (mk_functype (mk_list _ (t_lst ++ [::valtype_I32])) (mk_list _ t_lst))
	| br_table : forall (C : context) (l_lst : (seq labelidx)) (l' : labelidx) (t_1_lst : (seq valtype)) (t_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		List.Forall (fun (l : labelidx) => ((l :> nat) < (|(LABELS C)|))%N) l_lst ->
		List.Forall (fun (l : labelidx) => (Resulttype_sub (mk_list _ t_lst) ((LABELS C)[| (l :> nat) |]))) l_lst ->
		((l' :> nat) < (|(LABELS C)|))%N ->
		(Resulttype_sub (mk_list _ t_lst) ((LABELS C)[| (l' :> nat) |])) ->
		(wf_context C) ->
		(wf_instr (BR_TABLE l_lst l')) ->
		Instr_ok C (BR_TABLE l_lst l') (mk_functype (mk_list _ (t_1_lst ++ (t_lst ++ [::valtype_I32]))) (mk_list _ t_2_lst))
	| call : forall (C : context) (x : idx) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((x :> nat) < (|(context_FUNCS C)|))%N ->
		(((context_FUNCS C)[| (x :> nat) |]) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_context C) ->
		(wf_instr (CALL x)) ->
		Instr_ok C (CALL x) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| call_indirect : forall (C : context) (x : idx) (y : idx) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim FUNCREF)) ->
		((y :> nat) < (|(context_TYPES C)|))%N ->
		(((context_TYPES C)[| (y :> nat) |]) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_context C) ->
		(wf_instr (CALL_INDIRECT x y)) ->
		(wf_tabletype (mk_tabletype lim FUNCREF)) ->
		Instr_ok C (CALL_INDIRECT x y) (mk_functype (mk_list _ (t_1_lst ++ [::valtype_I32])) (mk_list _ t_2_lst))
	| res_return : forall (C : context) (t_1_lst : (seq valtype)) (t_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((context_RETURN C) == (Some (mk_list _ t_lst))) ->
		(wf_context C) ->
		(wf_instr RETURN) ->
		Instr_ok C RETURN (mk_functype (mk_list _ (t_1_lst ++ t_lst)) (mk_list _ t_2_lst))
	| const : forall (C : context) (nt : numtype) (c_nt : num_), 
		(wf_context C) ->
		(wf_instr (CONST nt c_nt)) ->
		Instr_ok C (CONST nt c_nt) (mk_functype (mk_list _ [:: ]) (mk_list _ [::(valtype_numtype nt)]))
	| unop : forall (C : context) (nt : numtype) (unop_nt : unop_), 
		(wf_context C) ->
		(wf_instr (UNOP nt unop_nt)) ->
		Instr_ok C (UNOP nt unop_nt) (mk_functype (mk_list _ [::(valtype_numtype nt)]) (mk_list _ [::(valtype_numtype nt)]))
	| binop : forall (C : context) (nt : numtype) (binop_nt : binop_), 
		(wf_context C) ->
		(wf_instr (BINOP nt binop_nt)) ->
		Instr_ok C (BINOP nt binop_nt) (mk_functype (mk_list _ [::(valtype_numtype nt); (valtype_numtype nt)]) (mk_list _ [::(valtype_numtype nt)]))
	| testop : forall (C : context) (nt : numtype) (testop_nt : testop_), 
		(wf_context C) ->
		(wf_instr (TESTOP nt testop_nt)) ->
		Instr_ok C (TESTOP nt testop_nt) (mk_functype (mk_list _ [::(valtype_numtype nt)]) (mk_list _ [::valtype_I32]))
	| relop : forall (C : context) (nt : numtype) (relop_nt : relop_), 
		(wf_context C) ->
		(wf_instr (RELOP nt relop_nt)) ->
		Instr_ok C (RELOP nt relop_nt) (mk_functype (mk_list _ [::(valtype_numtype nt); (valtype_numtype nt)]) (mk_list _ [::valtype_I32]))
	| cvtop_reinterpret : forall (C : context) (nt_1 : numtype) (nt_2 : numtype), 
		((res_size (valtype_numtype nt_1)) != None) ->
		((res_size (valtype_numtype nt_2)) != None) ->
		((!((res_size (valtype_numtype nt_1)))) == (!((res_size (valtype_numtype nt_2))))) ->
		(wf_context C) ->
		(wf_instr (CVTOP nt_1 nt_2 REINTERPRET)) ->
		Instr_ok C (CVTOP nt_1 nt_2 REINTERPRET) (mk_functype (mk_list _ [::(valtype_numtype nt_2)]) (mk_list _ [::(valtype_numtype nt_1)]))
	| cvtop_convert : forall (C : context) (nt_1 : numtype) (nt_2 : numtype) (v_cvtop : cvtop), 
		(wf_context C) ->
		(wf_instr (CVTOP nt_1 nt_2 v_cvtop)) ->
		Instr_ok C (CVTOP nt_1 nt_2 v_cvtop) (mk_functype (mk_list _ [::(valtype_numtype nt_2)]) (mk_list _ [::(valtype_numtype nt_1)]))
	| ref_null : forall (C : context) (rt : reftype), 
		(wf_context C) ->
		(wf_instr (REF_NULL rt)) ->
		Instr_ok C (REF_NULL rt) (mk_functype (mk_list _ [:: ]) (mk_list _ [::(valtype_reftype rt)]))
	| ref_func : forall (C : context) (x : idx) (ft : functype), 
		((x :> nat) < (|(context_FUNCS C)|))%N ->
		(((context_FUNCS C)[| (x :> nat) |]) == ft) ->
		(wf_context C) ->
		(wf_instr (REF_FUNC x)) ->
		Instr_ok C (REF_FUNC x) (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_FUNCREF]))
	| ref_is_null : forall (C : context) (rt : reftype), 
		(wf_context C) ->
		(wf_instr REF_IS_NULL) ->
		Instr_ok C REF_IS_NULL (mk_functype (mk_list _ [::(valtype_reftype rt)]) (mk_list _ [::valtype_I32]))
	| vconst : forall (C : context) (c : vec_), 
		(wf_context C) ->
		(wf_instr (VCONST V128 c)) ->
		Instr_ok C (VCONST V128 c) (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vvunop : forall (C : context) (v_vvunop : vvunop), 
		(wf_context C) ->
		(wf_instr (VVUNOP V128 v_vvunop)) ->
		Instr_ok C (VVUNOP V128 v_vvunop) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vvbinop : forall (C : context) (v_vvbinop : vvbinop), 
		(wf_context C) ->
		(wf_instr (VVBINOP V128 v_vvbinop)) ->
		Instr_ok C (VVBINOP V128 v_vvbinop) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vvternop : forall (C : context) (v_vvternop : vvternop), 
		(wf_context C) ->
		(wf_instr (VVTERNOP V128 v_vvternop)) ->
		Instr_ok C (VVTERNOP V128 v_vvternop) (mk_functype (mk_list _ [::valtype_V128; valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vvtestop : forall (C : context) (v_vvtestop : vvtestop), 
		(wf_context C) ->
		(wf_instr (VVTESTOP V128 v_vvtestop)) ->
		Instr_ok C (VVTESTOP V128 v_vvtestop) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_I32]))
	| vunop : forall (C : context) (sh : shape) (vunop_sh : vunop_), 
		(wf_context C) ->
		(wf_instr (VUNOP sh vunop_sh)) ->
		Instr_ok C (VUNOP sh vunop_sh) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_V128]))
	| vbinop : forall (C : context) (sh : shape) (vbinop_sh : vbinop_), 
		(wf_context C) ->
		(wf_instr (VBINOP sh vbinop_sh)) ->
		Instr_ok C (VBINOP sh vbinop_sh) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vtestop : forall (C : context) (sh : shape) (vtestop_sh : vtestop_), 
		(wf_context C) ->
		(wf_instr (VTESTOP sh vtestop_sh)) ->
		Instr_ok C (VTESTOP sh vtestop_sh) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_I32]))
	| vrelop : forall (C : context) (sh : shape) (vrelop_sh : vrelop_), 
		(wf_context C) ->
		(wf_instr (VRELOP sh vrelop_sh)) ->
		Instr_ok C (VRELOP sh vrelop_sh) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vshiftop : forall (C : context) (sh : ishape) (vshiftop_sh : vshiftop_), 
		(wf_context C) ->
		(wf_instr (VSHIFTOP sh vshiftop_sh)) ->
		Instr_ok C (VSHIFTOP sh vshiftop_sh) (mk_functype (mk_list _ [::valtype_V128; valtype_I32]) (mk_list _ [::valtype_V128]))
	| vbitmask : forall (C : context) (sh : ishape), 
		(wf_context C) ->
		(wf_instr (VBITMASK sh)) ->
		Instr_ok C (VBITMASK sh) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_I32]))
	| vswizzle : forall (C : context) (sh : ishape), 
		(wf_context C) ->
		(wf_instr (VSWIZZLE sh)) ->
		Instr_ok C (VSWIZZLE sh) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vshuffle : forall (C : context) (sh : ishape) (i_lst : (seq laneidx)), 
		List.Forall (fun (i : laneidx) => ((i :> nat) < (2 * ((fun_dim (shape_ishape sh)) :> nat))%N)%N) i_lst ->
		(wf_context C) ->
		(wf_dim (fun_dim (shape_ishape sh))) ->
		(wf_instr (VSHUFFLE sh i_lst)) ->
		Instr_ok C (VSHUFFLE sh i_lst) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vsplat : forall (C : context) (sh : shape), 
		(wf_context C) ->
		(wf_instr (VSPLAT sh)) ->
		Instr_ok C (VSPLAT sh) (mk_functype (mk_list _ [::(valtype_numtype (shunpack sh))]) (mk_list _ [::valtype_V128]))
	| vextract_lane : forall (C : context) (sh : shape) (sx_opt : (option sx)) (i : laneidx), 
		((i :> nat) < ((fun_dim sh) :> nat))%N ->
		(wf_context C) ->
		(wf_dim (fun_dim sh)) ->
		(wf_instr (VEXTRACT_LANE sh sx_opt i)) ->
		Instr_ok C (VEXTRACT_LANE sh sx_opt i) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::(valtype_numtype (shunpack sh))]))
	| vreplace_lane : forall (C : context) (sh : shape) (i : laneidx), 
		((i :> nat) < ((fun_dim sh) :> nat))%N ->
		(wf_context C) ->
		(wf_dim (fun_dim sh)) ->
		(wf_instr (VREPLACE_LANE sh i)) ->
		Instr_ok C (VREPLACE_LANE sh i) (mk_functype (mk_list _ [::valtype_V128; (valtype_numtype (shunpack sh))]) (mk_list _ [::valtype_V128]))
	| vextunop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop_), 
		(wf_context C) ->
		(wf_instr (VEXTUNOP sh_1 sh_2 vextunop)) ->
		Instr_ok C (VEXTUNOP sh_1 sh_2 vextunop) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_V128]))
	| vextbinop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop_), 
		(wf_context C) ->
		(wf_instr (VEXTBINOP sh_1 sh_2 vextbinop)) ->
		Instr_ok C (VEXTBINOP sh_1 sh_2 vextbinop) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vnarrow : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (v_sx : sx), 
		(wf_context C) ->
		(wf_instr (VNARROW sh_1 sh_2 v_sx)) ->
		Instr_ok C (VNARROW sh_1 sh_2 v_sx) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vcvtop : forall (C : context) (sh_1 : shape) (sh_2 : shape) (v_vcvtop : vcvtop), 
		(wf_context C) ->
		(wf_instr (VCVTOP sh_1 sh_2 v_vcvtop)) ->
		Instr_ok C (VCVTOP sh_1 sh_2 v_vcvtop) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_V128]))
	| local_get : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|))%N ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		(wf_context C) ->
		(wf_instr (LOCAL_GET x)) ->
		Instr_ok C (LOCAL_GET x) (mk_functype (mk_list _ [:: ]) (mk_list _ [::t]))
	| local_set : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|))%N ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		(wf_context C) ->
		(wf_instr (LOCAL_SET x)) ->
		Instr_ok C (LOCAL_SET x) (mk_functype (mk_list _ [::t]) (mk_list _ [:: ]))
	| local_tee : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|))%N ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		(wf_context C) ->
		(wf_instr (LOCAL_TEE x)) ->
		Instr_ok C (LOCAL_TEE x) (mk_functype (mk_list _ [::t]) (mk_list _ [::t]))
	| global_get : forall (C : context) (x : idx) (t : valtype) (v_mut : mut), 
		((x :> nat) < (|(context_GLOBALS C)|))%N ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype v_mut t)) ->
		(wf_context C) ->
		(wf_instr (GLOBAL_GET x)) ->
		Instr_ok C (GLOBAL_GET x) (mk_functype (mk_list _ [:: ]) (mk_list _ [::t]))
	| global_set : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_GLOBALS C)|))%N ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype (Some MUT) t)) ->
		(wf_context C) ->
		(wf_instr (GLOBAL_SET x)) ->
		Instr_ok C (GLOBAL_SET x) (mk_functype (mk_list _ [::t]) (mk_list _ [:: ]))
	| table_get : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		(wf_context C) ->
		(wf_instr (TABLE_GET x)) ->
		(wf_tabletype (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_GET x) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::(valtype_reftype rt)]))
	| table_set : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		(wf_context C) ->
		(wf_instr (TABLE_SET x)) ->
		(wf_tabletype (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_SET x) (mk_functype (mk_list _ [::valtype_I32; (valtype_reftype rt)]) (mk_list _ [:: ]))
	| table_size : forall (C : context) (x : idx) (lim : limits) (rt : reftype), 
		((x :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		(wf_context C) ->
		(wf_instr (TABLE_SIZE x)) ->
		(wf_tabletype (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_SIZE x) (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_I32]))
	| table_grow : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		(wf_context C) ->
		(wf_instr (TABLE_GROW x)) ->
		(wf_tabletype (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_GROW x) (mk_functype (mk_list _ [::(valtype_reftype rt); valtype_I32]) (mk_list _ [::valtype_I32]))
	| table_fill : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		(wf_context C) ->
		(wf_instr (TABLE_FILL x)) ->
		(wf_tabletype (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_FILL x) (mk_functype (mk_list _ [::valtype_I32; (valtype_reftype rt); valtype_I32]) (mk_list _ [:: ]))
	| table_copy : forall (C : context) (x_1 : idx) (x_2 : idx) (lim_1 : limits) (rt : reftype) (lim_2 : limits), 
		((x_1 :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x_1 :> nat) |]) == (mk_tabletype lim_1 rt)) ->
		((x_2 :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x_2 :> nat) |]) == (mk_tabletype lim_2 rt)) ->
		(wf_context C) ->
		(wf_instr (TABLE_COPY x_1 x_2)) ->
		(wf_tabletype (mk_tabletype lim_1 rt)) ->
		(wf_tabletype (mk_tabletype lim_2 rt)) ->
		Instr_ok C (TABLE_COPY x_1 x_2) (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| table_init : forall (C : context) (x_1 : idx) (x_2 : idx) (lim : limits) (rt : reftype), 
		((x_1 :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x_1 :> nat) |]) == (mk_tabletype lim rt)) ->
		((x_2 :> nat) < (|(context_ELEMS C)|))%N ->
		(((context_ELEMS C)[| (x_2 :> nat) |]) == rt) ->
		(wf_context C) ->
		(wf_instr (TABLE_INIT x_1 x_2)) ->
		(wf_tabletype (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_INIT x_1 x_2) (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| elem_drop : forall (C : context) (x : idx) (rt : reftype), 
		((x :> nat) < (|(context_ELEMS C)|))%N ->
		(((context_ELEMS C)[| (x :> nat) |]) == rt) ->
		(wf_context C) ->
		(wf_instr (ELEM_DROP x)) ->
		Instr_ok C (ELEM_DROP x) (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| memory_size : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr MEMORY_SIZE) ->
		Instr_ok C MEMORY_SIZE (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_I32]))
	| memory_grow : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr MEMORY_GROW) ->
		Instr_ok C MEMORY_GROW (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::valtype_I32]))
	| memory_fill : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr MEMORY_FILL) ->
		Instr_ok C MEMORY_FILL (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| memory_copy : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr MEMORY_COPY) ->
		Instr_ok C MEMORY_COPY (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| memory_init : forall (C : context) (x : idx) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		((x :> nat) < (|(context_DATAS C)|))%N ->
		(((context_DATAS C)[| (x :> nat) |]) == OK) ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (MEMORY_INIT x)) ->
		Instr_ok C (MEMORY_INIT x) (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| data_drop : forall (C : context) (x : idx), 
		((x :> nat) < (|(context_DATAS C)|))%N ->
		(((context_DATAS C)[| (x :> nat) |]) == OK) ->
		(wf_context C) ->
		(wf_instr (DATA_DROP x)) ->
		Instr_ok C (DATA_DROP x) (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| load_val : forall (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		((res_size (valtype_numtype nt)) != None) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= (((!((res_size (valtype_numtype nt)))) : rat) / (8 : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (LOAD nt None v_memarg)) ->
		Instr_ok C (LOAD nt None v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::(valtype_numtype nt)]))
	| load_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= ((v_M : rat) / (8 : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg)) ->
		Instr_ok C (LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::(valtype_Inn v_Inn)]))
	| store_val : forall (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		((res_size (valtype_numtype nt)) != None) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= (((!((res_size (valtype_numtype nt)))) : rat) / (8 : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (STORE nt None v_memarg)) ->
		Instr_ok C (STORE nt None v_memarg) (mk_functype (mk_list _ [::valtype_I32; (valtype_numtype nt)]) (mk_list _ [:: ]))
	| store_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= ((v_M : rat) / (8 : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg)) ->
		Instr_ok C (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg) (mk_functype (mk_list _ [::valtype_I32; (valtype_Inn v_Inn)]) (mk_list _ [:: ]))
	| vload : forall (C : context) (v_M : M) (v_N : res_N) (v_sx : sx) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= (((v_M : rat) / (8 : rat))%Q * (v_N : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (VLOAD V128 (Some (SHAPEX_ v_M v_N v_sx)) v_memarg)) ->
		Instr_ok C (VLOAD V128 (Some (SHAPEX_ v_M v_N v_sx)) v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::valtype_V128]))
	| vload_splat : forall (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= ((v_n : rat) / (8 : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (VLOAD V128 (Some (SPLAT v_n)) v_memarg)) ->
		Instr_ok C (VLOAD V128 (Some (SPLAT v_n)) v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::valtype_V128]))
	| vload_zero : forall (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= ((v_n : rat) / (8 : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (VLOAD V128 (Some (vloadop_ZERO v_n)) v_memarg)) ->
		Instr_ok C (VLOAD V128 (Some (vloadop_ZERO v_n)) v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::valtype_V128]))
	| vload_lane : forall (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= ((v_n : rat) / (8 : rat))%Q)%Q ->
		(((v_laneidx :> nat) : rat) < ((128 : rat) / (v_n : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) ->
		Instr_ok C (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx) (mk_functype (mk_list _ [::valtype_I32; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vstore : forall (C : context) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		((res_size valtype_V128) != None) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= (((!((res_size valtype_V128))) : rat) / (8 : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (VSTORE V128 v_memarg)) ->
		Instr_ok C (VSTORE V128 v_memarg) (mk_functype (mk_list _ [::valtype_I32; valtype_V128]) (mk_list _ [:: ]))
	| vstore_lane : forall (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat))%N : rat) <= ((v_n : rat) / (8 : rat))%Q)%Q ->
		(((v_laneidx :> nat) : rat) < ((128 : rat) / (v_n : rat))%Q)%Q ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_instr (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) ->
		Instr_ok C (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx) (mk_functype (mk_list _ [::valtype_I32; valtype_V128]) (mk_list _ [:: ]))

with

Instrs_ok : context -> (seq instr) -> functype -> Prop :=
	| empty : forall (C : context), 
		(wf_context C) ->
		Instrs_ok C [:: ] (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| Instrs_ok__instr : forall (C : context) (v_instr : instr) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instr_ok C v_instr (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_context C) ->
		(wf_instr v_instr) ->
		Instrs_ok C [::v_instr] (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| res_seq : forall (C : context) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_3_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok C instr_1_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok C instr_2_lst (mk_functype (mk_list _ t_2_lst) (mk_list _ t_3_lst))) ->
		(wf_context C) ->
		List.Forall (fun (instr_1 : instr) => (wf_instr instr_1)) instr_1_lst ->
		List.Forall (fun (instr_2 : instr) => (wf_instr instr_2)) instr_2_lst ->
		Instrs_ok C (instr_1_lst ++ instr_2_lst) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_3_lst))
	| sub : forall (C : context) (instr_lst : (seq instr)) (t'_1_lst : (seq valtype)) (t'_2_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok C instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Resulttype_sub (mk_list _ t'_1_lst) (mk_list _ t_1_lst)) ->
		(Resulttype_sub (mk_list _ t_2_lst) (mk_list _ t'_2_lst)) ->
		(wf_context C) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		Instrs_ok C instr_lst (mk_functype (mk_list _ t'_1_lst) (mk_list _ t'_2_lst))
	| Instrs_ok__frame : forall (C : context) (instr_lst : (seq instr)) (t_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok C instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_context C) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		Instrs_ok C instr_lst (mk_functype (mk_list _ (t_lst ++ t_1_lst)) (mk_list _ (t_lst ++ t_2_lst))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:139.1-139.69 *)
Inductive Expr_ok : context -> expr -> resulttype -> Prop :=
	| mk_Expr_ok : forall (C : context) (instr_lst : (seq instr)) (t_lst : (seq valtype)), 
		(Instrs_ok C instr_lst (mk_functype (mk_list _ [:: ]) (mk_list _ t_lst))) ->
		(wf_context C) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		Expr_ok C instr_lst (mk_list _ t_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:529.1-529.78 *)
Inductive Instr_const : context -> instr -> Prop :=
	| Instr_const__const : forall (C : context) (nt : numtype) (c : num_), 
		(wf_context C) ->
		(wf_instr (CONST nt c)) ->
		Instr_const C (CONST nt c)
	| Instr_const__vconst : forall (C : context) (vt : vectype) (vc : vec_), 
		(wf_context C) ->
		(wf_instr (VCONST vt vc)) ->
		Instr_const C (VCONST vt vc)
	| Instr_const__ref_null : forall (C : context) (rt : reftype), 
		(wf_context C) ->
		(wf_instr (REF_NULL rt)) ->
		Instr_const C (REF_NULL rt)
	| Instr_const__ref_func : forall (C : context) (x : idx), 
		(wf_context C) ->
		(wf_instr (REF_FUNC x)) ->
		Instr_const C (REF_FUNC x)
	| Instr_const__global_get : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_GLOBALS C)|))%N ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype None t)) ->
		(wf_context C) ->
		(wf_instr (GLOBAL_GET x)) ->
		Instr_const C (GLOBAL_GET x).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:530.1-530.77 *)
Inductive Expr_const : context -> expr -> Prop :=
	| mk_Expr_const : forall (C : context) (instr_lst : (seq instr)), 
		List.Forall (fun (v_instr : instr) => (Instr_const C v_instr)) instr_lst ->
		(wf_context C) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		Expr_const C instr_lst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:531.1-531.78 *)
Inductive Expr_ok_const : context -> expr -> valtype -> Prop :=
	| mk_Expr_ok_const : forall (C : context) (v_expr : expr) (t : valtype), 
		(Expr_ok C v_expr (mk_list _ [::t])) ->
		(Expr_const C v_expr) ->
		(wf_context C) ->
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		Expr_ok_const C v_expr t.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:564.1-564.73 *)
Inductive Type_ok : type -> functype -> Prop :=
	| mk_Type_ok : forall (ft : functype), 
		(Functype_ok ft) ->
		Type_ok (TYPE ft) ft.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:565.1-565.73 *)
Inductive Func_ok : context -> func -> functype -> Prop :=
	| mk_Func_ok : forall (C : context) (x : idx) (t_lst : (seq valtype)) (v_expr : expr) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((x :> nat) < (|(context_TYPES C)|))%N ->
		(((context_TYPES C)[| (x :> nat) |]) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		List.Forall (fun (t : valtype) => (t != BOT)) t_lst ->
		(Expr_ok (C @@ {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := (t_1_lst ++ t_lst); LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := (Some (mk_list _ t_2_lst)) |}) v_expr (mk_list _ t_2_lst)) ->
		(wf_context C) ->
		(wf_func (func_FUNC x (seq.map (fun (t : valtype) => (LOCAL t)) t_lst) v_expr)) ->
		(wf_context {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := (t_1_lst ++ t_lst); LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := (Some (mk_list _ t_2_lst)) |}) ->
		Func_ok C (func_FUNC x (seq.map (fun (t : valtype) => (LOCAL t)) t_lst) v_expr) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:566.1-566.75 *)
Inductive Global_ok : context -> global -> globaltype -> Prop :=
	| mk_Global_ok : forall (C : context) (gt : globaltype) (v_expr : expr) (v_mut : mut) (t : valtype), 
		(Globaltype_ok gt) ->
		(gt == (mk_globaltype v_mut t)) ->
		(Expr_ok_const C v_expr t) ->
		(wf_context C) ->
		(wf_global (global_GLOBAL gt v_expr)) ->
		Global_ok C (global_GLOBAL gt v_expr) gt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:567.1-567.74 *)
Inductive Table_ok : context -> table -> tabletype -> Prop :=
	| mk_Table_ok : forall (C : context) (res_tt : tabletype), 
		(Tabletype_ok res_tt) ->
		(wf_context C) ->
		(wf_table (table_TABLE res_tt)) ->
		Table_ok C (table_TABLE res_tt) res_tt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:568.1-568.72 *)
Inductive Mem_ok : context -> mem -> memtype -> Prop :=
	| mk_Mem_ok : forall (C : context) (mt : memtype), 
		(Memtype_ok mt) ->
		(wf_context C) ->
		(wf_mem (MEMORY mt)) ->
		Mem_ok C (MEMORY mt) mt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:571.1-571.77 *)
Inductive Elemmode_ok : context -> elemmode -> reftype -> Prop :=
	| active : forall (C : context) (x : idx) (v_expr : expr) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		(Expr_ok_const C v_expr valtype_I32) ->
		(wf_context C) ->
		(wf_elemmode (ACTIVE x v_expr)) ->
		(wf_tabletype (mk_tabletype lim rt)) ->
		Elemmode_ok C (ACTIVE x v_expr) rt
	| passive : forall (C : context) (rt : reftype), 
		(wf_context C) ->
		(wf_elemmode PASSIVE) ->
		Elemmode_ok C PASSIVE rt
	| declare : forall (C : context) (rt : reftype), 
		(wf_context C) ->
		(wf_elemmode DECLARE) ->
		Elemmode_ok C DECLARE rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:569.1-569.73 *)
Inductive Elem_ok : context -> elem -> reftype -> Prop :=
	| mk_Elem_ok : forall (C : context) (rt : reftype) (expr_lst : (seq expr)) (v_elemmode : elemmode), 
		List.Forall (fun (v_expr : expr) => (Expr_ok_const C v_expr (valtype_reftype rt))) expr_lst ->
		(Elemmode_ok C v_elemmode rt) ->
		(wf_context C) ->
		(wf_elem (ELEM rt expr_lst v_elemmode)) ->
		Elem_ok C (ELEM rt expr_lst v_elemmode) rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:572.1-572.77 *)
Inductive Datamode_ok : context -> datamode -> Prop :=
	| Datamode_ok__active : forall (C : context) (v_expr : expr) (mt : memtype), 
		(0 < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(Expr_ok_const C v_expr valtype_I32) ->
		(wf_context C) ->
		(wf_memtype mt) ->
		(wf_datamode (datamode_ACTIVE (mk_uN 0) v_expr)) ->
		Datamode_ok C (datamode_ACTIVE (mk_uN 0) v_expr)
	| Datamode_ok__passive : forall (C : context), 
		(wf_context C) ->
		(wf_datamode datamode_PASSIVE) ->
		Datamode_ok C datamode_PASSIVE.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:570.1-570.73 *)
Inductive Data_ok : context -> data -> Prop :=
	| mk_Data_ok : forall (C : context) (b_lst : (seq byte)) (v_datamode : datamode), 
		(Datamode_ok C v_datamode) ->
		(wf_context C) ->
		(wf_data (DATA b_lst v_datamode)) ->
		Data_ok C (DATA b_lst v_datamode).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:573.1-573.74 *)
Inductive Start_ok : context -> start -> Prop :=
	| mk_Start_ok : forall (C : context) (x : idx), 
		((x :> nat) < (|(context_FUNCS C)|))%N ->
		(((context_FUNCS C)[| (x :> nat) |]) == (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))) ->
		(wf_context C) ->
		(wf_start (START x)) ->
		Start_ok C (START x).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:637.1-637.80 *)
Inductive Import_ok : context -> import -> externtype -> Prop :=
	| mk_Import_ok : forall (C : context) (name_1 : name) (name_2 : name) (xt : externtype), 
		(Externtype_ok xt) ->
		(wf_context C) ->
		(wf_import (IMPORT name_1 name_2 xt)) ->
		Import_ok C (IMPORT name_1 name_2 xt) xt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:639.1-639.83 *)
Inductive Externidx_ok : context -> externidx -> externtype -> Prop :=
	| Externidx_ok__func : forall (C : context) (x : idx) (ft : functype), 
		((x :> nat) < (|(context_FUNCS C)|))%N ->
		(((context_FUNCS C)[| (x :> nat) |]) == ft) ->
		(wf_context C) ->
		(wf_externidx (externidx_FUNC x)) ->
		(wf_externtype (FUNC ft)) ->
		Externidx_ok C (externidx_FUNC x) (FUNC ft)
	| Externidx_ok__global : forall (C : context) (x : idx) (gt : globaltype), 
		((x :> nat) < (|(context_GLOBALS C)|))%N ->
		(((context_GLOBALS C)[| (x :> nat) |]) == gt) ->
		(wf_context C) ->
		(wf_externidx (externidx_GLOBAL x)) ->
		(wf_externtype (GLOBAL gt)) ->
		Externidx_ok C (externidx_GLOBAL x) (GLOBAL gt)
	| Externidx_ok__table : forall (C : context) (x : idx) (res_tt : tabletype), 
		((x :> nat) < (|(context_TABLES C)|))%N ->
		(((context_TABLES C)[| (x :> nat) |]) == res_tt) ->
		(wf_context C) ->
		(wf_externidx (externidx_TABLE x)) ->
		(wf_externtype (TABLE res_tt)) ->
		Externidx_ok C (externidx_TABLE x) (TABLE res_tt)
	| Externidx_ok__mem : forall (C : context) (x : idx) (mt : memtype), 
		((x :> nat) < (|(context_MEMS C)|))%N ->
		(((context_MEMS C)[| (x :> nat) |]) == mt) ->
		(wf_context C) ->
		(wf_externidx (externidx_MEM x)) ->
		(wf_externtype (MEM mt)) ->
		Externidx_ok C (externidx_MEM x) (MEM mt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:638.1-638.80 *)
Inductive Export_ok : context -> export -> externtype -> Prop :=
	| mk_Export_ok : forall (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype), 
		(Externidx_ok C v_externidx xt) ->
		(wf_context C) ->
		(wf_externtype xt) ->
		(wf_export (EXPORT v_name v_externidx)) ->
		Export_ok C (EXPORT v_name v_externidx) xt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:669.1-669.62 *)
Inductive Module_ok : module -> Prop :=
	| mk_Module_ok : forall (type_lst : (seq type)) (import_lst : (seq import)) (func_lst : (seq func)) (global_lst : (seq global)) (table_lst : (seq table)) (mem_lst : (seq mem)) (elem_lst : (seq elem)) (v_n : n) (data_lst : (seq data)) (start_opt : (option start)) (export_lst : (seq export)) (ft'_lst : (seq functype)) (ixt_lst : (seq externtype)) (C' : context) (gt_lst : (seq globaltype)) (tt_lst : (seq tabletype)) (mt_lst : (seq memtype)) (rt_lst : (seq reftype)) (C : context) (ft_lst : (seq functype)) (xt_lst : (seq externtype)) (ift_lst : (seq functype)) (igt_lst : (seq globaltype)) (itt_lst : (seq tabletype)) (imt_lst : (seq memtype)) (var_3 : (seq memtype)) (var_2 : (seq tabletype)) (var_1 : (seq globaltype)) (var_0 : (seq functype)), 
		(fun_memsxt ixt_lst var_3) ->
		(fun_tablesxt ixt_lst var_2) ->
		(fun_globalsxt ixt_lst var_1) ->
		(fun_funcsxt ixt_lst var_0) ->
		((|ft'_lst|) == (|type_lst|)) ->
		List.Forall2 (fun (ft' : functype) (v_type : type) => (Type_ok v_type ft')) ft'_lst type_lst ->
		((|import_lst|) == (|ixt_lst|)) ->
		List.Forall2 (fun (v_import : import) (ixt : externtype) => (Import_ok {| context_TYPES := ft'_lst; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |} v_import ixt)) import_lst ixt_lst ->
		((|global_lst|) == (|gt_lst|)) ->
		List.Forall2 (fun (v_global : global) (gt : globaltype) => (Global_ok C' v_global gt)) global_lst gt_lst ->
		((|table_lst|) == (|tt_lst|)) ->
		List.Forall2 (fun (v_table : table) (res_tt : tabletype) => (Table_ok C' v_table res_tt)) table_lst tt_lst ->
		((|mem_lst|) == (|mt_lst|)) ->
		List.Forall2 (fun (v_mem : mem) (mt : memtype) => (Mem_ok C' v_mem mt)) mem_lst mt_lst ->
		((|elem_lst|) == (|rt_lst|)) ->
		List.Forall2 (fun (v_elem : elem) (rt : reftype) => (Elem_ok C' v_elem rt)) elem_lst rt_lst ->
		List.Forall (fun (v_data : data) => (Data_ok C' v_data)) data_lst ->
		((|ft_lst|) == (|func_lst|)) ->
		List.Forall2 (fun (ft : functype) (v_func : func) => (Func_ok C v_func ft)) ft_lst func_lst ->
		List.Forall (fun (v_start : start) => (Start_ok C v_start)) (option_to_list start_opt) ->
		((|export_lst|) == (|xt_lst|)) ->
		List.Forall2 (fun (v_export : export) (xt : externtype) => (Export_ok C v_export xt)) export_lst xt_lst ->
		((|mt_lst|) <= 1)%N ->
		(C == {| context_TYPES := ft'_lst; context_FUNCS := (ift_lst ++ ft_lst); context_GLOBALS := (igt_lst ++ gt_lst); context_TABLES := (itt_lst ++ tt_lst); context_MEMS := (imt_lst ++ mt_lst); context_ELEMS := rt_lst; context_DATAS := (List.repeat OK v_n); context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(C' == {| context_TYPES := ft'_lst; context_FUNCS := (ift_lst ++ ft_lst); context_GLOBALS := igt_lst; context_TABLES := (itt_lst ++ tt_lst); context_MEMS := (imt_lst ++ mt_lst); context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(ift_lst == var_0) ->
		(igt_lst == var_1) ->
		(itt_lst == var_2) ->
		(imt_lst == var_3) ->
		List.Forall (fun (ixt : externtype) => (wf_externtype ixt)) ixt_lst ->
		(wf_context C') ->
		(wf_context C) ->
		List.Forall (fun (xt : externtype) => (wf_externtype xt)) xt_lst ->
		List.Forall (fun (iter : tabletype) => (wf_tabletype iter)) var_2 ->
		List.Forall (fun (iter : memtype) => (wf_memtype iter)) var_3 ->
		(wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ->
		(wf_context {| context_TYPES := ft'_lst; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(wf_context {| context_TYPES := ft'_lst; context_FUNCS := (ift_lst ++ ft_lst); context_GLOBALS := (igt_lst ++ gt_lst); context_TABLES := (itt_lst ++ tt_lst); context_MEMS := (imt_lst ++ mt_lst); context_ELEMS := rt_lst; context_DATAS := (List.repeat OK v_n); context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(wf_context {| context_TYPES := ft'_lst; context_FUNCS := (ift_lst ++ ft_lst); context_GLOBALS := igt_lst; context_TABLES := (itt_lst ++ tt_lst); context_MEMS := (imt_lst ++ mt_lst); context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(v_n == (|data_lst|)) ->
		Module_ok (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:224.1-226.15 *)
Inductive Step_pure_before_ref_is_null_false : (seq admininstr) -> Prop :=
	| ref_is_null_true_0 : forall (v_ref : ref) (rt : reftype), 
		(v_ref == (ref_REF_NULL rt)) ->
		Step_pure_before_ref_is_null_false [::(admininstr_ref v_ref); admininstr_REF_IS_NULL].

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:276.1-278.15 *)
Inductive Step_pure_before_vtestop_false : (seq admininstr) -> Prop :=
	| vtestop_true_0 : forall (c : vec_) (v_Jnn : Jnn) (v_N : res_N) (ci_1_lst : (seq lane_)), 
		(ci_1_lst == (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ->
		List.Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != None)) ci_1_lst ->
		List.Forall (fun (ci_1 : lane_) => (((!((proj_lane__2 ci_1))) :> nat) != 0)) ci_1_lst ->
		List.Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst ->
		(wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		Step_pure_before_vtestop_false [::(admininstr_VCONST V128 c); (admininstr_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE))].

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.109 *)
Inductive Step_pure : (seq admininstr) -> (seq admininstr) -> Prop :=
	| Step_pure__unreachable : Step_pure [::admininstr_UNREACHABLE] [::admininstr_TRAP]
	| Step_pure__nop : Step_pure [::admininstr_NOP] [:: ]
	| Step_pure__drop : forall (v_val : val), Step_pure [::(admininstr_val v_val); admininstr_DROP] [:: ]
	| select_true : forall (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : (option (seq valtype))), 
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_val val_1); (admininstr_val val_2); (admininstr_CONST I32 c); (admininstr_SELECT t_lst_opt)] [::(admininstr_val val_1)]
	| select_false : forall (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : (option (seq valtype))), 
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_val val_1); (admininstr_val val_2); (admininstr_CONST I32 c); (admininstr_SELECT t_lst_opt)] [::(admininstr_val val_2)]
	| if_true : forall (c : num_) (bt : blocktype) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)), 
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_IFELSE bt instr_1_lst instr_2_lst)] [::(admininstr_BLOCK bt instr_1_lst)]
	| if_false : forall (c : num_) (bt : blocktype) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)), 
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_IFELSE bt instr_1_lst instr_2_lst)] [::(admininstr_BLOCK bt instr_2_lst)]
	| label_vals : forall (v_n : n) (instr_lst : (seq instr)) (val_lst : (seq val)), Step_pure [::(LABEL_ v_n instr_lst (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
	| br_zero : forall (v_n : n) (instr'_lst : (seq instr)) (val'_lst : (seq val)) (val_lst : (seq val)) (instr_lst : (seq instr)), 
		(v_n == (|val_lst|)) ->
		Step_pure [::(LABEL_ v_n instr'_lst ((((seq.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)) ++ [::(admininstr_BR (mk_uN 0))]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (seq.map (fun (instr' : instr) => (admininstr_instr instr')) instr'_lst))
	| br_succ : forall (v_n : n) (instr'_lst : (seq instr)) (val_lst : (seq val)) (l : labelidx) (instr_lst : (seq instr)), Step_pure [::(LABEL_ v_n instr'_lst (((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_BR (mk_uN ((l :> nat) + 1)%N))]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_BR l)])
	| br_if_true : forall (c : num_) (l : labelidx), 
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_BR_IF l)] [::(admininstr_BR l)]
	| br_if_false : forall (c : num_) (l : labelidx), 
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_BR_IF l)] [:: ]
	| br_table_lt : forall (i : num_) (l_lst : (seq labelidx)) (l' : labelidx), 
		(((!((proj_num__0 i))) :> nat) < (|l_lst|))%N ->
		((proj_num__0 i) != None) ->
		Step_pure [::(admininstr_CONST I32 i); (admininstr_BR_TABLE l_lst l')] [::(admininstr_BR (l_lst[| ((!((proj_num__0 i))) :> nat) |]))]
	| br_table_ge : forall (i : num_) (l_lst : (seq labelidx)) (l' : labelidx), 
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 i))) :> nat) >= (|l_lst|))%N ->
		Step_pure [::(admininstr_CONST I32 i); (admininstr_BR_TABLE l_lst l')] [::(admininstr_BR l')]
	| frame_vals : forall (v_n : n) (f : frame) (val_lst : (seq val)), 
		(v_n == (|val_lst|)) ->
		Step_pure [::(FRAME_ v_n f (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
	| return_frame : forall (v_n : n) (f : frame) (val'_lst : (seq val)) (val_lst : (seq val)) (instr_lst : (seq instr)), 
		(v_n == (|val_lst|)) ->
		Step_pure [::(FRAME_ v_n f ((((seq.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)) ++ [::admininstr_RETURN]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
	| return_label : forall (v_n : n) (instr'_lst : (seq instr)) (val_lst : (seq val)) (instr_lst : (seq instr)), Step_pure [::(LABEL_ v_n instr'_lst (((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::admininstr_RETURN]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::admininstr_RETURN])
	| trap_vals : forall (val_lst : (seq val)) (instr_lst : (seq instr)), 
		((val_lst != [:: ]) || (instr_lst != [:: ])) ->
		Step_pure ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([::admininstr_TRAP] ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))) [::admininstr_TRAP]
	| trap_label : forall (v_n : n) (instr'_lst : (seq instr)), Step_pure [::(LABEL_ v_n instr'_lst [::admininstr_TRAP])] [::admininstr_TRAP]
	| trap_frame : forall (v_n : n) (f : frame), Step_pure [::(FRAME_ v_n f [::admininstr_TRAP])] [::admininstr_TRAP]
	| unop_val : forall (nt : numtype) (c_1 : num_) (unop : unop_) (c : num_), 
		((|(fun_unop_ nt unop c_1)|) > 0)%N ->
		(c \in (fun_unop_ nt unop c_1)) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_UNOP nt unop)] [::(admininstr_CONST nt c)]
	| unop_trap : forall (nt : numtype) (c_1 : num_) (unop : unop_), 
		((fun_unop_ nt unop c_1) == [:: ]) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_UNOP nt unop)] [::admininstr_TRAP]
	| binop_val : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (c : num_) (var_0 : (seq num_)), 
		(fun_binop_ nt binop c_1 c_2 var_0) ->
		((|var_0|) > 0)%N ->
		(c \in var_0) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_CONST nt c_2); (admininstr_BINOP nt binop)] [::(admininstr_CONST nt c)]
	| binop_trap : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (var_0 : (seq num_)), 
		(fun_binop_ nt binop c_1 c_2 var_0) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_CONST nt c_2); (admininstr_BINOP nt binop)] [::admininstr_TRAP]
	| Step_pure__testop : forall (nt : numtype) (c_1 : num_) (testop : testop_) (c : num_), 
		(c == (fun_testop_ nt testop c_1)) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_TESTOP nt testop)] [::(admininstr_CONST I32 c)]
	| Step_pure__relop : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (relop : relop_) (c : num_) (var_0 : num_), 
		(fun_relop_ nt relop c_1 c_2 var_0) ->
		(c == var_0) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_CONST nt c_2); (admininstr_RELOP nt relop)] [::(admininstr_CONST I32 c)]
	| cvtop_val : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (v_cvtop : cvtop) (c : num_) (var_0 : (seq num_)), 
		(fun_cvtop__ nt_1 nt_2 v_cvtop c_1 var_0) ->
		((|var_0|) > 0)%N ->
		(c \in var_0) ->
		Step_pure [::(admininstr_CONST nt_1 c_1); (admininstr_CVTOP nt_2 nt_1 v_cvtop)] [::(admininstr_CONST nt_2 c)]
	| cvtop_trap : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (v_cvtop : cvtop) (var_0 : (seq num_)), 
		(fun_cvtop__ nt_1 nt_2 v_cvtop c_1 var_0) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_CONST nt_1 c_1); (admininstr_CVTOP nt_2 nt_1 v_cvtop)] [::admininstr_TRAP]
	| ref_is_null_true : forall (v_ref : ref) (rt : reftype), 
		(v_ref == (ref_REF_NULL rt)) ->
		Step_pure [::(admininstr_ref v_ref); admininstr_REF_IS_NULL] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1)))]
	| ref_is_null_false : forall (v_ref : ref), 
		(~(Step_pure_before_ref_is_null_false [::(admininstr_ref v_ref); admininstr_REF_IS_NULL])) ->
		Step_pure [::(admininstr_ref v_ref); admininstr_REF_IS_NULL] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0)))]
	| Step_pure__vvunop : forall (c_1 : vec_) (v_vvunop : vvunop) (c : vec_), 
		(c == (vvunop_ V128 v_vvunop c_1)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VVUNOP V128 v_vvunop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vvbinop : forall (c_1 : vec_) (c_2 : vec_) (v_vvbinop : vvbinop) (c : vec_), 
		(c == (vvbinop_ V128 v_vvbinop c_1 c_2)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VVBINOP V128 v_vvbinop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vvternop : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (v_vvternop : vvternop) (c : vec_), 
		(c == (vvternop_ V128 v_vvternop c_1 c_2 c_3)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VCONST V128 c_3); (admininstr_VVTERNOP V128 v_vvternop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vvtestop : forall (c_1 : vec_) (c : num_), 
		((proj_num__0 c) != None) ->
		((res_size valtype_V128) != None) ->
		((!((proj_num__0 c))) == (ine_ (!((res_size valtype_V128))) c_1 (mk_uN 0))) ->
		(wf_uN 128 (mk_uN 0)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VVTESTOP V128 ANY_TRUE)] [::(admininstr_CONST I32 c)]
	| Step_pure__vunop : forall (c_1 : vec_) (sh : shape) (vunop : vunop_) (c : vec_) (var_0 : (seq vec_)), 
		(fun_vunop_ sh vunop c_1 var_0) ->
		((|var_0|) > 0)%N ->
		(c \in var_0) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VUNOP sh vunop)] [::(admininstr_VCONST V128 c)]
	| vunop_trap : forall (c_1 : vec_) (sh : shape) (vunop : vunop_) (var_0 : (seq vec_)), 
		(fun_vunop_ sh vunop c_1 var_0) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VUNOP sh vunop)] [::admininstr_TRAP]
	| vbinop_val : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (c : vec_) (var_0 : (seq vec_)), 
		(fun_vbinop_ sh vbinop c_1 c_2 var_0) ->
		((|var_0|) > 0)%N ->
		(c \in var_0) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VBINOP sh vbinop)] [::(admininstr_VCONST V128 c)]
	| vbinop_trap : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (var_0 : (seq vec_)), 
		(fun_vbinop_ sh vbinop c_1 c_2 var_0) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VBINOP sh vbinop)] [::admininstr_TRAP]
	| vtestop_true : forall (c : vec_) (v_Jnn : Jnn) (v_N : res_N) (ci_1_lst : (seq lane_)), 
		(ci_1_lst == (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ->
		List.Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != None)) ci_1_lst ->
		List.Forall (fun (ci_1 : lane_) => (((!((proj_lane__2 ci_1))) :> nat) != 0)) ci_1_lst ->
		List.Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst ->
		(wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		Step_pure [::(admininstr_VCONST V128 c); (admininstr_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE))] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1)))]
	| vtestop_false : forall (c : vec_) (v_Jnn : Jnn) (v_N : res_N), 
		(~(Step_pure_before_vtestop_false [::(admininstr_VCONST V128 c); (admininstr_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE))])) ->
		Step_pure [::(admininstr_VCONST V128 c); (admininstr_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE))] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0)))]
	| Step_pure__vrelop : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vrelop : vrelop_) (c : vec_) (var_0 : vec_), 
		(fun_vrelop_ sh vrelop c_1 c_2 var_0) ->
		(var_0 == c) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VRELOP sh vrelop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vshiftop : forall (c_1 : vec_) (v_n : n) (v_Jnn : Jnn) (v_N : res_N) (vshiftop : vshiftop_) (c : vec_) (c'_lst : (seq lane_)) (var_0_lst : (seq lane_)), 
		((|var_0_lst|) == (|c'_lst|)) ->
		List.Forall2 (fun (var_0 : lane_) (c' : lane_) => (fun_vshiftop_ (ishape_X v_Jnn (mk_dim v_N)) vshiftop c' (mk_uN v_n) var_0)) var_0_lst c'_lst ->
		(c'_lst == (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c_1)) ->
		(c == (inv_lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) var_0_lst)) ->
		List.Forall (fun (c' : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) c')) c'_lst ->
		(wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		(wf_ishape (ishape_X v_Jnn (mk_dim v_N))) ->
		(wf_uN 32 (mk_uN v_n)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_VSHIFTOP (ishape_X v_Jnn (mk_dim v_N)) vshiftop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vbitmask : forall (c : vec_) (v_Jnn : Jnn) (v_N : res_N) (ci : iN) (ci_1_lst : (seq lane_)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|ci_1_lst|)) ->
		List.Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != None)) ci_1_lst ->
		List.Forall2 (fun (var_0 : uN) (ci_1 : lane_) => (fun_ilt_ (lsize (lanetype_Jnn v_Jnn)) res_S (!((proj_lane__2 ci_1))) (mk_uN 0) var_0)) var_0_lst ci_1_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ->
		((ibits_ 32 ci) == ((seq.map (fun (var_0 : uN) => (mk_bit (var_0 :> (nat)))) var_0_lst) ++ (List.repeat (mk_bit 0) (((32 : int) - (v_N : int))%Z : nat)))) ->
		(wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		List.Forall (fun (var_0 : uN) => (wf_bit (mk_bit (var_0 :> (nat))))) var_0_lst ->
		(wf_bit (mk_bit 0)) ->
		Step_pure [::(admininstr_VCONST V128 c); (admininstr_VBITMASK (ishape_X v_Jnn (mk_dim v_N)))] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (irev_ 32 ci)))]
	| Step_pure__vswizzle : forall (c_1 : vec_) (c_2 : vec_) (v_Pnn : Pnn) (v_M : M) (c : vec_) (ci_lst : (seq lane_)) (c'_lst : (seq iN)) (k : nat), 
		(ci_lst == (lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_2)) ->
		List.Forall (fun (iter_0 : lane_) => ((proj_lane__1 iter_0) != None)) (lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1) ->
		(c'_lst == ((seq.map (fun (iter_0 : lane_) => (!((proj_lane__1 iter_0)))) (lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1)) ++ (List.repeat (mk_uN 0) (((256 : int) - (v_M : int))%Z : nat)))) ->
		holds_upto (fun k => (((!((proj_lane__1 (ci_lst[| k |])))) :> nat) < (|c'_lst|))%N) v_M ->
		holds_upto (fun k => ((proj_lane__1 (ci_lst[| k |])) != None)) v_M ->
		holds_upto (fun k => (k < (|ci_lst|))%N) v_M ->
		(c == (inv_lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_M)) (seq.mkseq (fun k => (mk_lane__1 v_Pnn (c'_lst[| ((!((proj_lane__1 (ci_lst[| k |])))) :> nat) |]))) v_M))) ->
		(wf_shape (X (lanetype_packtype v_Pnn) (mk_dim v_M))) ->
		(wf_uN (psize v_Pnn) (mk_uN 0)) ->
		holds_upto (fun k => (wf_lane_ (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_M))) (mk_lane__1 v_Pnn (c'_lst[| ((!((proj_lane__1 (ci_lst[| k |])))) :> nat) |])))) v_M ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VSWIZZLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M)))] [::(admininstr_VCONST V128 c)]
	| Step_pure__vshuffle : forall (c_1 : vec_) (c_2 : vec_) (v_Pnn : Pnn) (v_N : res_N) (i_lst : (seq laneidx)) (c : vec_) (c'_lst : (seq iN)) (k : nat), 
		((seq.map (fun (c' : iN) => (mk_lane__1 v_Pnn c')) c'_lst) == ((lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_1) ++ (lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_2))) ->
		holds_upto (fun k => (((i_lst[| k |]) :> nat) < (|c'_lst|))%N) v_N ->
		holds_upto (fun k => (k < (|i_lst|))%N) v_N ->
		(c == (inv_lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_N)) (seq.mkseq (fun k => (mk_lane__1 v_Pnn (c'_lst[| ((i_lst[| k |]) :> nat) |]))) v_N))) ->
		List.Forall (fun (c' : iN) => (wf_lane_ (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) (mk_lane__1 v_Pnn c'))) c'_lst ->
		(wf_shape (X (lanetype_packtype v_Pnn) (mk_dim v_N))) ->
		holds_upto (fun k => (wf_lane_ (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) (mk_lane__1 v_Pnn (c'_lst[| ((i_lst[| k |]) :> nat) |])))) v_N ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VSHUFFLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_N)) i_lst)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vsplat : forall (v_Lnn : Lnn) (c_1 : num_) (v_N : res_N) (c : vec_), 
		(c == (inv_lanes_ (X v_Lnn (mk_dim v_N)) (List.repeat (packnum_ v_Lnn c_1) v_N))) ->
		(wf_shape (X v_Lnn (mk_dim v_N))) ->
		Step_pure [::(admininstr_CONST (unpack v_Lnn) c_1); (admininstr_VSPLAT (X v_Lnn (mk_dim v_N)))] [::(admininstr_VCONST V128 c)]
	| vextract_lane_num : forall (c_1 : vec_) (nt : numtype) (v_N : res_N) (i : laneidx) (c_2 : num_), 
		((i :> nat) < (|(lanes_ (X (lanetype_numtype nt) (mk_dim v_N)) c_1)|))%N ->
		((mk_lane__0 nt c_2) == ((lanes_ (X (lanetype_numtype nt) (mk_dim v_N)) c_1)[| (i :> nat) |])) ->
		(wf_lane_ (fun_lanetype (X (lanetype_numtype nt) (mk_dim v_N))) (mk_lane__0 nt c_2)) ->
		(wf_shape (X (lanetype_numtype nt) (mk_dim v_N))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i)] [::(admininstr_CONST nt c_2)]
	| vextract_lane_pack : forall (c_1 : vec_) (pt : packtype) (v_N : res_N) (v_sx : sx) (i : laneidx) (c_2 : num_), 
		((proj_num__0 c_2) != None) ->
		((proj_lane__1 ((lanes_ (X (lanetype_packtype pt) (mk_dim v_N)) c_1)[| (i :> nat) |])) != None) ->
		((i :> nat) < (|(lanes_ (X (lanetype_packtype pt) (mk_dim v_N)) c_1)|))%N ->
		((!((proj_num__0 c_2))) == (extend__ (psize pt) 32 v_sx (!((proj_lane__1 ((lanes_ (X (lanetype_packtype pt) (mk_dim v_N)) c_1)[| (i :> nat) |])))))) ->
		(wf_shape (X (lanetype_packtype pt) (mk_dim v_N))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i)] [::(admininstr_CONST I32 c_2)]
	| Step_pure__vreplace_lane : forall (c_1 : vec_) (v_Lnn : Lnn) (c_2 : num_) (v_N : res_N) (i : laneidx) (c : vec_), 
		(c == (inv_lanes_ (X v_Lnn (mk_dim v_N)) (list_update_func (lanes_ (X v_Lnn (mk_dim v_N)) c_1) (i :> nat) (fun (_ : lane_) => (packnum_ v_Lnn c_2))))) ->
		(wf_shape (X v_Lnn (mk_dim v_N))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_CONST (unpack v_Lnn) c_2); (admininstr_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vextunop : forall (c_1 : vec_) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop_) (c : vec_) (var_0 : vec_), 
		(fun_vextunop__ sh_1 sh_2 vextunop c_1 var_0) ->
		(var_0 == c) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VEXTUNOP sh_1 sh_2 vextunop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vextbinop : forall (c_1 : vec_) (c_2 : vec_) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop_) (c : vec_) (var_0 : vec_), 
		(fun_vextbinop__ sh_1 sh_2 vextbinop c_1 c_2 var_0) ->
		(var_0 == c) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VEXTBINOP sh_1 sh_2 vextbinop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vnarrow : forall (c_1 : vec_) (c_2 : vec_) (Jnn_2 : Jnn) (N_2 : res_N) (Jnn_1 : Jnn) (N_1 : res_N) (v_sx : sx) (c : vec_) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		(ci_1_lst == (lanes_ (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_2)) ->
		List.Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != None)) ci_1_lst ->
		(cj_1_lst == (seq.map (fun (ci_1 : lane_) => (narrow__ (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (!((proj_lane__2 ci_1))))) ci_1_lst)) ->
		List.Forall (fun (ci_2 : lane_) => ((proj_lane__2 ci_2) != None)) ci_2_lst ->
		(cj_2_lst == (seq.map (fun (ci_2 : lane_) => (narrow__ (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (!((proj_lane__2 ci_2))))) ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Jnn Jnn_2) (mk_dim N_2)) ((seq.map (fun (cj_1 : iN) => (mk_lane__2 Jnn_2 cj_1)) cj_1_lst) ++ (seq.map (fun (cj_2 : iN) => (mk_lane__2 Jnn_2 cj_2)) cj_2_lst)))) ->
		List.Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ci_1)) ci_1_lst ->
		List.Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ci_2)) ci_2_lst ->
		(wf_shape (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ->
		(wf_shape (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) ->
		List.Forall (fun (cj_1 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) (mk_lane__2 Jnn_2 cj_1))) cj_1_lst ->
		List.Forall (fun (cj_2 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) (mk_lane__2 Jnn_2 cj_2))) cj_2_lst ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VNARROW (ishape_X Jnn_2 (mk_dim N_2)) (ishape_X Jnn_1 (mk_dim N_1)) v_sx)] [::(admininstr_VCONST V128 c)]
	| vcvtop_full : forall (c_1 : vec_) (Lnn_2 : Lnn) (v_M : M) (Lnn_1 : Lnn) (v_vcvtop : vcvtop) (c : vec_) (ci_lst : (seq lane_)) (cj_lst_lst : (seq (seq lane_))), 
		(((halfop v_vcvtop) == None) && ((zeroop v_vcvtop) == None)) ->
		(ci_lst == (lanes_ (X Lnn_1 (mk_dim v_M)) c_1)) ->
		(cj_lst_lst == (setproduct_ lane_ (seq.map (fun (ci : lane_) => (vcvtop__ (X Lnn_1 (mk_dim v_M)) (X Lnn_2 (mk_dim v_M)) v_vcvtop ci)) ci_lst))) ->
		((|(seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X Lnn_2 (mk_dim v_M)) cj_lst)) cj_lst_lst)|) > 0)%N ->
		(c \in (seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X Lnn_2 (mk_dim v_M)) cj_lst)) cj_lst_lst)) ->
		List.Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (X Lnn_1 (mk_dim v_M))) ci)) ci_lst ->
		List.Forall (fun (cj_lst : (seq lane_)) => List.Forall (fun (cj : lane_) => (wf_lane_ Lnn_2 cj)) cj_lst) cj_lst_lst ->
		(wf_shape (X Lnn_1 (mk_dim v_M))) ->
		(wf_shape (X Lnn_2 (mk_dim v_M))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCVTOP (X Lnn_2 (mk_dim v_M)) (X Lnn_1 (mk_dim v_M)) v_vcvtop)] [::(admininstr_VCONST V128 c)]
	| vcvtop_half : forall (c_1 : vec_) (Lnn_2 : Lnn) (M_2 : M) (Lnn_1 : Lnn) (M_1 : M) (v_vcvtop : vcvtop) (c : vec_) (v_half : half) (ci_lst : (seq lane_)) (cj_lst_lst : (seq (seq lane_))), 
		((halfop v_vcvtop) == (Some v_half)) ->
		(ci_lst == (list_slice (lanes_ (X Lnn_1 (mk_dim M_1)) c_1) (fun_half v_half 0 M_2) M_2)) ->
		(cj_lst_lst == (setproduct_ lane_ (seq.map (fun (ci : lane_) => (vcvtop__ (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) v_vcvtop ci)) ci_lst))) ->
		((|(seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X Lnn_2 (mk_dim M_2)) cj_lst)) cj_lst_lst)|) > 0)%N ->
		(c \in (seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X Lnn_2 (mk_dim M_2)) cj_lst)) cj_lst_lst)) ->
		List.Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (X Lnn_1 (mk_dim M_1))) ci)) ci_lst ->
		List.Forall (fun (cj_lst : (seq lane_)) => List.Forall (fun (cj : lane_) => (wf_lane_ Lnn_2 cj)) cj_lst) cj_lst_lst ->
		(wf_shape (X Lnn_1 (mk_dim M_1))) ->
		(wf_shape (X Lnn_2 (mk_dim M_2))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCVTOP (X Lnn_2 (mk_dim M_2)) (X Lnn_1 (mk_dim M_1)) v_vcvtop)] [::(admininstr_VCONST V128 c)]
	| vcvtop_zero : forall (c_1 : vec_) (nt_2 : numtype) (M_2 : M) (nt_1 : numtype) (M_1 : M) (v_vcvtop : vcvtop) (c : vec_) (ci_lst : (seq lane_)) (cj_lst_lst : (seq (seq lane_))), 
		((zeroop v_vcvtop) == (Some ZERO)) ->
		(ci_lst == (lanes_ (X (lanetype_numtype nt_1) (mk_dim M_1)) c_1)) ->
		(cj_lst_lst == (setproduct_ lane_ ((seq.map (fun (ci : lane_) => (vcvtop__ (X (lanetype_numtype nt_1) (mk_dim M_1)) (X (lanetype_numtype nt_2) (mk_dim M_2)) v_vcvtop ci)) ci_lst) ++ (List.repeat [::(mk_lane__0 nt_2 (fun_zero nt_2))] M_1)))) ->
		((|(seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst)) cj_lst_lst)|) > 0)%N ->
		(c \in (seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst)) cj_lst_lst)) ->
		List.Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_numtype nt_1) (mk_dim M_1))) ci)) ci_lst ->
		List.Forall (fun (cj_lst : (seq lane_)) => List.Forall (fun (cj : lane_) => (wf_lane_ (lanetype_numtype nt_2) cj)) cj_lst) cj_lst_lst ->
		(wf_shape (X (lanetype_numtype nt_1) (mk_dim M_1))) ->
		(wf_shape (X (lanetype_numtype nt_2) (mk_dim M_2))) ->
		(wf_lane_ (lanetype_numtype nt_2) (mk_lane__0 nt_2 (fun_zero nt_2))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCVTOP (X (lanetype_numtype nt_2) (mk_dim M_2)) (X (lanetype_numtype nt_1) (mk_dim M_1)) v_vcvtop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__local_tee : forall (v_val : val) (x : idx), Step_pure [::(admininstr_val v_val); (admininstr_LOCAL_TEE x)] [::(admininstr_val v_val); (admininstr_val v_val); (admininstr_LOCAL_SET x)].

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.10-6.19 *)
Lemma Step_pure_is_wf : forall (var_0 : (seq admininstr)) (var_1 : (seq admininstr)),
	List.Forall (fun (var_0 : admininstr) => (wf_admininstr var_0)) var_0 ->
	(Step_pure var_0 var_1) ->
	List.Forall (fun (var_1 : admininstr) => (wf_admininstr var_1)) var_1.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 *)
Definition fun_blocktype (v_state : state) (v_blocktype : blocktype) : functype :=
	match v_state, v_blocktype return functype with
		| z, (_RESULT None) => (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
		| z, (_RESULT (Some t)) => (mk_functype (mk_list _ [:: ]) (mk_list _ [::t]))
		| z, (_IDX x) => (fun_type z x)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:127.1-129.15 *)
Inductive Step_read_before_call_indirect_trap : config -> Prop :=
	| call_indirect_call_0 : forall (z : state) (i : num_) (x : idx) (y : idx) (a : addr), 
		(((!((proj_num__0 i))) :> nat) < (|(REFS (fun_table z x))|))%N ->
		((proj_num__0 i) != None) ->
		(((REFS (fun_table z x))[| ((!((proj_num__0 i))) :> nat) |]) == (REF_FUNC_ADDR a)) ->
		(a < (|(fun_funcinst z)|))%N ->
		((fun_type z y) == (funcinst_TYPE ((fun_funcinst z)[| a |]))) ->
		Step_read_before_call_indirect_trap (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:436.1-439.14 *)
Inductive Step_read_before_table_fill_zero : config -> Prop :=
	| table_fill_trap_0 : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(REFS (fun_table z x))|))%N ->
		Step_read_before_table_fill_zero (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_FILL x)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:452.1-455.14 *)
Inductive Step_read_before_table_copy_zero : config -> Prop :=
	| table_copy_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(REFS (fun_table z y))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(REFS (fun_table z x))|))%N) ->
		Step_read_before_table_copy_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:457.1-462.15 *)
Inductive Step_read_before_table_copy_le : config -> Prop :=
	| table_copy_zero_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(~(Step_read_before_table_copy_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]))) ->
		(v_n == 0) ->
		Step_read_before_table_copy_le (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)])
	| table_copy_trap_1 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(REFS (fun_table z y))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(REFS (fun_table z x))|))%N) ->
		Step_read_before_table_copy_le (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:475.1-478.14 *)
Inductive Step_read_before_table_init_zero : config -> Prop :=
	| table_init_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(eleminst_REFS (fun_elem z y))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(REFS (fun_table z x))|))%N) ->
		Step_read_before_table_init_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_INIT x y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:616.1-619.14 *)
Inductive Step_read_before_memory_fill_zero : config -> Prop :=
	| memory_fill_trap_0 : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read_before_memory_fill_zero (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_FILL]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:632.1-635.14 *)
Inductive Step_read_before_memory_copy_zero : config -> Prop :=
	| memory_copy_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read_before_memory_copy_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:637.1-642.15 *)
Inductive Step_read_before_memory_copy_le : config -> Prop :=
	| memory_copy_zero_0 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		(~(Step_read_before_memory_copy_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]))) ->
		(v_n == 0) ->
		Step_read_before_memory_copy_le (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY])
	| memory_copy_trap_1 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read_before_memory_copy_le (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:655.1-658.14 *)
Inductive Step_read_before_memory_init_zero : config -> Prop :=
	| memory_init_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(datainst_BYTES (fun_data z x))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read_before_memory_init_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_MEMORY_INIT x)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.109 *)
Inductive Step_read : config -> (seq admininstr) -> Prop :=
	| Step_read__block : forall (z : state) (k : nat) (val_lst : (seq val)) (bt : blocktype) (instr_lst : (seq instr)) (v_n : n) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((fun_blocktype z bt) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(k == (|val_lst|)) ->
		(k == (|t_1_lst|)) ->
		(v_n == (|t_2_lst|)) ->
		Step_read (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_BLOCK bt instr_lst)])) [::(LABEL_ v_n [:: ] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))]
	| Step_read__loop : forall (z : state) (k : nat) (val_lst : (seq val)) (bt : blocktype) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (v_n : n) (t_2_lst : (seq valtype)), 
		((fun_blocktype z bt) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(k == (|val_lst|)) ->
		(k == (|t_1_lst|)) ->
		(v_n == (|t_2_lst|)) ->
		Step_read (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_LOOP bt instr_lst)])) [::(LABEL_ k [::(LOOP bt instr_lst)] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))]
	| Step_read__call : forall (z : state) (x : idx), 
		((x :> nat) < (|(fun_funcaddr z)|))%N ->
		Step_read (mk_config z [::(admininstr_CALL x)]) [::(CALL_ADDR ((fun_funcaddr z)[| (x :> nat) |]))]
	| call_indirect_call : forall (z : state) (i : num_) (x : idx) (y : idx) (a : addr), 
		(((!((proj_num__0 i))) :> nat) < (|(REFS (fun_table z x))|))%N ->
		((proj_num__0 i) != None) ->
		(((REFS (fun_table z x))[| ((!((proj_num__0 i))) :> nat) |]) == (REF_FUNC_ADDR a)) ->
		(a < (|(fun_funcinst z)|))%N ->
		((fun_type z y) == (funcinst_TYPE ((fun_funcinst z)[| a |]))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x y)]) [::(CALL_ADDR a)]
	| call_indirect_trap : forall (z : state) (i : num_) (x : idx) (y : idx), 
		(~(Step_read_before_call_indirect_trap (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x y)]))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x y)]) [::admininstr_TRAP]
	| call_addr : forall (z : state) (k : nat) (val_lst : (seq val)) (a : addr) (v_n : n) (f : frame) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)) (mm : moduleinst) (v_func : func) (x : idx) (t_lst : (seq valtype)), 
		(a < (|(fun_funcinst z)|))%N ->
		(((fun_funcinst z)[| a |]) == {| funcinst_TYPE := (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)); funcinst_MODULE := mm; CODE := v_func |}) ->
		(v_func == (func_FUNC x (seq.map (fun (t : valtype) => (LOCAL t)) t_lst) instr_lst)) ->
		List.Forall (fun (t : valtype) => ((default_ t) != None)) t_lst ->
		(f == {| LOCALS := (val_lst ++ (seq.map (fun (t : valtype) => (!((default_ t)))) t_lst)); frame_MODULE := mm |}) ->
		(wf_funcinst {| funcinst_TYPE := (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)); funcinst_MODULE := mm; CODE := v_func |}) ->
		(wf_func (func_FUNC x (seq.map (fun (t : valtype) => (LOCAL t)) t_lst) instr_lst)) ->
		(wf_frame {| LOCALS := (val_lst ++ (seq.map (fun (t : valtype) => (!((default_ t)))) t_lst)); frame_MODULE := mm |}) ->
		(k == (|val_lst|)) ->
		(k == (|t_1_lst|)) ->
		(v_n == (|t_2_lst|)) ->
		Step_read (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(CALL_ADDR a)])) [::(FRAME_ v_n f [::(LABEL_ v_n [:: ] (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))])]
	| Step_read__ref_func : forall (z : state) (x : idx), 
		((x :> nat) < (|(fun_funcaddr z)|))%N ->
		Step_read (mk_config z [::(admininstr_REF_FUNC x)]) [::(admininstr_REF_FUNC_ADDR ((fun_funcaddr z)[| (x :> nat) |]))]
	| Step_read__local_get : forall (z : state) (x : idx), Step_read (mk_config z [::(admininstr_LOCAL_GET x)]) [::(admininstr_val (fun_local z x))]
	| Step_read__global_get : forall (z : state) (x : idx), Step_read (mk_config z [::(admininstr_GLOBAL_GET x)]) [::(admininstr_val (VALUE (fun_global z x)))]
	| table_get_trap : forall (z : state) (i : num_) (x : idx), 
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 i))) :> nat) >= (|(REFS (fun_table z x))|))%N ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_TABLE_GET x)]) [::admininstr_TRAP]
	| table_get_val : forall (z : state) (i : num_) (x : idx), 
		(((!((proj_num__0 i))) :> nat) < (|(REFS (fun_table z x))|))%N ->
		((proj_num__0 i) != None) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_TABLE_GET x)]) [::(admininstr_ref ((REFS (fun_table z x))[| ((!((proj_num__0 i))) :> nat) |]))]
	| Step_read__table_size : forall (z : state) (x : idx) (v_n : n), 
		((|(REFS (fun_table z x))|) == v_n) ->
		Step_read (mk_config z [::(admininstr_TABLE_SIZE x)]) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))]
	| table_fill_trap : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(REFS (fun_table z x))|))%N ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_FILL x)]) [::admininstr_TRAP]
	| table_fill_zero : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(REFS (fun_table z x))|))%N ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_FILL x)]) [:: ]
	| table_fill_succ : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		(v_n != 0) ->
		((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(REFS (fun_table z x))|))%N ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_FILL x)]) [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_TABLE_SET x); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)%N))); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : int) - (1 : int))%Z : nat)))); (admininstr_TABLE_FILL x)]
	| table_copy_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(REFS (fun_table z y))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(REFS (fun_table z x))|))%N) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]) [::admininstr_TRAP]
	| table_copy_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(REFS (fun_table z y))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(REFS (fun_table z x))|))%N) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]) [:: ]
	| table_copy_le : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 j) != None) ->
		((proj_num__0 i) != None) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(REFS (fun_table z y))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(REFS (fun_table z x))|))%N) ->
		(((!((proj_num__0 j))) :> nat) <= ((!((proj_num__0 i))) :> nat))%N ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]) [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_TABLE_GET y); (admininstr_TABLE_SET x); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 j))) :> nat) + 1)%N))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)%N))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : int) - (1 : int))%Z : nat)))); (admininstr_TABLE_COPY x y)]
	| table_copy_gt : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 j) != None) ->
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 j))) :> nat) > ((!((proj_num__0 i))) :> nat))%N ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(REFS (fun_table z y))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(REFS (fun_table z x))|))%N) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((((!((proj_num__0 j))) :> nat) + v_n)%N : int) - (1 : int))%Z : nat)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((((!((proj_num__0 i))) :> nat) + v_n)%N : int) - (1 : int))%Z : nat)))); (admininstr_TABLE_GET y); (admininstr_TABLE_SET x); (admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : int) - (1 : int))%Z : nat)))); (admininstr_TABLE_COPY x y)]
	| table_init_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(eleminst_REFS (fun_elem z y))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(REFS (fun_table z x))|))%N) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_INIT x y)]) [::admininstr_TRAP]
	| table_init_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(eleminst_REFS (fun_elem z y))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(REFS (fun_table z x))|))%N) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_INIT x y)]) [:: ]
	| table_init_succ : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(((!((proj_num__0 i))) :> nat) < (|(eleminst_REFS (fun_elem z y))|))%N ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(eleminst_REFS (fun_elem z y))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(REFS (fun_table z x))|))%N) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_INIT x y)]) [::(admininstr_CONST I32 j); (admininstr_ref ((eleminst_REFS (fun_elem z y))[| ((!((proj_num__0 i))) :> nat) |])); (admininstr_TABLE_SET x); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 j))) :> nat) + 1)%N))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)%N))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : int) - (1 : int))%Z : nat)))); (admininstr_TABLE_INIT x y)]
	| load_num_trap : forall (z : state) (i : num_) (nt : numtype) (ao : memarg), 
		((proj_num__0 i) != None) ->
		((res_size (valtype_numtype nt)) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + ((((!((res_size (valtype_numtype nt)))) : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD nt None ao)]) [::admininstr_TRAP]
	| load_num_val : forall (z : state) (i : num_) (nt : numtype) (ao : memarg) (c : num_), 
		((proj_num__0 i) != None) ->
		((res_size (valtype_numtype nt)) != None) ->
		((nbytes_ nt c) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N ((((!((res_size (valtype_numtype nt)))) : rat) / (8 : rat))%Q : nat))) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD nt None ao)]) [::(admininstr_CONST nt c)]
	| load_pack_trap : forall (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg), 
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + (((v_n : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)]) [::admininstr_TRAP]
	| load_pack_val : forall (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) (c : iN), 
		((res_size (valtype_Inn v_Inn)) != None) ->
		((proj_num__0 i) != None) ->
		((ibytes_ v_n c) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N (((v_n : rat) / (8 : rat))%Q : nat))) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)]) [::(admininstr_CONST (numtype_Inn v_Inn) (mk_num__0 v_Inn (extend__ v_n (!((res_size (valtype_Inn v_Inn)))) v_sx c)))]
	| vload_oob : forall (z : state) (i : num_) (ao : memarg), 
		((proj_num__0 i) != None) ->
		((res_size valtype_V128) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + ((((!((res_size valtype_V128))) : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 None ao)]) [::admininstr_TRAP]
	| vload_val : forall (z : state) (i : num_) (ao : memarg) (c : vec_), 
		((proj_num__0 i) != None) ->
		((res_size valtype_V128) != None) ->
		((vbytes_ V128 c) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N ((((!((res_size valtype_V128))) : rat) / (8 : rat))%Q : nat))) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 None ao)]) [::(admininstr_VCONST V128 c)]
	| vload_shape_oob : forall (z : state) (i : num_) (v_M : M) (v_N : res_N) (v_sx : sx) (ao : memarg), 
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + ((((v_M * v_N)%N : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (SHAPEX_ v_M v_N v_sx)) ao)]) [::admininstr_TRAP]
	| vload_shape_val : forall (z : state) (i : num_) (v_M : M) (v_N : res_N) (v_sx : sx) (ao : memarg) (c : vec_) (j_lst : (seq iN)) (v_Jnn : Jnn), 
		holds_upto (fun k => ((proj_num__0 i) != None)) v_N ->
		List_Foralli (fun k (j : iN) => ((ibytes_ v_M j) == (list_slice (BYTES (fun_mem z (mk_uN 0))) ((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + ((((k * v_M)%N : rat) / (8 : rat))%Q : nat))%N (((v_M : rat) / (8 : rat))%Q : nat)))) j_lst ->
		((jsize v_Jnn) == (v_M * 2)%N) ->
		(c == (inv_lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (seq.map (fun (j : iN) => (mk_lane__2 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j))) j_lst))) ->
		(wf_uN 32 (mk_uN 0)) ->
		(wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ->
		List.Forall (fun (j : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) (mk_lane__2 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j)))) j_lst ->
		(v_N == (|j_lst|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (SHAPEX_ v_M v_N v_sx)) ao)]) [::(admininstr_VCONST V128 c)]
	| vload_splat_oob : forall (z : state) (i : num_) (v_N : res_N) (ao : memarg), 
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + (((v_N : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (SPLAT v_N)) ao)]) [::admininstr_TRAP]
	| vload_splat_val : forall (z : state) (i : num_) (v_N : res_N) (ao : memarg) (c : vec_) (j : iN) (v_Jnn : Jnn) (v_M : M), 
		((proj_num__0 i) != None) ->
		((ibytes_ v_N j) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N (((v_N : rat) / (8 : rat))%Q : nat))) ->
		(v_N == (jsize v_Jnn)) ->
		((v_M : rat) == ((128 : rat) / (v_N : rat))%Q) ->
		(c == (inv_lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (List.repeat (mk_lane__2 v_Jnn (mk_uN (j :> (nat)))) v_M))) ->
		(wf_uN 32 (mk_uN 0)) ->
		(wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ->
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (j :> (nat))))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (SPLAT v_N)) ao)]) [::(admininstr_VCONST V128 c)]
	| vload_zero_oob : forall (z : state) (i : num_) (v_N : res_N) (ao : memarg), 
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + (((v_N : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (vloadop_ZERO v_N)) ao)]) [::admininstr_TRAP]
	| vload_zero_val : forall (z : state) (i : num_) (v_N : res_N) (ao : memarg) (c : vec_) (j : iN), 
		((proj_num__0 i) != None) ->
		((ibytes_ v_N j) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N (((v_N : rat) / (8 : rat))%Q : nat))) ->
		(c == (extend__ v_N 128 U j)) ->
		(wf_uN v_N j) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (vloadop_ZERO v_N)) ao)]) [::(admininstr_VCONST V128 c)]
	| vload_lane_oob : forall (z : state) (i : num_) (c_1 : vec_) (v_N : res_N) (ao : memarg) (j : laneidx), 
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + (((v_N : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c_1); (admininstr_VLOAD_LANE V128 (mk_sz v_N) ao j)]) [::admininstr_TRAP]
	| vload_lane_val : forall (z : state) (i : num_) (c_1 : vec_) (v_N : res_N) (ao : memarg) (j : laneidx) (c : vec_) (k : iN) (v_Jnn : Jnn) (v_M : M), 
		((proj_num__0 i) != None) ->
		((ibytes_ v_N k) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N (((v_N : rat) / (8 : rat))%Q : nat))) ->
		(v_N == (jsize v_Jnn)) ->
		((v_M : rat) == ((128 : rat) / (v_N : rat))%Q) ->
		(c == (inv_lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (list_update_func (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) (j :> nat) (fun (_ : lane_) => (mk_lane__2 v_Jnn (mk_uN (k :> (nat)))))))) ->
		(wf_uN 32 (mk_uN 0)) ->
		(wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ->
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (k :> (nat))))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c_1); (admininstr_VLOAD_LANE V128 (mk_sz v_N) ao j)]) [::(admininstr_VCONST V128 c)]
	| Step_read__memory_size : forall (z : state) (v_n : n), 
		(((v_n * 64)%N * (Ki ))%N == (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::admininstr_MEMORY_SIZE]) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))]
	| memory_fill_trap : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_FILL]) [::admininstr_TRAP]
	| memory_fill_zero : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_FILL]) [:: ]
	| memory_fill_succ : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
		((proj_num__0 i) != None) ->
		(v_n != 0) ->
		((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_FILL]) [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_STORE I32 (Some (mk_sz 8)) (memarg0 )); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)%N))); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : int) - (1 : int))%Z : nat)))); admininstr_MEMORY_FILL]
	| memory_copy_trap : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]) [::admininstr_TRAP]
	| memory_copy_zero : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]) [:: ]
	| memory_copy_le : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 j) != None) ->
		((proj_num__0 i) != None) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		(((!((proj_num__0 j))) :> nat) <= ((!((proj_num__0 i))) :> nat))%N ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]) [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) (memarg0 )); (admininstr_STORE I32 (Some (mk_sz 8)) (memarg0 )); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 j))) :> nat) + 1)%N))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)%N))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : int) - (1 : int))%Z : nat)))); admininstr_MEMORY_COPY]
	| memory_copy_gt : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 j) != None) ->
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 j))) :> nat) > ((!((proj_num__0 i))) :> nat))%N ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((((!((proj_num__0 j))) :> nat) + v_n)%N : int) - (1 : int))%Z : nat)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((((!((proj_num__0 i))) :> nat) + v_n)%N : int) - (1 : int))%Z : nat)))); (admininstr_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) (memarg0 )); (admininstr_STORE I32 (Some (mk_sz 8)) (memarg0 )); (admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : int) - (1 : int))%Z : nat)))); admininstr_MEMORY_COPY]
	| memory_init_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N > (|(datainst_BYTES (fun_data z x))|))%N || ((((!((proj_num__0 j))) :> nat) + v_n)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_MEMORY_INIT x)]) [::admininstr_TRAP]
	| memory_init_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(datainst_BYTES (fun_data z x))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_MEMORY_INIT x)]) [:: ]
	| memory_init_succ : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
		(((!((proj_num__0 i))) :> nat) < (|(datainst_BYTES (fun_data z x))|))%N ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n)%N <= (|(datainst_BYTES (fun_data z x))|))%N && ((((!((proj_num__0 j))) :> nat) + v_n)%N <= (|(BYTES (fun_mem z (mk_uN 0)))|))%N) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_MEMORY_INIT x)]) [::(admininstr_CONST I32 j); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((datainst_BYTES (fun_data z x))[| ((!((proj_num__0 i))) :> nat) |]) :> (nat))))); (admininstr_STORE I32 (Some (mk_sz 8)) (memarg0 )); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 j))) :> nat) + 1)%N))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)%N))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : int) - (1 : int))%Z : nat)))); (admininstr_MEMORY_INIT x)].

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 *)
Lemma Step_read_is_wf : forall (var_0 : config) (var_1 : (seq admininstr)),
	(wf_config var_0) ->
	(Step_read var_0 var_1) ->
	List.Forall (fun (var_1 : admininstr) => (wf_admininstr var_1)) var_1.
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 *)
Inductive Step : config -> config -> Prop :=
	| pure : forall (z : state) (admininstr_lst : (seq admininstr)) (admininstr'_lst : (seq admininstr)), 
		(Step_pure admininstr_lst admininstr'_lst) ->
		Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)
	| read : forall (z : state) (admininstr_lst : (seq admininstr)) (admininstr'_lst : (seq admininstr)), 
		(Step_read (mk_config z admininstr_lst) admininstr'_lst) ->
		Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)
	| ctxt_label : forall (z : state) (v_n : n) (instr_0_lst : (seq instr)) (admininstr_lst : (seq admininstr)) (z' : state) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ->
		(wf_config (mk_config z admininstr_lst)) ->
		(wf_config (mk_config z' admininstr'_lst)) ->
		Step (mk_config z [::(LABEL_ v_n instr_0_lst admininstr_lst)]) (mk_config z' [::(LABEL_ v_n instr_0_lst admininstr'_lst)])
	| ctxt_frame : forall (s : store) (f : frame) (v_n : n) (f' : frame) (admininstr_lst : (seq admininstr)) (s' : store) (f'' : frame) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config (mk_state s f') admininstr_lst) (mk_config (mk_state s' f'') admininstr'_lst)) ->
		(wf_config (mk_config (mk_state s f') admininstr_lst)) ->
		(wf_config (mk_config (mk_state s' f'') admininstr'_lst)) ->
		Step (mk_config (mk_state s f) [::(FRAME_ v_n f' admininstr_lst)]) (mk_config (mk_state s' f) [::(FRAME_ v_n f'' admininstr'_lst)])
	| ctxt_instrs : forall (z : state) (val_lst : (seq val)) (admininstr_lst : (seq admininstr)) (admininstr_1_lst : (seq admininstr)) (z' : state) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ->
		((val_lst != [:: ]) || (admininstr_1_lst != [:: ])) ->
		(wf_config (mk_config z admininstr_lst)) ->
		(wf_config (mk_config z' admininstr'_lst)) ->
		Step (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (admininstr_lst ++ admininstr_1_lst))) (mk_config z' ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (admininstr'_lst ++ admininstr_1_lst)))
	| Step__local_set : forall (z : state) (v_val : val) (x : idx), Step (mk_config z [::(admininstr_val v_val); (admininstr_LOCAL_SET x)]) (mk_config (with_local z x v_val) [:: ])
	| Step__global_set : forall (z : state) (v_val : val) (x : idx), Step (mk_config z [::(admininstr_val v_val); (admininstr_GLOBAL_SET x)]) (mk_config (with_global z x v_val) [:: ])
	| table_set_trap : forall (z : state) (i : num_) (v_ref : ref) (x : idx), 
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 i))) :> nat) >= (|(REFS (fun_table z x))|))%N ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_ref v_ref); (admininstr_TABLE_SET x)]) (mk_config z [::admininstr_TRAP])
	| table_set_val : forall (z : state) (i : num_) (v_ref : ref) (x : idx), 
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 i))) :> nat) < (|(REFS (fun_table z x))|))%N ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_ref v_ref); (admininstr_TABLE_SET x)]) (mk_config (with_table z x ((!((proj_num__0 i))) :> nat) v_ref) [:: ])
	| table_grow_succeed : forall (z : state) (v_ref : ref) (v_n : n) (x : idx) (ti : tableinst) (var_0 : (option tableinst)), 
		(fun_growtable (fun_table z x) v_n v_ref var_0) ->
		(var_0 != None) ->
		((!(var_0)) == ti) ->
		Step (mk_config z [::(admininstr_ref v_ref); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_GROW x)]) (mk_config (with_tableinst z x ti) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (|(REFS (fun_table z x))|))))])
	| table_grow_fail : forall (z : state) (v_ref : ref) (v_n : n) (x : idx) (var_0 : nat), 
		(fun_inv_signed_ 32 (0 - (1 : int))%Z var_0) ->
		Step (mk_config z [::(admininstr_ref v_ref); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_GROW x)]) (mk_config z [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN var_0)))])
	| Step__elem_drop : forall (z : state) (x : idx), Step (mk_config z [::(admininstr_ELEM_DROP x)]) (mk_config (with_elem z x [:: ]) [:: ])
	| store_num_trap : forall (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg), 
		((proj_num__0 i) != None) ->
		((res_size (valtype_numtype nt)) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + ((((!((res_size (valtype_numtype nt)))) : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST nt c); (admininstr_STORE nt None ao)]) (mk_config z [::admininstr_TRAP])
	| store_num_val : forall (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) (b_lst : (seq byte)), 
		((proj_num__0 i) != None) ->
		((res_size (valtype_numtype nt)) != None) ->
		(b_lst == (nbytes_ nt c)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST nt c); (admininstr_STORE nt None ao)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N ((((!((res_size (valtype_numtype nt)))) : rat) / (8 : rat))%Q : nat) b_lst) [:: ])
	| store_pack_trap : forall (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg), 
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + (((v_n : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST (numtype_Inn v_Inn) c); (admininstr_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]) (mk_config z [::admininstr_TRAP])
	| store_pack_val : forall (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) (b_lst : (seq byte)), 
		((proj_num__0 i) != None) ->
		((res_size (valtype_Inn v_Inn)) != None) ->
		((proj_num__0 c) != None) ->
		(b_lst == (ibytes_ v_n (wrap__ (!((res_size (valtype_Inn v_Inn)))) v_n (!((proj_num__0 c)))))) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST (numtype_Inn v_Inn) c); (admininstr_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N (((v_n : rat) / (8 : rat))%Q : nat) b_lst) [:: ])
	| vstore_oob : forall (z : state) (i : num_) (c : vec_) (ao : memarg), 
		((proj_num__0 i) != None) ->
		((res_size valtype_V128) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + ((((!((res_size valtype_V128))) : rat) / (8 : rat))%Q : nat))%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c); (admininstr_VSTORE V128 ao)]) (mk_config z [::admininstr_TRAP])
	| vstore_val : forall (z : state) (i : num_) (c : vec_) (ao : memarg) (b_lst : (seq byte)), 
		((proj_num__0 i) != None) ->
		((res_size valtype_V128) != None) ->
		(b_lst == (vbytes_ V128 c)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c); (admininstr_VSTORE V128 ao)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N ((((!((res_size valtype_V128))) : rat) / (8 : rat))%Q : nat) b_lst) [:: ])
	| vstore_lane_oob : forall (z : state) (i : num_) (c : vec_) (v_N : res_N) (ao : memarg) (j : laneidx), 
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N + v_N)%N > (|(BYTES (fun_mem z (mk_uN 0)))|))%N ->
		(wf_uN 32 (mk_uN 0)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c); (admininstr_VSTORE_LANE V128 (mk_sz v_N) ao j)]) (mk_config z [::admininstr_TRAP])
	| vstore_lane_val : forall (z : state) (i : num_) (c : vec_) (v_N : res_N) (ao : memarg) (j : laneidx) (b_lst : (seq byte)) (v_Jnn : Jnn) (v_M : M), 
		((proj_num__0 i) != None) ->
		(v_N == (jsize v_Jnn)) ->
		((v_M : rat) == ((128 : rat) / (v_N : rat))%Q) ->
		((proj_lane__2 ((lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c)[| (j :> nat) |])) != None) ->
		((j :> nat) < (|(lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c)|))%N ->
		(b_lst == (ibytes_ v_N (mk_uN ((!((proj_lane__2 ((lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c)[| (j :> nat) |])))) :> (nat))))) ->
		(wf_uN v_N (mk_uN ((!((proj_lane__2 ((lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c)[| (j :> nat) |])))) :> (nat)))) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c); (admininstr_VSTORE_LANE V128 (mk_sz v_N) ao j)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat))%N (((v_N : rat) / (8 : rat))%Q : nat) b_lst) [:: ])
	| memory_grow_succeed : forall (z : state) (v_n : n) (mi : meminst) (var_0 : (option meminst)), 
		(fun_growmemory (fun_mem z (mk_uN 0)) v_n var_0) ->
		(var_0 != None) ->
		((!(var_0)) == mi) ->
		(wf_uN 32 (mk_uN 0)) ->
		Step (mk_config z [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_GROW]) (mk_config (with_meminst z (mk_uN 0) mi) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((|(BYTES (fun_mem z (mk_uN 0)))|) : rat) / ((64 * (Ki ))%N : rat))%Q : nat))))])
	| memory_grow_fail : forall (z : state) (v_n : n) (var_0 : nat), 
		(fun_inv_signed_ 32 (0 - (1 : int))%Z var_0) ->
		Step (mk_config z [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_GROW]) (mk_config z [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN var_0)))])
	| Step__data_drop : forall (z : state) (x : idx), Step (mk_config z [::(admininstr_DATA_DROP x)]) (mk_config (with_data z x [:: ]) [:: ]).

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 *)
Lemma Step_is_wf : forall (var_0 : config) (var_1 : config),
	(wf_config var_0) ->
	(Step var_0 var_1) ->
	(wf_config var_1).
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 *)
Inductive Steps : config -> config -> Prop :=
	| Steps__refl : forall (z : state) (admininstr_lst : (seq admininstr)), 
		(wf_config (mk_config z admininstr_lst)) ->
		Steps (mk_config z admininstr_lst) (mk_config z admininstr_lst)
	| trans : forall (z : state) (admininstr_lst : (seq admininstr)) (z'' : state) (admininstr''_lst : (seq admininstr)) (z' : state) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ->
		(Steps (mk_config z' admininstr'_lst) (mk_config z'' admininstr''_lst)) ->
		(wf_config (mk_config z admininstr_lst)) ->
		(wf_config (mk_config z'' admininstr''_lst)) ->
		(wf_config (mk_config z' admininstr'_lst)) ->
		Steps (mk_config z admininstr_lst) (mk_config z'' admininstr''_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83 *)
Inductive Eval_expr : state -> expr -> state -> (seq val) -> Prop :=
	| mk_Eval_expr : forall (z : state) (instr_lst : (seq instr)) (z' : state) (val_lst : (seq val)), 
		(Steps (mk_config z (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)) (mk_config z' (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))) ->
		(wf_config (mk_config z (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))) ->
		(wf_config (mk_config z' (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))) ->
		Eval_expr z instr_lst z' val_lst.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:5.1-5.36 *)
Inductive fun_funcs : (seq externaddr) -> (seq funcaddr) -> Prop :=
	| fun_funcs_case_0 : fun_funcs [:: ] [:: ]
	| fun_funcs_case_1 : forall (fa : nat) (externaddr'_lst : (seq externaddr)) (var_0 : (seq funcaddr)), 
		(fun_funcs externaddr'_lst var_0) ->
		fun_funcs ([::(externaddr_FUNC fa)] ++ externaddr'_lst) ([::fa] ++ var_0)
	| fun_funcs_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (seq externaddr)) (var_0 : (seq funcaddr)), 
		(fun_funcs externaddr'_lst var_0) ->
		fun_funcs ([::v_externaddr] ++ externaddr'_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:11.1-11.40 *)
Inductive fun_globals : (seq externaddr) -> (seq globaladdr) -> Prop :=
	| fun_globals_case_0 : fun_globals [:: ] [:: ]
	| fun_globals_case_1 : forall (ga : nat) (externaddr'_lst : (seq externaddr)) (var_0 : (seq globaladdr)), 
		(fun_globals externaddr'_lst var_0) ->
		fun_globals ([::(externaddr_GLOBAL ga)] ++ externaddr'_lst) ([::ga] ++ var_0)
	| fun_globals_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (seq externaddr)) (var_0 : (seq globaladdr)), 
		(fun_globals externaddr'_lst var_0) ->
		fun_globals ([::v_externaddr] ++ externaddr'_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:17.1-17.38 *)
Inductive fun_tables : (seq externaddr) -> (seq tableaddr) -> Prop :=
	| fun_tables_case_0 : fun_tables [:: ] [:: ]
	| fun_tables_case_1 : forall (ta : nat) (externaddr'_lst : (seq externaddr)) (var_0 : (seq tableaddr)), 
		(fun_tables externaddr'_lst var_0) ->
		fun_tables ([::(externaddr_TABLE ta)] ++ externaddr'_lst) ([::ta] ++ var_0)
	| fun_tables_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (seq externaddr)) (var_0 : (seq tableaddr)), 
		(fun_tables externaddr'_lst var_0) ->
		fun_tables ([::v_externaddr] ++ externaddr'_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:23.1-23.34 *)
Inductive fun_mems : (seq externaddr) -> (seq memaddr) -> Prop :=
	| fun_mems_case_0 : fun_mems [:: ] [:: ]
	| fun_mems_case_1 : forall (ma : nat) (externaddr'_lst : (seq externaddr)) (var_0 : (seq memaddr)), 
		(fun_mems externaddr'_lst var_0) ->
		fun_mems ([::(externaddr_MEM ma)] ++ externaddr'_lst) ([::ma] ++ var_0)
	| fun_mems_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (seq externaddr)) (var_0 : (seq memaddr)), 
		(fun_mems externaddr'_lst var_0) ->
		fun_mems ([::v_externaddr] ++ externaddr'_lst) var_0.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 *)
Inductive fun_allocfunc : store -> moduleinst -> func -> (store * funcaddr) -> Prop :=
	| fun_allocfunc_case_0 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (fi : funcinst) (x : uN) (local_lst : (seq local)) (v_expr : (seq instr)), 
		((x :> nat) < (|(TYPES v_moduleinst)|))%N ->
		(fi == {| funcinst_TYPE := ((TYPES v_moduleinst)[| (x :> nat) |]); funcinst_MODULE := v_moduleinst; CODE := v_func |}) ->
		(v_func == (func_FUNC x local_lst v_expr)) ->
		(wf_funcinst {| funcinst_TYPE := ((TYPES v_moduleinst)[| (x :> nat) |]); funcinst_MODULE := v_moduleinst; CODE := v_func |}) ->
		(wf_func (func_FUNC x local_lst v_expr)) ->
		fun_allocfunc s v_moduleinst v_func ((s <| store_FUNCS := ((store_FUNCS s) ++ [::fi]) |>), (|(store_FUNCS s)|)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 *)
Lemma allocfunc_is_wf : forall (v_store : store) (v_moduleinst : moduleinst) (v_func : func) (ret_val : (store * funcaddr)) (var_0 : (store * funcaddr)),
	(fun_allocfunc v_store v_moduleinst v_func var_0) ->
	(wf_store v_store) ->
	(wf_moduleinst v_moduleinst) ->
	(wf_func v_func) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
Inductive fun_allocfuncs : store -> moduleinst -> (seq func) -> (store * (seq funcaddr)) -> Prop :=
	| fun_allocfuncs_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_allocfuncs s v_moduleinst [:: ] (s, [:: ])
	| fun_allocfuncs_case_1 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (func'_lst : (seq func)) (fa : funcaddr) (s_1 : store) (s_2 : store) (fa'_lst : (seq funcaddr)) (var_1 : (store * (seq funcaddr))) (var_0 : (store * funcaddr)), 
		(fun_allocfuncs s_1 v_moduleinst func'_lst var_1) ->
		(fun_allocfunc s v_moduleinst v_func var_0) ->
		((s_1, fa) == var_0) ->
		((s_2, fa'_lst) == var_1) ->
		fun_allocfuncs s v_moduleinst ([::v_func] ++ func'_lst) (s_2, ([::fa] ++ fa'_lst)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
Lemma allocfuncs_is_wf : forall (v_store : store) (v_moduleinst : moduleinst) (var_0_lst : (seq func)) (ret_val : (store * (seq funcaddr))) (var_0 : (store * (seq funcaddr))),
	(fun_allocfuncs v_store v_moduleinst var_0_lst var_0) ->
	(wf_store v_store) ->
	(wf_moduleinst v_moduleinst) ->
	List.Forall (fun (var_0 : func) => (wf_func var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
Inductive fun_allocglobal : store -> globaltype -> val -> (store * globaladdr) -> Prop :=
	| fun_allocglobal_case_0 : forall (s : store) (v_globaltype : globaltype) (v_val : val) (gi : globalinst), 
		(gi == {| globalinst_TYPE := v_globaltype; VALUE := v_val |}) ->
		(wf_globalinst {| globalinst_TYPE := v_globaltype; VALUE := v_val |}) ->
		fun_allocglobal s v_globaltype v_val ((s <| store_GLOBALS := ((store_GLOBALS s) ++ [::gi]) |>), (|(store_GLOBALS s)|)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
Lemma allocglobal_is_wf : forall (v_store : store) (v_globaltype : globaltype) (v_val : val) (ret_val : (store * globaladdr)) (var_0 : (store * globaladdr)),
	(fun_allocglobal v_store v_globaltype v_val var_0) ->
	(wf_store v_store) ->
	(wf_val v_val) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
Inductive fun_allocglobals : store -> (seq globaltype) -> (seq val) -> (store * (seq globaladdr)) -> Prop :=
	| fun_allocglobals_case_0 : forall (s : store), fun_allocglobals s [:: ] [:: ] (s, [:: ])
	| fun_allocglobals_case_1 : forall (s : store) (v_globaltype : globaltype) (globaltype'_lst : (seq globaltype)) (v_val : val) (val'_lst : (seq val)) (ga : globaladdr) (s_1 : store) (s_2 : store) (ga'_lst : (seq globaladdr)) (var_1 : (store * (seq globaladdr))) (var_0 : (store * globaladdr)), 
		(fun_allocglobals s_1 globaltype'_lst val'_lst var_1) ->
		(fun_allocglobal s v_globaltype v_val var_0) ->
		((s_1, ga) == var_0) ->
		((s_2, ga'_lst) == var_1) ->
		fun_allocglobals s ([::v_globaltype] ++ globaltype'_lst) ([::v_val] ++ val'_lst) (s_2, ([::ga] ++ ga'_lst)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
Lemma allocglobals_is_wf : forall (v_store : store) (var_0_lst : (seq globaltype)) (var_1_lst : (seq val)) (ret_val : (store * (seq globaladdr))) (var_0 : (store * (seq globaladdr))),
	(fun_allocglobals v_store var_0_lst var_1_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_1 : val) => (wf_val var_1)) var_1_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
Inductive fun_alloctable : store -> tabletype -> (store * tableaddr) -> Prop :=
	| fun_alloctable_case_0 : forall (s : store) (i : uN) (j_opt : (option u32)) (rt : reftype) (ti : tableinst), 
		(ti == {| tableinst_TYPE := (mk_tabletype (mk_limits i j_opt) rt); REFS := (List.repeat (ref_REF_NULL rt) (i :> nat)) |}) ->
		(wf_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits i j_opt) rt); REFS := (List.repeat (ref_REF_NULL rt) (i :> nat)) |}) ->
		fun_alloctable s (mk_tabletype (mk_limits i j_opt) rt) ((s <| store_TABLES := ((store_TABLES s) ++ [::ti]) |>), (|(store_TABLES s)|)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
Lemma alloctable_is_wf : forall (v_store : store) (v_tabletype : tabletype) (ret_val : (store * tableaddr)) (var_0 : (store * tableaddr)),
	(fun_alloctable v_store v_tabletype var_0) ->
	(wf_store v_store) ->
	(wf_tabletype v_tabletype) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
Inductive fun_alloctables : store -> (seq tabletype) -> (store * (seq tableaddr)) -> Prop :=
	| fun_alloctables_case_0 : forall (s : store), fun_alloctables s [:: ] (s, [:: ])
	| fun_alloctables_case_1 : forall (s : store) (v_tabletype : tabletype) (tabletype'_lst : (seq tabletype)) (ta : tableaddr) (s_1 : store) (s_2 : store) (ta'_lst : (seq tableaddr)) (var_1 : (store * (seq tableaddr))) (var_0 : (store * tableaddr)), 
		(fun_alloctables s_1 tabletype'_lst var_1) ->
		(fun_alloctable s v_tabletype var_0) ->
		((s_1, ta) == var_0) ->
		((s_2, ta'_lst) == var_1) ->
		fun_alloctables s ([::v_tabletype] ++ tabletype'_lst) (s_2, ([::ta] ++ ta'_lst)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
Lemma alloctables_is_wf : forall (v_store : store) (var_0_lst : (seq tabletype)) (ret_val : (store * (seq tableaddr))) (var_0 : (store * (seq tableaddr))),
	(fun_alloctables v_store var_0_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0 : tabletype) => (wf_tabletype var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
Inductive fun_allocmem : store -> memtype -> (store * memaddr) -> Prop :=
	| fun_allocmem_case_0 : forall (s : store) (i : uN) (j_opt : (option u32)) (mi : meminst), 
		(mi == {| meminst_TYPE := (PAGE (mk_limits i j_opt)); BYTES := (List.repeat (mk_byte 0) ((i :> nat) * (64 * (Ki ))%N)%N) |}) ->
		(wf_meminst {| meminst_TYPE := (PAGE (mk_limits i j_opt)); BYTES := (List.repeat (mk_byte 0) ((i :> nat) * (64 * (Ki ))%N)%N) |}) ->
		fun_allocmem s (PAGE (mk_limits i j_opt)) ((s <| store_MEMS := ((store_MEMS s) ++ [::mi]) |>), (|(store_MEMS s)|)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
Lemma allocmem_is_wf : forall (v_store : store) (v_memtype : memtype) (ret_val : (store * memaddr)) (var_0 : (store * memaddr)),
	(fun_allocmem v_store v_memtype var_0) ->
	(wf_store v_store) ->
	(wf_memtype v_memtype) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
Inductive fun_allocmems : store -> (seq memtype) -> (store * (seq memaddr)) -> Prop :=
	| fun_allocmems_case_0 : forall (s : store), fun_allocmems s [:: ] (s, [:: ])
	| fun_allocmems_case_1 : forall (s : store) (v_memtype : memtype) (memtype'_lst : (seq memtype)) (ma : memaddr) (s_1 : store) (s_2 : store) (ma'_lst : (seq memaddr)) (var_1 : (store * (seq memaddr))) (var_0 : (store * memaddr)), 
		(fun_allocmems s_1 memtype'_lst var_1) ->
		(fun_allocmem s v_memtype var_0) ->
		((s_1, ma) == var_0) ->
		((s_2, ma'_lst) == var_1) ->
		fun_allocmems s ([::v_memtype] ++ memtype'_lst) (s_2, ([::ma] ++ ma'_lst)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
Lemma allocmems_is_wf : forall (v_store : store) (var_0_lst : (seq memtype)) (ret_val : (store * (seq memaddr))) (var_0 : (store * (seq memaddr))),
	(fun_allocmems v_store var_0_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0 : memtype) => (wf_memtype var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
Inductive fun_allocelem : store -> reftype -> (seq ref) -> (store * elemaddr) -> Prop :=
	| fun_allocelem_case_0 : forall (s : store) (rt : reftype) (ref_lst : (seq ref)) (ei : eleminst), 
		(ei == {| eleminst_TYPE := rt; eleminst_REFS := ref_lst |}) ->
		fun_allocelem s rt ref_lst ((s <| store_ELEMS := ((store_ELEMS s) ++ [::ei]) |>), (|(store_ELEMS s)|)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
Lemma allocelem_is_wf : forall (v_store : store) (v_reftype : reftype) (var_0_lst : (seq ref)) (ret_val : (store * elemaddr)) (var_0 : (store * elemaddr)),
	(fun_allocelem v_store v_reftype var_0_lst var_0) ->
	(wf_store v_store) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
Inductive fun_allocelems : store -> (seq reftype) -> (seq (seq ref)) -> (store * (seq elemaddr)) -> Prop :=
	| fun_allocelems_case_0 : forall (s : store), fun_allocelems s [:: ] [:: ] (s, [:: ])
	| fun_allocelems_case_1 : forall (s : store) (rt : reftype) (rt'_lst : (seq reftype)) (ref_lst : (seq ref)) (ref'_lst_lst : (seq (seq ref))) (ea : elemaddr) (s_1 : store) (s_2 : store) (ea'_lst : (seq elemaddr)) (var_1 : (store * (seq elemaddr))) (var_0 : (store * elemaddr)), 
		(fun_allocelems s_1 rt'_lst ref'_lst_lst var_1) ->
		(fun_allocelem s rt ref_lst var_0) ->
		((s_1, ea) == var_0) ->
		((s_2, ea'_lst) == var_1) ->
		fun_allocelems s ([::rt] ++ rt'_lst) ([::ref_lst] ++ ref'_lst_lst) (s_2, ([::ea] ++ ea'_lst)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
Lemma allocelems_is_wf : forall (v_store : store) (var_0_lst : (seq reftype)) (var_1_lst_lst : (seq (seq ref))) (ret_val : (store * (seq elemaddr))) (var_0 : (store * (seq elemaddr))),
	(fun_allocelems v_store var_0_lst var_1_lst_lst var_0) ->
	(wf_store v_store) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
Inductive fun_allocdata : store -> (seq byte) -> (store * dataaddr) -> Prop :=
	| fun_allocdata_case_0 : forall (s : store) (byte_lst : (seq byte)) (di : datainst), 
		(di == {| datainst_BYTES := byte_lst |}) ->
		(wf_datainst {| datainst_BYTES := byte_lst |}) ->
		fun_allocdata s byte_lst ((s <| store_DATAS := ((store_DATAS s) ++ [::di]) |>), (|(store_DATAS s)|)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
Lemma allocdata_is_wf : forall (v_store : store) (var_0_lst : (seq byte)) (ret_val : (store * dataaddr)) (var_0 : (store * dataaddr)),
	(fun_allocdata v_store var_0_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
Inductive fun_allocdatas : store -> (seq (seq byte)) -> (store * (seq dataaddr)) -> Prop :=
	| fun_allocdatas_case_0 : forall (s : store), fun_allocdatas s [:: ] (s, [:: ])
	| fun_allocdatas_case_1 : forall (s : store) (byte_lst : (seq byte)) (byte'_lst_lst : (seq (seq byte))) (da : dataaddr) (s_1 : store) (s_2 : store) (da'_lst : (seq dataaddr)) (var_1 : (store * (seq dataaddr))) (var_0 : (store * dataaddr)), 
		(fun_allocdatas s_1 byte'_lst_lst var_1) ->
		(fun_allocdata s byte_lst var_0) ->
		((s_1, da) == var_0) ->
		((s_2, da'_lst) == var_1) ->
		fun_allocdatas s ([::byte_lst] ++ byte'_lst_lst) (s_2, ([::da] ++ da'_lst)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
Lemma allocdatas_is_wf : forall (v_store : store) (var_0_lst_lst : (seq (seq byte))) (ret_val : (store * (seq dataaddr))) (var_0 : (store * (seq dataaddr))),
	(fun_allocdatas v_store var_0_lst_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0_lst : (seq byte)) => List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst) var_0_lst_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:100.1-100.83 *)
Definition instexport (var_0_lst : (seq funcaddr)) (var_1_lst : (seq globaladdr)) (var_2_lst : (seq tableaddr)) (var_3_lst : (seq memaddr)) (v_export : export) : exportinst :=
	match var_0_lst, var_1_lst, var_2_lst, var_3_lst, v_export return exportinst with
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_FUNC x)) => {| NAME := v_name; ADDR := (externaddr_FUNC (fa_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_GLOBAL x)) => {| NAME := v_name; ADDR := (externaddr_GLOBAL (ga_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_TABLE x)) => {| NAME := v_name; ADDR := (externaddr_TABLE (ta_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_MEM x)) => {| NAME := v_name; ADDR := (externaddr_MEM (ma_lst[| (x :> nat) |])) |}
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:100.6-100.17 *)
Lemma instexport_is_wf : forall (var_0_lst : (seq funcaddr)) (var_1_lst : (seq globaladdr)) (var_2_lst : (seq tableaddr)) (var_3_lst : (seq memaddr)) (v_export : export) (ret_val : exportinst),
	(wf_export v_export) ->
	(ret_val == (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export)) ->
	(wf_exportinst ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
Inductive fun_allocmodule : store -> module -> (seq externaddr) -> (seq val) -> (seq (seq ref)) -> (store * moduleinst) -> Prop :=
	| fun_allocmodule_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (seq externaddr)) (val_lst : (seq val)) (ref_lst_lst : (seq (seq ref))) (s_6 : store) (v_moduleinst : moduleinst) (ft_lst : (seq functype)) (import_lst : (seq import)) (n_func : nat) (func_lst : (seq func)) (n_global : nat) (expr_1_lst : (seq expr)) (globaltype_lst : (seq globaltype)) (n_table : nat) (tabletype_lst : (seq tabletype)) (n_mem : nat) (memtype_lst : (seq memtype)) (n_elem : nat) (elemmode_lst : (seq elemmode)) (expr_2_lst_lst : (seq (seq expr))) (rt_lst : (seq reftype)) (n_data : nat) (byte_lst_lst : (seq (seq byte))) (datamode_lst : (seq datamode)) (start_opt : (option start)) (export_lst : (seq export)) (s_1 : store) (s_2 : store) (s_3 : store) (s_4 : store) (s_5 : store) (fa_ex_lst : (seq funcaddr)) (ga_ex_lst : (seq globaladdr)) (ta_ex_lst : (seq tableaddr)) (ma_ex_lst : (seq memaddr)) (fa_lst : (seq funcaddr)) (ga_lst : (seq globaladdr)) (ta_lst : (seq tableaddr)) (ma_lst : (seq memaddr)) (ea_lst : (seq elemaddr)) (da_lst : (seq dataaddr)) (xi_lst : (seq exportinst)) (var_9 : (store * (seq dataaddr))) (var_8 : (store * (seq elemaddr))) (var_7 : (store * (seq memaddr))) (var_6 : (store * (seq tableaddr))) (var_5 : (store * (seq globaladdr))) (var_4 : (store * (seq funcaddr))) (var_3 : (seq memaddr)) (var_2 : (seq tableaddr)) (var_1 : (seq globaladdr)) (var_0 : (seq funcaddr)), 
		(fun_allocdatas s_5 byte_lst_lst var_9) ->
		(fun_allocelems s_4 rt_lst ref_lst_lst var_8) ->
		(fun_allocmems s_3 memtype_lst var_7) ->
		(fun_alloctables s_2 tabletype_lst var_6) ->
		(fun_allocglobals s_1 globaltype_lst val_lst var_5) ->
		(fun_allocfuncs s v_moduleinst func_lst var_4) ->
		(fun_mems externaddr_lst var_3) ->
		(fun_tables externaddr_lst var_2) ->
		(fun_globals externaddr_lst var_1) ->
		(fun_funcs externaddr_lst var_0) ->
		(v_module == (MODULE (seq.map (fun (ft_1 : functype) => (TYPE ft_1)) ft_lst) import_lst func_lst (list_zipWith (fun (expr_1_1 : expr) (globaltype_195 : globaltype) => (global_GLOBAL globaltype_195 expr_1_1)) expr_1_lst globaltype_lst) (seq.map (fun (tabletype_241 : tabletype) => (table_TABLE tabletype_241)) tabletype_lst) (seq.map (fun (memtype_293 : memtype) => (MEMORY memtype_293)) memtype_lst) (list_map3 (fun (elemmode_397 : elemmode) (expr_2_lst_1 : (seq expr)) (rt_1 : reftype) => (ELEM rt_1 expr_2_lst_1 elemmode_397)) elemmode_lst expr_2_lst_lst rt_lst) (list_zipWith (fun (byte_lst_419 : (seq byte)) (datamode_419 : datamode) => (DATA byte_lst_419 datamode_419)) byte_lst_lst datamode_lst) start_opt export_lst)) ->
		(fa_ex_lst == var_0) ->
		(ga_ex_lst == var_1) ->
		(ta_ex_lst == var_2) ->
		(ma_ex_lst == var_3) ->
		(fa_lst == (seq.mkseq (fun i_func_1 => ((|(store_FUNCS s)|) + i_func_1)%N) n_func)) ->
		(ga_lst == (seq.mkseq (fun i_global_1 => ((|(store_GLOBALS s)|) + i_global_1)%N) n_global)) ->
		(ta_lst == (seq.mkseq (fun i_table_1 => ((|(store_TABLES s)|) + i_table_1)%N) n_table)) ->
		(ma_lst == (seq.mkseq (fun i_mem_1 => ((|(store_MEMS s)|) + i_mem_1)%N) n_mem)) ->
		(ea_lst == (seq.mkseq (fun i_elem_1 => ((|(store_ELEMS s)|) + i_elem_1)%N) n_elem)) ->
		(da_lst == (seq.mkseq (fun i_data_1 => ((|(store_DATAS s)|) + i_data_1)%N) n_data)) ->
		(xi_lst == (seq.map (fun (export_2 : export) => (instexport (fa_ex_lst ++ fa_lst) (ga_ex_lst ++ ga_lst) (ta_ex_lst ++ ta_lst) (ma_ex_lst ++ ma_lst) export_2)) export_lst)) ->
		(v_moduleinst == {| TYPES := ft_lst; FUNCS := (fa_ex_lst ++ fa_lst); GLOBALS := (ga_ex_lst ++ ga_lst); TABLES := (ta_ex_lst ++ ta_lst); MEMS := (ma_ex_lst ++ ma_lst); ELEMS := ea_lst; DATAS := da_lst; EXPORTS := xi_lst |}) ->
		((s_1, fa_lst) == var_4) ->
		((s_2, ga_lst) == var_5) ->
		((s_3, ta_lst) == var_6) ->
		((s_4, ma_lst) == var_7) ->
		((s_5, ea_lst) == var_8) ->
		((s_6, da_lst) == var_9) ->
		(wf_store s_1) ->
		(wf_store s_2) ->
		(wf_store s_3) ->
		(wf_store s_4) ->
		(wf_store s_5) ->
		(wf_module (MODULE (seq.map (fun (ft_3 : functype) => (TYPE ft_3)) ft_lst) import_lst func_lst (list_zipWith (fun (expr_1_2 : expr) (globaltype_198 : globaltype) => (global_GLOBAL globaltype_198 expr_1_2)) expr_1_lst globaltype_lst) (seq.map (fun (tabletype_244 : tabletype) => (table_TABLE tabletype_244)) tabletype_lst) (seq.map (fun (memtype_296 : memtype) => (MEMORY memtype_296)) memtype_lst) (list_map3 (fun (elemmode_399 : elemmode) (expr_2_lst_2 : (seq expr)) (rt_3 : reftype) => (ELEM rt_3 expr_2_lst_2 elemmode_399)) elemmode_lst expr_2_lst_lst rt_lst) (list_zipWith (fun (byte_lst_422 : (seq byte)) (datamode_421 : datamode) => (DATA byte_lst_422 datamode_421)) byte_lst_lst datamode_lst) start_opt export_lst)) ->
		(wf_moduleinst {| TYPES := ft_lst; FUNCS := (fa_ex_lst ++ fa_lst); GLOBALS := (ga_ex_lst ++ ga_lst); TABLES := (ta_ex_lst ++ ta_lst); MEMS := (ma_ex_lst ++ ma_lst); ELEMS := ea_lst; DATAS := da_lst; EXPORTS := xi_lst |}) ->
		fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst (s_6, v_moduleinst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
Lemma allocmodule_is_wf : forall (v_store : store) (v_module : module) (var_0_lst : (seq externaddr)) (var_1_lst : (seq val)) (var_2_lst_lst : (seq (seq ref))) (ret_val : (store * moduleinst)) (var_0 : (store * moduleinst)),
	(fun_allocmodule v_store v_module var_0_lst var_1_lst var_2_lst_lst var_0) ->
	(wf_store v_store) ->
	(wf_module v_module) ->
	List.Forall (fun (var_1 : val) => (wf_val var_1)) var_1_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1) ->
	(wf_moduleinst ret_val.2).
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:154.1-154.33 *)
Definition runelem (v_elem : elem) (v_idx : idx) : (seq instr) :=
	match v_elem, v_idx return (seq instr) with
		| (ELEM v_reftype expr_lst PASSIVE), i => [:: ]
		| (ELEM v_reftype expr_lst DECLARE), i => [::(ELEM_DROP i)]
		| (ELEM v_reftype expr_lst (ACTIVE x instr_lst)), i => 
			let v_n := (|expr_lst|) in 
			(instr_lst ++ [::(CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))); (CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (TABLE_INIT x i); (ELEM_DROP i)])
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:154.6-154.14 *)
Lemma runelem_is_wf : forall (v_elem : elem) (v_idx : idx) (ret_val_lst : (seq instr)),
	(wf_elem v_elem) ->
	(wf_uN 32 v_idx) ->
	(ret_val_lst == (runelem v_elem v_idx)) ->
	List.Forall (fun (ret_val : instr) => (wf_instr ret_val)) ret_val_lst.
Proof. Admitted.

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:161.1-161.47 *)
Definition rundata (v_data : data) (v_idx : idx) : (option (seq instr)) :=
	match v_data, v_idx return (option (seq instr)) with
		| (DATA byte_lst datamode_PASSIVE), i => (Some [:: ])
		| (DATA byte_lst (datamode_ACTIVE (mk_uN 0) instr_lst)), i => 
			let v_n := (|byte_lst|) in 
			(Some (instr_lst ++ [::(CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))); (CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (MEMORY_INIT i); (DATA_DROP i)]))
		| x0, x1 => None
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:161.6-161.14 *)
Lemma rundata_is_wf : forall (v_data : data) (v_idx : idx) (ret_val_lst : (seq instr)),
	(wf_data v_data) ->
	(wf_uN 32 v_idx) ->
	((rundata v_data v_idx) != None) ->
	(ret_val_lst == (!((rundata v_data v_idx)))) ->
	List.Forall (fun (ret_val : instr) => (wf_instr ret_val)) ret_val_lst.
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 *)
Inductive fun_instantiate : store -> module -> (seq externaddr) -> config -> Prop :=
	| fun_instantiate_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (seq externaddr)) (f : frame) (x_opt : (option idx)) (functype_lst : (seq functype)) (expr_G_lst : (seq expr)) (globaltype_lst : (seq globaltype)) (elemmode_lst : (seq elemmode)) (expr_E_lst_lst : (seq (seq expr))) (reftype_lst : (seq reftype)) (moduleinst_init : moduleinst) (f_init : frame) (val_lst : (seq val)) (ref_lst_lst : (seq (seq ref))) (i : nat) (j : nat) (type_lst : (seq type)) (import_lst : (seq import)) (func_lst : (seq func)) (global_lst : (seq global)) (table_lst : (seq table)) (mem_lst : (seq mem)) (elem_lst : (seq elem)) (data_lst : (seq data)) (start_opt : (option start)) (export_lst : (seq export)) (n_F : n) (n_E : n) (n_D : n) (z : state) (s' : store) (v_moduleinst : moduleinst) (instr_E_lst : (seq instr)) (instr_D_lst : (seq instr)) (var_4 : (seq globaladdr)) (var_3 : (seq funcaddr)) (var_2 : (store * moduleinst)) (var_1 : (seq globaladdr)) (var_0 : (seq funcaddr)), 
		(fun_globals externaddr_lst var_4) ->
		(fun_funcs externaddr_lst var_3) ->
		(fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst var_2) ->
		(fun_globals externaddr_lst var_1) ->
		(fun_funcs externaddr_lst var_0) ->
		((MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) == v_module) ->
		(type_lst == (seq.map (fun (functype_49 : functype) => (TYPE functype_49)) functype_lst)) ->
		(global_lst == (list_zipWith (fun (expr_G_1 : expr) (globaltype_200 : globaltype) => (global_GLOBAL globaltype_200 expr_G_1)) expr_G_lst globaltype_lst)) ->
		(elem_lst == (list_map3 (fun (elemmode_404 : elemmode) (expr_E_lst_1 : (seq expr)) (reftype_611 : reftype) => (ELEM reftype_611 expr_E_lst_1 elemmode_404)) elemmode_lst expr_E_lst_lst reftype_lst)) ->
		(start_opt == (option_map (fun (x_1 : idx) => (START x_1)) x_opt)) ->
		(n_F == (|func_lst|)) ->
		(n_E == (|elem_lst|)) ->
		(n_D == (|data_lst|)) ->
		(moduleinst_init == {| TYPES := functype_lst; FUNCS := (var_0 ++ (seq.mkseq (fun i_F_1 => ((|(store_FUNCS s)|) + i_F_1)%N) n_F)); GLOBALS := var_1; TABLES := [:: ]; MEMS := [:: ]; ELEMS := [:: ]; DATAS := [:: ]; EXPORTS := [:: ] |}) ->
		(f_init == {| LOCALS := [:: ]; frame_MODULE := moduleinst_init |}) ->
		(z == (mk_state s f_init)) ->
		((|expr_G_lst|) == (|val_lst|)) ->
		List.Forall2 (fun (expr_G_2 : expr) (val_3 : val) => (Eval_expr z expr_G_2 z [::val_3])) expr_G_lst val_lst ->
		((|expr_E_lst_lst|) == (|ref_lst_lst|)) ->
		List.Forall2 (fun (expr_E_lst_2 : (seq expr)) (ref_lst_3 : (seq ref)) => ((|expr_E_lst_2|) == (|ref_lst_3|))) expr_E_lst_lst ref_lst_lst ->
		List.Forall2 (fun (expr_E_lst_2 : (seq expr)) (ref_lst_3 : (seq ref)) => List.Forall2 (fun (expr_E_2 : expr) (ref_7 : ref) => (Eval_expr z expr_E_2 z [::(val_ref ref_7)])) expr_E_lst_2 ref_lst_3) expr_E_lst_lst ref_lst_lst ->
		((s', v_moduleinst) == var_2) ->
		(f == {| LOCALS := [:: ]; frame_MODULE := v_moduleinst |}) ->
		holds_upto (fun i_71285 => (i_71285 < (|elem_lst|))%N) n_E ->
		(instr_E_lst == (concat_ instr (seq.mkseq (fun i_71285 => (runelem (elem_lst[| i_71285 |]) (mk_uN i_71285))) n_E))) ->
		holds_upto (fun j_17 => ((rundata (data_lst[| j_17 |]) (mk_uN j_17)) != None)) n_D ->
		holds_upto (fun j_17 => (j_17 < (|data_lst|))%N) n_D ->
		(instr_D_lst == (concat_ instr (seq.mkseq (fun j_17 => (!((rundata (data_lst[| j_17 |]) (mk_uN j_17))))) n_D))) ->
		List.Forall (fun (val_5 : val) => (wf_val val_5)) val_lst ->
		(wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ->
		((|expr_G_lst|) == (|globaltype_lst|)) ->
		List.Forall2 (fun (expr_G_3 : expr) (globaltype_202 : globaltype) => (wf_global (global_GLOBAL globaltype_202 expr_G_3))) expr_G_lst globaltype_lst ->
		((|elemmode_lst|) == (|expr_E_lst_lst|)) ->
		((|elemmode_lst|) == (|reftype_lst|)) ->
		List_Forall3 (fun (elemmode_406 : elemmode) (expr_E_lst_3 : (seq expr)) (reftype_613 : reftype) => (wf_elem (ELEM reftype_613 expr_E_lst_3 elemmode_406))) elemmode_lst expr_E_lst_lst reftype_lst ->
		List.Forall (fun (x_2 : idx) => (wf_start (START x_2))) (option_to_list x_opt) ->
		(wf_moduleinst {| TYPES := functype_lst; FUNCS := (var_3 ++ (seq.mkseq (fun i_F_2 => ((|(store_FUNCS s)|) + i_F_2)%N) n_F)); GLOBALS := var_4; TABLES := [:: ]; MEMS := [:: ]; ELEMS := [:: ]; DATAS := [:: ]; EXPORTS := [:: ] |}) ->
		(wf_frame {| LOCALS := [:: ]; frame_MODULE := moduleinst_init |}) ->
		(wf_state (mk_state s f_init)) ->
		(wf_frame {| LOCALS := [:: ]; frame_MODULE := v_moduleinst |}) ->
		holds_upto (fun i_71288 => (wf_uN 32 (mk_uN i_71288))) n_E ->
		holds_upto (fun j_18 => (wf_uN 32 (mk_uN j_18))) n_D ->
		fun_instantiate s v_module externaddr_lst (mk_config (mk_state s' f) ((seq.map (fun (instr_E : instr) => (admininstr_instr instr_E)) instr_E_lst) ++ ((seq.map (fun (instr_D : instr) => (admininstr_instr instr_D)) instr_D_lst) ++ (option_to_list (option_map (fun (x : idx) => (admininstr_CALL x)) x_opt))))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 *)
Lemma instantiate_is_wf : forall (v_store : store) (v_module : module) (var_0_lst : (seq externaddr)) (ret_val : config) (var_0 : config),
	(fun_instantiate v_store v_module var_0_lst var_0) ->
	(wf_store v_store) ->
	(wf_module v_module) ->
	(ret_val == var_0) ->
	(wf_config ret_val).
Proof. Admitted.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
Inductive fun_invoke : store -> funcaddr -> (seq val) -> config -> Prop :=
	| fun_invoke_case_0 : forall (s : store) (fa : nat) (v_n : nat) (val_lst : (seq val)) (f : frame) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(f == {| LOCALS := [:: ]; frame_MODULE := {| TYPES := [:: ]; FUNCS := [:: ]; GLOBALS := [:: ]; TABLES := [:: ]; MEMS := [:: ]; ELEMS := [:: ]; DATAS := [:: ]; EXPORTS := [:: ] |} |}) ->
		(fa < (|(fun_funcinst (mk_state s f))|))%N ->
		((funcinst_TYPE ((fun_funcinst (mk_state s f))[| fa |])) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_frame {| LOCALS := [:: ]; frame_MODULE := {| TYPES := [:: ]; FUNCS := [:: ]; GLOBALS := [:: ]; TABLES := [:: ]; MEMS := [:: ]; ELEMS := [:: ]; DATAS := [:: ]; EXPORTS := [:: ] |} |}) ->
		(wf_state (mk_state s f)) ->
		(v_n == (|val_lst|)) ->
		fun_invoke s fa val_lst (mk_config (mk_state s f) ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(CALL_ADDR fa)])).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
Lemma invoke_is_wf : forall (v_store : store) (v_funcaddr : funcaddr) (var_0_lst : (seq val)) (ret_val : config) (var_0 : config),
	(fun_invoke v_store v_funcaddr var_0_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0 : val) => (wf_val var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_config ret_val).
Proof. Admitted.

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:849.1-849.43 *)
Definition startopt : Type := (seq start).

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:884.1-884.29 *)
Definition code : Type := ((seq local) * expr).

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:915.1-915.33 *)
Definition nopt : Type := (seq u32).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:3.1-3.61 *)
Inductive Context_ok : context -> Prop :=
	| mk_Context_ok : forall (C : context) (ft_lst : (seq functype)) (ft_2_lst : (seq functype)) (gt_lst : (seq globaltype)) (tt_lst : (seq tabletype)) (mt_lst : (seq memtype)) (et_lst : (seq elemtype)) (ok_lst : (seq datatype)) (lct_lst : (seq valtype)) (rt_lst : (seq reftype)) (rt'_opt : (option reftype)), 
		(C == {| context_TYPES := ft_lst; context_FUNCS := ft_2_lst; context_GLOBALS := gt_lst; context_TABLES := tt_lst; context_MEMS := mt_lst; context_ELEMS := et_lst; context_DATAS := ok_lst; context_LOCALS := lct_lst; LABELS := [::(mk_list _ (seq.map (fun (rt : reftype) => (valtype_reftype rt)) rt_lst))]; context_RETURN := (Some (mk_list _ (option_to_list (option_map (fun (rt' : reftype) => (valtype_reftype rt')) rt'_opt)))) |}) ->
		List.Forall (fun (ft : functype) => (Functype_ok ft)) ft_lst ->
		List.Forall (fun (gt : globaltype) => (Globaltype_ok gt)) gt_lst ->
		List.Forall (fun (mt : memtype) => (Memtype_ok mt)) mt_lst ->
		List.Forall (fun (res_tt : tabletype) => (Tabletype_ok res_tt)) tt_lst ->
		List.Forall (fun (ft_2 : functype) => (Functype_ok ft_2)) ft_2_lst ->
		(wf_context C) ->
		(wf_context {| context_TYPES := ft_lst; context_FUNCS := ft_2_lst; context_GLOBALS := gt_lst; context_TABLES := tt_lst; context_MEMS := mt_lst; context_ELEMS := et_lst; context_DATAS := ok_lst; context_LOCALS := lct_lst; LABELS := [::(mk_list _ (seq.map (fun (rt : reftype) => (valtype_reftype rt)) rt_lst))]; context_RETURN := (Some (mk_list _ (option_to_list (option_map (fun (rt' : reftype) => (valtype_reftype rt')) rt'_opt)))) |}) ->
		Context_ok C.

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:129.1-129.84 *)
Inductive Externaddr_ok : store -> externaddr -> externtype -> Prop :=
	| Externaddr_ok__global : forall (s : store) (a : addr) (v_globalinst : globalinst), 
		(a < (|(store_GLOBALS s)|))%N ->
		(((store_GLOBALS s)[| a |]) == v_globalinst) ->
		(wf_store s) ->
		(wf_externtype (GLOBAL (globalinst_TYPE v_globalinst))) ->
		Externaddr_ok s (externaddr_GLOBAL a) (GLOBAL (globalinst_TYPE v_globalinst))
	| Externaddr_ok__mem : forall (s : store) (a : addr) (v_meminst : meminst), 
		(a < (|(store_MEMS s)|))%N ->
		(((store_MEMS s)[| a |]) == v_meminst) ->
		(wf_store s) ->
		(wf_externtype (MEM (meminst_TYPE v_meminst))) ->
		Externaddr_ok s (externaddr_MEM a) (MEM (meminst_TYPE v_meminst))
	| Externaddr_ok__table : forall (s : store) (a : addr) (v_tableinst : tableinst), 
		(a < (|(store_TABLES s)|))%N ->
		(((store_TABLES s)[| a |]) == v_tableinst) ->
		(wf_store s) ->
		(wf_externtype (TABLE (tableinst_TYPE v_tableinst))) ->
		Externaddr_ok s (externaddr_TABLE a) (TABLE (tableinst_TYPE v_tableinst))
	| Externaddr_ok__func : forall (s : store) (a : addr) (v_funcinst : funcinst), 
		(a < (|(store_FUNCS s)|))%N ->
		(((store_FUNCS s)[| a |]) == v_funcinst) ->
		(wf_store s) ->
		(wf_externtype (FUNC (funcinst_TYPE v_funcinst))) ->
		Externaddr_ok s (externaddr_FUNC a) (FUNC (funcinst_TYPE v_funcinst))
	| Externaddr_ok__sub : forall (s : store) (v_externaddr : externaddr) (xt : externtype) (xt' : externtype), 
		(Externaddr_ok s v_externaddr xt') ->
		(Externtype_sub xt' xt) ->
		(wf_store s) ->
		(wf_externtype xt) ->
		(wf_externtype xt') ->
		Externaddr_ok s v_externaddr xt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:27.1-27.40 *)
Inductive Ref_ok : store -> ref -> reftype -> Prop :=
	| null : forall (s : store) (rt : reftype), 
		(wf_store s) ->
		Ref_ok s (ref_REF_NULL rt) rt
	| Ref_ok__func : forall (s : store) (a : addr) (ext : functype), 
		(Externaddr_ok s (externaddr_FUNC a) (FUNC ext)) ->
		(wf_store s) ->
		(wf_externtype (FUNC ext)) ->
		Ref_ok s (REF_FUNC_ADDR a) FUNCREF
	| extern : forall (s : store) (a : addr), 
		(wf_store s) ->
		Ref_ok s (REF_HOST_ADDR a) EXTERNREF.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:41.1-41.40 *)
Inductive Val_ok : store -> val -> valtype -> Prop :=
	| Val_ok__numtype : forall (s : store) (nt : numtype) (c_t : num_), 
		(wf_store s) ->
		(wf_val (val_CONST nt c_t)) ->
		Val_ok s (val_CONST nt c_t) (valtype_numtype nt)
	| Val_ok__vectype : forall (s : store) (vt : vectype) (c_t : vec_), 
		(wf_store s) ->
		(wf_val (val_VCONST vt c_t)) ->
		Val_ok s (val_VCONST vt c_t) (valtype_vectype vt)
	| Val_ok__reftype : forall (s : store) (r : ref) (rt : reftype), 
		(Ref_ok s r rt) ->
		(wf_store s) ->
		Val_ok s (val_ref r) (valtype_reftype rt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:55.1-55.47 *)
Inductive Result_ok : store -> result -> (seq valtype) -> Prop :=
	| Result_ok__result : forall (s : store) (v_lst : (seq val)) (t_lst : (seq valtype)), 
		((|t_lst|) == (|v_lst|)) ->
		List.Forall2 (fun (t : valtype) (v : val) => (Val_ok s v t)) t_lst v_lst ->
		(wf_store s) ->
		(wf_result (_VALS v_lst)) ->
		Result_ok s (_VALS v_lst) t_lst
	| trap : forall (s : store) (t_lst : (seq valtype)), 
		(wf_store s) ->
		(wf_result TRAP) ->
		Result_ok s TRAP t_lst.

(* Type Alias Definition at: ../specification/wasm-2.0/B-soundness.spectec:66.1-66.31 *)
Definition adminexpr : Type := (seq admininstr).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:158.1-158.51 *)
Inductive Datainst_ok : store -> datainst -> datatype -> Prop :=
	| mk_Datainst_ok : forall (s : store) (b_lst : (seq byte)), 
		(wf_store s) ->
		(wf_datainst {| datainst_BYTES := b_lst |}) ->
		Datainst_ok s {| datainst_BYTES := b_lst |} OK.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:159.1-159.51 *)
Inductive Eleminst_ok : store -> eleminst -> elemtype -> Prop :=
	| mk_Eleminst_ok : forall (s : store) (rt : reftype) (ref_lst : (seq ref)), 
		List.Forall (fun (v_ref : ref) => (Ref_ok s v_ref rt)) ref_lst ->
		(wf_store s) ->
		Eleminst_ok s {| eleminst_TYPE := rt; eleminst_REFS := ref_lst |} rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:160.1-160.49 *)
Inductive Exportinst_ok : store -> exportinst -> Prop :=
	| mk_Exportinst_ok : forall (s : store) (nm : name) (xa : externaddr) (xt : externtype), 
		(Externaddr_ok s xa xt) ->
		(wf_store s) ->
		(wf_externtype xt) ->
		(wf_exportinst {| NAME := nm; ADDR := xa |}) ->
		Exportinst_ok s {| NAME := nm; ADDR := xa |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:198.1-198.54 *)
Inductive Moduleinst_ok : store -> moduleinst -> context -> Prop :=
	| mk_Moduleinst_ok : forall (s : store) (functype_lst : (seq functype)) (funcaddr_lst : (seq funcaddr)) (globaladdr_lst : (seq globaladdr)) (tableaddr_lst : (seq tableaddr)) (memaddr_lst : (seq memaddr)) (elemaddr_lst : (seq elemaddr)) (dataaddr_lst : (seq dataaddr)) (exportinst_lst : (seq exportinst)) (functype_F_lst : (seq functype)) (globaltype_lst : (seq globaltype)) (tabletype_lst : (seq tabletype)) (memtype_lst : (seq memtype)) (elemtype_lst : (seq elemtype)) (datatype_lst : (seq datatype)), 
		List.Forall (fun (v_functype : functype) => (Functype_ok v_functype)) functype_lst ->
		((|globaladdr_lst|) == (|globaltype_lst|)) ->
		List.Forall2 (fun (v_globaladdr : globaladdr) (v_globaltype : globaltype) => (Externaddr_ok s (externaddr_GLOBAL v_globaladdr) (GLOBAL v_globaltype))) globaladdr_lst globaltype_lst ->
		((|funcaddr_lst|) == (|functype_F_lst|)) ->
		List.Forall2 (fun (v_funcaddr : funcaddr) (functype_F : functype) => (Externaddr_ok s (externaddr_FUNC v_funcaddr) (FUNC functype_F))) funcaddr_lst functype_F_lst ->
		((|memaddr_lst|) == (|memtype_lst|)) ->
		List.Forall2 (fun (v_memaddr : memaddr) (v_memtype : memtype) => (Externaddr_ok s (externaddr_MEM v_memaddr) (MEM v_memtype))) memaddr_lst memtype_lst ->
		((|tableaddr_lst|) == (|tabletype_lst|)) ->
		List.Forall2 (fun (v_tableaddr : tableaddr) (v_tabletype : tabletype) => (Externaddr_ok s (externaddr_TABLE v_tableaddr) (TABLE v_tabletype))) tableaddr_lst tabletype_lst ->
		List.Forall (fun (v_exportinst : exportinst) => (Exportinst_ok s v_exportinst)) exportinst_lst ->
		((|dataaddr_lst|) == (|datatype_lst|)) ->
		List.Forall (fun (v_dataaddr : nat) => (v_dataaddr < (|(store_DATAS s)|))%N) dataaddr_lst ->
		List.Forall2 (fun (v_dataaddr : nat) (v_datatype : datatype) => (Datainst_ok s ((store_DATAS s)[| v_dataaddr |]) v_datatype)) dataaddr_lst datatype_lst ->
		((|elemaddr_lst|) == (|elemtype_lst|)) ->
		List.Forall (fun (v_elemaddr : nat) => (v_elemaddr < (|(store_ELEMS s)|))%N) elemaddr_lst ->
		List.Forall2 (fun (v_elemaddr : nat) (v_elemtype : elemtype) => (Eleminst_ok s ((store_ELEMS s)[| v_elemaddr |]) v_elemtype)) elemaddr_lst elemtype_lst ->
		(disjoint_ name (seq.map (fun (v_exportinst : exportinst) => (NAME v_exportinst)) exportinst_lst)) ->
		((|((seq.map (fun (v_globaladdr : globaladdr) => (externaddr_GLOBAL v_globaladdr)) globaladdr_lst) ++ ((seq.map (fun (v_memaddr : memaddr) => (externaddr_MEM v_memaddr)) memaddr_lst) ++ ((seq.map (fun (v_tableaddr : tableaddr) => (externaddr_TABLE v_tableaddr)) tableaddr_lst) ++ (seq.map (fun (v_funcaddr : funcaddr) => (externaddr_FUNC v_funcaddr)) funcaddr_lst))))|) > 0)%N ->
		List.Forall (fun (v_exportinst : exportinst) => ((ADDR v_exportinst) \in ((seq.map (fun (v_globaladdr : globaladdr) => (externaddr_GLOBAL v_globaladdr)) globaladdr_lst) ++ ((seq.map (fun (v_memaddr : memaddr) => (externaddr_MEM v_memaddr)) memaddr_lst) ++ ((seq.map (fun (v_tableaddr : tableaddr) => (externaddr_TABLE v_tableaddr)) tableaddr_lst) ++ (seq.map (fun (v_funcaddr : funcaddr) => (externaddr_FUNC v_funcaddr)) funcaddr_lst)))))) exportinst_lst ->
		(wf_store s) ->
		(wf_moduleinst {| TYPES := functype_lst; FUNCS := funcaddr_lst; GLOBALS := globaladdr_lst; TABLES := tableaddr_lst; MEMS := memaddr_lst; ELEMS := elemaddr_lst; DATAS := dataaddr_lst; EXPORTS := exportinst_lst |}) ->
		(wf_context {| context_TYPES := functype_lst; context_FUNCS := functype_F_lst; context_GLOBALS := globaltype_lst; context_TABLES := tabletype_lst; context_MEMS := memtype_lst; context_ELEMS := elemtype_lst; context_DATAS := datatype_lst; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		List.Forall (fun (v_globaltype : globaltype) => (wf_externtype (GLOBAL v_globaltype))) globaltype_lst ->
		List.Forall (fun (functype_F : functype) => (wf_externtype (FUNC functype_F))) functype_F_lst ->
		List.Forall (fun (v_memtype : memtype) => (wf_externtype (MEM v_memtype))) memtype_lst ->
		List.Forall (fun (v_tabletype : tabletype) => (wf_externtype (TABLE v_tabletype))) tabletype_lst ->
		Moduleinst_ok s {| TYPES := functype_lst; FUNCS := funcaddr_lst; GLOBALS := globaladdr_lst; TABLES := tableaddr_lst; MEMS := memaddr_lst; ELEMS := elemaddr_lst; DATAS := dataaddr_lst; EXPORTS := exportinst_lst |} {| context_TYPES := functype_lst; context_FUNCS := functype_F_lst; context_GLOBALS := globaltype_lst; context_TABLES := tabletype_lst; context_MEMS := memtype_lst; context_ELEMS := elemtype_lst; context_DATAS := datatype_lst; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:292.1-292.44 *)
Inductive Frame_ok : store -> frame -> context -> Prop :=
	| mk_Frame_ok : forall (s : store) (val_lst : (seq val)) (v_moduleinst : moduleinst) (C : context) (t_lst : (seq valtype)), 
		(Moduleinst_ok s v_moduleinst C) ->
		((|t_lst|) == (|val_lst|)) ->
		List.Forall2 (fun (t : valtype) (v_val : val) => (Val_ok s v_val t)) t_lst val_lst ->
		(wf_store s) ->
		(wf_context C) ->
		(wf_frame {| LOCALS := val_lst; frame_MODULE := v_moduleinst |}) ->
		(wf_context {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := t_lst; LABELS := [:: ]; context_RETURN := None |}) ->
		Frame_ok s {| LOCALS := val_lst; frame_MODULE := v_moduleinst |} (C @@ {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := t_lst; LABELS := [:: ]; context_RETURN := None |}).

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:68.1-73.36 *)
Inductive Instr_ok2 : store -> context -> admininstr -> functype -> Prop :=
	| plain : forall (s : store) (C : context) (v_instr : instr) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instr_ok C v_instr (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_store s) ->
		(wf_context C) ->
		(wf_instr v_instr) ->
		Instr_ok2 s C (admininstr_instr v_instr) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| label : forall (s : store) (C : context) (v_n : n) (instr'_lst : (seq instr)) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)) (t'_lst : (seq valtype)), 
		(Instrs_ok2 s C (seq.map (fun (instr' : instr) => (admininstr_instr instr')) instr'_lst) (mk_functype (mk_list _ t'_lst) (mk_list _ t_lst))) ->
		(Instrs_ok2 s ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t'_lst)]; context_RETURN := None |} @@ C) admininstr_lst (mk_functype (mk_list _ [:: ]) (mk_list _ t_lst))) ->
		(wf_store s) ->
		(wf_context C) ->
		(wf_admininstr (LABEL_ v_n instr'_lst admininstr_lst)) ->
		(wf_context {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t'_lst)]; context_RETURN := None |}) ->
		(v_n == (|t'_lst|)) ->
		Instr_ok2 s C (LABEL_ v_n instr'_lst admininstr_lst) (mk_functype (mk_list _ [:: ]) (mk_list _ t_lst))
	| Instr_ok2__frame : forall (s : store) (C : context) (v_n : n) (f : frame) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)) (C' : context), 
		(Frame_ok s f C') ->
		(Expr_ok2 s C' admininstr_lst (mk_list _ t_lst)) ->
		(wf_store s) ->
		(wf_context C) ->
		(wf_context C') ->
		(wf_admininstr (FRAME_ v_n f admininstr_lst)) ->
		(v_n == (|t_lst|)) ->
		Instr_ok2 s C (FRAME_ v_n f admininstr_lst) (mk_functype (mk_list _ [:: ]) (mk_list _ t_lst))
	| Instr_ok2__call_addr : forall (s : store) (C : context) (v_funcaddr : funcaddr) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Externaddr_ok s (externaddr_FUNC v_funcaddr) (FUNC (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)))) ->
		(wf_store s) ->
		(wf_context C) ->
		(wf_admininstr (CALL_ADDR v_funcaddr)) ->
		(wf_externtype (FUNC (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)))) ->
		Instr_ok2 s C (CALL_ADDR v_funcaddr) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| Instr_ok2__ref : forall (s : store) (C : context) (v_ref : ref) (rt : reftype), 
		(Ref_ok s v_ref rt) ->
		(wf_store s) ->
		(wf_context C) ->
		Instr_ok2 s C (admininstr_ref v_ref) (mk_functype (mk_list _ [:: ]) (mk_list _ [::(valtype_reftype rt)]))
	| Instr_ok2__trap : forall (s : store) (C : context) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(wf_store s) ->
		(wf_context C) ->
		(wf_admininstr admininstr_TRAP) ->
		Instr_ok2 s C admininstr_TRAP (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))

with

Instrs_ok2 : store -> context -> (seq admininstr) -> functype -> Prop :=
	| Instrs_ok2__empty : forall (s : store) (C : context), 
		(wf_store s) ->
		(wf_context C) ->
		Instrs_ok2 s C [:: ] (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| Instrs_ok2__instr : forall (s : store) (C : context) (v_admininstr : admininstr) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instr_ok2 s C v_admininstr (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_store s) ->
		(wf_context C) ->
		(wf_admininstr v_admininstr) ->
		Instrs_ok2 s C [::v_admininstr] (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| Instrs_ok2__seq : forall (s : store) (C : context) (admininstr_1_lst : (seq admininstr)) (admininstr_2_lst : (seq admininstr)) (t_1_lst : (seq valtype)) (t_3_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok2 s C admininstr_1_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok2 s C admininstr_2_lst (mk_functype (mk_list _ t_2_lst) (mk_list _ t_3_lst))) ->
		(wf_store s) ->
		(wf_context C) ->
		List.Forall (fun (admininstr_1 : admininstr) => (wf_admininstr admininstr_1)) admininstr_1_lst ->
		List.Forall (fun (admininstr_2 : admininstr) => (wf_admininstr admininstr_2)) admininstr_2_lst ->
		Instrs_ok2 s C (admininstr_1_lst ++ admininstr_2_lst) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_3_lst))
	| Instrs_ok2__sub : forall (s : store) (C : context) (admininstr_lst : (seq admininstr)) (t'_1_lst : (seq valtype)) (t'_2_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok2 s C admininstr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Resulttype_sub (mk_list _ t'_1_lst) (mk_list _ t_1_lst)) ->
		(Resulttype_sub (mk_list _ t_2_lst) (mk_list _ t'_2_lst)) ->
		(wf_store s) ->
		(wf_context C) ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		Instrs_ok2 s C admininstr_lst (mk_functype (mk_list _ t'_1_lst) (mk_list _ t'_2_lst))
	| Instrs_ok2__frame : forall (s : store) (C : context) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok2 s C admininstr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(wf_store s) ->
		(wf_context C) ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		Instrs_ok2 s C admininstr_lst (mk_functype (mk_list _ (t_lst ++ t_1_lst)) (mk_list _ (t_lst ++ t_2_lst)))

with

Expr_ok2 : store -> context -> adminexpr -> resulttype -> Prop :=
	| mk_Expr_ok2 : forall (s : store) (C : context) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)), 
		(Instrs_ok2 s C admininstr_lst (mk_functype (mk_list _ [:: ]) (mk_list _ t_lst))) ->
		(wf_store s) ->
		(wf_context C) ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		Expr_ok2 s C admininstr_lst (mk_list _ t_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:154.1-154.57 *)
Inductive Globalinst_ok : store -> globalinst -> globaltype -> Prop :=
	| mk_Globalinst_ok : forall (s : store) (v_mut : mut) (t : valtype) (v_val : val), 
		(Globaltype_ok (mk_globaltype v_mut t)) ->
		(Val_ok s v_val t) ->
		(wf_store s) ->
		(wf_globalinst {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := v_val |}) ->
		Globalinst_ok s {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := v_val |} (mk_globaltype v_mut t).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:155.1-155.48 *)
Inductive Meminst_ok : store -> meminst -> memtype -> Prop :=
	| mk_Meminst_ok : forall (s : store) (v_n : n) (m_opt : (option m)) (b_lst : (seq byte)), 
		(Memtype_ok (PAGE (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)))) ->
		((|b_lst|) == (v_n * (64 * (Ki ))%N)%N) ->
		(wf_store s) ->
		(wf_meminst {| meminst_TYPE := (PAGE (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))); BYTES := b_lst |}) ->
		(wf_memtype (PAGE (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)))) ->
		Meminst_ok s {| meminst_TYPE := (PAGE (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))); BYTES := b_lst |} (PAGE (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:156.1-156.54 *)
Inductive Tableinst_ok : store -> tableinst -> tabletype -> Prop :=
	| mk_Tableinst_ok : forall (s : store) (v_n : n) (m_opt : (option m)) (rt : reftype) (ref_lst : (seq ref)), 
		(Tabletype_ok (mk_tabletype (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt)) ->
		List.Forall (fun (v_ref : ref) => (Ref_ok s v_ref rt)) ref_lst ->
		((|ref_lst|) == v_n) ->
		(wf_store s) ->
		(wf_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt); REFS := ref_lst |}) ->
		(wf_tabletype (mk_tabletype (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt)) ->
		Tableinst_ok s {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt); REFS := ref_lst |} (mk_tabletype (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:157.1-157.51 *)
Inductive Funcinst_ok : store -> funcinst -> functype -> Prop :=
	| mk_Funcinst_ok : forall (s : store) (ft : functype) (v_moduleinst : moduleinst) (v_func : func) (C : context), 
		(Functype_ok ft) ->
		(Moduleinst_ok s v_moduleinst C) ->
		(Func_ok C v_func ft) ->
		(wf_store s) ->
		(wf_context C) ->
		(wf_funcinst {| funcinst_TYPE := ft; funcinst_MODULE := v_moduleinst; CODE := v_func |}) ->
		Funcinst_ok s {| funcinst_TYPE := ft; funcinst_MODULE := v_moduleinst; CODE := v_func |} ft.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:232.1-232.33 *)
Inductive Store_ok : store -> Prop :=
	| mk_Store_ok : forall (s : store) (globalinst_lst : (seq globalinst)) (globaltype_lst : (seq globaltype)) (meminst_lst : (seq meminst)) (memtype_lst : (seq memtype)) (tableinst_lst : (seq tableinst)) (tabletype_lst : (seq tabletype)) (funcinst_lst : (seq funcinst)) (functype_lst : (seq functype)) (datainst_lst : (seq datainst)) (datatype_lst : (seq datatype)) (eleminst_lst : (seq eleminst)) (elemtype_lst : (seq elemtype)), 
		((|globalinst_lst|) == (|globaltype_lst|)) ->
		List.Forall2 (fun (v_globalinst : globalinst) (v_globaltype : globaltype) => (Globalinst_ok s v_globalinst v_globaltype)) globalinst_lst globaltype_lst ->
		((|meminst_lst|) == (|memtype_lst|)) ->
		List.Forall2 (fun (v_meminst : meminst) (v_memtype : memtype) => (Meminst_ok s v_meminst v_memtype)) meminst_lst memtype_lst ->
		((|tableinst_lst|) == (|tabletype_lst|)) ->
		List.Forall2 (fun (v_tableinst : tableinst) (v_tabletype : tabletype) => (Tableinst_ok s v_tableinst v_tabletype)) tableinst_lst tabletype_lst ->
		((|funcinst_lst|) == (|functype_lst|)) ->
		List.Forall2 (fun (v_funcinst : funcinst) (v_functype : functype) => (Funcinst_ok s v_funcinst v_functype)) funcinst_lst functype_lst ->
		((|datainst_lst|) == (|datatype_lst|)) ->
		List.Forall2 (fun (v_datainst : datainst) (v_datatype : datatype) => (Datainst_ok s v_datainst v_datatype)) datainst_lst datatype_lst ->
		((|eleminst_lst|) == (|elemtype_lst|)) ->
		List.Forall2 (fun (v_eleminst : eleminst) (v_elemtype : elemtype) => (Eleminst_ok s v_eleminst v_elemtype)) eleminst_lst elemtype_lst ->
		(s == {| store_FUNCS := funcinst_lst; store_GLOBALS := globalinst_lst; store_TABLES := tableinst_lst; store_MEMS := meminst_lst; store_ELEMS := eleminst_lst; store_DATAS := datainst_lst |}) ->
		(wf_store s) ->
		List.Forall (fun (v_memtype : memtype) => (wf_memtype v_memtype)) memtype_lst ->
		List.Forall (fun (v_tabletype : tabletype) => (wf_tabletype v_tabletype)) tabletype_lst ->
		(wf_store {| store_FUNCS := funcinst_lst; store_GLOBALS := globalinst_lst; store_TABLES := tableinst_lst; store_MEMS := meminst_lst; store_ELEMS := eleminst_lst; store_DATAS := datainst_lst |}) ->
		Store_ok s.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:248.1-248.54 *)
Inductive Extend_globalinst : globalinst -> globalinst -> Prop :=
	| mk_Extend_globalinst : forall (v_mut : mut) (t : valtype) (v_val : val) (val' : val), 
		((v_mut == (Some MUT)) || (v_val == val')) ->
		(wf_globalinst {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := v_val |}) ->
		(wf_globalinst {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := val' |}) ->
		Extend_globalinst {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := v_val |} {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := val' |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:249.1-249.45 *)
Inductive Extend_meminst : meminst -> meminst -> Prop :=
	| mk_Extend_meminst : forall (v_n : n) (m_opt : (option m)) (b_lst : (seq byte)) (n' : n) (b'_lst : (seq byte)), 
		(v_n <= n')%N ->
		((|b_lst|) <= (|b'_lst|))%N ->
		(wf_meminst {| meminst_TYPE := (PAGE (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))); BYTES := b_lst |}) ->
		(wf_meminst {| meminst_TYPE := (PAGE (mk_limits (mk_uN n') (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))); BYTES := b'_lst |}) ->
		Extend_meminst {| meminst_TYPE := (PAGE (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))); BYTES := b_lst |} {| meminst_TYPE := (PAGE (mk_limits (mk_uN n') (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))); BYTES := b'_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:250.1-250.51 *)
Inductive Extend_tableinst : tableinst -> tableinst -> Prop :=
	| mk_Extend_tableinst : forall (v_n : n) (m_opt : (option m)) (rt : reftype) (ref_lst : (seq ref)) (n' : n) (ref'_lst : (seq ref)), 
		(v_n <= n')%N ->
		((|ref_lst|) <= (|ref'_lst|))%N ->
		(wf_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt); REFS := ref_lst |}) ->
		(wf_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN n') (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt); REFS := ref'_lst |}) ->
		Extend_tableinst {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt); REFS := ref_lst |} {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN n') (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) rt); REFS := ref'_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:251.1-251.48 *)
Inductive Extend_funcinst : funcinst -> funcinst -> Prop :=
	| mk_Extend_funcinst : forall (ft : functype) (mm : moduleinst) (fc : func), 
		(wf_funcinst {| funcinst_TYPE := ft; funcinst_MODULE := mm; CODE := fc |}) ->
		Extend_funcinst {| funcinst_TYPE := ft; funcinst_MODULE := mm; CODE := fc |} {| funcinst_TYPE := ft; funcinst_MODULE := mm; CODE := fc |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:252.1-252.48 *)
Inductive Extend_datainst : datainst -> datainst -> Prop :=
	| mk_Extend_datainst : forall (b_lst : (seq byte)) (b'_lst : (seq byte)), 
		((b_lst == b'_lst) || (b'_lst == [:: ])) ->
		(wf_datainst {| datainst_BYTES := b_lst |}) ->
		(wf_datainst {| datainst_BYTES := b'_lst |}) ->
		Extend_datainst {| datainst_BYTES := b_lst |} {| datainst_BYTES := b'_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:253.1-253.48 *)
Inductive Extend_eleminst : eleminst -> eleminst -> Prop :=
	| mk_Extend_eleminst : forall (rt : reftype) (ref_lst : (seq ref)) (ref'_lst : (seq ref)), 
		((ref_lst == ref'_lst) || (ref'_lst == [:: ])) ->
		Extend_eleminst {| eleminst_TYPE := rt; eleminst_REFS := ref_lst |} {| eleminst_TYPE := rt; eleminst_REFS := ref'_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:254.1-254.39 *)
Inductive Extend_store : store -> store -> Prop :=
	| mk_Extend_store : forall (s : store) (s' : store), 
		holds_upto (fun a => (a < (|(store_GLOBALS s)|))%N) (|(store_GLOBALS s)|) ->
		holds_upto (fun a => (a < (|(store_GLOBALS s')|))%N) (|(store_GLOBALS s)|) ->
		holds_upto (fun a => (Extend_globalinst ((store_GLOBALS s)[| a |]) ((store_GLOBALS s')[| a |]))) (|(store_GLOBALS s)|) ->
		holds_upto (fun a => (a < (|(store_MEMS s)|))%N) (|(store_MEMS s)|) ->
		holds_upto (fun a => (a < (|(store_MEMS s')|))%N) (|(store_MEMS s)|) ->
		holds_upto (fun a => (Extend_meminst ((store_MEMS s)[| a |]) ((store_MEMS s')[| a |]))) (|(store_MEMS s)|) ->
		holds_upto (fun a => (a < (|(store_TABLES s)|))%N) (|(store_TABLES s)|) ->
		holds_upto (fun a => (a < (|(store_TABLES s')|))%N) (|(store_TABLES s)|) ->
		holds_upto (fun a => (Extend_tableinst ((store_TABLES s)[| a |]) ((store_TABLES s')[| a |]))) (|(store_TABLES s)|) ->
		holds_upto (fun a => (a < (|(store_FUNCS s)|))%N) (|(store_FUNCS s)|) ->
		holds_upto (fun a => (a < (|(store_FUNCS s')|))%N) (|(store_FUNCS s)|) ->
		holds_upto (fun a => (Extend_funcinst ((store_FUNCS s)[| a |]) ((store_FUNCS s')[| a |]))) (|(store_FUNCS s)|) ->
		holds_upto (fun a => (a < (|(store_DATAS s)|))%N) (|(store_DATAS s)|) ->
		holds_upto (fun a => (a < (|(store_DATAS s')|))%N) (|(store_DATAS s)|) ->
		holds_upto (fun a => (Extend_datainst ((store_DATAS s)[| a |]) ((store_DATAS s')[| a |]))) (|(store_DATAS s)|) ->
		holds_upto (fun a => (a < (|(store_ELEMS s)|))%N) (|(store_ELEMS s)|) ->
		holds_upto (fun a => (a < (|(store_ELEMS s')|))%N) (|(store_ELEMS s)|) ->
		holds_upto (fun a => (Extend_eleminst ((store_ELEMS s)[| a |]) ((store_ELEMS s')[| a |]))) (|(store_ELEMS s)|) ->
		(wf_store s) ->
		(wf_store s') ->
		Extend_store s s'.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:293.1-293.38 *)
Inductive State_ok : state -> context -> Prop :=
	| mk_State_ok : forall (s : store) (f : frame) (C : context), 
		(Store_ok s) ->
		(Frame_ok s f C) ->
		(wf_context C) ->
		(wf_state (mk_state s f)) ->
		State_ok (mk_state s f) C.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:294.1-294.43 *)
Inductive Config_ok : config -> resulttype -> Prop :=
	| mk_Config_ok : forall (s : store) (f : frame) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)) (C : context), 
		(State_ok (mk_state s f) C) ->
		(Expr_ok2 s C admininstr_lst (mk_list _ t_lst)) ->
		(wf_context C) ->
		(wf_config (mk_config (mk_state s f) admininstr_lst)) ->
		(wf_state (mk_state s f)) ->
		Config_ok (mk_config (mk_state s f) admininstr_lst) (mk_list _ t_lst).

(* Mutual Recursion at: ../specification/wasm-2.0/A-binary.spectec:20.1-22.82 *)
(* Mutual Recursion at: ../specification/wasm-2.0/A-binary.spectec:24.1-27.82 *)
(* Mutual Recursion at: ../specification/wasm-2.0/A-binary.spectec:742.1-752.59 *)
