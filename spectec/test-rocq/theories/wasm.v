(* Imported Code *)
From Stdlib Require Import String List Unicode.Utf8 Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
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

Class Append (α: Type) := _append : α -> α -> α.

Infix "@@" := _append (right associativity, at level 60) : wasm_scope.

Global Instance Append_List_ {α: Type}: Append (seq α) := { _append l1 l2 := seq.cat l1 l2 }.

Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.

Global Instance Append_nat : Append (nat) := { _append n1 n2 := n1 + n2}.

Global Instance Inh_unit : Inhabited unit := { default_val := tt }.

Global Instance Inh_nat : Inhabited nat := { default_val := O }.

Global Instance Inh_list {T: Type} : Inhabited (seq T) := { default_val := nil }.

Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.

Global Instance Inh_Z : Inhabited Z := { default_val := Z0 }.

Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.

Global Instance Inh_type : Inhabited Type := { default_val := nat }.

Definition option_to_list {T: Type} (arg : option T) : seq T :=
	match arg with
		| None => nil
		| Some a => a :: nil
	end.

Coercion option_to_list: option >-> seq.

Coercion Z.to_nat: Z >-> nat.

Coercion Z.of_nat: nat >-> Z.

Coercion ratz: int >-> rat.

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
Inductive MUT : Type :=
	| MUT_MUT : MUT.

Global Instance Inhabited__MUT : Inhabited (MUT) := { default_val := MUT_MUT }.

Definition MUT_eq_dec : forall (v1 v2 : MUT),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition MUT_eqb (v1 v2 : MUT) : bool :=
	is_left(MUT_eq_dec v1 v2).
Definition eqMUTP : Equality.axiom (MUT_eqb) :=
	eq_dec_Equality_axiom (MUT) (MUT_eq_dec).

HB.instance Definition _ := hasDecEq.Build (MUT) (eqMUTP).
Hint Resolve MUT_eq_dec : eq_dec_db.

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
		| i, j => (if (i <= j) then i else j)
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:25.1-25.21 *)
Inductive fun_sum : (seq nat) -> nat -> Prop :=
	| fun_sum_case_0 : fun_sum [:: ] 0
	| fun_sum_case_1 : forall (v_n : nat) (n'_lst : (seq n)) (var_0 : nat), 
		(fun_sum n'_lst var_0) ->
		fun_sum ([::v_n] ++ n'_lst) (v_n + var_0).

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:32.1-32.58 *)
Definition opt_ (X : eqType) (var_0 : (seq X)) : (option (option X)) :=
	match X, var_0 return (option (option X)) with
		| X, [:: ] => (Some None)
		| X, [::w] => (Some (Some w))
		| X, x1 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:36.1-36.45 *)
Definition list_ (X : eqType) (var_0 : (option X)) : (seq X) :=
	match X, var_0 return (seq X) with
		| X, None => [:: ]
		| X, (Some w) => [::w]
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:40.1-40.86 *)
Fixpoint concat_ (X : eqType) (var_0 : (seq (seq X))) : (seq X) :=
	match X, var_0 return (seq X) with
		| X, [:: ] => [:: ]
		| X, (w_lst :: w'_lst_lst) => (w_lst ++ (concat_ X w'_lst_lst))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:44.1-44.39 *)
Axiom inv_concat_ : forall (X : eqType) (var_0 : (seq X)), (seq (seq X)).

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.46 *)
Fixpoint setproduct2_ (X : eqType) (X_0 : X) (var_0 : (seq (seq X))) : (seq (seq X)) :=
	match X, X_0, var_0 return (seq (seq X)) with
		| X, w_1, [:: ] => [:: ]
		| X, w_1, (w'_lst :: w_lst_lst) => ([::([::w_1] ++ w'_lst)] ++ (setproduct2_ X w_1 w_lst_lst))
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.47 *)
Fixpoint setproduct1_ (X : eqType) (var_0 : (seq X)) (var_1 : (seq (seq X))) : (seq (seq X)) :=
	match X, var_0, var_1 return (seq (seq X)) with
		| X, [:: ], w_lst_lst => [:: ]
		| X, (w_1 :: w'_lst), w_lst_lst => ((setproduct2_ X w_1 w_lst_lst) ++ (setproduct1_ X w'_lst w_lst_lst))
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:49.1-49.84 *)
Fixpoint setproduct_ (X : eqType) (var_0 : (seq (seq X))) : (seq (seq X)) :=
	match X, var_0 return (seq (seq X)) with
		| X, [:: ] => [::[:: ]]
		| X, (w_1_lst :: w_lst_lst) => (setproduct1_ X w_1_lst (setproduct_ X w_lst_lst))
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
Definition proj_list_0 (X : eqType) (x : (res_list X)) : (seq X) :=
	match X, x return (seq X) with
		| X, (mk_list v_X_list_0) => (v_X_list_0)
	end.

Global Instance proj_list_0_coercion (X : eqType) : Coercion (res_list X) (seq X) := { coerce := proj_list_0 X }.

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
Definition proj_byte_0 (x : byte) : nat :=
	match x return nat with
		| (mk_byte v_num_0) => (v_num_0)
	end.

Global Instance proj_byte_0_coercion : Coercion byte nat := { coerce := proj_byte_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.8-16.12 *)
Inductive wf_byte : byte -> Prop :=
	| byte_case_0 : forall (i : nat), 
		((i >= 0) && (i <= 255)) ->
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
Definition proj_uN_0 (x : uN) : nat :=
	match x return nat with
		| (mk_uN v_num_0) => (v_num_0)
	end.

Global Instance proj_uN_0_coercion : Coercion uN nat := { coerce := proj_uN_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.8-18.11 *)
Inductive wf_uN : res_N -> uN -> Prop :=
	| uN_case_0 : forall (v_N : res_N) (i : nat), 
		((i >= 0) && (i <= ((((2 ^ v_N) : nat) - (1 : nat)) : nat))) ->
		wf_uN v_N (mk_uN i).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
Inductive sN : Type :=
	| mk_sN (i : nat) : sN.

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
Definition proj_sN_0 (x : sN) : nat :=
	match x return nat with
		| (mk_sN v_num_0) => (v_num_0)
	end.

Global Instance proj_sN_0_coercion : Coercion sN nat := { coerce := proj_sN_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.8-20.11 *)
Inductive wf_sN : res_N -> sN -> Prop :=
	| sN_case_0 : forall (v_N : res_N) (i : nat), 
		((((i >= (0 - ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat))) && (i <= (0 - (1 : nat)))) || (i == (0 : nat))) || ((i >= ((1 : nat))) && (i <= (((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat) - (1 : nat))))) ->
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
Definition exp : Type := nat.

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
		((v_m < (2 ^ (fun_M v_N))) && ((((2 : nat) - ((2 ^ ((((E v_N) : nat) - (1 : nat)) : nat)) : nat)) <= v_exp) && (v_exp <= (((2 ^ ((((E v_N) : nat) - (1 : nat)) : nat)) : nat) - (1 : nat))))) ->
		wf_fNmag v_N (NORM v_m v_exp)
	| fNmag_case_1 : forall (v_N : res_N) (v_exp : exp) (v_m : m), 
		((v_m < (2 ^ (fun_M v_N))) && (((2 : nat) - ((2 ^ ((((E v_N) : nat) - (1 : nat)) : nat)) : nat)) == v_exp)) ->
		wf_fNmag v_N (SUBNORM v_m)
	| fNmag_case_2 : forall (v_N : res_N), wf_fNmag v_N INF
	| fNmag_case_3 : forall (v_N : res_N) (v_m : m), 
		((1 <= v_m) && (v_m < (2 ^ (fun_M v_N)))) ->
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

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.1-71.39 *)
Definition fone (v_N : res_N) : fN :=
	match v_N return fN with
		| v_N => (POS (NORM 1 (0 : nat)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:74.1-74.21 *)
Definition canon_ (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (2 ^ ((((!((signif v_N))) : nat) - (1 : nat)) : nat))
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
Definition proj_char_0 (x : char) : nat :=
	match x return nat with
		| (mk_char v_num_0) => (v_num_0)
	end.

Global Instance proj_char_0_coercion : Coercion char nat := { coerce := proj_char_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.8-88.12 *)
Inductive wf_char : char -> Prop :=
	| char_case_0 : forall (i : nat), 
		(((i >= 0) && (i <= 55295)) || ((i >= 57344) && (i <= 1114111))) ->
		wf_char (mk_char i).

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25 *)
Inductive fun_utf8 : (seq char) -> (seq byte) -> Prop :=
	| fun_utf8_case_0 : forall (ch : char) (b : byte), 
		(((ch :> nat) < 128) && ((mk_byte (ch :> nat)) == b)) ->
		fun_utf8 [::ch] [::b]
	| fun_utf8_case_1 : forall (ch : char) (b_1 : byte) (b_2 : byte), 
		(((128 <= (ch :> nat)) && ((ch :> nat) < 2048)) && ((ch :> nat) == (((2 ^ 6) * ((((b_1 :> nat) : nat) - (192 : nat)) : nat)) + ((((b_2 :> nat) : nat) - (128 : nat)) : nat)))) ->
		fun_utf8 [::ch] [::b_1; b_2]
	| fun_utf8_case_2 : forall (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte), 
		((((2048 <= (ch :> nat)) && ((ch :> nat) < 55296)) || ((57344 <= (ch :> nat)) && ((ch :> nat) < 65536))) && ((ch :> nat) == ((((2 ^ 12) * ((((b_1 :> nat) : nat) - (224 : nat)) : nat)) + ((2 ^ 6) * ((((b_2 :> nat) : nat) - (128 : nat)) : nat))) + ((((b_3 :> nat) : nat) - (128 : nat)) : nat)))) ->
		fun_utf8 [::ch] [::b_1; b_2; b_3]
	| fun_utf8_case_3 : forall (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) (b_4 : byte), 
		(((65536 <= (ch :> nat)) && ((ch :> nat) < 69632)) && ((ch :> nat) == (((((2 ^ 18) * ((((b_1 :> nat) : nat) - (240 : nat)) : nat)) + ((2 ^ 12) * ((((b_2 :> nat) : nat) - (128 : nat)) : nat))) + ((2 ^ 6) * ((((b_3 :> nat) : nat) - (128 : nat)) : nat))) + ((((b_4 :> nat) : nat) - (128 : nat)) : nat)))) ->
		fun_utf8 [::ch] [::b_1; b_2; b_3; b_4]
	| fun_utf8_case_4 : forall (ch_lst : (seq char)) (var_0_lst : (seq (seq byte))), 
		((|var_0_lst|) == (|ch_lst|)) ->
		List.Forall2 (fun (var_0 : (seq byte)) (ch : char) => (fun_utf8 [::ch] var_0)) var_0_lst ch_lst ->
		fun_utf8 ch_lst (concat_ byte var_0_lst).

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
Definition proj_name_0 (x : name) : (seq char) :=
	match x return (seq char) with
		| (mk_name v_char_list_0) => (v_char_list_0)
	end.

Global Instance proj_name_0_coercion : Coercion name (seq char) := { coerce := proj_name_0 }.

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.8-92.12 *)
Inductive wf_name : name -> Prop :=
	| name_case_0 : forall (char_lst : (seq char)) (var_0 : (seq byte)), 
		(fun_utf8 char_lst var_0) ->
		List.Forall (fun (v_char : char) => (wf_char v_char)) char_lst ->
		((|var_0|) < (2 ^ 32)) ->
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
Definition mut : Type := (option MUT).

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
Definition proj_dim_0 (x : dim) : nat :=
	match x return nat with
		| (mk_dim v_num_0) => (v_num_0)
	end.

Global Instance proj_dim_0_coercion : Coercion dim nat := { coerce := proj_dim_0 }.

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

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.6-272.11 *)
Inductive fun_zero : numtype -> num_ -> Prop :=
	| fun_zero_case_0 : 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (mk_uN 0))) ->
		fun_zero I32 (mk_num__0 Inn_I32 (mk_uN 0))
	| fun_zero_case_1 : 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (mk_uN 0))) ->
		fun_zero I64 (mk_num__0 Inn_I64 (mk_uN 0))
	| fun_zero_case_2 : 
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		(wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 (fzero (!((res_size (valtype_Fnn Fnn_F32))))))) ->
		fun_zero F32 (mk_num__1 Fnn_F32 (fzero (!((res_size (valtype_Fnn Fnn_F32))))))
	| fun_zero_case_3 : 
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		(wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 (fzero (!((res_size (valtype_Fnn Fnn_F64))))))) ->
		fun_zero F64 (mk_num__1 Fnn_F64 (fzero (!((res_size (valtype_Fnn Fnn_F64)))))).

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
Definition proj_sz_0 (x : sz) : nat :=
	match x return nat with
		| (mk_sz v_num_0) => (v_num_0)
	end.

Global Instance proj_sz_0_coercion : Coercion sz nat := { coerce := proj_sz_0 }.

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

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.1-325.41 *)
Definition shsize (v_shape : shape) : nat :=
	match v_shape return nat with
		| (X v_Lnn (mk_dim v_N)) => ((lsize v_Lnn) * v_N)
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
		((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
		wf_vbinop_Jnn_N v_Jnn v_N (ADD_SAT v_sx)
	| vbinop_Jnn_N_case_3 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
		wf_vbinop_Jnn_N v_Jnn v_N (SUB_SAT v_sx)
	| vbinop_Jnn_N_case_4 : forall (v_Jnn : Jnn) (v_N : res_N), 
		((lsizenn (lanetype_Jnn v_Jnn)) >= 16) ->
		wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_MUL
	| vbinop_Jnn_N_case_5 : forall (v_Jnn : Jnn) (v_N : res_N), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
		wf_vbinop_Jnn_N v_Jnn v_N AVGRU
	| vbinop_Jnn_N_case_6 : forall (v_Jnn : Jnn) (v_N : res_N), 
		((lsizenn (lanetype_Jnn v_Jnn)) == 16) ->
		wf_vbinop_Jnn_N v_Jnn v_N Q15MULR_SATS
	| vbinop_Jnn_N_case_7 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 32) ->
		wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N_MIN v_sx)
	| vbinop_Jnn_N_case_8 : forall (v_Jnn : Jnn) (v_N : res_N) (v_sx : sx), 
		((lsizenn (lanetype_Jnn v_Jnn)) <= 32) ->
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
		((16 <= (lsizenn (lanetype_Jnn v_Jnn))) && ((lsizenn (lanetype_Jnn v_Jnn)) <= 32)) ->
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
		((v_sz :> nat) < (sizenn (numtype_Inn v_Inn))) ->
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
	| instr_case_6 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst_0 : (seq instr)), 
		(wf_blocktype v_blocktype) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		List.Forall (fun (instr_lst_0 : instr) => (wf_instr instr_lst_0)) instr_lst_0 ->
		wf_instr (IFELSE v_blocktype instr_lst instr_lst_0)
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
		((lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) ->
		wf_instr (VEXTUNOP ishape_1 ishape_2 var_0)
	| instr_case_37 : forall (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextbinop_), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(wf_vextbinop_ ishape_1 var_0) ->
		((lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) ->
		wf_instr (VEXTBINOP ishape_1 ishape_2 var_0)
	| instr_case_38 : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(((lsize (fun_lanetype (shape_ishape ishape_2))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) && ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) <= 32)) ->
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
	| instr_case_56 : forall (v_numtype : numtype) (var_0 : (option loadop_)) (v_memarg : memarg), 
		List.Forall (fun (var_0 : loadop_) => (wf_loadop_ v_numtype var_0)) (option_to_list var_0) ->
		(wf_memarg v_memarg) ->
		wf_instr (LOAD v_numtype var_0 v_memarg)
	| instr_case_57 : forall (Inn_opt : (option Inn)) (numtype_opt : (option numtype)) (v_numtype : numtype) (sz_opt : (option sz)) (v_memarg : memarg), 
		List.Forall (fun (v_sz : sz) => (wf_sz v_sz)) (option_to_list sz_opt) ->
		(wf_memarg v_memarg) ->
		((Inn_opt == None) <-> (numtype_opt == None)) ->
		((Inn_opt == None) <-> (sz_opt == None)) ->
		List_Forall3 (fun (v_Inn : Inn) (v_numtype : numtype) (v_sz : sz) => ((v_numtype == (numtype_Inn v_Inn)) && ((v_sz :> nat) < (sizenn (numtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list numtype_opt) (option_to_list sz_opt) ->
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

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
Inductive fun_memsxt : (seq externtype) -> (seq memtype) -> Prop :=
	| fun_memsxt_case_0 : fun_memsxt [:: ] [:: ]
	| fun_memsxt_case_1 : forall (mt : memtype) (xt_lst : (seq externtype)) (var_0 : (seq memtype)), 
		(fun_memsxt xt_lst var_0) ->
		fun_memsxt ([::(MEM mt)] ++ xt_lst) ([::mt] ++ var_0)
	| fun_memsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq memtype)), 
		(fun_memsxt xt_lst var_0) ->
		fun_memsxt ([::v_externtype] ++ xt_lst) var_0.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61 *)
Definition dataidx_instr (v_instr : instr) : (seq dataidx) :=
	match v_instr return (seq dataidx) with
		| (MEMORY_INIT x) => [::x]
		| (DATA_DROP x) => [::x]
		| res_in => [:: ]
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
Inductive fun_dataidx_instrs : (seq instr) -> (seq dataidx) -> Prop :=
	| fun_dataidx_instrs_case_0 : fun_dataidx_instrs [:: ] [:: ]
	| fun_dataidx_instrs_case_1 : forall (v_instr : instr) (instr'_lst : (seq instr)) (var_0 : (seq dataidx)), 
		(fun_dataidx_instrs instr'_lst var_0) ->
		fun_dataidx_instrs ([::v_instr] ++ instr'_lst) ((dataidx_instr v_instr) ++ var_0).

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
Inductive fun_dataidx_expr : expr -> (seq dataidx) -> Prop :=
	| fun_dataidx_expr_case_0 : forall (in_lst : (seq instr)) (var_0 : (seq dataidx)), 
		(fun_dataidx_instrs in_lst var_0) ->
		fun_dataidx_expr in_lst var_0.

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
Inductive fun_dataidx_func : func -> (seq dataidx) -> Prop :=
	| fun_dataidx_func_case_0 : forall (x : uN) (loc_lst : (seq local)) (e : (seq instr)) (var_0 : (seq dataidx)), 
		(fun_dataidx_expr e var_0) ->
		fun_dataidx_func (func_FUNC x loc_lst e) var_0.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
Inductive fun_dataidx_funcs : (seq func) -> (seq dataidx) -> Prop :=
	| fun_dataidx_funcs_case_0 : fun_dataidx_funcs [:: ] [:: ]
	| fun_dataidx_funcs_case_1 : forall (v_func : func) (func'_lst : (seq func)) (var_1 : (seq dataidx)) (var_0 : (seq dataidx)), 
		(fun_dataidx_funcs func'_lst var_1) ->
		(fun_dataidx_func v_func var_0) ->
		fun_dataidx_funcs ([::v_func] ++ func'_lst) (var_0 ++ var_1).

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35 *)
Definition memarg0 : memarg := {| ALIGN := (mk_uN 0); OFFSET := (mk_uN 0) |}.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41 *)
Axiom s33_to_u32 : forall (v_s33 : s33), u32.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22 *)
Definition res_bool (v_bool : bool) : nat :=
	match v_bool return nat with
		| false => 0
		| true => 1
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23 *)
Axiom truncz : forall (rat : nat), nat.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:20.6-20.14 *)
Inductive fun_signed_ : res_N -> nat -> nat -> Prop :=
	| fun_signed__case_0 : forall (v_N : nat) (i : nat), 
		(i < (2 ^ (((v_N : nat) - (1 : nat)) : nat))) ->
		fun_signed_ v_N i (i : nat)
	| fun_signed__case_1 : forall (v_N : nat) (i : nat), 
		(((2 ^ (((v_N : nat) - (1 : nat)) : nat)) <= i) && (i < (2 ^ v_N))) ->
		fun_signed_ v_N i ((i : nat) - ((2 ^ v_N) : nat)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:24.6-24.18 *)
Inductive fun_inv_signed_ : res_N -> nat -> nat -> Prop :=
	| fun_inv_signed__case_0 : forall (v_N : nat) (i : nat), 
		(((0 : nat) <= i) && (i < ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat))) ->
		fun_inv_signed_ v_N i (i : nat)
	| fun_inv_signed__case_1 : forall (v_N : nat) (i : nat), 
		(((0 - ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat)) <= i) && (i < (0 : nat))) ->
		fun_inv_signed_ v_N i ((i + ((2 ^ v_N) : nat)) : nat).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61 *)
Definition sat_u_ (v_N : res_N) (int : nat) : nat :=
	match v_N, int return nat with
		| v_N, i => (if (i < (0 : nat)) then 0 else (if (i > (((2 ^ v_N) : nat) - (1 : nat))) then ((((2 ^ v_N) : nat) - (1 : nat)) : nat) else (i : nat)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61 *)
Definition sat_s_ (v_N : res_N) (int : nat) : nat :=
	match v_N, int return nat with
		| v_N, i => (if (i < (0 - ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat))) then (0 - ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat)) else (if (i > (((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat) - (1 : nat))) then (((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat) - (1 : nat)) else i))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89 *)
Axiom extend__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30 *)
Axiom fabs_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31 *)
Axiom fceil_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32 *)
Axiom ffloor_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34 *)
Axiom fnearest_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30 *)
Axiom fneg_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31 *)
Axiom fsqrt_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32 *)
Axiom ftrunc_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29 *)
Axiom iclz_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29 *)
Axiom ictz_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32 *)
Axiom ipopcnt_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33 *)
Axiom wrap__ : forall (v_M : M) (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 *)
Inductive fun_unop_ : numtype -> unop_ -> num_ -> (seq num_) -> Prop :=
	| fun_unop__case_0 : forall (v_iN : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iclz_ (sizenn (numtype_Inn Inn_I32)) v_iN))) ->
		fun_unop_ I32 (mk_unop__0 Inn_I32 CLZ) (mk_num__0 Inn_I32 v_iN) [::(mk_num__0 Inn_I32 (iclz_ (sizenn (numtype_Inn Inn_I32)) v_iN))]
	| fun_unop__case_1 : forall (v_iN : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iclz_ (sizenn (numtype_Inn Inn_I64)) v_iN))) ->
		fun_unop_ I64 (mk_unop__0 Inn_I64 CLZ) (mk_num__0 Inn_I64 v_iN) [::(mk_num__0 Inn_I64 (iclz_ (sizenn (numtype_Inn Inn_I64)) v_iN))]
	| fun_unop__case_2 : forall (v_iN : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (ictz_ (sizenn (numtype_Inn Inn_I32)) v_iN))) ->
		fun_unop_ I32 (mk_unop__0 Inn_I32 CTZ) (mk_num__0 Inn_I32 v_iN) [::(mk_num__0 Inn_I32 (ictz_ (sizenn (numtype_Inn Inn_I32)) v_iN))]
	| fun_unop__case_3 : forall (v_iN : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (ictz_ (sizenn (numtype_Inn Inn_I64)) v_iN))) ->
		fun_unop_ I64 (mk_unop__0 Inn_I64 CTZ) (mk_num__0 Inn_I64 v_iN) [::(mk_num__0 Inn_I64 (ictz_ (sizenn (numtype_Inn Inn_I64)) v_iN))]
	| fun_unop__case_4 : forall (v_iN : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (ipopcnt_ (sizenn (numtype_Inn Inn_I32)) v_iN))) ->
		fun_unop_ I32 (mk_unop__0 Inn_I32 POPCNT) (mk_num__0 Inn_I32 v_iN) [::(mk_num__0 Inn_I32 (ipopcnt_ (sizenn (numtype_Inn Inn_I32)) v_iN))]
	| fun_unop__case_5 : forall (v_iN : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (ipopcnt_ (sizenn (numtype_Inn Inn_I64)) v_iN))) ->
		fun_unop_ I64 (mk_unop__0 Inn_I64 POPCNT) (mk_num__0 Inn_I64 v_iN) [::(mk_num__0 Inn_I64 (ipopcnt_ (sizenn (numtype_Inn Inn_I64)) v_iN))]
	| fun_unop__case_6 : forall (v_M : nat) (v_iN : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (extend__ v_M (sizenn (numtype_Inn Inn_I32)) res_S (wrap__ (sizenn (numtype_Inn Inn_I32)) v_M v_iN)))) ->
		fun_unop_ I32 (mk_unop__0 Inn_I32 (EXTEND v_M)) (mk_num__0 Inn_I32 v_iN) [::(mk_num__0 Inn_I32 (extend__ v_M (sizenn (numtype_Inn Inn_I32)) res_S (wrap__ (sizenn (numtype_Inn Inn_I32)) v_M v_iN)))]
	| fun_unop__case_7 : forall (v_M : nat) (v_iN : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (extend__ v_M (sizenn (numtype_Inn Inn_I64)) res_S (wrap__ (sizenn (numtype_Inn Inn_I64)) v_M v_iN)))) ->
		fun_unop_ I64 (mk_unop__0 Inn_I64 (EXTEND v_M)) (mk_num__0 Inn_I64 v_iN) [::(mk_num__0 Inn_I64 (extend__ v_M (sizenn (numtype_Inn Inn_I64)) res_S (wrap__ (sizenn (numtype_Inn Inn_I64)) v_M v_iN)))]
	| fun_unop__case_8 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_1 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_1))) (fabs_ (sizenn (numtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 ABS) (mk_num__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_2 : fN) => (mk_num__1 Fnn_F32 iter_0_2)) (fabs_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_9 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_3 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_3))) (fabs_ (sizenn (numtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 ABS) (mk_num__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_4 : fN) => (mk_num__1 Fnn_F64 iter_0_4)) (fabs_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_10 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_5 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_5))) (fneg_ (sizenn (numtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 unop_Fnn_NEG) (mk_num__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_6 : fN) => (mk_num__1 Fnn_F32 iter_0_6)) (fneg_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_11 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_7 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_7))) (fneg_ (sizenn (numtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 unop_Fnn_NEG) (mk_num__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_8 : fN) => (mk_num__1 Fnn_F64 iter_0_8)) (fneg_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_12 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_9 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_9))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 SQRT) (mk_num__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_10 : fN) => (mk_num__1 Fnn_F32 iter_0_10)) (fsqrt_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_13 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_11 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_11))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 SQRT) (mk_num__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_12 : fN) => (mk_num__1 Fnn_F64 iter_0_12)) (fsqrt_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_14 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_13 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_13))) (fceil_ (sizenn (numtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 CEIL) (mk_num__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_14 : fN) => (mk_num__1 Fnn_F32 iter_0_14)) (fceil_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_15 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_15 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_15))) (fceil_ (sizenn (numtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 CEIL) (mk_num__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_16 : fN) => (mk_num__1 Fnn_F64 iter_0_16)) (fceil_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_16 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_17 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_17))) (ffloor_ (sizenn (numtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 FLOOR) (mk_num__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_18 : fN) => (mk_num__1 Fnn_F32 iter_0_18)) (ffloor_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_17 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_19 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_19))) (ffloor_ (sizenn (numtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 FLOOR) (mk_num__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_20 : fN) => (mk_num__1 Fnn_F64 iter_0_20)) (ffloor_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_18 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_21 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_21))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 TRUNC) (mk_num__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_22 : fN) => (mk_num__1 Fnn_F32 iter_0_22)) (ftrunc_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_19 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_23 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_23))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 TRUNC) (mk_num__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_24 : fN) => (mk_num__1 Fnn_F64 iter_0_24)) (ftrunc_ (sizenn (numtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_20 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_25 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_25))) (fnearest_ (sizenn (numtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 NEAREST) (mk_num__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_26 : fN) => (mk_num__1 Fnn_F32 iter_0_26)) (fnearest_ (sizenn (numtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_21 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_27 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_27))) (fnearest_ (sizenn (numtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 NEAREST) (mk_num__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_28 : fN) => (mk_num__1 Fnn_F64 iter_0_28)) (fnearest_ (sizenn (numtype_Fnn Fnn_F64)) v_fN)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37 *)
Axiom fadd_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42 *)
Axiom fcopysign_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37 *)
Axiom fdiv_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37 *)
Axiom fmax_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37 *)
Axiom fmin_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37 *)
Axiom fmul_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37 *)
Axiom fsub_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36 *)
Definition iadd_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : iN :=
	match v_N, v_iN, v_iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN (((i_1 :> nat) + (i_2 :> nat)) mod (2 ^ v_N)))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36 *)
Axiom iand_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 *)
Inductive fun_idiv_ : res_N -> sx -> iN -> iN -> (option iN) -> Prop :=
	| fun_idiv__case_0 : forall (v_N : nat) (i_1 : uN), fun_idiv_ v_N U i_1 (mk_uN 0) None
	| fun_idiv__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_idiv_ v_N U i_1 i_2 (Some (mk_uN ((truncz (((i_1 :> nat) : nat) / ((i_2 :> nat) : nat))) : nat)))
	| fun_idiv__case_2 : forall (v_N : nat) (i_1 : uN), fun_idiv_ v_N res_S i_1 (mk_uN 0) None
	| fun_idiv__case_3 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		(((var_0 : nat) / (var_1 : nat)) == ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat)) ->
		fun_idiv_ v_N res_S i_1 i_2 None
	| fun_idiv__case_4 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_2 : nat) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_2) ->
		(fun_signed_ v_N (i_1 :> nat) var_1) ->
		(fun_inv_signed_ v_N (truncz ((var_1 : nat) / (var_2 : nat))) var_0) ->
		fun_idiv_ v_N res_S i_1 i_2 (Some (mk_uN var_0)).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36 *)
Definition imul_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : iN :=
	match v_N, v_iN, v_iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN (((i_1 :> nat) * (i_2 :> nat)) mod (2 ^ v_N)))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35 *)
Axiom ior_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
Inductive fun_irem_ : res_N -> sx -> iN -> iN -> (option iN) -> Prop :=
	| fun_irem__case_0 : forall (v_N : nat) (i_1 : uN), fun_irem_ v_N U i_1 (mk_uN 0) None
	| fun_irem__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_irem_ v_N U i_1 i_2 (Some (mk_uN ((((i_1 :> nat) : nat) - (((i_2 :> nat) * ((truncz (((i_1 :> nat) : nat) / ((i_2 :> nat) : nat))) : nat)) : nat)) : nat)))
	| fun_irem__case_2 : forall (v_N : nat) (i_1 : uN), fun_irem_ v_N res_S i_1 (mk_uN 0) None
	| fun_irem__case_3 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (j_1 : nat) (j_2 : nat) (var_2 : nat) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_2) ->
		(fun_signed_ v_N (i_1 :> nat) var_1) ->
		(fun_inv_signed_ v_N (j_1 - (j_2 * (truncz ((j_1 : nat) / (j_2 : nat))))) var_0) ->
		((j_1 == var_1) && (j_2 == var_2)) ->
		fun_irem_ v_N res_S i_1 i_2 (Some (mk_uN var_0)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37 *)
Axiom irotl_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37 *)
Axiom irotr_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.1-116.34 *)
Axiom ishl_ : forall (v_N : res_N) (v_iN : iN) (v_u32 : u32), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.1-117.74 *)
Axiom ishr_ : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (v_u32 : u32), iN.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36 *)
Definition isub_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : iN :=
	match v_N, v_iN, v_iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN ((((((2 ^ v_N) + (i_1 :> nat)) : nat) - ((i_2 :> nat) : nat)) mod ((2 ^ v_N) : nat)) : nat))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36 *)
Axiom ixor_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 *)
Inductive fun_binop_ : numtype -> binop_ -> num_ -> num_ -> (seq num_) -> Prop :=
	| fun_binop__case_0 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 ADD) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (iadd_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_1 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 ADD) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (iadd_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_2 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (isub_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 SUB) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (isub_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_3 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (isub_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 SUB) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (isub_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_4 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 MUL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (imul_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_5 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 MUL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (imul_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_idiv_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		List.Forall (fun (iter_0_29 : iN) => (wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iter_0_29))) (option_to_list var_0) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 (DIV v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (list_ num_ (option_map (fun (iter_0_30 : iN) => (mk_num__0 Inn_I32 iter_0_30)) var_0))
	| fun_binop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_idiv_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		List.Forall (fun (iter_0_31 : iN) => (wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iter_0_31))) (option_to_list var_0) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 (DIV v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (list_ num_ (option_map (fun (iter_0_32 : iN) => (mk_num__0 Inn_I64 iter_0_32)) var_0))
	| fun_binop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_irem_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		List.Forall (fun (iter_0_33 : iN) => (wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iter_0_33))) (option_to_list var_0) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 (REM v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (list_ num_ (option_map (fun (iter_0_34 : iN) => (mk_num__0 Inn_I32 iter_0_34)) var_0))
	| fun_binop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_irem_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		List.Forall (fun (iter_0_35 : iN) => (wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iter_0_35))) (option_to_list var_0) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 (REM v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (list_ num_ (option_map (fun (iter_0_36 : iN) => (mk_num__0 Inn_I64 iter_0_36)) var_0))
	| fun_binop__case_10 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iand_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 AND) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (iand_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_11 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iand_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 AND) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (iand_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_12 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (ior_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 OR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (ior_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_13 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (ior_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 OR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (ior_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_14 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (ixor_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 XOR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (ixor_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_15 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (ixor_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 XOR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (ixor_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_16 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (ishl_ (sizenn (numtype_Inn Inn_I32)) iN_1 (mk_uN (iN_2 :> nat))))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 SHL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (ishl_ (sizenn (numtype_Inn Inn_I32)) iN_1 (mk_uN (iN_2 :> nat))))]
	| fun_binop__case_17 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (ishl_ (sizenn (numtype_Inn Inn_I64)) iN_1 (mk_uN (iN_2 :> nat))))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 SHL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (ishl_ (sizenn (numtype_Inn Inn_I64)) iN_1 (mk_uN (iN_2 :> nat))))]
	| fun_binop__case_18 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (ishr_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 (mk_uN (iN_2 :> nat))))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 (SHR v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (ishr_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 (mk_uN (iN_2 :> nat))))]
	| fun_binop__case_19 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (ishr_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 (mk_uN (iN_2 :> nat))))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 (SHR v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (ishr_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 (mk_uN (iN_2 :> nat))))]
	| fun_binop__case_20 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (irotl_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 ROTL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (irotl_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_21 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (irotl_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 ROTL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (irotl_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_22 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (irotr_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 ROTR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [::(mk_num__0 Inn_I32 (irotr_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_23 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (irotr_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 ROTR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [::(mk_num__0 Inn_I64 (irotr_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_24 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_37 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_37))) (fadd_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_ADD) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_38 : fN) => (mk_num__1 Fnn_F32 iter_0_38)) (fadd_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_25 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_39 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_39))) (fadd_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_ADD) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_40 : fN) => (mk_num__1 Fnn_F64 iter_0_40)) (fadd_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_26 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_41 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_41))) (fsub_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_SUB) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_42 : fN) => (mk_num__1 Fnn_F32 iter_0_42)) (fsub_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_27 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_43 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_43))) (fsub_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_SUB) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_44 : fN) => (mk_num__1 Fnn_F64 iter_0_44)) (fsub_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_28 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_45 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_45))) (fmul_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_MUL) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_46 : fN) => (mk_num__1 Fnn_F32 iter_0_46)) (fmul_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_29 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_47 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_47))) (fmul_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_48 : fN) => (mk_num__1 Fnn_F64 iter_0_48)) (fmul_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_30 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_49 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_49))) (fdiv_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_DIV) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_50 : fN) => (mk_num__1 Fnn_F32 iter_0_50)) (fdiv_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_31 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_51 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_51))) (fdiv_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_DIV) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_52 : fN) => (mk_num__1 Fnn_F64 iter_0_52)) (fdiv_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_32 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_53 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_53))) (fmin_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 MIN) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_54 : fN) => (mk_num__1 Fnn_F32 iter_0_54)) (fmin_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_33 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_55 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_55))) (fmin_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 MIN) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_56 : fN) => (mk_num__1 Fnn_F64 iter_0_56)) (fmin_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_34 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_57 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_57))) (fmax_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 MAX) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_58 : fN) => (mk_num__1 Fnn_F32 iter_0_58)) (fmax_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_35 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_59 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_59))) (fmax_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 MAX) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_60 : fN) => (mk_num__1 Fnn_F64 iter_0_60)) (fmax_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_36 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_61 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_61))) (fcopysign_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 COPYSIGN) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_62 : fN) => (mk_num__1 Fnn_F32 iter_0_62)) (fcopysign_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_37 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_63 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_63))) (fcopysign_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 COPYSIGN) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_64 : fN) => (mk_num__1 Fnn_F64 iter_0_64)) (fcopysign_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2)).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27 *)
Definition ieqz_ (v_N : res_N) (v_iN : iN) : u32 :=
	match v_N, v_iN return u32 with
		| v_N, i_1 => (mk_uN (res_bool ((i_1 :> nat) == 0)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 *)
Inductive fun_testop_ : numtype -> testop_ -> num_ -> num_ -> Prop :=
	| fun_testop__case_0 : forall (v_iN : uN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (ieqz_ (sizenn (numtype_Inn Inn_I32)) v_iN))) ->
		fun_testop_ I32 (mk_testop__0 Inn_I32 EQZ) (mk_num__0 Inn_I32 v_iN) (mk_num__0 Inn_I32 (ieqz_ (sizenn (numtype_Inn Inn_I32)) v_iN))
	| fun_testop__case_1 : forall (v_iN : uN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (ieqz_ (sizenn (numtype_Inn Inn_I64)) v_iN))) ->
		fun_testop_ I64 (mk_testop__0 Inn_I64 EQZ) (mk_num__0 Inn_I64 v_iN) (mk_num__0 Inn_I32 (ieqz_ (sizenn (numtype_Inn Inn_I64)) v_iN)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33 *)
Axiom feq_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33 *)
Axiom fge_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33 *)
Axiom fgt_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33 *)
Axiom fle_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33 *)
Axiom flt_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33 *)
Axiom fne_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33 *)
Definition ieq_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : u32 :=
	match v_N, v_iN, v_iN_0 return u32 with
		| v_N, i_1, i_2 => (mk_uN (res_bool (i_1 == i_2)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
Inductive fun_ige_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ige__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ige_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) >= (i_2 :> nat))))
	| fun_ige__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ige_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 >= var_1))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
Inductive fun_igt_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_igt__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_igt_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) > (i_2 :> nat))))
	| fun_igt__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_igt_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 > var_1))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
Inductive fun_ile_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ile__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ile_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) <= (i_2 :> nat))))
	| fun_ile__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ile_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 <= var_1))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
Inductive fun_ilt_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ilt__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ilt_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) < (i_2 :> nat))))
	| fun_ilt__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ilt_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 < var_1))).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33 *)
Definition ine_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : u32 :=
	match v_N, v_iN, v_iN_0 return u32 with
		| v_N, i_1, i_2 => (mk_uN (res_bool (i_1 != i_2)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
Inductive fun_relop_ : numtype -> relop_ -> num_ -> num_ -> num_ -> Prop :=
	| fun_relop__case_0 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (ieq_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 EQ) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 (ieq_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))
	| fun_relop__case_1 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (ieq_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 EQ) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 (ieq_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))
	| fun_relop__case_2 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (ine_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 NE) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 (ine_ (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))
	| fun_relop__case_3 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (ine_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 NE) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 (ine_ (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))
	| fun_relop__case_4 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ilt_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		(wf_num_ I32 (mk_num__0 Inn_I32 var_0)) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (LT v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_5 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ilt_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		(wf_num_ I32 (mk_num__0 Inn_I32 var_0)) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (LT v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_igt_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		(wf_num_ I32 (mk_num__0 Inn_I32 var_0)) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (GT v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_igt_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		(wf_num_ I32 (mk_num__0 Inn_I32 var_0)) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (GT v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ile_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		(wf_num_ I32 (mk_num__0 Inn_I32 var_0)) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (LE v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ile_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		(wf_num_ I32 (mk_num__0 Inn_I32 var_0)) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (LE v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_10 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ige_ (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		(wf_num_ I32 (mk_num__0 Inn_I32 var_0)) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (GE v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_11 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ige_ (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		(wf_num_ I32 (mk_num__0 Inn_I32 var_0)) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (GE v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)
	| fun_relop__case_12 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (feq_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_EQ) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (feq_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_13 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (feq_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_EQ) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (feq_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_14 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (fne_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_NE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fne_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_15 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (fne_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_NE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fne_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_16 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (flt_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_LT) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (flt_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_17 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (flt_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_LT) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (flt_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_18 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (fgt_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_GT) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fgt_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_19 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (fgt_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_GT) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fgt_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_20 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (fle_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_LE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fle_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_21 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (fle_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_LE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fle_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_22 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (fge_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_GE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fge_ (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_23 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_num_ I32 (mk_num__0 Inn_I32 (fge_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_GE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fge_ (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90 *)
Axiom convert__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN), fN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36 *)
Axiom demote__ : forall (v_M : M) (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37 *)
Axiom promote__ : forall (v_M : M) (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76 *)
Axiom reinterpret__ : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_), num_.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88 *)
Axiom trunc__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN), (option iN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93 *)
Axiom trunc_sat__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN), (option iN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
Inductive fun_cvtop__ : numtype -> numtype -> cvtop -> num_ -> (seq num_) -> Prop :=
	| fun_cvtop___case_0 : forall (v_sx : sx) (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (extend__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))) ->
		fun_cvtop__ I32 I32 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I32 iN_1) [::(mk_num__0 Inn_I32 (extend__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))]
	| fun_cvtop___case_1 : forall (v_sx : sx) (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (extend__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))) ->
		fun_cvtop__ I64 I32 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I64 iN_1) [::(mk_num__0 Inn_I32 (extend__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))]
	| fun_cvtop___case_2 : forall (v_sx : sx) (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (extend__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))) ->
		fun_cvtop__ I32 I64 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I32 iN_1) [::(mk_num__0 Inn_I64 (extend__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))]
	| fun_cvtop___case_3 : forall (v_sx : sx) (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (extend__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))) ->
		fun_cvtop__ I64 I64 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I64 iN_1) [::(mk_num__0 Inn_I64 (extend__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))]
	| fun_cvtop___case_4 : forall (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (wrap__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))) ->
		fun_cvtop__ I32 I32 WRAP (mk_num__0 Inn_I32 iN_1) [::(mk_num__0 Inn_I32 (wrap__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))]
	| fun_cvtop___case_5 : forall (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (wrap__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))) ->
		fun_cvtop__ I64 I32 WRAP (mk_num__0 Inn_I64 iN_1) [::(mk_num__0 Inn_I32 (wrap__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))]
	| fun_cvtop___case_6 : forall (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (wrap__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))) ->
		fun_cvtop__ I32 I64 WRAP (mk_num__0 Inn_I32 iN_1) [::(mk_num__0 Inn_I64 (wrap__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))]
	| fun_cvtop___case_7 : forall (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (wrap__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))) ->
		fun_cvtop__ I64 I64 WRAP (mk_num__0 Inn_I64 iN_1) [::(mk_num__0 Inn_I64 (wrap__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))]
	| fun_cvtop___case_8 : forall (v_sx : sx) (fN_1 : fN), 
		List.Forall (fun (iter_0_65 : iN) => (wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iter_0_65))) (option_to_list (trunc__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)) ->
		fun_cvtop__ F32 I32 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F32 fN_1) (list_ num_ (option_map (fun (iter_0_66 : iN) => (mk_num__0 Inn_I32 iter_0_66)) (trunc__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))
	| fun_cvtop___case_9 : forall (v_sx : sx) (fN_1 : fN), 
		List.Forall (fun (iter_0_67 : iN) => (wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iter_0_67))) (option_to_list (trunc__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)) ->
		fun_cvtop__ F64 I32 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F64 fN_1) (list_ num_ (option_map (fun (iter_0_68 : iN) => (mk_num__0 Inn_I32 iter_0_68)) (trunc__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))
	| fun_cvtop___case_10 : forall (v_sx : sx) (fN_1 : fN), 
		List.Forall (fun (iter_0_69 : iN) => (wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iter_0_69))) (option_to_list (trunc__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)) ->
		fun_cvtop__ F32 I64 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F32 fN_1) (list_ num_ (option_map (fun (iter_0_70 : iN) => (mk_num__0 Inn_I64 iter_0_70)) (trunc__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))
	| fun_cvtop___case_11 : forall (v_sx : sx) (fN_1 : fN), 
		List.Forall (fun (iter_0_71 : iN) => (wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iter_0_71))) (option_to_list (trunc__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)) ->
		fun_cvtop__ F64 I64 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F64 fN_1) (list_ num_ (option_map (fun (iter_0_72 : iN) => (mk_num__0 Inn_I64 iter_0_72)) (trunc__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))
	| fun_cvtop___case_12 : forall (v_sx : sx) (fN_1 : fN), 
		List.Forall (fun (iter_0_73 : iN) => (wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iter_0_73))) (option_to_list (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)) ->
		fun_cvtop__ F32 I32 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F32 fN_1) (list_ num_ (option_map (fun (iter_0_74 : iN) => (mk_num__0 Inn_I32 iter_0_74)) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))
	| fun_cvtop___case_13 : forall (v_sx : sx) (fN_1 : fN), 
		List.Forall (fun (iter_0_75 : iN) => (wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iter_0_75))) (option_to_list (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)) ->
		fun_cvtop__ F64 I32 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F64 fN_1) (list_ num_ (option_map (fun (iter_0_76 : iN) => (mk_num__0 Inn_I32 iter_0_76)) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))
	| fun_cvtop___case_14 : forall (v_sx : sx) (fN_1 : fN), 
		List.Forall (fun (iter_0_77 : iN) => (wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iter_0_77))) (option_to_list (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)) ->
		fun_cvtop__ F32 I64 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F32 fN_1) (list_ num_ (option_map (fun (iter_0_78 : iN) => (mk_num__0 Inn_I64 iter_0_78)) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))
	| fun_cvtop___case_15 : forall (v_sx : sx) (fN_1 : fN), 
		List.Forall (fun (iter_0_79 : iN) => (wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iter_0_79))) (option_to_list (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)) ->
		fun_cvtop__ F64 I64 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F64 fN_1) (list_ num_ (option_map (fun (iter_0_80 : iN) => (mk_num__0 Inn_I64 iter_0_80)) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))
	| fun_cvtop___case_16 : forall (v_sx : sx) (iN_1 : uN), 
		(wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 (convert__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))) ->
		fun_cvtop__ I32 F32 (CONVERT v_sx) (mk_num__0 Inn_I32 iN_1) [::(mk_num__1 Fnn_F32 (convert__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))]
	| fun_cvtop___case_17 : forall (v_sx : sx) (iN_1 : uN), 
		(wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 (convert__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))) ->
		fun_cvtop__ I64 F32 (CONVERT v_sx) (mk_num__0 Inn_I64 iN_1) [::(mk_num__1 Fnn_F32 (convert__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))]
	| fun_cvtop___case_18 : forall (v_sx : sx) (iN_1 : uN), 
		(wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 (convert__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))) ->
		fun_cvtop__ I32 F64 (CONVERT v_sx) (mk_num__0 Inn_I32 iN_1) [::(mk_num__1 Fnn_F64 (convert__ (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))]
	| fun_cvtop___case_19 : forall (v_sx : sx) (iN_1 : uN), 
		(wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 (convert__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))) ->
		fun_cvtop__ I64 F64 (CONVERT v_sx) (mk_num__0 Inn_I64 iN_1) [::(mk_num__1 Fnn_F64 (convert__ (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))]
	| fun_cvtop___case_20 : forall (fN_1 : fN), 
		List.Forall (fun (iter_0_81 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_81))) (promote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1) ->
		fun_cvtop__ F32 F32 PROMOTE (mk_num__1 Fnn_F32 fN_1) (seq.map (fun (iter_0_82 : fN) => (mk_num__1 Fnn_F32 iter_0_82)) (promote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))
	| fun_cvtop___case_21 : forall (fN_1 : fN), 
		List.Forall (fun (iter_0_83 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_83))) (promote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1) ->
		fun_cvtop__ F64 F32 PROMOTE (mk_num__1 Fnn_F64 fN_1) (seq.map (fun (iter_0_84 : fN) => (mk_num__1 Fnn_F32 iter_0_84)) (promote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))
	| fun_cvtop___case_22 : forall (fN_1 : fN), 
		List.Forall (fun (iter_0_85 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_85))) (promote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1) ->
		fun_cvtop__ F32 F64 PROMOTE (mk_num__1 Fnn_F32 fN_1) (seq.map (fun (iter_0_86 : fN) => (mk_num__1 Fnn_F64 iter_0_86)) (promote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))
	| fun_cvtop___case_23 : forall (fN_1 : fN), 
		List.Forall (fun (iter_0_87 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_87))) (promote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1) ->
		fun_cvtop__ F64 F64 PROMOTE (mk_num__1 Fnn_F64 fN_1) (seq.map (fun (iter_0_88 : fN) => (mk_num__1 Fnn_F64 iter_0_88)) (promote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))
	| fun_cvtop___case_24 : forall (fN_1 : fN), 
		List.Forall (fun (iter_0_89 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_89))) (demote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1) ->
		fun_cvtop__ F32 F32 DEMOTE (mk_num__1 Fnn_F32 fN_1) (seq.map (fun (iter_0_90 : fN) => (mk_num__1 Fnn_F32 iter_0_90)) (demote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))
	| fun_cvtop___case_25 : forall (fN_1 : fN), 
		List.Forall (fun (iter_0_91 : fN) => (wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_91))) (demote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1) ->
		fun_cvtop__ F64 F32 DEMOTE (mk_num__1 Fnn_F64 fN_1) (seq.map (fun (iter_0_92 : fN) => (mk_num__1 Fnn_F32 iter_0_92)) (demote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))
	| fun_cvtop___case_26 : forall (fN_1 : fN), 
		List.Forall (fun (iter_0_93 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_93))) (demote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1) ->
		fun_cvtop__ F32 F64 DEMOTE (mk_num__1 Fnn_F32 fN_1) (seq.map (fun (iter_0_94 : fN) => (mk_num__1 Fnn_F64 iter_0_94)) (demote__ (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))
	| fun_cvtop___case_27 : forall (fN_1 : fN), 
		List.Forall (fun (iter_0_95 : fN) => (wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_95))) (demote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1) ->
		fun_cvtop__ F64 F64 DEMOTE (mk_num__1 Fnn_F64 fN_1) (seq.map (fun (iter_0_96 : fN) => (mk_num__1 Fnn_F64 iter_0_96)) (demote__ (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))
	| fun_cvtop___case_28 : forall (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_1)) ->
		((res_size (valtype_Inn Inn_I32)) != None) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((!((res_size (valtype_Inn Inn_I32)))) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		fun_cvtop__ I32 F32 REINTERPRET (mk_num__0 Inn_I32 iN_1) [::(reinterpret__ (numtype_Inn Inn_I32) (numtype_Fnn Fnn_F32) (mk_num__0 Inn_I32 iN_1))]
	| fun_cvtop___case_29 : forall (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_1)) ->
		((res_size (valtype_Inn Inn_I64)) != None) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((!((res_size (valtype_Inn Inn_I64)))) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		fun_cvtop__ I64 F32 REINTERPRET (mk_num__0 Inn_I64 iN_1) [::(reinterpret__ (numtype_Inn Inn_I64) (numtype_Fnn Fnn_F32) (mk_num__0 Inn_I64 iN_1))]
	| fun_cvtop___case_30 : forall (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_1)) ->
		((res_size (valtype_Inn Inn_I32)) != None) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((!((res_size (valtype_Inn Inn_I32)))) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		fun_cvtop__ I32 F64 REINTERPRET (mk_num__0 Inn_I32 iN_1) [::(reinterpret__ (numtype_Inn Inn_I32) (numtype_Fnn Fnn_F64) (mk_num__0 Inn_I32 iN_1))]
	| fun_cvtop___case_31 : forall (iN_1 : uN), 
		(wf_num_ (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_1)) ->
		((res_size (valtype_Inn Inn_I64)) != None) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((!((res_size (valtype_Inn Inn_I64)))) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		fun_cvtop__ I64 F64 REINTERPRET (mk_num__0 Inn_I64 iN_1) [::(reinterpret__ (numtype_Inn Inn_I64) (numtype_Fnn Fnn_F64) (mk_num__0 Inn_I64 iN_1))]
	| fun_cvtop___case_32 : forall (fN_1 : fN), 
		(wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_1)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((res_size (valtype_Inn Inn_I32)) != None) ->
		((!((res_size (valtype_Fnn Fnn_F32)))) == (!((res_size (valtype_Inn Inn_I32))))) ->
		fun_cvtop__ F32 I32 REINTERPRET (mk_num__1 Fnn_F32 fN_1) [::(reinterpret__ (numtype_Fnn Fnn_F32) (numtype_Inn Inn_I32) (mk_num__1 Fnn_F32 fN_1))]
	| fun_cvtop___case_33 : forall (fN_1 : fN), 
		(wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_1)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((res_size (valtype_Inn Inn_I32)) != None) ->
		((!((res_size (valtype_Fnn Fnn_F64)))) == (!((res_size (valtype_Inn Inn_I32))))) ->
		fun_cvtop__ F64 I32 REINTERPRET (mk_num__1 Fnn_F64 fN_1) [::(reinterpret__ (numtype_Fnn Fnn_F64) (numtype_Inn Inn_I32) (mk_num__1 Fnn_F64 fN_1))]
	| fun_cvtop___case_34 : forall (fN_1 : fN), 
		(wf_num_ (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_1)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((res_size (valtype_Inn Inn_I64)) != None) ->
		((!((res_size (valtype_Fnn Fnn_F32)))) == (!((res_size (valtype_Inn Inn_I64))))) ->
		fun_cvtop__ F32 I64 REINTERPRET (mk_num__1 Fnn_F32 fN_1) [::(reinterpret__ (numtype_Fnn Fnn_F32) (numtype_Inn Inn_I64) (mk_num__1 Fnn_F32 fN_1))]
	| fun_cvtop___case_35 : forall (fN_1 : fN), 
		(wf_num_ (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_1)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((res_size (valtype_Inn Inn_I64)) != None) ->
		((!((res_size (valtype_Fnn Fnn_F64)))) == (!((res_size (valtype_Inn Inn_I64))))) ->
		fun_cvtop__ F64 I64 REINTERPRET (mk_num__1 Fnn_F64 fN_1) [::(reinterpret__ (numtype_Fnn Fnn_F64) (numtype_Inn Inn_I64) (mk_num__1 Fnn_F64 fN_1))].

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87 *)
Axiom narrow__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 *)
Axiom ibits_ : forall (v_N : res_N) (v_iN : iN), (seq bit).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102 *)
Axiom fbits_ : forall (v_N : res_N) (v_fN : fN), (seq bit).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103 *)
Axiom ibytes_ : forall (v_N : res_N) (v_iN : iN), (seq byte).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103 *)
Axiom fbytes_ : forall (v_N : res_N) (v_fN : fN), (seq byte).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103 *)
Axiom nbytes_ : forall (v_numtype : numtype) (v_num_ : num_), (seq byte).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103 *)
Axiom vbytes_ : forall (v_vectype : vectype) (v_vec_ : vec_), (seq byte).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 *)
Axiom inv_ibits_ : forall (v_N : res_N) (var_0 : (seq bit)), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 *)
Axiom inv_fbits_ : forall (v_N : res_N) (var_0 : (seq bit)), fN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86 *)
Axiom inv_ibytes_ : forall (v_N : res_N) (var_0 : (seq byte)), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86 *)
Axiom inv_fbytes_ : forall (v_N : res_N) (var_0 : (seq byte)), fN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84 *)
Axiom inv_nbytes_ : forall (v_numtype : numtype) (var_0 : (seq byte)), num_.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84 *)
Axiom inv_vbytes_ : forall (v_vectype : vectype) (var_0 : (seq byte)), vec_.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29 *)
Axiom inot_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29 *)
Axiom irev_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39 *)
Axiom iandnot_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27 *)
Definition inez_ (v_N : res_N) (v_iN : iN) : u32 :=
	match v_N, v_iN return u32 with
		| v_N, i_1 => (mk_uN (res_bool ((i_1 :> nat) != 0)))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49 *)
Axiom ibitselect_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) (v_iN_1 : iN), iN.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29 *)
Definition ineg_ (v_N : res_N) (v_iN : iN) : iN :=
	match v_N, v_iN return iN with
		| v_N, i_1 => (mk_uN (((((2 ^ v_N) : nat) - ((i_1 :> nat) : nat)) mod ((2 ^ v_N) : nat)) : nat))
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
Inductive fun_iabs_ : res_N -> iN -> iN -> Prop :=
	| fun_iabs__case_0 : forall (v_N : nat) (i_1 : uN) (var_0 : nat), 
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_iabs_ v_N i_1 (if (var_0 >= (0 : nat)) then i_1 else (ineg_ v_N i_1)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
Inductive fun_imin_ : res_N -> sx -> iN -> iN -> iN -> Prop :=
	| fun_imin__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), 
		((i_1 :> nat) <= (i_2 :> nat)) ->
		fun_imin_ v_N U i_1 i_2 i_1
	| fun_imin__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), 
		((i_1 :> nat) > (i_2 :> nat)) ->
		fun_imin_ v_N U i_1 i_2 i_2
	| fun_imin__case_2 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_imin_ v_N res_S i_1 i_2 (if (var_0 <= var_1) then i_1 else i_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
Inductive fun_imax_ : res_N -> sx -> iN -> iN -> iN -> Prop :=
	| fun_imax__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), 
		((i_1 :> nat) >= (i_2 :> nat)) ->
		fun_imax_ v_N U i_1 i_2 i_1
	| fun_imax__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), 
		((i_1 :> nat) < (i_2 :> nat)) ->
		fun_imax_ v_N U i_1 i_2 i_2
	| fun_imax__case_2 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_imax_ v_N res_S i_1 i_2 (if (var_0 >= var_1) then i_1 else i_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
Inductive fun_iadd_sat_ : res_N -> sx -> iN -> iN -> iN -> Prop :=
	| fun_iadd_sat__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_iadd_sat_ v_N U i_1 i_2 (mk_uN (sat_u_ v_N (((i_1 :> nat) + (i_2 :> nat)) : nat)))
	| fun_iadd_sat__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_2 : nat) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_2) ->
		(fun_signed_ v_N (i_1 :> nat) var_1) ->
		(fun_inv_signed_ v_N (sat_s_ v_N (var_1 + var_2)) var_0) ->
		fun_iadd_sat_ v_N res_S i_1 i_2 (mk_uN var_0).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
Inductive fun_isub_sat_ : res_N -> sx -> iN -> iN -> iN -> Prop :=
	| fun_isub_sat__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_isub_sat_ v_N U i_1 i_2 (mk_uN (sat_u_ v_N (((i_1 :> nat) : nat) - ((i_2 :> nat) : nat))))
	| fun_isub_sat__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_2 : nat) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_2) ->
		(fun_signed_ v_N (i_1 :> nat) var_1) ->
		(fun_inv_signed_ v_N (sat_s_ v_N (var_1 - var_2)) var_0) ->
		fun_isub_sat_ v_N res_S i_1 i_2 (mk_uN var_0).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82 *)
Axiom iavgr_ : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90 *)
Axiom iq15mulr_sat_ : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38 *)
Axiom fpmin_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38 *)
Axiom fpmax_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.6-323.15 *)
Inductive fun_packnum_ : lanetype -> num_ -> lane_ -> Prop :=
	| fun_packnum__case_0 : forall (c : num_), 
		(wf_lane_ (lanetype_numtype I32) (mk_lane__0 I32 c)) ->
		fun_packnum_ lanetype_I32 c (mk_lane__0 I32 c)
	| fun_packnum__case_1 : forall (c : num_), 
		(wf_lane_ (lanetype_numtype I64) (mk_lane__0 I64 c)) ->
		fun_packnum_ lanetype_I64 c (mk_lane__0 I64 c)
	| fun_packnum__case_2 : forall (c : num_), 
		(wf_lane_ (lanetype_numtype F32) (mk_lane__0 F32 c)) ->
		fun_packnum_ lanetype_F32 c (mk_lane__0 F32 c)
	| fun_packnum__case_3 : forall (c : num_), 
		(wf_lane_ (lanetype_numtype F64) (mk_lane__0 F64 c)) ->
		fun_packnum_ lanetype_F64 c (mk_lane__0 F64 c)
	| fun_packnum__case_4 : forall (c : uN), 
		((res_size (valtype_numtype (unpack (lanetype_packtype I8)))) != None) ->
		(wf_lane_ (lanetype_packtype I8) (mk_lane__1 I8 (wrap__ (!((res_size (valtype_numtype (unpack (lanetype_packtype I8)))))) (psize I8) c))) ->
		fun_packnum_ lanetype_I8 (mk_num__0 Inn_I32 c) (mk_lane__1 I8 (wrap__ (!((res_size (valtype_numtype (unpack (lanetype_packtype I8)))))) (psize I8) c))
	| fun_packnum__case_5 : forall (c : uN), 
		((res_size (valtype_numtype (unpack (lanetype_packtype I16)))) != None) ->
		(wf_lane_ (lanetype_packtype I16) (mk_lane__1 I16 (wrap__ (!((res_size (valtype_numtype (unpack (lanetype_packtype I16)))))) (psize I16) c))) ->
		fun_packnum_ lanetype_I16 (mk_num__0 Inn_I32 c) (mk_lane__1 I16 (wrap__ (!((res_size (valtype_numtype (unpack (lanetype_packtype I16)))))) (psize I16) c)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.6-328.17 *)
Inductive fun_unpacknum_ : lanetype -> lane_ -> num_ -> Prop :=
	| fun_unpacknum__case_0 : forall (c : num_), fun_unpacknum_ lanetype_I32 (mk_lane__0 I32 c) c
	| fun_unpacknum__case_1 : forall (c : num_), fun_unpacknum_ lanetype_I64 (mk_lane__0 I64 c) c
	| fun_unpacknum__case_2 : forall (c : num_), fun_unpacknum_ lanetype_F32 (mk_lane__0 F32 c) c
	| fun_unpacknum__case_3 : forall (c : num_), fun_unpacknum_ lanetype_F64 (mk_lane__0 F64 c) c
	| fun_unpacknum__case_4 : forall (c : uN), 
		((res_size (valtype_numtype (unpack (lanetype_packtype I8)))) != None) ->
		(wf_num_ (unpack (lanetype_packtype I8)) (mk_num__0 Inn_I32 (extend__ (psize I8) (!((res_size (valtype_numtype (unpack (lanetype_packtype I8)))))) U c))) ->
		fun_unpacknum_ lanetype_I8 (mk_lane__1 I8 c) (mk_num__0 Inn_I32 (extend__ (psize I8) (!((res_size (valtype_numtype (unpack (lanetype_packtype I8)))))) U c))
	| fun_unpacknum__case_5 : forall (c : uN), 
		((res_size (valtype_numtype (unpack (lanetype_packtype I16)))) != None) ->
		(wf_num_ (unpack (lanetype_packtype I16)) (mk_num__0 Inn_I32 (extend__ (psize I16) (!((res_size (valtype_numtype (unpack (lanetype_packtype I16)))))) U c))) ->
		fun_unpacknum_ lanetype_I16 (mk_lane__1 I16 c) (mk_num__0 Inn_I32 (extend__ (psize I16) (!((res_size (valtype_numtype (unpack (lanetype_packtype I16)))))) U c)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.1-336.84 *)
Axiom lanes_ : forall (v_shape : shape) (v_vec_ : vec_), (seq lane_).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.1-340.36 *)
Axiom inv_lanes_ : forall (v_shape : shape) (var_0 : (seq lane_)), vec_.

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

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.1-365.31 *)
Definition vvbinop_ (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (v_vec__0 : vec_) : vec_ :=
	match v_vectype, v_vvbinop, v_vec_, v_vec__0 return vec_ with
		| V128, vvbinop_AND, v128_1, v128_2 => (iand_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, ANDNOT, v128_1, v128_2 => (iandnot_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, vvbinop_OR, v128_1, v128_2 => (ior_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, vvbinop_XOR, v128_1, v128_2 => (ixor_ (!((res_size valtype_V128))) v128_1 v128_2)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.1-367.34 *)
Definition vvternop_ (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (v_vec__0 : vec_) (v_vec__1 : vec_) : vec_ :=
	match v_vectype, v_vvternop, v_vec_, v_vec__0, v_vec__1 return vec_ with
		| V128, BITSELECT, v128_1, v128_2, v128_3 => (ibitselect_ (!((res_size valtype_V128))) v128_1 v128_2 v128_3)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 *)
Inductive fun_vunop_ : shape -> vunop_ -> vec_ -> (seq vec_) -> Prop :=
	| fun_vunop__case_0 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_3 : lane_) => ((proj_lane__2 lane_1_3) != None)) lane_1_lst ->
		List.Forall2 (fun (var_1 : uN) (lane_1_3 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_3))) var_1)) var_1_lst lane_1_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_1 : lane_) => ((proj_lane__2 lane_1_1) != None)) lane_1_lst ->
		List.Forall2 (fun (var_0 : uN) (lane_1_1 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_1))) var_0)) var_0_lst lane_1_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I32 var_1)) var_1_lst))) ->
		fun_vunop_ (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 v_M vunop_Jnn_N_ABS) v128_1 [::v128]
	| fun_vunop__case_1 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_6 : lane_) => ((proj_lane__2 lane_1_6) != None)) lane_1_lst ->
		List.Forall2 (fun (var_1 : uN) (lane_1_6 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_6))) var_1)) var_1_lst lane_1_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_4 : lane_) => ((proj_lane__2 lane_1_4) != None)) lane_1_lst ->
		List.Forall2 (fun (var_0 : uN) (lane_1_4 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_4))) var_0)) var_0_lst lane_1_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I64 var_1)) var_1_lst))) ->
		fun_vunop_ (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 v_M vunop_Jnn_N_ABS) v128_1 [::v128]
	| fun_vunop__case_2 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_9 : lane_) => ((proj_lane__2 lane_1_9) != None)) lane_1_lst ->
		List.Forall2 (fun (var_1 : uN) (lane_1_9 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_9))) var_1)) var_1_lst lane_1_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_7 : lane_) => ((proj_lane__2 lane_1_7) != None)) lane_1_lst ->
		List.Forall2 (fun (var_0 : uN) (lane_1_7 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_7))) var_0)) var_0_lst lane_1_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I8 var_1)) var_1_lst))) ->
		fun_vunop_ (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 v_M vunop_Jnn_N_ABS) v128_1 [::v128]
	| fun_vunop__case_3 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_12 : lane_) => ((proj_lane__2 lane_1_12) != None)) lane_1_lst ->
		List.Forall2 (fun (var_1 : uN) (lane_1_12 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_12))) var_1)) var_1_lst lane_1_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		List.Forall (fun (lane_1_10 : lane_) => ((proj_lane__2 lane_1_10) != None)) lane_1_lst ->
		List.Forall2 (fun (var_0 : uN) (lane_1_10 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_10))) var_0)) var_0_lst lane_1_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I16 var_1)) var_1_lst))) ->
		fun_vunop_ (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 v_M vunop_Jnn_N_ABS) v128_1 [::v128]
	| fun_vunop__case_4 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)), 
		List.Forall (fun (lane_1_13 : lane_) => ((proj_lane__2 lane_1_13) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_13 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (ineg_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_13))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_15 : lane_) => ((proj_lane__2 lane_1_15) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_1_15 : lane_) => (mk_lane__2 Jnn_I32 (ineg_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_15)))))) lane_1_lst))) ->
		fun_vunop_ (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 v_M vunop_Jnn_N_NEG) v128_1 [::v128]
	| fun_vunop__case_5 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)), 
		List.Forall (fun (lane_1_16 : lane_) => ((proj_lane__2 lane_1_16) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_16 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (ineg_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_16))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_18 : lane_) => ((proj_lane__2 lane_1_18) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_1_18 : lane_) => (mk_lane__2 Jnn_I64 (ineg_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_18)))))) lane_1_lst))) ->
		fun_vunop_ (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 v_M vunop_Jnn_N_NEG) v128_1 [::v128]
	| fun_vunop__case_6 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)), 
		List.Forall (fun (lane_1_19 : lane_) => ((proj_lane__2 lane_1_19) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_19 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (ineg_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_19))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_21 : lane_) => ((proj_lane__2 lane_1_21) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_1_21 : lane_) => (mk_lane__2 Jnn_I8 (ineg_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_21)))))) lane_1_lst))) ->
		fun_vunop_ (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 v_M vunop_Jnn_N_NEG) v128_1 [::v128]
	| fun_vunop__case_7 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)), 
		List.Forall (fun (lane_1_22 : lane_) => ((proj_lane__2 lane_1_22) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_22 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (ineg_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_22))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_24 : lane_) => ((proj_lane__2 lane_1_24) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_1_24 : lane_) => (mk_lane__2 Jnn_I16 (ineg_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_24)))))) lane_1_lst))) ->
		fun_vunop_ (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 v_M vunop_Jnn_N_NEG) v128_1 [::v128]
	| fun_vunop__case_8 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)), 
		List.Forall (fun (lane_1_25 : lane_) => ((proj_lane__2 lane_1_25) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_25 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_25))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_27 : lane_) => ((proj_lane__2 lane_1_27) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_1_27 : lane_) => (mk_lane__2 Jnn_I32 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_27)))))) lane_1_lst))) ->
		fun_vunop_ (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 v_M vunop_Jnn_N_POPCNT) v128_1 [::v128]
	| fun_vunop__case_9 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)), 
		List.Forall (fun (lane_1_28 : lane_) => ((proj_lane__2 lane_1_28) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_28 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_28))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_30 : lane_) => ((proj_lane__2 lane_1_30) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_1_30 : lane_) => (mk_lane__2 Jnn_I64 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_30)))))) lane_1_lst))) ->
		fun_vunop_ (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 v_M vunop_Jnn_N_POPCNT) v128_1 [::v128]
	| fun_vunop__case_10 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)), 
		List.Forall (fun (lane_1_31 : lane_) => ((proj_lane__2 lane_1_31) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_31 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_31))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_33 : lane_) => ((proj_lane__2 lane_1_33) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_1_33 : lane_) => (mk_lane__2 Jnn_I8 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_33)))))) lane_1_lst))) ->
		fun_vunop_ (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 v_M vunop_Jnn_N_POPCNT) v128_1 [::v128]
	| fun_vunop__case_11 : forall (v_M : nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (seq lane_)), 
		List.Forall (fun (lane_1_34 : lane_) => ((proj_lane__2 lane_1_34) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_34 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_34))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		List.Forall (fun (lane_1_36 : lane_) => ((proj_lane__2 lane_1_36) != None)) lane_1_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_1_36 : lane_) => (mk_lane__2 Jnn_I16 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_36)))))) lane_1_lst))) ->
		fun_vunop_ (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 v_M vunop_Jnn_N_POPCNT) v128_1 [::v128]
	| fun_vunop__case_12 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_1 : (seq lane_)) => List.Forall (fun (lane_1 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_1)) lane_lst_1) lane_lst_lst ->
		List.Forall (fun (lane_1_37 : lane_) => List.Forall (fun (iter_0_97 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_97)))) (fabs_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_37)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_39 : lane_) => (seq.map (fun (iter_0_98 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_98))) (fabs_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_39))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_3 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_3)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_ABS) v128_1 v128_lst
	| fun_vunop__case_13 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_4 : (seq lane_)) => List.Forall (fun (lane_4 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_4)) lane_lst_4) lane_lst_lst ->
		List.Forall (fun (lane_1_40 : lane_) => List.Forall (fun (iter_0_99 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_99)))) (fabs_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_40)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_42 : lane_) => (seq.map (fun (iter_0_100 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_100))) (fabs_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_42))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_6 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_6)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_ABS) v128_1 v128_lst
	| fun_vunop__case_14 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_7 : (seq lane_)) => List.Forall (fun (lane_7 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_7)) lane_lst_7) lane_lst_lst ->
		List.Forall (fun (lane_1_43 : lane_) => List.Forall (fun (iter_0_101 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_101)))) (fneg_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_43)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_45 : lane_) => (seq.map (fun (iter_0_102 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_102))) (fneg_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_45))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_9 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_9)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_NEG) v128_1 v128_lst
	| fun_vunop__case_15 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_10 : (seq lane_)) => List.Forall (fun (lane_10 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_10)) lane_lst_10) lane_lst_lst ->
		List.Forall (fun (lane_1_46 : lane_) => List.Forall (fun (iter_0_103 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_103)))) (fneg_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_46)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_48 : lane_) => (seq.map (fun (iter_0_104 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_104))) (fneg_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_48))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_12 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_12)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_NEG) v128_1 v128_lst
	| fun_vunop__case_16 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_13 : (seq lane_)) => List.Forall (fun (lane_13 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_13)) lane_lst_13) lane_lst_lst ->
		List.Forall (fun (lane_1_49 : lane_) => List.Forall (fun (iter_0_105 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_105)))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_49)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_51 : lane_) => (seq.map (fun (iter_0_106 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_106))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_51))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_15 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_15)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_SQRT) v128_1 v128_lst
	| fun_vunop__case_17 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_16 : (seq lane_)) => List.Forall (fun (lane_16 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_16)) lane_lst_16) lane_lst_lst ->
		List.Forall (fun (lane_1_52 : lane_) => List.Forall (fun (iter_0_107 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_107)))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_52)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_54 : lane_) => (seq.map (fun (iter_0_108 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_108))) (fsqrt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_54))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_18 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_18)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_SQRT) v128_1 v128_lst
	| fun_vunop__case_18 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_19 : (seq lane_)) => List.Forall (fun (lane_19 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_19)) lane_lst_19) lane_lst_lst ->
		List.Forall (fun (lane_1_55 : lane_) => List.Forall (fun (iter_0_109 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_109)))) (fceil_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_55)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_57 : lane_) => (seq.map (fun (iter_0_110 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_110))) (fceil_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_57))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_21 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_21)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_CEIL) v128_1 v128_lst
	| fun_vunop__case_19 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_22 : (seq lane_)) => List.Forall (fun (lane_22 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_22)) lane_lst_22) lane_lst_lst ->
		List.Forall (fun (lane_1_58 : lane_) => List.Forall (fun (iter_0_111 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_111)))) (fceil_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_58)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_60 : lane_) => (seq.map (fun (iter_0_112 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_112))) (fceil_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_60))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_24 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_24)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_CEIL) v128_1 v128_lst
	| fun_vunop__case_20 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_25 : (seq lane_)) => List.Forall (fun (lane_25 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_25)) lane_lst_25) lane_lst_lst ->
		List.Forall (fun (lane_1_61 : lane_) => List.Forall (fun (iter_0_113 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_113)))) (ffloor_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_61)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_63 : lane_) => (seq.map (fun (iter_0_114 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_114))) (ffloor_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_63))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_27 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_27)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_FLOOR) v128_1 v128_lst
	| fun_vunop__case_21 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_28 : (seq lane_)) => List.Forall (fun (lane_28 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_28)) lane_lst_28) lane_lst_lst ->
		List.Forall (fun (lane_1_64 : lane_) => List.Forall (fun (iter_0_115 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_115)))) (ffloor_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_64)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_66 : lane_) => (seq.map (fun (iter_0_116 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_116))) (ffloor_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_66))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_30 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_30)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_FLOOR) v128_1 v128_lst
	| fun_vunop__case_22 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_31 : (seq lane_)) => List.Forall (fun (lane_31 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_31)) lane_lst_31) lane_lst_lst ->
		List.Forall (fun (lane_1_67 : lane_) => List.Forall (fun (iter_0_117 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_117)))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_67)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_69 : lane_) => (seq.map (fun (iter_0_118 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_118))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_69))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_33 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_33)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_TRUNC) v128_1 v128_lst
	| fun_vunop__case_23 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_34 : (seq lane_)) => List.Forall (fun (lane_34 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_34)) lane_lst_34) lane_lst_lst ->
		List.Forall (fun (lane_1_70 : lane_) => List.Forall (fun (iter_0_119 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_119)))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_70)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_72 : lane_) => (seq.map (fun (iter_0_120 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_120))) (ftrunc_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_72))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_36 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_36)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_TRUNC) v128_1 v128_lst
	| fun_vunop__case_24 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_37 : (seq lane_)) => List.Forall (fun (lane_37 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_37)) lane_lst_37) lane_lst_lst ->
		List.Forall (fun (lane_1_73 : lane_) => List.Forall (fun (iter_0_121 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_121)))) (fnearest_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_73)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_75 : lane_) => (seq.map (fun (iter_0_122 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_122))) (fnearest_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_75))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_39 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_39)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_NEAREST) v128_1 v128_lst
	| fun_vunop__case_25 : forall (v_M : nat) (v128_1 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_40 : (seq lane_)) => List.Forall (fun (lane_40 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_40)) lane_lst_40) lane_lst_lst ->
		List.Forall (fun (lane_1_76 : lane_) => List.Forall (fun (iter_0_123 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_123)))) (fnearest_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_76)))))))) lane_1_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_lst_lst == (setproduct_ lane_ (seq.map (fun (lane_1_78 : lane_) => (seq.map (fun (iter_0_124 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_124))) (fnearest_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_78))))))))) lane_1_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_42 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_42)) lane_lst_lst)) ->
		fun_vunop_ (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_NEAREST) v128_1 v128_lst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 *)
Inductive fun_vbinop_ : shape -> vbinop_ -> vec_ -> vec_ -> (seq vec_) -> Prop :=
	| fun_vbinop__case_0 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_79 : lane_) => ((proj_lane__2 lane_1_79) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_1 : lane_) => ((proj_lane__2 lane_2_1) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_79 : lane_) (lane_2_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iadd_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_79))) (!((proj_lane__2 lane_2_1))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_81 : lane_) => ((proj_lane__2 lane_1_81) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_3 : lane_) => ((proj_lane__2 lane_2_3) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_81 : lane_) (lane_2_3 : lane_) => (mk_lane__2 Jnn_I32 (iadd_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_81))) (!((proj_lane__2 lane_2_3)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M vbinop_Jnn_N_ADD) v128_1 v128_2 [::v128]
	| fun_vbinop__case_1 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_82 : lane_) => ((proj_lane__2 lane_1_82) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_4 : lane_) => ((proj_lane__2 lane_2_4) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_82 : lane_) (lane_2_4 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iadd_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_82))) (!((proj_lane__2 lane_2_4))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_84 : lane_) => ((proj_lane__2 lane_1_84) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_6 : lane_) => ((proj_lane__2 lane_2_6) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_84 : lane_) (lane_2_6 : lane_) => (mk_lane__2 Jnn_I64 (iadd_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_84))) (!((proj_lane__2 lane_2_6)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M vbinop_Jnn_N_ADD) v128_1 v128_2 [::v128]
	| fun_vbinop__case_2 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_85 : lane_) => ((proj_lane__2 lane_1_85) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_7 : lane_) => ((proj_lane__2 lane_2_7) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_85 : lane_) (lane_2_7 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iadd_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_85))) (!((proj_lane__2 lane_2_7))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_87 : lane_) => ((proj_lane__2 lane_1_87) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_9 : lane_) => ((proj_lane__2 lane_2_9) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_87 : lane_) (lane_2_9 : lane_) => (mk_lane__2 Jnn_I8 (iadd_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_87))) (!((proj_lane__2 lane_2_9)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M vbinop_Jnn_N_ADD) v128_1 v128_2 [::v128]
	| fun_vbinop__case_3 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_88 : lane_) => ((proj_lane__2 lane_1_88) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_10 : lane_) => ((proj_lane__2 lane_2_10) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_88 : lane_) (lane_2_10 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iadd_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_88))) (!((proj_lane__2 lane_2_10))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_90 : lane_) => ((proj_lane__2 lane_1_90) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_12 : lane_) => ((proj_lane__2 lane_2_12) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_90 : lane_) (lane_2_12 : lane_) => (mk_lane__2 Jnn_I16 (iadd_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_90))) (!((proj_lane__2 lane_2_12)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M vbinop_Jnn_N_ADD) v128_1 v128_2 [::v128]
	| fun_vbinop__case_4 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_91 : lane_) => ((proj_lane__2 lane_1_91) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_13 : lane_) => ((proj_lane__2 lane_2_13) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_91 : lane_) (lane_2_13 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (isub_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_91))) (!((proj_lane__2 lane_2_13))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_93 : lane_) => ((proj_lane__2 lane_1_93) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_15 : lane_) => ((proj_lane__2 lane_2_15) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_93 : lane_) (lane_2_15 : lane_) => (mk_lane__2 Jnn_I32 (isub_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_93))) (!((proj_lane__2 lane_2_15)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M vbinop_Jnn_N_SUB) v128_1 v128_2 [::v128]
	| fun_vbinop__case_5 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_94 : lane_) => ((proj_lane__2 lane_1_94) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_16 : lane_) => ((proj_lane__2 lane_2_16) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_94 : lane_) (lane_2_16 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (isub_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_94))) (!((proj_lane__2 lane_2_16))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_96 : lane_) => ((proj_lane__2 lane_1_96) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_18 : lane_) => ((proj_lane__2 lane_2_18) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_96 : lane_) (lane_2_18 : lane_) => (mk_lane__2 Jnn_I64 (isub_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_96))) (!((proj_lane__2 lane_2_18)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M vbinop_Jnn_N_SUB) v128_1 v128_2 [::v128]
	| fun_vbinop__case_6 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_97 : lane_) => ((proj_lane__2 lane_1_97) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_19 : lane_) => ((proj_lane__2 lane_2_19) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_97 : lane_) (lane_2_19 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (isub_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_97))) (!((proj_lane__2 lane_2_19))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_99 : lane_) => ((proj_lane__2 lane_1_99) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_21 : lane_) => ((proj_lane__2 lane_2_21) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_99 : lane_) (lane_2_21 : lane_) => (mk_lane__2 Jnn_I8 (isub_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_99))) (!((proj_lane__2 lane_2_21)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M vbinop_Jnn_N_SUB) v128_1 v128_2 [::v128]
	| fun_vbinop__case_7 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_100 : lane_) => ((proj_lane__2 lane_1_100) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_22 : lane_) => ((proj_lane__2 lane_2_22) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_100 : lane_) (lane_2_22 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (isub_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_100))) (!((proj_lane__2 lane_2_22))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_102 : lane_) => ((proj_lane__2 lane_1_102) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_24 : lane_) => ((proj_lane__2 lane_2_24) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_102 : lane_) (lane_2_24 : lane_) => (mk_lane__2 Jnn_I16 (isub_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_102))) (!((proj_lane__2 lane_2_24)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M vbinop_Jnn_N_SUB) v128_1 v128_2 [::v128]
	| fun_vbinop__case_8 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_105 : lane_) => ((proj_lane__2 lane_1_105) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_27 : lane_) => ((proj_lane__2 lane_2_27) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_105 : lane_) (lane_2_27 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_105))) (!((proj_lane__2 lane_2_27))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_103 : lane_) => ((proj_lane__2 lane_1_103) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_25 : lane_) => ((proj_lane__2 lane_2_25) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_103 : lane_) (lane_2_25 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_103))) (!((proj_lane__2 lane_2_25))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I32 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_9 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_108 : lane_) => ((proj_lane__2 lane_1_108) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_30 : lane_) => ((proj_lane__2 lane_2_30) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_108 : lane_) (lane_2_30 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_108))) (!((proj_lane__2 lane_2_30))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_106 : lane_) => ((proj_lane__2 lane_1_106) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_28 : lane_) => ((proj_lane__2 lane_2_28) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_106 : lane_) (lane_2_28 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_106))) (!((proj_lane__2 lane_2_28))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I64 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_10 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_111 : lane_) => ((proj_lane__2 lane_1_111) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_33 : lane_) => ((proj_lane__2 lane_2_33) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_111 : lane_) (lane_2_33 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_111))) (!((proj_lane__2 lane_2_33))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_109 : lane_) => ((proj_lane__2 lane_1_109) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_31 : lane_) => ((proj_lane__2 lane_2_31) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_109 : lane_) (lane_2_31 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_109))) (!((proj_lane__2 lane_2_31))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I8 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_11 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_114 : lane_) => ((proj_lane__2 lane_1_114) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_36 : lane_) => ((proj_lane__2 lane_2_36) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_114 : lane_) (lane_2_36 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_114))) (!((proj_lane__2 lane_2_36))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_112 : lane_) => ((proj_lane__2 lane_1_112) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_34 : lane_) => ((proj_lane__2 lane_2_34) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_112 : lane_) (lane_2_34 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_112))) (!((proj_lane__2 lane_2_34))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I16 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_12 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_117 : lane_) => ((proj_lane__2 lane_1_117) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_39 : lane_) => ((proj_lane__2 lane_2_39) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_117 : lane_) (lane_2_39 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_117))) (!((proj_lane__2 lane_2_39))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_115 : lane_) => ((proj_lane__2 lane_1_115) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_37 : lane_) => ((proj_lane__2 lane_2_37) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_115 : lane_) (lane_2_37 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_115))) (!((proj_lane__2 lane_2_37))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I32 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_13 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_120 : lane_) => ((proj_lane__2 lane_1_120) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_42 : lane_) => ((proj_lane__2 lane_2_42) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_120 : lane_) (lane_2_42 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_120))) (!((proj_lane__2 lane_2_42))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_118 : lane_) => ((proj_lane__2 lane_1_118) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_40 : lane_) => ((proj_lane__2 lane_2_40) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_118 : lane_) (lane_2_40 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_118))) (!((proj_lane__2 lane_2_40))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I64 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_14 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_123 : lane_) => ((proj_lane__2 lane_1_123) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_45 : lane_) => ((proj_lane__2 lane_2_45) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_123 : lane_) (lane_2_45 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_123))) (!((proj_lane__2 lane_2_45))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_121 : lane_) => ((proj_lane__2 lane_1_121) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_43 : lane_) => ((proj_lane__2 lane_2_43) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_121 : lane_) (lane_2_43 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_121))) (!((proj_lane__2 lane_2_43))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I8 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_15 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_126 : lane_) => ((proj_lane__2 lane_1_126) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_48 : lane_) => ((proj_lane__2 lane_2_48) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_126 : lane_) (lane_2_48 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_126))) (!((proj_lane__2 lane_2_48))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_124 : lane_) => ((proj_lane__2 lane_1_124) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_46 : lane_) => ((proj_lane__2 lane_2_46) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_124 : lane_) (lane_2_46 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_124))) (!((proj_lane__2 lane_2_46))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I16 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_16 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_129 : lane_) => ((proj_lane__2 lane_1_129) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_51 : lane_) => ((proj_lane__2 lane_2_51) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_129 : lane_) (lane_2_51 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_129))) (!((proj_lane__2 lane_2_51))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_127 : lane_) => ((proj_lane__2 lane_1_127) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_49 : lane_) => ((proj_lane__2 lane_2_49) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_127 : lane_) (lane_2_49 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_127))) (!((proj_lane__2 lane_2_49))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I32 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M (ADD_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_17 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_132 : lane_) => ((proj_lane__2 lane_1_132) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_54 : lane_) => ((proj_lane__2 lane_2_54) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_132 : lane_) (lane_2_54 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_132))) (!((proj_lane__2 lane_2_54))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_130 : lane_) => ((proj_lane__2 lane_1_130) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_52 : lane_) => ((proj_lane__2 lane_2_52) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_130 : lane_) (lane_2_52 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_130))) (!((proj_lane__2 lane_2_52))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I64 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M (ADD_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_18 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_135 : lane_) => ((proj_lane__2 lane_1_135) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_57 : lane_) => ((proj_lane__2 lane_2_57) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_135 : lane_) (lane_2_57 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_135))) (!((proj_lane__2 lane_2_57))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_133 : lane_) => ((proj_lane__2 lane_1_133) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_55 : lane_) => ((proj_lane__2 lane_2_55) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_133 : lane_) (lane_2_55 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_133))) (!((proj_lane__2 lane_2_55))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I8 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M (ADD_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_19 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_138 : lane_) => ((proj_lane__2 lane_1_138) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_60 : lane_) => ((proj_lane__2 lane_2_60) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_138 : lane_) (lane_2_60 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_138))) (!((proj_lane__2 lane_2_60))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_136 : lane_) => ((proj_lane__2 lane_1_136) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_58 : lane_) => ((proj_lane__2 lane_2_58) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_136 : lane_) (lane_2_58 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_136))) (!((proj_lane__2 lane_2_58))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I16 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M (ADD_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_20 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_141 : lane_) => ((proj_lane__2 lane_1_141) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_63 : lane_) => ((proj_lane__2 lane_2_63) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_141 : lane_) (lane_2_63 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_141))) (!((proj_lane__2 lane_2_63))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_139 : lane_) => ((proj_lane__2 lane_1_139) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_61 : lane_) => ((proj_lane__2 lane_2_61) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_139 : lane_) (lane_2_61 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_139))) (!((proj_lane__2 lane_2_61))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I32 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M (SUB_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_21 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_144 : lane_) => ((proj_lane__2 lane_1_144) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_66 : lane_) => ((proj_lane__2 lane_2_66) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_144 : lane_) (lane_2_66 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_144))) (!((proj_lane__2 lane_2_66))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_142 : lane_) => ((proj_lane__2 lane_1_142) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_64 : lane_) => ((proj_lane__2 lane_2_64) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_142 : lane_) (lane_2_64 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_142))) (!((proj_lane__2 lane_2_64))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I64 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M (SUB_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_22 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_147 : lane_) => ((proj_lane__2 lane_1_147) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_69 : lane_) => ((proj_lane__2 lane_2_69) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_147 : lane_) (lane_2_69 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_147))) (!((proj_lane__2 lane_2_69))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_145 : lane_) => ((proj_lane__2 lane_1_145) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_67 : lane_) => ((proj_lane__2 lane_2_67) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_145 : lane_) (lane_2_67 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_145))) (!((proj_lane__2 lane_2_67))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I8 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M (SUB_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_23 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (var_1_lst : (seq uN)) (var_0_lst : (seq uN)), 
		((|var_1_lst|) == (|lane_1_lst|)) ->
		((|var_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_150 : lane_) => ((proj_lane__2 lane_1_150) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_72 : lane_) => ((proj_lane__2 lane_2_72) != None)) lane_2_lst ->
		List_Forall3 (fun (var_1 : uN) (lane_1_150 : lane_) (lane_2_72 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_150))) (!((proj_lane__2 lane_2_72))) var_1)) var_1_lst lane_1_lst lane_2_lst ->
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_148 : lane_) => ((proj_lane__2 lane_1_148) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_70 : lane_) => ((proj_lane__2 lane_2_70) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_148 : lane_) (lane_2_70 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_148))) (!((proj_lane__2 lane_2_70))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_0))) var_0_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (var_1 : uN) => (mk_lane__2 Jnn_I16 var_1)) var_1_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M (SUB_SAT v_sx)) v128_1 v128_2 [::v128]
	| fun_vbinop__case_24 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_151 : lane_) => ((proj_lane__2 lane_1_151) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_73 : lane_) => ((proj_lane__2 lane_2_73) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_151 : lane_) (lane_2_73 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (imul_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_151))) (!((proj_lane__2 lane_2_73))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_153 : lane_) => ((proj_lane__2 lane_1_153) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_75 : lane_) => ((proj_lane__2 lane_2_75) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_153 : lane_) (lane_2_75 : lane_) => (mk_lane__2 Jnn_I32 (imul_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_153))) (!((proj_lane__2 lane_2_75)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M vbinop_Jnn_N_MUL) v128_1 v128_2 [::v128]
	| fun_vbinop__case_25 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_154 : lane_) => ((proj_lane__2 lane_1_154) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_76 : lane_) => ((proj_lane__2 lane_2_76) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_154 : lane_) (lane_2_76 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (imul_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_154))) (!((proj_lane__2 lane_2_76))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_156 : lane_) => ((proj_lane__2 lane_1_156) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_78 : lane_) => ((proj_lane__2 lane_2_78) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_156 : lane_) (lane_2_78 : lane_) => (mk_lane__2 Jnn_I64 (imul_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_156))) (!((proj_lane__2 lane_2_78)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M vbinop_Jnn_N_MUL) v128_1 v128_2 [::v128]
	| fun_vbinop__case_26 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_157 : lane_) => ((proj_lane__2 lane_1_157) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_79 : lane_) => ((proj_lane__2 lane_2_79) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_157 : lane_) (lane_2_79 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (imul_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_157))) (!((proj_lane__2 lane_2_79))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_159 : lane_) => ((proj_lane__2 lane_1_159) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_81 : lane_) => ((proj_lane__2 lane_2_81) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_159 : lane_) (lane_2_81 : lane_) => (mk_lane__2 Jnn_I8 (imul_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_159))) (!((proj_lane__2 lane_2_81)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M vbinop_Jnn_N_MUL) v128_1 v128_2 [::v128]
	| fun_vbinop__case_27 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_160 : lane_) => ((proj_lane__2 lane_1_160) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_82 : lane_) => ((proj_lane__2 lane_2_82) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_160 : lane_) (lane_2_82 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (imul_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_160))) (!((proj_lane__2 lane_2_82))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_162 : lane_) => ((proj_lane__2 lane_1_162) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_84 : lane_) => ((proj_lane__2 lane_2_84) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_162 : lane_) (lane_2_84 : lane_) => (mk_lane__2 Jnn_I16 (imul_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_162))) (!((proj_lane__2 lane_2_84)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M vbinop_Jnn_N_MUL) v128_1 v128_2 [::v128]
	| fun_vbinop__case_28 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_163 : lane_) => ((proj_lane__2 lane_1_163) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_85 : lane_) => ((proj_lane__2 lane_2_85) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_163 : lane_) (lane_2_85 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I32)) U (!((proj_lane__2 lane_1_163))) (!((proj_lane__2 lane_2_85))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_165 : lane_) => ((proj_lane__2 lane_1_165) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_87 : lane_) => ((proj_lane__2 lane_2_87) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_165 : lane_) (lane_2_87 : lane_) => (mk_lane__2 Jnn_I32 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I32)) U (!((proj_lane__2 lane_1_165))) (!((proj_lane__2 lane_2_87)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M AVGRU) v128_1 v128_2 [::v128]
	| fun_vbinop__case_29 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_166 : lane_) => ((proj_lane__2 lane_1_166) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_88 : lane_) => ((proj_lane__2 lane_2_88) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_166 : lane_) (lane_2_88 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I64)) U (!((proj_lane__2 lane_1_166))) (!((proj_lane__2 lane_2_88))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_168 : lane_) => ((proj_lane__2 lane_1_168) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_90 : lane_) => ((proj_lane__2 lane_2_90) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_168 : lane_) (lane_2_90 : lane_) => (mk_lane__2 Jnn_I64 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I64)) U (!((proj_lane__2 lane_1_168))) (!((proj_lane__2 lane_2_90)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M AVGRU) v128_1 v128_2 [::v128]
	| fun_vbinop__case_30 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_169 : lane_) => ((proj_lane__2 lane_1_169) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_91 : lane_) => ((proj_lane__2 lane_2_91) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_169 : lane_) (lane_2_91 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I8)) U (!((proj_lane__2 lane_1_169))) (!((proj_lane__2 lane_2_91))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_171 : lane_) => ((proj_lane__2 lane_1_171) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_93 : lane_) => ((proj_lane__2 lane_2_93) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_171 : lane_) (lane_2_93 : lane_) => (mk_lane__2 Jnn_I8 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I8)) U (!((proj_lane__2 lane_1_171))) (!((proj_lane__2 lane_2_93)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M AVGRU) v128_1 v128_2 [::v128]
	| fun_vbinop__case_31 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_172 : lane_) => ((proj_lane__2 lane_1_172) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_94 : lane_) => ((proj_lane__2 lane_2_94) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_172 : lane_) (lane_2_94 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I16)) U (!((proj_lane__2 lane_1_172))) (!((proj_lane__2 lane_2_94))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_174 : lane_) => ((proj_lane__2 lane_1_174) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_96 : lane_) => ((proj_lane__2 lane_2_96) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_174 : lane_) (lane_2_96 : lane_) => (mk_lane__2 Jnn_I16 (iavgr_ (lsizenn (lanetype_Jnn Jnn_I16)) U (!((proj_lane__2 lane_1_174))) (!((proj_lane__2 lane_2_96)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M AVGRU) v128_1 v128_2 [::v128]
	| fun_vbinop__case_32 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_175 : lane_) => ((proj_lane__2 lane_1_175) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_97 : lane_) => ((proj_lane__2 lane_2_97) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_175 : lane_) (lane_2_97 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) res_S (!((proj_lane__2 lane_1_175))) (!((proj_lane__2 lane_2_97))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_177 : lane_) => ((proj_lane__2 lane_1_177) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_99 : lane_) => ((proj_lane__2 lane_2_99) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (fun (lane_1_177 : lane_) (lane_2_99 : lane_) => (mk_lane__2 Jnn_I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I32)) res_S (!((proj_lane__2 lane_1_177))) (!((proj_lane__2 lane_2_99)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M Q15MULR_SATS) v128_1 v128_2 [::v128]
	| fun_vbinop__case_33 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_178 : lane_) => ((proj_lane__2 lane_1_178) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_100 : lane_) => ((proj_lane__2 lane_2_100) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_178 : lane_) (lane_2_100 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) res_S (!((proj_lane__2 lane_1_178))) (!((proj_lane__2 lane_2_100))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_180 : lane_) => ((proj_lane__2 lane_1_180) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_102 : lane_) => ((proj_lane__2 lane_2_102) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (fun (lane_1_180 : lane_) (lane_2_102 : lane_) => (mk_lane__2 Jnn_I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I64)) res_S (!((proj_lane__2 lane_1_180))) (!((proj_lane__2 lane_2_102)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M Q15MULR_SATS) v128_1 v128_2 [::v128]
	| fun_vbinop__case_34 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_181 : lane_) => ((proj_lane__2 lane_1_181) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_103 : lane_) => ((proj_lane__2 lane_2_103) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_181 : lane_) (lane_2_103 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) res_S (!((proj_lane__2 lane_1_181))) (!((proj_lane__2 lane_2_103))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_183 : lane_) => ((proj_lane__2 lane_1_183) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_105 : lane_) => ((proj_lane__2 lane_2_105) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (fun (lane_1_183 : lane_) (lane_2_105 : lane_) => (mk_lane__2 Jnn_I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I8)) res_S (!((proj_lane__2 lane_1_183))) (!((proj_lane__2 lane_2_105)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M Q15MULR_SATS) v128_1 v128_2 [::v128]
	| fun_vbinop__case_35 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)), 
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_184 : lane_) => ((proj_lane__2 lane_1_184) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_106 : lane_) => ((proj_lane__2 lane_2_106) != None)) lane_2_lst ->
		List.Forall2 (fun (lane_1_184 : lane_) (lane_2_106 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) res_S (!((proj_lane__2 lane_1_184))) (!((proj_lane__2 lane_2_106))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_186 : lane_) => ((proj_lane__2 lane_1_186) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_108 : lane_) => ((proj_lane__2 lane_2_108) != None)) lane_2_lst ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (fun (lane_1_186 : lane_) (lane_2_108 : lane_) => (mk_lane__2 Jnn_I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn_I16)) res_S (!((proj_lane__2 lane_1_186))) (!((proj_lane__2 lane_2_108)))))) lane_1_lst lane_2_lst))) ->
		fun_vbinop_ (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M Q15MULR_SATS) v128_1 v128_2 [::v128]
	| fun_vbinop__case_36 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_43 : (seq lane_)) => List.Forall (fun (lane_43 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_43)) lane_lst_43) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_187 : lane_) (lane_2_109 : lane_) => List.Forall (fun (iter_0_125 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_125)))) (fadd_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_187)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_109)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_189 : lane_) (lane_2_111 : lane_) => (seq.map (fun (iter_0_126 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_126))) (fadd_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_189)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_111))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_45 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_45)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_ADD) v128_1 v128_2 v128_lst
	| fun_vbinop__case_37 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_46 : (seq lane_)) => List.Forall (fun (lane_46 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_46)) lane_lst_46) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_190 : lane_) (lane_2_112 : lane_) => List.Forall (fun (iter_0_127 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_127)))) (fadd_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_190)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_112)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_192 : lane_) (lane_2_114 : lane_) => (seq.map (fun (iter_0_128 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_128))) (fadd_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_192)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_114))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_48 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_48)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_ADD) v128_1 v128_2 v128_lst
	| fun_vbinop__case_38 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_49 : (seq lane_)) => List.Forall (fun (lane_49 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_49)) lane_lst_49) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_193 : lane_) (lane_2_115 : lane_) => List.Forall (fun (iter_0_129 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_129)))) (fsub_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_193)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_115)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_195 : lane_) (lane_2_117 : lane_) => (seq.map (fun (iter_0_130 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_130))) (fsub_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_195)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_117))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_51 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_51)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_SUB) v128_1 v128_2 v128_lst
	| fun_vbinop__case_39 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_52 : (seq lane_)) => List.Forall (fun (lane_52 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_52)) lane_lst_52) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_196 : lane_) (lane_2_118 : lane_) => List.Forall (fun (iter_0_131 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_131)))) (fsub_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_196)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_118)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_198 : lane_) (lane_2_120 : lane_) => (seq.map (fun (iter_0_132 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_132))) (fsub_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_198)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_120))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_54 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_54)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_SUB) v128_1 v128_2 v128_lst
	| fun_vbinop__case_40 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_55 : (seq lane_)) => List.Forall (fun (lane_55 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_55)) lane_lst_55) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_199 : lane_) (lane_2_121 : lane_) => List.Forall (fun (iter_0_133 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_133)))) (fmul_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_199)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_121)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_201 : lane_) (lane_2_123 : lane_) => (seq.map (fun (iter_0_134 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_134))) (fmul_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_201)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_123))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_57 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_57)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_MUL) v128_1 v128_2 v128_lst
	| fun_vbinop__case_41 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_58 : (seq lane_)) => List.Forall (fun (lane_58 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_58)) lane_lst_58) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_202 : lane_) (lane_2_124 : lane_) => List.Forall (fun (iter_0_135 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_135)))) (fmul_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_202)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_124)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_204 : lane_) (lane_2_126 : lane_) => (seq.map (fun (iter_0_136 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_136))) (fmul_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_204)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_126))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_60 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_60)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_MUL) v128_1 v128_2 v128_lst
	| fun_vbinop__case_42 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_61 : (seq lane_)) => List.Forall (fun (lane_61 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_61)) lane_lst_61) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_205 : lane_) (lane_2_127 : lane_) => List.Forall (fun (iter_0_137 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_137)))) (fdiv_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_205)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_127)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_207 : lane_) (lane_2_129 : lane_) => (seq.map (fun (iter_0_138 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_138))) (fdiv_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_207)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_129))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_63 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_63)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_DIV) v128_1 v128_2 v128_lst
	| fun_vbinop__case_43 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_64 : (seq lane_)) => List.Forall (fun (lane_64 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_64)) lane_lst_64) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_208 : lane_) (lane_2_130 : lane_) => List.Forall (fun (iter_0_139 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_139)))) (fdiv_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_208)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_130)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_210 : lane_) (lane_2_132 : lane_) => (seq.map (fun (iter_0_140 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_140))) (fdiv_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_210)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_132))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_66 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_66)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_DIV) v128_1 v128_2 v128_lst
	| fun_vbinop__case_44 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_67 : (seq lane_)) => List.Forall (fun (lane_67 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_67)) lane_lst_67) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_211 : lane_) (lane_2_133 : lane_) => List.Forall (fun (iter_0_141 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_141)))) (fmin_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_211)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_133)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_213 : lane_) (lane_2_135 : lane_) => (seq.map (fun (iter_0_142 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_142))) (fmin_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_213)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_135))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_69 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_69)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_MIN) v128_1 v128_2 v128_lst
	| fun_vbinop__case_45 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_70 : (seq lane_)) => List.Forall (fun (lane_70 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_70)) lane_lst_70) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_214 : lane_) (lane_2_136 : lane_) => List.Forall (fun (iter_0_143 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_143)))) (fmin_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_214)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_136)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_216 : lane_) (lane_2_138 : lane_) => (seq.map (fun (iter_0_144 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_144))) (fmin_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_216)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_138))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_72 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_72)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_MIN) v128_1 v128_2 v128_lst
	| fun_vbinop__case_46 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_73 : (seq lane_)) => List.Forall (fun (lane_73 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_73)) lane_lst_73) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_217 : lane_) (lane_2_139 : lane_) => List.Forall (fun (iter_0_145 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_145)))) (fmax_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_217)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_139)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_219 : lane_) (lane_2_141 : lane_) => (seq.map (fun (iter_0_146 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_146))) (fmax_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_219)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_141))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_75 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_75)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_MAX) v128_1 v128_2 v128_lst
	| fun_vbinop__case_47 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_76 : (seq lane_)) => List.Forall (fun (lane_76 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_76)) lane_lst_76) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_220 : lane_) (lane_2_142 : lane_) => List.Forall (fun (iter_0_147 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_147)))) (fmax_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_220)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_142)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_222 : lane_) (lane_2_144 : lane_) => (seq.map (fun (iter_0_148 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_148))) (fmax_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_222)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_144))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_78 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_78)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_MAX) v128_1 v128_2 v128_lst
	| fun_vbinop__case_48 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_79 : (seq lane_)) => List.Forall (fun (lane_79 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_79)) lane_lst_79) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_223 : lane_) (lane_2_145 : lane_) => List.Forall (fun (iter_0_149 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_149)))) (fpmin_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_223)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_145)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_225 : lane_) (lane_2_147 : lane_) => (seq.map (fun (iter_0_150 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_150))) (fpmin_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_225)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_147))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_81 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_81)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M PMIN) v128_1 v128_2 v128_lst
	| fun_vbinop__case_49 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_82 : (seq lane_)) => List.Forall (fun (lane_82 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_82)) lane_lst_82) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_226 : lane_) (lane_2_148 : lane_) => List.Forall (fun (iter_0_151 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_151)))) (fpmin_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_226)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_148)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_228 : lane_) (lane_2_150 : lane_) => (seq.map (fun (iter_0_152 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_152))) (fpmin_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_228)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_150))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_84 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_84)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M PMIN) v128_1 v128_2 v128_lst
	| fun_vbinop__case_50 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_85 : (seq lane_)) => List.Forall (fun (lane_85 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F32) lane_85)) lane_lst_85) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_229 : lane_) (lane_2_151 : lane_) => List.Forall (fun (iter_0_153 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_153)))) (fpmax_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_229)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_151)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_231 : lane_) (lane_2_153 : lane_) => (seq.map (fun (iter_0_154 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_154))) (fpmax_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_231)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_153))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_87 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_87)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M PMAX) v128_1 v128_2 v128_lst
	| fun_vbinop__case_51 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (seq vec_)) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_lst_lst : (seq (seq lane_))), 
		List.Forall (fun (lane_lst_88 : (seq lane_)) => List.Forall (fun (lane_88 : lane_) => (wf_lane_ (lanetype_Fnn Fnn_F64) lane_88)) lane_lst_88) lane_lst_lst ->
		((|lane_1_lst|) == (|lane_2_lst|)) ->
		List.Forall2 (fun (lane_1_232 : lane_) (lane_2_154 : lane_) => List.Forall (fun (iter_0_155 : fN) => (wf_lane_ (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_155)))) (fpmax_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_232)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_154)))))))) lane_1_lst lane_2_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		(lane_lst_lst == (setproduct_ lane_ (list_zipWith (fun (lane_1_234 : lane_) (lane_2_156 : lane_) => (seq.map (fun (iter_0_156 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_156))) (fpmax_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_234)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_156))))))))) lane_1_lst lane_2_lst))) ->
		(v128_lst == (seq.map (fun (lane_lst_90 : (seq lane_)) => (inv_lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_90)) lane_lst_lst)) ->
		fun_vbinop_ (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M PMAX) v128_1 v128_2 v128_lst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
Inductive fun_vrelop_ : shape -> vrelop_ -> vec_ -> vec_ -> vec_ -> Prop :=
	| fun_vrelop__case_0 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)), 
		List.Forall (fun (lane_1_235 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_1_235)) lane_1_lst ->
		List.Forall (fun (lane_2_157 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_2_157)) lane_2_lst ->
		List.Forall (fun (lane_3_1 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_1))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_237 : lane_) => ((proj_lane__2 lane_1_237) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_159 : lane_) => ((proj_lane__2 lane_2_159) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_237 : lane_) (lane_2_159 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_237))) (!((proj_lane__2 lane_2_159)))) :> nat)))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_3 : iN) => (mk_lane__2 Jnn_I32 lane_3_3)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M vrelop_Jnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_1 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)), 
		List.Forall (fun (lane_1_238 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_1_238)) lane_1_lst ->
		List.Forall (fun (lane_2_160 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_2_160)) lane_2_lst ->
		List.Forall (fun (lane_3_4 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_4))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_240 : lane_) => ((proj_lane__2 lane_1_240) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_162 : lane_) => ((proj_lane__2 lane_2_162) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_240 : lane_) (lane_2_162 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_240))) (!((proj_lane__2 lane_2_162)))) :> nat)))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_6 : iN) => (mk_lane__2 Jnn_I64 lane_3_6)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M vrelop_Jnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_2 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)), 
		List.Forall (fun (lane_1_241 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_1_241)) lane_1_lst ->
		List.Forall (fun (lane_2_163 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_2_163)) lane_2_lst ->
		List.Forall (fun (lane_3_7 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_7))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_243 : lane_) => ((proj_lane__2 lane_1_243) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_165 : lane_) => ((proj_lane__2 lane_2_165) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_243 : lane_) (lane_2_165 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_243))) (!((proj_lane__2 lane_2_165)))) :> nat)))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_9 : iN) => (mk_lane__2 Jnn_I8 lane_3_9)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M vrelop_Jnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_3 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)), 
		List.Forall (fun (lane_1_244 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_1_244)) lane_1_lst ->
		List.Forall (fun (lane_2_166 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_2_166)) lane_2_lst ->
		List.Forall (fun (lane_3_10 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_10))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_246 : lane_) => ((proj_lane__2 lane_1_246) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_168 : lane_) => ((proj_lane__2 lane_2_168) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_246 : lane_) (lane_2_168 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN ((ieq_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_246))) (!((proj_lane__2 lane_2_168)))) :> nat)))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_12 : iN) => (mk_lane__2 Jnn_I16 lane_3_12)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M vrelop_Jnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_4 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)), 
		List.Forall (fun (lane_1_247 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_1_247)) lane_1_lst ->
		List.Forall (fun (lane_2_169 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_2_169)) lane_2_lst ->
		List.Forall (fun (lane_3_13 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_13))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_249 : lane_) => ((proj_lane__2 lane_1_249) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_171 : lane_) => ((proj_lane__2 lane_2_171) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_249 : lane_) (lane_2_171 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I32)) (!((proj_lane__2 lane_1_249))) (!((proj_lane__2 lane_2_171)))) :> nat)))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_15 : iN) => (mk_lane__2 Jnn_I32 lane_3_15)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M vrelop_Jnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_5 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)), 
		List.Forall (fun (lane_1_250 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_1_250)) lane_1_lst ->
		List.Forall (fun (lane_2_172 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_2_172)) lane_2_lst ->
		List.Forall (fun (lane_3_16 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_16))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_252 : lane_) => ((proj_lane__2 lane_1_252) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_174 : lane_) => ((proj_lane__2 lane_2_174) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_252 : lane_) (lane_2_174 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I64)) (!((proj_lane__2 lane_1_252))) (!((proj_lane__2 lane_2_174)))) :> nat)))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_18 : iN) => (mk_lane__2 Jnn_I64 lane_3_18)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M vrelop_Jnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_6 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)), 
		List.Forall (fun (lane_1_253 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_1_253)) lane_1_lst ->
		List.Forall (fun (lane_2_175 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_2_175)) lane_2_lst ->
		List.Forall (fun (lane_3_19 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_19))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_255 : lane_) => ((proj_lane__2 lane_1_255) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_177 : lane_) => ((proj_lane__2 lane_2_177) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_255 : lane_) (lane_2_177 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I8)) (!((proj_lane__2 lane_1_255))) (!((proj_lane__2 lane_2_177)))) :> nat)))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_21 : iN) => (mk_lane__2 Jnn_I8 lane_3_21)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M vrelop_Jnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_7 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)), 
		List.Forall (fun (lane_1_256 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_1_256)) lane_1_lst ->
		List.Forall (fun (lane_2_178 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_2_178)) lane_2_lst ->
		List.Forall (fun (lane_3_22 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_22))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_258 : lane_) => ((proj_lane__2 lane_1_258) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_180 : lane_) => ((proj_lane__2 lane_2_180) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_258 : lane_) (lane_2_180 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN ((ine_ (lsizenn (lanetype_Jnn Jnn_I16)) (!((proj_lane__2 lane_1_258))) (!((proj_lane__2 lane_2_180)))) :> nat)))) lane_1_lst lane_2_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_24 : iN) => (mk_lane__2 Jnn_I16 lane_3_24)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M vrelop_Jnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_8 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_261 : lane_) => ((proj_lane__2 lane_1_261) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_183 : lane_) => ((proj_lane__2 lane_2_183) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_261 : lane_) (lane_2_183 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_261))) (!((proj_lane__2 lane_2_183))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_259 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_1_259)) lane_1_lst ->
		List.Forall (fun (lane_2_181 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_2_181)) lane_2_lst ->
		List.Forall (fun (lane_3_25 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_25))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_27 : iN) => (mk_lane__2 Jnn_I32 lane_3_27)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_9 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_264 : lane_) => ((proj_lane__2 lane_1_264) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_186 : lane_) => ((proj_lane__2 lane_2_186) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_264 : lane_) (lane_2_186 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_264))) (!((proj_lane__2 lane_2_186))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_262 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_1_262)) lane_1_lst ->
		List.Forall (fun (lane_2_184 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_2_184)) lane_2_lst ->
		List.Forall (fun (lane_3_28 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_28))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_30 : iN) => (mk_lane__2 Jnn_I64 lane_3_30)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_10 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_267 : lane_) => ((proj_lane__2 lane_1_267) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_189 : lane_) => ((proj_lane__2 lane_2_189) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_267 : lane_) (lane_2_189 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_267))) (!((proj_lane__2 lane_2_189))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_265 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_1_265)) lane_1_lst ->
		List.Forall (fun (lane_2_187 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_2_187)) lane_2_lst ->
		List.Forall (fun (lane_3_31 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_31))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_33 : iN) => (mk_lane__2 Jnn_I8 lane_3_33)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_11 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_270 : lane_) => ((proj_lane__2 lane_1_270) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_192 : lane_) => ((proj_lane__2 lane_2_192) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_270 : lane_) (lane_2_192 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_270))) (!((proj_lane__2 lane_2_192))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_268 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_1_268)) lane_1_lst ->
		List.Forall (fun (lane_2_190 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_2_190)) lane_2_lst ->
		List.Forall (fun (lane_3_34 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_34))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_36 : iN) => (mk_lane__2 Jnn_I16 lane_3_36)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_12 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_273 : lane_) => ((proj_lane__2 lane_1_273) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_195 : lane_) => ((proj_lane__2 lane_2_195) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_273 : lane_) (lane_2_195 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_273))) (!((proj_lane__2 lane_2_195))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_271 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_1_271)) lane_1_lst ->
		List.Forall (fun (lane_2_193 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_2_193)) lane_2_lst ->
		List.Forall (fun (lane_3_37 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_37))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_39 : iN) => (mk_lane__2 Jnn_I32 lane_3_39)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_13 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_276 : lane_) => ((proj_lane__2 lane_1_276) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_198 : lane_) => ((proj_lane__2 lane_2_198) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_276 : lane_) (lane_2_198 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_276))) (!((proj_lane__2 lane_2_198))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_274 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_1_274)) lane_1_lst ->
		List.Forall (fun (lane_2_196 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_2_196)) lane_2_lst ->
		List.Forall (fun (lane_3_40 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_40))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_42 : iN) => (mk_lane__2 Jnn_I64 lane_3_42)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_14 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_279 : lane_) => ((proj_lane__2 lane_1_279) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_201 : lane_) => ((proj_lane__2 lane_2_201) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_279 : lane_) (lane_2_201 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_279))) (!((proj_lane__2 lane_2_201))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_277 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_1_277)) lane_1_lst ->
		List.Forall (fun (lane_2_199 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_2_199)) lane_2_lst ->
		List.Forall (fun (lane_3_43 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_43))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_45 : iN) => (mk_lane__2 Jnn_I8 lane_3_45)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_15 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_282 : lane_) => ((proj_lane__2 lane_1_282) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_204 : lane_) => ((proj_lane__2 lane_2_204) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_282 : lane_) (lane_2_204 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_282))) (!((proj_lane__2 lane_2_204))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_280 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_1_280)) lane_1_lst ->
		List.Forall (fun (lane_2_202 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_2_202)) lane_2_lst ->
		List.Forall (fun (lane_3_46 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_46))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_48 : iN) => (mk_lane__2 Jnn_I16 lane_3_48)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_16 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_285 : lane_) => ((proj_lane__2 lane_1_285) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_207 : lane_) => ((proj_lane__2 lane_2_207) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_285 : lane_) (lane_2_207 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_285))) (!((proj_lane__2 lane_2_207))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_283 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_1_283)) lane_1_lst ->
		List.Forall (fun (lane_2_205 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_2_205)) lane_2_lst ->
		List.Forall (fun (lane_3_49 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_49))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_51 : iN) => (mk_lane__2 Jnn_I32 lane_3_51)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_17 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_288 : lane_) => ((proj_lane__2 lane_1_288) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_210 : lane_) => ((proj_lane__2 lane_2_210) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_288 : lane_) (lane_2_210 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_288))) (!((proj_lane__2 lane_2_210))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_286 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_1_286)) lane_1_lst ->
		List.Forall (fun (lane_2_208 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_2_208)) lane_2_lst ->
		List.Forall (fun (lane_3_52 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_52))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_54 : iN) => (mk_lane__2 Jnn_I64 lane_3_54)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_18 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_291 : lane_) => ((proj_lane__2 lane_1_291) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_213 : lane_) => ((proj_lane__2 lane_2_213) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_291 : lane_) (lane_2_213 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_291))) (!((proj_lane__2 lane_2_213))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_289 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_1_289)) lane_1_lst ->
		List.Forall (fun (lane_2_211 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_2_211)) lane_2_lst ->
		List.Forall (fun (lane_3_55 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_55))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_57 : iN) => (mk_lane__2 Jnn_I8 lane_3_57)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_19 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_294 : lane_) => ((proj_lane__2 lane_1_294) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_216 : lane_) => ((proj_lane__2 lane_2_216) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_294 : lane_) (lane_2_216 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_294))) (!((proj_lane__2 lane_2_216))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_292 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_1_292)) lane_1_lst ->
		List.Forall (fun (lane_2_214 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_2_214)) lane_2_lst ->
		List.Forall (fun (lane_3_58 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_58))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_60 : iN) => (mk_lane__2 Jnn_I16 lane_3_60)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_20 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_297 : lane_) => ((proj_lane__2 lane_1_297) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_219 : lane_) => ((proj_lane__2 lane_2_219) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_297 : lane_) (lane_2_219 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (!((proj_lane__2 lane_1_297))) (!((proj_lane__2 lane_2_219))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_295 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_1_295)) lane_1_lst ->
		List.Forall (fun (lane_2_217 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) lane_2_217)) lane_2_lst ->
		List.Forall (fun (lane_3_61 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_61))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I32)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (seq.map (fun (lane_3_63 : iN) => (mk_lane__2 Jnn_I32 lane_3_63)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_21 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_300 : lane_) => ((proj_lane__2 lane_1_300) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_222 : lane_) => ((proj_lane__2 lane_2_222) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_300 : lane_) (lane_2_222 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (!((proj_lane__2 lane_1_300))) (!((proj_lane__2 lane_2_222))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_298 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_1_298)) lane_1_lst ->
		List.Forall (fun (lane_2_220 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) lane_2_220)) lane_2_lst ->
		List.Forall (fun (lane_3_64 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_64))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I64)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (seq.map (fun (lane_3_66 : iN) => (mk_lane__2 Jnn_I64 lane_3_66)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_22 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_303 : lane_) => ((proj_lane__2 lane_1_303) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_225 : lane_) => ((proj_lane__2 lane_2_225) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_303 : lane_) (lane_2_225 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (!((proj_lane__2 lane_1_303))) (!((proj_lane__2 lane_2_225))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_301 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_1_301)) lane_1_lst ->
		List.Forall (fun (lane_2_223 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) lane_2_223)) lane_2_lst ->
		List.Forall (fun (lane_3_67 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_67))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I8)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (seq.map (fun (lane_3_69 : iN) => (mk_lane__2 Jnn_I8 lane_3_69)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_23 : forall (v_M : nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|lane_1_lst|)) ->
		((|var_0_lst|) == (|lane_2_lst|)) ->
		List.Forall (fun (lane_1_306 : lane_) => ((proj_lane__2 lane_1_306) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_228 : lane_) => ((proj_lane__2 lane_2_228) != None)) lane_2_lst ->
		List_Forall3 (fun (var_0 : uN) (lane_1_306 : lane_) (lane_2_228 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (!((proj_lane__2 lane_1_306))) (!((proj_lane__2 lane_2_228))) var_0)) var_0_lst lane_1_lst lane_2_lst ->
		List.Forall (fun (lane_1_304 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_1_304)) lane_1_lst ->
		List.Forall (fun (lane_2_226 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) lane_2_226)) lane_2_lst ->
		List.Forall (fun (lane_3_70 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_70))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ->
		(lane_3_lst == (seq.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn Jnn_I16)) res_S (mk_uN (var_0 :> nat)))) var_0_lst)) ->
		(v128 == (inv_lanes_ (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (seq.map (fun (lane_3_72 : iN) => (mk_lane__2 Jnn_I16 lane_3_72)) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128
	| fun_vrelop__case_24 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_307 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_1_307)) lane_1_lst ->
		List.Forall (fun (lane_2_229 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_2_229)) lane_2_lst ->
		List.Forall (fun (lane_3_73 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_73 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_309 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_309)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_309 : lane_) => ((proj_lane__0 lane_1_309) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_231 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_231)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_231 : lane_) => ((proj_lane__0 lane_2_231) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_309 : lane_) (lane_2_231 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((feq_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_309)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_231))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_75 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_75 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_25 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_310 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_1_310)) lane_1_lst ->
		List.Forall (fun (lane_2_232 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_2_232)) lane_2_lst ->
		List.Forall (fun (lane_3_76 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_76 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_312 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_312)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_312 : lane_) => ((proj_lane__0 lane_1_312) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_234 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_234)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_234 : lane_) => ((proj_lane__0 lane_2_234) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_312 : lane_) (lane_2_234 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((feq_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_312)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_234))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_78 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_78 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_EQ) v128_1 v128_2 v128
	| fun_vrelop__case_26 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_313 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_1_313)) lane_1_lst ->
		List.Forall (fun (lane_2_235 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_2_235)) lane_2_lst ->
		List.Forall (fun (lane_3_79 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_79 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_315 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_315)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_315 : lane_) => ((proj_lane__0 lane_1_315) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_237 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_237)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_237 : lane_) => ((proj_lane__0 lane_2_237) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_315 : lane_) (lane_2_237 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((fne_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_315)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_237))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_81 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_81 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_27 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_316 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_1_316)) lane_1_lst ->
		List.Forall (fun (lane_2_238 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_2_238)) lane_2_lst ->
		List.Forall (fun (lane_3_82 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_82 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_318 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_318)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_318 : lane_) => ((proj_lane__0 lane_1_318) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_240 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_240)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_240 : lane_) => ((proj_lane__0 lane_2_240) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_318 : lane_) (lane_2_240 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((fne_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_318)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_240))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_84 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_84 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_NE) v128_1 v128_2 v128
	| fun_vrelop__case_28 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_319 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_1_319)) lane_1_lst ->
		List.Forall (fun (lane_2_241 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_2_241)) lane_2_lst ->
		List.Forall (fun (lane_3_85 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_85 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_321 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_321)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_321 : lane_) => ((proj_lane__0 lane_1_321) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_243 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_243)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_243 : lane_) => ((proj_lane__0 lane_2_243) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_321 : lane_) (lane_2_243 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((flt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_321)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_243))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_87 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_87 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_LT) v128_1 v128_2 v128
	| fun_vrelop__case_29 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_322 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_1_322)) lane_1_lst ->
		List.Forall (fun (lane_2_244 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_2_244)) lane_2_lst ->
		List.Forall (fun (lane_3_88 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_88 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_324 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_324)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_324 : lane_) => ((proj_lane__0 lane_1_324) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_246 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_246)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_246 : lane_) => ((proj_lane__0 lane_2_246) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_324 : lane_) (lane_2_246 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((flt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_324)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_246))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_90 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_90 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_LT) v128_1 v128_2 v128
	| fun_vrelop__case_30 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_325 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_1_325)) lane_1_lst ->
		List.Forall (fun (lane_2_247 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_2_247)) lane_2_lst ->
		List.Forall (fun (lane_3_91 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_91 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_327 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_327)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_327 : lane_) => ((proj_lane__0 lane_1_327) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_249 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_249)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_249 : lane_) => ((proj_lane__0 lane_2_249) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_327 : lane_) (lane_2_249 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((fgt_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_327)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_249))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_93 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_93 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_GT) v128_1 v128_2 v128
	| fun_vrelop__case_31 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_328 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_1_328)) lane_1_lst ->
		List.Forall (fun (lane_2_250 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_2_250)) lane_2_lst ->
		List.Forall (fun (lane_3_94 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_94 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_330 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_330)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_330 : lane_) => ((proj_lane__0 lane_1_330) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_252 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_252)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_252 : lane_) => ((proj_lane__0 lane_2_252) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_330 : lane_) (lane_2_252 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((fgt_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_330)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_252))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_96 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_96 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_GT) v128_1 v128_2 v128
	| fun_vrelop__case_32 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_331 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_1_331)) lane_1_lst ->
		List.Forall (fun (lane_2_253 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_2_253)) lane_2_lst ->
		List.Forall (fun (lane_3_97 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_97 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_333 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_333)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_333 : lane_) => ((proj_lane__0 lane_1_333) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_255 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_255)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_255 : lane_) => ((proj_lane__0 lane_2_255) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_333 : lane_) (lane_2_255 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((fle_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_333)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_255))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_99 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_99 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_LE) v128_1 v128_2 v128
	| fun_vrelop__case_33 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_334 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_1_334)) lane_1_lst ->
		List.Forall (fun (lane_2_256 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_2_256)) lane_2_lst ->
		List.Forall (fun (lane_3_100 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_100 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_336 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_336)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_336 : lane_) => ((proj_lane__0 lane_1_336) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_258 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_258)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_258 : lane_) => ((proj_lane__0 lane_2_258) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_336 : lane_) (lane_2_258 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((fle_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_336)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_258))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_102 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_102 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_LE) v128_1 v128_2 v128
	| fun_vrelop__case_34 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_337 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_1_337)) lane_1_lst ->
		List.Forall (fun (lane_2_259 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) lane_2_259)) lane_2_lst ->
		List.Forall (fun (lane_3_103 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_103 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_339 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_339)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_339 : lane_) => ((proj_lane__0 lane_1_339) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_261 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_261)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_261 : lane_) => ((proj_lane__0 lane_2_261) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_339 : lane_) (lane_2_261 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F32)) res_S (mk_uN ((fge_ (sizenn (numtype_Fnn Fnn_F32)) (!((proj_num__1 (!((proj_lane__0 lane_1_339)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_261))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F32)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F32))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_105 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_105 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_GE) v128_1 v128_2 v128
	| fun_vrelop__case_35 : forall (v_M : nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (seq lane_)) (lane_2_lst : (seq lane_)) (lane_3_lst : (seq iN)) (v_Inn : Inn), 
		List.Forall (fun (lane_1_340 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_1_340)) lane_1_lst ->
		List.Forall (fun (lane_2_262 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) lane_2_262)) lane_2_lst ->
		List.Forall (fun (lane_3_106 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_106 :> nat)))))) lane_3_lst ->
		(lane_1_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ->
		(lane_2_lst == (lanes_ (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ->
		List.Forall (fun (lane_1_342 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_1_342)))) != None)) lane_1_lst ->
		List.Forall (fun (lane_1_342 : lane_) => ((proj_lane__0 lane_1_342) != None)) lane_1_lst ->
		List.Forall (fun (lane_2_264 : lane_) => ((proj_num__1 (!((proj_lane__0 lane_2_264)))) != None)) lane_2_lst ->
		List.Forall (fun (lane_2_264 : lane_) => ((proj_lane__0 lane_2_264) != None)) lane_2_lst ->
		(lane_3_lst == (list_zipWith (fun (lane_1_342 : lane_) (lane_2_264 : lane_) => (extend__ 1 (sizenn (numtype_Fnn Fnn_F64)) res_S (mk_uN ((fge_ (sizenn (numtype_Fnn Fnn_F64)) (!((proj_num__1 (!((proj_lane__0 lane_1_342)))))) (!((proj_num__1 (!((proj_lane__0 lane_2_264))))))) :> nat)))) lane_1_lst lane_2_lst)) ->
		((res_size (valtype_Fnn Fnn_F64)) != None) ->
		((isize v_Inn) == (!((res_size (valtype_Fnn Fnn_F64))))) ->
		(v128 == (inv_lanes_ (X (lanetype_Inn v_Inn) (mk_dim v_M)) (seq.map (fun (lane_3_108 : iN) => (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (lane_3_108 :> nat))))) lane_3_lst))) ->
		fun_vrelop_ (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_GE) v128_1 v128_2 v128.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.15 *)
Inductive fun_vcvtop__ : shape -> shape -> vcvtop -> lane_ -> (seq lane_) -> Prop :=
	| fun_vcvtop___case_0 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) [::(mk_lane__2 Jnn_I32 iN_2)]
	| fun_vcvtop___case_1 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) [::(mk_lane__2 Jnn_I32 iN_2)]
	| fun_vcvtop___case_2 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I8 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) [::(mk_lane__2 Jnn_I32 iN_2)]
	| fun_vcvtop___case_3 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I16 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) [::(mk_lane__2 Jnn_I32 iN_2)]
	| fun_vcvtop___case_4 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) [::(mk_lane__2 Jnn_I64 iN_2)]
	| fun_vcvtop___case_5 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) [::(mk_lane__2 Jnn_I64 iN_2)]
	| fun_vcvtop___case_6 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I8 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) [::(mk_lane__2 Jnn_I64 iN_2)]
	| fun_vcvtop___case_7 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I16 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) [::(mk_lane__2 Jnn_I64 iN_2)]
	| fun_vcvtop___case_8 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) [::(mk_lane__2 Jnn_I8 iN_2)]
	| fun_vcvtop___case_9 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) [::(mk_lane__2 Jnn_I8 iN_2)]
	| fun_vcvtop___case_10 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I8 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) [::(mk_lane__2 Jnn_I8 iN_2)]
	| fun_vcvtop___case_11 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I16 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) [::(mk_lane__2 Jnn_I8 iN_2)]
	| fun_vcvtop___case_12 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) [::(mk_lane__2 Jnn_I16 iN_2)]
	| fun_vcvtop___case_13 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) [::(mk_lane__2 Jnn_I16 iN_2)]
	| fun_vcvtop___case_14 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I8 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) [::(mk_lane__2 Jnn_I16 iN_2)]
	| fun_vcvtop___case_15 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 iN_2)) ->
		(iN_2 == (extend__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I16 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) [::(mk_lane__2 Jnn_I16 iN_2)]
	| fun_vcvtop___case_16 : forall (M_1 : nat) (M_2 : nat) (half_opt : (option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))) ->
		(fN_2 == (convert__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I32 iN_1) [::(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]
	| fun_vcvtop___case_17 : forall (M_1 : nat) (M_2 : nat) (half_opt : (option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))) ->
		(fN_2 == (convert__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I64 iN_1) [::(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]
	| fun_vcvtop___case_18 : forall (M_1 : nat) (M_2 : nat) (half_opt : (option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))) ->
		(fN_2 == (convert__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I8 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I8 iN_1) [::(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]
	| fun_vcvtop___case_19 : forall (M_1 : nat) (M_2 : nat) (half_opt : (option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))) ->
		(fN_2 == (convert__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I16 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I16 iN_1) [::(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]
	| fun_vcvtop___case_20 : forall (M_1 : nat) (M_2 : nat) (half_opt : (option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))) ->
		(fN_2 == (convert__ (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I32 iN_1) [::(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]
	| fun_vcvtop___case_21 : forall (M_1 : nat) (M_2 : nat) (half_opt : (option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))) ->
		(fN_2 == (convert__ (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I64 iN_1) [::(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]
	| fun_vcvtop___case_22 : forall (M_1 : nat) (M_2 : nat) (half_opt : (option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))) ->
		(fN_2 == (convert__ (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I8 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I8 iN_1) [::(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]
	| fun_vcvtop___case_23 : forall (M_1 : nat) (M_2 : nat) (half_opt : (option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
		(wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))) ->
		(fN_2 == (convert__ (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ->
		fun_vcvtop__ (X lanetype_I16 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I16 iN_1) [::(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]
	| fun_vcvtop___case_24 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (zero_opt : (option zero)) (fN_1 : fN) (iN_2_opt : (option iN)), 
		List.Forall (fun (iN_2_1 : iN) => (wf_lane_ (lanetype_Inn Inn_I32) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_1)))) (option_to_list iN_2_opt) ->
		(iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (list_ lane_ (option_map (fun (iN_2_3 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_3))) iN_2_opt))
	| fun_vcvtop___case_25 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (zero_opt : (option zero)) (fN_1 : fN) (iN_2_opt : (option iN)), 
		List.Forall (fun (iN_2_4 : iN) => (wf_lane_ (lanetype_Inn Inn_I32) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_4)))) (option_to_list iN_2_opt) ->
		(iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (list_ lane_ (option_map (fun (iN_2_6 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_6))) iN_2_opt))
	| fun_vcvtop___case_26 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (zero_opt : (option zero)) (fN_1 : fN) (iN_2_opt : (option iN)), 
		List.Forall (fun (iN_2_7 : iN) => (wf_lane_ (lanetype_Inn Inn_I64) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_7)))) (option_to_list iN_2_opt) ->
		(iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (list_ lane_ (option_map (fun (iN_2_9 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_9))) iN_2_opt))
	| fun_vcvtop___case_27 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (zero_opt : (option zero)) (fN_1 : fN) (iN_2_opt : (option iN)), 
		List.Forall (fun (iN_2_10 : iN) => (wf_lane_ (lanetype_Inn Inn_I64) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_10)))) (option_to_list iN_2_opt) ->
		(iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (list_ lane_ (option_map (fun (iN_2_12 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_12))) iN_2_opt))
	| fun_vcvtop___case_28 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (zero_opt : (option zero)) (fN_1 : fN) (iN_2_opt : (option iN)), 
		List.Forall (fun (iN_2_13 : iN) => (wf_lane_ (lanetype_Inn Inn_I32) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_13)))) (option_to_list iN_2_opt) ->
		(iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (list_ lane_ (option_map (fun (iN_2_15 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_15))) iN_2_opt))
	| fun_vcvtop___case_29 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (zero_opt : (option zero)) (fN_1 : fN) (iN_2_opt : (option iN)), 
		List.Forall (fun (iN_2_16 : iN) => (wf_lane_ (lanetype_Inn Inn_I32) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_16)))) (option_to_list iN_2_opt) ->
		(iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (list_ lane_ (option_map (fun (iN_2_18 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_18))) iN_2_opt))
	| fun_vcvtop___case_30 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (zero_opt : (option zero)) (fN_1 : fN) (iN_2_opt : (option iN)), 
		List.Forall (fun (iN_2_19 : iN) => (wf_lane_ (lanetype_Inn Inn_I64) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_19)))) (option_to_list iN_2_opt) ->
		(iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (list_ lane_ (option_map (fun (iN_2_21 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_21))) iN_2_opt))
	| fun_vcvtop___case_31 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (zero_opt : (option zero)) (fN_1 : fN) (iN_2_opt : (option iN)), 
		List.Forall (fun (iN_2_22 : iN) => (wf_lane_ (lanetype_Inn Inn_I64) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_22)))) (option_to_list iN_2_opt) ->
		(iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (list_ lane_ (option_map (fun (iN_2_24 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_24))) iN_2_opt))
	| fun_vcvtop___case_32 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_1 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_1)))) fN_2_lst ->
		(fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (seq.map (fun (fN_2_3 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_3))) fN_2_lst)
	| fun_vcvtop___case_33 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_4 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_4)))) fN_2_lst ->
		(fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (seq.map (fun (fN_2_6 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_6))) fN_2_lst)
	| fun_vcvtop___case_34 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_7 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_7)))) fN_2_lst ->
		(fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (seq.map (fun (fN_2_9 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_9))) fN_2_lst)
	| fun_vcvtop___case_35 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_10 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_10)))) fN_2_lst ->
		(fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (seq.map (fun (fN_2_12 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_12))) fN_2_lst)
	| fun_vcvtop___case_36 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_13 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_13)))) fN_2_lst ->
		(fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (seq.map (fun (fN_2_15 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_15))) fN_2_lst)
	| fun_vcvtop___case_37 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_16 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_16)))) fN_2_lst ->
		(fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (seq.map (fun (fN_2_18 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_18))) fN_2_lst)
	| fun_vcvtop___case_38 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_19 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_19)))) fN_2_lst ->
		(fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (seq.map (fun (fN_2_21 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_21))) fN_2_lst)
	| fun_vcvtop___case_39 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_22 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_22)))) fN_2_lst ->
		(fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (seq.map (fun (fN_2_24 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_24))) fN_2_lst)
	| fun_vcvtop___case_40 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_25 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_25)))) fN_2_lst ->
		(fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (seq.map (fun (fN_2_27 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_27))) fN_2_lst)
	| fun_vcvtop___case_41 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_28 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_28)))) fN_2_lst ->
		(fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (seq.map (fun (fN_2_30 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_30))) fN_2_lst)
	| fun_vcvtop___case_42 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_31 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_31)))) fN_2_lst ->
		(fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (seq.map (fun (fN_2_33 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_33))) fN_2_lst)
	| fun_vcvtop___case_43 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_34 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_34)))) fN_2_lst ->
		(fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (seq.map (fun (fN_2_36 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_36))) fN_2_lst)
	| fun_vcvtop___case_44 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_37 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_37)))) fN_2_lst ->
		(fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (seq.map (fun (fN_2_39 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_39))) fN_2_lst)
	| fun_vcvtop___case_45 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_40 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_40)))) fN_2_lst ->
		(fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (seq.map (fun (fN_2_42 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_42))) fN_2_lst)
	| fun_vcvtop___case_46 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_43 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_43)))) fN_2_lst ->
		(fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (seq.map (fun (fN_2_45 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_45))) fN_2_lst)
	| fun_vcvtop___case_47 : forall (M_1 : nat) (M_2 : nat) (fN_1 : fN) (fN_2_lst : (seq fN)), 
		List.Forall (fun (fN_2_46 : fN) => (wf_lane_ (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim M_2))) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_46)))) fN_2_lst ->
		(fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ->
		fun_vcvtop__ (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (seq.map (fun (fN_2_48 : fN) => (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_48))) fN_2_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 *)
Inductive fun_vextunop__ : ishape -> ishape -> vextunop_ -> vec_ -> vec_ -> Prop :=
	| fun_vextunop___case_0 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (c : uN) (ci_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1)) ci_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_1 : iN) (cj_2_1 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_1 cj_2_1))))) cj_1_lst cj_2_lst ->
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_3 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_3)))) != None)) ci_lst ->
		List.Forall (fun (ci_3 : lane_) => ((proj_lane__0 ci_3) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_2 : iN) (cj_2_2 : iN) => [::cj_1_2; cj_2_2]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_3 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_3)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_3 : iN) (cj_2_3 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_3 cj_2_3)))) cj_1_lst cj_2_lst))) ->
		fun_vextunop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_1 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (c : uN) (ci_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_4 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_4)) ci_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_4 : iN) (cj_2_4 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_4 cj_2_4))))) cj_1_lst cj_2_lst ->
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_6 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_6)))) != None)) ci_lst ->
		List.Forall (fun (ci_6 : lane_) => ((proj_lane__0 ci_6) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_5 : iN) (cj_2_5 : iN) => [::cj_1_5; cj_2_5]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_6 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_6)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_6 : iN) (cj_2_6 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_6 cj_2_6)))) cj_1_lst cj_2_lst))) ->
		fun_vextunop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_2 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (c : uN) (ci_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_7 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_7)) ci_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_7 : iN) (cj_2_7 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_7 cj_2_7))))) cj_1_lst cj_2_lst ->
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_9 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_9)))) != None)) ci_lst ->
		List.Forall (fun (ci_9 : lane_) => ((proj_lane__0 ci_9) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_8 : iN) (cj_2_8 : iN) => [::cj_1_8; cj_2_8]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_9 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_9)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_9 : iN) (cj_2_9 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_9 cj_2_9)))) cj_1_lst cj_2_lst))) ->
		fun_vextunop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_3 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (c : uN) (ci_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_10 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_10)) ci_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_10 : iN) (cj_2_10 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_10 cj_2_10))))) cj_1_lst cj_2_lst ->
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_12 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_12)))) != None)) ci_lst ->
		List.Forall (fun (ci_12 : lane_) => ((proj_lane__0 ci_12) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_11 : iN) (cj_2_11 : iN) => [::cj_1_11; cj_2_11]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_12 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_12)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_12 : iN) (cj_2_12 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_12 cj_2_12)))) cj_1_lst cj_2_lst))) ->
		fun_vextunop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_4 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (c : uN) (ci_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_13 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_13)) ci_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_13 : iN) (cj_2_13 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_13 cj_2_13))))) cj_1_lst cj_2_lst ->
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_15 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_15)))) != None)) ci_lst ->
		List.Forall (fun (ci_15 : lane_) => ((proj_lane__0 ci_15) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_14 : iN) (cj_2_14 : iN) => [::cj_1_14; cj_2_14]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_15 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_15)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_15 : iN) (cj_2_15 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_15 cj_2_15)))) cj_1_lst cj_2_lst))) ->
		fun_vextunop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_5 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (c : uN) (ci_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_16 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_16)) ci_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_16 : iN) (cj_2_16 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_16 cj_2_16))))) cj_1_lst cj_2_lst ->
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_18 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_18)))) != None)) ci_lst ->
		List.Forall (fun (ci_18 : lane_) => ((proj_lane__0 ci_18) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_17 : iN) (cj_2_17 : iN) => [::cj_1_17; cj_2_17]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_18 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_18)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_18 : iN) (cj_2_18 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_18 cj_2_18)))) cj_1_lst cj_2_lst))) ->
		fun_vextunop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_6 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (c : uN) (ci_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_19 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_19)) ci_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_19 : iN) (cj_2_19 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_19 cj_2_19))))) cj_1_lst cj_2_lst ->
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_21 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_21)))) != None)) ci_lst ->
		List.Forall (fun (ci_21 : lane_) => ((proj_lane__0 ci_21) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_20 : iN) (cj_2_20 : iN) => [::cj_1_20; cj_2_20]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_21 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_21)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_21 : iN) (cj_2_21 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_21 cj_2_21)))) cj_1_lst cj_2_lst))) ->
		fun_vextunop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1 (EXTADD_PAIRWISE v_sx)) c_1 c
	| fun_vextunop___case_7 : forall (M_1 : nat) (M_2 : nat) (v_sx : sx) (c_1 : uN) (c : uN) (ci_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_22 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_22)) ci_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_22 : iN) (cj_2_22 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_22 cj_2_22))))) cj_1_lst cj_2_lst ->
		(ci_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		List.Forall (fun (ci_24 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_24)))) != None)) ci_lst ->
		List.Forall (fun (ci_24 : lane_) => ((proj_lane__0 ci_24) != None)) ci_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_23 : iN) (cj_2_23 : iN) => [::cj_1_23; cj_2_23]) cj_1_lst cj_2_lst)) == (seq.map (fun (ci_24 : lane_) => (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_24)))))))) ci_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_24 : iN) (cj_2_24 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_24 cj_2_24)))) cj_1_lst cj_2_lst))) ->
		fun_vextunop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1 (EXTADD_PAIRWISE v_sx)) c_1 c.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 *)
Inductive fun_vextbinop__ : ishape -> ishape -> vextbinop_ -> vec_ -> vec_ -> vec_ -> Prop :=
	| fun_vextbinop___case_0 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)), 
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_1 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_1)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_1 : lane_) => ((proj_lane__0 ci_1_1) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_1 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_1)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_1 : lane_) => ((proj_lane__0 ci_2_1) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_1 : lane_) (ci_2_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_1))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_1)))))))))))) ci_1_lst ci_2_lst ->
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_3 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_3)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_3 : lane_) => ((proj_lane__0 ci_1_3) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_3 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_3)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_3 : lane_) => ((proj_lane__0 ci_2_3) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (ci_1_3 : lane_) (ci_2_3 : lane_) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_3))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_3))))))))))) ci_1_lst ci_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_1 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)), 
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_4 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_4)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_4 : lane_) => ((proj_lane__0 ci_1_4) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_4 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_4)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_4 : lane_) => ((proj_lane__0 ci_2_4) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_4 : lane_) (ci_2_4 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_4))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_4)))))))))))) ci_1_lst ci_2_lst ->
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_6 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_6)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_6 : lane_) => ((proj_lane__0 ci_1_6) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_6 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_6)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_6 : lane_) => ((proj_lane__0 ci_2_6) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (ci_1_6 : lane_) (ci_2_6 : lane_) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_6))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_6))))))))))) ci_1_lst ci_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_2 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)), 
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_7 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_7)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_7 : lane_) => ((proj_lane__0 ci_1_7) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_7 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_7)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_7 : lane_) => ((proj_lane__0 ci_2_7) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_7 : lane_) (ci_2_7 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_7))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_7)))))))))))) ci_1_lst ci_2_lst ->
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_9 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_9)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_9 : lane_) => ((proj_lane__0 ci_1_9) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_9 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_9)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_9 : lane_) => ((proj_lane__0 ci_2_9) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (ci_1_9 : lane_) (ci_2_9 : lane_) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_9))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_9))))))))))) ci_1_lst ci_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_3 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)), 
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_10 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_10)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_10 : lane_) => ((proj_lane__0 ci_1_10) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_10 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_10)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_10 : lane_) => ((proj_lane__0 ci_2_10) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_10 : lane_) (ci_2_10 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_10))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_10)))))))))))) ci_1_lst ci_2_lst ->
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_12 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_12)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_12 : lane_) => ((proj_lane__0 ci_1_12) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_12 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_12)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_12 : lane_) => ((proj_lane__0 ci_2_12) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (ci_1_12 : lane_) (ci_2_12 : lane_) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_12))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_12))))))))))) ci_1_lst ci_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_4 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)), 
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_13 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_13)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_13 : lane_) => ((proj_lane__0 ci_1_13) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_13 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_13)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_13 : lane_) => ((proj_lane__0 ci_2_13) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_13 : lane_) (ci_2_13 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_13))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_13)))))))))))) ci_1_lst ci_2_lst ->
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_15 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_15)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_15 : lane_) => ((proj_lane__0 ci_1_15) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_15 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_15)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_15 : lane_) => ((proj_lane__0 ci_2_15) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (ci_1_15 : lane_) (ci_2_15 : lane_) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_15))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_15))))))))))) ci_1_lst ci_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_5 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)), 
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_16 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_16)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_16 : lane_) => ((proj_lane__0 ci_1_16) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_16 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_16)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_16 : lane_) => ((proj_lane__0 ci_2_16) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_16 : lane_) (ci_2_16 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_16))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_16)))))))))))) ci_1_lst ci_2_lst ->
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_18 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_18)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_18 : lane_) => ((proj_lane__0 ci_1_18) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_18 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_18)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_18 : lane_) => ((proj_lane__0 ci_2_18) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (ci_1_18 : lane_) (ci_2_18 : lane_) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_18))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_18))))))))))) ci_1_lst ci_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_6 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)), 
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_19 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_19)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_19 : lane_) => ((proj_lane__0 ci_1_19) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_19 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_19)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_19 : lane_) => ((proj_lane__0 ci_2_19) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_19 : lane_) (ci_2_19 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_19))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_19)))))))))))) ci_1_lst ci_2_lst ->
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_21 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_21)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_21 : lane_) => ((proj_lane__0 ci_1_21) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_21 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_21)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_21 : lane_) => ((proj_lane__0 ci_2_21) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (ci_1_21 : lane_) (ci_2_21 : lane_) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_21))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_21))))))))))) ci_1_lst ci_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_7 : forall (M_1 : nat) (M_2 : nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)), 
		((|ci_1_lst|) == (|ci_2_lst|)) ->
		List.Forall (fun (ci_1_22 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_22)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_22 : lane_) => ((proj_lane__0 ci_1_22) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_22 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_22)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_22 : lane_) => ((proj_lane__0 ci_2_22) != None)) ci_2_lst ->
		List.Forall2 (fun (ci_1_22 : lane_) (ci_2_22 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_22))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_22)))))))))))) ci_1_lst ci_2_lst ->
		(ci_1_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
		(ci_2_lst == (list_slice (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
		List.Forall (fun (ci_1_24 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_24)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_24 : lane_) => ((proj_lane__0 ci_1_24) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_24 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_24)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_24 : lane_) => ((proj_lane__0 ci_2_24) != None)) ci_2_lst ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (ci_1_24 : lane_) (ci_2_24 : lane_) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_1_24))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (!((proj_num__0 (!((proj_lane__0 ci_2_24))))))))))) ci_1_lst ci_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1 (EXTMUL v_half v_sx)) c_1 c_2 c
	| fun_vextbinop___case_8 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1_25 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1_25)) ci_1_lst ->
		List.Forall (fun (ci_2_25 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_2_25)) ci_2_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_25 : iN) (cj_2_25 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_25 cj_2_25))))) cj_1_lst cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_27 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_27)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_27 : lane_) => ((proj_lane__0 ci_1_27) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_27 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_27)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_27 : lane_) => ((proj_lane__0 ci_2_27) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_26 : iN) (cj_2_26 : iN) => [::cj_1_26; cj_2_26]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_27 : lane_) (ci_2_27 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_27))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_27))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_27 : iN) (cj_2_27 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_27 cj_2_27)))) cj_1_lst cj_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1 DOTS) c_1 c_2 c
	| fun_vextbinop___case_9 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1_28 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1_28)) ci_1_lst ->
		List.Forall (fun (ci_2_28 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_2_28)) ci_2_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_28 : iN) (cj_2_28 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_28 cj_2_28))))) cj_1_lst cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_30 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_30)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_30 : lane_) => ((proj_lane__0 ci_1_30) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_30 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_30)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_30 : lane_) => ((proj_lane__0 ci_2_30) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_29 : iN) (cj_2_29 : iN) => [::cj_1_29; cj_2_29]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_30 : lane_) (ci_2_30 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_30))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_30))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_30 : iN) (cj_2_30 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_30 cj_2_30)))) cj_1_lst cj_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1 DOTS) c_1 c_2 c
	| fun_vextbinop___case_10 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1_31 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_1_31)) ci_1_lst ->
		List.Forall (fun (ci_2_31 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_2_31)) ci_2_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_31 : iN) (cj_2_31 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_31 cj_2_31))))) cj_1_lst cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_33 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_33)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_33 : lane_) => ((proj_lane__0 ci_1_33) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_33 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_33)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_33 : lane_) => ((proj_lane__0 ci_2_33) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_32 : iN) (cj_2_32 : iN) => [::cj_1_32; cj_2_32]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_33 : lane_) (ci_2_33 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_33))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_33))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_33 : iN) (cj_2_33 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_33 cj_2_33)))) cj_1_lst cj_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1 DOTS) c_1 c_2 c
	| fun_vextbinop___case_11 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1_34 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_1_34)) ci_1_lst ->
		List.Forall (fun (ci_2_34 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_2_34)) ci_2_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_34 : iN) (cj_2_34 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_34 cj_2_34))))) cj_1_lst cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_36 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_36)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_36 : lane_) => ((proj_lane__0 ci_1_36) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_36 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_36)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_36 : lane_) => ((proj_lane__0 ci_2_36) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_35 : iN) (cj_2_35 : iN) => [::cj_1_35; cj_2_35]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_36 : lane_) (ci_2_36 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I32)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_36))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_36))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (fun (cj_1_36 : iN) (cj_2_36 : iN) => (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_ (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_36 cj_2_36)))) cj_1_lst cj_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1 DOTS) c_1 c_2 c
	| fun_vextbinop___case_12 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1_37 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1_37)) ci_1_lst ->
		List.Forall (fun (ci_2_37 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_2_37)) ci_2_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_37 : iN) (cj_2_37 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_37 cj_2_37))))) cj_1_lst cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_39 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_39)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_39 : lane_) => ((proj_lane__0 ci_1_39) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_39 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_39)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_39 : lane_) => ((proj_lane__0 ci_2_39) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_38 : iN) (cj_2_38 : iN) => [::cj_1_38; cj_2_38]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_39 : lane_) (ci_2_39 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_39))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_39))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_39 : iN) (cj_2_39 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_39 cj_2_39)))) cj_1_lst cj_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1 DOTS) c_1 c_2 c
	| fun_vextbinop___case_13 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1_40 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1_40)) ci_1_lst ->
		List.Forall (fun (ci_2_40 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_2_40)) ci_2_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_40 : iN) (cj_2_40 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_40 cj_2_40))))) cj_1_lst cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_42 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_42)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_42 : lane_) => ((proj_lane__0 ci_1_42) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_42 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_42)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_42 : lane_) => ((proj_lane__0 ci_2_42) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_41 : iN) (cj_2_41 : iN) => [::cj_1_41; cj_2_41]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_42 : lane_) (ci_2_42 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_42))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_42))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_42 : iN) (cj_2_42 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_42 cj_2_42)))) cj_1_lst cj_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1 DOTS) c_1 c_2 c
	| fun_vextbinop___case_14 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1_43 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_1_43)) ci_1_lst ->
		List.Forall (fun (ci_2_43 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_2_43)) ci_2_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_43 : iN) (cj_2_43 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_43 cj_2_43))))) cj_1_lst cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_45 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_45)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_45 : lane_) => ((proj_lane__0 ci_1_45) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_45 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_45)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_45 : lane_) => ((proj_lane__0 ci_2_45) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_44 : iN) (cj_2_44 : iN) => [::cj_1_44; cj_2_44]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_45 : lane_) (ci_2_45 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_45))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_45))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_45 : iN) (cj_2_45 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_45 cj_2_45)))) cj_1_lst cj_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1 DOTS) c_1 c_2 c
	| fun_vextbinop___case_15 : forall (M_1 : nat) (M_2 : nat) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1_46 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_1_46)) ci_1_lst ->
		List.Forall (fun (ci_2_46 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_2_46)) ci_2_lst ->
		((|cj_1_lst|) == (|cj_2_lst|)) ->
		List.Forall2 (fun (cj_1_46 : iN) (cj_2_46 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_46 cj_2_46))))) cj_1_lst cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ->
		List.Forall (fun (ci_1_48 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_1_48)))) != None)) ci_1_lst ->
		List.Forall (fun (ci_1_48 : lane_) => ((proj_lane__0 ci_1_48) != None)) ci_1_lst ->
		List.Forall (fun (ci_2_48 : lane_) => ((proj_num__0 (!((proj_lane__0 ci_2_48)))) != None)) ci_2_lst ->
		List.Forall (fun (ci_2_48 : lane_) => ((proj_lane__0 ci_2_48) != None)) ci_2_lst ->
		((concat_ iN (list_zipWith (fun (cj_1_47 : iN) (cj_2_47 : iN) => [::cj_1_47; cj_2_47]) cj_1_lst cj_2_lst)) == (list_zipWith (fun (ci_1_48 : lane_) (ci_2_48 : lane_) => (imul_ (lsizenn1 (lanetype_Inn Inn_I64)) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_1_48))))))) (extend__ (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) res_S (!((proj_num__0 (!((proj_lane__0 ci_2_48))))))))) ci_1_lst ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (fun (cj_1_48 : iN) (cj_2_48 : iN) => (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_ (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_48 cj_2_48)))) cj_1_lst cj_2_lst))) ->
		fun_vextbinop__ (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1 DOTS) c_1 c_2 c.

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 *)
Inductive fun_vshiftop_ : ishape -> vshiftop_ -> lane_ -> u32 -> lane_ -> Prop :=
	| fun_vshiftop__case_0 : forall (v_Jnn : Jnn) (v_M : nat) (lane : uN) (v_n : nat), 
		(wf_lane_ (fun_lanetype (shape_ishape (ishape_X v_Jnn (mk_dim v_M)))) (mk_lane__2 v_Jnn (ishl_ (lsizenn (lanetype_Jnn v_Jnn)) lane (mk_uN v_n)))) ->
		fun_vshiftop_ (ishape_X v_Jnn (mk_dim v_M)) (mk_vshiftop__0 v_Jnn v_M vshiftop_Jnn_N_SHL) (mk_lane__2 v_Jnn lane) (mk_uN v_n) (mk_lane__2 v_Jnn (ishl_ (lsizenn (lanetype_Jnn v_Jnn)) lane (mk_uN v_n)))
	| fun_vshiftop__case_1 : forall (v_Jnn : Jnn) (v_M : nat) (v_sx : sx) (lane : uN) (v_n : nat), 
		(wf_lane_ (fun_lanetype (shape_ishape (ishape_X v_Jnn (mk_dim v_M)))) (mk_lane__2 v_Jnn (ishr_ (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (mk_uN v_n)))) ->
		fun_vshiftop_ (ishape_X v_Jnn (mk_dim v_M)) (mk_vshiftop__0 v_Jnn v_M (vshiftop_Jnn_N_SHR v_sx)) (mk_lane__2 v_Jnn lane) (mk_uN v_n) (mk_lane__2 v_Jnn (ishr_ (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (mk_uN v_n))).

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
	| moduleinst_case_ : forall (var_0 : (seq functype)) (var_1 : (seq funcaddr)) (var_2 : (seq globaladdr)) (var_3 : (seq tableaddr)) (var_4 : (seq memaddr)) (var_5 : (seq elemaddr)) (var_6 : (seq dataaddr)) (var_7 : (seq exportinst)), 
		List.Forall (fun (var_7 : exportinst) => (wf_exportinst var_7)) var_7 ->
		wf_moduleinst {| TYPES := var_0; FUNCS := var_1; GLOBALS := var_2; TABLES := var_3; MEMS := var_4; ELEMS := var_5; DATAS := var_6; EXPORTS := var_7 |}.

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
	| tableinst_case_ : forall (var_0 : tabletype) (var_1 : (seq ref)), 
		(wf_tabletype var_0) ->
		wf_tableinst {| tableinst_TYPE := var_0; REFS := var_1 |}.

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
	| meminst_case_ : forall (var_0 : memtype) (var_1 : (seq byte)), 
		(wf_memtype var_0) ->
		List.Forall (fun (var_1 : byte) => (wf_byte var_1)) var_1 ->
		wf_meminst {| meminst_TYPE := var_0; BYTES := var_1 |}.

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
	| datainst_case_ : forall (var_0 : (seq byte)), 
		List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0 ->
		wf_datainst {| datainst_BYTES := var_0 |}.

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
	| store_case_ : forall (var_0 : (seq funcinst)) (var_1 : (seq globalinst)) (var_2 : (seq tableinst)) (var_3 : (seq meminst)) (var_4 : (seq eleminst)) (var_5 : (seq datainst)), 
		List.Forall (fun (var_0 : funcinst) => (wf_funcinst var_0)) var_0 ->
		List.Forall (fun (var_1 : globalinst) => (wf_globalinst var_1)) var_1 ->
		List.Forall (fun (var_2 : tableinst) => (wf_tableinst var_2)) var_2 ->
		List.Forall (fun (var_3 : meminst) => (wf_meminst var_3)) var_3 ->
		List.Forall (fun (var_5 : datainst) => (wf_datainst var_5)) var_5 ->
		wf_store {| store_FUNCS := var_0; store_GLOBALS := var_1; store_TABLES := var_2; store_MEMS := var_3; store_ELEMS := var_4; store_DATAS := var_5 |}.

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
	| frame_case_ : forall (var_0 : (seq val)) (var_1 : moduleinst), 
		List.Forall (fun (var_0 : val) => (wf_val var_0)) var_0 ->
		(wf_moduleinst var_1) ->
		wf_frame {| LOCALS := var_0; frame_MODULE := var_1 |}.

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
	| admininstr_case_6 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst_0 : (seq instr)), 
		(wf_blocktype v_blocktype) ->
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		List.Forall (fun (instr_lst_0 : instr) => (wf_instr instr_lst_0)) instr_lst_0 ->
		wf_admininstr (admininstr_IFELSE v_blocktype instr_lst instr_lst_0)
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
		((lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) ->
		wf_admininstr (admininstr_VEXTUNOP ishape_1 ishape_2 var_0)
	| admininstr_case_37 : forall (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextbinop_), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(wf_vextbinop_ ishape_1 var_0) ->
		((lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) ->
		wf_admininstr (admininstr_VEXTBINOP ishape_1 ishape_2 var_0)
	| admininstr_case_38 : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx), 
		(wf_ishape ishape_1) ->
		(wf_ishape ishape_2) ->
		(((lsize (fun_lanetype (shape_ishape ishape_2))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) && ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) <= 32)) ->
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
	| admininstr_case_56 : forall (v_numtype : numtype) (var_0 : (option loadop_)) (v_memarg : memarg), 
		List.Forall (fun (var_0 : loadop_) => (wf_loadop_ v_numtype var_0)) (option_to_list var_0) ->
		(wf_memarg v_memarg) ->
		wf_admininstr (admininstr_LOAD v_numtype var_0 v_memarg)
	| admininstr_case_57 : forall (Inn_opt : (option Inn)) (numtype_opt : (option numtype)) (v_numtype : numtype) (sz_opt : (option sz)) (v_memarg : memarg), 
		List.Forall (fun (v_sz : sz) => (wf_sz v_sz)) (option_to_list sz_opt) ->
		(wf_memarg v_memarg) ->
		((Inn_opt == None) <-> (numtype_opt == None)) ->
		((Inn_opt == None) <-> (sz_opt == None)) ->
		List_Forall3 (fun (v_Inn : Inn) (v_numtype : numtype) (v_sz : sz) => ((v_numtype == (numtype_Inn v_Inn)) && ((v_sz :> nat) < (sizenn (numtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list numtype_opt) (option_to_list sz_opt) ->
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

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57 *)
Definition fun_frame (v_state : state) : frame :=
	match v_state return frame with
		| (mk_state s f) => f
	end.

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

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59 *)
Definition fun_globalinst (v_state : state) : (seq globalinst) :=
	match v_state return (seq globalinst) with
		| (mk_state s f) => (store_GLOBALS s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58 *)
Definition fun_tableinst (v_state : state) : (seq tableinst) :=
	match v_state return (seq tableinst) with
		| (mk_state s f) => (store_TABLES s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56 *)
Definition fun_meminst (v_state : state) : (seq meminst) :=
	match v_state return (seq meminst) with
		| (mk_state s f) => (store_MEMS s)
	end.

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

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58 *)
Definition fun_moduleinst (v_state : state) : moduleinst :=
	match v_state return moduleinst with
		| (mk_state s f) => (frame_MODULE f)
	end.

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

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68 *)
Definition fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
	match v_state, v_globalidx return globalinst with
		| (mk_state s f), x => ((store_GLOBALS s)[| ((GLOBALS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67 *)
Definition fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
	match v_state, v_tableidx return tableinst with
		| (mk_state s f), x => ((store_TABLES s)[| ((TABLES (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65 *)
Definition fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
	match v_state, v_memidx return meminst with
		| (mk_state s f), x => ((store_MEMS s)[| ((MEMS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

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

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67 *)
Definition fun_local (v_state : state) (v_localidx : localidx) : val :=
	match v_state, v_localidx return val with
		| (mk_state s f), x => ((LOCALS f)[| (x :> nat) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89 *)
Definition with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
	match v_state, v_localidx, v_val return state with
		| (mk_state s f), x, v => (mk_state s (f <| LOCALS := (list_update_func (LOCALS f) (x :> nat) (fun (_ : val) => v)) |>))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96 *)
Definition with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
	match v_state, v_globalidx, v_val return state with
		| (mk_state s f), x, v => (mk_state (s <| store_GLOBALS := (list_update_func (store_GLOBALS s) ((GLOBALS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : globalinst) => (var_1 <| VALUE := v |>))) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97 *)
Definition with_table (v_state : state) (v_tableidx : tableidx) (res_nat : nat) (v_ref : ref) : state :=
	match v_state, v_tableidx, res_nat, v_ref return state with
		| (mk_state s f), x, i, r => (mk_state (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : tableinst) => (var_1 <| REFS := (list_update_func (REFS var_1) i (fun (_ : ref) => r)) |>))) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89 *)
Definition with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
	match v_state, v_tableidx, v_tableinst return state with
		| (mk_state s f), x, ti => (mk_state (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f))[| (x :> nat) |]) (fun (_ : tableinst) => ti)) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100 *)
Definition with_mem (v_state : state) (v_memidx : memidx) (res_nat : nat) (nat_0 : nat) (var_0 : (seq byte)) : state :=
	match v_state, v_memidx, res_nat, nat_0, var_0 return state with
		| (mk_state s f), x, i, j, b_lst => (mk_state (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (BYTES var_1) i j b_lst) |>))) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87 *)
Definition with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
	match v_state, v_memidx, v_meminst return state with
		| (mk_state s f), x, mi => (mk_state (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f))[| (x :> nat) |]) (fun (_ : meminst) => mi)) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93 *)
Definition with_elem (v_state : state) (v_elemidx : elemidx) (var_0 : (seq ref)) : state :=
	match v_state, v_elemidx, var_0 return state with
		| (mk_state s f), x, r_lst => (mk_state (s <| store_ELEMS := (list_update_func (store_ELEMS s) ((ELEMS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : eleminst) => (var_1 <| eleminst_REFS := r_lst |>))) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94 *)
Definition with_data (v_state : state) (v_dataidx : dataidx) (var_0 : (seq byte)) : state :=
	match v_state, v_dataidx, var_0 return state with
		| (mk_state s f), x, b_lst => (mk_state (s <| store_DATAS := (list_update_func (store_DATAS s) ((DATAS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : datainst) => (var_1 <| datainst_BYTES := b_lst |>))) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
Inductive fun_growtable : tableinst -> nat -> ref -> (option tableinst) -> Prop :=
	| fun_growtable_case_0 : forall (ti : tableinst) (v_n : nat) (r : ref) (ti' : tableinst) (i : uN) (j_opt : (option u32)) (rt : reftype) (r'_lst : (seq ref)) (i' : nat), 
		(ti == {| tableinst_TYPE := (mk_tabletype (mk_limits i j_opt) rt); REFS := r'_lst |}) ->
		(i' == ((|r'_lst|) + v_n)) ->
		List.Forall (fun (j : u32) => (i' <= (j :> nat))) (option_to_list j_opt) ->
		(ti' == {| tableinst_TYPE := (mk_tabletype (mk_limits (mk_uN i') j_opt) rt); REFS := (r'_lst ++ (List.repeat r v_n)) |}) ->
		fun_growtable ti v_n r (Some ti')
	| fun_growtable_case_1 : forall (x0 : tableinst) (x1 : nat) (x2 : ref), fun_growtable x0 x1 x2 None.

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
Inductive fun_growmemory : meminst -> nat -> (option meminst) -> Prop :=
	| fun_growmemory_case_0 : forall (mi : meminst) (v_n : nat) (mi' : meminst) (i : uN) (j_opt : (option u32)) (b_lst : (seq byte)) (i' : nat), 
		(mi == {| meminst_TYPE := (PAGE (mk_limits i j_opt)); BYTES := b_lst |}) ->
		(i' == ((((|b_lst|) : nat) / ((64 * (Ki )) : nat)) + (v_n : nat))) ->
		List.Forall (fun (j : u32) => (i' <= ((j :> nat) : nat))) (option_to_list j_opt) ->
		(mi' == {| meminst_TYPE := (PAGE (mk_limits (mk_uN (i' : nat)) j_opt)); BYTES := (b_lst ++ (List.repeat (mk_byte 0) (v_n * (64 * (Ki ))))) |}) ->
		fun_growmemory mi v_n (Some mi')
	| fun_growmemory_case_1 : forall (x0 : meminst) (x1 : nat), fun_growmemory x0 x1 None.

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
	| context_case_ : forall (var_0 : (seq functype)) (var_1 : (seq functype)) (var_2 : (seq globaltype)) (var_3 : (seq tabletype)) (var_4 : (seq memtype)) (var_5 : (seq elemtype)) (var_6 : (seq datatype)) (var_7 : (seq valtype)) (var_8 : (seq resulttype)) (var_9 : (option resulttype)), 
		List.Forall (fun (var_3 : tabletype) => (wf_tabletype var_3)) var_3 ->
		List.Forall (fun (var_4 : memtype) => (wf_memtype var_4)) var_4 ->
		wf_context {| context_TYPES := var_0; context_FUNCS := var_1; context_GLOBALS := var_2; context_TABLES := var_3; context_MEMS := var_4; context_ELEMS := var_5; context_DATAS := var_6; context_LOCALS := var_7; LABELS := var_8; context_RETURN := var_9 |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:19.1-19.66 *)
Inductive Limits_ok : limits -> nat -> Prop :=
	| mk_Limits_ok : forall (v_n : n) (m_opt : (option m)) (k : nat), 
		(v_n <= k) ->
		List.Forall (fun (v_m : nat) => ((v_n <= v_m) && (v_m <= k))) (option_to_list m_opt) ->
		Limits_ok (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) k.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:20.1-20.64 *)
Inductive Functype_ok : functype -> Prop :=
	| mk_Functype_ok : forall (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), Functype_ok (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:21.1-21.66 *)
Inductive Globaltype_ok : globaltype -> Prop :=
	| mk_Globaltype_ok : forall (t : valtype), Globaltype_ok (mk_globaltype (Some MUT_MUT) t).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:22.1-22.65 *)
Inductive Tabletype_ok : tabletype -> Prop :=
	| mk_Tabletype_ok : forall (v_limits : limits) (v_reftype : reftype), 
		(Limits_ok v_limits ((((2 ^ 32) : nat) - (1 : nat)) : nat)) ->
		Tabletype_ok (mk_tabletype v_limits v_reftype).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:23.1-23.63 *)
Inductive Memtype_ok : memtype -> Prop :=
	| mk_Memtype_ok : forall (v_limits : limits), 
		(Limits_ok v_limits (2 ^ 16)) ->
		Memtype_ok (PAGE v_limits).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:24.1-24.66 *)
Inductive Externtype_ok : externtype -> Prop :=
	| Externtype_ok__func : forall (v_functype : functype), 
		(Functype_ok v_functype) ->
		Externtype_ok (FUNC v_functype)
	| Externtype_ok__global : forall (v_globaltype : globaltype), 
		(Globaltype_ok v_globaltype) ->
		Externtype_ok (GLOBAL v_globaltype)
	| Externtype_ok__table : forall (v_tabletype : tabletype), 
		(Tabletype_ok v_tabletype) ->
		Externtype_ok (TABLE v_tabletype)
	| Externtype_ok__mem : forall (v_memtype : memtype), 
		(Memtype_ok v_memtype) ->
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
		(n_11 >= n_21) ->
		(n_12 <= n_22) ->
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
		Tabletype_sub (mk_tabletype lim_1 rt) (mk_tabletype lim_2 rt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:91.1-91.72 *)
Inductive Memtype_sub : memtype -> memtype -> Prop :=
	| mk_Memtype_sub : forall (lim_1 : limits) (lim_2 : limits), 
		(Limits_sub lim_1 lim_2) ->
		Memtype_sub (PAGE lim_1) (PAGE lim_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:92.1-92.75 *)
Inductive Externtype_sub : externtype -> externtype -> Prop :=
	| Externtype_sub__func : forall (ft_1 : functype) (ft_2 : functype), 
		(Functype_sub ft_1 ft_2) ->
		Externtype_sub (FUNC ft_1) (FUNC ft_2)
	| Externtype_sub__global : forall (gt_1 : globaltype) (gt_2 : globaltype), 
		(Globaltype_sub gt_1 gt_2) ->
		Externtype_sub (GLOBAL gt_1) (GLOBAL gt_2)
	| Externtype_sub__table : forall (tt_1 : tabletype) (tt_2 : tabletype), 
		(Tabletype_sub tt_1 tt_2) ->
		Externtype_sub (TABLE tt_1) (TABLE tt_2)
	| Externtype_sub__mem : forall (mt_1 : memtype) (mt_2 : memtype), 
		(Memtype_sub mt_1 mt_2) ->
		Externtype_sub (MEM mt_1) (MEM mt_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:194.1-194.76 *)
Inductive Blocktype_ok : context -> blocktype -> functype -> Prop :=
	| Blocktype_ok__valtype : forall (C : context) (valtype_opt : (option valtype)), Blocktype_ok C (_RESULT valtype_opt) (mk_functype (mk_list _ [:: ]) (mk_list _ (option_to_list valtype_opt)))
	| Blocktype_ok__typeidx : forall (C : context) (v_typeidx : typeidx) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((v_typeidx :> nat) < (|(context_TYPES C)|)) ->
		(((context_TYPES C)[| (v_typeidx :> nat) |]) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Blocktype_ok C (_IDX v_typeidx) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)).

(* Mutual Recursion at: ../specification/wasm-2.0/6-typing.spectec:137.1-138.65 *)
Inductive Instr_ok : context -> instr -> functype -> Prop :=
	| nop : forall (C : context), Instr_ok C NOP (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| unreachable : forall (C : context) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), Instr_ok C UNREACHABLE (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| drop : forall (C : context) (t : valtype), Instr_ok C DROP (mk_functype (mk_list _ [::t]) (mk_list _ [:: ]))
	| select_expl : forall (C : context) (t : valtype), Instr_ok C (SELECT (Some [::t])) (mk_functype (mk_list _ [::t; t; valtype_I32]) (mk_list _ [::t]))
	| select_impl : forall (C : context) (t : valtype) (t' : valtype) (v_numtype : numtype) (v_vectype : vectype), 
		(Valtype_sub t t') ->
		((t' == (valtype_numtype v_numtype)) || (t' == (valtype_vectype v_vectype))) ->
		Instr_ok C (SELECT None) (mk_functype (mk_list _ [::t; t; valtype_I32]) (mk_list _ [::t]))
	| block : forall (C : context) (bt : blocktype) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Blocktype_ok C bt (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := None |} @@ C) instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Instr_ok C (BLOCK bt instr_lst) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| loop : forall (C : context) (bt : blocktype) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Blocktype_ok C bt (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_1_lst)]; context_RETURN := None |} @@ C) instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Instr_ok C (LOOP bt instr_lst) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| res_if : forall (C : context) (bt : blocktype) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Blocktype_ok C bt (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := None |} @@ C) instr_1_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := None |} @@ C) instr_2_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Instr_ok C (IFELSE bt instr_1_lst instr_2_lst) (mk_functype (mk_list _ (t_1_lst ++ [::valtype_I32])) (mk_list _ t_2_lst))
	| br : forall (C : context) (l : labelidx) (t_1_lst : (seq valtype)) (t_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((l :> nat) < (|(LABELS C)|)) ->
		((proj_list_0 valtype ((LABELS C)[| (l :> nat) |])) == t_lst) ->
		Instr_ok C (BR l) (mk_functype (mk_list _ (t_1_lst ++ t_lst)) (mk_list _ t_2_lst))
	| br_if : forall (C : context) (l : labelidx) (t_lst : (seq valtype)), 
		((l :> nat) < (|(LABELS C)|)) ->
		((proj_list_0 valtype ((LABELS C)[| (l :> nat) |])) == t_lst) ->
		Instr_ok C (BR_IF l) (mk_functype (mk_list _ (t_lst ++ [::valtype_I32])) (mk_list _ t_lst))
	| br_table : forall (C : context) (l_lst : (seq labelidx)) (l' : labelidx) (t_1_lst : (seq valtype)) (t_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		List.Forall (fun (l : labelidx) => ((l :> nat) < (|(LABELS C)|))) l_lst ->
		List.Forall (fun (l : labelidx) => (Resulttype_sub (mk_list _ t_lst) ((LABELS C)[| (l :> nat) |]))) l_lst ->
		((l' :> nat) < (|(LABELS C)|)) ->
		(Resulttype_sub (mk_list _ t_lst) ((LABELS C)[| (l' :> nat) |])) ->
		Instr_ok C (BR_TABLE l_lst l') (mk_functype (mk_list _ (t_1_lst ++ (t_lst ++ [::valtype_I32]))) (mk_list _ t_2_lst))
	| call : forall (C : context) (x : idx) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((x :> nat) < (|(context_FUNCS C)|)) ->
		(((context_FUNCS C)[| (x :> nat) |]) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Instr_ok C (CALL x) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| call_indirect : forall (C : context) (x : idx) (y : idx) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim FUNCREF)) ->
		((y :> nat) < (|(context_TYPES C)|)) ->
		(((context_TYPES C)[| (y :> nat) |]) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Instr_ok C (CALL_INDIRECT x y) (mk_functype (mk_list _ (t_1_lst ++ [::valtype_I32])) (mk_list _ t_2_lst))
	| res_return : forall (C : context) (t_1_lst : (seq valtype)) (t_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((context_RETURN C) == (Some (mk_list _ t_lst))) ->
		Instr_ok C RETURN (mk_functype (mk_list _ (t_1_lst ++ t_lst)) (mk_list _ t_2_lst))
	| const : forall (C : context) (nt : numtype) (c_nt : num_), 
		(wf_num_ nt c_nt) ->
		Instr_ok C (CONST nt c_nt) (mk_functype (mk_list _ [:: ]) (mk_list _ [::(valtype_numtype nt)]))
	| unop : forall (C : context) (nt : numtype) (unop_nt : unop_), 
		(wf_unop_ nt unop_nt) ->
		Instr_ok C (UNOP nt unop_nt) (mk_functype (mk_list _ [::(valtype_numtype nt)]) (mk_list _ [::(valtype_numtype nt)]))
	| binop : forall (C : context) (nt : numtype) (binop_nt : binop_), 
		(wf_binop_ nt binop_nt) ->
		Instr_ok C (BINOP nt binop_nt) (mk_functype (mk_list _ [::(valtype_numtype nt); (valtype_numtype nt)]) (mk_list _ [::(valtype_numtype nt)]))
	| testop : forall (C : context) (nt : numtype) (testop_nt : testop_), 
		(wf_testop_ nt testop_nt) ->
		Instr_ok C (TESTOP nt testop_nt) (mk_functype (mk_list _ [::(valtype_numtype nt)]) (mk_list _ [::valtype_I32]))
	| relop : forall (C : context) (nt : numtype) (relop_nt : relop_), 
		(wf_relop_ nt relop_nt) ->
		Instr_ok C (RELOP nt relop_nt) (mk_functype (mk_list _ [::(valtype_numtype nt); (valtype_numtype nt)]) (mk_list _ [::valtype_I32]))
	| cvtop_reinterpret : forall (C : context) (nt_1 : numtype) (nt_2 : numtype), 
		((res_size (valtype_numtype nt_1)) != None) ->
		((res_size (valtype_numtype nt_2)) != None) ->
		((!((res_size (valtype_numtype nt_1)))) == (!((res_size (valtype_numtype nt_2))))) ->
		Instr_ok C (CVTOP nt_1 nt_2 REINTERPRET) (mk_functype (mk_list _ [::(valtype_numtype nt_2)]) (mk_list _ [::(valtype_numtype nt_1)]))
	| cvtop_convert : forall (C : context) (nt_1 : numtype) (nt_2 : numtype) (v_cvtop : cvtop), Instr_ok C (CVTOP nt_1 nt_2 v_cvtop) (mk_functype (mk_list _ [::(valtype_numtype nt_2)]) (mk_list _ [::(valtype_numtype nt_1)]))
	| ref_null : forall (C : context) (rt : reftype), Instr_ok C (REF_NULL rt) (mk_functype (mk_list _ [:: ]) (mk_list _ [::(valtype_reftype rt)]))
	| ref_func : forall (C : context) (x : idx) (ft : functype), 
		((x :> nat) < (|(context_FUNCS C)|)) ->
		(((context_FUNCS C)[| (x :> nat) |]) == ft) ->
		Instr_ok C (REF_FUNC x) (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_FUNCREF]))
	| ref_is_null : forall (C : context) (rt : reftype), Instr_ok C REF_IS_NULL (mk_functype (mk_list _ [::(valtype_reftype rt)]) (mk_list _ [::valtype_I32]))
	| vconst : forall (C : context) (c : vec_), Instr_ok C (VCONST V128 c) (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vvunop : forall (C : context) (v_vvunop : vvunop), Instr_ok C (VVUNOP V128 v_vvunop) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vvbinop : forall (C : context) (v_vvbinop : vvbinop), Instr_ok C (VVBINOP V128 v_vvbinop) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vvternop : forall (C : context) (v_vvternop : vvternop), Instr_ok C (VVTERNOP V128 v_vvternop) (mk_functype (mk_list _ [::valtype_V128; valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vvtestop : forall (C : context) (v_vvtestop : vvtestop), Instr_ok C (VVTESTOP V128 v_vvtestop) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_I32]))
	| vunop : forall (C : context) (sh : shape) (vunop_sh : vunop_), 
		(wf_vunop_ sh vunop_sh) ->
		Instr_ok C (VUNOP sh vunop_sh) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_V128]))
	| vbinop : forall (C : context) (sh : shape) (vbinop_sh : vbinop_), 
		(wf_vbinop_ sh vbinop_sh) ->
		Instr_ok C (VBINOP sh vbinop_sh) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vtestop : forall (C : context) (sh : shape) (vtestop_sh : vtestop_), 
		(wf_vtestop_ sh vtestop_sh) ->
		Instr_ok C (VTESTOP sh vtestop_sh) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_I32]))
	| vrelop : forall (C : context) (sh : shape) (vrelop_sh : vrelop_), 
		(wf_vrelop_ sh vrelop_sh) ->
		Instr_ok C (VRELOP sh vrelop_sh) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vshiftop : forall (C : context) (sh : ishape) (vshiftop_sh : vshiftop_), 
		(wf_vshiftop_ sh vshiftop_sh) ->
		Instr_ok C (VSHIFTOP sh vshiftop_sh) (mk_functype (mk_list _ [::valtype_V128; valtype_I32]) (mk_list _ [::valtype_V128]))
	| vbitmask : forall (C : context) (sh : ishape), Instr_ok C (VBITMASK sh) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_I32]))
	| vswizzle : forall (C : context) (sh : ishape), Instr_ok C (VSWIZZLE sh) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vshuffle : forall (C : context) (sh : ishape) (i_lst : (seq laneidx)), 
		List.Forall (fun (i : laneidx) => ((i :> nat) < (2 * ((fun_dim (shape_ishape sh)) :> nat)))) i_lst ->
		Instr_ok C (VSHUFFLE sh i_lst) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vsplat : forall (C : context) (sh : shape), Instr_ok C (VSPLAT sh) (mk_functype (mk_list _ [::(valtype_numtype (shunpack sh))]) (mk_list _ [::valtype_V128]))
	| vextract_lane : forall (C : context) (sh : shape) (sx_opt : (option sx)) (i : laneidx), 
		((i :> nat) < ((fun_dim sh) :> nat)) ->
		Instr_ok C (VEXTRACT_LANE sh sx_opt i) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::(valtype_numtype (shunpack sh))]))
	| vreplace_lane : forall (C : context) (sh : shape) (i : laneidx), 
		((i :> nat) < ((fun_dim sh) :> nat)) ->
		Instr_ok C (VREPLACE_LANE sh i) (mk_functype (mk_list _ [::valtype_V128; (valtype_numtype (shunpack sh))]) (mk_list _ [::valtype_V128]))
	| vextunop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop_), 
		(wf_vextunop_ sh_1 vextunop) ->
		Instr_ok C (VEXTUNOP sh_1 sh_2 vextunop) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_V128]))
	| vextbinop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop_), 
		(wf_vextbinop_ sh_1 vextbinop) ->
		Instr_ok C (VEXTBINOP sh_1 sh_2 vextbinop) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vnarrow : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (v_sx : sx), Instr_ok C (VNARROW sh_1 sh_2 v_sx) (mk_functype (mk_list _ [::valtype_V128; valtype_V128]) (mk_list _ [::valtype_V128]))
	| Instr_ok__vcvtop : forall (C : context) (sh_1 : shape) (sh_2 : shape) (v_vcvtop : vcvtop), Instr_ok C (VCVTOP sh_1 sh_2 v_vcvtop) (mk_functype (mk_list _ [::valtype_V128]) (mk_list _ [::valtype_V128]))
	| local_get : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|)) ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		Instr_ok C (LOCAL_GET x) (mk_functype (mk_list _ [:: ]) (mk_list _ [::t]))
	| local_set : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|)) ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		Instr_ok C (LOCAL_SET x) (mk_functype (mk_list _ [::t]) (mk_list _ [:: ]))
	| local_tee : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|)) ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		Instr_ok C (LOCAL_TEE x) (mk_functype (mk_list _ [::t]) (mk_list _ [::t]))
	| global_get : forall (C : context) (x : idx) (t : valtype) (v_mut : mut), 
		((x :> nat) < (|(context_GLOBALS C)|)) ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype v_mut t)) ->
		Instr_ok C (GLOBAL_GET x) (mk_functype (mk_list _ [:: ]) (mk_list _ [::t]))
	| global_set : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_GLOBALS C)|)) ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype (Some MUT_MUT) t)) ->
		Instr_ok C (GLOBAL_SET x) (mk_functype (mk_list _ [::t]) (mk_list _ [:: ]))
	| table_get : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_GET x) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::(valtype_reftype rt)]))
	| table_set : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_SET x) (mk_functype (mk_list _ [::valtype_I32; (valtype_reftype rt)]) (mk_list _ [:: ]))
	| table_size : forall (C : context) (x : idx) (lim : limits) (rt : reftype), 
		((x :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_SIZE x) (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_I32]))
	| table_grow : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_GROW x) (mk_functype (mk_list _ [::(valtype_reftype rt); valtype_I32]) (mk_list _ [::valtype_I32]))
	| table_fill : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		Instr_ok C (TABLE_FILL x) (mk_functype (mk_list _ [::valtype_I32; (valtype_reftype rt); valtype_I32]) (mk_list _ [:: ]))
	| table_copy : forall (C : context) (x_1 : idx) (x_2 : idx) (lim_1 : limits) (rt : reftype) (lim_2 : limits), 
		((x_1 :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x_1 :> nat) |]) == (mk_tabletype lim_1 rt)) ->
		((x_2 :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x_2 :> nat) |]) == (mk_tabletype lim_2 rt)) ->
		Instr_ok C (TABLE_COPY x_1 x_2) (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| table_init : forall (C : context) (x_1 : idx) (x_2 : idx) (lim : limits) (rt : reftype), 
		((x_1 :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x_1 :> nat) |]) == (mk_tabletype lim rt)) ->
		((x_2 :> nat) < (|(context_ELEMS C)|)) ->
		(((context_ELEMS C)[| (x_2 :> nat) |]) == rt) ->
		Instr_ok C (TABLE_INIT x_1 x_2) (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| elem_drop : forall (C : context) (x : idx) (rt : reftype), 
		((x :> nat) < (|(context_ELEMS C)|)) ->
		(((context_ELEMS C)[| (x :> nat) |]) == rt) ->
		Instr_ok C (ELEM_DROP x) (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| memory_size : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		Instr_ok C MEMORY_SIZE (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_I32]))
	| memory_grow : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		Instr_ok C MEMORY_GROW (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::valtype_I32]))
	| memory_fill : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		Instr_ok C MEMORY_FILL (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| memory_copy : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		Instr_ok C MEMORY_COPY (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| memory_init : forall (C : context) (x : idx) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		((x :> nat) < (|(context_DATAS C)|)) ->
		(((context_DATAS C)[| (x :> nat) |]) == OK) ->
		Instr_ok C (MEMORY_INIT x) (mk_functype (mk_list _ [::valtype_I32; valtype_I32; valtype_I32]) (mk_list _ [:: ]))
	| data_drop : forall (C : context) (x : idx), 
		((x :> nat) < (|(context_DATAS C)|)) ->
		(((context_DATAS C)[| (x :> nat) |]) == OK) ->
		Instr_ok C (DATA_DROP x) (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| load_val : forall (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		((res_size (valtype_numtype nt)) != None) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= (((!((res_size (valtype_numtype nt)))) : nat) / (8 : nat))) ->
		Instr_ok C (LOAD nt None v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::(valtype_numtype nt)]))
	| load_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= ((v_M : nat) / (8 : nat))) ->
		Instr_ok C (LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::(valtype_Inn v_Inn)]))
	| store_val : forall (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		((res_size (valtype_numtype nt)) != None) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= (((!((res_size (valtype_numtype nt)))) : nat) / (8 : nat))) ->
		Instr_ok C (STORE nt None v_memarg) (mk_functype (mk_list _ [::valtype_I32; (valtype_numtype nt)]) (mk_list _ [:: ]))
	| store_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= ((v_M : nat) / (8 : nat))) ->
		Instr_ok C (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg) (mk_functype (mk_list _ [::valtype_I32; (valtype_Inn v_Inn)]) (mk_list _ [:: ]))
	| vload : forall (C : context) (v_M : M) (v_N : res_N) (v_sx : sx) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= (((v_M : nat) / (8 : nat)) * (v_N : nat))) ->
		Instr_ok C (VLOAD V128 (Some (SHAPEX_ v_M v_N v_sx)) v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::valtype_V128]))
	| vload_splat : forall (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= ((v_n : nat) / (8 : nat))) ->
		Instr_ok C (VLOAD V128 (Some (SPLAT v_n)) v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::valtype_V128]))
	| vload_zero : forall (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= ((v_n : nat) / (8 : nat))) ->
		Instr_ok C (VLOAD V128 (Some (vloadop_ZERO v_n)) v_memarg) (mk_functype (mk_list _ [::valtype_I32]) (mk_list _ [::valtype_V128]))
	| vload_lane : forall (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= ((v_n : nat) / (8 : nat))) ->
		(((v_laneidx :> nat) : nat) < ((128 : nat) / (v_n : nat))) ->
		Instr_ok C (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx) (mk_functype (mk_list _ [::valtype_I32; valtype_V128]) (mk_list _ [::valtype_V128]))
	| vstore : forall (C : context) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		((res_size valtype_V128) != None) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= (((!((res_size valtype_V128))) : nat) / (8 : nat))) ->
		Instr_ok C (VSTORE V128 v_memarg) (mk_functype (mk_list _ [::valtype_I32; valtype_V128]) (mk_list _ [:: ]))
	| vstore_lane : forall (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= ((v_n : nat) / (8 : nat))) ->
		(((v_laneidx :> nat) : nat) < ((128 : nat) / (v_n : nat))) ->
		Instr_ok C (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx) (mk_functype (mk_list _ [::valtype_I32; valtype_V128]) (mk_list _ [:: ]))

with

Instrs_ok : context -> (seq instr) -> functype -> Prop :=
	| empty : forall (C : context), Instrs_ok C [:: ] (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| res_seq : forall (C : context) (instr_1 : instr) (instr_2_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_3_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instr_ok C instr_1 (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Instrs_ok C instr_2_lst (mk_functype (mk_list _ t_2_lst) (mk_list _ t_3_lst))) ->
		Instrs_ok C ([::instr_1] ++ instr_2_lst) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_3_lst))
	| sub : forall (C : context) (instr_lst : (seq instr)) (t'_1_lst : (seq valtype)) (t'_2_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok C instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Resulttype_sub (mk_list _ t'_1_lst) (mk_list _ t_1_lst)) ->
		(Resulttype_sub (mk_list _ t_2_lst) (mk_list _ t'_2_lst)) ->
		Instrs_ok C instr_lst (mk_functype (mk_list _ t'_1_lst) (mk_list _ t'_2_lst))
	| Instrs_ok__frame : forall (C : context) (instr_lst : (seq instr)) (t_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok C instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Instrs_ok C instr_lst (mk_functype (mk_list _ (t_lst ++ t_1_lst)) (mk_list _ (t_lst ++ t_2_lst))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:139.1-139.69 *)
Inductive Expr_ok : context -> expr -> resulttype -> Prop :=
	| mk_Expr_ok : forall (C : context) (instr_lst : (seq instr)) (t_lst : (seq valtype)), 
		(Instrs_ok C instr_lst (mk_functype (mk_list _ [:: ]) (mk_list _ t_lst))) ->
		Expr_ok C instr_lst (mk_list _ t_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:525.1-525.78 *)
Inductive Instr_const : context -> instr -> Prop :=
	| Instr_const__const : forall (C : context) (nt : numtype) (c : num_), 
		(wf_num_ nt c) ->
		Instr_const C (CONST nt c)
	| Instr_const__vconst : forall (C : context) (vt : vectype) (vc : vec_), Instr_const C (VCONST vt vc)
	| Instr_const__ref_null : forall (C : context) (rt : reftype), Instr_const C (REF_NULL rt)
	| Instr_const__ref_func : forall (C : context) (x : idx), Instr_const C (REF_FUNC x)
	| Instr_const__global_get : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_GLOBALS C)|)) ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype None t)) ->
		Instr_const C (GLOBAL_GET x).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:526.1-526.77 *)
Inductive Expr_const : context -> expr -> Prop :=
	| mk_Expr_const : forall (C : context) (instr_lst : (seq instr)), 
		List.Forall (fun (v_instr : instr) => (Instr_const C v_instr)) instr_lst ->
		Expr_const C instr_lst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:527.1-527.78 *)
Inductive Expr_ok_const : context -> expr -> valtype -> Prop :=
	| mk_Expr_ok_const : forall (C : context) (v_expr : expr) (t : valtype), 
		(Expr_ok C v_expr (mk_list _ [::t])) ->
		(Expr_const C v_expr) ->
		Expr_ok_const C v_expr t.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:560.1-560.73 *)
Inductive Type_ok : type -> functype -> Prop :=
	| mk_Type_ok : forall (ft : functype), 
		(Functype_ok ft) ->
		Type_ok (TYPE ft) ft.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:561.1-561.73 *)
Inductive Func_ok : context -> func -> functype -> Prop :=
	| mk_Func_ok : forall (C : context) (x : idx) (t_lst : (seq valtype)) (v_expr : expr) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((x :> nat) < (|(context_TYPES C)|)) ->
		(((context_TYPES C)[| (x :> nat) |]) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		List.Forall (fun (t : valtype) => (t != BOT)) t_lst ->
		(Expr_ok (C @@ {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := (t_1_lst ++ t_lst); LABELS := [::(mk_list _ t_2_lst)]; context_RETURN := (Some (mk_list _ t_2_lst)) |}) v_expr (mk_list _ t_2_lst)) ->
		Func_ok C (func_FUNC x (seq.map (fun (t : valtype) => (LOCAL t)) t_lst) v_expr) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:562.1-562.75 *)
Inductive Global_ok : context -> global -> globaltype -> Prop :=
	| mk_Global_ok : forall (C : context) (gt : globaltype) (v_expr : expr) (v_mut : mut) (t : valtype), 
		(Globaltype_ok gt) ->
		(gt == (mk_globaltype v_mut t)) ->
		(Expr_ok_const C v_expr t) ->
		Global_ok C (global_GLOBAL gt v_expr) gt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:563.1-563.74 *)
Inductive Table_ok : context -> table -> tabletype -> Prop :=
	| mk_Table_ok : forall (C : context) (res_tt : tabletype), 
		(Tabletype_ok res_tt) ->
		Table_ok C (table_TABLE res_tt) res_tt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:564.1-564.72 *)
Inductive Mem_ok : context -> mem -> memtype -> Prop :=
	| mk_Mem_ok : forall (C : context) (mt : memtype), 
		(Memtype_ok mt) ->
		Mem_ok C (MEMORY mt) mt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:567.1-567.77 *)
Inductive Elemmode_ok : context -> elemmode -> reftype -> Prop :=
	| active : forall (C : context) (x : idx) (v_expr : expr) (rt : reftype) (lim : limits), 
		((x :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x :> nat) |]) == (mk_tabletype lim rt)) ->
		(Expr_ok_const C v_expr valtype_I32) ->
		Elemmode_ok C (ACTIVE x v_expr) rt
	| passive : forall (C : context) (rt : reftype), Elemmode_ok C PASSIVE rt
	| declare : forall (C : context) (rt : reftype), Elemmode_ok C DECLARE rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:565.1-565.73 *)
Inductive Elem_ok : context -> elem -> reftype -> Prop :=
	| mk_Elem_ok : forall (C : context) (rt : reftype) (expr_lst : (seq expr)) (v_elemmode : elemmode), 
		List.Forall (fun (v_expr : expr) => (Expr_ok_const C v_expr (valtype_reftype rt))) expr_lst ->
		(Elemmode_ok C v_elemmode rt) ->
		Elem_ok C (ELEM rt expr_lst v_elemmode) rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:568.1-568.77 *)
Inductive Datamode_ok : context -> datamode -> Prop :=
	| Datamode_ok__active : forall (C : context) (v_expr : expr) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(Expr_ok_const C v_expr valtype_I32) ->
		Datamode_ok C (datamode_ACTIVE (mk_uN 0) v_expr)
	| Datamode_ok__passive : forall (C : context), Datamode_ok C datamode_PASSIVE.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:566.1-566.73 *)
Inductive Data_ok : context -> data -> Prop :=
	| mk_Data_ok : forall (C : context) (b_lst : (seq byte)) (v_datamode : datamode), 
		(Datamode_ok C v_datamode) ->
		Data_ok C (DATA b_lst v_datamode).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:569.1-569.74 *)
Inductive Start_ok : context -> start -> Prop :=
	| mk_Start_ok : forall (C : context) (x : idx), 
		((x :> nat) < (|(context_FUNCS C)|)) ->
		(((context_FUNCS C)[| (x :> nat) |]) == (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))) ->
		Start_ok C (START x).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:633.1-633.80 *)
Inductive Import_ok : context -> import -> externtype -> Prop :=
	| mk_Import_ok : forall (C : context) (name_1 : name) (name_2 : name) (xt : externtype), 
		(Externtype_ok xt) ->
		Import_ok C (IMPORT name_1 name_2 xt) xt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:635.1-635.83 *)
Inductive Externidx_ok : context -> externidx -> externtype -> Prop :=
	| Externidx_ok__func : forall (C : context) (x : idx) (ft : functype), 
		((x :> nat) < (|(context_FUNCS C)|)) ->
		(((context_FUNCS C)[| (x :> nat) |]) == ft) ->
		Externidx_ok C (externidx_FUNC x) (FUNC ft)
	| Externidx_ok__global : forall (C : context) (x : idx) (gt : globaltype), 
		((x :> nat) < (|(context_GLOBALS C)|)) ->
		(((context_GLOBALS C)[| (x :> nat) |]) == gt) ->
		Externidx_ok C (externidx_GLOBAL x) (GLOBAL gt)
	| Externidx_ok__table : forall (C : context) (x : idx) (res_tt : tabletype), 
		((x :> nat) < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| (x :> nat) |]) == res_tt) ->
		Externidx_ok C (externidx_TABLE x) (TABLE res_tt)
	| Externidx_ok__mem : forall (C : context) (x : idx) (mt : memtype), 
		((x :> nat) < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| (x :> nat) |]) == mt) ->
		Externidx_ok C (externidx_MEM x) (MEM mt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:634.1-634.80 *)
Inductive Export_ok : context -> export -> externtype -> Prop :=
	| mk_Export_ok : forall (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype), 
		(Externidx_ok C v_externidx xt) ->
		Export_ok C (EXPORT v_name v_externidx) xt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:665.1-665.62 *)
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
		((|mt_lst|) <= 1) ->
		(C == {| context_TYPES := ft'_lst; context_FUNCS := (ift_lst ++ ft_lst); context_GLOBALS := (igt_lst ++ gt_lst); context_TABLES := (itt_lst ++ tt_lst); context_MEMS := (imt_lst ++ mt_lst); context_ELEMS := rt_lst; context_DATAS := (List.repeat OK v_n); context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(C' == {| context_TYPES := ft'_lst; context_FUNCS := (ift_lst ++ ft_lst); context_GLOBALS := igt_lst; context_TABLES := (itt_lst ++ tt_lst); context_MEMS := (imt_lst ++ mt_lst); context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(ift_lst == var_0) ->
		(igt_lst == var_1) ->
		(itt_lst == var_2) ->
		(imt_lst == var_3) ->
		Module_ok (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:276.1-278.15 *)
Inductive Step_pure_before_vtestop_false : (seq admininstr) -> Prop :=
	| vtestop_true_0 : forall (c : vec_) (v_Jnn : Jnn) (v_N : res_N) (ci_1_lst : (seq lane_)), 
		List.Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ->
		List.Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != None)) ci_1_lst ->
		List.Forall (fun (ci_1 : lane_) => (((!((proj_lane__2 ci_1))) :> nat) != 0)) ci_1_lst ->
		Step_pure_before_vtestop_false [::(admininstr_VCONST V128 c); (admininstr_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE))].

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.77 *)
Inductive Step_pure : (seq admininstr) -> (seq admininstr) -> Prop :=
	| Step_pure__unreachable : Step_pure [::admininstr_UNREACHABLE] [::admininstr_TRAP]
	| Step_pure__nop : Step_pure [::admininstr_NOP] [:: ]
	| Step_pure__drop : forall (v_val : val), Step_pure [::(admininstr_val v_val); admininstr_DROP] [:: ]
	| select_true : forall (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : (option (seq valtype))), 
		(wf_num_ I32 c) ->
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_val val_1); (admininstr_val val_2); (admininstr_CONST I32 c); (admininstr_SELECT t_lst_opt)] [::(admininstr_val val_1)]
	| select_false : forall (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : (option (seq valtype))), 
		(wf_num_ I32 c) ->
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_val val_1); (admininstr_val val_2); (admininstr_CONST I32 c); (admininstr_SELECT t_lst_opt)] [::(admininstr_val val_2)]
	| if_true : forall (c : num_) (bt : blocktype) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)), 
		(wf_num_ I32 c) ->
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_IFELSE bt instr_1_lst instr_2_lst)] [::(admininstr_BLOCK bt instr_1_lst)]
	| if_false : forall (c : num_) (bt : blocktype) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)), 
		(wf_num_ I32 c) ->
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_IFELSE bt instr_1_lst instr_2_lst)] [::(admininstr_BLOCK bt instr_2_lst)]
	| label_vals : forall (v_n : n) (instr_lst : (seq instr)) (val_lst : (seq val)), Step_pure [::(LABEL_ v_n instr_lst (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
	| br_zero : forall (v_n : n) (instr'_lst : (seq instr)) (val'_lst : (seq val)) (val_lst : (seq val)) (instr_lst : (seq instr)), Step_pure [::(LABEL_ v_n instr'_lst ((((seq.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)) ++ [::(admininstr_BR (mk_uN 0))]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (seq.map (fun (instr' : instr) => (admininstr_instr instr')) instr'_lst))
	| br_succ : forall (v_n : n) (instr'_lst : (seq instr)) (val_lst : (seq val)) (l : labelidx) (instr_lst : (seq instr)), Step_pure [::(LABEL_ v_n instr'_lst (((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_BR (mk_uN ((l :> nat) + 1)))]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_BR l)])
	| br_if_true : forall (c : num_) (l : labelidx), 
		(wf_num_ I32 c) ->
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_BR_IF l)] [::(admininstr_BR l)]
	| br_if_false : forall (c : num_) (l : labelidx), 
		(wf_num_ I32 c) ->
		((proj_num__0 c) != None) ->
		(((!((proj_num__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_BR_IF l)] [:: ]
	| br_table_lt : forall (i : num_) (l_lst : (seq labelidx)) (l' : labelidx), 
		(((!((proj_num__0 i))) :> nat) < (|l_lst|)) ->
		((proj_num__0 i) != None) ->
		(wf_num_ I32 i) ->
		Step_pure [::(admininstr_CONST I32 i); (admininstr_BR_TABLE l_lst l')] [::(admininstr_BR (l_lst[| ((!((proj_num__0 i))) :> nat) |]))]
	| br_table_ge : forall (i : num_) (l_lst : (seq labelidx)) (l' : labelidx), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 i))) :> nat) >= (|l_lst|)) ->
		Step_pure [::(admininstr_CONST I32 i); (admininstr_BR_TABLE l_lst l')] [::(admininstr_BR l')]
	| frame_vals : forall (v_n : n) (f : frame) (val_lst : (seq val)), Step_pure [::(FRAME_ v_n f (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
	| return_frame : forall (v_n : n) (f : frame) (val'_lst : (seq val)) (val_lst : (seq val)) (instr_lst : (seq instr)), Step_pure [::(FRAME_ v_n f ((((seq.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)) ++ [::admininstr_RETURN]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
	| return_label : forall (v_n : n) (instr'_lst : (seq instr)) (val_lst : (seq val)) (instr_lst : (seq instr)), Step_pure [::(LABEL_ v_n instr'_lst (((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::admininstr_RETURN]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::admininstr_RETURN])
	| trap_vals : forall (val_lst : (seq val)) (instr_lst : (seq instr)), 
		((val_lst != [:: ]) || (instr_lst != [:: ])) ->
		Step_pure ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([::admininstr_TRAP] ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))) [::admininstr_TRAP]
	| trap_label : forall (v_n : n) (instr'_lst : (seq instr)), Step_pure [::(LABEL_ v_n instr'_lst [::admininstr_TRAP])] [::admininstr_TRAP]
	| trap_frame : forall (v_n : n) (f : frame), Step_pure [::(FRAME_ v_n f [::admininstr_TRAP])] [::admininstr_TRAP]
	| unop_val : forall (nt : numtype) (c_1 : num_) (unop : unop_) (c : num_) (var_0 : (seq num_)), 
		(fun_unop_ nt unop c_1 var_0) ->
		(wf_num_ nt c_1) ->
		(wf_unop_ nt unop) ->
		(wf_num_ nt c) ->
		((|var_0|) > 0) ->
		(c \in var_0) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_UNOP nt unop)] [::(admininstr_CONST nt c)]
	| unop_trap : forall (nt : numtype) (c_1 : num_) (unop : unop_) (var_0 : (seq num_)), 
		(fun_unop_ nt unop c_1 var_0) ->
		(wf_num_ nt c_1) ->
		(wf_unop_ nt unop) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_UNOP nt unop)] [::admininstr_TRAP]
	| binop_val : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (c : num_) (var_0 : (seq num_)), 
		(fun_binop_ nt binop c_1 c_2 var_0) ->
		(wf_num_ nt c_1) ->
		(wf_num_ nt c_2) ->
		(wf_binop_ nt binop) ->
		(wf_num_ nt c) ->
		((|var_0|) > 0) ->
		(c \in var_0) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_CONST nt c_2); (admininstr_BINOP nt binop)] [::(admininstr_CONST nt c)]
	| binop_trap : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (var_0 : (seq num_)), 
		(fun_binop_ nt binop c_1 c_2 var_0) ->
		(wf_num_ nt c_1) ->
		(wf_num_ nt c_2) ->
		(wf_binop_ nt binop) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_CONST nt c_2); (admininstr_BINOP nt binop)] [::admininstr_TRAP]
	| Step_pure__testop : forall (nt : numtype) (c_1 : num_) (testop : testop_) (c : num_) (var_0 : num_), 
		(fun_testop_ nt testop c_1 var_0) ->
		(wf_num_ nt c_1) ->
		(wf_testop_ nt testop) ->
		(wf_num_ I32 c) ->
		(c == var_0) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_TESTOP nt testop)] [::(admininstr_CONST I32 c)]
	| Step_pure__relop : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (relop : relop_) (c : num_) (var_0 : num_), 
		(fun_relop_ nt relop c_1 c_2 var_0) ->
		(wf_num_ nt c_1) ->
		(wf_num_ nt c_2) ->
		(wf_relop_ nt relop) ->
		(wf_num_ I32 c) ->
		(c == var_0) ->
		Step_pure [::(admininstr_CONST nt c_1); (admininstr_CONST nt c_2); (admininstr_RELOP nt relop)] [::(admininstr_CONST I32 c)]
	| cvtop_val : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (v_cvtop : cvtop) (c : num_) (var_0 : (seq num_)), 
		(fun_cvtop__ nt_1 nt_2 v_cvtop c_1 var_0) ->
		(wf_num_ nt_1 c_1) ->
		(wf_num_ nt_2 c) ->
		((|var_0|) > 0) ->
		(c \in var_0) ->
		Step_pure [::(admininstr_CONST nt_1 c_1); (admininstr_CVTOP nt_2 nt_1 v_cvtop)] [::(admininstr_CONST nt_2 c)]
	| cvtop_trap : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (v_cvtop : cvtop) (var_0 : (seq num_)), 
		(fun_cvtop__ nt_1 nt_2 v_cvtop c_1 var_0) ->
		(wf_num_ nt_1 c_1) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_CONST nt_1 c_1); (admininstr_CVTOP nt_2 nt_1 v_cvtop)] [::admininstr_TRAP]
	| ref_is_null_true : forall (v_ref : ref) (rt : reftype), 
		(v_ref == (ref_REF_NULL rt)) ->
		Step_pure [::(admininstr_ref v_ref); admininstr_REF_IS_NULL] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1)))]
	| ref_is_null_false : forall (v_ref : ref) (rt : reftype), 
		(v_ref != (ref_REF_NULL rt)) ->
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
		(wf_num_ I32 c) ->
		((proj_num__0 c) != None) ->
		((res_size valtype_V128) != None) ->
		((!((proj_num__0 c))) == (ine_ (!((res_size valtype_V128))) c_1 (mk_uN 0))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VVTESTOP V128 ANY_TRUE)] [::(admininstr_CONST I32 c)]
	| Step_pure__vunop : forall (c_1 : vec_) (sh : shape) (vunop : vunop_) (c : vec_) (var_0 : (seq vec_)), 
		(fun_vunop_ sh vunop c_1 var_0) ->
		(wf_vunop_ sh vunop) ->
		((|var_0|) > 0) ->
		(c \in var_0) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VUNOP sh vunop)] [::(admininstr_VCONST V128 c)]
	| vunop_trap : forall (c_1 : vec_) (sh : shape) (vunop : vunop_) (var_0 : (seq vec_)), 
		(fun_vunop_ sh vunop c_1 var_0) ->
		(wf_vunop_ sh vunop) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VUNOP sh vunop)] [::admininstr_TRAP]
	| vbinop_val : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (c : vec_) (var_0 : (seq vec_)), 
		(fun_vbinop_ sh vbinop c_1 c_2 var_0) ->
		(wf_vbinop_ sh vbinop) ->
		((|var_0|) > 0) ->
		(c \in var_0) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VBINOP sh vbinop)] [::(admininstr_VCONST V128 c)]
	| vbinop_trap : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (var_0 : (seq vec_)), 
		(fun_vbinop_ sh vbinop c_1 c_2 var_0) ->
		(wf_vbinop_ sh vbinop) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VBINOP sh vbinop)] [::admininstr_TRAP]
	| vtestop_true : forall (c : vec_) (v_Jnn : Jnn) (v_N : res_N) (ci_1_lst : (seq lane_)), 
		List.Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ->
		List.Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != None)) ci_1_lst ->
		List.Forall (fun (ci_1 : lane_) => (((!((proj_lane__2 ci_1))) :> nat) != 0)) ci_1_lst ->
		Step_pure [::(admininstr_VCONST V128 c); (admininstr_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE))] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1)))]
	| vtestop_false : forall (c : vec_) (v_Jnn : Jnn) (v_N : res_N), 
		(~(Step_pure_before_vtestop_false [::(admininstr_VCONST V128 c); (admininstr_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE))])) ->
		Step_pure [::(admininstr_VCONST V128 c); (admininstr_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE))] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0)))]
	| Step_pure__vrelop : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vrelop : vrelop_) (c : vec_) (var_0 : vec_), 
		(fun_vrelop_ sh vrelop c_1 c_2 var_0) ->
		(wf_vrelop_ sh vrelop) ->
		(var_0 == c) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VRELOP sh vrelop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vshiftop : forall (c_1 : vec_) (v_n : n) (v_Jnn : Jnn) (v_N : res_N) (vshiftop : vshiftop_) (c : vec_) (c'_lst : (seq lane_)) (var_0_lst : (seq lane_)), 
		((|var_0_lst|) == (|c'_lst|)) ->
		List.Forall2 (fun (var_0 : lane_) (c' : lane_) => (fun_vshiftop_ (ishape_X v_Jnn (mk_dim v_N)) vshiftop c' (mk_uN v_n) var_0)) var_0_lst c'_lst ->
		(wf_vshiftop_ (ishape_X v_Jnn (mk_dim v_N)) vshiftop) ->
		List.Forall (fun (c' : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) c')) c'_lst ->
		(c'_lst == (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c_1)) ->
		(c == (inv_lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) var_0_lst)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_VSHIFTOP (ishape_X v_Jnn (mk_dim v_N)) vshiftop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vbitmask : forall (c : vec_) (v_Jnn : Jnn) (v_N : res_N) (ci : iN) (ci_1_lst : (seq lane_)) (var_0_lst : (seq uN)), 
		((|var_0_lst|) == (|ci_1_lst|)) ->
		List.Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != None)) ci_1_lst ->
		List.Forall2 (fun (var_0 : uN) (ci_1 : lane_) => (fun_ilt_ (lsize (lanetype_Jnn v_Jnn)) res_S (!((proj_lane__2 ci_1))) (mk_uN 0) var_0)) var_0_lst ci_1_lst ->
		List.Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ->
		((ibits_ 32 ci) == ((seq.map (fun (var_0 : uN) => (mk_bit (var_0 :> nat))) var_0_lst) ++ (List.repeat (mk_bit 0) (((32 : nat) - (v_N : nat)) : nat)))) ->
		Step_pure [::(admininstr_VCONST V128 c); (admininstr_VBITMASK (ishape_X v_Jnn (mk_dim v_N)))] [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (irev_ 32 ci)))]
	| Step_pure__vswizzle : forall (c_1 : vec_) (c_2 : vec_) (v_Pnn : Pnn) (v_M : M) (c : vec_) (ci_lst : (seq lane_)) (c'_lst : (seq iN)) (k : nat), 
		(((!((proj_lane__1 (ci_lst[| k |])))) :> nat) < (|c'_lst|)) ->
		((proj_lane__1 (ci_lst[| k |])) != None) ->
		(k < (|ci_lst|)) ->
		(wf_lane_ (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_M))) (mk_lane__1 v_Pnn (c'_lst[| ((!((proj_lane__1 (ci_lst[| k |])))) :> nat) |]))) ->
		(ci_lst == (lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_2)) ->
		List.Forall (fun (iter_0 : lane_) => ((proj_lane__1 iter_0) != None)) (lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1) ->
		(c'_lst == ((seq.map (fun (iter_0 : lane_) => (!((proj_lane__1 iter_0)))) (lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1)) ++ (List.repeat (mk_uN 0) (((256 : nat) - (v_M : nat)) : nat)))) ->
		(c == (inv_lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_M)) (seq.mkseq (fun k => (mk_lane__1 v_Pnn (c'_lst[| ((!((proj_lane__1 (ci_lst[| k |])))) :> nat) |]))) v_M))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VSWIZZLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M)))] [::(admininstr_VCONST V128 c)]
	| Step_pure__vshuffle : forall (c_1 : vec_) (c_2 : vec_) (v_Pnn : Pnn) (v_N : res_N) (i_lst : (seq laneidx)) (c : vec_) (c'_lst : (seq iN)) (k : nat), 
		List.Forall (fun (c' : iN) => (wf_lane_ (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) (mk_lane__1 v_Pnn c'))) c'_lst ->
		(((i_lst[| k |]) :> nat) < (|c'_lst|)) ->
		(k < (|i_lst|)) ->
		(wf_lane_ (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) (mk_lane__1 v_Pnn (c'_lst[| ((i_lst[| k |]) :> nat) |]))) ->
		((seq.map (fun (c' : iN) => (mk_lane__1 v_Pnn c')) c'_lst) == ((lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_1) ++ (lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_2))) ->
		(c == (inv_lanes_ (X (lanetype_packtype v_Pnn) (mk_dim v_N)) (seq.mkseq (fun k => (mk_lane__1 v_Pnn (c'_lst[| ((i_lst[| k |]) :> nat) |]))) v_N))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VSHUFFLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_N)) i_lst)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vsplat : forall (v_Lnn : Lnn) (c_1 : num_) (v_N : res_N) (c : vec_) (var_0 : lane_), 
		(fun_packnum_ v_Lnn c_1 var_0) ->
		(wf_num_ (unpack v_Lnn) c_1) ->
		(c == (inv_lanes_ (X v_Lnn (mk_dim v_N)) (List.repeat var_0 v_N))) ->
		Step_pure [::(admininstr_CONST (unpack v_Lnn) c_1); (admininstr_VSPLAT (X v_Lnn (mk_dim v_N)))] [::(admininstr_VCONST V128 c)]
	| vextract_lane_num : forall (c_1 : vec_) (nt : numtype) (v_N : res_N) (i : laneidx) (c_2 : num_), 
		(wf_lane_ (fun_lanetype (X (lanetype_numtype nt) (mk_dim v_N))) (mk_lane__0 nt c_2)) ->
		((i :> nat) < (|(lanes_ (X (lanetype_numtype nt) (mk_dim v_N)) c_1)|)) ->
		((mk_lane__0 nt c_2) == ((lanes_ (X (lanetype_numtype nt) (mk_dim v_N)) c_1)[| (i :> nat) |])) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i)] [::(admininstr_CONST nt c_2)]
	| vextract_lane_pack : forall (c_1 : vec_) (pt : packtype) (v_N : res_N) (v_sx : sx) (i : laneidx) (c_2 : num_), 
		(wf_num_ I32 c_2) ->
		((proj_num__0 c_2) != None) ->
		((proj_lane__1 ((lanes_ (X (lanetype_packtype pt) (mk_dim v_N)) c_1)[| (i :> nat) |])) != None) ->
		((i :> nat) < (|(lanes_ (X (lanetype_packtype pt) (mk_dim v_N)) c_1)|)) ->
		((!((proj_num__0 c_2))) == (extend__ (psize pt) 32 v_sx (!((proj_lane__1 ((lanes_ (X (lanetype_packtype pt) (mk_dim v_N)) c_1)[| (i :> nat) |])))))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i)] [::(admininstr_CONST I32 c_2)]
	| Step_pure__vreplace_lane : forall (c_1 : vec_) (v_Lnn : Lnn) (c_2 : num_) (v_N : res_N) (i : laneidx) (c : vec_) (var_0 : lane_), 
		(fun_packnum_ v_Lnn c_2 var_0) ->
		(wf_num_ (unpack v_Lnn) c_2) ->
		(c == (inv_lanes_ (X v_Lnn (mk_dim v_N)) (list_update_func (lanes_ (X v_Lnn (mk_dim v_N)) c_1) (i :> nat) (fun (_ : lane_) => var_0)))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_CONST (unpack v_Lnn) c_2); (admininstr_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vextunop : forall (c_1 : vec_) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop_) (c : vec_) (var_0 : vec_), 
		(fun_vextunop__ sh_1 sh_2 vextunop c_1 var_0) ->
		(wf_vextunop_ sh_1 vextunop) ->
		(var_0 == c) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VEXTUNOP sh_1 sh_2 vextunop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vextbinop : forall (c_1 : vec_) (c_2 : vec_) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop_) (c : vec_) (var_0 : vec_), 
		(fun_vextbinop__ sh_1 sh_2 vextbinop c_1 c_2 var_0) ->
		(wf_vextbinop_ sh_1 vextbinop) ->
		(var_0 == c) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VEXTBINOP sh_1 sh_2 vextbinop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__vnarrow : forall (c_1 : vec_) (c_2 : vec_) (Jnn_2 : Jnn) (N_2 : res_N) (Jnn_1 : Jnn) (N_1 : res_N) (v_sx : sx) (c : vec_) (ci_1_lst : (seq lane_)) (ci_2_lst : (seq lane_)) (cj_1_lst : (seq iN)) (cj_2_lst : (seq iN)), 
		List.Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ci_1)) ci_1_lst ->
		List.Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ci_2)) ci_2_lst ->
		List.Forall (fun (cj_1 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) (mk_lane__2 Jnn_2 cj_1))) cj_1_lst ->
		List.Forall (fun (cj_2 : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) (mk_lane__2 Jnn_2 cj_2))) cj_2_lst ->
		(ci_1_lst == (lanes_ (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_1)) ->
		(ci_2_lst == (lanes_ (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_2)) ->
		List.Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != None)) ci_1_lst ->
		(cj_1_lst == (seq.map (fun (ci_1 : lane_) => (narrow__ (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (!((proj_lane__2 ci_1))))) ci_1_lst)) ->
		List.Forall (fun (ci_2 : lane_) => ((proj_lane__2 ci_2) != None)) ci_2_lst ->
		(cj_2_lst == (seq.map (fun (ci_2 : lane_) => (narrow__ (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (!((proj_lane__2 ci_2))))) ci_2_lst)) ->
		(c == (inv_lanes_ (X (lanetype_Jnn Jnn_2) (mk_dim N_2)) ((seq.map (fun (cj_1 : iN) => (mk_lane__2 Jnn_2 cj_1)) cj_1_lst) ++ (seq.map (fun (cj_2 : iN) => (mk_lane__2 Jnn_2 cj_2)) cj_2_lst)))) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCONST V128 c_2); (admininstr_VNARROW (ishape_X Jnn_2 (mk_dim N_2)) (ishape_X Jnn_1 (mk_dim N_1)) v_sx)] [::(admininstr_VCONST V128 c)]
	| vcvtop_full : forall (c_1 : vec_) (Lnn_2 : Lnn) (v_M : M) (Lnn_1 : Lnn) (v_vcvtop : vcvtop) (c : vec_) (ci_lst : (seq lane_)) (cj_lst_lst : (seq (seq lane_))) (var_0_lst : (seq (seq lane_))), 
		((|var_0_lst|) == (|ci_lst|)) ->
		List.Forall2 (fun (var_0 : (seq lane_)) (ci : lane_) => (fun_vcvtop__ (X Lnn_1 (mk_dim v_M)) (X Lnn_2 (mk_dim v_M)) v_vcvtop ci var_0)) var_0_lst ci_lst ->
		List.Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (X Lnn_1 (mk_dim v_M))) ci)) ci_lst ->
		List.Forall (fun (cj_lst : (seq lane_)) => List.Forall (fun (cj : lane_) => (wf_lane_ Lnn_2 cj)) cj_lst) cj_lst_lst ->
		(((halfop v_vcvtop) == None) && ((zeroop v_vcvtop) == None)) ->
		(ci_lst == (lanes_ (X Lnn_1 (mk_dim v_M)) c_1)) ->
		(cj_lst_lst == (setproduct_ lane_ var_0_lst)) ->
		((|(seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X Lnn_2 (mk_dim v_M)) cj_lst)) cj_lst_lst)|) > 0) ->
		(c \in (seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X Lnn_2 (mk_dim v_M)) cj_lst)) cj_lst_lst)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCVTOP (X Lnn_2 (mk_dim v_M)) (X Lnn_1 (mk_dim v_M)) v_vcvtop)] [::(admininstr_VCONST V128 c)]
	| vcvtop_half : forall (c_1 : vec_) (Lnn_2 : Lnn) (M_2 : M) (Lnn_1 : Lnn) (M_1 : M) (v_vcvtop : vcvtop) (c : vec_) (v_half : half) (ci_lst : (seq lane_)) (cj_lst_lst : (seq (seq lane_))) (var_0_lst : (seq (seq lane_))), 
		((|var_0_lst|) == (|ci_lst|)) ->
		List.Forall2 (fun (var_0 : (seq lane_)) (ci : lane_) => (fun_vcvtop__ (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) v_vcvtop ci var_0)) var_0_lst ci_lst ->
		List.Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (X Lnn_1 (mk_dim M_1))) ci)) ci_lst ->
		List.Forall (fun (cj_lst : (seq lane_)) => List.Forall (fun (cj : lane_) => (wf_lane_ Lnn_2 cj)) cj_lst) cj_lst_lst ->
		((halfop v_vcvtop) == (Some v_half)) ->
		(ci_lst == (list_slice (lanes_ (X Lnn_1 (mk_dim M_1)) c_1) (fun_half v_half 0 M_2) M_2)) ->
		(cj_lst_lst == (setproduct_ lane_ var_0_lst)) ->
		((|(seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X Lnn_2 (mk_dim M_2)) cj_lst)) cj_lst_lst)|) > 0) ->
		(c \in (seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X Lnn_2 (mk_dim M_2)) cj_lst)) cj_lst_lst)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCVTOP (X Lnn_2 (mk_dim M_2)) (X Lnn_1 (mk_dim M_1)) v_vcvtop)] [::(admininstr_VCONST V128 c)]
	| vcvtop_zero : forall (c_1 : vec_) (nt_2 : numtype) (M_2 : M) (nt_1 : numtype) (M_1 : M) (v_vcvtop : vcvtop) (c : vec_) (ci_lst : (seq lane_)) (cj_lst_lst : (seq (seq lane_))) (var_1_lst : (seq (seq lane_))) (var_0 : num_), 
		((|var_1_lst|) == (|ci_lst|)) ->
		List.Forall2 (fun (var_1 : (seq lane_)) (ci : lane_) => (fun_vcvtop__ (X (lanetype_numtype nt_1) (mk_dim M_1)) (X (lanetype_numtype nt_2) (mk_dim M_2)) v_vcvtop ci var_1)) var_1_lst ci_lst ->
		(fun_zero nt_2 var_0) ->
		List.Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (X (lanetype_numtype nt_1) (mk_dim M_1))) ci)) ci_lst ->
		List.Forall (fun (cj_lst : (seq lane_)) => List.Forall (fun (cj : lane_) => (wf_lane_ (lanetype_numtype nt_2) cj)) cj_lst) cj_lst_lst ->
		(wf_lane_ (lanetype_numtype nt_2) (mk_lane__0 nt_2 var_0)) ->
		((zeroop v_vcvtop) == (Some ZERO)) ->
		(ci_lst == (lanes_ (X (lanetype_numtype nt_1) (mk_dim M_1)) c_1)) ->
		(cj_lst_lst == (setproduct_ lane_ (var_1_lst ++ (List.repeat [::(mk_lane__0 nt_2 var_0)] M_1)))) ->
		((|(seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst)) cj_lst_lst)|) > 0) ->
		(c \in (seq.map (fun (cj_lst : (seq lane_)) => (inv_lanes_ (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst)) cj_lst_lst)) ->
		Step_pure [::(admininstr_VCONST V128 c_1); (admininstr_VCVTOP (X (lanetype_numtype nt_2) (mk_dim M_2)) (X (lanetype_numtype nt_1) (mk_dim M_1)) v_vcvtop)] [::(admininstr_VCONST V128 c)]
	| Step_pure__local_tee : forall (v_val : val) (x : idx), Step_pure [::(admininstr_val v_val); (admininstr_LOCAL_TEE x)] [::(admininstr_val v_val); (admininstr_val v_val); (admininstr_LOCAL_SET x)].

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 *)
Definition fun_blocktype (v_state : state) (v_blocktype : blocktype) : functype :=
	match v_state, v_blocktype return functype with
		| z, (_RESULT None) => (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
		| z, (_RESULT (Some t)) => (mk_functype (mk_list _ [:: ]) (mk_list _ [::t]))
		| z, (_IDX x) => (fun_type z x)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:436.1-439.14 *)
Inductive Step_read_before_table_fill_zero : config -> Prop :=
	| table_fill_trap_0 : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n) > (|(REFS (fun_table z x))|)) ->
		Step_read_before_table_fill_zero (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_FILL x)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:452.1-455.14 *)
Inductive Step_read_before_table_copy_zero : config -> Prop :=
	| table_copy_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(REFS (fun_table z y))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(REFS (fun_table z x))|))) ->
		Step_read_before_table_copy_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:457.1-462.15 *)
Inductive Step_read_before_table_copy_le : config -> Prop :=
	| table_copy_zero_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		(~(Step_read_before_table_copy_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]))) ->
		(v_n == 0) ->
		Step_read_before_table_copy_le (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)])
	| table_copy_trap_1 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(REFS (fun_table z y))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(REFS (fun_table z x))|))) ->
		Step_read_before_table_copy_le (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:475.1-478.14 *)
Inductive Step_read_before_table_init_zero : config -> Prop :=
	| table_init_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(eleminst_REFS (fun_elem z y))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(REFS (fun_table z x))|))) ->
		Step_read_before_table_init_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_INIT x y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:616.1-619.14 *)
Inductive Step_read_before_memory_fill_zero : config -> Prop :=
	| memory_fill_trap_0 : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read_before_memory_fill_zero (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_FILL]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:632.1-635.14 *)
Inductive Step_read_before_memory_copy_zero : config -> Prop :=
	| memory_copy_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		Step_read_before_memory_copy_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:637.1-642.15 *)
Inductive Step_read_before_memory_copy_le : config -> Prop :=
	| memory_copy_zero_0 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		(~(Step_read_before_memory_copy_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]))) ->
		(v_n == 0) ->
		Step_read_before_memory_copy_le (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY])
	| memory_copy_trap_1 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		Step_read_before_memory_copy_le (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:655.1-658.14 *)
Inductive Step_read_before_memory_init_zero : config -> Prop :=
	| memory_init_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(datainst_BYTES (fun_data z x))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		Step_read_before_memory_init_zero (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_MEMORY_INIT x)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.77 *)
Inductive Step_read : config -> (seq admininstr) -> Prop :=
	| Step_read__block : forall (z : state) (k : nat) (val_lst : (seq val)) (bt : blocktype) (instr_lst : (seq instr)) (v_n : n) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		((fun_blocktype z bt) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Step_read (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_BLOCK bt instr_lst)])) [::(LABEL_ v_n [:: ] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))]
	| Step_read__loop : forall (z : state) (k : nat) (val_lst : (seq val)) (bt : blocktype) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (v_n : n) (t_2_lst : (seq valtype)), 
		((fun_blocktype z bt) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Step_read (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_LOOP bt instr_lst)])) [::(LABEL_ k [::(LOOP bt instr_lst)] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))]
	| Step_read__call : forall (z : state) (x : idx), 
		((x :> nat) < (|(fun_funcaddr z)|)) ->
		Step_read (mk_config z [::(admininstr_CALL x)]) [::(CALL_ADDR ((fun_funcaddr z)[| (x :> nat) |]))]
	| call_indirect_call : forall (z : state) (i : num_) (x : idx) (y : idx) (a : addr), 
		(wf_num_ I32 i) ->
		(((!((proj_num__0 i))) :> nat) < (|(REFS (fun_table z x))|)) ->
		((proj_num__0 i) != None) ->
		(((REFS (fun_table z x))[| ((!((proj_num__0 i))) :> nat) |]) == (REF_FUNC_ADDR a)) ->
		(a < (|(fun_funcinst z)|)) ->
		((fun_type z y) == (funcinst_TYPE ((fun_funcinst z)[| a |]))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x y)]) [::(CALL_ADDR a)]
	| call_indirect_trap : forall (z : state) (i : num_) (x : idx) (y : idx) (a : addr), 
		(((!((proj_num__0 i))) :> nat) < (|(REFS (fun_table z x))|)) ->
		((proj_num__0 i) != None) ->
		(a < (|(fun_funcinst z)|)) ->
		((((REFS (fun_table z x))[| ((!((proj_num__0 i))) :> nat) |]) != (REF_FUNC_ADDR a)) || ((fun_type z y) != (funcinst_TYPE ((fun_funcinst z)[| a |])))) ->
		(wf_num_ I32 i) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x y)]) [::admininstr_TRAP]
	| call_addr : forall (z : state) (k : nat) (val_lst : (seq val)) (a : addr) (v_n : n) (f : frame) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)) (mm : moduleinst) (v_func : func) (x : idx) (t_lst : (seq valtype)), 
		(a < (|(fun_funcinst z)|)) ->
		(((fun_funcinst z)[| a |]) == {| funcinst_TYPE := (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)); funcinst_MODULE := mm; CODE := v_func |}) ->
		(v_func == (func_FUNC x (seq.map (fun (t : valtype) => (LOCAL t)) t_lst) instr_lst)) ->
		List.Forall (fun (t : valtype) => ((default_ t) != None)) t_lst ->
		(f == {| LOCALS := (val_lst ++ (seq.map (fun (t : valtype) => (!((default_ t)))) t_lst)); frame_MODULE := mm |}) ->
		Step_read (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(CALL_ADDR a)])) [::(FRAME_ v_n f [::(LABEL_ v_n [:: ] (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))])]
	| Step_read__ref_func : forall (z : state) (x : idx), 
		((x :> nat) < (|(fun_funcaddr z)|)) ->
		Step_read (mk_config z [::(admininstr_REF_FUNC x)]) [::(admininstr_REF_FUNC_ADDR ((fun_funcaddr z)[| (x :> nat) |]))]
	| Step_read__local_get : forall (z : state) (x : idx), Step_read (mk_config z [::(admininstr_LOCAL_GET x)]) [::(admininstr_val (fun_local z x))]
	| Step_read__global_get : forall (z : state) (x : idx), Step_read (mk_config z [::(admininstr_GLOBAL_GET x)]) [::(admininstr_val (VALUE (fun_global z x)))]
	| table_get_trap : forall (z : state) (i : num_) (x : idx), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 i))) :> nat) >= (|(REFS (fun_table z x))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_TABLE_GET x)]) [::admininstr_TRAP]
	| table_get_val : forall (z : state) (i : num_) (x : idx), 
		(((!((proj_num__0 i))) :> nat) < (|(REFS (fun_table z x))|)) ->
		((proj_num__0 i) != None) ->
		(wf_num_ I32 i) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_TABLE_GET x)]) [::(admininstr_ref ((REFS (fun_table z x))[| ((!((proj_num__0 i))) :> nat) |]))]
	| Step_read__table_size : forall (z : state) (x : idx) (v_n : n), 
		((|(REFS (fun_table z x))|) == v_n) ->
		Step_read (mk_config z [::(admininstr_TABLE_SIZE x)]) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))]
	| table_fill_trap : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n) > (|(REFS (fun_table z x))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_FILL x)]) [::admininstr_TRAP]
	| table_fill_zero : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n) <= (|(REFS (fun_table z x))|)) ->
		(wf_num_ I32 i) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_FILL x)]) [:: ]
	| table_fill_succ : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		(v_n != 0) ->
		((((!((proj_num__0 i))) :> nat) + v_n) <= (|(REFS (fun_table z x))|)) ->
		(wf_num_ I32 i) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_FILL x)]) [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_TABLE_SET x); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)))); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : nat) - (1 : nat)) : nat)))); (admininstr_TABLE_FILL x)]
	| table_copy_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(REFS (fun_table z y))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(REFS (fun_table z x))|))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]) [::admininstr_TRAP]
	| table_copy_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(REFS (fun_table z y))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(REFS (fun_table z x))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]) [:: ]
	| table_copy_le : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 j) != None) ->
		((proj_num__0 i) != None) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(REFS (fun_table z y))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(REFS (fun_table z x))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		(((!((proj_num__0 j))) :> nat) <= ((!((proj_num__0 i))) :> nat)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]) [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_TABLE_GET y); (admininstr_TABLE_SET x); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 j))) :> nat) + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : nat) - (1 : nat)) : nat)))); (admininstr_TABLE_COPY x y)]
	| table_copy_gt : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 j) != None) ->
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 j))) :> nat) > ((!((proj_num__0 i))) :> nat)) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(REFS (fun_table z y))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(REFS (fun_table z x))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_COPY x y)]) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((((!((proj_num__0 j))) :> nat) + v_n) : nat) - (1 : nat)) : nat)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((((!((proj_num__0 i))) :> nat) + v_n) : nat) - (1 : nat)) : nat)))); (admininstr_TABLE_GET y); (admininstr_TABLE_SET x); (admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : nat) - (1 : nat)) : nat)))); (admininstr_TABLE_COPY x y)]
	| table_init_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(eleminst_REFS (fun_elem z y))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(REFS (fun_table z x))|))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_INIT x y)]) [::admininstr_TRAP]
	| table_init_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(eleminst_REFS (fun_elem z y))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(REFS (fun_table z x))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_INIT x y)]) [:: ]
	| table_init_succ : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
		(((!((proj_num__0 i))) :> nat) < (|(eleminst_REFS (fun_elem z y))|)) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(eleminst_REFS (fun_elem z y))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(REFS (fun_table z x))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_INIT x y)]) [::(admininstr_CONST I32 j); (admininstr_ref ((eleminst_REFS (fun_elem z y))[| ((!((proj_num__0 i))) :> nat) |])); (admininstr_TABLE_SET x); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 j))) :> nat) + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : nat) - (1 : nat)) : nat)))); (admininstr_TABLE_INIT x y)]
	| load_num_trap : forall (z : state) (i : num_) (nt : numtype) (ao : memarg), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((res_size (valtype_numtype nt)) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + ((((!((res_size (valtype_numtype nt)))) : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD nt None ao)]) [::admininstr_TRAP]
	| load_num_val : forall (z : state) (i : num_) (nt : numtype) (ao : memarg) (c : num_), 
		(wf_num_ I32 i) ->
		(wf_num_ nt c) ->
		((proj_num__0 i) != None) ->
		((res_size (valtype_numtype nt)) != None) ->
		((nbytes_ nt c) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) ((((!((res_size (valtype_numtype nt)))) : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD nt None ao)]) [::(admininstr_CONST nt c)]
	| load_pack_trap : forall (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + (((v_n : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)]) [::admininstr_TRAP]
	| load_pack_val : forall (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) (c : iN), 
		((res_size (valtype_Inn v_Inn)) != None) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((ibytes_ v_n c) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_n : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)]) [::(admininstr_CONST (numtype_Inn v_Inn) (mk_num__0 v_Inn (extend__ v_n (!((res_size (valtype_Inn v_Inn)))) v_sx c)))]
	| vload_oob : forall (z : state) (i : num_) (ao : memarg), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((res_size valtype_V128) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + ((((!((res_size valtype_V128))) : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 None ao)]) [::admininstr_TRAP]
	| vload_val : forall (z : state) (i : num_) (ao : memarg) (c : vec_), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((res_size valtype_V128) != None) ->
		((vbytes_ V128 c) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) ((((!((res_size valtype_V128))) : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 None ao)]) [::(admininstr_VCONST V128 c)]
	| vload_shape_oob : forall (z : state) (i : num_) (v_M : M) (v_N : res_N) (v_sx : sx) (ao : memarg), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + ((((v_M * v_N) : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (SHAPEX_ v_M v_N v_sx)) ao)]) [::admininstr_TRAP]
	| vload_shape_val : forall (z : state) (i : num_) (v_M : M) (v_N : res_N) (v_sx : sx) (ao : memarg) (c : vec_) (j_lst : (seq iN)) (v_Jnn : Jnn), 
		(wf_num_ I32 i) ->
		List.Forall (fun (j : iN) => (wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) (mk_lane__2 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j)))) j_lst ->
		((proj_num__0 i) != None) ->
		List_Foralli (fun k (j : iN) => ((ibytes_ v_M j) == (list_slice (BYTES (fun_mem z (mk_uN 0))) ((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + ((((k * v_M) : nat) / (8 : nat)) : nat)) (((v_M : nat) / (8 : nat)) : nat)))) j_lst ->
		((jsize v_Jnn) == (v_M * 2)) ->
		(c == (inv_lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (seq.map (fun (j : iN) => (mk_lane__2 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j))) j_lst))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (SHAPEX_ v_M v_N v_sx)) ao)]) [::(admininstr_VCONST V128 c)]
	| vload_splat_oob : forall (z : state) (i : num_) (v_N : res_N) (ao : memarg), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + (((v_N : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (SPLAT v_N)) ao)]) [::admininstr_TRAP]
	| vload_splat_val : forall (z : state) (i : num_) (v_N : res_N) (ao : memarg) (c : vec_) (j : iN) (v_Jnn : Jnn) (v_M : M), 
		(wf_num_ I32 i) ->
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (j :> nat)))) ->
		((proj_num__0 i) != None) ->
		((ibytes_ v_N j) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N == (jsize v_Jnn)) ->
		((v_M : nat) == ((128 : nat) / (v_N : nat))) ->
		(c == (inv_lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (List.repeat (mk_lane__2 v_Jnn (mk_uN (j :> nat))) v_M))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (SPLAT v_N)) ao)]) [::(admininstr_VCONST V128 c)]
	| vload_zero_oob : forall (z : state) (i : num_) (v_N : res_N) (ao : memarg), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + (((v_N : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (vloadop_ZERO v_N)) ao)]) [::admininstr_TRAP]
	| vload_zero_val : forall (z : state) (i : num_) (v_N : res_N) (ao : memarg) (c : vec_) (j : iN), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((ibytes_ v_N j) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_N : nat) / (8 : nat)) : nat))) ->
		(c == (extend__ v_N 128 U j)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VLOAD V128 (Some (vloadop_ZERO v_N)) ao)]) [::(admininstr_VCONST V128 c)]
	| vload_lane_oob : forall (z : state) (i : num_) (c_1 : vec_) (v_N : res_N) (ao : memarg) (j : laneidx), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + (((v_N : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c_1); (admininstr_VLOAD_LANE V128 (mk_sz v_N) ao j)]) [::admininstr_TRAP]
	| vload_lane_val : forall (z : state) (i : num_) (c_1 : vec_) (v_N : res_N) (ao : memarg) (j : laneidx) (c : vec_) (k : iN) (v_Jnn : Jnn) (v_M : M), 
		(wf_num_ I32 i) ->
		(wf_lane_ (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (k :> nat)))) ->
		((proj_num__0 i) != None) ->
		((ibytes_ v_N k) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N == (jsize v_Jnn)) ->
		((v_M : nat) == ((128 : nat) / (v_N : nat))) ->
		(c == (inv_lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (list_update_func (lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) (j :> nat) (fun (_ : lane_) => (mk_lane__2 v_Jnn (mk_uN (k :> nat))))))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c_1); (admininstr_VLOAD_LANE V128 (mk_sz v_N) ao j)]) [::(admininstr_VCONST V128 c)]
	| Step_read__memory_size : forall (z : state) (v_n : n), 
		(((v_n * 64) * (Ki )) == (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::admininstr_MEMORY_SIZE]) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))]
	| memory_fill_trap : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_FILL]) [::admininstr_TRAP]
	| memory_fill_zero : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
		((proj_num__0 i) != None) ->
		((((!((proj_num__0 i))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		(wf_num_ I32 i) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_FILL]) [:: ]
	| memory_fill_succ : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
		((proj_num__0 i) != None) ->
		(v_n != 0) ->
		((((!((proj_num__0 i))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		(wf_num_ I32 i) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_FILL]) [::(admininstr_CONST I32 i); (admininstr_val v_val); (admininstr_STORE I32 (Some (mk_sz 8)) (memarg0 )); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)))); (admininstr_val v_val); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : nat) - (1 : nat)) : nat)))); admininstr_MEMORY_FILL]
	| memory_copy_trap : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]) [::admininstr_TRAP]
	| memory_copy_zero : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]) [:: ]
	| memory_copy_le : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 j) != None) ->
		((proj_num__0 i) != None) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		(((!((proj_num__0 j))) :> nat) <= ((!((proj_num__0 i))) :> nat)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]) [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) (memarg0 )); (admininstr_STORE I32 (Some (mk_sz 8)) (memarg0 )); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 j))) :> nat) + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : nat) - (1 : nat)) : nat)))); admininstr_MEMORY_COPY]
	| memory_copy_gt : forall (z : state) (j : num_) (i : num_) (v_n : n), 
		((proj_num__0 j) != None) ->
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 j))) :> nat) > ((!((proj_num__0 i))) :> nat)) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_COPY]) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((((!((proj_num__0 j))) :> nat) + v_n) : nat) - (1 : nat)) : nat)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((((!((proj_num__0 i))) :> nat) + v_n) : nat) - (1 : nat)) : nat)))); (admininstr_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) (memarg0 )); (admininstr_STORE I32 (Some (mk_sz 8)) (memarg0 )); (admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : nat) - (1 : nat)) : nat)))); admininstr_MEMORY_COPY]
	| memory_init_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) > (|(datainst_BYTES (fun_data z x))|)) || ((((!((proj_num__0 j))) :> nat) + v_n) > (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_MEMORY_INIT x)]) [::admininstr_TRAP]
	| memory_init_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(datainst_BYTES (fun_data z x))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		(v_n == 0) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_MEMORY_INIT x)]) [:: ]
	| memory_init_succ : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
		(((!((proj_num__0 i))) :> nat) < (|(datainst_BYTES (fun_data z x))|)) ->
		((proj_num__0 i) != None) ->
		((proj_num__0 j) != None) ->
		(v_n != 0) ->
		(((((!((proj_num__0 i))) :> nat) + v_n) <= (|(datainst_BYTES (fun_data z x))|)) && ((((!((proj_num__0 j))) :> nat) + v_n) <= (|(BYTES (fun_mem z (mk_uN 0)))|))) ->
		(wf_num_ I32 j) ->
		(wf_num_ I32 i) ->
		Step_read (mk_config z [::(admininstr_CONST I32 j); (admininstr_CONST I32 i); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_MEMORY_INIT x)]) [::(admininstr_CONST I32 j); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((datainst_BYTES (fun_data z x))[| ((!((proj_num__0 i))) :> nat) |]) :> nat)))); (admininstr_STORE I32 (Some (mk_sz 8)) (memarg0 )); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 j))) :> nat) + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((!((proj_num__0 i))) :> nat) + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n : nat) - (1 : nat)) : nat)))); (admininstr_MEMORY_INIT x)].

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.77 *)
Inductive Step : config -> config -> Prop :=
	| pure : forall (z : state) (admininstr_lst : (seq admininstr)) (admininstr'_lst : (seq admininstr)), 
		(Step_pure admininstr_lst admininstr'_lst) ->
		Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)
	| read : forall (z : state) (admininstr_lst : (seq admininstr)) (admininstr'_lst : (seq admininstr)), 
		(Step_read (mk_config z admininstr_lst) admininstr'_lst) ->
		Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)
	| ctxt_label : forall (z : state) (v_n : n) (instr_0_lst : (seq instr)) (admininstr_lst : (seq admininstr)) (z' : state) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ->
		Step (mk_config z [::(LABEL_ v_n instr_0_lst admininstr_lst)]) (mk_config z' [::(LABEL_ v_n instr_0_lst admininstr'_lst)])
	| ctxt_frame : forall (s : store) (f : frame) (v_n : n) (f' : frame) (admininstr_lst : (seq admininstr)) (s' : store) (f'' : frame) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config (mk_state s f') admininstr_lst) (mk_config (mk_state s' f'') admininstr'_lst)) ->
		Step (mk_config (mk_state s f) [::(FRAME_ v_n f' admininstr_lst)]) (mk_config (mk_state s' f) [::(FRAME_ v_n f'' admininstr'_lst)])
	| ctxt_instrs : forall (z : state) (val_lst : (seq val)) (admininstr_lst : (seq admininstr)) (admininstr_1_lst : (seq admininstr)) (z' : state) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ->
		((val_lst != [:: ]) || (admininstr_1_lst != [:: ])) ->
		Step (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (admininstr_lst ++ admininstr_1_lst))) (mk_config z' ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (admininstr'_lst ++ admininstr_1_lst)))
	| Step__local_set : forall (z : state) (v_val : val) (x : idx), Step (mk_config z [::(admininstr_val v_val); (admininstr_LOCAL_SET x)]) (mk_config (with_local z x v_val) [:: ])
	| Step__global_set : forall (z : state) (v_val : val) (x : idx), Step (mk_config z [::(admininstr_val v_val); (admininstr_GLOBAL_SET x)]) (mk_config (with_global z x v_val) [:: ])
	| table_set_trap : forall (z : state) (i : num_) (v_ref : ref) (x : idx), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((!((proj_num__0 i))) :> nat) >= (|(REFS (fun_table z x))|)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_ref v_ref); (admininstr_TABLE_SET x)]) (mk_config z [::admininstr_TRAP])
	| table_set_val : forall (z : state) (i : num_) (v_ref : ref) (x : idx), 
		((proj_num__0 i) != None) ->
		(wf_num_ I32 i) ->
		(((!((proj_num__0 i))) :> nat) < (|(REFS (fun_table z x))|)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_ref v_ref); (admininstr_TABLE_SET x)]) (mk_config (with_table z x ((!((proj_num__0 i))) :> nat) v_ref) [:: ])
	| table_grow_succeed : forall (z : state) (v_ref : ref) (v_n : n) (x : idx) (ti : tableinst) (var_0 : (option tableinst)), 
		(fun_growtable (fun_table z x) v_n v_ref var_0) ->
		(var_0 != None) ->
		((!(var_0)) == ti) ->
		Step (mk_config z [::(admininstr_ref v_ref); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_GROW x)]) (mk_config (with_tableinst z x ti) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (|(REFS (fun_table z x))|))))])
	| table_grow_fail : forall (z : state) (v_ref : ref) (v_n : n) (x : idx) (var_0 : nat), 
		(fun_inv_signed_ 32 (0 - (1 : nat)) var_0) ->
		Step (mk_config z [::(admininstr_ref v_ref); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (admininstr_TABLE_GROW x)]) (mk_config z [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN var_0)))])
	| Step__elem_drop : forall (z : state) (x : idx), Step (mk_config z [::(admininstr_ELEM_DROP x)]) (mk_config (with_elem z x [:: ]) [:: ])
	| store_num_trap : forall (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg), 
		(wf_num_ I32 i) ->
		(wf_num_ nt c) ->
		((proj_num__0 i) != None) ->
		((res_size (valtype_numtype nt)) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + ((((!((res_size (valtype_numtype nt)))) : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST nt c); (admininstr_STORE nt None ao)]) (mk_config z [::admininstr_TRAP])
	| store_num_val : forall (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) (b_lst : (seq byte)), 
		((proj_num__0 i) != None) ->
		((res_size (valtype_numtype nt)) != None) ->
		(wf_num_ I32 i) ->
		(wf_num_ nt c) ->
		(b_lst == (nbytes_ nt c)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST nt c); (admininstr_STORE nt None ao)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) ((((!((res_size (valtype_numtype nt)))) : nat) / (8 : nat)) : nat) b_lst) [:: ])
	| store_pack_trap : forall (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg), 
		(wf_num_ I32 i) ->
		(wf_num_ (numtype_Inn v_Inn) c) ->
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + (((v_n : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST (numtype_Inn v_Inn) c); (admininstr_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]) (mk_config z [::admininstr_TRAP])
	| store_pack_val : forall (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) (b_lst : (seq byte)), 
		((proj_num__0 i) != None) ->
		(wf_num_ I32 i) ->
		(wf_num_ (numtype_Inn v_Inn) c) ->
		((res_size (valtype_Inn v_Inn)) != None) ->
		((proj_num__0 c) != None) ->
		(b_lst == (ibytes_ v_n (wrap__ (!((res_size (valtype_Inn v_Inn)))) v_n (!((proj_num__0 c)))))) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST (numtype_Inn v_Inn) c); (admininstr_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_n : nat) / (8 : nat)) : nat) b_lst) [:: ])
	| vstore_oob : forall (z : state) (i : num_) (c : vec_) (ao : memarg), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		((res_size valtype_V128) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + ((((!((res_size valtype_V128))) : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c); (admininstr_VSTORE V128 ao)]) (mk_config z [::admininstr_TRAP])
	| vstore_val : forall (z : state) (i : num_) (c : vec_) (ao : memarg) (b_lst : (seq byte)), 
		((proj_num__0 i) != None) ->
		((res_size valtype_V128) != None) ->
		(wf_num_ I32 i) ->
		(b_lst == (vbytes_ V128 c)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c); (admininstr_VSTORE V128 ao)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) ((((!((res_size valtype_V128))) : nat) / (8 : nat)) : nat) b_lst) [:: ])
	| vstore_lane_oob : forall (z : state) (i : num_) (c : vec_) (v_N : res_N) (ao : memarg) (j : laneidx), 
		(wf_num_ I32 i) ->
		((proj_num__0 i) != None) ->
		(((((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) + v_N) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c); (admininstr_VSTORE_LANE V128 (mk_sz v_N) ao j)]) (mk_config z [::admininstr_TRAP])
	| vstore_lane_val : forall (z : state) (i : num_) (c : vec_) (v_N : res_N) (ao : memarg) (j : laneidx) (b_lst : (seq byte)) (v_Jnn : Jnn) (v_M : M), 
		((proj_num__0 i) != None) ->
		(wf_num_ I32 i) ->
		(v_N == (jsize v_Jnn)) ->
		((v_M : nat) == ((128 : nat) / (v_N : nat))) ->
		((proj_lane__2 ((lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c)[| (j :> nat) |])) != None) ->
		((j :> nat) < (|(lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c)|)) ->
		(b_lst == (ibytes_ v_N (mk_uN ((!((proj_lane__2 ((lanes_ (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c)[| (j :> nat) |])))) :> nat)))) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_VCONST V128 c); (admininstr_VSTORE_LANE V128 (mk_sz v_N) ao j)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_num__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_N : nat) / (8 : nat)) : nat) b_lst) [:: ])
	| memory_grow_succeed : forall (z : state) (v_n : n) (mi : meminst) (var_0 : (option meminst)), 
		(fun_growmemory (fun_mem z (mk_uN 0)) v_n var_0) ->
		(var_0 != None) ->
		((!(var_0)) == mi) ->
		Step (mk_config z [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_GROW]) (mk_config (with_meminst z (mk_uN 0) mi) [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((|(BYTES (fun_mem z (mk_uN 0)))|) : nat) / ((64 * (Ki )) : nat)) : nat))))])
	| memory_grow_fail : forall (z : state) (v_n : n) (var_0 : nat), 
		(fun_inv_signed_ 32 (0 - (1 : nat)) var_0) ->
		Step (mk_config z [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_GROW]) (mk_config z [::(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN var_0)))])
	| Step__data_drop : forall (z : state) (x : idx), Step (mk_config z [::(admininstr_DATA_DROP x)]) (mk_config (with_data z x [:: ]) [:: ]).

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 *)
Inductive Steps : config -> config -> Prop :=
	| Steps__refl : forall (z : state) (admininstr_lst : (seq admininstr)), Steps (mk_config z admininstr_lst) (mk_config z admininstr_lst)
	| trans : forall (z : state) (admininstr_lst : (seq admininstr)) (z'' : state) (admininstr''_lst : (seq admininstr)) (z' : state) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ->
		(Steps (mk_config z' admininstr'_lst) (mk_config z'' admininstr''_lst)) ->
		Steps (mk_config z admininstr_lst) (mk_config z'' admininstr''_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83 *)
Inductive Eval_expr : state -> expr -> state -> (seq val) -> Prop :=
	| mk_Eval_expr : forall (z : state) (instr_lst : (seq instr)) (z' : state) (val_lst : (seq val)), 
		(Steps (mk_config z (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)) (mk_config z' (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))) ->
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
Inductive fun_allocfunc : store -> moduleinst -> func -> store * funcaddr -> Prop :=
	| fun_allocfunc_case_0 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (fi : funcinst) (x : uN) (local_lst : (seq local)) (v_expr : (seq instr)), 
		((x :> nat) < (|(TYPES v_moduleinst)|)) ->
		(fi == {| funcinst_TYPE := ((TYPES v_moduleinst)[| (x :> nat) |]); funcinst_MODULE := v_moduleinst; CODE := v_func |}) ->
		(v_func == (func_FUNC x local_lst v_expr)) ->
		fun_allocfunc s v_moduleinst v_func ((s <| store_FUNCS := ((store_FUNCS s) ++ [::fi]) |>), (|(store_FUNCS s)|)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
Inductive fun_allocfuncs : store -> moduleinst -> (seq func) -> store * (seq funcaddr) -> Prop :=
	| fun_allocfuncs_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_allocfuncs s v_moduleinst [:: ] (s, [:: ])
	| fun_allocfuncs_case_1 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (func'_lst : (seq func)) (s_2 : store) (fa : nat) (fa'_lst : (seq funcaddr)) (s_1 : store) (var_1 : store * (seq funcaddr)) (var_0 : store * funcaddr), 
		(fun_allocfuncs s_1 v_moduleinst func'_lst var_1) ->
		(fun_allocfunc s v_moduleinst v_func var_0) ->
		((s_1, fa) == var_0) ->
		((s_2, fa'_lst) == var_1) ->
		fun_allocfuncs s v_moduleinst ([::v_func] ++ func'_lst) (s_2, ([::fa] ++ fa'_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
Inductive fun_allocglobal : store -> globaltype -> val -> store * globaladdr -> Prop :=
	| fun_allocglobal_case_0 : forall (s : store) (v_globaltype : globaltype) (v_val : val) (gi : globalinst), 
		(gi == {| globalinst_TYPE := v_globaltype; VALUE := v_val |}) ->
		fun_allocglobal s v_globaltype v_val ((s <| store_GLOBALS := ((store_GLOBALS s) ++ [::gi]) |>), (|(store_GLOBALS s)|)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
Inductive fun_allocglobals : store -> (seq globaltype) -> (seq val) -> store * (seq globaladdr) -> Prop :=
	| fun_allocglobals_case_0 : forall (s : store), fun_allocglobals s [:: ] [:: ] (s, [:: ])
	| fun_allocglobals_case_1 : forall (s : store) (v_globaltype : globaltype) (globaltype'_lst : (seq globaltype)) (v_val : val) (val'_lst : (seq val)) (s_2 : store) (ga : nat) (ga'_lst : (seq globaladdr)) (s_1 : store) (var_1 : store * (seq globaladdr)) (var_0 : store * globaladdr), 
		(fun_allocglobals s_1 globaltype'_lst val'_lst var_1) ->
		(fun_allocglobal s v_globaltype v_val var_0) ->
		((s_1, ga) == var_0) ->
		((s_2, ga'_lst) == var_1) ->
		fun_allocglobals s ([::v_globaltype] ++ globaltype'_lst) ([::v_val] ++ val'_lst) (s_2, ([::ga] ++ ga'_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
Inductive fun_alloctable : store -> tabletype -> store * tableaddr -> Prop :=
	| fun_alloctable_case_0 : forall (s : store) (i : uN) (j_opt : (option u32)) (rt : reftype) (ti : tableinst), 
		(ti == {| tableinst_TYPE := (mk_tabletype (mk_limits i j_opt) rt); REFS := (List.repeat (ref_REF_NULL rt) (i :> nat)) |}) ->
		fun_alloctable s (mk_tabletype (mk_limits i j_opt) rt) ((s <| store_TABLES := ((store_TABLES s) ++ [::ti]) |>), (|(store_TABLES s)|)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
Inductive fun_alloctables : store -> (seq tabletype) -> store * (seq tableaddr) -> Prop :=
	| fun_alloctables_case_0 : forall (s : store), fun_alloctables s [:: ] (s, [:: ])
	| fun_alloctables_case_1 : forall (s : store) (v_tabletype : tabletype) (tabletype'_lst : (seq tabletype)) (s_2 : store) (ta : nat) (ta'_lst : (seq tableaddr)) (s_1 : store) (var_1 : store * (seq tableaddr)) (var_0 : store * tableaddr), 
		(fun_alloctables s_1 tabletype'_lst var_1) ->
		(fun_alloctable s v_tabletype var_0) ->
		((s_1, ta) == var_0) ->
		((s_2, ta'_lst) == var_1) ->
		fun_alloctables s ([::v_tabletype] ++ tabletype'_lst) (s_2, ([::ta] ++ ta'_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
Inductive fun_allocmem : store -> memtype -> store * memaddr -> Prop :=
	| fun_allocmem_case_0 : forall (s : store) (i : uN) (j_opt : (option u32)) (mi : meminst), 
		(mi == {| meminst_TYPE := (PAGE (mk_limits i j_opt)); BYTES := (List.repeat (mk_byte 0) ((i :> nat) * (64 * (Ki )))) |}) ->
		fun_allocmem s (PAGE (mk_limits i j_opt)) ((s <| store_MEMS := ((store_MEMS s) ++ [::mi]) |>), (|(store_MEMS s)|)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
Inductive fun_allocmems : store -> (seq memtype) -> store * (seq memaddr) -> Prop :=
	| fun_allocmems_case_0 : forall (s : store), fun_allocmems s [:: ] (s, [:: ])
	| fun_allocmems_case_1 : forall (s : store) (v_memtype : memtype) (memtype'_lst : (seq memtype)) (s_2 : store) (ma : nat) (ma'_lst : (seq memaddr)) (s_1 : store) (var_1 : store * (seq memaddr)) (var_0 : store * memaddr), 
		(fun_allocmems s_1 memtype'_lst var_1) ->
		(fun_allocmem s v_memtype var_0) ->
		((s_1, ma) == var_0) ->
		((s_2, ma'_lst) == var_1) ->
		fun_allocmems s ([::v_memtype] ++ memtype'_lst) (s_2, ([::ma] ++ ma'_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
Inductive fun_allocelem : store -> reftype -> (seq ref) -> store * elemaddr -> Prop :=
	| fun_allocelem_case_0 : forall (s : store) (rt : reftype) (ref_lst : (seq ref)) (ei : eleminst), 
		(ei == {| eleminst_TYPE := rt; eleminst_REFS := ref_lst |}) ->
		fun_allocelem s rt ref_lst ((s <| store_ELEMS := ((store_ELEMS s) ++ [::ei]) |>), (|(store_ELEMS s)|)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
Inductive fun_allocelems : store -> (seq reftype) -> (seq (seq ref)) -> store * (seq elemaddr) -> Prop :=
	| fun_allocelems_case_0 : forall (s : store), fun_allocelems s [:: ] [:: ] (s, [:: ])
	| fun_allocelems_case_1 : forall (s : store) (rt : reftype) (rt'_lst : (seq reftype)) (ref_lst : (seq ref)) (ref'_lst_lst : (seq (seq ref))) (s_2 : store) (ea : nat) (ea'_lst : (seq elemaddr)) (s_1 : store) (var_1 : store * (seq elemaddr)) (var_0 : store * elemaddr), 
		(fun_allocelems s_1 rt'_lst ref'_lst_lst var_1) ->
		(fun_allocelem s rt ref_lst var_0) ->
		((s_1, ea) == var_0) ->
		((s_2, ea'_lst) == var_1) ->
		fun_allocelems s ([::rt] ++ rt'_lst) ([::ref_lst] ++ ref'_lst_lst) (s_2, ([::ea] ++ ea'_lst)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
Inductive fun_allocdata : store -> (seq byte) -> store * dataaddr -> Prop :=
	| fun_allocdata_case_0 : forall (s : store) (byte_lst : (seq byte)) (di : datainst), 
		(di == {| datainst_BYTES := byte_lst |}) ->
		fun_allocdata s byte_lst ((s <| store_DATAS := ((store_DATAS s) ++ [::di]) |>), (|(store_DATAS s)|)).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
Inductive fun_allocdatas : store -> (seq (seq byte)) -> store * (seq dataaddr) -> Prop :=
	| fun_allocdatas_case_0 : forall (s : store), fun_allocdatas s [:: ] (s, [:: ])
	| fun_allocdatas_case_1 : forall (s : store) (byte_lst : (seq byte)) (byte'_lst_lst : (seq (seq byte))) (s_2 : store) (da : nat) (da'_lst : (seq dataaddr)) (s_1 : store) (var_1 : store * (seq dataaddr)) (var_0 : store * dataaddr), 
		(fun_allocdatas s_1 byte'_lst_lst var_1) ->
		(fun_allocdata s byte_lst var_0) ->
		((s_1, da) == var_0) ->
		((s_2, da'_lst) == var_1) ->
		fun_allocdatas s ([::byte_lst] ++ byte'_lst_lst) (s_2, ([::da] ++ da'_lst)).

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:100.1-100.83 *)
Definition instexport (var_0 : (seq funcaddr)) (var_1 : (seq globaladdr)) (var_2 : (seq tableaddr)) (var_3 : (seq memaddr)) (v_export : export) : exportinst :=
	match var_0, var_1, var_2, var_3, v_export return exportinst with
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_FUNC x)) => {| NAME := v_name; ADDR := (externaddr_FUNC (fa_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_GLOBAL x)) => {| NAME := v_name; ADDR := (externaddr_GLOBAL (ga_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_TABLE x)) => {| NAME := v_name; ADDR := (externaddr_TABLE (ta_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_MEM x)) => {| NAME := v_name; ADDR := (externaddr_MEM (ma_lst[| (x :> nat) |])) |}
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
Inductive fun_allocmodule : store -> module -> (seq externaddr) -> (seq val) -> (seq (seq ref)) -> store * moduleinst -> Prop :=
	| fun_allocmodule_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (seq externaddr)) (val_lst : (seq val)) (ref_lst_lst : (seq (seq ref))) (s_6 : store) (v_moduleinst : moduleinst) (ft_lst : (seq functype)) (import_lst : (seq import)) (n_func : nat) (func_lst : (seq func)) (n_global : nat) (expr_1_lst : (seq expr)) (globaltype_lst : (seq globaltype)) (n_table : nat) (tabletype_lst : (seq tabletype)) (n_mem : nat) (memtype_lst : (seq memtype)) (n_elem : nat) (elemmode_lst : (seq elemmode)) (expr_2_lst_lst : (seq (seq expr))) (rt_lst : (seq reftype)) (n_data : nat) (byte_lst_lst : (seq (seq byte))) (datamode_lst : (seq datamode)) (start_opt : (option start)) (export_lst : (seq export)) (fa_ex_lst : (seq funcaddr)) (ga_ex_lst : (seq globaladdr)) (ta_ex_lst : (seq tableaddr)) (ma_ex_lst : (seq memaddr)) (fa_lst : (seq funcaddr)) (ga_lst : (seq globaladdr)) (ta_lst : (seq tableaddr)) (ma_lst : (seq memaddr)) (ea_lst : (seq elemaddr)) (da_lst : (seq dataaddr)) (xi_lst : (seq exportinst)) (s_1 : store) (s_2 : store) (s_3 : store) (s_4 : store) (s_5 : store) (var_9 : store * (seq dataaddr)) (var_8 : store * (seq elemaddr)) (var_7 : store * (seq memaddr)) (var_6 : store * (seq tableaddr)) (var_5 : store * (seq globaladdr)) (var_4 : store * (seq funcaddr)) (var_3 : (seq memaddr)) (var_2 : (seq tableaddr)) (var_1 : (seq globaladdr)) (var_0 : (seq funcaddr)), 
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
		(v_module == (MODULE (seq.map (fun (ft : functype) => (TYPE ft)) ft_lst) import_lst func_lst (list_zipWith (fun (expr_1 : expr) (v_globaltype : globaltype) => (global_GLOBAL v_globaltype expr_1)) expr_1_lst globaltype_lst) (seq.map (fun (v_tabletype : tabletype) => (table_TABLE v_tabletype)) tabletype_lst) (seq.map (fun (v_memtype : memtype) => (MEMORY v_memtype)) memtype_lst) (list_map3 (fun (v_elemmode : elemmode) (expr_2_lst : (seq expr)) (rt : reftype) => (ELEM rt expr_2_lst v_elemmode)) elemmode_lst expr_2_lst_lst rt_lst) (list_zipWith (fun (byte_lst : (seq byte)) (v_datamode : datamode) => (DATA byte_lst v_datamode)) byte_lst_lst datamode_lst) start_opt export_lst)) ->
		(fa_ex_lst == var_0) ->
		(ga_ex_lst == var_1) ->
		(ta_ex_lst == var_2) ->
		(ma_ex_lst == var_3) ->
		(fa_lst == (seq.mkseq (fun i_func => ((|(store_FUNCS s)|) + i_func)) n_func)) ->
		(ga_lst == (seq.mkseq (fun i_global => ((|(store_GLOBALS s)|) + i_global)) n_global)) ->
		(ta_lst == (seq.mkseq (fun i_table => ((|(store_TABLES s)|) + i_table)) n_table)) ->
		(ma_lst == (seq.mkseq (fun i_mem => ((|(store_MEMS s)|) + i_mem)) n_mem)) ->
		(ea_lst == (seq.mkseq (fun i_elem => ((|(store_ELEMS s)|) + i_elem)) n_elem)) ->
		(da_lst == (seq.mkseq (fun i_data => ((|(store_DATAS s)|) + i_data)) n_data)) ->
		(xi_lst == (seq.map (fun (v_export : export) => (instexport (fa_ex_lst ++ fa_lst) (ga_ex_lst ++ ga_lst) (ta_ex_lst ++ ta_lst) (ma_ex_lst ++ ma_lst) v_export)) export_lst)) ->
		(v_moduleinst == {| TYPES := ft_lst; FUNCS := (fa_ex_lst ++ fa_lst); GLOBALS := (ga_ex_lst ++ ga_lst); TABLES := (ta_ex_lst ++ ta_lst); MEMS := (ma_ex_lst ++ ma_lst); ELEMS := ea_lst; DATAS := da_lst; EXPORTS := xi_lst |}) ->
		((s_1, fa_lst) == var_4) ->
		((s_2, ga_lst) == var_5) ->
		((s_3, ta_lst) == var_6) ->
		((s_4, ma_lst) == var_7) ->
		((s_5, ea_lst) == var_8) ->
		((s_6, da_lst) == var_9) ->
		fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst (s_6, v_moduleinst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:154.6-154.14 *)
Inductive fun_runelem : elem -> idx -> (seq instr) -> Prop :=
	| fun_runelem_case_0 : forall (v_reftype : reftype) (expr_lst : (seq expr)) (i : uN), fun_runelem (ELEM v_reftype expr_lst PASSIVE) i [:: ]
	| fun_runelem_case_1 : forall (v_reftype : reftype) (expr_lst : (seq expr)) (i : uN), fun_runelem (ELEM v_reftype expr_lst DECLARE) i [::(ELEM_DROP i)]
	| fun_runelem_case_2 : forall (v_reftype : reftype) (expr_lst : (seq expr)) (x : uN) (instr_lst : (seq instr)) (i : uN) (v_n : nat), 
		(v_n == (|expr_lst|)) ->
		fun_runelem (ELEM v_reftype expr_lst (ACTIVE x instr_lst)) i (instr_lst ++ [::(CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))); (CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (TABLE_INIT x i); (ELEM_DROP i)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:161.6-161.14 *)
Inductive fun_rundata : data -> idx -> (seq instr) -> Prop :=
	| fun_rundata_case_0 : forall (byte_lst : (seq byte)) (i : uN), fun_rundata (DATA byte_lst datamode_PASSIVE) i [:: ]
	| fun_rundata_case_1 : forall (byte_lst : (seq byte)) (instr_lst : (seq instr)) (i : uN) (v_n : nat), 
		(v_n == (|byte_lst|)) ->
		fun_rundata (DATA byte_lst (datamode_ACTIVE (mk_uN 0) instr_lst)) i (instr_lst ++ [::(CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))); (CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))); (MEMORY_INIT i); (DATA_DROP i)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 *)
Inductive fun_instantiate : store -> module -> (seq externaddr) -> config -> Prop :=
	| fun_instantiate_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (seq externaddr)) (s' : store) (f : frame) (instr_E_lst : (seq instr)) (instr_D_lst : (seq instr)) (x_opt : (option idx)) (type_lst : (seq type)) (import_lst : (seq import)) (func_lst : (seq func)) (global_lst : (seq global)) (table_lst : (seq table)) (mem_lst : (seq mem)) (elem_lst : (seq elem)) (data_lst : (seq data)) (start_opt : (option start)) (export_lst : (seq export)) (functype_lst : (seq functype)) (expr_G_lst : (seq expr)) (globaltype_lst : (seq globaltype)) (elemmode_lst : (seq elemmode)) (expr_E_lst_lst : (seq (seq expr))) (reftype_lst : (seq reftype)) (n_F : nat) (n_E : nat) (n_D : nat) (moduleinst_init : moduleinst) (f_init : frame) (z : state) (val_lst : (seq val)) (ref_lst_lst : (seq (seq ref))) (v_moduleinst : moduleinst) (i : nat) (j : nat) (var_4 : (seq instr)) (var_3 : (seq instr)) (var_2 : store * moduleinst) (var_1 : (seq globaladdr)) (var_0 : (seq funcaddr)), 
		(j < (|data_lst|)) ->
		(fun_rundata (data_lst[| j |]) (mk_uN j) var_4) ->
		(i < (|elem_lst|)) ->
		(fun_runelem (elem_lst[| i |]) (mk_uN i) var_3) ->
		(fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst var_2) ->
		(fun_globals externaddr_lst var_1) ->
		(fun_funcs externaddr_lst var_0) ->
		(v_module == (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ->
		(type_lst == (seq.map (fun (v_functype : functype) => (TYPE v_functype)) functype_lst)) ->
		(global_lst == (list_zipWith (fun (expr_G : expr) (v_globaltype : globaltype) => (global_GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ->
		(elem_lst == (list_map3 (fun (v_elemmode : elemmode) (expr_E_lst : (seq expr)) (v_reftype : reftype) => (ELEM v_reftype expr_E_lst v_elemmode)) elemmode_lst expr_E_lst_lst reftype_lst)) ->
		(start_opt == (option_map (fun (x : idx) => (START x)) x_opt)) ->
		(n_F == (|func_lst|)) ->
		(n_E == (|elem_lst|)) ->
		(n_D == (|data_lst|)) ->
		(moduleinst_init == {| TYPES := functype_lst; FUNCS := (var_0 ++ (seq.mkseq (fun i_F => ((|(store_FUNCS s)|) + i_F)) n_F)); GLOBALS := var_1; TABLES := [:: ]; MEMS := [:: ]; ELEMS := [:: ]; DATAS := [:: ]; EXPORTS := [:: ] |}) ->
		(f_init == {| LOCALS := [:: ]; frame_MODULE := moduleinst_init |}) ->
		(z == (mk_state s f_init)) ->
		((|expr_G_lst|) == (|val_lst|)) ->
		List.Forall2 (fun (expr_G : expr) (v_val : val) => (Eval_expr z expr_G z [::v_val])) expr_G_lst val_lst ->
		((|expr_E_lst_lst|) == (|ref_lst_lst|)) ->
		List.Forall2 (fun (expr_E_lst : (seq expr)) (ref_lst : (seq ref)) => ((|expr_E_lst|) == (|ref_lst|))) expr_E_lst_lst ref_lst_lst ->
		List.Forall2 (fun (expr_E_lst : (seq expr)) (ref_lst : (seq ref)) => List.Forall2 (fun (expr_E : expr) (v_ref : ref) => (Eval_expr z expr_E z [::(val_ref v_ref)])) expr_E_lst ref_lst) expr_E_lst_lst ref_lst_lst ->
		((s', v_moduleinst) == var_2) ->
		(f == {| LOCALS := [:: ]; frame_MODULE := v_moduleinst |}) ->
		(instr_E_lst == (concat_ instr (seq.mkseq (fun i => var_3) n_E))) ->
		(instr_D_lst == (concat_ instr (seq.mkseq (fun j => var_4) n_D))) ->
		fun_instantiate s v_module externaddr_lst (mk_config (mk_state s' f) ((seq.map (fun (instr_E : instr) => (admininstr_instr instr_E)) instr_E_lst) ++ ((seq.map (fun (instr_D : instr) => (admininstr_instr instr_D)) instr_D_lst) ++ (option_to_list (option_map (fun (x : idx) => (admininstr_CALL x)) x_opt))))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
Inductive fun_invoke : store -> funcaddr -> (seq val) -> config -> Prop :=
	| fun_invoke_case_0 : forall (s : store) (fa : nat) (v_n : nat) (val_lst : (seq val)) (f : frame) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(f == {| LOCALS := [:: ]; frame_MODULE := {| TYPES := [:: ]; FUNCS := [:: ]; GLOBALS := [:: ]; TABLES := [:: ]; MEMS := [:: ]; ELEMS := [:: ]; DATAS := [:: ]; EXPORTS := [:: ] |} |}) ->
		(fa < (|(fun_funcinst (mk_state s f))|)) ->
		((funcinst_TYPE ((fun_funcinst (mk_state s f))[| fa |])) == (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		fun_invoke s fa val_lst (mk_config (mk_state s f) ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(CALL_ADDR fa)])).

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:849.1-849.43 *)
Definition startopt : Type := (seq start).

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:884.1-884.29 *)
Definition code : Type := (seq local) * expr.

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:915.1-915.33 *)
Definition nopt : Type := (seq u32).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:7.1-7.85 *)
Inductive Externaddrs_ok : store -> externaddr -> externtype -> Prop :=
	| Externaddrs_ok__func : forall (v_S : store) (a : addr) (ext : functype) (minst : moduleinst) (v_func : func), 
		(a < (|(store_FUNCS v_S)|)) ->
		(((store_FUNCS v_S)[| a |]) == {| funcinst_TYPE := ext; funcinst_MODULE := minst; CODE := v_func |}) ->
		Externaddrs_ok v_S (externaddr_FUNC a) (FUNC ext)
	| Externaddrs_ok__table : forall (v_S : store) (a : addr) (res_tt : tabletype) (tt' : tabletype) (ref_lst : (seq ref)), 
		(a < (|(store_TABLES v_S)|)) ->
		(((store_TABLES v_S)[| a |]) == {| tableinst_TYPE := tt'; REFS := ref_lst |}) ->
		(Tabletype_sub tt' res_tt) ->
		Externaddrs_ok v_S (externaddr_TABLE a) (TABLE res_tt)
	| Externaddrs_ok__mem : forall (v_S : store) (a : addr) (mt : memtype) (mt' : memtype) (b_lst : (seq byte)), 
		(a < (|(store_MEMS v_S)|)) ->
		(((store_MEMS v_S)[| a |]) == {| meminst_TYPE := mt'; BYTES := b_lst |}) ->
		(Memtype_sub mt' mt) ->
		Externaddrs_ok v_S (externaddr_MEM a) (MEM mt)
	| Externaddrs_ok__global : forall (v_S : store) (a : addr) (v_mut : mut) (v_valtype : valtype) (v_val : val), 
		(a < (|(store_GLOBALS v_S)|)) ->
		(((store_GLOBALS v_S)[| a |]) == {| globalinst_TYPE := (mk_globaltype v_mut v_valtype); VALUE := v_val |}) ->
		Externaddrs_ok v_S (externaddr_GLOBAL a) (GLOBAL (mk_globaltype v_mut v_valtype)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:29.1-29.59 *)
Inductive Ref_ok : store -> ref -> reftype -> Prop :=
	| null : forall (v_S : store) (rt : reftype), Ref_ok v_S (ref_REF_NULL rt) rt
	| Ref_ok__func : forall (v_S : store) (a : addr) (ext : functype), 
		(Externaddrs_ok v_S (externaddr_FUNC a) (FUNC ext)) ->
		Ref_ok v_S (REF_FUNC_ADDR a) FUNCREF
	| extern : forall (v_S : store) (a : addr), Ref_ok v_S (REF_HOST_ADDR a) EXTERNREF.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:43.1-43.59 *)
Inductive Val_ok : store -> val -> valtype -> Prop :=
	| Val_ok__numtype : forall (v_S : store) (nt : numtype) (c_t : num_), 
		(wf_num_ nt c_t) ->
		Val_ok v_S (val_CONST nt c_t) (valtype_numtype nt)
	| Val_ok__vectype : forall (v_S : store) (vt : vectype) (c_t : vec_), Val_ok v_S (val_VCONST vt c_t) (valtype_vectype vt)
	| Val_ok__reftype : forall (v_S : store) (r : ref) (rt : reftype), 
		(Ref_ok v_S r rt) ->
		Val_ok v_S (val_ref r) (valtype_reftype rt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:57.1-57.66 *)
Inductive Result_ok : store -> result -> (seq valtype) -> Prop :=
	| Result_ok__result : forall (v_S : store) (v_lst : (seq val)) (t_lst : (seq valtype)), 
		((|t_lst|) == (|v_lst|)) ->
		List.Forall2 (fun (t : valtype) (v : val) => (Val_ok v_S v t)) t_lst v_lst ->
		Result_ok v_S (_VALS v_lst) t_lst
	| trap : forall (v_S : store) (t_lst : (seq valtype)), Result_ok v_S TRAP t_lst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:69.1-69.56 *)
Inductive Memory_instance_ok : store -> meminst -> memtype -> Prop :=
	| mk_Memory_instance_ok : forall (v_S : store) (mt : memtype) (b_lst : (seq byte)) (v_n : n) (v_m : m), 
		(mt == (PAGE (mk_limits (mk_uN v_n) (Some (mk_uN v_m))))) ->
		((|b_lst|) == ((v_n * 64) * (Ki ))) ->
		(Memtype_ok mt) ->
		Memory_instance_ok v_S {| meminst_TYPE := mt; BYTES := b_lst |} mt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:79.1-79.59 *)
Inductive Table_instance_ok : store -> tableinst -> tabletype -> Prop :=
	| mk_Table_instance_ok : forall (v_S : store) (res_tt : tabletype) (ref_lst : (seq ref)) (v_n : n) (v_m : m) (rt : reftype), 
		(res_tt == (mk_tabletype (mk_limits (mk_uN v_n) (Some (mk_uN v_m))) rt)) ->
		(v_n == (|ref_lst|)) ->
		List.Forall (fun (v_ref : ref) => (Ref_ok v_S v_ref rt)) ref_lst ->
		(Tabletype_ok res_tt) ->
		Table_instance_ok v_S {| tableinst_TYPE := res_tt; REFS := ref_lst |} res_tt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:90.1-90.62 *)
Inductive Global_instance_ok : store -> globalinst -> globaltype -> Prop :=
	| mk_Global_instance_ok : forall (v_S : store) (gt : globaltype) (v : val) (v_mut : mut) (vt : vectype), 
		(gt == (mk_globaltype v_mut (valtype_vectype vt))) ->
		(Globaltype_ok gt) ->
		(Val_ok v_S v (valtype_vectype vt)) ->
		Global_instance_ok v_S {| globalinst_TYPE := gt; VALUE := v |} gt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:100.1-100.54 *)
Inductive Export_instance_ok : store -> exportinst -> Prop :=
	| mk_Export_instance_ok : forall (v_S : store) (v_name : name) (eaddr : externaddr) (ext : externtype), 
		(Externaddrs_ok v_S eaddr ext) ->
		Export_instance_ok v_S {| NAME := v_name; ADDR := eaddr |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:108.1-108.58 *)
Inductive Element_instance_ok : store -> eleminst -> reftype -> Prop :=
	| mk_Element_instance_ok : forall (v_S : store) (rt : reftype) (ref_lst : (seq ref)), 
		List.Forall (fun (v_ref : ref) => (Ref_ok v_S v_ref rt)) ref_lst ->
		Element_instance_ok v_S {| eleminst_TYPE := rt; eleminst_REFS := ref_lst |} rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:116.1-116.50 *)
Inductive Data_instance_ok : store -> datainst -> Prop :=
	| mk_Data_instance_ok : forall (v_S : store) (b_lst : (seq byte)), Data_instance_ok v_S {| datainst_BYTES := b_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:123.1-123.59 *)
Inductive Module_instance_ok : store -> moduleinst -> context -> Prop :=
	| mk_Module_instance_ok : forall (v_S : store) (functype_lst : (seq functype)) (funcaddr_lst : (seq funcaddr)) (globaladdr_lst : (seq globaladdr)) (tableaddr_lst : (seq tableaddr)) (memaddr_lst : (seq memaddr)) (elemaddr_lst : (seq elemaddr)) (dataaddr_lst : (seq dataaddr)) (exportinst_lst : (seq exportinst)) (functype'_lst : (seq functype)) (globaltype_lst : (seq globaltype)) (tabletype_lst : (seq tabletype)) (memtype_lst : (seq memtype)) (reftype_lst : (seq reftype)) (datatype_lst : (seq datatype)), 
		List.Forall (fun (v_functype : functype) => (Functype_ok v_functype)) functype_lst ->
		((|funcaddr_lst|) == (|functype'_lst|)) ->
		List.Forall2 (fun (v_funcaddr : funcaddr) (functype' : functype) => (Externaddrs_ok v_S (externaddr_FUNC v_funcaddr) (FUNC functype'))) funcaddr_lst functype'_lst ->
		((|tableaddr_lst|) == (|tabletype_lst|)) ->
		List.Forall2 (fun (v_tableaddr : tableaddr) (v_tabletype : tabletype) => (Externaddrs_ok v_S (externaddr_TABLE v_tableaddr) (TABLE v_tabletype))) tableaddr_lst tabletype_lst ->
		((|memaddr_lst|) == (|memtype_lst|)) ->
		List.Forall2 (fun (v_memaddr : memaddr) (v_memtype : memtype) => (Externaddrs_ok v_S (externaddr_MEM v_memaddr) (MEM v_memtype))) memaddr_lst memtype_lst ->
		((|globaladdr_lst|) == (|globaltype_lst|)) ->
		List.Forall2 (fun (v_globaladdr : globaladdr) (v_globaltype : globaltype) => (Externaddrs_ok v_S (externaddr_GLOBAL v_globaladdr) (GLOBAL v_globaltype))) globaladdr_lst globaltype_lst ->
		((|elemaddr_lst|) == (|reftype_lst|)) ->
		List.Forall (fun (v_elemaddr : nat) => (v_elemaddr < (|(store_ELEMS v_S)|))) elemaddr_lst ->
		List.Forall2 (fun (v_elemaddr : nat) (v_reftype : reftype) => (Element_instance_ok v_S ((store_ELEMS v_S)[| v_elemaddr |]) v_reftype)) elemaddr_lst reftype_lst ->
		List.Forall (fun (v_dataaddr : nat) => (v_dataaddr < (|(store_DATAS v_S)|))) dataaddr_lst ->
		List.Forall (fun (v_dataaddr : nat) => (Data_instance_ok v_S ((store_DATAS v_S)[| v_dataaddr |]))) dataaddr_lst ->
		List.Forall (fun (v_exportinst : exportinst) => (Export_instance_ok v_S v_exportinst)) exportinst_lst ->
		((|datatype_lst|) == (|dataaddr_lst|)) ->
		Module_instance_ok v_S {| TYPES := functype_lst; FUNCS := funcaddr_lst; GLOBALS := globaladdr_lst; TABLES := tableaddr_lst; MEMS := memaddr_lst; ELEMS := elemaddr_lst; DATAS := dataaddr_lst; EXPORTS := exportinst_lst |} {| context_TYPES := functype_lst; context_FUNCS := functype'_lst; context_GLOBALS := globaltype_lst; context_TABLES := tabletype_lst; context_MEMS := memtype_lst; context_ELEMS := reftype_lst; context_DATAS := datatype_lst; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:141.1-141.60 *)
Inductive Function_instance_ok : store -> funcinst -> functype -> Prop :=
	| mk_Function_instance_ok : forall (v_S : store) (v_functype : functype) (v_moduleinst : moduleinst) (v_func : func) (C : context), 
		(Functype_ok v_functype) ->
		(Module_instance_ok v_S v_moduleinst C) ->
		(Func_ok C v_func v_functype) ->
		Function_instance_ok v_S {| funcinst_TYPE := v_functype; funcinst_MODULE := v_moduleinst; CODE := v_func |} v_functype.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:151.1-151.33 *)
Inductive Store_ok : store -> Prop :=
	| mk_Store_ok : forall (v_S : store) (funcinst_lst : (seq funcinst)) (globalinst_lst : (seq globalinst)) (tableinst_lst : (seq tableinst)) (meminst_lst : (seq meminst)) (eleminst_lst : (seq eleminst)) (datainst_lst : (seq datainst)) (functype_lst : (seq functype)) (globaltype_lst : (seq globaltype)) (tabletype_lst : (seq tabletype)) (memtype_lst : (seq memtype)) (reftype_lst : (seq reftype)), 
		(v_S == {| store_FUNCS := funcinst_lst; store_GLOBALS := globalinst_lst; store_TABLES := tableinst_lst; store_MEMS := meminst_lst; store_ELEMS := eleminst_lst; store_DATAS := datainst_lst |}) ->
		((|funcinst_lst|) == (|functype_lst|)) ->
		List.Forall2 (fun (v_funcinst : funcinst) (v_functype : functype) => (Function_instance_ok v_S v_funcinst v_functype)) funcinst_lst functype_lst ->
		((|globalinst_lst|) == (|globaltype_lst|)) ->
		List.Forall2 (fun (v_globalinst : globalinst) (v_globaltype : globaltype) => (Global_instance_ok v_S v_globalinst v_globaltype)) globalinst_lst globaltype_lst ->
		((|tableinst_lst|) == (|tabletype_lst|)) ->
		List.Forall2 (fun (v_tableinst : tableinst) (v_tabletype : tabletype) => (Table_instance_ok v_S v_tableinst v_tabletype)) tableinst_lst tabletype_lst ->
		((|meminst_lst|) == (|memtype_lst|)) ->
		List.Forall2 (fun (v_meminst : meminst) (v_memtype : memtype) => (Memory_instance_ok v_S v_meminst v_memtype)) meminst_lst memtype_lst ->
		((|eleminst_lst|) == (|reftype_lst|)) ->
		List.Forall2 (fun (v_eleminst : eleminst) (v_reftype : reftype) => (Element_instance_ok v_S v_eleminst v_reftype)) eleminst_lst reftype_lst ->
		List.Forall (fun (v_datainst : datainst) => (Data_instance_ok v_S v_datainst)) datainst_lst ->
		Store_ok v_S.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:242.1-242.44 *)
Inductive Frame_ok : store -> frame -> context -> Prop :=
	| mk_Frame_ok : forall (v_S : store) (val_lst : (seq val)) (v_moduleinst : moduleinst) (t_lst : (seq valtype)) (C : context), 
		(Module_instance_ok v_S v_moduleinst C) ->
		((|t_lst|) == (|val_lst|)) ->
		List.Forall2 (fun (t : valtype) (v_val : val) => (Val_ok v_S v_val t)) t_lst val_lst ->
		Frame_ok v_S {| LOCALS := val_lst; frame_MODULE := v_moduleinst |} ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := t_lst; LABELS := [:: ]; context_RETURN := None |} @@ C).

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:166.1-168.75 *)
Inductive Admin_instr_ok : store -> context -> admininstr -> functype -> Prop :=
	| Admin_instr_ok__instr : forall (v_S : store) (C : context) (v_instr : instr) (v_functype : functype), 
		(Instr_ok C v_instr v_functype) ->
		Admin_instr_ok v_S C (admininstr_instr v_instr) v_functype
	| Admin_instr_ok__trap : forall (v_S : store) (C : context) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), Admin_instr_ok v_S C admininstr_TRAP (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| ref_extern : forall (v_S : store) (C : context) (v_hostaddr : hostaddr), Admin_instr_ok v_S C (admininstr_REF_HOST_ADDR v_hostaddr) (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_EXTERNREF]))
	| Admin_instr_ok__ref : forall (v_S : store) (C : context) (v_funcaddr : funcaddr) (v_functype : functype), 
		(Externaddrs_ok v_S (externaddr_FUNC v_funcaddr) (FUNC v_functype)) ->
		Admin_instr_ok v_S C (admininstr_REF_FUNC_ADDR v_funcaddr) (mk_functype (mk_list _ [:: ]) (mk_list _ [::valtype_FUNCREF]))
	| Admin_instr_ok__call_addr : forall (v_S : store) (C : context) (v_funcaddr : funcaddr) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Externaddrs_ok v_S (externaddr_FUNC v_funcaddr) (FUNC (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst)))) ->
		Admin_instr_ok v_S C (CALL_ADDR v_funcaddr) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))
	| label : forall (v_S : store) (C : context) (v_n : n) (instr_lst : (seq instr)) (admininstr_lst : (seq admininstr)) (t_2_lst : (seq valtype)) (t_1_lst : (seq valtype)), 
		(Instrs_ok C instr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Admin_instrs_ok v_S ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [::(mk_list _ t_1_lst)]; context_RETURN := None |} @@ C) admininstr_lst (mk_functype (mk_list _ [:: ]) (mk_list _ t_2_lst))) ->
		(v_n == (|t_1_lst|)) ->
		Admin_instr_ok v_S C (LABEL_ v_n instr_lst admininstr_lst) (mk_functype (mk_list _ [:: ]) (mk_list _ t_2_lst))
	| Admin_instr_ok__frame : forall (v_S : store) (C : context) (v_n : n) (F : frame) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)), 
		(Thread_ok v_S (Some (mk_list _ t_lst)) F admininstr_lst (mk_list _ t_lst)) ->
		(v_n == (|t_lst|)) ->
		Admin_instr_ok v_S C (FRAME_ v_n F admininstr_lst) (mk_functype (mk_list _ [:: ]) (mk_list _ t_lst))
	| weakening : forall (v_S : store) (C : context) (v_admininstr : admininstr) (t'_lst : (seq valtype)) (t'_1_lst : (seq valtype)) (t_lst : (seq valtype)) (t'_2_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Admin_instr_ok v_S C v_admininstr (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Resulttype_sub (mk_list _ t'_lst) (mk_list _ t_lst)) ->
		(Resulttype_sub (mk_list _ t'_1_lst) (mk_list _ t_1_lst)) ->
		(Resulttype_sub (mk_list _ t_2_lst) (mk_list _ t'_2_lst)) ->
		Admin_instr_ok v_S C v_admininstr (mk_functype (mk_list _ (t'_lst ++ t'_1_lst)) (mk_list _ (t_lst ++ t'_2_lst)))

with

Admin_instrs_ok : store -> context -> (seq admininstr) -> functype -> Prop :=
	| Admin_instrs_ok__empty : forall (v_S : store) (C : context), Admin_instrs_ok v_S C [:: ] (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
	| Admin_instrs_ok__seq : forall (v_S : store) (C : context) (admininstr_1 : admininstr) (admininstr_2_lst : (seq admininstr)) (t_1_lst : (seq valtype)) (t_3_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Admin_instr_ok v_S C admininstr_1 (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Admin_instrs_ok v_S C admininstr_2_lst (mk_functype (mk_list _ t_2_lst) (mk_list _ t_3_lst))) ->
		Admin_instrs_ok v_S C ([::admininstr_1] ++ admininstr_2_lst) (mk_functype (mk_list _ t_1_lst) (mk_list _ t_3_lst))
	| Admin_instrs_ok__sub : forall (v_S : store) (C : context) (admininstr_lst : (seq admininstr)) (t'_1_lst : (seq valtype)) (t'_2_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Admin_instrs_ok v_S C admininstr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		(Resulttype_sub (mk_list _ t'_1_lst) (mk_list _ t_1_lst)) ->
		(Resulttype_sub (mk_list _ t_2_lst) (mk_list _ t'_2_lst)) ->
		Admin_instrs_ok v_S C admininstr_lst (mk_functype (mk_list _ t'_1_lst) (mk_list _ t'_2_lst))
	| Admin_instrs_ok__frame : forall (v_S : store) (C : context) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Admin_instrs_ok v_S C admininstr_lst (mk_functype (mk_list _ t_1_lst) (mk_list _ t_2_lst))) ->
		Admin_instrs_ok v_S C admininstr_lst (mk_functype (mk_list _ (t_lst ++ t_1_lst)) (mk_list _ (t_lst ++ t_2_lst)))
	| instrs : forall (v_S : store) (C : context) (instr_lst : (seq instr)) (v_functype : functype), 
		(Instrs_ok C instr_lst v_functype) ->
		Admin_instrs_ok v_S C (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst) v_functype

with

Thread_ok : store -> (option resulttype) -> frame -> (seq admininstr) -> resulttype -> Prop :=
	| mk_Thread_ok : forall (v_S : store) (resulttype_opt : (option resulttype)) (F : frame) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)) (C : context), 
		(Frame_ok v_S F C) ->
		(Admin_instrs_ok v_S ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_ELEMS := [:: ]; context_DATAS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := resulttype_opt |} @@ C) admininstr_lst (mk_functype (mk_list _ [:: ]) (mk_list _ t_lst))) ->
		Thread_ok v_S resulttype_opt F admininstr_lst (mk_list _ t_lst).

(* Auxiliary Definition at: ../specification/wasm-2.0/B-soundness.spectec:197.1-197.32 *)
Definition optionSize (var_0 : (option valtype)) : nat :=
	match var_0 return nat with
		| (Some v_valtype) => 1
		| None => 0
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:254.1-254.43 *)
Inductive Config_ok : config -> resulttype -> Prop :=
	| mk_Config_ok : forall (v_S : store) (F : frame) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)), 
		(Store_ok v_S) ->
		(Thread_ok v_S None F admininstr_lst (mk_list _ t_lst)) ->
		Config_ok (mk_config (mk_state v_S F) admininstr_lst) (mk_list _ t_lst).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:265.1-265.48 *)
Inductive Func_extension : funcinst -> funcinst -> Prop :=
	| mk_Func_extension : forall (v_funcinst : funcinst), Func_extension v_funcinst v_funcinst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:266.1-266.51 *)
Inductive Table_extension : tableinst -> tableinst -> Prop :=
	| mk_Table_extension : forall (n1 : u32) (v_m : m) (rt : reftype) (ref_1_lst : (seq ref)) (n2 : u32) (ref_2_lst : (seq ref)), 
		((n1 :> nat) <= (n2 :> nat)) ->
		Table_extension {| tableinst_TYPE := (mk_tabletype (mk_limits n1 (Some (mk_uN v_m))) rt); REFS := ref_1_lst |} {| tableinst_TYPE := (mk_tabletype (mk_limits n2 (Some (mk_uN v_m))) rt); REFS := ref_2_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:267.1-267.45 *)
Inductive Mem_extension : meminst -> meminst -> Prop :=
	| mk_Mem_extension : forall (n1 : u32) (v_m : m) (b_1_lst : (seq byte)) (n2 : u32) (b_2_lst : (seq byte)), 
		((n1 :> nat) <= (n2 :> nat)) ->
		Mem_extension {| meminst_TYPE := (PAGE (mk_limits n1 (Some (mk_uN v_m)))); BYTES := b_1_lst |} {| meminst_TYPE := (PAGE (mk_limits n2 (Some (mk_uN v_m)))); BYTES := b_2_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:268.1-268.54 *)
Inductive Global_extension : globalinst -> globalinst -> Prop :=
	| mk_Global_extension : forall (v_mut : mut) (t : valtype) (val_1 : val) (val_2 : val), 
		((v_mut == (Some MUT_MUT)) || (val_1 == val_2)) ->
		Global_extension {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := val_1 |} {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := val_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:269.1-269.48 *)
Inductive Elem_extension : eleminst -> eleminst -> Prop :=
	| mk_Elem_extension : forall (v_elemtype : elemtype) (ref_1_lst : (seq ref)) (ref_2_lst : (seq ref)), 
		((ref_1_lst == ref_2_lst) || (ref_2_lst == [:: ])) ->
		Elem_extension {| eleminst_TYPE := v_elemtype; eleminst_REFS := ref_1_lst |} {| eleminst_TYPE := v_elemtype; eleminst_REFS := ref_2_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:270.1-270.48 *)
Inductive Data_extension : datainst -> datainst -> Prop :=
	| mk_Data_extension : forall (byte_1_lst : (seq byte)) (byte_2_lst : (seq byte)), 
		((byte_1_lst == byte_2_lst) || (byte_2_lst == [:: ])) ->
		Data_extension {| datainst_BYTES := byte_1_lst |} {| datainst_BYTES := byte_2_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:271.1-271.43 *)
Inductive Store_extension : store -> store -> Prop :=
	| mk_Store_extension : forall (store_1 : store) (store_2 : store) (funcinst_1_lst : (seq funcinst)) (tableinst_1_lst : (seq tableinst)) (meminst_1_lst : (seq meminst)) (globalinst_1_lst : (seq globalinst)) (eleminst_1_lst : (seq eleminst)) (datainst_1_lst : (seq datainst)) (funcinst_1'_lst : (seq funcinst)) (funcinst_2_lst : (seq funcinst)) (tableinst_1'_lst : (seq tableinst)) (tableinst_2_lst : (seq tableinst)) (meminst_1'_lst : (seq meminst)) (meminst_2_lst : (seq meminst)) (globalinst_1'_lst : (seq globalinst)) (globalinst_2_lst : (seq globalinst)) (eleminst_1'_lst : (seq eleminst)) (eleminst_2_lst : (seq eleminst)) (datainst_1'_lst : (seq datainst)) (datainst_2_lst : (seq datainst)), 
		((store_FUNCS store_1) == funcinst_1_lst) ->
		((store_TABLES store_1) == tableinst_1_lst) ->
		((store_MEMS store_1) == meminst_1_lst) ->
		((store_GLOBALS store_1) == globalinst_1_lst) ->
		((store_ELEMS store_1) == eleminst_1_lst) ->
		((store_DATAS store_1) == datainst_1_lst) ->
		([::(store_FUNCS store_2)] == [::funcinst_1'_lst; funcinst_2_lst]) ->
		([::(store_TABLES store_2)] == [::tableinst_1'_lst; tableinst_2_lst]) ->
		([::(store_MEMS store_2)] == [::meminst_1'_lst; meminst_2_lst]) ->
		([::(store_GLOBALS store_2)] == [::globalinst_1'_lst; globalinst_2_lst]) ->
		([::(store_ELEMS store_2)] == [::eleminst_1'_lst; eleminst_2_lst]) ->
		([::(store_DATAS store_2)] == [::datainst_1'_lst; datainst_2_lst]) ->
		((|funcinst_1_lst|) == (|funcinst_1'_lst|)) ->
		List.Forall2 (fun (funcinst_1 : funcinst) (funcinst_1' : funcinst) => (Func_extension funcinst_1 funcinst_1')) funcinst_1_lst funcinst_1'_lst ->
		((|tableinst_1_lst|) == (|tableinst_1'_lst|)) ->
		List.Forall2 (fun (tableinst_1 : tableinst) (tableinst_1' : tableinst) => (Table_extension tableinst_1 tableinst_1')) tableinst_1_lst tableinst_1'_lst ->
		((|meminst_1_lst|) == (|meminst_1'_lst|)) ->
		List.Forall2 (fun (meminst_1 : meminst) (meminst_1' : meminst) => (Mem_extension meminst_1 meminst_1')) meminst_1_lst meminst_1'_lst ->
		((|globalinst_1_lst|) == (|globalinst_1'_lst|)) ->
		List.Forall2 (fun (globalinst_1 : globalinst) (globalinst_1' : globalinst) => (Global_extension globalinst_1 globalinst_1')) globalinst_1_lst globalinst_1'_lst ->
		((|eleminst_1_lst|) == (|eleminst_1'_lst|)) ->
		List.Forall2 (fun (eleminst_1 : eleminst) (eleminst_1' : eleminst) => (Elem_extension eleminst_1 eleminst_1')) eleminst_1_lst eleminst_1'_lst ->
		((|datainst_1_lst|) == (|datainst_1'_lst|)) ->
		List.Forall2 (fun (datainst_1 : datainst) (datainst_1' : datainst) => (Data_extension datainst_1 datainst_1')) datainst_1_lst datainst_1'_lst ->
		Store_extension store_1 store_2.

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:317.1-317.32 *)
Inductive fun_types__of : (seq val) -> (seq valtype) -> Prop :=
	| fun_types__of_case_0 : fun_types__of [:: ] [:: ]
	| fun_types__of_case_1 : forall (v_numtype : numtype) (val_ : num_) (val'_lst : (seq val)) (var_0 : (seq valtype)), 
		(fun_types__of val'_lst var_0) ->
		fun_types__of ([::(val_CONST v_numtype val_)] ++ val'_lst) ([::(valtype_numtype v_numtype)] ++ var_0)
	| fun_types__of_case_2 : forall (v_vectype : vectype) (val_ : uN) (val'_lst : (seq val)) (var_0 : (seq valtype)), 
		(fun_types__of val'_lst var_0) ->
		fun_types__of ([::(val_VCONST v_vectype val_)] ++ val'_lst) ([::(valtype_vectype v_vectype)] ++ var_0)
	| fun_types__of_case_3 : forall (rt : reftype) (val'_lst : (seq val)) (var_0 : (seq valtype)), 
		(fun_types__of val'_lst var_0) ->
		fun_types__of ([::(val_REF_NULL rt)] ++ val'_lst) ([::(valtype_reftype rt)] ++ var_0)
	| fun_types__of_case_4 : forall (a : nat) (val'_lst : (seq val)) (var_0 : (seq valtype)), 
		(fun_types__of val'_lst var_0) ->
		fun_types__of ([::(val_REF_FUNC_ADDR a)] ++ val'_lst) ([::valtype_FUNCREF] ++ var_0)
	| fun_types__of_case_5 : forall (a : nat) (val'_lst : (seq val)) (var_0 : (seq valtype)), 
		(fun_types__of val'_lst var_0) ->
		fun_types__of ([::(val_REF_HOST_ADDR a)] ++ val'_lst) ([::valtype_EXTERNREF] ++ var_0).

(* Auxiliary Definition at: ../specification/wasm-2.0/B-soundness.spectec:325.1-326.32 *)
Definition is__const (v_admininstr : admininstr) : bool :=
	match v_admininstr return bool with
		| (admininstr_CONST v_numtype val_) => true
		| (admininstr_VCONST v_vectype val_) => true
		| v_admininstr => false
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:331.1-332.41 *)
Inductive fun_const__list : (seq admininstr) -> bool -> Prop :=
	| fun_const__list_case_0 : fun_const__list [:: ] true
	| fun_const__list_case_1 : forall (v_admininstr : admininstr) (admininstr'_lst : (seq admininstr)) (var_0 : bool), 
		(fun_const__list admininstr'_lst var_0) ->
		fun_const__list ([::v_admininstr] ++ admininstr'_lst) ((is__const v_admininstr) && var_0).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:337.6-337.21 *)
Inductive fun_terminal__form : (seq admininstr) -> bool -> Prop :=
	| fun_terminal__form_case_0 : forall (admininstr_lst : (seq admininstr)) (var_0 : bool), 
		(fun_const__list admininstr_lst var_0) ->
		fun_terminal__form admininstr_lst (var_0 || (admininstr_lst == [::admininstr_TRAP])).

(* Mutual Recursion at: ../specification/wasm-2.0/A-binary.spectec:20.1-22.82 *)
(* Mutual Recursion at: ../specification/wasm-2.0/A-binary.spectec:24.1-27.82 *)
(* Mutual Recursion at: ../specification/wasm-2.0/A-binary.spectec:742.1-752.59 *)
