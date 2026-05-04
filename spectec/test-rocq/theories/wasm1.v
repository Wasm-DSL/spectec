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
(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.14-119.17 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:7.1-7.27 *)
Definition res_N : Type := nat.

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:8.1-8.27 *)
Definition M : Type := nat.

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:9.1-9.27 *)
Definition n : Type := nat.

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:10.1-10.27 *)
Definition m : Type := nat.

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:15.1-15.14 *)
Definition Ki : nat := 1024.

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:21.1-21.25 *)
Definition min (res_nat : nat) (nat_0 : nat) : nat :=
	match res_nat, nat_0 return nat with
		| i, j => (if (i <= j) then i else j)
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/0-aux.spectec:25.1-25.21 *)
Inductive fun_sum : (seq nat) -> nat -> Prop :=
	| fun_sum_case_0 : fun_sum [:: ] 0
	| fun_sum_case_1 : forall (v_n : nat) (n'_lst : (seq n)) (var_0 : nat), 
		(fun_sum n'_lst var_0) ->
		fun_sum ([::v_n] ++ n'_lst) (v_n + var_0).

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:32.1-32.58 *)
Definition opt_ (X : eqType) (var_0 : (seq X)) : (option (option X)) :=
	match X, var_0 return (option (option X)) with
		| X, [:: ] => (Some None)
		| X, [::w] => (Some (Some w))
		| X, x1 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:36.1-36.45 *)
Definition list_ (X : eqType) (var_0 : (option X)) : (seq X) :=
	match X, var_0 return (seq X) with
		| X, None => [:: ]
		| X, (Some w) => [::w]
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/0-aux.spectec:40.1-40.59 *)
Fixpoint concat_ (X : eqType) (var_0 : (seq (seq X))) : (seq X) :=
	match X, var_0 return (seq X) with
		| X, [:: ] => [:: ]
		| X, (w_lst :: w'_lst_lst) => (w_lst ++ (concat_ X w'_lst_lst))
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:6.1-6.49 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50 *)
Definition proj_byte_0 (x : byte) : (nat) :=
	match x return (nat) with
		| (mk_byte v_num_0) => (v_num_0)
	end.

Global Instance proj_byte_0_coercion : Coercion byte (nat) := { coerce := proj_byte_0 }.

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.8-15.12 *)
Inductive wf_byte : byte -> Prop :=
	| byte_case_0 : forall (i : nat), 
		((i >= 0) && (i <= 255)) ->
		wf_byte (mk_byte i).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25 *)
Definition proj_uN_0 (x : uN) : (nat) :=
	match x return (nat) with
		| (mk_uN v_num_0) => (v_num_0)
	end.

Global Instance proj_uN_0_coercion : Coercion uN (nat) := { coerce := proj_uN_0 }.

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.8-17.11 *)
Inductive wf_uN : res_N -> uN -> Prop :=
	| uN_case_0 : forall (v_N : res_N) (i : nat), 
		((i >= 0) && (i <= ((((2 ^ v_N) : nat) - (1 : nat)) : nat))) ->
		wf_uN v_N (mk_uN i).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49 *)
Definition proj_sN_0 (x : sN) : (nat) :=
	match x return (nat) with
		| (mk_sN v_num_0) => (v_num_0)
	end.

Global Instance proj_sN_0_coercion : Coercion sN (nat) := { coerce := proj_sN_0 }.

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.8-19.11 *)
Inductive wf_sN : res_N -> sN -> Prop :=
	| sN_case_0 : forall (v_N : res_N) (i : nat), 
		((((i >= (0 - ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat))) && (i <= (0 - (1 : nat)))) || (i == (0 : nat))) || ((i >= ((1 : nat))) && (i <= (((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat) - (1 : nat))))) ->
		wf_sN v_N (mk_sN i).

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:21.1-22.8 *)
Definition iN : Type := uN.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:24.1-24.20 *)
Definition u31 : Type := uN.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:25.1-25.20 *)
Definition u32 : Type := uN.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:26.1-26.20 *)
Definition u64 : Type := uN.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:28.1-28.20 *)
Definition i32 : Type := iN.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:29.1-29.20 *)
Definition i64 : Type := iN.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:36.1-36.35 *)
Definition signif (v_N : res_N) : (option nat) :=
	match v_N return (option nat) with
		| 32 => (Some 23)
		| 64 => (Some 52)
		| x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:40.1-40.34 *)
Definition expon (v_N : res_N) : (option nat) :=
	match v_N return (option nat) with
		| 32 => (Some 8)
		| 64 => (Some 11)
		| x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:44.1-44.30 *)
Definition fun_M (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (!((signif v_N)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:47.1-47.30 *)
Definition E (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (!((expon v_N)))
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:54.1-54.30 *)
Definition exp : Type := nat.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:55.1-59.84 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:55.8-55.14 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:50.1-52.35 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:50.8-50.11 *)
Inductive wf_fN : res_N -> fN -> Prop :=
	| fN_case_0 : forall (v_N : res_N) (var_0 : fNmag), 
		(wf_fNmag v_N var_0) ->
		wf_fN v_N (POS var_0)
	| fN_case_1 : forall (v_N : res_N) (var_0 : fNmag), 
		(wf_fNmag v_N var_0) ->
		wf_fN v_N (NEG var_0).

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:61.1-61.20 *)
Definition f32 : Type := fN.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:62.1-62.20 *)
Definition f64 : Type := fN.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:64.1-64.39 *)
Definition fzero (v_N : res_N) : fN :=
	match v_N return fN with
		| v_N => (POS (SUBNORM 0))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:67.1-67.39 *)
Definition fone (v_N : res_N) : fN :=
	match v_N return fN with
		| v_N => (POS (NORM 1 (0 : nat)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:70.1-70.21 *)
Definition canon_ (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (2 ^ ((((!((signif v_N))) : nat) - (1 : nat)) : nat))
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85 *)
Definition proj_char_0 (x : char) : (nat) :=
	match x return (nat) with
		| (mk_char v_num_0) => (v_num_0)
	end.

Global Instance proj_char_0_coercion : Coercion char (nat) := { coerce := proj_char_0 }.

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.8-78.12 *)
Inductive wf_char : char -> Prop :=
	| char_case_0 : forall (i : nat), 
		(((i >= 0) && (i <= 55295)) || ((i >= 57344) && (i <= 1114111))) ->
		wf_char (mk_char i).

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:80.1-80.25 *)
Inductive fun_utf8 : (seq char) -> (seq byte) -> Prop :=
	| fun_utf8_case_0 : forall (ch : char) (b : byte), 
		(((ch :> nat) < 128) && ((mk_byte (ch :> (nat))) == b)) ->
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70 *)
Definition proj_name_0 (x : name) : ((seq char)) :=
	match x return ((seq char)) with
		| (mk_name v_char_list_0) => (v_char_list_0)
	end.

Global Instance proj_name_0_coercion : Coercion name ((seq char)) := { coerce := proj_name_0 }.

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.8-82.12 *)
Inductive wf_name : name -> Prop :=
	| name_case_0 : forall (char_lst : (seq char)) (var_0 : (seq byte)), 
		(fun_utf8 char_lst var_0) ->
		List.Forall (fun (v_char : char) => (wf_char v_char)) char_lst ->
		((|var_0|) < (2 ^ 32)) ->
		wf_name (mk_name char_lst).

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:91.1-91.36 *)
Definition idx : Type := u32.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:93.1-93.45 *)
Definition typeidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:94.1-94.49 *)
Definition funcidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:95.1-95.49 *)
Definition globalidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:96.1-96.47 *)
Definition tableidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:97.1-97.46 *)
Definition memidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:98.1-98.47 *)
Definition labelidx : Type := idx.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:99.1-99.47 *)
Definition localidx : Type := idx.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:108.1-109.26 *)
Inductive valtype : Type :=
	| I32 : valtype
	| I64 : valtype
	| F32 : valtype
	| F64 : valtype.

Global Instance Inhabited__valtype : Inhabited (valtype) := { default_val := I32 }.

Definition valtype_eq_dec : forall (v1 v2 : valtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition valtype_eqb (v1 v2 : valtype) : bool :=
	is_left(valtype_eq_dec v1 v2).
Definition eqvaltypeP : Equality.axiom (valtype_eqb) :=
	eq_dec_Equality_axiom (valtype) (valtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (valtype) (eqvaltypeP).
Hint Resolve valtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:111.1-111.38 *)
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
Definition valtype_Inn (var_0 : Inn) : valtype :=
	match var_0 return valtype with
		| Inn_I32 => I32
		| Inn_I64 => I64
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:112.1-112.38 *)
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
Definition valtype_Fnn (var_0 : Fnn) : valtype :=
	match var_0 return valtype with
		| Fnn_F32 => F32
		| Fnn_F64 => F64
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:116.1-117.11 *)
Definition resulttype : Type := (option valtype).

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.1-119.18 *)
Definition mut : Type := (option MUT).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:121.1-122.17 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:121.8-121.14 *)
Inductive wf_limits : limits -> Prop :=
	| limits_case_0 : forall (v_u32 : u32) (u32_opt : (option u32)), 
		(wf_uN 32 v_u32) ->
		wf_limits (mk_limits v_u32 u32_opt).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:123.1-124.14 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:125.1-126.23 *)
Inductive functype : Type :=
	| mk_functype (valtype_lst : (seq valtype)) (valtype_lst : (seq valtype)) : functype.

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

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:127.1-128.9 *)
Definition tabletype : Type := limits.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:129.1-130.9 *)
Definition memtype : Type := limits.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:131.1-132.70 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:131.8-131.18 *)
Inductive wf_externtype : externtype -> Prop :=
	| externtype_case_0 : forall (v_functype : functype), wf_externtype (FUNC v_functype)
	| externtype_case_1 : forall (v_globaltype : globaltype), wf_externtype (GLOBAL v_globaltype)
	| externtype_case_2 : forall (v_tabletype : tabletype), 
		(wf_limits v_tabletype) ->
		wf_externtype (TABLE v_tabletype)
	| externtype_case_3 : forall (v_memtype : memtype), 
		(wf_limits v_memtype) ->
		wf_externtype (MEM v_memtype).

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:144.1-144.41 *)
Definition res_size (v_valtype : valtype) : nat :=
	match v_valtype return nat with
		| I32 => 32
		| I64 => 64
		| F32 => 32
		| F64 => 64
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 *)
Inductive val_ : Type :=
	| mk_val__0 (v_Inn : Inn) (var_x : iN) : val_
	| mk_val__1 (v_Fnn : Fnn) (var_x : fN) : val_.

Global Instance Inhabited__val_ : Inhabited (val_) := { default_val := mk_val__0 default_val default_val }.

Definition val__eq_dec : forall (v1 v2 : val_),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition val__eqb (v1 v2 : val_) : bool :=
	is_left(val__eq_dec v1 v2).
Definition eqval_P : Equality.axiom (val__eqb) :=
	eq_dec_Equality_axiom (val_) (val__eq_dec).

HB.instance Definition _ := hasDecEq.Build (val_) (eqval_P).
Hint Resolve val__eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13 *)
Inductive wf_val_ : valtype -> val_ -> Prop :=
	| val__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : iN), 
		(wf_uN (res_size (valtype_Inn v_Inn)) var_x) ->
		(v_valtype == (valtype_Inn v_Inn)) ->
		wf_val_ v_valtype (mk_val__0 v_Inn var_x)
	| val__case_1 : forall (v_valtype : valtype) (v_Fnn : Fnn) (var_x : fN), 
		(wf_fN (res_size (valtype_Fnn v_Fnn)) var_x) ->
		(v_valtype == (valtype_Fnn v_Fnn)) ->
		wf_val_ v_valtype (mk_val__1 v_Fnn var_x).

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 *)
Definition proj_val__0 (var_x : val_) : (option iN) :=
	match var_x return (option iN) with
		| (mk_val__0 v_Inn var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 *)
Definition proj_val__1 (var_x : val_) : (option fN) :=
	match var_x return (option fN) with
		| (mk_val__1 v_Fnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:153.1-153.42 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56 *)
Definition proj_sz_0 (x : sz) : (nat) :=
	match x return (nat) with
		| (mk_sz v_num_0) => (v_num_0)
	end.

Global Instance proj_sz_0_coercion : Coercion sz (nat) := { coerce := proj_sz_0 }.

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.8-154.10 *)
Inductive wf_sz : sz -> Prop :=
	| sz_case_0 : forall (i : nat), 
		((((i == 8) || (i == 16)) || (i == 32)) || (i == 64)) ->
		wf_sz (mk_sz i).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
Inductive unop_Inn : Type :=
	| CLZ : unop_Inn
	| CTZ : unop_Inn
	| POPCNT : unop_Inn.

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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14 *)
Inductive wf_unop_ : valtype -> unop_ -> Prop :=
	| unop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : unop_Inn), 
		(v_valtype == (valtype_Inn v_Inn)) ->
		wf_unop_ v_valtype (mk_unop__0 v_Inn var_x)
	| unop__case_1 : forall (v_valtype : valtype) (v_Fnn : Fnn) (var_x : unop_Fnn), 
		(v_valtype == (valtype_Fnn v_Fnn)) ->
		wf_unop_ v_valtype (mk_unop__1 v_Fnn var_x).

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
Definition proj_unop__0 (var_x : unop_) : (option unop_Inn) :=
	match var_x return (option unop_Inn) with
		| (mk_unop__0 v_Inn var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
Definition proj_unop__1 (var_x : unop_) : (option unop_Fnn) :=
	match var_x return (option unop_Fnn) with
		| (mk_unop__1 v_Fnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15 *)
Inductive wf_binop_ : valtype -> binop_ -> Prop :=
	| binop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : binop_Inn), 
		(v_valtype == (valtype_Inn v_Inn)) ->
		wf_binop_ v_valtype (mk_binop__0 v_Inn var_x)
	| binop__case_1 : forall (v_valtype : valtype) (v_Fnn : Fnn) (var_x : binop_Fnn), 
		(v_valtype == (valtype_Fnn v_Fnn)) ->
		wf_binop_ v_valtype (mk_binop__1 v_Fnn var_x).

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
Definition proj_binop__0 (var_x : binop_) : (option binop_Inn) :=
	match var_x return (option binop_Inn) with
		| (mk_binop__0 v_Inn var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
Definition proj_binop__1 (var_x : binop_) : (option binop_Fnn) :=
	match var_x return (option binop_Fnn) with
		| (mk_binop__1 v_Fnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.8-167.16 *)
Inductive wf_testop_ : valtype -> testop_ -> Prop :=
	| testop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : testop_Inn), 
		(v_valtype == (valtype_Inn v_Inn)) ->
		wf_testop_ v_valtype (mk_testop__0 v_Inn var_x).

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 *)
Definition proj_testop__0 (var_x : testop_) : testop_Inn :=
	match var_x return testop_Inn with
		| (mk_testop__0 v_Inn var_x) => var_x
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15 *)
Inductive wf_relop_ : valtype -> relop_ -> Prop :=
	| relop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : relop_Inn), 
		(v_valtype == (valtype_Inn v_Inn)) ->
		wf_relop_ v_valtype (mk_relop__0 v_Inn var_x)
	| relop__case_1 : forall (v_valtype : valtype) (v_Fnn : Fnn) (var_x : relop_Fnn), 
		(v_valtype == (valtype_Fnn v_Fnn)) ->
		wf_relop_ v_valtype (mk_relop__1 v_Fnn var_x).

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
Definition proj_relop__0 (var_x : relop_) : (option relop_Inn) :=
	match var_x return (option relop_Inn) with
		| (mk_relop__0 v_Inn var_x) => (Some var_x)
		| var_x => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
Definition proj_relop__1 (var_x : relop_) : (option relop_Fnn) :=
	match var_x return (option relop_Fnn) with
		| (mk_relop__1 v_Fnn var_x) => (Some var_x)
		| var_x => None
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:179.1-180.78 *)
Inductive cvtop : Type :=
	| EXTEND (v_sx : sx) : cvtop
	| WRAP : cvtop
	| CONVERT (v_sx : sx) : cvtop
	| cvtop_TRUNC (v_sx : sx) : cvtop
	| PROMOTE : cvtop
	| DEMOTE : cvtop
	| REINTERPRET : cvtop.

Global Instance Inhabited__cvtop : Inhabited (cvtop) := { default_val := EXTEND default_val }.

Definition cvtop_eq_dec : forall (v1 v2 : cvtop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition cvtop_eqb (v1 v2 : cvtop) : bool :=
	is_left(cvtop_eq_dec v1 v2).
Definition eqcvtopP : Equality.axiom (cvtop_eqb) :=
	eq_dec_Equality_axiom (cvtop) (cvtop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (cvtop) (eqcvtopP).
Hint Resolve cvtop_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-1.0/1-syntax.spectec:185.1-185.69 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:185.8-185.14 *)
Inductive wf_memarg : memarg -> Prop :=
	| memarg_case_ : forall (var_0 : u32) (var_1 : u32), 
		(wf_uN 32 var_0) ->
		(wf_uN 32 var_1) ->
		wf_memarg {| ALIGN := var_0; OFFSET := var_1 |}.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16 *)
Inductive wf_loadop_Inn : Inn -> loadop_Inn -> Prop :=
	| loadop_Inn_case_0 : forall (v_Inn : Inn) (v_sz : sz) (v_sx : sx), 
		(wf_sz v_sz) ->
		((v_sz :> nat) < (res_size (valtype_Inn v_Inn))) ->
		wf_loadop_Inn v_Inn (mk_loadop_Inn v_sz v_sx).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16 *)
Inductive wf_loadop_ : valtype -> loadop_ -> Prop :=
	| loadop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : loadop_Inn), 
		(wf_loadop_Inn v_Inn var_x) ->
		(v_valtype == (valtype_Inn v_Inn)) ->
		wf_loadop_ v_valtype (mk_loadop__0 v_Inn var_x).

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 *)
Definition proj_loadop__0 (var_x : loadop_) : loadop_Inn :=
	match var_x return loadop_Inn with
		| (mk_loadop__0 v_Inn var_x) => var_x
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:195.1-195.52 *)
Definition blocktype : Type := (option valtype).

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16 *)
Inductive instr : Type :=
	| NOP : instr
	| UNREACHABLE : instr
	| DROP : instr
	| SELECT : instr
	| BLOCK (v_blocktype : blocktype) (instr_lst : (seq instr)) : instr
	| LOOP (v_blocktype : blocktype) (instr_lst : (seq instr)) : instr
	| IFELSE (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst : (seq instr)) : instr
	| BR (v_labelidx : labelidx) : instr
	| BR_IF (v_labelidx : labelidx) : instr
	| BR_TABLE (labelidx_lst : (seq labelidx)) (v_labelidx : labelidx) : instr
	| CALL (v_funcidx : funcidx) : instr
	| CALL_INDIRECT (v_typeidx : typeidx) : instr
	| RETURN : instr
	| CONST (v_valtype : valtype) (_ : val_) : instr
	| UNOP (v_valtype : valtype) (_ : unop_) : instr
	| BINOP (v_valtype : valtype) (_ : binop_) : instr
	| TESTOP (v_valtype : valtype) (_ : testop_) : instr
	| RELOP (v_valtype : valtype) (_ : relop_) : instr
	| CVTOP (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : instr
	| LOCAL_GET (v_localidx : localidx) : instr
	| LOCAL_SET (v_localidx : localidx) : instr
	| LOCAL_TEE (v_localidx : localidx) : instr
	| GLOBAL_GET (v_globalidx : globalidx) : instr
	| GLOBAL_SET (v_globalidx : globalidx) : instr
	| LOAD (v_valtype : valtype) (_ : (option loadop_)) (v_memarg : memarg) : instr
	| STORE (v_valtype : valtype) (sz_opt : (option sz)) (v_memarg : memarg) : instr
	| MEMORY_SIZE : instr
	| MEMORY_GROW : instr.

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

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16 *)
Inductive wf_instr : instr -> Prop :=
	| instr_case_0 : wf_instr NOP
	| instr_case_1 : wf_instr UNREACHABLE
	| instr_case_2 : wf_instr DROP
	| instr_case_3 : wf_instr SELECT
	| instr_case_4 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)), 
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		wf_instr (BLOCK v_blocktype instr_lst)
	| instr_case_5 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)), 
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		wf_instr (LOOP v_blocktype instr_lst)
	| instr_case_6 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst_0 : (seq instr)), 
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
	| instr_case_11 : forall (v_typeidx : typeidx), 
		(wf_uN 32 v_typeidx) ->
		wf_instr (CALL_INDIRECT v_typeidx)
	| instr_case_12 : wf_instr RETURN
	| instr_case_13 : forall (v_valtype : valtype) (var_0 : val_), 
		(wf_val_ v_valtype var_0) ->
		wf_instr (CONST v_valtype var_0)
	| instr_case_14 : forall (v_valtype : valtype) (var_0 : unop_), 
		(wf_unop_ v_valtype var_0) ->
		wf_instr (UNOP v_valtype var_0)
	| instr_case_15 : forall (v_valtype : valtype) (var_0 : binop_), 
		(wf_binop_ v_valtype var_0) ->
		wf_instr (BINOP v_valtype var_0)
	| instr_case_16 : forall (v_valtype : valtype) (var_0 : testop_), 
		(wf_testop_ v_valtype var_0) ->
		wf_instr (TESTOP v_valtype var_0)
	| instr_case_17 : forall (v_valtype : valtype) (var_0 : relop_), 
		(wf_relop_ v_valtype var_0) ->
		wf_instr (RELOP v_valtype var_0)
	| instr_case_18 : forall (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop), 
		(valtype_1 != valtype_2) ->
		wf_instr (CVTOP valtype_1 valtype_2 v_cvtop)
	| instr_case_19 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_instr (LOCAL_GET v_localidx)
	| instr_case_20 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_instr (LOCAL_SET v_localidx)
	| instr_case_21 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_instr (LOCAL_TEE v_localidx)
	| instr_case_22 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_instr (GLOBAL_GET v_globalidx)
	| instr_case_23 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_instr (GLOBAL_SET v_globalidx)
	| instr_case_24 : forall (v_valtype : valtype) (var_0 : (option loadop_)) (v_memarg : memarg), 
		List.Forall (fun (var_0 : loadop_) => (wf_loadop_ v_valtype var_0)) (option_to_list var_0) ->
		(wf_memarg v_memarg) ->
		wf_instr (LOAD v_valtype var_0 v_memarg)
	| instr_case_25 : forall (Inn_opt : (option Inn)) (valtype_opt : (option valtype)) (v_valtype : valtype) (sz_opt : (option sz)) (v_memarg : memarg), 
		List.Forall (fun (v_sz : sz) => (wf_sz v_sz)) (option_to_list sz_opt) ->
		(wf_memarg v_memarg) ->
		((Inn_opt == None) <-> (sz_opt == None)) ->
		((Inn_opt == None) <-> (valtype_opt == None)) ->
		List_Forall3 (fun (v_Inn : Inn) (v_sz : sz) (v_valtype : valtype) => ((v_valtype == (valtype_Inn v_Inn)) && ((v_sz :> nat) < (res_size (valtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list sz_opt) (option_to_list valtype_opt) ->
		wf_instr (STORE v_valtype sz_opt v_memarg)
	| instr_case_26 : wf_instr MEMORY_SIZE
	| instr_case_27 : wf_instr MEMORY_GROW.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:252.1-253.9 *)
Definition expr : Type := (seq instr).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:263.1-264.16 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:265.1-266.16 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:267.1-268.27 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:267.8-267.12 *)
Inductive wf_func : func -> Prop :=
	| func_case_0 : forall (v_typeidx : typeidx) (local_lst : (seq local)) (v_expr : expr), 
		(wf_uN 32 v_typeidx) ->
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		wf_func (func_FUNC v_typeidx local_lst v_expr).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:269.1-270.25 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:269.8-269.14 *)
Inductive wf_global : global -> Prop :=
	| global_case_0 : forall (v_globaltype : globaltype) (v_expr : expr), 
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		wf_global (global_GLOBAL v_globaltype v_expr).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:271.1-272.18 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:271.8-271.13 *)
Inductive wf_table : table -> Prop :=
	| table_case_0 : forall (v_tabletype : tabletype), 
		(wf_limits v_tabletype) ->
		wf_table (table_TABLE v_tabletype).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:273.1-274.17 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:273.8-273.11 *)
Inductive wf_mem : mem -> Prop :=
	| mem_case_0 : forall (v_memtype : memtype), 
		(wf_limits v_memtype) ->
		wf_mem (MEMORY v_memtype).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:275.1-276.21 *)
Inductive elem : Type :=
	| ELEM (v_expr : expr) (funcidx_lst : (seq funcidx)) : elem.

Global Instance Inhabited__elem : Inhabited (elem) := { default_val := ELEM default_val default_val }.

Definition elem_eq_dec : forall (v1 v2 : elem),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elem_eqb (v1 v2 : elem) : bool :=
	is_left(elem_eq_dec v1 v2).
Definition eqelemP : Equality.axiom (elem_eqb) :=
	eq_dec_Equality_axiom (elem) (elem_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elem) (eqelemP).
Hint Resolve elem_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:275.8-275.12 *)
Inductive wf_elem : elem -> Prop :=
	| elem_case_0 : forall (v_expr : expr) (funcidx_lst : (seq funcidx)), 
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		List.Forall (fun (v_funcidx : funcidx) => (wf_uN 32 v_funcidx)) funcidx_lst ->
		wf_elem (ELEM v_expr funcidx_lst).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:277.1-278.18 *)
Inductive data : Type :=
	| DATA (v_expr : expr) (byte_lst : (seq byte)) : data.

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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:277.8-277.12 *)
Inductive wf_data : data -> Prop :=
	| data_case_0 : forall (v_expr : expr) (byte_lst : (seq byte)), 
		List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
		List.Forall (fun (v_byte : byte) => (wf_byte v_byte)) byte_lst ->
		wf_data (DATA v_expr byte_lst).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:279.1-280.16 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:279.8-279.13 *)
Inductive wf_start : start -> Prop :=
	| start_case_0 : forall (v_funcidx : funcidx), 
		(wf_uN 32 v_funcidx) ->
		wf_start (START v_funcidx).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:282.1-283.66 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:282.8-282.17 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:284.1-285.24 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:284.8-284.14 *)
Inductive wf_export : export -> Prop :=
	| export_case_0 : forall (v_name : name) (v_externidx : externidx), 
		(wf_name v_name) ->
		(wf_externidx v_externidx) ->
		wf_export (EXPORT v_name v_externidx).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:286.1-287.30 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:286.8-286.14 *)
Inductive wf_import : import -> Prop :=
	| import_case_0 : forall (v_name : name) (name_0 : name) (v_externtype : externtype), 
		(wf_name v_name) ->
		(wf_name name_0) ->
		(wf_externtype v_externtype) ->
		wf_import (IMPORT v_name name_0 v_externtype).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:289.1-290.76 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:289.8-289.14 *)
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

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:20.1-20.64 *)
Inductive fun_funcsxt : (seq externtype) -> (seq functype) -> Prop :=
	| fun_funcsxt_case_0 : fun_funcsxt [:: ] [:: ]
	| fun_funcsxt_case_1 : forall (ft : functype) (xt_lst : (seq externtype)) (var_0 : (seq functype)), 
		(fun_funcsxt xt_lst var_0) ->
		fun_funcsxt ([::(FUNC ft)] ++ xt_lst) ([::ft] ++ var_0)
	| fun_funcsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq functype)), 
		(fun_funcsxt xt_lst var_0) ->
		fun_funcsxt ([::v_externtype] ++ xt_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:21.1-21.66 *)
Inductive fun_globalsxt : (seq externtype) -> (seq globaltype) -> Prop :=
	| fun_globalsxt_case_0 : fun_globalsxt [:: ] [:: ]
	| fun_globalsxt_case_1 : forall (gt : globaltype) (xt_lst : (seq externtype)) (var_0 : (seq globaltype)), 
		(fun_globalsxt xt_lst var_0) ->
		fun_globalsxt ([::(GLOBAL gt)] ++ xt_lst) ([::gt] ++ var_0)
	| fun_globalsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq globaltype)), 
		(fun_globalsxt xt_lst var_0) ->
		fun_globalsxt ([::v_externtype] ++ xt_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:22.1-22.65 *)
Inductive fun_tablesxt : (seq externtype) -> (seq tabletype) -> Prop :=
	| fun_tablesxt_case_0 : fun_tablesxt [:: ] [:: ]
	| fun_tablesxt_case_1 : forall (res_tt : limits) (xt_lst : (seq externtype)) (var_0 : (seq tabletype)), 
		(fun_tablesxt xt_lst var_0) ->
		fun_tablesxt ([::(TABLE res_tt)] ++ xt_lst) ([::res_tt] ++ var_0)
	| fun_tablesxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq tabletype)), 
		(fun_tablesxt xt_lst var_0) ->
		fun_tablesxt ([::v_externtype] ++ xt_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:23.1-23.63 *)
Inductive fun_memsxt : (seq externtype) -> (seq memtype) -> Prop :=
	| fun_memsxt_case_0 : fun_memsxt [:: ] [:: ]
	| fun_memsxt_case_1 : forall (mt : limits) (xt_lst : (seq externtype)) (var_0 : (seq memtype)), 
		(fun_memsxt xt_lst var_0) ->
		fun_memsxt ([::(MEM mt)] ++ xt_lst) ([::mt] ++ var_0)
	| fun_memsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (seq externtype)) (var_0 : (seq memtype)), 
		(fun_memsxt xt_lst var_0) ->
		fun_memsxt ([::v_externtype] ++ xt_lst) var_0.

(* Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:49.1-49.35 *)
Definition memarg0 : memarg := {| ALIGN := (mk_uN 0); OFFSET := (mk_uN 0) |}.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:7.1-7.22 *)
Definition res_bool (v_bool : bool) : nat :=
	match v_bool return nat with
		| false => 0
		| true => 1
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:11.1-11.23 *)
Axiom truncz : forall (rat : nat), nat.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:18.6-18.14 *)
Inductive fun_signed_ : res_N -> nat -> nat -> Prop :=
	| fun_signed__case_0 : forall (v_N : nat) (i : nat), 
		(i < (2 ^ (((v_N : nat) - (1 : nat)) : nat))) ->
		fun_signed_ v_N i (i : nat)
	| fun_signed__case_1 : forall (v_N : nat) (i : nat), 
		(((2 ^ (((v_N : nat) - (1 : nat)) : nat)) <= i) && (i < (2 ^ v_N))) ->
		fun_signed_ v_N i ((i : nat) - ((2 ^ v_N) : nat)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:22.6-22.18 *)
Inductive fun_inv_signed_ : res_N -> nat -> nat -> Prop :=
	| fun_inv_signed__case_0 : forall (v_N : nat) (i : nat), 
		(((0 : nat) <= i) && (i < ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat))) ->
		fun_inv_signed_ v_N i (i : nat)
	| fun_inv_signed__case_1 : forall (v_N : nat) (i : nat), 
		(((0 - ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat)) <= i) && (i < (0 : nat))) ->
		fun_inv_signed_ v_N i ((i + ((2 ^ v_N) : nat)) : nat).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:152.1-152.30 *)
Axiom fabs_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:155.1-155.31 *)
Axiom fceil_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:156.1-156.32 *)
Axiom ffloor_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:158.1-158.34 *)
Axiom fnearest_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:153.1-153.30 *)
Axiom fneg_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:154.1-154.31 *)
Axiom fsqrt_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:157.1-157.32 *)
Axiom ftrunc_ : forall (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:86.1-86.29 *)
Axiom iclz_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:87.1-87.29 *)
Axiom ictz_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:88.1-88.32 *)
Axiom ipopcnt_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12 *)
Inductive fun_unop_ : valtype -> unop_ -> val_ -> (seq val_) -> Prop :=
	| fun_unop__case_0 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (iclz_ (res_size (valtype_Inn Inn_I32)) v_iN))) ->
		fun_unop_ I32 (mk_unop__0 Inn_I32 CLZ) (mk_val__0 Inn_I32 v_iN) [::(mk_val__0 Inn_I32 (iclz_ (res_size (valtype_Inn Inn_I32)) v_iN))]
	| fun_unop__case_1 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (iclz_ (res_size (valtype_Inn Inn_I64)) v_iN))) ->
		fun_unop_ I64 (mk_unop__0 Inn_I64 CLZ) (mk_val__0 Inn_I64 v_iN) [::(mk_val__0 Inn_I64 (iclz_ (res_size (valtype_Inn Inn_I64)) v_iN))]
	| fun_unop__case_2 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (ictz_ (res_size (valtype_Inn Inn_I32)) v_iN))) ->
		fun_unop_ I32 (mk_unop__0 Inn_I32 CTZ) (mk_val__0 Inn_I32 v_iN) [::(mk_val__0 Inn_I32 (ictz_ (res_size (valtype_Inn Inn_I32)) v_iN))]
	| fun_unop__case_3 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (ictz_ (res_size (valtype_Inn Inn_I64)) v_iN))) ->
		fun_unop_ I64 (mk_unop__0 Inn_I64 CTZ) (mk_val__0 Inn_I64 v_iN) [::(mk_val__0 Inn_I64 (ictz_ (res_size (valtype_Inn Inn_I64)) v_iN))]
	| fun_unop__case_4 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (ipopcnt_ (res_size (valtype_Inn Inn_I32)) v_iN))) ->
		fun_unop_ I32 (mk_unop__0 Inn_I32 POPCNT) (mk_val__0 Inn_I32 v_iN) [::(mk_val__0 Inn_I32 (ipopcnt_ (res_size (valtype_Inn Inn_I32)) v_iN))]
	| fun_unop__case_5 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (ipopcnt_ (res_size (valtype_Inn Inn_I64)) v_iN))) ->
		fun_unop_ I64 (mk_unop__0 Inn_I64 POPCNT) (mk_val__0 Inn_I64 v_iN) [::(mk_val__0 Inn_I64 (ipopcnt_ (res_size (valtype_Inn Inn_I64)) v_iN))]
	| fun_unop__case_6 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_1 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_1))) (fabs_ (res_size (valtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 ABS) (mk_val__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_2 : fN) => (mk_val__1 Fnn_F32 iter_0_2)) (fabs_ (res_size (valtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_7 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_3 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_3))) (fabs_ (res_size (valtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 ABS) (mk_val__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_4 : fN) => (mk_val__1 Fnn_F64 iter_0_4)) (fabs_ (res_size (valtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_8 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_5 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_5))) (fneg_ (res_size (valtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 unop_Fnn_NEG) (mk_val__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_6 : fN) => (mk_val__1 Fnn_F32 iter_0_6)) (fneg_ (res_size (valtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_9 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_7 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_7))) (fneg_ (res_size (valtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 unop_Fnn_NEG) (mk_val__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_8 : fN) => (mk_val__1 Fnn_F64 iter_0_8)) (fneg_ (res_size (valtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_10 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_9 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_9))) (fsqrt_ (res_size (valtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 SQRT) (mk_val__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_10 : fN) => (mk_val__1 Fnn_F32 iter_0_10)) (fsqrt_ (res_size (valtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_11 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_11 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_11))) (fsqrt_ (res_size (valtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 SQRT) (mk_val__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_12 : fN) => (mk_val__1 Fnn_F64 iter_0_12)) (fsqrt_ (res_size (valtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_12 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_13 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_13))) (fceil_ (res_size (valtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 CEIL) (mk_val__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_14 : fN) => (mk_val__1 Fnn_F32 iter_0_14)) (fceil_ (res_size (valtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_13 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_15 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_15))) (fceil_ (res_size (valtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 CEIL) (mk_val__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_16 : fN) => (mk_val__1 Fnn_F64 iter_0_16)) (fceil_ (res_size (valtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_14 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_17 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_17))) (ffloor_ (res_size (valtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 FLOOR) (mk_val__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_18 : fN) => (mk_val__1 Fnn_F32 iter_0_18)) (ffloor_ (res_size (valtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_15 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_19 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_19))) (ffloor_ (res_size (valtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 FLOOR) (mk_val__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_20 : fN) => (mk_val__1 Fnn_F64 iter_0_20)) (ffloor_ (res_size (valtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_16 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_21 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_21))) (ftrunc_ (res_size (valtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 TRUNC) (mk_val__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_22 : fN) => (mk_val__1 Fnn_F32 iter_0_22)) (ftrunc_ (res_size (valtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_17 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_23 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_23))) (ftrunc_ (res_size (valtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 TRUNC) (mk_val__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_24 : fN) => (mk_val__1 Fnn_F64 iter_0_24)) (ftrunc_ (res_size (valtype_Fnn Fnn_F64)) v_fN))
	| fun_unop__case_18 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_25 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_25))) (fnearest_ (res_size (valtype_Fnn Fnn_F32)) v_fN) ->
		fun_unop_ F32 (mk_unop__1 Fnn_F32 NEAREST) (mk_val__1 Fnn_F32 v_fN) (seq.map (fun (iter_0_26 : fN) => (mk_val__1 Fnn_F32 iter_0_26)) (fnearest_ (res_size (valtype_Fnn Fnn_F32)) v_fN))
	| fun_unop__case_19 : forall (v_fN : fN), 
		List.Forall (fun (iter_0_27 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_27))) (fnearest_ (res_size (valtype_Fnn Fnn_F64)) v_fN) ->
		fun_unop_ F64 (mk_unop__1 Fnn_F64 NEAREST) (mk_val__1 Fnn_F64 v_fN) (seq.map (fun (iter_0_28 : fN) => (mk_val__1 Fnn_F64 iter_0_28)) (fnearest_ (res_size (valtype_Fnn Fnn_F64)) v_fN)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:145.1-145.37 *)
Axiom fadd_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:151.1-151.42 *)
Axiom fcopysign_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:148.1-148.37 *)
Axiom fdiv_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:150.1-150.37 *)
Axiom fmax_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:149.1-149.37 *)
Axiom fmin_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:147.1-147.37 *)
Axiom fmul_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:146.1-146.37 *)
Axiom fsub_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), (seq fN).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:73.1-73.36 *)
Definition iadd_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : iN :=
	match v_N, v_iN, v_iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN (((i_1 :> nat) + (i_2 :> nat)) mod (2 ^ v_N)))
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:79.1-79.36 *)
Axiom iand_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:75.1-75.36 *)
Definition imul_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : iN :=
	match v_N, v_iN, v_iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN (((i_1 :> nat) * (i_2 :> nat)) mod (2 ^ v_N)))
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:80.1-80.35 *)
Axiom ior_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12 *)
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

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:84.1-84.37 *)
Axiom irotl_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:85.1-85.37 *)
Axiom irotr_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:82.1-82.34 *)
Axiom ishl_ : forall (v_N : res_N) (v_iN : iN) (v_u32 : u32), iN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:83.1-83.74 *)
Axiom ishr_ : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (v_u32 : u32), iN.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:74.1-74.36 *)
Definition isub_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : iN :=
	match v_N, v_iN, v_iN_0 return iN with
		| v_N, i_1, i_2 => (mk_uN ((((((2 ^ v_N) + (i_1 :> nat)) : nat) - ((i_2 :> nat) : nat)) mod ((2 ^ v_N) : nat)) : nat))
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:81.1-81.36 *)
Axiom ixor_ : forall (v_N : res_N) (v_iN : iN) (v_iN_0 : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13 *)
Inductive fun_binop_ : valtype -> binop_ -> val_ -> val_ -> (seq val_) -> Prop :=
	| fun_binop__case_0 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (iadd_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 ADD) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (iadd_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_1 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (iadd_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 ADD) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (iadd_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_2 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (isub_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 SUB) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (isub_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_3 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (isub_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 SUB) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (isub_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_4 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (imul_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 MUL) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (imul_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_5 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (imul_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 MUL) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (imul_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_idiv_ (res_size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		List.Forall (fun (iter_0_29 : iN) => (wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 iter_0_29))) (option_to_list var_0) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 (DIV v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (list_ val_ (option_map (fun (iter_0_30 : iN) => (mk_val__0 Inn_I32 iter_0_30)) var_0))
	| fun_binop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_idiv_ (res_size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		List.Forall (fun (iter_0_31 : iN) => (wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 iter_0_31))) (option_to_list var_0) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 (DIV v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (list_ val_ (option_map (fun (iter_0_32 : iN) => (mk_val__0 Inn_I64 iter_0_32)) var_0))
	| fun_binop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_irem_ (res_size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		List.Forall (fun (iter_0_33 : iN) => (wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 iter_0_33))) (option_to_list var_0) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 (REM v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (list_ val_ (option_map (fun (iter_0_34 : iN) => (mk_val__0 Inn_I32 iter_0_34)) var_0))
	| fun_binop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (option iN)), 
		(fun_irem_ (res_size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		List.Forall (fun (iter_0_35 : iN) => (wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 iter_0_35))) (option_to_list var_0) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 (REM v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (list_ val_ (option_map (fun (iter_0_36 : iN) => (mk_val__0 Inn_I64 iter_0_36)) var_0))
	| fun_binop__case_10 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (iand_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 AND) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (iand_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_11 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (iand_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 AND) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (iand_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_12 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (ior_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 OR) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (ior_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_13 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (ior_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 OR) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (ior_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_14 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (ixor_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 XOR) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (ixor_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_15 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (ixor_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 XOR) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (ixor_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_16 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (ishl_ (res_size (valtype_Inn Inn_I32)) iN_1 (mk_uN (iN_2 :> (nat)))))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 SHL) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (ishl_ (res_size (valtype_Inn Inn_I32)) iN_1 (mk_uN (iN_2 :> (nat)))))]
	| fun_binop__case_17 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (ishl_ (res_size (valtype_Inn Inn_I64)) iN_1 (mk_uN (iN_2 :> (nat)))))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 SHL) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (ishl_ (res_size (valtype_Inn Inn_I64)) iN_1 (mk_uN (iN_2 :> (nat)))))]
	| fun_binop__case_18 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (ishr_ (res_size (valtype_Inn Inn_I32)) v_sx iN_1 (mk_uN (iN_2 :> (nat)))))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 (SHR v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (ishr_ (res_size (valtype_Inn Inn_I32)) v_sx iN_1 (mk_uN (iN_2 :> (nat)))))]
	| fun_binop__case_19 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (ishr_ (res_size (valtype_Inn Inn_I64)) v_sx iN_1 (mk_uN (iN_2 :> (nat)))))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 (SHR v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (ishr_ (res_size (valtype_Inn Inn_I64)) v_sx iN_1 (mk_uN (iN_2 :> (nat)))))]
	| fun_binop__case_20 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (irotl_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 ROTL) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (irotl_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_21 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (irotl_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 ROTL) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (irotl_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_22 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 (irotr_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_binop_ I32 (mk_binop__0 Inn_I32 ROTR) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [::(mk_val__0 Inn_I32 (irotr_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))]
	| fun_binop__case_23 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 (irotr_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_binop_ I64 (mk_binop__0 Inn_I64 ROTR) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [::(mk_val__0 Inn_I64 (irotr_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))]
	| fun_binop__case_24 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_37 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_37))) (fadd_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_ADD) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_38 : fN) => (mk_val__1 Fnn_F32 iter_0_38)) (fadd_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_25 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_39 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_39))) (fadd_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_ADD) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_40 : fN) => (mk_val__1 Fnn_F64 iter_0_40)) (fadd_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_26 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_41 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_41))) (fsub_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_SUB) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_42 : fN) => (mk_val__1 Fnn_F32 iter_0_42)) (fsub_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_27 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_43 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_43))) (fsub_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_SUB) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_44 : fN) => (mk_val__1 Fnn_F64 iter_0_44)) (fsub_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_28 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_45 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_45))) (fmul_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_MUL) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_46 : fN) => (mk_val__1 Fnn_F32 iter_0_46)) (fmul_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_29 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_47 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_47))) (fmul_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_48 : fN) => (mk_val__1 Fnn_F64 iter_0_48)) (fmul_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_30 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_49 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_49))) (fdiv_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 binop_Fnn_DIV) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_50 : fN) => (mk_val__1 Fnn_F32 iter_0_50)) (fdiv_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_31 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_51 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_51))) (fdiv_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 binop_Fnn_DIV) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_52 : fN) => (mk_val__1 Fnn_F64 iter_0_52)) (fdiv_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_32 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_53 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_53))) (fmin_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 MIN) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_54 : fN) => (mk_val__1 Fnn_F32 iter_0_54)) (fmin_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_33 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_55 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_55))) (fmin_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 MIN) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_56 : fN) => (mk_val__1 Fnn_F64 iter_0_56)) (fmin_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_34 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_57 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_57))) (fmax_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 MAX) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_58 : fN) => (mk_val__1 Fnn_F32 iter_0_58)) (fmax_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_35 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_59 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_59))) (fmax_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 MAX) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_60 : fN) => (mk_val__1 Fnn_F64 iter_0_60)) (fmax_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_binop__case_36 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_61 : fN) => (wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 iter_0_61))) (fcopysign_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2) ->
		fun_binop_ F32 (mk_binop__1 Fnn_F32 COPYSIGN) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (seq.map (fun (iter_0_62 : fN) => (mk_val__1 Fnn_F32 iter_0_62)) (fcopysign_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_binop__case_37 : forall (fN_1 : fN) (fN_2 : fN), 
		List.Forall (fun (iter_0_63 : fN) => (wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 iter_0_63))) (fcopysign_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2) ->
		fun_binop_ F64 (mk_binop__1 Fnn_F64 COPYSIGN) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (seq.map (fun (iter_0_64 : fN) => (mk_val__1 Fnn_F64 iter_0_64)) (fcopysign_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2)).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:89.1-89.27 *)
Definition ieqz_ (v_N : res_N) (v_iN : iN) : u32 :=
	match v_N, v_iN return u32 with
		| v_N, i_1 => (mk_uN (res_bool ((i_1 :> nat) == 0)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14 *)
Inductive fun_testop_ : valtype -> testop_ -> val_ -> val_ -> Prop :=
	| fun_testop__case_0 : forall (v_iN : uN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (ieqz_ (res_size (valtype_Inn Inn_I32)) v_iN))) ->
		fun_testop_ I32 (mk_testop__0 Inn_I32 EQZ) (mk_val__0 Inn_I32 v_iN) (mk_val__0 Inn_I32 (ieqz_ (res_size (valtype_Inn Inn_I32)) v_iN))
	| fun_testop__case_1 : forall (v_iN : uN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (ieqz_ (res_size (valtype_Inn Inn_I64)) v_iN))) ->
		fun_testop_ I64 (mk_testop__0 Inn_I64 EQZ) (mk_val__0 Inn_I64 v_iN) (mk_val__0 Inn_I32 (ieqz_ (res_size (valtype_Inn Inn_I64)) v_iN)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:159.1-159.33 *)
Axiom feq_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:164.1-164.33 *)
Axiom fge_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:162.1-162.33 *)
Axiom fgt_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:163.1-163.33 *)
Axiom fle_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:161.1-161.33 *)
Axiom flt_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:160.1-160.33 *)
Axiom fne_ : forall (v_N : res_N) (v_fN : fN) (v_fN_0 : fN), u32.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:91.1-91.33 *)
Definition ieq_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : u32 :=
	match v_N, v_iN, v_iN_0 return u32 with
		| v_N, i_1, i_2 => (mk_uN (res_bool (i_1 == i_2)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:96.6-96.11 *)
Inductive fun_ige_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ige__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ige_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) >= (i_2 :> nat))))
	| fun_ige__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ige_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 >= var_1))).

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:94.6-94.11 *)
Inductive fun_igt_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_igt__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_igt_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) > (i_2 :> nat))))
	| fun_igt__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_igt_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 > var_1))).

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:95.6-95.11 *)
Inductive fun_ile_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ile__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ile_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) <= (i_2 :> nat))))
	| fun_ile__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ile_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 <= var_1))).

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:93.6-93.11 *)
Inductive fun_ilt_ : res_N -> sx -> iN -> iN -> u32 -> Prop :=
	| fun_ilt__case_0 : forall (v_N : nat) (i_1 : uN) (i_2 : uN), fun_ilt_ v_N U i_1 i_2 (mk_uN (res_bool ((i_1 :> nat) < (i_2 :> nat))))
	| fun_ilt__case_1 : forall (v_N : nat) (i_1 : uN) (i_2 : uN) (var_1 : nat) (var_0 : nat), 
		(fun_signed_ v_N (i_2 :> nat) var_1) ->
		(fun_signed_ v_N (i_1 :> nat) var_0) ->
		fun_ilt_ v_N res_S i_1 i_2 (mk_uN (res_bool (var_0 < var_1))).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:92.1-92.33 *)
Definition ine_ (v_N : res_N) (v_iN : iN) (v_iN_0 : iN) : u32 :=
	match v_N, v_iN, v_iN_0 return u32 with
		| v_N, i_1, i_2 => (mk_uN (res_bool (i_1 != i_2)))
	end.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13 *)
Inductive fun_relop_ : valtype -> relop_ -> val_ -> val_ -> val_ -> Prop :=
	| fun_relop__case_0 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (ieq_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 EQ) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 (ieq_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))
	| fun_relop__case_1 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (ieq_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 EQ) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 (ieq_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))
	| fun_relop__case_2 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (ine_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 NE) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 (ine_ (res_size (valtype_Inn Inn_I32)) iN_1 iN_2))
	| fun_relop__case_3 : forall (iN_1 : uN) (iN_2 : uN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (ine_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 NE) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 (ine_ (res_size (valtype_Inn Inn_I64)) iN_1 iN_2))
	| fun_relop__case_4 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ilt_ (res_size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		(wf_val_ I32 (mk_val__0 Inn_I32 var_0)) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (LT v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 var_0)
	| fun_relop__case_5 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ilt_ (res_size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		(wf_val_ I32 (mk_val__0 Inn_I32 var_0)) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (LT v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 var_0)
	| fun_relop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_igt_ (res_size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		(wf_val_ I32 (mk_val__0 Inn_I32 var_0)) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (GT v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 var_0)
	| fun_relop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_igt_ (res_size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		(wf_val_ I32 (mk_val__0 Inn_I32 var_0)) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (GT v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 var_0)
	| fun_relop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ile_ (res_size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		(wf_val_ I32 (mk_val__0 Inn_I32 var_0)) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (LE v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 var_0)
	| fun_relop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ile_ (res_size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		(wf_val_ I32 (mk_val__0 Inn_I32 var_0)) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (LE v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 var_0)
	| fun_relop__case_10 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ige_ (res_size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ->
		(wf_val_ I32 (mk_val__0 Inn_I32 var_0)) ->
		fun_relop_ I32 (mk_relop__0 Inn_I32 (GE v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 var_0)
	| fun_relop__case_11 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
		(fun_ige_ (res_size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ->
		(wf_val_ I32 (mk_val__0 Inn_I32 var_0)) ->
		fun_relop_ I64 (mk_relop__0 Inn_I64 (GE v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 var_0)
	| fun_relop__case_12 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (feq_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_EQ) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (feq_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_13 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (feq_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_EQ) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (feq_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_14 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (fne_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_NE) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (fne_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_15 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (fne_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_NE) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (fne_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_16 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (flt_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_LT) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (flt_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_17 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (flt_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_LT) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (flt_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_18 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (fgt_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_GT) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (fgt_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_19 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (fgt_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_GT) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (fgt_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_20 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (fle_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_LE) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (fle_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_21 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (fle_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_LE) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (fle_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))
	| fun_relop__case_22 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (fge_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))) ->
		fun_relop_ F32 (mk_relop__1 Fnn_F32 relop_Fnn_GE) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (fge_ (res_size (valtype_Fnn Fnn_F32)) fN_1 fN_2))
	| fun_relop__case_23 : forall (fN_1 : fN) (fN_2 : fN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (fge_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2))) ->
		fun_relop_ F64 (mk_relop__1 Fnn_F64 relop_Fnn_GE) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (fge_ (res_size (valtype_Fnn Fnn_F64)) fN_1 fN_2)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:44.1-44.90 *)
Axiom convert__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN), fN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:42.1-42.36 *)
Axiom demote__ : forall (v_M : M) (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:40.1-40.89 *)
Axiom extend__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN), iN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:43.1-43.37 *)
Axiom promote__ : forall (v_M : M) (v_N : res_N) (v_fN : fN), (seq fN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:45.1-45.76 *)
Axiom reinterpret__ : forall (valtype_1 : valtype) (valtype_2 : valtype) (v_val_ : val_), val_.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:41.1-41.88 *)
Axiom trunc__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN), (option iN).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:39.1-39.33 *)
Axiom wrap__ : forall (v_M : M) (v_N : res_N) (v_iN : iN), iN.

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14 *)
Inductive fun_cvtop__ : valtype -> valtype -> cvtop -> val_ -> (seq val_) -> Prop :=
	| fun_cvtop___case_0 : forall (v_sx : sx) (v_iN : uN), 
		(wf_val_ I64 (mk_val__0 Inn_I64 (extend__ 32 64 v_sx v_iN))) ->
		fun_cvtop__ I32 I64 (EXTEND v_sx) (mk_val__0 Inn_I32 v_iN) [::(mk_val__0 Inn_I64 (extend__ 32 64 v_sx v_iN))]
	| fun_cvtop___case_1 : forall (v_iN : uN), 
		(wf_val_ I32 (mk_val__0 Inn_I32 (wrap__ 64 32 v_iN))) ->
		fun_cvtop__ I64 I32 WRAP (mk_val__0 Inn_I64 v_iN) [::(mk_val__0 Inn_I32 (wrap__ 64 32 v_iN))]
	| fun_cvtop___case_2 : forall (v_sx : sx) (v_fN : fN), 
		List.Forall (fun (iter_0_65 : iN) => (wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 iter_0_65))) (option_to_list (trunc__ (res_size (valtype_Fnn Fnn_F32)) (res_size (valtype_Inn Inn_I32)) v_sx v_fN)) ->
		fun_cvtop__ F32 I32 (cvtop_TRUNC v_sx) (mk_val__1 Fnn_F32 v_fN) (list_ val_ (option_map (fun (iter_0_66 : iN) => (mk_val__0 Inn_I32 iter_0_66)) (trunc__ (res_size (valtype_Fnn Fnn_F32)) (res_size (valtype_Inn Inn_I32)) v_sx v_fN)))
	| fun_cvtop___case_3 : forall (v_sx : sx) (v_fN : fN), 
		List.Forall (fun (iter_0_67 : iN) => (wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 iter_0_67))) (option_to_list (trunc__ (res_size (valtype_Fnn Fnn_F64)) (res_size (valtype_Inn Inn_I32)) v_sx v_fN)) ->
		fun_cvtop__ F64 I32 (cvtop_TRUNC v_sx) (mk_val__1 Fnn_F64 v_fN) (list_ val_ (option_map (fun (iter_0_68 : iN) => (mk_val__0 Inn_I32 iter_0_68)) (trunc__ (res_size (valtype_Fnn Fnn_F64)) (res_size (valtype_Inn Inn_I32)) v_sx v_fN)))
	| fun_cvtop___case_4 : forall (v_sx : sx) (v_fN : fN), 
		List.Forall (fun (iter_0_69 : iN) => (wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 iter_0_69))) (option_to_list (trunc__ (res_size (valtype_Fnn Fnn_F32)) (res_size (valtype_Inn Inn_I64)) v_sx v_fN)) ->
		fun_cvtop__ F32 I64 (cvtop_TRUNC v_sx) (mk_val__1 Fnn_F32 v_fN) (list_ val_ (option_map (fun (iter_0_70 : iN) => (mk_val__0 Inn_I64 iter_0_70)) (trunc__ (res_size (valtype_Fnn Fnn_F32)) (res_size (valtype_Inn Inn_I64)) v_sx v_fN)))
	| fun_cvtop___case_5 : forall (v_sx : sx) (v_fN : fN), 
		List.Forall (fun (iter_0_71 : iN) => (wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 iter_0_71))) (option_to_list (trunc__ (res_size (valtype_Fnn Fnn_F64)) (res_size (valtype_Inn Inn_I64)) v_sx v_fN)) ->
		fun_cvtop__ F64 I64 (cvtop_TRUNC v_sx) (mk_val__1 Fnn_F64 v_fN) (list_ val_ (option_map (fun (iter_0_72 : iN) => (mk_val__0 Inn_I64 iter_0_72)) (trunc__ (res_size (valtype_Fnn Fnn_F64)) (res_size (valtype_Inn Inn_I64)) v_sx v_fN)))
	| fun_cvtop___case_6 : forall (v_fN : fN), 
		List.Forall (fun (iter_0 : fN) => (wf_val_ F64 (mk_val__1 Fnn_F64 iter_0))) (promote__ 32 64 v_fN) ->
		fun_cvtop__ F32 F64 PROMOTE (mk_val__1 Fnn_F32 v_fN) (seq.map (fun (iter_0 : fN) => (mk_val__1 Fnn_F64 iter_0)) (promote__ 32 64 v_fN))
	| fun_cvtop___case_7 : forall (v_fN : fN), 
		List.Forall (fun (iter_0 : fN) => (wf_val_ F32 (mk_val__1 Fnn_F32 iter_0))) (demote__ 64 32 v_fN) ->
		fun_cvtop__ F64 F32 DEMOTE (mk_val__1 Fnn_F64 v_fN) (seq.map (fun (iter_0 : fN) => (mk_val__1 Fnn_F32 iter_0)) (demote__ 64 32 v_fN))
	| fun_cvtop___case_8 : forall (v_sx : sx) (v_iN : uN), 
		(wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 (convert__ (res_size (valtype_Inn Inn_I32)) (res_size (valtype_Fnn Fnn_F32)) v_sx v_iN))) ->
		fun_cvtop__ I32 F32 (CONVERT v_sx) (mk_val__0 Inn_I32 v_iN) [::(mk_val__1 Fnn_F32 (convert__ (res_size (valtype_Inn Inn_I32)) (res_size (valtype_Fnn Fnn_F32)) v_sx v_iN))]
	| fun_cvtop___case_9 : forall (v_sx : sx) (v_iN : uN), 
		(wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 (convert__ (res_size (valtype_Inn Inn_I64)) (res_size (valtype_Fnn Fnn_F32)) v_sx v_iN))) ->
		fun_cvtop__ I64 F32 (CONVERT v_sx) (mk_val__0 Inn_I64 v_iN) [::(mk_val__1 Fnn_F32 (convert__ (res_size (valtype_Inn Inn_I64)) (res_size (valtype_Fnn Fnn_F32)) v_sx v_iN))]
	| fun_cvtop___case_10 : forall (v_sx : sx) (v_iN : uN), 
		(wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 (convert__ (res_size (valtype_Inn Inn_I32)) (res_size (valtype_Fnn Fnn_F64)) v_sx v_iN))) ->
		fun_cvtop__ I32 F64 (CONVERT v_sx) (mk_val__0 Inn_I32 v_iN) [::(mk_val__1 Fnn_F64 (convert__ (res_size (valtype_Inn Inn_I32)) (res_size (valtype_Fnn Fnn_F64)) v_sx v_iN))]
	| fun_cvtop___case_11 : forall (v_sx : sx) (v_iN : uN), 
		(wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 (convert__ (res_size (valtype_Inn Inn_I64)) (res_size (valtype_Fnn Fnn_F64)) v_sx v_iN))) ->
		fun_cvtop__ I64 F64 (CONVERT v_sx) (mk_val__0 Inn_I64 v_iN) [::(mk_val__1 Fnn_F64 (convert__ (res_size (valtype_Inn Inn_I64)) (res_size (valtype_Fnn Fnn_F64)) v_sx v_iN))]
	| fun_cvtop___case_12 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 v_iN)) ->
		((res_size (valtype_Inn Inn_I32)) == (res_size (valtype_Fnn Fnn_F32))) ->
		fun_cvtop__ I32 F32 REINTERPRET (mk_val__0 Inn_I32 v_iN) [::(reinterpret__ (valtype_Inn Inn_I32) (valtype_Fnn Fnn_F32) (mk_val__0 Inn_I32 v_iN))]
	| fun_cvtop___case_13 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 v_iN)) ->
		((res_size (valtype_Inn Inn_I64)) == (res_size (valtype_Fnn Fnn_F32))) ->
		fun_cvtop__ I64 F32 REINTERPRET (mk_val__0 Inn_I64 v_iN) [::(reinterpret__ (valtype_Inn Inn_I64) (valtype_Fnn Fnn_F32) (mk_val__0 Inn_I64 v_iN))]
	| fun_cvtop___case_14 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I32) (mk_val__0 Inn_I32 v_iN)) ->
		((res_size (valtype_Inn Inn_I32)) == (res_size (valtype_Fnn Fnn_F64))) ->
		fun_cvtop__ I32 F64 REINTERPRET (mk_val__0 Inn_I32 v_iN) [::(reinterpret__ (valtype_Inn Inn_I32) (valtype_Fnn Fnn_F64) (mk_val__0 Inn_I32 v_iN))]
	| fun_cvtop___case_15 : forall (v_iN : uN), 
		(wf_val_ (valtype_Inn Inn_I64) (mk_val__0 Inn_I64 v_iN)) ->
		((res_size (valtype_Inn Inn_I64)) == (res_size (valtype_Fnn Fnn_F64))) ->
		fun_cvtop__ I64 F64 REINTERPRET (mk_val__0 Inn_I64 v_iN) [::(reinterpret__ (valtype_Inn Inn_I64) (valtype_Fnn Fnn_F64) (mk_val__0 Inn_I64 v_iN))]
	| fun_cvtop___case_16 : forall (v_fN : fN), 
		(wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 v_fN)) ->
		((res_size (valtype_Inn Inn_I32)) == (res_size (valtype_Fnn Fnn_F32))) ->
		fun_cvtop__ F32 I32 REINTERPRET (mk_val__1 Fnn_F32 v_fN) [::(reinterpret__ (valtype_Fnn Fnn_F32) (valtype_Inn Inn_I32) (mk_val__1 Fnn_F32 v_fN))]
	| fun_cvtop___case_17 : forall (v_fN : fN), 
		(wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 v_fN)) ->
		((res_size (valtype_Inn Inn_I32)) == (res_size (valtype_Fnn Fnn_F64))) ->
		fun_cvtop__ F64 I32 REINTERPRET (mk_val__1 Fnn_F64 v_fN) [::(reinterpret__ (valtype_Fnn Fnn_F64) (valtype_Inn Inn_I32) (mk_val__1 Fnn_F64 v_fN))]
	| fun_cvtop___case_18 : forall (v_fN : fN), 
		(wf_val_ (valtype_Fnn Fnn_F32) (mk_val__1 Fnn_F32 v_fN)) ->
		((res_size (valtype_Inn Inn_I64)) == (res_size (valtype_Fnn Fnn_F32))) ->
		fun_cvtop__ F32 I64 REINTERPRET (mk_val__1 Fnn_F32 v_fN) [::(reinterpret__ (valtype_Fnn Fnn_F32) (valtype_Inn Inn_I64) (mk_val__1 Fnn_F32 v_fN))]
	| fun_cvtop___case_19 : forall (v_fN : fN), 
		(wf_val_ (valtype_Fnn Fnn_F64) (mk_val__1 Fnn_F64 v_fN)) ->
		((res_size (valtype_Inn Inn_I64)) == (res_size (valtype_Fnn Fnn_F64))) ->
		fun_cvtop__ F64 I64 REINTERPRET (mk_val__1 Fnn_F64 v_fN) [::(reinterpret__ (valtype_Fnn Fnn_F64) (valtype_Inn Inn_I64) (mk_val__1 Fnn_F64 v_fN))].

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:56.1-56.102 *)
Axiom ibytes_ : forall (v_N : res_N) (v_iN : iN), (seq byte).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:57.1-57.102 *)
Axiom fbytes_ : forall (v_N : res_N) (v_fN : fN), (seq byte).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:58.1-58.75 *)
Axiom bytes_ : forall (v_valtype : valtype) (v_val_ : val_), (seq byte).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:60.1-60.75 *)
Axiom inv_ibytes_ : forall (v_N : res_N) (var_0 : (seq byte)), iN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:61.1-61.75 *)
Axiom inv_fbytes_ : forall (v_N : res_N) (var_0 : (seq byte)), fN.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:62.1-62.73 *)
Axiom inv_bytes_ : forall (v_valtype : valtype) (var_0 : (seq byte)), val_.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:78.1-78.29 *)
Axiom inot_ : forall (v_N : res_N) (v_iN : iN), iN.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:90.1-90.27 *)
Definition inez_ (v_N : res_N) (v_iN : iN) : u32 :=
	match v_N, v_iN return u32 with
		| v_N, i_1 => (mk_uN (res_bool ((i_1 :> nat) != 0)))
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:5.1-5.39 *)
Definition addr : Type := nat.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:6.1-6.53 *)
Definition funcaddr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:7.1-7.53 *)
Definition globaladdr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:8.1-8.51 *)
Definition tableaddr : Type := addr.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:9.1-9.50 *)
Definition memaddr : Type := addr.

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:20.1-21.70 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:32.1-33.55 *)
Inductive val : Type :=
	| val_CONST (v_valtype : valtype) (_ : val_) : val.

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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:32.8-32.11 *)
Inductive wf_val : val -> Prop :=
	| val_case_0 : forall (v_valtype : valtype) (var_0 : val_), 
		(wf_val_ v_valtype var_0) ->
		wf_val (val_CONST v_valtype var_0).

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:35.1-36.22 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:35.8-35.14 *)
Inductive wf_result : result -> Prop :=
	| result_case_0 : forall (val_lst : (seq val)), 
		List.Forall (fun (v_val : val) => (wf_val v_val)) val_lst ->
		wf_result (_VALS val_lst)
	| result_case_1 : wf_result TRAP.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:61.1-63.22 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:61.8-61.18 *)
Inductive wf_exportinst : exportinst -> Prop :=
	| exportinst_case_ : forall (var_0 : name) (var_1 : externaddr), 
		(wf_name var_0) ->
		wf_exportinst {| NAME := var_0; ADDR := var_1 |}.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:65.1-71.26 *)
Record moduleinst := MKmoduleinst
{	TYPES : (seq functype)
;	FUNCS : (seq funcaddr)
;	GLOBALS : (seq globaladdr)
;	TABLES : (seq tableaddr)
;	MEMS : (seq memaddr)
;	EXPORTS : (seq exportinst)
}.

Global Instance Inhabited_moduleinst : Inhabited (moduleinst) := 
{default_val := {|
	TYPES := default_val;
	FUNCS := default_val;
	GLOBALS := default_val;
	TABLES := default_val;
	MEMS := default_val;
	EXPORTS := default_val|} }.

Definition _append_moduleinst (arg1 arg2 : (moduleinst)) :=
{|
	TYPES := arg1.(TYPES) @@ arg2.(TYPES);
	FUNCS := arg1.(FUNCS) @@ arg2.(FUNCS);
	GLOBALS := arg1.(GLOBALS) @@ arg2.(GLOBALS);
	TABLES := arg1.(TABLES) @@ arg2.(TABLES);
	MEMS := arg1.(MEMS) @@ arg2.(MEMS);
	EXPORTS := arg1.(EXPORTS) @@ arg2.(EXPORTS);
|}.

Global Instance Append_moduleinst : Append moduleinst := { _append arg1 arg2 := _append_moduleinst arg1 arg2 }.

#[export] Instance eta__moduleinst : Settable _ := settable! MKmoduleinst <TYPES;FUNCS;GLOBALS;TABLES;MEMS;EXPORTS>.

Definition moduleinst_eq_dec : forall (v1 v2 : moduleinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition moduleinst_eqb (v1 v2 : moduleinst) : bool :=
	is_left(moduleinst_eq_dec v1 v2).
Definition eqmoduleinstP : Equality.axiom (moduleinst_eqb) :=
	eq_dec_Equality_axiom (moduleinst) (moduleinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (moduleinst) (eqmoduleinstP).
Hint Resolve moduleinst_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:65.8-65.18 *)
Inductive wf_moduleinst : moduleinst -> Prop :=
	| moduleinst_case_ : forall (var_0 : (seq functype)) (var_1 : (seq funcaddr)) (var_2 : (seq globaladdr)) (var_3 : (seq tableaddr)) (var_4 : (seq memaddr)) (var_5 : (seq exportinst)), 
		List.Forall (fun (var_5 : exportinst) => (wf_exportinst var_5)) var_5 ->
		wf_moduleinst {| TYPES := var_0; FUNCS := var_1; GLOBALS := var_2; TABLES := var_3; MEMS := var_4; EXPORTS := var_5 |}.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:48.1-51.16 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:48.8-48.16 *)
Inductive wf_funcinst : funcinst -> Prop :=
	| funcinst_case_ : forall (var_0 : functype) (var_1 : moduleinst) (var_2 : func), 
		(wf_moduleinst var_1) ->
		(wf_func var_2) ->
		wf_funcinst {| funcinst_TYPE := var_0; funcinst_MODULE := var_1; CODE := var_2 |}.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:52.1-54.16 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:52.8-52.18 *)
Inductive wf_globalinst : globalinst -> Prop :=
	| globalinst_case_ : forall (var_0 : globaltype) (var_1 : val), 
		(wf_val var_1) ->
		wf_globalinst {| globalinst_TYPE := var_0; VALUE := var_1 |}.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:55.1-57.24 *)
Record tableinst := MKtableinst
{	tableinst_TYPE : tabletype
;	REFS : (seq (option funcaddr))
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:55.8-55.17 *)
Inductive wf_tableinst : tableinst -> Prop :=
	| tableinst_case_ : forall (var_0 : tabletype) (var_1 : (seq (option funcaddr))), 
		(wf_limits var_0) ->
		wf_tableinst {| tableinst_TYPE := var_0; REFS := var_1 |}.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:58.1-60.18 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:58.8-58.15 *)
Inductive wf_meminst : meminst -> Prop :=
	| meminst_case_ : forall (var_0 : memtype) (var_1 : (seq byte)), 
		(wf_limits var_0) ->
		List.Forall (fun (var_1 : byte) => (wf_byte var_1)) var_1 ->
		wf_meminst {| meminst_TYPE := var_0; BYTES := var_1 |}.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:83.1-87.20 *)
Record store := MKstore
{	store_FUNCS : (seq funcinst)
;	store_GLOBALS : (seq globalinst)
;	store_TABLES : (seq tableinst)
;	store_MEMS : (seq meminst)
}.

Global Instance Inhabited_store : Inhabited (store) := 
{default_val := {|
	store_FUNCS := default_val;
	store_GLOBALS := default_val;
	store_TABLES := default_val;
	store_MEMS := default_val|} }.

Definition _append_store (arg1 arg2 : (store)) :=
{|
	store_FUNCS := arg1.(store_FUNCS) @@ arg2.(store_FUNCS);
	store_GLOBALS := arg1.(store_GLOBALS) @@ arg2.(store_GLOBALS);
	store_TABLES := arg1.(store_TABLES) @@ arg2.(store_TABLES);
	store_MEMS := arg1.(store_MEMS) @@ arg2.(store_MEMS);
|}.

Global Instance Append_store : Append store := { _append arg1 arg2 := _append_store arg1 arg2 }.

#[export] Instance eta__store : Settable _ := settable! MKstore <store_FUNCS;store_GLOBALS;store_TABLES;store_MEMS>.

Definition store_eq_dec : forall (v1 v2 : store),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition store_eqb (v1 v2 : store) : bool :=
	is_left(store_eq_dec v1 v2).
Definition eqstoreP : Equality.axiom (store_eqb) :=
	eq_dec_Equality_axiom (store) (store_eq_dec).

HB.instance Definition _ := hasDecEq.Build (store) (eqstoreP).
Hint Resolve store_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:83.8-83.13 *)
Inductive wf_store : store -> Prop :=
	| store_case_ : forall (var_0 : (seq funcinst)) (var_1 : (seq globalinst)) (var_2 : (seq tableinst)) (var_3 : (seq meminst)), 
		List.Forall (fun (var_0 : funcinst) => (wf_funcinst var_0)) var_0 ->
		List.Forall (fun (var_1 : globalinst) => (wf_globalinst var_1)) var_1 ->
		List.Forall (fun (var_2 : tableinst) => (wf_tableinst var_2)) var_2 ->
		List.Forall (fun (var_3 : meminst) => (wf_meminst var_3)) var_3 ->
		wf_store {| store_FUNCS := var_0; store_GLOBALS := var_1; store_TABLES := var_2; store_MEMS := var_3 |}.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:89.1-91.24 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:89.8-89.13 *)
Inductive wf_frame : frame -> Prop :=
	| frame_case_ : forall (var_0 : (seq val)) (var_1 : moduleinst), 
		List.Forall (fun (var_0 : val) => (wf_val var_0)) var_0 ->
		(wf_moduleinst var_1) ->
		wf_frame {| LOCALS := var_0; frame_MODULE := var_1 |}.

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:93.1-93.47 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:93.8-93.13 *)
Inductive wf_state : state -> Prop :=
	| state_case_0 : forall (v_store : store) (v_frame : frame), 
		(wf_store v_store) ->
		(wf_frame v_frame) ->
		wf_state (mk_state v_store v_frame).

(* Mutual Recursion at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 *)
Inductive admininstr : Type :=
	| admininstr_NOP : admininstr
	| admininstr_UNREACHABLE : admininstr
	| admininstr_DROP : admininstr
	| admininstr_SELECT : admininstr
	| admininstr_BLOCK (v_blocktype : blocktype) (instr_lst : (seq instr)) : admininstr
	| admininstr_LOOP (v_blocktype : blocktype) (instr_lst : (seq instr)) : admininstr
	| admininstr_IFELSE (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst : (seq instr)) : admininstr
	| admininstr_BR (v_labelidx : labelidx) : admininstr
	| admininstr_BR_IF (v_labelidx : labelidx) : admininstr
	| admininstr_BR_TABLE (labelidx_lst : (seq labelidx)) (v_labelidx : labelidx) : admininstr
	| admininstr_CALL (v_funcidx : funcidx) : admininstr
	| admininstr_CALL_INDIRECT (v_typeidx : typeidx) : admininstr
	| admininstr_RETURN : admininstr
	| admininstr_CONST (v_valtype : valtype) (_ : val_) : admininstr
	| admininstr_UNOP (v_valtype : valtype) (_ : unop_) : admininstr
	| admininstr_BINOP (v_valtype : valtype) (_ : binop_) : admininstr
	| admininstr_TESTOP (v_valtype : valtype) (_ : testop_) : admininstr
	| admininstr_RELOP (v_valtype : valtype) (_ : relop_) : admininstr
	| admininstr_CVTOP (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : admininstr
	| admininstr_LOCAL_GET (v_localidx : localidx) : admininstr
	| admininstr_LOCAL_SET (v_localidx : localidx) : admininstr
	| admininstr_LOCAL_TEE (v_localidx : localidx) : admininstr
	| admininstr_GLOBAL_GET (v_globalidx : globalidx) : admininstr
	| admininstr_GLOBAL_SET (v_globalidx : globalidx) : admininstr
	| admininstr_LOAD (v_valtype : valtype) (_ : (option loadop_)) (v_memarg : memarg) : admininstr
	| admininstr_STORE (v_valtype : valtype) (sz_opt : (option sz)) (v_memarg : memarg) : admininstr
	| admininstr_MEMORY_SIZE : admininstr
	| admininstr_MEMORY_GROW : admininstr
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
		| SELECT => admininstr_SELECT
		| (BLOCK x0 x1) => (admininstr_BLOCK x0 x1)
		| (LOOP x0 x1) => (admininstr_LOOP x0 x1)
		| (IFELSE x0 x1 x2) => (admininstr_IFELSE x0 x1 x2)
		| (BR x0) => (admininstr_BR x0)
		| (BR_IF x0) => (admininstr_BR_IF x0)
		| (BR_TABLE x0 x1) => (admininstr_BR_TABLE x0 x1)
		| (CALL x0) => (admininstr_CALL x0)
		| (CALL_INDIRECT x0) => (admininstr_CALL_INDIRECT x0)
		| RETURN => admininstr_RETURN
		| (CONST x0 x1) => (admininstr_CONST x0 x1)
		| (UNOP x0 x1) => (admininstr_UNOP x0 x1)
		| (BINOP x0 x1) => (admininstr_BINOP x0 x1)
		| (TESTOP x0 x1) => (admininstr_TESTOP x0 x1)
		| (RELOP x0 x1) => (admininstr_RELOP x0 x1)
		| (CVTOP x0 x1 x2) => (admininstr_CVTOP x0 x1 x2)
		| (LOCAL_GET x0) => (admininstr_LOCAL_GET x0)
		| (LOCAL_SET x0) => (admininstr_LOCAL_SET x0)
		| (LOCAL_TEE x0) => (admininstr_LOCAL_TEE x0)
		| (GLOBAL_GET x0) => (admininstr_GLOBAL_GET x0)
		| (GLOBAL_SET x0) => (admininstr_GLOBAL_SET x0)
		| (LOAD x0 x1 x2) => (admininstr_LOAD x0 x1 x2)
		| (STORE x0 x1 x2) => (admininstr_STORE x0 x1 x2)
		| MEMORY_SIZE => admininstr_MEMORY_SIZE
		| MEMORY_GROW => admininstr_MEMORY_GROW
	end.

(* Auxiliary Definition at:  *)
Definition admininstr_val (var_0 : val) : admininstr :=
	match var_0 return admininstr with
		| (val_CONST x0 x1) => (admininstr_CONST x0 x1)
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 *)
Inductive wf_admininstr : admininstr -> Prop :=
	| admininstr_case_0 : wf_admininstr admininstr_NOP
	| admininstr_case_1 : wf_admininstr admininstr_UNREACHABLE
	| admininstr_case_2 : wf_admininstr admininstr_DROP
	| admininstr_case_3 : wf_admininstr admininstr_SELECT
	| admininstr_case_4 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)), 
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		wf_admininstr (admininstr_BLOCK v_blocktype instr_lst)
	| admininstr_case_5 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)), 
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		wf_admininstr (admininstr_LOOP v_blocktype instr_lst)
	| admininstr_case_6 : forall (v_blocktype : blocktype) (instr_lst : (seq instr)) (instr_lst_0 : (seq instr)), 
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
	| admininstr_case_11 : forall (v_typeidx : typeidx), 
		(wf_uN 32 v_typeidx) ->
		wf_admininstr (admininstr_CALL_INDIRECT v_typeidx)
	| admininstr_case_12 : wf_admininstr admininstr_RETURN
	| admininstr_case_13 : forall (v_valtype : valtype) (var_0 : val_), 
		(wf_val_ v_valtype var_0) ->
		wf_admininstr (admininstr_CONST v_valtype var_0)
	| admininstr_case_14 : forall (v_valtype : valtype) (var_0 : unop_), 
		(wf_unop_ v_valtype var_0) ->
		wf_admininstr (admininstr_UNOP v_valtype var_0)
	| admininstr_case_15 : forall (v_valtype : valtype) (var_0 : binop_), 
		(wf_binop_ v_valtype var_0) ->
		wf_admininstr (admininstr_BINOP v_valtype var_0)
	| admininstr_case_16 : forall (v_valtype : valtype) (var_0 : testop_), 
		(wf_testop_ v_valtype var_0) ->
		wf_admininstr (admininstr_TESTOP v_valtype var_0)
	| admininstr_case_17 : forall (v_valtype : valtype) (var_0 : relop_), 
		(wf_relop_ v_valtype var_0) ->
		wf_admininstr (admininstr_RELOP v_valtype var_0)
	| admininstr_case_18 : forall (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop), 
		(valtype_1 != valtype_2) ->
		wf_admininstr (admininstr_CVTOP valtype_1 valtype_2 v_cvtop)
	| admininstr_case_19 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_admininstr (admininstr_LOCAL_GET v_localidx)
	| admininstr_case_20 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_admininstr (admininstr_LOCAL_SET v_localidx)
	| admininstr_case_21 : forall (v_localidx : localidx), 
		(wf_uN 32 v_localidx) ->
		wf_admininstr (admininstr_LOCAL_TEE v_localidx)
	| admininstr_case_22 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_admininstr (admininstr_GLOBAL_GET v_globalidx)
	| admininstr_case_23 : forall (v_globalidx : globalidx), 
		(wf_uN 32 v_globalidx) ->
		wf_admininstr (admininstr_GLOBAL_SET v_globalidx)
	| admininstr_case_24 : forall (v_valtype : valtype) (var_0 : (option loadop_)) (v_memarg : memarg), 
		List.Forall (fun (var_0 : loadop_) => (wf_loadop_ v_valtype var_0)) (option_to_list var_0) ->
		(wf_memarg v_memarg) ->
		wf_admininstr (admininstr_LOAD v_valtype var_0 v_memarg)
	| admininstr_case_25 : forall (Inn_opt : (option Inn)) (valtype_opt : (option valtype)) (v_valtype : valtype) (sz_opt : (option sz)) (v_memarg : memarg), 
		List.Forall (fun (v_sz : sz) => (wf_sz v_sz)) (option_to_list sz_opt) ->
		(wf_memarg v_memarg) ->
		((Inn_opt == None) <-> (sz_opt == None)) ->
		((Inn_opt == None) <-> (valtype_opt == None)) ->
		List_Forall3 (fun (v_Inn : Inn) (v_sz : sz) (v_valtype : valtype) => ((v_valtype == (valtype_Inn v_Inn)) && ((v_sz :> nat) < (res_size (valtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list sz_opt) (option_to_list valtype_opt) ->
		wf_admininstr (admininstr_STORE v_valtype sz_opt v_memarg)
	| admininstr_case_26 : wf_admininstr admininstr_MEMORY_SIZE
	| admininstr_case_27 : wf_admininstr admininstr_MEMORY_GROW
	| admininstr_case_28 : forall (v_funcaddr : funcaddr), wf_admininstr (CALL_ADDR v_funcaddr)
	| admininstr_case_29 : forall (v_n : n) (instr_lst : (seq instr)) (admininstr_lst : (seq admininstr)), 
		List.Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		wf_admininstr (LABEL_ v_n instr_lst admininstr_lst)
	| admininstr_case_30 : forall (v_n : n) (v_frame : frame) (admininstr_lst : (seq admininstr)), 
		(wf_frame v_frame) ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		wf_admininstr (FRAME_ v_n v_frame admininstr_lst)
	| admininstr_case_31 : wf_admininstr admininstr_TRAP.

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:94.1-94.62 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:94.8-94.14 *)
Inductive wf_config : config -> Prop :=
	| config_case_0 : forall (v_state : state) (admininstr_lst : (seq admininstr)), 
		(wf_state v_state) ->
		List.Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
		wf_config (mk_config v_state admininstr_lst).

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:7.6-7.15 *)
Inductive fun_default_ : valtype -> val -> Prop :=
	| fun_default__case_0 : 
		(wf_val (val_CONST I32 (mk_val__0 Inn_I32 (mk_uN 0)))) ->
		fun_default_ I32 (val_CONST I32 (mk_val__0 Inn_I32 (mk_uN 0)))
	| fun_default__case_1 : 
		(wf_val (val_CONST I64 (mk_val__0 Inn_I64 (mk_uN 0)))) ->
		fun_default_ I64 (val_CONST I64 (mk_val__0 Inn_I64 (mk_uN 0)))
	| fun_default__case_2 : 
		(wf_val (val_CONST F32 (mk_val__1 Fnn_F32 (fzero 32)))) ->
		fun_default_ F32 (val_CONST F32 (mk_val__1 Fnn_F32 (fzero 32)))
	| fun_default__case_3 : 
		(wf_val (val_CONST F64 (mk_val__1 Fnn_F64 (fzero 64)))) ->
		fun_default_ F64 (val_CONST F64 (mk_val__1 Fnn_F64 (fzero 64))).

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:17.1-17.63 *)
Inductive fun_funcsxa : (seq externaddr) -> (seq funcaddr) -> Prop :=
	| fun_funcsxa_case_0 : fun_funcsxa [:: ] [:: ]
	| fun_funcsxa_case_1 : forall (fa : nat) (xv_lst : (seq externaddr)) (var_0 : (seq funcaddr)), 
		(fun_funcsxa xv_lst var_0) ->
		fun_funcsxa ([::(externaddr_FUNC fa)] ++ xv_lst) ([::fa] ++ var_0)
	| fun_funcsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (seq externaddr)) (var_0 : (seq funcaddr)), 
		(fun_funcsxa xv_lst var_0) ->
		fun_funcsxa ([::v_externaddr] ++ xv_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:18.1-18.65 *)
Inductive fun_globalsxa : (seq externaddr) -> (seq globaladdr) -> Prop :=
	| fun_globalsxa_case_0 : fun_globalsxa [:: ] [:: ]
	| fun_globalsxa_case_1 : forall (ga : nat) (xv_lst : (seq externaddr)) (var_0 : (seq globaladdr)), 
		(fun_globalsxa xv_lst var_0) ->
		fun_globalsxa ([::(externaddr_GLOBAL ga)] ++ xv_lst) ([::ga] ++ var_0)
	| fun_globalsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (seq externaddr)) (var_0 : (seq globaladdr)), 
		(fun_globalsxa xv_lst var_0) ->
		fun_globalsxa ([::v_externaddr] ++ xv_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:19.1-19.64 *)
Inductive fun_tablesxa : (seq externaddr) -> (seq tableaddr) -> Prop :=
	| fun_tablesxa_case_0 : fun_tablesxa [:: ] [:: ]
	| fun_tablesxa_case_1 : forall (ta : nat) (xv_lst : (seq externaddr)) (var_0 : (seq tableaddr)), 
		(fun_tablesxa xv_lst var_0) ->
		fun_tablesxa ([::(externaddr_TABLE ta)] ++ xv_lst) ([::ta] ++ var_0)
	| fun_tablesxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (seq externaddr)) (var_0 : (seq tableaddr)), 
		(fun_tablesxa xv_lst var_0) ->
		fun_tablesxa ([::v_externaddr] ++ xv_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:20.1-20.62 *)
Inductive fun_memsxa : (seq externaddr) -> (seq memaddr) -> Prop :=
	| fun_memsxa_case_0 : fun_memsxa [:: ] [:: ]
	| fun_memsxa_case_1 : forall (ma : nat) (xv_lst : (seq externaddr)) (var_0 : (seq memaddr)), 
		(fun_memsxa xv_lst var_0) ->
		fun_memsxa ([::(externaddr_MEM ma)] ++ xv_lst) ([::ma] ++ var_0)
	| fun_memsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (seq externaddr)) (var_0 : (seq memaddr)), 
		(fun_memsxa xv_lst var_0) ->
		fun_memsxa ([::v_externaddr] ++ xv_lst) var_0.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:46.1-46.57 *)
Definition fun_store (v_state : state) : store :=
	match v_state return store with
		| (mk_state s f) => s
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:47.1-47.57 *)
Definition fun_frame (v_state : state) : frame :=
	match v_state return frame with
		| (mk_state s f) => f
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:53.1-53.64 *)
Definition fun_funcaddr (v_state : state) : (seq funcaddr) :=
	match v_state return (seq funcaddr) with
		| (mk_state s f) => (FUNCS (frame_MODULE f))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:56.1-56.57 *)
Definition fun_funcinst (v_state : state) : (seq funcinst) :=
	match v_state return (seq funcinst) with
		| (mk_state s f) => (store_FUNCS s)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:57.1-57.59 *)
Definition fun_globalinst (v_state : state) : (seq globalinst) :=
	match v_state return (seq globalinst) with
		| (mk_state s f) => (store_GLOBALS s)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:58.1-58.58 *)
Definition fun_tableinst (v_state : state) : (seq tableinst) :=
	match v_state return (seq tableinst) with
		| (mk_state s f) => (store_TABLES s)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:59.1-59.56 *)
Definition fun_meminst (v_state : state) : (seq meminst) :=
	match v_state return (seq meminst) with
		| (mk_state s f) => (store_MEMS s)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:60.1-60.58 *)
Definition fun_moduleinst (v_state : state) : moduleinst :=
	match v_state return moduleinst with
		| (mk_state s f) => (frame_MODULE f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:68.1-68.66 *)
Definition fun_type (v_state : state) (v_typeidx : typeidx) : functype :=
	match v_state, v_typeidx return functype with
		| (mk_state s f), x => ((TYPES (frame_MODULE f))[| (x :> nat) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:69.1-69.66 *)
Definition fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
	match v_state, v_funcidx return funcinst with
		| (mk_state s f), x => ((store_FUNCS s)[| ((FUNCS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:70.1-70.68 *)
Definition fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
	match v_state, v_globalidx return globalinst with
		| (mk_state s f), x => ((store_GLOBALS s)[| ((GLOBALS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:71.1-71.67 *)
Definition fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
	match v_state, v_tableidx return tableinst with
		| (mk_state s f), x => ((store_TABLES s)[| ((TABLES (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:72.1-72.65 *)
Definition fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
	match v_state, v_memidx return meminst with
		| (mk_state s f), x => ((store_MEMS s)[| ((MEMS (frame_MODULE f))[| (x :> nat) |]) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:73.1-73.67 *)
Definition fun_local (v_state : state) (v_localidx : localidx) : val :=
	match v_state, v_localidx return val with
		| (mk_state s f), x => ((LOCALS f)[| (x :> nat) |])
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:85.1-85.89 *)
Definition with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
	match v_state, v_localidx, v_val return state with
		| (mk_state s f), x, v => (mk_state s (f <| LOCALS := (list_update_func (LOCALS f) (x :> nat) (fun (_ : val) => v)) |>))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:86.1-86.96 *)
Definition with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
	match v_state, v_globalidx, v_val return state with
		| (mk_state s f), x, v => (mk_state (s <| store_GLOBALS := (list_update_func (store_GLOBALS s) ((GLOBALS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : globalinst) => (var_1 <| VALUE := v |>))) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:87.1-87.97 *)
Definition with_table (v_state : state) (v_tableidx : tableidx) (res_nat : nat) (v_funcaddr : funcaddr) : state :=
	match v_state, v_tableidx, res_nat, v_funcaddr return state with
		| (mk_state s f), x, i, a => (mk_state (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : tableinst) => (var_1 <| REFS := (list_update_func (REFS var_1) i (fun (_ : (option funcaddr)) => (Some a))) |>))) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:88.1-88.89 *)
Definition with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
	match v_state, v_tableidx, v_tableinst return state with
		| (mk_state s f), x, ti => (mk_state (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f))[| (x :> nat) |]) (fun (_ : tableinst) => ti)) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:89.1-89.100 *)
Definition with_mem (v_state : state) (v_memidx : memidx) (res_nat : nat) (nat_0 : nat) (var_0 : (seq byte)) : state :=
	match v_state, v_memidx, res_nat, nat_0, var_0 return state with
		| (mk_state s f), x, i, j, b_lst => (mk_state (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f))[| (x :> nat) |]) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (BYTES var_1) i j b_lst) |>))) |>) f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:90.1-90.87 *)
Definition with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
	match v_state, v_memidx, v_meminst return state with
		| (mk_state s f), x, mi => (mk_state (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f))[| (x :> nat) |]) (fun (_ : meminst) => mi)) |>) f)
	end.

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16 *)
Inductive fun_growtable : tableinst -> nat -> (option tableinst) -> Prop :=
	| fun_growtable_case_0 : forall (ti : tableinst) (v_n : nat) (ti' : tableinst) (i : uN) (j_opt : (option u32)) (a_lst : (seq addr)) (i' : nat), 
		(ti == {| tableinst_TYPE := (mk_limits i j_opt); REFS := (seq.map (fun (a : addr) => (Some a)) a_lst) |}) ->
		(i' == ((|a_lst|) + v_n)) ->
		(ti' == {| tableinst_TYPE := (mk_limits (mk_uN i') j_opt); REFS := ((seq.map (fun (a : addr) => (Some a)) a_lst) ++ (List.repeat None v_n)) |}) ->
		List.Forall (fun (j : u32) => (i' <= (j :> nat))) (option_to_list j_opt) ->
		fun_growtable ti v_n (Some ti')
	| fun_growtable_case_1 : forall (x0 : tableinst) (x1 : nat), 
		True (* Unsupported premise: otherwise *) ->
		fun_growtable x0 x1 None.

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17 *)
Inductive fun_growmemory : meminst -> nat -> (option meminst) -> Prop :=
	| fun_growmemory_case_0 : forall (mi : meminst) (v_n : nat) (mi' : meminst) (i : uN) (j_opt : (option u32)) (b_lst : (seq byte)) (i' : nat), 
		(mi == {| meminst_TYPE := (mk_limits i j_opt); BYTES := b_lst |}) ->
		(i' == ((((|b_lst|) : nat) / ((64 * (Ki )) : nat)) + (v_n : nat))) ->
		(mi' == {| meminst_TYPE := (mk_limits (mk_uN (i' : nat)) j_opt); BYTES := (b_lst ++ (List.repeat (mk_byte 0) (v_n * (64 * (Ki ))))) |}) ->
		List.Forall (fun (j : u32) => (i' <= ((j :> nat) : nat))) (option_to_list j_opt) ->
		fun_growmemory mi v_n (Some mi')
	| fun_growmemory_case_1 : forall (x0 : meminst) (x1 : nat), 
		True (* Unsupported premise: otherwise *) ->
		fun_growmemory x0 x1 None.

(* Record Creation Definition at: ../specification/wasm-1.0/6-typing.spectec:5.1-8.62 *)
Record context := MKcontext
{	context_TYPES : (seq functype)
;	context_FUNCS : (seq functype)
;	context_GLOBALS : (seq globaltype)
;	context_TABLES : (seq tabletype)
;	context_MEMS : (seq memtype)
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
	context_LOCALS := arg1.(context_LOCALS) @@ arg2.(context_LOCALS);
	LABELS := arg1.(LABELS) @@ arg2.(LABELS);
	context_RETURN := arg1.(context_RETURN) @@ arg2.(context_RETURN);
|}.

Global Instance Append_context : Append context := { _append arg1 arg2 := _append_context arg1 arg2 }.

#[export] Instance eta__context : Settable _ := settable! MKcontext <context_TYPES;context_FUNCS;context_GLOBALS;context_TABLES;context_MEMS;context_LOCALS;LABELS;context_RETURN>.

Definition context_eq_dec : forall (v1 v2 : context),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition context_eqb (v1 v2 : context) : bool :=
	is_left(context_eq_dec v1 v2).
Definition eqcontextP : Equality.axiom (context_eqb) :=
	eq_dec_Equality_axiom (context) (context_eq_dec).

HB.instance Definition _ := hasDecEq.Build (context) (eqcontextP).
Hint Resolve context_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:5.8-5.15 *)
Inductive wf_context : context -> Prop :=
	| context_case_ : forall (var_0 : (seq functype)) (var_1 : (seq functype)) (var_2 : (seq globaltype)) (var_3 : (seq tabletype)) (var_4 : (seq memtype)) (var_5 : (seq valtype)) (var_6 : (seq resulttype)) (var_7 : (option resulttype)), 
		List.Forall (fun (var_3 : tabletype) => (wf_limits var_3)) var_3 ->
		List.Forall (fun (var_4 : memtype) => (wf_limits var_4)) var_4 ->
		wf_context {| context_TYPES := var_0; context_FUNCS := var_1; context_GLOBALS := var_2; context_TABLES := var_3; context_MEMS := var_4; context_LOCALS := var_5; LABELS := var_6; context_RETURN := var_7 |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:18.1-18.66 *)
Inductive Limits_ok : limits -> nat -> Prop :=
	| mk_Limits_ok : forall (v_n : n) (m_opt : (option m)) (k : nat), 
		(v_n <= k) ->
		List.Forall (fun (v_m : nat) => ((v_n <= v_m) && (v_m <= k))) (option_to_list m_opt) ->
		Limits_ok (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) k.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:19.1-19.64 *)
Inductive Functype_ok : functype -> Prop :=
	| mk_Functype_ok : forall (t_1_lst : (seq valtype)) (t_2_opt : (option valtype)), Functype_ok (mk_functype t_1_lst (option_to_list t_2_opt)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:20.1-20.66 *)
Inductive Globaltype_ok : globaltype -> Prop :=
	| mk_Globaltype_ok : forall (t : valtype), Globaltype_ok (mk_globaltype (Some MUT_MUT) t).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:21.1-21.65 *)
Inductive Tabletype_ok : tabletype -> Prop :=
	| mk_Tabletype_ok : forall (v_limits : limits), 
		(Limits_ok v_limits ((((2 ^ 32) : nat) - (1 : nat)) : nat)) ->
		Tabletype_ok v_limits.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:22.1-22.63 *)
Inductive Memtype_ok : memtype -> Prop :=
	| mk_Memtype_ok : forall (v_limits : limits), 
		(Limits_ok v_limits (2 ^ 16)) ->
		Memtype_ok v_limits.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:23.1-23.66 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:70.1-70.75 *)
Inductive Limits_sub : limits -> limits -> Prop :=
	| mk_Limits_sub : forall (n_11 : n) (n_12 : n) (n_21 : n) (n_22 : n), 
		(n_11 >= n_21) ->
		(n_12 <= n_22) ->
		Limits_sub (mk_limits (mk_uN n_11) (Some (mk_uN n_12))) (mk_limits (mk_uN n_21) (Some (mk_uN n_22))).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:71.1-71.73 *)
Inductive Functype_sub : functype -> functype -> Prop :=
	| mk_Functype_sub : forall (ft : functype), Functype_sub ft ft.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:72.1-72.75 *)
Inductive Globaltype_sub : globaltype -> globaltype -> Prop :=
	| mk_Globaltype_sub : forall (gt : globaltype), Globaltype_sub gt gt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:73.1-73.74 *)
Inductive Tabletype_sub : tabletype -> tabletype -> Prop :=
	| mk_Tabletype_sub : forall (lim_1 : limits) (lim_2 : limits), 
		(Limits_sub lim_1 lim_2) ->
		Tabletype_sub lim_1 lim_2.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:74.1-74.72 *)
Inductive Memtype_sub : memtype -> memtype -> Prop :=
	| mk_Memtype_sub : forall (lim_1 : limits) (lim_2 : limits), 
		(Limits_sub lim_1 lim_2) ->
		Memtype_sub lim_1 lim_2.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:75.1-75.75 *)
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

(* Mutual Recursion at: ../specification/wasm-1.0/6-typing.spectec:120.1-121.65 *)
Inductive Instr_ok : context -> instr -> functype -> Prop :=
	| nop : forall (C : context), Instr_ok C NOP (mk_functype [:: ] [:: ])
	| unreachable : forall (C : context) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), Instr_ok C UNREACHABLE (mk_functype t_1_lst t_2_lst)
	| drop : forall (C : context) (t : valtype), Instr_ok C DROP (mk_functype [::t] [:: ])
	| select : forall (C : context) (t : valtype), Instr_ok C SELECT (mk_functype [::t; t; I32] [::t])
	| block : forall (C : context) (t_opt : (option valtype)) (instr_lst : (seq instr)), 
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := [:: ]; LABELS := [::t_opt]; context_RETURN := None |} @@ C) instr_lst (mk_functype [:: ] (option_to_list t_opt))) ->
		Instr_ok C (BLOCK t_opt instr_lst) (mk_functype [:: ] (option_to_list t_opt))
	| loop : forall (C : context) (t_opt : (option valtype)) (instr_lst : (seq instr)), 
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := [:: ]; LABELS := [::None]; context_RETURN := None |} @@ C) instr_lst (mk_functype [:: ] [:: ])) ->
		Instr_ok C (LOOP t_opt instr_lst) (mk_functype [:: ] (option_to_list t_opt))
	| res_if : forall (C : context) (t_opt : (option valtype)) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)), 
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := [:: ]; LABELS := [::t_opt]; context_RETURN := None |} @@ C) instr_1_lst (mk_functype [:: ] (option_to_list t_opt))) ->
		(Instrs_ok ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := [:: ]; LABELS := [::t_opt]; context_RETURN := None |} @@ C) instr_2_lst (mk_functype [:: ] (option_to_list t_opt))) ->
		Instr_ok C (IFELSE t_opt instr_1_lst instr_2_lst) (mk_functype [::I32] (option_to_list t_opt))
	| br : forall (C : context) (l : labelidx) (t_1_lst : (seq valtype)) (t_opt : (option valtype)) (t_2_lst : (seq valtype)), 
		((l :> nat) < (|(LABELS C)|)) ->
		(((LABELS C)[| (l :> nat) |]) == t_opt) ->
		Instr_ok C (BR l) (mk_functype (t_1_lst ++ (option_to_list t_opt)) t_2_lst)
	| br_if : forall (C : context) (l : labelidx) (t_opt : (option valtype)), 
		((l :> nat) < (|(LABELS C)|)) ->
		(((LABELS C)[| (l :> nat) |]) == t_opt) ->
		Instr_ok C (BR_IF l) (mk_functype ((option_to_list t_opt) ++ [::I32]) (option_to_list t_opt))
	| br_table : forall (C : context) (l_lst : (seq labelidx)) (l' : labelidx) (t_1_lst : (seq valtype)) (t_opt : (option valtype)) (t_2_lst : (seq valtype)), 
		((l' :> nat) < (|(LABELS C)|)) ->
		(t_opt == ((LABELS C)[| (l' :> nat) |])) ->
		List.Forall (fun (l : labelidx) => ((l :> nat) < (|(LABELS C)|))) l_lst ->
		List.Forall (fun (l : labelidx) => (t_opt == ((LABELS C)[| (l :> nat) |]))) l_lst ->
		Instr_ok C (BR_TABLE l_lst l') (mk_functype (t_1_lst ++ ((option_to_list t_opt) ++ [::I32])) t_2_lst)
	| call : forall (C : context) (x : idx) (t_1_lst : (seq valtype)) (t_2_opt : (option valtype)), 
		((x :> nat) < (|(context_FUNCS C)|)) ->
		(((context_FUNCS C)[| (x :> nat) |]) == (mk_functype t_1_lst (option_to_list t_2_opt))) ->
		Instr_ok C (CALL x) (mk_functype t_1_lst (option_to_list t_2_opt))
	| call_indirect : forall (C : context) (x : idx) (t_1_lst : (seq valtype)) (t_2_opt : (option valtype)), 
		((x :> nat) < (|(context_TYPES C)|)) ->
		(((context_TYPES C)[| (x :> nat) |]) == (mk_functype t_1_lst (option_to_list t_2_opt))) ->
		Instr_ok C (CALL_INDIRECT x) (mk_functype (t_1_lst ++ [::I32]) (option_to_list t_2_opt))
	| res_return : forall (C : context) (t_1_lst : (seq valtype)) (t_opt : (option valtype)) (t_2_lst : (seq valtype)), 
		((context_RETURN C) == (Some t_opt)) ->
		Instr_ok C RETURN (mk_functype (t_1_lst ++ (option_to_list t_opt)) t_2_lst)
	| const : forall (C : context) (t : valtype) (c_t : val_), 
		(wf_instr (CONST t c_t)) ->
		Instr_ok C (CONST t c_t) (mk_functype [:: ] [::t])
	| unop : forall (C : context) (t : valtype) (unop_t : unop_), 
		(wf_instr (UNOP t unop_t)) ->
		Instr_ok C (UNOP t unop_t) (mk_functype [::t] [::t])
	| binop : forall (C : context) (t : valtype) (binop_t : binop_), 
		(wf_instr (BINOP t binop_t)) ->
		Instr_ok C (BINOP t binop_t) (mk_functype [::t; t] [::t])
	| testop : forall (C : context) (t : valtype) (testop_t : testop_), 
		(wf_instr (TESTOP t testop_t)) ->
		Instr_ok C (TESTOP t testop_t) (mk_functype [::t] [::I32])
	| relop : forall (C : context) (t : valtype) (relop_t : relop_), 
		(wf_instr (RELOP t relop_t)) ->
		Instr_ok C (RELOP t relop_t) (mk_functype [::t; t] [::I32])
	| cvtop_reinterpret : forall (C : context) (nt_1 : valtype) (nt_2 : valtype), 
		((res_size nt_1) == (res_size nt_2)) ->
		Instr_ok C (CVTOP nt_1 nt_2 REINTERPRET) (mk_functype [::nt_2] [::nt_1])
	| cvtop_convert : forall (C : context) (nt_1 : valtype) (nt_2 : valtype) (v_cvtop : cvtop), Instr_ok C (CVTOP nt_1 nt_2 v_cvtop) (mk_functype [::nt_2] [::nt_1])
	| local_get : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|)) ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		Instr_ok C (LOCAL_GET x) (mk_functype [:: ] [::t])
	| local_set : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|)) ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		Instr_ok C (LOCAL_SET x) (mk_functype [::t] [:: ])
	| local_tee : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_LOCALS C)|)) ->
		(((context_LOCALS C)[| (x :> nat) |]) == t) ->
		Instr_ok C (LOCAL_TEE x) (mk_functype [::t] [::t])
	| global_get : forall (C : context) (x : idx) (t : valtype) (v_mut : mut), 
		((x :> nat) < (|(context_GLOBALS C)|)) ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype v_mut t)) ->
		Instr_ok C (GLOBAL_GET x) (mk_functype [:: ] [::t])
	| global_set : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_GLOBALS C)|)) ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype (Some MUT_MUT) t)) ->
		Instr_ok C (GLOBAL_SET x) (mk_functype [::t] [:: ])
	| memory_size : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		Instr_ok C MEMORY_SIZE (mk_functype [:: ] [::I32])
	| memory_grow : forall (C : context) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		Instr_ok C MEMORY_GROW (mk_functype [::I32] [::I32])
	| load_val : forall (C : context) (t : valtype) (v_memarg : memarg) (mt : memtype), 
		(wf_instr (LOAD t None v_memarg)) ->
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= (((res_size t) : nat) / (8 : nat))) ->
		Instr_ok C (LOAD t None v_memarg) (mk_functype [::I32] [::t])
	| load_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (v_memarg : memarg) (mt : memtype), 
		(wf_instr (LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg)) ->
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= ((v_M : nat) / (8 : nat))) ->
		Instr_ok C (LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg) (mk_functype [::I32] [::(valtype_Inn v_Inn)])
	| store_val : forall (C : context) (t : valtype) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= (((res_size t) : nat) / (8 : nat))) ->
		Instr_ok C (STORE t None v_memarg) (mk_functype [::I32; t] [:: ])
	| store_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (mt : memtype), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == mt) ->
		(((2 ^ ((ALIGN v_memarg) :> nat)) : nat) <= ((v_M : nat) / (8 : nat))) ->
		Instr_ok C (STORE (valtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg) (mk_functype [::I32; (valtype_Inn v_Inn)] [:: ])

with

Instrs_ok : context -> (seq instr) -> functype -> Prop :=
	| empty : forall (C : context), Instrs_ok C [:: ] (mk_functype [:: ] [:: ])
	| res_seq : forall (C : context) (instr_1 : instr) (instr_2_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_3_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instr_ok C instr_1 (mk_functype t_1_lst t_2_lst)) ->
		(Instrs_ok C instr_2_lst (mk_functype t_2_lst t_3_lst)) ->
		Instrs_ok C ([::instr_1] ++ instr_2_lst) (mk_functype t_1_lst t_3_lst)
	| Instrs_ok__frame : forall (C : context) (instr_lst : (seq instr)) (t_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Instrs_ok C instr_lst (mk_functype t_1_lst t_2_lst)) ->
		Instrs_ok C instr_lst (mk_functype (t_lst ++ t_1_lst) (t_lst ++ t_2_lst)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:122.1-122.69 *)
Inductive Expr_ok : context -> expr -> resulttype -> Prop :=
	| mk_Expr_ok : forall (C : context) (instr_lst : (seq instr)) (t_opt : (option valtype)), 
		(Instrs_ok C instr_lst (mk_functype [:: ] (option_to_list t_opt))) ->
		Expr_ok C instr_lst t_opt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:315.1-315.79 *)
Inductive Instr_const : context -> instr -> Prop :=
	| Instr_const__const : forall (C : context) (t : valtype) (c : val_), 
		(wf_instr (CONST t c)) ->
		Instr_const C (CONST t c)
	| Instr_const__global_get : forall (C : context) (x : idx) (t : valtype), 
		((x :> nat) < (|(context_GLOBALS C)|)) ->
		(((context_GLOBALS C)[| (x :> nat) |]) == (mk_globaltype None t)) ->
		Instr_const C (GLOBAL_GET x).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:316.1-316.78 *)
Inductive Expr_const : context -> expr -> Prop :=
	| mk_Expr_const : forall (C : context) (instr_lst : (seq instr)), 
		List.Forall (fun (v_instr : instr) => (Instr_const C v_instr)) instr_lst ->
		Expr_const C instr_lst.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:317.1-317.79 *)
Inductive Expr_ok_const : context -> expr -> (option valtype) -> Prop :=
	| mk_Expr_ok_const : forall (C : context) (v_expr : expr) (t_opt : (option valtype)), 
		(Expr_ok C v_expr t_opt) ->
		(Expr_const C v_expr) ->
		Expr_ok_const C v_expr t_opt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:341.1-341.73 *)
Inductive Type_ok : type -> functype -> Prop :=
	| mk_Type_ok : forall (ft : functype), 
		(Functype_ok ft) ->
		Type_ok (TYPE ft) ft.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:342.1-342.73 *)
Inductive Func_ok : context -> func -> functype -> Prop :=
	| mk_Func_ok : forall (C : context) (x : idx) (t_lst : (seq valtype)) (v_expr : expr) (t_1_lst : (seq valtype)) (t_2_opt : (option valtype)), 
		((x :> nat) < (|(context_TYPES C)|)) ->
		(((context_TYPES C)[| (x :> nat) |]) == (mk_functype t_1_lst (option_to_list t_2_opt))) ->
		(Expr_ok (C @@ {| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := (t_1_lst ++ t_lst); LABELS := [::t_2_opt]; context_RETURN := (Some t_2_opt) |}) v_expr t_2_opt) ->
		Func_ok C (func_FUNC x (seq.map (fun (t : valtype) => (LOCAL t)) t_lst) v_expr) (mk_functype t_1_lst (option_to_list t_2_opt)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:343.1-343.75 *)
Inductive Global_ok : context -> global -> globaltype -> Prop :=
	| mk_Global_ok : forall (C : context) (gt : globaltype) (v_expr : expr) (v_mut : mut) (t : valtype), 
		(Globaltype_ok gt) ->
		(gt == (mk_globaltype v_mut t)) ->
		(Expr_ok_const C v_expr (Some t)) ->
		Global_ok C (global_GLOBAL gt v_expr) gt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:344.1-344.74 *)
Inductive Table_ok : context -> table -> tabletype -> Prop :=
	| mk_Table_ok : forall (C : context) (res_tt : tabletype), 
		(Tabletype_ok res_tt) ->
		Table_ok C (table_TABLE res_tt) res_tt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:345.1-345.72 *)
Inductive Mem_ok : context -> mem -> memtype -> Prop :=
	| mk_Mem_ok : forall (C : context) (mt : memtype), 
		(Memtype_ok mt) ->
		Mem_ok C (MEMORY mt) mt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:346.1-346.73 *)
Inductive Elem_ok : context -> elem -> Prop :=
	| mk_Elem_ok : forall (C : context) (v_expr : expr) (x_lst : (seq idx)) (lim : limits) (ft_lst : (seq functype)), 
		(0 < (|(context_TABLES C)|)) ->
		(((context_TABLES C)[| 0 |]) == lim) ->
		(Expr_ok_const C v_expr (Some I32)) ->
		((|ft_lst|) == (|x_lst|)) ->
		List.Forall (fun (x : idx) => ((x :> nat) < (|(context_FUNCS C)|))) x_lst ->
		List.Forall2 (fun (ft : functype) (x : idx) => (((context_FUNCS C)[| (x :> nat) |]) == ft)) ft_lst x_lst ->
		Elem_ok C (ELEM v_expr x_lst).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:347.1-347.73 *)
Inductive Data_ok : context -> data -> Prop :=
	| mk_Data_ok : forall (C : context) (v_expr : expr) (b_lst : (seq byte)) (lim : limits), 
		(0 < (|(context_MEMS C)|)) ->
		(((context_MEMS C)[| 0 |]) == lim) ->
		(Expr_ok_const C v_expr (Some I32)) ->
		Data_ok C (DATA v_expr b_lst).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:348.1-348.74 *)
Inductive Start_ok : context -> start -> Prop :=
	| mk_Start_ok : forall (C : context) (x : idx), 
		((x :> nat) < (|(context_FUNCS C)|)) ->
		(((context_FUNCS C)[| (x :> nat) |]) == (mk_functype [:: ] [:: ])) ->
		Start_ok C (START x).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:396.1-396.80 *)
Inductive Import_ok : context -> import -> externtype -> Prop :=
	| mk_Import_ok : forall (C : context) (name_1 : name) (name_2 : name) (xt : externtype), 
		(Externtype_ok xt) ->
		Import_ok C (IMPORT name_1 name_2 xt) xt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:398.1-398.83 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:397.1-397.80 *)
Inductive Export_ok : context -> export -> externtype -> Prop :=
	| mk_Export_ok : forall (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype), 
		(Externidx_ok C v_externidx xt) ->
		Export_ok C (EXPORT v_name v_externidx) xt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:428.1-428.62 *)
Inductive Module_ok : module -> Prop :=
	| mk_Module_ok : forall (type_lst : (seq type)) (import_lst : (seq import)) (func_lst : (seq func)) (global_lst : (seq global)) (table_lst : (seq table)) (mem_lst : (seq mem)) (elem_lst : (seq elem)) (data_lst : (seq data)) (start_opt : (option start)) (export_lst : (seq export)) (ft'_lst : (seq functype)) (ixt_lst : (seq externtype)) (C' : context) (gt_lst : (seq globaltype)) (C : context) (ft_lst : (seq functype)) (tt_lst : (seq tabletype)) (mt_lst : (seq memtype)) (xt_lst : (seq externtype)) (ift_lst : (seq functype)) (igt_lst : (seq globaltype)) (itt_lst : (seq tabletype)) (imt_lst : (seq memtype)) (var_3 : (seq memtype)) (var_2 : (seq tabletype)) (var_1 : (seq globaltype)) (var_0 : (seq functype)), 
		(fun_memsxt ixt_lst var_3) ->
		(fun_tablesxt ixt_lst var_2) ->
		(fun_globalsxt ixt_lst var_1) ->
		(fun_funcsxt ixt_lst var_0) ->
		((|ft'_lst|) == (|type_lst|)) ->
		List.Forall2 (fun (ft' : functype) (v_type : type) => (Type_ok v_type ft')) ft'_lst type_lst ->
		((|import_lst|) == (|ixt_lst|)) ->
		List.Forall2 (fun (v_import : import) (ixt : externtype) => (Import_ok {| context_TYPES := ft'_lst; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |} v_import ixt)) import_lst ixt_lst ->
		((|global_lst|) == (|gt_lst|)) ->
		List.Forall2 (fun (v_global : global) (gt : globaltype) => (Global_ok C' v_global gt)) global_lst gt_lst ->
		((|ft_lst|) == (|func_lst|)) ->
		List.Forall2 (fun (ft : functype) (v_func : func) => (Func_ok C v_func ft)) ft_lst func_lst ->
		((|table_lst|) == (|tt_lst|)) ->
		List.Forall2 (fun (v_table : table) (res_tt : tabletype) => (Table_ok C v_table res_tt)) table_lst tt_lst ->
		((|mem_lst|) == (|mt_lst|)) ->
		List.Forall2 (fun (v_mem : mem) (mt : memtype) => (Mem_ok C v_mem mt)) mem_lst mt_lst ->
		List.Forall (fun (v_elem : elem) => (Elem_ok C v_elem)) elem_lst ->
		List.Forall (fun (v_data : data) => (Data_ok C v_data)) data_lst ->
		List.Forall (fun (v_start : start) => (Start_ok C v_start)) (option_to_list start_opt) ->
		((|export_lst|) == (|xt_lst|)) ->
		List.Forall2 (fun (v_export : export) (xt : externtype) => (Export_ok C v_export xt)) export_lst xt_lst ->
		((|tt_lst|) <= 1) ->
		((|mt_lst|) <= 1) ->
		(C == {| context_TYPES := ft'_lst; context_FUNCS := (ift_lst ++ ft_lst); context_GLOBALS := (igt_lst ++ gt_lst); context_TABLES := (itt_lst ++ tt_lst); context_MEMS := (imt_lst ++ mt_lst); context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(C' == {| context_TYPES := ft'_lst; context_FUNCS := (ift_lst ++ ft_lst); context_GLOBALS := igt_lst; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}) ->
		(ift_lst == var_0) ->
		(igt_lst == var_1) ->
		(itt_lst == var_2) ->
		(imt_lst == var_3) ->
		Module_ok (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst).

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.77 *)
Inductive Step_pure : (seq admininstr) -> (seq admininstr) -> Prop :=
	| Step_pure__unreachable : Step_pure [::admininstr_UNREACHABLE] [::admininstr_TRAP]
	| Step_pure__nop : Step_pure [::admininstr_NOP] [:: ]
	| Step_pure__drop : forall (v_val : val), Step_pure [::(admininstr_val v_val); admininstr_DROP] [:: ]
	| select_true : forall (val_1 : val) (val_2 : val) (c : val_), 
		(wf_admininstr (admininstr_CONST I32 c)) ->
		((proj_val__0 c) != None) ->
		(((!((proj_val__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_val val_1); (admininstr_val val_2); (admininstr_CONST I32 c); admininstr_SELECT] [::(admininstr_val val_1)]
	| select_false : forall (val_1 : val) (val_2 : val) (c : val_), 
		(wf_admininstr (admininstr_CONST I32 c)) ->
		((proj_val__0 c) != None) ->
		(((!((proj_val__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_val val_1); (admininstr_val val_2); (admininstr_CONST I32 c); admininstr_SELECT] [::(admininstr_val val_2)]
	| if_true : forall (c : val_) (t_opt : (option valtype)) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)), 
		(wf_admininstr (admininstr_CONST I32 c)) ->
		((proj_val__0 c) != None) ->
		(((!((proj_val__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_IFELSE t_opt instr_1_lst instr_2_lst)] [::(admininstr_BLOCK t_opt instr_1_lst)]
	| if_false : forall (c : val_) (t_opt : (option valtype)) (instr_1_lst : (seq instr)) (instr_2_lst : (seq instr)), 
		(wf_admininstr (admininstr_CONST I32 c)) ->
		((proj_val__0 c) != None) ->
		(((!((proj_val__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_IFELSE t_opt instr_1_lst instr_2_lst)] [::(admininstr_BLOCK t_opt instr_2_lst)]
	| label_vals : forall (v_n : n) (instr_lst : (seq instr)) (val_lst : (seq val)), Step_pure [::(LABEL_ v_n instr_lst (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
	| br_zero : forall (v_n : n) (instr'_lst : (seq instr)) (val'_lst : (seq val)) (val_lst : (seq val)) (instr_lst : (seq instr)), 
		(v_n == (|val_lst|)) ->
		Step_pure [::(LABEL_ v_n instr'_lst ((((seq.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)) ++ [::(admininstr_BR (mk_uN 0))]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (seq.map (fun (instr' : instr) => (admininstr_instr instr')) instr'_lst))
	| br_succ : forall (v_n : n) (instr'_lst : (seq instr)) (val_lst : (seq val)) (l : labelidx) (instr_lst : (seq instr)), Step_pure [::(LABEL_ v_n instr'_lst (((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_BR (mk_uN ((l :> nat) + 1)))]) ++ (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))] ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(admininstr_BR l)])
	| br_if_true : forall (c : val_) (l : labelidx), 
		(wf_admininstr (admininstr_CONST I32 c)) ->
		((proj_val__0 c) != None) ->
		(((!((proj_val__0 c))) :> nat) != 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_BR_IF l)] [::(admininstr_BR l)]
	| br_if_false : forall (c : val_) (l : labelidx), 
		(wf_admininstr (admininstr_CONST I32 c)) ->
		((proj_val__0 c) != None) ->
		(((!((proj_val__0 c))) :> nat) == 0) ->
		Step_pure [::(admininstr_CONST I32 c); (admininstr_BR_IF l)] [:: ]
	| br_table_lt : forall (i : val_) (l_lst : (seq labelidx)) (l' : labelidx), 
		(((!((proj_val__0 i))) :> nat) < (|l_lst|)) ->
		((proj_val__0 i) != None) ->
		(wf_admininstr (admininstr_CONST I32 i)) ->
		(wf_admininstr (admininstr_BR (l_lst[| ((!((proj_val__0 i))) :> nat) |]))) ->
		Step_pure [::(admininstr_CONST I32 i); (admininstr_BR_TABLE l_lst l')] [::(admininstr_BR (l_lst[| ((!((proj_val__0 i))) :> nat) |]))]
	| br_table_ge : forall (i : val_) (l_lst : (seq labelidx)) (l' : labelidx), 
		(wf_admininstr (admininstr_CONST I32 i)) ->
		((proj_val__0 i) != None) ->
		(((!((proj_val__0 i))) :> nat) >= (|l_lst|)) ->
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
	| unop_val : forall (t : valtype) (c_1 : val_) (unop : unop_) (c : val_) (var_0 : (seq val_)), 
		(fun_unop_ t unop c_1 var_0) ->
		(wf_admininstr (admininstr_CONST t c_1)) ->
		(wf_admininstr (admininstr_UNOP t unop)) ->
		(wf_admininstr (admininstr_CONST t c)) ->
		((|var_0|) > 0) ->
		(c \in var_0) ->
		Step_pure [::(admininstr_CONST t c_1); (admininstr_UNOP t unop)] [::(admininstr_CONST t c)]
	| unop_trap : forall (t : valtype) (c_1 : val_) (unop : unop_) (var_0 : (seq val_)), 
		(fun_unop_ t unop c_1 var_0) ->
		(wf_admininstr (admininstr_CONST t c_1)) ->
		(wf_admininstr (admininstr_UNOP t unop)) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_CONST t c_1); (admininstr_UNOP t unop)] [::admininstr_TRAP]
	| binop_val : forall (t : valtype) (c_1 : val_) (c_2 : val_) (binop : binop_) (c : val_) (var_0 : (seq val_)), 
		(fun_binop_ t binop c_1 c_2 var_0) ->
		(wf_admininstr (admininstr_CONST t c_1)) ->
		(wf_admininstr (admininstr_CONST t c_2)) ->
		(wf_admininstr (admininstr_BINOP t binop)) ->
		(wf_admininstr (admininstr_CONST t c)) ->
		((|var_0|) > 0) ->
		(c \in var_0) ->
		Step_pure [::(admininstr_CONST t c_1); (admininstr_CONST t c_2); (admininstr_BINOP t binop)] [::(admininstr_CONST t c)]
	| binop_trap : forall (t : valtype) (c_1 : val_) (c_2 : val_) (binop : binop_) (var_0 : (seq val_)), 
		(fun_binop_ t binop c_1 c_2 var_0) ->
		(wf_admininstr (admininstr_CONST t c_1)) ->
		(wf_admininstr (admininstr_CONST t c_2)) ->
		(wf_admininstr (admininstr_BINOP t binop)) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_CONST t c_1); (admininstr_CONST t c_2); (admininstr_BINOP t binop)] [::admininstr_TRAP]
	| Step_pure__testop : forall (t : valtype) (c_1 : val_) (testop : testop_) (c : val_) (var_0 : val_), 
		(fun_testop_ t testop c_1 var_0) ->
		(wf_admininstr (admininstr_CONST t c_1)) ->
		(wf_admininstr (admininstr_TESTOP t testop)) ->
		(wf_admininstr (admininstr_CONST I32 c)) ->
		(c == var_0) ->
		Step_pure [::(admininstr_CONST t c_1); (admininstr_TESTOP t testop)] [::(admininstr_CONST I32 c)]
	| Step_pure__relop : forall (t : valtype) (c_1 : val_) (c_2 : val_) (relop : relop_) (c : val_) (var_0 : val_), 
		(fun_relop_ t relop c_1 c_2 var_0) ->
		(wf_admininstr (admininstr_CONST t c_1)) ->
		(wf_admininstr (admininstr_CONST t c_2)) ->
		(wf_admininstr (admininstr_RELOP t relop)) ->
		(wf_admininstr (admininstr_CONST I32 c)) ->
		(c == var_0) ->
		Step_pure [::(admininstr_CONST t c_1); (admininstr_CONST t c_2); (admininstr_RELOP t relop)] [::(admininstr_CONST I32 c)]
	| cvtop_val : forall (t_1 : valtype) (c_1 : val_) (t_2 : valtype) (v_cvtop : cvtop) (c : val_) (var_0 : (seq val_)), 
		(fun_cvtop__ t_1 t_2 v_cvtop c_1 var_0) ->
		(wf_admininstr (admininstr_CONST t_1 c_1)) ->
		(wf_admininstr (admininstr_CONST t_2 c)) ->
		((|var_0|) > 0) ->
		(c \in var_0) ->
		Step_pure [::(admininstr_CONST t_1 c_1); (admininstr_CVTOP t_2 t_1 v_cvtop)] [::(admininstr_CONST t_2 c)]
	| cvtop_trap : forall (t_1 : valtype) (c_1 : val_) (t_2 : valtype) (v_cvtop : cvtop) (var_0 : (seq val_)), 
		(fun_cvtop__ t_1 t_2 v_cvtop c_1 var_0) ->
		(wf_admininstr (admininstr_CONST t_1 c_1)) ->
		(var_0 == [:: ]) ->
		Step_pure [::(admininstr_CONST t_1 c_1); (admininstr_CVTOP t_2 t_1 v_cvtop)] [::admininstr_TRAP]
	| Step_pure__local_tee : forall (v_val : val) (x : idx), Step_pure [::(admininstr_val v_val); (admininstr_LOCAL_TEE x)] [::(admininstr_val v_val); (admininstr_val v_val); (admininstr_LOCAL_SET x)].

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:7.1-7.77 *)
Inductive Step_read : config -> (seq admininstr) -> Prop :=
	| Step_read__block : forall (z : state) (t_opt : (option valtype)) (instr_lst : (seq instr)) (v_n : n), 
		(((t_opt == None) && (v_n == 0)) || ((t_opt != None) && (v_n == 1))) ->
		Step_read (mk_config z [::(admininstr_BLOCK t_opt instr_lst)]) [::(LABEL_ v_n [:: ] (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))]
	| Step_read__loop : forall (z : state) (t_opt : (option valtype)) (instr_lst : (seq instr)), Step_read (mk_config z [::(admininstr_LOOP t_opt instr_lst)]) [::(LABEL_ 0 [::(LOOP t_opt instr_lst)] (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))]
	| Step_read__call : forall (z : state) (x : idx), 
		((x :> nat) < (|(fun_funcaddr z)|)) ->
		Step_read (mk_config z [::(admininstr_CALL x)]) [::(CALL_ADDR ((fun_funcaddr z)[| (x :> nat) |]))]
	| call_indirect_call : forall (z : state) (i : val_) (x : idx) (a : addr), 
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x)])) ->
		(((!((proj_val__0 i))) :> nat) < (|(REFS (fun_table z (mk_uN 0)))|)) ->
		((proj_val__0 i) != None) ->
		(((REFS (fun_table z (mk_uN 0)))[| ((!((proj_val__0 i))) :> nat) |]) == (Some a)) ->
		(a < (|(fun_funcinst z)|)) ->
		((fun_type z x) == (funcinst_TYPE ((fun_funcinst z)[| a |]))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x)]) [::(CALL_ADDR a)]
	| call_indirect_trap : forall (z : state) (i : val_) (x : idx) (a : addr), 
		(((!((proj_val__0 i))) :> nat) < (|(REFS (fun_table z (mk_uN 0)))|)) ->
		((proj_val__0 i) != None) ->
		(a < (|(fun_funcinst z)|)) ->
		((((REFS (fun_table z (mk_uN 0)))[| ((!((proj_val__0 i))) :> nat) |]) != (Some a)) || ((fun_type z x) != (funcinst_TYPE ((fun_funcinst z)[| a |])))) ->
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x)])) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_CALL_INDIRECT x)]) [::admininstr_TRAP]
	| call_addr : forall (z : state) (k : nat) (val_lst : (seq val)) (a : addr) (v_n : n) (f : frame) (instr_lst : (seq instr)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)) (mm : moduleinst) (v_func : func) (x : idx) (t_lst : (seq valtype)) (var_0_lst : (seq val)), 
		((|var_0_lst|) == (|t_lst|)) ->
		List.Forall2 (fun (var_0 : val) (t : valtype) => (fun_default_ t var_0)) var_0_lst t_lst ->
		(a < (|(fun_funcinst z)|)) ->
		(((fun_funcinst z)[| a |]) == {| funcinst_TYPE := (mk_functype t_1_lst t_2_lst); funcinst_MODULE := mm; CODE := v_func |}) ->
		(v_func == (func_FUNC x (seq.map (fun (t : valtype) => (LOCAL t)) t_lst) instr_lst)) ->
		(f == {| LOCALS := (val_lst ++ var_0_lst); frame_MODULE := mm |}) ->
		(k == (|val_lst|)) ->
		(k == (|t_1_lst|)) ->
		(v_n == (|t_2_lst|)) ->
		Step_read (mk_config z ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(CALL_ADDR a)])) [::(FRAME_ v_n f [::(LABEL_ v_n [:: ] (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))])]
	| Step_read__local_get : forall (z : state) (x : idx), Step_read (mk_config z [::(admininstr_LOCAL_GET x)]) [::(admininstr_val (fun_local z x))]
	| Step_read__global_get : forall (z : state) (x : idx), Step_read (mk_config z [::(admininstr_GLOBAL_GET x)]) [::(admininstr_val (VALUE (fun_global z x)))]
	| load_num_trap : forall (z : state) (i : val_) (t : valtype) (ao : memarg), 
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD t None ao)])) ->
		((proj_val__0 i) != None) ->
		(((((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) + ((((res_size t) : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD t None ao)]) [::admininstr_TRAP]
	| load_num_val : forall (z : state) (i : val_) (t : valtype) (ao : memarg) (c : val_), 
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD t None ao)])) ->
		(wf_admininstr (admininstr_CONST t c)) ->
		((proj_val__0 i) != None) ->
		((bytes_ t c) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) ((((res_size t) : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD t None ao)]) [::(admininstr_CONST t c)]
	| load_pack_trap : forall (z : state) (i : val_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg), 
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)])) ->
		((proj_val__0 i) != None) ->
		(((((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) + (((v_n : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)]) [::admininstr_TRAP]
	| load_pack_val : forall (z : state) (i : val_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) (c : iN), 
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)])) ->
		(wf_admininstr (admininstr_CONST (valtype_Inn v_Inn) (mk_val__0 v_Inn (extend__ v_n (res_size (valtype_Inn v_Inn)) v_sx c)))) ->
		((proj_val__0 i) != None) ->
		((ibytes_ v_n c) == (list_slice (BYTES (fun_mem z (mk_uN 0))) (((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_n : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config z [::(admininstr_CONST I32 i); (admininstr_LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)]) [::(admininstr_CONST (valtype_Inn v_Inn) (mk_val__0 v_Inn (extend__ v_n (res_size (valtype_Inn v_Inn)) v_sx c)))]
	| Step_read__memory_size : forall (z : state) (v_n : n), 
		(wf_admininstr (admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n)))) ->
		(((v_n * 64) * (Ki )) == (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step_read (mk_config z [::admininstr_MEMORY_SIZE]) [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n)))].

(* Mutual Recursion at: ../specification/wasm-1.0/8-reduction.spectec:5.1-5.77 *)
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
	| store_num_trap : forall (z : state) (i : val_) (t : valtype) (c : val_) (ao : memarg), 
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST t c); (admininstr_STORE t None ao)])) ->
		((proj_val__0 i) != None) ->
		(((((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) + ((((res_size t) : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST t c); (admininstr_STORE t None ao)]) (mk_config z [::admininstr_TRAP])
	| store_num_val : forall (z : state) (i : val_) (t : valtype) (c : val_) (ao : memarg) (b_lst : (seq byte)), 
		((proj_val__0 i) != None) ->
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST t c); (admininstr_STORE t None ao)])) ->
		(wf_config (mk_config (with_mem z (mk_uN 0) (((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) ((((res_size t) : nat) / (8 : nat)) : nat) b_lst) [:: ])) ->
		(b_lst == (bytes_ t c)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST t c); (admininstr_STORE t None ao)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) ((((res_size t) : nat) / (8 : nat)) : nat) b_lst) [:: ])
	| store_pack_trap : forall (z : state) (i : val_) (v_Inn : Inn) (c : val_) (v_n : n) (ao : memarg), 
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST (valtype_Inn v_Inn) c); (admininstr_STORE (valtype_Inn v_Inn) (Some (mk_sz v_n)) ao)])) ->
		((proj_val__0 i) != None) ->
		(((((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) + (((v_n : nat) / (8 : nat)) : nat)) > (|(BYTES (fun_mem z (mk_uN 0)))|)) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST (valtype_Inn v_Inn) c); (admininstr_STORE (valtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]) (mk_config z [::admininstr_TRAP])
	| store_pack_val : forall (z : state) (i : val_) (v_Inn : Inn) (c : val_) (v_n : n) (ao : memarg) (b_lst : (seq byte)), 
		((proj_val__0 i) != None) ->
		(wf_config (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST (valtype_Inn v_Inn) c); (admininstr_STORE (valtype_Inn v_Inn) (Some (mk_sz v_n)) ao)])) ->
		(wf_config (mk_config (with_mem z (mk_uN 0) (((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_n : nat) / (8 : nat)) : nat) b_lst) [:: ])) ->
		((proj_val__0 c) != None) ->
		(b_lst == (ibytes_ v_n (wrap__ (res_size (valtype_Inn v_Inn)) v_n (!((proj_val__0 c)))))) ->
		Step (mk_config z [::(admininstr_CONST I32 i); (admininstr_CONST (valtype_Inn v_Inn) c); (admininstr_STORE (valtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]) (mk_config (with_mem z (mk_uN 0) (((!((proj_val__0 i))) :> nat) + ((OFFSET ao) :> nat)) (((v_n : nat) / (8 : nat)) : nat) b_lst) [:: ])
	| memory_grow_succeed : forall (z : state) (v_n : n) (mi : meminst) (var_0 : (option meminst)), 
		(fun_growmemory (fun_mem z (mk_uN 0)) v_n var_0) ->
		(wf_config (mk_config z [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_GROW])) ->
		(wf_config (mk_config (with_meminst z (mk_uN 0) mi) [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN ((((|(BYTES (fun_mem z (mk_uN 0)))|) : nat) / ((64 * (Ki )) : nat)) : nat))))])) ->
		(var_0 != None) ->
		((!(var_0)) == mi) ->
		Step (mk_config z [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_GROW]) (mk_config (with_meminst z (mk_uN 0) mi) [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN ((((|(BYTES (fun_mem z (mk_uN 0)))|) : nat) / ((64 * (Ki )) : nat)) : nat))))])
	| memory_grow_fail : forall (z : state) (v_n : n) (var_0 : nat), 
		(fun_inv_signed_ 32 (0 - (1 : nat)) var_0) ->
		(wf_config (mk_config z [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_GROW])) ->
		(wf_config (mk_config z [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN var_0)))])) ->
		Step (mk_config z [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n))); admininstr_MEMORY_GROW]) (mk_config z [::(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN var_0)))]).

(* Mutual Recursion at: ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77 *)
Inductive Steps : config -> config -> Prop :=
	| refl : forall (z : state) (admininstr_lst : (seq admininstr)), Steps (mk_config z admininstr_lst) (mk_config z admininstr_lst)
	| trans : forall (z : state) (admininstr_lst : (seq admininstr)) (z'' : state) (admininstr''_lst : (seq admininstr)) (z' : state) (admininstr'_lst : (seq admininstr)), 
		(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ->
		(Steps (mk_config z' admininstr'_lst) (mk_config z'' admininstr''_lst)) ->
		Steps (mk_config z admininstr_lst) (mk_config z'' admininstr''_lst).

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:29.1-29.83 *)
Inductive Eval_expr : state -> expr -> state -> (seq val) -> Prop :=
	| mk_Eval_expr : forall (z : state) (instr_lst : (seq instr)) (z' : state) (val_lst : (seq val)), 
		(Steps (mk_config z (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)) (mk_config z' (seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))) ->
		Eval_expr z instr_lst z' val_lst.

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:5.1-5.36 *)
Inductive fun_funcs : (seq externaddr) -> (seq funcaddr) -> Prop :=
	| fun_funcs_case_0 : fun_funcs [:: ] [:: ]
	| fun_funcs_case_1 : forall (fa : nat) (externaddr'_lst : (seq externaddr)) (var_0 : (seq funcaddr)), 
		(fun_funcs externaddr'_lst var_0) ->
		fun_funcs ([::(externaddr_FUNC fa)] ++ externaddr'_lst) ([::fa] ++ var_0)
	| fun_funcs_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (seq externaddr)) (var_0 : (seq funcaddr)), 
		(fun_funcs externaddr'_lst var_0) ->
		fun_funcs ([::v_externaddr] ++ externaddr'_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:11.1-11.40 *)
Inductive fun_globals : (seq externaddr) -> (seq globaladdr) -> Prop :=
	| fun_globals_case_0 : fun_globals [:: ] [:: ]
	| fun_globals_case_1 : forall (ga : nat) (externaddr'_lst : (seq externaddr)) (var_0 : (seq globaladdr)), 
		(fun_globals externaddr'_lst var_0) ->
		fun_globals ([::(externaddr_GLOBAL ga)] ++ externaddr'_lst) ([::ga] ++ var_0)
	| fun_globals_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (seq externaddr)) (var_0 : (seq globaladdr)), 
		(fun_globals externaddr'_lst var_0) ->
		fun_globals ([::v_externaddr] ++ externaddr'_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:17.1-17.38 *)
Inductive fun_tables : (seq externaddr) -> (seq tableaddr) -> Prop :=
	| fun_tables_case_0 : fun_tables [:: ] [:: ]
	| fun_tables_case_1 : forall (ta : nat) (externaddr'_lst : (seq externaddr)) (var_0 : (seq tableaddr)), 
		(fun_tables externaddr'_lst var_0) ->
		fun_tables ([::(externaddr_TABLE ta)] ++ externaddr'_lst) ([::ta] ++ var_0)
	| fun_tables_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (seq externaddr)) (var_0 : (seq tableaddr)), 
		(fun_tables externaddr'_lst var_0) ->
		fun_tables ([::v_externaddr] ++ externaddr'_lst) var_0.

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:23.1-23.34 *)
Inductive fun_mems : (seq externaddr) -> (seq memaddr) -> Prop :=
	| fun_mems_case_0 : fun_mems [:: ] [:: ]
	| fun_mems_case_1 : forall (ma : nat) (externaddr'_lst : (seq externaddr)) (var_0 : (seq memaddr)), 
		(fun_mems externaddr'_lst var_0) ->
		fun_mems ([::(externaddr_MEM ma)] ++ externaddr'_lst) ([::ma] ++ var_0)
	| fun_mems_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (seq externaddr)) (var_0 : (seq memaddr)), 
		(fun_mems externaddr'_lst var_0) ->
		fun_mems ([::v_externaddr] ++ externaddr'_lst) var_0.

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:36.6-36.16 *)
Inductive fun_allocfunc : store -> moduleinst -> func -> (store * funcaddr) -> Prop :=
	| fun_allocfunc_case_0 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (fi : funcinst) (x : uN) (local_lst : (seq local)) (v_expr : (seq instr)), 
		((x :> nat) < (|(TYPES v_moduleinst)|)) ->
		(fi == {| funcinst_TYPE := ((TYPES v_moduleinst)[| (x :> nat) |]); funcinst_MODULE := v_moduleinst; CODE := v_func |}) ->
		(v_func == (func_FUNC x local_lst v_expr)) ->
		fun_allocfunc s v_moduleinst v_func ((s <| store_FUNCS := ((store_FUNCS s) ++ [::fi]) |>), (|(store_FUNCS s)|)).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:41.1-41.63 *)
Inductive fun_allocfuncs : store -> moduleinst -> (seq func) -> (store * (seq funcaddr)) -> Prop :=
	| fun_allocfuncs_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_allocfuncs s v_moduleinst [:: ] (s, [:: ])
	| fun_allocfuncs_case_1 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (func'_lst : (seq func)) (s_2 : store) (fa : nat) (fa'_lst : (seq funcaddr)) (s_1 : store) (var_1 : (store * (seq funcaddr))) (var_0 : (store * funcaddr)), 
		(fun_allocfuncs s_1 v_moduleinst func'_lst var_1) ->
		(fun_allocfunc s v_moduleinst v_func var_0) ->
		((s_1, fa) == var_0) ->
		((s_2, fa'_lst) == var_1) ->
		fun_allocfuncs s v_moduleinst ([::v_func] ++ func'_lst) (s_2, ([::fa] ++ fa'_lst)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:47.6-47.18 *)
Inductive fun_allocglobal : store -> globaltype -> val -> (store * globaladdr) -> Prop :=
	| fun_allocglobal_case_0 : forall (s : store) (v_globaltype : globaltype) (v_val : val) (gi : globalinst), 
		(gi == {| globalinst_TYPE := v_globaltype; VALUE := v_val |}) ->
		fun_allocglobal s v_globaltype v_val ((s <| store_GLOBALS := ((store_GLOBALS s) ++ [::gi]) |>), (|(store_GLOBALS s)|)).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:51.1-51.67 *)
Inductive fun_allocglobals : store -> (seq globaltype) -> (seq val) -> (store * (seq globaladdr)) -> Prop :=
	| fun_allocglobals_case_0 : forall (s : store), fun_allocglobals s [:: ] [:: ] (s, [:: ])
	| fun_allocglobals_case_1 : forall (s : store) (v_globaltype : globaltype) (globaltype'_lst : (seq globaltype)) (v_val : val) (val'_lst : (seq val)) (s_2 : store) (ga : nat) (ga'_lst : (seq globaladdr)) (s_1 : store) (var_1 : (store * (seq globaladdr))) (var_0 : (store * globaladdr)), 
		(fun_allocglobals s_1 globaltype'_lst val'_lst var_1) ->
		(fun_allocglobal s v_globaltype v_val var_0) ->
		((s_1, ga) == var_0) ->
		((s_2, ga'_lst) == var_1) ->
		fun_allocglobals s ([::v_globaltype] ++ globaltype'_lst) ([::v_val] ++ val'_lst) (s_2, ([::ga] ++ ga'_lst)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:57.6-57.17 *)
Inductive fun_alloctable : store -> tabletype -> (store * tableaddr) -> Prop :=
	| fun_alloctable_case_0 : forall (s : store) (i : uN) (j_opt : (option u32)) (ti : tableinst), 
		(ti == {| tableinst_TYPE := (mk_limits i j_opt); REFS := (List.repeat None (i :> nat)) |}) ->
		fun_alloctable s (mk_limits i j_opt) ((s <| store_TABLES := ((store_TABLES s) ++ [::ti]) |>), (|(store_TABLES s)|)).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:61.1-61.58 *)
Inductive fun_alloctables : store -> (seq tabletype) -> (store * (seq tableaddr)) -> Prop :=
	| fun_alloctables_case_0 : forall (s : store), fun_alloctables s [:: ] (s, [:: ])
	| fun_alloctables_case_1 : forall (s : store) (v_tabletype : limits) (tabletype'_lst : (seq tabletype)) (s_2 : store) (ta : nat) (ta'_lst : (seq tableaddr)) (s_1 : store) (var_1 : (store * (seq tableaddr))) (var_0 : (store * tableaddr)), 
		(fun_alloctables s_1 tabletype'_lst var_1) ->
		(fun_alloctable s v_tabletype var_0) ->
		((s_1, ta) == var_0) ->
		((s_2, ta'_lst) == var_1) ->
		fun_alloctables s ([::v_tabletype] ++ tabletype'_lst) (s_2, ([::ta] ++ ta'_lst)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:67.6-67.15 *)
Inductive fun_allocmem : store -> memtype -> (store * memaddr) -> Prop :=
	| fun_allocmem_case_0 : forall (s : store) (i : uN) (j_opt : (option u32)) (mi : meminst), 
		(mi == {| meminst_TYPE := (mk_limits i j_opt); BYTES := (List.repeat (mk_byte 0) ((i :> nat) * (64 * (Ki )))) |}) ->
		fun_allocmem s (mk_limits i j_opt) ((s <| store_MEMS := ((store_MEMS s) ++ [::mi]) |>), (|(store_MEMS s)|)).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:71.1-71.52 *)
Inductive fun_allocmems : store -> (seq memtype) -> (store * (seq memaddr)) -> Prop :=
	| fun_allocmems_case_0 : forall (s : store), fun_allocmems s [:: ] (s, [:: ])
	| fun_allocmems_case_1 : forall (s : store) (v_memtype : limits) (memtype'_lst : (seq memtype)) (s_2 : store) (ma : nat) (ma'_lst : (seq memaddr)) (s_1 : store) (var_1 : (store * (seq memaddr))) (var_0 : (store * memaddr)), 
		(fun_allocmems s_1 memtype'_lst var_1) ->
		(fun_allocmem s v_memtype var_0) ->
		((s_1, ma) == var_0) ->
		((s_2, ma'_lst) == var_1) ->
		fun_allocmems s ([::v_memtype] ++ memtype'_lst) (s_2, ([::ma] ++ ma'_lst)).

(* Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:80.1-80.83 *)
Definition instexport (var_0 : (seq funcaddr)) (var_1 : (seq globaladdr)) (var_2 : (seq tableaddr)) (var_3 : (seq memaddr)) (v_export : export) : exportinst :=
	match var_0, var_1, var_2, var_3, v_export return exportinst with
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_FUNC x)) => {| NAME := v_name; ADDR := (externaddr_FUNC (fa_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_GLOBAL x)) => {| NAME := v_name; ADDR := (externaddr_GLOBAL (ga_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_TABLE x)) => {| NAME := v_name; ADDR := (externaddr_TABLE (ta_lst[| (x :> nat) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_MEM x)) => {| NAME := v_name; ADDR := (externaddr_MEM (ma_lst[| (x :> nat) |])) |}
	end.

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:87.6-87.18 *)
Inductive fun_allocmodule : store -> module -> (seq externaddr) -> (seq val) -> (store * moduleinst) -> Prop :=
	| fun_allocmodule_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (seq externaddr)) (val_lst : (seq val)) (s_4 : store) (v_moduleinst : moduleinst) (ft_lst : (seq functype)) (import_lst : (seq import)) (n_func : nat) (func_lst : (seq func)) (n_global : nat) (expr_1_lst : (seq expr)) (globaltype_lst : (seq globaltype)) (n_table : nat) (tabletype_lst : (seq tabletype)) (n_mem : nat) (memtype_lst : (seq memtype)) (elem_lst : (seq elem)) (data_lst : (seq data)) (start_opt : (option start)) (export_lst : (seq export)) (fa_ex_lst : (seq funcaddr)) (ga_ex_lst : (seq globaladdr)) (ta_ex_lst : (seq tableaddr)) (ma_ex_lst : (seq memaddr)) (fa_lst : (seq funcaddr)) (ga_lst : (seq globaladdr)) (ta_lst : (seq tableaddr)) (ma_lst : (seq memaddr)) (xi_lst : (seq exportinst)) (s_1 : store) (s_2 : store) (s_3 : store) (var_7 : (store * (seq memaddr))) (var_6 : (store * (seq tableaddr))) (var_5 : (store * (seq globaladdr))) (var_4 : (store * (seq funcaddr))) (var_3 : (seq memaddr)) (var_2 : (seq tableaddr)) (var_1 : (seq globaladdr)) (var_0 : (seq funcaddr)), 
		(fun_allocmems s_3 memtype_lst var_7) ->
		(fun_alloctables s_2 tabletype_lst var_6) ->
		(fun_allocglobals s_1 globaltype_lst val_lst var_5) ->
		(fun_allocfuncs s v_moduleinst func_lst var_4) ->
		(fun_mems externaddr_lst var_3) ->
		(fun_tables externaddr_lst var_2) ->
		(fun_globals externaddr_lst var_1) ->
		(fun_funcs externaddr_lst var_0) ->
		(v_module == (MODULE (seq.map (fun (ft : functype) => (TYPE ft)) ft_lst) import_lst func_lst (list_zipWith (fun (expr_1 : expr) (v_globaltype : globaltype) => (global_GLOBAL v_globaltype expr_1)) expr_1_lst globaltype_lst) (seq.map (fun (v_tabletype : tabletype) => (table_TABLE v_tabletype)) tabletype_lst) (seq.map (fun (v_memtype : memtype) => (MEMORY v_memtype)) memtype_lst) elem_lst data_lst start_opt export_lst)) ->
		(fa_ex_lst == var_0) ->
		(ga_ex_lst == var_1) ->
		(ta_ex_lst == var_2) ->
		(ma_ex_lst == var_3) ->
		(fa_lst == (seq.mkseq (fun i_func => ((|(store_FUNCS s)|) + i_func)) n_func)) ->
		(ga_lst == (seq.mkseq (fun i_global => ((|(store_GLOBALS s)|) + i_global)) n_global)) ->
		(ta_lst == (seq.mkseq (fun i_table => ((|(store_TABLES s)|) + i_table)) n_table)) ->
		(ma_lst == (seq.mkseq (fun i_mem => ((|(store_MEMS s)|) + i_mem)) n_mem)) ->
		(xi_lst == (seq.map (fun (v_export : export) => (instexport (fa_ex_lst ++ fa_lst) (ga_ex_lst ++ ga_lst) (ta_ex_lst ++ ta_lst) (ma_ex_lst ++ ma_lst) v_export)) export_lst)) ->
		(v_moduleinst == {| TYPES := ft_lst; FUNCS := (fa_ex_lst ++ fa_lst); GLOBALS := (ga_ex_lst ++ ga_lst); TABLES := (ta_ex_lst ++ ta_lst); MEMS := (ma_ex_lst ++ ma_lst); EXPORTS := xi_lst |}) ->
		((s_1, fa_lst) == var_4) ->
		((s_2, ga_lst) == var_5) ->
		((s_3, ta_lst) == var_6) ->
		((s_4, ma_lst) == var_7) ->
		fun_allocmodule s v_module externaddr_lst val_lst (s_4, v_moduleinst).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:128.1-128.61 *)
Inductive fun_initelem : store -> moduleinst -> (seq u32) -> (seq (seq funcaddr)) -> store -> Prop :=
	| fun_initelem_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_initelem s v_moduleinst [:: ] [:: ] s
	| fun_initelem_case_1 : forall (s : store) (v_moduleinst : moduleinst) (i : uN) (i'_lst : (seq u32)) (a_lst : (seq addr)) (a'_lst_lst : (seq (seq addr))) (s_2 : store) (s_1 : store) (var_0 : store), 
		(fun_initelem s_1 v_moduleinst i'_lst a'_lst_lst var_0) ->
		(0 < (|(TABLES v_moduleinst)|)) ->
		(s_1 == (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES v_moduleinst)[| 0 |]) (fun (var_1 : tableinst) => (var_1 <| REFS := (list_slice_update (REFS var_1) (i :> nat) (|a_lst|) (seq.map (fun (a : addr) => (Some a)) a_lst)) |>))) |>)) ->
		(s_2 == var_0) ->
		fun_initelem s v_moduleinst ([::i] ++ i'_lst) ([::a_lst] ++ a'_lst_lst) s_2.

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:134.1-134.57 *)
Inductive fun_initdata : store -> moduleinst -> (seq u32) -> (seq (seq byte)) -> store -> Prop :=
	| fun_initdata_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_initdata s v_moduleinst [:: ] [:: ] s
	| fun_initdata_case_1 : forall (s : store) (v_moduleinst : moduleinst) (i : uN) (i'_lst : (seq u32)) (b_lst : (seq byte)) (b'_lst_lst : (seq (seq byte))) (s_2 : store) (s_1 : store) (var_0 : store), 
		(fun_initdata s_1 v_moduleinst i'_lst b'_lst_lst var_0) ->
		(0 < (|(MEMS v_moduleinst)|)) ->
		(s_1 == (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS v_moduleinst)[| 0 |]) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (BYTES var_1) (i :> nat) (|b_lst|) b_lst) |>))) |>)) ->
		(s_2 == var_0) ->
		fun_initdata s v_moduleinst ([::i] ++ i'_lst) ([::b_lst] ++ b'_lst_lst) s_2.

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:140.6-140.18 *)
Inductive fun_instantiate : store -> module -> (seq externaddr) -> config -> Prop :=
	| fun_instantiate_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (seq externaddr)) (s_3 : store) (f : frame) (x'_opt : (option idx)) (type_lst : (seq type)) (import_lst : (seq import)) (func_lst : (seq func)) (global_lst : (seq global)) (table_lst : (seq table)) (mem_lst : (seq mem)) (elem_lst : (seq elem)) (data_lst : (seq data)) (start_opt : (option start)) (export_lst : (seq export)) (functype_lst : (seq functype)) (expr_G_lst : (seq expr)) (globaltype_lst : (seq globaltype)) (expr_E_lst : (seq expr)) (x_lst_lst : (seq (seq idx))) (b_lst_lst : (seq (seq byte))) (expr_D_lst : (seq expr)) (n_F : nat) (moduleinst_init : moduleinst) (f_init : frame) (z : state) (val_lst : (seq val)) (i_E_lst : (seq val_)) (i_D_lst : (seq val_)) (s_1 : store) (v_moduleinst : moduleinst) (s_2 : store) (var_4 : store) (var_3 : store) (var_2 : (store * moduleinst)) (var_1 : (seq globaladdr)) (var_0 : (seq funcaddr)), 
		List.Forall (fun (i_D : val_) => ((proj_val__0 i_D) != None)) i_D_lst ->
		(fun_initdata s_2 v_moduleinst (seq.map (fun (i_D : val_) => (!((proj_val__0 i_D)))) i_D_lst) b_lst_lst var_4) ->
		List.Forall (fun (i_E : val_) => ((proj_val__0 i_E) != None)) i_E_lst ->
		List.Forall (fun (x_lst : (seq idx)) => List.Forall (fun (x : idx) => ((x :> nat) < (|(FUNCS v_moduleinst)|))) x_lst) x_lst_lst ->
		(fun_initelem s_1 v_moduleinst (seq.map (fun (i_E : val_) => (!((proj_val__0 i_E)))) i_E_lst) (seq.map (fun (x_lst : (seq idx)) => (seq.map (fun (x : idx) => ((FUNCS v_moduleinst)[| (x :> nat) |])) x_lst)) x_lst_lst) var_3) ->
		(fun_allocmodule s v_module externaddr_lst val_lst var_2) ->
		(fun_globals externaddr_lst var_1) ->
		(fun_funcs externaddr_lst var_0) ->
		List.Forall (fun (i_E : val_) => (wf_val (val_CONST I32 i_E))) i_E_lst ->
		List.Forall (fun (i_D : val_) => (wf_val (val_CONST I32 i_D))) i_D_lst ->
		(v_module == (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ->
		(type_lst == (seq.map (fun (v_functype : functype) => (TYPE v_functype)) functype_lst)) ->
		(global_lst == (list_zipWith (fun (expr_G : expr) (v_globaltype : globaltype) => (global_GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ->
		(elem_lst == (list_zipWith (fun (expr_E : expr) (x_lst : (seq idx)) => (ELEM expr_E x_lst)) expr_E_lst x_lst_lst)) ->
		(data_lst == (list_zipWith (fun (b_lst : (seq byte)) (expr_D : expr) => (DATA expr_D b_lst)) b_lst_lst expr_D_lst)) ->
		(start_opt == (option_map (fun (x' : idx) => (START x')) x'_opt)) ->
		(n_F == (|func_lst|)) ->
		(moduleinst_init == {| TYPES := functype_lst; FUNCS := (var_0 ++ (seq.mkseq (fun i_F => ((|(store_FUNCS s)|) + i_F)) n_F)); GLOBALS := var_1; TABLES := [:: ]; MEMS := [:: ]; EXPORTS := [:: ] |}) ->
		(f_init == {| LOCALS := [:: ]; frame_MODULE := moduleinst_init |}) ->
		(z == (mk_state s f_init)) ->
		((|expr_G_lst|) == (|val_lst|)) ->
		List.Forall2 (fun (expr_G : expr) (v_val : val) => (Eval_expr z expr_G z [::v_val])) expr_G_lst val_lst ->
		((|expr_E_lst|) == (|i_E_lst|)) ->
		List.Forall2 (fun (expr_E : expr) (i_E : val_) => (Eval_expr z expr_E z [::(val_CONST I32 i_E)])) expr_E_lst i_E_lst ->
		((|expr_D_lst|) == (|i_D_lst|)) ->
		List.Forall2 (fun (expr_D : expr) (i_D : val_) => (Eval_expr z expr_D z [::(val_CONST I32 i_D)])) expr_D_lst i_D_lst ->
		((s_1, v_moduleinst) == var_2) ->
		(s_2 == var_3) ->
		(s_3 == var_4) ->
		(f == {| LOCALS := [:: ]; frame_MODULE := v_moduleinst |}) ->
		fun_instantiate s v_module externaddr_lst (mk_config (mk_state s_3 f) (option_to_list (option_map (fun (x' : idx) => (admininstr_CALL x')) x'_opt))).

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:169.6-169.13 *)
Inductive fun_invoke : store -> funcaddr -> (seq val) -> config -> Prop :=
	| fun_invoke_case_0 : forall (s : store) (fa : nat) (v_n : nat) (val_lst : (seq val)) (f : frame) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(f == {| LOCALS := [:: ]; frame_MODULE := {| TYPES := [:: ]; FUNCS := [:: ]; GLOBALS := [:: ]; TABLES := [:: ]; MEMS := [:: ]; EXPORTS := [:: ] |} |}) ->
		(fa < (|(fun_funcinst (mk_state s f))|)) ->
		((funcinst_TYPE ((fun_funcinst (mk_state s f))[| fa |])) == (mk_functype t_1_lst t_2_lst)) ->
		(v_n == (|val_lst|)) ->
		fun_invoke s fa val_lst (mk_config (mk_state s f) ((seq.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [::(CALL_ADDR fa)])).

(* Type Alias Definition at: ../specification/wasm-1.0/A-binary.spectec:483.1-483.43 *)
Definition startopt : Type := (seq start).

(* Type Alias Definition at: ../specification/wasm-1.0/A-binary.spectec:500.1-500.29 *)
Definition code : Type := ((seq local) * expr).

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:7.1-7.58 *)
Inductive Externaddrs_ok : store -> externaddr -> externtype -> Prop :=
	| Externaddrs_ok__func : forall (v_S : store) (a : addr) (ext : functype) (minst : moduleinst) (v_func : func), 
		(a < (|(store_FUNCS v_S)|)) ->
		(((store_FUNCS v_S)[| a |]) == {| funcinst_TYPE := ext; funcinst_MODULE := minst; CODE := v_func |}) ->
		Externaddrs_ok v_S (externaddr_FUNC a) (FUNC ext)
	| Externaddrs_ok__table : forall (v_S : store) (a : addr) (res_tt : tabletype) (tt' : tabletype) (ref_lst : (seq funcaddr)), 
		(a < (|(store_TABLES v_S)|)) ->
		(((store_TABLES v_S)[| a |]) == {| tableinst_TYPE := tt'; REFS := (seq.map (fun (ref : funcaddr) => (Some ref)) ref_lst) |}) ->
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:29.1-29.40 *)
Inductive Val_ok : store -> val -> valtype -> Prop :=
	| numtype : forall (v_S : store) (nt : valtype) (c_t : val_), 
		(wf_val (val_CONST nt c_t)) ->
		Val_ok v_S (val_CONST nt c_t) nt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:36.1-36.47 *)
Inductive Result_ok : store -> result -> (seq valtype) -> Prop :=
	| Result_ok__result : forall (v_S : store) (v_lst : (seq val)) (t_lst : (seq valtype)), 
		((|t_lst|) == (|v_lst|)) ->
		List.Forall2 (fun (t : valtype) (v : val) => (Val_ok v_S v t)) t_lst v_lst ->
		Result_ok v_S (_VALS v_lst) t_lst
	| trap : forall (v_S : store) (t_lst : (seq valtype)), Result_ok v_S TRAP t_lst.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:48.1-48.56 *)
Inductive Memory_instance_ok : store -> meminst -> memtype -> Prop :=
	| mk_Memory_instance_ok : forall (v_S : store) (mt : memtype) (b_lst : (seq byte)) (v_n : n) (m_opt : (option m)), 
		(mt == (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt))) ->
		((|b_lst|) == ((v_n * 64) * (Ki ))) ->
		(Memtype_ok mt) ->
		Memory_instance_ok v_S {| meminst_TYPE := mt; BYTES := b_lst |} mt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:58.1-58.59 *)
Inductive Table_instance_ok : store -> tableinst -> tabletype -> Prop :=
	| mk_Table_instance_ok : forall (v_S : store) (res_tt : tabletype) (ref_lst : (seq funcaddr)) (v_n : n) (v_m : m), 
		(res_tt == (mk_limits (mk_uN v_n) (Some (mk_uN v_m)))) ->
		(v_n == (|ref_lst|)) ->
		(Tabletype_ok res_tt) ->
		Table_instance_ok v_S {| tableinst_TYPE := res_tt; REFS := (seq.map (fun (ref : funcaddr) => (Some ref)) ref_lst) |} res_tt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:68.1-68.62 *)
Inductive Global_instance_ok : store -> globalinst -> globaltype -> Prop :=
	| mk_Global_instance_ok : forall (v_S : store) (gt : globaltype) (v : val) (v_mut : mut) (vt : valtype), 
		(gt == (mk_globaltype v_mut vt)) ->
		(Globaltype_ok gt) ->
		(Val_ok v_S v vt) ->
		Global_instance_ok v_S {| globalinst_TYPE := gt; VALUE := v |} gt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:78.1-78.54 *)
Inductive Export_instance_ok : store -> exportinst -> Prop :=
	| mk_Export_instance_ok : forall (v_S : store) (v_name : name) (eaddr : externaddr) (ext : externtype), 
		(Externaddrs_ok v_S eaddr ext) ->
		Export_instance_ok v_S {| NAME := v_name; ADDR := eaddr |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:87.1-87.59 *)
Inductive Module_instance_ok : store -> moduleinst -> context -> Prop :=
	| mk_Module_instance_ok : forall (v_S : store) (functype_lst : (seq functype)) (funcaddr_lst : (seq funcaddr)) (globaladdr_lst : (seq globaladdr)) (tableaddr_lst : (seq tableaddr)) (memaddr_lst : (seq memaddr)) (exportinst_lst : (seq exportinst)) (functype'_lst : (seq functype)) (globaltype_lst : (seq globaltype)) (tabletype_lst : (seq tabletype)) (memtype_lst : (seq memtype)), 
		List.Forall (fun (v_functype : functype) => (Functype_ok v_functype)) functype_lst ->
		((|funcaddr_lst|) == (|functype'_lst|)) ->
		List.Forall2 (fun (v_funcaddr : funcaddr) (functype' : functype) => (Externaddrs_ok v_S (externaddr_FUNC v_funcaddr) (FUNC functype'))) funcaddr_lst functype'_lst ->
		((|tableaddr_lst|) == (|tabletype_lst|)) ->
		List.Forall2 (fun (v_tableaddr : tableaddr) (v_tabletype : tabletype) => (Externaddrs_ok v_S (externaddr_TABLE v_tableaddr) (TABLE v_tabletype))) tableaddr_lst tabletype_lst ->
		((|memaddr_lst|) == (|memtype_lst|)) ->
		List.Forall2 (fun (v_memaddr : memaddr) (v_memtype : memtype) => (Externaddrs_ok v_S (externaddr_MEM v_memaddr) (MEM v_memtype))) memaddr_lst memtype_lst ->
		((|globaladdr_lst|) == (|globaltype_lst|)) ->
		List.Forall2 (fun (v_globaladdr : globaladdr) (v_globaltype : globaltype) => (Externaddrs_ok v_S (externaddr_GLOBAL v_globaladdr) (GLOBAL v_globaltype))) globaladdr_lst globaltype_lst ->
		List.Forall (fun (v_exportinst : exportinst) => (Export_instance_ok v_S v_exportinst)) exportinst_lst ->
		Module_instance_ok v_S {| TYPES := functype_lst; FUNCS := funcaddr_lst; GLOBALS := globaladdr_lst; TABLES := tableaddr_lst; MEMS := memaddr_lst; EXPORTS := exportinst_lst |} {| context_TYPES := functype_lst; context_FUNCS := functype'_lst; context_GLOBALS := globaltype_lst; context_TABLES := tabletype_lst; context_MEMS := memtype_lst; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := None |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:102.1-102.60 *)
Inductive Function_instance_ok : store -> funcinst -> functype -> Prop :=
	| mk_Function_instance_ok : forall (v_S : store) (v_functype : functype) (v_moduleinst : moduleinst) (v_func : func) (C : context), 
		(Functype_ok v_functype) ->
		(Module_instance_ok v_S v_moduleinst C) ->
		(Func_ok C v_func v_functype) ->
		Function_instance_ok v_S {| funcinst_TYPE := v_functype; funcinst_MODULE := v_moduleinst; CODE := v_func |} v_functype.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:112.1-112.33 *)
Inductive Store_ok : store -> Prop :=
	| mk_Store_ok : forall (v_S : store) (funcinst_lst : (seq funcinst)) (globalinst_lst : (seq globalinst)) (tableinst_lst : (seq tableinst)) (meminst_lst : (seq meminst)) (functype_lst : (seq functype)) (globaltype_lst : (seq globaltype)) (tabletype_lst : (seq tabletype)) (memtype_lst : (seq memtype)), 
		(v_S == {| store_FUNCS := funcinst_lst; store_GLOBALS := globalinst_lst; store_TABLES := tableinst_lst; store_MEMS := meminst_lst |}) ->
		((|funcinst_lst|) == (|functype_lst|)) ->
		List.Forall2 (fun (v_funcinst : funcinst) (v_functype : functype) => (Function_instance_ok v_S v_funcinst v_functype)) funcinst_lst functype_lst ->
		((|globalinst_lst|) == (|globaltype_lst|)) ->
		List.Forall2 (fun (v_globalinst : globalinst) (v_globaltype : globaltype) => (Global_instance_ok v_S v_globalinst v_globaltype)) globalinst_lst globaltype_lst ->
		((|tableinst_lst|) == (|tabletype_lst|)) ->
		List.Forall2 (fun (v_tableinst : tableinst) (v_tabletype : tabletype) => (Table_instance_ok v_S v_tableinst v_tabletype)) tableinst_lst tabletype_lst ->
		((|meminst_lst|) == (|memtype_lst|)) ->
		List.Forall2 (fun (v_meminst : meminst) (v_memtype : memtype) => (Memory_instance_ok v_S v_meminst v_memtype)) meminst_lst memtype_lst ->
		Store_ok v_S.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:182.1-182.44 *)
Inductive Frame_ok : store -> frame -> context -> Prop :=
	| mk_Frame_ok : forall (v_S : store) (val_lst : (seq val)) (v_moduleinst : moduleinst) (t_lst : (seq valtype)) (C : context), 
		(Module_instance_ok v_S v_moduleinst C) ->
		((|t_lst|) == (|val_lst|)) ->
		List.Forall2 (fun (t : valtype) (v_val : val) => (Val_ok v_S v_val t)) t_lst val_lst ->
		Frame_ok v_S {| LOCALS := val_lst; frame_MODULE := v_moduleinst |} ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := t_lst; LABELS := [:: ]; context_RETURN := None |} @@ C).

(* Auxiliary Definition at: ../specification/wasm-1.0/B-soundness.spectec:148.1-148.32 *)
Definition optionSize (var_0 : (option valtype)) : nat :=
	match var_0 return nat with
		| (Some v_valtype) => 1
		| None => 0
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/B-soundness.spectec:124.1-126.75 *)
Inductive Admin_instr_ok : store -> context -> admininstr -> functype -> Prop :=
	| Admin_instr_ok__instr : forall (v_S : store) (C : context) (v_instr : instr) (v_functype : functype), 
		(Instr_ok C v_instr v_functype) ->
		Admin_instr_ok v_S C (admininstr_instr v_instr) v_functype
	| Admin_instr_ok__trap : forall (v_S : store) (C : context) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), Admin_instr_ok v_S C admininstr_TRAP (mk_functype t_1_lst t_2_lst)
	| Admin_instr_ok__call_addr : forall (v_S : store) (C : context) (v_funcaddr : funcaddr) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Externaddrs_ok v_S (externaddr_FUNC v_funcaddr) (FUNC (mk_functype t_1_lst t_2_lst))) ->
		Admin_instr_ok v_S C (CALL_ADDR v_funcaddr) (mk_functype t_1_lst t_2_lst)
	| label : forall (v_S : store) (C : context) (v_n : n) (instr_lst : (seq instr)) (admininstr_lst : (seq admininstr)) (t_2_lst : (seq valtype)) (t_1_opt : (option valtype)), 
		(Instrs_ok C instr_lst (mk_functype (option_to_list t_1_opt) t_2_lst)) ->
		(Admin_instrs_ok v_S ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := [:: ]; LABELS := [::t_1_opt]; context_RETURN := None |} @@ C) admininstr_lst (mk_functype [:: ] t_2_lst)) ->
		(v_n == (optionSize t_1_opt)) ->
		Admin_instr_ok v_S C (LABEL_ v_n instr_lst admininstr_lst) (mk_functype [:: ] t_2_lst)
	| Admin_instr_ok__frame : forall (v_S : store) (C : context) (v_n : n) (F : frame) (admininstr_lst : (seq admininstr)) (t_opt : (option valtype)), 
		(Thread_ok v_S (Some t_opt) F admininstr_lst t_opt) ->
		(v_n == (optionSize t_opt)) ->
		Admin_instr_ok v_S C (FRAME_ v_n F admininstr_lst) (mk_functype [:: ] (option_to_list t_opt))
	| weakening : forall (v_S : store) (C : context) (v_admininstr : admininstr) (t'_lst : (seq valtype)) (t'_1_lst : (seq valtype)) (t_lst : (seq valtype)) (t'_2_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Admin_instr_ok v_S C v_admininstr (mk_functype t_1_lst t_2_lst)) ->
		Admin_instr_ok v_S C v_admininstr (mk_functype (t'_lst ++ t'_1_lst) (t_lst ++ t'_2_lst))

with

Admin_instrs_ok : store -> context -> (seq admininstr) -> functype -> Prop :=
	| Admin_instrs_ok__empty : forall (v_S : store) (C : context), Admin_instrs_ok v_S C [:: ] (mk_functype [:: ] [:: ])
	| Admin_instrs_ok__seq : forall (v_S : store) (C : context) (admininstr_1 : admininstr) (admininstr_2_lst : (seq admininstr)) (t_1_lst : (seq valtype)) (t_3_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Admin_instr_ok v_S C admininstr_1 (mk_functype t_1_lst t_2_lst)) ->
		(Admin_instrs_ok v_S C admininstr_2_lst (mk_functype t_2_lst t_3_lst)) ->
		Admin_instrs_ok v_S C ([::admininstr_1] ++ admininstr_2_lst) (mk_functype t_1_lst t_3_lst)
	| Admin_instrs_ok__frame : forall (v_S : store) (C : context) (admininstr_lst : (seq admininstr)) (t_lst : (seq valtype)) (t_1_lst : (seq valtype)) (t_2_lst : (seq valtype)), 
		(Admin_instrs_ok v_S C admininstr_lst (mk_functype t_1_lst t_2_lst)) ->
		Admin_instrs_ok v_S C admininstr_lst (mk_functype (t_lst ++ t_1_lst) (t_lst ++ t_2_lst))
	| instrs : forall (v_S : store) (C : context) (instr_lst : (seq instr)) (v_functype : functype), 
		(Instrs_ok C instr_lst v_functype) ->
		Admin_instrs_ok v_S C (seq.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst) v_functype

with

Thread_ok : store -> (option resulttype) -> frame -> (seq admininstr) -> resulttype -> Prop :=
	| mk_Thread_ok : forall (v_S : store) (resulttype_opt : (option resulttype)) (F : frame) (admininstr_lst : (seq admininstr)) (t_opt : (option valtype)) (C : context), 
		(Frame_ok v_S F C) ->
		(Admin_instrs_ok v_S ({| context_TYPES := [:: ]; context_FUNCS := [:: ]; context_GLOBALS := [:: ]; context_TABLES := [:: ]; context_MEMS := [:: ]; context_LOCALS := [:: ]; LABELS := [:: ]; context_RETURN := resulttype_opt |} @@ C) admininstr_lst (mk_functype [:: ] (option_to_list t_opt))) ->
		Thread_ok v_S resulttype_opt F admininstr_lst t_opt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:194.1-194.43 *)
Inductive Config_ok : config -> resulttype -> Prop :=
	| mk_Config_ok : forall (v_S : store) (F : frame) (admininstr_lst : (seq admininstr)) (t_opt : (option valtype)), 
		(Store_ok v_S) ->
		(Thread_ok v_S None F admininstr_lst t_opt) ->
		Config_ok (mk_config (mk_state v_S F) admininstr_lst) t_opt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:205.1-205.48 *)
Inductive Func_extension : funcinst -> funcinst -> Prop :=
	| mk_Func_extension : forall (v_funcinst : funcinst), Func_extension v_funcinst v_funcinst.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:206.1-206.51 *)
Inductive Table_extension : tableinst -> tableinst -> Prop :=
	| mk_Table_extension : forall (n1 : u32) (m_opt : (option m)) (ref_1_lst : (seq funcaddr)) (n2 : u32) (ref_2_lst : (seq funcaddr)), 
		((n1 :> nat) <= (n2 :> nat)) ->
		Table_extension {| tableinst_TYPE := (mk_limits n1 (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)); REFS := (seq.map (fun (ref_1 : funcaddr) => (Some ref_1)) ref_1_lst) |} {| tableinst_TYPE := (mk_limits n2 (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)); REFS := (seq.map (fun (ref_2 : funcaddr) => (Some ref_2)) ref_2_lst) |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:207.1-207.45 *)
Inductive Mem_extension : meminst -> meminst -> Prop :=
	| mk_Mem_extension : forall (n1 : u32) (m_opt : (option m)) (b_1_lst : (seq byte)) (n2 : u32) (b_2_lst : (seq byte)), 
		((n1 :> nat) <= (n2 :> nat)) ->
		Mem_extension {| meminst_TYPE := (mk_limits n1 (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)); BYTES := b_1_lst |} {| meminst_TYPE := (mk_limits n2 (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)); BYTES := b_2_lst |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:208.1-208.54 *)
Inductive Global_extension : globalinst -> globalinst -> Prop :=
	| mk_Global_extension : forall (v_mut : mut) (t : valtype) (val_1 : val) (val_2 : val), 
		((v_mut == (Some MUT_MUT)) || (val_1 == val_2)) ->
		Global_extension {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := val_1 |} {| globalinst_TYPE := (mk_globaltype v_mut t); VALUE := val_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:209.1-209.43 *)
Inductive Store_extension : store -> store -> Prop :=
	| mk_Store_extension : forall (store_1 : store) (store_2 : store) (funcinst_1_lst : (seq funcinst)) (globalinst_1_lst : (seq globalinst)) (tableinst_1_lst : (seq tableinst)) (meminst_1 : meminst) (funcinst_1'_lst : (seq funcinst)) (funcinst_2_lst : (seq funcinst)) (globalinst_1'_lst : (seq globalinst)) (globalinst_2_lst : (seq globalinst)) (tableinst_1'_lst : (seq tableinst)) (tableinst_2_lst : (seq tableinst)) (meminst_1'_lst : (seq meminst)) (meminst_2_lst : (seq meminst)), 
		(store_1 == {| store_FUNCS := funcinst_1_lst; store_GLOBALS := globalinst_1_lst; store_TABLES := tableinst_1_lst; store_MEMS := [::meminst_1] |}) ->
		(store_2 == {| store_FUNCS := (funcinst_1'_lst ++ funcinst_2_lst); store_GLOBALS := (globalinst_1'_lst ++ globalinst_2_lst); store_TABLES := (tableinst_1'_lst ++ tableinst_2_lst); store_MEMS := (meminst_1'_lst ++ meminst_2_lst) |}) ->
		((|funcinst_1_lst|) == (|funcinst_1'_lst|)) ->
		List.Forall2 (fun (funcinst_1 : funcinst) (funcinst_1' : funcinst) => (Func_extension funcinst_1 funcinst_1')) funcinst_1_lst funcinst_1'_lst ->
		((|tableinst_1_lst|) == (|tableinst_1'_lst|)) ->
		List.Forall2 (fun (tableinst_1 : tableinst) (tableinst_1' : tableinst) => (Table_extension tableinst_1 tableinst_1')) tableinst_1_lst tableinst_1'_lst ->
		List.Forall (fun (meminst_1' : meminst) => (Mem_extension meminst_1 meminst_1')) meminst_1'_lst ->
		((|globalinst_1_lst|) == (|globalinst_1'_lst|)) ->
		List.Forall2 (fun (globalinst_1 : globalinst) (globalinst_1' : globalinst) => (Global_extension globalinst_1 globalinst_1')) globalinst_1_lst globalinst_1'_lst ->
		Store_extension store_1 store_2.

(* Mutual Recursion at: ../specification/wasm-1.0/B-soundness.spectec:236.1-236.32 *)
Inductive fun_types__of : (seq val) -> (seq valtype) -> Prop :=
	| fun_types__of_case_0 : fun_types__of [:: ] [:: ]
	| fun_types__of_case_1 : forall (numtype : valtype) (v_val_ : val_) (val'_lst : (seq val)) (var_0 : (seq valtype)), 
		(fun_types__of val'_lst var_0) ->
		fun_types__of ([::(val_CONST numtype v_val_)] ++ val'_lst) ([::numtype] ++ var_0).

(* Auxiliary Definition at: ../specification/wasm-1.0/B-soundness.spectec:240.1-241.32 *)
Definition is__const (v_admininstr : admininstr) : bool :=
	match v_admininstr return bool with
		| (admininstr_CONST v_valtype v_val_) => true
		| v_admininstr => false
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/B-soundness.spectec:245.1-246.41 *)
Inductive fun_const__list : (seq admininstr) -> bool -> Prop :=
	| fun_const__list_case_0 : fun_const__list [:: ] true
	| fun_const__list_case_1 : forall (v_admininstr : admininstr) (admininstr'_lst : (seq admininstr)) (var_0 : bool), 
		(fun_const__list admininstr'_lst var_0) ->
		fun_const__list ([::v_admininstr] ++ admininstr'_lst) ((is__const v_admininstr) && var_0).

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:251.6-251.21 *)
Inductive fun_terminal__form : (seq admininstr) -> bool -> Prop :=
	| fun_terminal__form_case_0 : forall (admininstr_lst : (seq admininstr)) (var_0 : bool), 
		(fun_const__list admininstr_lst var_0) ->
		fun_terminal__form admininstr_lst (var_0 || (admininstr_lst == [::admininstr_TRAP])).

(* Mutual Recursion at: ../specification/wasm-1.0/A-binary.spectec:20.1-22.82 *)
(* Mutual Recursion at: ../specification/wasm-1.0/A-binary.spectec:24.1-27.82 *)
(* Mutual Recursion at: ../specification/wasm-1.0/A-binary.spectec:361.1-386.38 *)
