From Stdlib Require Import String List Unicode.Utf8 NArith Arith QArith QArith.Qround.
From RecordUpdate Require Import RecordSet.
Import ListNotations.
Import RecordSetNotations.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
From WasmSpectec Require Import wasm.


(*** 

The following lemmas are simply simple facts that are needed for lists and predicates such as
Forall and Forall2. 

***)


Lemma id_succ_N : forall (i : nat), (N.of_nat (S i)) = N.succ (N.of_nat i).
Proof. intros i. induction i; eauto. Qed.

Lemma nth_is_same_as_seq_nth {T : Type} : forall (lst : list T) n x, List.nth n lst x = seq.nth x lst n.
Proof.
	move=> lst n.
	generalize dependent n.
	induction lst; move=> n; destruct n; eauto.
Qed.

(* Only use this if N.succ is in a match statement *)
Ltac resolve_Nsucc :=
	repeat match goal with
	| H : context [N.succ _] |- _ =>
		rewrite -N.succ_pos_spec in H;
		rewrite N.succ_pos_spec in H;
		rewrite N.pred_succ in H
	| _ : _ |- context [N.succ _] =>
		rewrite -N.succ_pos_spec;
		rewrite N.succ_pos_spec;
		rewrite N.pred_succ
	end.

Lemma length_same_split_zero: forall {A : Type} (l l2' : list A),
	seq.size l = (seq.size l + seq.size l2')%N ->
	seq.size l2' = 0.
Proof.
	move => A l l2' H.
	generalize dependent l2'.
	induction l; move => l2' H.
	- simpl in H. symmetry in H. apply H.
	- simpl in H. injection H as ?. apply IHl. apply H.
Qed.
	

Lemma length_app_both_nil: forall {A : Type} (l l' l1' l2': list A),
	seq.size l = seq.size l' ->
	seq.size l = seq.size l1' -> 
	l' = l1' ++ l2' -> 
	l2' = [].
Proof.
	move => A l l' l1' l2' HLength HLength2 HApp.

	apply f_equal with (f := fun t => seq.size t) in HApp.
	rewrite seq.size_cat in HApp.
	rewrite <- HLength in HApp.
	rewrite <- HLength2 in HApp.
	apply length_same_split_zero in HApp.
	rewrite <- List.length_zero_iff_nil => //=.
Qed.  

Lemma length_app_nil: forall {A : Type} (l' l1' l2': list A),
	seq.size l' = seq.size l1' -> 
	l' = l1' ++ l2' -> 
	l2' = [].
Proof.
	move => A l' l1' l2' HLength HApp.
	apply f_equal with (f := fun t => seq.size t) in HApp.
	rewrite seq.size_cat in HApp.
	rewrite <- HLength in HApp.
	apply length_same_split_zero in HApp.
	rewrite <- List.length_zero_iff_nil => //=.
Qed.

(* Lemma cvt_nat_N_lt {X : Type}: forall (i : N) (l : list X),  
	(N.to_nat i < length l)%coq_nat = (i < | l |)%BN.
Proof.
	move => i l.
	induction l.
	- simpl. rewrite lt_irrefl.
	eauto. *)

Lemma cvt_succ : forall (i : nat),
	N.of_nat (S i) = N.succ (N.of_nat i).
Proof. intros i. induction i; eauto. Qed.

Lemma cvt_succ' : forall (i : nat),
	N.pos (Pos.of_succ_nat i) = N.succ (N.of_nat i).
Proof. intros i. induction i; eauto. Qed.

Ltac simplNsucc :=
	repeat match goal with
	| _: _ |- context[?l [| ?i |]] =>
		rewrite /lookup_total;
		repeat rewrite N2Nat.inj_succ;
		simpl
	| H : context[?l [| ?i |]] |- _ =>
		rewrite /lookup_total in H;
		repeat rewrite N2Nat.inj_succ in H;
		simpl
	| _ : _ |- context[ (N.succ ?i)] =>
		repeat rewrite N2Nat.inj_succ;
		simpl
	| _ : _ |- _ => idtac
	end.

Ltac simplNsuccH H :=
	match type of H with
	| context[?l [| ?i |]] =>
		rewrite /lookup_total in H;
		repeat rewrite N2Nat.inj_succ in H;
		simpl
	| context[(N.succ ?i)] =>
		repeat rewrite N2Nat.inj_succ;
		simpl
	end.


Ltac simplNsizecons H :=
	match type of H with
	| context[(| cons ?x ?l |)] =>
		rewrite /size in H;
		repeat rewrite id_succ_N in H;
		simpl
	end.

Ltac simplNsizeconsgoal :=
	repeat match goal with
	| _ : _ |- context[(| cons ?x ?l |)] =>
		rewrite /size;
		repeat rewrite id_succ_N
	end.


Lemma Forall_size {A : Type} {_ : Inhabited A} (l : list A) (R : A -> Prop) :
      Forall R l -> (forall i, (i < |l|)%BN -> R (l [|i|])).
Proof.
	move => H i Hi.
	generalize dependent i.
	induction H; move => i Hi.
	- simpl in Hi. eapply N.nlt_0_r in Hi. exfalso. apply Hi.
	- simpl.
		destruct i using N.peano_ind.
		+ apply H.
		+ 
			simplNsucc.
			eapply IHForall.
			simplNsizecons Hi.
			apply N.succ_lt_mono in Hi. 
			apply Hi.
Qed.

Lemma Forall2_seq_size {A : Type} {B : Type} {_ : Inhabited A} {_ : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
	Forall2 R l l' -> |l| = |l'|.
Proof.
	move => H.
	induction H.
	- reflexivity.
	- simplNsizeconsgoal.
		f_equal.
		apply IHForall2.
Qed.

Lemma Forall2_size {A : Type} {B : Type} {_ : Inhabited A} {_ : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> (forall (i : N), (i < | l |)%BN -> R (l [|i|]) (l' [|i|])).
Proof.
	move => H.
	move => i H'.
	generalize dependent i. induction H; move => i HLength. 
	+ simpl in HLength. eapply N.nlt_0_r in HLength. exfalso. apply HLength.
	+ destruct i using N.peano_ind.
		+ apply H.
		+ 
			simplNsucc.
			simplNsizecons HLength.
			apply N.succ_lt_mono in HLength.
			apply IHForall2. apply HLength.
Qed.

Lemma Forall2_size2 {A : Type} {B : Type} {_ : Inhabited A} {_ : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> (forall (i : N), (i < | l' |)%BN -> R (l [|i|]) (l' [|i|])).
Proof.
	move => H.
	move => i H'.
	generalize dependent i. induction H; move => i HLength. 
	+ simpl in HLength. eapply N.nlt_0_r in HLength. exfalso. apply HLength.
	+ destruct i using N.peano_ind.
		+ apply H.
		+ 
			simplNsucc.
			simplNsizecons HLength.
			apply N.succ_lt_mono in HLength.
			apply IHForall2. apply HLength.
Qed.

Lemma Forall2_list_update_func2 {A B : Type} {C : Inhabited A} {D : Inhabited B}
	(l : list A) (l' : list B) (R : A -> B -> Prop) (i : N) (f : B -> B) (x : A) (y : B):
	Forall2 R l l' ->
	lookup_total l i = x -> 
	lookup_total l' i = y -> 
	R x (f y) -> Forall2 R l (list_update_func l' i f).
Proof.
	generalize dependent l'.
	generalize dependent i.
	generalize dependent x.
	generalize dependent y.
	generalize dependent f.
	induction l; move => f0 y0 x0 i0 l0' HForall HLx HLy HR.
	- inversion HForall. destruct i0 => //=.
	- destruct l0' => //=; inversion HForall => //=; subst.
		destruct i0 using N.peano_ind => //=.
		- apply Forall2_cons_iff; split.
			- by unfold lookup_total in HR.
			- apply H4.
		- resolve_Nsucc. 
			apply Forall2_cons_iff; split.
			- apply H2.
			- rewrite /lookup_total in HR.
				rewrite N2Nat.inj_succ in HR.
				eapply IHl; eauto.
Qed.

Lemma in_same_as_In (X : eqType) : forall (c : X) (l : seq X),
	c \in l <->
	In c l.
Proof.
	move => c l.
	split.
	(* -> *)
	- move=> Hin.
		induction l.
		- discriminate.
		- simpl. simpl in Hin. 
			rewrite -cat1s in Hin. 
			rewrite mem_cat in Hin. 
			move/orP in Hin.
			destruct Hin.
			- rewrite inE in H.
				move/eqP in H.
				left.
				symmetry.
				apply H.
			- right.
				by apply IHl.
	(* <- *)
	- move=> HIn.
		induction l.
		- unfold In in HIn. 
			exfalso. 
			apply HIn.
		- rewrite -cat1s.
			rewrite mem_cat.
			apply/orP.
			unfold In in HIn. destruct HIn.
			- left.
				rewrite inE.
				apply/eqP.
				symmetry.
				apply H.
			- right.
				by apply IHl.
Qed.

Fixpoint In2 {A B : Type} (x : A) (y : B) (l : list A) (l' : list B) : Prop :=
    match l, l' with
      | [], [] => False
	  | [], b :: ms => False
	  | a :: ns, [] => False
      | a :: ns, b :: ms => (a = x /\ b = y) \/ In2 x y ns ms
    end.

Lemma In2_split: forall {A B : Type} (x : A) (y : B) (l : list A) (l' : list B),
	In2 x y l l' -> In x l /\ In y l'.
Proof.
	move => A B x y l l' HIn.
	generalize dependent x.
	generalize dependent y.
	generalize dependent l'.
	induction l; move => l0' y0 x0 HIn => //=.
	- destruct l0' => //=.
	- destruct l0' => //=.
		simpl in HIn.
		destruct HIn. 
		- destruct H. split; by left.
		- apply IHl in H. destruct H. split; by right.
Qed.	

Lemma list_update_length: forall {A : Type} (l : list A) (i : N) (x : A),
	| (list_update l i x) | = | l |.
Proof.
	move => A l i x.
	f_equal.
	generalize dependent l.
	generalize dependent x.
	induction i using N.peano_ind.
	- destruct l => //=.
	- destruct l.
		- eauto. 
		- destruct i => //=.
			- rewrite IHi; eauto.
			- f_equal. rewrite Pos.pred_N_succ. apply IHi.
Qed.

Lemma list_update_length_func: forall {A : Type} (l : list A) (f : A -> A) (i : N),
	| (list_update_func l i f) | = | l |.
Proof.
	move => A l f i.
	f_equal.
	generalize dependent l.
	generalize dependent f.
	induction i using N.peano_ind; move => f l.
	- destruct l => //=.
	- destruct l => //=.
		destruct i => //=.
		- rewrite IHi; eauto.
		- f_equal. rewrite Pos.pred_N_succ. apply IHi.
Qed.

Lemma list_slice_update_length: forall {A : Type} (l l': list A) (i n: N),
	| (list_slice_update l i n l') | = | l |.
Proof.
	move => A l l' i n.
	f_equal.
	move : n i l'.
	induction l; move => n i l'; auto.
	destruct i; destruct l'; destruct n; simpl; auto.
Qed.

Lemma split_append_last : forall {A : Type} (z : list A) (y : list A) (i : A) (j : A),
	@app _ z [i] = @app _ y [j] ->
	z = y /\ i = j.
Proof.
	move => A z y i j H.
	apply app_inj_tail.
	apply H.
Qed.

Lemma split_cons : forall {A : Type} (j : A) (k : A),
	[j; k] = @app _ [j] [k].
Proof.
	move => A j k.
	done.
Qed.

Lemma split_append_1 : forall {A : Type} (z : list A) (i : A) (j : A),
	@app _ z [i] = [j] ->
	z = [] /\ i = j.
Proof.
	move => A z i j H.
	apply app_eq_unit in H.
	destruct H as [[H1 H2] | [H1 H2]].
		- split. apply H1. injection H2 as H3. apply H3.
		- discriminate.
Qed.

Lemma split_append_2 : forall {A : Type} (z : list A) (i : A) (j : A) (k : A),
	@app _ z [i] = [j; k] ->
	z = [j] /\ i = k.
Proof.
	move => A z i j k H.
	apply split_append_last.
	apply H.
Qed.

Lemma split_append_left_1 : forall {A : Type} (z : list A) (i : A) (j : A),
	@app _ [i] z = [j] ->
	z = [] /\ i = j.
Proof.
	move => A z i j H.
	apply app_eq_unit in H.
	destruct H as [[H1 H2] | [H1 H2]].
		- discriminate. 
		- split. apply H2. injection H1 as H3. apply H3.
Qed.


Lemma empty_append {A : Type}: forall (i : list A) (j : list A),
	[] = @app _ i j ->
	i = [] /\ j = [].
Proof.
	move => i j H.
	simpl.
	induction i.
		- rewrite -> app_nil_l in H. split. reflexivity. symmetry in H. apply H.
		- discriminate.
Qed. 

Lemma lookup_app: forall {A : Type} {B : Inhabited A} (l l' : list A) (n : N),
	(n < |l|)%BN ->
	l [| n |] = (l ++ l') [| n |].
Proof.
	move => A B l l' n.
	move: l l'.
	induction n using N.peano_ind; move => l l' H.
	- destruct l => //=.
	- destruct l => //=.
		- eapply N.nlt_0_r in H. exfalso. apply H.
	  - unfold lookup_total. 
			simplNsucc.
	  	apply IHn. 
			simplNsizecons H.
	  	apply N.succ_lt_mono in H. apply H.
Qed.


(* These lemmas are simply just issues with it recognizing the ssreflect lemmas. I'll probably remove them later *)
Lemma app_left_single_nil: forall {A : Type} (x : A), [x] = @app _ [] [x].
Proof. done. Qed.

Lemma app_right_nil: forall {A : Type} (x : list A), x = @app _ x [].
Proof. move => A x. rewrite app_nil_r. done. Qed.

Lemma app_left_nil: forall {A : Type} (x : list A), x = @app _ [] x.
Proof. move => A x. rewrite app_nil_l. done. Qed.

Lemma _append_option_none: forall {A : Type} (c : option A) ,
	_append c None = c.
Proof.
	move => A c.
	unfold _append. unfold Append_Option. unfold option_append.
	induction c => //.
Qed.

Lemma _append_option_none_left: forall {A : Type} (c : option A) ,
	_append None c = c.
Proof.
	move => A c.
	unfold _append. unfold Append_Option. unfold option_append.
	destruct c => //.
Qed.

Lemma _append_some_left: forall {A : Type} (b : A) (c : option A) ,
	_append (Some b) c = (Some b).
Proof. reflexivity. Qed.
(* 
Lemma list_update_same_unchanged: forall {X : Type} {Y : Inhabited X} (l: list X) e i,
    (lookup_total l i) = e ->
	(i < seq.size l)%coq_nat ->
    list_update l i e = l.
Proof.
	move => X Y l e i.
	generalize dependent l. generalize dependent e.
	induction i; move => e l HLookup HLT.
	- destruct l => //=. by f_equal.
	- destruct l => //=.
		f_equal. apply IHi. unfold lookup_total. unfold lookup_total in HLookup. simpl in HLookup. apply HLookup.
		by apply Nat.succ_lt_mono.
Qed. *)

(* Lemma list_update_map: forall {X Y:Type} (l:list X) i val {f: X -> Y},
    (i < seq.size l)%coq_nat ->
    List.map f (list_update l i val) = list_update (List.map f l) i (f val).
Proof.
	move => X Y l i val.
	generalize dependent l. generalize dependent val.
	induction i; move => val l f HSize => //=.
  	- by destruct l => //=.
  	- destruct l => //=.
    	f_equal.
    	apply IHi.
		simpl in HSize. by apply Nat.succ_lt_mono.
Qed. *)


Lemma app_cat : forall {A : Type} (xs ys: seq A),
  (xs ++ ys)%list = xs ++ ys.
Proof. auto. Qed.

Definition prepend_local (v_C : context) (t_lst : seq valtype) :=
	({| context_TYPES := []; context_FUNCS := []; 
	  context_GLOBALS := []; context_TABLES := []; context_MEMS := []; 
		context_ELEMS := []; context_DATAS := []; 
		context_LOCALS := t_lst; LABELS := []; context_RETURN := None|}) @@
	v_C.

Definition prepend_label (v_C: context) (v_t: resulttype) :=
({| context_TYPES := []; context_FUNCS := []; context_GLOBALS := []; context_TABLES := []; context_MEMS := []; context_ELEMS := []; context_DATAS := []; context_LOCALS := []; LABELS := [v_t]; context_RETURN := None |} @@ v_C).

Definition prepend_return (v_C: context) (v_t: resulttype) :=
({| context_TYPES := []; context_FUNCS := []; context_GLOBALS := []; context_TABLES := []; context_MEMS := []; context_ELEMS := []; context_DATAS := []; context_LOCALS := []; LABELS := []; context_RETURN := Some v_t |} @@ v_C).

Definition append_local (v_C : context) (t_lst : seq valtype) :=
	v_C @@
	({| context_TYPES := []; context_FUNCS := []; 
	  context_GLOBALS := []; context_TABLES := []; context_MEMS := []; 
		context_ELEMS := []; context_DATAS := []; 
		context_LOCALS := t_lst; LABELS := []; context_RETURN := None|}).

Definition append_label (v_C : context) (t_lst : resulttype) :=
	v_C @@
	({| context_TYPES := []; context_FUNCS := []; 
	  context_GLOBALS := []; context_TABLES := []; context_MEMS := []; 
		context_ELEMS := []; context_DATAS := []; 
		context_LOCALS := []; LABELS := [t_lst]; context_RETURN := None|}).

Definition append_return (v_C : context) (v_t : resulttype) :=
	v_C @@
	({| context_TYPES := []; context_FUNCS := []; 
	  context_GLOBALS := []; context_TABLES := []; context_MEMS := []; 
		context_ELEMS := []; context_DATAS := []; 
		context_LOCALS := []; LABELS := []; context_RETURN := Some v_t|}).
		
Lemma lookup_label_0: forall v_C (t: resulttype),
lookup_total (LABELS (prepend_label v_C t)) 0 = t.
Proof.
	eauto.
Qed.

Lemma lookup_label_1: forall v_C (t: resulttype) (n : N),
lookup_total (LABELS (prepend_label v_C t)) (n + 1) =
lookup_total (LABELS v_C) (n).
Proof.
	move=> v_C t n.
	unfold lookup_total.
	unfold LABELS, prepend_label, _append, Append_context, _append_context.
	unfold _append, Append_List_.
	unfold LABELS.
	rewrite <- app_cat.
	rewrite <- cat1s.
	rewrite N.add_1_r.
	simplNsucc.
	reflexivity.
Qed.

Lemma add_sub : forall a b,
	(a + b - b)%N = a.
Proof.
	move => a b.
	Search (_ + _ - _).
	by eapply Nat.add_sub.
Qed.

Lemma add_sub' : forall a b,
	(a + b - a)%N = b.
Proof.
	move => a b.
	rewrite addnC.
	by eapply Nat.add_sub.
Qed.

Lemma add_subBN : forall a b,
	(a + b - b)%BN = a.
Proof.
	move => a b.
	by eapply N.add_sub.
Qed.

Lemma add_subBN' : forall a b,
	(a + b - a)%BN = b.
Proof.
	move => a b.
	rewrite N.add_comm.
	by eapply N.add_sub.
Qed.

Lemma sizecat' : forall {A: Type} (l l': seq A),
	(|l ++ l'| = (|l| + |l'|)%BN).
Proof.
	move => A l l'.
	induction l.
		- reflexivity.
		- simplNsizeconsgoal. 
			rewrite IHl.
			rewrite N.add_succ_l.
			reflexivity.
Qed.

Lemma sizecat_le1: forall {A: Type} (l l': seq A),
	(|l| <= |l ++ l'|)%BN.
Proof.
	move => A l l'.
	rewrite sizecat'.
	eapply N.le_add_r.
Qed.

Lemma sizecat_le2: forall {A: Type} (l l': seq A),
	(|l'| <= |l ++ l'|)%BN.
Proof.
	move => A l l'.
	rewrite sizecat'.
	eapply N.le_add_l.
Qed.

Lemma drop_size_cat : forall {A: Type} (x y : seq A),
  seq.drop (size x) (x ++ y) = y.
Proof.
  move => A x y.
  rewrite drop_cat.
  rewrite ltnn.
  rewrite subnn.
  by rewrite drop0.
Qed.

Lemma take_size_cat : forall {A: Type} (x y : seq A),
  seq.take (size x) (x ++ y) = x.
Proof.
  move => A x y.
  rewrite take_cat.
  rewrite ltnn.
  rewrite subnn.
  rewrite take0.
  apply cats0.
Qed.

Lemma sizeN_inj: forall {A: Type} {B: Type} (l: seq A) (l': seq B),
	| l | = | l' | -> size l = size l'.
Proof.
	move => A B l l' H.
	move: l' H.
	induction l; move=> l' H; destruct l' => //=.
	- simplNsizecons H.
		apply N.succ_inj in H.
		specialize (IHl l' H).
		by rewrite IHl.
Qed.	

Lemma size_eq_cat: forall A (l1 l2 l1' l2': list A),
  | l1 | = | l2 | ->
  l1' ++ l1 = l2' ++ l2 ->
  l1' = l2' /\ l1 = l2.
Proof.
  move=> A l1 l2 l1' l2' Hsize Hcat.
  
  have Hsize_cat: | (l1' ++ l1) | = | (l2' ++ l2) | by rewrite Hcat.
  rewrite !sizecat' in Hsize_cat.
  
  have Hsize': |l1'|= |l2'|.
  {
		rewrite Hsize in Hsize_cat.
		by apply N.add_cancel_r in Hsize_cat.
  }
  
  have Htake: take (size l1') (l1' ++ l1) = take (size l1') (l2' ++ l2).
  { by rewrite Hcat. }
  
  rewrite take_size_cat // in Htake.
	eapply sizeN_inj in Hsize'.
  rewrite Hsize' take_size_cat // in Htake.
  
  split; first by exact Htake.
  
  have Hdrop: seq.drop (size l1') (l1' ++ l1) = seq.drop (size l1') (l2' ++ l2).
  { by rewrite Hcat. }
  
  rewrite drop_size_cat // in Hdrop.
  rewrite Hsize' drop_size_cat // in Hdrop.
Qed.

Lemma size_cons {X : Type} : forall x (s : seq X), 
	seq.size (x :: s) = S (seq.size s).
Proof. eauto. Qed.
