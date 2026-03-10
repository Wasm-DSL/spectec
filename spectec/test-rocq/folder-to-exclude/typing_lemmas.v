From Stdlib Require Import String List Unicode.Utf8 NArith Arith Logic.Eqdep.
Require Import Stdlib.Program.Equality.
From RecordUpdate Require Import RecordSet.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics subtyping.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.

Definition fun_nat__u32 : nat -> u32 := mk_uN.
Definition fun_u32__nat : u32 -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__u32 : nat >-> u32.
Coercion fun_u32__nat : u32 >-> nat.

Definition fun_nat__labelidx : nat -> labelidx := mk_uN.
Definition fun_labelidx__nat : labelidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__labelidx : nat >-> labelidx.
Coercion fun_labelidx__nat : labelidx >-> nat.

Definition fun_nat__localidx : nat -> localidx := mk_uN.
Definition fun_localidx__nat : localidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__localidx : nat >-> localidx.
Coercion fun_localidx__nat : localidx >-> nat.

Definition fun_nat__globalidx : nat -> globalidx := mk_uN.
Definition fun_globalidx__nat : globalidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__globalidx : nat >-> globalidx.
Coercion fun_globalidx__nat : globalidx >-> nat.

Definition fun_nat__memidx : nat -> memidx := mk_uN.
Definition fun_memidx__nat : memidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__memidx : nat >-> memidx.
Coercion fun_memidx__nat : memidx >-> nat.


Definition fun_nat__tableidx : nat -> tableidx := mk_uN.
Definition fun_tableidx__nat : tableidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__tableidx : nat >-> tableidx.
Coercion fun_tableidx__nat : tableidx >-> nat.

Definition fun_nat__idx : nat -> idx := mk_uN.
Definition fun_idx__nat : idx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__idx : nat >-> idx.
Coercion fun_idx__nat : idx >-> nat.

Definition fun_res_list__list :
forall T, res_list T -> list T := fun _ x => match x with
	| mk_list l => l
end.
Definition fun_list__res_list : forall T, list T -> res_list T := fun T => mk_list T.
Coercion fun_res_list__list : res_list >-> list.
Coercion fun_list__res_list : list >-> res_list.

Definition functype_from_lists (t1s t2s : list valtype) : functype :=
  mk_functype t1s t2s.

Notation "tf1 :-> tf2" :=
(mk_functype (mk_list _ tf1) (mk_list _ tf2)) (at level 40).

Definition upd_label C labs :=
	C <| LABELS := labs |>.

Definition upd_local C locs :=
	C <| context_LOCALS := locs |>.

Definition upd_return C ret :=
	C <| context_RETURN := ret |>.

Definition upd_local_return C loc ret :=
	upd_return (upd_local C loc) ret. 

Definition upd_local_label_return C loc lab ret := 
	upd_return (upd_label (upd_local C loc) lab) ret.


(*

Ltac fold_upd_context :=
	lazymatch goal with
	| |- context [upd_local (upd_return ?C ?ret) ?loc] =>
		replace (upd_local (upd_return C ret) loc) with
			(upd_local_return C ret loc); try by destruct C
	| |- context [upd_return (upd_local ?C ?ret) ?loc] =>
		replace (upd_return (upd_local C ret) loc) with
			(upd_local_return C ret loc); try by destruct C
	end.
	*)
	  
Lemma upd_label_overwrite: forall C l1 l2,
	upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Lemma upd_label_is_same_as_append: forall v_C lab,
	upd_label v_C (lab @@ (LABELS v_C)) = {| context_TYPES := []; context_FUNCS := []; context_GLOBALS := []; context_TABLES := []; context_MEMS := []; context_ELEMS := [];
	context_DATAS := []; context_LOCALS := []; LABELS := lab; context_RETURN := None |} @@ v_C.
Proof.
	move => v_C lab. reflexivity.
Qed.

Lemma upd_local_is_same_as_append: forall v_C loc,
	upd_local v_C (loc @@ (context_LOCALS v_C))  = {| context_TYPES := []; context_FUNCS := []; context_GLOBALS := []; context_TABLES := []; context_MEMS := []; context_ELEMS := [];
	context_DATAS := []; context_LOCALS := loc; LABELS := []; context_RETURN := None |} @@ v_C.
Proof.
	move => v_C loc. reflexivity.
Qed.

Lemma upd_local_return_is_same_as_append: forall v_C loc ret,
	upd_local_return v_C (loc @@ (context_LOCALS v_C)) (ret @@ (context_RETURN v_C)) 
	= {|
		context_TYPES := [];
		context_FUNCS := [];
		context_GLOBALS := [];
		context_TABLES := [];
		context_MEMS := [];
		context_ELEMS := [];
		context_DATAS := [];
		context_LOCALS := loc;
		LABELS := [];
		context_RETURN := ret
	|} @@ v_C.
Proof. reflexivity. Qed.


Lemma upd_return_is_same_as_append: forall v_C ret,
	upd_return v_C (ret @@ (context_RETURN v_C)) =
	{| context_TYPES := []; context_FUNCS := []; context_GLOBALS := []; context_TABLES := []; context_MEMS := []; context_ELEMS := [];
	context_DATAS := []; context_LOCALS := []; LABELS := []; context_RETURN := ret |} @@ v_C.
Proof.
	move => v_C ret. reflexivity.
Qed.

Lemma upd_label_unchanged: forall C lab,
    LABELS C = lab ->
    upd_label C lab = C.
Proof.
	move => C lab HLab.
	rewrite -HLab. unfold upd_label. by destruct C.
Qed.

Lemma upd_label_unchanged_typing: forall v_S v_C v_admininstrs v_funcontext_type,
    Admin_instrs_ok v_S v_C v_admininstrs v_funcontext_type <->
    Admin_instrs_ok v_S (upd_label v_C (LABELS v_C)) v_admininstrs v_funcontext_type.
Proof.
	move => s C es tf.
	split.
	- move => HType.
		by rewrite upd_label_unchanged.
	- move => HType.
		simpl in HType.
		remember (LABELS C) as lab.
		symmetry in Heqlab.
		apply upd_label_unchanged in Heqlab.
		rewrite <- Heqlab => //=. 
Qed.

Definition instr_of (ai: admininstr) : (option instr) :=
match ai with
  | (admininstr_NOP) => Some((NOP))
  | (admininstr_UNREACHABLE) => Some((UNREACHABLE))
  | (admininstr_DROP) => Some((DROP))
  | ((admininstr_SELECT v_0)) => Some((SELECT v_0))
  | ((admininstr_BLOCK v_0 v_1)) => Some((BLOCK v_0 v_1))
  | ((admininstr_LOOP v_0 v_1)) => Some((LOOP v_0 v_1))
  | ((admininstr_IFELSE v_0 v_1 v_2)) => Some((IFELSE v_0 v_1 v_2))
  | ((admininstr_BR v_0)) => Some((BR v_0))
  | ((admininstr_BR_IF v_0)) => Some((BR_IF v_0))
  | ((admininstr_BR_TABLE v_0 v_1)) => Some((BR_TABLE v_0 v_1))
  | ((admininstr_CALL v_0)) => Some((CALL v_0))
  | ((admininstr_CALL_INDIRECT v_0 v_1)) => Some((CALL_INDIRECT v_0 v_1))
  | (admininstr_RETURN) => Some((RETURN))
  | ((admininstr_CONST v_0 v_1)) => Some((CONST v_0 v_1))
  | ((admininstr_UNOP v_0 v_1)) => Some((UNOP v_0 v_1))
  | ((admininstr_BINOP v_0 v_1)) => Some((BINOP v_0 v_1))
  | ((admininstr_TESTOP v_0 v_1)) => Some((TESTOP v_0 v_1))
  | ((admininstr_RELOP v_0 v_1)) => Some((RELOP v_0 v_1))
  | ((admininstr_CVTOP v_0 v_1 v_2)) => Some((CVTOP v_0 v_1 v_2))
  | ((admininstr_EXTEND v_0 v_1)) => Some((instr_EXTEND v_0 v_1))
  | ((admininstr_VCONST v_0 v_1)) => Some((VCONST v_0 v_1))
  | ((admininstr_VVUNOP v_0 v_1)) => Some((VVUNOP v_0 v_1))
  | ((admininstr_VVBINOP v_0 v_1)) => Some((VVBINOP v_0 v_1))
  | ((admininstr_VVTERNOP v_0 v_1)) => Some((VVTERNOP v_0 v_1))
  | ((admininstr_VVTESTOP v_0 v_1)) => Some((VVTESTOP v_0 v_1))
  | ((admininstr_VUNOP v_0 v_1)) => Some((VUNOP v_0 v_1))
  | ((admininstr_VBINOP v_0 v_1)) => Some((VBINOP v_0 v_1))
  | ((admininstr_VTESTOP v_0 v_1)) => Some((VTESTOP v_0 v_1))
  | ((admininstr_VRELOP v_0 v_1)) => Some((VRELOP v_0 v_1))
  | ((admininstr_VSHIFTOP v_0 v_1)) => Some((VSHIFTOP v_0 v_1))
  | ((admininstr_VBITMASK v_0)) => Some((VBITMASK v_0))
  | ((admininstr_VSWIZZLE v_0)) => Some((VSWIZZLE v_0))
  | ((admininstr_VSHUFFLE v_0 v_1)) => Some((VSHUFFLE v_0 v_1))
  | ((admininstr_VSPLAT v_0)) => Some((VSPLAT v_0))
  | ((admininstr_VEXTRACT_LANE v_0 v_1 v_2)) => Some((VEXTRACT_LANE v_0 v_1 v_2))
  | ((admininstr_VREPLACE_LANE v_0 v_1)) => Some((VREPLACE_LANE v_0 v_1))
  | ((admininstr_VEXTUNOP v_0 v_1 v_2)) => Some((VEXTUNOP v_0 v_1 v_2))
  | ((admininstr_VEXTBINOP v_0 v_1 v_2)) => Some((VEXTBINOP v_0 v_1 v_2))
  | ((admininstr_VNARROW v_0 v_1 v_2)) => Some((VNARROW v_0 v_1 v_2))
  | ((admininstr_VCVTOP v_0 v_1 v_2)) => Some((VCVTOP v_0 v_1 v_2))
  | ((admininstr_REF_NULL v_0)) => Some((REF_NULL v_0))
  | ((admininstr_REF_FUNC v_0)) => Some((REF_FUNC v_0))
  | (admininstr_REF_IS_NULL) => Some((REF_IS_NULL))
  | ((admininstr_LOCAL_GET v_0)) => Some((LOCAL_GET v_0))
  | ((admininstr_LOCAL_SET v_0)) => Some((LOCAL_SET v_0))
  | ((admininstr_LOCAL_TEE v_0)) => Some((LOCAL_TEE v_0))
  | ((admininstr_GLOBAL_GET v_0)) => Some((GLOBAL_GET v_0))
  | ((admininstr_GLOBAL_SET v_0)) => Some((GLOBAL_SET v_0))
  | ((admininstr_TABLE_GET v_0)) => Some((TABLE_GET v_0))
  | ((admininstr_TABLE_SET v_0)) => Some((TABLE_SET v_0))
  | ((admininstr_TABLE_SIZE v_0)) => Some((TABLE_SIZE v_0))
  | ((admininstr_TABLE_GROW v_0)) => Some((TABLE_GROW v_0))
  | ((admininstr_TABLE_FILL v_0)) => Some((TABLE_FILL v_0))
  | ((admininstr_TABLE_COPY v_0 v_1)) => Some((TABLE_COPY v_0 v_1))
  | ((admininstr_TABLE_INIT v_0 v_1)) => Some((TABLE_INIT v_0 v_1))
  | ((admininstr_ELEM_DROP v_0)) => Some((ELEM_DROP v_0))
  | ((admininstr_LOAD v_0 v_1 v_2)) => Some((LOAD v_0 v_1 v_2))
  | ((admininstr_STORE v_0 v_1 v_2)) => Some((STORE v_0 v_1 v_2))
  | ((admininstr_VLOAD v_0 v_1 v_2)) => Some((VLOAD v_0 v_1 v_2))
  | ((admininstr_VLOAD_LANE v_0 v_1 v_2 v_3)) => Some((VLOAD_LANE v_0 v_1 v_2 v_3))
  | ((admininstr_VSTORE v_0 v_1)) => Some((VSTORE v_0 v_1))
  | ((admininstr_VSTORE_LANE v_0 v_1 v_2 v_3)) => Some((VSTORE_LANE v_0 v_1 v_2 v_3))
  | (admininstr_MEMORY_SIZE) => Some((MEMORY_SIZE))
  | (admininstr_MEMORY_GROW) => Some((MEMORY_GROW))
  | (admininstr_MEMORY_FILL) => Some((MEMORY_FILL))
  | (admininstr_MEMORY_COPY) => Some((MEMORY_COPY))
  | ((admininstr_MEMORY_INIT v_0)) => Some((MEMORY_INIT v_0))
  | ((admininstr_DATA_DROP v_0)) => Some((DATA_DROP v_0))
  | _ => None
  end.

Notation "tf1 :-> tf2" :=
(mk_functype (mk_list _ tf1) (mk_list _ tf2)) (at level 40).

Lemma instrs_composition_typing_single: forall v_C v_instrs v_instr t1s t2s,
	Instrs_ok v_C ([::v_instr] ++ v_instrs) ( t1s :-> t2s ) ->
	exists t3s, Instrs_ok v_C v_instrs ( t3s :-> t2s ) /\
				Instrs_ok v_C [v_instr] ( t1s :-> t3s ).
Proof.
	move => v_C v_instrs v_instr t1s t2s HType.
	dependent induction HType.
	-
	  exists t_2_lst.
	  split; auto.
	  eapply (res_seq _ v_instr [] t1s t_2_lst t_2_lst); eauto.
	  + rewrite -(cats0 t_2_lst).
	    eapply (Instrs_ok__frame _ _ t_2_lst [] []).
		apply empty.
	- specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists t3s.
	  split;
	  eapply sub; eauto;
    apply resulttype_sub_refl.
	- specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (t_lst ++ t3s).
	  split;
	  eapply Instrs_ok__frame; eauto.
Qed.

Lemma ais_composition_typing_single: forall v_S v_C v_ais v_ai t1s t2s,
	Admin_instrs_ok v_S v_C ([v_ai] ++ v_ais) ( t1s :-> t2s ) ->
	exists t3s, Admin_instrs_ok v_S v_C v_ais ( t3s :-> t2s ) /\
				Admin_instrs_ok v_S v_C [v_ai] ( t1s :-> t3s ).
Proof.
	move => v_S v_C v_ais v_ai t1s t2s HType.
	dependent induction HType.
	{ (* seq *)
	  exists t_2_lst.
	  split.
		* auto.
	  * eapply (Admin_instrs_ok__seq) with (t_2_lst := t_2_lst); eauto.
		  rewrite -(cats0 t_2_lst).
		  eapply Admin_instrs_ok__frame.
			by apply Admin_instrs_ok__empty.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists t3s.
	  split; eapply Admin_instrs_ok__sub; eauto; by apply resulttype_sub_refl.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (t_lst ++ t3s).
	  split; by eapply Admin_instrs_ok__frame.
	}
	{ (* instrs *)
	  move: v_ais v_ai x t1s t2s H.
	  induction instr_lst;
	  move => v_ais v_ai H t1s t2s Hinstr.
	  + inversion H.
	  + rewrite -> map_cons in H.
		apply instrs_composition_typing_single in Hinstr as [t3s [H1 H2]].
	  exists t3s.
		injection H as H; subst.
		split.
		* eapply instrs; auto.
		* assert ([ admininstr_instr a] =
		  ListDef.map [eta admininstr_instr] [ a]).
		  { auto. }
		  rewrite H.
		  eapply instrs.
			apply H2.
	}
Qed.

Lemma instrs_empty_typing : forall v_C t1s t2s,
	Instrs_ok v_C ([]) ( t1s :-> t2s ) <->
	( t1s <ts: t2s ).
Proof.
  move => v_C t1s t2s.
  split.
  - move => Hempty.
    dependent induction Hempty; subst.
	+ apply resulttype_sub_refl.
	+ destruct_list_eq x.
	+ eapply resulttype_sub_trans.
	apply H.
	eapply resulttype_sub_trans.
	apply IHHempty; auto.
	apply H0.
	eapply resulttype_sub_app.
	apply resulttype_sub_refl.
	apply IHHempty; auto.
  - move: t1s.
    move => t1s H.
	eapply (sub _ _ _ _ t2s t2s).
	+ rewrite -(cats0 t2s).
	  apply Instrs_ok__frame.
	  apply empty.
	  apply H.
	  apply resulttype_sub_refl.
Qed.

Lemma ais_empty_typing : forall v_S v_C t1s t2s,
	Admin_instrs_ok v_S v_C ([]) ( t1s :-> t2s ) <->
	( t1s <ts: t2s ).
Proof.
  move => v_S v_C t1s t2s.
  split.
  {
	move => Hempty.
	dependent induction Hempty; subst.
	+ apply resulttype_sub_refl.
	+ destruct_list_eq x.
	+ specialize (IHHempty _ _ erefl erefl). 
	  eapply resulttype_sub_trans.
	  eapply H.
	  eapply resulttype_sub_trans.
	  eapply IHHempty.
	  eapply H0.
	+ eapply resulttype_sub_app.
	  apply resulttype_sub_refl.
	  apply IHHempty; auto.
	+ destruct instr_lst.
	  * by apply instrs_empty_typing in H.
	  * discriminate.
  }
  {
	move => Hsub.
	assert ([] = (ListDef.map [eta admininstr_instr] [])). { auto. }
	rewrite H.
    apply instrs.
	by apply instrs_empty_typing.
  }
Qed.


Definition ai_principal_typing (v_S: store) (v_C: context) v_ai v_ft : Prop :=
match v_ai with
	| admininstr_NOP => v_ft = ([] :-> [])
	| admininstr_UNREACHABLE => True
	| admininstr_DROP => exists t1, v_ft = ([t1] :-> [])
	| (admininstr_SELECT (Some [t_lst])) => v_ft = ([t_lst; t_lst; valtype_I32] :-> [t_lst])
	| (admininstr_SELECT None) => exists (t t': valtype),
		v_ft = ([t; t; valtype_I32] :-> [t]) /\
		t <tv: t' /\
		((exists nt: numtype, t' = valtype_numtype nt) \/ (exists vt: vectype, t' = valtype_vectype vt))
	| (admininstr_SELECT _) => False
	| (admininstr_BLOCK v_bt v_instr) =>
	    exists t t',
	    v_ft = (t :-> t') /\
		(Blocktype_ok v_C v_bt (t :-> t')) /\
		(Instrs_ok (prepend_label v_C t') v_instr (t :-> t'))
	| (admininstr_LOOP v_bt v_instr) =>
	    exists t t',
		v_ft = (t :-> t') /\
	    (Blocktype_ok v_C v_bt (t :-> t')) /\
		(Instrs_ok (prepend_label v_C t) v_instr (t :-> t'))
	| (admininstr_IFELSE v_bt v_instrs1 v_instrs2) =>
	    exists (t t': seq valtype),
	  	v_ft = ((t ++ [valtype_I32]) :-> t') /\
		(Blocktype_ok v_C v_bt (t :-> t')) /\
		Instrs_ok (prepend_label v_C t') v_instrs1 (t :-> t') /\
		Instrs_ok (prepend_label v_C t') v_instrs2 (t :-> t')
	| (admininstr_BR v_l) =>
	    exists t t' t_lst,
	    v_ft = (t ++ t_lst) :-> t' /\
	    ((proj_uN_0 v_l) < (List.length (LABELS v_C))) /\
		((proj_list_0 valtype (lookup_total (LABELS v_C) (proj_uN_0 v_l))) = t_lst)
	| (admininstr_BR_IF v_l) =>
	  exists t,
	    v_ft = ((t ++ [valtype_I32]) :-> t) /\
	    ((proj_uN_0 v_l) < (List.length (LABELS v_C))) /\
		((proj_list_0 valtype (lookup_total (LABELS v_C) (proj_uN_0 v_l))) = t)
	| (admininstr_BR_TABLE v_l v_l') =>
      exists t t' t_lst,
	    v_ft = ((t ++ t_lst ++ [valtype_I32]) :-> t') /\
	    List.Forall (fun (v_l : labelidx) => ((proj_uN_0 v_l) < (List.length (LABELS v_C)))) (v_l) /\
		List.Forall (fun (v_l : labelidx) => (Resulttype_sub (mk_list _ t_lst) (lookup_total (LABELS v_C) (proj_uN_0 v_l)))) (v_l) /\
		((proj_uN_0 v_l') < (List.length (LABELS v_C))) /\
		(Resulttype_sub (mk_list _ t_lst) (lookup_total (LABELS v_C) (proj_uN_0 v_l')))
	| (admininstr_CALL v_x) =>
		exists t t',
		v_ft = (t :-> t') /\
		((proj_uN_0 v_x) < (List.length (context_FUNCS v_C))) /\
		((lookup_total (context_FUNCS v_C) (proj_uN_0 v_x)) = (t :-> t'))
	| (admininstr_CALL_INDIRECT v_x v_y) =>
		exists t t' v_lim,
		v_ft = ((t ++ [valtype_I32]) :-> t') /\
		((proj_uN_0 v_x) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x)) = (mk_tabletype v_lim FUNCREF)) /\
		((proj_uN_0 v_y) < (List.length (context_TYPES v_C))) /\
		((lookup_total (context_TYPES v_C) (proj_uN_0 v_y)) = (t :-> t'))
	| admininstr_RETURN =>
	  exists t t' t_lst,
	    v_ft = ((t ++ t_lst) :-> t') /\
		((context_RETURN v_C) = (Some (mk_list _ t_lst))) /\
		Instr_ok v_C RETURN ((t ++ t_lst) :-> t')
	| (admininstr_CONST v_nt n) =>
		wf_num_ v_nt n /\ 
	  v_ft = ([] :-> ([valtype_numtype v_nt]))
	| (admininstr_UNOP v_nt _) =>
	  v_ft = ([valtype_numtype v_nt] :-> [valtype_numtype v_nt])
	| (admininstr_BINOP v_nt _) =>
	  v_ft = ([valtype_numtype v_nt; valtype_numtype v_nt] :-> [valtype_numtype v_nt])
	| (admininstr_TESTOP v_nt _) =>
	  v_ft = ([valtype_numtype v_nt] :-> [valtype_I32])
	| (admininstr_RELOP v_nt v_1) =>
	  v_ft = ([valtype_numtype v_nt; valtype_numtype v_nt] :-> [valtype_I32])
	| (admininstr_CVTOP v_nt_1 v_nt_2 _) =>
	  v_ft = ([valtype_numtype v_nt_2] :-> [valtype_numtype v_nt_1])
	| (admininstr_VCONST (v_vectype) _ ) =>
	  v_ft = ([] :-> [valtype_vectype v_vectype])
	(*| (admininstr_VVUNOP v_0 v_1)
	| (admininstr_VVBINOP v_0 v_1)
	| (admininstr_VVTERNOP v_0 v_1)
	| (admininstr_VVTESTOP v_0 v_1)
	| (admininstr_VUNOP v_0 v_1)
	| (admininstr_VBINOP v_0 v_1)
	| (admininstr_VTESTOP v_0 v_1)
	| (admininstr_VRELOP v_0 v_1)
	| (admininstr_VSHIFTOP v_0 v_1)
	| (admininstr_VBITMASK v_0)
	| (admininstr_VSWIZZLE v_0)
	| (admininstr_VSHUFFLE v_0 v_1)
	| (admininstr_VSPLAT v_0)
	| (admininstr_VEXTRACT_LANE v_0 v_1 v_2)
	| (admininstr_VREPLACE_LANE v_0 v_1)
	| (admininstr_VEXTUNOP v_0 v_1 v_2)
	| (admininstr_VEXTBINOP v_0 v_1 v_2)
	| (admininstr_VNARROW v_0 v_1 v_2)
	| (admininstr_VCVTOP v_0 v_1 v_2)*)
	| (admininstr_REF_NULL (v_rt)) =>
	  v_ft = ([] :-> [valtype_reftype v_rt])
	| (admininstr_REF_FUNC v_x) =>
	  exists v_fty, v_ft = ([] :-> [valtype_FUNCREF]) /\
		((proj_uN_0 v_x) < (List.length (context_FUNCS v_C))) /\
		((lookup_total (context_FUNCS v_C) (proj_uN_0 v_x)) = v_fty)
	| admininstr_REF_IS_NULL =>
	  exists v_rt: reftype,
	  v_ft = ([valtype_reftype v_rt] :-> [valtype_I32])
	| (admininstr_LOCAL_GET v_x) =>
	  exists t_lst, v_ft = ([] :-> [t_lst]) /\
	    ((proj_uN_0 v_x) < (List.length (context_LOCALS v_C))) /\
		((lookup_total (context_LOCALS v_C) (proj_uN_0 v_x)) = t_lst)
	| (admininstr_LOCAL_SET v_x) =>
	  exists t_lst, v_ft = ([t_lst] :-> []) /\
	    ((proj_uN_0 v_x) < (List.length (context_LOCALS v_C))) /\
		((lookup_total (context_LOCALS v_C) (proj_uN_0 v_x)) = t_lst)
	| (admininstr_LOCAL_TEE v_x) =>
	  exists t_lst, v_ft = ([t_lst] :-> [t_lst]) /\
	    ((proj_uN_0 v_x) < (List.length (context_LOCALS v_C))) /\
	    ((lookup_total (context_LOCALS v_C) (proj_uN_0 v_x)) = t_lst)
	| (admininstr_GLOBAL_GET v_x) =>
	  exists t_lst v_mut, v_ft = ([] :-> [t_lst]) /\
	  	((proj_uN_0 v_x) < (List.length (context_GLOBALS v_C))) /\
		((lookup_total (context_GLOBALS v_C) (proj_uN_0 v_x)) = (mk_globaltype v_mut t_lst))
	| (admininstr_GLOBAL_SET v_x) =>
	  exists t_lst, v_ft = ([t_lst] :-> []) /\
	  	((proj_uN_0 v_x) < (List.length (context_GLOBALS v_C))) /\
		((lookup_total (context_GLOBALS v_C) (proj_uN_0 v_x)) = (mk_globaltype (Some MUT_MUT) t_lst))
	| (admininstr_TABLE_GET v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([valtype_I32] :-> [(valtype_reftype v_rt)]) /\
	  	((proj_uN_0 v_x) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x)) = (mk_tabletype v_lim v_rt))
	| (admininstr_TABLE_SET v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([valtype_I32; valtype_reftype v_rt] :-> []) /\
	  	((proj_uN_0 v_x) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x)) = (mk_tabletype v_lim v_rt))
	| (admininstr_TABLE_SIZE v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([] :-> [valtype_I32]) /\
	  	((proj_uN_0 v_x) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x)) = (mk_tabletype v_lim v_rt))
	| (admininstr_TABLE_GROW v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([valtype_reftype v_rt; valtype_I32] :-> [valtype_I32]) /\
	  	((proj_uN_0 v_x) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x)) = (mk_tabletype v_lim v_rt))
	| (admininstr_TABLE_FILL v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([valtype_I32; valtype_reftype v_rt; valtype_I32] :-> []) /\
	  	((proj_uN_0 v_x) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x)) = (mk_tabletype v_lim v_rt))
	| (admininstr_TABLE_COPY v_x_1 v_x_2) =>
	  exists (v_rt: reftype) v_lim_1 v_lim_2, v_ft = ([valtype_I32; valtype_I32; valtype_I32] :-> []) /\
	  	((proj_uN_0 v_x_1) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x_1)) = (mk_tabletype v_lim_1 v_rt))/\
	  	((proj_uN_0 v_x_2) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x_2)) = (mk_tabletype v_lim_2 v_rt))
	| (admininstr_TABLE_INIT v_x_1 v_x_2) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([valtype_I32; valtype_I32; valtype_I32] :-> []) /\
	  	((proj_uN_0 v_x_1) < (List.length (context_TABLES v_C))) /\
		((lookup_total (context_TABLES v_C) (proj_uN_0 v_x_1)) = (mk_tabletype v_lim v_rt))/\
	  	((proj_uN_0 v_x_2) < (List.length (context_ELEMS v_C))) /\
		((lookup_total (context_ELEMS v_C) (proj_uN_0 v_x_2)) = v_rt)
	| (admininstr_ELEM_DROP v_x) =>
	  exists (v_rt: reftype), v_ft = ([] :-> []) /\
	  	((proj_uN_0 v_x) < (List.length (context_ELEMS v_C))) /\
		((lookup_total (context_ELEMS v_C) (proj_uN_0 v_x)) = v_rt)
	| (admininstr_LOAD v_nt None v_memarg) =>
	  exists v_mt, v_ft = ([valtype_I32] :-> [(valtype_numtype v_nt)]) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt) /\
		((res_size (valtype_numtype v_nt)) <> None) /\
		(((2 ^ (proj_uN_0 (ALIGN v_memarg))) : nat) <= (((the (res_size (valtype_numtype v_nt))) : nat) / (8 : nat)))
	| (admininstr_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg) =>
	  exists v_mt, v_ft = ([valtype_I32] :-> [(valtype_I32)]) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt) /\
		(((2 ^ (proj_uN_0 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat)))
	| (admininstr_LOAD I64 (Some (mk_loadop__0 Inn_I64 (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg) =>
	  exists v_mt, v_ft = ([valtype_I32] :-> [valtype_I64]) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt) /\
		(((2 ^ (proj_uN_0 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat)))
	| (admininstr_LOAD F32 (Some _) _) => False
	| (admininstr_LOAD F64 (Some _) _) => False
	| (admininstr_STORE v_nt None v_memarg) =>
	  exists v_mt, v_ft = ([valtype_I32; (valtype_numtype v_nt)] :-> []) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt) /\
		((res_size (valtype_numtype v_nt)) <> None) /\
		(((2 ^ (proj_uN_0 (ALIGN v_memarg))) : nat) <= (((the (res_size (valtype_numtype v_nt))) : nat) / (8 : nat)))
	(* | (admininstr_STORE F32 (Some _) _) => False
	| (admininstr_STORE F64 (Some _) _) => False *)
	| (admininstr_STORE v_Inn (Some (mk_sz v_M)) v_memarg) =>
	  exists v_mt, v_ft = ([valtype_I32; (valtype_numtype v_Inn)] :-> []) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt) /\
		(((2 ^ (proj_uN_0 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat)))
	(*| (admininstr_VLOAD v_0 v_1 v_2)
	| (admininstr_VLOAD_LANE v_0 v_1 v_2 v_3)
	| (admininstr_VSTORE v_0 v_1)
	| (admininstr_VSTORE_LANE v_0 v_1 v_2 v_3)*)
	| admininstr_MEMORY_SIZE =>
	  exists v_mt, v_ft = ([] :-> [valtype_I32]) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt)
	| admininstr_MEMORY_GROW =>
	  exists v_mt, v_ft = ([valtype_I32] :-> [valtype_I32]) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt)
	| admininstr_MEMORY_FILL =>
	  exists v_mt, v_ft = ([valtype_I32; valtype_I32; valtype_I32] :-> []) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt)
	| admininstr_MEMORY_COPY =>
	  exists v_mt, v_ft = ([valtype_I32; valtype_I32; valtype_I32] :-> []) /\
	  	(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt)
	| (admininstr_MEMORY_INIT v_x) =>
	  exists v_mt, v_ft = ([valtype_I32; valtype_I32; valtype_I32] :-> []) /\
		(0 < (List.length (context_MEMS v_C))) /\
		((lookup_total (context_MEMS v_C) 0) = v_mt) /\
		((proj_uN_0 v_x) < (List.length (context_DATAS v_C))) /\
		((lookup_total (context_DATAS v_C) (proj_uN_0 v_x)) = OK)
	| (admininstr_DATA_DROP v_x) =>
	  v_ft = ([] :-> []) /\
		((proj_uN_0 v_x) < (List.length (context_DATAS v_C))) /\
		((lookup_total (context_DATAS v_C) (proj_uN_0 v_x)) = OK)
	| (admininstr_REF_FUNC_ADDR v_funcaddr) =>
	  exists v_functype,
	  v_ft = ([] :-> [valtype_FUNCREF]) /\
	  (Externaddrs_ok v_S (externaddr_FUNC v_funcaddr) (FUNC v_functype))
	| (admininstr_REF_HOST_ADDR _) =>
	  v_ft = ([] :-> [valtype_EXTERNREF])
	| (CALL_ADDR v_funcaddr) =>
		exists t t', v_ft = (t :-> t') /\
		(Externaddrs_ok v_S (externaddr_FUNC v_funcaddr) (FUNC (t :-> t')))
	| (LABEL_ v_n v_instrs v_ais) =>
	  exists t t',
	  v_ft = ([] :-> t') /\
	  (Instrs_ok v_C v_instrs (t :-> t')) /\
	  (Admin_instrs_ok v_S (prepend_label v_C t) v_ais ([] :-> t')) /\
	  (v_n = (length t))
	| (FRAME_ v_n v_F v_ais) =>
	  exists t,
	    v_ft = ([] :-> t) /\
	    (Thread_ok v_S (Some (mk_list _ t)) v_F v_ais (mk_list _ t)) /\
		(v_n = (List.length t))
	| admininstr_TRAP => True
	| (admininstr_EXTEND v_0 v_1) => False
	| _ => True
end.

(* v_ft must be the subtype of v_instr's type *)
Definition instr_principal_typing (v_C : context) v_instr v_ft : Prop :=
ai_principal_typing default_val v_C (admininstr_instr v_instr) v_ft.

Lemma instr_typing_inversion: forall (v_C: context) v_instr t1s t2s,
  Instr_ok v_C v_instr (t1s :-> t2s) ->
  instr_principal_typing v_C v_instr (t1s :-> t2s).
Proof.
	move=> v_C v_instr t1s t2s HType.
	inversion HType; subst.
	all: eq_to_prop; unfold instr_principal_typing;
		unfold ai_principal_typing;
		unfold admininstr_instr.
	all: try exact.
	all: try repeat eexists; eauto.
	{
	 (* SELECT *)
	  solve [eq_to_prop; destruct_disjunctions;
	  repeat eexists; eauto].
	}
	{
		(* TABLE Init *)
		rewrite H2. rewrite H6; reflexivity.
	}
	{ (* LOAD None *)
		destruct nt; repeat eexists; eauto.
	}
	{ (* Load Some *)
		destruct v_Inn; simpl; try repeat eexists; eauto.
	}
	(*
	{ (* STORE None *)
		destruct v_Inn; eauto.
	}*)
	{ (* STORE Some *)
		destruct v_Inn; 
		eexists; eauto.
	}
Qed.


Lemma ai_typing_inversion: forall (v_S: store) (v_C: context) v_ai t1s t2s,
	Admin_instr_ok v_S v_C v_ai (t1s :-> t2s) ->
	exists t1s' t2s',
	ai_principal_typing v_S v_C v_ai (t1s' :-> t2s') /\
	((t1s' :-> t2s') <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C v_ai t1s t2s.
	move => HType.
	dependent induction HType.
	{ (* instr *)
		destruct v_instr.
		all: unfold ai_principal_typing;
		unfold admininstr_instr; eq_to_prop.
		57: { (* LOAD *)
			inversion H; subst. eq_to_prop.
			{
				eexists [valtype_I32], [valtype_numtype v_numtype]; split.
				destruct v_numtype;
				exists mt;
				repeat split; auto.
				eapply instrtype_sub_refl.
			}
			{
				destruct v_Inn.
				{
					exists [valtype_I32], [valtype_I32].
					split.
					2: eapply instrtype_sub_refl.
					simpl.
					exists mt; subst; auto.
				}
				{
					exists [valtype_I32], [valtype_I64].
					split.
					2: eapply instrtype_sub_refl.
					inversion H. exists mt; subst; clear H; auto.
				}
			}
		}
		all: inversion H; subst.
		all: do 2 eexists; eq_to_prop.
		all: try (split;
		[
			first [
				solve exact
			|
				solve [simpl; eauto]
			|
				solve [destruct_disjunctions; repeat eexists; eauto]
			|
				solve [destruct v_numtype; repeat eexists; eauto]
			]
		|
				exists []; do 3 eexists;
				split; [ |split; [ |split; [ |split]]];
				try apply resulttype_sub_refl;
				simpl; try exact;
				try destruct v_Inn; rewrite /numtype_Inn; eexists; eauto
	  	]).
		{ (* BR *)
			split.
			exists t_1_lst, t2s, t_lst; split; eauto.
			apply instrtype_sub_refl.
		}
		{ (* TABLE INIT *)
			split.
			2: apply instrtype_sub_refl.
			exists rt, lim; split; eauto.	
		}
	}
	{ (* trap *)
	  exists t1s, t2s.
	  split.
	  - unfold ai_principal_typing; exact.
	  - apply instrtype_sub_refl.
	}
	{ (* ref_extern *)
	  exists [], [valtype_EXTERNREF].
	  split.
	  - unfold ai_principal_typing; auto.
	  - apply instrtype_sub_refl. 
	}
	{ (* ref *)
	  exists [], [valtype_FUNCREF].
	  split.
	  - unfold ai_principal_typing;
	    do 2 eexists; eauto.
	  - apply instrtype_sub_refl.
	}
	{ (* call_addr *)
	  eexists _, _.
	  split.
	  - unfold ai_principal_typing; repeat eexists; eauto.
	  - apply instrtype_sub_refl.
	}
	{ (* label *)
	  eexists _, _.
		eq_to_prop.
	  split.
	  - unfold ai_principal_typing; repeat eexists; eauto.
	  - apply instrtype_sub_refl.
	}
	{ (* frame *) (* TODO *)
	  eexists _, _.
		eq_to_prop.
	  split.
	  - unfold ai_principal_typing.
		eexists.
		split; [ |split]; eauto.
	  - apply instrtype_sub_refl.
	}
	{ (* weakening *)
		specialize (IHHType _ _ erefl) as [t1' [t2' [Hpt His]]].
		exists t1', t2'.
		split. exact.
		eapply instrtype_sub_trans.
		eapply His.
		unfold instrtype_sub.
		eexists
		(t'_lst),
		(t_lst),
		(t'_1_lst),
		(t'_2_lst).
		split; [ |split; [ |split; [ |split]]]; auto.
	}
Qed.

Lemma instrs_single_typing_inversion: forall (v_C: context) v_instr t1s t2s,
Instrs_ok v_C [v_instr] (t1s :-> t2s) ->
exists t1s_sup t2s_sub,
	Instr_ok v_C v_instr (t1s_sup :-> t2s_sub) /\
	(t1s_sup :-> t2s_sub) <ti: (t1s :-> t2s).
Proof.
	move=> v_C v_instr t1s t2s HType.
	dependent induction HType.
	{ (* seq *)
	  destruct_list_eq x; subst.
	  apply instrs_empty_typing in HType.
	  exists t1s, t_2_lst.
	  split. auto.
	  unfold instrtype_sub.
	  exists [], [], t1s, t2s.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split. by apply resulttype_sub_refl. 
		auto.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ erefl erefl) as [t1s_sup [t2s_sub [Hpt Hsub]]].
	  exists t1s_sup, t2s_sub.
	  split. auto.
	  eapply instrtype_sub_trans.
	  apply Hsub.
	  unfold instrtype_sub.
	  exists [], [], t1s, t2s.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split. by apply H.
	  by apply H0.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ erefl erefl) as [t1s_sup [t2s_sub [Hpt Hsub]]].
	  exists t1s_sup, t2s_sub.
	  split. auto.
	  eapply instrtype_sub_trans.
	  apply Hsub.
	  unfold instrtype_sub.
	  exists t_lst, t_lst, t_1_lst, t_2_lst.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split; by apply resulttype_sub_refl.
	}
Qed.

Lemma ais_single_typing_inversion' : forall (v_S: store) (v_C: context) v_ai t1s t2s,
	Admin_instrs_ok v_S v_C [v_ai] (t1s :-> t2s) ->
	Admin_instr_ok v_S v_C v_ai (t1s :-> t2s).
Proof.
	move=> v_S v_C v_ai t1s t2s HType.
	dependent induction HType.
	- destruct_list_eq x; subst.
	  eapply ais_empty_typing in HType.
	  eapply (weakening _ _ _ [] _ []).
	  eapply H.
	  eapply resulttype_sub_refl.
		eapply resulttype_sub_refl.
	  eapply HType.
	- eapply (weakening _ _ _ [] _ []); eauto.
	  eapply resulttype_sub_refl.
	- eapply (weakening _ _ _ t_lst _ t_lst); eauto;
	  eapply resulttype_sub_refl.
	- destruct instr_lst. discriminate.
	  simpl in x.
	  destruct_list_eq x; subst.
	  destruct instr_lst. 2: discriminate.
	  eapply instrs_single_typing_inversion in H
	    as [t1s_sup [t2s_sub [Hi Hsub]]].
	  unfold instrtype_sub in Hsub.
	  destruct Hsub as [ts_sub [ts [ts1 [ts2 [
		H1 [H2 [H3 [H4 H5]]]
	  ]]]]]; subst.
	  eapply (weakening _ _ _ ); eauto.
	  eapply Admin_instr_ok__instr.
	  eapply Hi.
Qed.



Lemma ais_single_typing_inversion: forall (v_S: store) (v_C: context) v_ai t1s t2s,
Admin_instrs_ok v_S v_C [v_ai] (t1s :-> t2s) ->
exists t1s_sup t2s_sub,
	ai_principal_typing v_S v_C v_ai (t1s_sup :-> t2s_sub) /\
	(t1s_sup :-> t2s_sub) <ti: (t1s :-> t2s).
Proof.
	move=> v_S v_C v_ai t1s t2s HType.
	dependent induction HType.
	{ (* seq *)
	  destruct_list_eq x; subst.
	  apply ais_empty_typing in HType.
	  eapply ai_typing_inversion in H as [t1s' [t2s' [Hpt Hsub]]].
	  exists (t1s'), (t2s').
	  split. auto.
	  eapply instrtype_sub_trans. eapply Hsub.
	  unfold instrtype_sub.
	  exists [], [], t1s, t2s.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split. auto.
	  by apply resulttype_sub_refl.
		apply HType.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ erefl erefl) as [t1s_sup [t2s_sub [Hpt Hsub]]].
	  exists t1s_sup, t2s_sub.
	  split. auto.
	  eapply instrtype_sub_trans.
	  apply Hsub.
	  unfold instrtype_sub.
	  exists [], [], t1s, t2s.
	  split; auto.
	  split; auto.
	  split; auto.
	  by apply resulttype_sub_refl.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ erefl erefl) as [t1s_sup [t2s_sub [Hpt Hsub]]].
	  exists t1s_sup, t2s_sub.
	  split. auto.
	  eapply instrtype_sub_trans.
	  apply Hsub.
	  unfold instrtype_sub.
	  exists t_lst, t_lst, t_1_lst, t_2_lst.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split; by apply resulttype_sub_refl.
	}
	{ (* instrs *)
	  destruct instr_lst. discriminate x.
	  simpl in x.
	  destruct_list_eq x;
	  apply map_eq_nil in x_body;
	  subst.

	  eapply instrs_single_typing_inversion in H
	    as [t1s_sup [t2s_sub [Hi H1]]].
	  eapply instr_typing_inversion in Hi.
	  unfold instr_principal_typing in Hi.
	  exists t1s_sup, t2s_sub.
	  split. 2: auto.
	  destruct i;
	  auto.
	}
Qed.

Lemma ais_single_ref_typing_inversion: forall v_S v_C (v_ref: wasm.ref) ts1 ts2,
  Admin_instrs_ok v_S v_C [admininstr_ref v_ref] (ts1 :-> ts2) ->
  exists (t: reftype), 
	(([] :-> [valtype_reftype t]) <ti: (ts1 :-> ts2)) /\
   	Ref_ok v_S v_ref t.
Proof.
	move => v_S v_C v_ref ts1 ts2 HType.
	eapply ais_single_typing_inversion in HType as [t1 [t2 [Hai Hsub]]].
	destruct v_ref; unfold ai_principal_typing, admininstr_ref in Hai.
	2: destruct Hai as [v_ft [Hai Heok]].
	all: inversion Hai; subst.
	- exists v_reftype. split; auto. by constructor.
	- exists FUNCREF. split; auto. econstructor; eauto.
	- exists EXTERNREF. split; auto. econstructor; eauto.
Qed.

Lemma val_ref_null_is_ref: forall rt,
	val_REF_NULL rt = val_ref (ref_REF_NULL rt).
Proof. auto. Qed.

Lemma ais_single_val_typing_inversion: forall v_S v_C (v_val: wasm.val) ts1 ts2,
  Admin_instrs_ok v_S v_C [admininstr_val v_val] (ts1 :-> ts2) ->
  exists t, 
	(([] :-> [t]) <ti: (ts1 :-> ts2)) /\
   	Val_ok v_S v_val t.
Proof.
	move => v_S v_C v_val ts1 ts2 HType.
	eapply ais_single_typing_inversion in HType as [t1 [t2 [Hai Hsub]]].
	destruct v_val; unfold ai_principal_typing, admininstr_val in Hai.
	4: destruct Hai as [v_ft [Hai Heok]].
	1: destruct Hai as [Hwf Hai].
	all: inversion Hai; subst.
	- exists (valtype_numtype v_numtype). split; auto. by constructor.
	- exists (valtype_vectype v_vectype). split; auto. by constructor.
	- exists (valtype_reftype v_reftype). split; auto.
		rewrite val_ref_null_is_ref.
	  eapply Val_ok__reftype.
	  econstructor.
	- exists (valtype_reftype FUNCREF). split; auto.
		assert (val_REF_FUNC_ADDR v_funcaddr = val_ref (REF_FUNC_ADDR v_funcaddr)). { auto. }
		rewrite H.
	  eapply Val_ok__reftype.
	  econstructor. eauto.
	- exists (valtype_reftype EXTERNREF). split; auto.
		assert (val_REF_HOST_ADDR v_hostaddr = val_ref (REF_HOST_ADDR v_hostaddr)). { auto. }
	  rewrite H.
		eapply Val_ok__reftype.
	  econstructor.
Qed.

Lemma instrs_seq_typing_inversion: forall (v_C: context) v_instrs v_instr t1s t2s,
Instrs_ok v_C ([v_instr] ++ v_instrs) (t1s :-> t2s) ->
exists t3s, Instrs_ok v_C v_instrs (t3s :-> t2s) /\
	Instrs_ok v_C [v_instr] (t1s :-> t3s).
Proof.
	move=> v_C v_instrs v_instr t1s t2s HType.
	dependent induction HType.
	{ (* seq *)
	  exists t_2_lst.
	  split. auto.
	  eapply res_seq.
		apply H.
	  apply instrs_empty_typing.
	  apply resulttype_sub_refl.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists t3s. split.
	  - eapply sub.
	    eapply H1. apply resulttype_sub_refl. eauto.
	  - eapply sub.
	    eapply H2. eauto. apply resulttype_sub_refl.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (t_lst ++ t3s). split.
	  - eapply Instrs_ok__frame. auto.
	  - eapply Instrs_ok__frame. auto.
	}
Qed.

Lemma ais_seq_typing_inversion: forall (v_S: store) (v_C: context) v_ais v_ai t1s t2s,
Admin_instrs_ok v_S v_C ([v_ai] ++ v_ais) (t1s :-> t2s) ->
exists t3s, Admin_instrs_ok v_S v_C v_ais (t3s :-> t2s) /\
	Admin_instrs_ok v_S v_C [v_ai] (t1s :-> t3s).
Proof.
	move=> v_S v_C v_ais v_ai t1s t2s HType.
	dependent induction HType.
	{ (* seq *)
	  exists t_2_lst.
	  split. auto.
	  eapply Admin_instrs_ok__seq.
		- apply H.
	  - apply ais_empty_typing.
	    apply resulttype_sub_refl.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (t3s).
	  split; eapply Admin_instrs_ok__sub; eauto; apply resulttype_sub_refl.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (t_lst ++ t3s).
	  split; eapply Admin_instrs_ok__frame; auto.
	}
	{ (* instrs *)
	  destruct instr_lst.
	  - simpl in x. destruct_list_eq x.
	  - rewrite map_cons in x.
	    destruct_list_eq x; subst.
		eapply instrs_seq_typing_inversion in H as [t3s [H1 H2]].
		exists t3s. split.
		- eapply instrs. auto.
		- assert (ListDef.map [eta admininstr_instr] [i] =
		  [admininstr_instr i]).
		  { auto. }
			rewrite -H.
			eapply instrs.
			auto.
	}
Qed.

Lemma ais_composition_typing: forall (v_S: store) (v_C: context) v_ais1 v_ais2 t1s t2s,
Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (t1s :-> t2s) ->
exists t3s, Admin_instrs_ok v_S v_C v_ais1 (t1s :-> t3s) /\
	Admin_instrs_ok v_S v_C v_ais2 (t3s :-> t2s).
Proof.
	move=> v_S v_C v_ais1 v_ais2 t1s t2s HType.
	move: v_ais2 t1s t2s HType.
	induction v_ais1.
	{
		move=> v_ais2 t1s t2s HType.
		exists t1s.
		split.
		eapply ais_empty_typing.
		eapply resulttype_sub_refl.
		rewrite cat0s in HType. auto.
	}
	{
		move=> v_ais2 t1s t2s HType.
		rewrite -cat1s in HType.
		rewrite -catA in HType.
		eapply ais_seq_typing_inversion in HType as [t3s [H1 H2]].
		eapply IHv_ais1 in H1 as [t3s' [H3 H4]].
		exists t3s'.
		split. auto.
		rewrite -cat1s.
		eapply Admin_instrs_ok__seq.
		eapply ais_single_typing_inversion'.
		eauto.
		apply H3.
		apply H4.
	}
Qed.

Ltac do_instr_typing_inversion H :=
  lazymatch type of H with
  | Instr_ok _ ?v_instr _ =>
    let Hpt := fresh "Hpt" in
    eapply instr_typing_inversion in H as Hpt;
	clear H
  | _ => idtac
end.

Ltac do_instrs_typing_inversion H :=
  lazymatch type of H with
  | Instrs_ok _ [] _ =>
    eapply instrs_empty_typing in H
  | Instrs_ok _ [?v_instr] ( ?t1s :-> ?t2s ) =>
    let t1s_sup := fresh t1s "_sup" in
	let t2s_sub := fresh t2s "_sub" in
	let Hinstr := fresh "Hinstr" in
	let Hsub := fresh "Hsub" in
    eapply instrs_single_typing_inversion in H
	  as [t1s_sup [t2s_sub [Hinstr Hsub]]]
  | Instrs_ok _ [?v_instr1; ?v_instr2] _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
    eapply (instrs_seq_typing_inversion _ [v_instr1] v_instr2) in H
	  as [t3s [H1 H2]]
  | Instrs_ok _ (?v_instrs ++ [?v_instr]) _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
    eapply (instrs_seq_typing_inversion _ v_instrs v_instr) in H
	  as [t3s [H1 H2]];
	do_instrs_typing_inversion H1
  | Instrs_ok _ _ (_ :: _) _ =>
    repeat rewrite -(cat1s _ (_ :: _)) in H;
	repeat rewrite !catA in H;
	do_instrs_typing_inversion H
  | _ => idtac
  end.

Ltac do_ai_typing_inversion H :=
  lazymatch type of H with
  | Admin_instr_ok _ _ _ _ =>
    let Hpt := fresh "Hpt" in
	let t1s' := fresh "t1s'" in
	let t2s' := fresh "t2s'" in
	let Hsub := fresh "Hsub" in
    eapply ai_typing_inversion in H as [t1s' [t2s' [Hpt Hsub]]]
  | _ => idtac
  end.

Ltac do_ais_typing_inversion H :=
  lazymatch type of H with
  | Admin_instrs_ok _ _ [] _ =>
    eapply ais_empty_typing in H
  | Admin_instrs_ok _ _ [map admininstr_val ?v_vals] ( ?t1s :-> ?t2s ) =>
    let t1s_sup := fresh t1s "_sup" in
	let t2s_sub := fresh t2s "_sub" in
	let Hai := fresh "Hai" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_typing_inversion in H
	  as [t1s_sup [t2s_sub [Hai Hsub]]]
  | Admin_instrs_ok _ _ [admininstr_val ?v_val] ( ?t1s :-> ?t2s ) =>
    let t := fresh "t" in
	let HValok := fresh "HValok" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_val_typing_inversion in H
	  as [t [Hsub HValok]]
  | Admin_instrs_ok _ _ [?v_ai] ( ?t1s :-> ?t2s ) =>
    let t1s_sup := fresh t1s "_sup" in
	let t2s_sub := fresh t2s "_sub" in
	let Hai := fresh "Hai" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_typing_inversion in H
	  as [t1s_sup [t2s_sub [Hai Hsub]]]
  | Admin_instrs_ok _ _ [?v_ai1; ?v_ai2] _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
    eapply (ais_seq_typing_inversion _ _ [v_ai1] v_ai2) in H
	  as [t3s [H1 H2]]
  | Admin_instrs_ok _ _ (?v_ais ++ [?v_ai]) _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
    eapply (ais_seq_typing_inversion _ _ v_ais v_ai) in H
	  as [t3s [H1 H2]];
	do_ais_typing_inversion H1
  | Admin_instrs_ok _ _ (_ :: (_ :: _)) _ =>
    repeat rewrite -(cat1s _ (_ :: _)) in H;
	repeat rewrite !catA in H;
	do_ais_typing_inversion H
  | Admin_instrs_ok _ _ (_ ++ _) _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
	eapply ais_composition_typing in H as [t3s [H1 H2]]
  | _ => idtac
  end.

Ltac typing_inversion H :=
  destruct_functypes;
  try rewrite !app_cat in H;
  lazymatch type of H with
  | Admin_instrs_ok _ _ _ _ =>
    do_ais_typing_inversion H
  | Admin_instr_ok _ _ _ _ =>
    do_ai_typing_inversion H
  | Instrs_ok _ _ _ =>
    do_instrs_typing_inversion H
  | Instr_ok _ _ _ =>
    do_instr_typing_inversion H
  | _ => idtac
end.

Lemma ai_val_principal_typing_inversion: forall (v_S: store) (v_C: context) (v_val: wasm.val) t1s t2s,
ai_principal_typing v_S v_C (admininstr_val v_val) (t1s :-> t2s) ->
exists t_lst,
	([] = t1s) /\ ([t_lst] = t2s).
Proof.
  move=> v_S v_C v_val t1s t2s HType.
  destruct v_val;
  [
	exists v_numtype |
	exists v_vectype |
	exists v_reftype |
	exists valtype_FUNCREF |
	exists VALTYPE_EXTERNREF
  ].
  all: unfold ai_principal_typing, admininstr_val in HType; 
  inversion HType; auto.
  destruct HType as [v_functype [H1 H2]].
  inversion H1; auto.
Qed.


Ltac unfold_instrtype_sub H :=
  destruct_functypes;
  match type of H with
  | ((?ts11 :-> ?ts12) <ti: (?ts21 :-> ?ts22)) =>
	let ts := fresh "ts" in
	let ts_sub := fresh ts "_sub" in
	let ts11_sub := fresh "ts11_sub" in
	let ts12_sup := fresh "ts12_sup" in
	let H1 := fresh "H" in
	let H2 := fresh "H" in
	let Hsub1 := fresh "Hsub" in
	let Hsub2 := fresh "Hsub" in
	let Hsub3 := fresh "Hsub" in
	destruct H as [ts [ts_sub [ts11_sub [ts12_sup [
	  H1 [H2 [Hsub1 [Hsub2 Hsub3]]]
	]]]]]
  end.

Lemma injective_admininstr_instr : injective admininstr_instr.
Proof.
	unfold injective.
	move=> x1 x2 H.
	destruct x1; destruct x2; try discriminate; inversion H; auto.
Qed.

Lemma construct_instrs_typing_single : forall v_C v_ai ts1 ts2 ts1' ts2',
	Instr_ok v_C v_ai (ts1 :-> ts2) ->
	((ts1 :-> ts2) <ti: (ts1' :-> ts2')) ->
	Instrs_ok v_C [v_ai] (ts1' :-> ts2').
Proof.
	move=> v_C v_ai ts1 ts2 ts1' ts2' Hai Hsub.
	unfold_instrtype_sub Hsub; subst.
	eapply (instrs_ok_sub).
	2: { eapply resulttype_sub_app; eauto. }
	2: {
		eapply resulttype_sub_app.
		eapply resulttype_sub_refl.
		eauto.
	}
	{
		eapply instrs_ok_frame.
		eapply (instrs_ok_seq _ []).
		{
			eapply instrs_empty_typing.
			eapply resulttype_sub_refl.
		}
		eauto.
	}
Qed.

Lemma construct_ais_typing_single : forall v_S v_C v_ai ts1 ts2 ts1' ts2',
	Admin_instr_ok v_S v_C v_ai (ts1 :-> ts2) ->
	((ts1 :-> ts2) <ti: (ts1' :-> ts2')) ->
	Admin_instrs_ok v_S v_C [v_ai] (ts1' :-> ts2').
Proof.
	move=> v_S v_C v_ai ts1 ts2 ts1' ts2' Hai Hsub.
	unfold_instrtype_sub Hsub; subst.
	eapply (Admin_instrs_ok__sub _ _); [
		eapply (Admin_instrs_ok__frame) |
		eapply resulttype_sub_refl |
		eapply resulttype_sub_app; eauto
	].
	eapply (Admin_instrs_ok__seq _ _ []).
	- apply ais_empty_typing. by apply Hsub1.
	- eauto.
Qed.

Lemma construct_ais_subtyping : forall v_S v_C v_ais ts1 ts2 ts1' ts2',
	Admin_instrs_ok v_S v_C v_ais (ts1 :-> ts2) ->
	((ts1 :-> ts2) <ti: (ts1' :-> ts2')) ->
	Admin_instrs_ok v_S v_C v_ais (ts1' :-> ts2').
Proof.
	move=> v_S v_C v_ais ts1 ts2 ts1' ts2' Hai Hsub.
	unfold_instrtype_sub Hsub; subst.
	eapply (Admin_instrs_ok__sub _ _).
	- eapply Admin_instrs_ok__frame. by eapply Hai.
	- eapply resulttype_sub_app; eauto.
	- eapply resulttype_sub_app; eauto.
	  by eapply resulttype_sub_refl.
Qed.

Ltac unfold_principal_typing H :=
  unfold instr_principal_typing in H;
  try (unfold admininstr_instr in H);
  unfold ai_principal_typing in H;
  try (unfold admininstr_val in H);
  try (unfold fun_coecontext_ref__admininstr in H).

Lemma injective_fun_coecontext_numtype__valtype: injective fun_coecontext_numtype__valtype.
Proof.
	unfold injective.
	move=> x1 x2 H.
	destruct x1; destruct x2; try discriminate; auto.
Qed.

Ltac valtype_discriminate_helper H :=
  lazymatch type of H with
  | (_ ?x) = (_ ?y) =>
    destruct x; destruct y
  | (_ ?x) = _ =>
    destruct x
  | _ = (_ ?y) =>
    destruct y
  | _ = _ => idtac
  end;
  first [discriminate H | subst].

Lemma construct_ais_compose : forall v_S v_C v_ais1 v_ais2 t1s t2s t3s,
	Admin_instrs_ok v_S v_C v_ais1 (t1s :-> t2s) ->
	Admin_instrs_ok v_S v_C v_ais2 (t2s :-> t3s) ->
	Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (t1s :-> t3s).
Proof.
	move => v_S v_C v_ais1 v_ais2 t1s t2s t3s H1 H2.
	move: v_ais1 t1s t2s t3s H1 H2.
	induction v_ais2 using last_ind.
	{
		move=> v_ais1 t1s t2s t3s H1 H2.
		rewrite cats0.
		eapply Admin_instrs_ok__sub.
		eapply H1.
		eapply resulttype_sub_refl.
		eapply ais_empty_typing in H2.
		eapply H2.
	}
	{
		move=> v_ais1 t1s t2s t3s H1 H2.
		rewrite -cats1.
		rewrite catA.
		rewrite -cats1 in H2.
		typing_inversion H2.

		eapply Admin_instrs_ok__seq.
		eapply IHv_ais2.
		eapply H1.
		eapply H0.
		by eapply ais_single_typing_inversion'.
	}
Qed.

Lemma construct_ai_const_I32 : forall v_S v_C v_num,
	Admin_instr_ok v_S v_C (admininstr_CONST I32 v_num) ([] :-> [valtype_I32]).
Proof.
	move => v_S v_C v_num.
	eapply admininstr_ok_instr with (v_instr := instr_CONST _ _).
	econstructor.
Qed.

Lemma construct_ai_ref : forall v_S v_C (v_ref: wasm.ref) t_lst,
	Ref_ok v_S v_ref t_lst ->
	Admin_instr_ok v_S v_C (v_ref: admininstr) ([] :-> [t_lst: valtype]).
Proof.
	move => v_S v_C v_ref t_lst HRef.
	destruct HRef.
	{
		eapply admininstr_ok_instr with (v_instr := instr_REF_NULL v_rt).
		econstructor.
	}
	{
		eapply admininstr_ok_ref; eauto.
	}
	{
		eapply admininstr_ok_ref_extern.
	}
Qed.

Lemma construct_ai_val : forall v_S v_C (v_val: wasm.val) t_lst,
	Val_ok v_S v_val t_lst ->
	Admin_instr_ok v_S v_C (admininstr_val v_val) ([] :-> [t_lst]).
Proof.
	move => v_S v_C v_val t_lst HValok.
	inversion HValok; subst.
	- eapply admininstr_ok_instr with (v_instr := (CONST v_nt v_context_t)).
	  by econstructor.
	- eapply admininstr_ok_instr with (v_instr := (VCONST v_vt v_context_t)).
	  destruct v_vt.
	  by econstructor.
	- inversion H; subst.
	  + eapply admininstr_ok_instr with (v_instr := (REF_NULL v_rt)).
	    by econstructor.
	  + eapply admininstr_ok_ref. by eauto.
	  + by eapply admininstr_ok_ref_extern.
Qed.

Lemma construct_ai_weakening : forall v_S v_C ai tf1 tf2,
	(tf1 <ti: tf2) ->
	Admin_instr_ok v_S v_C ai tf1 ->
	Admin_instr_ok v_S v_C ai tf2.
Proof.
	move => v_S v_C ai tf1 tf2 Hsub HType.
	unfold_instrtype_sub Hsub; subst.
	eapply admininstr_ok_weakening; eauto.
Qed.

Lemma construct_ai_maybe : forall v_S v_C ai tf,
	((of ai) <> None) ->
	(ok v_C (the (of ai)) tf) ->
	Admin_instr_ok v_S v_C ai tf.
Proof.
	move => v_S v_C ai tf HSome HInstr.
	remember (the (of ai)) as instr.
	destruct ai;
	simpl in Heqinstr; subst;
	rewrite /instr_of in HSome;
	try contradiction;
	eapply admininstr_ok_instr in HInstr;
	by eauto.
Qed.

Lemma construct_ais_vals' : forall v_S v_C v_C' (v_vals: seq wasm.val) v_ft,
	Admin_instrs_ok v_S v_C (map admininstr_val v_vals) v_ft ->
	Admin_instrs_ok v_S v_C' (map admininstr_val v_vals) v_ft.
Proof.
	move=> v_S v_C v_C' v_vals v_ft HType.
	generalize dependent v_ft.
	induction v_vals using last_ind.
	{ (* v_vals = [] *)
	  move=> v_ft HType.
	  unfold map.
	  destruct_functypes.
	  eapply ais_empty_typing.
	  eapply ais_empty_typing in HType.
	  auto.
	}
	{ (* v_vals = xs ++ [x] *)
	  move=> v_ft HType.
	  destruct_functypes.
	  rewrite map_rcons in HType.
	  rewrite -cats1 in HType.
	  rewrite map_rcons.
	  rewrite -cats1.
	  typing_inversion HType.
	  typing_inversion H2.

	  eapply construct_ais_compose.
	  - eapply IHv_vals. eauto.
	  - eapply construct_ais_typing_single.
	    eapply construct_ai_val; eauto.
		by eauto.
	}
Qed.

Lemma construct_ais_trap : forall v_S v_C v_ft,
Admin_instrs_ok v_S v_C [(admininstr_TRAP )] v_ft.
Proof.
	move=> v_S v_C v_ft.
	destruct_functypes.
	eapply (Admin_instrs_ok__seq _ _ [] admininstr_TRAP).
	eapply ais_empty_typing.
	eapply resulttype_sub_refl.
	eapply admininstr_ok_trap.
Qed.


Definition value_extra (v_S: store) (v_val: wasm.val) : Prop :=
  match v_val with
  | VAL_REF_FUNcontext_ADDR v_funcaddr => ∃ v_ft : functype, 
    Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (FUNC v_ft)
  | _ => True
  end.

Definition Vals_ok v_S v_vals v_ts: Prop :=
List.Forall2 (fun (t_lst : valtype) (v_val : val) => (Val_ok v_S v_val t_lst)) (v_ts) (v_vals).

Lemma ais_vals_typing_inversion: forall v_S v_C v_vals t1s t2s,
	Admin_instrs_ok v_S v_C (map admininstr_val v_vals) (t1s :-> t2s) ->
	exists (v_ts: list valtype),
	(([] :-> v_ts) <ti: (t1s :-> t2s)) /\
	(Vals_ok v_S v_vals v_ts).
Proof.
	move=> v_S v_C v_vals t1s t2s HType.
	move: t1s t2s HType.

	induction v_vals using last_ind.
	{
		move => t1s t2s HType.
		exists [].
		split.
		- eapply ais_empty_typing in HType.
		  exists t1s, t2s, [], [].
		  split. by rewrite cats0.
		  split. by rewrite cats0.
		  split; auto.
		  split; by eapply resulttype_sub_refl.
		- constructor.
	}
	{
		move => t1s t2s HType.
		rewrite map_rcons in HType.
		rewrite -cats1 in HType.
		typing_inversion HType.
		eapply IHv_vals in H1 as [v_ts [Hsub Hforall]].
		typing_inversion H2.
		rewrite -(cats0 v_ts) in Hsub.
		eapply (instrtype_sub_compose2 _ _ [] _ _ _ _ Hsub) in Hsub0.
		  
		exists (v_ts ++ [t]).
		split. auto.
		rewrite -cats1.
		eapply Forall2_app. eauto.
		constructor. auto.
		constructor.
	}
Qed.

Ltac vals_typing_inversion H :=
  match type of H with
  | Admin_instrs_ok ?v_S ?v_C (map admininstr_val ?v_vals) (?t1s :-> ?t2s) =>
	let v_ts := fresh "v_ts" in
	let Hsub := fresh "Hsub" in
	let Hforall := fresh "Hforall" in
	eapply ais_vals_typing_inversion in H as [v_ts [Hsub Hforall]]
  | Admin_instrs_ok ?v_S ?v_C (ListDef.map (fun x => admininstr_val x) ?v_vals) (?t1s :-> ?t2s) =>
	let v_ts := fresh "v_ts" in
	let Hsub := fresh "Hsub" in
	let Hforall := fresh "Hforall" in
	eapply ais_vals_typing_inversion in H as [v_ts [Hsub Hforall]]
  | _ => idtac
  end.

Lemma construct_ais_vals: forall v_S v_C (v_vals: list wasm.val) t1s t2s ts,
	(([] :-> ts) <ti: (t1s :-> t2s)) ->
	(Vals_ok v_S v_vals ts) ->
	Admin_instrs_ok v_S v_C (map admininstr_val v_vals) (t1s :-> t2s).
Proof.
	move => v_S v_C v_vals t1s t2s ts Hsub Hforall.
	move: t1s t2s ts Hsub Hforall.
	induction v_vals using last_ind.
	{
		move => t1s t2s ts Hsub Hforall.
		inversion Hforall; subst.
		unfold_instrtype_sub Hsub; subst.
		eapply ais_empty_typing.
		eapply resulttype_sub_app; auto.
		eapply resulttype_sub_trans; eauto.
	}
	{
		induction ts using last_ind.
		{
			move => Hsub Hforall.
			inversion Hforall; subst.
			rewrite -cats1 in H.
			destruct_list_eq H.
		}
		{
			clear IHts.
			move => Hsub Hforall.
			rewrite -!cats1 in Hforall.
			eapply Forall2_app' in Hforall as [H1 H2].
			2: {
				apply Forall2_length in Hforall.
				rewrite !last_length in Hforall.
				by inversion Hforall.
			} 
			rewrite map_rcons.
			rewrite -cats1.
			induction t2s using last_ind.
			{
				unfold_instrtype_sub Hsub.
				destruct_list_eq H0; subst.
				inversion Hsub2.
				rewrite -size_length in H3.
				rewrite size_rcons in H3.
				discriminate.
			}
			clear IHt2s.

			rewrite -!cats1 in Hsub.
			unfold_instrtype_sub Hsub; subst.
			eapply resulttype_sub_empty in Hsub1; subst.
			eapply (resulttype_sub_app _ _ _ _ Hsub0) in Hsub2.
			rewrite -H0 in Hsub2.
			rewrite catA in Hsub2.
			eapply (resulttype_sub_app') in Hsub2 as [Hsub3 Hsub4].
			2: {
				inversion Hsub2.
				rewrite !last_length in H4.
				by inversion H4.
			}

			rewrite cats0.
			eapply (Admin_instrs_ok__seq _ _ _ _ _ _ t2s).
			2: {
				rewrite -cats1.
				rewrite <-(cats0 t2s) at 1.
				eapply admininstr_ok_weakening.
				2: by apply resulttype_sub_refl.
				2: by apply resulttype_sub_refl.
				2: by apply Hsub4.
				inversion H2.
				by eapply construct_ai_val.
			}
			eapply (IHv_vals _ t2s ts); auto.
			eexists ts0, ts0_sub, [], (drop (size ts0) t2s).
			split. by rewrite cats0.
			split.
			{
				rewrite <-(cat_take_drop (size ts0) t2s) at 1.
				rewrite -!app_cat.
				rewrite app_inv_tail_iff.
				assert (take (size ts0) (t2s ++ [x1]) = take (size ts0) t2s).
				{
					eapply takel_cat.
					inversion Hsub3.
					rewrite -!size_length in H4.
					rewrite -H4.
					rewrite size_cat.
					eapply leq_addr.
				}
				rewrite -H.
				rewrite H0.
				inversion Hsub0.
				rewrite -size_length in H5.
				by rewrite take_size_cat.
			}
			split. auto.
			split. by apply resulttype_sub_refl.
			pose proof Hsub3 as Hsub3_0.
			rewrite -(cat_take_drop (size ts0) t2s) in Hsub3.
			eapply resulttype_sub_app' in Hsub3 as [Hsub5 Hsub6]; auto.
			rewrite -!size_length.
			rewrite size_takel; auto.
			inversion Hsub3_0.
			rewrite -!size_length in H4.
			rewrite -H4.
			rewrite size_cat.
			eapply leq_addr.
		}
	}
Qed.

Lemma resulttype_sub_single_inversion: forall t1 t2,
	([t1] <ts: [t2]) ->
	(t1 <tv: t2).
Proof.
	move => t1 t2 Hsub.
	inversion Hsub; subst; clear Hsub.
	inversion H2; subst.
	auto.
Qed.

Lemma construct_ais_instrtype_sub: forall v_S v_C v_ais t1s t2s t1s' t2s',
	Admin_instrs_ok v_S v_C v_ais (t1s :-> t2s) ->
	((t1s :-> t2s) <ti: (t1s' :-> t2s')) ->
	Admin_instrs_ok v_S v_C v_ais (t1s' :-> t2s').
Proof.
	move => v_S v_C v_ais t1s t2s t1s' t2s' HType Hsub.
	unfold_instrtype_sub Hsub; subst.
	eapply (Admin_instrs_ok__sub _ _ _ _ _ (ts_sub ++ t1s) (ts_sub ++ t2s)).
	- eapply Admin_instrs_ok__frame; eauto.
	- eapply resulttype_sub_app; eauto.
	- eapply resulttype_sub_app; eauto.
	  eapply resulttype_sub_refl.
Qed.



Definition inst_match C C' : Prop :=
	context_TYPES C = context_TYPES C' /\
	context_FUNCS C = context_FUNCS C' /\
	context_GLOBALS C = context_GLOBALS C' /\
	context_TABLES C = context_TABLES C' /\
	context_MEMS C = context_MEMS C' /\
	context_ELEMS C = context_ELEMS C' /\
	context_DATAS C = context_DATAS C'.

Lemma construct_inst_match_label : forall C C' lab,
	inst_match C C' -> inst_match C (upd_label C' lab).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_match_return : forall C C' ret,
	inst_match C C' -> inst_match C (upd_return C' ret).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_match_local : forall C C' loc,
	inst_match C C' -> inst_match C (upd_local C' loc).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_match_local_label_return : forall C C' loc lab ret,
	inst_match C C' -> inst_match C (upd_local_label_return C' loc lab ret).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_match_local_return : forall C C' loc ret,
	inst_match C C' -> inst_match C (upd_local_return C' loc ret).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_prepend_label : forall C C' lab,
	inst_match C C' -> inst_match C (prepend_label C' lab).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Ltac resolve_inst_match :=
	repeat lazymatch goal with
	| _ : _ |- inst_match _ (prepend_label _ _) =>
		eapply construct_inst_prepend_label
	| _ : _ |- inst_match _ (upd_local_label_return _ _ _) =>
		eapply construct_inst_match_local_label_return
	| _ : _ |- inst_match _ (upd_local_return _ _ _) =>
		eapply construct_inst_match_local_return
	| _ : _ |- inst_match _ (upd_local _ _) =>
		eapply construct_inst_match_local
	| _ : _ |- inst_match _ (upd_return _ _) =>
		eapply construct_inst_match_return
	| _ : _ |- inst_match _ (upd_label _ _) =>
		eapply construct_inst_match_label
	| _ => idtac
	end;
	unfold inst_match;
	simpl;
	unfold _append;
	simpl;
	repeat eexists; auto.

Lemma Val_ok_non_bot : forall v_S v_val t_lst,
	Val_ok v_S v_val t_lst ->
	t_lst <> VALTYPE_BOT.
Proof.
	move=> v_S v_val t_lst HValok.
	inversion HValok; subst.
	- destruct v_nt; discriminate.
	- destruct v_vt; discriminate.
	- destruct v_rt; discriminate.
Qed.



Lemma Vals_ok_non_bot : forall v_S v_val v_ts,
	Forall2	(λ (v_t0 : valtype) (v_val0 : wasm.val),
		Val_ok v_S v_val0 v_t0) v_ts v_val ->
	Forall (λ (t_lst : valtype),
		t_lst <> VALTYPE_BOT) v_ts.
Proof.
	move=> v_S v_val v_ts H.
	move : v_ts H.
	induction v_val.
	{
		move=> v_ts H.
		inversion H; subst; econstructor.
	}
	{
		move=> v_ts H.
		destruct v_ts.
		{
			inversion H.
		}
		inversion H; subst; econstructor.
		2: by eapply IHv_val.
		eapply Val_ok_non_bot; eauto.
	}
Qed.

Lemma Ref_ok_non_bot : forall v_S v_val (t_lst: reftype),
	Ref_ok v_S v_val t_lst ->
	(t_lst: valtype) <> VALTYPE_BOT.
Proof.
	move=> v_S v_val t_lst HRefok.
	inversion HRefok; subst; try discriminate.
	destruct t_lst; discriminate.
Qed.




Ltac construct_ais_typing :=
  repeat rewrite app_cat;
  repeat lazymatch goal with
    | H: _ |- Admin_instrs_ok _ _ [] (_ :-> _) =>
        eapply ais_empty_typing
    | H1: (([] :-> ?tp2) <ti: (?ts1 :-> ?ts2)),
	  H2: (Vals_ok ?v_S ?v_vals ?tp2)
	  |- Admin_instrs_ok _ _ (map admininstr_val ?v_vals) (?ts1 :-> ?ts2) =>
        eapply (construct_ais_vals _ _ _ _ _ _ H1) in H2
    | H: (_ <ti: ?ts) |- Admin_instrs_ok _ _ [_] ?ts =>
        eapply construct_ais_typing_single;
		[| eapply H]
    | H: _ |- Admin_instrs_ok _ _ (_ ++ _) ?ts =>
        eapply construct_ais_compose
    | H: _ |- Admin_instrs_ok _ _ (_ :: (_ :: _)) ?ts =>
        rewrite -cat1s
	| _ : _ |- _ => idtac
  end.

Ltac extract_premise :=
  repeat match goal with
  | H: (_ :-> _) = (_ :-> _) |- _ =>
    inversion H; subst; clear H
  | H: exists t, ?P |- _ =>
    let extr := fresh "extr" in
    let Hextr := fresh "Hextr" in  
    destruct H as [extr Hextr]
  | H: ?P /\ ?Q |- _ =>
    let H1 := fresh "H1" in  
    let H2 := fresh "H2" in  
    destruct H as [H1 H2]
  | H: ?x = ?x -> _ |- _ =>
    specialize (H erefl)
  | H: forall x, ?x0 = x -> _ |- _ =>
    try specialize (H _ erefl)
  | H: forall x, _ = _ -> _ |- _ =>
    try specialize (H _ erefl)
  | H: forall x y, _ = _ -> _ |- _ =>
    try specialize (H _ _ erefl)
  | H: forall x y z, _ = _ -> _ |- _ =>
    try specialize (H _ _ _ erefl)
  | _ => idtac
end.

Ltac destruct_all :=
  repeat match goal with
  | H: exists t, ?P |- _ =>
    let extr := fresh "extr" in
    let Hextr := fresh "Hextr" in
    destruct H as [extr Hextr]
  | H: ?P /\ ?Q |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct H as [H1 H2]
  | _ => idtac
end.

Ltac invert_ais_single_val_typing H :=
  let t := fresh "t" in
  let HValok := fresh "HValok" in
  let Hsub := fresh "Hsub" in
  eapply ais_single_val_typing_inversion in H
    as [t [Hsub HValok]].

Ltac invert_ais_vals_typing H :=
  let t := fresh "t" in
  let HValsok := fresh "HValsok" in
  let Hsub := fresh "Hsub" in
  eapply ais_vals_typing_inversion in H
    as [t [Hsub HValsok]].

Ltac invert_ais_single_ref_typing H :=
  let t := fresh "t" in
  let HValsok := fresh "HRefok" in
  let Hsub := fresh "Hsub" in
  eapply ais_single_ref_typing_inversion in H
    as [t [Hsub HRefok]].

Ltac invert_ais_typing :=
  destruct_functypes;
  repeat match goal with
  | H : Admin_instrs_ok _ _ (app _ _) _ |- _ => 
	repeat rewrite app_cat in H
  end;
  repeat lazymatch goal with
  | H: Admin_instrs_ok _ _ [] _ |- _ =>
    eapply ais_empty_typing in H;
	idtac
  | H: Admin_instrs_ok _ _ [admininstr_val _] ( _ :-> _ ) |- _ =>
    invert_ais_single_val_typing H;
	idtac
  | H: Admin_instrs_ok _ _ [fun_coecontext_ref__admininstr _] ( _ :-> _ ) |- _ =>
    invert_ais_single_ref_typing H;
	idtac
  | H: Admin_instrs_ok _ _ (map admininstr_val _) ( _ :-> _ ) |- _ =>
    invert_ais_vals_typing H;
	idtac
  | H: Admin_instrs_ok _ _ [?v_ai] ( ?t1s :-> ?t2s ) |- _ =>
    let t1s' := fresh "t1s'" in
	let t2s' := fresh "t2s'" in
	let Hai := fresh "Hai" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_typing_inversion in H
	  as [t1s' [t2s' [Hai Hsub]]];
	idtac
  | H: Admin_instrs_ok _ _ (_ ++ _) _ |- _ =>
    let t3s := fresh "t3s" in
	let HType1 := fresh "HType1" in
	let HType2 := fresh "HType2" in
	eapply ais_composition_typing in H as [t3s [HType1 HType2]];
	idtac
  | H: Admin_instrs_ok _ _ (_ :: ( _ :: _)) _ |- _ =>
    try rewrite -cat1s in H
  | _ => idtac
  end.

Ltac invert_instrtype_sub :=
  repeat match goal with
  | H: ((?txs :-> ?tys) <ti: ([] :-> []) ) |- _ =>
	eapply instrtype_sub_sub_empty in H
  | H: (([] :-> []) <ti: (?txs :-> ?tys) ) |- _ =>
	eapply instrtype_sub_empty in H
  | H: ((?txs :-> ?tys) <ti: (?tzs :-> []) ) |- _ =>
	eapply instrtype_sub_sub_empty2 in H
  | H: ((?txs :-> ?tys) <ti: ([] :-> ?tzs) ) |- _ =>
	eapply instrtype_sub_sub_empty1 in H
  | _ => idtac
  end.

Ltac resolve_pt H :=
  unfold ai_principal_typing in H;
  extract_premise.

Ltac resolve_all_pt :=
  repeat match goal with
  | H: (ai_principal_typing _ _ _ _) |- _ =>
	resolve_pt H
  | _ => idtac
  end.

Opaque instrtype_sub.

Create HintDb take_drop_size_db.

Hint Rewrite take_size drop_size size_cat
	@helper_lemmas.take_size_cat @helper_lemmas.drop_size_cat
	cats0 subn0 add_sub add_sub': take_drop_size_db.

Ltac simplify_take_drop_size H :=
	repeat (
		autorewrite with take_drop_size_db in H;
		repeat match goal with
		| He : length ?l1 = length ?l2 |- _ =>
			rewrite -!size_length in He
		| He : size ?l1 = size ?l2 |- _ =>
			rewrite He in H
		| _ => auto
		end;
		autorewrite with take_drop_size_db in H;
		simpl in H
	).

Ltac simplify_resulttype_sub H :=
  simplify_take_drop_size H;
  repeat lazymatch type of H with
  | (?ts) <ts: (?ts) => clear H
  | (_ :: _) <ts: (_ :: _) =>
    let Hsubv := fresh "Hsubv" in
    let Hsubs := fresh "Hsubs" in
    eapply resulttype_sub_cons in H
    as [Hsubv Hsubs];
	simplify_resulttype_sub Hsubs
  | _ => idtac
  end.


Ltac join_subtyping_trans H1 H2 :=
  let Hsubi := fresh "Hsubi" in
  eapply (instrtype_sub_trans _ _ _ H1) in H2
	as Hsubi.

Ltac construct_size_le :=
  repeat rewrite take_size drop_size /=;
  repeat match goal with
  | _ : _ |- context [ size (?l1 ++ ?l2) ] =>
	rewrite !size_cat
  | H : length ?l1 = length ?l2 |- _ =>
	rewrite -!size_length in H
  | H : size ?l1 = size ?l2 |- context [ size ?l1 ] =>
	rewrite H
  | _ : _ |- is_true (?a <= ?a + ?b) =>
	by eapply leq_addr
  | _ : _ |- is_true (?b <= ?a + ?b) =>
	by eapply leq_addl
  | _ => auto
  end.

Ltac join_subtyping_eq H1 H2 :=
  let Hsubi := fresh "Hsubi" in
  let Hsubs := fresh "Hsubs" in
  eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ H1) in H2
		as [Hsubi Hsubs];
  [simpl in Hsubi, Hsubs;
   simplify_resulttype_sub Hsubs |
   auto]
  .

Ltac join_subtyping_ge H1 H2 :=
	let Hsubi := fresh "Hsubi" in
	let Hsubs := fresh "Hsubs" in
  	eapply (instrtype_sub_compose_ge' _ _ _ _ _ _ _ H1) in H2
	  as [Hsubi Hsubs];
	simplify_take_drop_size Hsubi;
	simplify_resulttype_sub Hsubs;
	[ |
		construct_size_le
	].

Ltac join_subtyping_le H1 H2 :=
	let Hsubi := fresh "Hsubi" in
	let Hsubs := fresh "Hsubs" in
  	eapply (instrtype_sub_compose_le' _ _ _ _ _ _ _ H1) in H2
	  as [Hsubi Hsubs];
	simplify_take_drop_size Hsubi;
	simplify_resulttype_sub Hsubs;
	[ |
		construct_size_le
	].

Ltac resolve_subtyping :=
  repeat lazymatch goal with
  | H: ([] :-> []) <ti: (?ts1 :-> ?ts2) |- _ =>
	eapply instrtype_sub_empty in H
  | H: ([] :-> ?ts1) <ti: ([] :-> ?ts2) |- _ =>
	eapply instrtype_sub_iff_resulttype_sub in H
  | H: (?ts1 :-> []) <ti: (?ts2 :-> []) |- _ =>
	eapply instrtype_sub_iff_resulttype_sub' in H
  | _ => idtac
  end.