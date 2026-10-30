(* Imported Code *)
From Stdlib Require Import String List Unicode.Utf8 NArith QArith QArith.Qround.
From mathcomp Require Import ssreflect eqtype ssrbool ssrfun seq.
From HB Require Import structures.
From RecordUpdate Require Import RecordSet.
From WasmSpectec Require Import wasm.

Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.

(* Generated Well-Formedness Lemmas *)
(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.6-68.12 *)
Lemma fzero_is_wf : forall (v_N : res_N) (ret_val : fN),
	(ret_val == (fzero v_N)) ->
	(wf_fN v_N ret_val).
Proof.
	move => v_N ret_val /eqP ->.
	apply: fN_case_0. eapply fNmag_case_1.
	apply/andP; split; last by apply/eqP.
	by apply/N.ltb_spec0; apply/N.neq_0_lt_0; apply: N.pow_nonzero.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:281.6-281.11 *)
Lemma zero_is_wf : forall (v_numtype : numtype) (ret_val : num_),
	(ret_val == (fun_zero v_numtype)) ->
	(wf_num_ v_numtype ret_val).
Proof.
	move => v_numtype ret_val /eqP ->.
	destruct v_numtype; simpl.
	- by eapply num__case_0.
	- by eapply num__case_0.
	- eapply num__case_1; last by [].
		apply: fN_case_0. eapply fNmag_case_1.
		by apply/andP; split; [ | apply/eqP].
	- eapply num__case_1; last by [].
		apply: fN_case_0. eapply fNmag_case_1.
		by apply/andP; split; [ | apply/eqP].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.6-342.10 *)
Lemma dim_is_wf : forall (v_shape : shape) (ret_val : dim),
	(wf_shape v_shape) ->
	(ret_val == (fun_dim v_shape)) ->
	(wf_dim ret_val).
Proof.
	move => v_shape ret_val Hwf /eqP ->.
	case: Hwf => lt d Hd. by case: d Hd => i Hd.
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
Lemma concat_bytes_is_wf : forall (var_0_lst_lst : (seq (seq byte))) (ret_val_lst : (seq byte)) (var_0 : (seq byte)),
	(fun_concat_bytes var_0_lst_lst var_0) ->
	List.Forall (fun (var_0_lst : (seq byte)) => List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst) var_0_lst_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.
Proof.
	move => var_0_lst_lst ret_val_lst var_0 H Hall /eqP ->.
	move: Hall. elim: H => //= b_lst b'_lst_lst v H IH Hall.
	move: Hall => /List.Forall_cons_iff [H1 H2].
	by apply/List.Forall_app; split; [ exact: H1 | exact: IH ].
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
Lemma tablesxt_is_wf : forall (var_0_lst : (seq externtype)) (ret_val_lst : (seq tabletype)) (var_0 : (seq tabletype)),
	(fun_tablesxt var_0_lst var_0) ->
	List.Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : tabletype) => (wf_tabletype ret_val)) ret_val_lst.
Proof.
	move => var_0_lst ret_val_lst var_0 H Hall /eqP ->.
	move: Hall. elim: H => //=.
	- move => tt xt_lst v H IH /List.Forall_cons_iff [H1 H2].
		apply: List.Forall_cons; last by apply: IH.
		by inversion H1.
	- move => xt xt_lst v H IH /List.Forall_cons_iff [H1 H2]. by apply: IH.
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
Lemma memsxt_is_wf : forall (var_0_lst : (seq externtype)) (ret_val_lst : (seq memtype)) (var_0 : (seq memtype)),
	(fun_memsxt var_0_lst var_0) ->
	List.Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : memtype) => (wf_memtype ret_val)) ret_val_lst.
Proof.
	move => var_0_lst ret_val_lst var_0 H Hall /eqP ->.
	move: Hall. elim: H => //=.
	- move => mt xt_lst v H IH /List.Forall_cons_iff [H1 H2].
		apply: List.Forall_cons; last by apply: IH.
		by inversion H1.
	- move => xt xt_lst v H IH /List.Forall_cons_iff [H1 H2]. by apply: IH.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.6-80.20 *)
Lemma dataidx_instr_is_wf : forall (v_instr : instr) (ret_val_lst : (seq dataidx)),
	(wf_instr v_instr) ->
	(ret_val_lst == (dataidx_instr v_instr)) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32%N ret_val)) ret_val_lst.
Proof.
	move => v_instr ret_val_lst Hwf /eqP ->.
	case: Hwf; simpl; intros;
		first [ by apply: List.Forall_nil
			| by apply: List.Forall_cons; [ eassumption | apply: List.Forall_nil ] ].
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
Lemma dataidx_instrs_is_wf : forall (var_0_lst : (seq instr)) (ret_val_lst : (seq dataidx)) (var_0 : (seq dataidx)),
	(fun_dataidx_instrs var_0_lst var_0) ->
	List.Forall (fun (var_0 : instr) => (wf_instr var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32%N ret_val)) ret_val_lst.
Proof.
	move => var_0_lst ret_val_lst var_0 H Hall /eqP ->.
	move: Hall. elim: H => //= v_instr instr'_lst v H IH /List.Forall_cons_iff [H1 H2].
	apply/List.Forall_app; split; last by apply: IH.
	by apply: (dataidx_instr_is_wf v_instr _ H1).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
Lemma dataidx_expr_is_wf : forall (v_expr : expr) (ret_val_lst : (seq dataidx)) (var_0 : (seq dataidx)),
	(fun_dataidx_expr v_expr var_0) ->
	List.Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32%N ret_val)) ret_val_lst.
Proof.
	move => v_expr ret_val_lst var_0 H Hall /eqP ->.
	move: Hall. case: H => in_lst v H Hall.
	by apply: (dataidx_instrs_is_wf in_lst _ _ H Hall).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
Lemma dataidx_func_is_wf : forall (v_func : func) (ret_val_lst : (seq dataidx)) (var_0 : (seq dataidx)),
	(fun_dataidx_func v_func var_0) ->
	(wf_func v_func) ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32%N ret_val)) ret_val_lst.
Proof.
	move => v_func ret_val_lst var_0 H Hwf /eqP ->.
	move: Hwf. case: H => x loc_lst e v H Hwf.
	inversion Hwf; subst.
	by apply: (dataidx_expr_is_wf e _ _ H _).
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
Lemma dataidx_funcs_is_wf : forall (var_0_lst : (seq func)) (ret_val_lst : (seq dataidx)) (var_0 : (seq dataidx)),
	(fun_dataidx_funcs var_0_lst var_0) ->
	List.Forall (fun (var_0 : func) => (wf_func var_0)) var_0_lst ->
	(ret_val_lst == var_0) ->
	List.Forall (fun (ret_val : dataidx) => (wf_uN 32%N ret_val)) ret_val_lst.
Proof.
	move => var_0_lst ret_val_lst var_0 H Hall /eqP ->.
	move: Hall. elim: H => //= v_func func'_lst v1 v H IH H2 /List.Forall_cons_iff [Hf Hr].
	apply/List.Forall_app; split; last by apply: IH.
	by apply: (dataidx_func_is_wf v_func _ _ H2 Hf).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.6-106.13 *)
Lemma memarg0_is_wf : forall (ret_val : memarg),
	(ret_val == (memarg0 )) ->
	(wf_memarg ret_val).
Proof.
	move => ret_val /eqP ->.
	by apply: memarg_case_; apply: uN_case_0.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.6-7.17 *)
Axiom s33_to_u32_is_wf : forall (v_s33 : s33) (ret_val : u32),
	(wf_sN 33%N v_s33) ->
	(ret_val == (s33_to_u32 v_s33)) ->
	(wf_uN 32%N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.6-56.15 *)
Axiom extend___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN) (ret_val : iN),
	(wf_uN v_M v_iN) ->
	(ret_val == (extend__ v_M v_N v_sx v_iN)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.6-224.12 *)
Axiom fabs__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fabs_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.6-227.13 *)
Axiom fceil__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fceil_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.6-228.14 *)
Axiom ffloor__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (ffloor_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.6-230.16 *)
Axiom fnearest__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fnearest_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.6-225.12 *)
Axiom fneg__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fneg_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.6-226.13 *)
Axiom fsqrt__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fsqrt_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.6-229.14 *)
Axiom ftrunc__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (ftrunc_ v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.6-120.12 *)
Axiom iclz__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (iclz_ v_N v_iN)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.6-121.12 *)
Axiom ictz__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (ictz_ v_N v_iN)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.6-122.15 *)
Axiom ipopcnt__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (ipopcnt_ v_N v_iN)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.6-55.13 *)
Axiom wrap___is_wf : forall (v_M : M) (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_M v_iN) ->
	(ret_val == (wrap__ v_M v_N v_iN)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 *)
Lemma unop__is_wf : forall (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) (ret_val_lst : (seq num_)),
	(wf_unop_ v_numtype v_unop_) ->
	(wf_num_ v_numtype v_num_) ->
	((fun_unop_ v_numtype v_unop_ v_num_) != None) ->
	(ret_val_lst == (!((fun_unop_ v_numtype v_unop_ v_num_)))) ->
	List.Forall (fun (ret_val : num_) => (wf_num_ v_numtype ret_val)) ret_val_lst.
Proof.
	move => nt op n ret H1 H2 Hne /eqP ->.
	have Hmap : forall (F : Fnn) (v_nt : numtype) (l : seq fN),
		(v_nt == (numtype_Fnn F)) ->
		List.Forall (fun x => wf_fN (sizenn (numtype_Fnn F)) x) l ->
		List.Forall (fun x => wf_num_ v_nt x) (seq.map (fun y => mk_num__1 F y) l).
	{ move => F v_nt l Hnt. elim: l => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ apply: num__case_1 | apply: IH ]. }
	destruct nt; destruct op as [inn oi|fnn ofn];
		try (destruct inn; destruct oi); try (destruct fnn; destruct ofn);
		destruct n as [inn2 i|fnn2 f]; try destruct inn2; try destruct fnn2; simpl.
	all: first
		[ by apply: List.Forall_nil
		| (inversion H2; subst;
			apply: List.Forall_cons;
			[ apply: num__case_0;
				[ by []
				| first [ (eapply iclz__is_wf; [ eassumption | by apply: eqxx ])
					| (eapply ictz__is_wf; [ eassumption | by apply: eqxx ])
					| (eapply ipopcnt__is_wf; [ eassumption | by apply: eqxx ])
					| (eapply extend___is_wf;
						[ eapply wrap___is_wf; [ eassumption | by apply: eqxx ]
						| by apply: eqxx ]) ]
				| by [] ]
			| by apply: List.Forall_nil ])
		| (inversion H2; subst; apply: Hmap;
			[ by []
			| first [ (eapply fabs__is_wf; [ eassumption | by apply: eqxx ])
				| (eapply fneg__is_wf; [ eassumption | by apply: eqxx ])
				| (eapply fsqrt__is_wf; [ eassumption | by apply: eqxx ])
				| (eapply fceil__is_wf; [ eassumption | by apply: eqxx ])
				| (eapply ffloor__is_wf; [ eassumption | by apply: eqxx ])
				| (eapply ftrunc__is_wf; [ eassumption | by apply: eqxx ])
				| (eapply fnearest__is_wf; [ eassumption | by apply: eqxx ]) ] ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.6-215.12 *)
Axiom fadd__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fadd_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.6-223.17 *)
Axiom fcopysign__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fcopysign_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.6-218.12 *)
Axiom fdiv__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fdiv_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.6-220.12 *)
Axiom fmax__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fmax_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.6-219.12 *)
Axiom fmin__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fmin_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.6-217.12 *)
Axiom fmul__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fmul_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.6-216.12 *)
Axiom fsub__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fsub_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.6-105.12 *)
Lemma iadd__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iadd_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_iN iN_0 ret_val H1 H2 /eqP ->.
	have Hnz : ((2%N ^ v_N)%BN <> 0%N) by apply: N.pow_nonzero.
	have Hpow : (1 <= (2%N ^ v_N)%BN)%BN by apply: N.pow_lower_bound.
	apply: uN_case_0.
	rewrite /N_geb -Znat.N2Z.inj_sub // Znat.N2Z.id.
	apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
	apply/N.leb_spec0. rewrite N.sub_1_r. apply: N.lt_le_pred.
	by apply: N.mod_lt.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.6-112.12 *)
Axiom iand__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iand_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.6-107.12 *)
Lemma imul__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (imul_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_iN iN_0 ret_val H1 H2 /eqP ->.
	have Hnz : ((2%N ^ v_N)%BN <> 0%N) by apply: N.pow_nonzero.
	have Hpow : (1 <= (2%N ^ v_N)%BN)%BN by apply: N.pow_lower_bound.
	apply: uN_case_0.
	rewrite /N_geb -Znat.N2Z.inj_sub // Znat.N2Z.id.
	apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
	apply/N.leb_spec0. rewrite N.sub_1_r. apply: N.lt_le_pred.
	by apply: N.mod_lt.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.6-114.11 *)
Axiom ior__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ior_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
Lemma irem__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : (option iN)) (var_0 : (option iN)),
	(fun_irem_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val_opt == var_0) ->
	List.Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (option_to_list ret_val_opt).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val_opt var_0 H Hw1 Hw2 /eqP ->.
	have Hto : forall m : N, ((((m : Z) - (1%N : Z))%Z : N) = (m - 1)%BN).
	{ case => [ |p] //. by rewrite -Znat.N2Z.inj_sub ?Znat.N2Z.id //; apply/N.neq_0_le_1. }
	have Hp : forall (vN : res_N), (0 < (2%N ^ vN)%BN)%BN.
	{ by move => vN; apply/N.neq_0_lt_0; apply: N.pow_nonzero. }
	have HtoN : forall (vN : res_N) (z2 : Z),
		(z2 < ((2%N ^ vN)%BN : Z))%Z -> (((z2 : N)) < (2%N ^ vN)%BN)%BN.
	{ move => vN; case => [ |q|q] Hz //=; try exact: Hp.
		have Hnn : (0 <= Z.pos q)%Z by [].
		have := (proj1 (Znat.Z2N.inj_lt (Z.pos q) _ Hnn (Znat.N2Z.is_nonneg _)) Hz).
		by rewrite Znat.N2Z.id. }
	have Hbnd : forall (vN : res_N) (x : N), (x < (2%N ^ vN)%BN)%BN -> wf_uN vN (mk_uN x).
	{ move => vN x Hx. apply: uN_case_0. rewrite Hto /N_geb.
		apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		by apply/N.leb_spec0; rewrite N.sub_1_r; apply: N.lt_le_pred. }
	have Hle : forall (vN : res_N),
		((2%N ^ ((((vN : Z) - (1%N : Z))%Z : N)))%BN <= (2%N ^ vN)%BN)%BN.
	{ move => vN. apply: N.pow_le_mono_r => //. rewrite Hto. exact: N.le_sub_l. }
	have Hinv : forall (vN : res_N) (z : Z) (m : N), fun_inv_signed_ vN z m -> wf_uN vN (mk_uN m).
	{ move => vN0 z m Hi. case: Hi => vN i /andP [Ha Hb]; apply: Hbnd; apply: HtoN.
		- have Hlt2 : (i < ((2%N ^ ((((vN : Z) - (1%N : Z))%Z : N)))%BN : Z))%Z
				by apply: (proj1 (Z.ltb_lt _ _) Hb).
			apply: (Z.lt_le_trans _ _ _ Hlt2). by apply/Znat.N2Z.inj_le; apply: Hle.
		- rewrite -{2}(Z.add_0_l ((2%N ^ vN)%BN : Z)).
			by apply: (proj1 (Z.add_lt_mono_r _ _ _) (proj1 (Z.ltb_lt _ _) Hb)). }
	(* The unsigned remainder is (i_1 - X) truncated to N for some X : N, which
	   is at most i_1 whatever truncz returns. *)
	have Hrem : forall (vN : res_N) (a : uN) (X : N),
		wf_uN vN a -> wf_uN vN (mk_uN ((((proj_uN_0 a) : Z) - (X : Z))%Z : N)).
	{ move => vN [a] X Hw. inversion Hw as [vN' a' Hb]; subst. apply: Hbnd.
		move/andP: Hb => [_ Hub]. move/N.leb_spec0 in Hub. rewrite Hto in Hub.
		rewrite /= Znat.Z2N.inj_sub ?Znat.N2Z.id; last exact: Znat.N2Z.is_nonneg.
		apply: (N.le_lt_trans _ a); first exact: N.le_sub_l.
		apply: (N.le_lt_trans _ _ _ Hub). apply: N.sub_lt => //.
		exact: (proj2 (N.le_succ_l 0 _) (Hp vN)). }
	case: H Hw1 Hw2 => *; simpl.
	all: try by apply: List.Forall_nil.
	all: try (by apply: List.Forall_cons;
		[ apply: Hinv; eassumption | apply: List.Forall_nil ]).
	all: by apply: List.Forall_cons; [ apply: Hrem; eassumption | apply: List.Forall_nil ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.6-118.13 *)
Axiom irotl__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (irotl_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.6-119.13 *)
Axiom irotr__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (irotr_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.6-116.12 *)
Axiom ishl__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ishl_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.6-117.12 *)
Axiom ishr__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ishr_ v_N v_sx v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.6-106.12 *)
Lemma isub__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (isub_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_iN iN_0 ret_val H1 H2 /eqP ->.
	have Hpow : (1 <= (2%N ^ v_N)%BN)%BN by apply: N.pow_lower_bound.
	have Hsub : (((((2%N ^ v_N)%BN : Z) - (1%N : Z))%Z : N)) = ((2%N ^ v_N)%BN - 1%N)%BN
		by rewrite -Znat.N2Z.inj_sub // Znat.N2Z.id.
	have HposZ : (0 < ((2%N ^ v_N)%BN : Z))%Z.
	{ have Hp : (0 < (2%N ^ v_N)%BN)%BN by apply/N.neq_0_lt_0; apply: N.pow_nonzero.
		by move/Znat.N2Z.inj_lt: Hp. }
	apply: uN_case_0.
	rewrite Hsub /N_geb.
	apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
	apply/N.leb_spec0. rewrite N.sub_1_r. apply: N.lt_le_pred.
	have [Hlo Hhi] := Z.mod_pos_bound ((((2%N ^ v_N)%BN + (v_iN :> N))%BN : Z) - ((iN_0 :> N) : Z))%Z _ HposZ.
	have Hres := (proj1 (Znat.Z2N.inj_lt _ _ Hlo (Z.lt_le_incl _ _ HposZ)) Hhi).
	by rewrite Znat.N2Z.id in Hres.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.6-115.12 *)
Axiom ixor__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ixor_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.6-123.12 *)
Lemma ieqz__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : u32),
	(wf_uN v_N v_iN) ->
	(ret_val == (ieqz_ v_N v_iN)) ->
	(wf_uN 32%N ret_val).
Proof.
	move => v_N v_iN ret_val H /eqP ->.
	apply: uN_case_0. by case: ((v_iN :> N) == 0%N).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 *)
Lemma testop__is_wf : forall (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) (ret_val : num_),
	(wf_testop_ v_numtype v_testop_) ->
	(wf_num_ v_numtype v_num_) ->
	((fun_testop_ v_numtype v_testop_ v_num_) != None) ->
	(ret_val == (!((fun_testop_ v_numtype v_testop_ v_num_)))) ->
	(wf_num_ I32 ret_val).
Proof.
	move => nt top n ret H1 H2 Hne /eqP ->.
	destruct nt; destruct top as [inn t]; destruct inn; destruct t;
		destruct n as [inn2 i|fnn f]; try destruct inn2; try destruct fnn; simpl.
	all: first [ by apply: num__case_0
		| (inversion H2; subst; apply: num__case_0 => //;
			eapply ieqz__is_wf; [ eassumption | by apply: eqxx ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.6-231.11 *)
Axiom feq__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (feq_ v_N v_fN fN_0)) ->
	(wf_uN 32%N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.6-236.11 *)
Axiom fge__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (fge_ v_N v_fN fN_0)) ->
	(wf_uN 32%N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.6-234.11 *)
Axiom fgt__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (fgt_ v_N v_fN fN_0)) ->
	(wf_uN 32%N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.6-235.11 *)
Axiom fle__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (fle_ v_N v_fN fN_0)) ->
	(wf_uN 32%N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.6-233.11 *)
Axiom flt__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (flt_ v_N v_fN fN_0)) ->
	(wf_uN 32%N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.6-232.11 *)
Axiom fne__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val : u32),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val == (fne_ v_N v_fN fN_0)) ->
	(wf_uN 32%N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.6-125.11 *)
Lemma ieq__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : u32),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ieq_ v_N v_iN iN_0)) ->
	(wf_uN 32%N ret_val).
Proof.
	move => v_N v_iN iN_0 ret_val H1 H2 /eqP ->.
	apply: uN_case_0. by case: (v_iN == iN_0).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
Lemma ige__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32),
	(fun_ige_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN 32%N ret_val).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val var_0 H H1 H2 /eqP ->.
	have Hb : forall b : bool, (wf_uN 32%N (mk_uN (res_bool b))).
	{ by move => b; apply: uN_case_0; case: b. }
	by case: H => *; apply: Hb.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
Lemma igt__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32),
	(fun_igt_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN 32%N ret_val).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val var_0 H H1 H2 /eqP ->.
	have Hb : forall b : bool, (wf_uN 32%N (mk_uN (res_bool b))).
	{ by move => b; apply: uN_case_0; case: b. }
	by case: H => *; apply: Hb.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
Lemma ile__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32),
	(fun_ile_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN 32%N ret_val).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val var_0 H H1 H2 /eqP ->.
	have Hb : forall b : bool, (wf_uN 32%N (mk_uN (res_bool b))).
	{ by move => b; apply: uN_case_0; case: b. }
	by case: H => *; apply: Hb.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
Lemma ilt__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32),
	(fun_ilt_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN 32%N ret_val).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val var_0 H H1 H2 /eqP ->.
	have Hb : forall b : bool, (wf_uN 32%N (mk_uN (res_bool b))).
	{ by move => b; apply: uN_case_0; case: b. }
	by case: H => *; apply: Hb.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.6-126.11 *)
Lemma ine__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : u32),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (ine_ v_N v_iN iN_0)) ->
	(wf_uN 32%N ret_val).
Proof.
	move => v_N v_iN iN_0 ret_val H1 H2 /eqP ->.
	apply: uN_case_0. by case: (v_iN != iN_0).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
Lemma relop__is_wf : forall (v_numtype : numtype) (v_relop_ : relop_) (v_num_ : num_) (num__0 : num_) (ret_val : num_) (var_0 : (option num_)),
	(fun_relop_ v_numtype v_relop_ v_num_ num__0 var_0) ->
	(wf_relop_ v_numtype v_relop_) ->
	(wf_num_ v_numtype v_num_) ->
	(wf_num_ v_numtype num__0) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_num_ I32 ret_val).
Proof.
	move => nt rop n1 n2 ret var0 H Hr H1 H2 Hne /eqP ->.
	case: H Hr H1 H2 Hne => *; simpl.
	all: repeat match goal with | [ Hx : wf_num_ _ _ |- _ ] => inversion Hx; subst; clear Hx end.
	all: first
		[ by apply: num__case_0
		| (apply: num__case_0;
			[ by []
			| first [ ((eapply ieq__is_wf; only 3: by apply: eqxx); eassumption)
				| ((eapply ine__is_wf; only 3: by apply: eqxx); eassumption)
				| ((eapply feq__is_wf; only 3: by apply: eqxx); eassumption)
				| ((eapply fne__is_wf; only 3: by apply: eqxx); eassumption)
				| ((eapply flt__is_wf; only 3: by apply: eqxx); eassumption)
				| ((eapply fgt__is_wf; only 3: by apply: eqxx); eassumption)
				| ((eapply fle__is_wf; only 3: by apply: eqxx); eassumption)
				| ((eapply fge__is_wf; only 3: by apply: eqxx); eassumption)
				| ((eapply ilt__is_wf; only 4: by apply: eqxx); eassumption)
				| ((eapply igt__is_wf; only 4: by apply: eqxx); eassumption)
				| ((eapply ile__is_wf; only 4: by apply: eqxx); eassumption)
				| ((eapply ige__is_wf; only 4: by apply: eqxx); eassumption) ]
			| by [] ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.6-61.16 *)
Axiom convert___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN) (ret_val : fN),
	(wf_uN v_M v_iN) ->
	(ret_val == (convert__ v_M v_N v_sx v_iN)) ->
	(wf_fN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.6-59.15 *)
Axiom demote___is_wf : forall (v_M : M) (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_M v_fN) ->
	(ret_val_lst == (demote__ v_M v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.6-60.16 *)
Axiom promote___is_wf : forall (v_M : M) (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_M v_fN) ->
	(ret_val_lst == (promote__ v_M v_N v_fN)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.6-63.20 *)
Axiom reinterpret___is_wf : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) (ret_val : num_),
	(wf_num_ numtype_1 v_num_) ->
	(ret_val == (reinterpret__ numtype_1 numtype_2 v_num_)) ->
	(wf_num_ numtype_2 ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.6-57.14 *)
Axiom trunc___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN) (ret_val_opt : (option iN)),
	(wf_fN v_M v_fN) ->
	(ret_val_opt == (trunc__ v_M v_N v_sx v_fN)) ->
	List.Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (option_to_list ret_val_opt).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.6-58.18 *)
Axiom trunc_sat___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : fN) (ret_val_opt : (option iN)),
	(wf_fN v_M v_fN) ->
	(ret_val_opt == (trunc_sat__ v_M v_N v_sx v_fN)) ->
	List.Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (option_to_list ret_val_opt).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
Lemma cvtop___is_wf : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop__ : cvtop__) (v_num_ : num_) (ret_val_lst : (seq num_)) (var_0 : (option (seq num_))),
	(fun_cvtop__ numtype_1 numtype_2 v_cvtop__ v_num_ var_0) ->
	(wf_cvtop__ numtype_1 numtype_2 v_cvtop__) ->
	(wf_num_ numtype_1 v_num_) ->
	(var_0 != None) ->
	(ret_val_lst == (!(var_0))) ->
	List.Forall (fun (ret_val : num_) => (wf_num_ numtype_2 ret_val)) ret_val_lst.
Proof.
	move => nt1 nt2 cop n ret var0 H Hc H1 Hne /eqP ->.
	have Hmap : forall (F : Fnn) (v_nt : numtype) (l : seq fN),
		(v_nt == (numtype_Fnn F)) ->
		List.Forall (fun x => wf_fN (sizenn (numtype_Fnn F)) x) l ->
		List.Forall (fun x => wf_num_ v_nt x) (seq.map (fun y => mk_num__1 F y) l).
	{ move => F v_nt l Hnt. elim: l => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ apply: num__case_1 | apply: IH ]. }
	have Hmapo : forall (I : Inn) (v_nt : numtype) (o : (option iN)),
		(v_nt == (numtype_Inn I)) ->
		((res_size (valtype_Inn I)) != None) ->
		List.Forall (fun x => wf_uN (!((res_size (valtype_Inn I)))) x) (option_to_list o) ->
		List.Forall (fun x => wf_num_ v_nt x) (list_ num_ (option_map (fun y => mk_num__0 I y) o)).
	{ move => I v_nt o Hnt Hs Ho. case: o Ho => [x| ] Ho; last by apply: List.Forall_nil.
		inversion Ho; subst.
		by apply: List.Forall_cons; [ apply: num__case_0 | apply: List.Forall_nil ]. }
	case: H Hc H1 Hne => *; simpl.
	all: repeat match goal with | [ Hx : wf_num_ _ _ |- _ ] => inversion Hx; subst; clear Hx end.
	all: try (by apply: List.Forall_nil).
	all: try (apply: List.Forall_cons;
		[ first [ (apply: num__case_0;
				[ by []
				| first [ ((eapply extend___is_wf; only 2: by apply: eqxx); eassumption)
					| ((eapply wrap___is_wf; only 2: by apply: eqxx); eassumption) ]
				| by [] ])
			| (apply: num__case_1;
				[ ((eapply convert___is_wf; only 2: by apply: eqxx); eassumption)
				| by [] ])
			| ((eapply reinterpret___is_wf; only 2: by apply: eqxx);
				first [ by apply: num__case_0 | by apply: num__case_1 ]) ]
		| by apply: List.Forall_nil ]).
	all: try (apply: Hmap;
		[ by []
		| first [ ((eapply promote___is_wf; only 2: by apply: eqxx); eassumption)
			| ((eapply demote___is_wf; only 2: by apply: eqxx); eassumption) ] ]).
	all: try (apply: Hmapo;
		[ by [] | by []
		| first [ ((eapply trunc___is_wf; only 2: by apply: eqxx); eassumption)
			| ((eapply trunc_sat___is_wf; only 2: by apply: eqxx); eassumption) ] ]).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.6-62.15 *)
Axiom narrow___is_wf : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : iN) (ret_val : iN),
	(wf_uN v_M v_iN) ->
	(ret_val == (narrow__ v_M v_N v_sx v_iN)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.6-76.13 *)
Axiom ibits__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val_lst : (seq bit)),
	(wf_uN v_N v_iN) ->
	(ret_val_lst == (ibits_ v_N v_iN)) ->
	List.Forall (fun (ret_val : bit) => (wf_bit ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.6-77.13 *)
Axiom fbits__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq bit)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fbits_ v_N v_fN)) ->
	List.Forall (fun (ret_val : bit) => (wf_bit ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.6-78.14 *)
Axiom ibytes__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val_lst : (seq byte)),
	(wf_uN v_N v_iN) ->
	(ret_val_lst == (ibytes_ v_N v_iN)) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.6-79.14 *)
Axiom fbytes__is_wf : forall (v_N : res_N) (v_fN : fN) (ret_val_lst : (seq byte)),
	(wf_fN v_N v_fN) ->
	(ret_val_lst == (fbytes_ v_N v_fN)) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.6-80.14 *)
Axiom nbytes__is_wf : forall (v_numtype : numtype) (v_num_ : num_) (ret_val_lst : (seq byte)),
	(wf_num_ v_numtype v_num_) ->
	(ret_val_lst == (nbytes_ v_numtype v_num_)) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.6-81.14 *)
Axiom vbytes__is_wf : forall (v_vectype : vectype) (v_vec_ : vec_) (ret_val_lst : (seq byte)),
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) v_vec_) ->
	(ret_val_lst == (vbytes_ v_vectype v_vec_)) ->
	List.Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.6-83.17 *)
Axiom inv_ibits__is_wf : forall (v_N : res_N) (var_0_lst : (seq bit)) (ret_val : iN),
	List.Forall (fun (var_0 : bit) => (wf_bit var_0)) var_0_lst ->
	(ret_val == (inv_ibits_ v_N var_0_lst)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.6-84.17 *)
Axiom inv_fbits__is_wf : forall (v_N : res_N) (var_0_lst : (seq bit)) (ret_val : fN),
	List.Forall (fun (var_0 : bit) => (wf_bit var_0)) var_0_lst ->
	(ret_val == (inv_fbits_ v_N var_0_lst)) ->
	(wf_fN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.6-85.18 *)
Axiom inv_ibytes__is_wf : forall (v_N : res_N) (var_0_lst : (seq byte)) (ret_val : iN),
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (inv_ibytes_ v_N var_0_lst)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.6-86.18 *)
Axiom inv_fbytes__is_wf : forall (v_N : res_N) (var_0_lst : (seq byte)) (ret_val : fN),
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (inv_fbytes_ v_N var_0_lst)) ->
	(wf_fN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.6-87.18 *)
Axiom inv_nbytes__is_wf : forall (v_numtype : numtype) (var_0_lst : (seq byte)) (ret_val : num_),
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (inv_nbytes_ v_numtype var_0_lst)) ->
	(wf_num_ v_numtype ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.6-88.18 *)
Axiom inv_vbytes__is_wf : forall (v_vectype : vectype) (var_0_lst : (seq byte)) (ret_val : vec_),
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (inv_vbytes_ v_vectype var_0_lst)) ->
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.6-110.12 *)
Axiom inot__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (inot_ v_N v_iN)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.6-111.12 *)
Axiom irev__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (irev_ v_N v_iN)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.6-113.15 *)
Axiom iandnot__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iandnot_ v_N v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.6-124.12 *)
Lemma inez__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : u32),
	(wf_uN v_N v_iN) ->
	(ret_val == (inez_ v_N v_iN)) ->
	(wf_uN 32%N ret_val).
Proof.
	move => v_N v_iN ret_val H /eqP ->.
	apply: uN_case_0. by case: ((v_iN :> N) == 0%N).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.6-131.18 *)
Axiom ibitselect__is_wf : forall (v_N : res_N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(wf_uN v_N iN_1) ->
	(ret_val == (ibitselect_ v_N v_iN iN_0 iN_1)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.6-133.12 *)
Lemma ineg__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(ret_val == (ineg_ v_N v_iN)) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_iN ret_val H /eqP ->.
	have Hpow : (1 <= (2%N ^ v_N)%BN)%BN by apply: N.pow_lower_bound.
	have Hsub : (((((2%N ^ v_N)%BN : Z) - (1%N : Z))%Z : N)) = ((2%N ^ v_N)%BN - 1%N)%BN
		by rewrite -Znat.N2Z.inj_sub // Znat.N2Z.id.
	have HposZ : (0 < ((2%N ^ v_N)%BN : Z))%Z.
	{ have Hp : (0 < (2%N ^ v_N)%BN)%BN by apply/N.neq_0_lt_0; apply: N.pow_nonzero.
		by move/Znat.N2Z.inj_lt: Hp. }
	apply: uN_case_0.
	rewrite Hsub /N_geb.
	apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
	apply/N.leb_spec0. rewrite N.sub_1_r. apply: N.lt_le_pred.
	have [Hlo Hhi] := Z.mod_pos_bound ((((2%N ^ v_N)%BN : Z) - ((v_iN :> N) : Z))%Z) _ HposZ.
	have Hres := (proj1 (Znat.Z2N.inj_lt _ _ Hlo (Z.lt_le_incl _ _ HposZ)) Hhi).
	by rewrite Znat.N2Z.id in Hres.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
Lemma iabs__is_wf : forall (v_N : res_N) (v_iN : iN) (ret_val : iN) (var_0 : iN),
	(fun_iabs_ v_N v_iN var_0) ->
	(wf_uN v_N v_iN) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_iN ret_val var_0 H H1 /eqP ->.
	case: H H1 => v_N0 i_1 z Hsig H1.
	case: ifP => _ //.
	by apply: (ineg__is_wf v_N0 i_1).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
Lemma imin__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN),
	(fun_imin_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val var_0 H H1 H2 /eqP ->.
	case: H H1 H2 => * //.
	by case: ifP.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
Lemma imax__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN),
	(fun_imax_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val var_0 H H1 H2 /eqP ->.
	case: H H1 H2 => * //.
	by case: ifP.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
Lemma iadd_sat__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN),
	(fun_iadd_sat_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val var_0 H Hw1 Hw2 /eqP ->.
	have Hto : forall m : N, ((((m : Z) - (1%N : Z))%Z : N) = (m - 1)%BN).
	{ case => [ |p] //. by rewrite -Znat.N2Z.inj_sub ?Znat.N2Z.id //; apply/N.neq_0_le_1. }
	have Hp : forall (vN : res_N), (0 < (2%N ^ vN)%BN)%BN.
	{ by move => vN; apply/N.neq_0_lt_0; apply: N.pow_nonzero. }
	have HtoN : forall (vN : res_N) (z2 : Z),
		(z2 < ((2%N ^ vN)%BN : Z))%Z -> (((z2 : N)) < (2%N ^ vN)%BN)%BN.
	{ move => vN; case => [ |q|q] Hz //=; try exact: Hp.
		have Hnn : (0 <= Z.pos q)%Z by [].
		have := (proj1 (Znat.Z2N.inj_lt (Z.pos q) _ Hnn (Znat.N2Z.is_nonneg _)) Hz).
		by rewrite Znat.N2Z.id. }
	have Hbnd : forall (vN : res_N) (x : N), (x < (2%N ^ vN)%BN)%BN -> wf_uN vN (mk_uN x).
	{ move => vN x Hx. apply: uN_case_0. rewrite Hto /N_geb.
		apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		by apply/N.leb_spec0; rewrite N.sub_1_r; apply: N.lt_le_pred. }
	have Hle : forall (vN : res_N),
		((2%N ^ ((((vN : Z) - (1%N : Z))%Z : N)))%BN <= (2%N ^ vN)%BN)%BN.
	{ move => vN. apply: N.pow_le_mono_r => //. rewrite Hto. exact: N.le_sub_l. }
	have Hinv : forall (vN : res_N) (z : Z) (m : N), fun_inv_signed_ vN z m -> wf_uN vN (mk_uN m).
	{ move => vN0 z m Hi. case: Hi => vN i /andP [Ha Hb]; apply: Hbnd; apply: HtoN.
		- have Hlt2 : (i < ((2%N ^ ((((vN : Z) - (1%N : Z))%Z : N)))%BN : Z))%Z
				by apply: (proj1 (Z.ltb_lt _ _) Hb).
			apply: (Z.lt_le_trans _ _ _ Hlt2). by apply/Znat.N2Z.inj_le; apply: Hle.
		- rewrite -{2}(Z.add_0_l ((2%N ^ vN)%BN : Z)).
			by apply: (proj1 (Z.add_lt_mono_r _ _ _) (proj1 (Z.ltb_lt _ _) Hb)). }
	have Hsatu : forall (vN : res_N) (z : Z), wf_uN vN (mk_uN (sat_u_ vN z)).
	{ move => vN z. rewrite /sat_u_. apply: Hbnd.
		case: ifP => Hlt; first exact: Hp.
		case: ifP => Hgt.
		- rewrite Hto. apply: N.sub_lt; last by []. by apply: N.pow_lower_bound.
		- apply: HtoN.
			have H1 : (z <= (((2%N ^ vN)%BN : Z) - (1%N : Z))%Z)%Z
				by move: Hgt; rewrite Z.gtb_ltb => /Z.ltb_ge.
			apply: (Z.le_lt_trans _ _ _ H1). by apply: (proj1 (Z.lt_sub_pos _ _)). }
	case: H Hw1 Hw2 => *; first by apply: Hsatu.
	by apply: Hinv; eassumption.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
Lemma isub_sat__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN),
	(fun_isub_sat_ v_N v_sx v_iN iN_0 var_0) ->
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == var_0) ->
	(wf_uN v_N ret_val).
Proof.
	move => v_N v_sx v_iN iN_0 ret_val var_0 H Hw1 Hw2 /eqP ->.
	have Hto : forall m : N, ((((m : Z) - (1%N : Z))%Z : N) = (m - 1)%BN).
	{ case => [ |p] //. by rewrite -Znat.N2Z.inj_sub ?Znat.N2Z.id //; apply/N.neq_0_le_1. }
	have Hp : forall (vN : res_N), (0 < (2%N ^ vN)%BN)%BN.
	{ by move => vN; apply/N.neq_0_lt_0; apply: N.pow_nonzero. }
	have HtoN : forall (vN : res_N) (z2 : Z),
		(z2 < ((2%N ^ vN)%BN : Z))%Z -> (((z2 : N)) < (2%N ^ vN)%BN)%BN.
	{ move => vN; case => [ |q|q] Hz //=; try exact: Hp.
		have Hnn : (0 <= Z.pos q)%Z by [].
		have := (proj1 (Znat.Z2N.inj_lt (Z.pos q) _ Hnn (Znat.N2Z.is_nonneg _)) Hz).
		by rewrite Znat.N2Z.id. }
	have Hbnd : forall (vN : res_N) (x : N), (x < (2%N ^ vN)%BN)%BN -> wf_uN vN (mk_uN x).
	{ move => vN x Hx. apply: uN_case_0. rewrite Hto /N_geb.
		apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		by apply/N.leb_spec0; rewrite N.sub_1_r; apply: N.lt_le_pred. }
	have Hle : forall (vN : res_N),
		((2%N ^ ((((vN : Z) - (1%N : Z))%Z : N)))%BN <= (2%N ^ vN)%BN)%BN.
	{ move => vN. apply: N.pow_le_mono_r => //. rewrite Hto. exact: N.le_sub_l. }
	have Hinv : forall (vN : res_N) (z : Z) (m : N), fun_inv_signed_ vN z m -> wf_uN vN (mk_uN m).
	{ move => vN0 z m Hi. case: Hi => vN i /andP [Ha Hb]; apply: Hbnd; apply: HtoN.
		- have Hlt2 : (i < ((2%N ^ ((((vN : Z) - (1%N : Z))%Z : N)))%BN : Z))%Z
				by apply: (proj1 (Z.ltb_lt _ _) Hb).
			apply: (Z.lt_le_trans _ _ _ Hlt2). by apply/Znat.N2Z.inj_le; apply: Hle.
		- rewrite -{2}(Z.add_0_l ((2%N ^ vN)%BN : Z)).
			by apply: (proj1 (Z.add_lt_mono_r _ _ _) (proj1 (Z.ltb_lt _ _) Hb)). }
	have Hsatu : forall (vN : res_N) (z : Z), wf_uN vN (mk_uN (sat_u_ vN z)).
	{ move => vN z. rewrite /sat_u_. apply: Hbnd.
		case: ifP => Hlt; first exact: Hp.
		case: ifP => Hgt.
		- rewrite Hto. apply: N.sub_lt; last by []. by apply: N.pow_lower_bound.
		- apply: HtoN.
			have H1 : (z <= (((2%N ^ vN)%BN : Z) - (1%N : Z))%Z)%Z
				by move: Hgt; rewrite Z.gtb_ltb => /Z.ltb_ge.
			apply: (Z.le_lt_trans _ _ _ H1). by apply: (proj1 (Z.lt_sub_pos _ _)). }
	case: H Hw1 Hw2 => *; first by apply: Hsatu.
	by apply: Hinv; eassumption.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.6-138.13 *)
Axiom iavgr__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iavgr_ v_N v_sx v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.6-139.20 *)
Axiom iq15mulr_sat__is_wf : forall (v_N : res_N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN),
	(wf_uN v_N v_iN) ->
	(wf_uN v_N iN_0) ->
	(ret_val == (iq15mulr_sat_ v_N v_sx v_iN iN_0)) ->
	(wf_uN v_N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.6-221.13 *)
Axiom fpmin__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fpmin_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.6-222.13 *)
Axiom fpmax__is_wf : forall (v_N : res_N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (seq fN)),
	(wf_fN v_N v_fN) ->
	(wf_fN v_N fN_0) ->
	(ret_val_lst == (fpmax_ v_N v_fN fN_0)) ->
	List.Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.6-323.15 *)
Lemma packnum__is_wf : forall (v_lanetype : lanetype) (v_num_ : num_) (ret_val : lane_),
	(wf_num_ (unpack v_lanetype) v_num_) ->
	((packnum_ v_lanetype v_num_) != None) ->
	(ret_val == (!((packnum_ v_lanetype v_num_)))) ->
	(wf_lane_ v_lanetype ret_val).
Proof.
	move => lt n ret H Hne /eqP ->.
	case: lt H Hne => H Hne; destruct n as [inn i|fnn f]; try destruct inn; try destruct fnn; simpl in *.
	all: try by move: Hne; rewrite eqxx.
	all: repeat match goal with | [ Hx : wf_num_ _ _ |- _ ] => inversion Hx; subst; clear Hx end.
	all: first [ (apply: lane__case_0; [ done | done ]) | (apply: lane__case_1; [ done | done ])
		| (apply: lane__case_0; last by []; (eapply wrap___is_wf; only 2: by apply: eqxx); eassumption) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:329.6-329.17 *)
Lemma unpacknum__is_wf : forall (v_lanetype : lanetype) (v_lane_ : lane_) (ret_val : num_),
	(wf_lane_ v_lanetype v_lane_) ->
	((unpacknum_ v_lanetype v_lane_) != None) ->
	(ret_val == (!((unpacknum_ v_lanetype v_lane_)))) ->
	(wf_num_ (unpack v_lanetype) ret_val).
Proof.
	move => lt l ret H Hne /eqP ->.
	case: lt H Hne => H Hne;
		destruct l as [jn c|fn c]; try destruct jn; try destruct fn;
		simpl in H, Hne |- *.
	all: try (by move: Hne; rewrite eqxx).
	all: repeat match goal with | [ Hx : wf_lane_ _ _ |- _ ] => inversion Hx; subst; clear Hx end.
	all: first [ (apply: num__case_0; [ by [] | done | by [] ]) | (apply: num__case_1; [ done | by [] ])
		| (apply: num__case_0; [ by [] | | by [] ]; (eapply extend___is_wf; only 2: by apply: eqxx); eassumption) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:338.6-338.13 *)
Axiom lanes__is_wf : forall (v_shape : shape) (v_vec_ : vec_) (ret_val_lst : (seq lane_)),
	(wf_shape v_shape) ->
	(wf_uN 128%N v_vec_) ->
	(ret_val_lst == (lanes_ v_shape v_vec_)) ->
	List.Forall (fun (ret_val : lane_) => (wf_lane_ (fun_lanetype v_shape) ret_val)) ret_val_lst.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:341.6-341.17 *)
Axiom inv_lanes__is_wf : forall (v_shape : shape) (var_0_lst : (seq lane_)) (ret_val : vec_),
	(wf_shape v_shape) ->
	List.Forall (fun (var_0 : lane_) => (wf_lane_ (fun_lanetype v_shape) var_0)) var_0_lst ->
	(ret_val == (inv_lanes_ v_shape var_0_lst)) ->
	(wf_uN 128%N ret_val).

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.6-364.14 *)
Lemma vvunop__is_wf : forall (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) (ret_val : vec_),
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) v_vec_) ->
	(ret_val == (vvunop_ v_vectype v_vvunop v_vec_)) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) ret_val).
Proof.
	move => v_vectype v_vvunop v_vec_ ret_val Hs Hv /eqP ->.
	case: v_vectype Hs Hv => Hs Hv. case: v_vvunop => /=.
	by (eapply inot__is_wf; only 2: by apply: eqxx); eassumption.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.6-366.15 *)
Lemma vvbinop__is_wf : forall (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_),
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) v_vec_) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) vec__0) ->
	(ret_val == (vvbinop_ v_vectype v_vvbinop v_vec_ vec__0)) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) ret_val).
Proof.
	move => v_vectype v_vvbinop v_vec_ vec__0 ret_val Hs H1 H2 /eqP ->.
	case: v_vectype Hs H1 H2 => Hs H1 H2. case: v_vvbinop => /=.
	all: first [ ((eapply iand__is_wf; only 3: by apply: eqxx); eassumption)
		| ((eapply iandnot__is_wf; only 3: by apply: eqxx); eassumption)
		| ((eapply ior__is_wf; only 3: by apply: eqxx); eassumption)
		| ((eapply ixor__is_wf; only 3: by apply: eqxx); eassumption) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:368.6-368.16 *)
Lemma vvternop__is_wf : forall (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val : vec_),
	((res_size (valtype_vectype v_vectype)) != None) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) v_vec_) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) vec__0) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) vec__1) ->
	(ret_val == (vvternop_ v_vectype v_vvternop v_vec_ vec__0 vec__1)) ->
	(wf_uN (!((res_size (valtype_vectype v_vectype)))) ret_val).
Proof.
	move => v_vectype v_vvternop v_vec_ vec__0 vec__1 ret_val Hs H1 H2 H3 /eqP ->.
	case: v_vectype Hs H1 H2 H3 => Hs H1 H2 H3. case: v_vvternop => /=.
	by (eapply ibitselect__is_wf; only 4: by apply: eqxx); eassumption.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.13 *)
Lemma vunop__is_wf : forall (v_shape : shape) (v_vunop_ : vunop_) (v_vec_ : vec_) (ret_val_lst : (seq vec_)) (var_0 : (option (seq vec_))),
	(fun_vunop_ v_shape v_vunop_ v_vec_ var_0) ->
	(wf_shape v_shape) ->
	(wf_vunop_ v_shape v_vunop_) ->
	(wf_uN 128%N v_vec_) ->
	(var_0 != None) ->
	(ret_val_lst == (!(var_0))) ->
	List.Forall (fun (ret_val : vec_) => (wf_uN 128%N ret_val)) ret_val_lst.
Proof.
	move => v_shape v_vunop_ v_vec_ ret_val_lst var_0 H Hsh Hop Hvec Hne /eqP ->.
	have Hmono : forall (T : Type) (P Q : T -> Prop) (l : seq T),
		List.Forall P l -> (forall x, P x -> Q x) -> List.Forall Q l.
	{ move => T P Q. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl] Hpq.
		by apply: List.Forall_cons; [ apply: Hpq | apply: IH ]. }
	have Hfmap : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall (fun x => P (f x)) l -> List.Forall P (seq.map f l).
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hsp2 : forall (X : eqType) (P : X -> Prop) (w : X) (lls : seq (seq X)),
		P w -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct2_ X w lls).
	{ move => X P w. elim => [ |l lls IH] //= Hw /List.Forall_cons_iff [Hl Hlls].
		by apply: List.Forall_cons; [ apply: List.Forall_cons | apply: IH ]. }
	have Hsp1 : forall (X : eqType) (P : X -> Prop) (l : seq X) (lls : seq (seq X)),
		List.Forall P l -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct1_ X l lls).
	{ move => X P. elim => [ |w l IH] lls //= /List.Forall_cons_iff [Hw Hl] Hlls.
		by apply/List.Forall_app; split; [ apply: Hsp2 | apply: IH ]. }
	have Hsp : forall (X : eqType) (P : X -> Prop) (lls : seq (seq X)),
		List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct_ X lls).
	{ move => X P. elim => [ |l lls IH] /=.
		- by move => _; apply: List.Forall_cons; apply: List.Forall_nil.
		- move => /List.Forall_cons_iff [Hl Hlls]. by apply: Hsp1; [ | apply: IH ]. }
	have Hfin : forall (sh : shape) (lls : seq (seq lane_)),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		List.Forall (fun v => wf_uN 128%N v) (seq.map (fun l => inv_lanes_ sh l) lls).
	{ move => sh lls Hsh0. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hf2 : forall (T U : Type) (R : T -> U -> Prop) (ll : seq U) (l1 l2 : seq T),
		List.Forall2 R l1 ll -> List.Forall2 R l2 ll ->
		(forall a b u, R a u -> R b u -> a = b) -> l1 = l2.
	{ move => T U R ll l1 l2 H1. elim: H1 l2 => [ |x y l l' Hxy H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 l2' ll2 Hxy2 H2' E1 E2]; subst.
			by rewrite (Hfun _ _ _ Hxy Hxy2) (IH _ H2' Hfun). }
	have Hsig : forall (vN : res_N) (i : N) (a b : Z),
		fun_signed_ vN i a -> fun_signed_ vN i b -> a = b.
	{ move => vN i a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (N.ltb ?u ?X), Hy : is_true (andb (N.leb ?X ?u) _) |- _ ] =>
				move: Hy => /andP [Hy _];
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hx) (proj1 (N.leb_le _ _) Hy));
				apply: N.lt_irrefl
			end. }
	have Hinvsig : forall (vN : res_N) (z : Z) (a b : N),
		fun_inv_signed_ vN z a -> fun_inv_signed_ vN z b -> a = b.
	{ move => vN z a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (andb (Z.leb _ ?u) _), Hy : is_true (andb _ (Z.ltb ?u _)) |- _ ] =>
				move: (Hx) => /andP [Hx1 _]; move: (Hy) => /andP [_ Hy1];
				move: (Z.le_lt_trans _ _ _ (proj1 (Z.leb_le _ _) Hx1) (proj1 (Z.ltb_lt _ _) Hy1));
				apply: Z.lt_irrefl
			end. }
	have Hiabs : forall (vN : res_N) (i a b : iN),
		fun_iabs_ vN i a -> fun_iabs_ vN i b -> a = b.
	{ move => vN i a b Ha Hb. inversion Ha; inversion Hb; subst.
		by match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				rewrite (Hsig _ _ _ _ Hx Hy) end. }
	case: H Hsh Hop Hvec Hne => *.
	all: try by apply: List.Forall_nil.
	all: repeat match goal with
		| [ Ha : List.Forall2 ?R ?l1 ?ll, Hb : List.Forall2 ?R ?l2 ?ll |- _ ] =>
			tryif constr_eq l1 l2 then fail else
			(have Heq : l1 = l2;
				[ apply: (Hf2 _ _ R ll l1 l2 Ha Hb); move => x y u Hx Hy;
					exact: (Hiabs _ _ _ _ Hx Hy)
				| subst ])
		end.
	all: repeat match goal with | [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end.
	all: subst.
	all: first
		[ (apply: List.Forall_cons;
			[ ((eapply inv_lanes__is_wf; only 3: by apply: eqxx);
				[ eassumption | (apply Hfmap; eassumption) ])
			| by apply: List.Forall_nil ])
		| (apply Hfin;
			[ eassumption
			| (apply Hsp; apply Hfmap;
				match goal with
				| [ Hh : List.Forall _ _ |- _ ] =>
					(eapply Hmono; [ exact: Hh | move => x Hx; apply Hfmap; exact: Hx ])
				end) ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
Lemma vbinop__is_wf : forall (v_shape : shape) (v_vbinop_ : vbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : (seq vec_)) (var_0 : (option (seq vec_))),
	(fun_vbinop_ v_shape v_vbinop_ v_vec_ vec__0 var_0) ->
	(wf_shape v_shape) ->
	(wf_vbinop_ v_shape v_vbinop_) ->
	(wf_uN 128%N v_vec_) ->
	(wf_uN 128%N vec__0) ->
	(var_0 != None) ->
	(ret_val_lst == (!(var_0))) ->
	List.Forall (fun (ret_val : vec_) => (wf_uN 128%N ret_val)) ret_val_lst.
Proof.
	move => v_shape v_vbinop_ v_vec_ vec__0 ret_val_lst var_0 H Hsh Hop Hvec1 Hvec2 Hne /eqP ->.
	have Hmono : forall (T : Type) (P Q : T -> Prop) (l : seq T),
		List.Forall P l -> (forall x, P x -> Q x) -> List.Forall Q l.
	{ move => T P Q. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl] Hpq.
		by apply: List.Forall_cons; [ apply: Hpq | apply: IH ]. }
	have Hfmap : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall (fun x => P (f x)) l -> List.Forall P (seq.map f l).
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hsp2 : forall (X : eqType) (P : X -> Prop) (w : X) (lls : seq (seq X)),
		P w -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct2_ X w lls).
	{ move => X P w. elim => [ |l lls IH] //= Hw /List.Forall_cons_iff [Hl Hlls].
		by apply: List.Forall_cons; [ apply: List.Forall_cons | apply: IH ]. }
	have Hsp1 : forall (X : eqType) (P : X -> Prop) (l : seq X) (lls : seq (seq X)),
		List.Forall P l -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct1_ X l lls).
	{ move => X P. elim => [ |w l IH] lls //= /List.Forall_cons_iff [Hw Hl] Hlls.
		by apply/List.Forall_app; split; [ apply: Hsp2 | apply: IH ]. }
	have Hsp : forall (X : eqType) (P : X -> Prop) (lls : seq (seq X)),
		List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct_ X lls).
	{ move => X P. elim => [ |l lls IH] /=.
		- by move => _; apply: List.Forall_cons; apply: List.Forall_nil.
		- move => /List.Forall_cons_iff [Hl Hlls]. by apply: Hsp1; [ | apply: IH ]. }
	have Hfin : forall (sh : shape) (lls : seq (seq lane_)),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		List.Forall (fun v => wf_uN 128%N v) (seq.map (fun l => inv_lanes_ sh l) lls).
	{ move => sh lls Hsh0. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hf2 : forall (T U : Type) (R : T -> U -> Prop) (ll : seq U) (l1 l2 : seq T),
		List.Forall2 R l1 ll -> List.Forall2 R l2 ll ->
		(forall a b u, R a u -> R b u -> a = b) -> l1 = l2.
	{ move => T U R ll l1 l2 H1. elim: H1 l2 => [ |x y l l' Hxy H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 l2' ll2 Hxy2 H2' E1 E2]; subst.
			by rewrite (Hfun _ _ _ Hxy Hxy2) (IH _ H2' Hfun). }
	have Hsig : forall (vN : res_N) (i : N) (a b : Z),
		fun_signed_ vN i a -> fun_signed_ vN i b -> a = b.
	{ move => vN i a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (N.ltb ?u ?X), Hy : is_true (andb (N.leb ?X ?u) _) |- _ ] =>
				move: Hy => /andP [Hy _];
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hx) (proj1 (N.leb_le _ _) Hy));
				apply: N.lt_irrefl
			end. }
	have Hinvsig : forall (vN : res_N) (z : Z) (a b : N),
		fun_inv_signed_ vN z a -> fun_inv_signed_ vN z b -> a = b.
	{ move => vN z a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (andb (Z.leb _ ?u) _), Hy : is_true (andb _ (Z.ltb ?u _)) |- _ ] =>
				move: (Hx) => /andP [Hx1 _]; move: (Hy) => /andP [_ Hy1];
				move: (Z.le_lt_trans _ _ _ (proj1 (Z.leb_le _ _) Hx1) (proj1 (Z.ltb_lt _ _) Hy1));
				apply: Z.lt_irrefl
			end. }
	have Hzip : forall (T U V : Type) (P : V -> Prop) (f : T -> U -> V)
		(l1 : seq T) (l2 : seq U),
		List.Forall2 (fun a b => P (f a b)) l1 l2 -> List.Forall P (list_zipWith f l1 l2).
	{ move => T U V P f l1 l2 Hz. rewrite /list_zipWith.
		elim: Hz => [ |x y l l' Hxy Hz IH] //=. by apply: List.Forall_cons. }
	have Hmono2 : forall (T U : Type) (P Q : T -> U -> Prop) (l1 : seq T) (l2 : seq U),
		List.Forall2 P l1 l2 -> (forall x y, P x y -> Q x y) -> List.Forall2 Q l1 l2.
	{ move => T U P Q l1 l2 Hz Hpq. elim: Hz => [ |x y l l' Hxy Hz IH].
		- by apply: List.Forall2_nil.
		- by apply: List.Forall2_cons; [ apply: Hpq | ]. }
	have Hf3 : forall (T U V : Type) (R : T -> U -> V -> Prop) (lu : seq U) (lv : seq V)
		(l1 l2 : seq T),
		List_Forall3 R l1 lu lv -> List_Forall3 R l2 lu lv ->
		(forall a b u v, R a u v -> R b u v -> a = b) -> l1 = l2.
	{ move => T U V R lu lv l1 l2 H1. elim: H1 l2 => [ |x y z l l' l'' Hxyz H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 z2 l2' lu2 lv2 Hxyz2 H2' E1 E2 E3]; subst.
			by rewrite (Hfun _ _ _ _ Hxyz Hxyz2) (IH _ H2' Hfun). }
	have Hordfun : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_imin_ n0 s0 p q r1 -> fun_imin_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: try (exfalso;
			match goal with
			| [ Hx : is_true (N.leb ?u ?v), Hy : is_true (N_gtb ?u ?v) |- _ ] =>
				rewrite /N_gtb in Hy;
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hy) (proj1 (N.leb_le _ _) Hx));
				apply: N.lt_irrefl
			end).
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Hmaxfun : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_imax_ n0 s0 p q r1 -> fun_imax_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: try (exfalso;
			match goal with
			| [ Hx : is_true (N_geb ?u ?v), Hy : is_true (N.ltb ?u ?v) |- _ ] =>
				rewrite /N_geb in Hx;
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hy) (proj1 (N.leb_le _ _) Hx));
				apply: N.lt_irrefl
			end).
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Haddsat : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_iadd_sat_ n0 s0 p q r1 -> fun_iadd_sat_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: repeat match goal with
			| [ Hx : fun_inv_signed_ ?n ?k ?u, Hy : fun_inv_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hinvsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Hsubsat : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_isub_sat_ n0 s0 p q r1 -> fun_isub_sat_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: repeat match goal with
			| [ Hx : fun_inv_signed_ ?n ?k ?u, Hy : fun_inv_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hinvsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	case: H Hsh Hop Hvec1 Hvec2 Hne => *.
	all: try by apply: List.Forall_nil.
	all: repeat match goal with
		| [ Ha : List_Forall3 ?R ?l1 ?lu ?lv, Hb : List_Forall3 ?R ?l2 ?lu ?lv |- _ ] =>
			tryif constr_eq l1 l2 then fail else
			(have Heq : l1 = l2;
				[ apply: (Hf3 _ _ _ R lu lv l1 l2 Ha Hb); move => a b u v Hx Hy;
					first [ exact: (Hordfun _ _ _ _ _ _ Hx Hy)
						| exact: (Hmaxfun _ _ _ _ _ _ Hx Hy)
						| exact: (Haddsat _ _ _ _ _ _ Hx Hy)
						| exact: (Hsubsat _ _ _ _ _ _ Hx Hy) ]
				| subst ])
		end.
	all: repeat match goal with | [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end.
	all: subst.
	all: first
		[ (apply: List.Forall_cons;
			[ ((eapply inv_lanes__is_wf; only 3: by apply: eqxx);
				[ eassumption
				| first [ (apply Hfmap; eassumption) | (apply Hzip; eassumption) ] ])
			| by apply: List.Forall_nil ])
		| (apply Hfin;
			[ eassumption
			| (apply Hsp; apply Hzip;
				match goal with
				| [ Hh : List.Forall2 _ _ _ |- _ ] =>
					(eapply Hmono2; [ exact: Hh | move => x y Hxy; apply Hfmap; exact: Hxy ])
				end) ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.14 *)
Lemma vrelop__is_wf : forall (v_shape : shape) (v_vrelop_ : vrelop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : (option vec_)),
	(fun_vrelop_ v_shape v_vrelop_ v_vec_ vec__0 var_0) ->
	(wf_shape v_shape) ->
	(wf_vrelop_ v_shape v_vrelop_) ->
	(wf_uN 128%N v_vec_) ->
	(wf_uN 128%N vec__0) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_uN 128%N ret_val).
Proof.
	move => v_shape v_vrelop_ v_vec_ vec__0 ret_val var_0 H Hsh Hop Hvec1 Hvec2 Hne /eqP ->.
	have Hmono : forall (T : Type) (P Q : T -> Prop) (l : seq T),
		List.Forall P l -> (forall x, P x -> Q x) -> List.Forall Q l.
	{ move => T P Q. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl] Hpq.
		by apply: List.Forall_cons; [ apply: Hpq | apply: IH ]. }
	have Hfmap : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall (fun x => P (f x)) l -> List.Forall P (seq.map f l).
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hsp2 : forall (X : eqType) (P : X -> Prop) (w : X) (lls : seq (seq X)),
		P w -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct2_ X w lls).
	{ move => X P w. elim => [ |l lls IH] //= Hw /List.Forall_cons_iff [Hl Hlls].
		by apply: List.Forall_cons; [ apply: List.Forall_cons | apply: IH ]. }
	have Hsp1 : forall (X : eqType) (P : X -> Prop) (l : seq X) (lls : seq (seq X)),
		List.Forall P l -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct1_ X l lls).
	{ move => X P. elim => [ |w l IH] lls //= /List.Forall_cons_iff [Hw Hl] Hlls.
		by apply/List.Forall_app; split; [ apply: Hsp2 | apply: IH ]. }
	have Hsp : forall (X : eqType) (P : X -> Prop) (lls : seq (seq X)),
		List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct_ X lls).
	{ move => X P. elim => [ |l lls IH] /=.
		- by move => _; apply: List.Forall_cons; apply: List.Forall_nil.
		- move => /List.Forall_cons_iff [Hl Hlls]. by apply: Hsp1; [ | apply: IH ]. }
	have Hfin : forall (sh : shape) (lls : seq (seq lane_)),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		List.Forall (fun v => wf_uN 128%N v) (seq.map (fun l => inv_lanes_ sh l) lls).
	{ move => sh lls Hsh0. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hf2 : forall (T U : Type) (R : T -> U -> Prop) (ll : seq U) (l1 l2 : seq T),
		List.Forall2 R l1 ll -> List.Forall2 R l2 ll ->
		(forall a b u, R a u -> R b u -> a = b) -> l1 = l2.
	{ move => T U R ll l1 l2 H1. elim: H1 l2 => [ |x y l l' Hxy H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 l2' ll2 Hxy2 H2' E1 E2]; subst.
			by rewrite (Hfun _ _ _ Hxy Hxy2) (IH _ H2' Hfun). }
	have Hsig : forall (vN : res_N) (i : N) (a b : Z),
		fun_signed_ vN i a -> fun_signed_ vN i b -> a = b.
	{ move => vN i a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (N.ltb ?u ?X), Hy : is_true (andb (N.leb ?X ?u) _) |- _ ] =>
				move: Hy => /andP [Hy _];
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hx) (proj1 (N.leb_le _ _) Hy));
				apply: N.lt_irrefl
			end. }
	have Hinvsig : forall (vN : res_N) (z : Z) (a b : N),
		fun_inv_signed_ vN z a -> fun_inv_signed_ vN z b -> a = b.
	{ move => vN z a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (andb (Z.leb _ ?u) _), Hy : is_true (andb _ (Z.ltb ?u _)) |- _ ] =>
				move: (Hx) => /andP [Hx1 _]; move: (Hy) => /andP [_ Hy1];
				move: (Z.le_lt_trans _ _ _ (proj1 (Z.leb_le _ _) Hx1) (proj1 (Z.ltb_lt _ _) Hy1));
				apply: Z.lt_irrefl
			end. }
	have Hzip : forall (T U V : Type) (P : V -> Prop) (f : T -> U -> V)
		(l1 : seq T) (l2 : seq U),
		List.Forall2 (fun a b => P (f a b)) l1 l2 -> List.Forall P (list_zipWith f l1 l2).
	{ move => T U V P f l1 l2 Hz. rewrite /list_zipWith.
		elim: Hz => [ |x y l l' Hxy Hz IH] //=. by apply: List.Forall_cons. }
	have Hmono2 : forall (T U : Type) (P Q : T -> U -> Prop) (l1 : seq T) (l2 : seq U),
		List.Forall2 P l1 l2 -> (forall x y, P x y -> Q x y) -> List.Forall2 Q l1 l2.
	{ move => T U P Q l1 l2 Hz Hpq. elim: Hz => [ |x y l l' Hxy Hz IH].
		- by apply: List.Forall2_nil.
		- by apply: List.Forall2_cons; [ apply: Hpq | ]. }
	have Hf3 : forall (T U V : Type) (R : T -> U -> V -> Prop) (lu : seq U) (lv : seq V)
		(l1 l2 : seq T),
		List_Forall3 R l1 lu lv -> List_Forall3 R l2 lu lv ->
		(forall a b u v, R a u v -> R b u v -> a = b) -> l1 = l2.
	{ move => T U V R lu lv l1 l2 H1. elim: H1 l2 => [ |x y z l l' l'' Hxyz H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 z2 l2' lu2 lv2 Hxyz2 H2' E1 E2 E3]; subst.
			by rewrite (Hfun _ _ _ _ Hxyz Hxyz2) (IH _ H2' Hfun). }
	have Hordfun : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_imin_ n0 s0 p q r1 -> fun_imin_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: try (exfalso;
			match goal with
			| [ Hx : is_true (N.leb ?u ?v), Hy : is_true (N_gtb ?u ?v) |- _ ] =>
				rewrite /N_gtb in Hy;
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hy) (proj1 (N.leb_le _ _) Hx));
				apply: N.lt_irrefl
			end).
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Hmaxfun : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_imax_ n0 s0 p q r1 -> fun_imax_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: try (exfalso;
			match goal with
			| [ Hx : is_true (N_geb ?u ?v), Hy : is_true (N.ltb ?u ?v) |- _ ] =>
				rewrite /N_geb in Hx;
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hy) (proj1 (N.leb_le _ _) Hx));
				apply: N.lt_irrefl
			end).
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Haddsat : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_iadd_sat_ n0 s0 p q r1 -> fun_iadd_sat_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: repeat match goal with
			| [ Hx : fun_inv_signed_ ?n ?k ?u, Hy : fun_inv_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hinvsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Hsubsat : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_isub_sat_ n0 s0 p q r1 -> fun_isub_sat_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: repeat match goal with
			| [ Hx : fun_inv_signed_ ?n ?k ?u, Hy : fun_inv_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hinvsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	case: H Hsh Hop Hvec1 Hvec2 Hne => *.
	all: repeat match goal with
		| [ Ha : List_Forall3 ?R ?l1 ?lu ?lv, Hb : List_Forall3 ?R ?l2 ?lu ?lv |- _ ] =>
			tryif constr_eq l1 l2 then fail else
			(have Heq : l1 = l2;
				[ apply: (Hf3 _ _ _ R lu lv l1 l2 Ha Hb); move => a b u v Hx Hy;
					first [ exact: (Hordfun _ _ _ _ _ _ Hx Hy)
						| exact: (Hmaxfun _ _ _ _ _ _ Hx Hy)
						| exact: (Haddsat _ _ _ _ _ _ Hx Hy)
						| exact: (Hsubsat _ _ _ _ _ _ Hx Hy) ]
				| subst ])
		end.
	all: repeat match goal with | [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end.
	all: subst.
	all: first
		[ by apply: uN_case_0
		| ((eapply inv_lanes__is_wf; only 3: by apply: eqxx);
			[ eassumption
			| first [ (apply Hfmap; eassumption)
				| (apply Hzip; eassumption)
				| (apply Hfmap; apply Hzip; eassumption)
				| (apply Hfmap; apply Hzip;
					match goal with
					| [ Hh : List.Forall2 _ _ _ |- _ ] =>
						(eapply Hmono2; [ exact: Hh | move => x y Hxy; apply Hfmap; exact: Hxy ])
					end) ] ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:385.6-385.15 *)
Lemma lcvtop___is_wf : forall (shape_1 : shape) (shape_2 : shape) (v_vcvtop__ : vcvtop__) (v_lane_ : lane_) (ret_val_lst : (seq lane_)) (var_0 : (option (seq lane_))),
	(fun_lcvtop__ shape_1 shape_2 v_vcvtop__ v_lane_ var_0) ->
	(wf_shape shape_1) ->
	(wf_shape shape_2) ->
	(wf_vcvtop__ shape_1 shape_2 v_vcvtop__) ->
	(wf_lane_ (fun_lanetype shape_1) v_lane_) ->
	(var_0 != None) ->
	(ret_val_lst == (!(var_0))) ->
	List.Forall (fun (ret_val : lane_) => (wf_lane_ (fun_lanetype shape_2) ret_val)) ret_val_lst.
Proof.
	move => shape_1 shape_2 v_vcvtop v_lane_ ret_val_lst var_0 Hf Hs1 Hs2 Hop Hln Hne /eqP ->.
	have Hmapo : forall (J : Jnn) (lt : lanetype) (o : (option iN)),
		(lt == (lanetype_Jnn J)) ->
		List.Forall (fun x => wf_uN (lsize (lanetype_Jnn J)) x) (option_to_list o) ->
		List.Forall (fun x => wf_lane_ lt x) (list_ lane_ (option_map (fun x => mk_lane__0 J x) o)).
	{ move => J lt o H1 Ho. case: o Ho => [x| ] Ho; last by apply: List.Forall_nil.
		inversion Ho; subst. apply: List.Forall_cons; last by apply: List.Forall_nil.
		by apply: lane__case_0. }
	have Hmap : forall (F : Fnn) (lt : lanetype) (l : seq fN),
		(lt == (lanetype_Fnn F)) ->
		List.Forall (fun x => wf_fN (sizenn (numtype_Fnn F)) x) l ->
		List.Forall (fun x => wf_lane_ lt x) (seq.map (fun x => mk_lane__1 F x) l).
	{ move => F lt l H1. elim: l => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ apply: lane__case_1 | apply: IH ]. }
	inversion Hf; subst; simpl; last by move: Hne.
	all: repeat match goal with | [ H : is_true (?x == _) |- _ ] => is_var x; move/eqP: H => H; subst x end.
	all: repeat match goal with | [ Hx : wf_lane_ _ _ |- _ ] => inversion Hx; subst; clear Hx end.
	all: first
		[ (apply: List.Forall_cons;
			[ first [ (apply: lane__case_0;
					[ ((eapply extend___is_wf; only 2: by apply: eqxx); eassumption) | by [] ])
				| (apply: lane__case_1;
					[ ((eapply convert___is_wf; only 2: by apply: eqxx); eassumption) | by [] ]) ]
			| by apply: List.Forall_nil ])
		| (apply: Hmapo; [ by []
			| first [ ((eapply trunc_sat___is_wf; only 2: by apply: eqxx); eassumption)
				| ((eapply trunc___is_wf; only 2: by apply: eqxx); eassumption) ] ])
		| (apply: Hmap; [ by []
			| first [ ((eapply demote___is_wf; only 2: by apply: eqxx); eassumption)
				| ((eapply promote___is_wf; only 2: by apply: eqxx); eassumption) ] ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:387.6-387.15 *)
Lemma vcvtop___is_wf : forall (shape_1 : shape) (shape_2 : shape) (v_vcvtop__ : vcvtop__) (v_vec_ : vec_) (ret_val : vec_) (var_0 : (option vec_)),
	(fun_vcvtop__ shape_1 shape_2 v_vcvtop__ v_vec_ var_0) ->
	(wf_shape shape_1) ->
	(wf_shape shape_2) ->
	(wf_vcvtop__ shape_1 shape_2 v_vcvtop__) ->
	(wf_uN 128%N v_vec_) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_uN 128%N ret_val).
Proof.
	move => sh1 sh2 op v1 ret var_0 H Hs1 Hs2 Hop Hv Hne /eqP ->.
	have Hsp2 : forall (X : eqType) (P : X -> Prop) (w : X) (lls : seq (seq X)),
		P w -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct2_ X w lls).
	{ move => X P w. elim => [ |l lls IH] //= Hw /List.Forall_cons_iff [Hl Hlls].
		by apply: List.Forall_cons; [ apply: List.Forall_cons | apply: IH ]. }
	have Hsp1 : forall (X : eqType) (P : X -> Prop) (l : seq X) (lls : seq (seq X)),
		List.Forall P l -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct1_ X l lls).
	{ move => X P. elim => [ |w l IH] lls //= /List.Forall_cons_iff [Hw Hl] Hlls.
		by apply/List.Forall_app; split; [ apply: Hsp2 | apply: IH ]. }
	have Hsp : forall (X : eqType) (P : X -> Prop) (lls : seq (seq X)),
		List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct_ X lls).
	{ move => X P. elim => [ |l lls IH] /=.
		- by move => _; apply: List.Forall_cons; apply: List.Forall_nil.
		- move => /List.Forall_cons_iff [Hl Hlls]. by apply: Hsp1; [ | apply: IH ]. }
	have Hslice : forall (T : Type) (P : T -> Prop) (l : seq T) (i j : N),
		List.Forall P l -> List.Forall P (list_slice l i j).
	{ move => T P. elim => [ |x l IH] i j //= /List.Forall_cons_iff [Hx Hl].
		case: i => [ |p]; case: j => [ |q] //=; try by apply: IH.
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hmem : forall (sh : shape) (lls : seq (seq lane_)) (v : vec_),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		v \in [seq inv_lanes_ sh l | l <- lls] -> wf_uN 128%N v.
	{ move => sh lls v Hsh. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		rewrite in_cons => /orP [/eqP -> | Hin]; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hlc : forall (s1 s2 : shape) (o : vcvtop__) (vs : seq (option (seq lane_))) (cs : seq lane_),
		wf_shape s1 -> wf_shape s2 -> wf_vcvtop__ s1 s2 o ->
		List.Forall2 (fun v c => fun_lcvtop__ s1 s2 o c v) vs cs ->
		List.Forall (fun c => wf_lane_ (fun_lanetype s1) c) cs ->
		List.Forall (fun v => v != None) vs ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype s2) x) l) [seq !(v) | v <- vs].
	{ move => s1 s2 o vs cs W1 W2 Wo. elim => [ |v c vs' cs' Hvc H2 IH] //=.
		move => /List.Forall_cons_iff [Hc Hcs] /List.Forall_cons_iff [Hvn Hvs].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (lcvtop___is_wf s1 s2 o c (!(v)) v Hvc W1 W2 Wo Hc Hvn). }
	case: H Hs1 Hs2 Hop Hv Hne => //=.
	(* full *)
	- move => L1 M L2 o v128_1 v128 M0 cs css vs z h Hlen Hf Hz Hh _ _ _ Hcs Hvs Hcss _ Hin W1 W2 /eqP HM.
		subst M0 => _ _ Wo Wv _.
		move/eqP: Hcs => Hcs; move/eqP: Hcss => Hcss; rewrite Hcss in Hin.
		apply: (Hmem _ _ _ W2 _ Hin). apply: Hsp.
		apply: (Hlc _ _ _ _ cs W1 W2 Wo Hf _ Hvs).
		rewrite Hcs. by apply: (lanes__is_wf _ v128_1).
	(* half *)
	- move => L1 M1 L2 M2 o v128_1 v128 hf cs css vs h Hlen Hf Hh _ _ Hcs Hvs Hcss _ Hin W1 W2 _ _ Wo Wv _.
		move/eqP: Hcs => Hcs; move/eqP: Hcss => Hcss; rewrite Hcss in Hin.
		apply: (Hmem _ _ _ W2 _ Hin). apply: Hsp.
		apply: (Hlc _ _ _ _ cs W1 W2 Wo Hf _ Hvs).
		rewrite Hcs. apply: Hslice. by apply: (lanes__is_wf _ v128_1).
	(* zero *)
	- move => L1 M1 L2 M2 o v128_1 v128 cs css vs z Hlen Hf Hz _ _ Hcs Hvs Hpn Hcss _ Hin W1 W2 _ _ Wo Wv _.
		move/eqP: Hcs => Hcs; move/eqP: Hcss => Hcss; rewrite Hcss in Hin.
		apply: (Hmem _ _ _ W2 _ Hin). apply: Hsp.
		apply/List.Forall_app; split.
		+ apply: (Hlc _ _ _ _ cs W1 W2 Wo Hf _ Hvs).
			rewrite Hcs. by apply: (lanes__is_wf _ v128_1).
		+ rewrite /list_repeat. elim: (N.to_nat M1) => [ |n IH] /=; first by apply: List.Forall_nil.
			apply: List.Forall_cons => //. apply: List.Forall_cons; last by apply: List.Forall_nil.
			apply: (packnum__is_wf _ (fun_zero (unpack L2))) => //.
			by apply: (zero_is_wf (unpack L2)).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:603.6-603.17 *)
Lemma vextunop___is_wf : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop__ : vextunop__) (v_vec_ : vec_) (ret_val : vec_) (var_0 : (option vec_)),
	(fun_vextunop__ ishape_1 ishape_2 v_vextunop__ v_vec_ var_0) ->
	(wf_ishape ishape_1) ->
	(wf_ishape ishape_2) ->
	(wf_vextunop__ ishape_1 ishape_2 v_vextunop__) ->
	(wf_uN 128%N v_vec_) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_uN 128%N ret_val).
Proof.
	move => ishape_1 ishape_2 v_vextunop_ v_vec_ ret_val var_0 H Hs1 Hs2 Hop Hvec Hne /eqP ->.
	have Hmono : forall (T : Type) (P Q : T -> Prop) (l : seq T),
		List.Forall P l -> (forall x, P x -> Q x) -> List.Forall Q l.
	{ move => T P Q. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl] Hpq.
		by apply: List.Forall_cons; [ apply: Hpq | apply: IH ]. }
	have Hfmap : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall (fun x => P (f x)) l -> List.Forall P (seq.map f l).
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hsp2 : forall (X : eqType) (P : X -> Prop) (w : X) (lls : seq (seq X)),
		P w -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct2_ X w lls).
	{ move => X P w. elim => [ |l lls IH] //= Hw /List.Forall_cons_iff [Hl Hlls].
		by apply: List.Forall_cons; [ apply: List.Forall_cons | apply: IH ]. }
	have Hsp1 : forall (X : eqType) (P : X -> Prop) (l : seq X) (lls : seq (seq X)),
		List.Forall P l -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct1_ X l lls).
	{ move => X P. elim => [ |w l IH] lls //= /List.Forall_cons_iff [Hw Hl] Hlls.
		by apply/List.Forall_app; split; [ apply: Hsp2 | apply: IH ]. }
	have Hsp : forall (X : eqType) (P : X -> Prop) (lls : seq (seq X)),
		List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct_ X lls).
	{ move => X P. elim => [ |l lls IH] /=.
		- by move => _; apply: List.Forall_cons; apply: List.Forall_nil.
		- move => /List.Forall_cons_iff [Hl Hlls]. by apply: Hsp1; [ | apply: IH ]. }
	have Hfin : forall (sh : shape) (lls : seq (seq lane_)),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		List.Forall (fun v => wf_uN 128%N v) (seq.map (fun l => inv_lanes_ sh l) lls).
	{ move => sh lls Hsh0. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hf2 : forall (T U : Type) (R : T -> U -> Prop) (ll : seq U) (l1 l2 : seq T),
		List.Forall2 R l1 ll -> List.Forall2 R l2 ll ->
		(forall a b u, R a u -> R b u -> a = b) -> l1 = l2.
	{ move => T U R ll l1 l2 H1. elim: H1 l2 => [ |x y l l' Hxy H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 l2' ll2 Hxy2 H2' E1 E2]; subst.
			by rewrite (Hfun _ _ _ Hxy Hxy2) (IH _ H2' Hfun). }
	have Hsig : forall (vN : res_N) (i : N) (a b : Z),
		fun_signed_ vN i a -> fun_signed_ vN i b -> a = b.
	{ move => vN i a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (N.ltb ?u ?X), Hy : is_true (andb (N.leb ?X ?u) _) |- _ ] =>
				move: Hy => /andP [Hy _];
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hx) (proj1 (N.leb_le _ _) Hy));
				apply: N.lt_irrefl
			end. }
	have Hinvsig : forall (vN : res_N) (z : Z) (a b : N),
		fun_inv_signed_ vN z a -> fun_inv_signed_ vN z b -> a = b.
	{ move => vN z a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (andb (Z.leb _ ?u) _), Hy : is_true (andb _ (Z.ltb ?u _)) |- _ ] =>
				move: (Hx) => /andP [Hx1 _]; move: (Hy) => /andP [_ Hy1];
				move: (Z.le_lt_trans _ _ _ (proj1 (Z.leb_le _ _) Hx1) (proj1 (Z.ltb_lt _ _) Hy1));
				apply: Z.lt_irrefl
			end. }
	have Hzip : forall (T U V : Type) (P : V -> Prop) (f : T -> U -> V)
		(l1 : seq T) (l2 : seq U),
		List.Forall2 (fun a b => P (f a b)) l1 l2 -> List.Forall P (list_zipWith f l1 l2).
	{ move => T U V P f l1 l2 Hz. rewrite /list_zipWith.
		elim: Hz => [ |x y l l' Hxy Hz IH] //=. by apply: List.Forall_cons. }
	have Hmono2 : forall (T U : Type) (P Q : T -> U -> Prop) (l1 : seq T) (l2 : seq U),
		List.Forall2 P l1 l2 -> (forall x y, P x y -> Q x y) -> List.Forall2 Q l1 l2.
	{ move => T U P Q l1 l2 Hz Hpq. elim: Hz => [ |x y l l' Hxy Hz IH].
		- by apply: List.Forall2_nil.
		- by apply: List.Forall2_cons; [ apply: Hpq | ]. }
	have Hf3 : forall (T U V : Type) (R : T -> U -> V -> Prop) (lu : seq U) (lv : seq V)
		(l1 l2 : seq T),
		List_Forall3 R l1 lu lv -> List_Forall3 R l2 lu lv ->
		(forall a b u v, R a u v -> R b u v -> a = b) -> l1 = l2.
	{ move => T U V R lu lv l1 l2 H1. elim: H1 l2 => [ |x y z l l' l'' Hxyz H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 z2 l2' lu2 lv2 Hxyz2 H2' E1 E2 E3]; subst.
			by rewrite (Hfun _ _ _ _ Hxyz Hxyz2) (IH _ H2' Hfun). }
	have Hordfun : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_imin_ n0 s0 p q r1 -> fun_imin_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: try (exfalso;
			match goal with
			| [ Hx : is_true (N.leb ?u ?v), Hy : is_true (N_gtb ?u ?v) |- _ ] =>
				rewrite /N_gtb in Hy;
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hy) (proj1 (N.leb_le _ _) Hx));
				apply: N.lt_irrefl
			end).
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Hmaxfun : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_imax_ n0 s0 p q r1 -> fun_imax_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: try (exfalso;
			match goal with
			| [ Hx : is_true (N_geb ?u ?v), Hy : is_true (N.ltb ?u ?v) |- _ ] =>
				rewrite /N_geb in Hx;
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hy) (proj1 (N.leb_le _ _) Hx));
				apply: N.lt_irrefl
			end).
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Haddsat : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_iadd_sat_ n0 s0 p q r1 -> fun_iadd_sat_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: repeat match goal with
			| [ Hx : fun_inv_signed_ ?n ?k ?u, Hy : fun_inv_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hinvsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Hsubsat : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_isub_sat_ n0 s0 p q r1 -> fun_isub_sat_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: repeat match goal with
			| [ Hx : fun_inv_signed_ ?n ?k ?u, Hy : fun_inv_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hinvsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	case: H Hs1 Hs2 Hop Hvec Hne => *.
	all: repeat match goal with
		| [ Ha : List_Forall3 ?R ?l1 ?lu ?lv, Hb : List_Forall3 ?R ?l2 ?lu ?lv |- _ ] =>
			tryif constr_eq l1 l2 then fail else
			(have Heq : l1 = l2;
				[ apply: (Hf3 _ _ _ R lu lv l1 l2 Ha Hb); move => a b u v Hx Hy;
					first [ exact: (Hordfun _ _ _ _ _ _ Hx Hy)
						| exact: (Hmaxfun _ _ _ _ _ _ Hx Hy)
						| exact: (Haddsat _ _ _ _ _ _ Hx Hy)
						| exact: (Hsubsat _ _ _ _ _ _ Hx Hy) ]
				| subst ])
		end.
	all: repeat match goal with | [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end.
	all: subst.
	all: first
		[ by apply: uN_case_0
		| ((eapply inv_lanes__is_wf; only 3: by apply: eqxx);
			[ eassumption
			| first [ (apply Hfmap; eassumption)
				| (apply Hzip; eassumption)
				| (apply Hfmap; apply Hzip; eassumption)
				| (apply Hfmap; apply Hzip;
					match goal with
					| [ Hh : List.Forall2 _ _ _ |- _ ] =>
						(eapply Hmono2; [ exact: Hh | move => x y Hxy; apply Hfmap; exact: Hxy ])
					end) ] ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:605.6-605.18 *)
Lemma vextbinop___is_wf : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop__ : vextbinop__) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : (option vec_)),
	(fun_vextbinop__ ishape_1 ishape_2 v_vextbinop__ v_vec_ vec__0 var_0) ->
	(wf_ishape ishape_1) ->
	(wf_ishape ishape_2) ->
	(wf_vextbinop__ ishape_1 ishape_2 v_vextbinop__) ->
	(wf_uN 128%N v_vec_) ->
	(wf_uN 128%N vec__0) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_uN 128%N ret_val).
Proof.
	move => ishape_1 ishape_2 v_vextbinop_ v_vec_ vec__0 ret_val var_0 H Hs1 Hs2 Hop Hvec1 Hvec2 Hne /eqP ->.
	have Hmono : forall (T : Type) (P Q : T -> Prop) (l : seq T),
		List.Forall P l -> (forall x, P x -> Q x) -> List.Forall Q l.
	{ move => T P Q. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl] Hpq.
		by apply: List.Forall_cons; [ apply: Hpq | apply: IH ]. }
	have Hfmap : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall (fun x => P (f x)) l -> List.Forall P (seq.map f l).
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hsp2 : forall (X : eqType) (P : X -> Prop) (w : X) (lls : seq (seq X)),
		P w -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct2_ X w lls).
	{ move => X P w. elim => [ |l lls IH] //= Hw /List.Forall_cons_iff [Hl Hlls].
		by apply: List.Forall_cons; [ apply: List.Forall_cons | apply: IH ]. }
	have Hsp1 : forall (X : eqType) (P : X -> Prop) (l : seq X) (lls : seq (seq X)),
		List.Forall P l -> List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct1_ X l lls).
	{ move => X P. elim => [ |w l IH] lls //= /List.Forall_cons_iff [Hw Hl] Hlls.
		by apply/List.Forall_app; split; [ apply: Hsp2 | apply: IH ]. }
	have Hsp : forall (X : eqType) (P : X -> Prop) (lls : seq (seq X)),
		List.Forall (fun l => List.Forall P l) lls ->
		List.Forall (fun l => List.Forall P l) (setproduct_ X lls).
	{ move => X P. elim => [ |l lls IH] /=.
		- by move => _; apply: List.Forall_cons; apply: List.Forall_nil.
		- move => /List.Forall_cons_iff [Hl Hlls]. by apply: Hsp1; [ | apply: IH ]. }
	have Hfin : forall (sh : shape) (lls : seq (seq lane_)),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		List.Forall (fun v => wf_uN 128%N v) (seq.map (fun l => inv_lanes_ sh l) lls).
	{ move => sh lls Hsh0. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hf2 : forall (T U : Type) (R : T -> U -> Prop) (ll : seq U) (l1 l2 : seq T),
		List.Forall2 R l1 ll -> List.Forall2 R l2 ll ->
		(forall a b u, R a u -> R b u -> a = b) -> l1 = l2.
	{ move => T U R ll l1 l2 H1. elim: H1 l2 => [ |x y l l' Hxy H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 l2' ll2 Hxy2 H2' E1 E2]; subst.
			by rewrite (Hfun _ _ _ Hxy Hxy2) (IH _ H2' Hfun). }
	have Hsig : forall (vN : res_N) (i : N) (a b : Z),
		fun_signed_ vN i a -> fun_signed_ vN i b -> a = b.
	{ move => vN i a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (N.ltb ?u ?X), Hy : is_true (andb (N.leb ?X ?u) _) |- _ ] =>
				move: Hy => /andP [Hy _];
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hx) (proj1 (N.leb_le _ _) Hy));
				apply: N.lt_irrefl
			end. }
	have Hinvsig : forall (vN : res_N) (z : Z) (a b : N),
		fun_inv_signed_ vN z a -> fun_inv_signed_ vN z b -> a = b.
	{ move => vN z a b Ha Hb. inversion Ha; inversion Hb; subst => //.
		all: exfalso;
			match goal with
			| [ Hx : is_true (andb (Z.leb _ ?u) _), Hy : is_true (andb _ (Z.ltb ?u _)) |- _ ] =>
				move: (Hx) => /andP [Hx1 _]; move: (Hy) => /andP [_ Hy1];
				move: (Z.le_lt_trans _ _ _ (proj1 (Z.leb_le _ _) Hx1) (proj1 (Z.ltb_lt _ _) Hy1));
				apply: Z.lt_irrefl
			end. }
	have Hzip : forall (T U V : Type) (P : V -> Prop) (f : T -> U -> V)
		(l1 : seq T) (l2 : seq U),
		List.Forall2 (fun a b => P (f a b)) l1 l2 -> List.Forall P (list_zipWith f l1 l2).
	{ move => T U V P f l1 l2 Hz. rewrite /list_zipWith.
		elim: Hz => [ |x y l l' Hxy Hz IH] //=. by apply: List.Forall_cons. }
	have Hmono2 : forall (T U : Type) (P Q : T -> U -> Prop) (l1 : seq T) (l2 : seq U),
		List.Forall2 P l1 l2 -> (forall x y, P x y -> Q x y) -> List.Forall2 Q l1 l2.
	{ move => T U P Q l1 l2 Hz Hpq. elim: Hz => [ |x y l l' Hxy Hz IH].
		- by apply: List.Forall2_nil.
		- by apply: List.Forall2_cons; [ apply: Hpq | ]. }
	have Hf3 : forall (T U V : Type) (R : T -> U -> V -> Prop) (lu : seq U) (lv : seq V)
		(l1 l2 : seq T),
		List_Forall3 R l1 lu lv -> List_Forall3 R l2 lu lv ->
		(forall a b u v, R a u v -> R b u v -> a = b) -> l1 = l2.
	{ move => T U V R lu lv l1 l2 H1. elim: H1 l2 => [ |x y z l l' l'' Hxyz H1' IH] l2 H2 Hfun.
		- by inversion H2.
		- inversion H2 as [ |x2 y2 z2 l2' lu2 lv2 Hxyz2 H2' E1 E2 E3]; subst.
			by rewrite (Hfun _ _ _ _ Hxyz Hxyz2) (IH _ H2' Hfun). }
	have Hordfun : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_imin_ n0 s0 p q r1 -> fun_imin_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: try (exfalso;
			match goal with
			| [ Hx : is_true (N.leb ?u ?v), Hy : is_true (N_gtb ?u ?v) |- _ ] =>
				rewrite /N_gtb in Hy;
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hy) (proj1 (N.leb_le _ _) Hx));
				apply: N.lt_irrefl
			end).
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Hmaxfun : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_imax_ n0 s0 p q r1 -> fun_imax_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: try (exfalso;
			match goal with
			| [ Hx : is_true (N_geb ?u ?v), Hy : is_true (N.ltb ?u ?v) |- _ ] =>
				rewrite /N_geb in Hx;
				move: (N.lt_le_trans _ _ _ (proj1 (N.ltb_lt _ _) Hy) (proj1 (N.leb_le _ _) Hx));
				apply: N.lt_irrefl
			end).
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Haddsat : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_iadd_sat_ n0 s0 p q r1 -> fun_iadd_sat_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: repeat match goal with
			| [ Hx : fun_inv_signed_ ?n ?k ?u, Hy : fun_inv_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hinvsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	have Hsubsat : forall (n0 : res_N) (s0 : sx) (p q r1 r2 : iN),
		fun_isub_sat_ n0 s0 p q r1 -> fun_isub_sat_ n0 s0 p q r2 -> r1 = r2.
	{ move => n0 s0 p q r1 r2 HA HB. inversion HA; inversion HB; subst => //.
		all: repeat match goal with
			| [ Hx : fun_signed_ ?n ?k ?u, Hy : fun_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hsig _ _ _ _ Hx Hy; subst)
			end.
		all: repeat match goal with
			| [ Hx : fun_inv_signed_ ?n ?k ?u, Hy : fun_inv_signed_ ?n ?k ?v |- _ ] =>
				tryif constr_eq u v then fail else (have Heq := Hinvsig _ _ _ _ Hx Hy; subst)
			end.
		all: by []. }
	case: H Hs1 Hs2 Hop Hvec1 Hvec2 Hne => *.
	all: repeat match goal with
		| [ Ha : List_Forall3 ?R ?l1 ?lu ?lv, Hb : List_Forall3 ?R ?l2 ?lu ?lv |- _ ] =>
			tryif constr_eq l1 l2 then fail else
			(have Heq : l1 = l2;
				[ apply: (Hf3 _ _ _ R lu lv l1 l2 Ha Hb); move => a b u v Hx Hy;
					first [ exact: (Hordfun _ _ _ _ _ _ Hx Hy)
						| exact: (Hmaxfun _ _ _ _ _ _ Hx Hy)
						| exact: (Haddsat _ _ _ _ _ _ Hx Hy)
						| exact: (Hsubsat _ _ _ _ _ _ Hx Hy) ]
				| subst ])
		end.
	all: repeat match goal with | [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end.
	all: subst.
	all: first
		[ by apply: uN_case_0
		| ((eapply inv_lanes__is_wf; only 3: by apply: eqxx);
			[ eassumption
			| first [ (apply Hfmap; eassumption)
				| (apply Hzip; eassumption)
				| (apply Hfmap; apply Hzip; eassumption)
				| (apply Hfmap; apply Hzip;
					match goal with
					| [ Hh : List.Forall2 _ _ _ |- _ ] =>
						(eapply Hmono2; [ exact: Hh | move => x y Hxy; apply Hfmap; exact: Hxy ])
					end) ] ]) ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:628.6-628.16 *)
Lemma vshiftop__is_wf : forall (v_ishape : ishape) (v_vshiftop_ : vshiftop_) (v_lane_ : lane_) (v_u32 : u32) (ret_val : lane_) (var_0 : (option lane_)),
	(fun_vshiftop_ v_ishape v_vshiftop_ v_lane_ v_u32 var_0) ->
	(wf_ishape v_ishape) ->
	(wf_vshiftop_ v_ishape v_vshiftop_) ->
	(wf_lane_ (fun_lanetype (v_ishape :> shape)) v_lane_) ->
	(wf_uN 32%N v_u32) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_lane_ (fun_lanetype (v_ishape :> shape)) ret_val).
Proof.
	move => v_ishape v_vshiftop_ v_lane_ v_u32 ret_val var_0 H Hsh Hop Hl Hu Hne /eqP ->.
	case: H Hsh Hop Hl Hu Hne => *.
	all: try (by match goal with | [ Hn : is_true (_ != _) |- _ ] => move: Hn; rewrite eqxx end).
	all: repeat match goal with | [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end.
	all: subst.
	all: repeat match goal with
		| [ Hx : wf_lane_ _ (mk_lane__0 _ _) |- _ ] => inversion Hx; subst; clear Hx end.
	all: apply: lane__case_0; last by [].
	all: first [ (eapply ishl__is_wf; only 3: by apply: eqxx)
		| (eapply ishr__is_wf; only 3: by apply: eqxx) ]; first eassumption.
	(* The shift amount is $(n \ $lsizenn(Jnn)) < $lsizenn(Jnn) < 2^$lsizenn(Jnn). *)
	all: apply: uN_case_0; unfold N_geb; apply/andP; split;
		[ by apply/N.leb_spec0; apply: N.le_0_l | apply/N.leb_spec0 ].
	all: match goal with |- N.le (N.modulo ?v ?k) _ =>
		apply: (N.le_trans _ k); [ apply: N.lt_le_incl; apply: N.mod_lt; by vm_compute | by vm_compute ] end.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.6-7.15 *)
Lemma default__is_wf : forall (v_valtype : valtype) (ret_val : val),
	((default_ v_valtype) != None) ->
	(ret_val == (!((default_ v_valtype)))) ->
	(wf_val ret_val).
Proof.
	move => v_valtype ret_val Hne /eqP ->.
	case: v_valtype Hne => //= _.
	- by apply: val_case_0; apply: num__case_0.
	- by apply: val_case_0; apply: num__case_0.
	- by apply: val_case_0; apply: num__case_1 => //; apply: (fzero_is_wf 32%N).
	- by apply: val_case_0; apply: num__case_1 => //; apply: (fzero_is_wf 64%N).
	- by apply: val_case_1.
	- by apply: val_case_2.
	- by apply: val_case_2.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.6-48.12 *)
Lemma store_is_wf : forall (v_state : state) (ret_val : store),
	(wf_state v_state) ->
	(ret_val == (fun_store v_state)) ->
	(wf_store ret_val).
Proof.
	move => v_state ret_val Hwf /eqP ->.
	by case: Hwf.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.6-49.12 *)
Lemma frame_is_wf : forall (v_state : state) (ret_val : frame),
	(wf_state v_state) ->
	(ret_val == (fun_frame v_state)) ->
	(wf_frame ret_val).
Proof.
	move => v_state ret_val Hwf /eqP ->.
	by case: Hwf.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.6-58.15 *)
Lemma funcinst_is_wf : forall (v_state : state) (ret_val_lst : (seq funcinst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_funcinst v_state)) ->
	List.Forall (fun (ret_val : funcinst) => (wf_funcinst ret_val)) ret_val_lst.
Proof.
	move => v_state ret_val_lst Hwf /eqP ->.
	case: Hwf => s f Hs Hf. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.6-59.17 *)
Lemma globalinst_is_wf : forall (v_state : state) (ret_val_lst : (seq globalinst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_globalinst v_state)) ->
	List.Forall (fun (ret_val : globalinst) => (wf_globalinst ret_val)) ret_val_lst.
Proof.
	move => v_state ret_val_lst Hwf /eqP ->.
	case: Hwf => s f Hs Hf. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.6-60.16 *)
Lemma tableinst_is_wf : forall (v_state : state) (ret_val_lst : (seq tableinst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_tableinst v_state)) ->
	List.Forall (fun (ret_val : tableinst) => (wf_tableinst ret_val)) ret_val_lst.
Proof.
	move => v_state ret_val_lst Hwf /eqP ->.
	case: Hwf => s f Hs Hf. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.6-61.14 *)
Lemma meminst_is_wf : forall (v_state : state) (ret_val_lst : (seq meminst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_meminst v_state)) ->
	List.Forall (fun (ret_val : meminst) => (wf_meminst ret_val)) ret_val_lst.
Proof.
	move => v_state ret_val_lst Hwf /eqP ->.
	case: Hwf => s f Hs Hf. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.6-63.15 *)
Lemma datainst_is_wf : forall (v_state : state) (ret_val_lst : (seq datainst)),
	(wf_state v_state) ->
	(ret_val_lst == (fun_datainst v_state)) ->
	List.Forall (fun (ret_val : datainst) => (wf_datainst ret_val)) ret_val_lst.
Proof.
	move => v_state ret_val_lst Hwf /eqP ->.
	case: Hwf => s f Hs Hf. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.6-64.17 *)
Lemma moduleinst_is_wf : forall (v_state : state) (ret_val : moduleinst),
	(wf_state v_state) ->
	(ret_val == (fun_moduleinst v_state)) ->
	(wf_moduleinst ret_val).
Proof.
	move => v_state ret_val Hwf /eqP ->.
	case: Hwf => s f Hs Hf. by case: Hf.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.6-75.11 *)
Lemma func_is_wf : forall (v_state : state) (v_funcidx : funcidx) (ret_val : funcinst),
	(wf_state v_state) ->
	(wf_uN 32%N v_funcidx) ->
	(ret_val == (fun_func v_state v_funcidx)) ->
	(wf_funcinst ret_val).
Proof.
	move => v_state v_funcidx ret_val Hwf Hidx /eqP ->.
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hall Hd; first by rewrite seq.nth_nil.
		inversion Hall; subst. case: n => [ |n] //=. by apply: IH. }
	have Hdef : wf_funcinst default_val.
	{ apply: funcinst_case_; first by apply: moduleinst_case_; apply: List.Forall_nil.
		by apply: func_case_0; [ apply: uN_case_0 | apply: List.Forall_nil ]. }
	case: Hwf => s f Hs Hf. rewrite /fun_func /lookup_total.
	apply: Hnth => //. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.6-76.13 *)
Lemma global_is_wf : forall (v_state : state) (v_globalidx : globalidx) (ret_val : globalinst),
	(wf_state v_state) ->
	(wf_uN 32%N v_globalidx) ->
	(ret_val == (fun_global v_state v_globalidx)) ->
	(wf_globalinst ret_val).
Proof.
	move => v_state v_globalidx ret_val Hwf Hidx /eqP ->.
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hall Hd; first by rewrite seq.nth_nil.
		inversion Hall; subst. case: n => [ |n] //=. by apply: IH. }
	have Hdef : wf_globalinst default_val.
	{ by apply: globalinst_case_; apply: val_case_0; apply: num__case_0. }
	case: Hwf => s f Hs Hf. rewrite /fun_global /lookup_total.
	apply: Hnth => //. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.6-77.12 *)
Lemma table_is_wf : forall (v_state : state) (v_tableidx : tableidx) (ret_val : tableinst),
	(wf_state v_state) ->
	(wf_uN 32%N v_tableidx) ->
	(ret_val == (fun_table v_state v_tableidx)) ->
	(wf_tableinst ret_val).
Proof.
	move => v_state v_tableidx ret_val Hwf Hidx /eqP ->.
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hall Hd; first by rewrite seq.nth_nil.
		inversion Hall; subst. case: n => [ |n] //=. by apply: IH. }
	have Hdef : wf_tableinst default_val.
	{ by apply: tableinst_case_; apply: tabletype_case_0; apply: limits_case_0. }
	case: Hwf => s f Hs Hf. rewrite /fun_table /lookup_total.
	apply: Hnth => //. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.6-78.10 *)
Lemma mem_is_wf : forall (v_state : state) (v_memidx : memidx) (ret_val : meminst),
	(wf_state v_state) ->
	(wf_uN 32%N v_memidx) ->
	(ret_val == (fun_mem v_state v_memidx)) ->
	(wf_meminst ret_val).
Proof.
	move => v_state v_memidx ret_val Hwf Hidx /eqP ->.
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hall Hd; first by rewrite seq.nth_nil.
		inversion Hall; subst. case: n => [ |n] //=. by apply: IH. }
	have Hdef : wf_meminst default_val.
	{ by apply: meminst_case_; [apply: memtype_case_0; apply: limits_case_0 | apply: List.Forall_nil]. }
	case: Hwf => s f Hs Hf. rewrite /fun_mem /lookup_total.
	apply: Hnth => //. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.6-80.11 *)
Lemma data_is_wf : forall (v_state : state) (v_dataidx : dataidx) (ret_val : datainst),
	(wf_state v_state) ->
	(wf_uN 32%N v_dataidx) ->
	(ret_val == (fun_data v_state v_dataidx)) ->
	(wf_datainst ret_val).
Proof.
	move => v_state v_dataidx ret_val Hwf Hidx /eqP ->.
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hall Hd; first by rewrite seq.nth_nil.
		inversion Hall; subst. case: n => [ |n] //=. by apply: IH. }
	have Hdef : wf_datainst default_val.
	{ by apply: datainst_case_; apply: List.Forall_nil. }
	case: Hwf => s f Hs Hf. rewrite /fun_data /lookup_total.
	apply: Hnth => //. by case: Hs.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.6-81.12 *)
Lemma local_is_wf : forall (v_state : state) (v_localidx : localidx) (ret_val : val),
	(wf_state v_state) ->
	(wf_uN 32%N v_localidx) ->
	(ret_val == (fun_local v_state v_localidx)) ->
	(wf_val ret_val).
Proof.
	move => v_state v_localidx ret_val Hwf Hidx /eqP ->.
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hall Hd; first by rewrite seq.nth_nil.
		inversion Hall; subst. case: n => [ |n] //=. by apply: IH. }
	have Hdef : wf_val default_val.
	{ by apply: val_case_0; apply: num__case_0. }
	case: Hwf => s f Hs Hf. rewrite /fun_local /lookup_total.
	apply: Hnth => //. by case: Hf.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.6-95.17 *)
Lemma with_local_is_wf : forall (v_state : state) (v_localidx : localidx) (v_val : val) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32%N v_localidx) ->
	(wf_val v_val) ->
	(ret_val == (with_local v_state v_localidx v_val)) ->
	(wf_state ret_val).
Proof.
	move => v_state v_localidx v_val ret_val Hwf Hidx Hv /eqP ->.
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hall Hg //=.
		inversion Hall; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	case: Hwf => s f Hs Hf. rewrite /with_local /=.
	apply: state_case_0 => //.
	case: Hf => ls m Hls Hm. apply: frame_case_ => //.
	by apply: Hupd.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.6-96.18 *)
Lemma with_global_is_wf : forall (v_state : state) (v_globalidx : globalidx) (v_val : val) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32%N v_globalidx) ->
	(wf_val v_val) ->
	(ret_val == (with_global v_state v_globalidx v_val)) ->
	(wf_state ret_val).
Proof.
	move => v_state v_globalidx v_val ret_val Hwf Hidx Hv /eqP ->.
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hall Hg //=.
		inversion Hall; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	case: Hwf => s f Hs Hf. rewrite /with_global /=.
	apply: state_case_0 => //.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //.
	apply: Hupd; first by [].
	move => x Hx. case: Hx => t v0 Hv0. by apply: globalinst_case_.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.6-97.17 *)
Lemma with_table_is_wf : forall (v_state : state) (v_tableidx : tableidx) (res_nat : N) (v_ref : ref) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32%N v_tableidx) ->
	(ret_val == (with_table v_state v_tableidx res_nat v_ref)) ->
	(wf_state ret_val).
Proof.
	move => v_state v_tableidx res_nat v_ref ret_val Hwf Hidx /eqP ->.
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hall Hg //=.
		inversion Hall; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	case: Hwf => s f Hs Hf. rewrite /with_table /=.
	apply: state_case_0 => //.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //.
	apply: Hupd; first by [].
	move => x Hx. case: Hx => t rl Ht. by apply: tableinst_case_.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.6-98.21 *)
Lemma with_tableinst_is_wf : forall (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32%N v_tableidx) ->
	(wf_tableinst v_tableinst) ->
	(ret_val == (with_tableinst v_state v_tableidx v_tableinst)) ->
	(wf_state ret_val).
Proof.
	move => v_state v_tableidx v_tableinst ret_val Hwf Hidx Hti /eqP ->.
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hall Hg //=.
		inversion Hall; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	case: Hwf => s f Hs Hf. rewrite /with_tableinst /=.
	apply: state_case_0 => //.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //.
	apply: Hupd; first by [].
	by move => x _.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.6-99.15 *)
Lemma with_mem_is_wf : forall (v_state : state) (v_memidx : memidx) (res_nat : N) (nat_0 : N) (var_0_lst : (seq byte)) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32%N v_memidx) ->
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (with_mem v_state v_memidx res_nat nat_0 var_0_lst)) ->
	(wf_state ret_val).
Proof.
	move => v_state v_memidx res_nat nat_0 var_0_lst ret_val Hwf Hidx Hb /eqP ->.
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hall Hg //=.
		inversion Hall; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	have Hslice : forall (T : Type) (P : T -> Prop) (l : seq T) (i j : N) (u : seq T),
		List.Forall P l -> List.Forall P u -> List.Forall P (list_slice_update l i j u).
	{ move => T P l. elim: l => [ |x l IH] i j u Hl Hu //=.
		case: i => [ |pi]; case: j => [ |pj]; case: u Hu => [ |y u] Hu //=;
			inversion Hl; inversion Hu; subst; apply: List.Forall_cons => //; by apply: IH. }
	case: Hwf => s f Hs Hf. rewrite /with_mem /=.
	apply: state_case_0 => //.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //.
	apply: Hupd; first by [].
	move => x Hx. case: Hx => t bl Ht Hbl. apply: meminst_case_ => //.
	by apply: Hslice.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.6-100.19 *)
Lemma with_meminst_is_wf : forall (v_state : state) (v_memidx : memidx) (v_meminst : meminst) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32%N v_memidx) ->
	(wf_meminst v_meminst) ->
	(ret_val == (with_meminst v_state v_memidx v_meminst)) ->
	(wf_state ret_val).
Proof.
	move => v_state v_memidx v_meminst ret_val Hwf Hidx Hmi /eqP ->.
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hall Hg //=.
		inversion Hall; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	case: Hwf => s f Hs Hf. rewrite /with_meminst /=.
	apply: state_case_0 => //.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //.
	apply: Hupd; first by [].
	by move => x _.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.6-101.16 *)
Lemma with_elem_is_wf : forall (v_state : state) (v_elemidx : elemidx) (var_0_lst : (seq ref)) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32%N v_elemidx) ->
	(ret_val == (with_elem v_state v_elemidx var_0_lst)) ->
	(wf_state ret_val).
Proof.
	move => v_state v_elemidx var_0_lst ret_val Hwf Hidx /eqP ->.
	case: Hwf => s f Hs Hf. rewrite /with_elem /=.
	apply: state_case_0 => //.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	by apply: store_case_.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.6-102.16 *)
Lemma with_data_is_wf : forall (v_state : state) (v_dataidx : dataidx) (var_0_lst : (seq byte)) (ret_val : state),
	(wf_state v_state) ->
	(wf_uN 32%N v_dataidx) ->
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == (with_data v_state v_dataidx var_0_lst)) ->
	(wf_state ret_val).
Proof.
	move => v_state v_dataidx var_0_lst ret_val Hwf Hidx Hb /eqP ->.
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hall Hg //=.
		inversion Hall; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	case: Hwf => s f Hs Hf. rewrite /with_data /=.
	apply: state_case_0 => //.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //.
	apply: Hupd; first by [].
	move => x Hx. case: Hx => bl Hbl. by apply: datainst_case_.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
Lemma growtable_is_wf : forall (v_tableinst : tableinst) (res_nat : N) (v_ref : ref) (ret_val : tableinst) (var_0 : (option tableinst)),
	(fun_growtable v_tableinst res_nat v_ref var_0) ->
	(wf_tableinst v_tableinst) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_tableinst ret_val).
Proof.
	move => v_tableinst res_nat v_ref ret_val var_0 H Hwf Hne /eqP ->.
	by case: H Hne => [ti v_n r ti' i j_opt rt r'_lst i' _ _ _ /eqP -> _ Hwf2 _ | x0 x1 x2 _ ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
Lemma growmemory_is_wf : forall (v_meminst : meminst) (res_nat : N) (ret_val : meminst) (var_0 : (option meminst)),
	(fun_growmemory v_meminst res_nat var_0) ->
	(wf_meminst v_meminst) ->
	(var_0 != None) ->
	(ret_val == (!(var_0))) ->
	(wf_meminst ret_val).
Proof.
	move => v_meminst res_nat ret_val var_0 H Hwf Hne /eqP ->.
	by case: H Hne => [mi v_n mi' i j_opt b_lst i' _ _ _ _ /eqP -> _ Hwf2 _ | x0 x1 _ ].
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.10-6.19 *)
Lemma Step_pure_is_wf : forall (var_0 : (seq admininstr)) (var_1 : (seq admininstr)),
	List.Forall (fun (var_0 : admininstr) => (wf_admininstr var_0)) var_0 ->
	(Step_pure var_0 var_1) ->
	List.Forall (fun (var_1 : admininstr) => (wf_admininstr var_1)) var_1.
Proof.
	move => var_0 var_1 Hall H.
	have Hmono : forall (T : Type) (P Q : T -> Prop) (l : seq T),
		List.Forall P l -> (forall x, P x -> Q x) -> List.Forall Q l.
	{ move => T P Q. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl] Hpq.
		by apply: List.Forall_cons; [ apply: Hpq | apply: IH ]. }
	have Hav : forall v, wf_val v -> wf_admininstr (admininstr_val v).
	{ by move => v Hv; case: Hv => *; constructor. }
	have Hai : forall i, wf_instr i -> wf_admininstr (admininstr_instr i).
	{ move => i Hi. case: Hi => *; simpl;
		solve [ constructor | (econstructor; eassumption) ]. }
	have Hfmap : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall (fun x => P (f x)) l -> List.Forall P (seq.map f l).
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hfmapinv : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall P (seq.map f l) -> List.Forall (fun x => P (f x)) l.
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hmapi : forall l, List.Forall (fun x => wf_instr x) l ->
		List.Forall wf_admininstr (seq.map (fun x => admininstr_instr x) l).
	{ move => l Hl. apply: Hfmap. by apply: (Hmono _ _ _ _ Hl). }
	have Hin : forall (T : eqType) (P : T -> Prop) (l : seq T) (x : T),
		List.Forall P l -> (x \in l) -> P x.
	{ move => T P. elim => [ |y l IH] x //= /List.Forall_cons_iff [Hy Hl].
		rewrite in_cons => /orP [ /eqP -> // | Hx]. by apply: IH. }
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hs Hd; first by rewrite seq.nth_nil.
		inversion Hs; subst. case: n => [ |n] //=. by apply: IH. }
	have Har : forall r, wf_admininstr (admininstr_ref r).
	{ by case => *; constructor. }
	have Hrep : forall (T : Type) (P : T -> Prop) (x : T) (n : N),
		P x -> List.Forall P (list_repeat x n).
	{ move => T P x n Hx. rewrite /list_repeat. elim: (N.to_nat n) => [ |m IH] //=.
		by apply: List.Forall_cons. }
	have Hmkseq : forall (T : Type) (P : T -> Prop) (f : N -> T) (n : N),
		holds_upto (fun k => P (f k)) n -> List.Forall P (mkseqN f n).
	{ move => T P f n. rewrite /holds_upto /iotaN /mkseqN /mkseq => Hh.
		apply: Hfmap. by apply: (Hfmapinv _ _ (fun k => P (f k)) N.of_nat). }
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hl0 Hg //=.
		inversion Hl0; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	have Hfin : forall (sh : shape) (lls : seq (seq lane_)),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		List.Forall (fun v => wf_uN 128%N v) (seq.map (fun l => inv_lanes_ sh l) lls).
	{ move => sh lls Hsh0. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hcomb : forall (T U : Type) (P P1 : T -> Prop) (Q : U -> Prop) (R : T -> U -> Prop)
		(l1 : seq T) (l2 : seq U),
		List.Forall2 R l1 l2 -> List.Forall P1 l1 -> List.Forall Q l2 ->
		(forall a b, R a b -> P1 a -> Q b -> P a) -> List.Forall P l1.
	{ move => T U P P1 Q R l1 l2 H12 H1 H2 Hstep.
		elim: H12 H1 H2 => [ |x y l l' Hxy H12 IH] H1 H2.
		- by apply: List.Forall_nil.
		- move: H1 => /List.Forall_cons_iff [Hx H1]. move: H2 => /List.Forall_cons_iff [Hy H2].
			by apply: List.Forall_cons; [ apply: (Hstep _ _ Hxy Hx Hy) | apply: IH ]. }
	have Hbr : forall (l : uN), wf_uN 32%N (mk_uN (((l :> N) + 1%N)%BN)) -> wf_uN 32%N l.
	{ move => [i] Hw. apply: uN_case_0. inversion Hw; subst.
		match goal with | [ Hb : is_true (andb _ _) |- _ ] => move: Hb => /andP [_ Hle] end.
		rewrite /N_geb. apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		apply/N.leb_spec0. apply: (N.le_trans i (i + 1)%BN); first by apply: N.le_add_r.
		by apply/N.leb_spec0. }
	(* binop_ has no wf lemma: its clauses carry the wf premises of their results. *)
	have Hbinop : forall (nt : numtype) (op : binop_) (a b : num_) (l : seq num_),
		fun_binop_ nt op a b (Some l) -> List.Forall (fun x => wf_num_ nt x) l.
	{ move => nt op a b l Hb. inversion Hb; subst.
		all: first [ eassumption
			| (apply: List.Forall_cons; [ eassumption | apply: List.Forall_nil ])
			| (apply: Hfmap; eassumption) ]. }
	(* An in-range lane of a well-formed vector is well-formed. *)
	have Hlnth : forall (sh : shape) (v : vec_) (k : N),
		wf_shape sh -> wf_uN 128%N v -> is_true ((k <? (|lanes_ sh v|))%BN) ->
		wf_lane_ (fun_lanetype sh) ((lanes_ sh v)[| k |]).
	{ move => sh v k Hsh Hv /N.ltb_spec0 Hk.
		have Hk' : Peano.lt (N.to_nat k) (size (lanes_ sh v)).
		{ rewrite -(Nnat.Nat2N.id (size (lanes_ sh v))). apply/PeanoNat.Nat.compare_lt_iff.
			rewrite -Nnat.N2Nat.inj_compare. exact: Hk. }
		apply: (Hin _ _ _ _ (lanes__is_wf sh v _ Hsh Hv (eqxx _))).
		by rewrite /lookup_total; apply: mem_nth; apply/ssrnat.ltP. }
	case: H Hall => *.
	all: do 3 (
		repeat match goal with
			| [ Hx : List.Forall _ (_ :: _) |- _ ] => move: Hx => /List.Forall_cons_iff [? ?]
			| [ Hx : List.Forall _ (_ ++ _) |- _ ] => move: Hx => /List.Forall_app [? ?]
			end;
		repeat match goal with
			| [ Hx : wf_admininstr (admininstr_val _) |- _ ] => move: Hx
			| [ Hx : wf_admininstr (admininstr_instr _) |- _ ] => move: Hx
			| [ Hx : wf_admininstr (admininstr_ref _) |- _ ] => move: Hx
			end;
		repeat match goal with
			| [ Hx : wf_admininstr _ |- _ ] => inversion Hx; subst; clear Hx
			| [ Hx : wf_lane_ _ (mk_lane__0 _ _) |- _ ] => inversion Hx; subst; clear Hx
			| [ Hx : wf_lane_ _ (mk_lane__1 _ _) |- _ ] => inversion Hx; subst; clear Hx
			end;
		move => * ).
	all: try (by repeat first [ apply: List.Forall_nil | (apply/List.Forall_app; split)
		| apply: List.Forall_cons | eassumption | (apply: Har)
		| (apply: Hav; first [ eassumption
			| (eapply local_is_wf; first [ by apply: eqxx | eassumption | by [] ]) ])
		| (apply: Hai; eassumption) | (apply: Hmapi; eassumption)
		| (apply Hbr; eassumption)
		| (apply: Hnth; last by constructor) | constructor ]).
	all: try (apply: List.Forall_cons;
		[ (constructor;
			first [ by []
				| ( first [ (match goal with | [ Hc : is_true (?c == _) |- wf_num_ _ ?c ] =>
							move/eqP: Hc => -> end)
						| (match goal with | [ Hc : is_true (?c == _) |- wf_uN _ ?c ] =>
							move/eqP: Hc => -> end)
						| (match goal with | [ Hc : is_true (_ == ?c) |- wf_num_ _ ?c ] =>
							move/eqP: Hc => <- end)
						| (match goal with | [ Hc : is_true (_ == ?c) |- wf_uN _ ?c ] =>
							move/eqP: Hc => <- end)
						| (match goal with | [ Hc : is_true (?c \in _) |- wf_num_ _ ?c ] =>
							eapply Hin; last exact: Hc end)
						| (match goal with | [ Hc : is_true (?c \in _) |- wf_uN _ ?c ] =>
							eapply Hin; last exact: Hc end)
						| idtac ];
					solve [ (((eapply inv_lanes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption
							| (apply Hfmap; eassumption)
							| (apply Hmkseq; eassumption)
							| (apply Hrep; ((eapply packnum__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
							| ((apply/List.Forall_app; split); apply Hfmap; eassumption)
							| (apply Hupd;
								[ (((eapply lanes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
								| (move => ? ?; ((eapply packnum__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
							| (apply Hfmap; (eapply Hcomb;
								[ eassumption | eassumption | eassumption
								| (move => ? ? Hr Hp Hq; cbv beta in Hr, Hp, Hq;
									match type of Hr with
									| fun_vshiftop_ ?ish ?op ?cc ?uu _ =>
										((eapply (vshiftop__is_wf ish op cc uu); cycle -1);
											first (by apply: eqxx));
										first [ eassumption | by [] ]
									end) ])) ])
					| (apply Hfin; first [ eassumption | by [] ])
					| (((eapply unop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply testop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply relop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply cvtop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vvunop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vvbinop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vvternop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vunop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vbinop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vrelop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vshiftop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vcvtop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply lcvtop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vextunop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vextbinop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply narrow___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply lanes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply packnum__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply unpacknum__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply ieqz__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply irev__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply inez__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ] ) ])
		| by apply: List.Forall_nil ]).
	(* binop *)
	all: try (match goal with
		| [ Hb : fun_binop_ _ _ _ _ ?v, Hne : is_true (?v != None), Hc : is_true (?c \in !(?v)) |- _ ] =>
			apply: List.Forall_cons; last (by apply: List.Forall_nil);
			constructor; destruct v as [l| ]; last (by move: Hne; rewrite eqxx);
			exact: (Hin _ _ _ _ (Hbinop _ _ _ _ _ Hb) Hc) end).
	(* vextract_lane (numtype): the result comes through unpacknum_ from an
	   in-range lane of the operand. *)
	all: try (match goal with
		| [ Hc : is_true (?c == !(unpacknum_ ?lt ((lanes_ ?sh ?v)[| ?k |]))),
			Hne : is_true (unpacknum_ _ _ != None),
			Hk : is_true ((?k <? (|lanes_ ?sh ?v|))%BN),
			Hsh : wf_shape ?sh |- List.Forall _ [:: admininstr_CONST ?nt ?c] ] =>
			have Hl := Hlnth sh v k Hsh ltac:(eassumption) Hk;
			apply: List.Forall_cons; last (by apply: List.Forall_nil);
			constructor; destruct nt; exact: (unpacknum__is_wf _ _ _ Hl Hne Hc)
		end).
	(* vbitmask: ci is only related to a bit list through the ibits_ axiom, so
	   the rule carries a (wf_uN 32 ci) premise. *)
	all: apply: List.Forall_cons; last (by apply: List.Forall_nil).
	all: constructor; apply: num__case_0; [ by [] | | by [] ].
	all: match goal with | [ Hc : wf_uN 32%N ?ci |- wf_uN _ (irev_ 32%N ?ci) ] =>
			exact: (irev__is_wf 32%N ci _ Hc (eqxx _)) end.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 *)
(* Hand-modified statement: takes (Store_ok (fun_store z)) as a hypothesis,
   since the store bounds are needed for table.size, memory.size and the bulk rules. *)
Lemma Step_read_is_wf : forall (z : state) (admininstr_lst : (seq admininstr)) (var_1 : (seq admininstr)),
	(wf_config (mk_config z admininstr_lst)) ->
	(Store_ok (fun_store z)) ->
	(Step_read (mk_config z admininstr_lst) var_1) ->
	List.Forall (fun (var_1 : admininstr) => (wf_admininstr var_1)) var_1.
Proof.
	move => z0 ais0 var_1 Hcfg Hst0 H.
	remember (mk_config z0 ais0) as var_0 eqn:Heq0.
	have Hmono : forall (T : Type) (P Q : T -> Prop) (l : seq T),
		List.Forall P l -> (forall x, P x -> Q x) -> List.Forall Q l.
	{ move => T P Q. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl] Hpq.
		by apply: List.Forall_cons; [ apply: Hpq | apply: IH ]. }
	have Hav : forall v, wf_val v -> wf_admininstr (admininstr_val v).
	{ by move => v Hv; case: Hv => *; constructor. }
	have Hai : forall i, wf_instr i -> wf_admininstr (admininstr_instr i).
	{ move => i Hi. case: Hi => *; simpl;
		solve [ constructor | (econstructor; eassumption) ]. }
	have Hfmap : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall (fun x => P (f x)) l -> List.Forall P (seq.map f l).
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hfmapinv : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall P (seq.map f l) -> List.Forall (fun x => P (f x)) l.
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hmapi : forall l, List.Forall (fun x => wf_instr x) l ->
		List.Forall wf_admininstr (seq.map (fun x => admininstr_instr x) l).
	{ move => l Hl. apply: Hfmap. by apply: (Hmono _ _ _ _ Hl). }
	have Hin : forall (T : eqType) (P : T -> Prop) (l : seq T) (x : T),
		List.Forall P l -> (x \in l) -> P x.
	{ move => T P. elim => [ |y l IH] x //= /List.Forall_cons_iff [Hy Hl].
		rewrite in_cons => /orP [ /eqP -> // | Hx]. by apply: IH. }
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hs Hd; first by rewrite seq.nth_nil.
		inversion Hs; subst. case: n => [ |n] //=. by apply: IH. }
	have Har : forall r, wf_admininstr (admininstr_ref r).
	{ by case => *; constructor. }
	have Hrep : forall (T : Type) (P : T -> Prop) (x : T) (n : N),
		P x -> List.Forall P (list_repeat x n).
	{ move => T P x n Hx. rewrite /list_repeat. elim: (N.to_nat n) => [ |m IH] //=.
		by apply: List.Forall_cons. }
	have Hmkseq : forall (T : Type) (P : T -> Prop) (f : N -> T) (n : N),
		holds_upto (fun k => P (f k)) n -> List.Forall P (mkseqN f n).
	{ move => T P f n. rewrite /holds_upto /iotaN /mkseqN /mkseq => Hh.
		apply: Hfmap. by apply: (Hfmapinv _ _ (fun k => P (f k)) N.of_nat). }
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hl0 Hg //=.
		inversion Hl0; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	have Hfin : forall (sh : shape) (lls : seq (seq lane_)),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		List.Forall (fun v => wf_uN 128%N v) (seq.map (fun l => inv_lanes_ sh l) lls).
	{ move => sh lls Hsh0. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hcomb : forall (T U : Type) (P P1 : T -> Prop) (Q : U -> Prop) (R : T -> U -> Prop)
		(l1 : seq T) (l2 : seq U),
		List.Forall2 R l1 l2 -> List.Forall P1 l1 -> List.Forall Q l2 ->
		(forall a b, R a b -> P1 a -> Q b -> P a) -> List.Forall P l1.
	{ move => T U P P1 Q R l1 l2 H12 H1 H2 Hstep.
		elim: H12 H1 H2 => [ |x y l l' Hxy H12 IH] H1 H2.
		- by apply: List.Forall_nil.
		- move: H1 => /List.Forall_cons_iff [Hx H1]. move: H2 => /List.Forall_cons_iff [Hy H2].
			by apply: List.Forall_cons; [ apply: (Hstep _ _ Hxy Hx Hy) | apply: IH ]. }
	have Hbr : forall (l : uN), wf_uN 32%N (mk_uN (((l :> N) + 1%N)%BN)) -> wf_uN 32%N l.
	{ move => [i] Hw. apply: uN_case_0. inversion Hw; subst.
		match goal with | [ Hb : is_true (andb _ _) |- _ ] => move: Hb => /andP [_ Hle] end.
		rewrite /N_geb. apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		apply/N.leb_spec0. apply: (N.le_trans i (i + 1)%BN); first by apply: N.le_add_r.
		by apply/N.leb_spec0. }
	have Hgv : forall (z : state) (x : globalidx),
		wf_state z -> wf_uN 32%N x -> wf_val (VALUE (fun_global z x)).
	{ move => z x Hz Hx. have Hg := global_is_wf z x (fun_global z x) Hz Hx (eqxx _).
		by inversion Hg. }
	have Hl2 : forall (J : Jnn) (d : dim) (x : iN),
		wf_uN (lsize (lanetype_Jnn J)) x -> wf_lane_ (fun_lanetype (X (lanetype_Jnn J) d)) (mk_lane__0 J x).
	{ move => J [dn] x Hx. apply: lane__case_0; [ exact: Hx | exact: eqxx ]. }
	(* Bounds that Store_ok gives on the store looked up through a frame.
	   Out-of-range indices return default_val, whose lists are empty. *)
	have Hsnth : forall (T U : Type) (iT : Inhabited T) (R : T -> U -> Prop) (Q : T -> Prop)
		(l1 : seq T) (l2 : seq U) (k : N),
		List.Forall2 R l1 l2 -> (forall a b, R a b -> Q a) -> Q default_val -> Q (l1 [| k |]).
	{ move => T U iT R Q l1 l2 k H12 HRQ Hd. rewrite /lookup_total.
		elim: H12 (N.to_nat k) => [ |a b l1' l2' Hab _ IH] [ |n] //=.
		by apply: HRQ Hab. }
	have Hlim : forall (v_n : n) (m_opt : option m) (k : N),
		Limits_ok (mk_limits (mk_uN v_n) (option_map (fun (v_m : m) => (mk_uN v_m)) m_opt)) k ->
		(v_n <= k)%N.
	{ move => v_n m_opt k Hl. inversion Hl; subst.
		match goal with | [ Hb0 : is_true (N.leb v_n _) |- _ ] => by move/N.leb_spec0: Hb0 end. }
	have Htlen : forall (s : store) (f : frame) (x : tableidx),
		Store_ok s -> (|REFS (fun_table (mk_state s f) x)| < 4294967296)%N.
	{ move => s f x Hs.
		case: Hs => {}s gis gts mis mts tis tts fis fts dis dts eis ets
			_ _ _ _ _ Htab _ _ _ _ _ _ /eqP Hs _ _ _ _. subst s => /=.
		apply: (Hsnth _ _ _ _ (fun ti => (|REFS ti| < 4294967296)%N) _ _ _ Htab); last by [].
		move => a b Hab. inversion Hab as [s0 v_n m_opt rt refs Htt _ Hlen]; subst => /=.
		move/eqP: Hlen => ->. inversion Htt; subst.
		by apply: (N.le_lt_trans _ 4294967295); first by apply: (Hlim _ m_opt). }
	have Hmlen : forall (s : store) (f : frame) (x : memidx),
		Store_ok s -> exists (v_n : N),
			(|BYTES (fun_mem (mk_state s f) x)| = v_n * (64 * Ki))%N /\ (v_n <= 65536)%N /\
			(|BYTES (fun_mem (mk_state s f) x)| <= 4294967296)%N.
	{ move => s f x Hs.
		case: Hs => {}s gis gts mis mts tis tts fis fts dis dts eis ets
			_ _ _ Hmem _ _ _ _ _ _ _ _ /eqP Hs _ _ _ _. subst s => /=.
		apply: (Hsnth _ _ _ _ (fun mi => exists v_n : N,
			(|BYTES mi| = v_n * (64 * Ki))%N /\ (v_n <= 65536)%N /\ (|BYTES mi| <= 4294967296)%N) _ _ _ Hmem);
			last by exists 0%N; split; [ | split; vm_compute; discriminate ].
		move => a b Hab. inversion Hab as [s0 v_n m_opt bs Hmt Hlen]; subst => /=.
		move/eqP: Hlen => Hlen. inversion Hmt; subst.
		have Hv : (v_n <= 65536)%N by apply: (Hlim _ m_opt).
		exists v_n. split; first by []. split; first by [].
		rewrite Hlen. apply: (N.le_trans _ (65536 * (64 * Ki))); first by apply/N.mul_le_mono_r.
		by vm_compute; discriminate. }
	have Helen : forall (s : store) (f : frame) (y : tableidx),
		Store_ok s -> (|eleminst_REFS (fun_elem (mk_state s f) y)| < 4294967296)%N.
	{ move => s f y Hs.
		case: Hs => {}s gis gts mis mts tis tts fis fts dis dts eis ets
			_ _ _ _ _ _ _ _ _ _ _ Hel /eqP Hs _ _ _ _. subst s => /=.
		apply: (Hsnth _ _ _ _ (fun ei => (|eleminst_REFS ei| < 4294967296)%N) _ _ _ Hel);
			last by [].
		move => a b Hab. inversion Hab as [s0 rt refs _ Hlen]; subst => /=.
		by move/N.ltb_spec0: Hlen. }
	have Hdlen : forall (s : store) (f : frame) (y : dataidx),
		Store_ok s -> (|datainst_BYTES (fun_data (mk_state s f) y)| < 4294967296)%N.
	{ move => s f y Hs.
		case: Hs => {}s gis gts mis mts tis tts fis fts dis dts eis ets
			_ _ _ _ _ _ _ _ _ Hdat _ _ /eqP Hs _ _ _ _. subst s => /=.
		apply: (Hsnth _ _ _ _ (fun di => (|datainst_BYTES di| < 4294967296)%N) _ _ _ Hdat);
			last by [].
		move => a b Hab. inversion Hab as [s0 bs Hlen]; subst => /=.
		by move/N.ltb_spec0: Hlen. }
	have Hdbyte : forall (s : store) (f : frame) (x : dataidx) (j : N),
		wf_state (mk_state s f) ->
		(proj_byte_0 ((datainst_BYTES (fun_data (mk_state s f) x))[| j |]) < 4294967296)%N.
	{ move => s f x j Hz. inversion Hz as [? ? Hs _]; subst.
		inversion Hs as [? ? ? ? ? dis _ _ _ _ Hd]; subst => /=. rewrite /lookup_total.
		have Hdi : wf_datainst (seq.nth default_val dis (N.to_nat ((DATAS (frame_MODULE f))[| (x :> N) |]))).
		{ apply: Hnth => //; by constructor. }
		case: Hdi Hd => bs Hbs _ /=.
		have : wf_byte (seq.nth default_val bs (N.to_nat j)) by apply: Hnth => //; by constructor.
		case => i /andP [_ /N.leb_spec0 Hi] /=.
		by apply: (N.le_lt_trans _ 255). }
	(* Arithmetic on u32 results, without lia. *)
	have Hc32 : forall (x : N), (x < 4294967296)%N ->
		wf_admininstr (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN x))).
	{ move => x Hx. constructor. apply: num__case_0 => //. apply: uN_case_0.
		rewrite /N_geb. apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		apply/N.leb_spec0. by apply/N.lt_succ_r. }
	have Hwn : forall (x : N), wf_num_ I32 (mk_num__0 Inn_I32 (mk_uN x)) -> (x < 4294967296)%N.
	{ move => x Hw. inversion Hw as [? ? ? _ Hu | ]; subst. inversion Hu; subst.
		match goal with | [ Hb : is_true (andb _ _) |- _ ] => move: Hb => /andP [_ /N.leb_spec0 Hle] end.
		by apply: (N.le_lt_trans _ _ _ Hle). }
	have Hp1 : forall (x v_n L : N), (x + v_n <= L)%N -> v_n <> 0%N -> (L < 4294967296)%N ->
		(x + 1 < 4294967296)%N.
	{ move => x v_n L H1 H2 H3. apply: (N.le_lt_trans _ L) => //.
		apply: (N.le_trans _ (x + v_n)) => //. apply: (proj1 (N.add_le_mono_l 1 v_n x)).
		case: v_n {H1 H3} H2 => [ |p] Hnz; first by case: Hnz. clear Hnz. by case: p. }
	have Hm1 : forall (a : N), (a <= 4294967296)%N -> ((((a : Z) - (1%N : Z))%Z : N) < 4294967296)%N.
	{ case => [ |p] Ha //.
		have H1p : (1 <= N.pos p)%N by case: p {Ha}.
		rewrite -Znat.N2Z.inj_sub ?Znat.N2Z.id //.
		apply: (N.lt_le_trans _ (N.pos p)) => //. by apply: N.sub_lt. }
	have Hmsz : forall (v x L : N), is_true ((((v * 64)%N * Ki)%N) == L) -> L = (x * (64 * Ki))%N ->
		(x <= 65536)%N -> (v < 4294967296)%N.
	{ move => v x L /eqP H1 H2 H3. rewrite H2 -N.mul_assoc in H1.
		have Hnz : (64 * Ki)%N <> 0%N by vm_compute; discriminate.
		have Hv := proj1 (N.mul_cancel_r v x (64 * Ki) Hnz) H1. subst v.
		by apply: (N.le_lt_trans _ 65536). }
	case: H Hcfg Heq0 => *.
	all: match goal with | [ He : mk_config _ _ = mk_config _ _ |- _ ] => case: He => ? ?; subst end.
	all: repeat match goal with | [ Hx : wf_config _ |- _ ] => inversion Hx; subst; clear Hx end.

	all: do 3 (
		repeat match goal with
			| [ Hx : List.Forall _ (_ :: _) |- _ ] => move: Hx => /List.Forall_cons_iff [? ?]
			| [ Hx : List.Forall _ (_ ++ _) |- _ ] => move: Hx => /List.Forall_app [? ?]
			end;
		repeat match goal with
			| [ Hx : wf_admininstr (admininstr_val _) |- _ ] => move: Hx
			| [ Hx : wf_admininstr (admininstr_instr _) |- _ ] => move: Hx
			| [ Hx : wf_admininstr (admininstr_ref _) |- _ ] => move: Hx
			end;
		repeat match goal with
			| [ Hx : wf_admininstr _ |- _ ] => inversion Hx; subst; clear Hx
			| [ Hx : wf_lane_ _ (mk_lane__0 _ _) |- _ ] => inversion Hx; subst; clear Hx
			| [ Hx : wf_lane_ _ (mk_lane__1 _ _) |- _ ] => inversion Hx; subst; clear Hx
			end;
		move => * ).
	all: try (by repeat first [ apply: List.Forall_nil | (apply/List.Forall_app; split)
		| apply: List.Forall_cons | eassumption | (apply: Har)
		| (apply: Hav; first [ eassumption | (apply Hgv; first [ eassumption | by [] ])
			| (eapply local_is_wf; first [ by apply: eqxx | eassumption | by [] ]) ])
		| (apply: Hai; eassumption) | (apply: Hmapi; eassumption)
		| (apply Hbr; eassumption)
		| (apply: Hnth; last by constructor) | constructor ]).
	all: try (apply: List.Forall_cons;
		[ (constructor;
			first [ by []
				| ( first [ (match goal with | [ Hc : is_true (?c == _) |- wf_num_ _ ?c ] =>
							move/eqP: Hc => -> end)
						| (match goal with | [ Hc : is_true (?c == _) |- wf_uN _ ?c ] =>
							move/eqP: Hc => -> end)
						| (match goal with | [ Hc : is_true (_ == ?c) |- wf_num_ _ ?c ] =>
							move/eqP: Hc => <- end)
						| (match goal with | [ Hc : is_true (_ == ?c) |- wf_uN _ ?c ] =>
							move/eqP: Hc => <- end)
						| (match goal with | [ Hc : is_true (?c \in _) |- wf_num_ _ ?c ] =>
							eapply Hin; last exact: Hc end)
						| (match goal with | [ Hc : is_true (?c \in _) |- wf_uN _ ?c ] =>
							eapply Hin; last exact: Hc end)
						| idtac ];
					solve [ (((eapply inv_lanes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption
							| (apply Hfmap; eassumption)
							| (apply Hmkseq; eassumption)
							| (apply Hrep; ((eapply packnum__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
							| ((apply/List.Forall_app; split); apply Hfmap; eassumption)
							| (apply Hupd;
								[ (((eapply lanes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
								| (move => ? ?; ((eapply packnum__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
							| (apply Hfmap; (eapply Hcomb;
								[ eassumption | eassumption | eassumption
								| (move => ? ? Hr Hp Hq; cbv beta in Hr, Hp, Hq;
									match type of Hr with
									| fun_vshiftop_ ?ish ?op ?cc ?uu _ =>
										((eapply (vshiftop__is_wf ish op cc uu); cycle -1);
											first (by apply: eqxx));
										first [ eassumption | by [] ]
									end) ])) ])
					| (apply Hfin; first [ eassumption | by [] ])
					| (((eapply unop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply testop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply relop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply cvtop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vvunop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vvbinop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vvternop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vunop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vbinop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vrelop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vshiftop__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vcvtop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply lcvtop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vextunop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply vextbinop___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply narrow___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply lanes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply packnum__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply unpacknum__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply ieqz__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply irev__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ])
					| (((eapply inez__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ] ) ])
		| by apply: List.Forall_nil ]).
	all: try (repeat match goal with
			| [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end;
		subst;
		do 2 (repeat match goal with
			| [ Hx : wf_funcinst _ |- _ ] => inversion Hx; subst; clear Hx
			| [ Hx : wf_func _ |- _ ] => inversion Hx; subst; clear Hx
			end);
		by repeat first [ apply: List.Forall_nil | (apply/List.Forall_app; split)
			| apply: List.Forall_cons | eassumption | (apply: Har)
			| (apply: Hav; first [ eassumption | (apply Hgv; first [ eassumption | by [] ])
				| (eapply local_is_wf; first [ by apply: eqxx | eassumption | by [] ]) ])
			| (apply: Hai; eassumption) | (apply: Hmapi; eassumption)
			| (apply Hbr; eassumption)
			| (apply: Hnth; last by constructor) | constructor ]).
	(* vload shape / splat / lane: the result is built by inv_lanes_ from lanes
	   whose well-formedness is a premise (or, for vload_lane, follows from
	   lanes__is_wf on the input vector). *)
	all: try (apply: List.Forall_cons; last (by apply: List.Forall_nil);
		apply: admininstr_case_19; first (by []);
		match goal with | [ Hc : is_true (?c == inv_lanes_ ?sh ?l) |- _ ] =>
			apply: (inv_lanes__is_wf sh l); [ assumption | | exact Hc ] end;
		first [ assumption
			| (apply: Hrep; apply: Hl2; eassumption)
			| (apply: Hupd; [ (eapply lanes__is_wf; [ eassumption | eassumption | by apply: eqxx ])
				| (move => _ _; apply: Hl2; eassumption) ]) ]).
	(* vload zero: the result is (extend__ N 128 U j) with (wf_uN N j) a premise. *)
	all: try (apply: List.Forall_cons; last (by apply: List.Forall_nil);
		apply: admininstr_case_19; first (by []);
		match goal with | [ Hc : is_true (?c == extend__ ?m ?n ?sx ?j) |- _ ] =>
			apply: (extend___is_wf m n sx j); [ assumption | exact Hc ] end).
	(* With Store_ok: Tabletype_ok bounds every table by 2^32 - 1 entries,
	   Memtype_ok every memory by 2^16 pages, and Eleminst_ok / Datainst_ok
	   every segment instance by 2^32 - 1 entries. *)
	all: try (match goal with | [ Hs : Store_ok (fun_store ?z) |- _ ] =>
			is_var z; destruct z as [s0 f0]; simpl in Hs end).
	all: do 6 try match goal with
			| [ Hs : Store_ok ?s, H : context [ N.of_nat (seq.size (REFS (fun_table (mk_state ?s ?f) ?x))) ] |- _ ] =>
				have := Htlen s f x Hs; move => ?;
				let L := fresh "L" in set (L := N.of_nat (seq.size (REFS (fun_table (mk_state s f) x)))) in *; clearbody L
			| [ Hs : Store_ok ?s, H : context [ N.of_nat (seq.size (BYTES (fun_mem (mk_state ?s ?f) ?x))) ] |- _ ] =>
				have [? [? [? ?]]] := Hmlen s f x Hs;
				let L := fresh "L" in set (L := N.of_nat (seq.size (BYTES (fun_mem (mk_state s f) x)))) in *; clearbody L
			| [ Hs : Store_ok ?s, H : context [ N.of_nat (seq.size (eleminst_REFS (fun_elem (mk_state ?s ?f) ?x))) ] |- _ ] =>
				have := Helen s f x Hs; move => ?;
				let L := fresh "L" in set (L := N.of_nat (seq.size (eleminst_REFS (fun_elem (mk_state s f) x)))) in *; clearbody L
			| [ Hs : Store_ok ?s, H : context [ N.of_nat (seq.size (datainst_BYTES (fun_data (mk_state ?s ?f) ?x))) ] |- _ ] =>
				have := Hdlen s f x Hs; move => ?;
				let L := fresh "L" in set (L := N.of_nat (seq.size (datainst_BYTES (fun_data (mk_state s f) x)))) in *; clearbody L
			end.
	all: repeat match goal with
			| [ H : is_true (_ && _) |- _ ] => move/andP: H => [? ?]
			end.
	all: repeat match goal with
			| [ H : is_true (N.leb _ _) |- _ ] => move/N.leb_spec0: H => ?
			| [ H : is_true (_ != 0%N) |- _ ] => move/eqP: H => ?
			| [ H : wf_num_ I32 (mk_num__0 Inn_I32 (mk_uN ?a)) |- _ ] => have := Hwn a H; clear H; move => ?
			end.
	all: repeat first [ apply: List.Forall_nil | apply: List.Forall_cons ].
	all: try (apply: Hc32; first
		[ (apply: Hp1; eassumption)
		| (apply: Hm1; apply: N.lt_le_incl; eassumption)
		| (apply: Hm1; eapply N.le_trans; [ eassumption | apply: N.lt_le_incl; eassumption ])
		| (apply: Hm1; eapply N.le_trans; eassumption)
		| (match goal with | [ H : is_true (?L == ?v) |- (?v < _)%N ] => move/eqP: H => <-; assumption end)
		| (eapply Hmsz; eassumption)
		| (apply: Hdbyte; eassumption) ]).
	all: try (first [ assumption | apply: Har | (apply: Hav; eassumption)
		| (by constructor) | (by constructor; eassumption)
		| (solve [ constructor; try exact: (memarg0_is_wf memarg0 (eqxx _)); repeat constructor ])
		| (solve [ apply: (admininstr_case_56 (Some Inn_I32));
			[ by repeat constructor | exact: (memarg0_is_wf memarg0 (eqxx _)) | by split
			| by repeat constructor ] ]) ]).
	(* load-pack-val: the loaded value c carries a (wf_uN n c) premise, and the
	   result is (extend__ n (size Inn) sx c). *)
	all: try (match goal with |- context [ mk_num__0 ?v (extend__ _ _ _ _) ] => is_var v; destruct v end;
		constructor; apply: num__case_0 => //;
		(eapply extend___is_wf; last by apply: eqxx); eassumption).
	(* memory.fill-succ, memory.copy-le and memory.init-succ: the incremented
	   offsets are $iadd_(32, i, 1), well formed by iadd__is_wf. *)
	all: (match goal with |- context [ iadd_ _ (!(proj_num__0 ?k)) _ ] =>
		match goal with H : wf_num_ _ k |- _ => inversion H; subst end end).
	all: match goal with
		| [ Hn : is_true (proj_num__0 (mk_num__1 _ _) != None) |- _ ] => by move: Hn
		| [ Hn : is_true (I32 == numtype_Inn ?v) |- _ ] => destruct v; try by move: Hn
		end.
	all: constructor; apply: num__case_0 => //=.
	all: (eapply iadd__is_wf; last by apply: eqxx); [ eassumption | by apply: uN_case_0 ].
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 *)
(* Hand-modified statement: takes (Store_ok (fun_store z)) as a hypothesis,
   as its read case goes through Step_read_is_wf. *)
Lemma Step_is_wf : forall (z : state) (admininstr_lst : (seq admininstr)) (var_1 : config),
	(wf_config (mk_config z admininstr_lst)) ->
	(Store_ok (fun_store z)) ->
	(Step (mk_config z admininstr_lst) var_1) ->
	(wf_config var_1).
Proof.
	move => z0 ais0 var_1 Hcfg Hst0 H.
	remember (mk_config z0 ais0) as var_0 eqn:Heq0.
	have Hmono : forall (T : Type) (P Q : T -> Prop) (l : seq T),
		List.Forall P l -> (forall x, P x -> Q x) -> List.Forall Q l.
	{ move => T P Q. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl] Hpq.
		by apply: List.Forall_cons; [ apply: Hpq | apply: IH ]. }
	have Hav : forall v, wf_val v -> wf_admininstr (admininstr_val v).
	{ by move => v Hv; case: Hv => *; constructor. }
	have Hai : forall i, wf_instr i -> wf_admininstr (admininstr_instr i).
	{ move => i Hi. case: Hi => *; simpl;
		solve [ constructor | (econstructor; eassumption) ]. }
	have Hfmap : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall (fun x => P (f x)) l -> List.Forall P (seq.map f l).
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hfmapinv : forall (T U : Type) (P : U -> Prop) (f : T -> U) (l : seq T),
		List.Forall P (seq.map f l) -> List.Forall (fun x => P (f x)) l.
	{ move => T U P f. elim => [ |x l IH] //= /List.Forall_cons_iff [Hx Hl].
		by apply: List.Forall_cons; [ | apply: IH ]. }
	have Hmapi : forall l, List.Forall (fun x => wf_instr x) l ->
		List.Forall wf_admininstr (seq.map (fun x => admininstr_instr x) l).
	{ move => l Hl. apply: Hfmap. by apply: (Hmono _ _ _ _ Hl). }
	have Hin : forall (T : eqType) (P : T -> Prop) (l : seq T) (x : T),
		List.Forall P l -> (x \in l) -> P x.
	{ move => T P. elim => [ |y l IH] x //= /List.Forall_cons_iff [Hy Hl].
		rewrite in_cons => /orP [ /eqP -> // | Hx]. by apply: IH. }
	have Hnth : forall (T : Type) (P : T -> Prop) (d : T) (s : seq T) (n : nat),
		List.Forall P s -> P d -> P (seq.nth d s n).
	{ move => T P d s. elim: s => [ |x s IH] n Hs Hd; first by rewrite seq.nth_nil.
		inversion Hs; subst. case: n => [ |n] //=. by apply: IH. }
	have Har : forall r, wf_admininstr (admininstr_ref r).
	{ by case => *; constructor. }
	have Hrep : forall (T : Type) (P : T -> Prop) (x : T) (n : N),
		P x -> List.Forall P (list_repeat x n).
	{ move => T P x n Hx. rewrite /list_repeat. elim: (N.to_nat n) => [ |m IH] //=.
		by apply: List.Forall_cons. }
	have Hmkseq : forall (T : Type) (P : T -> Prop) (f : N -> T) (n : N),
		holds_upto (fun k => P (f k)) n -> List.Forall P (mkseqN f n).
	{ move => T P f n. rewrite /holds_upto /iotaN /mkseqN /mkseq => Hh.
		apply: Hfmap. by apply: (Hfmapinv _ _ (fun k => P (f k)) N.of_nat). }
	have Hupd : forall (T : Type) (P : T -> Prop) (l : seq T) (n : N) (g : T -> T),
		List.Forall P l -> (forall x, P x -> P (g x)) -> List.Forall P (list_update_func l n g).
	{ move => T P l. elim: l => [ |x l IH] n g Hl0 Hg //=.
		inversion Hl0; subst. case: n => [ |p]; apply: List.Forall_cons => //.
		- by apply: Hg.
		- by apply: IH. }
	have Hfin : forall (sh : shape) (lls : seq (seq lane_)),
		wf_shape sh ->
		List.Forall (fun l => List.Forall (fun x => wf_lane_ (fun_lanetype sh) x) l) lls ->
		List.Forall (fun v => wf_uN 128%N v) (seq.map (fun l => inv_lanes_ sh l) lls).
	{ move => sh lls Hsh0. elim: lls => [ |l lls IH] //= /List.Forall_cons_iff [Hl Hlls].
		apply: List.Forall_cons; last by apply: IH.
		by apply: (inv_lanes__is_wf sh l). }
	have Hcomb : forall (T U : Type) (P P1 : T -> Prop) (Q : U -> Prop) (R : T -> U -> Prop)
		(l1 : seq T) (l2 : seq U),
		List.Forall2 R l1 l2 -> List.Forall P1 l1 -> List.Forall Q l2 ->
		(forall a b, R a b -> P1 a -> Q b -> P a) -> List.Forall P l1.
	{ move => T U P P1 Q R l1 l2 H12 H1 H2 Hstep.
		elim: H12 H1 H2 => [ |x y l l' Hxy H12 IH] H1 H2.
		- by apply: List.Forall_nil.
		- move: H1 => /List.Forall_cons_iff [Hx H1]. move: H2 => /List.Forall_cons_iff [Hy H2].
			by apply: List.Forall_cons; [ apply: (Hstep _ _ Hxy Hx Hy) | apply: IH ]. }
	have Hbr : forall (l : uN), wf_uN 32%N (mk_uN (((l :> N) + 1%N)%BN)) -> wf_uN 32%N l.
	{ move => [i] Hw. apply: uN_case_0. inversion Hw; subst.
		match goal with | [ Hb : is_true (andb _ _) |- _ ] => move: Hb => /andP [_ Hle] end.
		rewrite /N_geb. apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		apply/N.leb_spec0. apply: (N.le_trans i (i + 1)%BN); first by apply: N.le_add_r.
		by apply/N.leb_spec0. }
	have Hmono32 : forall (a b : N), (a <= b)%BN -> wf_uN 32%N (mk_uN b) -> wf_uN 32%N (mk_uN a).
	{ move => a b Hab Hb0. apply: uN_case_0. inversion Hb0; subst.
		match goal with | [ Hc : is_true (andb _ _) |- _ ] => move: Hc => /andP [_ Hle0] end.
		rewrite /N_geb. apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		apply/N.leb_spec0. apply: (N.le_trans _ _ _ Hab). by apply/N.leb_spec0. }
	have HtoNmono : forall (a b : Z), (a <= b)%Z -> (Z.to_N a <= Z.to_N b)%BN.
	{ move => a b Hab. case: (Z.le_gt_cases 0 a) => Ha.
		- by apply: (proj1 (Znat.Z2N.inj_le a b Ha (Z.le_trans _ _ _ Ha Hab)) Hab).
		- have Hz : (Z.to_N a = 0%N) by case: a Ha Hab => [ |p|p] //=.
			rewrite Hz. by apply: N.le_0_l. }
	have HQnn : forall (m : N), (0 <= (m : Q))%Q.
	{ move => m. rewrite -(Qle_bool_iff 0 (m : Q)). by case: m. }
	have HQle : forall (q : Q) (m : N), (((q : N)) <= (((q + (m : Q))%Q : N)))%BN.
	{ move => q m. apply: HtoNmono. apply: Qfloor_resp_le.
		rewrite -{1}(Qplus_0_r q). by apply/Qplus_le_r; apply: HQnn. }
	have HinnInj : forall a b : Inn, numtype_Inn a = numtype_Inn b -> a = b.
	{ by move => [] []. }
	have Hva : forall v, wf_admininstr (admininstr_val v) -> wf_val v.
	{ move => v Hx. case: v Hx => *; simpl in *;
		match goal with | [ Hy : wf_admininstr _ |- _ ] => inversion Hy; subst end;
		solve [ (constructor; eassumption) | constructor ]. }
	have Hfr : forall s f, wf_state (mk_state s f) -> wf_frame f.
	{ move => s f Hs0. by inversion Hs0. }
	have Hst : forall s f s' f', wf_state (mk_state s f) -> wf_state (mk_state s' f') ->
		wf_state (mk_state s f').
	{ move => s f s' f' H1 H2. inversion H1; inversion H2; subst. by apply: state_case_0. }
	have Hto : forall m : N, ((((m : Z) - (1%N : Z))%Z : N) = (m - 1)%BN).
	{ case => [ |p] //. by rewrite -Znat.N2Z.inj_sub ?Znat.N2Z.id //; apply/N.neq_0_le_1. }
	have Hp : forall (vN : res_N), (0 < (2%N ^ vN)%BN)%BN.
	{ by move => vN; apply/N.neq_0_lt_0; apply: N.pow_nonzero. }
	have HtoN : forall (vN : res_N) (z2 : Z),
		(z2 < ((2%N ^ vN)%BN : Z))%Z -> (((z2 : N)) < (2%N ^ vN)%BN)%BN.
	{ move => vN; case => [ |q|q] Hz //=; try exact: Hp.
		have Hnn : (0 <= Z.pos q)%Z by [].
		have := (proj1 (Znat.Z2N.inj_lt (Z.pos q) _ Hnn (Znat.N2Z.is_nonneg _)) Hz).
		by rewrite Znat.N2Z.id. }
	have Hbnd : forall (vN : res_N) (x : N), (x < (2%N ^ vN)%BN)%BN -> wf_uN vN (mk_uN x).
	{ move => vN x Hx. apply: uN_case_0. rewrite Hto /N_geb.
		apply/andP; split; first by apply/N.leb_spec0; apply: N.le_0_l.
		by apply/N.leb_spec0; rewrite N.sub_1_r; apply: N.lt_le_pred. }
	have Hle : forall (vN : res_N),
		((2%N ^ ((((vN : Z) - (1%N : Z))%Z : N)))%BN <= (2%N ^ vN)%BN)%BN.
	{ move => vN. apply: N.pow_le_mono_r => //. rewrite Hto. exact: N.le_sub_l. }
	have Hinv : forall (vN : res_N) (z : Z) (m : N), fun_inv_signed_ vN z m -> wf_uN vN (mk_uN m).
	{ move => vN0 z m Hi. case: Hi => vN i /andP [Ha Hb]; apply: Hbnd; apply: HtoN.
		- have Hlt2 : (i < ((2%N ^ ((((vN : Z) - (1%N : Z))%Z : N)))%BN : Z))%Z
				by apply: (proj1 (Z.ltb_lt _ _) Hb).
			apply: (Z.lt_le_trans _ _ _ Hlt2). by apply/Znat.N2Z.inj_le; apply: Hle.
		- rewrite -{2}(Z.add_0_l ((2%N ^ vN)%BN : Z)).
			by apply: (proj1 (Z.add_lt_mono_r _ _ _) (proj1 (Z.ltb_lt _ _) Hb)). }
	case: H Hcfg Heq0 => *.
	all: match goal with | [ He : mk_config _ _ = mk_config _ _ |- _ ] => case: He => ? ?; subst end.
	all: try by eassumption.
	all: repeat match goal with | [ Hx : wf_config _ |- _ ] => inversion Hx; subst; clear Hx end.
	all: do 2 (
		repeat match goal with
			| [ Hx : List.Forall _ (_ :: _) |- _ ] => move: Hx => /List.Forall_cons_iff [? ?]
			| [ Hx : List.Forall _ (_ ++ _) |- _ ] => move: Hx => /List.Forall_app [? ?]
			end;
		repeat match goal with
			| [ Hx : wf_admininstr (admininstr_val _) |- _ ] => move: Hx
			| [ Hx : wf_admininstr (admininstr_instr _) |- _ ] => move: Hx
			| [ Hx : wf_admininstr (admininstr_ref _) |- _ ] => move: Hx
			end;
		repeat match goal with
			| [ Hx : wf_admininstr _ |- _ ] => inversion Hx; subst; clear Hx
			| [ Hx : wf_num_ _ (mk_num__0 _ _) |- _ ] => inversion Hx; subst; clear Hx
			end;
		move => * ).
	all: repeat match goal with | [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end.
	all: subst.
	all: try (apply: config_case_0;
		[ solve [ eassumption | (apply: state_case_0; eassumption)
			| (eapply Hst; eassumption)
			| (((eapply with_local_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_global_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_tableinst_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_meminst_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_elem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_data_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) ]
		| solve [ ((eapply Step_pure_is_wf; only 2: eassumption); eassumption)
			| ((eapply Step_read_is_wf; only 3: eassumption);
				first [ eassumption | (apply: config_case_0; eassumption) ])
			| repeat first [ apply: List.Forall_nil | (apply/List.Forall_app; split)
				| apply: List.Forall_cons | eassumption | (apply: Har)
				| (apply: Hav; eassumption) | (apply: Hai; eassumption)
				| (apply: Hmapi; eassumption) | (eapply Hinv; eassumption)
				| (eapply Hfr; eassumption) | constructor ] ] ]).
	all: try (apply: config_case_0;
		[ solve [ eassumption | (apply: state_case_0; eassumption)
			| (eapply Hst; eassumption)
			| (((eapply with_local_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_global_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_tableinst_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_meminst_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_elem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_data_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])  ]
		| ( match goal with
				| [ Hg : fun_growtable _ _ _ _ |- _ ] => inversion Hg; subst
				| [ Hg : fun_growmemory _ _ _ |- _ ] => inversion Hg; subst
				end;
			first
			[ (by match goal with
					| [ Hn : is_true (_ != _) |- _ ] => move: Hn; rewrite eqxx end)
			| ( repeat match goal with
						| [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end;
				match goal with
					| [ Het : _ = fun_table _ _ |- _ ] => rewrite -Het
					| [ Het : _ = fun_mem _ _ |- _ ] => rewrite -Het
					end; simpl; subst;
				repeat match goal with
					| [ Hx : wf_tableinst _ |- _ ] => inversion Hx; subst; clear Hx
					| [ Hx : wf_tabletype _ |- _ ] => inversion Hx; subst; clear Hx
					| [ Hx : wf_meminst _ |- _ ] => inversion Hx; subst; clear Hx
					| [ Hx : wf_memtype _ |- _ ] => inversion Hx; subst; clear Hx
					| [ Hx : wf_limits _ |- _ ] => inversion Hx; subst; clear Hx
					end;
				apply: List.Forall_cons; [ | by apply: List.Forall_nil ];
				(* `i'` is now only pinned up to Qeq, so replace it by its definition
				   under the (Qeq-invariant) N projection instead of by subst. *)
				try (match goal with
					| [ Hq : is_true (Qeq_bool _ _) |- _ ] =>
						let Hn := fresh "Hn" in
						move: (Qeq_bool_toN _ _ Hq) => Hn;
						match goal with
						| [ Hw : wf_uN 32%N (mk_uN (Z.to_N (Qfloor _))) |- _ ] => rewrite Hn in Hw
						end
					end);
				constructor; constructor;
				first [ by []
					| ((eapply Hmono32; last (by eassumption)); by apply: N.le_add_r)
					| ((eapply Hmono32; last (by eassumption)); by apply: HQle) ] ) ] ) ]).
	all: try (apply: config_case_0;
		[ solve [ eassumption | (apply: state_case_0; eassumption)
			| (eapply Hst; eassumption)
			| (((eapply with_local_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_global_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_tableinst_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_meminst_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_elem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_data_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])  ]
		| ( match goal with
				| [ Hg : fun_growtable _ _ _ _ |- _ ] => inversion Hg; subst
				| [ Hg : fun_growmemory _ _ _ |- _ ] => inversion Hg; subst
				end;
			first
			[ (by match goal with
					| [ Hn : is_true (_ != _) |- _ ] => move: Hn; rewrite eqxx end)
			| ( repeat match goal with
						| [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end;
				match goal with
					| [ Het : _ = fun_table _ _ |- _ ] => rewrite -Het
					| [ Het : _ = fun_mem _ _ |- _ ] => rewrite -Het
					end; cbn [REFS BYTES]; subst;
				repeat match goal with
					| [ Hx : wf_tableinst _ |- _ ] => inversion Hx; subst; clear Hx
					| [ Hx : wf_tabletype _ |- _ ] => inversion Hx; subst; clear Hx
					| [ Hx : wf_meminst _ |- _ ] => inversion Hx; subst; clear Hx
					| [ Hx : wf_memtype _ |- _ ] => inversion Hx; subst; clear Hx
					| [ Hx : wf_limits _ |- _ ] => inversion Hx; subst; clear Hx
					end;
				apply: List.Forall_cons; [ | by apply: List.Forall_nil ];
				(* `i'` is now only pinned up to Qeq, so replace it by its definition
				   under the (Qeq-invariant) N projection instead of by subst. *)
				try (match goal with
					| [ Hq : is_true (Qeq_bool _ _) |- _ ] =>
						let Hn := fresh "Hn" in
						move: (Qeq_bool_toN _ _ Hq) => Hn;
						match goal with
						| [ Hw : wf_uN 32%N (mk_uN (Z.to_N (Qfloor _))) |- _ ] => rewrite Hn in Hw
						end
					end);
				constructor; constructor;
				first [ by []
					| ((eapply Hmono32; last (by eassumption)); by apply: N.le_add_r)
					| ((eapply Hmono32; last (by eassumption)); by apply: HQle) ] ) ] ) ]).
	all: (
		match goal with
			| [ Hn : wf_num_ (numtype_Inn _) _ |- _ ] => inversion Hn; subst
			end;
		first
		[ (by match goal with
				| [ Hq : is_true (_ != _) |- _ ] => move: Hq; rewrite eqxx end)
		| ( repeat match goal with
					| [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end;
			repeat match goal with
				| [ He : numtype_Inn ?a = numtype_Inn ?b |- _ ] =>
					tryif constr_eq a b then fail else (have Hab := HinnInj _ _ He; subst)
				end;
			apply: config_case_0;
			[ solve [ eassumption | (apply: state_case_0; eassumption)
				| (eapply Hst; eassumption)
				| (((eapply with_local_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_global_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_tableinst_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_meminst_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_elem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
			| (((eapply with_data_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (apply: Hva; eassumption)
				| (((eapply growtable_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ]) | (((eapply growmemory_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by []
					| (((eapply table_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply mem_is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply ibytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] | (((eapply wrap___is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])
				| (((eapply nbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) | (((eapply vbytes__is_wf; cycle -1); first (by apply: eqxx)); first [ eassumption | by [] ]) ])  ]
			| solve [ repeat first [ apply: List.Forall_nil | (apply/List.Forall_app; split)
				| apply: List.Forall_cons | eassumption | (apply: Har)
				| (apply: Hav; eassumption) | (apply: Hai; eassumption)
				| (apply: Hmapi; eassumption) | (eapply Hinv; eassumption)
				| (eapply Hfr; eassumption) | constructor ] ] ] ) ]).
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 *)
Lemma allocfunc_is_wf : forall (v_store : store) (v_moduleinst : moduleinst) (v_func : func) (ret_val : (store * funcaddr)) (var_0 : (store * funcaddr)),
	(fun_allocfunc v_store v_moduleinst v_func var_0) ->
	(wf_store v_store) ->
	(wf_moduleinst v_moduleinst) ->
	(wf_func v_func) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store v_moduleinst v_func ret_val var_0 H Hs Hm Hf /eqP ->.
	case: H Hs => /= s mi fn fi x loc e H1 /eqP -> H3 H4 H5 Hs.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //=.
	by apply/List.Forall_app; split; [ | apply: List.Forall_cons ].
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
Lemma allocfuncs_is_wf : forall (v_store : store) (v_moduleinst : moduleinst) (var_0_lst : (seq func)) (ret_val : (store * (seq funcaddr))) (var_0 : (store * (seq funcaddr))),
	(fun_allocfuncs v_store v_moduleinst var_0_lst var_0) ->
	(wf_store v_store) ->
	(wf_moduleinst v_moduleinst) ->
	List.Forall (fun (var_0 : func) => (wf_func var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store v_moduleinst var_0_lst ret_val var_0 H Hs Hm Hall /eqP ->.
	elim: H Hs Hm Hall.
	- by move => s mi Hs _ _.
	- move => s mi fn fl fa s1 s2 fal var1 var0 Hfs IH Hfa /eqP E1 /eqP E2 Hs Hm
			/List.Forall_cons_iff [Hf Hfl].
		rewrite -E2 /= in IH. rewrite /=. apply: IH => //.
		have Hs1 := allocfunc_is_wf s mi fn var0 var0 Hfa Hs Hm Hf (eqxx var0).
		by rewrite -E1 /= in Hs1.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
Lemma allocglobal_is_wf : forall (v_store : store) (v_globaltype : globaltype) (v_val : val) (ret_val : (store * globaladdr)) (var_0 : (store * globaladdr)),
	(fun_allocglobal v_store v_globaltype v_val var_0) ->
	(wf_store v_store) ->
	(wf_val v_val) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store v_globaltype v_val ret_val var_0 H Hs Hv /eqP ->.
	case: H Hs => /= s gt v gi /eqP -> Hgi Hs.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //=.
	by apply/List.Forall_app; split; [ | apply: List.Forall_cons ].
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
Lemma allocglobals_is_wf : forall (v_store : store) (var_0_lst : (seq globaltype)) (var_1_lst : (seq val)) (ret_val : (store * (seq globaladdr))) (var_0 : (store * (seq globaladdr))),
	(fun_allocglobals v_store var_0_lst var_1_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_1 : val) => (wf_val var_1)) var_1_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store var_0_lst var_1_lst ret_val var_0 H Hs Hall /eqP ->.
	elim: H Hs Hall.
	- by move => s Hs _.
	- move => s gt gtl v vl ga s1 s2 gal var1 var0 Hgs IH Hga /eqP E1 /eqP E2 Hs
			/List.Forall_cons_iff [Hv Hvl].
		rewrite -E2 /= in IH. rewrite /=. apply: IH => //.
		have Hs1 := allocglobal_is_wf s gt v var0 var0 Hga Hs Hv (eqxx var0).
		by rewrite -E1 /= in Hs1.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
Lemma alloctable_is_wf : forall (v_store : store) (v_tabletype : tabletype) (ret_val : (store * tableaddr)) (var_0 : (store * tableaddr)),
	(fun_alloctable v_store v_tabletype var_0) ->
	(wf_store v_store) ->
	(wf_tabletype v_tabletype) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store v_tabletype ret_val var_0 H Hs Ht /eqP ->.
	case: H Hs Ht => /= s i j_opt rt ti /eqP -> Hti Hs Ht.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //=.
	by apply/List.Forall_app; split; [ | apply: List.Forall_cons ].
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
Lemma alloctables_is_wf : forall (v_store : store) (var_0_lst : (seq tabletype)) (ret_val : (store * (seq tableaddr))) (var_0 : (store * (seq tableaddr))),
	(fun_alloctables v_store var_0_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0 : tabletype) => (wf_tabletype var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store var_0_lst ret_val var_0 H Hs Hall /eqP ->.
	elim: H Hs Hall.
	- by move => s Hs _.
	- move => s tt ttl ta s1 s2 tal var1 var0 Hts IH Hta /eqP E1 /eqP E2 Hs
			/List.Forall_cons_iff [Ht Htl].
		rewrite -E2 /= in IH. rewrite /=. apply: IH => //.
		have Hs1 := alloctable_is_wf s tt var0 var0 Hta Hs Ht (eqxx var0).
		by rewrite -E1 /= in Hs1.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
Lemma allocmem_is_wf : forall (v_store : store) (v_memtype : memtype) (ret_val : (store * memaddr)) (var_0 : (store * memaddr)),
	(fun_allocmem v_store v_memtype var_0) ->
	(wf_store v_store) ->
	(wf_memtype v_memtype) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store v_memtype ret_val var_0 H Hs Hm /eqP ->.
	case: H Hs Hm => /= s i j_opt mi /eqP -> Hmi Hs Hm.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //=.
	by apply/List.Forall_app; split; [ | apply: List.Forall_cons ].
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
Lemma allocmems_is_wf : forall (v_store : store) (var_0_lst : (seq memtype)) (ret_val : (store * (seq memaddr))) (var_0 : (store * (seq memaddr))),
	(fun_allocmems v_store var_0_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0 : memtype) => (wf_memtype var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store var_0_lst ret_val var_0 H Hs Hall /eqP ->.
	elim: H Hs Hall.
	- by move => s Hs _.
	- move => s mt mtl ma s1 s2 mal var1 var0 Hms IH Hma /eqP E1 /eqP E2 Hs
			/List.Forall_cons_iff [Hm Hml].
		rewrite -E2 /= in IH. rewrite /=. apply: IH => //.
		have Hs1 := allocmem_is_wf s mt var0 var0 Hma Hs Hm (eqxx var0).
		by rewrite -E1 /= in Hs1.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
Lemma allocelem_is_wf : forall (v_store : store) (v_reftype : reftype) (var_0_lst : (seq ref)) (ret_val : (store * elemaddr)) (var_0 : (store * elemaddr)),
	(fun_allocelem v_store v_reftype var_0_lst var_0) ->
	(wf_store v_store) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store v_reftype var_0_lst ret_val var_0 H Hs /eqP ->.
	case: H Hs => /= s rt rl ei /eqP -> Hs.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	by apply: store_case_.
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
Lemma allocelems_is_wf : forall (v_store : store) (var_0_lst : (seq reftype)) (var_1_lst_lst : (seq (seq ref))) (ret_val : (store * (seq elemaddr))) (var_0 : (store * (seq elemaddr))),
	(fun_allocelems v_store var_0_lst var_1_lst_lst var_0) ->
	(wf_store v_store) ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store var_0_lst var_1_lst_lst ret_val var_0 H Hs /eqP ->.
	elim: H Hs.
	- by move => s Hs.
	- move => s rt rtl rl rll ea s1 s2 eal var1 var0 Hes IH Hea /eqP E1 /eqP E2 Hs.
		rewrite -E2 /= in IH. rewrite /=. apply: IH.
		have Hs1 := allocelem_is_wf s rt rl var0 var0 Hea Hs (eqxx var0).
		by rewrite -E1 /= in Hs1.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
Lemma allocdata_is_wf : forall (v_store : store) (var_0_lst : (seq byte)) (ret_val : (store * dataaddr)) (var_0 : (store * dataaddr)),
	(fun_allocdata v_store var_0_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store var_0_lst ret_val var_0 H Hs Hb /eqP ->.
	case: H Hs Hb => /= s bl di /eqP -> Hdi Hs Hb.
	case: Hs => fl gl tl ml el dl Hfl Hgl Htl Hml Hdl.
	apply: store_case_ => //=.
	by apply/List.Forall_app; split; [ | apply: List.Forall_cons ].
Qed.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
Lemma allocdatas_is_wf : forall (v_store : store) (var_0_lst_lst : (seq (seq byte))) (ret_val : (store * (seq dataaddr))) (var_0 : (store * (seq dataaddr))),
	(fun_allocdatas v_store var_0_lst_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0_lst : (seq byte)) => List.Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst) var_0_lst_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1).
Proof.
	move => v_store var_0_lst_lst ret_val var_0 H Hs Hall /eqP ->.
	elim: H Hs Hall.
	- by move => s Hs _.
	- move => s bl bll da s1 s2 dal var1 var0 Hds IH Hda /eqP E1 /eqP E2 Hs
			/List.Forall_cons_iff [Hb Hbl].
		rewrite -E2 /= in IH. rewrite /=. apply: IH => //.
		have Hs1 := allocdata_is_wf s bl var0 var0 Hda Hs Hb (eqxx var0).
		by rewrite -E1 /= in Hs1.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:100.6-100.17 *)
Lemma instexport_is_wf : forall (var_0_lst : (seq funcaddr)) (var_1_lst : (seq globaladdr)) (var_2_lst : (seq tableaddr)) (var_3_lst : (seq memaddr)) (v_export : export) (ret_val : exportinst),
	(wf_export v_export) ->
	(ret_val == (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export)) ->
	(wf_exportinst ret_val).
Proof.
	move => var_0_lst var_1_lst var_2_lst var_3_lst v_export ret_val Hwf /eqP ->.
	case: Hwf => nm xi Hn Hx.
	by case: xi Hx => x Hx /=; apply: exportinst_case_.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
Lemma allocmodule_is_wf : forall (v_store : store) (v_module : module) (var_0_lst : (seq externaddr)) (var_1_lst : (seq val)) (var_2_lst_lst : (seq (seq ref))) (ret_val : (store * moduleinst)) (var_0 : (store * moduleinst)),
	(fun_allocmodule v_store v_module var_0_lst var_1_lst var_2_lst_lst var_0) ->
	(wf_store v_store) ->
	(wf_module v_module) ->
	List.Forall (fun (var_1 : val) => (wf_val var_1)) var_1_lst ->
	(ret_val == var_0) ->
	(wf_store ret_val.1) ->
	(wf_moduleinst ret_val.2).
Proof.
	move => v_store v_module var_0_lst var_1_lst var_2_lst_lst ret_val var_0 H Hs Hm Hall /eqP -> _.
	case: H => *; simpl.
	repeat match goal with | [ Hq : is_true (_ == _) |- _ ] => move/eqP: Hq => Hq end.
	by subst.
Qed.

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
Lemma invoke_is_wf : forall (v_store : store) (v_funcaddr : funcaddr) (var_0_lst : (seq val)) (ret_val : config) (var_0 : config),
	(fun_invoke v_store v_funcaddr var_0_lst var_0) ->
	(wf_store v_store) ->
	List.Forall (fun (var_0 : val) => (wf_val var_0)) var_0_lst ->
	(ret_val == var_0) ->
	(wf_config ret_val).
Proof.
	move => v_store v_funcaddr var_0_lst ret_val var_0 H Hs Hall /eqP ->.
	have Hav : forall v, wf_val v -> wf_admininstr (admininstr_val v).
	{ by move => v Hv; case: Hv => *; constructor. }
	case: H Hall => s fa v_n vl f t_1_lst t_2_lst _ _ _ _ Hst _ Hall.
	apply: config_case_0 => //.
	apply/List.Forall_app; split; last first.
	- by apply: List.Forall_cons; [ apply: admininstr_case_69 | apply: List.Forall_nil ].
	- elim: vl Hall => [ |v vl IH] //= /List.Forall_cons_iff [Hv Hvl].
		by apply: List.Forall_cons; [ apply: Hav | apply: IH ].
Qed.

