(* Total counterparts of the partial SpecTec functions.

   The Rocq backend translates every SpecTec function with a partial operation
   (an option projection [!], a list lookup [_[|_|]]) into an inductive
   relation [fun_X] whose premises are the side conditions.  This file gives
   back the total function computed by each relation (under its old name when
   the relation has taken a new one, with an [_f] suffix otherwise), with
   lemmas relating the two:

     fun_X_inv   : fun_X args v -> v = X args (and the side conditions)
     fun_X_intro : side conditions -> fun_X args (X args)

   The size functions of number and lane types are total, so their relations
   hold exactly of their functions ([fun_sizenn_eq] etc.). *)

From Stdlib Require Import String List Unicode.Utf8 NArith QArith QArith.Qround.
From mathcomp Require Import ssreflect eqtype ssrbool ssrfun seq.
From HB Require Import structures.
From RecordUpdate Require Import RecordSet.
From WasmSpectec Require Import wasm.

Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.

(** * Sizes *)

Definition sizenn (v_numtype : numtype) : N := !((res_size (valtype_numtype v_numtype))).
Definition sizenn1 (v_numtype : numtype) : N := !((res_size (valtype_numtype v_numtype))).
Definition sizenn2 (v_numtype : numtype) : N := !((res_size (valtype_numtype v_numtype))).
Definition isize (v_Inn : Inn) : N := !((res_size (valtype_Inn v_Inn))).
Definition fsize (v_Fnn : Fnn) : N := !((res_size (valtype_Fnn v_Fnn))).

Definition lsize (v_lanetype : lanetype) : N :=
	match v_lanetype return N with
		| lanetype_I32 => (!((res_size (valtype_numtype I32))))
		| lanetype_I64 => (!((res_size (valtype_numtype I64))))
		| lanetype_F32 => (!((res_size (valtype_numtype F32))))
		| lanetype_F64 => (!((res_size (valtype_numtype F64))))
		| lanetype_I8 => (psize I8)
		| lanetype_I16 => (psize I16)
	end.

Definition jsize (v_Jnn : Jnn) : N := lsize (lanetype_Jnn v_Jnn).
Definition lsizenn (v_lanetype : lanetype) : N := lsize v_lanetype.
Definition lsizenn1 (v_lanetype : lanetype) : N := lsize v_lanetype.
Definition lsizenn2 (v_lanetype : lanetype) : N := lsize v_lanetype.

Definition shsize (v_shape : shape) : N :=
	match v_shape return N with
		| (X v_Lnn (mk_dim v_N)) => ((lsize v_Lnn) * v_N)%BN
	end.

Lemma res_size_numtype nt : res_size (valtype_numtype nt) != None.
Proof. by case: nt. Qed.

Lemma res_size_Inn t : res_size (valtype_Inn t) != None.
Proof. by case: t. Qed.

Lemma res_size_Fnn t : res_size (valtype_Fnn t) != None.
Proof. by case: t. Qed.

Lemma fun_sizenn_eq nt n : fun_sizenn nt n <-> n = sizenn nt.
Proof. split; [by case | move ->; constructor; exact: res_size_numtype]. Qed.

Lemma fun_sizenn1_eq nt n : fun_sizenn1 nt n <-> n = sizenn1 nt.
Proof. split; [by case | move ->; constructor; exact: res_size_numtype]. Qed.

Lemma fun_sizenn2_eq nt n : fun_sizenn2 nt n <-> n = sizenn2 nt.
Proof. split; [by case | move ->; constructor; exact: res_size_numtype]. Qed.

Lemma fun_isize_eq t n : fun_isize t n <-> n = isize t.
Proof. split; [by case | move ->; constructor; exact: res_size_Inn]. Qed.

Lemma fun_fsize_eq t n : fun_fsize t n <-> n = fsize t.
Proof. split; [by case | move ->; constructor; exact: res_size_Fnn]. Qed.

Lemma fun_lsize_eq lt n : fun_lsize lt n <-> n = lsize lt.
Proof. split; [by case | move ->; case: lt; by constructor]. Qed.

Lemma fun_jsize_eq t n : fun_jsize t n <-> n = jsize t.
Proof.
	split; [by case => ? ? /fun_lsize_eq | move ->; constructor; exact/fun_lsize_eq].
Qed.

Lemma fun_lsizenn_eq lt n : fun_lsizenn lt n <-> n = lsizenn lt.
Proof.
	split; [by case => ? ? /fun_lsize_eq | move ->; constructor; exact/fun_lsize_eq].
Qed.

Lemma fun_lsizenn1_eq lt n : fun_lsizenn1 lt n <-> n = lsizenn1 lt.
Proof.
	split; [by case => ? ? /fun_lsize_eq | move ->; constructor; exact/fun_lsize_eq].
Qed.

Lemma fun_lsizenn2_eq lt n : fun_lsizenn2 lt n <-> n = lsizenn2 lt.
Proof.
	split; [by case => ? ? /fun_lsize_eq | move ->; constructor; exact/fun_lsize_eq].
Qed.

Lemma fun_shsize_eq sh n : fun_shsize sh n <-> n = shsize sh.
Proof.
	split; first by case => ? ? ? /fun_lsize_eq ->.
	case: sh => L [d] ->. constructor. exact/fun_lsize_eq.
Qed.

(** * Floating-point parameters *)

Definition fun_M_f (v_N : res_N) : N := !((signif v_N)).
Definition E (v_N : res_N) : N := !((expon v_N)).
Definition canon_ (v_N : res_N) : N :=
	(2%N ^ ((((!((signif v_N))) : Z) - (1%N : Z))%Z : N))%BN.
Definition fzero (v_N : res_N) : fN := POS (SUBNORM 0%N).

Lemma fun_M_inv n m : fun_M n m -> m = fun_M_f n /\ signif n != None.
Proof. by case. Qed.

Lemma fun_M_intro n : signif n != None -> fun_M n (fun_M_f n).
Proof. by constructor. Qed.

Lemma fun_E_inv n m : fun_E n m -> m = E n /\ expon n != None.
Proof. by case. Qed.

Lemma fun_E_intro n : expon n != None -> fun_E n (E n).
Proof. by constructor. Qed.

Lemma fun_canon__inv n m : fun_canon_ n m -> m = canon_ n /\ signif n != None.
Proof. by case. Qed.

Lemma fun_canon__intro n : signif n != None -> fun_canon_ n (canon_ n).
Proof. by constructor. Qed.

Lemma fun_fzero_inv n z : fun_fzero n z -> z = fzero n /\ wf_fN n (fzero n).
Proof. by case. Qed.

Lemma fun_fzero_intro n : wf_fN n (fzero n) -> fun_fzero n (fzero n).
Proof. by constructor. Qed.

(* +0 is a well-formed float of the sizes that have a significand and an
   exponent (32 and 64). *)
Lemma wf_fzero n : signif n != None -> expon n != None -> wf_fN n (fzero n).
Proof.
	move => Hs He. apply: fN_case_0.
	eapply (fNmag_case_1 n _ 0%N (E n) (fun_M_f n)); [exact: fun_E_intro | exact: fun_M_intro | ].
	apply/andP; split; last exact: eqxx.
	by apply/N.ltb_spec0; apply/N.neq_0_lt_0; apply: N.pow_nonzero.
Qed.

Lemma fun_fzero_32 : fun_fzero 32%N (fzero 32%N).
Proof. by apply: fun_fzero_intro; apply: wf_fzero. Qed.

Lemma fun_fzero_64 : fun_fzero 64%N (fzero 64%N).
Proof. by apply: fun_fzero_intro; apply: wf_fzero. Qed.

(** * Zero and default values *)

Definition fun_zero_f (v_numtype : numtype) : num_ :=
	match v_numtype return num_ with
		| I32 => (mk_num__0 Inn_I32 (mk_uN 0%N))
		| I64 => (mk_num__0 Inn_I64 (mk_uN 0%N))
		| F32 => (mk_num__1 Fnn_F32 (fzero (!((res_size (valtype_Fnn Fnn_F32))))))
		| F64 => (mk_num__1 Fnn_F64 (fzero (!((res_size (valtype_Fnn Fnn_F64))))))
	end.

Lemma fun_zero_inv nt z : fun_zero nt z -> z = fun_zero_f nt.
Proof. by case => // v /fun_fzero_inv [-> _]. Qed.
Lemma fun_zero_intro nt : fun_zero nt (fun_zero_f nt).
Proof. case: nt; constructor => //; [exact: fun_fzero_32 | exact: fun_fzero_64]. Qed.

Definition default_ (v_valtype : valtype) : (option val) :=
	match v_valtype return (option val) with
		| valtype_I32 => (Some (val_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0%N))))
		| valtype_I64 => (Some (val_CONST I64 (mk_num__0 Inn_I64 (mk_uN 0%N))))
		| valtype_F32 => (Some (val_CONST F32 (mk_num__1 Fnn_F32 (fzero 32%N))))
		| valtype_F64 => (Some (val_CONST F64 (mk_num__1 Fnn_F64 (fzero 64%N))))
		| valtype_V128 => (Some (val_VCONST V128 (mk_uN 0%N)))
		| valtype_FUNCREF => (Some (val_REF_NULL FUNCREF))
		| valtype_EXTERNREF => (Some (val_REF_NULL EXTERNREF))
		| x0 => None
	end.

Lemma fun_default__intro t : fun_default_ t (default_ t).
Proof.
	case: t; try by constructor.
	- constructor; exact: fun_fzero_32.
	- constructor; exact: fun_fzero_64.
	- by apply: fun_default__case_7 => H; inversion H.
Qed.

Lemma fun_default__inv t o : fun_default_ t o -> o = default_ t.
Proof.
	case => //; try by move => v /fun_fzero_inv [-> _].
	move => t' Hn. case: t' Hn => //= Hn.
	all: exfalso; apply: Hn; first [ exact: (fun_default__case_2 (fzero 32%N))
		| exact: (fun_default__case_3 (fzero 64%N)) | constructor ].
Qed.

(** * Bitwise vector operations *)

Definition vvunop_ (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) : vec_ :=
	match v_vectype, v_vvunop, v_vec_ return vec_ with
		| V128, NOT, v128 => (inot_ (!((res_size valtype_V128))) v128)
	end.

Definition vvbinop_ (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) : vec_ :=
	match v_vectype, v_vvbinop, v_vec_, vec__0 return vec_ with
		| V128, vvbinop_AND, v128_1, v128_2 => (iand_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, ANDNOT, v128_1, v128_2 => (iandnot_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, vvbinop_OR, v128_1, v128_2 => (ior_ (!((res_size valtype_V128))) v128_1 v128_2)
		| V128, vvbinop_XOR, v128_1, v128_2 => (ixor_ (!((res_size valtype_V128))) v128_1 v128_2)
	end.

Definition vvternop_ (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) : vec_ :=
	match v_vectype, v_vvternop, v_vec_, vec__0, vec__1 return vec_ with
		| V128, BITSELECT, v128_1, v128_2, v128_3 => (ibitselect_ (!((res_size valtype_V128))) v128_1 v128_2 v128_3)
	end.

Lemma fun_vvunop__eq vt op v r : fun_vvunop_ vt op v r <-> r = vvunop_ vt op v.
Proof. split; [by case | case: vt; case: op => ->; by constructor]. Qed.

Lemma fun_vvbinop__eq vt op v1 v2 r : fun_vvbinop_ vt op v1 v2 r <-> r = vvbinop_ vt op v1 v2.
Proof. split; [by case | case: vt; case: op => ->; by constructor]. Qed.

Lemma fun_vvternop__eq vt op v1 v2 v3 r :
	fun_vvternop_ vt op v1 v2 v3 r <-> r = vvternop_ vt op v1 v2 v3.
Proof. split; [by case | case: vt; case: op => ->; by constructor]. Qed.

(** * State accessors *)

Definition fun_type_f (v_state : state) (v_typeidx : typeidx) : functype :=
	match v_state, v_typeidx return functype with
		| (mk_state s f), x => ((TYPES (frame_MODULE f))[| (x :> N) |])
	end.

Definition fun_func_f (v_state : state) (v_funcidx : funcidx) : funcinst :=
	match v_state, v_funcidx return funcinst with
		| (mk_state s f), x => ((store_FUNCS s)[| ((FUNCS (frame_MODULE f))[| (x :> N) |]) |])
	end.

Definition fun_global_f (v_state : state) (v_globalidx : globalidx) : globalinst :=
	match v_state, v_globalidx return globalinst with
		| (mk_state s f), x => ((store_GLOBALS s)[| ((GLOBALS (frame_MODULE f))[| (x :> N) |]) |])
	end.

Definition fun_table_f (v_state : state) (v_tableidx : tableidx) : tableinst :=
	match v_state, v_tableidx return tableinst with
		| (mk_state s f), x => ((store_TABLES s)[| ((TABLES (frame_MODULE f))[| (x :> N) |]) |])
	end.

Definition fun_mem_f (v_state : state) (v_memidx : memidx) : meminst :=
	match v_state, v_memidx return meminst with
		| (mk_state s f), x => ((store_MEMS s)[| ((MEMS (frame_MODULE f))[| (x :> N) |]) |])
	end.

Definition fun_elem_f (v_state : state) (v_tableidx : tableidx) : eleminst :=
	match v_state, v_tableidx return eleminst with
		| (mk_state s f), x => ((store_ELEMS s)[| ((ELEMS (frame_MODULE f))[| (x :> N) |]) |])
	end.

Definition fun_data_f (v_state : state) (v_dataidx : dataidx) : datainst :=
	match v_state, v_dataidx return datainst with
		| (mk_state s f), x => ((store_DATAS s)[| ((DATAS (frame_MODULE f))[| (x :> N) |]) |])
	end.

Definition fun_local_f (v_state : state) (v_localidx : localidx) : val :=
	match v_state, v_localidx return val with
		| (mk_state s f), x => ((LOCALS f)[| (x :> N) |])
	end.

(* The side condition of the accessors: an index of the module instance that
   points into the store. *)
Definition addr_in {A B : Type} (idx : seq N) (st : seq A) (x : N) : Prop :=
	(x <? |idx|)%BN /\ (idx[| x |] <? |st|)%BN.

Lemma fun_type_inv z x ft :
	fun_type z x ft -> ft = fun_type_f z x /\ ((x :> N) <? |TYPES (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_type_intro s f x :
	((x :> N) <? |TYPES (frame_MODULE f)|)%BN -> fun_type (mk_state s f) x (fun_type_f (mk_state s f) x).
Proof. case: x => x. by constructor. Qed.

Lemma fun_func_inv z x fi :
	fun_func z x fi -> fi = fun_func_f z x /\
		((FUNCS (frame_MODULE (fun_frame z)))[| x :> N |] <? |store_FUNCS (fun_store z)|)%BN /\
		((x :> N) <? |FUNCS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_func_intro s f x :
	((FUNCS (frame_MODULE f))[| x :> N |] <? |store_FUNCS s|)%BN ->
	((x :> N) <? |FUNCS (frame_MODULE f)|)%BN ->
	fun_func (mk_state s f) x (fun_func_f (mk_state s f) x).
Proof. case: x => x. by constructor. Qed.

Lemma fun_global_inv z x gi :
	fun_global z x gi -> gi = fun_global_f z x /\
		((GLOBALS (frame_MODULE (fun_frame z)))[| x :> N |] <? |store_GLOBALS (fun_store z)|)%BN /\
		((x :> N) <? |GLOBALS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_global_intro s f x :
	((GLOBALS (frame_MODULE f))[| x :> N |] <? |store_GLOBALS s|)%BN ->
	((x :> N) <? |GLOBALS (frame_MODULE f)|)%BN ->
	fun_global (mk_state s f) x (fun_global_f (mk_state s f) x).
Proof. case: x => x. by constructor. Qed.

Lemma fun_table_inv z x ti :
	fun_table z x ti -> ti = fun_table_f z x /\
		((TABLES (frame_MODULE (fun_frame z)))[| x :> N |] <? |store_TABLES (fun_store z)|)%BN /\
		((x :> N) <? |TABLES (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_table_intro s f x :
	((TABLES (frame_MODULE f))[| x :> N |] <? |store_TABLES s|)%BN ->
	((x :> N) <? |TABLES (frame_MODULE f)|)%BN ->
	fun_table (mk_state s f) x (fun_table_f (mk_state s f) x).
Proof. case: x => x. by constructor. Qed.

Lemma fun_mem_inv z x mi :
	fun_mem z x mi -> mi = fun_mem_f z x /\
		((MEMS (frame_MODULE (fun_frame z)))[| x :> N |] <? |store_MEMS (fun_store z)|)%BN /\
		((x :> N) <? |MEMS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_mem_intro s f x :
	((MEMS (frame_MODULE f))[| x :> N |] <? |store_MEMS s|)%BN ->
	((x :> N) <? |MEMS (frame_MODULE f)|)%BN ->
	fun_mem (mk_state s f) x (fun_mem_f (mk_state s f) x).
Proof. case: x => x. by constructor. Qed.

Lemma fun_elem_inv z x ei :
	fun_elem z x ei -> ei = fun_elem_f z x /\
		((ELEMS (frame_MODULE (fun_frame z)))[| x :> N |] <? |store_ELEMS (fun_store z)|)%BN /\
		((x :> N) <? |ELEMS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_elem_intro s f x :
	((ELEMS (frame_MODULE f))[| x :> N |] <? |store_ELEMS s|)%BN ->
	((x :> N) <? |ELEMS (frame_MODULE f)|)%BN ->
	fun_elem (mk_state s f) x (fun_elem_f (mk_state s f) x).
Proof. case: x => x. by constructor. Qed.

Lemma fun_data_inv z x di :
	fun_data z x di -> di = fun_data_f z x /\
		((DATAS (frame_MODULE (fun_frame z)))[| x :> N |] <? |store_DATAS (fun_store z)|)%BN /\
		((x :> N) <? |DATAS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_data_intro s f x :
	((DATAS (frame_MODULE f))[| x :> N |] <? |store_DATAS s|)%BN ->
	((x :> N) <? |DATAS (frame_MODULE f)|)%BN ->
	fun_data (mk_state s f) x (fun_data_f (mk_state s f) x).
Proof. case: x => x. by constructor. Qed.

Lemma fun_local_inv z x v :
	fun_local z x v -> v = fun_local_f z x /\ ((x :> N) <? |LOCALS (fun_frame z)|)%BN.
Proof. by case. Qed.

Lemma fun_local_intro s f x :
	((x :> N) <? |LOCALS f|)%BN -> fun_local (mk_state s f) x (fun_local_f (mk_state s f) x).
Proof. case: x => x. by constructor. Qed.

Definition fun_blocktype_f (v_state : state) (v_blocktype : blocktype) : functype :=
	match v_state, v_blocktype return functype with
		| z, (_RESULT None) => (mk_functype (mk_list _ [:: ]) (mk_list _ [:: ]))
		| z, (_RESULT (Some t)) => (mk_functype (mk_list _ [:: ]) (mk_list _ [::t]))
		| z, (_IDX x) => (fun_type_f z x)
	end.

Lemma fun_blocktype_inv z bt ft :
	fun_blocktype z bt ft -> ft = fun_blocktype_f z bt.
Proof. by case => // ? ? ? /fun_type_inv []. Qed.

(** * State updates *)

Definition with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
	match v_state, v_globalidx, v_val return state with
		| (mk_state s f), x, v => (mk_state (s <| store_GLOBALS := (list_update_func (store_GLOBALS s) ((GLOBALS (frame_MODULE f))[| (x :> N) |]) (fun (var_1 : globalinst) => (var_1 <| VALUE := v |>))) |>) f)
	end.

Definition with_table (v_state : state) (v_tableidx : tableidx) (res_nat : N) (v_ref : ref) : state :=
	match v_state, v_tableidx, res_nat, v_ref return state with
		| (mk_state s f), x, i, r => (mk_state (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f))[| (x :> N) |]) (fun (var_1 : tableinst) => (var_1 <| REFS := (list_update_func (REFS var_1) i (fun (_ : ref) => r)) |>))) |>) f)
	end.

Definition with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
	match v_state, v_tableidx, v_tableinst return state with
		| (mk_state s f), x, ti => (mk_state (s <| store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f))[| (x :> N) |]) (fun (_ : tableinst) => ti)) |>) f)
	end.

Definition with_mem (v_state : state) (v_memidx : memidx) (res_nat : N) (nat_0 : N) (var_0_lst : (seq byte)) : state :=
	match v_state, v_memidx, res_nat, nat_0, var_0_lst return state with
		| (mk_state s f), x, i, j, b_lst => (mk_state (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f))[| (x :> N) |]) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (BYTES var_1) i j b_lst) |>))) |>) f)
	end.

Definition with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
	match v_state, v_memidx, v_meminst return state with
		| (mk_state s f), x, mi => (mk_state (s <| store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f))[| (x :> N) |]) (fun (_ : meminst) => mi)) |>) f)
	end.

Definition with_elem (v_state : state) (v_elemidx : elemidx) (var_0_lst : (seq ref)) : state :=
	match v_state, v_elemidx, var_0_lst return state with
		| (mk_state s f), x, r_lst => (mk_state (s <| store_ELEMS := (list_update_func (store_ELEMS s) ((ELEMS (frame_MODULE f))[| (x :> N) |]) (fun (var_1 : eleminst) => (var_1 <| eleminst_REFS := r_lst |>))) |>) f)
	end.

Definition with_data (v_state : state) (v_dataidx : dataidx) (var_0_lst : (seq byte)) : state :=
	match v_state, v_dataidx, var_0_lst return state with
		| (mk_state s f), x, b_lst => (mk_state (s <| store_DATAS := (list_update_func (store_DATAS s) ((DATAS (frame_MODULE f))[| (x :> N) |]) (fun (var_1 : datainst) => (var_1 <| datainst_BYTES := b_lst |>))) |>) f)
	end.

Lemma fun_with_global_inv z x v z' :
	fun_with_global z x v z' -> z' = with_global z x v /\
		((x :> N) <? |GLOBALS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_with_global_intro s f x v :
	((x :> N) <? |GLOBALS (frame_MODULE f)|)%BN ->
	fun_with_global (mk_state s f) x v (with_global (mk_state s f) x v).
Proof. case: x => x. by constructor. Qed.

Lemma fun_with_table_inv z x i r z' :
	fun_with_table z x i r z' -> z' = with_table z x i r /\
		((x :> N) <? |TABLES (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_with_table_intro s f x i r :
	((x :> N) <? |TABLES (frame_MODULE f)|)%BN ->
	fun_with_table (mk_state s f) x i r (with_table (mk_state s f) x i r).
Proof. case: x => x. by constructor. Qed.

Lemma fun_with_tableinst_inv z x ti z' :
	fun_with_tableinst z x ti z' -> z' = with_tableinst z x ti /\
		((x :> N) <? |TABLES (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_with_tableinst_intro s f x ti :
	((x :> N) <? |TABLES (frame_MODULE f)|)%BN ->
	fun_with_tableinst (mk_state s f) x ti (with_tableinst (mk_state s f) x ti).
Proof. case: x => x. by constructor. Qed.

Lemma fun_with_mem_inv z x i j bs z' :
	fun_with_mem z x i j bs z' -> z' = with_mem z x i j bs /\
		((x :> N) <? |MEMS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_with_mem_intro s f x i j bs :
	((x :> N) <? |MEMS (frame_MODULE f)|)%BN ->
	fun_with_mem (mk_state s f) x i j bs (with_mem (mk_state s f) x i j bs).
Proof. case: x => x. by constructor. Qed.

Lemma fun_with_meminst_inv z x mi z' :
	fun_with_meminst z x mi z' -> z' = with_meminst z x mi /\
		((x :> N) <? |MEMS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_with_meminst_intro s f x mi :
	((x :> N) <? |MEMS (frame_MODULE f)|)%BN ->
	fun_with_meminst (mk_state s f) x mi (with_meminst (mk_state s f) x mi).
Proof. case: x => x. by constructor. Qed.

Lemma fun_with_elem_inv z x rs z' :
	fun_with_elem z x rs z' -> z' = with_elem z x rs /\
		((x :> N) <? |ELEMS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_with_elem_intro s f x rs :
	((x :> N) <? |ELEMS (frame_MODULE f)|)%BN ->
	fun_with_elem (mk_state s f) x rs (with_elem (mk_state s f) x rs).
Proof. case: x => x. by constructor. Qed.

Lemma fun_with_data_inv z x bs z' :
	fun_with_data z x bs z' -> z' = with_data z x bs /\
		((x :> N) <? |DATAS (frame_MODULE (fun_frame z))|)%BN.
Proof. by case. Qed.

Lemma fun_with_data_intro s f x bs :
	((x :> N) <? |DATAS (frame_MODULE f)|)%BN ->
	fun_with_data (mk_state s f) x bs (with_data (mk_state s f) x bs).
Proof. case: x => x. by constructor. Qed.

(** * Module instantiation *)

Definition instexport (var_0_lst : (seq funcaddr)) (var_1_lst : (seq globaladdr)) (var_2_lst : (seq tableaddr)) (var_3_lst : (seq memaddr)) (v_export : export) : exportinst :=
	match var_0_lst, var_1_lst, var_2_lst, var_3_lst, v_export return exportinst with
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_FUNC x)) => {| NAME := v_name; ADDR := (externaddr_FUNC (fa_lst[| (x :> N) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_GLOBAL x)) => {| NAME := v_name; ADDR := (externaddr_GLOBAL (ga_lst[| (x :> N) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_TABLE x)) => {| NAME := v_name; ADDR := (externaddr_TABLE (ta_lst[| (x :> N) |])) |}
		| fa_lst, ga_lst, ta_lst, ma_lst, (EXPORT v_name (externidx_MEM x)) => {| NAME := v_name; ADDR := (externaddr_MEM (ma_lst[| (x :> N) |])) |}
	end.

Lemma fun_instexport_inv fa ga ta ma e ei :
	fun_instexport fa ga ta ma e ei -> ei = instexport fa ga ta ma e.
Proof. by case. Qed.

(** * Well-formedness in terms of the total functions

   The constructors of the well-formedness predicates whose premises now go
   through the size relations, restated with the old (functional) premises,
   and their inversions. *)

Lemma shape_case_0' L d : wf_dim d -> ((lsize L * (d :> N))%BN == 128%N) -> wf_shape (X L d).
Proof. move=> Hd H. apply: (shape_case_0 _ _ (lsize L)) => //. exact/fun_lsize_eq. Qed.

Lemma wf_shape_inv L d : wf_shape (X L d) -> wf_dim d /\ ((lsize L * (d :> N))%BN == 128%N).
Proof. inversion 1; subst. match goal with H : fun_lsize _ _ |- _ => move/fun_lsize_eq: H => <- end. by split. Qed.

Lemma num__case_1' nt F x :
	wf_fN (sizenn (numtype_Fnn F)) x -> nt == numtype_Fnn F -> wf_num_ nt (mk_num__1 F x).
Proof. move=> H1 H2. apply: (num__case_1 _ _ _ (sizenn (numtype_Fnn F))) => //. exact/fun_sizenn_eq. Qed.

Lemma wf_num_1_inv nt F x :
	wf_num_ nt (mk_num__1 F x) -> wf_fN (sizenn (numtype_Fnn F)) x /\ nt == numtype_Fnn F.
Proof. inversion 1; subst. match goal with H : fun_sizenn _ _ |- _ => move/fun_sizenn_eq: H => <- end. by split. Qed.

Lemma lane__case_0' L J x :
	wf_uN (lsize (lanetype_Jnn J)) x -> L == lanetype_Jnn J -> wf_lane_ L (mk_lane__0 J x).
Proof. move=> H1 H2. apply: (lane__case_0 _ _ _ (lsize (lanetype_Jnn J))) => //. exact/fun_lsize_eq. Qed.

Lemma wf_lane_0_inv L J x :
	wf_lane_ L (mk_lane__0 J x) -> wf_uN (lsize (lanetype_Jnn J)) x /\ L == lanetype_Jnn J.
Proof. inversion 1; subst. match goal with H : fun_lsize _ _ |- _ => move/fun_lsize_eq: H => <- end. by split. Qed.

Lemma lane__case_1' L F x :
	wf_fN (sizenn (numtype_Fnn F)) x -> L == lanetype_Fnn F -> wf_lane_ L (mk_lane__1 F x).
Proof. move=> H1 H2. apply: (lane__case_1 _ _ _ (sizenn (numtype_Fnn F))) => //. exact/fun_sizenn_eq. Qed.

Lemma wf_lane_1_inv L F x :
	wf_lane_ L (mk_lane__1 F x) -> wf_fN (sizenn (numtype_Fnn F)) x /\ L == lanetype_Fnn F.
Proof. inversion 1; subst. match goal with H : fun_sizenn _ _ |- _ => move/fun_sizenn_eq: H => <- end. by split. Qed.

Lemma loadop_Inn_case_0' I sz sx :
	wf_sz sz -> ((sz :> N) <? sizenn (numtype_Inn I))%BN -> wf_loadop_Inn I (mk_loadop_Inn sz sx).
Proof. move=> H1 H2. apply: (loadop_Inn_case_0 _ _ _ (sizenn (numtype_Inn I))) => //. exact/fun_sizenn_eq. Qed.

(* The default values of the locals of a call. *)
Lemma Forall2_default_eq (vl : seq (option val)) (tl : seq valtype) :
	List.Forall2 (fun v t => fun_default_ t v) vl tl -> vl = map default_ tl.
Proof. elim => //= v t vl' tl' /fun_default__inv -> _ ->. by []. Qed.

Lemma map_the_default (tl : seq valtype) :
	map (fun v : option val => !(v)) (map default_ tl) = map (fun t => !(default_ t)) tl.
Proof. by rewrite -map_comp. Qed.

(** * Tactics *)

(* The default values of the locals of a call, as [map default_]. *)
Ltac inv_defaults :=
	repeat match goal with
	| H : List.Forall2 (fun _ _ => fun_default_ _ _) ?vl _ |- _ =>
		move/Forall2_default_eq: H => H; subst vl
	end;
	repeat match goal with
	| H : is_true (size (map default_ ?tl) == size ?tl) |- _ => clear H
	| H : List.Forall (fun _ => is_true (_ != None)) (map default_ _) |- _ =>
		move/List.Forall_map: H => H
	end;
	repeat match goal with H : context [map (fun _ => !(_)) (map default_ _)] |- _ =>
		rewrite map_the_default in H end.

(* Turn the size relations into equations with the total functions above.
   (Plain [apply ... in], not ssreflect views: the views of an [Ltac] are only
   found where wasm_funs is imported, while this one is also used through a
   module alias.) *)
Ltac inv_size_rels :=
	repeat match goal with
	| H : fun_sizenn _ _ |- _ => apply fun_sizenn_eq in H; subst
	| H : fun_sizenn1 _ _ |- _ => apply fun_sizenn1_eq in H; subst
	| H : fun_sizenn2 _ _ |- _ => apply fun_sizenn2_eq in H; subst
	| H : fun_isize _ _ |- _ => apply fun_isize_eq in H; subst
	| H : fun_fsize _ _ |- _ => apply fun_fsize_eq in H; subst
	| H : fun_lsize _ _ |- _ => apply fun_lsize_eq in H; subst
	| H : fun_jsize _ _ |- _ => apply fun_jsize_eq in H; subst
	| H : fun_lsizenn _ _ |- _ => apply fun_lsizenn_eq in H; subst
	| H : fun_lsizenn1 _ _ |- _ => apply fun_lsizenn1_eq in H; subst
	| H : fun_lsizenn2 _ _ |- _ => apply fun_lsizenn2_eq in H; subst
	| H : fun_shsize _ _ |- _ => apply fun_shsize_eq in H; subst
	end.

(* The same for the float parameters, zero and default values and the
   bitwise vector operations. *)
Ltac inv_other_rels :=
	match goal with
	| H : fun_M _ _ |- _ => case/fun_M_inv: H => H ?; subst
	| H : fun_E _ _ |- _ => case/fun_E_inv: H => H ?; subst
	| H : fun_canon_ _ _ |- _ => case/fun_canon__inv: H => H ?; subst
	| H : fun_fzero _ _ |- _ => case/fun_fzero_inv: H => H ?; subst
	| H : fun_zero _ _ |- _ => move/fun_zero_inv: H => H; subst
	| H : fun_default_ _ _ |- _ => move/fun_default__inv: H => H; subst
	| H : fun_vvunop_ _ _ _ _ |- _ => move/fun_vvunop__eq: H => H; subst
	| H : fun_vvbinop_ _ _ _ _ _ |- _ => move/fun_vvbinop__eq: H => H; subst
	| H : fun_vvternop_ _ _ _ _ _ _ |- _ => move/fun_vvternop__eq: H => H; subst
	end.

Ltac inv_sizes := repeat (progress inv_size_rels || inv_other_rels).

(* The same for the state accessors and updates, keeping their side
   conditions. *)
Ltac inv_state :=
	repeat match goal with
	| H : fun_type _ _ _ |- _ => case/fun_type_inv: H => H ?; subst
	| H : fun_func _ _ _ |- _ => case/fun_func_inv: H => H [? ?]; subst
	| H : fun_global _ _ _ |- _ => case/fun_global_inv: H => H [? ?]; subst
	| H : fun_table _ _ _ |- _ => case/fun_table_inv: H => H [? ?]; subst
	| H : fun_mem _ _ _ |- _ => case/fun_mem_inv: H => H [? ?]; subst
	| H : fun_elem _ _ _ |- _ => case/fun_elem_inv: H => H [? ?]; subst
	| H : fun_data _ _ _ |- _ => case/fun_data_inv: H => H [? ?]; subst
	| H : fun_local _ _ _ |- _ => case/fun_local_inv: H => H ?; subst
	| H : fun_blocktype _ _ _ |- _ => move/fun_blocktype_inv: H => H; subst
	| H : fun_with_global _ _ _ _ |- _ => case/fun_with_global_inv: H => H ?; subst
	| H : fun_with_table _ _ _ _ _ |- _ => case/fun_with_table_inv: H => H ?; subst
	| H : fun_with_tableinst _ _ _ _ |- _ => case/fun_with_tableinst_inv: H => H ?; subst
	| H : fun_with_mem _ _ _ _ _ _ |- _ => case/fun_with_mem_inv: H => H ?; subst
	| H : fun_with_meminst _ _ _ _ |- _ => case/fun_with_meminst_inv: H => H ?; subst
	| H : fun_with_elem _ _ _ _ |- _ => case/fun_with_elem_inv: H => H ?; subst
	| H : fun_with_data _ _ _ _ |- _ => case/fun_with_data_inv: H => H ?; subst
	| H : fun_instexport _ _ _ _ _ _ |- _ => move/fun_instexport_inv: H => H; subst
	end.

(* [STORE] and [VNARROW] with their old premises. *)
Lemma store_wf_args Inn_opt nt (sz_opt : option sz) :
	List.Forall2 (fun (I : Inn) (v : sz) => (nt == numtype_Inn I) && ((v :> N) <? sizenn (numtype_Inn I))%BN)
		(option_to_list Inn_opt) (option_to_list sz_opt) ->
	List.Forall2 (fun (v : N) (I : Inn) => fun_sizenn (numtype_Inn I) v)
		(option_to_list (option_map (fun I => sizenn (numtype_Inn I)) Inn_opt)) (option_to_list Inn_opt) /\
	List_Forall3 (fun (v : N) (I : Inn) (s : sz) => (nt == numtype_Inn I) && ((s :> N) <? v)%BN)
		(option_to_list (option_map (fun I => sizenn (numtype_Inn I)) Inn_opt)) (option_to_list Inn_opt) (option_to_list sz_opt).
Proof.
	case: Inn_opt => [I| ]; case: sz_opt => [s| ] /= H; inversion H; subst; split.
	1: (constructor; [exact/fun_sizenn_eq | constructor]).
	1: (constructor; [assumption | constructor]).
	all: constructor.
Qed.

Lemma instr_case_56' Inn_opt nt sz_opt ma :
	List.Forall (fun v => wf_sz v) (option_to_list sz_opt) -> wf_memarg ma ->
	((Inn_opt == None) <-> (sz_opt == None)) ->
	List.Forall2 (fun (I : Inn) (v : sz) => (nt == numtype_Inn I) && ((v :> N) <? sizenn (numtype_Inn I))%BN)
		(option_to_list Inn_opt) (option_to_list sz_opt) ->
	wf_instr (STORE nt sz_opt ma).
Proof.
	move=> H1 H2 H3 /store_wf_args [H4 H5].
	exact: (instr_case_56 Inn_opt nt sz_opt ma _ H4 H1 H2 H3 H5).
Qed.

Lemma admininstr_case_56' Inn_opt nt sz_opt ma :
	List.Forall (fun v => wf_sz v) (option_to_list sz_opt) -> wf_memarg ma ->
	((Inn_opt == None) <-> (sz_opt == None)) ->
	List.Forall2 (fun (I : Inn) (v : sz) => (nt == numtype_Inn I) && ((v :> N) <? sizenn (numtype_Inn I))%BN)
		(option_to_list Inn_opt) (option_to_list sz_opt) ->
	wf_admininstr (admininstr_STORE nt sz_opt ma).
Proof.
	move=> H1 H2 H3 /store_wf_args [H4 H5].
	exact: (admininstr_case_56 Inn_opt nt sz_opt ma _ H4 H1 H2 H3 H5).
Qed.

Lemma instr_case_37' sh1 sh2 sx :
	wf_ishape sh1 -> wf_ishape sh2 ->
	((lsize (fun_lanetype (sh2 :> shape))) == (2%N * (lsize (fun_lanetype (sh1 :> shape))))%BN) &&
		((2%N * (lsize (fun_lanetype (sh1 :> shape))))%BN <=? 32%N)%BN ->
	wf_instr (VNARROW sh1 sh2 sx).
Proof. move=> H1 H2 H3. apply: (instr_case_37 _ _ _ _ _ _ _ H1 H2 H3); exact/fun_lsize_eq. Qed.

Lemma admininstr_case_37' sh1 sh2 sx :
	wf_ishape sh1 -> wf_ishape sh2 ->
	((lsize (fun_lanetype (sh2 :> shape))) == (2%N * (lsize (fun_lanetype (sh1 :> shape))))%BN) &&
		((2%N * (lsize (fun_lanetype (sh1 :> shape))))%BN <=? 32%N)%BN ->
	wf_admininstr (admininstr_VNARROW sh1 sh2 sx).
Proof. move=> H1 H2 H3. apply: (admininstr_case_37 _ _ _ _ _ _ _ H1 H2 H3); exact/fun_lsize_eq. Qed.

