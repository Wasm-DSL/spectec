theory Wf_preservation
(* Imported Lemma Formulation, Proofs Added Manually *)
	imports isabelle_reference_output_wasm2
begin


(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.6-68.12 *)
lemma fzero_is_wf :
	"(ret_val = (fzero v_N)) \<Longrightarrow>
	 (wf_fN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:281.6-281.11 *)
lemma zero_is_wf :
	"(ret_val = (fun_zero v_numtype)) \<Longrightarrow>
	 (wf_num_underscore v_numtype ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.6-342.10 *)
lemma dim_is_wf :
	"(wf_shape v_shape) \<Longrightarrow>
	 (ret_val = (fun_dim v_shape)) \<Longrightarrow>
	 (wf_dim ret_val)"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
lemma concat_bytes_is_wf :
	"(fun_concat_bytes var_0_lst_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0_lst :: (byte list)). list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst) var_0_lst_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
lemma tablesxt_is_wf :
	"(fun_tablesxt var_0_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: externtype). (wf_externtype var_0)) var_0_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: tabletype). (wf_tabletype ret_val)) ret_val_lst"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
lemma memsxt_is_wf :
	"(fun_memsxt var_0_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: externtype). (wf_externtype var_0)) var_0_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: memtype). (wf_memtype ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.6-80.20 *)
lemma dataidx_instr_is_wf :
	"(wf_instr v_instr) \<Longrightarrow>
	 (ret_val_lst = (dataidx_instr v_instr)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
lemma dataidx_instrs_is_wf :
	"(fun_dataidx_instrs var_0_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: instr). (wf_instr var_0)) var_0_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
lemma dataidx_expr_is_wf :
	"(fun_dataidx_expr v_expr var_0) \<Longrightarrow>
	 list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
lemma dataidx_func_is_wf :
	"(fun_dataidx_func v_func var_0) \<Longrightarrow>
	 (wf_func v_func) \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
lemma dataidx_funcs_is_wf :
	"(fun_dataidx_funcs var_0_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: func). (wf_func var_0)) var_0_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.6-106.13 *)
lemma memarg0_is_wf :
	"(ret_val = (memarg0 )) \<Longrightarrow>
	 (wf_memarg ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 *)
lemma unop__is_wf :
	"(wf_unop_underscore v_numtype v_unop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 ((fun_unop_underscore v_numtype v_unop_underscore v_num_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the ((fun_unop_underscore v_numtype v_unop_underscore v_num_underscore)))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: num_underscore). (wf_num_underscore v_numtype ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.6-105.12 *)
lemma iadd__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (iadd_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.6-107.12 *)
lemma imul__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (imul_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
lemma irem__is_wf :
	"(fun_irem_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val_opt = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.6-106.12 *)
lemma isub__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (isub_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.6-123.12 *)
lemma ieqz__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (ieqz_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 *)
lemma testop__is_wf :
	"(wf_testop_underscore v_numtype v_testop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 ((fun_testop_underscore v_numtype v_testop_underscore v_num_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((fun_testop_underscore v_numtype v_testop_underscore v_num_underscore)))) \<Longrightarrow>
	 (wf_num_underscore I32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.6-125.11 *)
lemma ieq__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (ieq_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
lemma ige__is_wf :
	"(fun_ige_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
lemma igt__is_wf :
	"(fun_igt_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
lemma ile__is_wf :
	"(fun_ile_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
lemma ilt__is_wf :
	"(fun_ilt_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.6-126.11 *)
lemma ine__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (ine_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
lemma relop__is_wf :
	"(fun_relop_underscore v_numtype v_relop_underscore v_num_underscore num__0 var_0) \<Longrightarrow>
	 (wf_relop_underscore v_numtype v_relop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype num__0) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_num_underscore I32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
lemma cvtop___is_wf :
	"(fun_cvtop__underscore numtype_1 numtype_2 v_cvtop__underscore v_num_underscore var_0) \<Longrightarrow>
	 (wf_cvtop__underscore numtype_1 numtype_2 v_cvtop__underscore) \<Longrightarrow>
	 (wf_num_underscore numtype_1 v_num_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the (var_0))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: num_underscore). (wf_num_underscore numtype_2 ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.6-124.12 *)
lemma inez__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (inez_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.6-133.12 *)
lemma ineg__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (ineg_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
lemma iabs__is_wf :
	"(fun_iabs_underscore v_N v_iN var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
lemma imin__is_wf :
	"(fun_imin_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
lemma imax__is_wf :
	"(fun_imax_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
lemma iadd_sat__is_wf :
	"(fun_iadd_sat_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
lemma isub_sat__is_wf :
	"(fun_isub_sat_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.6-323.15 *)
lemma packnum__is_wf :
	"(wf_num_underscore (unpack v_lanetype) v_num_underscore) \<Longrightarrow>
	 ((packnum_underscore v_lanetype v_num_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((packnum_underscore v_lanetype v_num_underscore)))) \<Longrightarrow>
	 (wf_lane_underscore v_lanetype ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:329.6-329.17 *)
lemma unpacknum__is_wf :
	"(wf_lane_underscore v_lanetype v_lane_underscore) \<Longrightarrow>
	 ((unpacknum_underscore v_lanetype v_lane_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((unpacknum_underscore v_lanetype v_lane_underscore)))) \<Longrightarrow>
	 (wf_num_underscore (unpack v_lanetype) ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.6-364.14 *)
lemma vvunop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (ret_val = (vvunop_underscore v_vectype v_vvunop v_vec_underscore)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.6-366.15 *)
lemma vvbinop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__0) \<Longrightarrow>
	 (ret_val = (vvbinop_underscore v_vectype v_vvbinop v_vec_underscore vec__0)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:368.6-368.16 *)
lemma vvternop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__0) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__1) \<Longrightarrow>
	 (ret_val = (vvternop_underscore v_vectype v_vvternop v_vec_underscore vec__0 vec__1)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.13 *)
lemma vunop__is_wf :
	"(fun_vunop_underscore v_shape v_vunop_underscore v_vec_underscore var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vunop_underscore v_shape v_vunop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the (var_0))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: vec_underscore). (wf_uN 128 ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
lemma vbinop__is_wf :
	"(fun_vbinop_underscore v_shape v_vbinop_underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vbinop_underscore v_shape v_vbinop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the (var_0))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: vec_underscore). (wf_uN 128 ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.14 *)
lemma vrelop__is_wf :
	"(fun_vrelop_underscore v_shape v_vrelop_underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vrelop_underscore v_shape v_vrelop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:385.6-385.15 *)
lemma lcvtop___is_wf :
	"(fun_lcvtop__underscore shape_1 shape_2 v_vcvtop__underscore v_lane_underscore var_0) \<Longrightarrow>
	 (wf_shape shape_1) \<Longrightarrow>
	 (wf_shape shape_2) \<Longrightarrow>
	 (wf_vcvtop__underscore shape_1 shape_2 v_vcvtop__underscore) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype shape_1) v_lane_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the (var_0))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: lane_underscore). (wf_lane_underscore (fun_lanetype shape_2) ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:387.6-387.15 *)
lemma vcvtop___is_wf :
	"(fun_vcvtop__underscore shape_1 shape_2 v_vcvtop__underscore v_vec_underscore var_0) \<Longrightarrow>
	 (wf_shape shape_1) \<Longrightarrow>
	 (wf_shape shape_2) \<Longrightarrow>
	 (wf_vcvtop__underscore shape_1 shape_2 v_vcvtop__underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:603.6-603.17 *)
lemma vextunop___is_wf :
	"(fun_vextunop__underscore ishape_1 ishape_2 v_vextunop__underscore v_vec_underscore var_0) \<Longrightarrow>
	 (wf_ishape ishape_1) \<Longrightarrow>
	 (wf_ishape ishape_2) \<Longrightarrow>
	 (wf_vextunop__underscore ishape_1 ishape_2 v_vextunop__underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:605.6-605.18 *)
lemma vextbinop___is_wf :
	"(fun_vextbinop__underscore ishape_1 ishape_2 v_vextbinop__underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_ishape ishape_1) \<Longrightarrow>
	 (wf_ishape ishape_2) \<Longrightarrow>
	 (wf_vextbinop__underscore ishape_1 ishape_2 v_vextbinop__underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:628.6-628.16 *)
lemma vshiftop__is_wf :
	"(fun_vshiftop_underscore v_ishape v_vshiftop_underscore v_lane_underscore v_u32 var_0) \<Longrightarrow>
	 (wf_ishape v_ishape) \<Longrightarrow>
	 (wf_vshiftop_underscore v_ishape v_vshiftop_underscore) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype (proj_ishape_0 v_ishape)) v_lane_underscore) \<Longrightarrow>
	 (wf_uN 32 v_u32) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype (proj_ishape_0 v_ishape)) ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.6-7.15 *)
lemma default__is_wf :
	"((default_underscore v_valtype) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((default_underscore v_valtype)))) \<Longrightarrow>
	 (wf_val ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.6-48.12 *)
lemma store_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_store v_state)) \<Longrightarrow>
	 (wf_store ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.6-49.12 *)
lemma frame_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_frame v_state)) \<Longrightarrow>
	 (wf_frame ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.6-58.15 *)
lemma funcinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_funcinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: funcinst). (wf_funcinst ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.6-59.17 *)
lemma globalinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_globalinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: globalinst). (wf_globalinst ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.6-60.16 *)
lemma tableinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_tableinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: tableinst). (wf_tableinst ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.6-61.14 *)
lemma meminst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_meminst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: meminst). (wf_meminst ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.6-63.15 *)
lemma datainst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_datainst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: datainst). (wf_datainst ret_val)) ret_val_lst"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.6-64.17 *)
lemma moduleinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_moduleinst v_state)) \<Longrightarrow>
	 (wf_moduleinst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.6-75.11 *)
lemma func_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_funcidx) \<Longrightarrow>
	 (ret_val = (fun_func v_state v_funcidx)) \<Longrightarrow>
	 (wf_funcinst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.6-76.13 *)
lemma global_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_globalidx) \<Longrightarrow>
	 (ret_val = (fun_global v_state v_globalidx)) \<Longrightarrow>
	 (wf_globalinst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.6-77.12 *)
lemma table_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_tableidx) \<Longrightarrow>
	 (ret_val = (fun_table v_state v_tableidx)) \<Longrightarrow>
	 (wf_tableinst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.6-78.10 *)
lemma mem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 (ret_val = (fun_mem v_state v_memidx)) \<Longrightarrow>
	 (wf_meminst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.6-80.11 *)
lemma data_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_dataidx) \<Longrightarrow>
	 (ret_val = (fun_data v_state v_dataidx)) \<Longrightarrow>
	 (wf_datainst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.6-81.12 *)
lemma local_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_localidx) \<Longrightarrow>
	 (ret_val = (fun_local v_state v_localidx)) \<Longrightarrow>
	 (wf_val ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.6-95.17 *)
lemma with_local_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_localidx) \<Longrightarrow>
	 (wf_val v_val) \<Longrightarrow>
	 (ret_val = (with_local v_state v_localidx v_val)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.6-96.18 *)
lemma with_global_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_globalidx) \<Longrightarrow>
	 (wf_val v_val) \<Longrightarrow>
	 (ret_val = (with_global v_state v_globalidx v_val)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.6-97.17 *)
lemma with_table_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_tableidx) \<Longrightarrow>
	 (ret_val = (with_table v_state v_tableidx res_nat v_ref)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.6-98.21 *)
lemma with_tableinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_tableidx) \<Longrightarrow>
	 (wf_tableinst v_tableinst) \<Longrightarrow>
	 (ret_val = (with_tableinst v_state v_tableidx v_tableinst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.6-99.15 *)
lemma with_mem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (with_mem v_state v_memidx res_nat nat_0 var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.6-100.19 *)
lemma with_meminst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 (wf_meminst v_meminst) \<Longrightarrow>
	 (ret_val = (with_meminst v_state v_memidx v_meminst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.6-101.16 *)
lemma with_elem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_elemidx) \<Longrightarrow>
	 (ret_val = (with_elem v_state v_elemidx var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.6-102.16 *)
lemma with_data_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_dataidx) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (with_data v_state v_dataidx var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
lemma growtable_is_wf :
	"(fun_growtable v_tableinst res_nat v_ref var_0) \<Longrightarrow>
	 (wf_tableinst v_tableinst) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_tableinst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
lemma growmemory_is_wf :
	"(fun_growmemory v_meminst res_nat var_0) \<Longrightarrow>
	 (wf_meminst v_meminst) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_meminst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.10-6.19 *)
lemma Step_pure_is_wf :
	"list_all (\<lambda> (var_0 :: admininstr). (wf_admininstr var_0)) var_0 \<Longrightarrow>
	 (Step_pure var_0 var_1) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: admininstr). (wf_admininstr var_1)) var_1"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 *)
lemma Step_read_is_wf :
	"(wf_config (mk_config (mk_state s f) es)) \<Longrightarrow>
   Store_ok s \<Longrightarrow>
	 (Step_read (mk_config (mk_state s f) es) var_1) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: admininstr). (wf_admininstr var_1)) var_1"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 *)
lemma Step_is_wf :
	"(wf_config (mk_config (mk_state s f) es)) \<Longrightarrow>
    Store_ok s \<Longrightarrow>
	 (Step (mk_config (mk_state s f) es) var_1) \<Longrightarrow>
	 (wf_config var_1)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 *)
lemma allocfunc_is_wf :
	"(fun_allocfunc v_store v_moduleinst v_func var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_moduleinst v_moduleinst) \<Longrightarrow>
	 (wf_func v_func) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
lemma allocfuncs_is_wf :
	"(fun_allocfuncs v_store v_moduleinst var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_moduleinst v_moduleinst) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: func). (wf_func var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
lemma allocglobal_is_wf :
	"(fun_allocglobal v_store v_globaltype v_val var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_val v_val) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
lemma allocglobals_is_wf :
	"(fun_allocglobals v_store var_0_lst var_1_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: val). (wf_val var_1)) var_1_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
lemma alloctable_is_wf :
	"(fun_alloctable v_store v_tabletype var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_tabletype v_tabletype) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
lemma alloctables_is_wf :
	"(fun_alloctables v_store var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: tabletype). (wf_tabletype var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
lemma allocmem_is_wf :
	"(fun_allocmem v_store v_memtype var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_memtype v_memtype) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
lemma allocmems_is_wf :
	"(fun_allocmems v_store var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: memtype). (wf_memtype var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
lemma allocelem_is_wf :
	"(fun_allocelem v_store v_reftype var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
lemma allocelems_is_wf :
	"(fun_allocelems v_store var_0_lst var_1_lst_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
lemma allocdata_is_wf :
	"(fun_allocdata v_store var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
lemma allocdatas_is_wf :
	"(fun_allocdatas v_store var_0_lst_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0_lst :: (byte list)). list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst) var_0_lst_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:100.6-100.17 *)
lemma instexport_is_wf :
	"(wf_export v_export) \<Longrightarrow>
	 (ret_val = (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export)) \<Longrightarrow>
	 (wf_exportinst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
lemma allocmodule_is_wf :
	"(fun_allocmodule v_store v_module var_0_lst var_1_lst var_2_lst_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_module v_module) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: val). (wf_val var_1)) var_1_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val)) \<Longrightarrow>
	 (wf_moduleinst (snd ret_val))"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
lemma invoke_is_wf :
	"(fun_invoke v_store v_funcaddr var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: val). (wf_val var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_config ret_val)"
sorry


end