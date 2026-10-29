theory Wf_preservation_extra
(* Well-formedness lemmas that the type safety proof does not depend on.
   Nothing imports this theory, so it can be deleted without affecting the proof. *)
	imports Wf_preservation
begin

(* Helper lemmas for the well-formedness proofs below *)

lemma wf_store_iff:
  "wf_store s \<longleftrightarrow> list_all wf_funcinst (store_FUNCS s) \<and> list_all wf_globalinst (store_GLOBALS s)
     \<and> list_all wf_tableinst (store_TABLES s) \<and> list_all wf_meminst (store_MEMS s)
     \<and> list_all wf_datainst (store_DATAS s)"
  by (cases s) (simp add: wf_store.simps)

lemma wf_frame_iff: "wf_frame f \<longleftrightarrow> list_all wf_val (LOCALS f) \<and> wf_moduleinst (frame_MODULE f)"
  by (cases f) (simp add: wf_frame.simps)

lemma wf_globalinst_iff: "wf_globalinst g \<longleftrightarrow> wf_val (VALUE g)"
  by (cases g) (simp add: wf_globalinst.simps)

lemma wf_tableinst_iff: "wf_tableinst t \<longleftrightarrow> wf_tabletype (tableinst_TYPE t)"
  by (cases t) (simp add: wf_tableinst.simps)

lemma wf_meminst_iff: "wf_meminst m \<longleftrightarrow> wf_memtype (meminst_TYPE m) \<and> list_all wf_byte (BYTES m)"
  by (cases m) (simp add: wf_meminst.simps)

lemma wf_datainst_iff: "wf_datainst d \<longleftrightarrow> list_all wf_byte (datainst_BYTES d)"
  by (cases d) (simp add: wf_datainst.simps)

lemmas wf_inst_iffs = wf_globalinst_iff wf_tableinst_iff wf_meminst_iff wf_datainst_iff

lemma wf_exportinst_iff: "wf_exportinst e \<longleftrightarrow> wf_name (NAME e)"
  by (cases e) (simp add: wf_exportinst.simps)

lemma list_all_list_slice_update:
  "list_all P l \<Longrightarrow> list_all P ul \<Longrightarrow> list_all P (list_slice_update l i j ul)"
  by (induction l i j ul rule: list_slice_update.induct) auto

lemma list_all_list_update_func_pres:
  "list_all P xs \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P (g x)) \<Longrightarrow> list_all P (list_update_func xs i g)"
  by (rule list_all_list_update_func_gen) (auto simp: list_all_length)

lemma dataidx_instr_dom: "dataidx_instr_dom e"
  by (rule accpI) (erule dataidx_instr_rel.cases)

lemma dataidx_instr_set:
  "x \<in> set (dataidx_instr e) \<Longrightarrow> e = instr_sc7 (MEMORY_INIT x) \<or> e = instr_sc7 (DATA_DROP x)"
  by (induction e rule: dataidx_instr.pinduct[OF dataidx_instr_dom])
     (auto simp: dataidx_instr.psimps dataidx_instr_dom)

inductive_cases wf_instr_MEMORY_INIT_E: "wf_instr (instr_sc7 (MEMORY_INIT x))"
inductive_cases wf_instr_DATA_DROP_E: "wf_instr (instr_sc7 (DATA_DROP x))"

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.6-68.12 *)
lemma fzero_is_wf :
	"(ret_val = (fzero v_N)) \<Longrightarrow>
	 (wf_fN v_N ret_val)"
  using wf_fN_fzero by simp

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.6-342.10 *)
lemma dim_is_wf :
	"(wf_shape v_shape) \<Longrightarrow>
	 (ret_val = (fun_dim v_shape)) \<Longrightarrow>
	 (wf_dim ret_val)"
  by (auto elim!: wf_shape.cases wf_dim.cases simp: fun_dim.psimps fun_dim.domintros wf_dim.simps)

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
lemma concat_bytes_is_wf :
	"(fun_concat_bytes var_0_lst_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0_lst :: (byte list)). list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst) var_0_lst_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
  by (induction var_0_lst_lst var_0 arbitrary: ret_val_lst rule: fun_concat_bytes.induct) auto

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
lemma tablesxt_is_wf :
	"(fun_tablesxt var_0_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: externtype). (wf_externtype var_0)) var_0_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: tabletype). (wf_tabletype ret_val)) ret_val_lst"
  by (induction var_0_lst var_0 arbitrary: ret_val_lst rule: fun_tablesxt.induct)
     (auto simp: wf_externtype.simps)

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
lemma memsxt_is_wf :
	"(fun_memsxt var_0_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: externtype). (wf_externtype var_0)) var_0_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: memtype). (wf_memtype ret_val)) ret_val_lst"
  by (induction var_0_lst var_0 arbitrary: ret_val_lst rule: fun_memsxt.induct)
     (auto simp: wf_externtype.simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.6-80.20 *)
lemma dataidx_instr_is_wf :
	"(wf_instr v_instr) \<Longrightarrow>
	 (ret_val_lst = (dataidx_instr v_instr)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
  by (auto simp: list_all_iff dest!: dataidx_instr_set elim: wf_instr_MEMORY_INIT_E wf_instr_DATA_DROP_E)

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
lemma dataidx_instrs_is_wf :
	"(fun_dataidx_instrs var_0_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: instr). (wf_instr var_0)) var_0_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
  by (induction var_0_lst var_0 arbitrary: ret_val_lst rule: fun_dataidx_instrs.induct)
     (auto simp: dataidx_instr_is_wf[OF _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
lemma dataidx_expr_is_wf :
	"(fun_dataidx_expr v_expr var_0) \<Longrightarrow>
	 list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
  by (auto elim!: fun_dataidx_expr.cases intro!: dataidx_instrs_is_wf[OF _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
lemma dataidx_func_is_wf :
	"(fun_dataidx_func v_func var_0) \<Longrightarrow>
	 (wf_func v_func) \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
  by (auto elim!: fun_dataidx_func.cases wf_func.cases intro!: dataidx_expr_is_wf[OF _ _ HOL.refl])

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
lemma dataidx_funcs_is_wf :
	"(fun_dataidx_funcs var_0_lst var_0) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: func). (wf_func var_0)) var_0_lst \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
  by (induction var_0_lst var_0 arbitrary: ret_val_lst rule: fun_dataidx_funcs.induct)
     (auto simp: dataidx_func_is_wf[OF _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.6-106.13 *)
lemma memarg0_is_wf :
	"(ret_val = (memarg0 )) \<Longrightarrow>
	 (wf_memarg ret_val)"
  unfolding memarg0_def by (auto intro!: wf_memarg.intros simp: wf_uN_iff)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.6-123.12 *)
lemma ieqz__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (ieqz_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
  by (simp add: ieqz_underscore.psimps ieqz_underscore.domintros wf_uN_res_bool)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.6-125.11 *)
lemma ieq__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (ieq_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
  by (simp add: ieq_underscore.psimps ieq_underscore.domintros wf_uN_res_bool)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
lemma ige__is_wf :
	"(fun_ige_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
  by (auto elim!: fun_ige_underscore.cases simp: wf_uN_res_bool)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
lemma igt__is_wf :
	"(fun_igt_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
  by (auto elim!: fun_igt_underscore.cases simp: wf_uN_res_bool)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
lemma ile__is_wf :
	"(fun_ile_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
  by (auto elim!: fun_ile_underscore.cases simp: wf_uN_res_bool)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
lemma ilt__is_wf :
	"(fun_ilt_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
  by (auto elim!: fun_ilt_underscore.cases simp: wf_uN_res_bool)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.6-126.11 *)
lemma ine__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (ine_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
  by (simp add: ine_underscore.psimps ine_underscore.domintros wf_uN_res_bool)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.6-124.12 *)
lemma inez__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (inez_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
  by (simp add: inez_underscore.psimps inez_underscore.domintros wf_uN_res_bool)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.6-48.12 *)
lemma store_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_store v_state)) \<Longrightarrow>
	 (wf_store ret_val)"
  by (cases v_state) (simp add: fun_store.psimps fun_store.domintros wf_state.simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.6-49.12 *)
lemma frame_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_frame v_state)) \<Longrightarrow>
	 (wf_frame ret_val)"
  by (cases v_state) (simp add: fun_frame.psimps fun_frame.domintros wf_state.simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.6-58.15 *)
lemma funcinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_funcinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: funcinst). (wf_funcinst ret_val)) ret_val_lst"
  by (cases v_state) (simp add: fun_funcinst.psimps fun_funcinst.domintros wf_state.simps wf_store_iff)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.6-59.17 *)
lemma globalinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_globalinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: globalinst). (wf_globalinst ret_val)) ret_val_lst"
  by (cases v_state) (simp add: fun_globalinst.psimps fun_globalinst.domintros wf_state.simps wf_store_iff)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.6-60.16 *)
lemma tableinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_tableinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: tableinst). (wf_tableinst ret_val)) ret_val_lst"
  by (cases v_state) (simp add: fun_tableinst.psimps fun_tableinst.domintros wf_state.simps wf_store_iff)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.6-61.14 *)
lemma meminst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_meminst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: meminst). (wf_meminst ret_val)) ret_val_lst"
  by (cases v_state) (simp add: fun_meminst.psimps fun_meminst.domintros wf_state.simps wf_store_iff)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.6-63.15 *)
lemma datainst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_datainst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: datainst). (wf_datainst ret_val)) ret_val_lst"
  by (cases v_state) (simp add: fun_datainst.psimps fun_datainst.domintros wf_state.simps wf_store_iff)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.6-64.17 *)
lemma moduleinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_moduleinst v_state)) \<Longrightarrow>
	 (wf_moduleinst ret_val)"
  by (cases v_state) (simp add: fun_moduleinst.psimps fun_moduleinst.domintros wf_state.simps wf_frame_iff)

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
  by (cases v_state)
     (auto simp: with_local.psimps with_local.domintros wf_state.simps wf_frame_iff
        intro!: list_all_list_update_func_pres)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.6-96.18 *)
lemma with_global_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_globalidx) \<Longrightarrow>
	 (wf_val v_val) \<Longrightarrow>
	 (ret_val = (with_global v_state v_globalidx v_val)) \<Longrightarrow>
	 (wf_state ret_val)"
  by (cases v_state)
     (auto simp: with_global.psimps with_global.domintros wf_state.simps wf_store_iff wf_inst_iffs
        intro!: list_all_list_update_func_pres)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.6-97.17 *)
lemma with_table_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_tableidx) \<Longrightarrow>
	 (ret_val = (with_table v_state v_tableidx res_nat v_ref)) \<Longrightarrow>
	 (wf_state ret_val)"
  by (cases v_state)
     (auto simp: with_table.psimps with_table.domintros wf_state.simps wf_store_iff wf_inst_iffs
        intro!: list_all_list_update_func_pres)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.6-98.21 *)
lemma with_tableinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_tableidx) \<Longrightarrow>
	 (wf_tableinst v_tableinst) \<Longrightarrow>
	 (ret_val = (with_tableinst v_state v_tableidx v_tableinst)) \<Longrightarrow>
	 (wf_state ret_val)"
  by (cases v_state)
     (auto simp: with_tableinst.psimps with_tableinst.domintros wf_state.simps wf_store_iff wf_inst_iffs
        intro!: list_all_list_update_func_pres)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.6-99.15 *)
lemma with_mem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (with_mem v_state v_memidx res_nat nat_0 var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
  by (cases v_state)
     (auto simp: with_mem.psimps with_mem.domintros wf_state.simps wf_store_iff wf_inst_iffs
        list_all_list_slice_update intro!: list_all_list_update_func_pres)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.6-100.19 *)
lemma with_meminst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 (wf_meminst v_meminst) \<Longrightarrow>
	 (ret_val = (with_meminst v_state v_memidx v_meminst)) \<Longrightarrow>
	 (wf_state ret_val)"
  by (cases v_state)
     (auto simp: with_meminst.psimps with_meminst.domintros wf_state.simps wf_store_iff wf_inst_iffs
        intro!: list_all_list_update_func_pres)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.6-101.16 *)
lemma with_elem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_elemidx) \<Longrightarrow>
	 (ret_val = (with_elem v_state v_elemidx var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
  by (cases v_state) (simp add: with_elem.psimps with_elem.domintros wf_state.simps wf_store_iff wf_inst_iffs)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.6-102.16 *)
lemma with_data_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_dataidx) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (with_data v_state v_dataidx var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
  by (cases v_state)
     (auto simp: with_data.psimps with_data.domintros wf_state.simps wf_store_iff wf_inst_iffs
        intro!: list_all_list_update_func_pres)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
lemma growtable_is_wf :
	"(fun_growtable v_tableinst res_nat v_ref var_0) \<Longrightarrow>
	 (wf_tableinst v_tableinst) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_tableinst ret_val)"
  by (auto elim!: fun_growtable.cases)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
lemma growmemory_is_wf :
	"(fun_growmemory v_meminst res_nat var_0) \<Longrightarrow>
	 (wf_meminst v_meminst) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_meminst ret_val)"
  by (auto elim!: fun_growmemory.cases)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 *)
lemma allocfunc_is_wf :
	"(fun_allocfunc v_store v_moduleinst v_func var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_moduleinst v_moduleinst) \<Longrightarrow>
	 (wf_func v_func) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (auto elim!: fun_allocfunc.cases simp: wf_store_iff)

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
lemma allocfuncs_is_wf :
	"(fun_allocfuncs v_store v_moduleinst var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_moduleinst v_moduleinst) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: func). (wf_func var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (induction v_store v_moduleinst var_0_lst var_0 arbitrary: ret_val rule: fun_allocfuncs.induct)
     (auto dest!: allocfunc_is_wf[OF _ _ _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
lemma allocglobal_is_wf :
	"(fun_allocglobal v_store v_globaltype v_val var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_val v_val) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (auto elim!: fun_allocglobal.cases simp: wf_store_iff)

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
lemma allocglobals_is_wf :
	"(fun_allocglobals v_store var_0_lst var_1_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: val). (wf_val var_1)) var_1_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (induction v_store var_0_lst var_1_lst var_0 arbitrary: ret_val rule: fun_allocglobals.induct)
     (auto dest!: allocglobal_is_wf[OF _ _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
lemma alloctable_is_wf :
	"(fun_alloctable v_store v_tabletype var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_tabletype v_tabletype) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (auto elim!: fun_alloctable.cases simp: wf_store_iff)

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
lemma alloctables_is_wf :
	"(fun_alloctables v_store var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: tabletype). (wf_tabletype var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (induction v_store var_0_lst var_0 arbitrary: ret_val rule: fun_alloctables.induct)
     (auto dest!: alloctable_is_wf[OF _ _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
lemma allocmem_is_wf :
	"(fun_allocmem v_store v_memtype var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_memtype v_memtype) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (auto elim!: fun_allocmem.cases simp: wf_store_iff)

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
lemma allocmems_is_wf :
	"(fun_allocmems v_store var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: memtype). (wf_memtype var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (induction v_store var_0_lst var_0 arbitrary: ret_val rule: fun_allocmems.induct)
     (auto dest!: allocmem_is_wf[OF _ _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
lemma allocelem_is_wf :
	"(fun_allocelem v_store v_reftype var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (auto elim!: fun_allocelem.cases simp: wf_store_iff)

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
lemma allocelems_is_wf :
	"(fun_allocelems v_store var_0_lst var_1_lst_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (induction v_store var_0_lst var_1_lst_lst var_0 arbitrary: ret_val rule: fun_allocelems.induct)
     (auto dest!: allocelem_is_wf[OF _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
lemma allocdata_is_wf :
	"(fun_allocdata v_store var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (auto elim!: fun_allocdata.cases simp: wf_store_iff)

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
lemma allocdatas_is_wf :
	"(fun_allocdatas v_store var_0_lst_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0_lst :: (byte list)). list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst) var_0_lst_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
  by (induction v_store var_0_lst_lst var_0 arbitrary: ret_val rule: fun_allocdatas.induct)
     (auto dest!: allocdata_is_wf[OF _ _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:100.6-100.17 *)
lemma instexport_is_wf :
	"(wf_export v_export) \<Longrightarrow>
	 (ret_val = (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export)) \<Longrightarrow>
	 (wf_exportinst ret_val)"
  by (auto elim!: wf_export.cases simp: wf_exportinst_iff)
     (case_tac v_externidx; simp add: instexport.psimps instexport.domintros)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
lemma allocmodule_is_wf :
	"(fun_allocmodule v_store v_module var_0_lst var_1_lst var_2_lst_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_module v_module) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: val). (wf_val var_1)) var_1_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val)) \<Longrightarrow>
	 (wf_moduleinst (snd ret_val))"
  by (auto elim!: fun_allocmodule.cases)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
lemma invoke_is_wf :
	"(fun_invoke v_store v_funcaddr var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: val). (wf_val var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_config ret_val)"
  by (auto elim!: fun_invoke.cases intro!: wf_config.intros wf_admininstr.intros
      simp: list.pred_map comp_def wf_admininstr_val_iff)

end
