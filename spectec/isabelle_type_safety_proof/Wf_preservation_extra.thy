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

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.6-68.12 *)
lemma fzero_is_wf :
	"(ret_val = (fzero v_N)) \<Longrightarrow>
	 (wf_fN v_N ret_val)"
  using wf_fN_fzero by simp

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

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/9-module.spectec:100.6-100.17 *)
lemma instexport_is_wf :
	"(wf_export v_export) \<Longrightarrow>
	 (ret_val = (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export)) \<Longrightarrow>
	 (wf_exportinst ret_val)"
  by (auto elim!: wf_export.cases simp: wf_exportinst_iff)
     (case_tac v_externidx; simp add: instexport.psimps instexport.domintros)

end
