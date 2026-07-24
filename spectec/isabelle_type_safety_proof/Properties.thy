theory Properties
	imports Main isabelle_reference_output_wasm2

begin

lemma func_extension_refl:
 shows "wf_funcinst g \<Longrightarrow> Extend_funcinst g g"
  apply (induction rule: wf_funcinst.induct)
  by (simp add: funcinst_case_underscore mk_Extend_funcinst)

lemma global_extension_refl:
  shows "wf_globalinst g \<Longrightarrow> Extend_globalinst g g"
  apply (induction rule: wf_globalinst.induct)
  by (metis globalinst_case_underscore globaltype.exhaust
      mk_Extend_globalinst)

lemma mem_extension_refl:
assumes "wf_meminst m"
shows "Extend_meminst m m"
proof -
obtain min maxOpt bs where m_is:"m = \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) maxOpt), BYTES = bs\<rparr>"
  by (metis meminst.cases memtype.exhaust limits.exhaust uN.exhaust)
have "Extend_meminst \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) maxOpt), BYTES = bs\<rparr> \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) maxOpt), BYTES = bs\<rparr>"
  proof (cases maxOpt)
    case (Some maxSize)
      then obtain max where "maxSize = mk_uN max" by (cases maxSize)
      moreover have "wf_meminst \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) maxOpt), BYTES = bs\<rparr>"
        using assms m_is by simp
      ultimately show ?thesis using Some Extend_meminst.intros[of "min" "min" "bs" "bs" "Some max"]
        by simp
  next
    case None
      have "wf_meminst \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) (map_option mk_uN None)), BYTES = bs\<rparr>"
        using None assms m_is by auto
      then show ?thesis using Extend_meminst.intros[of "min" "min" "bs" "bs" "None"] None
        by simp
  qed
  then show ?thesis using m_is by simp
qed

lemma tab_extension_refl:
  assumes "wf_tableinst m"
  shows   "Extend_tableinst m m"
proof -
obtain min maxOpt ref_t ref_lst where m_is: "m = \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) maxOpt) ref_t), REFS = ref_lst \<rparr>"
  by (metis limits.exhaust tableinst.cases tabletype.exhaust uN.exhaust)
have "Extend_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) maxOpt) ref_t), REFS = ref_lst \<rparr> \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) maxOpt) ref_t), REFS = ref_lst \<rparr>"
  proof (cases maxOpt)
    case (Some maxSize)
      then obtain max where "maxSize = mk_uN max" by (cases maxSize)
      moreover have "wf_tableinst \<lparr>tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) maxOpt) ref_t), REFS = ref_lst \<rparr>"
        using assms m_is by auto
      ultimately show ?thesis using Extend_tableinst.intros[of "min" "min" "ref_lst" "ref_lst" "Some max" "ref_t"]
        using Some by simp
  next
    case None
      have "wf_tableinst \<lparr>tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) None) ref_t), REFS = ref_lst \<rparr>"
        using None assms m_is by auto
      then show ?thesis using Extend_tableinst.intros[of "min" "min" "ref_lst" "ref_lst" "None"] None
        by simp
  qed
  then show ?thesis using m_is by simp
qed

lemma elem_extension_refl:
  shows "Extend_eleminst el el"
  by (metis Extend_eleminst.simps eleminst.cases)

lemma data_extension_refl:
  shows "wf_datainst d \<Longrightarrow> Extend_datainst d d"
  by (metis Extend_datainst.simps datainst.cases)

lemma store_extension_refl:
  assumes "wf_store s"
  shows   "Extend_store s s"
  using assms func_extension_refl global_extension_refl mem_extension_refl tab_extension_refl elem_extension_refl data_extension_refl
  apply(simp add: Extend_store.simps)
  apply(induction rule: wf_store.induct)
  unfolding holds_upto_def
  apply simp+
  by (metis list_all_length)

(*Store extension reduction*)
lemma reduce_store_extension:
  assumes "Step (mk_config (mk_state s f) admininstr_lst) (mk_config (mk_state s' f') admininstr'_lst)"
          "Store_ok s"
          "Moduleinst_ok s module_inst C"
          "Instrs_ok2 s C admininstr_lst (mk_functype t_1_lst t_2_lst)"
          "C = Ci\<lparr>context_LOCALS := (map typeofval (LOCALS f)), LABELS := lbl, context_RETURN := rtn\<rparr>"
  shows "Extend_store s s' \<and> Store_ok s'"
  using assms
  proof (induction "(mk_config (mk_state s f) admininstr_lst)" "(mk_config (mk_state s' f') admininstr'_lst)" arbitrary: admininstr_lst admininstr'_lst rule: Step.induct)
  case (pure admininstr_lst admininstr'_lst)
    have "wf_store s"
      using Instrs_ok2.simps pure.prems(3) by blast
    then show ?case using store_extension_refl pure(2,4)
      by blast
  next
    case (read admininstr_lst admininstr'_lst)
    then show ?case sorry
  next
    case (ctxt_label admininstr_lst admininstr'_lst v_n instr_0_lst)
    then show ?case sorry
  next
    case (ctxt_frame f' admininstr_lst f'' admininstr'_lst v_n)
    then show ?case sorry
  next
    case (ctxt_instrs admininstr_lst admininstr'_lst val_lst admininstr_1_lst)
    then show ?case sorry
  next
    case (Step__local_set v_val x)
    then show ?case sorry
  next
    case (Step__global_set v_val x)
    then show ?case sorry
  next
    case (table_set_trap i x v_ref)
    then show ?case sorry
  next
    case (table_set_val i x v_ref)
    then show ?case sorry
  next
    case (table_grow_succeed x v_n v_ref var_0 ti)
    then show ?case sorry
  next
    case (table_grow_fail var_0 v_ref v_n x)
    then show ?case sorry
  next
    case (Step__elem_drop x)
    then show ?case sorry
  next
    case (store_num_trap i nt ao c)
    then show ?case sorry
  next
    case (store_num_val i nt b_lst c ao)
    then show ?case sorry
  next
    case (store_pack_trap i ao v_n v_Inn c)
    then show ?case sorry
  next
    case (store_pack_val i v_Inn c b_lst v_n ao)
    then show ?case sorry
  next
    case (vstore_oob i ao c)
    then show ?case sorry
  next
    case (vstore_val i b_lst c ao)
    then show ?case sorry
  next
    case (vstore_lane_oob i ao v_N c j)
    then show ?case sorry
  next
    case (vstore_lane_val i v_N v_Jnn v_M c j b_lst ao)
    then show ?case sorry
  next
    case (memory_grow_succeed v_n var_0 mi)
    then show ?case sorry
  next
    case (memory_grow_fail var_0 v_n)
    then show ?case sorry
  next
    case (Step__data_drop x)
    then show ?case sorry
  qed

end