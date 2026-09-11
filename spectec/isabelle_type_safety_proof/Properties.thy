theory Properties
	imports Main isabelle_reference_output_wasm2 Type_Inversion
          Context_Store_Agreement store_extension_typing
          helper_lemmas
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
lemma store_typing_imp_glob_agree:
assumes "Moduleinst_ok s i C"
        "j < length (context_GLOBALS C)"
shows "(GLOBALS i) ! j < length (store_GLOBALS s) \<and>
       (globalinst_TYPE ((store_GLOBALS s) ! ((GLOBALS i) ! j))) = ((context_GLOBALS C) ! j)"
proof -
  obtain functype_lst funcaddr_lst globaladdr_lst tableaddr_lst memaddr_lst elemaddr_lst dataaddr_lst exportinst_lst functype_F_lst globaltype_lst tabletype_lst memtype_lst elemtype_lst datatype_lst where
  i_eq: "i = \<lparr>
    TYPES   = functype_lst,
    FUNCS   = funcaddr_lst,
    GLOBALS = globaladdr_lst,
    TABLES  = tableaddr_lst,
    MEMS    = memaddr_lst,
    ELEMS   = elemaddr_lst,
    DATAS   = dataaddr_lst,
    EXPORTS = exportinst_lst \<rparr>" and
  C_eq: "C = \<lparr>
    context_TYPES    = functype_lst,
     context_FUNCS   = functype_F_lst,
     context_GLOBALS = globaltype_lst,
     context_TABLES  = tabletype_lst,
     context_MEMS    = memtype_lst,
     context_ELEMS   = elemtype_lst,
     context_DATAS   = datatype_lst,
     context_LOCALS  = [],
     LABELS          = [],
     context_RETURN  = None \<rparr>" and
  globals_ok: "
    list_all2
    (\<lambda>ga gt. Externaddr_ok s (externaddr_GLOBAL ga) (GLOBAL gt))
    globaladdr_lst globaltype_lst" using assms(1)
    by (cases rule: Moduleinst_ok.cases) auto

  have j_len:    "j < length globaltype_lst" using assms(2) C_eq by simp
  have glob_i_j: "(GLOBALS i) ! j = globaladdr_lst ! j" using i_eq by simp
  have C_j:      "(context_GLOBALS C) ! j = globaltype_lst ! j" using C_eq by simp

  have "Externaddr_ok s (externaddr_GLOBAL (globaladdr_lst ! j)) (GLOBAL (globaltype_lst ! j))" using list_all2_nth'[OF globals_ok] j_len
    by auto
  then have "Externaddr_ok s (externaddr_GLOBAL ((GLOBALS i) ! j)) (GLOBAL ((context_GLOBALS C) ! j))" using glob_i_j C_j
    by simp
  then obtain t where
    "((GLOBALS i) ! j < (length (store_GLOBALS s)))"
    "((globalinst_TYPE ((store_GLOBALS s) ! ((GLOBALS i) ! j))) = t)"
    "(GLOBAL t) = (GLOBAL ((context_GLOBALS C) ! j))" using inv_Externaddr_ok_global
    by blast
  then show ?thesis
    by auto
qed

lemma update_glob_store_extension:
assumes "Store_ok s"
        "with_global (mk_state s f) x v_val = mk_state s' f'"
        "(GLOBALS (frame_MODULE f)) ! (proj_uN_0 x) = i"
        "i < length (store_GLOBALS s)"
        "globalinst_TYPE ((store_GLOBALS s) ! i) = mk_globaltype (Some MUT) t"
        "wf_val v_val"
        "Val_ok s v_val t"
  shows "Extend_store s s' \<and> Store_ok s'"
proof (cases s) case (fields store_FUNCS store_GLOBALS store_TABLES store_MEMS store_ELEMS store_DATAS)
  have s_eq: "s = \<lparr>
    store_FUNCS   = store_FUNCS,
    store_GLOBALS = store_GLOBALS,
    store_TABLES  = store_TABLES,
    store_MEMS    = store_MEMS,
    store_ELEMS   = store_ELEMS,
    store_DATAS   = store_DATAS\<rparr>" using fields
    by simp
  have s'_eq: "s' = \<lparr>
    store_FUNCS   = store_FUNCS,
    store_GLOBALS = list_update_func store_GLOBALS i (\<lambda>var_1. var_1 \<lparr> VALUE := v_val \<rparr>),
    store_TABLES  = store_TABLES,
    store_MEMS    = store_MEMS,
    store_ELEMS   = store_ELEMS,
    store_DATAS   = store_DATAS\<rparr>" using with_global.domintros with_global.psimps assms(2) assms(3) fields
    by auto

  have s_globals:
    "store.store_GLOBALS s = store_GLOBALS" using fields
    by simp

  obtain old_val where
    s_global:
    "store_GLOBALS ! i = \<lparr>globalinst_TYPE = mk_globaltype (Some MUT) t, VALUE = old_val\<rparr>" using assms(5) globalinst.cases globalinst.ext_inject globalinst.surjective s_globals
      by (metis (mono_tags, lifting))

  have wf_s: "wf_store s" using assms(1)
    by (cases rule: Store_ok.cases)

  have wf_insts:
    "list_all wf_funcinst store_FUNCS \<and>
     list_all wf_globalinst store_GLOBALS \<and>
     list_all wf_tableinst store_TABLES \<and>
     list_all wf_meminst store_MEMS \<and>
     list_all wf_datainst store_DATAS" using wf_s fields wf_store.cases
    by force

  have s'_global_wf:
    "wf_globalinst \<lparr> globalinst_TYPE = mk_globaltype (Some MUT) t, VALUE = v_val \<rparr>" using assms(6) globalinst_case_underscore
    by auto

  have extend_store: "Extend_store s s'"
    apply (rule Extend_store.mk_Extend_store)
    using fields s'_eq elem_extension_refl holds_upto_def wf_insts tab_extension_refl func_extension_refl data_extension_refl mem_extension_refl wf_s
    apply (simp_all add: list_all_length)
    apply (simp add: list_update_func_length)
    using Extend_globalinst.simps assms(4) list_update_func_nth list_update_func_nth_neq
    apply (metis global_extension_refl globalinst.update_convs(2) s'_global_wf s_global s_globals)
    using assms(4,6) globalinst.update_convs(2) s_globals store_case_underscore wf_globalinst.simps wf_insts list_all_list_update_func
    by metis

  moreover have "Store_ok s'"
  proof -
    obtain functype_lst globaltype_lst tabletype_lst memtype_lst elemtype_lst datatype_lst where
      len_globals: "length store_GLOBALS = length globaltype_lst" and
      len_mems:    "length store_MEMS    = length memtype_lst" and
      len_tables:  "length store_TABLES  = length tabletype_lst" and
      len_funcs:   "length store_FUNCS   = length functype_lst" and
      len_datas:   "length store_DATAS   = length datatype_lst" and
      len_elems:   "length store_ELEMS   = length elemtype_lst" and
  
      globals_ok:  "list_all2 (Globalinst_ok s) (store.store_GLOBALS s) globaltype_lst" and
      mems_ok:     "list_all2 (Meminst_ok s)    store_MEMS   memtype_lst" and
      tables_ok:   "list_all2 (Tableinst_ok s)  store_TABLES tabletype_lst" and
      funcs_ok:    "list_all2 (Funcinst_ok s)   store_FUNCS  functype_lst" and
      datas_ok:    "list_all2 (Datainst_ok s)   store_DATAS  datatype_lst" and
      elems_ok:    "list_all2 (Eleminst_ok s)   store_ELEMS  elemtype_lst" and
  
      wf_memtypes:   "list_all wf_memtype memtype_lst" and
      wf_tabletypes: "list_all wf_tabletype tabletype_lst" using assms(1) Store_ok.simps s_eq
      by auto
  
    moreover then have
      mems_ok':   "list_all2 (Meminst_ok s')   store_MEMS   memtype_lst" and
      tables_ok': "list_all2 (Tableinst_ok s') store_TABLES tabletype_lst" and
      funcs_ok':  "list_all2 (Funcinst_ok s')  store_FUNCS  functype_lst" and 
      datas_ok':  "list_all2 (Datainst_ok s')  store_DATAS  datatype_lst" and
      elems_ok':  "list_all2 (Eleminst_ok s')  store_ELEMS  elemtype_lst" using 
        extend_store list_all2_mono 
        store_extension_Meminst_ok[of s _ _ s']
        store_extension_Tableinst_ok[of s _ _ s']
        store_extension_Funcinst_ok[of s _ _ s']
        store_extension_Datainst_ok[of s _ _ s']
        store_extension_Eleminst_ok[of s _ _ s']
      by metis+
  
    moreover have len_globals':
      "((length (store.store_GLOBALS s')) = (length globaltype_lst))" using assms(4) list_update_func_length[of  store_GLOBALS i] len_globals s'_eq
      by simp
    moreover have wf_s': "wf_store s'" using extend_store store_extension_wf
      by simp
    moreover have globals_ok': "list_all2 (Globalinst_ok s') (store.store_GLOBALS s') globaltype_lst" proof -
      have untouched: "Globalinst_ok s x y \<Longrightarrow> Globalinst_ok s' x y" for x y
        using extend_store store_extension_Globalinst_ok by simp
      have updated: "Globalinst_ok s (store.store_GLOBALS s ! i) (globaltype_lst ! i) \<Longrightarrow> Globalinst_ok s' ((store.store_GLOBALS s ! i)\<lparr>VALUE := v_val\<rparr>) (globaltype_lst ! i)"
        proof -
          have "Globaltype_ok (mk_globaltype (Some MUT) t)" using mk_Globaltype_ok
            by metis
          moreover have "Val_ok s' v_val t" using store_extension_valok assms(7) wf_s' extend_store
            by simp
          moreover have "wf_globalinst \<lparr>globalinst_TYPE = mk_globaltype (Some MUT) t, VALUE = old_val\<rparr>" using assms(4) fields list_all_length wf_insts s_global
            by fastforce
          moreover have "globaltype_lst ! i = mk_globaltype (Some MUT) t"
            proof -
              have "Globalinst_ok s (store_GLOBALS ! i) (globaltype_lst ! i)" using globals_ok assms(4) list_all2_nthD s_globals
                by auto
              then show ?thesis using assms(5) s_globals Globalinst_ok.cases
                by force
            qed
          ultimately show ?thesis using mk_Globalinst_ok wf_s' s'_global_wf s_global s_globals
            by simp
        qed
      
      have s'_globals:
        "store.store_GLOBALS s' = list_update_func (store.store_GLOBALS s) i (\<lambda>var_1. var_1 \<lparr> VALUE := v_val \<rparr>)" using s'_eq s_globals
        by simp
        
      show ?thesis using list_all2_list_update_func[OF assms(4) globals_ok s'_globals, where ?Q = "Globalinst_ok s'"] untouched updated
       by blast
    qed
  
    ultimately show ?thesis using mk_Store_ok s'_eq
      by simp
  qed

  ultimately show ?thesis
    by simp
qed

termination admininstr_instr
  by lexicographic_order

lemma global_set_store_extension: 
assumes "with_global (mk_state s f) x v_val = mk_state s' f'"
        "Store_ok s"
        "Moduleinst_ok s (frame_MODULE f) C'"
        "C' = (append_res_context \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [],
        context_LOCALS = map typeofval (LOCALS f), LABELS = lbl, context_RETURN = rtn\<rparr> C)"
        "Instrs_ok2 s C [admininstr_val v_val, admininstr_sc5 (admininstr_st5_GLOBAL_SET x)] ft"
        "t_inst_match C C'"
shows "Extend_store s s' \<and> Store_ok s'"
proof (cases ft)
  case (mk_functype t1 t3)
  obtain functype_lst functype_F_lst globaltype_lst tabletype_lst memtype_lst elemtype_lst datatype_lst ctx_LOCALS labels return where
    ctx: "C = \<lparr>
      context_TYPES   = functype_lst,
      context_FUNCS   = functype_F_lst, 
      context_GLOBALS = globaltype_lst,
      context_TABLES  = tabletype_lst,
      context_MEMS    = memtype_lst,
      context_ELEMS   = elemtype_lst,
      context_DATAS   = datatype_lst,
      context_LOCALS  = ctx_LOCALS,
      LABELS          = labels,
      context_RETURN  = return \<rparr>" using old.unit.exhaust res_context.surjective by (metis)
  from Moduleinst_ok.simps[of s "(frame_MODULE f)" C'] obtain globaladdr_lst funcaddr_lst memaddr_lst tableaddr_lst exportinst_lst dataaddr_lst elemaddr_lst where
    len_globals_eq:    "((length globaladdr_lst) = (length globaltype_lst))" and
    extern_globals_ok: "list_all2 (\<lambda>g_addr g_type. Externaddr_ok s (externaddr_GLOBAL g_addr) (GLOBAL g_type)) globaladdr_lst globaltype_lst" and
    ctx': "C' = \<lparr>
      context_TYPES   = functype_lst,
      context_FUNCS   = functype_F_lst, 
      context_GLOBALS = globaltype_lst,
      context_TABLES  = tabletype_lst,
      context_MEMS    = memtype_lst,
      context_ELEMS   = elemtype_lst,
      context_DATAS   = datatype_lst,  
      context_LOCALS  = [],
      LABELS          = [],
      context_RETURN  = None \<rparr>" and
    frame_module: "(frame_MODULE f) = \<lparr>
      TYPES   = functype_lst,
      FUNCS   = funcaddr_lst,
      GLOBALS = globaladdr_lst,
      TABLES  = tableaddr_lst,
      MEMS    = memaddr_lst,
      ELEMS   = elemaddr_lst,
      DATAS   = dataaddr_lst,
      EXPORTS = exportinst_lst \<rparr>" using assms(3) t_inst_match_is[of C C'] append_res_context_def assms(4) ctx by force

  from mk_functype obtain t2 where
    admin_val:      "Instrs_ok2 s C [admininstr_val v_val] (mk_functype t1 t2)" and
    admin_glob_set: "Instrs_ok2 s C [admininstr_sc5 (admininstr_st5_GLOBAL_SET x)] (mk_functype t2 t3)"
      using assms(5) inv_seq[of s C _ t1 t3 "[admininstr_val v_val]" "[admininstr_sc5 (admininstr_st5_GLOBAL_SET x)]"] by fastforce

  from admin_val have val_wf: 
  "wf_val v_val" using Instrs_ok2_wf_instr wf_admininstr_val_inv by fastforce

  from admin_glob_set obtain t_1_lst t_2_lst where
        "Instr_ok2 s C (admininstr_sc5 (admininstr_st5_GLOBAL_SET x)) (mk_functype t_1_lst t_2_lst)" and
    st: "mk_instrtype t_1_lst t_2_lst <ti: mk_instrtype t2 t3" using inv_one_admininstr by fast
  then have
    "Instr_ok C (instr_sc4 (GLOBAL_SET x)) (mk_functype t_1_lst t_2_lst)" using inv_plain by auto
  then obtain mut t where glob_set_inv:
    "(proj_uN_0 x) < length (context_GLOBALS C)"
    "context_GLOBALS C ! (proj_uN_0 x) = mk_globaltype (Some mut) t" 
    "mk_functype (mk_list [t]) (mk_list []) = mk_functype t_1_lst t_2_lst" using inv_global_set by blast

  from admin_val have 
       "mk_instrtype (mk_list []) (mk_list [typeofval v_val]) <ti: mk_instrtype t1 t2" and
  vok: "Val_ok s v_val (typeofval v_val)"
      using Instrs_ok2_const_replace[of s C "[v_val]" _ C] Instrs_ok2_wf(1) inv_const_list[of s C "[_]" t1 t2 "[_]"] by auto
  then have
    "Resulttype_sub (mk_list [typeofval v_val]) (mk_list [t])"
      using st glob_set_inv(3) produce_consume[of "[_]" t1 t2 "[]" "[_]" "[]" t3] by auto
  then have
    "Valtype_sub (typeofval v_val) t"
      by (induction "mk_list [typeofval v_val]" "mk_list [t]" rule: Resulttype_sub.induct) blast
  then have val_ok_principal:
  "Val_ok s v_val t"
      using vok Val_ok_sub by blast

  from extern_globals_ok have
    "Externaddr_ok s 
     (externaddr_GLOBAL (globaladdr_lst ! (proj_uN_0 x))) 
     (GLOBAL (globaltype_lst ! (proj_uN_0 x)))" 
      using list_all2_nth[of _ globaladdr_lst globaltype_lst "(proj_uN_0 x)"] glob_set_inv(1) ctx len_globals_eq by auto
  then have
    "(context_GLOBALS C) ! (proj_uN_0 x) = globalinst_TYPE (store_GLOBALS s ! ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)))"
      using inv_Externaddr_ok frame_module ctx by fastforce
  then have store_glob_mut:
  "globalinst_TYPE ((store_GLOBALS s ! ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)))) = mk_globaltype (Some MUT) t"
      using glob_set_inv(2) r_MUT.exhaust by metis

  show ?thesis using update_glob_store_extension[OF assms(2) assms(1) _ _ store_glob_mut val_wf val_ok_principal] store_typing_imp_glob_agree[OF assms(3), of "(proj_uN_0 x)"] glob_set_inv(1) ctx ctx'
    by simp
qed

lemma reduce_store_extension:
assumes "Step (mk_config (mk_state s f) admininstr_lst) (mk_config (mk_state s' f') admininstr'_lst)"
        "Store_ok s"
        "Moduleinst_ok s (frame_MODULE f) C'"
        "C' = (append_res_context \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [],
        context_LOCALS = map typeofval (LOCALS f), LABELS = lbl, context_RETURN = rtn\<rparr> C)"
        "Instrs_ok2 s C admininstr_lst (mk_functype t_1_lst t_2_lst)"
        "t_inst_match C C'"
shows "Extend_store s s' \<and> Store_ok s'"
using assms
proof (induction "(mk_config (mk_state s f) admininstr_lst)" "(mk_config (mk_state s' f') admininstr'_lst)" arbitrary: C lbl rtn admininstr_lst  admininstr'_lst rule: Step.induct)
  case (Step__global_set v_val x)
  then show ?case using global_set_store_extension by simp
next
  case (Step__local_set v_val x)
  then show ?case sorry      
next
  case (table_set_val i x v_ref)
  then show ?case sorry    
next
  case (table_set_trap i x v_ref)
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
  case (pure admininstr_lst admininstr'_lst)
  have "wf_store s" using Instrs_ok2.simps pure.prems(4) by blast
  then show ?case using store_extension_refl pure(2,4)
    by blast
next
  case (read admininstr_lst admininstr'_lst)
  have "wf_store s" using Instrs_ok2_wf(2) assms(5) by auto
  then show ?case using store_extension_refl read(2,4)
    by blast
qed

end