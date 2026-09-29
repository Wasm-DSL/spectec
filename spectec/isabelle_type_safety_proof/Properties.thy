theory Properties
	imports Main isabelle_reference_output_wasm2 Type_Inversion
          Context_Store_Agreement store_extension_typing
          helper_lemmas Typing_Simplified
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
(*global_set*)
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
      using inv_Externaddr_ok_global frame_module ctx by fastforce
  then have store_glob_mut:
  "globalinst_TYPE ((store_GLOBALS s ! ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)))) = mk_globaltype (Some MUT) t"
      using glob_set_inv(2) r_MUT.exhaust by metis

  show ?thesis using update_glob_store_extension[OF assms(2) assms(1) _ _ store_glob_mut val_wf val_ok_principal] store_typing_imp_glob_agree[OF assms(3), of "(proj_uN_0 x)"] glob_set_inv(1) ctx ctx'
    by simp
qed

(*table_set*)
lemma inst_typing_imp_tabi_agree:
assumes "Moduleinst_ok s (frame_MODULE f) C"
        "frame_MODULE f = \<lparr> TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, TABLES = tableaddr_lst, MEMS = memaddr_lst, ELEMS = elemaddr_lst, DATAS = dataaddr_lst, EXPORTS = exportinst_lst \<rparr>"
        "C = \<lparr> context_TYPES = functype_lst, context_FUNCS = functype_F_lst, context_GLOBALS = globaltype_lst, context_TABLES = tabletype_lst, context_MEMS = memtype_lst, context_ELEMS = elemtype_lst, context_DATAS = datatype_lst, context_LOCALS = ctx_LOCALS, LABELS = lbls, context_RETURN = rtn \<rparr>"
        "proj_uN_0 x < length tabletype_lst"
shows "Externaddr_ok s (externaddr_TABLE (tableaddr_lst ! (proj_uN_0 x))) (TABLE (tabletype_lst ! (proj_uN_0 x)))"
proof -
  obtain functype_lst' funcaddr_lst' globaladdr_lst' tableaddr_lst' memaddr_lst' elemaddr_lst' dataaddr_lst' exportinst_lst' functype_F_lst' globaltype_lst' tabletype_lst' memtype_lst' elemtype_lst' datatype_lst' where
    f_eq: "frame_MODULE f = \<lparr> TYPES = functype_lst', FUNCS = funcaddr_lst', GLOBALS = globaladdr_lst', TABLES = tableaddr_lst', MEMS = memaddr_lst', ELEMS = elemaddr_lst', DATAS = dataaddr_lst', EXPORTS = exportinst_lst' \<rparr>" and
    C_eq: "C = \<lparr> context_TYPES = functype_lst', context_FUNCS = functype_F_lst', context_GLOBALS = globaltype_lst', context_TABLES = tabletype_lst', context_MEMS = memtype_lst', context_ELEMS = elemtype_lst', context_DATAS = datatype_lst', context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr>" and
    tables_ok': "list_all2 (\<lambda>ta tt. Externaddr_ok s (externaddr_TABLE ta) (TABLE tt)) tableaddr_lst' tabletype_lst'" and
    len_tables_eq: "length tableaddr_lst' = length tabletype_lst'"
    using assms(1) by (cases rule: Moduleinst_ok.cases) auto

  have tableaddr_eq: "tableaddr_lst = tableaddr_lst'"
    using assms(2) f_eq by simp
  have tabletype_eq: "tabletype_lst = tabletype_lst'"
    using assms(3) C_eq by simp

  have x_len: "proj_uN_0 x < length tableaddr_lst'"
    using assms(4) len_tables_eq tabletype_eq by auto

  have tables_ok: "list_all2 (\<lambda>ta tt. Externaddr_ok s (externaddr_TABLE ta) (TABLE tt)) tableaddr_lst tabletype_lst"
    using tables_ok' tableaddr_eq tabletype_eq by simp

  show ?thesis
    by (metis list_all2_nthD x_len tables_ok tableaddr_eq)
qed

lemma types_preserved_table_set_aux:
assumes "Instrs_ok2 s C [
          admininstr_sc1 (admininstr_st1_CONST I32 i), 
          admininstr_ref v_ref, 
          admininstr_sc5 (admininstr_st5_TABLE_SET x)
        ] ft"
shows "\<exists>lim rt.
         proj_uN_0 x < length (context_TABLES C) \<and>
         (context_TABLES C) ! (proj_uN_0 x) = mk_tabletype lim rt \<and>
         wf_tabletype (mk_tabletype lim rt) \<and>
         Ref_ok s v_ref rt \<and>
         typeofval (val_ref v_ref) = valtype_reftype rt \<and>
         Instr_ok C (instr_sc5 (TABLE_SET x)) 
           (mk_functype (mk_list [valtype_I32, valtype_reftype rt]) (mk_list []))"
proof (cases ft)
  case (mk_functype t1 t3)
  obtain t2 where
    admin_const_ref: "Instrs_ok2 s C [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_ref v_ref] (mk_functype t1 t2)" and
    admin_table_set: "Instrs_ok2 s C [admininstr_sc5 (admininstr_st5_TABLE_SET x)] (mk_functype t2 t3)"
    using assms inv_seq[of s C _ t1 t3 "[admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_ref v_ref]" "[admininstr_sc5 (admininstr_st5_TABLE_SET x)]"] mk_functype
    by fastforce

  from admin_table_set obtain t_1_lst t_2_lst where
    ok_ts2: "Instr_ok2 s C (admininstr_sc5 (admininstr_st5_TABLE_SET x)) (mk_functype t_1_lst t_2_lst)" and
    st: "mk_instrtype t_1_lst t_2_lst <ti: mk_instrtype t2 t3"
    using inv_one_admininstr by fast

  then have ok_ts_plain: "Instr_ok C (instr_sc5 (TABLE_SET x)) (mk_functype t_1_lst t_2_lst)"
    using inv_plain admininstr_instr.domintros admininstr_instr.psimps by fastforce
  then obtain lim rt where
    x_lt: "proj_uN_0 x < length (context_TABLES C)" and
    tab_C: "(context_TABLES C) ! (proj_uN_0 x) = mk_tabletype lim rt" and
    wf_tab: "wf_tabletype (mk_tabletype lim rt)" and
    ft_eq: "mk_functype (mk_list [valtype_I32, valtype_reftype rt]) (mk_list []) = mk_functype t_1_lst t_2_lst"
    using inv_table_set by blast

  have ok_ts: "Instr_ok C (instr_sc5 (TABLE_SET x)) (mk_functype (mk_list [valtype_I32, valtype_reftype rt]) (mk_list []))"
    using ok_ts_plain ft_eq by simp

  have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32, typeofval (val_ref v_ref)]) <ti: mk_instrtype t1 t2"
    using inv_const_list[of s C "[_,_]" t1 t2 "[val_CONST I32 i, val_ref v_ref]"] admin_const_ref
      admininstr_val.domintros admininstr_val.psimps admininstr_val_ref
      valtype_numtype.domintros valtype_numtype.psimps typeofval.domintros typeofval.psimps
    by fastforce

  have "Resulttype_sub (mk_list [valtype_I32, typeofval (val_ref v_ref)]) (mk_list [valtype_I32, valtype_reftype rt])"
    using st ft_eq produce_consume[of "[valtype_I32, typeofval (val_ref v_ref)]" t1 t2 "[]" "[valtype_I32, valtype_reftype rt]" "[]" t3] subv
    by auto
  then have "Valtype_sub (typeofval (val_ref v_ref)) (valtype_reftype rt)"
    by (induction "mk_list [valtype_I32, typeofval (val_ref v_ref)]" "mk_list [valtype_I32, valtype_reftype rt]" rule: Resulttype_sub.induct) auto
  then have val_ty: "typeofval (val_ref v_ref) = valtype_reftype rt"
  proof (cases rule: Valtype_sub.cases)
    case refl
    then show ?thesis by simp
  next
    case bot
    then have "typeofval (val_ref v_ref) = BOT" by simp
    then show ?thesis
    proof (cases v_ref)
      case (ref_REF_NULL rt0)
      then show ?thesis using `typeofval (val_ref v_ref) = BOT`
        by (cases rt0) (auto simp add: typeofval.psimps typeofval.domintros val_ref.psimps val_ref.domintros valtype_reftype.psimps valtype_reftype.domintros)
    next
      case (REF_FUNC_ADDR fa)
      then show ?thesis using `typeofval (val_ref v_ref) = BOT`
        by (auto simp add: typeofval.psimps typeofval.domintros val_ref.psimps val_ref.domintros)
    next
      case (REF_HOST_ADDR ha)
      then show ?thesis using `typeofval (val_ref v_ref) = BOT`
        by (auto simp add: typeofval.psimps typeofval.domintros val_ref.psimps val_ref.domintros)
    qed
  qed

  obtain t_ref_in where
    admin_ref: "Instrs_ok2 s C [admininstr_ref v_ref] (mk_functype t_ref_in t2)"
    using inv_seq[of s C _ t1 t2 "[admininstr_sc1 (admininstr_st1_CONST I32 i)]" "[admininstr_ref v_ref]"] admin_const_ref
    by fastforce
  then obtain tr1 tr2 where
    ok_ref: "Instr_ok2 s C (admininstr_ref v_ref) (mk_functype tr1 tr2)"
    using inv_one_admininstr by fast
  then obtain rt' where ref_ok: "Ref_ok s v_ref rt'"
    using inv_ref by blast
  then have "typeofval (val_ref v_ref) = valtype_reftype rt'"
    using ref_ok_agree by simp
  then have "valtype_reftype rt' = valtype_reftype rt"
    using val_ty by simp
  then have "rt' = rt"
    by (cases rt; cases rt') (auto simp add: valtype_reftype.psimps valtype_reftype.domintros)
  then have ref_ok_rt: "Ref_ok s v_ref rt"
    using ref_ok by simp

   show ?thesis using x_lt tab_C wf_tab ref_ok_rt val_ty ok_ts by blast
qed

lemma store_tabs1_store_extension:
assumes "proj_uN_0 (the (proj_num__0 i)) < length (REFS (fun_table (mk_state s f) x))"
        "(TABLES (frame_MODULE f) ! proj_uN_0 x) < length (store.store_TABLES s)"
        "with_table (mk_state s f) x (proj_uN_0 (the (proj_num__0 i))) v_ref = mk_state s' f'"
        "Store_ok s"
        "Ref_ok s v_ref ref_type"
        "tableinst_TYPE (fun_table (mk_state s f) x) = mk_tabletype (mk_limits (mk_uN lm) (map_option mk_uN u32_opt)) ref_type"
shows "Extend_store s s' \<and> Store_ok s'"
proof (cases s)
  case (fields store_FUNCS store_GLOBALS store_TABLES store_MEMS store_ELEMS store_DATAS)
  let ?i = "(proj_uN_0 (the (proj_num__0 i)))"
  let ?x = "(TABLES (frame_MODULE f) ! proj_uN_0 x)"

  let ?with_ref = "(\<lambda>tbl. tbl \<lparr> REFS := list_update_func (REFS tbl) (proj_uN_0 (the (proj_num__0 i))) (\<lambda>_. v_ref) \<rparr>)"

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
    store_GLOBALS = store_GLOBALS,
    store_TABLES  = list_update_func store_TABLES ?x ?with_ref,
    store_MEMS    = store_MEMS,
    store_ELEMS   = store_ELEMS,
    store_DATAS   = store_DATAS\<rparr>" using with_table.domintros with_table.psimps assms(3) fields
    by auto

  have s_tables:  "store.store_TABLES s  = store_TABLES" using fields by simp
  have s'_tables: "store.store_TABLES s' = list_update_func store_TABLES ?x ?with_ref" using s'_eq by simp

  let ?tbl  = "store_TABLES          ! ?x"
  let ?tbl' = "store.store_TABLES s' ! ?x"

  have
  wf_s: "wf_store s" using assms(4) by (cases rule: Store_ok.cases)
  then have
  wf_insts:
    "list_all wf_funcinst   store_FUNCS \<and>
     list_all wf_globalinst store_GLOBALS \<and>
     list_all wf_tableinst  store_TABLES \<and>
     list_all wf_meminst    store_MEMS \<and>
     list_all wf_datainst   store_DATAS" using fields wf_store.cases by force

  have
  x_lt: "?x < length store_TABLES" using assms(2) s_tables by simp
  
  have
  s_table_wf: "wf_tableinst ?tbl" using list_all_nth wf_insts x_lt by meson

  let ?old_lst = "REFS (fun_table (mk_state s f) x)"
  have
  s_table: "?tbl = \<lparr> 
    tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN lm) (map_option mk_uN u32_opt)) ref_type),
    REFS           = ?old_lst \<rparr>"
    using assms(6) fun_table.domintros fun_table.psimps s_tables by force

  have tbl'_eq: "?tbl' = ?with_ref ?tbl" using s'_eq list_update_func_nth[OF x_lt] by simp
  then have
  s'_table: "?tbl' = \<lparr> 
      tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN lm)  (map_option mk_uN u32_opt)) ref_type),
      REFS = (list_update_func ?old_lst ?i (\<lambda>_. v_ref)) \<rparr>"  using s_table by auto 

  have
  s'_table_wf: "wf_tableinst ?tbl'"
  proof -
    have "wf_tabletype (tableinst_TYPE ?tbl')" using s_table_wf wf_tableinst.simps s'_table s_table by simp
    then show ?thesis using s'_table tableinst_case_underscore by simp
  qed

  have extend_store: "Extend_store s s'"
    apply (rule Extend_store.mk_Extend_store)
    using holds_upto_def apply simp_all
    using s_eq s'_eq     apply simp_all
    using wf_insts elem_extension_refl global_extension_refl func_extension_refl data_extension_refl mem_extension_refl   apply (simp_all add: list_all_length)
    using list_update_func_length apply metis
    subgoal proof -
      have at_x: "Extend_tableinst ?tbl ?tbl'" using list_update_func_length le_refl mk_Extend_tableinst s_table_wf s'_table_wf s_table s'_table by metis
    
      show ?thesis
      proof (intro allI impI)
        fix ia
        assume "ia < length store_TABLES"
        then show "Extend_tableinst (store_TABLES ! ia) ((list_update_func store_TABLES ?x ?with_ref) ! ia)"
          using at_x list_update_func_nth_neq[OF x_lt] wf_insts list_all_length tab_extension_refl s'_tables by (metis (no_types, lifting))
      qed qed
    using wf_s apply simp
    using wf_store.simps list_all_list_update_func list_update_func_nth s'_table_wf s'_tables wf_insts x_lt by (metis (mono_tags, lifting))
  
  moreover have "Store_ok s'" proof -
    obtain globaltype_lst memtype_lst tabletype_lst functype_lst elemtype_lst datatype_lst where
      len_globals: "length store_GLOBALS = length globaltype_lst" and
      len_mems:    "length store_MEMS    = length memtype_lst"    and
      len_tables:  "length store_TABLES  = length tabletype_lst"  and
      len_funcs:   "length store_FUNCS   = length functype_lst"   and
      len_datas:   "length store_DATAS   = length datatype_lst"   and
      len_elems:   "length store_ELEMS   = length elemtype_lst"   and
  
      globals_ok:  "list_all2 (Globalinst_ok s) store_GLOBALS globaltype_lst" and
      mems_ok:     "list_all2 (Meminst_ok s)    store_MEMS   memtype_lst"     and
      tables_ok:   "list_all2 (Tableinst_ok s) store_TABLES tabletype_lst"    and
      funcs_ok:    "list_all2 (Funcinst_ok s)   store_FUNCS  functype_lst"    and
      datas_ok:    "list_all2 (Datainst_ok s)   store_DATAS  datatype_lst"    and
      elems_ok:    "list_all2 (Eleminst_ok s)   store_ELEMS  elemtype_lst"    and
  
      wf_memtypes:   "list_all wf_memtype memtype_lst" and
      wf_tabletypes: "list_all wf_tabletype tabletype_lst" using assms(4) Store_ok.simps s_eq wf_s by auto

    moreover then have
      globals_ok': "list_all2 (Globalinst_ok s') store_GLOBALS globaltype_lst" and
      mems_ok':    "list_all2 (Meminst_ok s')    store_MEMS    memtype_lst" and
      funcs_ok':   "list_all2 (Funcinst_ok s')   store_FUNCS   functype_lst" and 
      datas_ok':   "list_all2 (Datainst_ok s')   store_DATAS   datatype_lst" and
      elems_ok':   "list_all2 (Eleminst_ok s')   store_ELEMS   elemtype_lst" using 
        extend_store list_all2_mono 
        store_extension_Globalinst_ok[of s _ _ s']
        store_extension_Meminst_ok[of s _ _ s']
        store_extension_Funcinst_ok[of s _ _ s']
        store_extension_Datainst_ok[of s _ _ s']
        store_extension_Eleminst_ok[of s _ _ s']
      by metis+

    moreover have len_tables':
      "((length (store.store_TABLES s')) = (length tabletype_lst))" using list_update_func_length[of store_TABLES ?i] len_tables s'_eq 
      by (simp add: list_update_func_length)
    moreover have wf_s': "wf_store s'" using extend_store store_extension_wf
      by simp
    moreover have tables_ok': "list_all2 (Tableinst_ok s') (store.store_TABLES s') tabletype_lst" proof -
      have at_x: "Tableinst_ok s' ?tbl' (tabletype_lst ! ?x)"
      proof -
        have tbl_cases: "
          (tabletype_lst ! ?x) = (tableinst_TYPE ?tbl) \<and>
          Tabletype_ok (tableinst_TYPE ?tbl) \<and>
          list_all (\<lambda>v_ref. Ref_ok s v_ref ref_type) ?old_lst \<and>
          length ?old_lst = lm \<and>
          wf_tabletype (tableinst_TYPE ?tbl)" using list_all2_nthD[OF tables_ok] x_lt Tableinst_ok.simps s_table by force

        have 2: "list_all (\<lambda>v_ref. Ref_ok s' v_ref ref_type) (REFS ?tbl')"
        proof -
          have old_ref_ok: "list_all (\<lambda>v_ref. Ref_ok s' v_ref ref_type) ?old_lst"
            using tbl_cases extend_store store_extension_refok list.pred_mono_strong by metis

          have at_x: "Ref_ok s' v_ref ref_type"
            using assms(5) extend_store store_extension_refok by simp

          show ?thesis
            using list_all_list_update_func[OF old_ref_ok assms(1) at_x] s'_table by simp
        qed

        have 3: "length (REFS ?tbl') = lm" using list_update_func_length tbl_cases s'_table by auto

        show ?thesis using mk_Tableinst_ok[OF _ 2 3 wf_s'] s'_table s_table tbl_cases s'_table_wf by simp
      qed 

      have untouched: "Tableinst_ok s x y \<Longrightarrow> Tableinst_ok s' x y" for x y using extend_store store_extension_Tableinst_ok by simp

      show ?thesis using list_all2_list_update_func[OF x_lt, of _ _ "store.store_TABLES s'" "?with_ref" "Tableinst_ok s'", OF tables_ok] s'_tables tbl'_eq untouched at_x
        by auto
    qed

    show ?thesis using mk_Store_ok[OF len_globals globals_ok' len_mems mems_ok' len_tables' tables_ok' len_funcs funcs_ok' len_datas datas_ok' len_elems elems_ok' _ wf_s' wf_memtypes wf_tabletypes _] s'_eq s'_tables wf_s' by simp
  qed

  ultimately show ?thesis by simp
qed

lemma table_set_store_extension:
assumes "proj_num__0 i \<noteq> None"
        "proj_uN_0 (the (proj_num__0 i)) < length (REFS (fun_table (mk_state s f) x))"
        "with_table (mk_state s f) x (proj_uN_0 (the (proj_num__0 i))) v_ref = mk_state s' f'"
        "Store_ok s"
        "Moduleinst_ok s (frame_MODULE f) C'"
        "C' = append_res_context \<lparr>
         context_TYPES = [], context_FUNCS = [],
         context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [],
         context_DATAS = [],
         context_LOCALS = map typeofval (LOCALS f),
         LABELS = lbl, context_RETURN = rtn\<rparr> C"
        "Instrs_ok2 s C [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_ref v_ref, admininstr_sc5 (admininstr_st5_TABLE_SET x)] (mk_functype t_1_lst t_2_lst)"
        "t_inst_match C C'"
shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?x = "proj_uN_0 x"
  have ctx_table_eq: "(context_TABLES C) = (context_TABLES C')" using assms(8) t_inst_match_def by auto

  obtain functype_lst functype_F_lst globaltype_lst tabletype_lst memtype_lst elemtype_lst datatype_lst
  globaladdr_lst funcaddr_lst memaddr_lst tableaddr_lst exportinst_lst dataaddr_lst elemaddr_lst where
    ctx: "C' = \<lparr>
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
        EXPORTS = exportinst_lst \<rparr>"
    using assms(5) by (cases rule: Moduleinst_ok.cases) auto 

  obtain lm u32_opt rt where 
  tab_type: "(context_TABLES C) ! ?x = mk_tabletype (mk_limits (mk_uN lm) (map_option mk_uN u32_opt)) rt"
  proof -
    obtain lim rt where 1: "(context_TABLES C) ! ?x = mk_tabletype lim rt"
      by (cases "(context_TABLES C) ! (proj_uN_0 x)")
    obtain lim2 u32 where "lim = mk_limits lim2 u32" by (cases lim)
    then obtain lm u32_opt where 2: "lim = mk_limits (mk_uN lm) (map_option mk_uN u32_opt)"
      apply (cases lim2; cases u32)
      using  None_eq_map_option_iff apply simp
      using  map_option_eq_Some uN.exhaust by metis

    show ?thesis using that 1 2 by simp
  qed

  have 
                 "?x < length (context_TABLES C)" and
    refOk:       "Ref_ok s v_ref rt" and
    mk_functype: "Instr_ok C (instr_sc5 (TABLE_SET x)) (mk_functype (mk_list [valtype_I32, (valtype_reftype rt)]) (mk_list []))"
    using types_preserved_table_set_aux[OF assms(7)] tab_type by simp+
  then have x_lt: "?x < length (context_TABLES C')" using ctx_table_eq by simp
 
  obtain v limv limup rtv where
     1:      "(TABLES (frame_MODULE f) ! ?x) < length (store_TABLES s)" and
     tab_v:  "store_TABLES s ! (TABLES (frame_MODULE f) ! ?x) = v" and
     v_ty:   "tableinst_TYPE v = mk_tabletype limv rtv" and
     tab_up: "TABLE (mk_tabletype limup rtv) = TABLE (tabletype_lst ! ?x)"
  proof -
    have x_lt_tab: "?x < length tabletype_lst"
      using x_lt ctx by simp
    have ext: "Externaddr_ok s (externaddr_TABLE (tableaddr_lst ! ?x)) (TABLE (tabletype_lst ! ?x))" using inst_typing_imp_tabi_agree[OF assms(5) frame_module ctx x_lt_tab] by simp
    then obtain v' limv' limup' rtv' where 
              "tableaddr_lst ! ?x < length (store_TABLES s)" and 
              "store_TABLES s ! (tableaddr_lst ! ?x) = v'" and
      v_ty:   "tableinst_TYPE v' = mk_tabletype limv' rtv'" and
      tab_up: "TABLE (mk_tabletype limup' rtv') =  (TABLE (tabletype_lst !  ?x))"
      using inv_Externaddr_ok_table by blast
    then have "(TABLES (frame_MODULE f) ! ?x) < length (store_TABLES s)" and "store_TABLES s !(TABLES (frame_MODULE f) ! ?x) = v'" using frame_module by auto

    then show ?thesis using inv_Externaddr_ok_table[OF ext] that[OF _ _ v_ty tab_up]
      by blast
  qed

  obtain lm' u32_opt' where 2: "tableinst_TYPE (fun_table (mk_state s f) x) = mk_tabletype (mk_limits (mk_uN lm') (map_option mk_uN u32_opt')) rt"
  proof -
    have "fun_table (mk_state s f) x = v"
      using tab_v fun_table.psimps fun_table.domintros by auto
    then have fun_ty: "tableinst_TYPE (fun_table (mk_state s f) x) = mk_tabletype limv rtv"
      using tab_v v_ty by auto

    have tab_ctx_eq: "tabletype_lst ! ?x = (context_TABLES C) ! ?x"
      using ctx ctx_table_eq by auto
    have rtv_eq: "rtv = rt"
      using tab_up tab_ctx_eq tab_type by auto

    then have fun_ty_rt: "tableinst_TYPE (fun_table (mk_state s f) x) = mk_tabletype limv rt"
      using fun_ty by simp

    obtain lim2 u32 where "limv = mk_limits lim2 u32"
      by (cases limv)
    then obtain lm' u32_opt' where limv_eq: "limv = mk_limits (mk_uN lm') (map_option mk_uN u32_opt')"
      apply (cases lim2; cases u32)
      using None_eq_map_option_iff apply simp
      using map_option_eq_Some uN.exhaust by metis

    have "tableinst_TYPE (fun_table (mk_state s f) x) = mk_tabletype (mk_limits (mk_uN lm') (map_option mk_uN u32_opt')) rt"
      using fun_ty_rt limv_eq by simp
    then show ?thesis
      using that by blast
  qed

  show ?thesis
    using store_tabs1_store_extension[OF assms(2) 1 assms(3) assms(4) refOk 2]  
    by blast
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
  case (table_set_val i x v_ref)
  then show ?case using table_set_store_extension by simp    
next
  case (table_grow_succeed x v_n v_ref var_0 ti)
  then show ?case sorry
next
  case (Step__elem_drop x)
  then show ?case sorry
next
  case (store_num_val i nt b_lst c ao)
  then show ?case sorry
next
  case (store_pack_val i v_Inn c b_lst v_n ao)
  then show ?case sorry
next
  case (vstore_val i b_lst c ao)
  then show ?case sorry
next
  case (vstore_lane_val i v_N v_Jnn v_M c j b_lst ao)
  then show ?case sorry
next
  case (memory_grow_succeed v_n var_0 mi)
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
next
  case (Step__local_set v_val x)
  have "s = s'" using with_local.psimps with_local.domintros Step__local_set(1) by auto
  then show ?case using assms(2) store_extension_refl Instrs_ok2_wf(2) Step__local_set(5)
    by metis
next
  case (table_set_trap i x v_ref)
  then show ?case using store_extension_refl Instrs_ok2_wf(2) by simp 
next
  case (table_grow_fail var_0 v_ref v_n x)
  then show ?case using store_extension_refl Instrs_ok2_wf(2) by simp
next
  case (store_num_trap i nt ao c)
  then show ?case using store_extension_refl Instrs_ok2_wf(2) by simp
next
  case (store_pack_trap i ao v_n v_Inn c)
  then show ?case using store_extension_refl Instrs_ok2_wf(2) by simp
next
  case (vstore_oob i ao c)
  then show ?case using store_extension_refl Instrs_ok2_wf(2) by simp
next
  case (vstore_lane_oob i ao v_N c j)
  then show ?case using store_extension_refl Instrs_ok2_wf(2) by simp
next
  case (memory_grow_fail var_0 v_n)
  then show ?case using store_extension_refl Instrs_ok2_wf(2) by simp
qed

end