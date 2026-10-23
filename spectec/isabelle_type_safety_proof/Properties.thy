theory Properties
	imports Main isabelle_reference_output_wasm2 Type_Inversion
          Context_Store_Agreement store_extension_typing
          helper_lemmas Typing_Simplified Axioms
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
  have ctx_agree: "context_TYPES C' = functype_lst" "context_FUNCS C' = functype_F_lst"
    "context_GLOBALS C' = globaltype_lst" "context_TABLES C' = tabletype_lst" "context_MEMS C' = memtype_lst"
    "context_ELEMS C' = elemtype_lst" "context_DATAS C' = datatype_lst"
    using assms(5) ctx unfolding t_inst_match_def by simp_all
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
      EXPORTS = exportinst_lst \<rparr>" using assms(3) ctx_agree by force

  from mk_functype obtain t2 where
    admin_val:      "Instrs_ok2 s C [admininstr_val v_val] (mk_functype t1 t2)" and
    admin_glob_set: "Instrs_ok2 s C [admininstr_sc5 (admininstr_st5_GLOBAL_SET x)] (mk_functype t2 t3)"
      using assms(4) inv_seq[of s C _ t1 t3 "[admininstr_val v_val]" "[admininstr_sc5 (admininstr_st5_GLOBAL_SET x)]"] by fastforce

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
        "Instrs_ok2 s C [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_ref v_ref, admininstr_sc5 (admininstr_st5_TABLE_SET x)] (mk_functype t_1_lst t_2_lst)"
        "t_inst_match C C'"
shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?x = "proj_uN_0 x"
  have ctx_table_eq: "(context_TABLES C) = (context_TABLES C')" using assms(7) t_inst_match_def by auto

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
    using types_preserved_table_set_aux[OF assms(6)] tab_type by simp+
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

(*Generic lemmas: updating a single store slot*)
lemma list_update_func_out_of_range:
  assumes "length xs \<le> i"
  shows "list_update_func xs i g = xs"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases i) auto
qed

lemma list_all_list_update_func_gen:
  assumes "list_all P xs"
          "i < length xs \<Longrightarrow> P (g (xs ! i))"
  shows "list_all P (list_update_func xs i g)"
  using assms list_all_list_update_func list_update_func_out_of_range
  by (metis not_le)

lemma list_all2_list_update_func_gen:
  assumes "list_all2 P xs ys"
          "\<And>x y. P x y \<Longrightarrow> Q x y"
          "i < length xs \<Longrightarrow> Q (g (xs ! i)) y'"
  shows "list_all2 Q (list_update_func xs i g) (ys[i := y'])"
proof (cases "i < length xs")
  case True
  have len: "length xs = length ys" using assms(1) list_all2_lengthD by blast
  show ?thesis
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length (list_update_func xs i g) = length (ys[i := y'])"
      using len list_update_func_length[of xs i g] by simp
  next
    fix k assume "k < length (list_update_func xs i g)"
    then have k: "k < length xs" using list_update_func_length by metis
    show "Q (list_update_func xs i g ! k) (ys[i := y'] ! k)"
    proof (cases "k = i")
      case True
      then show ?thesis using assms(3) \<open>i < length xs\<close> list_update_func_nth[of i xs g] len by simp
    next
      case False
      then have "list_update_func xs i g ! k = xs ! k" "ys[i := y'] ! k = ys ! k"
        using \<open>i < length xs\<close> list_update_func_nth_neq by auto
      then show ?thesis using assms(1,2) k list_all2_nthD by metis
    qed
  qed
next
  case False
  then have "length ys \<le> i" using assms(1) list_all2_lengthD by fastforce
  then show ?thesis using False assms(1,2) list_update_func_out_of_range list_all2_mono
    by (metis list_update_beyond not_le)
qed

lemma holds_upto_list_update_func:
  assumes "list_all P xs"
          "\<And>x. P x \<Longrightarrow> Ext x x"
          "i < length xs \<Longrightarrow> Ext (xs ! i) (g (xs ! i))"
  shows "holds_upto (\<lambda>k. Ext (xs ! k) (list_update_func xs i g ! k)) (length xs)"
  unfolding holds_upto_def
proof (intro allI impI)
  fix k assume k: "k < length xs"
  show "Ext (xs ! k) (list_update_func xs i g ! k)"
  proof (cases "i < length xs")
    case True
    show ?thesis
    proof (cases "k = i")
      case True
      then show ?thesis using assms(3) \<open>i < length xs\<close> list_update_func_nth[of i xs g] by simp
    next
      case False
      then show ?thesis
        using assms(1,2) k \<open>i < length xs\<close> list_update_func_nth_neq list_all_length by metis
    qed
  next
    case False
    then show ?thesis
      using assms(1,2) k list_update_func_out_of_range list_all_length by (metis not_le)
  qed
qed

lemma holds_upto_refl:
  assumes "list_all P xs" "\<And>x. P x \<Longrightarrow> Ext x x"
  shows "holds_upto (\<lambda>k. Ext (xs ! k) (xs ! k)) (length xs)"
  using assms by (simp add: holds_upto_def list_all_length)

lemma list_all_True: "list_all (\<lambda>_. True) xs"
  by (simp add: list_all_iff)

lemma elem_extension_refl': "True \<Longrightarrow> Extend_eleminst e e"
  by (rule elem_extension_refl)

lemma Store_ok_wf: "Store_ok s \<Longrightarrow> wf_store s"
  by (auto elim: Store_ok.cases)

lemma wf_store_parts:
  assumes "wf_store s"
  shows "list_all wf_funcinst (store_FUNCS s)" "list_all wf_globalinst (store_GLOBALS s)"
        "list_all wf_tableinst (store_TABLES s)" "list_all wf_meminst (store_MEMS s)"
        "list_all wf_datainst (store_DATAS s)"
  using assms by (auto elim: wf_store.cases)

lemma wf_store_intro:
  assumes "list_all wf_funcinst (store_FUNCS s)" "list_all wf_globalinst (store_GLOBALS s)"
          "list_all wf_tableinst (store_TABLES s)" "list_all wf_meminst (store_MEMS s)"
          "list_all wf_datainst (store_DATAS s)"
  shows "wf_store s"
  using assms by (cases s) (auto intro!: store_case_underscore)

lemma Extend_tableinst_wf: "Extend_tableinst t t' \<Longrightarrow> wf_tableinst t'"
  by (auto elim: Extend_tableinst.cases)

lemma Extend_meminst_wf: "Extend_meminst m m' \<Longrightarrow> wf_meminst m'"
  by (auto elim: Extend_meminst.cases)

lemma Extend_datainst_wf: "Extend_datainst d d' \<Longrightarrow> wf_datainst d'"
  by (auto elim: Extend_datainst.cases)

lemma Meminst_ok_wf_memtype: "Meminst_ok s m mt \<Longrightarrow> wf_memtype mt"
  by (auto elim: Meminst_ok.cases)

lemma Tableinst_ok_wf_tabletype: "Tableinst_ok s t tt \<Longrightarrow> wf_tabletype tt"
  by (auto elim: Tableinst_ok.cases)

lemma Store_ok_intro:
  assumes "wf_store s"
    "list_all2 (Globalinst_ok s) (store_GLOBALS s) gts"
    "list_all2 (Meminst_ok s) (store_MEMS s) mts"
    "list_all2 (Tableinst_ok s) (store_TABLES s) tts"
    "list_all2 (Funcinst_ok s) (store_FUNCS s) fts"
    "list_all2 (Datainst_ok s) (store_DATAS s) dts"
    "list_all2 (Eleminst_ok s) (store_ELEMS s) ets"
  shows "Store_ok s"
proof -
  have "list_all wf_memtype mts"
    using assms(3) Meminst_ok_wf_memtype by (induction rule: list_all2_induct) auto
  moreover have "list_all wf_tabletype tts"
    using assms(4) Tableinst_ok_wf_tabletype by (induction rule: list_all2_induct) auto
  ultimately show ?thesis
    using assms
  proof (cases s)
    case (fields fs gs ts ms es ds)
    show ?thesis
      apply (rule mk_Store_ok[where globaltype_lst = gts and memtype_lst = mts and tabletype_lst = tts
          and functype_lst = fts and datatype_lst = dts and elemtype_lst = ets])
      using assms \<open>list_all wf_memtype mts\<close> \<open>list_all wf_tabletype tts\<close> fields
      by (auto simp: list_all2_lengthD)
  qed
qed

lemma Store_ok_lists_extend:
  assumes "Store_ok s" "Extend_store s s'"
  obtains gts mts tts fts dts ets where
    "list_all2 (Globalinst_ok s') (store_GLOBALS s) gts"
    "list_all2 (Meminst_ok s')    (store_MEMS s)    mts"
    "list_all2 (Tableinst_ok s')  (store_TABLES s)  tts"
    "list_all2 (Funcinst_ok s')   (store_FUNCS s)   fts"
    "list_all2 (Datainst_ok s')   (store_DATAS s)   dts"
    "list_all2 (Eleminst_ok s')   (store_ELEMS s)   ets"
    "list_all2 (Globalinst_ok s)  (store_GLOBALS s) gts"
    "list_all2 (Meminst_ok s)     (store_MEMS s)    mts"
    "list_all2 (Tableinst_ok s)   (store_TABLES s)  tts"
    "list_all2 (Funcinst_ok s)    (store_FUNCS s)   fts"
    "list_all2 (Datainst_ok s)    (store_DATAS s)   dts"
    "list_all2 (Eleminst_ok s)    (store_ELEMS s)   ets"
proof -
  obtain gts mts tts fts dts ets where L:
    "list_all2 (Globalinst_ok s)  (store_GLOBALS s) gts"
    "list_all2 (Meminst_ok s)     (store_MEMS s)    mts"
    "list_all2 (Tableinst_ok s)   (store_TABLES s)  tts"
    "list_all2 (Funcinst_ok s)    (store_FUNCS s)   fts"
    "list_all2 (Datainst_ok s)    (store_DATAS s)   dts"
    "list_all2 (Eleminst_ok s)    (store_ELEMS s)   ets"
    using assms(1) by (cases rule: Store_ok.cases) auto
  show ?thesis
    by (rule that[OF
          list_all2_mono[OF L(1) store_extension_Globalinst_ok[OF _ assms(2)]]
          list_all2_mono[OF L(2) store_extension_Meminst_ok[OF _ assms(2)]]
          list_all2_mono[OF L(3) store_extension_Tableinst_ok[OF _ assms(2)]]
          list_all2_mono[OF L(4) store_extension_Funcinst_ok[OF _ assms(2)]]
          list_all2_mono[OF L(5) store_extension_Datainst_ok[OF _ assms(2)]]
          list_all2_mono[OF L(6) store_extension_Eleminst_ok[OF _ assms(2)]]
          L])
qed

lemma tables_update_store_extension:
  assumes "Store_ok s"
          "s' = s\<lparr>store_TABLES := list_update_func (store_TABLES s) a g\<rparr>"
          "\<And>tt. a < length (store_TABLES s) \<Longrightarrow> Tableinst_ok s (store_TABLES s ! a) tt \<Longrightarrow>
                 Extend_tableinst (store_TABLES s ! a) (g (store_TABLES s ! a))"
          "\<And>tt. a < length (store_TABLES s) \<Longrightarrow> Extend_store s s' \<Longrightarrow> Tableinst_ok s (store_TABLES s ! a) tt \<Longrightarrow>
                 \<exists>tt'. Tableinst_ok s' (g (store_TABLES s ! a)) tt'"
  shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?xs = "store_TABLES s"
  have wf_s: "wf_store s" using assms(1) Store_ok_wf by simp
  note wf = wf_store_parts[OF wf_s]
  obtain tts0 where tts0: "list_all2 (Tableinst_ok s) ?xs tts0"
    using assms(1) by (cases rule: Store_ok.cases) auto
  have ext_a: "a < length ?xs \<Longrightarrow> Extend_tableinst (?xs ! a) (g (?xs ! a))"
    using assms(3) tts0 list_all2_nthD by blast
  have wf_s': "wf_store s'"
    using wf assms(2) ext_a Extend_tableinst_wf
    by (auto intro!: wf_store_intro list_all_list_update_func_gen)
  have ext: "Extend_store s s'"
    apply (rule mk_Extend_store)
    using assms(2) wf_s wf_s'
      holds_upto_list_update_func[where Ext = Extend_tableinst and i = a and g = g, OF wf(3) tab_extension_refl ext_a]
      holds_upto_refl[where Ext = Extend_funcinst, OF wf(1) func_extension_refl] holds_upto_refl[where Ext = Extend_globalinst, OF wf(2) global_extension_refl]
      holds_upto_refl[where Ext = Extend_meminst, OF wf(4) mem_extension_refl] holds_upto_refl[where Ext = Extend_datainst, OF wf(5) data_extension_refl]
    by (simp_all add: holds_upto_def list_update_func_length elem_extension_refl)
  obtain gts mts tts fts dts ets where L:
    "list_all2 (Globalinst_ok s') (store_GLOBALS s) gts"
    "list_all2 (Meminst_ok s')    (store_MEMS s)    mts"
    "list_all2 (Tableinst_ok s')  (store_TABLES s)  tts"
    "list_all2 (Funcinst_ok s')   (store_FUNCS s)   fts"
    "list_all2 (Datainst_ok s')   (store_DATAS s)   dts"
    "list_all2 (Eleminst_ok s')   (store_ELEMS s)   ets"
    "list_all2 (Tableinst_ok s)   (store_TABLES s)  tts"
    using Store_ok_lists_extend[OF assms(1) ext] by metis
  obtain tt' where tt': "a < length ?xs \<Longrightarrow> Tableinst_ok s' (g (?xs ! a)) tt'"
    using assms(4) ext L(7) list_all2_nthD by blast
  have "list_all2 (Tableinst_ok s') (store_TABLES s') (tts[a := tt'])"
    using list_all2_list_update_func_gen[where Q = "Tableinst_ok s'" and i = a and g = g, OF L(7) store_extension_Tableinst_ok[OF _ ext] tt'] assms(2) by simp
  then have "Store_ok s'"
    using Store_ok_intro[OF wf_s', of gts mts "tts[a := tt']" fts dts ets] L(1,2,4,5,6) assms(2) by simp
  then show ?thesis using ext by simp
qed

lemma mems_update_store_extension:
  assumes "Store_ok s"
          "s' = s\<lparr>store_MEMS := list_update_func (store_MEMS s) a g\<rparr>"
          "\<And>mt. a < length (store_MEMS s) \<Longrightarrow> Meminst_ok s (store_MEMS s ! a) mt \<Longrightarrow>
                 Extend_meminst (store_MEMS s ! a) (g (store_MEMS s ! a))"
          "\<And>mt. a < length (store_MEMS s) \<Longrightarrow> Extend_store s s' \<Longrightarrow> Meminst_ok s (store_MEMS s ! a) mt \<Longrightarrow>
                 \<exists>mt'. Meminst_ok s' (g (store_MEMS s ! a)) mt'"
  shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?xs = "store_MEMS s"
  have wf_s: "wf_store s" using assms(1) Store_ok_wf by simp
  note wf = wf_store_parts[OF wf_s]
  obtain mts0 where mts0: "list_all2 (Meminst_ok s) ?xs mts0"
    using assms(1) by (cases rule: Store_ok.cases) auto
  have ext_a: "a < length ?xs \<Longrightarrow> Extend_meminst (?xs ! a) (g (?xs ! a))"
    using assms(3) mts0 list_all2_nthD by blast
  have wf_s': "wf_store s'"
    using wf assms(2) ext_a Extend_meminst_wf
    by (auto intro!: wf_store_intro list_all_list_update_func_gen)
  have ext: "Extend_store s s'"
    apply (rule mk_Extend_store)
    using assms(2) wf_s wf_s'
      holds_upto_list_update_func[where Ext = Extend_meminst and i = a and g = g, OF wf(4) mem_extension_refl ext_a]
      holds_upto_refl[where Ext = Extend_funcinst, OF wf(1) func_extension_refl] holds_upto_refl[where Ext = Extend_globalinst, OF wf(2) global_extension_refl]
      holds_upto_refl[where Ext = Extend_tableinst, OF wf(3) tab_extension_refl] holds_upto_refl[where Ext = Extend_datainst, OF wf(5) data_extension_refl]
    by (simp_all add: holds_upto_def list_update_func_length elem_extension_refl)
  obtain gts mts tts fts dts ets where L:
    "list_all2 (Globalinst_ok s') (store_GLOBALS s) gts"
    "list_all2 (Meminst_ok s')    (store_MEMS s)    mts"
    "list_all2 (Tableinst_ok s')  (store_TABLES s)  tts"
    "list_all2 (Funcinst_ok s')   (store_FUNCS s)   fts"
    "list_all2 (Datainst_ok s')   (store_DATAS s)   dts"
    "list_all2 (Eleminst_ok s')   (store_ELEMS s)   ets"
    "list_all2 (Meminst_ok s)     (store_MEMS s)    mts"
    using Store_ok_lists_extend[OF assms(1) ext] by metis
  obtain mt' where mt': "a < length ?xs \<Longrightarrow> Meminst_ok s' (g (?xs ! a)) mt'"
    using assms(4) ext L(7) list_all2_nthD by blast
  have "list_all2 (Meminst_ok s') (store_MEMS s') (mts[a := mt'])"
    using list_all2_list_update_func_gen[where Q = "Meminst_ok s'" and i = a and g = g, OF L(7) store_extension_Meminst_ok[OF _ ext] mt'] assms(2) by simp
  then have "Store_ok s'"
    using Store_ok_intro[OF wf_s', of gts "mts[a := mt']" tts fts dts ets] L(1,3,4,5,6) assms(2) by simp
  then show ?thesis using ext by simp
qed

lemma elems_update_store_extension:
  assumes "Store_ok s"
          "s' = s\<lparr>store_ELEMS := list_update_func (store_ELEMS s) a g\<rparr>"
          "a < length (store_ELEMS s) \<Longrightarrow> Extend_eleminst (store_ELEMS s ! a) (g (store_ELEMS s ! a))"
          "\<And>et. a < length (store_ELEMS s) \<Longrightarrow> Extend_store s s' \<Longrightarrow> Eleminst_ok s (store_ELEMS s ! a) et \<Longrightarrow>
                 \<exists>et'. Eleminst_ok s' (g (store_ELEMS s ! a)) et'"
  shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?xs = "store_ELEMS s"
  have wf_s: "wf_store s" using assms(1) Store_ok_wf by simp
  note wf = wf_store_parts[OF wf_s]
  have wf_s': "wf_store s'"
    using wf assms(2) by (auto intro!: wf_store_intro)
  have ext: "Extend_store s s'"
    apply (rule mk_Extend_store)
    using assms(2) wf_s wf_s'
      holds_upto_list_update_func[where P = "\<lambda>_. True" and Ext = Extend_eleminst and i = a and g = g, OF list_all_True elem_extension_refl' assms(3)]
      holds_upto_refl[where Ext = Extend_funcinst, OF wf(1) func_extension_refl] holds_upto_refl[where Ext = Extend_globalinst, OF wf(2) global_extension_refl]
      holds_upto_refl[where Ext = Extend_tableinst, OF wf(3) tab_extension_refl] holds_upto_refl[where Ext = Extend_meminst, OF wf(4) mem_extension_refl]
      holds_upto_refl[where Ext = Extend_datainst, OF wf(5) data_extension_refl]
    by (simp_all add: holds_upto_def list_update_func_length list_all_iff)
  obtain gts mts tts fts dts ets where L:
    "list_all2 (Globalinst_ok s') (store_GLOBALS s) gts"
    "list_all2 (Meminst_ok s')    (store_MEMS s)    mts"
    "list_all2 (Tableinst_ok s')  (store_TABLES s)  tts"
    "list_all2 (Funcinst_ok s')   (store_FUNCS s)   fts"
    "list_all2 (Datainst_ok s')   (store_DATAS s)   dts"
    "list_all2 (Eleminst_ok s')   (store_ELEMS s)   ets"
    "list_all2 (Eleminst_ok s)    (store_ELEMS s)   ets"
    using Store_ok_lists_extend[OF assms(1) ext] by metis
  obtain et' where et': "a < length ?xs \<Longrightarrow> Eleminst_ok s' (g (?xs ! a)) et'"
    using assms(4) ext L(7) list_all2_nthD by blast
  have "list_all2 (Eleminst_ok s') (store_ELEMS s') (ets[a := et'])"
    using list_all2_list_update_func_gen[where Q = "Eleminst_ok s'" and i = a and g = g, OF L(7) store_extension_Eleminst_ok[OF _ ext] et'] assms(2) by simp
  then have "Store_ok s'"
    using Store_ok_intro[OF wf_s', of gts mts tts fts dts "ets[a := et']"] L(1,2,3,4,5) assms(2) by simp
  then show ?thesis using ext by simp
qed

lemma datas_update_store_extension:
  assumes "Store_ok s"
          "s' = s\<lparr>store_DATAS := list_update_func (store_DATAS s) a g\<rparr>"
          "a < length (store_DATAS s) \<Longrightarrow> Extend_datainst (store_DATAS s ! a) (g (store_DATAS s ! a))"
          "\<And>dt. a < length (store_DATAS s) \<Longrightarrow> Extend_store s s' \<Longrightarrow> Datainst_ok s (store_DATAS s ! a) dt \<Longrightarrow>
                 \<exists>dt'. Datainst_ok s' (g (store_DATAS s ! a)) dt'"
  shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?xs = "store_DATAS s"
  have wf_s: "wf_store s" using assms(1) Store_ok_wf by simp
  note wf = wf_store_parts[OF wf_s]
  have wf_s': "wf_store s'"
    using wf assms(2,3) Extend_datainst_wf
    by (auto intro!: wf_store_intro list_all_list_update_func_gen)
  have ext: "Extend_store s s'"
    apply (rule mk_Extend_store)
    using assms(2) wf_s wf_s'
      holds_upto_list_update_func[where Ext = Extend_datainst and i = a and g = g, OF wf(5) data_extension_refl assms(3)]
      holds_upto_refl[where Ext = Extend_funcinst, OF wf(1) func_extension_refl] holds_upto_refl[where Ext = Extend_globalinst, OF wf(2) global_extension_refl]
      holds_upto_refl[where Ext = Extend_tableinst, OF wf(3) tab_extension_refl] holds_upto_refl[where Ext = Extend_meminst, OF wf(4) mem_extension_refl]
    by (simp_all add: holds_upto_def list_update_func_length elem_extension_refl)
  obtain gts mts tts fts dts ets where L:
    "list_all2 (Globalinst_ok s') (store_GLOBALS s) gts"
    "list_all2 (Meminst_ok s')    (store_MEMS s)    mts"
    "list_all2 (Tableinst_ok s')  (store_TABLES s)  tts"
    "list_all2 (Funcinst_ok s')   (store_FUNCS s)   fts"
    "list_all2 (Datainst_ok s')   (store_DATAS s)   dts"
    "list_all2 (Eleminst_ok s')   (store_ELEMS s)   ets"
    "list_all2 (Datainst_ok s)    (store_DATAS s)   dts"
    using Store_ok_lists_extend[OF assms(1) ext] by metis
  obtain dt' where dt': "a < length ?xs \<Longrightarrow> Datainst_ok s' (g (?xs ! a)) dt'"
    using assms(4) ext L(7) list_all2_nthD by blast
  have "list_all2 (Datainst_ok s') (store_DATAS s') (dts[a := dt'])"
    using list_all2_list_update_func_gen[where Q = "Datainst_ok s'" and i = a and g = g, OF L(7) store_extension_Datainst_ok[OF _ ext] dt'] assms(2) by simp
  then have "Store_ok s'"
    using Store_ok_intro[OF wf_s', of gts mts tts fts "dts[a := dt']" ets] L(1,2,3,4,6) assms(2) by simp
  then show ?thesis using ext by simp
qed

(*elem_drop*)
lemma elem_drop_store_extension:
  assumes "with_elem (mk_state s f) x [] = mk_state s' f'"
          "Store_ok s"
  shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?a = "ELEMS (frame_MODULE f) ! proj_uN_0 x"
  have s'_eq: "s' = s\<lparr>store_ELEMS := list_update_func (store_ELEMS s) ?a (\<lambda>e. e\<lparr>eleminst_REFS := []\<rparr>)\<rparr>"
    using assms(1) with_elem.psimps with_elem.domintros by auto
  show ?thesis
  proof (rule elems_update_store_extension[OF assms(2) s'_eq])
    show "Extend_eleminst (store_ELEMS s ! ?a) ((store_ELEMS s ! ?a)\<lparr>eleminst_REFS := []\<rparr>)"
      by (cases "store_ELEMS s ! ?a") (auto intro: mk_Extend_eleminst)
  next
    fix et
    assume "Extend_store s s'"
    then have wf': "wf_store s'" using store_extension_wf by blast
    show "\<exists>et'. Eleminst_ok s' ((store_ELEMS s ! ?a)\<lparr>eleminst_REFS := []\<rparr>) et'"
    proof (cases "store_ELEMS s ! ?a")
      case (fields rt refs)
      then show ?thesis
        using wf' mk_Eleminst_ok[where s = s' and ref_lst = "[]" and rt = rt] by auto
    qed
  qed
qed

(*data_drop*)
lemma data_drop_store_extension:
  assumes "with_data (mk_state s f) x [] = mk_state s' f'"
          "Store_ok s"
  shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?a = "DATAS (frame_MODULE f) ! proj_uN_0 x"
  have s'_eq: "s' = s\<lparr>store_DATAS := list_update_func (store_DATAS s) ?a (\<lambda>d. d\<lparr>datainst_BYTES := []\<rparr>)\<rparr>"
    using assms(1) with_data.psimps with_data.domintros by auto
  have wf_empty: "wf_datainst \<lparr>datainst_BYTES = []\<rparr>"
    by (auto intro: datainst_case_underscore)
  show ?thesis
  proof (rule datas_update_store_extension[OF assms(2) s'_eq])
    assume "?a < length (store_DATAS s)"
    then have "wf_datainst (store_DATAS s ! ?a)"
      using wf_store_parts(5)[OF Store_ok_wf[OF assms(2)]] list_all_length by blast
    then show "Extend_datainst (store_DATAS s ! ?a) ((store_DATAS s ! ?a)\<lparr>datainst_BYTES := []\<rparr>)"
      using wf_empty by (cases "store_DATAS s ! ?a") (auto intro!: mk_Extend_datainst datainst_case_underscore)
  next
    fix dt
    assume "Extend_store s s'"
    then show "\<exists>dt'. Datainst_ok s' ((store_DATAS s ! ?a)\<lparr>datainst_BYTES := []\<rparr>) dt'"
      using store_extension_wf wf_empty mk_Datainst_ok[where s = s' and b_lst = "[]"]
      by (cases "store_DATAS s ! ?a") auto
  qed
qed

lemma length_repeat: "length (repeat n x) = n"
  by (induction n) auto

lemma list_all_repeat: "P x \<Longrightarrow> list_all P (repeat n x)"
  by (induction n) auto

lemma map_option_mk_uN_inj: "map_option mk_uN x = map_option mk_uN y \<Longrightarrow> x = y"
  by (cases x; cases y) auto

lemma proj_uN_0_mk_uN[simp]: "proj_uN_0 (mk_uN n) = n"
  by (simp add: proj_uN_0.psimps proj_uN_0.domintros)

(*memory_grow*)
lemma memory_grow_store_extension:
  assumes "fun_growmemory (fun_mem (mk_state s f) (mk_uN 0)) v_n (Some mi)"
          "with_meminst (mk_state s f) (mk_uN 0) mi = mk_state s' f'"
          "Store_ok s"
  shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?a = "MEMS (frame_MODULE f) ! 0"
  have s'_eq: "s' = s\<lparr>store_MEMS := list_update_func (store_MEMS s) ?a (\<lambda>_. mi)\<rparr>"
    using assms(2) with_meminst.psimps with_meminst.domintros by auto
  have mem_eq: "fun_mem (mk_state s f) (mk_uN 0) = store_MEMS s ! ?a"
    using fun_mem.psimps fun_mem.domintros by auto
  obtain i j_opt b_lst i' where
    old: "store_MEMS s ! ?a = \<lparr>meminst_TYPE = PAGE (mk_limits i j_opt), BYTES = b_lst\<rparr>" and
    i': "i' = length b_lst div (64 * Ki) + v_n" and
    j_bound: "list_all (\<lambda>j. i' \<le> proj_uN_0 j) (option_to_list j_opt)" and
    i'_bound: "i' \<le> 2 ^ 16" and
    new: "mi = \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN i') j_opt), BYTES = b_lst @ repeat (v_n * (64 * Ki)) (mk_byte 0)\<rparr>" and
    wf_old: "wf_meminst (store_MEMS s ! ?a)" and
    wf_new: "wf_meminst mi"
    using assms(1) mem_eq by (cases rule: fun_growmemory.cases) (rule that[OF sym], auto)

  have old_ok: "\<exists>n m_opt. i = mk_uN n \<and> j_opt = map_option mk_uN m_opt \<and> length b_lst = n * (64 * Ki) \<and>
                  Memtype_ok (PAGE (mk_limits (mk_uN n) (map_option mk_uN m_opt)))"
    if "Meminst_ok s (store_MEMS s ! ?a) mt" for mt
    using that old by (cases rule: Meminst_ok.cases) auto

  show ?thesis
  proof (rule mems_update_store_extension[OF assms(3) s'_eq])
    fix mt
    assume "Meminst_ok s (store_MEMS s ! ?a) mt"
    then obtain n m_opt where
      i_eq: "i = mk_uN n" and j_eq: "j_opt = map_option mk_uN m_opt" and len: "length b_lst = n * (64 * Ki)"
      using old_ok by blast
    have "i' = n + v_n" using i' len by (simp add: Ki_def)
    then show "Extend_meminst (store_MEMS s ! ?a) mi"
      using old new wf_old wf_new i_eq j_eq mk_Extend_meminst[of n i' b_lst "b_lst @ repeat (v_n * (64 * Ki)) (mk_byte 0)" m_opt]
      by simp
  next
    fix mt
    assume ext: "Extend_store s s'" and ok: "Meminst_ok s (store_MEMS s ! ?a) mt"
    then obtain n m_opt where
      i_eq: "i = mk_uN n" and j_eq: "j_opt = map_option mk_uN m_opt" and len: "length b_lst = n * (64 * Ki)" and
      mt_ok: "Memtype_ok (PAGE (mk_limits (mk_uN n) (map_option mk_uN m_opt)))"
      using old_ok by blast
    have i'_eq: "i' = n + v_n" using i' len by (simp add: Ki_def)
    have m_le: "list_all (\<lambda>m. m \<le> 2 ^ 16) (option_to_list m_opt)"
      using mt_ok
      by (auto elim!: Memtype_ok.cases Limits_ok.cases dest!: map_option_mk_uN_inj simp: list_all_iff)
    have i'_le: "list_all (\<lambda>m. i' \<le> m) (option_to_list m_opt)"
      using j_bound j_eq by (cases m_opt) auto
    have wf_lim: "wf_limits (mk_limits (mk_uN i') (map_option mk_uN m_opt))"
      using wf_new new j_eq by (auto elim!: wf_meminst.cases wf_memtype.cases)
    have lim_ok: "Limits_ok (mk_limits (mk_uN i') (map_option mk_uN m_opt)) (2 ^ 16)"
      using i'_bound m_le i'_le wf_lim
      by (intro mk_Limits_ok) (auto simp: list_all_iff)
    have wf_mt: "wf_memtype (PAGE (mk_limits (mk_uN i') (map_option mk_uN m_opt)))"
      using wf_lim by (rule memtype_case_0)
    have "length (b_lst @ repeat (v_n * (64 * Ki)) (mk_byte 0)) = i' * (64 * Ki)"
      using len i'_eq by (simp add: length_repeat algebra_simps)
    then have "Meminst_ok s' mi (PAGE (mk_limits (mk_uN i') (map_option mk_uN m_opt)))"
      using new j_eq wf_new wf_mt lim_ok store_extension_wf[OF ext]
      by (auto intro!: mk_Meminst_ok mk_Memtype_ok)
    then show "\<exists>mt'. Meminst_ok s' mi mt'" by blast
  qed
qed

(*table_grow*)
lemma types_preserved_table_grow_aux:
assumes "Instrs_ok2 s C [
          admininstr_ref v_ref,
          admininstr_sc1 (admininstr_st1_CONST I32 c),
          admininstr_sc5 (admininstr_st5_TABLE_GROW x)
        ] ft"
shows "\<exists>lim rt.
         proj_uN_0 x < length (context_TABLES C) \<and>
         (context_TABLES C) ! (proj_uN_0 x) = mk_tabletype lim rt \<and>
         Ref_ok s v_ref rt"
proof (cases ft)
  case (mk_functype t1 t3)
  obtain t2 where
    admin_ref_const: "Instrs_ok2 s C [admininstr_ref v_ref, admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" and
    admin_table_grow: "Instrs_ok2 s C [admininstr_sc5 (admininstr_st5_TABLE_GROW x)] (mk_functype t2 t3)"
    using assms inv_seq[of s C _ t1 t3 "[admininstr_ref v_ref, admininstr_sc1 (admininstr_st1_CONST I32 c)]" "[admininstr_sc5 (admininstr_st5_TABLE_GROW x)]"] mk_functype
    by fastforce

  from admin_table_grow obtain t_1_lst t_2_lst where
    ok_tg2: "Instr_ok2 s C (admininstr_sc5 (admininstr_st5_TABLE_GROW x)) (mk_functype t_1_lst t_2_lst)" and
    st: "mk_instrtype t_1_lst t_2_lst <ti: mk_instrtype t2 t3"
    using inv_one_admininstr by fast

  then have "Instr_ok C (instr_sc5 (TABLE_GROW x)) (mk_functype t_1_lst t_2_lst)"
    using inv_plain admininstr_instr.domintros admininstr_instr.psimps by fastforce
  then obtain lim rt where
    x_lt: "proj_uN_0 x < length (context_TABLES C)" and
    tab_C: "(context_TABLES C) ! (proj_uN_0 x) = mk_tabletype lim rt" and
    ft_eq: "mk_functype (mk_list [valtype_reftype rt, valtype_I32]) (mk_list [valtype_I32]) = mk_functype t_1_lst t_2_lst"
    using inv_table_grow by blast

  have subv: "mk_instrtype (mk_list []) (mk_list [typeofval (val_ref v_ref), valtype_I32]) <ti: mk_instrtype t1 t2"
    using inv_const_list[of s C "[_,_]" t1 t2 "[val_ref v_ref, val_CONST I32 c]"] admin_ref_const
      admininstr_val.domintros admininstr_val.psimps admininstr_val_ref
      valtype_numtype.domintros valtype_numtype.psimps typeofval.domintros typeofval.psimps
    by fastforce

  have "Resulttype_sub (mk_list [typeofval (val_ref v_ref), valtype_I32]) (mk_list [valtype_reftype rt, valtype_I32])"
    using st ft_eq produce_consume[of "[typeofval (val_ref v_ref), valtype_I32]" t1 t2 "[]" "[valtype_reftype rt, valtype_I32]" "[valtype_I32]" t3] subv
    by auto
  then have val_sub: "Valtype_sub (typeofval (val_ref v_ref)) (valtype_reftype rt)"
    by (induction "mk_list [typeofval (val_ref v_ref), valtype_I32]" "mk_list [valtype_reftype rt, valtype_I32]" rule: Resulttype_sub.induct) auto

  obtain t_ref_out where
    "Instrs_ok2 s C [admininstr_ref v_ref] (mk_functype t1 t_ref_out)"
    using inv_seq[of s C _ t1 t2 "[admininstr_ref v_ref]" "[admininstr_sc1 (admininstr_st1_CONST I32 c)]"] admin_ref_const
    by fastforce
  then obtain tr1 tr2 where
    "Instr_ok2 s C (admininstr_ref v_ref) (mk_functype tr1 tr2)"
    using inv_one_admininstr by fast
  then obtain rt' where ref_ok: "Ref_ok s v_ref rt'"
    using inv_ref by blast
  then have "typeofval (val_ref v_ref) = valtype_reftype rt'"
    using ref_ok_agree by simp
  then have "Valtype_sub (valtype_reftype rt') (valtype_reftype rt)"
    using val_sub by simp
  then have "valtype_reftype rt' = valtype_reftype rt"
  proof (cases rule: Valtype_sub.cases)
    case refl
    then show ?thesis by simp
  next
    case bot
    then show ?thesis
      by (cases rt') (auto simp add: valtype_reftype.psimps valtype_reftype.domintros)
  qed
  then have "rt' = rt"
    by (cases rt; cases rt') (auto simp add: valtype_reftype.psimps valtype_reftype.domintros)
  then show ?thesis using x_lt tab_C ref_ok by blast
qed

lemma table_grow_store_extension:
assumes "fun_growtable (fun_table (mk_state s f) x) v_n v_ref (Some ti)"
        "with_tableinst (mk_state s f) x ti = mk_state s' f'"
        "Store_ok s"
        "Moduleinst_ok s (frame_MODULE f) C'"
        "Instrs_ok2 s C [admininstr_ref v_ref, admininstr_sc1 (admininstr_st1_CONST I32 c), admininstr_sc5 (admininstr_st5_TABLE_GROW x)] ft"
        "t_inst_match C C'"
shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?x = "proj_uN_0 x"
  let ?a = "TABLES (frame_MODULE f) ! ?x"
  obtain lim rt where
    x_lt: "?x < length (context_TABLES C)" and
    tab_C: "context_TABLES C ! ?x = mk_tabletype lim rt" and
    ref_ok: "Ref_ok s v_ref rt"
    using types_preserved_table_grow_aux[OF assms(5)] by blast
  have ctx_eq: "context_TABLES C' = context_TABLES C" using assms(6) t_inst_match_def by auto
  obtain tableaddr_lst tabletype_lst where
     tabs_mod: "TABLES (frame_MODULE f) = tableaddr_lst" and
     tabs_ctx: "context_TABLES C' = tabletype_lst" and
     tabs_ok: "list_all2 (\<lambda>ta tt. Externaddr_ok s (externaddr_TABLE ta) (TABLE tt)) tableaddr_lst tabletype_lst"
    using assms(4) by (cases rule: Moduleinst_ok.cases) auto
  have "Externaddr_ok s (externaddr_TABLE (tableaddr_lst ! ?x)) (TABLE (tabletype_lst ! ?x))"
    using list_all2_nthD[OF tabs_ok] list_all2_lengthD[OF tabs_ok] x_lt ctx_eq tabs_ctx by simp
  then have ext_ok: "Externaddr_ok s (externaddr_TABLE ?a) (TABLE (mk_tabletype lim rt))"
    using tabs_mod tabs_ctx ctx_eq tab_C by simp
  obtain v rtv limv limup where
    "store_TABLES s ! ?a = v" and v_ty: "tableinst_TYPE v = mk_tabletype limv rtv" and
    up: "TABLE (mk_tabletype limup rtv) = TABLE (mk_tabletype lim rt)"
    using inv_Externaddr_ok_table[OF ext_ok HOL.refl] by blast
  then have a_ty: "tableinst_TYPE (store_TABLES s ! ?a) = mk_tabletype limv rt"
    by simp

  have tab_eq: "fun_table (mk_state s f) x = store_TABLES s ! ?a"
    using fun_table.psimps fun_table.domintros by auto
  have s'_eq: "s' = s\<lparr>store_TABLES := list_update_func (store_TABLES s) ?a (\<lambda>_. ti)\<rparr>"
    using assms(2) with_tableinst.psimps with_tableinst.domintros by auto
  obtain i j_opt rt0 r_lst i' where
    old: "store_TABLES s ! ?a = \<lparr>tableinst_TYPE = mk_tabletype (mk_limits i j_opt) rt0, REFS = r_lst\<rparr>" and
    i': "i' = length r_lst + v_n" and
    j_bound: "list_all (\<lambda>j. i' \<le> proj_uN_0 j) (option_to_list j_opt)" and
    new: "ti = \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN i') j_opt) rt0, REFS = r_lst @ repeat v_n v_ref\<rparr>" and
    wf_old: "wf_tableinst (store_TABLES s ! ?a)" and
    wf_new: "wf_tableinst ti"
    using assms(1) tab_eq by (cases rule: fun_growtable.cases) (rule that[OF sym], auto)
  have rt0: "rt0 = rt" using a_ty old by simp

  have old_ok: "\<exists>n m_opt. i = mk_uN n \<and> j_opt = map_option mk_uN m_opt \<and> length r_lst = n \<and>
                  list_all (\<lambda>r. Ref_ok s r rt0) r_lst"
    if "Tableinst_ok s (store_TABLES s ! ?a) tt" for tt
    using that old by (cases rule: Tableinst_ok.cases) auto

  show ?thesis
  proof (rule tables_update_store_extension[OF assms(3) s'_eq])
    fix tt
    assume "Tableinst_ok s (store_TABLES s ! ?a) tt"
    then obtain n m_opt where
      i_eq: "i = mk_uN n" and j_eq: "j_opt = map_option mk_uN m_opt" and len: "length r_lst = n"
      using old_ok by blast
    have wf_old': "wf_tableinst \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN n) (map_option mk_uN m_opt)) rt0, REFS = r_lst\<rparr>"
      using wf_old old i_eq j_eq by simp
    have wf_new': "wf_tableinst \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN i') (map_option mk_uN m_opt)) rt0, REFS = r_lst @ repeat v_n v_ref\<rparr>"
      using wf_new new j_eq by simp
    have "n \<le> i'" "length r_lst \<le> length (r_lst @ repeat v_n v_ref)"
      using i' len by simp_all
    then have "Extend_tableinst
      \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN n) (map_option mk_uN m_opt)) rt0, REFS = r_lst\<rparr>
      \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN i') (map_option mk_uN m_opt)) rt0, REFS = r_lst @ repeat v_n v_ref\<rparr>"
      by (rule mk_Extend_tableinst[OF _ _ wf_old' wf_new'])
    then show "Extend_tableinst (store_TABLES s ! ?a) ti"
      using old new i_eq j_eq by simp
  next
    fix tt
    assume ext: "Extend_store s s'" and ok: "Tableinst_ok s (store_TABLES s ! ?a) tt"
    then obtain n m_opt where
      i_eq: "i = mk_uN n" and j_eq: "j_opt = map_option mk_uN m_opt" and len: "length r_lst = n" and
      refs_ok: "list_all (\<lambda>r. Ref_ok s r rt0) r_lst"
      using old_ok by blast
    have wf_new': "wf_tableinst \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN i') (map_option mk_uN m_opt)) rt0, REFS = r_lst @ repeat v_n v_ref\<rparr>"
      using wf_new new j_eq by simp
    have wf_tt: "wf_tabletype (mk_tabletype (mk_limits (mk_uN i') (map_option mk_uN m_opt)) rt0)"
      using wf_new' by (cases rule: wf_tableinst.cases) simp
    have wf_lim: "wf_limits (mk_limits (mk_uN i') (map_option mk_uN m_opt))"
      using wf_tt by (cases rule: wf_tabletype.cases) simp
    have wf_i': "wf_uN 32 (mk_uN i')" and wf_m: "list_all (wf_uN 32) (option_to_list (map_option mk_uN m_opt))"
      using wf_lim by (cases rule: wf_limits.cases, simp)+
    have i'_bound: "i' \<le> 2 ^ 32 - 1"
      using wf_i' by (cases rule: wf_uN.cases) simp
    have m_bound: "list_all (\<lambda>m. m \<le> 2 ^ 32 - 1) (option_to_list m_opt)"
    proof (cases m_opt)
      case None
      then show ?thesis by simp
    next
      case (Some m)
      then have "wf_uN 32 (mk_uN m)" using wf_m by simp
      then show ?thesis using Some by (cases rule: wf_uN.cases) simp
    qed
    have i'_le: "list_all (\<lambda>m. i' \<le> m) (option_to_list m_opt)"
      using j_bound j_eq by (cases m_opt) auto
    have "list_all (\<lambda>m. i' \<le> m \<and> m \<le> 2 ^ 32 - 1) (option_to_list m_opt)"
      using m_bound i'_le by (auto simp: list_all_iff)
    then have lim_ok: "Limits_ok (mk_limits (mk_uN i') (map_option mk_uN m_opt)) (2 ^ 32 - 1)"
      using mk_Limits_ok[OF i'_bound _ wf_lim] by blast
    have tt_ok: "Tabletype_ok (mk_tabletype (mk_limits (mk_uN i') (map_option mk_uN m_opt)) rt0)"
      by (rule mk_Tabletype_ok[OF lim_ok wf_tt])
    have refs_ok': "list_all (\<lambda>r. Ref_ok s' r rt0) (r_lst @ repeat v_n v_ref)"
    proof -
      have "list_all (\<lambda>r. Ref_ok s' r rt0) r_lst"
        using refs_ok store_extension_refok[OF _ ext] by (simp add: list.pred_mono_strong)
      moreover have "list_all (\<lambda>r. Ref_ok s' r rt0) (repeat v_n v_ref)"
        using list_all_repeat[of "\<lambda>r. Ref_ok s' r rt", OF store_extension_refok[OF ref_ok ext]] rt0 by simp
      ultimately show ?thesis by simp
    qed
    have len': "length (r_lst @ repeat v_n v_ref) = i'"
      using i' by (simp add: length_repeat)
    have "Tableinst_ok s'
      \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN i') (map_option mk_uN m_opt)) rt0, REFS = r_lst @ repeat v_n v_ref\<rparr>
      (mk_tabletype (mk_limits (mk_uN i') (map_option mk_uN m_opt)) rt0)"
      by (rule mk_Tableinst_ok[OF tt_ok refs_ok' len' store_extension_wf[OF ext] wf_new' wf_tt])
    then show "\<exists>tt'. Tableinst_ok s' ti tt'"
      unfolding new j_eq by (rule exI)
  qed
qed

(*memory stores*)
lemma list_slice_update_length:
  "length u \<le> j \<Longrightarrow> length (list_slice_update l i j u) = length l"
  by (induction l i j u rule: list_slice_update.induct) auto

lemma list_slice_update_set:
  "set (list_slice_update l i j u) \<subseteq> set l \<union> set u"
  by (induction l i j u rule: list_slice_update.induct) auto

lemma list_all_list_slice_update:
  "list_all P l \<Longrightarrow> list_all P u \<Longrightarrow> list_all P (list_slice_update l i j u)"
  using list_slice_update_set by (fastforce simp: list_all_iff)

lemma wf_admininstr_CONST_inv:
  "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST nt c)) \<Longrightarrow> wf_num_underscore nt c"
  by (cases rule: wf_admininstr.cases) auto

lemma wf_admininstr_VCONST_inv:
  "wf_admininstr (admininstr_sc2 (admininstr_st2_VCONST vt c)) \<Longrightarrow>
   size (valtype_vectype vt) \<noteq> None \<and> wf_uN (the (size (valtype_vectype vt))) c"
  by (cases rule: wf_admininstr.cases) auto

lemma wf_num_Inn:
  assumes "wf_num_underscore (numtype_Inn v_Inn) c" "proj_num__0 c \<noteq> None"
  shows "wf_uN (the (size (valtype_Inn v_Inn))) (the (proj_num__0 c))"
  using assms
proof (cases rule: wf_num_underscore.cases)
  case (num__case_0 v_Inn' x)
  then have "v_Inn' = v_Inn"
    by (cases v_Inn; cases v_Inn') (auto simp: numtype_Inn.psimps numtype_Inn.domintros)
  then show ?thesis
    using num__case_0 by (simp add: proj_num__0.psimps proj_num__0.domintros)
next
  case (num__case_1 v_Fnn x)
  then show ?thesis
    using assms(2) by (simp add: proj_num__0.psimps proj_num__0.domintros)
qed

lemma mem_store_store_extension:
  assumes "with_mem (mk_state s f) (mk_uN 0) off n bs = mk_state s' f'"
          "Store_ok s"
          "list_all wf_byte bs"
          "length bs \<le> n"
  shows "Extend_store s s' \<and> Store_ok s'"
proof -
  let ?a = "MEMS (frame_MODULE f) ! 0"
  let ?g = "\<lambda>m. m\<lparr>BYTES := list_slice_update (BYTES m) off n bs\<rparr>"
  have s'_eq: "s' = s\<lparr>store_MEMS := list_update_func (store_MEMS s) ?a ?g\<rparr>"
    using assms(1) with_mem.psimps with_mem.domintros by auto
  have old_ok: "\<exists>k mo b. store_MEMS s ! ?a = \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)), BYTES = b\<rparr> \<and>
                  mt = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)) \<and>
                  length b = k * (64 * Ki) \<and>
                  Memtype_ok (PAGE (mk_limits (mk_uN k) (map_option mk_uN mo))) \<and>
                  wf_memtype (PAGE (mk_limits (mk_uN k) (map_option mk_uN mo))) \<and>
                  wf_meminst (store_MEMS s ! ?a)"
    if "Meminst_ok s (store_MEMS s ! ?a) mt" for mt
    using that by (cases rule: Meminst_ok.cases) auto
  have new_facts: "length (list_slice_update b off n bs) = length b \<and>
                   wf_meminst \<lparr>meminst_TYPE = mty, BYTES = list_slice_update b off n bs\<rparr>"
    if "wf_meminst \<lparr>meminst_TYPE = mty, BYTES = b\<rparr>" for mty b
    using that assms(3,4) list_slice_update_length list_all_list_slice_update
    by (auto elim!: wf_meminst.cases intro!: meminst_case_underscore)
  show ?thesis
  proof (rule mems_update_store_extension[OF assms(2) s'_eq])
    fix mt
    assume "Meminst_ok s (store_MEMS s ! ?a) mt"
    then obtain k mo b where
      old: "store_MEMS s ! ?a = \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)), BYTES = b\<rparr>" and
      wf_old: "wf_meminst (store_MEMS s ! ?a)"
      using old_ok by blast
    have wf_old': "wf_meminst \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)), BYTES = b\<rparr>"
      using wf_old old by simp
    note new = new_facts[OF wf_old']
    have "Extend_meminst
      \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)), BYTES = b\<rparr>
      \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)), BYTES = list_slice_update b off n bs\<rparr>"
      using new by (intro mk_Extend_meminst[OF le_refl _ wf_old']) simp_all
    then show "Extend_meminst (store_MEMS s ! ?a) (?g (store_MEMS s ! ?a))"
      using old by simp
  next
    fix mt
    assume ext: "Extend_store s s'" and "Meminst_ok s (store_MEMS s ! ?a) mt"
    then obtain k mo b where
      old: "store_MEMS s ! ?a = \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)), BYTES = b\<rparr>" and
      len: "length b = k * (64 * Ki)" and
      mt_ok: "Memtype_ok (PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)))" and
      wf_mt: "wf_memtype (PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)))" and
      wf_old: "wf_meminst (store_MEMS s ! ?a)"
      using old_ok by blast
    have wf_old': "wf_meminst \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)), BYTES = b\<rparr>"
      using wf_old old by simp
    note new = new_facts[OF wf_old']
    have "Meminst_ok s'
      \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)), BYTES = list_slice_update b off n bs\<rparr>
      (PAGE (mk_limits (mk_uN k) (map_option mk_uN mo)))"
      using new len by (intro mk_Meminst_ok[OF mt_ok _ store_extension_wf[OF ext] _ wf_mt]) simp_all
    then show "\<exists>mt'. Meminst_ok s' (?g (store_MEMS s ! ?a)) mt'"
      using old by auto
  qed
qed

lemma t_inst_match_trans:
  "t_inst_match C1 C2 \<Longrightarrow> t_inst_match C2 C3 \<Longrightarrow> t_inst_match C1 C3"
  by (simp add: t_inst_match_def)

(*Store extension reduction, general form (cf. Rocq `store_extension_reduce`)*)
lemma reduce_store_extension_gen:
assumes "Step c c'"
        "c  = mk_config (mk_state s f) admininstr_lst"
        "c' = mk_config (mk_state s' f') admininstr'_lst"
        "Store_ok s"
        "Moduleinst_ok s (frame_MODULE f) C'"
        "Instrs_ok2 s C admininstr_lst tf"
        "t_inst_match C C'"
shows "Extend_store s s' \<and> Store_ok s'"
using assms
proof (induction c c' arbitrary: s f s' f' admininstr_lst admininstr'_lst C C' tf rule: Step.induct)
  case (pure admininstr_lst admininstr'_lst z)
  then show ?case using store_extension_refl Store_ok_wf by auto
next
  case (read z admininstr_lst admininstr'_lst)
  then show ?case using store_extension_refl Store_ok_wf by auto
next
  case (ctxt_label z ais z' ais' v_n instr_0_lst)
  have z: "z = mk_state s f" "z' = mk_state s' f'"
    and es: "admininstr_lst = [admininstr_sc8 (LABEL_underscore v_n instr_0_lst ais)]"
    using ctxt_label.prems(1,2) by auto
  obtain t1 t2 where tf: "tf = mk_functype t1 t2" by (cases tf)
  obtain tp1 tp2 where lab_ok: "Instr_ok2 s C (admininstr_sc8 (LABEL_underscore v_n instr_0_lst ais)) (mk_functype tp1 tp2)"
    using inv_one_admininstr ctxt_label.prems(5) es tf by blast
  obtain C_in tf_in where inner: "Instrs_ok2 s C_in ais tf_in" and match_in: "t_inst_match C_in C"
    using inv_label[OF lab_ok HOL.refl] by (fastforce simp: t_inst_match_def append_res_context_def)
  show ?case
    using ctxt_label.IH[OF _ _ ctxt_label.prems(3,4) inner t_inst_match_trans[OF match_in ctxt_label.prems(6)]] z
    by simp
next
  case (ctxt_frame s0 f0 ais s0' f0' ais' fr v_n)
  have s: "s0 = s" "fr = f" "s0' = s'"
    and es: "admininstr_lst = [admininstr_sc8 (FRAME_underscore v_n f0 ais)]"
    using ctxt_frame.prems(1,2) by auto
  obtain t1 t2 where tf: "tf = mk_functype t1 t2" by (cases tf)
  obtain tp1 tp2 where fr_ok: "Instr_ok2 s C (admininstr_sc8 (FRAME_underscore v_n f0 ais)) (mk_functype tp1 tp2)"
    using inv_one_admininstr ctxt_frame.prems(5) es tf by blast
  obtain C_f t_lst where
    frame_ok: "Frame_ok s f0 C_f" and
    expr_ok: "Expr_ok2 s (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [],
        context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = Some (mk_list t_lst)\<rparr> C_f) ais (mk_list t_lst)"
    using inv_frame[OF fr_ok HOL.refl] by blast
  obtain C_m where
    mod_ok: "Moduleinst_ok s (frame_MODULE f0) C_m" and
    match_f: "t_inst_match (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [],
        context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = Some (mk_list t_lst)\<rparr> C_f) C_m"
    using frame_ok by (cases rule: Frame_ok.cases) (auto simp: t_inst_match_def append_res_context_def)
  show ?case
    using ctxt_frame.IH[OF _ _ ctxt_frame.prems(3) mod_ok inv_expr(1)[OF expr_ok] match_f] s
    by simp
next
  case (ctxt_instrs z ais z' ais' val_lst admininstr_1_lst)
  have z: "z = mk_state s f" "z' = mk_state s' f'"
    and es: "admininstr_lst = map admininstr_val val_lst @ ais @ admininstr_1_lst"
    using ctxt_instrs.prems(1,2) by auto
  obtain t1 t3 where tf: "tf = mk_functype t1 t3" by (cases tf)
  obtain t2 where "Instrs_ok2 s C (ais @ admininstr_1_lst) (mk_functype t2 t3)"
    using inv_seq[OF _ es] ctxt_instrs.prems(5) tf by blast
  then obtain t2' where inner: "Instrs_ok2 s C ais (mk_functype t2 t2')"
    using inv_seq[OF _ HOL.refl] by blast
  show ?case
    using ctxt_instrs.IH[OF _ _ ctxt_instrs.prems(3,4) inner ctxt_instrs.prems(6)] z
    by simp
next
  case (Step__local_set z v_val x)
  then have "s' = s" using with_local.psimps with_local.domintros by auto
  then show ?case using Step__local_set.prems(3) store_extension_refl Store_ok_wf by auto
next
  case (Step__global_set z v_val x)
  then have "with_global (mk_state s f) x v_val = mk_state s' f'"
        and "admininstr_lst = [admininstr_val v_val, admininstr_sc5 (admininstr_st5_GLOBAL_SET x)]"
    by auto
  then show ?case
    using global_set_store_extension Step__global_set.prems(3-6) by metis
next
  case (table_set_val i z x v_ref)
  obtain t1 t2 where tf: "tf = mk_functype t1 t2" by (cases tf)
  from table_set_val have "with_table (mk_state s f) x (proj_uN_0 (the (proj_num__0 i))) v_ref = mk_state s' f'"
        and "z = mk_state s f"
        and "admininstr_lst = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_ref v_ref, admininstr_sc5 (admininstr_st5_TABLE_SET x)]"
    by auto
  then show ?case
    using table_set_store_extension table_set_val.hyps table_set_val.prems(3-6) tf by metis
next
  case (table_grow_succeed z x v_n v_ref var_0 ti)
  from table_grow_succeed have "with_tableinst (mk_state s f) x ti = mk_state s' f'"
        and "fun_growtable (fun_table (mk_state s f) x) v_n v_ref (Some ti)"
        and "admininstr_lst = [admininstr_ref v_ref, admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))), admininstr_sc5 (admininstr_st5_TABLE_GROW x)]"
    by auto
  then show ?case
    using table_grow_store_extension table_grow_succeed.prems(3-6) by metis
next
  case (Step__elem_drop z x)
  then have "with_elem (mk_state s f) x [] = mk_state s' f'" by auto
  then show ?case using elem_drop_store_extension Step__elem_drop.prems(3) by blast
next
  case (store_num_val i nt b_lst c z ao)
  have es: "admininstr_lst = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_sc6 (admininstr_st6_STORE nt None ao)]"
    using store_num_val.prems(1) by simp
  have upd: "with_mem (mk_state s f) (mk_uN 0) (proj_uN_0 (the (proj_num__0 i)) + proj_uN_0 (OFFSET ao))
               (the (size (valtype_numtype nt)) div 8) b_lst = mk_state s' f'"
    using store_num_val by auto
  have "wf_num_underscore nt c"
    using Instrs_ok2_wf_instr[OF store_num_val.prems(5)] es wf_admininstr_CONST_inv by simp
  then have "list_all wf_byte b_lst"
    using nbytes__is_wf store_num_val.hyps(3) by blast
  moreover have "length b_lst \<le> the (size (valtype_numtype nt)) div 8"
    using nbytes_length store_num_val.hyps(3) by simp
  ultimately show ?case
    using mem_store_store_extension[OF upd store_num_val.prems(3)] by blast
next
  case (store_pack_val i v_Inn c b_lst v_n z ao)
  have es: "admininstr_lst = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST (numtype_Inn v_Inn) c), admininstr_sc6 (admininstr_st6_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]"
    using store_pack_val.prems(1) by simp
  have upd: "with_mem (mk_state s f) (mk_uN 0) (proj_uN_0 (the (proj_num__0 i)) + proj_uN_0 (OFFSET ao))
               (v_n div 8) b_lst = mk_state s' f'"
    using store_pack_val by auto
  have "wf_num_underscore (numtype_Inn v_Inn) c"
    using Instrs_ok2_wf_instr[OF store_pack_val.prems(5)] es wf_admininstr_CONST_inv by simp
  then have "wf_uN (the (size (valtype_Inn v_Inn))) (the (proj_num__0 c))"
    using wf_num_Inn store_pack_val.hyps(3) by blast
  then have "wf_uN v_n (wrap__underscore (the (size (valtype_Inn v_Inn))) v_n (the (proj_num__0 c)))"
    using wrap___is_wf by blast
  then have "list_all wf_byte b_lst"
    using ibytes__is_wf store_pack_val.hyps(4) by blast
  moreover have "length b_lst \<le> v_n div 8"
    using ibytes_length store_pack_val.hyps(4) by simp
  ultimately show ?case
    using mem_store_store_extension[OF upd store_pack_val.prems(3)] by blast
next
  case (vstore_val i b_lst c z ao)
  have es: "admininstr_lst = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc2 (admininstr_st2_VCONST V128 c), admininstr_sc6 (admininstr_st6_VSTORE V128 ao)]"
    using vstore_val.prems(1) by simp
  have upd: "with_mem (mk_state s f) (mk_uN 0) (proj_uN_0 (the (proj_num__0 i)) + proj_uN_0 (OFFSET ao))
               (the (size valtype_V128) div 8) b_lst = mk_state s' f'"
    using vstore_val by auto
  have v128: "valtype_vectype V128 = valtype_V128"
    by (simp add: valtype_vectype.psimps valtype_vectype.domintros)
  have "wf_admininstr (admininstr_sc2 (admininstr_st2_VCONST V128 c))"
    using Instrs_ok2_wf_instr[OF vstore_val.prems(5)] es by simp
  then have "size (valtype_vectype V128) \<noteq> None \<and> wf_uN (the (size (valtype_vectype V128))) c"
    by (rule wf_admininstr_VCONST_inv)
  then have "list_all wf_byte b_lst"
    using vbytes__is_wf vstore_val.hyps(3) by blast
  moreover have "length b_lst \<le> the (size valtype_V128) div 8"
    using vbytes_length[of V128 c] v128 vstore_val.hyps(3) by simp
  ultimately show ?case
    using mem_store_store_extension[OF upd vstore_val.prems(3)] by blast
next
  case (vstore_lane_val i v_N v_Jnn v_M c j b_lst z ao)
  have upd: "with_mem (mk_state s f) (mk_uN 0) (proj_uN_0 (the (proj_num__0 i)) + proj_uN_0 (OFFSET ao))
               (v_N div 8) b_lst = mk_state s' f'"
    using vstore_lane_val by auto
  have "list_all wf_byte b_lst"
    using ibytes__is_wf vstore_lane_val.hyps(6,7) by blast
  moreover have "length b_lst \<le> v_N div 8"
    using ibytes_length vstore_lane_val.hyps(6) by simp
  ultimately show ?case
    using mem_store_store_extension[OF upd vstore_lane_val.prems(3)] by blast
next
  case (memory_grow_succeed z v_n var_0 mi)
  from memory_grow_succeed have "with_meminst (mk_state s f) (mk_uN 0) mi = mk_state s' f'"
        and "fun_growmemory (fun_mem (mk_state s f) (mk_uN 0)) v_n (Some mi)"
    by auto
  then show ?case using memory_grow_store_extension memory_grow_succeed.prems(3) by blast
next
  case (Step__data_drop z x)
  then have "with_data (mk_state s f) x [] = mk_state s' f'" by auto
  then show ?case using data_drop_store_extension Step__data_drop.prems(3) by blast
qed (auto intro: store_extension_refl Store_ok_wf)

lemma reduce_store_extension:
assumes "Step (mk_config (mk_state s f) admininstr_lst) (mk_config (mk_state s' f') admininstr'_lst)"
        "Store_ok s"
        "Moduleinst_ok s (frame_MODULE f) C'"
        "C' = (append_res_context \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [],
        context_LOCALS = map typeofval (LOCALS f), LABELS = lbl, context_RETURN = rtn\<rparr> C)"
        "Instrs_ok2 s C admininstr_lst (mk_functype t_1_lst t_2_lst)"
        "t_inst_match C C'"
shows "Extend_store s s' \<and> Store_ok s'"
  using reduce_store_extension_gen[OF assms(1) HOL.refl HOL.refl assms(2,3,5,6)] .

end
