theory Wasm2_Type_Soundness
(* Imported Code *)
	imports isabelle_reference_output_wasm2 store_extension_typing Properties 
	        Type_Inversion Subtyping_Theorem Context_Store_Agreement
begin


lemma step_wf: "(wf_config var_0) \<Longrightarrow>
		 (Step var_0 var_1) \<Longrightarrow>
		 (wf_config var_1)"
  sorry


lemma list_update_func_length:
  assumes "list_update_func l k f = l'"
  shows "length l = length l'"
  using assms
proof (induction l arbitrary: k l')
  case Nil
  then show ?case
  by simp 
next
  case (Cons a l)
  then show ?case 
  proof (cases k)
    case 0
    then show ?thesis
    using Cons.prems by force
  next
    case (Suc nat)
    then show ?thesis using Cons by auto
  qed 
qed

lemma list_all2_list_update_func_r :
  assumes "list_all2 f l1 l2"
          "list_update_func l2 k g = l2'" 
          "f (l1 ! k) (g (l2 ! k))"
        shows "list_all2 f l1 l2'"
  using assms
proof (induction l2 arbitrary: k l2')
  case Nil
  then show ?case
  by simp 
next
  case (Cons a l2)
  then show ?case 
  proof (cases k)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc nat)
    then show ?thesis using Cons by auto
  qed
qed


lemma val_ok_sub:
  assumes "Val_ok s v t"
  "Valtype_sub t t'"
shows "Val_ok s v t'"
  using assms proof(induction s v t rule:Val_ok.induct)
  case (Val_ok__numtype s nt c_t)
  show ?case using Val_ok__numtype(3,1,2) 
  proof (induction "valtype_numtype nt" t' rule:Valtype_sub.induct)
    case refl
    then show ?case
      using Val_ok.Val_ok__numtype by force
  next
    case (bot t)
    then show ?case proof(cases nt) qed(simp_all)
  qed
next
  case (Val_ok__vectype s vt c_t)
   show ?case using Val_ok__vectype(3,1,2) 
  proof (induction "valtype_vectype vt" t' rule:Valtype_sub.induct)
    case refl
    then show ?case
      using Val_ok.Val_ok__vectype by force
  next
    case (bot t)
    then show ?case proof(cases vt) qed(simp_all add:valtype_vectype.psimps valtype_vectype.domintros)
  qed
next
  case (Val_ok__reftype s r rt)
   show ?case using Val_ok__reftype(3,1,2) 
  proof (induction "valtype_reftype rt" t' rule:Valtype_sub.induct)
    case refl
    then show ?case
      using Val_ok.Val_ok__reftype by force
  next
    case (bot t)
    then show ?case proof(cases rt) qed(simp_all add:valtype_reftype.psimps valtype_reftype.domintros)
  qed
qed


lemma e_preservation_locals:
  assumes "Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
          "Store_ok s"
          "Store_ok s'"
	        "Extend_store s s'"
          "Moduleinst_ok s (frame_MODULE f) C"
          "Moduleinst_ok s' (frame_MODULE f) C"
          "t_inst_match C C'"
          "list_all2 (\<lambda>(t :: valtype) (v :: val). (Val_ok s v t)) (context_LOCALS C') (LOCALS f)"
          "Instrs_ok2 s C' es tf"

shows
          "length (LOCALS f) = length (LOCALS f')"
          "frame_MODULE f = frame_MODULE f'"
          "list_all2 (\<lambda>(t :: valtype) (v :: val). (Val_ok s' v t)) (context_LOCALS C') (LOCALS f')"
  using assms
proof (induction "mk_config (mk_state s f) es" "mk_config (mk_state s' f') es'" 
       arbitrary: es es' s s' f f' tf C' rule: Step.induct)
  case pure 
  {
    case 1
    then show ?case using pure by simp
  next
    case 2
    then show ?case using pure by simp
  next
    case 3
    then show ?case using pure by simp
  }
next
  case read
  {
    case 1
    then show ?case using read by simp
  next
    case 2
    then show ?case using read by simp
  next
    case 3
    then show ?case using read by simp
  }
next
  case (ctxt_label es0 es1 v_n es')
  {
    case 1 
    show ?case 
    proof (cases tf)
      case (mk_functype t1 t2)
      then obtain t1' t2' where 
        "Instr_ok2 s C' (admininstr_sc8 (LABEL_underscore v_n es' es0)) (mk_functype t1' t2')"
        "mk_instrtype t1' t2' <ti: mk_instrtype t1 t2"
        using inv_one_admininstr 1 by blast
    then obtain ts' ts where ih:
      "Instrs_ok2 s C' (map admininstr_instr es') (mk_functype (mk_list ts') (mk_list ts))"
      "Instrs_ok2 s
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')
    es0 (mk_functype (mk_list []) (mk_list ts))"
   "wf_context
    \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
       context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [mk_list ts'],
       context_RETURN = None\<rparr>"
   "v_n = length ts'" "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'"
      using inv_label by blast
    have c1: "t_inst_match C (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')" 
      proof (cases C')
        case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
              context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
        note outer = fields
        then show ?thesis 
        proof (cases C)
          case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
                context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
          then show ?thesis using 1(6) outer append_res_context_def t_inst_match_def
            by auto
        qed
      qed
      have c2: "context_LOCALS C' = context_LOCALS (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')" proof(cases C')
        case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
              context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
        then show ?thesis using append_res_context_def by auto
      qed
      then show ?thesis using ctxt_label 1 c1 c2 ih by simp
    qed
  next
    case 2
    show ?case 
    proof (cases tf)
      case (mk_functype t1 t2)
      then obtain t1' t2' where 
        "Instr_ok2 s C' (admininstr_sc8 (LABEL_underscore v_n es' es0)) (mk_functype t1' t2')"
        "mk_instrtype t1' t2' <ti: mk_instrtype t1 t2"
        using inv_one_admininstr 2 by blast
    then obtain ts' ts where ih:
      "Instrs_ok2 s C' (map admininstr_instr es') (mk_functype (mk_list ts') (mk_list ts))"
      "Instrs_ok2 s
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')
    es0 (mk_functype (mk_list []) (mk_list ts))"
   "wf_context
    \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
       context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [mk_list ts'],
       context_RETURN = None\<rparr>"
   "v_n = length ts'" "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'"
      using inv_label by blast
    have c1: "t_inst_match C (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')" 
      proof (cases C')
        case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
              context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
        note outer = fields
        then show ?thesis 
        proof (cases C)
          case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
                context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
          then show ?thesis using 2(6) outer append_res_context_def t_inst_match_def
            by auto
        qed
      qed
      have c2: "context_LOCALS C' = context_LOCALS (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')" proof(cases C')
        case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
              context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
        then show ?thesis using append_res_context_def by auto
      qed
      then show ?thesis using ctxt_label 2 c1 c2 ih by simp
    qed
  next
    case 3
    show ?case 
    proof (cases tf)
      case (mk_functype t1 t2)
      then obtain t1' t2' where 
        "Instr_ok2 s C' (admininstr_sc8 (LABEL_underscore v_n es' es0)) (mk_functype t1' t2')"
        "mk_instrtype t1' t2' <ti: mk_instrtype t1 t2"
        using inv_one_admininstr 3 by blast
    then obtain ts' ts where ih:
      "Instrs_ok2 s C' (map admininstr_instr es') (mk_functype (mk_list ts') (mk_list ts))"
      "Instrs_ok2 s
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')
    es0 (mk_functype (mk_list []) (mk_list ts))"
   "wf_context
    \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
       context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [mk_list ts'],
       context_RETURN = None\<rparr>"
   "v_n = length ts'" "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'"
      using inv_label by blast
    have c1: "t_inst_match C (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')" 
      proof (cases C')
        case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
              context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
        note outer = fields
        then show ?thesis 
        proof (cases C)
          case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
                context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
          then show ?thesis using 3(6) outer append_res_context_def t_inst_match_def
            by auto
        qed
      qed
      have c2: "context_LOCALS C' = context_LOCALS (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list ts'], context_RETURN = None\<rparr>
      C')" proof(cases C')
        case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
              context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
        then show ?thesis using append_res_context_def by auto
      qed
      then show ?thesis using ctxt_label 3 c1 c2 ih by simp
    qed
  }
next
  case (ctxt_frame f' es0 f'' es1 v_n)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (ctxt_instrs es0 es1 vs aft)
  {
    case 1
    then show ?case proof(cases tf)
      case (mk_functype t1 t4)
      then obtain t2 where 
        "Instrs_ok2 s C' (map admininstr_val vs) (mk_functype t1 t2)" 
        "Instrs_ok2 s C' (es0 @ aft) (mk_functype t2 t4)"
        using 1 inv_seq by blast
      then obtain t3 where 
        "Instrs_ok2 s C' es0 (mk_functype t2 t3)"
        "Instrs_ok2 s C' aft (mk_functype t3 t4)"
        using inv_seq by blast
      then show ?thesis using 1 ctxt_instrs by simp
    qed
  next
    case 2
    then show ?case proof(cases tf)
      case (mk_functype t1 t4)
      then obtain t2 where 
        "Instrs_ok2 s C' (map admininstr_val vs) (mk_functype t1 t2)" 
        "Instrs_ok2 s C' (es0 @ aft) (mk_functype t2 t4)"
        using 2 inv_seq by blast
      then obtain t3 where 
        "Instrs_ok2 s C' es0 (mk_functype t2 t3)"
        "Instrs_ok2 s C' aft (mk_functype t3 t4)"
        using inv_seq by blast
      then show ?thesis using 2 ctxt_instrs by simp
    qed
  next
    case 3
    then show ?case proof(cases tf)
      case (mk_functype t1 t4)
      then obtain t2 where 
        "Instrs_ok2 s C' (map admininstr_val vs) (mk_functype t1 t2)" 
        "Instrs_ok2 s C' (es0 @ aft) (mk_functype t2 t4)"
        using 3 inv_seq by blast
      then obtain t3 where 
        "Instrs_ok2 s C' es0 (mk_functype t2 t3)"
        "Instrs_ok2 s C' aft (mk_functype t3 t4)"
        using inv_seq by blast
      then show ?thesis using 3 ctxt_instrs by simp
    qed
  }
next
  case (Step__local_set v_val x)
  {
    case 1
    have "list_update_func (LOCALS f) (proj_uN_0 x) (\<lambda> _. v_val) = LOCALS f'" 
      using Step__local_set 
      by (metis local.Step__local_set with_local.psimps state.inject 
          with_local.domintros frame.update_convs(1) frame.ext_inject frame.surjective)
    then show ?case using list_update_func_length
      by blast
  next
    case 2
    then show ?case using Step__local_set using with_local.domintros with_local.psimps by auto 
  next
    case 3
    then show ?case proof (cases tf)
      case (mk_functype t1 t3)
      then obtain t2 where splitval:
         "Instrs_ok2 s C'  [admininstr_val v_val] (mk_functype t1 t2)"
         "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_LOCAL_SET x)] (mk_functype t2 t3)" 
        using 3 inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
      then have subv: "mk_instrtype (mk_list []) (mk_list [typeofval v_val]) <ti: mk_instrtype t1 t2"
        using inv_const_list[of s C' "[_]" t1 t2 "[_]"] by fastforce
      have valok: "Val_ok s v_val (typeofval v_val)" 
        using splitval(1) Instrs_ok2_const_replace[of s C' "[_]" _ C'] Instrs_ok2_wf
        by force
      obtain t2' t3' where
        "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_LOCAL_SET x)) (mk_functype t2' t3')" 
        and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3"
        using splitval inv_one_admininstr by blast
      then have "Instr_ok C' (instr_sc4 (LOCAL_SET x)) (mk_functype t2' t3')"
        using inv_plain admininstr_instr.domintros admininstr_instr.psimps by fastforce
      then obtain t where hyps:
          "proj_uN_0 x < length (context_LOCALS C')"
          "context_LOCALS C' ! proj_uN_0 x = t" 
          "mk_functype (mk_list [t]) (mk_list []) = mk_functype t2' t3'"
        using inv_local_set by blast
      then have 
         subt: "mk_instrtype (mk_list []) (mk_list []) <ti: mk_instrtype t1 t3" 
            "Resulttype_sub (mk_list [typeofval v_val]) (mk_list [t])" 
        using subv subt produce_consume[of "[_]" t1 t2 "[]" "[_]" "[]" t3] by auto
      have "Valtype_sub (typeofval v_val) t" using subt(2)
      proof (induction "mk_list [typeofval v_val]" "mk_list [t]" rule:Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by blast
      qed
      then have valok: "Val_ok s v_val t" using valok val_ok_sub by blast
    have localsupd: "list_update_func (LOCALS f) (proj_uN_0 x) (\<lambda> _. v_val) = LOCALS f'" 
      using Step__local_set 
      by (metis local.Step__local_set with_local.psimps state.inject 
          with_local.domintros frame.update_convs(1) frame.ext_inject frame.surjective)
    have types': "list_all2 (\<lambda> t v. Val_ok s' v t) (context_LOCALS C') (LOCALS f)" 
      using 3 store_extension_valok list_all2_mono
      by (metis (mono_tags, lifting) Extend_store.simps)
    have "Val_ok s' v_val (context_LOCALS C' ! proj_uN_0 x)" 
      using hyps subt valok store_extension_valok 3 
      using store_extension_wf by blast
    then show ?thesis using localsupd types' list_all2_list_update_func_r
      by blast
  qed
  }
next
  case (Step__global_set v_val x)
  then have samef: "f = f'" by (simp add: with_global.domintros with_global.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps) 
  }
next
  case (table_set_trap i x v_ref)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using table_set_trap by simp
  }
next
  case (table_set_val i x v_ref)
  then have samef: "f = f'" by (simp add: with_table.domintros with_table.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (table_grow_succeed x v_n v_ref var_0 ti)
  then have samef: "f = f'" by (simp add: with_tableinst.domintros with_tableinst.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (table_grow_fail var_0 v_ref v_n x)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using table_grow_fail by simp
  }
next
  case (Step__elem_drop x)
  then have samef: "f = f'" using with_elem.domintros with_elem.psimps by force
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (store_num_trap i nt ao c)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using store_num_trap by simp
  }
next
  case (store_num_val i nt b_lst c ao)
  then have samef: "f = f'" by (simp add: with_mem.domintros with_mem.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (store_pack_trap i ao v_n v_Inn c)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using store_pack_trap by simp
  }
next
  case (store_pack_val i v_Inn c b_lst v_n ao)
  then have samef: "f = f'" by (simp add: with_mem.domintros with_mem.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (vstore_oob i ao c)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using vstore_oob by simp
  }
next
  case (vstore_val i b_lst c ao)
  then have samef: "f = f'" by (simp add: with_mem.domintros with_mem.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (vstore_lane_oob i ao v_N c j)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using vstore_lane_oob by simp
  }
next
  case (vstore_lane_val i v_N v_Jnn v_M c j b_lst ao)
  then have samef: "f = f'" by (simp add: with_mem.domintros with_mem.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (memory_grow_succeed v_n var_0 mi)
  then have samef: "f = f'" by (simp add: with_meminst.domintros with_meminst.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (memory_grow_fail var_0 v_n)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using memory_grow_fail by simp
  }
next
  case (Step__data_drop x)
  then have samef: "f = f'" by (simp add: with_data.domintros with_data.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
qed

lemma mk_uN_proj_uN_0:
  shows "mk_uN (proj_uN_0 k) = k" 
proof (cases k)
  case (mk_uN x)
  then show ?thesis using proj_uN_0.domintros proj_uN_0.psimps by simp
qed

lemma mk_list_proj_list_0:
  shows "mk_list (proj_list_0 l) = l"
proof (cases l)
  case (mk_list x)
  then show ?thesis using proj_list_0.domintros proj_list_0.psimps by blast
qed





lemma e_preservation:
  assumes "Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
          "Store_ok s"
          "Store_ok s'"
	        "Extend_store s s'"
          "Moduleinst_ok s (frame_MODULE f) C"
          "Moduleinst_ok s' (frame_MODULE f) C"
          "t_inst_match C C'"
          "list_all2 (\<lambda>(t :: valtype) (v :: val). (Val_ok s v t)) (context_LOCALS C') (LOCALS f)"
          "Instrs_ok2 s C' es tf"

shows
          "Instrs_ok2 s' C' es' tf"
proof (cases tf)
  case (mk_functype t1 t3)
  (* have wfconfiges: "wf_config (mk_config (mk_state s f) es)" 
    using assms(9) Instrs_ok2_wf Instrs_ok2_wf_instr 
  have wfres: "list_all wf_admininstr es'" using assms step_wf Instrs_ok2_wf Instrs_ok2_wf_instr
    sledgehamm er *)
  show ?thesis 
  using assms mk_functype
proof (induction "mk_config (mk_state s f) es" "mk_config (mk_state s' f') es'" 
    arbitrary: s f es s' f' es' tf t1 t3 rule:Step.induct)
  case (pure es0 es1)
  then have wfres: "list_all wf_admininstr es1" 
    using Instrs_ok2_wf_instr Step_pure_is_wf by blast 
  show ?case using pure wfres
  proof (induction rule:Step_pure.induct)
    case Step_pure__unreachable
    then have wfs: "wf_store s" "wf_context C'" using Instrs_ok2_wf by auto
    then show ?case 
         using Instrs_ok2__instr admininstr_case_73 mk_functype Instr_ok2__trap res_list.exhaust
         by (metis wfs(1) Instrs_ok2__instr admininstr_case_73 wfs(2) Instr_ok2__trap 
             res_list.exhaust pure.prems(9))
  next
    case Step_pure__nop
    obtain t1' t2' where 
      "Instr_ok2 s C' (admininstr_sc0 admininstr_st0_NOP) (mk_functype t1' t2')" 
      and sub: "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using Step_pure__nop(8,9) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc0 NOP) (mk_functype t1' t2')"            
      using inv_plain[where ?v_instr = "instr_sc0 NOP"]
      using admininstr_instr.domintros(1) admininstr_instr.psimps(1) 
      by simp
    then show ?case 
      using Instrs_ok2_subtyping
            Instrs_ok2__empty Instrs_ok2_wf(1,2) pure.prems(8,9)
            inv_nop instr_ok_instrs_ok instr_case_0
            sub by blast
  next
    case (Step_pure__drop v_val)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_val v_val] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 admininstr_st0_DROP] (mk_functype t2 t3)"
      using inv_seq[of s C' "[admininstr_val v_val, admininstr_sc0 admininstr_st0_DROP]"
              t1 t3 "[admininstr_val v_val]" "[admininstr_sc0 admininstr_st0_DROP]"] by fastforce
    have tv: "mk_instrtype (mk_list []) (mk_list [typeofval v_val]) <ti: mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[v_val]"] by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
      and "Instr_ok2 s C' (admininstr_sc0 admininstr_st0_DROP) (mk_functype t2'' t3'')" 
      using Step_pure__drop(9) splitih(2)
         inv_one_admininstr 
      by blast
    then have "Instr_ok C' (instr_sc0 DROP) (mk_functype t2'' t3'')" 
      using inv_plain[where ?v_instr = "instr_sc0 DROP"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain t where 
      "mk_functype (mk_list [t]) (mk_list []) = mk_functype t2'' t3''"
      using inv_drop by blast
    then have "mk_instrtype (mk_list []) (mk_list []) <ti: mk_instrtype t1 t3" 
      using td tv Instrtype_sub_trans produce_consume[of 
           "[typeofval v_val]" t1 t2 "[]" "[t]" "[]"] 
      by fastforce
    then show ?case 
      using Instrs_ok2_subtyping 
            Instrs_ok2__empty Instrs_ok2_wf(1,2) pure.prems(8,9) 
      by fast
  next
    case (select_true c val_1 val_2 t_lst_opt)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_val val_1, admininstr_val val_2, 
                        admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_SELECT t_lst_opt)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_, admininstr_sc0 _]"
              t1 t3 "[admininstr_val _,_,_]" "[admininstr_sc0 _]"] by fastforce
    obtain t2v where splitval1:
      "Instrs_ok2 s C' [admininstr_val val_1] (mk_functype t1 t2v)"
      "Instrs_ok2 s C' [admininstr_val val_2, admininstr_sc1 (admininstr_st1_CONST I32 c)] 
              (mk_functype t2v t2)" 
      using inv_seq[OF splitih(1), of "[_]" "[_,_]"] by fastforce
   
    have tv: "mk_instrtype (mk_list []) 
              (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) <ti: mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[val_1,val_2,val_CONST I32 c]"] 
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps 
       by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
        "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_SELECT t_lst_opt)) 
              (mk_functype t2'' t3'')"
      using select_true(9) splitih(2) inv_one_admininstr by blast
    then have
       td': "Instr_ok C' (instr_sc0 (SELECT t_lst_opt)) (mk_functype t2'' t3'')" 
      using inv_plain[where ?v_instr = "instr_sc0 _"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then show ?case 
    proof (cases t_lst_opt)
      case None
      then obtain t v_numtype v_vectype t' where
       "Valtype_sub t t'"
       "(t' = valtype_numtype v_numtype \<or> t' = valtype_vectype v_vectype)"
       "mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]) = 
        mk_functype t2'' t3''"
        using td' inv_select_impl by blast
      then have "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3) \<and>
            Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])"
        using td(1) tv produce_consume[of 
              "[typeofval val_1 , typeofval val_2 , valtype_I32]" t1 t2 "[]"  
              "[t,t,valtype_I32]" "[t]" t3]
              Instrtype_sub_trans by force
      then have 
        subs: "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3)"
            "Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])" by auto
      have "Valtype_sub (typeofval val_1) t" 
        using subs(2) 
      proof(induction "mk_list [typeofval val_1, typeofval val_2, valtype_I32]" 
              "mk_list [t,t,valtype_I32]" rule: Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by simp 
      qed
      then have "Resulttype_sub (mk_list [typeofval val_1]) (mk_list [t])" 
        using mk_Resulttype_sub by simp
      then have "mk_instrtype (mk_list []) (mk_list [typeofval val_1]) <ti:
              mk_instrtype t1 t3" 
        using subs 
        by (meson Instrtype_sub_sub_rule Instrtype_sub_trans Resulttype_sub_refl)
      then show ?thesis 
        using pure.prems(9) splitval1(1) 
            Instrs_ok2_const_replace[of s C' "[val_1]" _ C'] Instrs_ok2_subtyping Instrs_ok2_wf by auto
    next
      case (Some ts)
       then obtain t where "ts = [t]"
       "mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]) = 
        mk_functype t2'' t3''"
        using td' inv_select_expl by blast
      then have "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3) \<and>
            Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])"
        using td(1) tv produce_consume[of 
              "[typeofval val_1 , typeofval val_2 , valtype_I32]" t1 t2  "[]" 
              "[t,t,valtype_I32]" "[t]" t3]
              Instrtype_sub_trans by force
      then have 
        subs: "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3)"
            "Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])" by auto
      have "Valtype_sub (typeofval val_1) t" 
        using subs(2) 
      proof(induction "mk_list [typeofval val_1, typeofval val_2, valtype_I32]" 
              "mk_list [t,t,valtype_I32]" rule: Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by simp 
      qed
      then have "Resulttype_sub (mk_list [typeofval val_1]) (mk_list [t])" 
        using mk_Resulttype_sub by simp
      then have "mk_instrtype (mk_list []) (mk_list [typeofval val_1]) <ti:
              mk_instrtype t1 t3" 
        using subs
        by (meson Instrtype_sub_sub_rule Instrtype_sub_trans Resulttype_sub_refl)
      then show ?thesis 
        using pure.prems(9) splitval1(1) 
            Instrs_ok2_const_replace[of s C' "[val_1]" _ C'] Instrs_ok2_subtyping Instrs_ok2_wf by auto
    qed
  next
    case (select_false c val_1 val_2 t_lst_opt)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_val val_1, admininstr_val val_2, 
                        admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_SELECT t_lst_opt)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_, admininstr_sc0 _]"
              t1 t3 "[admininstr_val _,_,_]" "[admininstr_sc0 _]"] by fastforce
    obtain t2v where splitval1:
      "Instrs_ok2 s C' [admininstr_val val_1] (mk_functype t1 t2v)"
      "Instrs_ok2 s C' [admininstr_val val_2, admininstr_sc1 (admininstr_st1_CONST I32 c)] 
              (mk_functype t2v t2)" 
      using inv_seq[OF splitih(1), of "[_]" "[_,_]"] by fastforce
    then obtain t1v' t2v' where splitval2:
      "Instrs_ok2 s C' [admininstr_val val_2] (mk_functype t1v' t2v')"
      using inv_seq[OF splitval1(2), of "[_]" "[_]"] by fastforce
    have tv: "mk_instrtype (mk_list []) 
              (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) <ti: mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[val_1,val_2,val_CONST I32 c]"] 
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps 
       by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
       "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_SELECT t_lst_opt)) (mk_functype t2'' t3'')" 
      using inv_one_admininstr select_false(9) splitih(2) by blast
    then have
      td': "Instr_ok C' (instr_sc0 (SELECT t_lst_opt)) (mk_functype t2'' t3'')" 
      using inv_plain[where ?v_instr = "instr_sc0 _"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then show ?case 
    proof (cases t_lst_opt)
      case None
      then obtain t v_numtype v_vectype t' where
       "Valtype_sub t t'"
       "(t' = valtype_numtype v_numtype \<or> t' = valtype_vectype v_vectype)"
       "mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]) =
        mk_functype t2'' t3''"
        using td' inv_select_impl
        by blast
      then have "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3) \<and>
            Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])"
        using td(1) tv produce_consume[of 
              "[typeofval val_1 , typeofval val_2 , valtype_I32]" t1 t2 "[]" 
              "[t,t,valtype_I32]" "[t]" t3]
              Instrtype_sub_trans by force
      then have 
        subs: "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3)"
            "Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])" by auto
      have "Valtype_sub (typeofval val_2) t" 
        using subs(2) 
      proof(induction "mk_list [typeofval val_1, typeofval val_2, valtype_I32]" 
              "mk_list [t,t,valtype_I32]" rule: Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by simp 
      qed
      then have "Resulttype_sub (mk_list [typeofval val_2]) (mk_list [t])" 
        using mk_Resulttype_sub by simp
      then have "mk_instrtype (mk_list []) (mk_list [typeofval val_2]) <ti:
              mk_instrtype t1 t3" 
        using subs 
        by (meson Instrtype_sub_sub_rule Instrtype_sub_trans Resulttype_sub_refl)
      then show ?thesis 
        using pure.prems(9) splitval2(1) 
            Instrs_ok2_const_replace[of s C' "[val_2]" _ C'] Instrs_ok2_subtyping Instrs_ok2_wf by auto
    next
      case (Some ts)
       then obtain t where "ts = [t]"
       "mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]) =
        mk_functype t2'' t3''"
        using td' inv_select_expl
        by blast
      then have "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3) \<and>
            Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])"
        using td(1) tv produce_consume[of 
              "[typeofval val_1 , typeofval val_2 , valtype_I32]" t1 t2 "[]" 
              "[t,t,valtype_I32]" "[t]" t3]
              Instrtype_sub_trans by fastforce
      then have 
        subs: "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3)"
            "Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])" by auto
      have "Valtype_sub (typeofval val_2) t" 
        using subs(2) 
      proof(induction "mk_list [typeofval val_1, typeofval val_2, valtype_I32]" 
              "mk_list [t,t,valtype_I32]" rule: Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by simp 
      qed
      then have "Resulttype_sub (mk_list [typeofval val_2]) (mk_list [t])" 
        using mk_Resulttype_sub by simp
      then have "mk_instrtype (mk_list []) (mk_list [typeofval val_2]) <ti:
              mk_instrtype t1 t3" 
        using subs
        by (meson Instrtype_sub_sub_rule Instrtype_sub_trans Resulttype_sub_refl)
      then show ?thesis 
        using pure.prems(9) splitval2(1) 
            Instrs_ok2_const_replace[of s C' "[val_2]" _ C'] Instrs_ok2_subtyping Instrs_ok2_wf by auto
    qed
  next
    case (if_true c bt es1 es2)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_IFELSE bt es1 es2)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]"
              t1 t3 "[_]" "[_]"] by fastforce
    have tv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
          mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[val_CONST I32 c]"] typeofval.domintros
          typeofval.psimps admininstr_val.domintros admininstr_val.psimps 
         by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
      and "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_IFELSE bt es1 es2)) (mk_functype t2'' t3'')"
      using if_true(9) splitih(2) inv_one_admininstr by blast
    then have
      td': "Instr_ok C' (instr_sc7 (IFELSE bt es1 es2)) (mk_functype t2'' t3'')" 
      using inv_plain[where ?v_instr = "instr_sc7 (IFELSE bt es1 es2)"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain t1l t2l where blockhyps:
      "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
           context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [],
           context_LOCALS = [], LABELS = [mk_list t2l], context_RETURN = None\<rparr>"
       "Blocktype_ok C' bt (mk_functype (mk_list t1l) (mk_list t2l))"
       "Instrs_ok
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
             context_TABLES = [], context_MEMS = [], context_ELEMS = [],
             context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2l],
             context_RETURN = None\<rparr>
          C')
        es1 (mk_functype (mk_list t1l) (mk_list t2l))"
       "Instrs_ok
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
             context_TABLES = [], context_MEMS = [], context_ELEMS = [],
             context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2l],
             context_RETURN = None\<rparr>
          C')
        es2 (mk_functype (mk_list t1l) (mk_list t2l))"
       "mk_functype (mk_list (t1l @ [valtype_I32]))
        (mk_list t2l) = mk_functype  t2'' t3''"
      using inv_res_if instr_ok_instrs_ok by metis
    have sub: "mk_instrtype (mk_list t1l) (mk_list t2l) <ti: mk_instrtype t1 t3"
      using tv td blockhyps(5)
        produce_consume[of "[valtype_I32]" t1 t2 t1l "[valtype_I32]" t2l t3]
      using Instrtype_sub_sub_rule Instrtype_sub_trans by blast
    have "Instr_ok C' (instr_sc7 (BLOCK bt es1)) 
      (mk_functype (mk_list t1l) (mk_list t2l))" 
      using blockhyps block[OF blockhyps(2) blockhyps(3)] pure.prems(8)
          Instrs_ok2_wf Instrs_ok_wf instr_case_4
      by (metis Blocktype_ok.simps)
    then have "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BLOCK bt es1)]
          (mk_functype (mk_list t1l) (mk_list t2l))"
      using instr_ok2_instrs_ok2 instr_ok_instr_ok2 
          admininstr_instr.domintros admininstr_instr.psimps
        pure.prems(8) Instrs_ok2_wf by metis
    then show ?case using sub Instrs_ok2_subtyping pure.prems(9) by auto
  next
    case (if_false c bt es1 es2)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_IFELSE bt es1 es2)] (mk_functype t2 t3)" 
      using inv_seq[of s C' "[_,_]"
              t1 t3 "[_]" "[_]"] by fastforce
    have tv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
          mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[val_CONST I32 c]"] typeofval.domintros
          typeofval.psimps admininstr_val.domintros admininstr_val.psimps 
         by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
      and "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_IFELSE bt es1 es2)) (mk_functype t2'' t3'')" 
      using if_false(9) splitih(2) inv_one_admininstr by blast
      then have "Instr_ok C' (instr_sc7 (IFELSE bt es1 es2)) (mk_functype t2'' t3'')"
      using inv_plain[where ?v_instr = "instr_sc7 (IFELSE bt es1 es2)"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain t1l t2l where blockhyps:
      "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
           context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [],
           context_LOCALS = [], LABELS = [mk_list t2l], context_RETURN = None\<rparr>"
       "Blocktype_ok C' bt (mk_functype (mk_list t1l) (mk_list t2l))"
       "Instrs_ok
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
             context_TABLES = [], context_MEMS = [], context_ELEMS = [],
             context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2l],
             context_RETURN = None\<rparr>
          C')
        es1 (mk_functype (mk_list t1l) (mk_list t2l))"
       "Instrs_ok
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
             context_TABLES = [], context_MEMS = [], context_ELEMS = [],
             context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2l],
             context_RETURN = None\<rparr>
          C')
        es2 (mk_functype (mk_list t1l) (mk_list t2l))"
       "mk_functype (mk_list (t1l @ [valtype_I32]))
        (mk_list t2l) = mk_functype t2'' t3''"
      using inv_res_if instr_ok_instrs_ok by metis
    have sub: "mk_instrtype (mk_list t1l) (mk_list t2l) <ti: mk_instrtype t1 t3"
      using tv td blockhyps(5) 
        produce_consume[of "[valtype_I32]" t1 t2 t1l "[valtype_I32]" t2l t3]
      using Instrtype_sub_sub_rule Instrtype_sub_trans by blast
    have "Instr_ok C' (instr_sc7 (BLOCK bt es2)) 
      (mk_functype (mk_list t1l) (mk_list t2l))" 
      using blockhyps block[OF blockhyps(2) blockhyps(4)] pure.prems(8)
          Instrs_ok2_wf Instrs_ok_wf instr_case_4
      by (metis Blocktype_ok.simps)
    then have "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BLOCK bt es2)]
          (mk_functype (mk_list t1l) (mk_list t2l))"
      using instr_ok2_instrs_ok2 instr_ok_instr_ok2
        admininstr_instr.domintros admininstr_instr.psimps
        pure.prems(8) Instrs_ok2_wf
      by metis
    then show ?case using sub Instrs_ok2_subtyping pure.prems(9) by auto
  next
    case (label_vals n es vs)
    then obtain t1' t2' where 
      td: "Instr_ok2 s C' (admininstr_sc8 (LABEL_underscore n es (map admininstr_val vs)))
        (mk_functype t1' t2')"
      "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using inv_one_admininstr by blast
    then obtain ts ts' where splitih: 
        "Instrs_ok2 s C' (map admininstr_instr es)
        (mk_functype (mk_list ts') (mk_list ts))"
       "Instrs_ok2 s
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C')
        (map admininstr_val vs) (mk_functype (mk_list []) (mk_list ts))"
       "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
           LABELS = [mk_list ts'], context_RETURN = None\<rparr>"
       "n = length ts'" 
       "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'" 
      using inv_label by blast
    then show ?case using Instrs_ok2_const_replace td 
      by (metis Instrs_ok2_subtyping Instrs_ok2_wf(1) inv_const_list pure.prems(9))
  next
    case (br_zero n vs es' vs' es)
    then obtain t1' t2' where td:
      "Instr_ok2 s C'
     (admininstr_sc8
       (LABEL_underscore n es'
         (((map admininstr_val vs' @ map admininstr_val vs) @
           [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))]) @
          map admininstr_instr es))) (mk_functype t1' t2')"
     "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using inv_one_admininstr by blast
    then obtain ts ts' where splitih0: 
        "Instrs_ok2 s C' (map admininstr_instr es')
        (mk_functype (mk_list ts') (mk_list ts))"
       "Instrs_ok2 s
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C')
         (((map admininstr_val vs' @ map admininstr_val vs) @
           [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))]) @
          map admininstr_instr es) (mk_functype (mk_list []) (mk_list ts))"
       "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
           LABELS = [mk_list ts'], context_RETURN = None\<rparr>"
       "n = length ts'" 
       "mk_instrtype (mk_list []) (mk_list ts) <ti: mk_instrtype t1 t3" 
      using inv_label by blast
    then obtain ts2 where splitih:
       "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ((map admininstr_val vs' @ map admininstr_val vs) @ 
              [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))]) (mk_functype (mk_list []) ts2)"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_instr es) (mk_functype ts2 (mk_list ts))"
      using inv_seq by blast 
    then obtain ts2' where splitih': 
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs' @ map admininstr_val vs) (mk_functype (mk_list []) ts2')"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))] (mk_functype ts2' ts2)" 
      using inv_seq by blast
    then obtain ts2'' ts3'' where splitih'': 
       "Instr_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (admininstr_sc0 (admininstr_st0_BR (mk_uN 0))) (mk_functype ts2'' ts3'')" 
        "mk_instrtype ts2'' ts3'' <ti: mk_instrtype ts2' ts2"
      using inv_one_admininstr by blast
      then have "Instr_ok (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (instr_sc0 (BR (mk_uN 0))) (mk_functype ts2'' ts3'')"
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain tsbr ts1br ts2br where splitihbr:
      "proj_uN_0 (mk_uN 0) < length (LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C'))"
      "proj_list_0 (LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ! proj_uN_0 (mk_uN 0)) = tsbr"
      "mk_functype (mk_list (ts1br @ tsbr)) (mk_list ts2br) = mk_functype ts2'' ts3''" 
      using inv_br by presburger
    obtain t2v where splitihv:
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs') (mk_functype (mk_list []) t2v)" 
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs) (mk_functype t2v ts2')"
      using inv_seq[OF splitih'(1)] by blast
    then have subvs': "mk_instrtype (mk_list []) (mk_list (map typeofval vs')) <ti: 
        mk_instrtype (mk_list []) t2v" using inv_const_list by blast
    have subvs: "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti:
        mk_instrtype t2v ts2'" using inv_const_list splitihv by blast
    have typevs: "Instrs_ok2 s C' (map admininstr_val vs) 
            (mk_functype (mk_list []) (mk_list (map typeofval vs)))"
      using splitihv Instrs_ok2_const_replace splitih0 Instrs_ok2_wf by blast
    have zeq: "proj_uN_0 (mk_uN 0) = 0" using proj_uN_0.domintros proj_uN_0.psimps by simp
    have "ts' = tsbr" proof(cases C')
      case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
              context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
      then have "res_context.LABELS
       (append_res_context
         \<lparr>res_context.context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
            context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
            LABELS = [mk_list ts'], context_RETURN = None\<rparr>
         C') = (mk_list ts') # LABELS" using append_res_context_def by simp
      then show ?thesis 
        using splitihbr(2) zeq 
          proj_list_0.domintros proj_list_0.psimps
        by (metis nth_Cons_0)
    qed  
    then have "Resulttype_sub (mk_list (map typeofval vs)) (mk_list ts')"
      using splitihbr(3) splitih''(2)
        Instrtype_sub_emptyl[OF subvs' subvs] 
        produce_consume_waste[of "map typeofval vs'" "map typeofval vs" "mk_list []" ts2' ts1br tsbr 
            ts2br ts2] 
        br_zero(1) splitih0(4) Instrtype_sub_trans length_map map_append 
      by (metis functype.inject inv_const_list splitih'(1)) 
    then show ?case using typevs splitih0(1,5) pure(10) Instrs_ok2__seq Instrs_ok2_subtyping
      by (meson Instrs_ok2__sub Instrs_ok2_wf(1,2) Instrs_ok2_wf_instr Resulttype_sub_empty)
  next
    case (br_succ n es' vs l es)
    then obtain t1' t2' where td:
      "Instr_ok2 s C'
     (admininstr_sc8
       (LABEL_underscore n es'
         ((map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))]) @
          map admininstr_instr es))) (mk_functype t1' t2')"
      "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using inv_one_admininstr by blast
    then obtain ts ts' where splitih0: 
        "Instrs_ok2 s C' (map admininstr_instr es')
        (mk_functype (mk_list ts') (mk_list ts))"
       "Instrs_ok2 s
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C')
         (((map admininstr_val vs) @
           [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))]) @
          map admininstr_instr es) (mk_functype (mk_list []) (mk_list ts))"
       "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
           LABELS = [mk_list ts'], context_RETURN = None\<rparr>"
       "n = length ts'" 
       "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'" 
      using inv_label by blast
    then obtain ts2 where splitih:
       "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ((map admininstr_val vs) @ 
              [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))]) (mk_functype (mk_list []) ts2)"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_instr es) (mk_functype ts2 (mk_list ts))"
      using inv_seq by blast 
    then obtain ts2' where splitih': 
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs) (mk_functype (mk_list []) ts2')"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))] (mk_functype ts2' ts2)" 
      using inv_seq by blast
    then obtain ts2'' ts3'' where splitih'': 
       "Instr_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))) (mk_functype ts2'' ts3'')" 
        "mk_instrtype ts2'' ts3'' <ti: mk_instrtype ts2' ts2"
      using inv_one_admininstr by blast
    then have brok: "Instr_ok (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (instr_sc0 (BR (mk_uN (proj_uN_0 l + 1)))) (mk_functype ts2'' ts3'')" 
using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain tsbr ts1br ts2br where splitihbr:
      "proj_uN_0 (mk_uN (proj_uN_0 l + 1)) < length (LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C'))"
      "proj_list_0 (LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ! proj_uN_0 (mk_uN (proj_uN_0 l + 1))) = tsbr"
      "mk_functype (mk_list (ts1br @ tsbr)) (mk_list ts2br) = mk_functype ts2'' ts3''" 
      using inv_br by presburger
    then have proj1: "proj_uN_0 l < length (LABELS C')" 
    proof (cases C')
      case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
            context_ELEMS context_DATAS context_LOCALS context_LABELS context_RETURN)
      then have "LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') = (mk_list ts') # context_LABELS" using append_res_context_def by simp
      then show ?thesis using splitihbr proj_uN_0.domintros proj_uN_0.psimps fields by force
    qed
    have proj2: "proj_list_0 (LABELS C' ! proj_uN_0 l) = tsbr" 
    proof (cases C')
      case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
            context_ELEMS context_DATAS context_LOCALS context_LABELS context_RETURN)
      then have "LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') = (mk_list ts') # context_LABELS" using append_res_context_def by simp
      then show ?thesis using splitihbr proj_uN_0.domintros proj_uN_0.psimps fields by force
    qed
    have wfbr: "wf_instr (instr_sc0 (BR l))" using br_succ(10) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    have subvs: "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: 
          mk_instrtype (mk_list []) ts2'" using splitih' inv_const_list by blast
    have vsok: "Instrs_ok2 s C' (map admininstr_val vs) 
          (mk_functype (mk_list []) (mk_list (map typeofval vs)))" 
      using splitih' Instrs_ok2_const_replace splitih0 Instrs_ok2_wf by blast
    have sucl: "proj_uN_0 l + 1 = Suc (proj_uN_0 l)" by auto
    have "LABELS C' ! proj_uN_0 l = mk_list tsbr"
      proof (cases "LABELS C' ! proj_uN_0 l")
      case (mk_list x)
      then show ?thesis using proj2 proj_list_0.domintros proj_list_0.psimps by metis
    qed
    then obtain vs1 vs2 where 
      "vs = vs1 @ vs2" 
      "Resulttype_sub (mk_list (map typeofval vs2)) (mk_list tsbr)"
      using inv_label_const_list_br td(1) sucl
      by metis 
    then have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti:
                 mk_instrtype (mk_list []) (mk_list (map typeofval vs1 @ tsbr))" 
      using mk_Instrtype_sub Resulttype_sub_refl 
      using Instrtype_sub_sub_rule Resulttype_sub_append by simp
    then have "Instrs_ok2 s C' (map admininstr_val vs @ 
              [admininstr_sc0 (admininstr_st0_BR l)])
              (mk_functype (mk_list []) (mk_list ts)) "  
      using 
        vsok
        instr_ok2_instrs_ok2[OF
        instr_ok_instr_ok2[OF 
          br[OF proj1 proj2 Instrs_ok2_wf(1)[OF splitih0(1)] wfbr, of "map typeofval vs1" ts]
           Instrs_ok2_wf(2)[OF splitih0(1)]]]
        instrs_ok2_seq[of s C' "map admininstr_val vs" "mk_list []" 
              "mk_list (map typeofval vs1 @ tsbr)" "[_]" "mk_list ts"]
        Instrs_ok2_subtyping
      by (simp add: admininstr_instr.domintros(8) admininstr_instr.psimps(8))
    then show ?case using splitihbr(3) splitih''(2) subvs 
         br_succ(9) splitih0(5) td(2)
      using Instrs_ok2_subtyping by blast
  next
    case (br_if_true c l)
    then obtain t2 where split:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" 
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BR_IF l)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce 
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2"
      using inv_const_list[OF split(1), of "[val_CONST I32 c]"]
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps
      by simp
    obtain ts2' ts3' where 
      "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_BR_IF l)) (mk_functype ts2' ts3')" 
      and subt: "mk_instrtype ts2' ts3' <ti: mk_instrtype t2 t3" 
      using split inv_one_admininstr by blast
    then have brifok: "Instr_ok C' (instr_sc0 (BR_IF l)) (mk_functype ts2' ts3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by simp
    then obtain ts where brhyps:
      "proj_uN_0 l < length (LABELS C')"
      "proj_list_0 (LABELS C' ! proj_uN_0 l) = ts"
      "mk_functype (mk_list (ts @ [valtype_I32])) (mk_list ts) = mk_functype ts2' ts3'"
      using inv_br_if by blast
    then have sub: "mk_instrtype (mk_list ts) (mk_list ts) <ti: mk_instrtype t1 t3"
      using produce_consume[of "[valtype_I32]" t1 t2 ts "[valtype_I32]" ts t3]
        subv subt by fastforce
    have wfbr: "wf_instr (instr_sc0 (BR l))" using br_if_true(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    show ?case using subv 
        br[OF brhyps(1) brhyps(2) Instrs_ok2_wf(1)[OF split(1)] wfbr, of "[]" ts] 
        instr_ok_instr_ok2 instr_ok2_instrs_ok2 
        Instrs_ok2_wf(2)[OF split(1)] br_if_true(11)
        Instrs_ok2_subtyping sub 
      by (metis admininstr_instr.domintros(8) admininstr_instr.psimps(8) append_Nil)
  next
    case (br_if_false c l)
 then obtain t2 where split:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" 
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BR_IF l)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce 
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2"
      using inv_const_list[OF split(1), of "[val_CONST I32 c]"]
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps
      by simp
    obtain ts2' ts3' where 
      "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_BR_IF l)) (mk_functype ts2' ts3')" 
      and subt: "mk_instrtype ts2' ts3' <ti: mk_instrtype t2 t3" 
      using split inv_one_admininstr by blast
    then have brifok: "Instr_ok C' (instr_sc0 (BR_IF l)) (mk_functype ts2' ts3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by simp
    then obtain ts where brhyps:
      "proj_uN_0 l < length (LABELS C')"
      "proj_list_0 (LABELS C' ! proj_uN_0 l) = ts"
      "mk_functype (mk_list (ts @ [valtype_I32])) (mk_list ts) = mk_functype ts2' ts3'"
      using inv_br_if by blast
    then have sub: "mk_instrtype (mk_list ts) (mk_list ts) <ti: mk_instrtype t1 t3"
      using produce_consume[of "[valtype_I32]" t1 t2 ts "[valtype_I32]" ts t3]
        subv subt by fastforce
    have "mk_instrtype (mk_list []) (mk_list []) <ti: mk_instrtype (mk_list ts) (mk_list ts)" 
      by (metis Instrtype_sub_frame_rule append.right_neutral)
    then show ?case using Instrs_ok2__empty Instrs_ok2_wf[OF split(1)] 
      br_if_false(11) sub Instrs_ok2_subtyping by auto
  next
    case (br_table_lt c ls l)
    then obtain t2 where split:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" 
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_BR_TABLE ls l)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce 
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2"
      using inv_const_list[OF split(1), of "[val_CONST I32 c]"]
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps
      by simp
    obtain ts2' ts3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_BR_TABLE ls l)) (mk_functype ts2' ts3')" 
      and subt: "mk_instrtype ts2' ts3' <ti: mk_instrtype t2 t3" 
      using split inv_one_admininstr by blast
    then have brifok: "Instr_ok C' (instr_sc0 (BR_TABLE ls l)) (mk_functype ts2' ts3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by simp
    then obtain ts tbef taft where brhyps:
      "list_all (\<lambda>l. proj_uN_0 l < length (LABELS C')) ls"
      "list_all (\<lambda>l. Resulttype_sub (mk_list ts) (LABELS C' ! proj_uN_0 l)) ls"
      "proj_uN_0 l < length (LABELS C')"
      "Resulttype_sub (mk_list ts) (LABELS C' ! proj_uN_0 l)"
      "mk_functype (mk_list (tbef @ ts @ [valtype_I32])) (mk_list taft) = mk_functype ts2' ts3'"
      using inv_br_table by blast  
    then have sub: "mk_instrtype (mk_list (tbef @ ts)) (mk_list taft) <ti: mk_instrtype t1 t3"
      using produce_consume[of "[valtype_I32]" t1 t2 "tbef @ ts" "[valtype_I32]" taft t3]
        subv subt by fastforce
    have wfbr: "wf_instr (instr_sc0 (BR (ls ! proj_uN_0 (the (proj_num__0 c)))))" 
       using br_table_lt(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then have brok: "Instr_ok C' (instr_sc0 (BR (ls ! proj_uN_0 (the (proj_num__0 c))))) 
                (mk_functype (mk_list (tbef @  
                  proj_list_0 (LABELS C' ! proj_uN_0 (ls ! proj_uN_0 (the (proj_num__0 c)))))) 
              (mk_list taft))" 
      using br brhyps br_table_lt(1) list_all_length Instrs_ok2_wf(1)[OF split(1)]
      by meson
    have "mk_instrtype (mk_list (tbef @  
                  proj_list_0 (LABELS C' ! proj_uN_0 (ls ! proj_uN_0 (the (proj_num__0 c)))))) 
              (mk_list taft) <ti: mk_instrtype (mk_list (tbef @ ts)) (mk_list taft)" 
      using 
        Instrtype_sub_sub_rule[of "mk_list (tbef @ ts)" "mk_list (tbef @ proj_list_0 
            (LABELS C' ! proj_uN_0 (ls ! proj_uN_0 (the (proj_num__0 c)))))" "mk_list taft" 
            "mk_list taft"]
        Resulttype_sub_append[OF Resulttype_sub_refl[of "mk_list tbef"], of ts 
            "proj_list_0 (LABELS C' ! proj_uN_0 (ls ! proj_uN_0 (the (proj_num__0 c))))"] 
        brhyps(2) br_table_lt(1) list_all_length Resulttype_sub_refl[of "mk_list taft"]
        mk_list_proj_list_0 by metis
    then have "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BR 
              (ls ! proj_uN_0 (the (proj_num__0 c))))]
                (mk_functype (mk_list (tbef @ ts)) (mk_list taft))"
      using instr_ok_instr_ok2 instr_ok2_instrs_ok2 Instrs_ok2_subtyping brok 
        Instrs_ok2_wf(2)[OF split(1)]
      by (metis admininstr_instr.domintros(8) admininstr_instr.psimps(8))
    then show ?case using sub Instrs_ok2_subtyping br_table_lt(11)
      Instrtype_sub_sub_rule by meson
  next
    case (br_table_ge c ls l)
    then obtain t2 where split:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" 
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_BR_TABLE ls l)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce 
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2"
      using inv_const_list[OF split(1), of "[val_CONST I32 c]"]
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps
      by simp
    obtain ts2' ts3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_BR_TABLE ls l)) (mk_functype ts2' ts3')" 
      and subt: "mk_instrtype ts2' ts3' <ti: mk_instrtype t2 t3" 
      using split inv_one_admininstr by blast
    then have brifok: "Instr_ok C' (instr_sc0 (BR_TABLE ls l)) (mk_functype ts2' ts3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by simp
    then obtain ts tbef taft where brhyps:
      "list_all (\<lambda>l. proj_uN_0 l < length (LABELS C')) ls"
      "list_all (\<lambda>l. Resulttype_sub (mk_list ts) (LABELS C' ! proj_uN_0 l)) ls"
      "proj_uN_0 l < length (LABELS C')"
      "Resulttype_sub (mk_list ts) (LABELS C' ! proj_uN_0 l)"
      "mk_functype (mk_list (tbef @ ts @ [valtype_I32])) (mk_list taft) = mk_functype ts2' ts3'"
      using inv_br_table by blast  
    then have sub: "mk_instrtype (mk_list (tbef @ ts)) (mk_list taft) <ti: mk_instrtype t1 t3"
      using produce_consume[of "[valtype_I32]" t1 t2 "tbef @ ts" "[valtype_I32]" taft t3]
        subv subt by fastforce
    have wfbr: "wf_instr (instr_sc0 (BR l))"  using br_table_ge(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then have brok: "Instr_ok C' (instr_sc0 (BR l)) 
                (mk_functype (mk_list (tbef @  
                  proj_list_0 (LABELS C' ! proj_uN_0 l))) 
              (mk_list taft))" 
      using br brhyps Instrs_ok2_wf(1)[OF split(1)]
      by meson
    have "mk_instrtype (mk_list (tbef @  
                  proj_list_0 (LABELS C' ! proj_uN_0 l))) 
              (mk_list taft) <ti: mk_instrtype (mk_list (tbef @ ts)) (mk_list taft)" 
      using 
        Instrtype_sub_sub_rule[of "mk_list (tbef @ ts)" "mk_list (tbef @ proj_list_0 
            (LABELS C' ! proj_uN_0 l))" "mk_list taft" 
            "mk_list taft"]
        Resulttype_sub_append[OF Resulttype_sub_refl[of "mk_list tbef"], of ts 
            "proj_list_0 (LABELS C' ! proj_uN_0 l)"] 
        brhyps(4) Resulttype_sub_refl[of "mk_list taft"]
        mk_list_proj_list_0 by metis
    then have "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BR 
              l)]
                (mk_functype (mk_list (tbef @ ts)) (mk_list taft))"
      using instr_ok_instr_ok2 instr_ok2_instrs_ok2 Instrs_ok2_subtyping brok 
        Instrs_ok2_wf(2)[OF split(1)]
      by (metis admininstr_instr.domintros(8) admininstr_instr.psimps(8))
    then show ?case using sub Instrs_ok2_subtyping br_table_ge(11)
      Instrtype_sub_sub_rule by meson
  next
    case (frame_vals n vs f)
    then obtain ts1 ts2 where 
      "Instr_ok2 s C' (admininstr_sc8 (FRAME_underscore n f (map admininstr_val vs)))
          (mk_functype ts1 ts2)" 
      and sub: "mk_instrtype ts1 ts2 <ti: mk_instrtype t1 t3" 
      using inv_one_admininstr by blast
    then obtain Cf ts where invframe:
        "Frame_ok s f Cf" 
        "Expr_ok2 s Cf (map admininstr_val vs) (mk_list ts)"
        "wf_context Cf" "n = length ts" 
        "mk_functype (mk_list []) (mk_list ts) = mk_functype ts1 ts2"
      using inv_frame by blast
    then have inv:
        "Instrs_ok2 s Cf (map admininstr_val vs) (mk_functype (mk_list []) (mk_list ts))"
      using inv_expr by blast
    then show ?case using sub frame_vals(10) invframe(5) Instrs_ok2_subtyping
      by (metis Instrs_ok2_subtyping invframe(5) pure.prems(9) inv local.sub 
          inv_const_list pure.prems(8) Instrs_ok2_wf(1) Instrs_ok2_const_replace)
  next
    case (return_frame n vs f vs' es)
    then obtain t1' t2' where
      "Instr_ok2 s C' (admininstr_sc8
       (FRAME_underscore n f
         (((map admininstr_val vs' @ map admininstr_val vs) @ [admininstr_sc1 admininstr_st1_RETURN]) @
          map admininstr_instr es))) (mk_functype t1' t2')"
      and subt: "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3" 
      using inv_one_admininstr by blast
    then obtain Cf ts where framehyps:
      "Frame_ok s f Cf"
      "Expr_ok2 s Cf (((map admininstr_val vs' @ map admininstr_val vs) @ [admininstr_sc1 admininstr_st1_RETURN]) @
          map admininstr_instr es) (mk_list ts)"
      "wf_context Cf" "n = length ts" "context_RETURN Cf = Some (mk_list ts)"
      "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'"
      using inv_frame by blast
    then have "Instrs_ok2 s Cf (((map admininstr_val vs' @ map admininstr_val vs) @ 
            [admininstr_sc1 admininstr_st1_RETURN]) @
          map admininstr_instr es) (mk_functype (mk_list []) (mk_list ts))" 
      using inv_expr by blast
    then obtain ts2 where splites:
      "Instrs_ok2 s Cf ((map admininstr_val vs' @ map admininstr_val vs) @ 
            [admininstr_sc1 admininstr_st1_RETURN]) (mk_functype (mk_list []) ts2)"
      "Instrs_ok2 s Cf (map admininstr_instr es) (mk_functype ts2 (mk_list ts))" 
      using inv_seq by blast
    then obtain ts2' where splitret:
      "Instrs_ok2 s Cf (map admininstr_val vs' @ map admininstr_val vs) (mk_functype (mk_list []) ts2')"
      "Instrs_ok2 s Cf [admininstr_sc1 admininstr_st1_RETURN] (mk_functype ts2' ts2)" 
      using inv_seq by blast
    then obtain ts2'' ts3'' where 
      "Instr_ok2 s Cf (admininstr_sc1 admininstr_st1_RETURN) (mk_functype ts2'' ts3'')"
      and subt': "mk_instrtype ts2'' ts3'' <ti: mk_instrtype ts2' ts2"
      using inv_one_admininstr by blast
    then have "Instr_ok Cf (instr_sc1 RETURN) (mk_functype ts2'' ts3'')"
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain tret tbef taft where rethyps:
      "context_RETURN Cf = Some (mk_list tret)"
      "mk_functype (mk_list (tbef @ tret)) (mk_list taft) = mk_functype ts2'' ts3''"
      using inv_return by blast
    then obtain tv2 where splitvs:
      "Instrs_ok2 s Cf (map admininstr_val vs') (mk_functype (mk_list []) tv2)"
      "Instrs_ok2 s Cf (map admininstr_val vs) (mk_functype tv2 ts2')" 
      using splitret inv_seq by blast
    then have subv1: "mk_instrtype (mk_list []) (mk_list (map typeofval vs')) <ti: mk_instrtype (mk_list []) tv2"
      using inv_const_list by blast
    have subv2: "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: mk_instrtype tv2 ts2'"
      using splitvs inv_const_list by blast
    have subv: "mk_instrtype (mk_list []) (mk_list (map typeofval vs' @ map typeofval vs)) <ti:
      mk_instrtype (mk_list []) ts2'" using splitret(1) inv_const_list
      by (metis inv_const_list splitret(1) map_append)
    have "Resulttype_sub (mk_list (map typeofval vs)) (mk_list ts)"
      using produce_consume_waste[OF subv] rethyps subt' return_frame(1) framehyps(4,5)
      by force
    then have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: mk_instrtype t1 t3" 
      using return_frame(10) subt framehyps(6) Instrtype_sub_sub_rule Resulttype_sub_refl
      using Instrtype_sub_trans by blast
    then show ?case 
      using splitvs(1) Instrs_ok2_const_replace Instrs_ok2_wf(1)[OF return_frame(9)]
      Instrs_ok2_subtyping
      using return_frame.prems(9) splitvs(2) by force
  next
    case (return_label n es' vs es)
 then obtain t1' t2' where td:
      "Instr_ok2 s C'
     (admininstr_sc8
       (LABEL_underscore n es'
         ((map admininstr_val vs @ [admininstr_sc1 (admininstr_st1_RETURN)]) @
          map admininstr_instr es))) (mk_functype t1' t2')"
      "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using inv_one_admininstr by blast
    then obtain ts ts' where splitih0: 
        "Instrs_ok2 s C' (map admininstr_instr es')
        (mk_functype (mk_list ts') (mk_list ts))"
       "Instrs_ok2 s
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C')
         (((map admininstr_val vs) @
           [admininstr_sc1 (admininstr_st1_RETURN)]) @
          map admininstr_instr es) (mk_functype (mk_list []) (mk_list ts))"
       "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
           LABELS = [mk_list ts'], context_RETURN = None\<rparr>"
       "n = length ts'" 
       "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'" 
      using inv_label by blast
    then obtain ts2 where splitih:
       "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ((map admininstr_val vs) @ 
              [admininstr_sc1 (admininstr_st1_RETURN)]) (mk_functype (mk_list []) ts2)"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_instr es) (mk_functype ts2 (mk_list ts))"
      using inv_seq by blast 
    then obtain ts2' where splitih': 
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs) (mk_functype (mk_list []) ts2')"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') [admininstr_sc1 (admininstr_st1_RETURN)] (mk_functype ts2' ts2)" 
      using inv_seq by blast
    then obtain ts2'' ts3'' where splitih'': 
       "Instr_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (admininstr_sc1 admininstr_st1_RETURN) (mk_functype ts2'' ts3'')" 
        "mk_instrtype ts2'' ts3'' <ti: mk_instrtype ts2' ts2"
      using inv_one_admininstr by blast
    then have brok: "Instr_ok (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (instr_sc1 RETURN) (mk_functype ts2'' ts3'')" 
using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain tsbr ts1br ts2br where splitihbr:
      "context_RETURN (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') = Some (mk_list tsbr)"
      "mk_functype (mk_list (ts1br @ tsbr)) (mk_list ts2br) = mk_functype ts2'' ts3''" 
      using inv_return by blast
    have proj2: "context_RETURN C' = Some (mk_list tsbr)" 
    proof (cases C')
      case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
            context_ELEMS context_DATAS context_LOCALS context_LABELS context_RETURN)
      then have "res_context.context_RETURN (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') = res_context.context_RETURN C'" using append_res_context_def by simp
      then show ?thesis using splitihbr fields by force
    qed
    have wfbr: "wf_instr (instr_sc1 RETURN)"  using return_label(10) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    have subvs: "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: 
          mk_instrtype (mk_list []) ts2'" using splitih' inv_const_list by blast
    have vsok: "Instrs_ok2 s C' (map admininstr_val vs) 
          (mk_functype (mk_list []) (mk_list (map typeofval vs)))" 
      using splitih' Instrs_ok2_const_replace splitih0 Instrs_ok2_wf by blast
    then obtain vs1 vs2 where 
      "vs = vs1 @ vs2" 
      "Resulttype_sub (mk_list (map typeofval vs2)) (mk_list tsbr)"
      using inv_label_const_list_return td(1) proj2
      by metis 
    then have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti:
                 mk_instrtype (mk_list []) (mk_list (map typeofval vs1 @ tsbr))" 
      using mk_Instrtype_sub Resulttype_sub_refl 
      using Instrtype_sub_sub_rule Resulttype_sub_append by simp
    then have "Instrs_ok2 s C' (map admininstr_val vs @ 
              [admininstr_sc1 (admininstr_st1_RETURN)])
              (mk_functype (mk_list []) (mk_list ts)) "  
      using 
        vsok
        instr_ok2_instrs_ok2[OF
        instr_ok_instr_ok2[OF 
          return[OF proj2 Instrs_ok2_wf(1)[OF splitih0(1)] wfbr, of "map typeofval vs1" ts]
           Instrs_ok2_wf(2)[OF splitih0(1)]]]
        instrs_ok2_seq[of s C' "map admininstr_val vs" "mk_list []" 
              "mk_list (map typeofval vs1 @ tsbr)" "[_]" "mk_list ts"]
        Instrs_ok2_subtyping
      by (simp add: admininstr_instr.domintros admininstr_instr.psimps)
    then show ?case using splitihbr(2) splitih''(2) subvs 
        return_label(9) splitih0(5) td(2)
      using Instrs_ok2_subtyping by blast
  next
    case (trap_vals val_lst instr_lst)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (trap_label v_n instr'_lst)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (trap_frame v_n f)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (unop_val nt unop c_1 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST nt c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_UNOP nt unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_UNOP nt unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc1 (UNOP nt unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_numtype nt]) (mk_list [valtype_numtype nt]) =
        mk_functype t2' t3'" using inv_unop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST nt c))" 
       using unop_val(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using unop_val(11) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF unop_val(10)] subt
      by (metis admininstr_instr.domintros(14) admininstr_instr.psimps(14))
  next
    case (unop_trap nt unop c_1)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (binop_val nt binop c_1 c_2 var_0 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST nt c_1),
                        admininstr_sc1 (admininstr_st1_CONST nt c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_BINOP nt binop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt, valtype_numtype nt]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_CONST _ _, val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_BINOP nt binop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc1 (BINOP nt binop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_numtype nt, valtype_numtype nt]) (mk_list [valtype_numtype nt]) =
        mk_functype t2' t3'" using inv_binop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST nt c))" 
       using binop_val(13) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using binop_val(12) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF binop_val(11)] subt
      by (metis admininstr_instr.domintros(14) admininstr_instr.psimps(14))
  next
    case (binop_trap nt binop c_1 c_2 var_0)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (Step_pure__testop c nt testop c_1)
     then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST nt c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_TESTOP nt testop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_TESTOP nt testop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc1 (TESTOP nt testop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_numtype nt]) (mk_list [valtype_I32]) =
        mk_functype t2' t3'" using inv_testop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST I32 c))" 
       using Step_pure__testop(11) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    
    then show ?case using Step_pure__testop(10) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__testop(9)] subt valtype_numtype.domintros
      valtype_numtype.psimps
      by (metis admininstr_instr.domintros(14) admininstr_instr.psimps(14))
  next
    case (Step_pure__relop nt relop c_1 c_2 var_0 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST nt c_1),
                        admininstr_sc1 (admininstr_st1_CONST nt c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_RELOP nt relop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt, valtype_numtype nt]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_CONST _ _, val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_RELOP nt relop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc1 (RELOP nt relop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_numtype nt, valtype_numtype nt]) (mk_list [valtype_I32]) =
        mk_functype t2' t3'" using inv_relop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST I32 c))" 
       using Step_pure__relop(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__relop(11) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__relop(10)] subt valtype_numtype.domintros
      valtype_numtype.psimps
      by (metis admininstr_instr.domintros(14) admininstr_instr.psimps(14))
  next
    case (cvtop_val nt_1 nt_2 v_cvtop c_1 var_0 c)
      then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST nt_1 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_CVTOP nt_2 nt_1 v_cvtop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt_1]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc2 (admininstr_st2_CVTOP nt_2 nt_1 v_cvtop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc1 (CVTOP nt_2 nt_1 v_cvtop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_numtype nt_1]) (mk_list [valtype_numtype nt_2]) =
        mk_functype t2' t3'" using inv_cvtop_convert by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt_2]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST nt_2 c))" 
       using cvtop_val(13) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using cvtop_val(12) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF cvtop_val(11)] subt
      by (metis admininstr_instr.domintros(14) admininstr_instr.psimps(14))
  next
    case (cvtop_trap nt_1 nt_2 v_cvtop c_1 var_0)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (ref_is_null_true v_ref rt)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_ref v_ref] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_REF_IS_NULL)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [typeofval (val_ref v_ref)]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_ref v_ref]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps
        val_ref.domintros val_ref.psimps
      by (metis Ref_ok_ref_NULL_unique functype.inject inv_one_admininstr inv_ref ref_is_null_true.hyps
          splitunop(1))
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_REF_IS_NULL)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc4 REF_IS_NULL) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain rt where 
      "mk_functype (mk_list [valtype_reftype rt]) (mk_list [valtype_I32]) =
        mk_functype t2' t3'" using inv_ref_is_null by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
                mk_instrtype t1 t3" "Resulttype_sub (mk_list [typeofval (val_ref v_ref)]) 
                  (mk_list [valtype_reftype rt])" 
      using subt produce_consume[OF subv, of "[]" "[valtype_reftype rt]" "[valtype_I32]" t3]
      by auto
    have "wf_instr (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1))))" 
       using ref_is_null_true(11) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using ref_is_null_true(10) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF ref_is_null_true(9)] subt(1)
      admininstr_instr.domintros(14) admininstr_instr.psimps(14) valtype_numtype.domintros 
      valtype_numtype.psimps by metis
  next
    case (ref_is_null_false v_ref)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_ref v_ref] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_REF_IS_NULL)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [typeofval (val_ref v_ref)]) <ti:
                mk_instrtype t1 t2" 
    proof(cases v_ref)
      case (ref_REF_NULL x1)
      then show ?thesis using ref_is_null_false
        using ref_is_null_true_0 by blast
    next
      case (REF_FUNC_ADDR x2)
      then show ?thesis using inv_const_list[OF splitunop(1), of "[val_ref v_ref]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps
        val_ref.domintros val_ref.psimps admininstr_ref.domintros admininstr_ref.psimps by simp
    next
      case (REF_HOST_ADDR x3)
      then show ?thesis using inv_const_list[OF splitunop(1), of "[val_ref v_ref]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps
        val_ref.domintros val_ref.psimps admininstr_ref.domintros admininstr_ref.psimps by simp
    qed
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_REF_IS_NULL)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc4 REF_IS_NULL) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain rt where 
      "mk_functype (mk_list [valtype_reftype rt]) (mk_list [valtype_I32]) =
        mk_functype t2' t3'" using inv_ref_is_null by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
                mk_instrtype t1 t3" "Resulttype_sub (mk_list [typeofval (val_ref v_ref)]) 
                  (mk_list [valtype_reftype rt])" 
      using subt produce_consume[OF subv, of "[]" "[valtype_reftype rt]" "[valtype_I32]" t3]
      by auto
    have "wf_instr (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))" 
       using ref_is_null_false(11) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using ref_is_null_false(10) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF ref_is_null_false(9)] subt(1)
      admininstr_instr.domintros(14) admininstr_instr.psimps(14) valtype_numtype.domintros 
      valtype_numtype.psimps by metis
  next
    case (Step_pure__vvunop c unop c_1)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VVUNOP V128 unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc2 (admininstr_st2_VVUNOP V128 unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VVUNOP V128 unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vvunop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vvunop(11) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vvunop(10) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vvunop(9)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vvbinop c unop c_1 c_2)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VVBINOP V128 unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc2 (admininstr_st2_VVBINOP V128 unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VVBINOP V128 unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vvbinop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vvbinop(11) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vvbinop(10) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vvbinop(9)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vvternop c unop c_1 c_2 c_3)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_2),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_3)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VVTERNOP V128 unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_,_]" t1 t3 "[_,_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_V128, valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_VCONST _ _, val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc2 (admininstr_st2_VVTERNOP V128 unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VVTERNOP V128 unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_V128, valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vvternop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))"
       using Step_pure__vvternop(11) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vvternop(10) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vvternop(9)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vvtestop c c_1)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VVTESTOP V128 ANY_TRUE)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc2 (admininstr_st2_VVTESTOP V128 ANY_TRUE)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VVTESTOP V128 ANY_TRUE)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]) =
        mk_functype t2' t3'" using inv_vvtestop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST I32 c))" 
       using Step_pure__vvtestop(14) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vvtestop(13) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vvtestop(12)] subt
      admininstr_instr.domintros(14) admininstr_instr.psimps(14) valtype_numtype.domintros(1)
      valtype_numtype.psimps(1) by metis
  next
    case (Step_pure__vunop sh unop c_1 var_0 c) 
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VUNOP sh unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc2 (admininstr_st2_VUNOP sh unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VUNOP sh unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vunop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vunop(13) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vunop(12) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vunop(11)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (vunop_trap sh vunop c_1 var_0)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (vbinop_val sh unop c_1 c_2 var_0 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VBINOP sh unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc2 (admininstr_st2_VBINOP sh unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VBINOP sh unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vbinop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using vbinop_val(13) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using vbinop_val(12) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF vbinop_val(11)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (vbinop_trap sh vbinop c_1 c_2 var_0)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (vtestop_true ci_1_lst v_Jnn v_N c_1)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N))
               (mk_vtestop__0 v_Jnn v_N ALL_TRUE))] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N))
               (mk_vtestop__0 v_Jnn v_N ALL_TRUE))) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N))
               (mk_vtestop__0 v_Jnn v_N ALL_TRUE))) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]) =
        mk_functype t2' t3'" using inv_vtestop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1))))" 
       using vtestop_true(15) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using vtestop_true(14) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF vtestop_true(13)] subt valtype_numtype.domintros
      valtype_numtype.psimps
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (vtestop_false c_1 v_Jnn v_N)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N))
               (mk_vtestop__0 v_Jnn v_N ALL_TRUE))] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N))
               (mk_vtestop__0 v_Jnn v_N ALL_TRUE))) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N))
               (mk_vtestop__0 v_Jnn v_N ALL_TRUE))) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]) =
        mk_functype t2' t3'" using inv_vtestop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))" 
       using vtestop_false(11) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using vtestop_false(10) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF vtestop_false(9)] subt valtype_numtype.domintros
      valtype_numtype.psimps
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vrelop sh unop c_1 c_2 var_0 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VRELOP sh unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VRELOP sh unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VRELOP sh unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vrelop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vrelop(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vrelop(11) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vrelop(10)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vshiftop var_0_lst c'_lst v_Jnn v_N unop v_n c_1 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))] 
              (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VSHIFTOP (ishape_X v_Jnn (mk_dim v_N)) unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_I32]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps valtype_numtype.domintros valtype_numtype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VSHIFTOP (ishape_X v_Jnn (mk_dim v_N)) unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc2 (VSHIFTOP (ishape_X v_Jnn (mk_dim v_N)) unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_I32]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vshiftop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vshiftop(18) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vshiftop(17) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vshiftop(16)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vbitmask var_0_lst ci_1_lst v_Jnn v_N c ci)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VBITMASK (ishape_X v_Jnn (mk_dim v_N)))] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VBITMASK (ishape_X v_Jnn (mk_dim v_N)))) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VBITMASK (ishape_X v_Jnn (mk_dim v_N)))) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]) =
        mk_functype t2' t3'" using inv_vbitmask by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32
              (irev_underscore
                (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
    (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))))
                ci))))"
       using Step_pure__vbitmask(18) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vbitmask(17) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vbitmask(16)] subt
      admininstr_instr.domintros admininstr_instr.psimps valtype_numtype.domintros 
          valtype_numtype.psimps by metis
  next
    case (Step_pure__vswizzle ci_lst v_Pnn v_M c_2 c_1 c'_lst c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VSWIZZLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M)))] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VSWIZZLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M)))) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VSWIZZLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M)))) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vswizzle by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vswizzle(20) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vswizzle(19) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vswizzle(18)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vshuffle v_Pnn c'_lst v_M c_1 c_2 i_lst c) then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VSHUFFLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M)) i_lst)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VSHUFFLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M)) i_lst)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VSHUFFLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M)) i_lst)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have shuffhyps:
        "list_all (\<lambda>i. proj_uN_0 i < 2 * proj_dim_0 (fun_dim (shape_ishape 
            (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M))))) i_lst"
        "wf_dim (fun_dim (shape_ishape (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M))))"
        "mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vshuffle by auto
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vshuffle(17) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vshuffle(16) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vshuffle(15)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vsplat c v_Lnn v_N c_1)then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST (unpack v_Lnn) c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VSPLAT (X v_Lnn (mk_dim v_N)))] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_numtype (unpack v_Lnn)]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VSPLAT (X v_Lnn (mk_dim v_N)))) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VSPLAT (X v_Lnn (mk_dim v_N)))) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_numtype (unpack v_Lnn)]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vsplat shunpack.domintros shunpack.psimps by metis
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
     have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vsplat(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vsplat(11) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vsplat(10)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (vextract_lane_num i nt v_N c_1 c_2)
      then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_numtype (shunpack (X (lanetype_numtype nt) (mk_dim v_N)))]) =
        mk_functype t2' t3'" using inv_vextract_lane by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_numtype (shunpack (X (lanetype_numtype nt) (mk_dim v_N)))]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have eqt: "shunpack (X (lanetype_numtype nt) (mk_dim v_N)) = nt" 
    proof(cases nt)
    qed(simp_all add: shunpack.domintros shunpack.psimps unpack.domintros unpack.psimps
            lanetype_numtype.domintros lanetype_numtype.psimps)+
     have "wf_instr (instr_sc1 (res_CONST nt c_2))" 
       using vextract_lane_num(14) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using vextract_lane_num(13) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF vextract_lane_num(12)] subt
      admininstr_instr.domintros admininstr_instr.psimps eqt by metis
  next
    case (vextract_lane_pack c_2 pt v_N c_1 i v_sx)
      then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_numtype (shunpack (X (lanetype_packtype pt) (mk_dim v_N)))]) =
        mk_functype t2' t3'" using inv_vextract_lane by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_numtype (shunpack (X (lanetype_packtype pt) (mk_dim v_N)))]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
     have eqt: "shunpack (X (lanetype_packtype pt) (mk_dim v_N)) = I32" 
    proof(cases pt) 
    qed(simp_all add: shunpack.domintros shunpack.psimps unpack.domintros unpack.psimps
            lanetype_packtype.domintros lanetype_packtype.psimps)+ 
     have "wf_instr (instr_sc1 (res_CONST I32 c_2))" 
       using vextract_lane_pack(15) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using vextract_lane_pack(14) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF vextract_lane_pack(13)] subt
      admininstr_instr.domintros admininstr_instr.psimps eqt by metis
  next
    case (Step_pure__vreplace_lane c v_Lnn v_N c_1 i c_2)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc1 (admininstr_st1_CONST (unpack v_Lnn) c_2)] 
              (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc3 (admininstr_st3_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_numtype (unpack v_Lnn)]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps valtype_numtype.domintros valtype_numtype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc3 (admininstr_st3_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_numtype (unpack v_Lnn)]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vreplace_lane shunpack.domintros shunpack.psimps by metis
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vreplace_lane(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vreplace_lane(11) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vreplace_lane(10)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vextunop sh_1 sh_2 unop c_1 var_0 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_VEXTUNOP sh_1 sh_2 unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_VEXTUNOP sh_1 sh_2 unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VEXTUNOP sh_1 sh_2 unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vextunop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vextunop(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vextunop(11) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vextunop(10)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vextbinop sh_1 sh_2 unop c_1 c_2 var_0 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_VEXTBINOP sh_1 sh_2 unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_VEXTBINOP sh_1 sh_2 unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VEXTBINOP sh_1 sh_2 unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vextbinop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vextbinop(12) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vextbinop(11) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vextbinop(10)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__vnarrow ci_1_lst Jnn_1 N_1 c_1 ci_2_lst c_2 cj_1_lst Jnn_2 v_sx cj_2_lst c N_2)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1),
                        admininstr_sc2 (admininstr_st2_VCONST V128 c_2)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_VNARROW (ishape_X Jnn_2 (mk_dim N_2)) (ishape_X Jnn_1 (mk_dim N_1)) v_sx)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_]" t1 t3 "[_,_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128, valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _, val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_VNARROW (ishape_X Jnn_2 (mk_dim N_2)) (ishape_X Jnn_1 (mk_dim N_1)) v_sx)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc3 (VNARROW (ishape_X Jnn_2 (mk_dim N_2)) (ishape_X Jnn_1 (mk_dim N_1)) v_sx)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vnarrow by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using Step_pure__vnarrow(23) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using Step_pure__vnarrow(22) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF Step_pure__vnarrow(21)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (vcvtop_full v_vcvtop ci_lst Lnn_1 v_M c_1 cj_lst_lst Lnn_2 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_VCVTOP (X Lnn_2 (mk_dim v_M)) (X Lnn_1 (mk_dim v_M)) v_vcvtop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_VCVTOP (X Lnn_2 (mk_dim v_M)) (X Lnn_1 (mk_dim v_M)) v_vcvtop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc4 (VCVTOP (X Lnn_2 (mk_dim v_M)) (X Lnn_1 (mk_dim v_M)) v_vcvtop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vcvtop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using vcvtop_full(19) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using vcvtop_full(18) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF vcvtop_full(17)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (vcvtop_half v_vcvtop v_half ci_lst Lnn_1 M_1 c_1 M_2 cj_lst_lst Lnn_2 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_VCVTOP (X Lnn_2 (mk_dim M_2)) (X Lnn_1 (mk_dim M_1)) v_vcvtop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_VCVTOP (X Lnn_2 (mk_dim M_2)) (X Lnn_1 (mk_dim M_1)) v_vcvtop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc4 (VCVTOP (X Lnn_2 (mk_dim M_2)) (X Lnn_1 (mk_dim M_1)) v_vcvtop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vcvtop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using vcvtop_half(19) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using vcvtop_half(18) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF vcvtop_half(17)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (vcvtop_zero v_vcvtop ci_lst nt_1 M_1 c_1 cj_lst_lst nt_2 M_2 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc2 (admininstr_st2_VCONST V128 c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_VCVTOP (X (lanetype_numtype nt_2) (mk_dim M_2)) (X (lanetype_numtype nt_1) (mk_dim M_1)) v_vcvtop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_VCONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps valtype_vectype.domintros
        valtype_vectype.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc4 (admininstr_st4_VCVTOP (X (lanetype_numtype nt_2) (mk_dim M_2)) (X (lanetype_numtype nt_1) (mk_dim M_1)) v_vcvtop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc4 (VCVTOP (X (lanetype_numtype nt_2) (mk_dim M_2)) (X (lanetype_numtype nt_1) (mk_dim M_1)) v_vcvtop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]) =
        mk_functype t2' t3'" using inv_vcvtop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_V128]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (VCONST V128 c))" 
       using vcvtop_zero(20) wf_admininstr_instr_inv
      admininstr_instr.domintros admininstr_instr.psimps by simp
    then show ?case using vcvtop_zero(19) vconst instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF vcvtop_zero(18)] subt
      admininstr_instr.domintros admininstr_instr.psimps by metis
  next
    case (Step_pure__local_tee v_val x)
    then obtain t2 where splitvs:
      "Instrs_ok2 s C' [admininstr_val v_val] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc5 (admininstr_st5_LOCAL_TEE x)] (mk_functype t2 t3)" 
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    then have subv:
      "mk_instrtype (mk_list []) (mk_list [typeofval v_val]) <ti: mk_instrtype t1 t2" 
      using inv_const_list[of s C' "[_]" t1 t2 "[_]"] by fastforce
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc5 (admininstr_st5_LOCAL_TEE x)) (mk_functype t2' t3')"
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using inv_one_admininstr splitvs by blast
    then have "Instr_ok C' (instr_sc4 (LOCAL_TEE x)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.psimps admininstr_instr.domintros by fastforce
    then obtain t where teehyps:
      "proj_uN_0 x < length (context_LOCALS C')"
      "context_LOCALS C' ! proj_uN_0 x = t" 
      "mk_functype (mk_list [t]) (mk_list [t]) = mk_functype t2' t3'" 
      using inv_local_tee by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3"
        "Resulttype_sub (mk_list [typeofval v_val]) (mk_list [t])"
      using subv subt produce_consume[of "[_]" t1 t2 "[]" "[_]" "[_]" t3] by auto 
    then have "mk_instrtype (mk_list []) (mk_list [typeofval v_val]) <ti:
        mk_instrtype (mk_list []) (mk_list [t])" using Instrtype_sub_sub_rule Resulttype_sub_refl
      by fast
    then have ok1: "Instrs_ok2 s C' [admininstr_val v_val] (mk_functype (mk_list []) (mk_list [t]))" 
      using splitvs(1) Instrs_ok2_const_replace Instrs_ok2_subtyping
      by (meson Instr_ok2_const_replace Instrs_ok2_wf(1) instr_ok2_instrs_ok2 inv_one_admininstr)
    then have ok2: "Instrs_ok2 s C' [admininstr_val v_val] (mk_functype (mk_list [t]) (mk_list [t,t]))"
      using Instrs_ok2__frame[where ?t_lst = "[t]"] Instrs_ok2_wf Instrs_ok2_wf_instr by auto
    have wfres: "wf_instr (instr_sc4 (LOCAL_SET x))" using Step_pure__local_tee(10)
      admininstr_instr.domintros admininstr_instr.psimps wf_admininstr_instr_inv by simp
    then have "Instr_ok C' (instr_sc4 (LOCAL_SET x)) (mk_functype (mk_list [t]) (mk_list []))" 
      using local_set teehyps Instrs_ok2_wf[OF splitvs(1)] by blast
     then have ok3: "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_LOCAL_SET x)]
        (mk_functype (mk_list [t]) (mk_list []))"
      using Instrs_ok2_wf[OF splitvs(1)] instr_ok_instr_ok2 instr_ok2_instrs_ok2
      by (metis admininstr_instr.domintros(45) admininstr_instr.psimps(45))
    then have ok3: "Instrs_ok2 s C' [admininstr_sc4 (admininstr_st4_LOCAL_SET x)]
        (mk_functype (mk_list [t,t]) (mk_list [t]))"
      using 
        Instrs_ok2_subtyping Instrtype_sub_frame_rule[of "[t]" "[]" "[t]"] 
      by auto
    have "Instrs_ok2 s C'
     [admininstr_val v_val, admininstr_val v_val, admininstr_sc4 (admininstr_st4_LOCAL_SET x)] 
      (mk_functype (mk_list []) (mk_list [t]))"
      using instrs_ok2_seq[OF ok1 ok2] instrs_ok2_seq[OF _ ok3] by force
    then show ?case using Step_pure__local_tee(9) subt Instrs_ok2_subtyping by blast
  qed

next
  case (read es es')
  then show ?case
  proof (induction "mk_config (mk_state s f) es" es' rule:Step_read.induct)
    case (Step_read__block bt t_1_lst t_2_lst k val_lst v_n instr_lst)
    then obtain t2 where splitvs: 
      "Instrs_ok2 s C' (map admininstr_val val_lst) (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BLOCK bt instr_lst)] (mk_functype t2 t3)"
      using inv_seq by blast
    then have subv: "mk_instrtype (mk_list []) (mk_list (map typeofval val_lst)) <ti:
               mk_instrtype t1 t2" using inv_const_list by blast
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_BLOCK bt instr_lst)) (mk_functype t2' t3')"
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3"
      using splitvs(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc7 (BLOCK bt instr_lst)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.psimps admininstr_instr.domintros by fastforce
    then obtain t1s t2s where blockhyps:
      "wf_context
    \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
       context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2s],
       context_RETURN = None\<rparr>"
   "Blocktype_ok C' bt (mk_functype (mk_list t1s) (mk_list t2s))"
   "Instrs_ok
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list t2s], context_RETURN = None\<rparr>
      C')
    instr_lst (mk_functype (mk_list t1s) (mk_list t2s))"
   "mk_functype (mk_list t1s) (mk_list t2s) = mk_functype t2' t3'"
      using inv_block by blast
    have eqt: "mk_functype (mk_list t1s) (mk_list t2s) = mk_functype (mk_list t_1_lst) 
          (mk_list t_2_lst)" using blockhyps(2) Step_read__block(1,10,11)
      using blocktype_ok_agree by auto
    then have subt: "mk_instrtype (mk_list []) (mk_list t2s) <ti: mk_instrtype t1 t3" 
        "Resulttype_sub (mk_list (map typeofval val_lst)) (mk_list t1s)"
      using blockhyps Step_read__block subv subt 
          produce_consume[of "map typeofval val_lst" t1 t2 "[]" t1s t2s t3] 
      by auto
    then have okvs: "Instrs_ok2 s (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list t2s], context_RETURN = None\<rparr>
      C') (map admininstr_val val_lst) (mk_functype (mk_list []) (mk_list (map typeofval val_lst)))"
      using splitvs Instrs_ok2_const_replace blockhyps(3) Instrs_ok_wf(1) by blast
    have "Instrs_ok
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list t2s], context_RETURN = None\<rparr>
      C')
    instr_lst (mk_functype (mk_list (map typeofval val_lst)) (mk_list t2s))"
      using blockhyps subt
      using Instrs_ok_wf(1,2) Resulttype_sub_refl sub by blast
    then have ok_inside: "Instrs_ok2 s
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list t2s], context_RETURN = None\<rparr>
      C')
    (map admininstr_val val_lst @ map admininstr_instr instr_lst) 
    (mk_functype (mk_list []) (mk_list t2s))"
      using okvs instrs_ok_instrs_ok2 instrs_ok2_seq 
      using Instrs_ok2_wf(2) by blast
    then have wffinal: "wf_admininstr (admininstr_sc8
       (LABEL_underscore v_n [] (map admininstr_val val_lst @ map admininstr_instr instr_lst)))"
      using admininstr_case_71 Instrs_ok2_wf_instr by fastforce
    have "Instr_ok2 s C'
     (admininstr_sc8
       (LABEL_underscore v_n [] (map admininstr_val val_lst @ map admininstr_instr instr_lst)))
        (mk_functype (mk_list []) (mk_list t2s))"
      using label[OF _ ok_inside Instrs_ok2_wf(2,1)[OF splitvs(1)] wffinal] 
        blockhyps Step_read__block eqt Instrs_ok2__empty[OF Instrs_ok2_wf(2,1)[OF splitvs(1)]]
      using Instrs_ok2_frame_sub Resulttype_sub_refl by fastforce
    then show ?case using instr_ok2_instrs_ok2 Instrs_ok2_subtyping subt Step_read__block(14)
      by auto
  next
    case (Step_read__loop bt t_1_lst t_2_lst k val_lst v_n instr_lst)
    then obtain t2 where splitvs: 
      "Instrs_ok2 s C' (map admininstr_val val_lst) (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_LOOP bt instr_lst)] (mk_functype t2 t3)"
      using inv_seq by blast
    then have subv: "mk_instrtype (mk_list []) (mk_list (map typeofval val_lst)) <ti:
               mk_instrtype t1 t2" using inv_const_list by blast
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_LOOP bt instr_lst)) (mk_functype t2' t3')"
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3"
      using splitvs(2) inv_one_admininstr by blast
    then have okloop: "Instr_ok C' (instr_sc7 (LOOP bt instr_lst)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.psimps admininstr_instr.domintros by fastforce
    then obtain t1s t2s where blockhyps:
      "wf_context
    \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
       context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t1s],
       context_RETURN = None\<rparr>"
   "Blocktype_ok C' bt (mk_functype (mk_list t1s) (mk_list t2s))"
   "Instrs_ok
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list t1s], context_RETURN = None\<rparr>
      C')
    instr_lst (mk_functype (mk_list t1s) (mk_list t2s))"
   "mk_functype (mk_list t1s) (mk_list t2s) = mk_functype t2' t3'"
      using inv_loop by blast
    have eqt: "mk_functype (mk_list t1s) (mk_list t2s) = mk_functype (mk_list t_1_lst) 
          (mk_list t_2_lst)" using blockhyps(2) Step_read__loop(1)
      using blocktype_ok_agree[OF blockhyps(2) Step_read__loop(10,11)] by auto
    then have subt: "mk_instrtype (mk_list []) (mk_list t2s) <ti: mk_instrtype t1 t3" 
        "Resulttype_sub (mk_list (map typeofval val_lst)) (mk_list t1s)"
      using blockhyps Step_read__loop subv subt 
          produce_consume[of "map typeofval val_lst" t1 t2 "[]" t1s t2s t3] 
      by auto
    then have okvs: "Instrs_ok2 s (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list t1s], context_RETURN = None\<rparr>
      C') (map admininstr_val val_lst) (mk_functype (mk_list []) (mk_list (map typeofval val_lst)))"
      using splitvs Instrs_ok2_const_replace blockhyps(3) Instrs_ok_wf(1) by blast
    have "Instrs_ok
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list t1s], context_RETURN = None\<rparr>
      C')
    instr_lst (mk_functype (mk_list (map typeofval val_lst)) (mk_list t2s))"
      using blockhyps subt
      using Instrs_ok_wf(1,2) Resulttype_sub_refl sub by blast
    then have ok_inside: "Instrs_ok2 s
    (append_res_context
      \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
         context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
         LABELS = [mk_list t1s], context_RETURN = None\<rparr>
      C')
    (map admininstr_val val_lst @ map admininstr_instr instr_lst) 
    (mk_functype (mk_list []) (mk_list t2s))"
      using okvs instrs_ok_instrs_ok2 instrs_ok2_seq 
      using Instrs_ok2_wf(2) by blast
    then have wffinal: "wf_admininstr (admininstr_sc8
       (LABEL_underscore k [instr_sc7 (LOOP bt instr_lst)] 
        (map admininstr_val val_lst @ map admininstr_instr instr_lst)))"
      using admininstr_case_71 Instrs_ok2_wf_instr okloop Instr_ok_wf(2) by fastforce
    have "Instrs_ok2 s C' (map admininstr_instr [instr_sc7 (LOOP bt instr_lst)])
     (mk_functype (mk_list t1s) (mk_list t2s))"
      using splitvs(2) admininstr_instr.domintros 
        admininstr_instr.psimps blockhyps subt Instrs_ok2_subtyping 
      by (metis Instrs_ok2_wf(2) instr_ok_instrs_ok instrs_ok_instrs_ok2 okloop) 
    then have "Instr_ok2 s C'
     (admininstr_sc8
       (LABEL_underscore k [instr_sc7 (LOOP bt instr_lst)] (map admininstr_val val_lst @ map admininstr_instr instr_lst)))
        (mk_functype (mk_list []) (mk_list t2s))"
      using label[OF _ ok_inside Instrs_ok2_wf(2,1)[OF splitvs(1)] wffinal] 
        blockhyps Step_read__block eqt 
      using Instrs_ok2_frame_sub Resulttype_sub_refl
      using Step_read__loop.hyps(3) by blast
    then show ?case using instr_ok2_instrs_ok2 Instrs_ok2_subtyping subt Step_read__loop(14)
      by auto
  next
    case (Step_read__call x)
    then obtain t1' t3' where 
      ok': "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_CALL x)) (mk_functype t1' t3')" 
      and subt: "mk_instrtype t1' t3' <ti: mk_instrtype t1 t3" 
      using inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc0 (CALL x)) (mk_functype t1' t3')"
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by fastforce
    then have callhyps:
      "proj_uN_0 x < length (context_FUNCS C')" 
      "context_FUNCS C' ! proj_uN_0 x = mk_functype t1' t3'"
      using inv_call by auto
    then have "Instr_ok2 s C' (admininstr_sc7 (CALL_ADDR 
          (fun_funcaddr (mk_state s f) ! proj_uN_0 x))) (mk_functype t1' t3')"
      using Instr_ok2__call_addr[OF _ Instrs_ok2_wf(2,1)[OF Step_read__call(10)]] 
        context_funcs_agree Step_read__call externtype_case_0 admininstr_case_70 
      using Instr_ok2.simps ok'
      by auto
    then show ?case using 
        subt instr_ok2_instrs_ok2 Instrs_ok2_subtyping Step_read__call by fast
  next
    case (call_indirect_call i x a y)
    then obtain t2 where splitv:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 i)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)] (mk_functype t2 t3)" 
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    then have subv:
      "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2" 
      using inv_const_list[of s C' "[_]" t1 t2 "[val_CONST I32 i]"] admininstr_val.domintros
        admininstr_val.psimps valtype_numtype.domintros valtype_numtype.psimps
      typeofval.domintros typeofval.psimps by fastforce
    obtain t2' t3' where
      ok': "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)) (mk_functype t2' t3')"
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3"
      using splitv(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc0 (CALL_INDIRECT x y)) (mk_functype t2' t3')"
      using inv_plain admininstr_instr.psimps admininstr_instr.domintros by fastforce
    then obtain lim t_1_lst t_2_lst where callhyps:
      "proj_uN_0 x < length (context_TABLES C')"
      "context_TABLES C' ! proj_uN_0 x = mk_tabletype lim FUNCREF"
      "proj_uN_0 y < length (context_TYPES C')"
      "context_TYPES C' ! proj_uN_0 y = mk_functype (mk_list t_1_lst) (mk_list t_2_lst)"
      "wf_tabletype (mk_tabletype lim FUNCREF)"
      "mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst) = mk_functype t2' t3'" 
      using inv_call_indirect by blast
    then have subt: "mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst) <ti: mk_instrtype t1 t3" 
      using subv subt produce_consume by fastforce
    have typeeq: "funcinst_TYPE (fun_funcinst (mk_state s f) ! a) = 
                  mk_functype (mk_list t_1_lst) (mk_list t_2_lst)"
      using callhyps(3,4) call_indirect_call context_types_agree by metis
    have "Externaddr_ok s (externaddr_FUNC a)
     (FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))"
      using Externaddr_ok__func[of a s "store_FUNCS s ! a"]
        Instrs_ok2_wf(2)[OF splitv(1)]
        externtype_case_0 call_indirect_call
        typeeq fun_funcinst.domintros fun_funcinst.psimps
      by auto
    then have "Instr_ok2 s C' (admininstr_sc7 (CALL_ADDR 
          a)) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
      using Instr_ok2__call_addr[OF _ Instrs_ok2_wf(2,1)[OF call_indirect_call(14)]] 
         externtype_case_0 admininstr_case_70 
      by auto
    then show ?case using 
        subt instr_ok2_instrs_ok2 Instrs_ok2_subtyping call_indirect_call by fast
  next
    case (call_indirect_trap i x y)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (call_addr a t_1_lst t_2_lst mm v_func x t_lst instr_lst f' val_lst k v_n)
    then obtain t2 where splitvs:
      "Instrs_ok2 s C' (map admininstr_val val_lst) (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc7 (CALL_ADDR a)] (mk_functype t2 t3)"
      using inv_seq by blast
    then have subv: "mk_instrtype (mk_list []) (mk_list (map typeofval val_lst)) <ti:
          mk_instrtype t1 t2" using inv_const_list by blast
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc7 (CALL_ADDR a)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitvs inv_one_admininstr by blast
    then have 
      "Externaddr_ok s (externaddr_FUNC a) (FUNC (mk_functype t2' t3'))" 
     (* "wf_externtype (FUNC (mk_functype t2' t3'))" *)
      using inv_call_addr by auto
    then have eqt: "mk_functype t2' t3' = mk_functype (mk_list t_1_lst) (mk_list t_2_lst)"
      using call_addr(2)
    proof(induction s "externaddr_FUNC a" "FUNC (mk_functype t2' t3')" rule:Externaddr_ok.induct)
      case (Externaddr_ok__func s v_funcinst)
      then show ?case using fun_funcinst.domintros fun_funcinst.psimps by force
    next
      case (Externaddr_ok__sub s xt')
      show ?case using Externaddr_ok__sub(3) Externaddr_ok__sub
      proof (induction xt' "FUNC (mk_functype t2' t3')" rule:Externtype_sub.induct)
       case (Externtype_sub__func ft_1)
       then show ?case 
       proof (induction ft_1 "mk_functype t2' t3'" rule:Functype_sub.induct)
         case mk_Functype_sub
         then show ?case by fast
       qed
     qed    
   qed
   have "Expr_ok (append_res_context C \<lparr> context_TYPES = [], context_FUNCS = [], 
            context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], 
            context_DATAS = [], context_LOCALS = (t_1_lst @ t_lst), 
            LABELS = [(mk_list t_2_lst)], context_RETURN = (Some (mk_list t_2_lst)) \<rparr>) 
            instr_lst (mk_list t_2_lst)"
     using call_addr(14) call_addr
   proof (induction s rule: Store_ok.induct)
     case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst 
              tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst 
              elemtype_lst)
     then have
      "Funcinst_ok s \<lparr>funcinst_TYPE = mk_functype (mk_list t_1_lst) (mk_list t_2_lst), 
                      funcinst_MODULE = mm, CODE = v_func\<rparr> (functype_lst ! a)"
       using list_all2_nth[OF mk_Store_ok(8)] fun_funcinst.domintros fun_funcinst.psimps
       by simp
     then show ?case using mk_Store_ok
     proof (induction s "\<lparr> funcinst_TYPE = mk_functype (mk_list t_1_lst) (mk_list t_2_lst), 
                      funcinst_MODULE = mm, CODE = v_func\<rparr>" "functype_lst ! a" 
            rule: Funcinst_ok.induct)
       case (mk_Funcinst_ok s v_moduleinst C v_func')
       show ?case using mk_Funcinst_ok(3) mk_Funcinst_ok  
       proof (induction C v_func' "functype_lst ! a" rule:Func_ok.induct)
         case (mk_Func_ok x' C' t_1_lst' t_2_lst' t_lst' v_expr)
         then show ?case sorry
       qed
     qed
   qed
    then show ?case sorry
  next
    case (Step_read__ref_func x)
    then show ?case sorry
  next
    case (Step_read__local_get x)
    then show ?case sorry
  next
    case (Step_read__global_get x)
    then show ?case sorry
  next
    case (table_get_trap i x)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (table_get_val i x)
    then show ?case sorry
  next
    case (Step_read__table_size x v_n)
    then show ?case sorry
  next
    case (table_fill_trap i v_n x v_val)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (table_fill_zero i v_n x v_val)
    then show ?case sorry
  next
    case (table_fill_succ i v_n x v_val)
    then show ?case sorry
  next
    case (table_copy_trap i j v_n y x)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (table_copy_zero i j v_n y x)
    then show ?case sorry
  next
    case (table_copy_le j i v_n y x)
    then show ?case sorry
  next
    case (table_copy_gt j i v_n y x)
    then show ?case sorry
  next
    case (table_init_trap i j v_n y x)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (table_init_zero i j v_n y x)
    then show ?case sorry
  next
    case (table_init_succ i y j v_n x)
    then show ?case sorry
  next
    case (load_num_trap i nt ao)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (load_num_val i nt c ao)
    then show ?case sorry
  next
    case (load_pack_trap i ao v_n v_Inn v_sx)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (load_pack_val v_Inn i v_n c ao v_sx)
    then show ?case sorry
  next
    case (vload_oob i ao)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (vload_val i c ao)
    then show ?case sorry
  next
    case (vload_shape_oob i ao v_M v_N v_sx)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (vload_shape_val i v_N v_M ao j_lst v_Jnn c v_sx)
    then show ?case sorry
  next
    case (vload_splat_oob i ao v_N)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (vload_splat_val i v_N j ao v_Jnn v_M c)
    then show ?case sorry
  next
    case (vload_zero_oob i ao v_N)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (vload_zero_val i v_N j ao c)
    then show ?case sorry
  next
    case (vload_lane_oob i ao v_N c_1 j)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (vload_lane_val i v_N k ao v_Jnn v_M c c_1 j)
    then show ?case sorry
  next
    case (Step_read__memory_size v_n)
    then show ?case sorry
  next
    case (memory_fill_trap i v_n v_val)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (memory_fill_zero i v_n v_val)
    then show ?case sorry
  next
    case (memory_fill_succ i v_n v_val)
    then show ?case sorry
  next
    case (memory_copy_trap i j v_n)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (memory_copy_zero i j v_n)
    then show ?case sorry
  next
    case (memory_copy_le j i v_n)
    then show ?case sorry
  next
    case (memory_copy_gt j i v_n)
    then show ?case sorry
  next
    case (memory_init_trap i j v_n x)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (memory_init_zero i j v_n x)
    then show ?case sorry
  next
    case (memory_init_succ i x j v_n)
    then show ?case sorry
  qed
next
  case (ctxt_label admininstr_lst admininstr'_lst v_n instr_0_lst)
  then show ?case sorry
next
  case (ctxt_frame s f' admininstr_lst s' f'' admininstr'_lst f v_n)
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
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
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
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
next
  case (store_num_val i nt b_lst c ao)
  then show ?case sorry
next
  case (store_pack_trap i ao v_n v_Inn c)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
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
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
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
qed 



theorem preservation:
  assumes "Config_ok cfg ts"
          "Step cfg cfg'"
  shows "Config_ok cfg' ts"
proof -

  obtain s s' f f' es es' C where cfg_is:"cfg = mk_config (mk_state s f) es"
                                         "cfg' = mk_config (mk_state s' f') es'"
                                         "State_ok (mk_state s f) C"
                                         "(Expr_ok2 s C es ts)"
                                         "(wf_context C)"
                                         "(wf_config (mk_config (mk_state s f) es))"
                                         "(wf_state (mk_state s f))"
    using assms(1) Config_ok.simps
    by (metis config.exhaust state.exhaust)

  have 7:"Store_ok s"
    using State_ok.cases cfg_is(3)
    by blast

  have "Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
    by (metis assms(2) cfg_is(1) cfg_is(2))

	have 1:"Frame_ok s f C"
	  using State_ok.cases cfg_is(3)
	  by blast

  obtain C' t_lst where C'_is:"Moduleinst_ok s (frame_MODULE f) C'"
                  "C =
        append_res_context C'
         \<lparr>context_TYPES = [],
            context_FUNCS = [],
            context_GLOBALS = [],
            context_TABLES = [],
            context_MEMS = [],
            context_ELEMS = [],
            context_DATAS = [],
            context_LOCALS = t_lst,
            LABELS = [],
            context_RETURN =
              None\<rparr>"
        "length t_lst = length (LOCALS f)"
        "list_all2 (\<lambda>t v_val. Val_ok s v_val t) t_lst (LOCALS f)"
    using Frame_ok.cases[OF 1]
    by (metis frame.select_convs(1,2))

  have 0:"Store_ok s'"
         "Extend_store s s'"
         "Moduleinst_ok s' (frame_MODULE f) C'"
    sorry
    (* should come from A's proof *)

  have 2:"context_LOCALS C = t_lst"
    using C'_is(1,2)
    unfolding Moduleinst_ok.simps append_res_context_def
    apply simp
    apply (metis res_context.select_convs(8))
    done

    have 4:"list_all2 (\<lambda>(t :: valtype) (v :: val). (Val_ok s v t)) (context_LOCALS C) (LOCALS f)"
      by (simp add: "2" C'_is(4))

    have 3:"Instrs_ok2 s C es (mk_functype (mk_list []) ts)"
      by (metis Expr_ok2.cases cfg_is(4))

    have 5:"Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
      using assms(2) cfg_is(1,2)
      by auto

    have 6:"t_inst_match C' C"
      using C'_is(2)
      unfolding append_res_context_def t_inst_match_def
      by simp

    have a:"Instrs_ok2 s' C es' (mk_functype (mk_list []) ts)"
         "list_all2 (\<lambda>t v. Val_ok s' v t) (context_LOCALS C) (LOCALS f')"
         "length (LOCALS f) = length (LOCALS f')"
         "frame_MODULE f = frame_MODULE f'"
      using e_preservation[OF 5 7 0(1) 0(2) C'_is(1) 0(3) 6 4 3]
            e_preservation_locals[OF 5 7 0(1) 0(2) C'_is(1) 0(3) 6 4 3]
      by simp_all

		have bc:"(wf_state (mk_state s' f'))"
  by (metis "5" cfg_is(6) config.inject step_wf wf_config.cases)
		  

    have c:"wf_store s'"
      by (metis bc state.inject wf_state.cases)

    have cc:"wf_context C'"
      by (fastforce intro: C'_is Moduleinst_ok.cases)

    have ccc:"length (context_LOCALS C) = length (LOCALS f')"
      by (simp add: "2" C'_is(3) a(3))

    have ccccc:"wf_frame \<lparr>LOCALS = LOCALS f', frame_MODULE = frame_MODULE f\<rparr>"
      by (metis (full_types) a(4) bc frame.surjective old.unit.exhaust state.inject
          wf_state.cases)

    have cccc:"wf_context
   \<lparr>context_TYPES = [],
      context_FUNCS = [],
      context_GLOBALS = [],
      context_TABLES = [],
      context_MEMS = [],
      context_ELEMS = [],
      context_DATAS = [],
      context_LOCALS =
        context_LOCALS C,
      LABELS = [],
      context_RETURN = None\<rparr>"
      unfolding wf_context.simps
      by auto

    have bb:"(Frame_ok s' f' C)"
      using Frame_ok.intros[OF 0(3) ccc a(2) c cc ccccc cccc]
      by (metis "2" C'_is(2) a(4) frame.surjective old.unit.exhaust)

    have b:"(State_ok (mk_state s' f') C)"
      by (simp add: "0"(1) bb bc cfg_is(5)
          mk_State_ok)


    have d:"(Expr_ok2 s' C es' ts)"
      using a(1) cfg_is(5) b
      unfolding Expr_ok2.simps
      apply simp
      using Config_ok.simps assms(1) c Instrs_ok2_wf_instr by auto

    show ?thesis
      using "5" Config_ok.simps assms(1) b bc cfg_is(1,2,5) d step_wf by auto
qed

theorem progress:
  assumes "Config_ok (mk_config s es) ts"
  shows "\<exists>cfg'. Step (mk_config s es) cfg' \<or> es = [admininstr_subcase_7 admininstr_subtype_7_TRAP] \<or> (\<exists>vs. es = map admininstr_val vs)"
  sorry


end