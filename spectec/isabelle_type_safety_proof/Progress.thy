theory Progress
(* Imported Code *)
	imports isabelle_reference_output_wasm2 store_extension_typing Properties 
	        Type_Inversion Subtyping_Theorem Context_Store_Agreement Preservation
begin

definition strip :: "res_context \<Rightarrow> res_context" where 
  "strip C = \<lparr> 
context_TYPES = context_TYPES C,
	context_FUNCS = context_FUNCS C,
	context_GLOBALS = context_GLOBALS C,
	context_TABLES = context_TABLES C,
	context_MEMS = context_MEMS C ,
	context_ELEMS = context_ELEMS C,
	context_DATAS = context_DATAS C,
	context_LOCALS = context_LOCALS C,
	LABELS = [],
	context_RETURN = None \<rparr>"

lemma t_inst_match_strip: shows "t_inst_match C (strip C)" 
proof(cases C)
  case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES 
      context_MEMS context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
  then show ?thesis using strip_def t_inst_match_def by auto
qed 

lemma State_ok_strip: assumes "State_ok s C" shows "C = strip C" 
  using assms proof(induction s C)
  case (mk_State_ok s f C)
  show ?case using mk_State_ok(2) proof(induction s f C)
    case (mk_Frame_ok s v_moduleinst C t_lst val_lst)
    show ?case using mk_Frame_ok(1) proof(induction s v_moduleinst C)
      case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
            functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst 
            exportinst_lst dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
      show ?case using append_res_context_def strip_def by simp
    qed
  qed
qed

lemma reducible_left_v:
  assumes "Ex (Step (mk_config s es))" "wf_config (mk_config s es)" (* "wf_config c'"  *)  
  shows "Ex (Step (mk_config s (map admininstr_val vs @ 
              es)))"
proof (cases vs)
  case Nil
  then show ?thesis using assms by auto
next
  case (Cons a list)
  then obtain c' where step: "Step (mk_config s es) c'" using assms
    by auto
  then show ?thesis proof(cases c')
    case (mk_config x1 x2)
    then have "wf_config c'" using assms step_wf step (* annonying to need to use step_wf but cannot work around it *)
      by fast
    then show ?thesis 
    using assms ctxt_instrs[of s es x1 x2 vs "[]"] mk_config step Cons
    by fastforce 
qed qed

lemma reducible_right: 
  assumes "Ex (Step (mk_config s es1))" "wf_config (mk_config s es1)" "list_all wf_admininstr es2"  
  shows "Ex (Step (mk_config s (es1 @ es2)))" 
proof(cases es2)
  case Nil
  then show ?thesis using assms by simp
next
  case (Cons a list)
  obtain c' where step: "Step (mk_config s es1) c'" using assms by blast
  then show ?thesis proof(cases c')
    case (mk_config x1 x2)
    then have "wf_config (mk_config x1 x2)" using step_wf step assms (* I hate using step_wf here 
        but there is no way around it! ! ! *)
      by blast
    then show ?thesis using step_wf assms step mk_config Cons ctxt_instrs[of s es1 x1 x2 "[]" es2]
      by auto
  qed
qed

lemma list_all_map_impl:
  assumes "list_all P l" "\<forall> x. P x \<longrightarrow> Q (f x)" shows "list_all Q (map f l)"
  using assms proof(induction l) qed(auto)


lemma list_all_map_impl_inv:
  assumes "list_all P (map f l)" "\<forall> x. P (f x) \<longrightarrow> Q x" shows "list_all Q l"
  using assms proof(induction l) qed(auto)

lemma list_all_app:
(* SURELY THIS HAST TO EXIST ALREADY *)
  assumes "list_all P l1" "list_all P l2" shows "list_all P (l1 @ l2)"
  using assms proof(induction l1) qed(auto)



lemma typeofval_is_i32: assumes "Valtype_sub (typeofval v) valtype_I32" 
  shows "\<exists> c. v = val_CONST I32 c"
  using assms proof(induction "typeofval v" valtype_I32)
  case refl
  then show ?case proof(cases v)
  case (val_CONST x11 x12)
  then show ?thesis using assms typeofval.psimps typeofval.domintros valtype_numtype.domintros 
      valtype_numtype.psimps refl
    by (metis lanetype_numtype.cases valtype.distinct(1,3,5))
next
  case (val_VCONST x21 x22)
  then show ?thesis proof(cases x21)
    case V128
    then show ?thesis using val_VCONST assms typeofval.psimps typeofval.domintros 
      valtype_vectype.domintros valtype_vectype.psimps refl
      by simp
  qed
next
  case (val_REF_NULL x3)
  then show ?thesis using assms typeofval.psimps typeofval.domintros valtype_reftype.domintros
    valtype_reftype.psimps refl proof(induction x3) qed(simp_all)
next
  case (val_REF_FUNC_ADDR x4)
  then show ?thesis using assms refl typeofval.psimps typeofval.domintros by simp
next
  case (val_REF_HOST_ADDR x5)
  then show ?thesis using assms refl typeofval.psimps typeofval.domintros by simp
qed
next
  case bot
  then show ?case proof(induction v)
    case (val_CONST x1 x2)
    then show ?case using typeofval.domintros typeofval.psimps
      by (metis lanetype_numtype.cases valtype.distinct(25,35,43) valtype_numtype.simps(2,3,4))
  next
    case (val_VCONST x1 x2)
    then show ?case using typeofval.domintros typeofval.psimps
      by (metis valtype.distinct(49) valtype_vectype.domintros valtype_vectype.psimps vectype.exhaust)
  next
    case (val_REF_NULL x)
    then show ?case using typeofval.domintros typeofval.psimps
      by (metis valtype.distinct(53,55) valtype_reftype.cases valtype_reftype.domintros(1,2)
          valtype_reftype.psimps(1,2))
  next
    case (val_REF_FUNC_ADDR x)
    then show ?case using typeofval.domintros typeofval.psimps by simp
  next
    case (val_REF_HOST_ADDR x)
    then show ?case using typeofval.domintros typeofval.psimps by simp
  qed
qed


theorem progress:
  assumes "Config_ok (mk_config s es) ts"
  shows "\<exists>cfg'. Step (mk_config s es) cfg' \<or> es = [admininstr_sc7 admininstr_st7_TRAP] \<or> (\<exists>vs. es = map admininstr_val vs)"
  using assms proof(induction "mk_config s es" ts)
  case (mk_Config_ok s' f C t_lst)
  then have stok: "State_ok (mk_state s' f) (strip C)" using State_ok_strip by simp
  show ?case using mk_Config_ok(2) stok mk_Config_ok(3-)
  proof (induction s' C es "mk_list t_lst" 
          arbitrary: s t_lst C f
        rule:Instr_ok2_Instrs_ok2_Expr_ok2.inducts(3)[where
      ?P1.0 = "\<lambda> s' C e t. (case t of mk_functype (mk_list t1) t2 \<Rightarrow> 
        (\<forall> vs. ((list_all2 Valtype_sub (map typeofval vs) t1) \<longrightarrow> 
            (list_all wf_val vs) \<longrightarrow> 
          (State_ok (mk_state s' f) (strip C)) \<longrightarrow> (wf_context C) \<longrightarrow>
         wf_config (mk_config (mk_state s' f) [e]) \<longrightarrow>
           wf_state (mk_state s' f) \<longrightarrow> (\<exists> cfg'.
       Step (mk_config (mk_state s' f) (map admininstr_val vs @ [e])) cfg' \<or>
       e = admininstr_sc7 admininstr_st7_TRAP \<or> (\<exists>v. e = admininstr_val v)))))" and 
      ?P2.0 = "\<lambda> s' C es t. (case t of mk_functype (mk_list t1) t2 \<Rightarrow> 
        (\<forall> vs. (list_all2 Valtype_sub (map typeofval vs) t1 \<longrightarrow> (list_all wf_val vs) \<longrightarrow> 
        (State_ok (mk_state s' f) (strip C)) \<longrightarrow> (wf_context C) \<longrightarrow>
         wf_config (mk_config (mk_state s' f) es) \<longrightarrow>
           wf_state (mk_state s' f) \<longrightarrow> (\<exists> cfg'.
       Step (mk_config (mk_state s' f) (map admininstr_val vs @ es)) cfg' \<or>
       es = [admininstr_sc7 admininstr_st7_TRAP] \<or> (\<exists>vs. es = map admininstr_val vs)))))"])
    case (plain C v_instr t_1_lst t_2_lst s')
    then show ?case
      apply(auto)
      subgoal for vs
      proof - 
        assume 
          "Instr_ok C v_instr (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
          "wf_store s'"
          "wf_context C"
          "wf_instr v_instr"
          "list_all2 Valtype_sub (map typeofval vs) t_1_lst"
          "list_all wf_val vs"
          "State_ok (mk_state s' f) (strip C)"
          "wf_config (mk_config (mk_state s' f) [admininstr_instr v_instr])"
          "wf_state (mk_state s' f)"
          "\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ [admininstr_instr v_instr])) x"
          "\<forall>v. admininstr_instr v_instr \<noteq> admininstr_val v" 
        then have "False" (* show "admininstr_instr v_instr = admininstr_sc7 admininstr_st7_TRAP"  *)
        proof(induction C v_instr "mk_functype (mk_list t_1_lst) (mk_list t_2_lst)" 
        arbitrary: t_1_lst t_2_lst vs
        rule: Instr_ok_Instrs_ok.inducts(1)[where
        ?P2.0 = "\<lambda> C es t. (case t of mk_functype (mk_list t1) t2 \<Rightarrow>
        \<forall> vs.
            wf_store s' \<longrightarrow>
        wf_context C \<longrightarrow>
    list_all wf_instr es \<longrightarrow>
    list_all2 Valtype_sub (map typeofval vs) t1 \<longrightarrow>
    list_all wf_val vs \<longrightarrow>
    State_ok (mk_state s' f) (strip C) \<longrightarrow>
    wf_config (mk_config (mk_state s' f) (map admininstr_instr es)) \<longrightarrow>
    wf_state (mk_state s' f) \<longrightarrow>
    (\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr es)) x) \<longrightarrow>
    (\<forall>vs. map admininstr_instr es \<noteq> map admininstr_val vs) \<longrightarrow> False)
  "])
      case (nop C)
      then show ?case 
        using Step.intros(1) Step_pure.intros(2)
        by fastforce
    next 
      case (unreachable C')
      then show ?case using reducible_left_v[of "mk_state s' f" "[admininstr_instr (instr_sc0 UNREACHABLE)]" vs]  
          Step.intros(1)[OF Step_pure.intros(1)]
        admininstr_case_73 config_case_0
        admininstr_case_1 by auto
    next
      case (drop C t)
      then show ?case 
      proof (induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case using Step.intros(1) Step_pure.intros(3)
            by fastforce
        next
          case (Cons a vs)
          show ?case using Cons by auto 
        qed
      qed
    next
      case (select_expl C' t)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs')
        show ?case using Cons(2-) proof(induction vs')
          case Nil
          then show ?case by simp
        next
          case (Cons b vs'')
          show ?case using Cons(2-) proof(induction vs'')
            case Nil
            then show ?case by simp
          next
            case (Cons c vs''')
             show ?case using Cons(2-) proof(induction vs''')
               case Nil
               then obtain c' where c: "c = val_CONST I32 c'" using typeofval_is_i32
                 by fastforce 
               have "wf_val c" using Nil by simp
               then have projc: "proj_num__0 c' \<noteq> None" using c proof(induction c)
                 case (val_case_0 v_numtype var_0)
                 then show ?case proof(induction v_numtype var_0)
                   case (num__case_0 v_Inn var_x v_numtype)
                   then show ?case using proj_num__0.psimps proj_num__0.domintros
                     by fast
                 next
                   case (num__case_1 v_Fnn var_x v_numtype)
                   then show ?case 
                   proof(cases v_Fnn) qed(auto simp add:num__case_1 numtype_Fnn.domintros 
                                  numtype_Fnn.psimps)
                 qed
               qed(auto)
               then show ?case proof(cases "proj_uN_0 (the (proj_num__0 c'))")
                 case 0
                 then show ?thesis using Nil c projc Step.intros(1) 
                     Step_pure.intros(5)[of c' a b "Some [t]"] admininstr_val.domintros
                     admininstr_val.psimps valtype_numtype.domintros valtype_numtype.psimps 
                   by fastforce 
               next
                 case (Suc nat)
                 then show ?thesis using projc Nil c Step.intros(1) 
                     Step_pure.intros(4)[of c' a b "Some [t]"] admininstr_val.domintros
                     admininstr_val.psimps valtype_numtype.domintros valtype_numtype.psimps 
                   by fastforce 
               qed 
             next
               case (Cons a vs)
               then show ?case by simp
             qed
          qed
        qed
      qed
    next
      case (select_impl t t' v_numtype v_vectype C)
      then show ?case sorry
    next
      case (block C' bt t_1_lst t_2_lst instr_lst)
      have bt: "fun_blocktype (mk_state s' f) bt = mk_functype
                    (mk_list t_1_lst) (mk_list t_2_lst)"
        using block(12) blocktype_ok_agree[OF block(1)]
      proof(induction "mk_state s' f" "strip C'")
        case (mk_State_ok)
        show ?case using mk_State_ok(2,1,3-) proof(induction s' f "strip C'")
          case (mk_Frame_ok s v_moduleinst C''' t_lst val_lst)
          have "t_inst_match C'''
     (append_res_context C'''
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = t_lst, LABELS = [],
          context_RETURN = None\<rparr>)" proof(cases C''')
            case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES 
                context_MEMS context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
            then show ?thesis using t_inst_match_def append_res_context_def
              by auto
          qed
          then have "t_inst_match C''' C'"
            using mk_Frame_ok(8) t_inst_match_strip
            using t_inst_match_def by auto
          then show ?case using mk_Frame_ok(1) mk_Frame_ok(12)[of s 
                "\<lparr>LOCALS = val_lst, frame_MODULE = v_moduleinst\<rparr>" C''']
            by force
        qed
      qed
      show ?case using block(10) list_all2_lengthD 
          Step_read__block[OF bt, of "length vs" vs "length t_2_lst" instr_lst] 
         Step.intros(2) block(15)
        by fastforce
    next
      case (loop C bt instr_lst)
      then show ?case sorry
    next
      case (res_if C bt t_1_lst instr_1_lst instr_2_lst)
      then show ?case sorry
    next
      case (br l C t_lst t_1_lst)
      then show ?case sorry
    next
      case (br_if l C)
      then show ?case sorry
    next
      case (br_table C l_lst t_lst l' t_1_lst)
      then show ?case sorry
    next
      case (call x C)
      then show ?case sorry
    next
      case (call_indirect x C lim y t_1_lst)
      then show ?case sorry
    next
      case (return C t_lst t_1_lst)
      then show ?case sorry
    next
      case (const C nt c_nt)
      then show ?case sorry
    next
      case (unop C nt unop_nt)
      then show ?case sorry
    next
      case (binop C nt binop_nt)
      then show ?case sorry
    next
      case (testop C nt testop_nt)
      then show ?case sorry
    next
      case (relop C nt relop_nt)
      then show ?case sorry
    next
      case (cvtop C nt_1 nt_2 cvtop)
      then show ?case sorry
    next
      case (ref_null C rt)
      then show ?case sorry
    next
      case (ref_func x C ft)
      then show ?case sorry
    next
      case (ref_is_null C rt)
      then show ?case sorry
    next
      case (vconst C c)
      then show ?case sorry
    next
      case (Instr_ok__vvunop C v_vvunop)
      then show ?case sorry
    next
      case (Instr_ok__vvbinop C v_vvbinop)
      then show ?case sorry
    next
      case (Instr_ok__vvternop C v_vvternop)
      then show ?case sorry
    next
      case (Instr_ok__vvtestop C v_vvtestop)
      then show ?case sorry
    next
      case (vunop C sh vunop_sh)
      then show ?case sorry
    next
      case (vbinop C sh vbinop_sh)
      then show ?case sorry
    next
      case (vtestop C sh vtestop_sh)
      then show ?case sorry
    next
      case (vrelop C sh vrelop_sh)
      then show ?case sorry
    next
      case (vshiftop C sh vshiftop_sh)
      then show ?case sorry
    next
      case (vbitmask C sh)
      then show ?case sorry
    next
      case (vswizzle C sh)
      then show ?case sorry
    next
      case (vshuffle sh i_lst C)
      then show ?case sorry
    next
      case (vsplat C sh)
      then show ?case sorry
    next
      case (vextract_lane i sh C sx_opt)
      then show ?case sorry
    next
      case (vreplace_lane i sh C)
      then show ?case sorry
    next
      case (vextunop C sh_1 sh_2 vextunop)
      then show ?case sorry
    next
      case (vextbinop C sh_1 sh_2 vextbinop)
      then show ?case sorry
    next
      case (vnarrow C sh_1 sh_2 v_sx)
      then show ?case sorry
    next
      case (Instr_ok__vcvtop C sh_1 sh_2 v_vcvtop)
      then show ?case sorry
    next
      case (local_get x C t)
      then show ?case sorry
    next
      case (local_set x C t)
      then show ?case sorry
    next
      case (local_tee x C t)
      then show ?case sorry
    next
      case (global_get x C v_mut t)
      then show ?case sorry
    next
      case (global_set x C t)
      then show ?case sorry
    next
      case (table_get x C lim rt)
      then show ?case sorry
    next
      case (table_set x C lim rt)
      then show ?case sorry
    next
      case (table_size x C lim rt)
      then show ?case sorry
    next
      case (table_grow x C lim rt)
      then show ?case sorry
    next
      case (table_fill x C lim rt)
      then show ?case sorry
    next
      case (table_copy x_1 C lim_1 rt x_2 lim_2)
      then show ?case sorry
    next
      case (table_init x_1 C lim rt x_2)
      then show ?case sorry
    next
      case (elem_drop x C rt)
      then show ?case sorry
    next
      case (memory_size C mt)
      then show ?case sorry
    next
      case (memory_grow C mt)
      then show ?case sorry
    next
      case (memory_fill C mt)
      then show ?case sorry
    next
      case (memory_copy C mt)
      then show ?case sorry
    next
      case (memory_init C mt x)
      then show ?case sorry
    next
      case (data_drop x C)
      then show ?case sorry
    next
      case (load_val C mt nt v_memarg)
      then show ?case sorry
    next
      case (load_pack C mt v_memarg v_M v_Inn v_sx)
      then show ?case sorry
    next
      case (store_val C mt nt v_memarg)
      then show ?case sorry
    next
      case (store_pack C mt v_memarg v_M v_Inn)
      then show ?case sorry
    next
      case (vload_val C mt v_memarg)
      then show ?case sorry
    next
      case (vload_pack C mt v_memarg v_M v_N v_sx)
      then show ?case sorry
    next
      case (vload_splat C mt v_memarg v_n)
      then show ?case sorry
    next
      case (vload_zero C mt v_memarg v_n)
      then show ?case sorry
    next
      case (vload_lane C mt v_memarg v_n v_laneidx)
      then show ?case sorry
    next
      case (vstore C mt v_memarg)
      then show ?case sorry
    next
      case (vstore_lane C mt v_memarg v_n v_laneidx)
      then show ?case sorry
    next
      case (empty C)
      then show ?case
        by auto
    next
      case (Instrs_ok__instr C' v_instr' t_1_lst' t_2_lst')
      then show ?case
        apply(auto)
        subgoal for vs
      proof -
        assume "(\<And>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<Longrightarrow>
           list_all wf_val vs \<Longrightarrow>
           \<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ [admininstr_instr v_instr']))
                   x \<Longrightarrow>
           \<forall>v. admininstr_instr v_instr' \<noteq> admininstr_val v \<Longrightarrow> False)"
        " list_all2 Valtype_sub (map typeofval vs) t_1_lst'"
        "list_all wf_val vs"
        "\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ [admininstr_instr v_instr'])) x"
        then have "\<exists> v. admininstr_instr v_instr' = admininstr_val v"
          by blast
        then show "\<exists>vs. [admininstr_instr v_instr'] = map admininstr_val vs"
          by (metis \<open>\<exists>v. admininstr_instr v_instr' = admininstr_val v\<close> map_eq_Cons_conv list.simps(8))
      qed done
    next
      case (seq C' instr_1_lst t_1_lst' t_2_lst' instr_2_lst t_3_lst)
      then show ?case  
        apply(simp)
        subgoal 
        proof -
          assume assms:
          "Instrs_ok C' instr_1_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
          "wf_store s' \<longrightarrow> (\<forall> vs.
          list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
          list_all wf_val vs \<longrightarrow>
          State_ok (mk_state s' f) (strip C') \<longrightarrow>
          wf_config (mk_config (mk_state s' f) (map admininstr_instr instr_1_lst)) \<longrightarrow>
          wf_state (mk_state s' f) \<longrightarrow>
          (\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_1_lst))
             x) \<longrightarrow>
          (\<exists>vs. map admininstr_instr instr_1_lst = map admininstr_val vs))"
          "Instrs_ok C' instr_2_lst (mk_functype (mk_list t_2_lst') (mk_list t_3_lst))"
          "wf_store s' \<longrightarrow> (\<forall> vs.
          list_all2 Valtype_sub (map typeofval vs) t_2_lst' \<longrightarrow>
          list_all wf_val vs \<longrightarrow>
          State_ok (mk_state s' f) (strip C') \<longrightarrow>
          wf_config (mk_config (mk_state s' f) (map admininstr_instr instr_2_lst)) \<longrightarrow>
          wf_state (mk_state s' f) \<longrightarrow>
          (\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_2_lst))
             x) \<longrightarrow>
          (\<exists>vs. map admininstr_instr instr_2_lst = map admininstr_val vs))"
          "wf_context C'"
          "list_all wf_instr instr_1_lst"
          "list_all wf_instr instr_2_lst"
          show "wf_store s' \<longrightarrow> (\<forall> vs.
          list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
          list_all wf_val vs \<longrightarrow>
          State_ok (mk_state s' f) (strip C') \<longrightarrow>
          wf_config
       (mk_config (mk_state s' f) (map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst)) \<longrightarrow>
      wf_state (mk_state s' f) \<longrightarrow>
          (\<forall>x. \<not> Step
             (mk_config (mk_state s' f)
               (map admininstr_val vs @
                map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst))
             x) \<longrightarrow>
          (\<exists>vs. map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst = 
          map admininstr_val vs))"
            apply(auto)
            subgoal for vs
            proof - 
              assume assms': 
                "wf_store s'"
    "list_all2 Valtype_sub (map typeofval vs) t_1_lst'"
    "list_all wf_val vs"
    "State_ok (mk_state s' f) (strip C')"
    "wf_config
     (mk_config (mk_state s' f) (map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst))"
      "wf_state (mk_state s' f)"
     "\<forall>x. \<not> Step
            (mk_config (mk_state s' f)
              (map admininstr_val vs @
               map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst))
            x"
              show "\<exists>vs. map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst = map admininstr_val vs "
              proof (cases "(Ex (Step (mk_config (mk_state s' f) 
      (map admininstr_val vs @ map admininstr_instr instr_1_lst))))")
                case True
                then have "wf_config (
                  mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_1_lst))"
                  using assms(6) assms'(3) wf_admininstr_val wf_admininstr_instr
                  config_case_0[OF assms'(6)] 
                  list_all_map_impl[of wf_val vs wf_admininstr admininstr_val]
                  list_all_map_impl[of wf_instr instr_1_lst wf_admininstr admininstr_instr]
                  list_all_app
                  by force
                then have "(Ex (Step (mk_config (mk_state s' f) 
      (map admininstr_val vs @ map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst))))"
                  using True reducible_right assms(7) 
                  list_all_map_impl[of wf_instr instr_2_lst wf_admininstr admininstr_instr]
                  wf_admininstr_instr
                  by fastforce
                then show ?thesis using assms'(7)
                  by blast
              next
                case False
                then obtain vs1 where const: "map admininstr_instr instr_1_lst = map admininstr_val vs1"
                   using assms assms'
                   by (metis config.inject config_case_0 list_all_append wf_config.cases)
                 then have "mk_instrtype (mk_list []) (mk_list (map typeofval vs1)) <ti: 
                      mk_instrtype (mk_list t_1_lst') (mk_list t_2_lst')"  
                   using inv_const_list assms(1) instrs_ok_instrs_ok2 assms'(1) by fastforce
                 then show ?thesis
                   using const assms assms'
                 proof(induction "mk_instrtype (mk_list []) (mk_list (map typeofval vs1))" 
                    "mk_instrtype (mk_list t_1_lst') (mk_list t_2_lst')")
                   case (mk_Instrtype_sub t_lst emp t'_lst t_12'_lst)
                   then show ?case 
                   proof(cases "Ex (Step
                   (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_1_lst @
                  map admininstr_instr instr_2_lst)))")
                     case True
                     then show ?thesis using mk_Instrtype_sub
                       by fast
                   next
                     case False
                     have 1: "list_all2 Valtype_sub (map typeofval (vs @ vs1)) t_2_lst'"
                       using mk_Instrtype_sub(3,1,2,4-6,15)
                     proof(induction "mk_list t_lst" "mk_list t'_lst")
                       case mk_Resulttype_sub
                       show ?case using mk_Resulttype_sub(6,1-5,7-)
                        proof(induction "mk_list (map typeofval vs1)" "mk_list t_12'_lst")
                          case mk_Resulttype_sub
                          have "emp = []" using mk_Resulttype_sub(7)
                            by (simp add: Resulttype_sub.simps)
                          then have "list_all2 Valtype_sub (map typeofval vs) t'_lst"
                            using mk_Resulttype_sub Valtype_sub_trans 
                              list_all2_trans[of Valtype_sub Valtype_sub Valtype_sub "map typeofval vs"
                                  t_1_lst' t'_lst]
                            by fastforce
                          then show ?case using mk_Resulttype_sub(2,6)
                            by (simp add: list_all2_appendI)
                        qed
                     qed
                     have 2: "list_all wf_val (vs @ vs1)" 
                       using mk_Instrtype_sub(6,12,16) wf_admininstr_instr wf_admininstr_val_inv 
                       list_all_map_impl[of wf_instr instr_1_lst wf_admininstr admininstr_instr]
                       list_all_map_impl_inv[of wf_admininstr admininstr_val vs1 wf_val ]
                       by simp
                     have 3: "(\<forall>x. \<not> Step
                   (mk_config (mk_state s' f) (map admininstr_val (vs @ vs1) @ map admininstr_instr instr_2_lst))
                   x)" using False const
                       by fastforce
                     obtain vs2 where "map admininstr_instr instr_2_lst = map admininstr_val vs2"
                       using mk_Instrtype_sub 1 2 3
                       by (metis config.inject config_case_0 list_all_append wf_config.cases)
                     then show ?thesis using const
                       by (metis \<open>map admininstr_instr instr_2_lst = map admininstr_val vs2\<close> 
                           local.const map_append)
                   qed
                 qed 
              qed
        qed done qed done
    next
      case (sub C' instr_lst t_1_lst' t_2_lst' t'_1_lst t'_2_lst)
      then show ?case
        apply(auto)
        subgoal for vs
        proof -
          assume  assms:
            "Instrs_ok C' instr_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
    "Resulttype_sub (mk_list t'_1_lst) (mk_list t_1_lst')"
    "Resulttype_sub (mk_list t_2_lst') (mk_list t'_2_lst)"
    "wf_context C'"
    "list_all wf_instr instr_lst"
    "wf_store s'"
    "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         (\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_lst))
                  x) \<longrightarrow>
         (\<exists>vs. map admininstr_instr instr_lst = map admininstr_val vs)"
    "list_all2 Valtype_sub (map typeofval vs) t'_1_lst"
    "list_all wf_val vs"
    "State_ok (mk_state s' f) (strip C')"
    "wf_config (mk_config (mk_state s' f) (map admininstr_instr instr_lst))"
    "wf_state (mk_state s' f)"
    "\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_lst)) x"
          have "list_all2 Valtype_sub (map typeofval vs) t_1_lst'" 
            using assms(2,8) proof(induction "mk_list t'_1_lst" "mk_list t_1_lst'")
            case mk_Resulttype_sub
            then show ?case using Valtype_sub_trans list_all2_trans 
              by blast 
          qed
          then show "\<exists>vs. map admininstr_instr instr_lst = map admininstr_val vs" 
            using assms
            by blast
        qed done
    next
      case (Instrs_ok__frame C' instr_lst t_1_lst' t_2_lst' t_lst)
      then show ?case 
        apply(auto)
        subgoal for vs
        proof -
          assume assms:
  "Instrs_ok C' instr_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
    "wf_context C'"
    "list_all wf_instr instr_lst"
    "wf_store s'"
    "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         (\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_lst))
                  x) \<longrightarrow>
         (\<exists>vs. map admininstr_instr instr_lst = map admininstr_val vs)"
    "list_all2 Valtype_sub (map typeofval vs) (t_lst @ t_1_lst')"
    "list_all wf_val vs"
    "State_ok (mk_state s' f) (strip C')"
    "wf_config (mk_config (mk_state s' f) (map admininstr_instr instr_lst))"
    "wf_state (mk_state s' f)"
    "\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_lst)) x"
          then obtain ts1 ts2 where split1:
            "map typeofval vs = ts1 @ ts2" "list_all2 Valtype_sub ts1 t_lst" 
            "list_all2 Valtype_sub ts2 t_1_lst'" 
            using list_all2_append2
            by metis
          then obtain vs1 vs2 where split2:
            "vs = vs1 @ vs2" "ts1 = map typeofval vs1" "ts2 = map typeofval vs2" 
            using map_is_app by blast
          show "\<exists>vs. map admininstr_instr instr_lst = map admininstr_val vs" 
          proof (cases "Ex (Step (mk_config (mk_state s' f) 
              (map admininstr_val vs2 @ map admininstr_instr instr_lst)))")
            case True
            have "wf_config (mk_config (mk_state s' f) 
                (map admininstr_val vs2 @ map admininstr_instr instr_lst))"
              using assms split2
              by (metis config.inject config_case_0 list_all_append list_all_map_impl wf_admininstr_val
                  wf_config.cases)
            then show ?thesis using assms split2 reducible_left_v[OF True, of vs1]
              by auto
          next
            case False
            then show ?thesis using assms
              using split1(3) split2(1,3) by auto
          qed
        qed done
    qed
    then show ?thesis by simp
  qed done
  next
    case (label s C instr'_lst t'_lst t_lst admininstr_lst v_n)
    then show ?case 
      apply(simp)
      subgoal
      proof -
        assume assms:
        "Instrs_ok2 s C (map admininstr_instr instr'_lst) (mk_functype (mk_list t'_lst) (mk_list t_lst))"
        "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t'_lst \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         State_ok (mk_state s f) (strip C) \<longrightarrow>
         wf_config (mk_config (mk_state s f) (map admininstr_instr instr'_lst)) \<longrightarrow>
         wf_state (mk_state s f) \<longrightarrow>
         Ex (Step (mk_config (mk_state s f) (map admininstr_val vs @ map admininstr_instr instr'_lst))) \<or>
         map admininstr_instr instr'_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
         (\<exists>vs. map admininstr_instr instr'_lst = map admininstr_val vs)"
        "Instrs_ok2 s
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)
     admininstr_lst (mk_functype (mk_list []) (mk_list t_lst))"
        "State_ok (mk_state s f)
     (strip (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)) \<longrightarrow>
    wf_context
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C) \<longrightarrow>
    wf_config (mk_config (mk_state s f) admininstr_lst) \<longrightarrow>
    wf_state (mk_state s f) \<longrightarrow>
    Ex (Step (mk_config (mk_state s f) admininstr_lst)) \<or>
    admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
    (\<exists>vs. admininstr_lst = map admininstr_val vs)"
        "wf_store s"
        "wf_context C"
        "wf_admininstr (admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst))"
        "wf_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
        context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t'_lst],
        context_RETURN = None\<rparr>"
        "v_n = length t'_lst"
        show "State_ok (mk_state s f) (strip C) \<longrightarrow>
    wf_config
     (mk_config (mk_state s f)
       [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]) \<longrightarrow>
    wf_state (mk_state s f) \<longrightarrow>
    Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)])) \<or>
    (\<exists>v. admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst) = admininstr_val v)" 
          apply(auto)
          subgoal 
          proof -
            assume assms':
  "State_ok (mk_state s f) (strip C)"
      "wf_config
     (mk_config (mk_state s f)
       [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)])"
      "wf_state (mk_state s f)"
             "\<forall>v. admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst) \<noteq> admininstr_val v"
            have 2: "
    wf_context
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)" using 
assms(6) proof(induction "C")
                case (context_case_underscore var_3_lst var_4_lst var_0_lst var_1_lst 
                    var_2_lst var_5_lst var_6_lst var_7_lst var_8_lst var_9_opt)
                then show ?case
                  by (simp add: append_res_context_wf wf_context.context_case_underscore)
              qed     
            have 1: "strip
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C) = strip C" proof(cases C) qed(auto simp add: append_res_context_def strip_def) 
            have "Ex (Step (mk_config (mk_state s f) admininstr_lst)) \<or>
    admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or> (\<exists>vs. admininstr_lst = map admininstr_val vs)"
              using assms assms' 1 2
              by (metis Instrs_ok2_wf_instr config_case_0)
            then show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))"
            proof 
              assume "Ex (Step (mk_config (mk_state s f) admininstr_lst))"
              then obtain c where step: "Step (mk_config (mk_state s f) admininstr_lst) c" by blast
              have wf: "wf_config (mk_config (mk_state s f) admininstr_lst)"
                using assms assms'
                by (simp add: Instrs_ok2_wf_instr config_case_0)
              
              show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))" 
              proof (cases c)
                case (mk_config x1 x2)
                then show ?thesis using ctxt_label assms assms' step_wf step wf
                  by metis
              qed
                  
              next 
                assume " admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
    (\<exists>vs. admininstr_lst = map admininstr_val vs)"
                  then show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))" 
                  proof
                    assume "admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP]"
                      then show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))"
                        using trap_label Step.intros(1)
                        by blast 
                    next 
                      assume " \<exists>vs. admininstr_lst = map admininstr_val vs"
                        then show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))" 
                          using label_vals Step.intros(1)
                          by fast
                      qed qed
          qed done
      qed done
  next
    case (Instr_ok2__frame s' f' C' t_lst' admininstr_lst C v_n)
    then show ?case
      apply(auto)
      subgoal
      proof -
        assume assms:
  "Frame_ok s' f' C'"
     "Expr_ok2 s'
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
          context_RETURN = Some (mk_list t_lst')\<rparr>
       C')
     admininstr_lst (mk_list t_lst')"
     "(\<And>f C s. State_ok s (strip C) \<Longrightarrow>
            wf_context C \<Longrightarrow>
            wf_config (mk_config s admininstr_lst) \<Longrightarrow>
            wf_state s \<Longrightarrow>
            mk_state s' f = s \<Longrightarrow>
            (\<exists>cfg'. Step (mk_config s admininstr_lst) cfg') \<or>
            admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
            (\<exists>vs. admininstr_lst = map admininstr_val vs))"
     "wf_store s'"
     "wf_context C"
     "wf_context C'"
     "wf_admininstr (admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst))"
     "wf_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
        context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
        context_RETURN = Some (mk_list t_lst')\<rparr>"
     "v_n = length t_lst'"
     "State_ok (mk_state s' f) (strip C)"
     "wf_config
     (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)])"
     "wf_state (mk_state s' f)"
     "\<forall>v. admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst) \<noteq> admininstr_val v"
        have 1: "State_ok (mk_state s' f') (strip C')"
          using assms
          by (metis Frame_ok.cases State_ok.cases State_ok_strip mk_State_ok state.inject state_case_0)
        have 3: "wf_config (mk_config (mk_state s' f') admininstr_lst)" using assms 
          by (metis Expr_ok2.cases Frame_ok.cases config_case_0 state_case_0)
        have "(\<exists>cfg'. Step (mk_config (mk_state s' f') admininstr_lst) cfg') \<or>
          admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
          (\<exists>vs. admininstr_lst = map admininstr_val vs)"
          using assms(3)[OF 1 assms(6) 3] assms
          by (metis "1" State_ok.cases)
        then show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))"
        proof
          assume " \<exists>cfg'. Step (mk_config (mk_state s' f') admininstr_lst) cfg'"
          then obtain cfg' where step: "Step (mk_config (mk_state s' f') admininstr_lst) cfg'" 
            by blast
          show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))"
          proof(cases cfg')
            case (mk_config x1 x2)
            then show ?thesis using ctxt_frame 3 step_wf step
              by (metis wf_config.simps wf_state.cases)
          qed
            next
              assume " admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
    (\<exists>vs. admininstr_lst = map admininstr_val vs)"
              then show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))" 
              proof
                assume "admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP]"
                then show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))"
                  using trap_frame Step.intros(1)
                  by fast
              next
                assume "\<exists>vs. admininstr_lst = map admininstr_val vs"
                then obtain vs where val: "admininstr_lst = map admininstr_val vs" by blast
                have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: 
                    mk_instrtype (mk_list []) (mk_list t_lst')" 
                  using assms(2) val inv_expr(1) inv_const_list
                  by blast
                then have "length vs = length t_lst'" proof(induction 
                      "mk_instrtype (mk_list []) (mk_list (map typeofval vs))" 
                      "mk_instrtype (mk_list []) (mk_list t_lst')")
                  case (mk_Instrtype_sub t_lst t_11'_lst t'_lst t_12'_lst)
                  then show ?case
                    by (metis mk_Instrtype_sub.hyps(5) mk_Instrtype_sub.hyps(2) 
                          mk_Instrtype_sub.hyps(1) mk_Instrtype_sub.hyps(3) 
                          mk_Instrtype_sub.hyps(4) length_map val res_list.inject 
                          append_eq_append_conv append.assoc Resulttype_sub.simps)
                qed
                  then show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))"
                    using frame_vals Step.intros(1) val
                    by metis
                  qed
              qed
        qed done
  next
    case (Instr_ok2__call_addr s v_funcaddr t_1_lst t_2_lst C)
    then show ?case apply(auto)
      subgoal for vs
      proof -
        assume assms:
        "Externaddr_ok s (externaddr_FUNC v_funcaddr)
     (FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))"
        "wf_store s"
        "wf_context C"
        "wf_admininstr (admininstr_sc7 (CALL_ADDR v_funcaddr))"
        "wf_externtype (FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))"
        "list_all2 Valtype_sub (map typeofval vs) t_1_lst"
        "list_all wf_val vs"
        "State_ok (mk_state s f) (strip C)"
        "wf_config (mk_config (mk_state s f) [admininstr_sc7 (CALL_ADDR v_funcaddr)])"
        "wf_state (mk_state s f)"
        "\<forall>v. admininstr_sc7 (CALL_ADDR v_funcaddr) \<noteq> admininstr_val v"
        then show "Ex (Step (mk_config (mk_state s f) (map admininstr_val vs @ [admininstr_sc7 (CALL_ADDR v_funcaddr)])))" 
         proof (induction s "externaddr_FUNC v_funcaddr" "FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))")
           case (Externaddr_ok__func s v_funcinst)
           show ?case proof(cases v_funcinst)
             case (fields funcinst_TYPE mm v_func)
             then show ?thesis 
             proof(cases v_func)
               case (func_FUNC x locs body)
               have 1: "v_funcaddr < length (fun_funcinst (mk_state s f))" 
                 using Externaddr_ok__func(1) fun_funcinst.domintros fun_funcinst.psimps by auto
               have 2: "fun_funcinst (mk_state s f) ! v_funcaddr =
    \<lparr>funcinst.funcinst_TYPE = mk_functype (mk_list t_1_lst) (mk_list t_2_lst), funcinst_MODULE = mm,
       CODE = v_func\<rparr>" using Externaddr_ok__func fields
                 using fun_funcinst.domintros fun_funcinst.psimps by force
               obtain t_locs where 3: "v_func = func_FUNC x (map LOCAL t_locs) body" sorry
               have 4: "list_all (\<lambda>t. default_underscore t \<noteq> None) t_locs" sorry
               have 5: "wf_funcinst
     \<lparr>funcinst.funcinst_TYPE = mk_functype (mk_list t_1_lst) (mk_list t_2_lst), funcinst_MODULE = mm,
        CODE = v_func\<rparr>" sorry
               have 6: "wf_func (func_FUNC x (map LOCAL t_locs) body)" sorry
                 have 7: "wf_frame \<lparr>LOCALS = vs @ map (\<lambda>t. the (default_underscore t)) t_locs, 
                    frame_MODULE = mm\<rparr>" sorry
                   have 8: "length t_1_lst = length vs"
                     by (metis assms(6) length_map list_all2_lengthD)
               then show ?thesis 
                 using call_addr[where ?z = "mk_state s f" and ?val_lst = vs and ?a = v_funcaddr]  
  1 2 3 4 5 6 7 8 Step.intros(2)
                 by metis
           qed 
           qed
         next
           case (Externaddr_ok__sub s xt')
           show ?case using Externaddr_ok__sub(3,1,2,4-) 
            proof(induction xt' "FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))")
              case (Externtype_sub__func ft_1)
              then show ?case
                using Functype_sub.cases by blast
         qed      
        qed qed done
  next
    case (Instr_ok2__ref s v_ref rt C)
    then show ?case sorry
  next
    case (Instr_ok2__trap s C t_1_lst t_2_lst)
    then show ?case by auto
  next
    case (Instrs_ok2__empty s C)
    then show ?case by auto
  next
    case (Instrs_ok2__instr s C v_instr' t_1_lst' t_2_lst') 
    then show ?case
        apply(auto)
        subgoal for vs
      proof -
        assume assms:
          "Instr_ok2 s C v_instr' (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
          "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         Ex (Step (mk_config (mk_state s f) (map admininstr_val vs @ [v_instr']))) \<or>
         v_instr' = admininstr_sc7 admininstr_st7_TRAP \<or> (\<exists>v. v_instr' = admininstr_val v)"
          "wf_store s"
          "wf_context C"
          "wf_admininstr v_instr'"
          "list_all2 Valtype_sub (map typeofval vs) t_1_lst'"
          "list_all wf_val vs"
          "State_ok (mk_state s f) (strip C)"
          "wf_config (mk_config (mk_state s f) [v_instr'])"
          "wf_state (mk_state s f)"
          "\<forall>x. \<not> Step (mk_config (mk_state s f) (map admininstr_val vs @ [v_instr'])) x"
          "\<forall>vs. [v_instr'] \<noteq> map admininstr_val vs" 
        have "\<forall> v. v_instr' \<noteq> admininstr_val v"
          by (metis assms(12) list.distinct(1) opt_underscore.cases Cons_eq_map_conv)
          then show "v_instr' = admininstr_sc7 admininstr_st7_TRAP" using assms
            by blast
      qed done
  next
    case (Instrs_ok2__seq s' C' instr_1_lst t_1_lst' t_2_lst' instr_2_lst t_3_lst)
      then show ?case  
        apply(auto)
        subgoal for vs
        proof -
          assume assms:
          "Instrs_ok2 s' C' instr_1_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
          "(\<forall> vs.
          list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
          list_all wf_val vs \<longrightarrow>
          wf_config (mk_config (mk_state s' f) ( instr_1_lst)) \<longrightarrow>
           Ex (Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_1_lst))) \<or>
         instr_1_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
         (\<exists>vs. instr_1_lst = map admininstr_val vs))"
          "Instrs_ok2 s' C' instr_2_lst (mk_functype (mk_list t_2_lst') (mk_list t_3_lst))"
          "(\<forall> vs.
          list_all2 Valtype_sub (map typeofval vs) t_2_lst' \<longrightarrow>
          list_all wf_val vs \<longrightarrow>
          wf_config (mk_config (mk_state s' f) ( instr_2_lst)) \<longrightarrow>
         Ex (Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_2_lst))) \<or>
         instr_2_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
         (\<exists>vs. instr_2_lst = map admininstr_val vs))"
        "wf_store s'"
          "wf_context C'"
          "list_all wf_admininstr instr_1_lst"
          "list_all wf_admininstr instr_2_lst"
          "list_all2 Valtype_sub (map typeofval vs) t_1_lst'"
          "list_all wf_val vs"
          "State_ok (mk_state s' f) (strip C')"
          "wf_config
       (mk_config (mk_state s' f) ( instr_1_lst @ instr_2_lst))"
      "wf_state (mk_state s' f)"
       " \<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_1_lst @ instr_2_lst)) x"
   " \<forall>vs. instr_1_lst @ instr_2_lst \<noteq> map admininstr_val vs"
          show " instr_1_lst @ instr_2_lst = [admininstr_sc7 admininstr_st7_TRAP]"
       proof (cases "(Ex (Step (mk_config (mk_state s' f) 
      (map admininstr_val vs @ instr_1_lst))))")
                case True
                then have "wf_config (
                  mk_config (mk_state s' f) (map admininstr_val vs @ instr_1_lst))"
                  using assms wf_admininstr_val wf_admininstr_instr
                  config_case_0 
                  list_all_map_impl[of wf_val vs wf_admininstr admininstr_val]
                  list_all_app
                  by force
                then have "(Ex (Step (mk_config (mk_state s' f) 
      (map admininstr_val vs @ instr_1_lst @ instr_2_lst))))"
                  using True reducible_right assms 
                  by fastforce
                then show ?thesis using assms
                  by blast
              next
                case False
                note False' = False
                then show ?thesis proof(cases "instr_1_lst = [admininstr_sc7 admininstr_st7_TRAP]")
                  case True
                  then show ?thesis 
                  proof(cases instr_2_lst)
                         case Nil
                         then show ?thesis using True by simp
                       next
                         case (Cons a list)
                         then show ?thesis using True trap_vals[of "vs"] 
                              const assms(14)
                              Step.intros(1) sorry (* need to allow admininstr on RHS of trap *)
                          (* by auto *)
                       qed
                next
                  case False
                then obtain vs1 where const: "instr_1_lst = map admininstr_val vs1"
                   using assms False'
                   by (metis config_case_0)
                 then have "mk_instrtype (mk_list []) (mk_list (map typeofval vs1)) <ti: 
                      mk_instrtype (mk_list t_1_lst') (mk_list t_2_lst')"  
                   using inv_const_list assms instrs_ok_instrs_ok2 by fastforce
                 then show ?thesis
                   using const assms
                 proof(induction "mk_instrtype (mk_list []) (mk_list (map typeofval vs1))" 
                    "mk_instrtype (mk_list t_1_lst') (mk_list t_2_lst')")
                   case (mk_Instrtype_sub t_lst emp t'_lst t_12'_lst)
                   then show ?case 
                   proof(cases "Ex (Step
                   (mk_config (mk_state s' f) (map admininstr_val vs @ instr_1_lst @
                   instr_2_lst)))")
                     case True
                     then show ?thesis using mk_Instrtype_sub
                       by fast
                   next
                     case False
                     have 1: "list_all2 Valtype_sub (map typeofval (vs @ vs1)) t_2_lst'"
                       using mk_Instrtype_sub(3,1,2,4-6,15)
                     proof(induction "mk_list t_lst" "mk_list t'_lst")
                       case mk_Resulttype_sub
                       show ?case using mk_Resulttype_sub(6,1-5,7-)
                        proof(induction "mk_list (map typeofval vs1)" "mk_list t_12'_lst")
                          case mk_Resulttype_sub
                          have "emp = []" using mk_Resulttype_sub(7)
                            by (simp add: Resulttype_sub.simps)
                          then have "list_all2 Valtype_sub (map typeofval vs) t'_lst"
                            using mk_Resulttype_sub Valtype_sub_trans 
                              list_all2_trans[of Valtype_sub Valtype_sub Valtype_sub "map typeofval vs"
                                  t_1_lst' t'_lst]
                            by fastforce
                          then show ?case using mk_Resulttype_sub(2,6)
                            by (simp add: list_all2_appendI)
                        qed
                     qed
                     have 2: "list_all wf_val (vs @ vs1)" 
                       using mk_Instrtype_sub wf_admininstr_val_inv 
                       list_all_map_impl_inv[of wf_admininstr admininstr_val vs1 wf_val ]
                       by simp
                     have 3: "(\<forall>x. \<not> Step
                   (mk_config (mk_state s' f) (map admininstr_val (vs @ vs1) @ instr_2_lst))
                   x)" using False const
                       by fastforce
                     show ?thesis 
                     proof (cases "instr_2_lst = [admininstr_sc7 admininstr_st7_TRAP]")
                       case True
                       then show ?thesis proof(cases vs1)
                         case Nil
                         then show ?thesis using True const by simp
                       next
                         case (Cons a list)
                         then show ?thesis using True trap_vals[of "vs @ vs1" "[]"] const mk_Instrtype_sub(20)
                    Step.intros(1)
                           by auto
                       qed
                     next
                       case False
                     then obtain vs2 where "instr_2_lst = map admininstr_val vs2"
                       using mk_Instrtype_sub 1 2 3 
                       by (metis config_case_0)
                     then show ?thesis using const
                       by (metis \<open>instr_2_lst = map admininstr_val vs2\<close> 
                            local.const mk_Instrtype_sub.prems(16) map_append)
                   qed
                 qed 
              qed qed qed
        qed done 
  next
    case (Instrs_ok2__sub s' C' instr_lst t_1_lst' t_2_lst' t'_1_lst t'_2_lst)
      then show ?case
        apply(auto)
        subgoal for vs
        proof -
          assume  assms:
            "Instrs_ok2 s' C' instr_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
    "Resulttype_sub (mk_list t'_1_lst) (mk_list t_1_lst')"
    "Resulttype_sub (mk_list t_2_lst') (mk_list t'_2_lst)"
    "wf_context C'"
    "list_all wf_admininstr instr_lst"
    "wf_store s'"
    "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
        Ex (Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_lst))) \<or>
         instr_lst = [admininstr_sc7 admininstr_st7_TRAP]"
    "list_all2 Valtype_sub (map typeofval vs) t'_1_lst"
    "list_all wf_val vs"
    "State_ok (mk_state s' f) (strip C')"
    "wf_config (mk_config (mk_state s' f) ( instr_lst))"
    "wf_state (mk_state s' f)"
    "\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_lst)) x"
          have "list_all2 Valtype_sub (map typeofval vs) t_1_lst'" 
            using assms(2,8) proof(induction "mk_list t'_1_lst" "mk_list t_1_lst'")
            case mk_Resulttype_sub
            then show ?case using Valtype_sub_trans list_all2_trans 
              by blast 
          qed
          then show " instr_lst = [admininstr_sc7 admininstr_st7_TRAP]" 
            using assms
            by blast
        qed done
  next
    case (Instrs_ok2__frame s' C' instr_lst t_1_lst' t_2_lst' t_lst)
      then show ?case 
        apply(auto)
        subgoal for vs
        proof -
          assume assms:
  "Instrs_ok2 s' C' instr_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
    "wf_context C'"
    "list_all wf_admininstr instr_lst"
    "wf_store s'"
    "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
          Ex (Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_lst))) \<or>
         instr_lst = [admininstr_sc7 admininstr_st7_TRAP]"
    "list_all2 Valtype_sub (map typeofval vs) (t_lst @ t_1_lst')"
    "list_all wf_val vs"
    "State_ok (mk_state s' f) (strip C')"
    "wf_config (mk_config (mk_state s' f) ( instr_lst))"
    "wf_state (mk_state s' f)"
    "\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_lst)) x"
          then obtain ts1 ts2 where split1:
            "map typeofval vs = ts1 @ ts2" "list_all2 Valtype_sub ts1 t_lst" 
            "list_all2 Valtype_sub ts2 t_1_lst'" 
            using list_all2_append2
            by metis
          then obtain vs1 vs2 where split2:
            "vs = vs1 @ vs2" "ts1 = map typeofval vs1" "ts2 = map typeofval vs2" 
            using map_is_app by blast
          show "instr_lst = [admininstr_sc7 admininstr_st7_TRAP]" 
          proof (cases "Ex (Step (mk_config (mk_state s' f) 
              (map admininstr_val vs2 @ instr_lst)))")
            case True
            have "wf_config (mk_config (mk_state s' f) 
                (map admininstr_val vs2 @  instr_lst))"
              using assms split2
              by (metis config_case_0 list_all_append list_all_map_impl wf_admininstr_val)
            then show ?thesis using assms split2 reducible_left_v[OF True, of vs1]
              by auto
          next
            case False
            then show ?thesis using assms
              using split1(3) split2(1,3) by auto
          qed
        qed done
  next
    case (mk_Expr_ok2 s C admininstr_lst)
    then show ?case
      by auto
  qed
qed

end