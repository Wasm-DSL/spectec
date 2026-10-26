theory Progress
(* Imported Code *)
	imports isabelle_reference_output_wasm2 store_extension_typing Properties 
	        Type_Inversion Subtyping_Theorem Context_Store_Agreement Preservation Axioms
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

definition not_br_return :: "admininstr list \<Rightarrow> bool" where 
  "not_br_return es = 
      ((\<forall> vs l aft. es \<noteq> map admininstr_val vs @ [admininstr_sc0
        (admininstr_st0_BR l)] @ aft) \<and> 
      (\<forall> vs aft. es \<noteq> map admininstr_val vs @ [
        admininstr_sc1 admininstr_st1_RETURN] @ aft))" 

lemma br_type_not_strip: 
  assumes 
    "es = map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR l)] @ aft"
    "Expr_ok2 s C es ts" 
  shows "C \<noteq> strip C" 
proof - 
  have "Instrs_ok2 s C es (mk_functype (mk_list []) ts)" using inv_expr[OF assms(2)] by simp
  then obtain t1 where 
     "Instrs_ok2 s C ([admininstr_sc0 (admininstr_st0_BR l)] @ aft) (mk_functype
        t1 ts)" using inv_seq[OF _ assms(1)] by blast
  then obtain t2 where 
     "Instrs_ok2 s C [admininstr_sc0 (admininstr_st0_BR l)] (mk_functype t1 t2)" 
    using inv_seq by blast
  then obtain t1' t2' where "Instr_ok2 s C (admininstr_sc0 (admininstr_st0_BR l)) (mk_functype t1' t2')"
    using inv_one_admininstr by blast
  then have "Instr_ok C (instr_sc0 (BR l)) (mk_functype t1' t2')" 
    using inv_plain admininstr_instr.domintros admininstr_instr.psimps by fastforce
  then have "proj_uN_0 l < length (LABELS C)" using inv_br by auto
  then have "LABELS C \<noteq> []" by auto
  then show ?thesis proof(induction C) qed(auto simp add: strip_def) 
qed

lemma return_type_not_strip: 
  assumes 
    "es = map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ aft"
    "Expr_ok2 s C es ts" 
  shows "C \<noteq> strip C" 
proof - 
  have "Instrs_ok2 s C es (mk_functype (mk_list []) ts)" using inv_expr[OF assms(2)] by simp
  then obtain t1 where 
     "Instrs_ok2 s C ([admininstr_sc1 admininstr_st1_RETURN] @ aft) (mk_functype
        t1 ts)" using inv_seq[OF _ assms(1)] by blast
  then obtain t2 where 
     "Instrs_ok2 s C [admininstr_sc1 admininstr_st1_RETURN] (mk_functype t1 t2)" 
    using inv_seq by blast
  then obtain t1' t2' where "Instr_ok2 s C (admininstr_sc1 admininstr_st1_RETURN) (mk_functype t1' t2')"
    using inv_one_admininstr by blast
  then have "Instr_ok C (instr_sc1 RETURN) (mk_functype t1' t2')" 
    using inv_plain admininstr_instr.domintros admininstr_instr.psimps by fastforce
  then obtain t_lst where "context_RETURN C = Some (mk_list t_lst)" using inv_return by blast
  then have "context_RETURN C \<noteq> None" by auto
  then show ?thesis proof(induction C) qed(auto simp add: strip_def) 
qed

lemma typecheck_strip_not_return: 
  assumes "Expr_ok2 s C es ts" "C = strip C"
  shows "not_br_return es" 
  using assms br_type_not_strip return_type_not_strip not_br_return_def
  by metis

lemma br_return_contaminate_left:
  assumes "\<not> (not_br_return es)" 
  shows "\<not> (not_br_return (map admininstr_val vs @ es))" 
proof - 
  have "((\<exists> vs l aft. es = map admininstr_val vs @ [admininstr_sc0
        (admininstr_st0_BR l)] @ aft) \<or> 
      (\<exists> vs aft. es = map admininstr_val vs @ [
        admininstr_sc1 admininstr_st1_RETURN] @ aft))"
    using assms not_br_return_def by simp
  then show ?thesis proof
    assume "\<exists>vs l aft. es = map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR l)] @ aft"
    then obtain vs' l aft where "es = map admininstr_val vs' @ 
          [admininstr_sc0 (admininstr_st0_BR l)] @ aft" by blast
    then show "\<not> not_br_return (map admininstr_val vs @ es)"
      by (metis append.assoc map_append not_br_return_def)
  next 
    assume "\<exists>vs aft. es = map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ aft"
    then obtain vs' aft where 
      "es = map admininstr_val vs' @ [admininstr_sc1 admininstr_st1_RETURN] @ aft" by blast
    then show "\<not> not_br_return (map admininstr_val vs @ es)"
      by (metis map_append not_br_return_def append.assoc)
  qed
qed


lemma br_return_contaminate_right:
  assumes "\<not> (not_br_return es)" 
  shows "\<not> (not_br_return (es @ es'))" 
proof - 
  have "((\<exists> vs l aft. es = map admininstr_val vs @ [admininstr_sc0
        (admininstr_st0_BR l)] @ aft) \<or> 
      (\<exists> vs aft. es = map admininstr_val vs @ [
        admininstr_sc1 admininstr_st1_RETURN] @ aft))"
    using assms not_br_return_def by simp
  then show ?thesis proof
    assume "\<exists>vs l aft. es = map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR l)] @ aft"
    then obtain vs' l aft where "es = map admininstr_val vs' @ 
          [admininstr_sc0 (admininstr_st0_BR l)] @ aft" by blast
    then show "\<not> not_br_return (es @ es')"
      by (metis append.assoc not_br_return_def)
  next 
    assume "\<exists>vs aft. es = map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ aft"
    then obtain vs' aft where 
      "es = map admininstr_val vs' @ [admininstr_sc1 admininstr_st1_RETURN] @ aft" by blast
    then show "\<not> not_br_return (es @ es')"
      by (metis not_br_return_def append.assoc)
  qed
qed

lemma list_splitable: assumes "length l \<ge> n" shows "\<exists> l1 l2. l = l1 @ l2 \<and> length l2 = n" 
  using assms 
  by (metis append_take_drop_id diff_diff_cancel length_drop)

lemma default_not_bot: assumes "t \<noteq> BOT" shows "default_underscore t \<noteq> None" 
proof(cases t) qed(auto simp add: assms default_underscore.domintros default_underscore.psimps)

lemma Inn_Fnn_diff: "numtype_Inn x \<noteq> numtype_Fnn y" 
proof(induction x)
  case Inn_I32
  then show ?case proof(induction y) qed(auto simp add: numtype_Inn.domintros numtype_Inn.psimps
numtype_Fnn.domintros numtype_Fnn.psimps)
next
  case Inn_I64
  then show ?case proof(induction y) qed(auto simp add: numtype_Inn.domintros numtype_Inn.psimps
numtype_Fnn.domintros numtype_Fnn.psimps)
qed

lemma fun_unop_underscore_total:
  assumes "wf_val (val_CONST nt c)" "wf_unop_underscore nt op"
  shows "fun_unop_underscore nt op c \<noteq> None"
  using assms proof(induction "val_CONST nt c")
  case val_case_0
  then show ?case proof(induction nt c)
    case (num__case_0 v_Inn var_x v_numtype)
    show ?case using num__case_0(4,1-3) proof(induction v_numtype op)
      case (unop__case_0 v_numtype v_Inn' var_x')
      then have eqv: "v_Inn = v_Inn'"
        by (metis numtype.simps(2) numtype_Inn.elims)
      then show ?case using unop__case_0 proof(induction v_Inn)
        case Inn_I32
        then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
fun_unop_underscore.domintros fun_unop_underscore.psimps fun_unop__I32.domintros
fun_unop__I32.psimps proof(induction var_x') qed(auto)
      next
        case Inn_I64
        then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
fun_unop_underscore.domintros fun_unop_underscore.psimps fun_unop__I64.domintros
fun_unop__I64.psimps proof(induction var_x') qed(auto)
      qed
    next
      case (unop__case_1 v_numtype v_Fnn var_x)
      then show ?case using Inn_Fnn_diff by simp
    qed
  next
    case (num__case_1 v_Fnn var_x v_numtype)
    show ?case using num__case_1(3,1-2) proof(induction v_numtype op)
      case (unop__case_0 v_numtype v_Inn var_x')
      then show ?case using Inn_Fnn_diff
        by blast
    next
      case (unop__case_1 v_numtype v_Fnn' var_x')
      then have eqv: "v_Fnn = v_Fnn'"
        by (metis Fnn.exhaust numtype.distinct(11) numtype_Fnn.domintros(1,2) numtype_Fnn.psimps(1,2))
      then show ?case using unop__case_1 proof(induction v_Fnn)
        case Fnn_F32
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
fun_unop_underscore.domintros fun_unop_underscore.psimps fun_unop__F32.domintros
fun_unop__F32.psimps proof(induction var_x') qed(auto)
      next
        case Fnn_F64
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
fun_unop_underscore.domintros fun_unop_underscore.psimps fun_unop__F64.domintros
fun_unop__F64.psimps proof(induction var_x') qed(auto)
      qed
    qed
  qed
qed


lemma fun_testop_underscore_total:
  assumes "wf_val (val_CONST nt c)" "wf_testop_underscore nt op"
  shows "fun_testop_underscore nt op c \<noteq> None"
  using assms proof(induction "val_CONST nt c")
  case val_case_0
  then show ?case proof(induction nt c)
    case (num__case_0 v_Inn var_x v_numtype)
    show ?case using num__case_0(4,1-3) proof(induction v_numtype op)
      case (testop__case_0 v_numtype v_Inn' var_x')
      then have eqv: "v_Inn = v_Inn'"
        by (metis numtype.simps(2) numtype_Inn.elims)
      then show ?case using unop__case_0 proof(induction v_Inn)
        case Inn_I32
        then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
fun_testop_underscore.domintros fun_testop_underscore.psimps proof(induction var_x')
          case EQZ
          then show ?case
            by (metis option.distinct(1) testop__case_0.hyps)
        qed
      next
        case Inn_I64
        then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
fun_testop_underscore.domintros fun_testop_underscore.psimps 
        proof(induction var_x')
          case EQZ
          then show ?case
            by (simp add: testop__case_0.hyps)
        qed 
      qed
    qed
  next
    case (num__case_1 v_Fnn var_x v_numtype)
    show ?case using num__case_1(3,1-2) proof(induction v_numtype op)
      case (testop__case_0 v_numtype v_Inn var_x')
      then show ?case using Inn_Fnn_diff
        by blast
      qed
    qed
  qed

lemma fun_signed_underscore_total:
  assumes "0 \<le> c \<and> c \<le> 2 ^ sz - 1" 
  shows "\<exists> res. fun_signed_underscore sz c res \<and> (0 - (2 ^ (sz - 1)) \<le> res) \<and> 
            res \<le> 2 ^ (sz - 1) - 1" 
proof (cases "c \<le> 2 ^ (sz - 1) - 1")
  case True
  then show ?thesis using assms fun_signed_underscore.intros(1)
    by (metis diff_diff_cancel diff_less less_imp_diff_less nat_zero_less_power_iff power_0 zero_diff
        zero_less_numeral)
next
  case False
  then show ?thesis using assms fun_signed_underscore.intros(2)
    by (metis (no_types, lifting) dec_less_imp_less_eq diff_diff_cancel diff_less less_imp_diff_less
        linorder_not_le nat_diff_split nat_zero_less_power_iff power_0 zero_less_numeral)
qed

lemma fun_inv_signed_underscore_total:
  assumes "0 - 2 ^ (sz - 1) \<le> c \<and> c \<le> 2 ^ (sz - 1) - 1" 
  shows "\<exists> res. fun_inv_signed_underscore sz c res \<and> 0 \<le> res \<and> res \<le> 2 ^ sz - 1" 
proof(cases "0 \<le> c")
  case True
  then have 1: "0 \<le> c \<and> c < 2 ^ (sz - 1)"
    by (metis assms diff_diff_cancel diff_less less_imp_diff_less nat_zero_less_power_iff power_0
        zero_less_numeral)
  show ?thesis using fun_inv_signed_underscore.intros(1)[OF 1] 1
    by (metis wf_uN.simps fun_inv_signed_wf proj_uN_0.psimps proj_uN_0.domintros)
next
  case False
  then show ?thesis using assms fun_inv_signed_underscore.intros(2)
    by blast
qed



lemma fun_idiv_underscore_total:
  assumes "0 \<le> c1 \<and> c1 \<le> 2 ^ sz - 1" "0 \<le> c2 \<and> c2 \<le> 2 ^ sz - 1"
  shows "\<exists> res. fun_idiv_underscore sz sg (mk_uN c1) (mk_uN c2) res"
  using assms proof(induction sg)
  case U
  then show ?case using fun_idiv_underscore.intros(1,2) wf_uN.intros truncz_spec
    by (metis fun_idiv__case_1 assms(1) truncz_spec uN_case_0 proj_uN_0.psimps 
        proj_uN_0.domintros div_le_dividend bot_nat_0.extremum le_trans)
next
  case S
  then show ?case proof(cases c2)
    case 0
    then show ?thesis using fun_idiv_underscore.intros(3) by blast
  next
    case (Suc nat)
    obtain c1' where c1: "fun_signed_underscore sz (proj_uN_0 (mk_uN c1)) c1'" 
      "0 - 2 ^ (sz - 1) \<le> c1' \<and> c1' \<le> 2 ^ (sz - 1) - 1" 
      using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps
      by metis
    obtain c2' where c2: "fun_signed_underscore sz (proj_uN_0 (mk_uN c2)) c2'" 
      "0 - 2 ^ (sz - 1) \<le> c2' \<and> c2' \<le> 2 ^ (sz - 1) - 1" 
      using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps
      by metis
    show ?thesis proof(cases "c1' div c2' = 2 ^ (sz - 1)")
      case True
      show ?thesis using fun_idiv_underscore.intros(4)[OF c2(1) c1(1) True] by blast
    next
      case False
      then have "0 - 2 ^ (sz - 1) \<le> truncz (c1' div c2') \<and> truncz (c1' div c2') \<le> 2 ^ (sz - 1) - 1" 
        using truncz_spec
        by (metis bot_nat_0.extremum c1(2) div_le_dividend le_trans zero_diff)
      then obtain res where 1: "fun_inv_signed_underscore sz (truncz (c1' div c2')) res" 
        using fun_inv_signed_underscore_total[of sz "truncz (c1' div c2')"] by blast
      show ?thesis using fun_idiv_underscore.intros(5)[OF c2(1) c1(1) 1] wf_uN.intros
        by (meson "1" fun_inv_signed_wf)
    qed
  qed
qed

lemma fun_irem_underscore_total:
  assumes "0 \<le> c1 \<and> c1 \<le> 2 ^ sz - 1" "0 \<le> c2 \<and> c2 \<le> 2 ^ sz - 1"
  shows "\<exists> res. fun_irem_underscore sz sg (mk_uN c1) (mk_uN c2) res"
proof (cases sg)
  case U
  then show ?thesis using assms fun_irem_underscore.intros(1,2) by blast
next
  case S
  then show ?thesis proof(cases c2)
    case 0
    then show ?thesis using S fun_irem_underscore.intros(3) by blast
  next
    case (Suc nat)
     obtain c1' where c1: "fun_signed_underscore sz (proj_uN_0 (mk_uN c1)) c1'" 
      "0 - 2 ^ (sz - 1) \<le> c1' \<and> c1' \<le> 2 ^ (sz - 1) - 1" 
      using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps
      by metis
    obtain c2' where c2: "fun_signed_underscore sz (proj_uN_0 (mk_uN c2)) c2'" 
      "0 - 2 ^ (sz - 1) \<le> c2' \<and> c2' \<le> 2 ^ (sz - 1) - 1" 
      using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps
      by metis
    have "0 - 2 ^ (sz - 1) \<le> c1' - c2' * truncz (c1' div c2') \<and> c1' - c2' * truncz (c1' div c2') \<le> 2 ^ (sz - 1) - 1" 
      using truncz_spec
      using c1(2) diff_le_self le_trans by blast
    then obtain res where 1: "fun_inv_signed_underscore sz (c1' - c2' * truncz (c1' div c2')) res" 
      using fun_inv_signed_underscore_total by blast
    show ?thesis using fun_irem_underscore.intros(4)[OF c2(1) c1(1) 1] S by blast
  qed
qed



lemma numtype_size_simps:
  "numtype_Fnn Fnn_F32 = F32" "numtype_Fnn Fnn_F64 = F64"
  "valtype_Inn Inn_I32 = valtype_I32" "valtype_Inn Inn_I64 = valtype_I64"
  "valtype_Fnn Fnn_F32 = valtype_F32" "valtype_Fnn Fnn_F64 = valtype_F64"
  "sizenn I32 = 32" "sizenn I64 = 64" "sizenn F32 = 32" "sizenn F64 = 64"
  "sizenn1 I32 = 32" "sizenn1 I64 = 64" "sizenn1 F32 = 32" "sizenn1 F64 = 64"
  "sizenn2 I32 = 32" "sizenn2 I64 = 64" "sizenn2 F32 = 32" "sizenn2 F64 = 64"
  by (simp_all add: numtype_Inn.psimps numtype_Inn.domintros numtype_Fnn.psimps
      numtype_Fnn.domintros valtype_Inn.psimps valtype_Inn.domintros valtype_Fnn.psimps
      valtype_Fnn.domintros size.psimps size.domintros sizenn.psimps sizenn.domintros
      sizenn1.psimps sizenn1.domintros sizenn2.psimps sizenn2.domintros
      valtype_numtype.psimps valtype_numtype.domintros)

lemma Inn_inj: "numtype_Inn a = numtype_Inn b \<Longrightarrow> a = b"
  by (cases a; cases b) (simp_all add: numtype_size_simps)

lemma Fnn_inj: "numtype_Fnn a = numtype_Fnn b \<Longrightarrow> a = b"
  by (cases a; cases b) (simp_all add: numtype_size_simps)

lemma fun_binop_underscore_total:
  assumes "wf_val (val_CONST nt c1)" "wf_val (val_CONST nt c2)" "wf_binop_underscore nt op"
  shows "\<exists> res. fun_binop_underscore nt op c1 c2 (Some res)"
proof -
  note numtype_size_simps[simp]
  have wf1: "wf_num_underscore nt c1" and wf2: "wf_num_underscore nt c2"
    using assms(1,2) wf_val.simps by auto
  from assms(3) show ?thesis
  proof cases
    case (binop__case_0 inn x)
    define sz where "sz = the (size (valtype_Inn inn))"
    have sz: "sizenn (numtype_Inn inn) = sz" unfolding sz_def by (cases inn) simp_all
    have inv: "\<exists>i. c = mk_num__0 inn (mk_uN i) \<and> 0 \<le> i \<and> i \<le> 2 ^ sz - 1"
      if "wf_num_underscore nt c" for c
      using that
    proof cases
      case (num__case_0 inn' v)
      then have "inn' = inn" using binop__case_0 Inn_inj by auto
      then show ?thesis using num__case_0 by (auto simp: sz_def elim!: wf_uN.cases)
    next
      case (num__case_1 fnn v)
      then show ?thesis using binop__case_0 Inn_Fnn_diff by metis
    qed
    obtain i1 i2 where c: "c1 = mk_num__0 inn (mk_uN i1)" "c2 = mk_num__0 inn (mk_uN i2)"
      and b: "0 \<le> i1 \<and> i1 \<le> 2 ^ sz - 1" "0 \<le> i2 \<and> i2 \<le> 2 ^ sz - 1"
      using inv[OF wf1] inv[OF wf2] by blast
    have w: "wf_uN sz (mk_uN i1)" "wf_uN sz (mk_uN i2)" using b by (auto intro: wf_uN.intros)
    have opt: "list_all (\<lambda>i. wf_num_underscore (numtype_Inn inn) (mk_num__0 inn i)) (option_to_list r)
      \<and> list_all (wf_num_underscore (numtype_Inn inn)) (list_underscore (map_option (mk_num__0 inn) r))"
      if "list_all (wf_uN sz) (option_to_list r)" for r
      using that by (cases inn; cases r)
        (auto simp: sz_def list_underscore.psimps list_underscore.domintros intro: num__case_0)
    show ?thesis
    proof (cases x)
      case (DIV sx)
      obtain r where r: "fun_idiv_underscore sz sx (mk_uN i1) (mk_uN i2) r"
        using fun_idiv_underscore_total[OF b] by blast
      have "list_all (wf_uN sz) (option_to_list r)"
        using r by (cases rule: fun_idiv_underscore.cases) auto
      then show ?thesis using r opt binop__case_0 c DIV
        by (cases inn) (auto simp: sz_def
            intro!: exI[of _ "list_underscore (map_option (mk_num__0 inn) r)"]
              fun_binop_underscore.intros(7,8))
    next
      case (REM sx)
      obtain r where r: "fun_irem_underscore sz sx (mk_uN i1) (mk_uN i2) r"
        using fun_irem_underscore_total[OF b] by blast
      have "list_all (wf_uN sz) (option_to_list r)"
        using irem__is_wf[OF r w HOL.refl] .
      then show ?thesis using r opt binop__case_0 c REM
        by (cases inn) (auto simp: sz_def
            intro!: exI[of _ "list_underscore (map_option (mk_num__0 inn) r)"]
              fun_binop_underscore.intros(9,10))
    qed (insert binop__case_0 c w, (cases inn; auto simp: sz_def
          intro!: exI fun_binop_underscore.intros num__case_0
            iadd__is_wf[OF _ _ HOL.refl] isub__is_wf[OF _ _ HOL.refl] imul__is_wf[OF _ _ HOL.refl]
            iand__is_wf[OF _ _ HOL.refl] ior__is_wf[OF _ _ HOL.refl] ixor__is_wf[OF _ _ HOL.refl]
            ishl__is_wf[OF _ _ HOL.refl] ishr__is_wf[OF _ _ HOL.refl]
            irotl__is_wf[OF _ _ HOL.refl] irotr__is_wf[OF _ _ HOL.refl])+)
  next
    case (binop__case_1 fnn x)
    have inv: "\<exists>f. c = mk_num__1 fnn f \<and> wf_fN (sizenn nt) f"
      if "wf_num_underscore nt c" for c
      using that
    proof cases
      case (num__case_0 inn v)
      then show ?thesis using binop__case_1 Inn_Fnn_diff by metis
    next
      case (num__case_1 fnn' v)
      then have "fnn' = fnn" using binop__case_1 Fnn_inj by auto
      then show ?thesis using num__case_1 by auto
    qed
    obtain f1 f2 where c: "c1 = mk_num__1 fnn f1" "c2 = mk_num__1 fnn f2"
      and w: "wf_fN (sizenn nt) f1" "wf_fN (sizenn nt) f2"
      using inv[OF wf1] inv[OF wf2] by blast
    have lift: "\<And>l. list_all (wf_fN (sizenn nt)) l \<Longrightarrow>
      list_all (\<lambda>f. wf_num_underscore nt (mk_num__1 fnn f)) l"
      using binop__case_1 by (auto simp: list_all_iff intro: num__case_1)
    note fw = fadd__is_wf[OF w HOL.refl] fsub__is_wf[OF w HOL.refl] fmul__is_wf[OF w HOL.refl]
      fdiv__is_wf[OF w HOL.refl] fmin__is_wf[OF w HOL.refl] fmax__is_wf[OF w HOL.refl]
      fcopysign__is_wf[OF w HOL.refl]
    show ?thesis using binop__case_1 c fw lift[OF fw(1)] lift[OF fw(2)] lift[OF fw(3)]
      lift[OF fw(4)] lift[OF fw(5)] lift[OF fw(6)] lift[OF fw(7)]
      by (cases fnn; cases x) (auto intro!: exI fun_binop_underscore.intros)
  qed
qed

lemma fun_ilt_underscore_total:
  assumes "0 \<le> c1 \<and> c1 \<le> 2 ^ sz - 1" "0 \<le> c2 \<and> c2 \<le> 2 ^ sz - 1" 
  shows "\<exists> res. fun_ilt_underscore sz sg (mk_uN c1) (mk_uN c2) res"
proof(cases sg)
  case U
  then show ?thesis using fun_ilt_underscore.intros(1) by blast
next
  case S
  obtain c1' where c1: "fun_signed_underscore sz (proj_uN_0 (mk_uN c1)) c1'" 
    using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps by fastforce
  obtain c2' where c2: "fun_signed_underscore sz (proj_uN_0 (mk_uN c2)) c2'" 
    using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps by fastforce
  show ?thesis using S c1 c2 fun_ilt_underscore.intros(2) by blast
qed

lemma fun_igt_underscore_total:
  assumes "0 \<le> c1 \<and> c1 \<le> 2 ^ sz - 1" "0 \<le> c2 \<and> c2 \<le> 2 ^ sz - 1" 
  shows "\<exists> res. fun_igt_underscore sz sg (mk_uN c1) (mk_uN c2) res"
proof(cases sg)
  case U
  then show ?thesis using fun_igt_underscore.intros(1) by blast
next
  case S
  obtain c1' where c1: "fun_signed_underscore sz (proj_uN_0 (mk_uN c1)) c1'" 
    using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps by fastforce
  obtain c2' where c2: "fun_signed_underscore sz (proj_uN_0 (mk_uN c2)) c2'" 
    using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps by fastforce
  show ?thesis using S c1 c2 fun_igt_underscore.intros(2) by blast
qed

lemma fun_ile_underscore_total:
  assumes "0 \<le> c1 \<and> c1 \<le> 2 ^ sz - 1" "0 \<le> c2 \<and> c2 \<le> 2 ^ sz - 1" 
  shows "\<exists> res. fun_ile_underscore sz sg (mk_uN c1) (mk_uN c2) res"
proof(cases sg)
  case U
  then show ?thesis using fun_ile_underscore.intros(1) by blast
next
  case S
  obtain c1' where c1: "fun_signed_underscore sz (proj_uN_0 (mk_uN c1)) c1'" 
    using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps by fastforce
  obtain c2' where c2: "fun_signed_underscore sz (proj_uN_0 (mk_uN c2)) c2'" 
    using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps by fastforce
  show ?thesis using S c1 c2 fun_ile_underscore.intros(2) by blast
qed

lemma fun_ige_underscore_total:
  assumes "0 \<le> c1 \<and> c1 \<le> 2 ^ sz - 1" "0 \<le> c2 \<and> c2 \<le> 2 ^ sz - 1" 
  shows "\<exists> res. fun_ige_underscore sz sg (mk_uN c1) (mk_uN c2) res"
proof(cases sg)
  case U
  then show ?thesis using fun_ige_underscore.intros(1) by blast
next
  case S
  obtain c1' where c1: "fun_signed_underscore sz (proj_uN_0 (mk_uN c1)) c1'" 
    using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps by fastforce
  obtain c2' where c2: "fun_signed_underscore sz (proj_uN_0 (mk_uN c2)) c2'" 
    using fun_signed_underscore_total assms proj_uN_0.domintros proj_uN_0.psimps by fastforce
  show ?thesis using S c1 c2 fun_ige_underscore.intros(2) by blast
qed

lemma fun_relop_underscore_total:
  assumes "wf_val (val_CONST nt c1)" "wf_val (val_CONST nt c2)" "wf_relop_underscore nt op"
  shows "\<exists> res. fun_relop_underscore nt op c1 c2 (Some res)"
  using assms proof(induction "val_CONST nt c1")
  case val_case_0
  then show ?case proof(induction nt c1)
    case (num__case_0 v_Inn var_x v_numtype)
    show ?case using num__case_0(2,1,3-)
    proof(induction "the (size (valtype_Inn v_Inn))" var_x)
      case (uN_case_0 i)
    show ?case using uN_case_0(4,1-3,5-)
    proof(induction "val_CONST v_numtype c2")
      case val_case_0
      then show ?case proof(induction v_numtype c2)
        case (num__case_0 v_Inn' var_y v_numtype)
        then have eqv: "v_Inn = v_Inn'" by (metis numtype.simps(2) numtype_Inn.elims)
        show ?case using num__case_0(2,1,3-) eqv 
        proof(induction "the (size (valtype_Inn v_Inn'))" var_y)
          case (uN_case_0 i')
        show ?case using uN_case_0(7,1-6,8-)
    proof(induction v_numtype op)
      case (relop__case_0 v_numtype v_Inn'' var_x')
      then have eqv: "v_Inn = v_Inn''"
        by (metis numtype.simps(2) numtype_Inn.elims)
      show ?case using relop__case_0 eqv proof(induction v_Inn)
        case Inn_I32
        then show ?case using numtype_Inn.domintros numtype_Inn.psimps fun_relop_underscore.intros
        proof(induction var_x')
          case (LT x)
          have 1: "0 \<le> i' \<and> i' \<le> 2 ^ 32 - 1" using LT size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          have 2: "0 \<le> i \<and> i \<le> 2 ^ 32 - 1" using LT size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          obtain res where 
            res: "fun_ilt_underscore (sizenn (numtype_Inn Inn_I32)) x (mk_uN i) (mk_uN i') res"
            using fun_ilt_underscore_total[OF 2 1]
            sizenn.domintros sizenn.psimps
            by fastforce
          show ?case using LT(18)[OF res]
            using LT.prems(7,8,9) by auto
        next
          case (GT x)
          have 1: "0 \<le> i' \<and> i' \<le> 2 ^ 32 - 1" using GT size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          have 2: "0 \<le> i \<and> i \<le> 2 ^ 32 - 1" using GT size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          obtain res where 
            res: "fun_igt_underscore (sizenn (numtype_Inn Inn_I32)) x (mk_uN i) (mk_uN i') res"
            using fun_igt_underscore_total[OF 2 1]
            sizenn.domintros sizenn.psimps
            by fastforce
          show ?case using GT(20)[OF res]
            using GT.prems(7,8,9) by auto
        next
          case (LE x)
          have 1: "0 \<le> i' \<and> i' \<le> 2 ^ 32 - 1" using LE size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          have 2: "0 \<le> i \<and> i \<le> 2 ^ 32 - 1" using LE size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          obtain res where 
            res: "fun_ile_underscore (sizenn (numtype_Inn Inn_I32)) x (mk_uN i) (mk_uN i') res"
            using fun_ile_underscore_total[OF 2 1]
            sizenn.domintros sizenn.psimps
            by fastforce
          show ?case using LE(22)[OF res]
            using LE.prems(7,8,9) by auto
        next
          case (GE x)
          have 1: "0 \<le> i' \<and> i' \<le> 2 ^ 32 - 1" using GE size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          have 2: "0 \<le> i \<and> i \<le> 2 ^ 32 - 1" using GE size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          obtain res where 
            res: "fun_ige_underscore (sizenn (numtype_Inn Inn_I32)) x (mk_uN i) (mk_uN i') res"
            using fun_ige_underscore_total[OF 2 1]
            sizenn.domintros sizenn.psimps
            by fastforce
          show ?case using GE(24)[OF res]
            using GE.prems(7,8,9) by auto
        qed(metis)+
      next
        case Inn_I64
        then show ?case using numtype_Inn.domintros numtype_Inn.psimps fun_relop_underscore.intros
        proof(induction var_x')
          case (LT x)
          have 1: "0 \<le> i' \<and> i' \<le> 2 ^ 64 - 1" using LT size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          have 2: "0 \<le> i \<and> i \<le> 2 ^ 64 - 1" using LT size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          obtain res where 
            res: "fun_ilt_underscore (sizenn (numtype_Inn Inn_I64)) x (mk_uN i) (mk_uN i') res"
            using fun_ilt_underscore_total[OF 2 1]
            sizenn.domintros sizenn.psimps
            by fastforce
          show ?case using LT(19)[OF res]
            using LT.prems(7,8,9) by auto
        next
          case (GT x)
          have 1: "0 \<le> i' \<and> i' \<le> 2 ^ 64 - 1" using GT size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          have 2: "0 \<le> i \<and> i \<le> 2 ^ 64 - 1" using GT size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          obtain res where 
            res: "fun_igt_underscore (sizenn (numtype_Inn Inn_I64)) x (mk_uN i) (mk_uN i') res"
            using fun_igt_underscore_total[OF 2 1]
            sizenn.domintros sizenn.psimps
            by fastforce
          show ?case using GT(21)[OF res]
            using GT.prems(7,8,9) by auto
        next
          case (LE x)
          have 1: "0 \<le> i' \<and> i' \<le> 2 ^ 64 - 1" using LE size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          have 2: "0 \<le> i \<and> i \<le> 2 ^ 64 - 1" using LE size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          obtain res where 
            res: "fun_ile_underscore (sizenn (numtype_Inn Inn_I64)) x (mk_uN i) (mk_uN i') res"
            using fun_ile_underscore_total[OF 2 1]
            sizenn.domintros sizenn.psimps
            by fastforce
          show ?case using LE(23)[OF res]
            using LE.prems(7,8,9) by auto
        next
          case (GE x)
          have 1: "0 \<le> i' \<and> i' \<le> 2 ^ 64 - 1" using GE size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          have 2: "0 \<le> i \<and> i \<le> 2 ^ 64 - 1" using GE size.domintros size.psimps 
            valtype_Inn.domintros valtype_Inn.psimps 
            by simp
          obtain res where 
            res: "fun_ige_underscore (sizenn (numtype_Inn Inn_I64)) x (mk_uN i) (mk_uN i') res"
            using fun_ige_underscore_total[OF 2 1]
            sizenn.domintros sizenn.psimps
            by fastforce
          show ?case using GE(25)[OF res]
            using GE.prems(7,8,9) by auto
        qed(metis)+
      qed
    next
      case (relop__case_1 v_numtype v_Inn'' var_x')
      then show ?case using Inn_Fnn_diff by simp
    qed qed
  next
      case (num__case_1 v_Fnn var_y v_numtype)
      then show ?case using Inn_Fnn_diff by simp
    qed qed qed
  next
    case (num__case_1 v_Fnn var_x v_numtype)
    show ?case using num__case_1
    proof(induction "sizenn (numtype_Fnn v_Fnn)" var_x)
      case (fN_case_0 i)
    show ?case using fN_case_0(3,1-2,4-)
    proof(induction "val_CONST v_numtype c2")
      case val_case_0
      then show ?case proof(induction v_numtype c2)
        case (num__case_0 v_Inn' var_y v_numtype)
        then show ?case using Inn_Fnn_diff by blast
      next
        case (num__case_1 v_Fnn' var_y v_numtype)
        then have eqv: "v_Fnn = v_Fnn'"
          by (metis (full_types) Fnn.exhaust fun_zero.domintros(3,4) fun_zero.psimps(3,4)
              num_underscore.distinct(1) numtype.distinct(11) wf_num_underscore.simps zero_is_wf)
        show ?case using num__case_1 eqv 
        proof(induction "sizenn (numtype_Fnn v_Fnn')" var_y)
          case (fN_case_0 i')
        show ?case using fN_case_0(5,1-4,6-)
    proof(induction v_numtype op)
      case (relop__case_0 v_numtype v_Inn'' var_x')
      then show ?case using Inn_Fnn_diff by blast
    next
      case (relop__case_1 v_numtype v_Fnn'' var_x')
      then have eqv: "v_Fnn = v_Fnn''"
        by (metis Fnn.exhaust numtype.distinct(11) numtype_Fnn.domintros(1,2) numtype_Fnn.psimps(1,2))
      show ?case using relop__case_1 eqv proof(induction v_Fnn)
        case Fnn_F32
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps fun_relop_underscore.intros
        proof(induction var_x')
        qed(metis)+
      next
        case Fnn_F64
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps fun_relop_underscore.intros
        proof(induction var_x')
        qed(metis)+
      qed 
    qed
  next
    case (fN_case_1 i')
    show ?case using fN_case_1(5,1-4,6-)
    proof(induction v_numtype op)
      case (relop__case_0 v_numtype v_Inn'' var_x')
      then show ?case using Inn_Fnn_diff by blast
    next
      case (relop__case_1 v_numtype v_Fnn'' var_x')
      then have eqv: "v_Fnn = v_Fnn''"
        by (metis Fnn.exhaust numtype.distinct(11) numtype_Fnn.domintros(1,2) numtype_Fnn.psimps(1,2))
      show ?case using relop__case_1 eqv proof(induction v_Fnn)
        case Fnn_F32
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps fun_relop_underscore.intros
        proof(induction var_x') qed(metis)+
      next
        case Fnn_F64
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps fun_relop_underscore.intros
        proof(induction var_x')
        qed(metis)+
      qed 
    qed
  qed
qed
qed
next
case (fN_case_1 i)
    show ?case using fN_case_1(3,1-2,4-)
    proof(induction "val_CONST v_numtype c2")
      case val_case_0
      then show ?case proof(induction v_numtype c2)
        case (num__case_0 v_Inn' var_y v_numtype)
        then show ?case using Inn_Fnn_diff by blast
      next
        case (num__case_1 v_Fnn' var_y v_numtype)
        then have eqv: "v_Fnn = v_Fnn'"
          by (metis (full_types) Fnn.exhaust fun_zero.domintros(3,4) fun_zero.psimps(3,4)
              num_underscore.distinct(1) numtype.distinct(11) wf_num_underscore.simps zero_is_wf)
        show ?case using num__case_1 eqv 
        proof(induction "sizenn (numtype_Fnn v_Fnn')" var_y)
          case (fN_case_0 i')
        show ?case using fN_case_0(5,1-4,6-)
    proof(induction v_numtype op)
      case (relop__case_0 v_numtype v_Inn'' var_x')
      then show ?case using Inn_Fnn_diff by blast
    next
      case (relop__case_1 v_numtype v_Fnn'' var_x')
      then have eqv: "v_Fnn = v_Fnn''"
        by (metis Fnn.exhaust numtype.distinct(11) numtype_Fnn.domintros(1,2) numtype_Fnn.psimps(1,2))
      show ?case using relop__case_1 eqv proof(induction v_Fnn)
        case Fnn_F32
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps fun_relop_underscore.intros
        proof(induction var_x')
        qed(metis)+
      next
        case Fnn_F64
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps fun_relop_underscore.intros
        proof(induction var_x')
        qed(metis)+
      qed 
    qed
  next
    case (fN_case_1 i')
    show ?case using fN_case_1(5,1-4,6-)
    proof(induction v_numtype op)
      case (relop__case_0 v_numtype v_Inn'' var_x')
      then show ?case using Inn_Fnn_diff by blast
    next
      case (relop__case_1 v_numtype v_Fnn'' var_x')
      then have eqv: "v_Fnn = v_Fnn''"
        by (metis Fnn.exhaust numtype.distinct(11) numtype_Fnn.domintros(1,2) numtype_Fnn.psimps(1,2))
      show ?case using relop__case_1 eqv proof(induction v_Fnn)
        case Fnn_F32
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps fun_relop_underscore.intros
        proof(induction var_x')
        qed(metis)+
      next
        case Fnn_F64
        then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps fun_relop_underscore.intros
        proof(induction var_x')
        qed(metis)+
      qed 
    qed
  qed
qed
qed qed qed qed

lemma valtype_sub_reftype:
  assumes "Valtype_sub t (valtype_reftype rt)" 
  shows "t = BOT \<or> t = valtype_reftype rt" 
  using assms proof(induction t "valtype_reftype rt")
qed(auto)

lemma reducible_left_v:
  assumes "Ex (Step (mk_config (mk_state s f) es))" 
    "wf_config (mk_config (mk_state s f) es)" "Store_ok s"  
  shows "Ex (Step (mk_config (mk_state s f) (map admininstr_val vs @ 
              es)))"
proof (cases vs)
  case Nil
  then show ?thesis using assms by auto
next
  case (Cons a list)
  then obtain c' where step: "Step (mk_config (mk_state s f) es) c'" using assms
    by auto
  then show ?thesis proof(cases c')
    case (mk_config x1 x2)
    then have "wf_config c'" using assms Step_is_wf step 
      by fast
    then show ?thesis 
    using assms ctxt_instrs[of "mk_state s f" es x1 x2 vs "[]"] mk_config step Cons
    by fastforce 
qed qed

lemma reducible_right: 
  assumes "Ex (Step (mk_config (mk_state s f) es1))" 
    "wf_config (mk_config (mk_state s f) es1)" "list_all wf_admininstr es2" "Store_ok s"  
  shows "Ex (Step (mk_config (mk_state s f) (es1 @ es2)))" 
proof(cases es2)
  case Nil
  then show ?thesis using assms by simp
next
  case (Cons a list)
  obtain c' where step: "Step (mk_config (mk_state s f) es1) c'" using assms by blast
  then show ?thesis proof(cases c')
    case (mk_config x1 x2)
    then have "wf_config (mk_config x1 x2)" using Step_is_wf step assms 
      by blast
    then show ?thesis using Step_is_wf assms step mk_config Cons 
        ctxt_instrs[of "mk_state s f" es1 x1 x2 "[]" es2]
      by auto
  qed
qed

lemma Resulttype_sub_length: assumes "Resulttype_sub (mk_list l1) (mk_list l2)" 
  shows "length l1 = length l2" using assms
  by (simp add: Resulttype_sub.simps)


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

lemma length_list_slice:
  assumes "i + j \<le> length bs" 
  shows "length (list_slice bs i j) = j" 
  using assms proof(induction bs arbitrary: i j)
  case Nil
  then show ?case by auto
next
  case (Cons a bs)
  then show ?case proof(induction i arbitrary:j)
    case 0
    then show ?case proof(induction j)
    qed(auto)
  next
    case (Suc i)
    then show ?case proof(induction j) qed(auto)
  qed
qed

lemma list_all_list_slice:
  assumes "list_all P l"
  shows "list_all P (list_slice l i j)"
  using assms proof(induction l arbitrary: i j)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case proof(induction i arbitrary:j)
    case 0
    then show ?case proof(induction j) qed(auto)
  next
    case (Suc i)
    then show ?case proof(induction j) qed(auto)
  qed
qed


lemma local_list_is_local_list: shows "\<exists> tlocs. l = map LOCAL tlocs" 
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case proof(cases a)
    case (LOCAL x)
    then show ?thesis using Cons
      by (metis LOCAL list.simps(9))
  qed
qed


lemma typeofval_is_nt: assumes "Valtype_sub (typeofval v) (valtype_numtype nt)" 
  shows "\<exists> c. v = val_CONST nt c"
  using assms proof(induction "typeofval v" "valtype_numtype nt")
  case refl
  then show ?case proof(cases v)
  case (val_CONST x11 x12)
  then show ?thesis using assms typeofval.psimps typeofval.domintros valtype_numtype.domintros 
      valtype_numtype.psimps refl
    by (metis (full_types) lanetype_numtype.cases valtype.distinct(1,15,17,27,3,5))
next
  case (val_VCONST x21 x22)
  then show ?thesis proof(cases x21)
    case V128
    then show ?thesis using val_VCONST assms typeofval.psimps typeofval.domintros 
      valtype_vectype.domintros valtype_vectype.psimps refl
      by (metis valtype.distinct(19,29,37,7) valtype_numtype.elims)
  qed
next
  case (val_REF_NULL x3)
  then show ?thesis using assms typeofval.psimps typeofval.domintros valtype_reftype.domintros
    valtype_reftype.psimps refl
    by (metis valtype.distinct(11,21,23,31,33,39,41,9) valtype_numtype.elims[of nt valtype_FUNCREF]
        valtype_numtype.elims[of nt "typeofval (val_REF_HOST_ADDR undefined)"]
        valtype_reftype.cases[of x3]) 
next
  case (val_REF_FUNC_ADDR x4)
  then show ?thesis using assms refl typeofval.psimps typeofval.domintros
    by (metis valtype.distinct(21,31,39,9) valtype_numtype.elims) 
next
  case (val_REF_HOST_ADDR x5)
  then show ?thesis using assms refl typeofval.psimps typeofval.domintros
    by (metis valtype.distinct(11,23,33,41) valtype_numtype.elims)
qed
next
  case bot
  then show ?case proof(induction v)
    case (val_CONST x1 x2)
    then show ?case using typeofval.domintros typeofval.psimps
      by (metis lanetype_numtype.cases valtype.distinct(13,25,35,43) valtype_numtype.simps(1,2,3,4))
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

lemma typeofval_is_v128: assumes "Valtype_sub (typeofval v) valtype_V128" 
  shows "\<exists> c. v = val_VCONST V128 c"
  using assms proof(induction "typeofval v" valtype_V128)
  case refl
  then show ?case proof(cases v)
  case (val_CONST x11 x12)
  then show ?thesis using refl typeofval.domintros typeofval.psimps valtype_numtype.domintros
      valtype_numtype.psimps proof(induction x11) qed(auto)
next
  case (val_VCONST x21 x22)
  then show ?thesis proof(cases x21) qed(auto)
next
  case (val_REF_NULL x3)
  then show ?thesis using assms typeofval.psimps typeofval.domintros valtype_reftype.domintros
    valtype_reftype.psimps refl
    by (metis valtype.distinct(45,47) valtype_reftype.cases)
next
  case (val_REF_FUNC_ADDR x4)
  then show ?thesis using assms refl typeofval.psimps typeofval.domintros
    by simp
next
  case (val_REF_HOST_ADDR x5)
  then show ?thesis using assms refl typeofval.psimps typeofval.domintros
    by simp
qed
next
  case bot
  then show ?case proof(induction v)
    case (val_CONST x1 x2)
    then show ?case using typeofval.domintros typeofval.psimps
      by (metis lanetype_numtype.cases valtype.distinct(13,25,35,43) valtype_numtype.simps(1,2,3,4))
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


lemma typeofval_is_i32: assumes "Valtype_sub (typeofval v) valtype_I32" 
  shows "\<exists> c. v = val_CONST I32 c"
  using assms typeofval_is_nt[of v I32] valtype_numtype.domintros valtype_numtype.psimps by auto


lemma typeofval_is_rt: assumes "Valtype_sub (typeofval v) (valtype_reftype rt)" 
  shows "\<exists> ref. v = val_ref ref"
  using assms proof(induction "typeofval v" "valtype_reftype rt")
  case refl
  then show ?case proof(cases v)
  case (val_CONST x11 x12)
  then show ?thesis using assms typeofval.psimps typeofval.domintros valtype_numtype.domintros 
      valtype_numtype.psimps refl 
    by (metis val_CONST typeofval_is_nt val.distinct(3))
next
  case (val_VCONST x21 x22)
  then show ?thesis proof(cases x21)
    case V128
    then show ?thesis using val_VCONST assms typeofval.psimps typeofval.domintros 
      valtype_vectype.domintros valtype_vectype.psimps refl
      by (metis valtype.distinct(45,47) valtype_reftype.cases valtype_reftype.domintros(1,2)
          valtype_reftype.psimps(1,2))
  qed
next
  case (val_REF_NULL x3)
  then show ?thesis using val_ref.domintros val_ref.psimps(1)[of x3] 
    by metis
next
  case (val_REF_FUNC_ADDR x4)
  then show ?thesis using val_ref.domintros val_ref.psimps(2)[of x4] by metis 
next
  case (val_REF_HOST_ADDR x5)
  then show ?thesis using val_ref.domintros val_ref.psimps(3)[of x5] by metis
qed
next
  case bot
  then show ?case proof(induction v)
    case (val_CONST x1 x2)
    then show ?case using typeofval.domintros typeofval.psimps
      by (metis lanetype_numtype.cases valtype.distinct(13,25,35,43) valtype_numtype.simps(1,2,3,4))
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


lemma list_alli_aux_forall:
  assumes "\<forall> k. k < length l \<longrightarrow> P (n + k) (l ! k)"
  shows "list_alli_aux P n l" 
  using assms proof(induction l arbitrary:n)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then have Pna: "P n a"
    by auto
  have "list_alli_aux P (Suc n) l" using Cons
    by force
  then show ?case using Pna by simp
qed


lemma list_alli_forall:
  assumes "\<forall> k. k < length l \<longrightarrow> P k (l ! k)" 
  shows "list_alli P l"
  using assms list_alli_aux_forall[of l P 0] list_alli_def[of P l]
  by simp

lemma packnum_not_None:
  assumes "wf_num_underscore (unpack lt) c" 
  shows "packnum_underscore lt c \<noteq> None" 
  using assms packnum_underscore.psimps packnum_underscore.domintros
   numtype_Inn.domintros numtype_Inn.psimps 
numtype_Fnn.domintros numtype_Fnn.psimps
unpack.domintros unpack.psimps lanetype_packtype.domintros
   lanetype_packtype.psimps valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps 
proof(induction "unpack lt" c)
  case (num__case_0 v_Inn var_x)
  then show ?case
  proof(induction v_Inn)
    case Inn_I32
    then show ?case proof(induction lt)
    qed(auto)
  next
    case Inn_I64
    then show ?case proof(induction lt) qed(auto)
  qed
next
  case (num__case_1 v_Fnn var_x)
  then show ?case proof(induction v_Fnn)
    case Fnn_F32
    then show ?case proof(induction lt) qed(auto)
  next
    case Fnn_F64
    then show ?case proof(induction lt) qed(auto)
  qed
qed

lemma fun_cvtop_underscore_total:
  assumes "wf_val (val_CONST nt_1 c)" "wf_cvtop__underscore nt_1 nt_2 op"
  shows "\<exists> res. fun_cvtop__underscore nt_1 nt_2 op c (Some res)"
proof -
  note numtype_size_simps[simp]
  have wf: "wf_num_underscore nt_1 c" using assms(1) wf_val.simps by auto
  have inn_c: "\<exists>v. c = mk_num__0 inn v" if "nt_1 = numtype_Inn inn" for inn
    using wf
  proof cases
    case (num__case_0 inn' v)
    then show ?thesis using that Inn_inj by metis
  next
    case (num__case_1 fnn v)
    then show ?thesis using that Inn_Fnn_diff by metis
  qed
  have fnn_c: "\<exists>v. c = mk_num__1 fnn v" if "nt_1 = numtype_Fnn fnn" for fnn
    using wf
  proof cases
    case (num__case_0 inn v)
    then show ?thesis using that Inn_Fnn_diff by metis
  next
    case (num__case_1 fnn' v)
    then show ?thesis using that Fnn_inj by metis
  qed
  from assms(2) show ?thesis
  proof cases
    case (cvtop___case_0 inn_1 inn_2 x)
    then obtain v where "c = mk_num__0 inn_1 v" using inn_c by blast
    then show ?thesis using cvtop___case_0
      by (cases inn_1; cases inn_2; cases x) (auto intro!: exI fun_cvtop__underscore.intros)
  next
    case (cvtop___case_1 inn_1 fnn_2 x)
    then obtain v where "c = mk_num__0 inn_1 v" using inn_c by blast
    then show ?thesis using cvtop___case_1
      by (cases inn_1; cases fnn_2; cases x)
        (auto elim!: wf_cvtop__Inn_1_Fnn_2.cases intro!: exI fun_cvtop__underscore.intros)
  next
    case (cvtop___case_2 fnn_1 inn_2 x)
    then obtain v where "c = mk_num__1 fnn_1 v" using fnn_c by blast
    then show ?thesis using cvtop___case_2
      by (cases fnn_1; cases inn_2; cases x)
        (auto elim!: wf_cvtop__Fnn_1_Inn_2.cases intro!: exI fun_cvtop__underscore.intros)
  next
    case (cvtop___case_3 fnn_1 fnn_2 x)
    then obtain v where "c = mk_num__1 fnn_1 v" using fnn_c by blast
    then show ?thesis using cvtop___case_3
      by (cases fnn_1; cases fnn_2; cases x) (auto intro!: exI fun_cvtop__underscore.intros)
  qed
qed


(* Totality of the SIMD (V128) semantic relations on well-formed inputs, used by the
   vector cases of the progress theorem.  The generated relations are partial functions
   with a fall-through `None` case; the lemmas here show that well-formed shapes,
   operators and vectors always hit one of the `Some` cases. *)

section \<open>Simplification facts\<close>

lemma vt_simps:
  "lanetype_Jnn Jnn_I32 = lanetype_I32" "lanetype_Jnn Jnn_I64 = lanetype_I64"
  "lanetype_Jnn Jnn_I8 = lanetype_I8" "lanetype_Jnn Jnn_I16 = lanetype_I16"
  "lanetype_Fnn Fnn_F32 = lanetype_F32" "lanetype_Fnn Fnn_F64 = lanetype_F64"
  "lanetype_Inn Inn_I32 = lanetype_I32" "lanetype_Inn Inn_I64 = lanetype_I64"
  "lanetype_packtype I8 = lanetype_I8" "lanetype_packtype I16 = lanetype_I16"
  "lanetype_numtype I32 = lanetype_I32" "lanetype_numtype I64 = lanetype_I64"
  "lanetype_numtype F32 = lanetype_F32" "lanetype_numtype F64 = lanetype_F64"
  "Jnn_packtype I8 = Jnn_I8" "Jnn_packtype I16 = Jnn_I16"
  "Jnn_Inn Inn_I32 = Jnn_I32" "Jnn_Inn Inn_I64 = Jnn_I64"
  "numtype_Fnn Fnn_F32 = F32" "numtype_Fnn Fnn_F64 = F64"
  "valtype_Inn Inn_I32 = valtype_I32" "valtype_Inn Inn_I64 = valtype_I64"
  "valtype_Fnn Fnn_F32 = valtype_F32" "valtype_Fnn Fnn_F64 = valtype_F64"
  "valtype_vectype V128 = valtype_V128"
  "sizenn I32 = 32" "sizenn I64 = 64" "sizenn F32 = 32" "sizenn F64 = 64"
  "sizenn1 I32 = 32" "sizenn1 I64 = 64" "sizenn1 F32 = 32" "sizenn1 F64 = 64"
  "sizenn2 I32 = 32" "sizenn2 I64 = 64" "sizenn2 F32 = 32" "sizenn2 F64 = 64"
  "lsize lanetype_I32 = 32" "lsize lanetype_I64 = 64" "lsize lanetype_F32 = 32"
  "lsize lanetype_F64 = 64" "lsize lanetype_I8 = 8" "lsize lanetype_I16 = 16"
  "psize I8 = 8" "psize I16 = 16"
  "isize Inn_I32 = 32" "isize Inn_I64 = 64"
  "unpack lanetype_I32 = I32" "unpack lanetype_I64 = I64" "unpack lanetype_F32 = F32"
  "unpack lanetype_F64 = F64" "unpack lanetype_I8 = I32" "unpack lanetype_I16 = I32"
  by (simp_all add: lanetype_Jnn.psimps lanetype_Jnn.domintros lanetype_Fnn.psimps
      lanetype_Fnn.domintros lanetype_Inn.psimps lanetype_Inn.domintros
      lanetype_packtype.psimps lanetype_packtype.domintros lanetype_numtype.psimps
      lanetype_numtype.domintros Jnn_packtype.psimps Jnn_packtype.domintros
      Jnn_Inn.psimps Jnn_Inn.domintros numtype_Inn.psimps numtype_Inn.domintros
      numtype_Fnn.psimps numtype_Fnn.domintros valtype_Inn.psimps valtype_Inn.domintros
      valtype_Fnn.psimps valtype_Fnn.domintros valtype_vectype.psimps valtype_vectype.domintros
      size.psimps size.domintros sizenn.psimps sizenn.domintros sizenn1.psimps
      sizenn1.domintros sizenn2.psimps sizenn2.domintros valtype_numtype.psimps
      valtype_numtype.domintros lsize.psimps lsize.domintros psize.psimps psize.domintros
      isize.psimps isize.domintros unpack.psimps unpack.domintros)

lemma vt_generic_simps:
  "lsizenn lt = lsize lt" "lsizenn1 lt = lsize lt" "lsizenn2 lt = lsize lt"
  "fun_lanetype (X lt (mk_dim n)) = lt" "fun_dim (X lt (mk_dim n)) = mk_dim n"
  "proj_dim_0 (mk_dim n) = n" "proj_ishape_0 (mk_ishape sh) = sh"
  "shunpack (X lt (mk_dim n)) = unpack lt"
  "proj_lane__0 (mk_lane__0 j x) = Some x" "proj_lane__0 (mk_lane__1 f y) = None"
  "proj_lane__1 (mk_lane__1 f y) = Some y" "proj_lane__1 (mk_lane__0 j x) = None"
  "proj_num__0 (mk_num__0 inn u) = Some u"
  "res_bool True = 1" "res_bool False = 0"
  "list_underscore None = []" "list_underscore (Some w) = [w]"
  by (simp_all add: lsizenn.psimps lsizenn.domintros lsizenn1.psimps lsizenn1.domintros
      lsizenn2.psimps lsizenn2.domintros fun_lanetype.psimps fun_lanetype.domintros
      fun_dim.psimps fun_dim.domintros proj_dim_0.psimps proj_dim_0.domintros
      proj_ishape_0.psimps proj_ishape_0.domintros shunpack.psimps shunpack.domintros
      proj_uN_0.psimps proj_uN_0.domintros proj_lane__0.psimps proj_lane__0.domintros
      proj_lane__1.psimps proj_lane__1.domintros proj_num__0.psimps proj_num__0.domintros
      res_bool.psimps res_bool.domintros list_underscore.psimps list_underscore.domintros)

lemmas vt_all_simps = vt_simps vt_generic_simps

lemma lanetype_Jnn_inj: "lanetype_Jnn a = lanetype_Jnn b \<Longrightarrow> a = b"
  by (cases a; cases b) (simp_all add: vt_simps)

lemma lanetype_Fnn_inj: "lanetype_Fnn a = lanetype_Fnn b \<Longrightarrow> a = b"
  by (cases a; cases b) (simp_all add: vt_simps)

lemma lanetype_Jnn_Fnn_diff: "lanetype_Jnn a \<noteq> lanetype_Fnn b"
  by (cases a; cases b) (simp_all add: vt_simps)

lemma wf_V128_val: "wf_val (val_VCONST V128 c) \<Longrightarrow> wf_uN 128 c"
  by (auto elim: wf_val.cases simp: vt_simps)

section \<open>Lanes of a well-formed vector\<close>

lemma map_decomp:
  assumes "\<forall>l\<in>set L. \<exists>x. l = f x \<and> P x"
  shows "\<exists>xs. L = map f xs \<and> (\<forall>x\<in>set xs. P x)"
  using assms
proof (induction L)
  case Nil
  then show ?case by simp
next
  case (Cons a L)
  then obtain x xs where "a = f x" "P x" "L = map f xs" "\<forall>x\<in>set xs. P x" by auto
  then show ?case by (intro exI[of _ "x # xs"]) simp
qed

lemma lanes_Jnn:
  assumes "wf_shape (X (lanetype_Jnn J) (mk_dim M))" "wf_uN 128 v"
  shows "\<exists>xs. lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) v = map (mk_lane__0 J) xs
    \<and> (\<forall>x\<in>set xs. wf_uN (lsize (lanetype_Jnn J)) x) \<and> length xs = M"
proof -
  let ?L = "lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) v"
  have wf: "\<forall>l\<in>set ?L. wf_lane_underscore (lanetype_Jnn J) l"
    using lanes__is_wf[OF assms HOL.refl] by (simp add: list_all_iff vt_generic_simps)
  have "\<forall>l\<in>set ?L. \<exists>x. l = mk_lane__0 J x \<and> wf_uN (lsize (lanetype_Jnn J)) x"
  proof
    fix l assume "l \<in> set ?L"
    then have "wf_lane_underscore (lanetype_Jnn J) l" using wf by blast
    then show "\<exists>x. l = mk_lane__0 J x \<and> wf_uN (lsize (lanetype_Jnn J)) x"
    proof cases
      case (lane__case_0 J' x)
      then show ?thesis using lanetype_Jnn_inj by metis
    next
      case (lane__case_1 F y)
      then show ?thesis using lanetype_Jnn_Fnn_diff by metis
    qed
  qed
  then obtain xs where xs: "?L = map (mk_lane__0 J) xs" "\<forall>x\<in>set xs. wf_uN (lsize (lanetype_Jnn J)) x"
    using map_decomp[where f = "mk_lane__0 J"] by blast
  moreover have "length xs = M"
    using xs(1) length_lanes[of "lanetype_Jnn J" M v] by simp
  ultimately show ?thesis by blast
qed

lemma lanes_Fnn:
  assumes "wf_shape (X (lanetype_Fnn F) (mk_dim M))" "wf_uN 128 v"
  shows "\<exists>xs. lanes_underscore (X (lanetype_Fnn F) (mk_dim M)) v = map (mk_lane__1 F) xs
    \<and> (\<forall>x\<in>set xs. wf_fN (sizenn (numtype_Fnn F)) x) \<and> length xs = M"
proof -
  let ?L = "lanes_underscore (X (lanetype_Fnn F) (mk_dim M)) v"
  have wf: "\<forall>l\<in>set ?L. wf_lane_underscore (lanetype_Fnn F) l"
    using lanes__is_wf[OF assms HOL.refl] by (simp add: list_all_iff vt_generic_simps)
  have "\<forall>l\<in>set ?L. \<exists>x. l = mk_lane__1 F x \<and> wf_fN (sizenn (numtype_Fnn F)) x"
  proof
    fix l assume "l \<in> set ?L"
    then have "wf_lane_underscore (lanetype_Fnn F) l" using wf by blast
    then show "\<exists>x. l = mk_lane__1 F x \<and> wf_fN (sizenn (numtype_Fnn F)) x"
    proof cases
      case (lane__case_0 J x)
      then show ?thesis using lanetype_Jnn_Fnn_diff by metis
    next
      case (lane__case_1 F' y)
      then show ?thesis using lanetype_Fnn_inj by metis
    qed
  qed
  then obtain xs where xs: "?L = map (mk_lane__1 F) xs" "\<forall>x\<in>set xs. wf_fN (sizenn (numtype_Fnn F)) x"
    using map_decomp[where f = "mk_lane__1 F"] by blast
  moreover have "length xs = M"
    using xs(1) length_lanes[of "lanetype_Fnn F" M v] by simp
  ultimately show ?thesis by blast
qed

section \<open>List construction lemmas\<close>

lemma length_list_zipWith: "length (list_zipWith f A B) = Orderings.min (length A) (length B)"
  by (simp add: list_zipWith_def)

lemma list_all2_mapI:
  assumes "\<And>a. a \<in> set A \<Longrightarrow> P (f a) a"
  shows "list_all2 P (map f A) A"
  using assms by (induction A) auto

lemma list_all_mapI:
  assumes "\<And>a. a \<in> set A \<Longrightarrow> P (f a)"
  shows "list_all P (map f A)"
  using assms by (induction A) auto

lemma vt_list_allI:
  assumes "\<And>a. a \<in> set A \<Longrightarrow> P a"
  shows "list_all P A"
  using assms by (simp add: list_all_iff)

lemma list_all2_setI:
  assumes "length A = length B" "\<And>a b. a \<in> set A \<Longrightarrow> b \<in> set B \<Longrightarrow> P a b"
  shows "list_all2 P A B"
  using assms
proof (induction A arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  then show ?case by (cases B) auto
qed

lemma list_all3_zipWithI:
  assumes "length A = length B" "\<And>a b. a \<in> set A \<Longrightarrow> b \<in> set B \<Longrightarrow> P (f a b) a b"
  shows "list_all3 P (list_zipWith f A B) A B"
  using assms
proof (induction A arbitrary: B)
  case Nil
  then show ?case by (simp add: list_zipWith_def list_all3.intros(1))
next
  case (Cons a A)
  then obtain b B' where "B = b # B'" by (cases B) auto
  then show ?case using Cons
    by (auto simp: list_zipWith_def intro!: list_all3.intros(2))
qed

lemma set_list_zipWithD: "a \<in> set (list_zipWith f A B) \<Longrightarrow> \<exists>x\<in>set A. \<exists>y\<in>set B. a = f x y"
  by (auto simp: list_zipWith_def dest: set_zip_leftD set_zip_rightD)

lemma list_all_zipWithI:
  assumes "\<And>a b. a \<in> set A \<Longrightarrow> b \<in> set B \<Longrightarrow> P (f a b)"
  shows "list_all P (list_zipWith f A B)"
  using assms by (auto simp: list_zipWith_def list_all_iff dest: set_zip_leftD set_zip_rightD)

section \<open>Integer lane operations\<close>

lemma wf_uN_bound: "wf_uN n x \<Longrightarrow> 0 \<le> proj_uN_0 x \<and> proj_uN_0 x \<le> 2 ^ n - 1"
  by (auto elim: wf_uN.cases simp: vt_generic_simps)

lemma vt_signed_ex: "wf_uN n x \<Longrightarrow> \<exists>r. fun_signed_underscore n (proj_uN_0 x) r"
  using fun_signed_underscore_total wf_uN_bound by blast

lemma vt_inv_signed_ex: "c \<le> 2 ^ (n - 1) - 1 \<Longrightarrow> \<exists>r. fun_inv_signed_underscore n c r"
  using fun_inv_signed_underscore_total by fastforce

lemma sat_s_bound: "sat_s_underscore n i \<le> 2 ^ (n - 1) - 1"
  by (simp add: sat_s_underscore.psimps sat_s_underscore.domintros)

lemma res_bool_le1: "res_bool b \<le> Suc 0"
  by (cases b) (simp_all add: vt_generic_simps)

lemma iabs_ex: "wf_uN n x \<Longrightarrow> \<exists>r. fun_iabs_underscore n x r"
  using vt_signed_ex fun_iabs_underscore.intros by blast

lemma iminmax_ex:
  assumes "wf_uN n x" "wf_uN n y"
  shows "\<exists>r. fun_imin_underscore n sx x y r" "\<exists>r. fun_imax_underscore n sx x y r"
proof -
  obtain a b where "fun_signed_underscore n (proj_uN_0 y) b" "fun_signed_underscore n (proj_uN_0 x) a"
    using vt_signed_ex assms by blast
  then show "\<exists>r. fun_imin_underscore n sx x y r" "\<exists>r. fun_imax_underscore n sx x y r"
    by (cases sx; metis not_le fun_imin_underscore.intros fun_imax_underscore.intros)+
qed

lemma isat_ex:
  assumes "wf_uN n x" "wf_uN n y"
  shows "\<exists>r. fun_iadd_sat_underscore n sx x y r" "\<exists>r. fun_isub_sat_underscore n sx x y r"
proof -
  obtain a b where ab: "fun_signed_underscore n (proj_uN_0 y) b" "fun_signed_underscore n (proj_uN_0 x) a"
    using vt_signed_ex assms by blast
  obtain r1 r2 where "fun_inv_signed_underscore n (sat_s_underscore n (a + b)) r1"
      "fun_inv_signed_underscore n (sat_s_underscore n (a - b)) r2"
    using vt_inv_signed_ex[OF sat_s_bound] by blast
  then show "\<exists>r. fun_iadd_sat_underscore n sx x y r" "\<exists>r. fun_isub_sat_underscore n sx x y r"
    using ab by (cases sx; blast intro: fun_iadd_sat_underscore.intros fun_isub_sat_underscore.intros)+
qed

lemmas imin_ex = iminmax_ex(1) and imax_ex = iminmax_ex(2)
  and iadd_sat_ex = isat_ex(1) and isub_sat_ex = isat_ex(2)

lemma icmp_ex:
  assumes "wf_uN n x" "wf_uN n y"
  shows "\<exists>r. fun_ilt_underscore n sx x y r" "\<exists>r. fun_igt_underscore n sx x y r"
    "\<exists>r. fun_ile_underscore n sx x y r" "\<exists>r. fun_ige_underscore n sx x y r"
proof -
  obtain a b where "fun_signed_underscore n (proj_uN_0 y) b" "fun_signed_underscore n (proj_uN_0 x) a"
    using vt_signed_ex assms by blast
  then show "\<exists>r. fun_ilt_underscore n sx x y r" "\<exists>r. fun_igt_underscore n sx x y r"
    "\<exists>r. fun_ile_underscore n sx x y r" "\<exists>r. fun_ige_underscore n sx x y r"
    by (cases sx; blast intro: fun_ilt_underscore.intros fun_igt_underscore.intros
        fun_ile_underscore.intros fun_ige_underscore.intros)+
qed

lemmas ilt_ex = icmp_ex(1) and igt_ex = icmp_ex(2) and ile_ex = icmp_ex(3) and ige_ex = icmp_ex(4)

(* "SOME" forms: the chosen result is related to the inputs and is well-formed.  They have
   specific conclusions so they can be used as intro rules in the case proofs below. *)

lemmas iabs_some = someI_ex[OF iabs_ex]
lemma iabs_some_wf: "wf_uN n x \<Longrightarrow> wf_uN n (SOME r. fun_iabs_underscore n x r)"
  using iabs__is_wf[OF iabs_some _ HOL.refl] by blast

lemmas imin_some = someI_ex[OF imin_ex]
lemma imin_some_wf: "wf_uN n x \<Longrightarrow> wf_uN n y \<Longrightarrow> wf_uN n (SOME r. fun_imin_underscore n sx x y r)"
  using imin__is_wf[OF imin_some _ _ HOL.refl] by blast

lemmas imax_some = someI_ex[OF imax_ex]
lemma imax_some_wf: "wf_uN n x \<Longrightarrow> wf_uN n y \<Longrightarrow> wf_uN n (SOME r. fun_imax_underscore n sx x y r)"
  using imax__is_wf[OF imax_some _ _ HOL.refl] by blast

lemmas iadd_sat_some = someI_ex[OF iadd_sat_ex]
lemma iadd_sat_some_wf: "wf_uN n x \<Longrightarrow> wf_uN n y \<Longrightarrow> wf_uN n (SOME r. fun_iadd_sat_underscore n sx x y r)"
  using iadd_sat__is_wf[OF iadd_sat_some _ _ HOL.refl] by blast

lemmas isub_sat_some = someI_ex[OF isub_sat_ex]
lemma isub_sat_some_wf: "wf_uN n x \<Longrightarrow> wf_uN n y \<Longrightarrow> wf_uN n (SOME r. fun_isub_sat_underscore n sx x y r)"
  using isub_sat__is_wf[OF isub_sat_some _ _ HOL.refl] by blast

lemmas ilt_some = someI_ex[OF ilt_ex]
lemmas igt_some = someI_ex[OF igt_ex]
lemmas ile_some = someI_ex[OF ile_ex]
lemmas ige_some = someI_ex[OF ige_ex]

(* Comparison results are booleans, so they fit in a single bit.  In this context `1` is
   simplified to `Suc 0`, so the bit lemmas are stated with `Suc 0`; `mk_uN (proj_uN_0 u)`
   simplifies to `u` (mk_uN_proj), so they are stated on `u` directly. *)
lemma mk_uN_proj: "mk_uN (proj_uN_0 u) = u"
  by (cases u) (simp add: vt_generic_simps)

lemma wf_uN_1I: "proj_uN_0 u \<le> 1 \<Longrightarrow> wf_uN (Suc 0) u"
  by (cases u) (auto simp: vt_generic_simps intro!: wf_uN.intros)

lemma icmp_bit:
  "fun_ilt_underscore n sx x y r \<Longrightarrow> wf_uN (Suc 0) r"
  "fun_igt_underscore n sx x y r \<Longrightarrow> wf_uN (Suc 0) r"
  "fun_ile_underscore n sx x y r \<Longrightarrow> wf_uN (Suc 0) r"
  "fun_ige_underscore n sx x y r \<Longrightarrow> wf_uN (Suc 0) r"
  by (auto elim!: fun_ilt_underscore.cases fun_igt_underscore.cases fun_ile_underscore.cases
      fun_ige_underscore.cases intro!: wf_uN_1I simp: vt_generic_simps res_bool_le1)

lemma ieq_bit: "wf_uN (Suc 0) (ieq_underscore n x y)"
  by (rule wf_uN_1I) (simp add: ieq_underscore.psimps ieq_underscore.domintros vt_generic_simps res_bool_le1)
lemma ine_bit: "wf_uN (Suc 0) (ine_underscore n x y)"
  by (rule wf_uN_1I) (simp add: ine_underscore.psimps ine_underscore.domintros vt_generic_simps res_bool_le1)

lemmas icmp_some_bit = icmp_bit(1)[OF ilt_some] icmp_bit(2)[OF igt_some] icmp_bit(3)[OF ile_some]
  icmp_bit(4)[OF ige_some]

lemma frel_bits:
  "wf_uN (Suc 0) (feq_underscore n x y)" "wf_uN (Suc 0) (fne_underscore n x y)"
  "wf_uN (Suc 0) (flt_underscore n x y)" "wf_uN (Suc 0) (fgt_underscore n x y)"
  "wf_uN (Suc 0) (fle_underscore n x y)" "wf_uN (Suc 0) (fge_underscore n x y)"
  by (rule wf_uN_1I, rule frel_bool)+

lemmas bit_lemmas = ieq_bit ine_bit icmp_some_bit frel_bits

section \<open>Float lane operations\<close>

lemma flane_wf32: "list_all (wf_fN 32) l \<Longrightarrow> list_all (\<lambda>it. wf_lane_underscore lanetype_F32 (mk_lane__1 Fnn_F32 it)) l"
  by (auto simp: list_all_iff vt_simps intro!: lane__case_1)
lemma flane_wf64: "list_all (wf_fN 64) l \<Longrightarrow> list_all (\<lambda>it. wf_lane_underscore lanetype_F64 (mk_lane__1 Fnn_F64 it)) l"
  by (auto simp: list_all_iff vt_simps intro!: lane__case_1)

lemmas flane_unop =
  flane_wf32[OF fabs__is_wf[OF _ HOL.refl]] flane_wf64[OF fabs__is_wf[OF _ HOL.refl]]
  flane_wf32[OF fneg__is_wf[OF _ HOL.refl]] flane_wf64[OF fneg__is_wf[OF _ HOL.refl]]
  flane_wf32[OF fsqrt__is_wf[OF _ HOL.refl]] flane_wf64[OF fsqrt__is_wf[OF _ HOL.refl]]
  flane_wf32[OF fceil__is_wf[OF _ HOL.refl]] flane_wf64[OF fceil__is_wf[OF _ HOL.refl]]
  flane_wf32[OF ffloor__is_wf[OF _ HOL.refl]] flane_wf64[OF ffloor__is_wf[OF _ HOL.refl]]
  flane_wf32[OF ftrunc__is_wf[OF _ HOL.refl]] flane_wf64[OF ftrunc__is_wf[OF _ HOL.refl]]
  flane_wf32[OF fnearest__is_wf[OF _ HOL.refl]] flane_wf64[OF fnearest__is_wf[OF _ HOL.refl]]

lemmas flane_binop =
  flane_wf32[OF fadd__is_wf[OF _ _ HOL.refl]] flane_wf64[OF fadd__is_wf[OF _ _ HOL.refl]]
  flane_wf32[OF fsub__is_wf[OF _ _ HOL.refl]] flane_wf64[OF fsub__is_wf[OF _ _ HOL.refl]]
  flane_wf32[OF fmul__is_wf[OF _ _ HOL.refl]] flane_wf64[OF fmul__is_wf[OF _ _ HOL.refl]]
  flane_wf32[OF fdiv__is_wf[OF _ _ HOL.refl]] flane_wf64[OF fdiv__is_wf[OF _ _ HOL.refl]]
  flane_wf32[OF fmin__is_wf[OF _ _ HOL.refl]] flane_wf64[OF fmin__is_wf[OF _ _ HOL.refl]]
  flane_wf32[OF fmax__is_wf[OF _ _ HOL.refl]] flane_wf64[OF fmax__is_wf[OF _ _ HOL.refl]]
  flane_wf32[OF fpmin__is_wf[OF _ _ HOL.refl]] flane_wf64[OF fpmin__is_wf[OF _ _ HOL.refl]]
  flane_wf32[OF fpmax__is_wf[OF _ _ HOL.refl]] flane_wf64[OF fpmax__is_wf[OF _ _ HOL.refl]]

(* Float comparisons produce integer lanes of the same width. *)
lemma wf_shape_F32_I32: "wf_shape (X lanetype_F32 d) \<Longrightarrow> wf_shape (X lanetype_I32 d)"
  by (auto elim!: wf_shape.cases intro!: wf_shape.intros simp: vt_simps)
lemma wf_shape_F64_I64: "wf_shape (X lanetype_F64 d) \<Longrightarrow> wf_shape (X lanetype_I64 d)"
  by (auto elim!: wf_shape.cases intro!: wf_shape.intros simp: vt_simps)

section \<open>Rule sets for the case lemmas\<close>

lemmas vt_list_intros = list_all2_mapI list_all3_zipWithI list_all_mapI list_all_zipWithI
  list_all2_setI vt_list_allI

lemmas vt_case_simps = vt_all_simps mk_uN_proj length_list_zipWith

lemmas vt_case_intros = lane__case_0 lane__case_1
  iabs_some iabs_some_wf imin_some imin_some_wf imax_some imax_some_wf
  iadd_sat_some iadd_sat_some_wf isub_sat_some isub_sat_some_wf
  ilt_some igt_some ile_some ige_some bit_lemmas
  iadd__is_wf[OF _ _ HOL.refl] isub__is_wf[OF _ _ HOL.refl] imul__is_wf[OF _ _ HOL.refl]
  ineg__is_wf[OF _ HOL.refl] ipopcnt__is_wf[OF _ HOL.refl]
  iavgr__is_wf[OF _ _ HOL.refl] iq15mulr_sat__is_wf[OF _ _ HOL.refl]
  ishl__is_wf[OF _ _ HOL.refl] ishr__is_wf[OF _ _ HOL.refl]
  extend___is_wf[OF _ HOL.refl]
  flane_unop flane_binop wf_shape_F32_I32 wf_shape_F64_I64

section \<open>Case lemmas: one per `Some` rule of fun_vunop, fun_vbinop and fun_vrelop\<close>

lemma fun_vunop_underscore_case_0:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 v_M vunop_Jnn_N_ABS) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(1)[where var_1_lst = "map (\<lambda> lane_1_3. SOME var_1. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_3))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1))" and var_0_lst = "map (\<lambda> lane_1_2. SOME var_0. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_2))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I32 var_0)) (map (\<lambda> lane_1_2. SOME var_0. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_2))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_1:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 v_M vunop_Jnn_N_ABS) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(2)[where var_1_lst = "map (\<lambda> lane_1_6. SOME var_1. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_6))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1))" and var_0_lst = "map (\<lambda> lane_1_5. SOME var_0. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_5))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I64 var_0)) (map (\<lambda> lane_1_5. SOME var_0. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_5))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_2:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 v_M vunop_Jnn_N_ABS) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(3)[where var_1_lst = "map (\<lambda> lane_1_9. SOME var_1. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_9))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1))" and var_0_lst = "map (\<lambda> lane_1_8. SOME var_0. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_8))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I8 var_0)) (map (\<lambda> lane_1_8. SOME var_0. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_8))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_3:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 v_M vunop_Jnn_N_ABS) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(4)[where var_1_lst = "map (\<lambda> lane_1_12. SOME var_1. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_12))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1))" and var_0_lst = "map (\<lambda> lane_1_11. SOME var_0. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_11))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I16 var_0)) (map (\<lambda> lane_1_11. SOME var_0. (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_11))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_4:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 v_M vunop_Jnn_N_NEG) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(5)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_1_14 :: lane_underscore). (mk_lane__0 Jnn_I32 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_14)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_5:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 v_M vunop_Jnn_N_NEG) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(6)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_1_17 :: lane_underscore). (mk_lane__0 Jnn_I64 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_17)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_6:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 v_M vunop_Jnn_N_NEG) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(7)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_1_20 :: lane_underscore). (mk_lane__0 Jnn_I8 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_20)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_7:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 v_M vunop_Jnn_N_NEG) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(8)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_1_23 :: lane_underscore). (mk_lane__0 Jnn_I16 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_23)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_8:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 v_M vunop_Jnn_N_POPCNT) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(9)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_1_26 :: lane_underscore). (mk_lane__0 Jnn_I32 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_26)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_9:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 v_M vunop_Jnn_N_POPCNT) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(10)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_1_29 :: lane_underscore). (mk_lane__0 Jnn_I64 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_29)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_10:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 v_M vunop_Jnn_N_POPCNT) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(11)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_1_32 :: lane_underscore). (mk_lane__0 Jnn_I8 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_32)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_11:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 v_M vunop_Jnn_N_POPCNT) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(12)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_1_35 :: lane_underscore). (mk_lane__0 Jnn_I16 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_35)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_12:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_ABS) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(13)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_38 :: lane_underscore). (map (\<lambda> (iter_0_71 :: fN). (mk_lane__1 Fnn_F32 iter_0_71)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_38)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_2 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_2)) ((setproduct_underscore  (map (\<lambda> (lane_1_38 :: lane_underscore). (map (\<lambda> (iter_0_71 :: fN). (mk_lane__1 Fnn_F32 iter_0_71)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_38)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_13:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_ABS) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(14)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_41 :: lane_underscore). (map (\<lambda> (iter_0_73 :: fN). (mk_lane__1 Fnn_F64 iter_0_73)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_41)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_4 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_4)) ((setproduct_underscore  (map (\<lambda> (lane_1_41 :: lane_underscore). (map (\<lambda> (iter_0_73 :: fN). (mk_lane__1 Fnn_F64 iter_0_73)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_41)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_14:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_NEG) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(15)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_44 :: lane_underscore). (map (\<lambda> (iter_0_75 :: fN). (mk_lane__1 Fnn_F32 iter_0_75)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_44)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_6 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_6)) ((setproduct_underscore  (map (\<lambda> (lane_1_44 :: lane_underscore). (map (\<lambda> (iter_0_75 :: fN). (mk_lane__1 Fnn_F32 iter_0_75)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_44)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_15:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_NEG) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(16)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_47 :: lane_underscore). (map (\<lambda> (iter_0_77 :: fN). (mk_lane__1 Fnn_F64 iter_0_77)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_47)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_8 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_8)) ((setproduct_underscore  (map (\<lambda> (lane_1_47 :: lane_underscore). (map (\<lambda> (iter_0_77 :: fN). (mk_lane__1 Fnn_F64 iter_0_77)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_47)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_16:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_SQRT) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(17)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_50 :: lane_underscore). (map (\<lambda> (iter_0_79 :: fN). (mk_lane__1 Fnn_F32 iter_0_79)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_50)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_10 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_10)) ((setproduct_underscore  (map (\<lambda> (lane_1_50 :: lane_underscore). (map (\<lambda> (iter_0_79 :: fN). (mk_lane__1 Fnn_F32 iter_0_79)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_50)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_17:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_SQRT) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(18)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_53 :: lane_underscore). (map (\<lambda> (iter_0_81 :: fN). (mk_lane__1 Fnn_F64 iter_0_81)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_53)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_12 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_12)) ((setproduct_underscore  (map (\<lambda> (lane_1_53 :: lane_underscore). (map (\<lambda> (iter_0_81 :: fN). (mk_lane__1 Fnn_F64 iter_0_81)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_53)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_18:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_CEIL) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(19)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_56 :: lane_underscore). (map (\<lambda> (iter_0_83 :: fN). (mk_lane__1 Fnn_F32 iter_0_83)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_56)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_14 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_14)) ((setproduct_underscore  (map (\<lambda> (lane_1_56 :: lane_underscore). (map (\<lambda> (iter_0_83 :: fN). (mk_lane__1 Fnn_F32 iter_0_83)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_56)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_19:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_CEIL) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(20)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_59 :: lane_underscore). (map (\<lambda> (iter_0_85 :: fN). (mk_lane__1 Fnn_F64 iter_0_85)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_59)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_16 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_16)) ((setproduct_underscore  (map (\<lambda> (lane_1_59 :: lane_underscore). (map (\<lambda> (iter_0_85 :: fN). (mk_lane__1 Fnn_F64 iter_0_85)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_59)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_20:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_FLOOR) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(21)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_62 :: lane_underscore). (map (\<lambda> (iter_0_87 :: fN). (mk_lane__1 Fnn_F32 iter_0_87)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_62)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_18 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_18)) ((setproduct_underscore  (map (\<lambda> (lane_1_62 :: lane_underscore). (map (\<lambda> (iter_0_87 :: fN). (mk_lane__1 Fnn_F32 iter_0_87)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_62)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_21:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_FLOOR) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(22)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_65 :: lane_underscore). (map (\<lambda> (iter_0_89 :: fN). (mk_lane__1 Fnn_F64 iter_0_89)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_65)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_20 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_20)) ((setproduct_underscore  (map (\<lambda> (lane_1_65 :: lane_underscore). (map (\<lambda> (iter_0_89 :: fN). (mk_lane__1 Fnn_F64 iter_0_89)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_65)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_22:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_TRUNC) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(23)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_68 :: lane_underscore). (map (\<lambda> (iter_0_91 :: fN). (mk_lane__1 Fnn_F32 iter_0_91)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_68)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_22 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_22)) ((setproduct_underscore  (map (\<lambda> (lane_1_68 :: lane_underscore). (map (\<lambda> (iter_0_91 :: fN). (mk_lane__1 Fnn_F32 iter_0_91)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_68)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_23:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_TRUNC) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(24)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_71 :: lane_underscore). (map (\<lambda> (iter_0_93 :: fN). (mk_lane__1 Fnn_F64 iter_0_93)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_71)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_24 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_24)) ((setproduct_underscore  (map (\<lambda> (lane_1_71 :: lane_underscore). (map (\<lambda> (iter_0_93 :: fN). (mk_lane__1 Fnn_F64 iter_0_93)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_71)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_24:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 v_M vunop_Fnn_N_NEAREST) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(25)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_74 :: lane_underscore). (map (\<lambda> (iter_0_95 :: fN). (mk_lane__1 Fnn_F32 iter_0_95)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_74)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_26 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_26)) ((setproduct_underscore  (map (\<lambda> (lane_1_74 :: lane_underscore). (map (\<lambda> (iter_0_95 :: fN). (mk_lane__1 Fnn_F32 iter_0_95)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_74)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vunop_underscore_case_25:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1"
  shows "\<exists>r. fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 v_M vunop_Fnn_N_NEAREST) v128_1 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vunop_underscore.intros(26)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_lst_lst = "(setproduct_underscore  (map (\<lambda> (lane_1_77 :: lane_underscore). (map (\<lambda> (iter_0_97 :: fN). (mk_lane__1 Fnn_F64 iter_0_97)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_77)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))" and v128_lst = "(map (\<lambda> (lane_lst_28 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_28)) ((setproduct_underscore  (map (\<lambda> (lane_1_77 :: lane_underscore). (map (\<lambda> (iter_0_97 :: fN). (mk_lane__1 Fnn_F64 iter_0_97)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_77)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1))))))"];
        (rule vt_list_intros)?)
    using assms xs0 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed


lemma fun_vbinop_underscore_case_0:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M vbinop_Jnn_N_ADD) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(1)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_80 :: lane_underscore) (lane_2_2 :: lane_underscore). (mk_lane__0 Jnn_I32 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_80))) (the ((proj_lane__0 lane_2_2)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_1:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M vbinop_Jnn_N_ADD) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(2)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_83 :: lane_underscore) (lane_2_5 :: lane_underscore). (mk_lane__0 Jnn_I64 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_83))) (the ((proj_lane__0 lane_2_5)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_2:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M vbinop_Jnn_N_ADD) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(3)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_86 :: lane_underscore) (lane_2_8 :: lane_underscore). (mk_lane__0 Jnn_I8 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_86))) (the ((proj_lane__0 lane_2_8)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_3:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M vbinop_Jnn_N_ADD) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(4)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_89 :: lane_underscore) (lane_2_11 :: lane_underscore). (mk_lane__0 Jnn_I16 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_89))) (the ((proj_lane__0 lane_2_11)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_4:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M vbinop_Jnn_N_SUB) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(5)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_92 :: lane_underscore) (lane_2_14 :: lane_underscore). (mk_lane__0 Jnn_I32 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_92))) (the ((proj_lane__0 lane_2_14)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_5:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M vbinop_Jnn_N_SUB) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(6)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_95 :: lane_underscore) (lane_2_17 :: lane_underscore). (mk_lane__0 Jnn_I64 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_95))) (the ((proj_lane__0 lane_2_17)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_6:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M vbinop_Jnn_N_SUB) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(7)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_98 :: lane_underscore) (lane_2_20 :: lane_underscore). (mk_lane__0 Jnn_I8 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_98))) (the ((proj_lane__0 lane_2_20)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_7:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M vbinop_Jnn_N_SUB) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(8)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_101 :: lane_underscore) (lane_2_23 :: lane_underscore). (mk_lane__0 Jnn_I16 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_101))) (the ((proj_lane__0 lane_2_23)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_8:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(9)[where var_1_lst = "list_zipWith (\<lambda> lane_1_105 lane_2_27. SOME var_1. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_105))) (the ((proj_lane__0 lane_2_27))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_104 lane_2_26. SOME var_0. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_104))) (the ((proj_lane__0 lane_2_26))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I32 var_0)) (list_zipWith (\<lambda> lane_1_104 lane_2_26. SOME var_0. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_104))) (the ((proj_lane__0 lane_2_26))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_9:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(10)[where var_1_lst = "list_zipWith (\<lambda> lane_1_108 lane_2_30. SOME var_1. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_108))) (the ((proj_lane__0 lane_2_30))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_107 lane_2_29. SOME var_0. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_107))) (the ((proj_lane__0 lane_2_29))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I64 var_0)) (list_zipWith (\<lambda> lane_1_107 lane_2_29. SOME var_0. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_107))) (the ((proj_lane__0 lane_2_29))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_10:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(11)[where var_1_lst = "list_zipWith (\<lambda> lane_1_111 lane_2_33. SOME var_1. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_111))) (the ((proj_lane__0 lane_2_33))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_110 lane_2_32. SOME var_0. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_110))) (the ((proj_lane__0 lane_2_32))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I8 var_0)) (list_zipWith (\<lambda> lane_1_110 lane_2_32. SOME var_0. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_110))) (the ((proj_lane__0 lane_2_32))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_11:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(12)[where var_1_lst = "list_zipWith (\<lambda> lane_1_114 lane_2_36. SOME var_1. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_114))) (the ((proj_lane__0 lane_2_36))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_113 lane_2_35. SOME var_0. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_113))) (the ((proj_lane__0 lane_2_35))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I16 var_0)) (list_zipWith (\<lambda> lane_1_113 lane_2_35. SOME var_0. (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_113))) (the ((proj_lane__0 lane_2_35))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_12:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(13)[where var_1_lst = "list_zipWith (\<lambda> lane_1_117 lane_2_39. SOME var_1. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_117))) (the ((proj_lane__0 lane_2_39))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_116 lane_2_38. SOME var_0. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_116))) (the ((proj_lane__0 lane_2_38))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I32 var_0)) (list_zipWith (\<lambda> lane_1_116 lane_2_38. SOME var_0. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_116))) (the ((proj_lane__0 lane_2_38))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_13:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(14)[where var_1_lst = "list_zipWith (\<lambda> lane_1_120 lane_2_42. SOME var_1. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_120))) (the ((proj_lane__0 lane_2_42))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_119 lane_2_41. SOME var_0. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_119))) (the ((proj_lane__0 lane_2_41))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I64 var_0)) (list_zipWith (\<lambda> lane_1_119 lane_2_41. SOME var_0. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_119))) (the ((proj_lane__0 lane_2_41))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_14:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(15)[where var_1_lst = "list_zipWith (\<lambda> lane_1_123 lane_2_45. SOME var_1. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_123))) (the ((proj_lane__0 lane_2_45))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_122 lane_2_44. SOME var_0. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_122))) (the ((proj_lane__0 lane_2_44))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I8 var_0)) (list_zipWith (\<lambda> lane_1_122 lane_2_44. SOME var_0. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_122))) (the ((proj_lane__0 lane_2_44))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_15:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(16)[where var_1_lst = "list_zipWith (\<lambda> lane_1_126 lane_2_48. SOME var_1. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_126))) (the ((proj_lane__0 lane_2_48))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_125 lane_2_47. SOME var_0. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_125))) (the ((proj_lane__0 lane_2_47))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I16 var_0)) (list_zipWith (\<lambda> lane_1_125 lane_2_47. SOME var_0. (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_125))) (the ((proj_lane__0 lane_2_47))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_16:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M (ADD_SAT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(17)[where var_1_lst = "list_zipWith (\<lambda> lane_1_129 lane_2_51. SOME var_1. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_129))) (the ((proj_lane__0 lane_2_51))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_128 lane_2_50. SOME var_0. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_128))) (the ((proj_lane__0 lane_2_50))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I32 var_0)) (list_zipWith (\<lambda> lane_1_128 lane_2_50. SOME var_0. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_128))) (the ((proj_lane__0 lane_2_50))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_17:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M (ADD_SAT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(18)[where var_1_lst = "list_zipWith (\<lambda> lane_1_132 lane_2_54. SOME var_1. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_132))) (the ((proj_lane__0 lane_2_54))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_131 lane_2_53. SOME var_0. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_131))) (the ((proj_lane__0 lane_2_53))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I64 var_0)) (list_zipWith (\<lambda> lane_1_131 lane_2_53. SOME var_0. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_131))) (the ((proj_lane__0 lane_2_53))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_18:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M (ADD_SAT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(19)[where var_1_lst = "list_zipWith (\<lambda> lane_1_135 lane_2_57. SOME var_1. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_135))) (the ((proj_lane__0 lane_2_57))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_134 lane_2_56. SOME var_0. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_134))) (the ((proj_lane__0 lane_2_56))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I8 var_0)) (list_zipWith (\<lambda> lane_1_134 lane_2_56. SOME var_0. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_134))) (the ((proj_lane__0 lane_2_56))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_19:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M (ADD_SAT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(20)[where var_1_lst = "list_zipWith (\<lambda> lane_1_138 lane_2_60. SOME var_1. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_138))) (the ((proj_lane__0 lane_2_60))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_137 lane_2_59. SOME var_0. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_137))) (the ((proj_lane__0 lane_2_59))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I16 var_0)) (list_zipWith (\<lambda> lane_1_137 lane_2_59. SOME var_0. (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_137))) (the ((proj_lane__0 lane_2_59))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_20:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M (SUB_SAT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(21)[where var_1_lst = "list_zipWith (\<lambda> lane_1_141 lane_2_63. SOME var_1. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_141))) (the ((proj_lane__0 lane_2_63))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_140 lane_2_62. SOME var_0. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_140))) (the ((proj_lane__0 lane_2_62))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I32 var_0)) (list_zipWith (\<lambda> lane_1_140 lane_2_62. SOME var_0. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_140))) (the ((proj_lane__0 lane_2_62))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_21:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M (SUB_SAT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(22)[where var_1_lst = "list_zipWith (\<lambda> lane_1_144 lane_2_66. SOME var_1. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_144))) (the ((proj_lane__0 lane_2_66))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_143 lane_2_65. SOME var_0. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_143))) (the ((proj_lane__0 lane_2_65))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I64 var_0)) (list_zipWith (\<lambda> lane_1_143 lane_2_65. SOME var_0. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_143))) (the ((proj_lane__0 lane_2_65))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_22:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M (SUB_SAT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(23)[where var_1_lst = "list_zipWith (\<lambda> lane_1_147 lane_2_69. SOME var_1. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_147))) (the ((proj_lane__0 lane_2_69))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_146 lane_2_68. SOME var_0. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_146))) (the ((proj_lane__0 lane_2_68))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I8 var_0)) (list_zipWith (\<lambda> lane_1_146 lane_2_68. SOME var_0. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_146))) (the ((proj_lane__0 lane_2_68))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_23:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M (SUB_SAT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(24)[where var_1_lst = "list_zipWith (\<lambda> lane_1_150 lane_2_72. SOME var_1. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_150))) (the ((proj_lane__0 lane_2_72))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_149 lane_2_71. SOME var_0. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_149))) (the ((proj_lane__0 lane_2_71))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__0 Jnn_I16 var_0)) (list_zipWith (\<lambda> lane_1_149 lane_2_71. SOME var_0. (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_149))) (the ((proj_lane__0 lane_2_71))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_24:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M vbinop_Jnn_N_MUL) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(25)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_152 :: lane_underscore) (lane_2_74 :: lane_underscore). (mk_lane__0 Jnn_I32 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_152))) (the ((proj_lane__0 lane_2_74)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_25:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M vbinop_Jnn_N_MUL) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(26)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_155 :: lane_underscore) (lane_2_77 :: lane_underscore). (mk_lane__0 Jnn_I64 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_155))) (the ((proj_lane__0 lane_2_77)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_26:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M vbinop_Jnn_N_MUL) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(27)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_158 :: lane_underscore) (lane_2_80 :: lane_underscore). (mk_lane__0 Jnn_I8 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_158))) (the ((proj_lane__0 lane_2_80)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_27:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M vbinop_Jnn_N_MUL) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(28)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_161 :: lane_underscore) (lane_2_83 :: lane_underscore). (mk_lane__0 Jnn_I16 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_161))) (the ((proj_lane__0 lane_2_83)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_28:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M AVGRU) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(29)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_164 :: lane_underscore) (lane_2_86 :: lane_underscore). (mk_lane__0 Jnn_I32 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I32)) U (the ((proj_lane__0 lane_1_164))) (the ((proj_lane__0 lane_2_86)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_29:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M AVGRU) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(30)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_167 :: lane_underscore) (lane_2_89 :: lane_underscore). (mk_lane__0 Jnn_I64 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I64)) U (the ((proj_lane__0 lane_1_167))) (the ((proj_lane__0 lane_2_89)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_30:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M AVGRU) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(31)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_170 :: lane_underscore) (lane_2_92 :: lane_underscore). (mk_lane__0 Jnn_I8 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I8)) U (the ((proj_lane__0 lane_1_170))) (the ((proj_lane__0 lane_2_92)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_31:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M AVGRU) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(32)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_173 :: lane_underscore) (lane_2_95 :: lane_underscore). (mk_lane__0 Jnn_I16 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I16)) U (the ((proj_lane__0 lane_1_173))) (the ((proj_lane__0 lane_2_95)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_32:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 v_M Q15MULR_SATS) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(33)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_176 :: lane_underscore) (lane_2_98 :: lane_underscore). (mk_lane__0 Jnn_I32 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) S (the ((proj_lane__0 lane_1_176))) (the ((proj_lane__0 lane_2_98)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_33:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 v_M Q15MULR_SATS) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(34)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_179 :: lane_underscore) (lane_2_101 :: lane_underscore). (mk_lane__0 Jnn_I64 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) S (the ((proj_lane__0 lane_1_179))) (the ((proj_lane__0 lane_2_101)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_34:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 v_M Q15MULR_SATS) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(35)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_182 :: lane_underscore) (lane_2_104 :: lane_underscore). (mk_lane__0 Jnn_I8 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) S (the ((proj_lane__0 lane_1_182))) (the ((proj_lane__0 lane_2_104)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_35:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 v_M Q15MULR_SATS) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(36)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_185 :: lane_underscore) (lane_2_107 :: lane_underscore). (mk_lane__0 Jnn_I16 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) S (the ((proj_lane__0 lane_1_185))) (the ((proj_lane__0 lane_2_107)))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_36:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_ADD) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(37)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_188 :: lane_underscore) (lane_2_110 :: lane_underscore). (map (\<lambda> (iter_0_99 :: fN). (mk_lane__1 Fnn_F32 iter_0_99)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_188))) (the ((proj_lane__1 lane_2_110)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_30 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_30)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_188 :: lane_underscore) (lane_2_110 :: lane_underscore). (map (\<lambda> (iter_0_99 :: fN). (mk_lane__1 Fnn_F32 iter_0_99)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_188))) (the ((proj_lane__1 lane_2_110)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_37:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_ADD) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(38)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_191 :: lane_underscore) (lane_2_113 :: lane_underscore). (map (\<lambda> (iter_0_101 :: fN). (mk_lane__1 Fnn_F64 iter_0_101)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_191))) (the ((proj_lane__1 lane_2_113)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_32 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_32)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_191 :: lane_underscore) (lane_2_113 :: lane_underscore). (map (\<lambda> (iter_0_101 :: fN). (mk_lane__1 Fnn_F64 iter_0_101)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_191))) (the ((proj_lane__1 lane_2_113)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_38:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_SUB) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(39)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_194 :: lane_underscore) (lane_2_116 :: lane_underscore). (map (\<lambda> (iter_0_103 :: fN). (mk_lane__1 Fnn_F32 iter_0_103)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_194))) (the ((proj_lane__1 lane_2_116)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_34 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_34)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_194 :: lane_underscore) (lane_2_116 :: lane_underscore). (map (\<lambda> (iter_0_103 :: fN). (mk_lane__1 Fnn_F32 iter_0_103)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_194))) (the ((proj_lane__1 lane_2_116)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_39:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_SUB) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(40)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_197 :: lane_underscore) (lane_2_119 :: lane_underscore). (map (\<lambda> (iter_0_105 :: fN). (mk_lane__1 Fnn_F64 iter_0_105)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_197))) (the ((proj_lane__1 lane_2_119)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_36 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_36)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_197 :: lane_underscore) (lane_2_119 :: lane_underscore). (map (\<lambda> (iter_0_105 :: fN). (mk_lane__1 Fnn_F64 iter_0_105)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_197))) (the ((proj_lane__1 lane_2_119)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_40:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_MUL) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(41)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_200 :: lane_underscore) (lane_2_122 :: lane_underscore). (map (\<lambda> (iter_0_107 :: fN). (mk_lane__1 Fnn_F32 iter_0_107)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_200))) (the ((proj_lane__1 lane_2_122)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_38 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_38)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_200 :: lane_underscore) (lane_2_122 :: lane_underscore). (map (\<lambda> (iter_0_107 :: fN). (mk_lane__1 Fnn_F32 iter_0_107)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_200))) (the ((proj_lane__1 lane_2_122)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_41:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_MUL) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(42)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_203 :: lane_underscore) (lane_2_125 :: lane_underscore). (map (\<lambda> (iter_0_109 :: fN). (mk_lane__1 Fnn_F64 iter_0_109)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_203))) (the ((proj_lane__1 lane_2_125)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_40 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_40)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_203 :: lane_underscore) (lane_2_125 :: lane_underscore). (map (\<lambda> (iter_0_109 :: fN). (mk_lane__1 Fnn_F64 iter_0_109)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_203))) (the ((proj_lane__1 lane_2_125)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_42:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_DIV) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(43)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_206 :: lane_underscore) (lane_2_128 :: lane_underscore). (map (\<lambda> (iter_0_111 :: fN). (mk_lane__1 Fnn_F32 iter_0_111)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_206))) (the ((proj_lane__1 lane_2_128)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_42 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_42)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_206 :: lane_underscore) (lane_2_128 :: lane_underscore). (map (\<lambda> (iter_0_111 :: fN). (mk_lane__1 Fnn_F32 iter_0_111)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_206))) (the ((proj_lane__1 lane_2_128)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_43:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_DIV) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(44)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_209 :: lane_underscore) (lane_2_131 :: lane_underscore). (map (\<lambda> (iter_0_113 :: fN). (mk_lane__1 Fnn_F64 iter_0_113)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_209))) (the ((proj_lane__1 lane_2_131)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_44 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_44)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_209 :: lane_underscore) (lane_2_131 :: lane_underscore). (map (\<lambda> (iter_0_113 :: fN). (mk_lane__1 Fnn_F64 iter_0_113)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_209))) (the ((proj_lane__1 lane_2_131)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_44:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_MIN) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(45)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_212 :: lane_underscore) (lane_2_134 :: lane_underscore). (map (\<lambda> (iter_0_115 :: fN). (mk_lane__1 Fnn_F32 iter_0_115)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_212))) (the ((proj_lane__1 lane_2_134)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_46 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_46)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_212 :: lane_underscore) (lane_2_134 :: lane_underscore). (map (\<lambda> (iter_0_115 :: fN). (mk_lane__1 Fnn_F32 iter_0_115)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_212))) (the ((proj_lane__1 lane_2_134)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_45:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_MIN) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(46)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_215 :: lane_underscore) (lane_2_137 :: lane_underscore). (map (\<lambda> (iter_0_117 :: fN). (mk_lane__1 Fnn_F64 iter_0_117)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_215))) (the ((proj_lane__1 lane_2_137)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_48 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_48)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_215 :: lane_underscore) (lane_2_137 :: lane_underscore). (map (\<lambda> (iter_0_117 :: fN). (mk_lane__1 Fnn_F64 iter_0_117)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_215))) (the ((proj_lane__1 lane_2_137)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_46:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M vbinop_Fnn_N_MAX) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(47)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_218 :: lane_underscore) (lane_2_140 :: lane_underscore). (map (\<lambda> (iter_0_119 :: fN). (mk_lane__1 Fnn_F32 iter_0_119)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_218))) (the ((proj_lane__1 lane_2_140)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_50 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_50)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_218 :: lane_underscore) (lane_2_140 :: lane_underscore). (map (\<lambda> (iter_0_119 :: fN). (mk_lane__1 Fnn_F32 iter_0_119)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_218))) (the ((proj_lane__1 lane_2_140)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_47:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M vbinop_Fnn_N_MAX) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(48)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_221 :: lane_underscore) (lane_2_143 :: lane_underscore). (map (\<lambda> (iter_0_121 :: fN). (mk_lane__1 Fnn_F64 iter_0_121)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_221))) (the ((proj_lane__1 lane_2_143)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_52 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_52)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_221 :: lane_underscore) (lane_2_143 :: lane_underscore). (map (\<lambda> (iter_0_121 :: fN). (mk_lane__1 Fnn_F64 iter_0_121)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_221))) (the ((proj_lane__1 lane_2_143)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_48:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M PMIN) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(49)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_224 :: lane_underscore) (lane_2_146 :: lane_underscore). (map (\<lambda> (iter_0_123 :: fN). (mk_lane__1 Fnn_F32 iter_0_123)) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_224))) (the ((proj_lane__1 lane_2_146)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_54 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_54)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_224 :: lane_underscore) (lane_2_146 :: lane_underscore). (map (\<lambda> (iter_0_123 :: fN). (mk_lane__1 Fnn_F32 iter_0_123)) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_224))) (the ((proj_lane__1 lane_2_146)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_49:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M PMIN) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(50)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_227 :: lane_underscore) (lane_2_149 :: lane_underscore). (map (\<lambda> (iter_0_125 :: fN). (mk_lane__1 Fnn_F64 iter_0_125)) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_227))) (the ((proj_lane__1 lane_2_149)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_56 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_56)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_227 :: lane_underscore) (lane_2_149 :: lane_underscore). (map (\<lambda> (iter_0_125 :: fN). (mk_lane__1 Fnn_F64 iter_0_125)) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_227))) (the ((proj_lane__1 lane_2_149)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_50:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 v_M PMAX) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(51)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_230 :: lane_underscore) (lane_2_152 :: lane_underscore). (map (\<lambda> (iter_0_127 :: fN). (mk_lane__1 Fnn_F32 iter_0_127)) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_230))) (the ((proj_lane__1 lane_2_152)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_58 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_58)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_230 :: lane_underscore) (lane_2_152 :: lane_underscore). (map (\<lambda> (iter_0_127 :: fN). (mk_lane__1 Fnn_F32 iter_0_127)) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_230))) (the ((proj_lane__1 lane_2_152)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vbinop_underscore_case_51:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 v_M PMAX) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vbinop_underscore.intros(52)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_lst_lst = "(setproduct_underscore  (list_zipWith (\<lambda> (lane_1_233 :: lane_underscore) (lane_2_155 :: lane_underscore). (map (\<lambda> (iter_0_129 :: fN). (mk_lane__1 Fnn_F64 iter_0_129)) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_233))) (the ((proj_lane__1 lane_2_155)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))" and v128_lst = "(map (\<lambda> (lane_lst_60 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_60)) ((setproduct_underscore  (list_zipWith (\<lambda> (lane_1_233 :: lane_underscore) (lane_2_155 :: lane_underscore). (map (\<lambda> (iter_0_129 :: fN). (mk_lane__1 Fnn_F64 iter_0_129)) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_233))) (the ((proj_lane__1 lane_2_155)))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed


lemma fun_vrelop_underscore_case_0:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M vrelop_Jnn_N_EQ) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(1)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_236 :: lane_underscore) (lane_2_158 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_236))) (the ((proj_lane__0 lane_2_158)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_2 :: iN). (mk_lane__0 Jnn_I32 lane_3_2)) ((list_zipWith (\<lambda> (lane_1_236 :: lane_underscore) (lane_2_158 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_236))) (the ((proj_lane__0 lane_2_158)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_1:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M vrelop_Jnn_N_EQ) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(2)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_239 :: lane_underscore) (lane_2_161 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_239))) (the ((proj_lane__0 lane_2_161)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_5 :: iN). (mk_lane__0 Jnn_I64 lane_3_5)) ((list_zipWith (\<lambda> (lane_1_239 :: lane_underscore) (lane_2_161 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_239))) (the ((proj_lane__0 lane_2_161)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_2:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M vrelop_Jnn_N_EQ) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(3)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_242 :: lane_underscore) (lane_2_164 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_242))) (the ((proj_lane__0 lane_2_164)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_8 :: iN). (mk_lane__0 Jnn_I8 lane_3_8)) ((list_zipWith (\<lambda> (lane_1_242 :: lane_underscore) (lane_2_164 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_242))) (the ((proj_lane__0 lane_2_164)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_3:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M vrelop_Jnn_N_EQ) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(4)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_245 :: lane_underscore) (lane_2_167 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_245))) (the ((proj_lane__0 lane_2_167)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_11 :: iN). (mk_lane__0 Jnn_I16 lane_3_11)) ((list_zipWith (\<lambda> (lane_1_245 :: lane_underscore) (lane_2_167 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_245))) (the ((proj_lane__0 lane_2_167)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_4:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M vrelop_Jnn_N_NE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(5)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_248 :: lane_underscore) (lane_2_170 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_248))) (the ((proj_lane__0 lane_2_170)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_14 :: iN). (mk_lane__0 Jnn_I32 lane_3_14)) ((list_zipWith (\<lambda> (lane_1_248 :: lane_underscore) (lane_2_170 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__0 lane_1_248))) (the ((proj_lane__0 lane_2_170)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_5:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M vrelop_Jnn_N_NE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(6)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_251 :: lane_underscore) (lane_2_173 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_251))) (the ((proj_lane__0 lane_2_173)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_17 :: iN). (mk_lane__0 Jnn_I64 lane_3_17)) ((list_zipWith (\<lambda> (lane_1_251 :: lane_underscore) (lane_2_173 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__0 lane_1_251))) (the ((proj_lane__0 lane_2_173)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_6:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M vrelop_Jnn_N_NE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(7)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_254 :: lane_underscore) (lane_2_176 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_254))) (the ((proj_lane__0 lane_2_176)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_20 :: iN). (mk_lane__0 Jnn_I8 lane_3_20)) ((list_zipWith (\<lambda> (lane_1_254 :: lane_underscore) (lane_2_176 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__0 lane_1_254))) (the ((proj_lane__0 lane_2_176)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_7:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M vrelop_Jnn_N_NE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(8)[where lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_257 :: lane_underscore) (lane_2_179 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_257))) (the ((proj_lane__0 lane_2_179)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_23 :: iN). (mk_lane__0 Jnn_I16 lane_3_23)) ((list_zipWith (\<lambda> (lane_1_257 :: lane_underscore) (lane_2_179 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__0 lane_1_257))) (the ((proj_lane__0 lane_2_179)))))))) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_8:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(9)[where var_1_lst = "list_zipWith (\<lambda> lane_1_261 lane_2_183. SOME var_1. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_261))) (the ((proj_lane__0 lane_2_183))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_260 lane_2_182. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_260))) (the ((proj_lane__0 lane_2_182))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_260 lane_2_182. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_260))) (the ((proj_lane__0 lane_2_182))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_26 :: iN). (mk_lane__0 Jnn_I32 lane_3_26)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_260 lane_2_182. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_260))) (the ((proj_lane__0 lane_2_182))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_9:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(10)[where var_1_lst = "list_zipWith (\<lambda> lane_1_264 lane_2_186. SOME var_1. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_264))) (the ((proj_lane__0 lane_2_186))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_263 lane_2_185. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_263))) (the ((proj_lane__0 lane_2_185))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_263 lane_2_185. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_263))) (the ((proj_lane__0 lane_2_185))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_29 :: iN). (mk_lane__0 Jnn_I64 lane_3_29)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_263 lane_2_185. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_263))) (the ((proj_lane__0 lane_2_185))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_10:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(11)[where var_1_lst = "list_zipWith (\<lambda> lane_1_267 lane_2_189. SOME var_1. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_267))) (the ((proj_lane__0 lane_2_189))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_266 lane_2_188. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_266))) (the ((proj_lane__0 lane_2_188))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_266 lane_2_188. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_266))) (the ((proj_lane__0 lane_2_188))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_32 :: iN). (mk_lane__0 Jnn_I8 lane_3_32)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_266 lane_2_188. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_266))) (the ((proj_lane__0 lane_2_188))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_11:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(12)[where var_1_lst = "list_zipWith (\<lambda> lane_1_270 lane_2_192. SOME var_1. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_270))) (the ((proj_lane__0 lane_2_192))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_269 lane_2_191. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_269))) (the ((proj_lane__0 lane_2_191))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_269 lane_2_191. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_269))) (the ((proj_lane__0 lane_2_191))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_35 :: iN). (mk_lane__0 Jnn_I16 lane_3_35)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_269 lane_2_191. SOME var_0. (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_269))) (the ((proj_lane__0 lane_2_191))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_12:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(13)[where var_1_lst = "list_zipWith (\<lambda> lane_1_273 lane_2_195. SOME var_1. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_273))) (the ((proj_lane__0 lane_2_195))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_272 lane_2_194. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_272))) (the ((proj_lane__0 lane_2_194))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_272 lane_2_194. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_272))) (the ((proj_lane__0 lane_2_194))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_38 :: iN). (mk_lane__0 Jnn_I32 lane_3_38)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_272 lane_2_194. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_272))) (the ((proj_lane__0 lane_2_194))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_13:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(14)[where var_1_lst = "list_zipWith (\<lambda> lane_1_276 lane_2_198. SOME var_1. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_276))) (the ((proj_lane__0 lane_2_198))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_275 lane_2_197. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_275))) (the ((proj_lane__0 lane_2_197))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_275 lane_2_197. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_275))) (the ((proj_lane__0 lane_2_197))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_41 :: iN). (mk_lane__0 Jnn_I64 lane_3_41)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_275 lane_2_197. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_275))) (the ((proj_lane__0 lane_2_197))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_14:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(15)[where var_1_lst = "list_zipWith (\<lambda> lane_1_279 lane_2_201. SOME var_1. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_279))) (the ((proj_lane__0 lane_2_201))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_278 lane_2_200. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_278))) (the ((proj_lane__0 lane_2_200))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_278 lane_2_200. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_278))) (the ((proj_lane__0 lane_2_200))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_44 :: iN). (mk_lane__0 Jnn_I8 lane_3_44)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_278 lane_2_200. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_278))) (the ((proj_lane__0 lane_2_200))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_15:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(16)[where var_1_lst = "list_zipWith (\<lambda> lane_1_282 lane_2_204. SOME var_1. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_282))) (the ((proj_lane__0 lane_2_204))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_281 lane_2_203. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_281))) (the ((proj_lane__0 lane_2_203))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_281 lane_2_203. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_281))) (the ((proj_lane__0 lane_2_203))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_47 :: iN). (mk_lane__0 Jnn_I16 lane_3_47)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_281 lane_2_203. SOME var_0. (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_281))) (the ((proj_lane__0 lane_2_203))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_16:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(17)[where var_1_lst = "list_zipWith (\<lambda> lane_1_285 lane_2_207. SOME var_1. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_285))) (the ((proj_lane__0 lane_2_207))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_284 lane_2_206. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_284))) (the ((proj_lane__0 lane_2_206))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_284 lane_2_206. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_284))) (the ((proj_lane__0 lane_2_206))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_50 :: iN). (mk_lane__0 Jnn_I32 lane_3_50)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_284 lane_2_206. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_284))) (the ((proj_lane__0 lane_2_206))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_17:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(18)[where var_1_lst = "list_zipWith (\<lambda> lane_1_288 lane_2_210. SOME var_1. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_288))) (the ((proj_lane__0 lane_2_210))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_287 lane_2_209. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_287))) (the ((proj_lane__0 lane_2_209))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_287 lane_2_209. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_287))) (the ((proj_lane__0 lane_2_209))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_53 :: iN). (mk_lane__0 Jnn_I64 lane_3_53)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_287 lane_2_209. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_287))) (the ((proj_lane__0 lane_2_209))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_18:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(19)[where var_1_lst = "list_zipWith (\<lambda> lane_1_291 lane_2_213. SOME var_1. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_291))) (the ((proj_lane__0 lane_2_213))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_290 lane_2_212. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_290))) (the ((proj_lane__0 lane_2_212))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_290 lane_2_212. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_290))) (the ((proj_lane__0 lane_2_212))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_56 :: iN). (mk_lane__0 Jnn_I8 lane_3_56)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_290 lane_2_212. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_290))) (the ((proj_lane__0 lane_2_212))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_19:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(20)[where var_1_lst = "list_zipWith (\<lambda> lane_1_294 lane_2_216. SOME var_1. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_294))) (the ((proj_lane__0 lane_2_216))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_293 lane_2_215. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_293))) (the ((proj_lane__0 lane_2_215))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_293 lane_2_215. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_293))) (the ((proj_lane__0 lane_2_215))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_59 :: iN). (mk_lane__0 Jnn_I16 lane_3_59)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_293 lane_2_215. SOME var_0. (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_293))) (the ((proj_lane__0 lane_2_215))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_20:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 v_M (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I32) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I32) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I32)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(21)[where var_1_lst = "list_zipWith (\<lambda> lane_1_297 lane_2_219. SOME var_1. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_297))) (the ((proj_lane__0 lane_2_219))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_296 lane_2_218. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_296))) (the ((proj_lane__0 lane_2_218))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_296 lane_2_218. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_296))) (the ((proj_lane__0 lane_2_218))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_62 :: iN). (mk_lane__0 Jnn_I32 lane_3_62)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_296 lane_2_218. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__0 lane_1_296))) (the ((proj_lane__0 lane_2_218))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_21:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 v_M (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I64) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I64) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I64)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(22)[where var_1_lst = "list_zipWith (\<lambda> lane_1_300 lane_2_222. SOME var_1. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_300))) (the ((proj_lane__0 lane_2_222))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_299 lane_2_221. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_299))) (the ((proj_lane__0 lane_2_221))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_299 lane_2_221. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_299))) (the ((proj_lane__0 lane_2_221))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_65 :: iN). (mk_lane__0 Jnn_I64 lane_3_65)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_299 lane_2_221. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__0 lane_1_299))) (the ((proj_lane__0 lane_2_221))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_22:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 v_M (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I8) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I8) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I8 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(23)[where var_1_lst = "list_zipWith (\<lambda> lane_1_303 lane_2_225. SOME var_1. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_303))) (the ((proj_lane__0 lane_2_225))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_302 lane_2_224. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_302))) (the ((proj_lane__0 lane_2_224))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_302 lane_2_224. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_302))) (the ((proj_lane__0 lane_2_224))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_68 :: iN). (mk_lane__0 Jnn_I8 lane_3_68)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_302 lane_2_224. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__0 lane_1_302))) (the ((proj_lane__0 lane_2_224))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_23:
  assumes "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 v_M (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1 = map (mk_lane__0 Jnn_I16) xs0"
      "\<forall>x\<in>set xs0. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs0 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2 = map (mk_lane__0 Jnn_I16) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I16)) x" "length xs1 = v_M"
    using lanes_Jnn[of Jnn_I16 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(24)[where var_1_lst = "list_zipWith (\<lambda> lane_1_306 lane_2_228. SOME var_1. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_306))) (the ((proj_lane__0 lane_2_228))) var_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and var_0_lst = "list_zipWith (\<lambda> lane_1_305 lane_2_227. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_305))) (the ((proj_lane__0 lane_2_227))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))" and lane_1_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)" and lane_3_lst = "(map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_305 lane_2_227. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_305))) (the ((proj_lane__0 lane_2_227))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2))))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_71 :: iN). (mk_lane__0 Jnn_I16 lane_3_71)) ((map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) (list_zipWith (\<lambda> lane_1_305 lane_2_227. SOME var_0. (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__0 lane_1_305))) (the ((proj_lane__0 lane_2_227))) var_0)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)))))))"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_24:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_EQ) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(25)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_308 :: lane_underscore) (lane_2_230 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_308))) (the ((proj_lane__1 lane_2_230)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_74 :: iN). (mk_lane__0 (Jnn_Inn Inn_I32) (mk_uN (proj_uN_0 lane_3_74)))) ((list_zipWith (\<lambda> (lane_1_308 :: lane_underscore) (lane_2_230 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_308))) (the ((proj_lane__1 lane_2_230)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I32"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_25:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_EQ) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(26)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_311 :: lane_underscore) (lane_2_233 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_311))) (the ((proj_lane__1 lane_2_233)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_77 :: iN). (mk_lane__0 (Jnn_Inn Inn_I64) (mk_uN (proj_uN_0 lane_3_77)))) ((list_zipWith (\<lambda> (lane_1_311 :: lane_underscore) (lane_2_233 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_311))) (the ((proj_lane__1 lane_2_233)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I64"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_26:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_NE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(27)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_314 :: lane_underscore) (lane_2_236 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_314))) (the ((proj_lane__1 lane_2_236)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_80 :: iN). (mk_lane__0 (Jnn_Inn Inn_I32) (mk_uN (proj_uN_0 lane_3_80)))) ((list_zipWith (\<lambda> (lane_1_314 :: lane_underscore) (lane_2_236 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_314))) (the ((proj_lane__1 lane_2_236)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I32"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_27:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_NE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(28)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_317 :: lane_underscore) (lane_2_239 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_317))) (the ((proj_lane__1 lane_2_239)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_83 :: iN). (mk_lane__0 (Jnn_Inn Inn_I64) (mk_uN (proj_uN_0 lane_3_83)))) ((list_zipWith (\<lambda> (lane_1_317 :: lane_underscore) (lane_2_239 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_317))) (the ((proj_lane__1 lane_2_239)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I64"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_28:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_LT) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(29)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_320 :: lane_underscore) (lane_2_242 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_320))) (the ((proj_lane__1 lane_2_242)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_86 :: iN). (mk_lane__0 (Jnn_Inn Inn_I32) (mk_uN (proj_uN_0 lane_3_86)))) ((list_zipWith (\<lambda> (lane_1_320 :: lane_underscore) (lane_2_242 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_320))) (the ((proj_lane__1 lane_2_242)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I32"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_29:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_LT) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(30)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_323 :: lane_underscore) (lane_2_245 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_323))) (the ((proj_lane__1 lane_2_245)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_89 :: iN). (mk_lane__0 (Jnn_Inn Inn_I64) (mk_uN (proj_uN_0 lane_3_89)))) ((list_zipWith (\<lambda> (lane_1_323 :: lane_underscore) (lane_2_245 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_323))) (the ((proj_lane__1 lane_2_245)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I64"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_30:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_GT) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(31)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_326 :: lane_underscore) (lane_2_248 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_326))) (the ((proj_lane__1 lane_2_248)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_92 :: iN). (mk_lane__0 (Jnn_Inn Inn_I32) (mk_uN (proj_uN_0 lane_3_92)))) ((list_zipWith (\<lambda> (lane_1_326 :: lane_underscore) (lane_2_248 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_326))) (the ((proj_lane__1 lane_2_248)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I32"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_31:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_GT) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(32)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_329 :: lane_underscore) (lane_2_251 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_329))) (the ((proj_lane__1 lane_2_251)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_95 :: iN). (mk_lane__0 (Jnn_Inn Inn_I64) (mk_uN (proj_uN_0 lane_3_95)))) ((list_zipWith (\<lambda> (lane_1_329 :: lane_underscore) (lane_2_251 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_329))) (the ((proj_lane__1 lane_2_251)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I64"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_32:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_LE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(33)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_332 :: lane_underscore) (lane_2_254 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_332))) (the ((proj_lane__1 lane_2_254)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_98 :: iN). (mk_lane__0 (Jnn_Inn Inn_I32) (mk_uN (proj_uN_0 lane_3_98)))) ((list_zipWith (\<lambda> (lane_1_332 :: lane_underscore) (lane_2_254 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_332))) (the ((proj_lane__1 lane_2_254)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I32"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_33:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_LE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(34)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_335 :: lane_underscore) (lane_2_257 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_335))) (the ((proj_lane__1 lane_2_257)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_101 :: iN). (mk_lane__0 (Jnn_Inn Inn_I64) (mk_uN (proj_uN_0 lane_3_101)))) ((list_zipWith (\<lambda> (lane_1_335 :: lane_underscore) (lane_2_257 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_335))) (the ((proj_lane__1 lane_2_257)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I64"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_34:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 v_M vrelop_Fnn_N_GE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F32) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F32) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F32)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F32 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(35)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_338 :: lane_underscore) (lane_2_260 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_338))) (the ((proj_lane__1 lane_2_260)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_104 :: iN). (mk_lane__0 (Jnn_Inn Inn_I32) (mk_uN (proj_uN_0 lane_3_104)))) ((list_zipWith (\<lambda> (lane_1_338 :: lane_underscore) (lane_2_260 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_lane__1 lane_1_338))) (the ((proj_lane__1 lane_2_260)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I32"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed

lemma fun_vrelop_underscore_case_35:
  assumes "wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))" "wf_uN 128 v128_1" "wf_uN 128 v128_2"
  shows "\<exists>r. fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 v_M vrelop_Fnn_N_GE) v128_1 v128_2 (Some r)"
proof -
  obtain xs0 where xs0: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1 = map (mk_lane__1 Fnn_F64) xs0"
      "\<forall>x\<in>set xs0. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs0 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_1] assms by blast
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2 = map (mk_lane__1 Fnn_F64) xs1"
      "\<forall>x\<in>set xs1. wf_fN (sizenn (numtype_Fnn Fnn_F64)) x" "length xs1 = v_M"
    using lanes_Fnn[of Fnn_F64 v_M v128_2] assms by blast
  show ?thesis
    apply (rule exI)
    apply (rule fun_vrelop_underscore.intros(36)[where lane_1_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)" and lane_2_lst = "(lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)" and lane_3_lst = "(list_zipWith (\<lambda> (lane_1_341 :: lane_underscore) (lane_2_263 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_341))) (the ((proj_lane__1 lane_2_263)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)))" and ?v128.0 = "(inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_107 :: iN). (mk_lane__0 (Jnn_Inn Inn_I64) (mk_uN (proj_uN_0 lane_3_107)))) ((list_zipWith (\<lambda> (lane_1_341 :: lane_underscore) (lane_2_263 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_lane__1 lane_1_341))) (the ((proj_lane__1 lane_2_263)))))))) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ((lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2))))))" and v_Inn = "Inn_I64"];
        (rule vt_list_intros)?)
    using assms xs0 xs1 by (auto simp: vt_case_simps intro!: vt_case_intros dest!: set_list_zipWithD)
qed



section \<open>Totality of the vector relations\<close>

lemmas vunop_cases = fun_vunop_underscore_case_0 fun_vunop_underscore_case_1 
  fun_vunop_underscore_case_2 fun_vunop_underscore_case_3 fun_vunop_underscore_case_4 
  fun_vunop_underscore_case_5 fun_vunop_underscore_case_6 fun_vunop_underscore_case_7 
  fun_vunop_underscore_case_8 fun_vunop_underscore_case_9 fun_vunop_underscore_case_10 
  fun_vunop_underscore_case_11 fun_vunop_underscore_case_12 fun_vunop_underscore_case_13 
  fun_vunop_underscore_case_14 fun_vunop_underscore_case_15 fun_vunop_underscore_case_16 
  fun_vunop_underscore_case_17 fun_vunop_underscore_case_18 fun_vunop_underscore_case_19 
  fun_vunop_underscore_case_20 fun_vunop_underscore_case_21 fun_vunop_underscore_case_22 
  fun_vunop_underscore_case_23 fun_vunop_underscore_case_24 fun_vunop_underscore_case_25 
  lemmas vbinop_cases = fun_vbinop_underscore_case_0 fun_vbinop_underscore_case_1 
  fun_vbinop_underscore_case_2 fun_vbinop_underscore_case_3 fun_vbinop_underscore_case_4 
  fun_vbinop_underscore_case_5 fun_vbinop_underscore_case_6 fun_vbinop_underscore_case_7 
  fun_vbinop_underscore_case_8 fun_vbinop_underscore_case_9 fun_vbinop_underscore_case_10 
  fun_vbinop_underscore_case_11 fun_vbinop_underscore_case_12 fun_vbinop_underscore_case_13 
  fun_vbinop_underscore_case_14 fun_vbinop_underscore_case_15 fun_vbinop_underscore_case_16 
  fun_vbinop_underscore_case_17 fun_vbinop_underscore_case_18 fun_vbinop_underscore_case_19 
  fun_vbinop_underscore_case_20 fun_vbinop_underscore_case_21 fun_vbinop_underscore_case_22 
  fun_vbinop_underscore_case_23 fun_vbinop_underscore_case_24 fun_vbinop_underscore_case_25 
  fun_vbinop_underscore_case_26 fun_vbinop_underscore_case_27 fun_vbinop_underscore_case_28 
  fun_vbinop_underscore_case_29 fun_vbinop_underscore_case_30 fun_vbinop_underscore_case_31 
  fun_vbinop_underscore_case_32 fun_vbinop_underscore_case_33 fun_vbinop_underscore_case_34 
  fun_vbinop_underscore_case_35 fun_vbinop_underscore_case_36 fun_vbinop_underscore_case_37 
  fun_vbinop_underscore_case_38 fun_vbinop_underscore_case_39 fun_vbinop_underscore_case_40 
  fun_vbinop_underscore_case_41 fun_vbinop_underscore_case_42 fun_vbinop_underscore_case_43 
  fun_vbinop_underscore_case_44 fun_vbinop_underscore_case_45 fun_vbinop_underscore_case_46 
  fun_vbinop_underscore_case_47 fun_vbinop_underscore_case_48 fun_vbinop_underscore_case_49 
  fun_vbinop_underscore_case_50 fun_vbinop_underscore_case_51 
  lemmas vrelop_cases = fun_vrelop_underscore_case_0 fun_vrelop_underscore_case_1 
  fun_vrelop_underscore_case_2 fun_vrelop_underscore_case_3 fun_vrelop_underscore_case_4 
  fun_vrelop_underscore_case_5 fun_vrelop_underscore_case_6 fun_vrelop_underscore_case_7 
  fun_vrelop_underscore_case_8 fun_vrelop_underscore_case_9 fun_vrelop_underscore_case_10 
  fun_vrelop_underscore_case_11 fun_vrelop_underscore_case_12 fun_vrelop_underscore_case_13 
  fun_vrelop_underscore_case_14 fun_vrelop_underscore_case_15 fun_vrelop_underscore_case_16 
  fun_vrelop_underscore_case_17 fun_vrelop_underscore_case_18 fun_vrelop_underscore_case_19 
  fun_vrelop_underscore_case_20 fun_vrelop_underscore_case_21 fun_vrelop_underscore_case_22 
  fun_vrelop_underscore_case_23 fun_vrelop_underscore_case_24 fun_vrelop_underscore_case_25 
  fun_vrelop_underscore_case_26 fun_vrelop_underscore_case_27 fun_vrelop_underscore_case_28 
  fun_vrelop_underscore_case_29 fun_vrelop_underscore_case_30 fun_vrelop_underscore_case_31 
  fun_vrelop_underscore_case_32 fun_vrelop_underscore_case_33 fun_vrelop_underscore_case_34 
  fun_vrelop_underscore_case_35 

(* For a fixed lane type, every operator has exactly one `Some` rule; dispatch to its case
   lemma.  `simp only:` substitutes the equations produced by `cases`, and `(no_asm)`
   rewrites the shape in the conclusion only, so it matches the case lemmas. *)
lemma vunop_Jnn_total:
  assumes "wf_shape (X (lanetype_Jnn J) (mk_dim M))" "wf_uN 128 v"
  shows "\<exists>r. fun_vunop_underscore (X (lanetype_Jnn J) (mk_dim M)) (mk_vunop__0 J M x) v (Some r)"
  using assms
  apply (cases J; cases x)
    apply (simp_all only:)
   apply (simp_all (no_asm) only: vt_simps)
  apply (rule vunop_cases; assumption)+
  done

lemma vunop_Fnn_total:
  assumes "wf_shape (X (lanetype_Fnn F) (mk_dim M))" "wf_uN 128 v"
  shows "\<exists>r. fun_vunop_underscore (X (lanetype_Fnn F) (mk_dim M)) (mk_vunop__1 F M x) v (Some r)"
  using assms
  apply (cases F; cases x)
    apply (simp_all only:)
   apply (simp_all (no_asm) only: vt_simps)
  apply (rule vunop_cases; assumption)+
  done

lemma vbinop_Jnn_total:
  assumes "wf_shape (X (lanetype_Jnn J) (mk_dim M))" "wf_uN 128 v1" "wf_uN 128 v2"
  shows "\<exists>r. fun_vbinop_underscore (X (lanetype_Jnn J) (mk_dim M)) (mk_vbinop__0 J M x) v1 v2 (Some r)"
  using assms
  apply (cases J; cases x)
    apply (simp_all only:)
   apply (simp_all (no_asm) only: vt_simps)
  apply (rule vbinop_cases; assumption)+
  done

lemma vbinop_Fnn_total:
  assumes "wf_shape (X (lanetype_Fnn F) (mk_dim M))" "wf_uN 128 v1" "wf_uN 128 v2"
  shows "\<exists>r. fun_vbinop_underscore (X (lanetype_Fnn F) (mk_dim M)) (mk_vbinop__1 F M x) v1 v2 (Some r)"
  using assms
  apply (cases F; cases x)
    apply (simp_all only:)
   apply (simp_all (no_asm) only: vt_simps)
  apply (rule vbinop_cases; assumption)+
  done

lemma vrelop_Jnn_total:
  assumes "wf_shape (X (lanetype_Jnn J) (mk_dim M))" "wf_uN 128 v1" "wf_uN 128 v2"
  shows "\<exists>r. fun_vrelop_underscore (X (lanetype_Jnn J) (mk_dim M)) (mk_vrelop__0 J M x) v1 v2 (Some r)"
  using assms
  apply (cases J; cases x)
    apply (simp_all only:)
   apply (simp_all (no_asm) only: vt_simps)
  apply (rule vrelop_cases; assumption)+
  done

lemma vrelop_Fnn_total:
  assumes "wf_shape (X (lanetype_Fnn F) (mk_dim M))" "wf_uN 128 v1" "wf_uN 128 v2"
  shows "\<exists>r. fun_vrelop_underscore (X (lanetype_Fnn F) (mk_dim M)) (mk_vrelop__1 F M x) v1 v2 (Some r)"
  using assms
  apply (cases F; cases x)
    apply (simp_all only:)
   apply (simp_all (no_asm) only: vt_simps)
  apply (rule vrelop_cases; assumption)+
  done

lemma vunop_total:
  assumes "wf_shape sh" "wf_vunop_underscore sh op" "wf_uN 128 v"
  shows "\<exists>r. fun_vunop_underscore sh op v (Some r)"
  using assms(2) by cases (use assms(1,3) vunop_Jnn_total vunop_Fnn_total in blast)+

lemma vbinop_total:
  assumes "wf_shape sh" "wf_vbinop_underscore sh op" "wf_uN 128 v1" "wf_uN 128 v2"
  shows "\<exists>r. fun_vbinop_underscore sh op v1 v2 (Some r)"
  using assms(2) by cases (use assms(1,3,4) vbinop_Jnn_total vbinop_Fnn_total in blast)+

lemma vrelop_total:
  assumes "wf_shape sh" "wf_vrelop_underscore sh op" "wf_uN 128 v1" "wf_uN 128 v2"
  shows "\<exists>r. fun_vrelop_underscore sh op v1 v2 (Some r)"
  using assms(2) by cases (use assms(1,3,4) vrelop_Jnn_total vrelop_Fnn_total in blast)+

lemma vshiftop_lane_ex:
  "\<exists>r. fun_vshiftop_underscore (mk_ishape (X (lanetype_Jnn J) (mk_dim M))) (mk_vshiftop__0 J M x)
     (mk_lane__0 J l) (mk_uN n) (Some r)"
  by (cases J; cases x; simp only:; simp (no_asm) only: vt_simps; blast intro: fun_vshiftop_underscore.intros)

lemma vshiftop_lane_some:
  "fun_vshiftop_underscore (mk_ishape (X (lanetype_Jnn J) (mk_dim M))) (mk_vshiftop__0 J M x)
     (mk_lane__0 J l) (mk_uN n) (Some (SOME r. fun_vshiftop_underscore
       (mk_ishape (X (lanetype_Jnn J) (mk_dim M))) (mk_vshiftop__0 J M x) (mk_lane__0 J l) (mk_uN n) (Some r)))"
  using vshiftop_lane_ex[of J M x l n] by (rule someI_ex)

lemma wf_ishape_form:
  assumes "wf_ishape sh"
  shows "\<exists>J N. sh = mk_ishape (X (lanetype_Jnn J) (mk_dim N)) \<and> wf_shape (X (lanetype_Jnn J) (mk_dim N))"
  using assms
proof cases
  case (ishape_case_0 s J)
  obtain lt d where s: "s = X lt d" by (cases s)
  obtain N where d: "d = mk_dim N" by (cases d)
  have "lt = lanetype_Jnn J" using ishape_case_0 s d by (simp add: vt_generic_simps)
  then show ?thesis using ishape_case_0 s d by blast
qed

lemma i32_num_form:
  assumes "wf_num_underscore I32 c"
  shows "\<exists>n. c = mk_num__0 Inn_I32 (mk_uN n) \<and> wf_uN 32 (mk_uN n)"
  using assms
proof cases
  case (num__case_0 inn x)
  then have "inn = Inn_I32" by (cases inn) (simp_all add: vt_simps)
  then show ?thesis using num__case_0 by (cases x) (auto simp: vt_simps)
next
  case (num__case_1 fnn x)
  then show ?thesis by (cases fnn) (simp_all add: vt_simps)
qed

section \<open>Lane extraction\<close>

lemma unpack_lane_some:
  assumes "wf_shape (X (lanetype_numtype nt) (mk_dim N))" "wf_uN 128 v" "k < N"
  shows "unpacknum_underscore (lanetype_numtype nt) (lanes_underscore (X (lanetype_numtype nt) (mk_dim N)) v ! k) \<noteq> None"
proof (cases nt)
  case I32
  then show ?thesis using lanes_Jnn[of Jnn_I32 N v] assms
    by (auto simp: vt_simps unpacknum_underscore.psimps unpacknum_underscore.domintros)
next
  case I64
  then show ?thesis using lanes_Jnn[of Jnn_I64 N v] assms
    by (auto simp: vt_simps unpacknum_underscore.psimps unpacknum_underscore.domintros)
next
  case F32
  then show ?thesis using lanes_Fnn[of Fnn_F32 N v] assms
    by (auto simp: vt_simps unpacknum_underscore.psimps unpacknum_underscore.domintros)
next
  case F64
  then show ?thesis using lanes_Fnn[of Fnn_F64 N v] assms
    by (auto simp: vt_simps unpacknum_underscore.psimps unpacknum_underscore.domintros)
qed

lemma pack_lane:
  assumes s: "wf_shape (X (lanetype_packtype pt) (mk_dim N))" and v: "wf_uN 128 v" and k: "k < N"
  shows "\<exists>x. lanes_underscore (X (lanetype_packtype pt) (mk_dim N)) v ! k = mk_lane__0 (Jnn_packtype pt) x
    \<and> wf_uN (psize pt) x"
proof -
  obtain J where J: "lanetype_packtype pt = lanetype_Jnn J" "Jnn_packtype pt = J"
      "lsize (lanetype_Jnn J) = psize pt"
    by (cases pt) (auto simp: vt_simps)
  obtain xs where xs: "lanes_underscore (X (lanetype_Jnn J) (mk_dim N)) v = map (mk_lane__0 J) xs"
      "\<forall>x\<in>set xs. wf_uN (lsize (lanetype_Jnn J)) x" "length xs = N"
    using lanes_Jnn[of J N v] s v J(1) by auto
  show ?thesis using xs J k bspec[OF xs(2) nth_mem[of k xs]] by auto
qed

section \<open>Lane-rearranging vector operations\<close>

lemma wf_shape_size: "wf_shape (X lt (mk_dim n)) \<Longrightarrow> lsize lt * n = 128"
  by (auto elim: wf_shape.cases simp: vt_generic_simps)

lemma wf_ishape_shape: "wf_ishape (mk_ishape s) \<Longrightarrow> wf_shape s"
  by (auto elim: wf_ishape.cases)

lemma concat_underscore_dom: "concat_underscore_dom ws"
  by (induction ws) (auto intro: concat_underscore.domintros)

lemma concat_underscore_eq: "concat_underscore ws = concat ws"
  by (induction ws) (simp_all add: concat_underscore.psimps[OF concat_underscore_dom])

(* An even-length list is the interleaving of two equally long lists. *)
lemma pair_split:
  assumes "even (length xs)"
  shows "\<exists>a b. length a = length b \<and> concat_underscore (list_zipWith (\<lambda>x y. [x, y]) a b) = xs
    \<and> set a \<subseteq> set xs \<and> set b \<subseteq> set xs"
  using assms
proof (induction xs rule: induct_list012)
  case 1
  then show ?case by (auto simp: list_zipWith_def concat_underscore_eq)
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y zs)
  then obtain a b where "length a = length b" "concat_underscore (list_zipWith (\<lambda>x y. [x, y]) a b) = zs"
      "set a \<subseteq> set zs" "set b \<subseteq> set zs"
    by auto
  then show ?case
    by (intro exI[of _ "x # a"] exI[of _ "y # b"]) (auto simp: list_zipWith_def concat_underscore_eq)
qed

(* The generated vbitmask rule spells the bit width 32 as a Suc chain. *)
lemma thirty_two: "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))) = (32::nat)"
  by simp

lemma set_repeat: "set (repeat n x) \<subseteq> {x}"
  by (induction n) auto

lemma nth_repeat: "i < n \<Longrightarrow> repeat n x ! i = x"
  by (induction n arbitrary: i) (auto simp: nth_Cons split: nat.split)

lemma set_list_slice: "set (list_slice xs n m) \<subseteq> set xs"
  by (induction xs n m rule: list_slice.induct) auto

lemma length_list_slice_min: "length (list_slice xs n m) = Orderings.min m (length xs - n)"
  by (induction xs n m rule: list_slice.induct) auto

lemma lanes_proj_some:
  "lanes_underscore sh v = map (mk_lane__0 J) xs \<Longrightarrow>
   list_all (\<lambda>ci. proj_lane__0 ci \<noteq> None) (lanes_underscore sh v)"
  by (simp add: list_all_iff vt_generic_simps)

(* After fixing the lane types, exactly one generated rule applies; its equational premises
   are closed by `refl` and the remaining ones are the facts passed in. *)
lemma vextunop_total:
  assumes op: "wf_vextunop__underscore ish1 ish2 op" and s: "wf_ishape ish1" "wf_ishape ish2"
    and v: "wf_uN 128 v"
  shows "\<exists>r. fun_vextunop__underscore ish1 ish2 op v (Some r)"
proof -
  from op obtain J1 M1 J2 M2 sx where e: "ish1 = mk_ishape (X (lanetype_Jnn J1) (mk_dim M1))"
      "ish2 = mk_ishape (X (lanetype_Jnn J2) (mk_dim M2))" "op = mk_vextunop___0 J1 M1 J2 M2 (EXTADD_PAIRWISE sx)"
    and sz: "2 * lsize (lanetype_Jnn J1) = lsize (lanetype_Jnn J2)"
    by (auto elim!: wf_vextunop__underscore.cases wf_vextunop__Jnn_1_M_1_Jnn_2_M_2.cases
        simp: vt_generic_simps)
  have s1: "wf_shape (X (lanetype_Jnn J1) (mk_dim M1))" and s2: "wf_shape (X (lanetype_Jnn J2) (mk_dim M2))"
    using s e by (auto intro: wf_ishape_shape)
  have M: "M1 = 2 * M2"
    using sz wf_shape_size[OF s1] wf_shape_size[OF s2] by (cases J1; cases J2) (auto simp: vt_simps)
  obtain xs where xs: "lanes_underscore (X (lanetype_Jnn J1) (mk_dim M1)) v = map (mk_lane__0 J1) xs"
      "\<forall>x\<in>set xs. wf_uN (lsize (lanetype_Jnn J1)) x" "length xs = M1"
    using lanes_Jnn[OF s1 v] by blast
  define ext where "ext = map (\<lambda>ci. extend__underscore (lsizenn1 (lanetype_Jnn J1))
    (lsizenn2 (lanetype_Jnn J2)) sx (the (proj_lane__0 ci))) (lanes_underscore (X (lanetype_Jnn J1) (mk_dim M1)) v)"
  have ext_wf: "\<forall>y\<in>set ext. wf_uN (lsize (lanetype_Jnn J2)) y"
    using xs(1,2) by (auto simp: ext_def vt_generic_simps intro: extend___is_wf[OF _ HOL.refl])
  obtain a b where ab: "length a = length b" "concat_underscore (list_zipWith (\<lambda>x y. [x, y]) a b) = ext"
      "set a \<subseteq> set ext" "set b \<subseteq> set ext"
    using pair_split[of ext] xs(1,3) M by (auto simp: ext_def)
  have wfab: "list_all2 (\<lambda>cj_1 cj_2. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn J2) (mk_dim M2)))
      (mk_lane__0 J2 (iadd_underscore (lsizenn2 (lanetype_Jnn J2)) cj_1 cj_2))) a b"
    using ab(1,3,4) ext_wf
    by (auto intro!: list_all2_setI lane__case_0 iadd__is_wf[OF _ _ HOL.refl] simp: vt_generic_simps)
  show ?thesis unfolding e
    using lanes_proj_some[OF xs(1)] ab(2)[unfolded ext_def] s1 s2 ab(1) wfab
    apply (cases J1; cases J2)
    apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule fun_vextunop__underscore.intros, (rule HOL.refl | assumption)+)+
    done
qed

lemma vextbinop_total:
  assumes op: "wf_vextbinop__underscore ish1 ish2 op" and s: "wf_ishape ish1" "wf_ishape ish2"
    and v: "wf_uN 128 v1" "wf_uN 128 v2"
  shows "\<exists>r. fun_vextbinop__underscore ish1 ish2 op v1 v2 (Some r)"
proof -
  from op obtain J1 M1 J2 M2 x where e: "ish1 = mk_ishape (X (lanetype_Jnn J1) (mk_dim M1))"
      "ish2 = mk_ishape (X (lanetype_Jnn J2) (mk_dim M2))" "op = mk_vextbinop___0 J1 M1 J2 M2 x"
    and sz: "2 * lsize (lanetype_Jnn J1) = lsize (lanetype_Jnn J2)"
    by (auto elim!: wf_vextbinop__underscore.cases wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.cases
        simp: vt_generic_simps)
  have s1: "wf_shape (X (lanetype_Jnn J1) (mk_dim M1))" and s2: "wf_shape (X (lanetype_Jnn J2) (mk_dim M2))"
    using s e by (auto intro: wf_ishape_shape)
  have M: "M1 = 2 * M2"
    using sz wf_shape_size[OF s1] wf_shape_size[OF s2] by (cases J1; cases J2) (auto simp: vt_simps)
  obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn J1) (mk_dim M1)) v1 = map (mk_lane__0 J1) xs1"
      "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn J1)) x" "length xs1 = M1"
    using lanes_Jnn[OF s1 v(1)] by blast
  obtain xs2 where xs2: "lanes_underscore (X (lanetype_Jnn J1) (mk_dim M1)) v2 = map (mk_lane__0 J1) xs2"
      "\<forall>x\<in>set xs2. wf_uN (lsize (lanetype_Jnn J1)) x" "length xs2 = M1"
    using lanes_Jnn[OF s1 v(2)] by blast
  let ?L1 = "lanes_underscore (X (lanetype_Jnn J1) (mk_dim M1)) v1"
  let ?L2 = "lanes_underscore (X (lanetype_Jnn J1) (mk_dim M1)) v2"
  (* the extended product of two lanes is well-formed at the wider lane size *)
  have prod_wf: "wf_uN (lsize (lanetype_Jnn J2)) (imul_underscore (lsize (lanetype_Jnn J2))
      (extend__underscore (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2)) s (the (proj_lane__0 a)))
      (extend__underscore (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2)) s (the (proj_lane__0 b))))"
    if "a \<in> set ?L1" "b \<in> set ?L2" for a b s
    using that xs1(1,2) xs2(1,2)
    by (auto simp: vt_generic_simps intro!: imul__is_wf[OF _ _ HOL.refl] extend___is_wf[OF _ HOL.refl])
  show ?thesis
  proof (cases x)
    case (EXTMUL h sx)
    let ?S1 = "list_slice ?L1 (fun_half h 0 M2) M2"
    let ?S2 = "list_slice ?L2 (fun_half h 0 M2) M2"
    have nn: "list_all (\<lambda>ci. proj_lane__0 ci \<noteq> None) ?S1" "list_all (\<lambda>ci. proj_lane__0 ci \<noteq> None) ?S2"
      using set_list_slice lanes_proj_some[OF xs1(1)] lanes_proj_some[OF xs2(1)]
      by (fastforce simp: list_all_iff)+
    have len: "length ?S1 = length ?S2" using xs1(1,3) xs2(1,3) by (simp add: length_list_slice_min)
    have wf: "list_all2 (\<lambda>ci_1 ci_2. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn J2) (mk_dim M2)))
        (mk_lane__0 J2 (imul_underscore (lsizenn2 (lanetype_Jnn J2))
          (extend__underscore (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx (the (proj_lane__0 ci_1)))
          (extend__underscore (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx (the (proj_lane__0 ci_2))))))
        ?S1 ?S2"
      using len by (auto intro!: list_all2_setI lane__case_0 prod_wf dest!: set_list_slice[THEN subsetD]
          simp: vt_generic_simps)
    show ?thesis unfolding e EXTMUL
      using nn s1 s2 len wf
      apply (cases J1; cases J2)
      apply (simp_all only:)
      apply (simp_all (no_asm) only: vt_simps)
      apply (rule exI, rule fun_vextbinop__underscore.intros, (rule HOL.refl | assumption)+)+
      done
  next
    case DOTS
    define prods where "prods = list_zipWith (\<lambda>ci_1 ci_2. imul_underscore (lsizenn2 (lanetype_Jnn J2))
      (extend__underscore (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) S (the (proj_lane__0 ci_1)))
      (extend__underscore (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) S (the (proj_lane__0 ci_2))))
      ?L1 ?L2"
    have prods_wf: "\<forall>y\<in>set prods. wf_uN (lsize (lanetype_Jnn J2)) y"
      by (auto simp: prods_def vt_generic_simps intro!: prod_wf dest!: set_list_zipWithD)
    obtain a b where ab: "length a = length b" "concat_underscore (list_zipWith (\<lambda>x y. [x, y]) a b) = prods"
        "set a \<subseteq> set prods" "set b \<subseteq> set prods"
      using pair_split[of prods] xs1(1,3) xs2(1,3) M by (auto simp: prods_def length_list_zipWith)
    have wfab: "list_all2 (\<lambda>cj_1 cj_2. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn J2) (mk_dim M2)))
        (mk_lane__0 J2 (iadd_underscore (lsizenn2 (lanetype_Jnn J2)) cj_1 cj_2))) a b"
      using ab(1,3,4) prods_wf
      by (auto intro!: list_all2_setI lane__case_0 iadd__is_wf[OF _ _ HOL.refl] simp: vt_generic_simps)
    show ?thesis unfolding e DOTS
      using lanes_proj_some[OF xs1(1)] lanes_proj_some[OF xs2(1)] ab(2)[unfolded prods_def] s1 s2 ab(1) wfab
      apply (cases J1; cases J2)
      apply (simp_all only:)
      apply (simp_all (no_asm) only: vt_simps)
      apply (rule exI, rule fun_vextbinop__underscore.intros, (rule HOL.refl | assumption)+)+
      done
  qed
qed

section \<open>Vector conversions\<close>

lemma setproduct2_dom: "setproduct2_underscore_dom (w, yss)"
  by (induction yss) (auto intro: setproduct2_underscore.domintros)

lemma setproduct1_dom: "setproduct1_underscore_dom (ws, yss)"
  by (induction ws) (auto intro: setproduct1_underscore.domintros)

lemma setproduct_dom: "setproduct_underscore_dom xss"
  by (induction xss) (auto intro: setproduct_underscore.domintros)

lemma setproduct2_nonempty: "yss \<noteq> [] \<Longrightarrow> setproduct2_underscore w yss \<noteq> []"
  by (cases yss) (simp_all add: setproduct2_underscore.psimps[OF setproduct2_dom])

lemma setproduct1_nonempty: "ws \<noteq> [] \<Longrightarrow> yss \<noteq> [] \<Longrightarrow> setproduct1_underscore ws yss \<noteq> []"
  by (cases ws) (simp_all add: setproduct1_underscore.psimps[OF setproduct1_dom] setproduct2_nonempty)

lemma setproduct_nonempty: "\<forall>xs\<in>set xss. xs \<noteq> [] \<Longrightarrow> setproduct_underscore xss \<noteq> []"
  by (induction xss) (simp_all add: setproduct_underscore.psimps[OF setproduct_dom] setproduct1_nonempty)

lemma list_underscore_nonempty: "x \<noteq> None \<Longrightarrow> list_underscore (map_option f x) \<noteq> []"
  by (cases x) (simp_all add: vt_generic_simps)

lemma zero_eq: "(z :: zero) = ZERO"
  by (cases z) simp

(* Every lane of a well-formed input converts to a non-empty list of output lanes. *)
lemma lcvtop_ex:
  assumes op: "wf_vcvtop__underscore sh1 sh2 op" and s: "wf_shape sh1" and v: "wf_uN 128 v"
    and l: "l \<in> set (lanes_underscore sh1 v)"
  shows "\<exists>ys. fun_lcvtop__underscore sh1 sh2 op l (Some ys) \<and> ys \<noteq> []"
  using op
proof cases
  case (vcvtop___case_0 J1 M1 J2 M2 x)
  then obtain i where "l = mk_lane__0 J1 i" using lanes_Jnn[of J1 M1 v] s v l by auto
  then show ?thesis using vcvtop___case_0
    apply (cases J1; cases J2; cases x)
                   apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule conjI, rule fun_lcvtop__underscore.intros, (rule HOL.refl)+, simp)+
    done
next
  case (vcvtop___case_1 J M1 F M2 x)
  then obtain i where "l = mk_lane__0 J i" using lanes_Jnn[of J M1 v] s v l by auto
  then show ?thesis using vcvtop___case_1
    apply (cases J; cases F; cases x)
           apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule conjI, rule fun_lcvtop__underscore.intros, (rule HOL.refl)+, simp)+
    done
next
  case (vcvtop___case_2 F M1 I M2 x)
  then obtain i where "l = mk_lane__1 F i" using lanes_Fnn[of F M1 v] s v l by auto
  then show ?thesis using vcvtop___case_2
    apply (cases F; cases I; cases x)
       apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule conjI, rule fun_lcvtop__underscore.intros, (rule HOL.refl)+,
        simp add: list_underscore_nonempty float_cvt_nonempty)+
    done
next
  case (vcvtop___case_3 F1 M1 F2 M2 x)
  then obtain i where "l = mk_lane__1 F1 i" using lanes_Fnn[of F1 M1 v] s v l by auto
  moreover have "x = vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO \<or> x = PROMOTELOW"
    by (cases x) (simp_all add: zero_eq)
  ultimately show ?thesis using vcvtop___case_3
    apply (cases F1; cases F2; elim disjE)
           apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule conjI, rule fun_lcvtop__underscore.intros, (rule HOL.refl)+,
        simp add: float_cvt_nonempty)+
    done
qed

(* The half/zero selectors are never both set, and when neither is, the shapes have the same
   number of lanes (the conversion is lane-by-lane). *)
lemma vcvtop_halfop_zeroop:
  assumes op: "wf_vcvtop__underscore sh1 sh2 op" and s: "wf_shape sh1" "wf_shape sh2"
  shows "\<exists>h z. fun_halfop sh1 sh2 op (Some h) \<and> fun_zeroop sh1 sh2 op (Some z) \<and> (h = None \<or> z = None)
    \<and> (h = None \<and> z = None \<longrightarrow> (\<exists>lt1 lt2 M. sh1 = X lt1 (mk_dim M) \<and> sh2 = X lt2 (mk_dim M)))"
  using op
proof cases
  case (vcvtop___case_0 J1 M1 J2 M2 x)
  then show ?thesis
    apply (cases J1; cases J2; cases x)
                   apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule exI, intro conjI,
        (rule fun_halfop.intros fun_zeroop.intros, (rule HOL.refl)+)+, simp, simp)+
    done
next
  case (vcvtop___case_1 J M1 F M2 x)
  (* converting without a half needs equal lane sizes, hence equal lane counts *)
  obtain ho sx where x: "x = vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT ho sx" by (cases x)
  have dim: "M1 = M2" if "ho = None"
    using that vcvtop___case_1 x s wf_shape_size[of "lanetype_Jnn J" M1] wf_shape_size[of "lanetype_Fnn F" M2]
    by (cases J; cases F) (auto elim!: wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2.cases simp: vt_all_simps)
  show ?thesis using vcvtop___case_1 x dim
    apply (cases J; cases F)
           apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule exI, intro conjI,
        (rule fun_halfop.intros fun_zeroop.intros, (rule HOL.refl)+)+, simp, simp)+
    done
next
  case (vcvtop___case_2 F M1 I M2 x)
  obtain sx zo where x: "x = vcvtop__Fnn_1_M_1_Inn_2_M_2_TRUNC_SAT sx zo" by (cases x)
  have dim: "M1 = M2" if "zo = None"
    using that vcvtop___case_2 x s wf_shape_size[of "lanetype_Fnn F" M1] wf_shape_size[of "lanetype_Inn I" M2]
    by (cases F; cases I) (auto elim!: wf_vcvtop__Fnn_1_M_1_Inn_2_M_2.cases simp: vt_all_simps)
  show ?thesis using vcvtop___case_2 x dim
    apply (cases F; cases I)
       apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule exI, intro conjI,
        (rule fun_halfop.intros fun_zeroop.intros, (rule HOL.refl)+)+, simp, simp)+
    done
next
  case (vcvtop___case_3 F1 M1 F2 M2 x)
  moreover have "x = vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO \<or> x = PROMOTELOW"
    by (cases x) (simp_all add: zero_eq)
  ultimately show ?thesis
    apply (cases F1; cases F2; elim disjE)
           apply (simp_all only:)
    apply (simp_all (no_asm) only: vt_simps)
    apply (rule exI, rule exI, intro conjI,
        (rule fun_halfop.intros fun_zeroop.intros, (rule HOL.refl)+)+, simp, simp)+
    done
qed

lemma vcvtop_total:
  assumes op: "wf_vcvtop__underscore sh1 sh2 op" and s: "wf_shape sh1" "wf_shape sh2"
    and v: "wf_uN 128 v"
  shows "\<exists>r. fun_vcvtop__underscore sh1 sh2 op v (Some r)"
proof -
  define f where "f = (\<lambda>l. SOME ys. fun_lcvtop__underscore sh1 sh2 op l (Some ys) \<and> ys \<noteq> [])"
  have f: "fun_lcvtop__underscore sh1 sh2 op l (Some (f l)) \<and> f l \<noteq> []"
    if "l \<in> set (lanes_underscore sh1 v)" for l
    unfolding f_def using lcvtop_ex[OF op s(1) v that] by (rule someI_ex)
  obtain h z where H: "fun_halfop sh1 sh2 op (Some h)" and Z: "fun_zeroop sh1 sh2 op (Some z)"
      and hz: "h = None \<or> z = None"
      and dim: "h = None \<Longrightarrow> z = None \<Longrightarrow> \<exists>lt1 lt2 M. sh1 = X lt1 (mk_dim M) \<and> sh2 = X lt2 (mk_dim M)"
    using vcvtop_halfop_zeroop[OF op s] by blast
  obtain lt1 M1 where sh1: "sh1 = X lt1 (mk_dim M1)" by (metis shape.exhaust dim.exhaust)
  obtain lt2 M2 where sh2: "sh2 = X lt2 (mk_dim M2)" by (metis shape.exhaust dim.exhaust)
  (* for any selection C of input lanes, convert each lane and take one combination *)
  have conv: "length (map (\<lambda>l. Some (f l)) C) = length C"
      "list_all2 (\<lambda>var c. fun_lcvtop__underscore sh1 sh2 op c var) (map (\<lambda>l. Some (f l)) C) C"
      "list_all (\<lambda>var. var \<noteq> None) (map (\<lambda>l. Some (f l)) C)"
      "\<forall>ys\<in>set (map the (map (\<lambda>l. Some (f l)) C)). ys \<noteq> []"
    if "set C \<subseteq> set (lanes_underscore sh1 v)" for C
    using that f by (auto intro!: list_all2_mapI simp: list_all_iff)
  show ?thesis
  proof (cases h)
    case (Some hv)
    let ?C = "list_slice (lanes_underscore (X lt1 (mk_dim M1)) v) (fun_half hv 0 M2) M2"
    let ?P = "setproduct_underscore (map the (map (\<lambda>l. Some (f l)) ?C))"
    have C: "set ?C \<subseteq> set (lanes_underscore sh1 v)" using set_list_slice sh1 by simp
    have "?P \<noteq> []" using setproduct_nonempty conv(4)[OF C] by blast
    then have P: "0 < length (map (inv_lanes_underscore (X lt2 (mk_dim M2))) ?P)"
        "hd (map (inv_lanes_underscore (X lt2 (mk_dim M2))) ?P) \<in> set (map (inv_lanes_underscore (X lt2 (mk_dim M2))) ?P)"
      using hd_in_set[of "map (inv_lanes_underscore (X lt2 (mk_dim M2))) ?P"] by simp_all
    have opt: "Some (Some hv) \<noteq> None" "the (Some (Some hv)) = Some hv" by simp_all
    from conv[OF C] H[unfolded Some] opt P s
    show ?thesis unfolding sh1 sh2
      apply -
      apply (rule exI, rule fun_vcvtop__underscore.intros(2))
                apply (rule HOL.refl | assumption)+
      done
  next
    case None
    then have z: "z = None \<or> z = Some ZERO" using zero_eq by (cases z) auto
    then show ?thesis
    proof
      assume z0: "z = Some ZERO"
      let ?C = "lanes_underscore (X lt1 (mk_dim M1)) v"
      let ?p = "the (packnum_underscore lt2 (fun_zero (unpack lt2)))"
      let ?P = "setproduct_underscore (map the (map (\<lambda>l. Some (f l)) ?C) @ repeat M1 [?p])"
      have C: "set ?C \<subseteq> set (lanes_underscore sh1 v)" using sh1 by simp
      have pk: "packnum_underscore lt2 (fun_zero (unpack lt2)) \<noteq> None"
        using packnum_not_None zero_is_wf[OF HOL.refl] by blast
      have "\<forall>ys\<in>set (map the (map (\<lambda>l. Some (f l)) ?C) @ repeat M1 [?p]). ys \<noteq> []"
        using conv(4)[OF C] set_repeat[of M1 "[?p]"] by auto
      then have "?P \<noteq> []" by (rule setproduct_nonempty)
      then have P: "0 < length (map (inv_lanes_underscore (X lt2 (mk_dim M2))) ?P)"
          "hd (map (inv_lanes_underscore (X lt2 (mk_dim M2))) ?P) \<in> set (map (inv_lanes_underscore (X lt2 (mk_dim M2))) ?P)"
        using hd_in_set[of "map (inv_lanes_underscore (X lt2 (mk_dim M2))) ?P"] by simp_all
      have opt: "Some (Some ZERO) \<noteq> None" "the (Some (Some ZERO)) = Some ZERO" by simp_all
      from conv[OF C] Z[unfolded z0] opt pk P s
      show ?thesis unfolding sh1 sh2
        apply -
        apply (rule exI, rule fun_vcvtop__underscore.intros(3))
                    apply (rule HOL.refl | assumption)+
        done
    next
      assume z0: "z = None"
      then obtain lt1' lt2' M where e: "sh1 = X lt1' (mk_dim M)" "sh2 = X lt2' (mk_dim M)"
        using dim None by blast
      let ?C = "lanes_underscore (X lt1' (mk_dim M)) v"
      let ?P = "setproduct_underscore (map the (map (\<lambda>l. Some (f l)) ?C))"
      have C: "set ?C \<subseteq> set (lanes_underscore sh1 v)" using e by simp
      have "?P \<noteq> []" using setproduct_nonempty conv(4)[OF C] by blast
      then have P: "0 < length (map (inv_lanes_underscore (X lt2' (mk_dim M))) ?P)"
          "hd (map (inv_lanes_underscore (X lt2' (mk_dim M))) ?P) \<in> set (map (inv_lanes_underscore (X lt2' (mk_dim M))) ?P)"
        using hd_in_set[of "map (inv_lanes_underscore (X lt2' (mk_dim M))) ?P"] by simp_all
      have opt: "Some (None :: half option) \<noteq> None" "Some (None :: zero option) \<noteq> None"
          "the (Some (None :: half option)) = None \<and> the (Some (None :: zero option)) = None" by simp_all
      from conv[OF C] H[unfolded None] Z[unfolded z0] opt P s
      show ?thesis unfolding e
        apply -
        apply (rule exI, rule fun_vcvtop__underscore.intros(1))
                      apply (rule HOL.refl | assumption)+
        done
    qed
  qed
qed


theorem progress:
  assumes "Config_ok (mk_config s es) ts"
  shows "\<exists>cfg'. Step (mk_config s es) cfg' \<or> es = [admininstr_sc7 admininstr_st7_TRAP] \<or> (\<exists>vs. es = map admininstr_val vs)"
  using assms proof(induction "mk_config s es" ts)
  case (mk_Config_ok s' f C t_lst)
  then have stok: "State_ok (mk_state s' f) (strip C)" "C = strip C" using State_ok_strip by auto
  then have notbr: "not_br_return es" using typecheck_strip_not_return mk_Config_ok by auto
  show ?case using mk_Config_ok(2) stok(1) notbr mk_Config_ok(3-)
  proof (induction s' C es "mk_list t_lst" 
          arbitrary: s t_lst f
        rule:Instr_ok2_Instrs_ok2_Expr_ok2.inducts(3)[where
      ?P1.0 = "\<lambda> s' C e t. (case t of mk_functype (mk_list t1) t2 \<Rightarrow> 
        (\<forall> vs f. ((list_all2 Valtype_sub (map typeofval vs) t1) \<longrightarrow> 
            (list_all wf_val vs) \<longrightarrow> 
          (State_ok (mk_state s' f) (strip C)) \<longrightarrow> not_br_return [e] \<longrightarrow> (wf_context C) \<longrightarrow>
         wf_config (mk_config (mk_state s' f) [e]) \<longrightarrow>
           wf_state (mk_state s' f) \<longrightarrow> (\<exists> cfg'.
       Step (mk_config (mk_state s' f) (map admininstr_val vs @ [e])) cfg' \<or>
       e = admininstr_sc7 admininstr_st7_TRAP \<or> (\<exists>v. e = admininstr_val v)))))" and 
      ?P2.0 = "\<lambda> s' C es t. (case t of mk_functype (mk_list t1) t2 \<Rightarrow> 
        (\<forall> vs f. (list_all2 Valtype_sub (map typeofval vs) t1 \<longrightarrow> (list_all wf_val vs) \<longrightarrow> 
        (State_ok (mk_state s' f) (strip C)) \<longrightarrow> not_br_return es \<longrightarrow> (wf_context C) \<longrightarrow>
         wf_config (mk_config (mk_state s' f) es) \<longrightarrow>
           wf_state (mk_state s' f) \<longrightarrow> (\<exists> cfg'.
       Step (mk_config (mk_state s' f) (map admininstr_val vs @ es)) cfg' \<or>
       es = [admininstr_sc7 admininstr_st7_TRAP] \<or> (\<exists>vs. es = map admininstr_val vs)))))"])
    case (plain C v_instr t_1_lst t_2_lst s')
    then show ?case
      apply(auto)
      subgoal for vs f
      proof - 
        assume 
          "Instr_ok C v_instr (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
          "wf_store s'"
          "wf_context C"
          "wf_instr v_instr"
          "list_all2 Valtype_sub (map typeofval vs) t_1_lst"
          "list_all wf_val vs"
          "State_ok (mk_state s' f) (strip C)"
          "not_br_return [admininstr_instr v_instr]"
          "wf_config (mk_config (mk_state s' f) [admininstr_instr v_instr])"
          "wf_state (mk_state s' f)"
          "\<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ [admininstr_instr v_instr])) x"
          "\<forall>v. admininstr_instr v_instr \<noteq> admininstr_val v" 
        then have "False" (* show "admininstr_instr v_instr = admininstr_sc7 admininstr_st7_TRAP"  *)
        proof(induction C v_instr "mk_functype (mk_list t_1_lst) (mk_list t_2_lst)" 
        arbitrary: t_1_lst t_2_lst vs f
        rule: Instr_ok_Instrs_ok.inducts(1)[where
        ?P2.0 = "\<lambda> C es t. (case t of mk_functype (mk_list t1) t2 \<Rightarrow>
        \<forall> vs f.
            wf_store s' \<longrightarrow>
        wf_context C \<longrightarrow>
    list_all wf_instr es \<longrightarrow>
    list_all2 Valtype_sub (map typeofval vs) t1 \<longrightarrow>
    list_all wf_val vs \<longrightarrow>
    State_ok (mk_state s' f) (strip C) \<longrightarrow> not_br_return (map admininstr_instr es) \<longrightarrow>
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
      have "Store_ok s'" using unreachable(8) proof(induction "mk_state s' f" "strip C'") qed(auto)
      then show ?case using 
          reducible_left_v[of s' f "[admininstr_instr (instr_sc0 UNREACHABLE)]" vs]  
          Step.intros(1)[OF Step_pure.intros(1)]
        admininstr_case_73 config_case_0 unreachable
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
      case (select_impl t t' v_numtype v_vectype C')
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
                     Step_pure.intros(5)[of c' a b "None"] admininstr_val.domintros
                     admininstr_val.psimps valtype_numtype.domintros valtype_numtype.psimps 
                   by fastforce 
               next
                 case (Suc nat)
                 then show ?thesis using projc Nil c Step.intros(1) 
                     Step_pure.intros(4)[of c' a b "None"] admininstr_val.domintros
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
      case (block C' bt t_1_lst t_2_lst instr_lst)
      have bt: "fun_blocktype (mk_state s' f) bt = mk_functype
                    (mk_list t_1_lst) (mk_list t_2_lst)"
        using block(12) blocktype_ok_agree[OF block(1)]
      proof(induction "mk_state s' f" "strip C'")
        case (mk_State_ok)
        show ?case using mk_State_ok(2,1,3-) proof(induction s' f "strip C'")
          case (mk_Frame_ok s v_moduleinst C''' t_lst val_lst)
          have "t_inst_match C'''
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = t_lst, LABELS = [],
          context_RETURN = None\<rparr> C''')" proof(cases C''')
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
         Step.intros(2) block(16)
        by fastforce
    next
      case (loop C' bt t_1_lst t_2_lst instr_lst)
      have bt: "fun_blocktype (mk_state s' f) bt = mk_functype
                    (mk_list t_1_lst) (mk_list t_2_lst)"
        using loop(12) blocktype_ok_agree[OF loop(1)]
      proof(induction "mk_state s' f" "strip C'")
        case (mk_State_ok)
        show ?case using mk_State_ok(2,1,3-) proof(induction s' f "strip C'")
          case (mk_Frame_ok s v_moduleinst C''' t_lst val_lst)
          have "t_inst_match C'''
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = t_lst, LABELS = [],
          context_RETURN = None\<rparr> C''')" proof(cases C''')
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
      show ?case using loop(10) list_all2_lengthD 
          Step_read__loop[OF bt, of "length vs" vs "length t_2_lst" instr_lst] 
         Step.intros(2) loop(16)
        by fastforce
    next
      case (res_if C' bt t_1_lst t_2_lst instr_1_lst instr_2_lst)
      have stok: "Store_ok s'" using res_if(14) proof(induction "mk_state s' f" "strip C'") qed(auto)
      obtain ts1 ts2 where ts: "map typeofval vs = ts1 @ ts2" "list_all2 Valtype_sub ts1 t_1_lst" 
        "list_all2 Valtype_sub ts2 [valtype_I32]" 
        using list_all2_append2 res_if(12)
        by meson
      then obtain vs1 vs2 where vs: "vs = vs1 @ vs2" "map typeofval vs1 = ts1" "map typeofval vs2 = ts2" 
        using map_is_app by blast
      obtain t where ts2: "ts2 = [t]" using ts(3)
        by (metis ts(3) list.exhaust list_all2_Cons2 list.rel_distinct(2))
      then obtain c where c: "vs2 = [val_CONST I32 c]" using ts(3) typeofval_is_i32 vs(3)
        by blast
      have "wf_val (val_CONST I32 c)" using res_if vs c by simp
      then have projc: "proj_num__0 c \<noteq> None" using c proof(induction "val_CONST I32 c")
                 case (val_case_0)
                 then show ?case proof(induction I32 c)
                   case (num__case_0 v_Inn var_x)
                   then show ?case using proj_num__0.psimps proj_num__0.domintros
                     by fast
                 next
                   case (num__case_1 v_Fnn var_x)
                   then have "False"
                   proof(cases v_Fnn)
                     case Fnn_F32
                     then show ?thesis using num__case_1(2)
                        by (simp add: numtype_Fnn.domintros(1) numtype_Fnn.psimps(1)) 
                   next
                     case Fnn_F64
                     then show ?thesis using num__case_1(2)
                       by (simp add: numtype_Fnn.domintros(2) numtype_Fnn.psimps(2)) 
                   qed
                   then show ?case by simp
                 qed
               qed      
               have wfc: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 c))"
                   using res_if(13) vs c wf_admininstr_val admininstr_val.domintros 
        admininstr_val.psimps
                   by fastforce
                 have wfc: "wf_config
     (mk_config (mk_state s' f) [admininstr_sc1 (admininstr_st1_CONST I32 c), 
            admininstr_sc0 (admininstr_st0_IFELSE bt instr_1_lst instr_2_lst)])"
                   using res_if(16) wfc
                 proof(induction "mk_config (mk_state s' f) [admininstr_instr 
                        (instr_sc7 (IFELSE bt instr_1_lst instr_2_lst))]")
                   case config_case_0
                   then show ?case using isabelle_reference_output_wasm2.config_case_0
                     by auto
                 qed
                 have vs: "map admininstr_val vs = map admininstr_val vs1 @ [admininstr_sc1 
                      (admininstr_st1_CONST I32 c)]"
                   using vs(1) c admininstr_val.domintros(1) 
                      admininstr_val.psimps(1)
                   by simp
               show ?case proof(cases "proj_uN_0 (the (proj_num__0 c))")
                 case 0
                 show ?thesis using if_false[OF projc 0] res_if(18)
                     Step.intros(1) reducible_left_v[OF _ wfc] vs stok
                   by fastforce
               next
                 case (Suc nat)
                 then show ?thesis using if_true[OF projc] res_if(18)
                     Step.intros(1) reducible_left_v[OF _ wfc] vs stok
                   by fastforce
               qed
    next
      case (br l C t_lst t_1_lst)
      show ?case using br(11) not_br_return_def
        by force
    next
      case (br_if l C t_lst)
      have stok: "Store_ok s'" using br_if(10) proof(induction "mk_state s' f" "strip C") qed(auto)
      obtain ts1 ts2 where ts: "map typeofval vs = ts1 @ ts2" "list_all2 Valtype_sub ts1 t_lst" 
        "list_all2 Valtype_sub ts2 [valtype_I32]" 
        using list_all2_append2 br_if(8)
        by meson
      then obtain vs1 vs2 where vs: "vs = vs1 @ vs2" "map typeofval vs1 = ts1" "map typeofval vs2 = ts2" 
        using map_is_app by blast
      obtain t where ts2: "ts2 = [t]" using ts(3)
        by (metis ts(3) list.exhaust list_all2_Cons2 list.rel_distinct(2))
      then obtain c where c: "vs2 = [val_CONST I32 c]" using ts(3) typeofval_is_i32 vs(3)
        by blast
      have "wf_val (val_CONST I32 c)" using br_if vs c by simp
      then have projc: "proj_num__0 c \<noteq> None" using c proof(induction "val_CONST I32 c")
                 case (val_case_0)
                 then show ?case proof(induction I32 c)
                   case (num__case_0 v_Inn var_x)
                   then show ?case using proj_num__0.psimps proj_num__0.domintros
                     by fast
                 next
                   case (num__case_1 v_Fnn var_x)
                   then have "False"
                   proof(cases v_Fnn)
                     case Fnn_F32
                     then show ?thesis using num__case_1(2)
                        by (simp add: numtype_Fnn.domintros(1) numtype_Fnn.psimps(1)) 
                   next
                     case Fnn_F64
                     then show ?thesis using num__case_1(2)
                       by (simp add: numtype_Fnn.domintros(2) numtype_Fnn.psimps(2)) 
                   qed
                   then show ?case by simp
                 qed
               qed
      have wfc: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 c))"
                   using br_if(9) vs c wf_admininstr_val admininstr_val.domintros 
        admininstr_val.psimps
                   by fastforce
                 have wfc: "wf_config
     (mk_config (mk_state s' f) [admininstr_sc1 (admininstr_st1_CONST I32 c), 
            admininstr_sc0 (admininstr_st0_BR_IF l)])"
                   using br_if(12) wfc
                 proof(induction "mk_config (mk_state s' f) [admininstr_instr 
                        (instr_sc0 (BR_IF l))]")
                   case config_case_0
                   then show ?case using isabelle_reference_output_wasm2.config_case_0
                     by auto
                 qed
                 have vs: "map admininstr_val vs = map admininstr_val vs1 @ [admininstr_sc1 
                      (admininstr_st1_CONST I32 c)]"
                   using vs(1) c admininstr_val.domintros(1) 
                      admininstr_val.psimps(1)
                   by simp
               show ?case proof(cases "proj_uN_0 (the (proj_num__0 c))")
                 case 0
                 show ?thesis using br_if_false[OF projc 0] br_if(14)
                     Step.intros(1) reducible_left_v[OF _ wfc] vs stok
                   by fastforce
               next
                 case (Suc nat)
                 then show ?thesis using br_if_true[OF projc] br_if(14)
                     Step.intros(1) reducible_left_v[OF _ wfc] vs stok
                   by fastforce
               qed
    next
      case (br_table C l_lst t_lst l' t_1_lst)
      have stok: "Store_ok s'" using br_table(12) proof(induction "mk_state s' f" "strip C") qed(auto)
      obtain ts1 ts2 where ts: "map typeofval vs = ts1 @ ts2" "list_all2 Valtype_sub ts1 (t_1_lst @ t_lst)" 
        "list_all2 Valtype_sub ts2 [valtype_I32]" 
        using list_all2_append2 br_table(10) append_assoc
        by metis
      then obtain vs1 vs2 where vs: "vs = vs1 @ vs2" "map typeofval vs1 = ts1" "map typeofval vs2 = ts2" 
        using map_is_app by blast
      obtain t where ts2: "ts2 = [t]" using ts(3)
        by (metis ts(3) list.exhaust list_all2_Cons2 list.rel_distinct(2))
      then obtain c where c: "vs2 = [val_CONST I32 c]" using ts(3) typeofval_is_i32 vs(3)
        by blast
      have "wf_val (val_CONST I32 c)" using br_table vs c by simp
      then have projc: "proj_num__0 c \<noteq> None" using c proof(induction "val_CONST I32 c")
                 case (val_case_0)
                 then show ?case proof(induction I32 c)
                   case (num__case_0 v_Inn var_x)
                   then show ?case using proj_num__0.psimps proj_num__0.domintros
                     by fast
                 next
                   case (num__case_1 v_Fnn var_x)
                   then have "False"
                   proof(cases v_Fnn)
                     case Fnn_F32
                     then show ?thesis using num__case_1(2)
                        by (simp add: numtype_Fnn.domintros(1) numtype_Fnn.psimps(1)) 
                   next
                     case Fnn_F64
                     then show ?thesis using num__case_1(2)
                       by (simp add: numtype_Fnn.domintros(2) numtype_Fnn.psimps(2)) 
                   qed
                   then show ?case by simp
                 qed
               qed
      have wfc: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 c))"
                   using br_table(11) vs c wf_admininstr_val admininstr_val.domintros 
        admininstr_val.psimps
                   by fastforce
                 have wfc: "wf_config
     (mk_config (mk_state s' f) [admininstr_sc1 (admininstr_st1_CONST I32 c), 
            admininstr_sc1 (admininstr_st1_BR_TABLE l_lst l')])"
                   using br_table(14) wfc
                 proof(induction "mk_config (mk_state s' f) [admininstr_instr 
                        (instr_sc0 (BR_TABLE l_lst l'))]")
                   case config_case_0
                   then show ?case using isabelle_reference_output_wasm2.config_case_0
                     by auto
                 qed
                 have vs: "map admininstr_val vs = map admininstr_val vs1 @ [admininstr_sc1 
                      (admininstr_st1_CONST I32 c)]"
                   using vs(1) c admininstr_val.domintros(1) 
                      admininstr_val.psimps(1)
                   by simp
               show ?case proof(cases "proj_uN_0 (the (proj_num__0 c)) < length l_lst")
                 case True
                 show ?thesis using br_table_lt[OF True projc] br_table(16)
                     Step.intros(1) reducible_left_v[OF _ wfc] vs stok
                   by fastforce
               next
                 case False
                 then have "length l_lst \<le> proj_uN_0 (the (proj_num__0 c))"
                   by simp
                 then show ?thesis using br_table_ge[OF projc] br_table(16)
                     Step.intros(1) reducible_left_v[OF _ wfc] vs stok
                   by fastforce
               qed
    next
      case (call x C' t_1_lst t_2_lst)
      have stok: "Store_ok s'" using call(10) proof(induction "mk_state s' f" "strip C'") qed(auto)
      have "length (context_FUNCS C') = length (fun_funcaddr (mk_state s' f))"
        using call(10) proof(induction "mk_state s' f" "strip C'")
        case mk_State_ok
        show ?case using mk_State_ok(2) proof(induction s' f "strip C'")
          case (mk_Frame_ok s v_moduleinst C t_lst val_lst)
          show ?case using mk_Frame_ok(1,8) proof(induction s v_moduleinst C)
            case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
                  functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
                  dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
            show ?case using mk_Moduleinst_ok(4,27) append_res_context_def strip_def
              fun_funcaddr.domintros fun_funcaddr.psimps
              by simp 
          qed
        qed
      qed
      then show ?case using Step_read__call call(1,14) Step.intros(2) 
          reducible_left_v[OF _ call(12)] stok
        by fastforce
    next
      case (call_indirect x C lim y t_1_lst)
      obtain ts1 ts2 where ts: "map typeofval vs = ts1 @ ts2" "list_all2 Valtype_sub ts1 t_1_lst" 
        "list_all2 Valtype_sub ts2 [valtype_I32]" 
        using list_all2_append2 call_indirect(11)
        by meson
      then obtain vs1 vs2 where vs: "vs = vs1 @ vs2" "map typeofval vs1 = ts1" "map typeofval vs2 = ts2" 
        using map_is_app by blast
      obtain t where ts2: "ts2 = [t]" using ts(3)
        by (metis ts(3) list.exhaust list_all2_Cons2 list.rel_distinct(2))
      then obtain c where c: "vs2 = [val_CONST I32 c]" using ts(3) typeofval_is_i32 vs(3)
        by blast
      have "wf_val (val_CONST I32 c)" using call_indirect vs c by simp
      then have projc: "proj_num__0 c \<noteq> None" using c proof(induction "val_CONST I32 c")
                 case (val_case_0)
                 then show ?case proof(induction I32 c)
                   case (num__case_0 v_Inn var_x)
                   then show ?case using proj_num__0.psimps proj_num__0.domintros
                     by fast
                 next
                   case (num__case_1 v_Fnn var_x)
                   then have "False"
                   proof(cases v_Fnn)
                     case Fnn_F32
                     then show ?thesis using num__case_1(2)
                        by (simp add: numtype_Fnn.domintros(1) numtype_Fnn.psimps(1)) 
                   next
                     case Fnn_F64
                     then show ?thesis using num__case_1(2)
                       by (simp add: numtype_Fnn.domintros(2) numtype_Fnn.psimps(2)) 
                   qed
                   then show ?case by simp
                 qed
               qed  
               have wfc: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 c))"
                   using call_indirect(12) vs c wf_admininstr_val admininstr_val.domintros 
        admininstr_val.psimps
                   by fastforce
                 have wfc: "wf_config
     (mk_config (mk_state s' f) [admininstr_sc1 (admininstr_st1_CONST I32 c), 
            admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)])"
                   using call_indirect(15) wfc
                 proof(induction "mk_config (mk_state s' f) [admininstr_instr 
                        (instr_sc0 (CALL_INDIRECT x y))]")
                   case config_case_0
                   then show ?case using isabelle_reference_output_wasm2.config_case_0
                     by auto
                 qed
                 have vs: "map admininstr_val vs = map admininstr_val vs1 @ [admininstr_sc1 
                      (admininstr_st1_CONST I32 c)]"
                   using vs(1) c admininstr_val.domintros(1) 
                      admininstr_val.psimps(1)
                   by simp
      show ?case proof(cases "Step_read_before_call_indirect_trap
      (mk_config (mk_state s' f)
        [admininstr_sc1 (admininstr_st1_CONST I32 c),
         admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)])")
        case True
        then show ?thesis proof(induction "mk_config
          (mk_state s' f)
       [admininstr_sc1 (admininstr_st1_CONST I32 c), admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)]")
          case (call_indirect_call_0 a)
         have "Store_ok s'" using call_indirect(13) proof(induction "mk_state s' f" "strip C") qed(auto)
        then show ?case using Step.intros(2)[OF call_indirect_call[OF call_indirect_call_0(1-5)]] 
              reducible_left_v[of s' f "[_,_]" vs1] wfc
            call_indirect(17) vs
            by auto
        qed
      next
        case False
        have "Store_ok s'" using call_indirect(13) proof(induction "mk_state s' f" "strip C") qed(auto)
        then show ?thesis using Step.intros(2)[OF call_indirect_trap[OF False]] call_indirect(17)  
          vs reducible_left_v[of s' f "[_,_]" vs1] wfc
          by auto
      qed
    next
      case (return C t_lst t_1_lst)
      then show ?case using not_br_return_def by fastforce
    next
      case (const C nt c_nt)
      then show ?case using admininstr_val.domintros(1) admininstr_val.psimps(1)[of nt c_nt]
         by (metis admininstr_instr.simps(14))
    next
      case (unop C nt unop_nt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain c where c: "a = val_CONST nt c" using typeofval_is_nt
            by fastforce 
          then have wfv:"wf_val (val_CONST nt c)" using outer(7) by simp
          have "wf_unop_underscore nt unop_nt" using outer(10)
          proof(induction "mk_config (mk_state s' f) [admininstr_instr (instr_sc1 (UNOP nt unop_nt))]")
            case config_case_0
            then have "wf_instr (instr_sc1 (UNOP nt unop_nt))" using wf_admininstr_instr_inv by simp
            then show ?case proof(induction "instr_sc1 (UNOP nt unop_nt)")
            qed(auto)
          qed
          then have notnone: "fun_unop_underscore nt unop_nt c \<noteq> None" 
            using wfv fun_unop_underscore_total by simp
          then show ?case proof(cases "the (fun_unop_underscore nt unop_nt c)")
            case Nil
            then show ?thesis using notnone unop_trap Step.intros(1) c outer(12) 
                admininstr_val.domintros admininstr_val.psimps by fastforce
          next
            case (Cons a' list)
            then have 1: "a' \<in> set (the (fun_unop_underscore nt unop_nt c))" by simp
            have 2: "0 < length (the (fun_unop_underscore nt unop_nt c))" using Cons by simp
            show ?thesis using unop_val[OF 2 notnone 1] Step.intros(1) c outer(12)
                admininstr_val.domintros admininstr_val.psimps by fastforce
          qed
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (binop C nt binop_nt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            note outer = Nil
            then obtain c1 where c1: "a1 = val_CONST nt c1" using typeofval_is_nt by fastforce
            obtain c2 where c2: "a2 = val_CONST nt c2" using typeofval_is_nt Nil by fastforce
            have "wf_binop_underscore nt binop_nt" using Nil(10)
            proof(induction "mk_config (mk_state s' f) [admininstr_instr (instr_sc1 (BINOP nt binop_nt))]")
              case config_case_0
              have "wf_instr (instr_sc1 (BINOP nt binop_nt))" 
                using config_case_0(2) wf_admininstr_instr_inv by simp
              then show ?case proof(induction "instr_sc1 (BINOP nt binop_nt)")
              qed
            qed
            then obtain res where res: "fun_binop_underscore nt binop_nt c1 c2 (Some res)" 
              using fun_binop_underscore_total Nil(7) c1 c2
              by fastforce
            show ?case proof(cases res)
              case Nil
              then show ?thesis using binop_trap[OF res] outer(12) Step.intros(1) c1 c2
                admininstr_val.domintros(1) admininstr_val.psimps(1)
                by auto
            next
              case (Cons a list)
              then show ?thesis using binop_val[OF res] outer(12) Step.intros(1) c1 c2
                admininstr_val.domintros(1) admininstr_val.psimps(1)
                by fastforce
            qed
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (testop C nt testop_nt)
        then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain c where c: "a = val_CONST nt c" using typeofval_is_nt
            by fastforce 
          then have wfv:"wf_val (val_CONST nt c)" using outer(7) by simp
          then have wfc: "wf_num_underscore nt c" proof(induction "val_CONST nt c") qed(auto)
          have wfop: "wf_testop_underscore nt testop_nt" using outer(10)
          proof(induction "mk_config (mk_state s' f) [admininstr_instr (instr_sc1 (TESTOP nt testop_nt))]")
            case config_case_0
            then have "wf_instr (instr_sc1 (TESTOP nt testop_nt))" using wf_admininstr_instr_inv by simp
            then show ?case proof(induction "instr_sc1 (TESTOP nt testop_nt)")
            qed(auto)
          qed
          then have notnone: "fun_testop_underscore nt testop_nt c \<noteq> None" 
            using wfv fun_testop_underscore_total by simp
          then show ?case 
          using Step_pure__testop Step.intros(1) c outer(12)
                admininstr_val.domintros admininstr_val.psimps testop__is_wf[OF wfop wfc notnone]
                by fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (relop C nt relop_nt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            note outer = Nil
            then obtain c1 where c1: "a1 = val_CONST nt c1" using typeofval_is_nt by fastforce
            obtain c2 where c2: "a2 = val_CONST nt c2" using typeofval_is_nt Nil by fastforce
            have wfop: "wf_relop_underscore nt relop_nt" using Nil(10)
            proof(induction "mk_config (mk_state s' f) [admininstr_instr (instr_sc1 (RELOP nt relop_nt))]")
              case config_case_0
              have "wf_instr (instr_sc1 (RELOP nt relop_nt))"
                using config_case_0(2) wf_admininstr_instr_inv by simp
              then show ?case proof(induction "instr_sc1 (RELOP nt relop_nt)")
              qed
            qed
            then obtain res where res: "fun_relop_underscore nt relop_nt c1 c2 (Some res)"
              using fun_relop_underscore_total Nil(7) c1 c2
              by fastforce
            have wfc1: "wf_num_underscore nt c1" and wfc2: "wf_num_underscore nt c2"
              using outer(7) c1 c2 wf_val.simps by auto
            have nn: "Some res \<noteq> None" by simp
            have wfres: "wf_num_underscore I32 (the (Some res))"
              using relop__is_wf[OF res wfop wfc1 wfc2 nn HOL.refl] .
            show ?case using Step_pure__relop[OF res nn HOL.refl wfres] outer(12) Step.intros(1) c1 c2
                admininstr_val.domintros(1) admininstr_val.psimps(1)
                by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (cvtop C nt_1 nt_2 cvtop)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain c where c: "a = val_CONST nt_2 c" using typeofval_is_nt
            by fastforce
          then have wfv: "wf_val (val_CONST nt_2 c)" using outer(7) by simp
          have wfop: "wf_cvtop__underscore nt_2 nt_1 cvtop" using outer(10)
          proof(induction "mk_config (mk_state s' f) [admininstr_instr (instr_sc1 (CVTOP nt_1 nt_2 cvtop))]")
            case config_case_0
            then have "wf_instr (instr_sc1 (CVTOP nt_1 nt_2 cvtop))" using wf_admininstr_instr_inv by simp
            then show ?case proof(induction "instr_sc1 (CVTOP nt_1 nt_2 cvtop)")
            qed(auto)
          qed
          obtain res where res: "fun_cvtop__underscore nt_2 nt_1 cvtop c (Some res)"
            using fun_cvtop_underscore_total[OF wfv wfop] by blast
          show ?case proof(cases res)
            case Nil
            then show ?thesis using cvtop_trap[OF res] outer(12) Step.intros(1) c
              admininstr_val.domintros(1) admininstr_val.psimps(1)
              by auto
          next
            case (Cons a list)
            then show ?thesis using cvtop_val[OF res] outer(12) Step.intros(1) c
              admininstr_val.domintros(1) admininstr_val.psimps(1)
              by fastforce
          qed
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (ref_null C rt)
      then show ?case using admininstr_val.domintros(3) admininstr_val.psimps(3)[of rt]
        by (metis admininstr_instr.simps(41))
    next
      case (ref_func x C' ft)
      have stok: "Store_ok s'" using ref_func(10) proof(induction "mk_state s' f" "strip C'") qed(auto) 
      have "length (context_FUNCS C') = length (fun_funcaddr (mk_state s' f))"
        using ref_func(10) proof(induction "mk_state s' f" "strip C'")
        case mk_State_ok
        show ?case using mk_State_ok(2) proof(induction s' f "strip C'")
          case (mk_Frame_ok s v_moduleinst C t_lst val_lst)
          show ?case using mk_Frame_ok(1,8) proof(induction s v_moduleinst C)
            case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
                  functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
                  dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
            show ?case using mk_Moduleinst_ok(4,27) append_res_context_def strip_def
              fun_funcaddr.domintros fun_funcaddr.psimps
              by simp 
          qed
        qed
      qed
      then show ?case using Step_read__ref_func ref_func(1,14) Step.intros(2) 
          reducible_left_v[OF _ ref_func(12)] stok
        by fastforce
    next
      case (ref_is_null C rt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then have "typeofval a = BOT \<or> typeofval a = valtype_reftype rt" 
            using valtype_sub_reftype
            by auto
          then show ?case using Nil proof(induction a)
            case (val_CONST x1 x2)
            show ?case using val_CONST(1) typeofval.domintros(1) typeofval.psimps(1)
              by (metis Valtype_sub_refl lanetype_numtype.cases typeofval.domintros(3) typeofval.psimps(3)
                  typeofval_is_nt val.distinct(3) valtype.distinct(13,25,35,43) valtype_numtype.simps(1,2,3,4))
          next
            case (val_VCONST x1 x2)
            show ?case using val_VCONST(1) typeofval.domintros(2) typeofval.psimps(2) 
            proof(induction x1)
              case V128
              then show ?case using valtype_reftype.domintros valtype_reftype.psimps 
                valtype_vectype.domintros valtype_vectype.psimps
              proof(induction rt) qed(auto)
            qed
          next
            case (val_REF_NULL x)
            then show ?case using ref_is_null_true[of "ref_REF_NULL x" x]
                  Step.intros(1) admininstr_val.domintros 
                  admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps
                  admininstr_ref.psimps admininstr_ref.domintros
              by fastforce
          next
            case (val_REF_FUNC_ADDR x)
            have "\<not> Step_pure_before_ref_is_null_false
                [admininstr_ref (REF_FUNC_ADDR x), admininstr_sc4 admininstr_st4_REF_IS_NULL]" 
              using Step_pure_before_ref_is_null_false.cases admininstr_ref.domintros(1,2) 
                admininstr_ref.psimps(1,2)
              by auto
            then show ?case using val_REF_FUNC_ADDR(13) ref_is_null_false[of "REF_FUNC_ADDR x"]
                  Step.intros(1) admininstr_val.domintros 
                  admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps
                  admininstr_ref.psimps admininstr_ref.domintros
               by auto
          next
            case (val_REF_HOST_ADDR x)
            have "\<not> Step_pure_before_ref_is_null_false
                [admininstr_ref (REF_HOST_ADDR x), admininstr_sc4 admininstr_st4_REF_IS_NULL]" 
              using Step_pure_before_ref_is_null_false.cases admininstr_ref.domintros 
                admininstr_ref.psimps
              by auto
            then show ?case using val_REF_HOST_ADDR(13) ref_is_null_false[of "REF_HOST_ADDR x"]
                  Step.intros(1) admininstr_val.domintros 
                  admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps
                  admininstr_ref.psimps admininstr_ref.domintros
               by auto
          qed
        next
          case (Cons a vs)
          then show ?case by simp
        qed 
      qed
    next
      case (vconst C c)
      then show ?case using admininstr_val.domintros(2) admininstr_val.psimps(2)[of V128 c]
        by (metis admininstr_instr.simps(21))
    next
      case (Instr_ok__vvunop C v_vvunop)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain vec where vec: "a = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
          show ?case using Nil Step_pure__vvunop[OF HOL.refl] Step.intros(1) vec
              admininstr_val.domintros(2) admininstr_val.psimps(2)
            by fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (Instr_ok__vvbinop C v_vvbinop)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            then obtain vec1 where vec1: "a1 = val_VCONST V128 vec1" using typeofval_is_v128 by fastforce
            obtain vec2 where vec2: "a2 = val_VCONST V128 vec2" using typeofval_is_v128 Nil by fastforce
            show ?case using Nil Step_pure__vvbinop[OF HOL.refl] Step.intros(1) vec1 vec2
                admininstr_val.domintros(2) admininstr_val.psimps(2)
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (Instr_ok__vvternop C v_vvternop)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            then show ?case by simp
          next
            case (Cons a3 vs)
            show ?case using Cons(2-) proof(induction vs)
              case Nil
              then obtain vec1 where vec1: "a1 = val_VCONST V128 vec1" using typeofval_is_v128 by fastforce
              obtain vec2 where vec2: "a2 = val_VCONST V128 vec2" using typeofval_is_v128 Nil by fastforce
              obtain vec3 where vec3: "a3 = val_VCONST V128 vec3" using typeofval_is_v128 Nil by fastforce
              show ?case using Nil Step_pure__vvternop[OF HOL.refl] Step.intros(1) vec1 vec2 vec3
                  admininstr_val.domintros(2) admininstr_val.psimps(2)
                by fastforce
            next
              case (Cons a vs)
              then show ?case by simp
            qed
          qed
        qed
      qed
    next
      case (Instr_ok__vvtestop C v_vvtestop)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain vec where vec: "a = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
          define r where "r = ine_underscore (the (size valtype_V128)) vec (mk_uN 0)"
          have wfr: "wf_uN 32 r" unfolding r_def
            by (cases "vec = mk_uN 0") (auto simp: ine_underscore.psimps ine_underscore.domintros
                res_bool.psimps res_bool.domintros intro: wf_uN.intros)
          have step: "Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
              admininstr_sc2 (admininstr_st2_VVTESTOP V128 ANY_TRUE)]
              [admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 r))]"
            using wfr by (intro Step_pure__vvtestop)
              (auto simp: r_def numtype_size_simps proj_num__0.psimps proj_num__0.domintros
                size.psimps size.domintros intro!: num__case_0 wf_uN.intros)
          show ?case using Nil step Step.intros(1) vec
              admininstr_val.domintros(2) admininstr_val.psimps(2)
            by (cases v_vvtestop) fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vunop C sh vunop_sh)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain vec where vec: "a = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
          have wfv: "wf_uN 128 vec" using outer(7) vec by (auto intro: wf_V128_val)
          have wfi: "wf_shape sh \<and> wf_vunop_underscore sh vunop_sh" using outer(5)
            proof(induction "instr_sc2 (VUNOP sh vunop_sh)") qed(auto)
          obtain r where r: "fun_vunop_underscore sh vunop_sh vec (Some r)"
            using vunop_total wfi wfv by blast
          show ?case proof(cases r)
            case Nil
            then show ?thesis using vunop_trap[OF r] outer(12) Step.intros(1) vec
                admininstr_val.domintros(2) admininstr_val.psimps(2)
              by auto
          next
            case (Cons c0 l)
            then show ?thesis using Step_pure__vunop[OF r, where c = c0] outer(12) Step.intros(1) vec
                admininstr_val.domintros(2) admininstr_val.psimps(2)
              by fastforce
          qed
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vbinop C sh vbinop_sh)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            note outer = Nil
            then obtain vec1 where vec1: "a1 = val_VCONST V128 vec1" using typeofval_is_v128 by fastforce
            obtain vec2 where vec2: "a2 = val_VCONST V128 vec2" using typeofval_is_v128 Nil by fastforce
            have wfv: "wf_uN 128 vec1" "wf_uN 128 vec2" using outer(7) vec1 vec2 by (auto intro: wf_V128_val)
            have wfi: "wf_shape sh \<and> wf_vbinop_underscore sh vbinop_sh" using outer(5)
              proof(induction "instr_sc2 (VBINOP sh vbinop_sh)") qed(auto)
            obtain r where r: "fun_vbinop_underscore sh vbinop_sh vec1 vec2 (Some r)"
              using vbinop_total wfi wfv by blast
            show ?case proof(cases r)
              case Nil
              then show ?thesis using vbinop_trap[OF r] outer(12) Step.intros(1) vec1 vec2
                  admininstr_val.domintros(2) admininstr_val.psimps(2)
                by auto
            next
              case (Cons c0 l)
              then show ?thesis using vbinop_val[OF r, where c = c0] outer(12) Step.intros(1) vec1 vec2
                  admininstr_val.domintros(2) admininstr_val.psimps(2)
                by fastforce
            qed
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vtestop C sh vtestop_sh)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain vec where vec: "a = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
          have wfi: "wf_shape sh \<and> wf_vtestop_underscore sh vtestop_sh" using outer(5)
            proof(induction "instr_sc2 (VTESTOP sh vtestop_sh)") qed(auto)
          then obtain J M x where e: "sh = X (lanetype_Jnn J) (mk_dim M)" "vtestop_sh = mk_vtestop__0 J M x"
            by (auto elim: wf_vtestop_underscore.cases)
          have x: "x = ALL_TRUE" by (cases x) simp
          (* ALL_TRUE either finds all lanes non-zero, or the side condition of vtestop_false holds. *)
          have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
              admininstr_sc3 (admininstr_st3_VTESTOP sh vtestop_sh)] es"
          proof(cases "Step_pure_before_vtestop_false [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
              admininstr_sc3 (admininstr_st3_VTESTOP sh vtestop_sh)]")
            case True
            then show ?thesis
              by (cases rule: Step_pure_before_vtestop_false.cases)
                (clarsimp, rule exI, rule vtestop_true[OF HOL.refl], auto)
          next
            case False
            then show ?thesis using vtestop_false[where c = vec and v_Jnn = J and v_N = M] e x by auto
          qed
          then show ?case using outer(12) Step.intros(1) vec
              admininstr_val.domintros(2) admininstr_val.psimps(2)
            by fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vrelop C sh vrelop_sh)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            note outer = Nil
            then obtain vec1 where vec1: "a1 = val_VCONST V128 vec1" using typeofval_is_v128 by fastforce
            obtain vec2 where vec2: "a2 = val_VCONST V128 vec2" using typeofval_is_v128 Nil by fastforce
            have wfv: "wf_uN 128 vec1" "wf_uN 128 vec2" using outer(7) vec1 vec2 by (auto intro: wf_V128_val)
            have wfi: "wf_shape sh \<and> wf_vrelop_underscore sh vrelop_sh" using outer(5)
              proof(induction "instr_sc2 (VRELOP sh vrelop_sh)") qed(auto)
            obtain r where r: "fun_vrelop_underscore sh vrelop_sh vec1 vec2 (Some r)"
              using vrelop_total wfi wfv by blast
            show ?case using Step_pure__vrelop[OF r] outer(12) Step.intros(1) vec1 vec2
                admininstr_val.domintros(2) admininstr_val.psimps(2)
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vshiftop C sh vshiftop_sh)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            note outer = Nil
            then obtain vec where vec: "a1 = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
            obtain c2 where c2: "a2 = val_CONST I32 c2" using typeofval_is_i32 Nil by fastforce
            have wfv: "wf_uN 128 vec" using outer(7) vec by (auto intro: wf_V128_val)
            have "wf_num_underscore I32 c2" using outer(7) c2 by (auto elim: wf_val.cases)
            then obtain n where n: "c2 = mk_num__0 Inn_I32 (mk_uN n)" "wf_uN 32 (mk_uN n)"
              using i32_num_form by blast
            have wfi: "wf_ishape sh \<and> wf_vshiftop_underscore sh vshiftop_sh" using outer(5)
              proof(induction "instr_sc2 (VSHIFTOP sh vshiftop_sh)") qed(auto)
            then obtain J M x where e: "sh = mk_ishape (X (lanetype_Jnn J) (mk_dim M))"
                "vshiftop_sh = mk_vshiftop__0 J M x"
              by (auto elim: wf_vshiftop_underscore.cases)
            have shp: "wf_shape (X (lanetype_Jnn J) (mk_dim M))"
              using wfi e by (auto elim: wf_ishape.cases simp: vt_generic_simps)
            obtain xs where xs: "lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) vec = map (mk_lane__0 J) xs"
                "\<forall>x\<in>set xs. wf_uN (lsize (lanetype_Jnn J)) x" "length xs = M"
              using lanes_Jnn[OF shp wfv] by blast
            (* every lane is shifted, so pick the shifted lane for each input lane *)
            have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
                admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN n))),
                admininstr_sc3 (admininstr_st3_VSHIFTOP sh vshiftop_sh)] es"
              unfolding e
              apply (rule exI)
              apply (rule Step_pure__vshiftop[where v_Jnn = J and v_N = M and v_n = n and ?c_1.0 = vec
                  and vshiftop = "mk_vshiftop__0 J M x"
                  and c'_lst = "lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) vec"
                  and var_0_lst = "map (\<lambda>c'. Some (SOME r. fun_vshiftop_underscore
                    (mk_ishape (X (lanetype_Jnn J) (mk_dim M))) (mk_vshiftop__0 J M x) c' (mk_uN n) (Some r)))
                    (lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) vec)"
                  and c = "inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) (map the (map (\<lambda>c'. Some
                    (SOME r. fun_vshiftop_underscore (mk_ishape (X (lanetype_Jnn J) (mk_dim M)))
                    (mk_vshiftop__0 J M x) c' (mk_uN n) (Some r))) (lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) vec)))"];
                  (rule list_all2_mapI vt_list_allI)?)
              using shp xs wfi e n by (auto simp: vt_generic_simps intro!: vshiftop_lane_some lane__case_0)
            show ?case using step outer(12) Step.intros(1) vec c2 n
                admininstr_val.domintros(1,2) admininstr_val.psimps(1,2)
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vbitmask C sh)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain vec where vec: "a = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
          have wfv: "wf_uN 128 vec" using outer(7) vec by (auto intro: wf_V128_val)
          have "wf_ishape sh" using outer(5)
            proof(induction "instr_sc3 (VBITMASK sh)") qed(auto)
          then obtain J N where e: "sh = mk_ishape (X (lanetype_Jnn J) (mk_dim N))"
              and s: "wf_shape (X (lanetype_Jnn J) (mk_dim N))"
            using wf_ishape_form by blast
          obtain xs where xs: "lanes_underscore (X (lanetype_Jnn J) (mk_dim N)) vec = map (mk_lane__0 J) xs"
              "\<forall>x\<in>set xs. wf_uN (lsize (lanetype_Jnn J)) x" "length xs = N"
            using lanes_Jnn[OF s wfv] by blast
          (* the sign bit of each lane, i.e. whether it is negative as a signed number *)
          define var where "var = map (\<lambda>ci. SOME v. fun_ilt_underscore (lsize (lanetype_Jnn J)) S
            (the (proj_lane__0 ci)) (mk_uN 0) v) (lanes_underscore (X (lanetype_Jnn J) (mk_dim N)) vec)"
          have zero: "wf_uN (lsize (lanetype_Jnn J)) (mk_uN 0)" by (auto intro: wf_uN.intros)
          have rel: "list_all2 (\<lambda>v ci. fun_ilt_underscore (lsize (lanetype_Jnn J)) S (the (proj_lane__0 ci))
              (mk_uN 0) v) var (lanes_underscore (X (lanetype_Jnn J) (mk_dim N)) vec)"
            unfolding var_def
            apply (rule list_all2_mapI)
            using xs(1,2) zero by (auto intro!: ilt_some simp: vt_generic_simps)
          have bit: "\<forall>v\<in>set var. wf_uN (Suc 0) v"
            unfolding var_def using xs(1,2) zero by (auto intro!: icmp_some_bit(1) simp: vt_generic_simps)
          have bits_wf: "list_all (\<lambda>v. wf_bit (mk_bit (proj_uN_0 v))) var"
            using bit by (fastforce simp: list_all_iff intro!: wf_bit.intros dest!: wf_uN_bound)
          have bit0: "wf_bit (mk_bit 0)" by (auto intro: wf_bit.intros)
          define bits where "bits = map (\<lambda>v. mk_bit (proj_uN_0 v)) var @ repeat (32 - N) (mk_bit 0)"
          have "N \<le> 32" using wf_shape_size[OF s] by (cases J) (auto simp: vt_simps)
          then have "length bits = 32" using xs(1,3) by (simp add: bits_def var_def length_repeat)
          moreover have "list_all wf_bit bits"
            using bits_wf bit0 set_repeat by (fastforce simp: bits_def list_all_iff)
          ultimately obtain ci where ci: "wf_uN 32 ci" "ibits_underscore 32 ci = bits"
            using ibits_surj by blast
          have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
              admininstr_sc3 (admininstr_st3_VBITMASK sh)] es"
            unfolding e
            apply (rule exI)
            apply (rule Step_pure__vbitmask[unfolded thirty_two, where v_Jnn = J and v_N = N and c = vec
                and ci = ci and var_0_lst = var
                and ci_1_lst = "lanes_underscore (X (lanetype_Jnn J) (mk_dim N)) vec"])
            using rel ci s bits_wf bit0 lanes_proj_some[OF xs(1)] list_all2_lengthD[OF rel]
            by (auto simp: bits_def)
          then show ?case using outer(12) Step.intros(1) vec
              admininstr_val.domintros(2) admininstr_val.psimps(2)
            by fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vswizzle C sh)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            note outer = Nil
            then obtain vec1 where vec1: "a1 = val_VCONST V128 vec1" using typeofval_is_v128 by fastforce
            obtain vec2 where vec2: "a2 = val_VCONST V128 vec2" using typeofval_is_v128 Nil by fastforce
            have wfv: "wf_uN 128 vec1" "wf_uN 128 vec2" using outer(7) vec1 vec2 by (auto intro: wf_V128_val)
            have "sh = mk_ishape (X lanetype_I8 (mk_dim 16))" using outer(5)
              proof(induction "instr_sc3 (VSWIZZLE sh)") qed(auto)
            then have e: "sh = mk_ishape (X (lanetype_packtype I8) (mk_dim 16))" by (simp add: vt_simps)
            have s: "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim 16))"
              by (auto intro!: wf_shape.intros wf_dim.intros simp: vt_all_simps)
            obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim 16)) vec1 = map (mk_lane__0 Jnn_I8) xs1"
                "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = 16"
              using lanes_Jnn[OF s wfv(1)] by blast
            obtain xs2 where xs2: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim 16)) vec2 = map (mk_lane__0 Jnn_I8) xs2"
                "\<forall>x\<in>set xs2. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs2 = 16"
              using lanes_Jnn[OF s wfv(2)] by blast
            have w1: "\<forall>x\<in>set xs1. wf_uN 8 x" and w2: "\<forall>x\<in>set xs2. wf_uN 8 x"
              using xs1(2) xs2(2) by (simp_all add: vt_simps)
            (* the selector lanes index into the 16 lanes padded with zeros up to 256 *)
            have idx: "proj_uN_0 (xs2 ! k) < 256" if "k < 16" for k
              using wf_uN_bound[OF bspec[OF w2 nth_mem[of k xs2]]] that xs2(3) by simp
            have sel: "wf_uN 8 ((xs1 @ repeat 240 (mk_uN 0)) ! j)" if "j < 256" for j
            proof (cases "j < 16")
              case True
              then show ?thesis using bspec[OF w1 nth_mem[of j xs1]] xs1(3) by (simp add: nth_append)
            next
              case False
              then show ?thesis using that xs1(3) by (simp add: nth_append nth_repeat wf_uN.intros)
            qed
            have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec1),
                admininstr_sc2 (admininstr_st2_VCONST V128 vec2),
                admininstr_sc3 (admininstr_st3_VSWIZZLE sh)] es"
              unfolding e
              apply (rule exI)
              apply (rule Step_pure__vswizzle[where v_Pnn = I8 and v_M = 16 and ?c_1.0 = vec1 and ?c_2.0 = vec2];
                  (rule HOL.refl)?)
              using xs1(1,3) xs2(1,3) idx sel s
              by (auto simp: holds_upto_def vt_all_simps length_repeat o_def list_all_iff intro!: lane__case_0 wf_uN.intros)
            then show ?case using outer(12) Step.intros(1) vec1 vec2
                admininstr_val.domintros(2) admininstr_val.psimps(2)
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vshuffle sh i_lst C)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            (* this Instr_ok rule has 4 premises, so the stack facts are at 9 and 14 *)
            note outer = Nil
            then obtain vec1 where vec1: "a1 = val_VCONST V128 vec1" using typeofval_is_v128 by fastforce
            obtain vec2 where vec2: "a2 = val_VCONST V128 vec2" using typeofval_is_v128 Nil by fastforce
            have wfv: "wf_uN 128 vec1" "wf_uN 128 vec2" using outer(9) vec1 vec2 by (auto intro: wf_V128_val)
            have wfi: "sh = mk_ishape (X lanetype_I8 (mk_dim 16)) \<and> length i_lst = 16" using outer(7)
              proof(induction "instr_sc3 (VSHUFFLE sh i_lst)") qed(auto)
            then have e: "sh = mk_ishape (X (lanetype_packtype I8) (mk_dim 16))" by (simp add: vt_simps)
            (* the typing rule bounds every lane index by 2 * 16 *)
            have idx: "proj_uN_0 (i_lst ! k) < 32" if "k < 16" for k
              using outer(1) wfi that by (auto simp: list_all_length vt_generic_simps)
            have s: "wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim 16))"
              by (auto intro!: wf_shape.intros wf_dim.intros simp: vt_all_simps)
            obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim 16)) vec1 = map (mk_lane__0 Jnn_I8) xs1"
                "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs1 = 16"
              using lanes_Jnn[OF s wfv(1)] by blast
            obtain xs2 where xs2: "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim 16)) vec2 = map (mk_lane__0 Jnn_I8) xs2"
                "\<forall>x\<in>set xs2. wf_uN (lsize (lanetype_Jnn Jnn_I8)) x" "length xs2 = 16"
              using lanes_Jnn[OF s wfv(2)] by blast
            have w1: "\<forall>x\<in>set xs1. wf_uN 8 x" and w2: "\<forall>x\<in>set xs2. wf_uN 8 x"
              using xs1(2) xs2(2) by (simp_all add: vt_simps)
            have sel: "wf_uN 8 ((xs1 @ xs2) ! j)" if "j < 32" for j
            proof (cases "j < 16")
              case True
              then show ?thesis using bspec[OF w1 nth_mem[of j xs1]] xs1(3) by (simp add: nth_append)
            next
              case False
              then show ?thesis using bspec[OF w2 nth_mem[of "j - 16" xs2]] that xs1(3) xs2(3)
                by (simp add: nth_append)
            qed
            have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec1),
                admininstr_sc2 (admininstr_st2_VCONST V128 vec2),
                admininstr_sc3 (admininstr_st3_VSHUFFLE sh i_lst)] es"
              unfolding e
              apply (rule exI)
              apply (rule Step_pure__vshuffle[where v_Pnn = I8 and v_N = 16 and ?c_1.0 = vec1 and ?c_2.0 = vec2
                  and c'_lst = "xs1 @ xs2"]; (rule HOL.refl)?)
              using xs1(1,3) xs2(1,3) wfi idx sel s w1 w2
              by (auto simp: holds_upto_def vt_all_simps list_all_iff intro!: lane__case_0)
            then show ?case using outer(14) Step.intros(1) vec1 vec2
                admininstr_val.domintros(2) admininstr_val.psimps(2)
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vsplat C sh)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain c1 where c1: "a = val_CONST (shunpack sh) c1" using typeofval_is_nt by fastforce
          have wfc: "wf_num_underscore (shunpack sh) c1" using outer(7) c1 by (auto elim: wf_val.cases)
          have wfs: "wf_shape sh" using outer(5)
            proof(induction "instr_sc3 (VSPLAT sh)") qed(auto)
          obtain lt N where e: "sh = X lt (mk_dim N)" by (metis dim.exhaust shape.exhaust)
          have wfc': "wf_num_underscore (unpack lt) c1" using wfc e by (simp add: vt_generic_simps)
          have step: "\<exists>es. Step_pure [admininstr_sc1 (admininstr_st1_CONST (shunpack sh) c1),
              admininstr_sc3 (admininstr_st3_VSPLAT sh)] es"
            using Step_pure__vsplat[where v_Lnn = lt and v_N = N and ?c_1.0 = c1,
                OF packnum_not_None[OF wfc'] HOL.refl] wfs e
            by (auto simp: vt_generic_simps)
          show ?case using step outer(12) Step.intros(1) c1
              admininstr_val.domintros(1) admininstr_val.psimps(1)
            by fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vextract_lane j sh C sx_opt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          (* this Instr_ok rule has 4 premises, so the stack facts are at 7, 9 and 14 *)
          note outer = Nil
          then obtain vec where vec: "a = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
          have wfv: "wf_uN 128 vec" using outer(9) vec by (auto intro: wf_V128_val)
          have wfi: "wf_shape sh"
              "fun_lanetype sh \<in> set [lanetype_I32, lanetype_I64, lanetype_F32, lanetype_F64] \<longleftrightarrow> sx_opt = None"
            using outer(7) proof(induction "instr_sc3 (VEXTRACT_LANE sh sx_opt j)") qed(auto)
          obtain lt N where e: "sh = X lt (mk_dim N)" by (metis dim.exhaust shape.exhaust)
          have jN: "proj_uN_0 j < N" using outer(1) e by (simp add: vt_generic_simps)
          have len: "proj_uN_0 j < length (lanes_underscore (X lt (mk_dim N)) vec)"
            using jN length_lanes by simp
          have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
              admininstr_sc3 (admininstr_st3_VEXTRACT_LANE sh sx_opt j)] es"
          proof (cases sx_opt)
            case None
            (* a numeric lane type: unpack the selected lane *)
            obtain nt where nt: "lt = lanetype_numtype nt"
            proof (cases lt)
              case lanetype_I32 then show ?thesis using that[of I32] by (simp add: vt_simps)
            next
              case lanetype_I64 then show ?thesis using that[of I64] by (simp add: vt_simps)
            next
              case lanetype_F32 then show ?thesis using that[of F32] by (simp add: vt_simps)
            next
              case lanetype_F64 then show ?thesis using that[of F64] by (simp add: vt_simps)
            next
              case lanetype_I8 then show ?thesis using wfi(2) e None by (simp add: vt_generic_simps)
            next
              case lanetype_I16 then show ?thesis using wfi(2) e None by (simp add: vt_generic_simps)
            qed
            have s: "wf_shape (X (lanetype_numtype nt) (mk_dim N))" using wfi(1) e nt by simp
            show ?thesis unfolding e nt None
              using vextract_lane_num[OF unpack_lane_some[OF s wfv jN] len[unfolded nt] HOL.refl s] by blast
          next
            case (Some sx)
            (* a packed lane type: sign- or zero-extend the selected lane to 32 bits *)
            obtain pt where pt: "lt = lanetype_packtype pt"
            proof (cases lt)
              case lanetype_I8 then show ?thesis using that[of I8] by (simp add: vt_simps)
            next
              case lanetype_I16 then show ?thesis using that[of I16] by (simp add: vt_simps)
            qed (use wfi(2) e Some in \<open>simp_all add: vt_generic_simps\<close>)
            have s: "wf_shape (X (lanetype_packtype pt) (mk_dim N))" using wfi(1) e pt by simp
            obtain x where x: "lanes_underscore (X (lanetype_packtype pt) (mk_dim N)) vec ! proj_uN_0 j
                = mk_lane__0 (Jnn_packtype pt) x" "wf_uN (psize pt) x"
              using pack_lane[OF s wfv jN] by blast
            define c2 where "c2 = mk_num__0 Inn_I32 (extend__underscore (psize pt) 32 sx x)"
            have wfc2: "wf_num_underscore I32 c2"
              using x(2) by (auto simp: c2_def vt_simps intro!: num__case_0 extend___is_wf[OF _ HOL.refl])
            show ?thesis unfolding e pt Some
              apply (rule exI)
              apply (rule vextract_lane_pack[unfolded thirty_two, where pt = pt and v_N = N and ?c_1.0 = vec
                  and ?c_2.0 = c2 and i = j and v_sx = sx])
              using x wfc2 s len pt by (auto simp: c2_def vt_generic_simps)
          qed
          show ?case using step outer(14) Step.intros(1) vec
              admininstr_val.domintros(2) admininstr_val.psimps(2)
            by fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vreplace_lane i sh C)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            (* this Instr_ok rule has 4 premises, so the stack facts are at 7, 9 and 14 *)
            note outer = Nil
            then obtain vec where vec: "a1 = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
            obtain c2 where c2: "a2 = val_CONST (shunpack sh) c2" using typeofval_is_nt Nil by fastforce
            have wfc: "wf_num_underscore (shunpack sh) c2" using outer(9) c2 by (auto elim: wf_val.cases)
            have wfs: "wf_shape sh" using outer(7)
              proof(induction "instr_sc3 (VREPLACE_LANE sh i)") qed(auto)
            obtain lt N where e: "sh = X lt (mk_dim N)" by (metis dim.exhaust shape.exhaust)
            have wfc': "wf_num_underscore (unpack lt) c2" using wfc e by (simp add: vt_generic_simps)
            have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
                admininstr_sc1 (admininstr_st1_CONST (shunpack sh) c2),
                admininstr_sc3 (admininstr_st3_VREPLACE_LANE sh i)] es"
              using Step_pure__vreplace_lane[where v_Lnn = lt and v_N = N and ?c_1.0 = vec and ?c_2.0 = c2 and i = i,
                  OF packnum_not_None[OF wfc'] HOL.refl] wfs e
              by (auto simp: vt_generic_simps)
            show ?case using step outer(14) Step.intros(1) vec c2
                admininstr_val.domintros(1,2) admininstr_val.psimps(1,2)
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vextunop C sh_1 sh_2 vextunop)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain vec where vec: "a = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
          have wfv: "wf_uN 128 vec" using outer(7) vec by (auto intro: wf_V128_val)
          have wfi: "wf_ishape sh_1 \<and> wf_ishape sh_2 \<and> wf_vextunop__underscore sh_2 sh_1 vextunop"
            using outer(5) proof(induction "instr_sc3 (VEXTUNOP sh_1 sh_2 vextunop)") qed(auto)
          obtain r where r: "fun_vextunop__underscore sh_2 sh_1 vextunop vec (Some r)"
            using vextunop_total wfi wfv by blast
          have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
              admininstr_sc4 (admininstr_st4_VEXTUNOP sh_1 sh_2 vextunop)] es"
            using Step_pure__vextunop[OF r _ HOL.refl] by auto
          then show ?case using outer(12) Step.intros(1) vec
              admininstr_val.domintros(2) admininstr_val.psimps(2)
            by fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vextbinop C sh_1 sh_2 vextbinop)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            note outer = Nil
            then obtain vec1 where vec1: "a1 = val_VCONST V128 vec1" using typeofval_is_v128 by fastforce
            obtain vec2 where vec2: "a2 = val_VCONST V128 vec2" using typeofval_is_v128 Nil by fastforce
            have wfv: "wf_uN 128 vec1" "wf_uN 128 vec2" using outer(7) vec1 vec2 by (auto intro: wf_V128_val)
            have wfi: "wf_ishape sh_1 \<and> wf_ishape sh_2 \<and> wf_vextbinop__underscore sh_2 sh_1 vextbinop"
              using outer(5) proof(induction "instr_sc3 (VEXTBINOP sh_1 sh_2 vextbinop)") qed(auto)
            obtain r where r: "fun_vextbinop__underscore sh_2 sh_1 vextbinop vec1 vec2 (Some r)"
              using vextbinop_total wfi wfv by blast
            have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec1),
                admininstr_sc2 (admininstr_st2_VCONST V128 vec2),
                admininstr_sc4 (admininstr_st4_VEXTBINOP sh_1 sh_2 vextbinop)] es"
              using Step_pure__vextbinop[OF r _ HOL.refl] by auto
            then show ?case using outer(12) Step.intros(1) vec1 vec2
                admininstr_val.domintros(2) admininstr_val.psimps(2)
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vnarrow C sh_1 sh_2 v_sx)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            note outer = Nil
            then obtain vec1 where vec1: "a1 = val_VCONST V128 vec1" using typeofval_is_v128 by fastforce
            obtain vec2 where vec2: "a2 = val_VCONST V128 vec2" using typeofval_is_v128 Nil by fastforce
            have wfv: "wf_uN 128 vec1" "wf_uN 128 vec2" using outer(7) vec1 vec2 by (auto intro: wf_V128_val)
            have wfi: "wf_ishape sh_1 \<and> wf_ishape sh_2" using outer(5)
              proof(induction "instr_sc3 (VNARROW sh_1 sh_2 v_sx)") qed(auto)
            obtain J2 N2 where e1: "sh_1 = mk_ishape (X (lanetype_Jnn J2) (mk_dim N2))"
                and s1: "wf_shape (X (lanetype_Jnn J2) (mk_dim N2))"
              using wf_ishape_form wfi by blast
            obtain J1 N1 where e2: "sh_2 = mk_ishape (X (lanetype_Jnn J1) (mk_dim N1))"
                and s2: "wf_shape (X (lanetype_Jnn J1) (mk_dim N1))"
              using wf_ishape_form wfi by blast
            obtain xs1 where xs1: "lanes_underscore (X (lanetype_Jnn J1) (mk_dim N1)) vec1 = map (mk_lane__0 J1) xs1"
                "\<forall>x\<in>set xs1. wf_uN (lsize (lanetype_Jnn J1)) x" "length xs1 = N1"
              using lanes_Jnn[OF s2 wfv(1)] by blast
            obtain xs2 where xs2: "lanes_underscore (X (lanetype_Jnn J1) (mk_dim N1)) vec2 = map (mk_lane__0 J1) xs2"
                "\<forall>x\<in>set xs2. wf_uN (lsize (lanetype_Jnn J1)) x" "length xs2 = N1"
              using lanes_Jnn[OF s2 wfv(2)] by blast
            (* each input lane is narrowed; the result lanes are well-formed by narrow___is_wf *)
            have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec1),
                admininstr_sc2 (admininstr_st2_VCONST V128 vec2),
                admininstr_sc4 (admininstr_st4_VNARROW sh_1 sh_2 v_sx)] es"
              unfolding e1 e2
              apply (rule exI)
              apply (rule Step_pure__vnarrow[where ?Jnn_1.0 = J1 and ?N_1.0 = N1 and ?Jnn_2.0 = J2 and ?N_2.0 = N2
                  and ?c_1.0 = vec1 and ?c_2.0 = vec2 and v_sx = v_sx
                  and ci_1_lst = "lanes_underscore (X (lanetype_Jnn J1) (mk_dim N1)) vec1"
                  and ci_2_lst = "lanes_underscore (X (lanetype_Jnn J1) (mk_dim N1)) vec2"
                  and cj_1_lst = "map (\<lambda>ci. narrow__underscore (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2))
                    v_sx (the (proj_lane__0 ci))) (lanes_underscore (X (lanetype_Jnn J1) (mk_dim N1)) vec1)"
                  and cj_2_lst = "map (\<lambda>ci. narrow__underscore (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2))
                    v_sx (the (proj_lane__0 ci))) (lanes_underscore (X (lanetype_Jnn J1) (mk_dim N1)) vec2)"
                  and c = "inv_lanes_underscore (X (lanetype_Jnn J2) (mk_dim N2))
                    (map (mk_lane__0 J2) (map (\<lambda>ci. narrow__underscore (lsize (lanetype_Jnn J1))
                      (lsize (lanetype_Jnn J2)) v_sx (the (proj_lane__0 ci)))
                      (lanes_underscore (X (lanetype_Jnn J1) (mk_dim N1)) vec1)) @
                     map (mk_lane__0 J2) (map (\<lambda>ci. narrow__underscore (lsize (lanetype_Jnn J1))
                      (lsize (lanetype_Jnn J2)) v_sx (the (proj_lane__0 ci)))
                      (lanes_underscore (X (lanetype_Jnn J1) (mk_dim N1)) vec2)))"];
                  (rule list_all_mapI vt_list_allI)?)
              using s1 s2 xs1 xs2
              by (auto simp: vt_generic_simps intro!: lane__case_0 narrow___is_wf[OF _ HOL.refl])
            show ?case using step outer(12) Step.intros(1) vec1 vec2
                admininstr_val.domintros(2) admininstr_val.psimps(2)
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vcvtop C sh_1 sh_2 vcvtop)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          note outer = Nil
          then obtain vec where vec: "a = val_VCONST V128 vec" using typeofval_is_v128 by fastforce
          have wfv: "wf_uN 128 vec" using outer(7) vec by (auto intro: wf_V128_val)
          have wfi: "wf_shape sh_1 \<and> wf_shape sh_2 \<and> wf_vcvtop__underscore sh_2 sh_1 vcvtop"
            using outer(5) proof(induction "instr_sc4 (VCVTOP sh_1 sh_2 vcvtop)") qed(auto)
          obtain r where r: "fun_vcvtop__underscore sh_2 sh_1 vcvtop vec (Some r)"
            using vcvtop_total wfi wfv by blast
          have step: "\<exists>es. Step_pure [admininstr_sc2 (admininstr_st2_VCONST V128 vec),
              admininstr_sc4 (admininstr_st4_VCVTOP sh_1 sh_2 vcvtop)] es"
            using Step_pure__vcvtop[OF r _ HOL.refl] by auto
          then show ?case using outer(12) Step.intros(1) vec
              admininstr_val.domintros(2) admininstr_val.psimps(2)
            by fastforce
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (local_get x C t)
      then show ?case proof(induction vs)
        case Nil
        then show ?case using Step_read__local_get Step.intros(2)
          by fastforce
      next
        case (Cons a vs)
        then show ?case by simp
      qed 
    next
      case (local_set x C t)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        then show ?case using Step__local_set
          by fastforce
      qed
    next
      case (local_tee x C t)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        then show ?case using Step_pure__local_tee Step.intros(1) by fastforce
      qed
    next
      case (global_get x C v_mut t)
      then show ?case proof(induction vs)
        case Nil
        then show ?case using Step_read__global_get Step.intros(2) by fastforce
      next
        case (Cons a vs)
        then show ?case by simp
      qed
    next
      case (global_set x C t)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        then show ?case using Step__global_set by fastforce
      qed
    next
      case (table_get x C lim rt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain c where c: "a = val_CONST I32 c" using typeofval_is_i32
            by fastforce
          have "wf_val a" using Nil(10) by simp
          then have projc: "proj_num__0 c \<noteq> None" using c proof(induction a)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
              proof(induction v_Fnn) qed(auto)
            qed 
          qed(auto)
          then show ?case proof(cases "proj_uN_0 (the (proj_num__0 c)) < 
                  length (REFS (fun_table (mk_state s' f) x))")
            case True
            show ?thesis using table_get_val[OF True projc] Step.intros(2) Nil(15)
              c admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros
              admininstr_instr.psimps by fastforce
          next
            case False
            then show ?thesis using table_get_trap[OF projc, of "mk_state s' f" x]
               Step.intros(2) Nil(15) c admininstr_val.domintros admininstr_val.psimps 
               admininstr_instr.domintros admininstr_instr.psimps by fastforce
          qed
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (table_set x C lim rt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            then obtain c where c: "a1 = val_CONST I32 c" using typeofval_is_i32
              by fastforce
            obtain ref where ref: "a2 = val_ref ref" using typeofval_is_rt Nil by fastforce 
          have "wf_val a1" using Nil(10) by simp
          then have projc: "proj_num__0 c \<noteq> None" using c proof(induction a1)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
              proof(induction v_Fnn) qed(auto)
            qed 
          qed(auto)
          then show ?case proof(cases "proj_uN_0 (the (proj_num__0 c)) < 
                  length (REFS (fun_table (mk_state s' f) x))")
            case True
            show ?thesis using table_set_val[OF projc True] Nil(15)
              c admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros
              admininstr_instr.psimps ref admininstr_val_ref by fastforce
          next
            case False
            then show ?thesis using table_set_trap[OF projc, of "mk_state s' f" x]
               Nil(15) c admininstr_val.domintros admininstr_val.psimps 
               admininstr_instr.domintros admininstr_instr.psimps ref admininstr_val_ref by fastforce
          qed
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (table_size x C lim rt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case using Step_read__table_size Step.intros(2) by fastforce
      next
        case (Cons a vs)
        then show ?case by simp
      qed
    next
      case (table_grow x C lim rt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            obtain ref where ref: "a1 = val_ref ref" using Nil(9) typeofval_is_rt by fastforce
            obtain c where c: "a2 = val_CONST I32 c" using Nil(9) typeofval_is_i32 by fastforce
            have "wf_val a2" using Nil(10) by simp
            then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a2)
              case (val_case_0 v_numtype var_0)
              then show ?case proof(induction v_numtype var_0)
                case (num__case_0 v_Inn var_x v_numtype)
                show ?case using num__case_0(2-) 
                proof(induction "the (isabelle_reference_output_wasm2.size (valtype_Inn v_Inn))"
                      var_x)
                  case (uN_case_0 i)
                  then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
                  proof(induction v_Inn) qed(auto)
                qed
              next
                case (num__case_1 v_Fnn var_x v_numtype)
                then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                proof(induction v_Fnn) qed(auto)
              qed
            qed(auto)
            obtain res where res: "fun_inv_signed_underscore 32 (0 - 1) res" 
              using fun_inv_signed_underscore_total by fastforce
            show ?case using Nil(15) table_grow_fail[OF res] ref c n 
               admininstr_val.domintros admininstr_val.psimps admininstr_val_ref
               admininstr_instr.domintros admininstr_instr.psimps by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (table_fill x C lim rt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons (2-) proof(induction vs)
            case Nil
            then show ?case by simp
          next
            case (Cons a3 vs)
            show ?case using Cons(2-) proof(induction vs)
              case Nil
              obtain i where a1: "a1 = val_CONST I32 i" using Nil(9) typeofval_is_i32 by fastforce
              have "wf_val a1" using Nil(10) by simp
              then have proji: "proj_num__0 i \<noteq> None" using a1 proof(induction a1)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              obtain c where a3: "a3 = val_CONST I32 c" using Nil(9) typeofval_is_i32 by fastforce
              have "wf_val a3" using Nil(10) by simp
              then obtain n where c: "c = mk_num__0 Inn_I32 (mk_uN n)" using a3 proof(induction a3)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  show ?case using num__case_0(2-) 
                  proof(induction "the (isabelle_reference_output_wasm2.size (valtype_Inn v_Inn))" var_x)
                    case (uN_case_0 i)
                    then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
                    proof(induction v_Inn) qed(auto)
                  qed
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              then show ?case proof(cases "length (REFS (fun_table (mk_state s' f) x)) < proj_uN_0 (the (proj_num__0 i)) + n")
                case True
                then show ?thesis using table_fill_trap[of i "mk_state s' f" x n a2] proji Nil(15)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros 
                  admininstr_instr.psimps Step.intros(2) a1 a3 c by fastforce
              next
                case False
                then show ?thesis proof(cases n)
                  case 0
                  then show ?thesis using table_fill_zero[of i n "mk_state s' f" x a2] proji Nil(15)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a3 c by fastforce
                next
                  case (Suc nat)
                  then show ?thesis using table_fill_succ[of i n "mk_state s' f" x a2] proji Nil(15)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a3 c by fastforce
                qed
              qed
            next
              case (Cons a vs)
              then show ?case by simp
            qed
          qed
        qed
      qed
    next
      case (table_copy x_1 C lim_1 rt x_2 lim_2)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons (2-) proof(induction vs)
            case Nil
            then show ?case by simp
          next
            case (Cons a3 vs)
            show ?case using Cons(2-) proof(induction vs)
              case Nil
              obtain j where a1: "a1 = val_CONST I32 j" using Nil(12) typeofval_is_i32 by fastforce
              have "wf_val a1" using Nil(13) by simp
              then have projj: "proj_num__0 j \<noteq> None" using a1 proof(induction a1)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              obtain i where a2: "a2 = val_CONST I32 i" using Nil(12) typeofval_is_i32 by fastforce
              have "wf_val a2" using Nil(13) by simp
              then have proji: "proj_num__0 i \<noteq> None" using a2 proof(induction a2)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              obtain c where a3: "a3 = val_CONST I32 c" using Nil(12) typeofval_is_i32 by fastforce
              have "wf_val a3" using Nil(13) by simp
              then obtain n where c: "c = mk_num__0 Inn_I32 (mk_uN n)" using a3 proof(induction a3)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  show ?case using num__case_0(2-) 
                  proof(induction "the (isabelle_reference_output_wasm2.size (valtype_Inn v_Inn))" var_x)
                    case (uN_case_0 i)
                    then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
                    proof(induction v_Inn) qed(auto)
                  qed
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              then show ?case proof(cases 
                  "length (REFS (fun_table (mk_state s' f) x_2)) < proj_uN_0 (the (proj_num__0 i)) + n \<or>
                  length (REFS (fun_table (mk_state s' f) x_1)) < proj_uN_0 (the (proj_num__0 j)) + n")
                case True
                then show ?thesis using table_copy_trap[of i j "mk_state s' f" x_2 n x_1] proji 
                  projj Nil(18)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros 
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
              next
                case False
                note outer = False
                then show ?thesis proof(cases n)
                  case 0
                  then show ?thesis using table_copy_zero[of i j n "mk_state s' f" x_2 x_1] proji 
                      projj Nil(18)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                next
                  case (Suc nat) 
                  then show ?thesis proof(cases "proj_uN_0 (the (proj_num__0 j)) \<le> proj_uN_0 (the (proj_num__0 i))")
                    case True
                    then show ?thesis using table_copy_le[of j i n "mk_state s' f" x_2 x_1] proji 
                      projj Nil(18) Suc
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros outer
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                  next
                    case False
                    then show ?thesis using table_copy_gt[of j i n "mk_state s' f" x_2 x_1] proji 
                      projj Nil(18) Suc
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros outer
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                  qed     
                qed
              qed
            next
              case (Cons a vs)
              then show ?case by simp
            qed
          qed
        qed
      qed
    next
      case (table_init x_1 C lim rt x_2)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons (2-) proof(induction vs)
            case Nil
            then show ?case by simp
          next
            case (Cons a3 vs)
            show ?case using Cons(2-) proof(induction vs)
              case Nil
              obtain j where a1: "a1 = val_CONST I32 j" using Nil(11) typeofval_is_i32 by fastforce
              have "wf_val a1" using Nil(12) by simp
              then have projj: "proj_num__0 j \<noteq> None" using a1 proof(induction a1)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto) 
              obtain i where a2: "a2 = val_CONST I32 i" using Nil(11) typeofval_is_i32 by fastforce
              have "wf_val a2" using Nil(12) by simp
              then have proji: "proj_num__0 i \<noteq> None" using a2 proof(induction a2)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto) 
              obtain c where a3: "a3 = val_CONST I32 c" using Nil(11) typeofval_is_i32 by fastforce
              have "wf_val a3" using Nil(12) by simp
              then obtain n where c: "c = mk_num__0 Inn_I32 (mk_uN n)" using a3 proof(induction a3)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  show ?case using num__case_0(2-) 
                  proof(induction "the (isabelle_reference_output_wasm2.size (valtype_Inn v_Inn))" var_x)
                    case (uN_case_0 i)
                    then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
                    proof(induction v_Inn) qed(auto)
                  qed
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              then show ?case 
              proof(cases "length (eleminst_REFS (fun_elem (mk_state s' f) x_2)) < proj_uN_0 (the (proj_num__0 i)) + n \<or>
    length (REFS (fun_table (mk_state s' f) x_1)) < proj_uN_0 (the (proj_num__0 j)) + n")
                case True
                then show ?thesis using table_init_trap[of i j "mk_state s' f" x_2 n x_1] proji projj Nil(17)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros 
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
              next
                case False
                then show ?thesis proof(cases n)
                  case 0
                  then show ?thesis using table_init_zero[of i j n "mk_state s' f" x_2 x_1] proji projj Nil(17)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                next
                  case (Suc nat)
                  then show ?thesis using table_init_succ[of i "mk_state s' f" x_2 j n x_1] proji projj Nil(17)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                qed
              qed
            next
              case (Cons a vs)
              then show ?case by simp
            qed
          qed
        qed
      qed
    next
      case (elem_drop x C rt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case using Step__elem_drop admininstr_instr.domintros admininstr_instr.psimps
          by fastforce
      next
        case (Cons a vs)
        then show ?case by simp
      qed
    next
      case (memory_size C mt) 
      obtain v_n where vn: "v_n * 64 * Ki = length (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
        using memory_size(11,1) proof(induction "mk_state s' f" "strip C")
        case mk_State_ok
        then show ?case proof(induction s')
          case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst 
                tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst 
                eleminst_lst elemtype_lst)
          have "(MEMS (frame_MODULE f) ! proj_uN_0 (mk_uN 0)) < length (store_MEMS s)" 
            using mk_Store_ok(18,22) proof(induction s f "strip C")
            case (mk_Frame_ok s v_moduleinst C' t_lst val_lst)
            then show ?case proof(induction s v_moduleinst C')
              case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
                    functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst 
                    exportinst_lst dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
              have "0 < length memtype_lst" using mk_Moduleinst_ok(33-) append_res_context_def
                strip_def
                by simp
              then have "Externaddr_ok s (externaddr_MEM (memaddr_lst ! 0)) (MEM (memtype_lst ! 0))"
                using list_all2_nth' mk_Moduleinst_ok
                by metis
              then show ?case 
                using Externaddr_ok_mem
                by (simp add: proj_uN_0.domintros proj_uN_0.psimps)
            qed
          qed
          then have "Meminst_ok s (fun_mem (mk_state s f) (mk_uN 0)) 
                  (memtype_lst ! (MEMS (frame_MODULE f) ! proj_uN_0 (mk_uN 0)))"
            using list_all2_nth[OF mk_Store_ok(4)] fun_mem.domintros fun_mem.psimps
            by (simp add: mk_Store_ok.hyps(13))
          then show ?case using mk_Store_ok(13,21) proof(induction s "fun_mem (mk_state s f) (mk_uN 0)" 
              "memtype_lst ! (MEMS (frame_MODULE f) ! proj_uN_0 (mk_uN 0))")
            case (mk_Meminst_ok v_n m_opt b_lst s)
            then show ?case
              by (metis meminst.select_convs(2) mult.assoc)
          qed
        qed
      qed
      have wfz: "wf_uN 32 (mk_uN 0)"
        using uN_case_0 by blast
      show ?case using memory_size proof(induction vs)
        case Nil
        then show ?case using Step_read__memory_size[OF vn wfz] Step.intros(2) by fastforce
      next
        case (Cons a vs)
        then show ?case by simp
      qed
    next
      case (memory_grow C mt)
       then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a2 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
            obtain c where c: "a2 = val_CONST I32 c" using Nil(9) typeofval_is_i32 by fastforce
            have "wf_val a2" using Nil(10) by simp
            then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a2)
              case (val_case_0 v_numtype var_0)
              then show ?case proof(induction v_numtype var_0)
                case (num__case_0 v_Inn var_x v_numtype)
                show ?case using num__case_0(2-) 
                proof(induction "the (isabelle_reference_output_wasm2.size (valtype_Inn v_Inn))"
                      var_x)
                  case (uN_case_0 i)
                  then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
                  proof(induction v_Inn) qed(auto)
                qed
              next
                case (num__case_1 v_Fnn var_x v_numtype)
                then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                proof(induction v_Fnn) qed(auto)
              qed
            qed(auto)
            obtain res where res: "fun_inv_signed_underscore 32 (0 - 1) res" 
              using fun_inv_signed_underscore_total by fastforce
            show ?case using Nil(15) memory_grow_fail[OF res] c n 
               admininstr_val.domintros admininstr_val.psimps admininstr_val_ref
               admininstr_instr.domintros admininstr_instr.psimps by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
    next
      case (memory_fill C mt) 
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons (2-) proof(induction vs)
            case Nil
            then show ?case by simp
          next
            case (Cons a3 vs)
            show ?case using Cons(2-) proof(induction vs)
              case Nil
               have wfz: "wf_uN 32 (mk_uN 0)"
        using uN_case_0 by blast
              obtain i where a1: "a1 = val_CONST I32 i" using Nil(9) typeofval_is_i32 by fastforce
              have "wf_val a1" using Nil(10) by simp
              then have proji: "proj_num__0 i \<noteq> None" using a1 proof(induction a1)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              obtain c where a3: "a3 = val_CONST I32 c" using Nil(9) typeofval_is_i32 by fastforce
              have "wf_val a3" using Nil(10) by simp
              then obtain n where c: "c = mk_num__0 Inn_I32 (mk_uN n)" using a3 proof(induction a3)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  show ?case using num__case_0(2-) 
                  proof(induction "the (isabelle_reference_output_wasm2.size (valtype_Inn v_Inn))" var_x)
                    case (uN_case_0 i)
                    then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
                    proof(induction v_Inn) qed(auto)
                  qed
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              then show ?case proof(cases "length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) < proj_uN_0 (the (proj_num__0 i)) + n")
                case True
                then show ?thesis using memory_fill_trap[of i "mk_state s' f" n a2] proji Nil(15)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros 
                  admininstr_instr.psimps Step.intros(2) a1 a3 c wfz by fastforce
              next
                case False
                then show ?thesis proof(cases n)
                  case 0
                  then show ?thesis using memory_fill_zero[of i n "mk_state s' f" a2] wfz proji Nil(15)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a3 c by fastforce
                next
                  case (Suc nat)
                  then show ?thesis using memory_fill_succ[of i n "mk_state s' f" a2] wfz proji Nil(15)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a3 c by fastforce
                qed
              qed
            next
              case (Cons a vs)
              then show ?case by simp
            qed
          qed
        qed
      qed
    next
      case (memory_copy C mt)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons (2-) proof(induction vs)
            case Nil
            then show ?case by simp
          next
            case (Cons a3 vs)
            show ?case using Cons(2-) proof(induction vs)
              case Nil
               have wfz: "wf_uN 32 (mk_uN 0)"
        using uN_case_0 by blast
              obtain j where a1: "a1 = val_CONST I32 j" using Nil(9) typeofval_is_i32 by fastforce
              have "wf_val a1" using Nil(10) by simp
              then have projj: "proj_num__0 j \<noteq> None" using a1 proof(induction a1)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              obtain i where a2: "a2 = val_CONST I32 i" using Nil(9) typeofval_is_i32 by fastforce
              have "wf_val a2" using Nil(10) by simp
              then have proji: "proj_num__0 i \<noteq> None" using a2 proof(induction a2)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              obtain c where a3: "a3 = val_CONST I32 c" using Nil(9) typeofval_is_i32 by fastforce
              have "wf_val a3" using Nil(10) by simp
              then obtain n where c: "c = mk_num__0 Inn_I32 (mk_uN n)" using a3 proof(induction a3)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  show ?case using num__case_0(2-) 
                  proof(induction "the (isabelle_reference_output_wasm2.size (valtype_Inn v_Inn))" var_x)
                    case (uN_case_0 i)
                    then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
                    proof(induction v_Inn) qed(auto)
                  qed
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              then show ?case proof(cases 
                  "length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) < proj_uN_0 (the (proj_num__0 i)) + n \<or>
                  length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) < proj_uN_0 (the (proj_num__0 j)) + n")
                case True
                then show ?thesis using memory_copy_trap[of i j "mk_state s' f" n] proji 
                  projj Nil(15)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros 
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c wfz by fastforce
              next
                case False
                note outer = False
                then show ?thesis proof(cases n)
                  case 0
                  then show ?thesis using memory_copy_zero[of i j n "mk_state s' f"] proji 
                      projj Nil(15) wfz
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                next
                  case (Suc nat) 
                  then show ?thesis proof(cases "proj_uN_0 (the (proj_num__0 j)) \<le> proj_uN_0 (the (proj_num__0 i))")
                    case True
                    then show ?thesis using memory_copy_le[of j i n "mk_state s' f"] proji 
                      projj Nil(15) wfz Suc
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros outer
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                  next
                    case False
                    then show ?thesis using memory_copy_gt[of j i n "mk_state s' f"] proji 
                      projj Nil(15) wfz Suc
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros outer
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                  qed     
                qed
              qed
            next
              case (Cons a vs)
              then show ?case by simp
            qed
          qed
        qed
      qed
    next
      case (memory_init C mt x)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons (2-) proof(induction vs)
            case Nil
            then show ?case by simp
          next
            case (Cons a3 vs)
            show ?case using Cons(2-) proof(induction vs)
              case Nil
              obtain j where a1: "a1 = val_CONST I32 j" using Nil(11) typeofval_is_i32 by fastforce
              have "wf_val a1" using Nil(12) by simp
              then have projj: "proj_num__0 j \<noteq> None" using a1 proof(induction a1)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto) 
              obtain i where a2: "a2 = val_CONST I32 i" using Nil(11) typeofval_is_i32 by fastforce
              have "wf_val a2" using Nil(12) by simp
              then have proji: "proj_num__0 i \<noteq> None" using a2 proof(induction a2)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto) 
               have wfz: "wf_uN 32 (mk_uN 0)"
        using uN_case_0 by blast
              obtain c where a3: "a3 = val_CONST I32 c" using Nil(11) typeofval_is_i32 by fastforce
              have "wf_val a3" using Nil(12) by simp
              then obtain n where c: "c = mk_num__0 Inn_I32 (mk_uN n)" using a3 proof(induction a3)
                case (val_case_0 v_numtype var_0)
                then show ?case proof(induction v_numtype var_0)
                  case (num__case_0 v_Inn var_x v_numtype)
                  show ?case using num__case_0(2-) 
                  proof(induction "the (isabelle_reference_output_wasm2.size (valtype_Inn v_Inn))" var_x)
                    case (uN_case_0 i)
                    then show ?case using numtype_Inn.domintros numtype_Inn.psimps 
                    proof(induction v_Inn) qed(auto)
                  qed
                next
                  case (num__case_1 v_Fnn var_x v_numtype)
                  then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps 
                  proof(induction v_Fnn) qed(auto)
                qed
              qed(auto)
              then show ?case 
              proof(cases "length (datainst_BYTES (fun_data (mk_state s' f) x)) < proj_uN_0 (the (proj_num__0 i)) + n \<or>
    length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) < proj_uN_0 (the (proj_num__0 j)) + n")
                case True
                then show ?thesis using memory_init_trap[of i j "mk_state s' f" x n] proji projj Nil(17)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros 
                  admininstr_instr.psimps Step.intros(2) wfz a1 a2 a3 c by fastforce
              next
                case False
                then show ?thesis proof(cases n)
                  case 0
                  then show ?thesis using memory_init_zero[of i j n "mk_state s' f" x] wfz proji projj Nil(17)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c by fastforce
                next
                  case (Suc nat)
                  then show ?thesis using memory_init_succ[of i "mk_state s' f" x j n] proji projj Nil(17)
                  admininstr_val.domintros admininstr_val.psimps admininstr_instr.domintros False
                  admininstr_instr.psimps Step.intros(2) a1 a2 a3 c wfz by fastforce
                qed
              qed
            next
              case (Cons a vs)
              then show ?case by simp
            qed
          qed
        qed
      qed
    next
      case (data_drop x C)
      then show ?case proof(induction vs)
        case Nil
        then show ?case using Step__data_drop admininstr_instr.domintros admininstr_instr.psimps
          by fastforce
      next
        case (Cons a vs)
        then show ?case by simp
      qed
    next
      case (load_val C mt nt v_memarg)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain c where c: "a = val_CONST I32 c" using typeofval_is_i32 by fastforce
          have "wf_val a" using Nil by simp
          then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case proof(induction v_Inn)
               case Inn_I32
               then show ?case proof(induction var_x) qed(auto)
              qed(auto)
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.psimps numtype_Fnn.domintros
              proof(induction v_Fnn) qed(auto)
            qed
          qed(auto)
          then show ?case proof(cases
              "(n + proj_uN_0 (OFFSET v_memarg) + (the (size (valtype_numtype nt))) div 8) >
                (length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) :: nat)")
            case True
            have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis
              using load_num_trap[of c nt "mk_state s' f" v_memarg] n c proj_num__0.domintros 
proj_uN_0.domintros proj_uN_0.psimps
                proj_num__0.psimps Nil(3,17) Step.intros(2) admininstr_val.domintros 
              admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps True
              by fastforce
          next
            case False
            then have "length (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size (valtype_numtype nt)) div 8)) = 
  the (size (valtype_numtype nt)) div 8" 
              using length_list_slice n proj_uN_0.domintros proj_uN_0.psimps
              proj_num__0.domintros proj_num__0.psimps
              by (metis linorder_not_less option.sel)
            then have bs: "nbytes_underscore nt (inv_nbytes_underscore nt ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size (valtype_numtype nt)) div 8))) =
    list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size (valtype_numtype nt)) div 8)" 
              using nbytes_inv by fastforce
            have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
              using Nil(13,1) proof(induction "mk_state s' f" "strip C")
              case mk_State_ok
              then show ?case proof(induction s')
                case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                thm fun_mem.psimps
                show ?case using mk_Store_ok(14,13) proof(induction s)
                  case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                  then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                    using 
                        fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                        proj_uN_0.psimps
                    by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                  then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                    case (meminst_case_underscore var_0 var_1_lst)
                    then show ?case
                      by (metis meminst.select_convs(2))
                  qed
                qed
              qed
            qed
            then have "list_all wf_byte ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size (valtype_numtype nt)) div 8))"
              using list_all_list_slice by auto
            then have wfbs: "wf_num_underscore nt (inv_nbytes_underscore nt ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size (valtype_numtype nt)) div 8)))"
              using inv_nbytes__is_wf bs by auto
             have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis using load_num_val[of c nt "inv_nbytes_underscore nt _" 
                  "mk_state s' f" v_memarg] Nil(3,17) c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs
              by fastforce
          qed  
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (load_pack C mt v_memarg v_M v_Inn v_sx)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain c where c: "a = val_CONST I32 c" using typeofval_is_i32 by fastforce
          have "wf_val a" using Nil by simp
          then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case proof(induction v_Inn)
               case Inn_I32
               then show ?case proof(induction var_x) qed(auto)
              qed(auto)
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.psimps numtype_Fnn.domintros
              proof(induction v_Fnn) qed(auto)
            qed
          qed(auto)
          then show ?case proof(cases
              "(n + proj_uN_0 (OFFSET v_memarg) + v_M div 8) >
                (length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) :: nat)")
            case True
            have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis
              using load_pack_trap[of c "mk_state s' f" v_memarg v_M] n c proj_num__0.domintros 
proj_uN_0.domintros proj_uN_0.psimps
                proj_num__0.psimps Nil(16) Step.intros(2) admininstr_val.domintros 
              admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps True
              by fastforce
          next
            case False
            then have "length (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_M div 8)) = 
  v_M div 8" 
              using length_list_slice n proj_uN_0.domintros proj_uN_0.psimps
              proj_num__0.domintros proj_num__0.psimps
              by (metis linorder_not_less option.sel)
            then have bs: "ibytes_underscore v_M (inv_ibytes_underscore v_M ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_M div 8))) =
    list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_M div 8)" 
              using ibytes_inv by fastforce
            have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
              using Nil(12,1) proof(induction "mk_state s' f" "strip C")
              case mk_State_ok
              then show ?case proof(induction s')
                case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                thm fun_mem.psimps
                show ?case using mk_Store_ok(14,13) proof(induction s)
                  case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                  then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                    using 
                        fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                        proj_uN_0.psimps
                    by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                  then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                    case (meminst_case_underscore var_0 var_1_lst)
                    then show ?case
                      by (metis meminst.select_convs(2))
                  qed
                qed
              qed
            qed
            then have "list_all wf_byte ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_M div 8))"
              using list_all_list_slice by auto
            then have wfbs: "wf_uN v_M (inv_ibytes_underscore v_M ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_M div 8)))"
              using inv_ibytes__is_wf bs by auto
             have wfz: "wf_uN 32 (mk_uN 0)"
               using uN_case_0 by blast
             have " isabelle_reference_output_wasm2.size (valtype_Inn v_Inn) \<noteq> None"
               using valtype_Inn.domintros valtype_Inn.psimps size.domintros size.psimps proof(induction v_Inn) 
             qed(auto)
            then show ?thesis using load_pack_val[of v_Inn c v_M "inv_ibytes_underscore v_M _" 
                  "mk_state s' f" v_memarg] Nil(16) c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz
              by fastforce
          qed  
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (store_val C mt nt v_memarg)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            then obtain c1 where a1: "a1 = val_CONST I32 c1" using typeofval_is_i32 by fastforce
            have "wf_val a1" using Nil by simp
            then have c1: "proj_num__0 c1 \<noteq> None" using a1 proof(induction a1)
              case (val_case_0 v_numtype var_0)
              then show ?case proof(induction v_numtype var_0)
                case (num__case_0 v_Inn var_x v_numtype)
                then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
              next
                case (num__case_1 v_Fnn var_x v_numtype)
                then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                proof(induction v_Fnn) qed(auto)
              qed
            qed(auto)
            obtain c2 where a2: "a2 = val_CONST nt c2" using typeofval_is_nt Nil by fastforce
            show ?case using 
              store_num_val[OF c1 Nil(3)] a1 a2 Nil(17) admininstr_val.domintros admininstr_val.psimps
    admininstr_instr.domintros admininstr_instr.psimps
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (store_pack C mt v_memarg v_M v_Inn)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            then obtain c1 where a1: "a1 = val_CONST I32 c1" using typeofval_is_i32 by fastforce
            have "wf_val a1" using Nil by simp
            then have c1: "proj_num__0 c1 \<noteq> None" using a1 proof(induction a1)
              case (val_case_0 v_numtype var_0)
              then show ?case proof(induction v_numtype var_0)
                case (num__case_0 v_Inn var_x v_numtype)
                then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
              next
                case (num__case_1 v_Fnn var_x v_numtype)
                then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                proof(induction v_Fnn) qed(auto)
              qed
            qed(auto)
            obtain c2 where a2: "a2 = val_CONST (numtype_Inn v_Inn) c2" 
              using typeofval_is_nt Nil valtype_numtype_Inn by fastforce
            have "wf_val a2" using Nil by simp
            then have c2: "proj_num__0 c2 \<noteq> None" using a2 proof(induction a2)
              case (val_case_0 v_numtype var_0)
              then show ?case proof(induction v_numtype var_0)
                case (num__case_0 v_Inn var_x v_numtype)
                then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
              next
                case (num__case_1 v_Fnn var_x v_numtype)
                then show ?case using Inn_Fnn_diff
                  by (metis val.inject(1))
              qed
            qed(auto)
            have sz: "isabelle_reference_output_wasm2.size (valtype_Inn v_Inn) \<noteq> None"
              using size.domintros size.psimps valtype_Inn.domintros valtype_Inn.psimps
            proof(induction v_Inn) qed(auto)
            show ?case using 
              store_pack_val[OF c1 sz c2] a1 a2 Nil(16) admininstr_val.domintros admininstr_val.psimps
    admininstr_instr.domintros admininstr_instr.psimps
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vload_val C mt v_memarg)
       then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain c where c: "a = val_CONST I32 c" using typeofval_is_i32 by fastforce
          have "wf_val a" using Nil by simp
          then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case proof(induction v_Inn)
               case Inn_I32
               then show ?case proof(induction var_x) qed(auto)
              qed(auto)
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.psimps numtype_Fnn.domintros
              proof(induction v_Fnn) qed(auto)
            qed
          qed(auto)
          then show ?case proof(cases
              "(n + proj_uN_0 (OFFSET v_memarg) + (the (size (valtype_V128))) div 8) >
                (length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) :: nat)")
            case True
            have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis
              using vload_oob[of c "mk_state s' f" v_memarg] n c proj_num__0.domintros 
proj_uN_0.domintros proj_uN_0.psimps
                proj_num__0.psimps Nil(3,17) Step.intros(2) admininstr_val.domintros 
              admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps True
              by fastforce
          next
            case False
            then have "length (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size valtype_V128) div 8)) = 
  the (size valtype_V128) div 8" 
              using length_list_slice n proj_uN_0.domintros proj_uN_0.psimps
              proj_num__0.domintros proj_num__0.psimps
              by (metis linorder_not_less option.sel)
            then have bs: "vbytes_underscore V128 (inv_vbytes_underscore V128 ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size valtype_V128) div 8))) =
    list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size valtype_V128) div 8)" 
              using vbytes_inv valtype_vectype.domintros valtype_vectype.psimps by fastforce
            have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
              using Nil(13,1) proof(induction "mk_state s' f" "strip C")
              case mk_State_ok
              then show ?case proof(induction s')
                case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                thm fun_mem.psimps
                show ?case using mk_Store_ok(14,13) proof(induction s)
                  case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                  then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                    using 
                        fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                        proj_uN_0.psimps
                    by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                  then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                    case (meminst_case_underscore var_0 var_1_lst)
                    then show ?case
                      by (metis meminst.select_convs(2))
                  qed
                qed
              qed
            qed
            then have "list_all wf_byte ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size (valtype_V128)) div 8))"
              using list_all_list_slice by auto
            then have wfbs: "wf_uN 128 (inv_vbytes_underscore V128 ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (the (isabelle_reference_output_wasm2.size (valtype_V128)) div 8)))"
              using inv_vbytes__is_wf[of _ _ V128] bs size.domintros size.psimps valtype_vectype.domintros
              valtype_vectype.psimps by fastforce
             have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis using Step_read__vload_val[of c "inv_vbytes_underscore V128 _" 
                  "mk_state s' f" v_memarg] Nil(3,17) c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs
              by fastforce
          qed  
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vload_pack C mt v_memarg v_M v_N v_sx)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain c where c: "a = val_CONST I32 c" using typeofval_is_i32 by fastforce
          have "wf_val a" using Nil by simp
          then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case proof(induction v_Inn)
                case Inn_I32
                then show ?case proof(induction var_x) qed(auto)
              qed(auto)
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.psimps numtype_Fnn.domintros
              proof(induction v_Fnn) qed(auto)
            qed
          qed(auto)
          then show ?case proof(cases
              "(n + proj_uN_0 (OFFSET v_memarg) + v_M * v_N div 8) >
                (length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) :: nat)")
            case True
            have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis
              using vload_shape_oob[of c "mk_state s' f" v_memarg] n c proj_num__0.domintros 
                proj_uN_0.domintros proj_uN_0.psimps
                proj_num__0.psimps Nil(3,16) Step.intros(2) admininstr_val.domintros 
                admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps True
              by fastforce
          next
            case False


            have "wf_vloadop_underscore V128 (SHAPEX_underscore (mk_sz v_M) v_N v_sx)"
              using Nil(6) proof(induction "instr_sc6 (VLOAD V128 (Some (SHAPEX_underscore (mk_sz v_M) v_N v_sx)) v_memarg)")
            qed(auto)
            then show ?thesis using Nil proof(induction "SHAPEX_underscore (mk_sz v_M) v_N v_sx")
              case (vloadop__case_0 v_vectype)
              then show ?case proof(induction "mk_sz v_M")
                case sz_case_0
                have 1: "holds_upto (\<lambda>k. proj_num__0 c \<noteq> None) v_N" 
                  using n proj_num__0.domintros proj_num__0.psimps holds_upto_def by simp
                have 4: "wf_uN 32 (mk_uN 0)" using uN_case_0 by simp
                have 7: "v_N =
                      length
                (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1]))" using length_map length_upto
                  by simp
                have "\<forall>k<length (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1])). (\<lambda>k j. ibytes_underscore v_M j =
        list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
         (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)) k ((map (\<lambda>k. inv_ibytes_underscore v_M

            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1])) ! k)"
                  apply(auto)
                  subgoal for k
                  proof - 
                    assume le: "k < v_N"
                    have "v_M mod 8 = 0" using sz_case_0(1) proof 
                      assume "(v_M = 8 \<or> v_M = 16) \<or> v_M = 32"
                      then show ?thesis proof
                        assume "v_M = 8 \<or> v_M = 16" 
                        then show ?thesis proof
                          assume "v_M = 8" then show ?thesis by simp
                        next assume "v_M = 16" then show ?thesis by simp
                        qed
                      next
                        assume "v_M = 32" then show ?thesis by simp
                      qed
                    next
                      assume "v_M = 64" then show ?thesis by simp 
                    qed
                    then have "k * v_M div 8 + v_M div 8 \<le> v_M * v_N div 8"
                      by (metis (no_types, lifting) Suc_leI add.commute add_cancel_left_left div_add1_eq div_le_mono le
                          mod_div_trivial mult.commute mult_Suc_right nat_mult_le_cancel_disj)
                    then have "proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8 +
            v_M div 8 \<le> length (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))" 
                      using False proj_num__0.domintros proj_num__0.psimps
                        proj_uN_0.domintros proj_uN_0.psimps n
                      by simp
                    then have "length ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)) =
v_M div 8" 
                      using length_list_slice
                      by auto
                    then show "ibytes_underscore v_M
     (inv_ibytes_underscore v_M
       (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
         (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8))) =
    list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)"
                      using ibytes_inv
                      by blast 
                  qed
                  done
                then have 2: "list_alli
 (\<lambda>k j. ibytes_underscore v_M j =
        list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
         (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8))
 (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1]))" using list_alli_forall
                  by meson

                show ?case using sz_case_0(1) proof
                  assume "(v_M = 8 \<or> v_M = 16) \<or> v_M = 32" 
                  then show ?thesis proof
                    assume "v_M = 8 \<or> v_M = 16" 
                    then show ?thesis proof 
                      assume m: "v_M = 8" 
                      have 3: "jsize Jnn_I16 = v_M * 2" using jsize.domintros jsize.psimps m
                          lsize.domintros lsize.psimps lanetype_Jnn.domintros lanetype_Jnn.psimps
                          size.domintros size.psimps valtype_numtype.domintros valtype_numtype.psimps psize.domintros
                          psize.psimps
                        by simp
                      have vec128: "v_vectype = V128" proof(cases v_vectype) qed(auto)
                      have 5: "wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_N))" 
                        using sz_case_0(2) proj_sz_0.domintros proj_sz_0.psimps 
                          shape_case_0 vec128 vsize.domintros vsize.psimps dim_case_0
                          lsize.domintros lsize.psimps size.domintros size.psimps valtype_numtype.domintros
                          valtype_numtype.psimps psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                          lanetype_Jnn.domintros lanetype_Jnn.psimps m by force
                      have "\<forall> k < length (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1])). 
(\<lambda>j. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_N)))
       (mk_lane__0 Jnn_I16 (extend__underscore v_M (jsize Jnn_I16) v_sx j)))
((map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1])) ! k)"
                        apply(auto)
                        subgoal for k
                        proof - 
                          assume "k < v_N"
                          have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
                            using Nil(12,1) proof(induction "mk_state s' f" "strip C")
                            case mk_State_ok
                            then show ?case proof(induction s')
                              case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                              thm fun_mem.psimps
                              show ?case using mk_Store_ok(14,13) proof(induction s)
                                case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                                then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                                  using 
                                    fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                                    proj_uN_0.psimps
                                  by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                                then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                                  case (meminst_case_underscore var_0 var_1_lst)
                                  then show ?case
                                    by (metis meminst.select_convs(2))
                                qed
                              qed
                            qed
                          qed
                          then show "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_N)))
     (mk_lane__0 Jnn_I16
       (extend__underscore v_M (jsize Jnn_I16) v_sx
         (inv_ibytes_underscore v_M
           (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
             (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8)
             (v_M div 8)))))" 
                            using lane__case_0[of Jnn_I16]
                              fun_lanetype.domintros fun_lanetype.psimps extend___is_wf
                              inv_ibytes__is_wf list_all_list_slice
                            by (metis "3" lanetype_Jnn.domintros(4) lanetype_Jnn.psimps(4) lsize.domintros(6) lsize.psimps(6) m
                                mult.commute numeral_Bit0_eq_double psize.domintros(2) psize.psimps(2))
                        qed
                        done
                      then have 6: "list_all
 (\<lambda>j. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_N)))
       (mk_lane__0 Jnn_I16 (extend__underscore v_M (jsize Jnn_I16) v_sx j)))
 (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1]))" 
                        using list_all_length
                        by blast
                      show ?thesis using vload_shape_val[OF 1 2 3 _ 4 5 6 7] sz_case_0(18) Step.intros(2)
                          n c vec128 admininstr_instr.domintros admininstr_instr.psimps admininstr_val.domintros admininstr_val.psimps
                        by auto
                    next 
                      assume m: "v_M = 16"
                      have 3: "jsize Jnn_I32 = v_M * 2" using jsize.domintros jsize.psimps m
                          lsize.domintros lsize.psimps lanetype_Jnn.domintros lanetype_Jnn.psimps
                          size.domintros size.psimps valtype_numtype.domintros valtype_numtype.psimps psize.domintros
                          psize.psimps
                        by simp
                      have vec128: "v_vectype = V128" proof(cases v_vectype) qed(auto)
                      have 5: "wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_N))" 
                        using sz_case_0(2) proj_sz_0.domintros proj_sz_0.psimps 
                          shape_case_0 vec128 vsize.domintros vsize.psimps dim_case_0
                          lsize.domintros lsize.psimps size.domintros size.psimps valtype_numtype.domintros
                          valtype_numtype.psimps psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                          lanetype_Jnn.domintros lanetype_Jnn.psimps m by force
                      have "\<forall> k < length (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1])). 
(\<lambda>j. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_N)))
       (mk_lane__0 Jnn_I32 (extend__underscore v_M (jsize Jnn_I32) v_sx j)))
((map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1])) ! k)"
                        apply(auto)
                        subgoal for k
                        proof - 
                          assume "k < v_N"
                          have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
                            using Nil(12,1) proof(induction "mk_state s' f" "strip C")
                            case mk_State_ok
                            then show ?case proof(induction s')
                              case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                              thm fun_mem.psimps
                              show ?case using mk_Store_ok(14,13) proof(induction s)
                                case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                                then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                                  using 
                                    fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                                    proj_uN_0.psimps
                                  by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                                then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                                  case (meminst_case_underscore var_0 var_1_lst)
                                  then show ?case
                                    by (metis meminst.select_convs(2))
                                qed
                              qed
                            qed
                          qed
                          then show "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_N)))
     (mk_lane__0 Jnn_I32
       (extend__underscore v_M (jsize Jnn_I32) v_sx
         (inv_ibytes_underscore v_M
           (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
             (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8)
             (v_M div 8)))))" 
                            using lane__case_0[of Jnn_I32]
                              fun_lanetype.domintros fun_lanetype.psimps extend___is_wf
                              inv_ibytes__is_wf list_all_list_slice
                            by (metis "3" lanetype_Jnn.domintros(1) lanetype_Jnn.psimps(1) lsize.domintros(1) lsize.psimps(1) m
                                mult.commute numeral_Bit0_eq_double option.sel size.domintros(1) size.psimps(1)
                                valtype_numtype.simps(1))
                        qed
                        done
                      then have 6: "list_all
 (\<lambda>j. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_N)))
       (mk_lane__0 Jnn_I32 (extend__underscore v_M (jsize Jnn_I32) v_sx j)))
 (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1]))" 
                        using list_all_length
                        by blast
                      show ?thesis using vload_shape_val[OF 1 2 3 _ 4 5 6 7] sz_case_0(18) Step.intros(2)
                          n c vec128 admininstr_instr.domintros admininstr_instr.psimps admininstr_val.domintros admininstr_val.psimps
                        by auto
                    qed
                  next
                    assume m: "v_M = 32" 
                    have 3: "jsize Jnn_I64 = v_M * 2" using jsize.domintros jsize.psimps m
                        lsize.domintros lsize.psimps lanetype_Jnn.domintros lanetype_Jnn.psimps
                        size.domintros size.psimps valtype_numtype.domintros valtype_numtype.psimps psize.domintros
                        psize.psimps
                      by simp
                    have vec128: "v_vectype = V128" proof(cases v_vectype) qed(auto)
                    have 5: "wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_N))" 
                      using sz_case_0(2) proj_sz_0.domintros proj_sz_0.psimps 
                        shape_case_0 vec128 vsize.domintros vsize.psimps dim_case_0
                        lsize.domintros lsize.psimps size.domintros size.psimps valtype_numtype.domintros
                        valtype_numtype.psimps psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                        lanetype_Jnn.domintros lanetype_Jnn.psimps m by force
                    have "\<forall> k < length (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1])). 
(\<lambda>j. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_N)))
       (mk_lane__0 Jnn_I64 (extend__underscore v_M (jsize Jnn_I64) v_sx j)))
((map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1])) ! k)"
                      apply(auto)
                      subgoal for k
                      proof - 
                        assume "k < v_N"
                        have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
                          using Nil(12,1) proof(induction "mk_state s' f" "strip C")
                          case mk_State_ok
                          then show ?case proof(induction s')
                            case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                            thm fun_mem.psimps
                            show ?case using mk_Store_ok(14,13) proof(induction s)
                              case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                              then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                                using 
                                  fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                                  proj_uN_0.psimps
                                by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                              then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                                case (meminst_case_underscore var_0 var_1_lst)
                                then show ?case
                                  by (metis meminst.select_convs(2))
                              qed
                            qed
                          qed
                        qed
                        then show "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_N)))
     (mk_lane__0 Jnn_I64
       (extend__underscore v_M (jsize Jnn_I64) v_sx
         (inv_ibytes_underscore v_M
           (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
             (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8)
             (v_M div 8)))))" 
                          using lane__case_0[of Jnn_I64]
                            fun_lanetype.domintros fun_lanetype.psimps extend___is_wf
                            inv_ibytes__is_wf list_all_list_slice
                          by (metis "3" lanetype_Jnn.domintros(2) lanetype_Jnn.psimps(2) lsize.domintros(2) lsize.psimps(2) m
                              mult.commute numeral_Bit0_eq_double option.sel size.domintros(2) size.psimps(2)
                              valtype_numtype.domintros(2) valtype_numtype.psimps(2))
                      qed
                      done
                    then have 6: "list_all
 (\<lambda>j. wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_N)))
       (mk_lane__0 Jnn_I64 (extend__underscore v_M (jsize Jnn_I64) v_sx j)))
 (map (\<lambda>k. inv_ibytes_underscore v_M
            (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
              (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg) + k * v_M div 8) (v_M div 8)))
   (map nat [0..int v_N - 1]))" 
                      using list_all_length
                      by blast
                    show ?thesis using vload_shape_val[OF 1 2 3 _ 4 5 6 7] sz_case_0(18) Step.intros(2)
                        n c vec128 admininstr_instr.domintros admininstr_instr.psimps admininstr_val.domintros admininstr_val.psimps
                      by auto
                  qed
                next 
                  assume m: "v_M = 64" 
                  have vec128: "v_vectype = V128" proof(cases v_vectype) qed(auto)
                  then show ?thesis using sz_case_0(2) m vsize.domintros vsize.psimps 
                      proj_sz_0.domintros proj_sz_0.psimps
                    by auto
                qed
              qed 
            qed 
          qed
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vload_splat C mt v_memarg v_n)
       then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain c where c: "a = val_CONST I32 c" using typeofval_is_i32 by fastforce
          have "wf_val a" using Nil by simp
          then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case proof(induction v_Inn)
               case Inn_I32
               then show ?case proof(induction var_x) qed(auto)
              qed(auto)
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.psimps numtype_Fnn.domintros
              proof(induction v_Fnn) qed(auto)
            qed
          qed(auto) 
          then show ?case proof(cases 
              "(n + proj_uN_0 (OFFSET v_memarg) + v_n div 8) >
                (length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) :: nat)")
            case True
            have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis
              using vload_splat_oob[of c "mk_state s' f" v_memarg v_n] n c proj_num__0.domintros 
proj_uN_0.domintros proj_uN_0.psimps
                proj_num__0.psimps Nil(16) Step.intros(2) admininstr_val.domintros 
              admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps True
              by fastforce
          next
            case False
            then have "length (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)) = 
  v_n div 8" 
              using length_list_slice n proj_uN_0.domintros proj_uN_0.psimps
              proj_num__0.domintros proj_num__0.psimps
              by (metis linorder_not_less option.sel)
            then have bs: "ibytes_underscore v_n (inv_ibytes_underscore v_n ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8))) =
    list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)" 
              using ibytes_inv by fastforce
            have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
              using Nil(12,1) proof(induction "mk_state s' f" "strip C")
              case mk_State_ok
              then show ?case proof(induction s')
                case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                thm fun_mem.psimps
                show ?case using mk_Store_ok(14,13) proof(induction s)
                  case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                  then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                    using 
                        fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                        proj_uN_0.psimps
                    by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                  then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                    case (meminst_case_underscore var_0 var_1_lst)
                    then show ?case
                      by (metis meminst.select_convs(2))
                  qed
                qed
              qed
            qed
            then have "list_all wf_byte ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8))"
              using list_all_list_slice by auto
            then have wfbs: "wf_uN v_n (inv_ibytes_underscore v_n ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)))"
              using inv_ibytes__is_wf bs by auto
             have wfz: "wf_uN 32 (mk_uN 0)"
               using uN_case_0 by blast
             have "wf_vloadop_underscore V128 (SPLAT (mk_sz v_n))" using Nil(6)
             proof(induction "instr_sc6 (VLOAD V128 (Some (SPLAT (mk_sz v_n))) v_memarg)")
             qed(auto)
             then show ?thesis proof(induction V128 "SPLAT (mk_sz v_n)")
               case vloadop__case_1
               then show ?case proof(induction "mk_sz v_n")
                 case sz_case_0
                 then show ?case proof
                   assume "(v_n = 8 \<or> v_n = 16) \<or> v_n = 32"
                   then show ?thesis proof 
                     assume "v_n = 8 \<or> v_n = 16" 
                     then show ?thesis proof
                       assume vn: "v_n = 8" 
                       have 1: "v_n = jsize Jnn_I8" using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 2: " wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n)))"
                         using shape_case_0 dim_case_0 vn lsize.domintros lsize.psimps
                           valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps
                           psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                         lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 3: "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))))
     (mk_lane__0 Jnn_I8 (mk_uN (proj_uN_0 (inv_ibytes_underscore v_n (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg)) (v_n div 8))))))"
                         using lane__case_0 fun_lanetype.domintros fun_lanetype.psimps wfbs
                           mk_uN_proj_uN_0 1 jsize.domintros jsize.psimps by simp
                       then show ?thesis using vload_splat_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(16) c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz 1 2 3
              by fastforce
                     next
                       assume vn: "v_n = 16" 
                       have 1: "v_n = jsize Jnn_I16" using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 2: " wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n)))"
                         using shape_case_0 dim_case_0 vn lsize.domintros lsize.psimps
                           valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps
                           psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                         lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 3: "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))))
     (mk_lane__0 Jnn_I16 (mk_uN (proj_uN_0 (inv_ibytes_underscore v_n (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg)) (v_n div 8))))))"
                         using lane__case_0 fun_lanetype.domintros fun_lanetype.psimps wfbs
                           mk_uN_proj_uN_0 1 jsize.domintros jsize.psimps by simp
                       then show ?thesis using vload_splat_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(16) c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz 1 2 3
              by fastforce
                     qed
                   next 
                     assume vn: "v_n = 32" 
                       have 1: "v_n = jsize Jnn_I32" using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 2: " wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n)))"
                         using shape_case_0 dim_case_0 vn lsize.domintros lsize.psimps
                           valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps
                           psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                         lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 3: "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))))
     (mk_lane__0 Jnn_I32 (mk_uN (proj_uN_0 (inv_ibytes_underscore v_n (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg)) (v_n div 8))))))"
                         using lane__case_0 fun_lanetype.domintros fun_lanetype.psimps wfbs
                           mk_uN_proj_uN_0 1 jsize.domintros jsize.psimps by simp
                       then show ?thesis using vload_splat_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(16) c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz 1 2 3
              by fastforce
                   qed
                 next 
                   assume vn: "v_n = 64"
                       have 1: "v_n = jsize Jnn_I64" using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 2: " wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n)))"
                         using shape_case_0 dim_case_0 vn lsize.domintros lsize.psimps
                           valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps
                           psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                         lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 3: "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))))
     (mk_lane__0 Jnn_I64 (mk_uN (proj_uN_0 (inv_ibytes_underscore v_n (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg)) (v_n div 8))))))"
                         using lane__case_0 fun_lanetype.domintros fun_lanetype.psimps wfbs
                           mk_uN_proj_uN_0 1 jsize.domintros jsize.psimps by simp
                       then show ?thesis using vload_splat_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(16) c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz 1 2 3
              by fastforce
                 qed
               qed
             qed
          qed  
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vload_zero C mt v_memarg v_n)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then obtain c where c: "a = val_CONST I32 c" using typeofval_is_i32 by fastforce
          have "wf_val a" using Nil by simp
          then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case proof(induction v_Inn)
               case Inn_I32
               then show ?case proof(induction var_x) qed(auto)
              qed(auto)
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.psimps numtype_Fnn.domintros
              proof(induction v_Fnn) qed(auto)
            qed
          qed(auto)
          then show ?case proof(cases
              "(n + proj_uN_0 (OFFSET v_memarg) + v_n div 8) >
                (length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) :: nat)")
            case True
            have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis
              using vload_zero_oob[of c "mk_state s' f" v_memarg v_n] n c proj_num__0.domintros 
proj_uN_0.domintros proj_uN_0.psimps
                proj_num__0.psimps Nil(16) Step.intros(2) admininstr_val.domintros 
              admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps True
              by fastforce
          next
            case False
            then have "length (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)) = 
  v_n div 8" 
              using length_list_slice n proj_uN_0.domintros proj_uN_0.psimps
              proj_num__0.domintros proj_num__0.psimps
              by (metis linorder_not_less option.sel)
            then have bs: "ibytes_underscore v_n (inv_ibytes_underscore v_n ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8))) =
    list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)" 
              using ibytes_inv by fastforce
            have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
              using Nil(12,1) proof(induction "mk_state s' f" "strip C")
              case mk_State_ok
              then show ?case proof(induction s')
                case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                thm fun_mem.psimps
                show ?case using mk_Store_ok(14,13) proof(induction s)
                  case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                  then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                    using 
                        fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                        proj_uN_0.psimps
                    by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                  then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                    case (meminst_case_underscore var_0 var_1_lst)
                    then show ?case
                      by (metis meminst.select_convs(2))
                  qed
                qed
              qed
            qed
            then have "list_all wf_byte ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8))"
              using list_all_list_slice by auto
            then have wfbs: "wf_uN v_n (inv_ibytes_underscore v_n ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)))"
              using inv_ibytes__is_wf bs by auto
             have wfz: "wf_uN 32 (mk_uN 0)"
               using uN_case_0 by blast
            then show ?thesis using vload_zero_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(16) c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz
              by fastforce
          qed  
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    next
      case (vload_lane C mt v_memarg v_n v_laneidx)
       then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp 
        next
          case (Cons b vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
          then obtain c where c: "a = val_CONST I32 c" using typeofval_is_i32 by fastforce
          have "wf_val a" using Nil by simp
          then obtain n where n: "c = mk_num__0 Inn_I32 (mk_uN n)" using c proof(induction a)
            case (val_case_0 v_numtype var_0)
            then show ?case proof(induction v_numtype var_0)
              case (num__case_0 v_Inn var_x v_numtype)
              then show ?case proof(induction v_Inn)
               case Inn_I32
               then show ?case proof(induction var_x) qed(auto)
              qed(auto)
            next
              case (num__case_1 v_Fnn var_x v_numtype)
              then show ?case using numtype_Fnn.psimps numtype_Fnn.domintros
              proof(induction v_Fnn) qed(auto)
            qed
          qed(auto) 
          obtain vec where vec: "b = val_VCONST V128 vec" using typeofval_is_v128 Nil by fastforce
          then show ?case proof(cases 
              "(n + proj_uN_0 (OFFSET v_memarg) + v_n div 8) >
                (length (BYTES (fun_mem (mk_state s' f) (mk_uN 0))) :: nat)")
            case True
            have "wf_uN 32 (mk_uN 0)"
              using uN_case_0 by blast
            then show ?thesis
              using vload_lane_oob[of c "mk_state s' f" v_memarg v_n] n c proj_num__0.domintros 
proj_uN_0.domintros proj_uN_0.psimps
                proj_num__0.psimps Nil(17) Step.intros(2) admininstr_val.domintros vec
              admininstr_val.psimps admininstr_instr.domintros admininstr_instr.psimps True
              by fastforce
          next
            case False
            then have "length (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)) = 
  v_n div 8" 
              using length_list_slice n proj_uN_0.domintros proj_uN_0.psimps
              proj_num__0.domintros proj_num__0.psimps
              by (metis linorder_not_less option.sel)
            then have bs: "ibytes_underscore v_n (inv_ibytes_underscore v_n ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8))) =
    list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)" 
              using ibytes_inv by fastforce
            have "list_all wf_byte (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))"
              using Nil(13,1) proof(induction "mk_state s' f" "strip C")
              case mk_State_ok
              then show ?case proof(induction s')
                case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst datatype_lst eleminst_lst elemtype_lst)
                thm fun_mem.psimps
                show ?case using mk_Store_ok(14,13) proof(induction s)
                  case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
                  then have "wf_meminst (fun_mem (mk_state \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
              store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr> f) (mk_uN 0))" 
                    using 
                        fun_mem.domintros fun_mem.psimps proj_uN_0.domintros
                        proj_uN_0.psimps
                    by (metis bot_nat_0.extremum mem_is_wf mk_Store_ok.hyps(13) mk_Store_ok.prems(3) uN_case_0)
                  then show ?case proof(induction "fun_mem
     (mk_state
       \<lparr>store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst,
          store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst\<rparr>
       f)
     (mk_uN 0)")
                    case (meminst_case_underscore var_0 var_1_lst)
                    then show ?case
                      by (metis meminst.select_convs(2))
                  qed
                qed
              qed
            qed
            then have "list_all wf_byte ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8))"
              using list_all_list_slice by auto
            then have wfbs: "wf_uN v_n (inv_ibytes_underscore v_n ( list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg))
     (v_n div 8)))"
              using inv_ibytes__is_wf bs by auto
             have wfz: "wf_uN 32 (mk_uN 0)"
               using uN_case_0 by blast
             have "wf_sz (mk_sz v_n)" using Nil(7)
             proof(induction "instr_sc6 (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx)")
             qed(auto)
             then show ?thesis proof(induction "mk_sz v_n")
                 case sz_case_0
                 then show ?case proof
                   assume "(v_n = 8 \<or> v_n = 16) \<or> v_n = 32"
                   then show ?thesis proof 
                     assume "v_n = 8 \<or> v_n = 16" 
                     then show ?thesis proof
                       assume vn: "v_n = 8" 
                       have 1: "v_n = jsize Jnn_I8" using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 2: " wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n)))"
                         using shape_case_0 dim_case_0 vn lsize.domintros lsize.psimps
                           valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps
                           psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                         lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 3: "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))))
     (mk_lane__0 Jnn_I8 (mk_uN (proj_uN_0 (inv_ibytes_underscore v_n (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg)) (v_n div 8))))))"
                         using lane__case_0 fun_lanetype.domintros fun_lanetype.psimps wfbs
                           mk_uN_proj_uN_0 1 jsize.domintros jsize.psimps by simp
                       then show ?thesis using vload_lane_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(17) c n vec admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz 1 2 3
              by fastforce
                     next
                       assume vn: "v_n = 16" 
                       have 1: "v_n = jsize Jnn_I16" using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 2: " wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n)))"
                         using shape_case_0 dim_case_0 vn lsize.domintros lsize.psimps
                           valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps
                           psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                         lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 3: "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))))
     (mk_lane__0 Jnn_I16 (mk_uN (proj_uN_0 (inv_ibytes_underscore v_n (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg)) (v_n div 8))))))"
                         using lane__case_0 fun_lanetype.domintros fun_lanetype.psimps wfbs
                           mk_uN_proj_uN_0 1 jsize.domintros jsize.psimps by simp
                       then show ?thesis using vload_lane_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(17) c n vec admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz 1 2 3
              by fastforce
                     qed
                   next 
                     assume vn: "v_n = 32" 
                       have 1: "v_n = jsize Jnn_I32" using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 2: " wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n)))"
                         using shape_case_0 dim_case_0 vn lsize.domintros lsize.psimps
                           valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps
                           psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                         lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 3: "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))))
     (mk_lane__0 Jnn_I32 (mk_uN (proj_uN_0 (inv_ibytes_underscore v_n (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg)) (v_n div 8))))))"
                         using lane__case_0 fun_lanetype.domintros fun_lanetype.psimps wfbs
                           mk_uN_proj_uN_0 1 jsize.domintros jsize.psimps by simp
                       then show ?thesis using vload_lane_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(17) vec c n admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz 1 2 3
              by fastforce
                   qed
                 next 
                   assume vn: "v_n = 64"
                       have 1: "v_n = jsize Jnn_I64" using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 2: " wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n)))"
                         using shape_case_0 dim_case_0 vn lsize.domintros lsize.psimps
                           valtype_numtype.domintros valtype_numtype.psimps size.domintros size.psimps
                           psize.domintros psize.psimps proj_dim_0.domintros proj_dim_0.psimps
                         lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                       have 3: "wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))))
     (mk_lane__0 Jnn_I64 (mk_uN (proj_uN_0 (inv_ibytes_underscore v_n (list_slice (BYTES (fun_mem (mk_state s' f) (mk_uN 0)))
     (proj_uN_0 (the (proj_num__0 c)) + proj_uN_0 (OFFSET v_memarg)) (v_n div 8))))))"
                         using lane__case_0 fun_lanetype.domintros fun_lanetype.psimps wfbs
                           mk_uN_proj_uN_0 1 jsize.domintros jsize.psimps by simp
                       then show ?thesis using vload_lane_val[of c v_n "inv_ibytes_underscore v_n _" 
                  "mk_state s' f" v_memarg] Nil(17) c n vec admininstr_val.domintros admininstr_val.psimps
admininstr_instr.domintros admininstr_instr.psimps Step.intros(2) bs proj_num__0.domintros 
              proj_num__0.psimps wfbs wfz 1 2 3
              by fastforce
                 qed
               qed
             qed
        next
          case (Cons a vs)
          then show ?case by simp
        qed
      qed
    qed
    next
      case (vstore C mt v_memarg)
      then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            then obtain c1 where a1: "a1 = val_CONST I32 c1" using typeofval_is_i32 by fastforce
            have "wf_val a1" using Nil by simp
            then have c1: "proj_num__0 c1 \<noteq> None" using a1 proof(induction a1)
              case (val_case_0 v_numtype var_0)
              then show ?case proof(induction v_numtype var_0)
                case (num__case_0 v_Inn var_x v_numtype)
                then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
              next
                case (num__case_1 v_Fnn var_x v_numtype)
                then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                proof(induction v_Fnn) qed(auto)
              qed
            qed(auto)
            obtain c2 where a2: "a2 = val_VCONST V128 c2" using typeofval_is_v128 Nil by fastforce
            show ?case using 
              vstore_val[OF c1] a1 a2 Nil(17) admininstr_val.domintros admininstr_val.psimps
    admininstr_instr.domintros admininstr_instr.psimps
              by fastforce
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (vstore_lane C mt v_memarg v_n v_laneidx)
       then show ?case proof(induction vs)
        case Nil
        then show ?case by simp
      next
        case (Cons a1 vs)
        show ?case using Cons(2-) proof(induction vs)
          case Nil
          then show ?case by simp
        next
          case (Cons a2 vs)
          show ?case using Cons(2-) proof(induction vs)
            case Nil
            then obtain c1 where a1: "a1 = val_CONST I32 c1" using typeofval_is_i32 by fastforce
            have "wf_val a1" using Nil by simp
            then have c1: "proj_num__0 c1 \<noteq> None" using a1 proof(induction a1)
              case (val_case_0 v_numtype var_0)
              then show ?case proof(induction v_numtype var_0)
                case (num__case_0 v_Inn var_x v_numtype)
                then show ?case using proj_num__0.domintros proj_num__0.psimps by auto
              next
                case (num__case_1 v_Fnn var_x v_numtype)
                then show ?case using numtype_Fnn.domintros numtype_Fnn.psimps
                proof(induction v_Fnn) qed(auto)
              qed
            qed(auto)
            obtain c2 where a2: "a2 = val_VCONST V128 c2" using typeofval_is_v128 Nil by fastforce
            have "wf_sz (mk_sz v_n)" using Nil(7) 
            proof(induction "instr_sc6 (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx)")
            qed(auto)
            then show ?case proof(induction "mk_sz v_n")
              case sz_case_0
              then show ?case proof
                assume "(v_n = 8 \<or> v_n = 16) \<or> v_n = 32"
                then show ?thesis proof
                  assume "v_n = 8 \<or> v_n = 16" 
                  then show ?thesis proof
                    assume vn: "v_n = 8" 
                    have 1: "v_n = jsize Jnn_I8" 
                     using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                   have "wf_val a2" using Nil by simp
                   then have wfc2: "wf_uN 128 c2" using a2 proof(induction a2)
                     case (val_case_1 v_vectype var_0)
                     then show ?case using valtype_vectype.domintros valtype_vectype.psimps
                         size.domintros size.psimps by auto
                   qed(auto)
                   have wfl: "list_all (wf_lane_underscore lanetype_I8)
        (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))) c2)"
                     using lanes__is_wf shape_case_0 dim_case_0 fun_lanetype.domintros fun_lanetype.psimps
                       wfc2 lanetype_Jnn.domintros lanetype_Jnn.psimps lsize.domintros lsize.psimps
                       psize.domintros psize.psimps valtype_numtype.domintros valtype_numtype.psimps
                       size.domintros size.psimps
                     by (metis div_mult2_eq double_half_numeral_Bit_0_eq(2) mult.assoc
                         numeral_Bit0_div_2 proj_dim_0.domintros proj_dim_0.psimps
                         vn)
                   have lenl: 
                     "length (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))) c2)
                      = 128 div v_n" using length_lanes by simp
                   have wfl: 
                     "wf_lane_underscore lanetype_I8  (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx)"
                     using lenl wfl list_all_nth Nil(4)
                     by metis
                   then have 2: "proj_lane__0
        (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx) \<noteq>
           None"
                   proof (induction lanetype_I8 "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx")
                     case (lane__case_0 v_Jnn var_x)
                     then show ?case using 
                       proj_lane__0.psimps(1)[OF proj_lane__0.domintros(1)] 
                       by (metis option.distinct(1))
                   next
                     case (lane__case_1 v_Fnn var_x)
                     then show ?case using lanetype_Fnn.domintros lanetype_Fnn.psimps
                     proof(induction v_Fnn) qed(auto)
                   qed
                   have 3: "proj_uN_0 v_laneidx < length (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))) c2)"
                     using length_lanes Nil(4) by simp
                   have 4: "wf_uN v_n
     (mk_uN
       (proj_uN_0
         (the (proj_lane__0
                (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))) c2 !
                 proj_uN_0 v_laneidx)))))" 
                     using wfl
                   proof(induction lanetype_I8 "lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx")
                     case (lane__case_0 v_Jnn var_x)
                     then have "v_Jnn = Jnn_I8" using lanetype_Jnn.domintros lanetype_Jnn.psimps
                     proof (induction v_Jnn) qed(auto)
                     then show ?case
                       using lane__case_0 1 jsize.domintros jsize.psimps 
                         proj_lane__0.domintros proj_lane__0.psimps mk_uN_proj_uN_0
                       by (metis option.sel)
                   next
                     case (lane__case_1 v_Fnn var_x)
                     then show ?case using lanetype_Fnn.domintros lanetype_Fnn.psimps 
                     proof(induction v_Fnn) qed(auto)
                   qed
                    show ?case using 
                        vstore_lane_val[OF c1 1 _ 2 3 _ 4] 
                        a1 a2 Nil(17) 
                        admininstr_val.domintros admininstr_val.psimps
                        admininstr_instr.domintros admininstr_instr.psimps
                      by fastforce
                  next
                    assume vn: "v_n = 16"
                   have 1: "v_n = jsize Jnn_I16" 
                     using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                   have "wf_val a2" using Nil by simp
                   then have wfc2: "wf_uN 128 c2" using a2 proof(induction a2)
                     case (val_case_1 v_vectype var_0)
                     then show ?case using valtype_vectype.domintros valtype_vectype.psimps
                         size.domintros size.psimps by auto
                   qed(auto)
                   have wfl: "list_all (wf_lane_underscore lanetype_I16)
        (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))) c2)"
                     using lanes__is_wf shape_case_0 dim_case_0 fun_lanetype.domintros fun_lanetype.psimps
                       wfc2 lanetype_Jnn.domintros lanetype_Jnn.psimps lsize.domintros lsize.psimps
                       psize.domintros psize.psimps valtype_numtype.domintros valtype_numtype.psimps
                       size.domintros size.psimps
                     by (metis div_mult2_eq double_half_numeral_Bit_0_eq(2) mult.assoc
                         numeral_Bit0_div_2 proj_dim_0.domintros proj_dim_0.psimps
                         vn)
                   have lenl: 
                     "length (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))) c2)
                      = 128 div v_n" using length_lanes by simp
                   have wfl: 
                     "wf_lane_underscore lanetype_I16  (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx)"
                     using lenl wfl list_all_nth Nil(4)
                     by metis
                   then have 2: "proj_lane__0
        (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx) \<noteq>
           None"
                   proof (induction lanetype_I16 "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx")
                     case (lane__case_0 v_Jnn var_x)
                     then show ?case using 
                       proj_lane__0.psimps(1)[OF proj_lane__0.domintros(1)] 
                       by (metis option.distinct(1))
                   next
                     case (lane__case_1 v_Fnn var_x)
                     then show ?case using lanetype_Fnn.domintros lanetype_Fnn.psimps
                     proof(induction v_Fnn) qed(auto)
                   qed
                   have 3: "proj_uN_0 v_laneidx < length (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))) c2)"
                     using length_lanes Nil(4) by simp
                   have 4: "wf_uN v_n
     (mk_uN
       (proj_uN_0
         (the (proj_lane__0
                (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))) c2 !
                 proj_uN_0 v_laneidx)))))" 
                     using wfl
                   proof(induction lanetype_I16 "lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx")
                     case (lane__case_0 v_Jnn var_x)
                     then have "v_Jnn = Jnn_I16" using lanetype_Jnn.domintros lanetype_Jnn.psimps
                     proof (induction v_Jnn) qed(auto)
                     then show ?case
                       using lane__case_0 1 jsize.domintros jsize.psimps 
                         proj_lane__0.domintros proj_lane__0.psimps mk_uN_proj_uN_0
                       by (metis option.sel)
                   next
                     case (lane__case_1 v_Fnn var_x)
                     then show ?case using lanetype_Fnn.domintros lanetype_Fnn.psimps 
                     proof(induction v_Fnn) qed(auto)
                   qed
                    show ?case using 
                        vstore_lane_val[OF c1 1 _ 2 3 _ 4] 
                        a1 a2 Nil(17) 
                        admininstr_val.domintros admininstr_val.psimps
                        admininstr_instr.domintros admininstr_instr.psimps
                      by fastforce
                  qed
                next 
                  assume vn: "v_n = 32" 
                  have 1: "v_n = jsize Jnn_I32" 
                     using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                   have "wf_val a2" using Nil by simp
                   then have wfc2: "wf_uN 128 c2" using a2 proof(induction a2)
                     case (val_case_1 v_vectype var_0)
                     then show ?case using valtype_vectype.domintros valtype_vectype.psimps
                         size.domintros size.psimps by auto
                   qed(auto)
                   have wfl: "list_all (wf_lane_underscore lanetype_I32)
        (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))) c2)"
                     using lanes__is_wf shape_case_0 dim_case_0 fun_lanetype.domintros fun_lanetype.psimps
                       wfc2 lanetype_Jnn.domintros lanetype_Jnn.psimps lsize.domintros lsize.psimps
                       psize.domintros psize.psimps valtype_numtype.domintros valtype_numtype.psimps
                       size.domintros size.psimps
                     by (metis div_mult2_eq double_half_numeral_Bit_0_eq(1) mult.assoc numeral_Bit0_div_2 option.sel
                         proj_dim_0.domintros proj_dim_0.psimps vn)
                     
                   have lenl: 
                     "length (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))) c2)
                      = 128 div v_n" using length_lanes by simp
                   have wfl: 
                     "wf_lane_underscore lanetype_I32  (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx)"
                     using lenl wfl list_all_nth Nil(4)
                     by metis
                   then have 2: "proj_lane__0
        (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx) \<noteq>
           None"
                   proof (induction lanetype_I32 "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx")
                     case (lane__case_0 v_Jnn var_x)
                     then show ?case using 
                       proj_lane__0.psimps(1)[OF proj_lane__0.domintros(1)] 
                       by (metis option.distinct(1))
                   next
                     case (lane__case_1 v_Fnn var_x)
                     then show ?case using lanetype_Fnn.domintros lanetype_Fnn.psimps
                     proof(induction v_Fnn) qed(auto)
                   qed
                   have 3: "proj_uN_0 v_laneidx < length (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))) c2)"
                     using length_lanes Nil(4) by simp
                   have 4: "wf_uN v_n
     (mk_uN
       (proj_uN_0
         (the (proj_lane__0
                (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))) c2 !
                 proj_uN_0 v_laneidx)))))" 
                     using wfl
                   proof(induction lanetype_I32 "lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx")
                     case (lane__case_0 v_Jnn var_x)
                     then have "v_Jnn = Jnn_I32" using lanetype_Jnn.domintros lanetype_Jnn.psimps
                     proof (induction v_Jnn) qed(auto)
                     then show ?case
                       using lane__case_0 1 jsize.domintros jsize.psimps 
                         proj_lane__0.domintros proj_lane__0.psimps mk_uN_proj_uN_0
                       by (metis option.sel)
                   next
                     case (lane__case_1 v_Fnn var_x)
                     then show ?case using lanetype_Fnn.domintros lanetype_Fnn.psimps 
                     proof(induction v_Fnn) qed(auto)
                   qed
                    show ?case using 
                        vstore_lane_val[OF c1 1 _ 2 3 _ 4] 
                        a1 a2 Nil(17) 
                        admininstr_val.domintros admininstr_val.psimps
                        admininstr_instr.domintros admininstr_instr.psimps
                      by fastforce
                qed
              next
                assume vn: "v_n = 64" 
                have 1: "v_n = jsize Jnn_I64" 
                     using jsize.domintros jsize.psimps
                           lsize.domintros lsize.psimps valtype_numtype.domintros valtype_numtype.psimps
                           size.domintros size.psimps psize.domintros psize.psimps vn 
                           lanetype_Jnn.domintros lanetype_Jnn.psimps by auto
                   have "wf_val a2" using Nil by simp
                   then have wfc2: "wf_uN 128 c2" using a2 proof(induction a2)
                     case (val_case_1 v_vectype var_0)
                     then show ?case using valtype_vectype.domintros valtype_vectype.psimps
                         size.domintros size.psimps by auto
                   qed(auto)
                   have wfl: "list_all (wf_lane_underscore lanetype_I64)
        (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))) c2)"
                     using lanes__is_wf shape_case_0 dim_case_0 fun_lanetype.domintros fun_lanetype.psimps
                       wfc2 lanetype_Jnn.domintros lanetype_Jnn.psimps lsize.domintros lsize.psimps
                       psize.domintros psize.psimps valtype_numtype.domintros valtype_numtype.psimps
                       size.domintros size.psimps
                     by (metis double_half_numeral_Bit_0_eq(2) nonzero_mult_div_cancel_left numeral_Bit0_div_2 option.sel
                         proj_dim_0.domintros proj_dim_0.psimps vn zero_neq_numeral)
                   have lenl: 
                     "length (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))) c2)
                      = 128 div v_n" using length_lanes by simp
                   have wfl: 
                     "wf_lane_underscore lanetype_I64 (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx)"
                     using lenl wfl list_all_nth Nil(4)
                     by metis
                   then have 2: "proj_lane__0
        (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx) \<noteq>
           None"
                   proof (induction lanetype_I64 "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx")
                     case (lane__case_0 v_Jnn var_x)
                     then show ?case using 
                       proj_lane__0.psimps(1)[OF proj_lane__0.domintros(1)] 
                       by (metis option.distinct(1))
                   next
                     case (lane__case_1 v_Fnn var_x)
                     then show ?case using lanetype_Fnn.domintros lanetype_Fnn.psimps
                     proof(induction v_Fnn) qed(auto)
                   qed
                   have 3: "proj_uN_0 v_laneidx < length (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))) c2)"
                     using length_lanes Nil(4) by simp
                   have 4: "wf_uN v_n
     (mk_uN
       (proj_uN_0
         (the (proj_lane__0
                (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))) c2 !
                 proj_uN_0 v_laneidx)))))" 
                     using wfl
                   proof(induction lanetype_I64 "lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim (128 div v_n))) c2 ! proj_uN_0 v_laneidx")
                     case (lane__case_0 v_Jnn var_x)
                     then have "v_Jnn = Jnn_I64" using lanetype_Jnn.domintros lanetype_Jnn.psimps
                     proof (induction v_Jnn) qed(auto)
                     then show ?case
                       using lane__case_0 1 jsize.domintros jsize.psimps 
                         proj_lane__0.domintros proj_lane__0.psimps mk_uN_proj_uN_0
                       by (metis option.sel)
                   next
                     case (lane__case_1 v_Fnn var_x)
                     then show ?case using lanetype_Fnn.domintros lanetype_Fnn.psimps 
                     proof(induction v_Fnn) qed(auto)
                   qed
                    show ?case using 
                        vstore_lane_val[OF c1 1 _ 2 3 _ 4] 
                        a1 a2 Nil(17) 
                        admininstr_val.domintros admininstr_val.psimps
                        admininstr_instr.domintros admininstr_instr.psimps
                      by fastforce
              qed
            qed
          next
            case (Cons a vs)
            then show ?case by simp
          qed
        qed
      qed
    next
      case (empty C)
      then show ?case
        by auto
    next
      case (Instrs_ok__instr C' v_instr' t_1_lst' t_2_lst')
      then show ?case
        apply(auto)
        subgoal for vs f
        proof -
        assume "(\<And>vs f. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<Longrightarrow>
           list_all wf_val vs \<Longrightarrow>
           State_ok (mk_state s' f) (strip C') \<Longrightarrow>
        wf_config (mk_config (mk_state s' f) [admininstr_instr v_instr']) \<Longrightarrow>
        wf_state (mk_state s' f) \<Longrightarrow>
           \<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ [admininstr_instr v_instr']))
                   x \<Longrightarrow>
           \<forall>v. admininstr_instr v_instr' \<noteq> admininstr_val v \<Longrightarrow> False)"
        " list_all2 Valtype_sub (map typeofval vs) t_1_lst'"
        "list_all wf_val vs"
        "State_ok (mk_state s' f) (strip C')"
        "wf_config (mk_config (mk_state s' f) [admininstr_instr v_instr'])"
      "wf_state (mk_state s' f)"
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
          "wf_store s' \<longrightarrow> (\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
          list_all wf_val vs \<longrightarrow>
          (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
               not_br_return (map admininstr_instr instr_1_lst) \<longrightarrow>
               wf_config (mk_config (mk_state s' f) (map admininstr_instr instr_1_lst)) \<longrightarrow>
               wf_state (mk_state s' f) \<longrightarrow>
               (\<forall>x. \<not> Step
                        (mk_config (mk_state s' f)
                          (map admininstr_val vs @ map admininstr_instr instr_1_lst))
                        x) \<longrightarrow>
               (\<exists>vs. map admininstr_instr instr_1_lst = map admininstr_val vs)))"
          "Instrs_ok C' instr_2_lst (mk_functype (mk_list t_2_lst') (mk_list t_3_lst))"
          "wf_store s' \<longrightarrow> (\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_2_lst' \<longrightarrow>
          list_all wf_val vs \<longrightarrow>
          (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
               not_br_return (map admininstr_instr instr_2_lst) \<longrightarrow>
               wf_config (mk_config (mk_state s' f) (map admininstr_instr instr_2_lst)) \<longrightarrow>
               wf_state (mk_state s' f) \<longrightarrow>
               (\<forall>x. \<not> Step
                        (mk_config (mk_state s' f)
                          (map admininstr_val vs @ map admininstr_instr instr_2_lst))
                        x) \<longrightarrow>
               (\<exists>vs. map admininstr_instr instr_2_lst = map admininstr_val vs)))"
          "wf_context C'"
          "list_all wf_instr instr_1_lst"
          "list_all wf_instr instr_2_lst"
          show "wf_store s' \<longrightarrow> (\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
          list_all wf_val vs \<longrightarrow>
          (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
                not_br_return (map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst) \<longrightarrow>
               wf_config
                (mk_config (mk_state s' f)
                  (map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst)) \<longrightarrow>
               wf_state (mk_state s' f) \<longrightarrow>
               (\<forall>x. \<not> Step
                        (mk_config (mk_state s' f)
                          (map admininstr_val vs @
                           map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst))
                        x) \<longrightarrow>
               (\<exists>vs. map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst =
                     map admininstr_val vs)))"
            apply(auto)
            subgoal for vs f
            proof - 
              assume assms': 
                "wf_store s'"
    "list_all2 Valtype_sub (map typeofval vs) t_1_lst'"
    "list_all wf_val vs"
    "State_ok (mk_state s' f) (strip C')"
    "not_br_return (map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst)"
    "wf_config
     (mk_config (mk_state s' f) (map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst))"
      "wf_state (mk_state s' f)"
     "\<forall>x. \<not> Step
            (mk_config (mk_state s' f)
              (map admininstr_val vs @
               map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst))
            x"
              have stok: "Store_ok s'" using assms'(4) proof(induction "mk_state s' f" "strip C'") 
              qed(auto)
              show "\<exists>vs. map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst = map admininstr_val vs "
              proof (cases "(Ex (Step (mk_config (mk_state s' f) 
      (map admininstr_val vs @ map admininstr_instr instr_1_lst))))")
                case True
                then have "wf_config (
                  mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_1_lst))"
                  using assms(6) assms'(3) wf_admininstr_val wf_admininstr_instr
                  config_case_0[OF assms'(7)] 
                  list_all_map_impl[of wf_val vs wf_admininstr admininstr_val]
                  list_all_map_impl[of wf_instr instr_1_lst wf_admininstr admininstr_instr]
                  list_all_app
                  by force
                then have "(Ex (Step (mk_config (mk_state s' f) 
      (map admininstr_val vs @ map admininstr_instr instr_1_lst @ map admininstr_instr instr_2_lst))))"
                  using True reducible_right assms(7) 
                  list_all_map_impl[of wf_instr instr_2_lst wf_admininstr admininstr_instr]
                  wf_admininstr_instr stok
                  by fastforce
                then show ?thesis using assms'(8)
                  by blast
              next
                case False
                then obtain vs1 where const: "map admininstr_instr instr_1_lst = map admininstr_val vs1"
                   using assms assms' br_return_contaminate_right
                   by (metis config.inject list_all_append wf_config.simps) 
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
                       using mk_Instrtype_sub 1 2 3 br_return_contaminate_left
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
        subgoal for vs f
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
         (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
              wf_config (mk_config (mk_state s' f) (map admininstr_instr instr_lst)) \<longrightarrow>
              wf_state (mk_state s' f) \<longrightarrow>
              (\<forall>x. \<not> Step
                       (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_lst))
                       x) \<longrightarrow>
              (\<exists>vs. map admininstr_instr instr_lst = map admininstr_val vs))"
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
        subgoal for vs f
        proof -
          assume assms:
  "Instrs_ok C' instr_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
    "wf_context C'"
    "list_all wf_instr instr_lst"
    "wf_store s'"
    "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
              wf_config (mk_config (mk_state s' f) (map admininstr_instr instr_lst)) \<longrightarrow>
              wf_state (mk_state s' f) \<longrightarrow>
              (\<forall>x. \<not> Step
                       (mk_config (mk_state s' f) (map admininstr_val vs @ map admininstr_instr instr_lst))
                       x) \<longrightarrow>
              (\<exists>vs. map admininstr_instr instr_lst = map admininstr_val vs))"
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
            have stok: "Store_ok s'" using assms(8) proof(induction "mk_state s' f" "strip C'")
            qed(auto)
            have "wf_config (mk_config (mk_state s' f) 
                (map admininstr_val vs2 @ map admininstr_instr instr_lst))"
              using assms split2
              by (metis config.inject config_case_0 list_all_append list_all_map_impl wf_admininstr_val
                  wf_config.cases)
            then show ?thesis using stok assms split2 reducible_left_v[OF True, of vs1]
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
         (\<forall>f. State_ok (mk_state s f) (strip C) \<longrightarrow>
              not_br_return (map admininstr_instr instr'_lst) \<longrightarrow>
              wf_config (mk_config (mk_state s f) (map admininstr_instr instr'_lst)) \<longrightarrow>
              wf_state (mk_state s f) \<longrightarrow>
              Ex (Step
                   (mk_config (mk_state s f) (map admininstr_val vs @ map admininstr_instr instr'_lst))) \<or>
              map admininstr_instr instr'_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
              (\<exists>vs. map admininstr_instr instr'_lst = map admininstr_val vs))"
        "Instrs_ok2 s
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)
     admininstr_lst (mk_functype (mk_list []) (mk_list t_lst))"
        "\<forall> f. State_ok (mk_state s f)
     (strip (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)) \<longrightarrow>
      not_br_return admininstr_lst \<longrightarrow>
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
        show "\<forall> f. State_ok (mk_state s f) (strip C) \<longrightarrow>
      not_br_return [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)] \<longrightarrow> 
    wf_config
     (mk_config (mk_state s f)
       [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]) \<longrightarrow>
    wf_state (mk_state s f) \<longrightarrow>
    Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)])) \<or>
    (\<exists>v. admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst) = admininstr_val v)" 
          apply(auto)
          subgoal for f
          proof -
            assume assms':
  "State_ok (mk_state s f) (strip C)"
    "not_br_return [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]"
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
            then show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))"
            proof (cases "not_br_return admininstr_lst")
              case True
            then have "Ex (Step (mk_config (mk_state s f) admininstr_lst)) \<or>
    admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or> (\<exists>vs. admininstr_lst = map admininstr_val vs)"
              using assms assms' 1 2
              by (metis Instrs_ok2_wf_instr config_case_0)
            then show ?thesis
            proof 
              assume "Ex (Step (mk_config (mk_state s f) admininstr_lst))"
              then obtain c where step: "Step (mk_config (mk_state s f) admininstr_lst) c" by blast
              have wf: "wf_config (mk_config (mk_state s f) admininstr_lst)"
                using assms assms'
                by (simp add: Instrs_ok2_wf_instr config_case_0)
              have stok: "Store_ok s" using assms' proof(induction "mk_state s f" "strip C")
              qed(auto)
              show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))" 
              proof (cases c)
                case (mk_config x1 x2)
                then show ?thesis using stok ctxt_label assms assms' Step_is_wf step wf
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
                    next 
                      case False 
                      then have "((\<exists> vs l aft. admininstr_lst = map admininstr_val vs @ [admininstr_sc0
        (admininstr_st0_BR l)] @ aft) \<or> 
      (\<exists> vs aft. admininstr_lst = map admininstr_val vs @ [
        admininstr_sc1 admininstr_st1_RETURN] @ aft))" using not_br_return_def by simp
                      then show ?thesis proof
                        assume "\<exists>vs l aft. admininstr_lst = map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR l)] @ aft"
                        then obtain vs l aft where eq: "admininstr_lst = map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR l)] @ aft"
                          by blast 
                        then show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))" 
                        proof(cases l)
                          case (mk_uN x)
                          then show ?thesis proof(cases x)
                            case 0
                            obtain t2 where split:
    " Instrs_ok2 s
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)
     (map admininstr_val vs) (mk_functype (mk_list []) t2)"
  "Instrs_ok2 s
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)
     ([admininstr_sc0 (admininstr_st0_BR l)] @ aft) (mk_functype t2 (mk_list t_lst))"
                              using assms(3) eq inv_seq by blast
                            then obtain t3 where 
  "Instrs_ok2 s
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)
     ([admininstr_sc0 (admininstr_st0_BR l)]) (mk_functype t2 t3)"
"Instrs_ok2 s
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)
     (aft) (mk_functype t3 (mk_list t_lst))"
                              using inv_seq by blast
                            then obtain t2' t3' where 
  "Instr_ok2 s
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)
     (admininstr_sc0 (admininstr_st0_BR l)) (mk_functype t2' t3')" 
                              and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3"
                              using inv_one_admininstr by blast
                            then have "Instr_ok
     (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C)
     (instr_sc0 (BR l)) (mk_functype t2' t3')" using inv_plain admininstr_instr.domintros 
    admininstr_instr.psimps by fastforce
                            then obtain t_lst t_1_lst t_2_lst where hyps:
                              "proj_uN_0 l < length (LABELS (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C))"
   "proj_list_0 (LABELS (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
          context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
          LABELS = [mk_list t'_lst], context_RETURN = None\<rparr>
       C) ! proj_uN_0 l) = t_lst"
  "mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst) = mk_functype t2' t3'"
                              using inv_br by blast
                            have eqt: "t_lst = t'_lst" proof(cases C)
                              case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
                              then show ?thesis using hyps(2) 0 mk_uN proj_uN_0.domintros
    proj_uN_0.psimps append_res_context_def proj_list_0.domintros proj_list_0.psimps
                                by fastforce
                            qed 
                            have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: 
          mk_instrtype (mk_list []) t2" using split(1) inv_const_list
                              by auto
                            
                              
                              then have "length vs \<ge> length t'_lst"
                                using subt eqt hyps(3) proof(induction "mk_instrtype (mk_list [])
                                  (mk_list (map typeofval vs))" "mk_instrtype (mk_list []) t2")
                                case (mk_Instrtype_sub t_lst2 t_11'_lst t_22_lst t'_lst' t_12'_lst)
                                show ?case using mk_Instrtype_sub(7,1-6,8-)
                                proof(induction "mk_instrtype t2' t3'" "mk_instrtype t2 t3")
                                  case (mk_Instrtype_sub t_21_lst' t_lst'' t_11'_lst' t_22_lst'
                                      t'_lst'' t_12'_lst' t_11_lst' t_12_lst')
                                  then show ?case using Resulttype_sub_length
                                    by (metis
                                        Instrtype_sub.mk_Instrtype_sub[of "t_lst'' @ t_11'_lst'" t_lst'' t_11'_lst' "t_lst'' @ t_11'_lst'"
                                          t_lst'' t_11'_lst' t_11'_lst' t_11'_lst']
                                        Instrtype_sub.mk_Instrtype_sub[of "t_1_lst @ t'_lst" t_1_lst t'_lst "t_1_lst @ t'_lst" t_1_lst t'_lst
                                          t'_lst t'_lst]
                                        Nil_is_append_conv[of t_lst2 t_11'_lst] Resulttype_sub_refl[of "mk_list t_lst''"]
                                        Resulttype_sub_refl[of "mk_list t_11'_lst'"] Resulttype_sub_refl[of "mk_list t_1_lst"]
                                        Resulttype_sub_refl[of "mk_list t'_lst"]
                                        functype.inject[of t2' t3' "mk_list (t_1_lst @ t'_lst)" "mk_list t_2_lst"] label.hyps(9)
                                        le_trans[of v_n "length t_11'_lst'" "length vs"] length_0_conv[of t'_lst'] length_map[of typeofval vs]
                                        list.size(3) self_append_conv2[of t_12'_lst "t_lst2 @ t_11'_lst"]
                                        subtyping_length_r[of t_11'_lst' t_11'_lst' "t_lst'' @ t_11'_lst'" "t_lst'' @ t_11'_lst'"]
                                        subtyping_length_r[of t'_lst t'_lst "t_1_lst @ t'_lst" "t_1_lst @ t'_lst"])
                                qed
                              qed
                            then obtain vs1 vs2 where "vs = vs1 @ vs2" "length vs2 = length t'_lst"
                              using list_splitable by blast
                            then show ?thesis 
                              using eq br_zero[of "length t'_lst" vs2 instr'_lst vs1]
                                Step.intros(1) mk_uN 0 by fastforce
                          next
                            case (Suc nat)
                            then show ?thesis 
                              using eq br_succ[of "length t'_lst" instr'_lst vs "mk_uN nat"] 
                                Step.intros(1) mk_uN proj_uN_0.domintros proj_uN_0.psimps
                              by fastforce 
                          qed
                        qed
                        next 
                          assume "\<exists>vs aft. admininstr_lst = map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ aft"
                          then obtain vs aft where "admininstr_lst = map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ aft"
                            by blast
                          then show "Ex (Step
         (mk_config (mk_state s f)
           [admininstr_sc8 (LABEL_underscore (length t'_lst) instr'_lst admininstr_lst)]))" 
                            using return_label[of "length t'_lst" instr'_lst vs] Step.intros(1)
                            by fastforce
                          qed
                    qed
          qed done
      qed done
  next
    case (Instr_ok2__frame s' f' C' t_lst' admininstr_lst C v_n)
    then show ?case 
      apply(auto)
      subgoal for f
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
     "(\<And>f s. State_ok s
             (strip
               (append_res_context
                 \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                    context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                    LABELS = [], context_RETURN = Some (mk_list t_lst')\<rparr>
                 C')) \<Longrightarrow>
            not_br_return admininstr_lst \<Longrightarrow>
            wf_context
             (append_res_context
               \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                  context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                  LABELS = [], context_RETURN = Some (mk_list t_lst')\<rparr>
               C') \<Longrightarrow>
            wf_config (mk_config s admininstr_lst) \<Longrightarrow>
            wf_state s \<Longrightarrow>
            mk_state s' f = s \<Longrightarrow>
            (\<exists>cfg'. Step (mk_config s admininstr_lst) cfg') \<or>
            admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
            (\<exists>vs. admininstr_lst = map admininstr_val vs))" (* State_ok s (strip C) \<Longrightarrow>
            wf_context C \<Longrightarrow>
            wf_config (mk_config s admininstr_lst) \<Longrightarrow>
            wf_state s \<Longrightarrow>
            mk_state s' f = s \<Longrightarrow>
            (\<exists>cfg'. Step (mk_config s admininstr_lst) cfg') \<or>
            admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
            (\<exists>vs. admininstr_lst = map admininstr_val vs))" *)
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
        have 4:"(strip
       (append_res_context
         \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
            context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
            context_RETURN = Some (mk_list t_lst')\<rparr>
         C')) = strip C'" proof(cases C') qed(auto simp add: append_res_context_def strip_def)
        show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))"
        proof(cases "not_br_return admininstr_lst")
          case True 
        then have "(\<exists>cfg'. Step (mk_config (mk_state s' f') admininstr_lst) cfg') \<or>
          admininstr_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
          (\<exists>vs. admininstr_lst = map admininstr_val vs)"
          using assms 4
          by (metis "1" "3" Expr_ok2.cases State_ok.cases)
        then show ?thesis
        proof
          assume " \<exists>cfg'. Step (mk_config (mk_state s' f') admininstr_lst) cfg'"
          then obtain cfg' where step: "Step (mk_config (mk_state s' f') admininstr_lst) cfg'" 
            by blast
          have stok: "Store_ok s'" using assms(10) proof(induction "mk_state s' f" "strip C")
          qed(auto)
          show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))"
          proof(cases cfg')
            case (mk_config x1 x2)
            then show ?thesis using ctxt_frame 3 Step_is_wf step stok
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
              next 
                case False
      then have "((\<exists> vs l aft. admininstr_lst = map admininstr_val vs @ [admininstr_sc0
        (admininstr_st0_BR l)] @ aft) \<or> 
      (\<exists> vs aft. admininstr_lst = map admininstr_val vs @ [
        admininstr_sc1 admininstr_st1_RETURN] @ aft))" using not_br_return_def by simp
                then show ?thesis
                proof
                  assume " \<exists>vs l aft. admininstr_lst = map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR l)] @ aft"
                  then obtain vs l aft where eq:
      "admininstr_lst = map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR l)] @ aft" by blast
                   have "Instrs_ok2 s'
 (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
 admininstr_lst (mk_functype (mk_list []) (mk_list t_lst'))"
                    using assms(2) inv_expr by simp
           then obtain t2 where split:
    " Instrs_ok2 s'
     (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     (map admininstr_val vs) (mk_functype (mk_list []) t2)"
  "Instrs_ok2 s'
     (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     ([admininstr_sc0 (admininstr_st0_BR l)] @ aft) (mk_functype t2 (mk_list t_lst'))"
                                using eq inv_seq by blast
                            then obtain t3 where 
  "Instrs_ok2 s'
      (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     ([admininstr_sc0 (admininstr_st0_BR l)]) (mk_functype t2 t3)"
"Instrs_ok2 s'
      (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     (aft) (mk_functype t3 (mk_list t_lst'))"
                              using inv_seq by blast
                            then obtain t2' t3' where 
  "Instr_ok2 s'
     (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     (admininstr_sc0 (admininstr_st0_BR l)) (mk_functype t2' t3')" 
                              and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3"
                              using inv_one_admininstr by blast
                            then have "Instr_ok
      (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     (instr_sc0 (BR l)) (mk_functype t2' t3')" using inv_plain admininstr_instr.domintros 
    admininstr_instr.psimps by fastforce
                            then have hyp: "proj_uN_0 l < length (LABELS  (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C'))" 
                              using inv_br by blast
                  have "False" using assms(1) hyp proof(induction s' f' C')
                    case (mk_Frame_ok s v_moduleinst C t_lst val_lst)
                    show ?case using mk_Frame_ok(1,8) 
                    proof(induction s v_moduleinst C)
                      case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s 
                            funcaddr_lst functype_F_lst memaddr_lst memtype_lst tableaddr_lst 
                            tabletype_lst exportinst_lst dataaddr_lst datatype_lst elemaddr_lst 
                            elemtype_lst)
                      show ?case using mk_Moduleinst_ok(27) append_res_context_def by simp
                    qed
                  qed
                  then show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))"
                    by simp
                next 
                  assume " \<exists>vs aft. admininstr_lst = map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ aft"
                  then obtain vs aft where 
  eq: "admininstr_lst = map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ aft" by blast
                  have "Instrs_ok2 s'
 (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
 admininstr_lst (mk_functype (mk_list []) (mk_list t_lst'))"
                    using assms(2) inv_expr by simp
           then obtain t2 where split:
    " Instrs_ok2 s'
     (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     (map admininstr_val vs) (mk_functype (mk_list []) t2)"
  "Instrs_ok2 s'
     (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     ([admininstr_sc1 admininstr_st1_RETURN] @ aft) (mk_functype t2 (mk_list t_lst'))"
                                using eq inv_seq by blast
                            then obtain t3 where 
  "Instrs_ok2 s'
      (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     ([admininstr_sc1 admininstr_st1_RETURN]) (mk_functype t2 t3)"
"Instrs_ok2 s'
      (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     (aft) (mk_functype t3 (mk_list t_lst'))"
                              using inv_seq by blast
                            then obtain t2' t3' where 
  "Instr_ok2 s'
     (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     (admininstr_sc1 admininstr_st1_RETURN) (mk_functype t2' t3')" 
                              and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3"
                              using inv_one_admininstr by blast
                            then have "Instr_ok
      (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C')
     (instr_sc1 RETURN) (mk_functype t2' t3')" using inv_plain admininstr_instr.domintros 
    admininstr_instr.psimps by fastforce
                            then obtain t_lst t_1_lst t_2_lst where hyps:
                              "context_RETURN  (append_res_context
   \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [],
      context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [],
      context_RETURN = Some (mk_list t_lst')\<rparr>
   C') = Some (mk_list t_lst)"
                              "mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst) = mk_functype t2' t3'"
                              using inv_return by blast
                            have eqt: "t_lst = t_lst'" proof(cases C)
                              case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
                              then show ?thesis using hyps(1) proj_uN_0.domintros
    proj_uN_0.psimps append_res_context_def proj_list_0.domintros proj_list_0.psimps
                                by fastforce
                            qed 
                            have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: 
          mk_instrtype (mk_list []) t2" using split(1) inv_const_list
                              by auto
                            
                              
                              then have "length vs \<ge> length t_lst'"
                                using subt eqt hyps(2) proof(induction "mk_instrtype (mk_list [])
                                  (mk_list (map typeofval vs))" "mk_instrtype (mk_list []) t2")
                                case (mk_Instrtype_sub t_lst2 t_11'_lst t_22_lst t'_lst' t_12'_lst)
                                show ?case using mk_Instrtype_sub(7,1-6,8-)
                                proof(induction "mk_instrtype t2' t3'" "mk_instrtype t2 t3")
                                  case (mk_Instrtype_sub t_21_lst' t_lst'' t_11'_lst' t_22_lst'
                                      t'_lst'' t_12'_lst' t_11_lst' t_12_lst')
                                  then show ?case using Resulttype_sub_length 
                                    by (metis
                                        Instrtype_sub.mk_Instrtype_sub[of "t_lst'' @ t_11'_lst'" t_lst'' t_11'_lst' "t_lst'' @ t_11'_lst'"
                                          t_lst'' t_11'_lst' t_11'_lst' t_11'_lst']
                                        Instrtype_sub.mk_Instrtype_sub[of "t_1_lst @ t_lst'" t_1_lst t_lst' "t_1_lst @ t_lst'" t_1_lst t_lst'
                                          t_lst' t_lst']
                                        Nil_is_append_conv[of t_lst2 t_11'_lst] Resulttype_sub_refl[of "mk_list t_lst''"]
                                        Resulttype_sub_refl[of "mk_list t_11'_lst'"] Resulttype_sub_refl[of "mk_list t_1_lst"]
                                        Resulttype_sub_refl[of "mk_list t_lst'"]
                                        functype.inject[of t2' t3' "mk_list (t_1_lst @ t_lst')" "mk_list t_2_lst"] Instr_ok2__frame.hyps(9)
                                        le_trans[of v_n "length t_11'_lst'" "length vs"] length_0_conv[of t'_lst'] length_map[of typeofval vs]
                                        list.size(3) self_append_conv2[of t_12'_lst "t_lst2 @ t_11'_lst"]
                                        subtyping_length_r[of t_11'_lst' t_11'_lst' "t_lst'' @ t_11'_lst'" "t_lst'' @ t_11'_lst'"]
                                        subtyping_length_r[of t_lst' t_lst' "t_1_lst @ t_lst'" "t_1_lst @ t_lst'"]) qed
                              qed
                            then obtain vs1 vs2 where "vs = vs1 @ vs2" "length vs2 = length t_lst'"
                              using list_splitable by blast

                  then show "Ex (Step
         (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore (length t_lst') f' admininstr_lst)]))"
                    using return_frame[of "length t_lst'" vs2 f' vs1 aft] Step.intros(1) eq
                    by fastforce
                  qed
              qed
        qed done 
  next
    case (Instr_ok2__call_addr s v_funcaddr t_1_lst t_2_lst C)
    then show ?case apply(auto)
      subgoal for vs f
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
               obtain t_locs where 3: "v_func = func_FUNC x (map LOCAL t_locs) body"
                  using func_FUNC local_list_is_local_list by blast
                have 4: "list_all (\<lambda>t. default_underscore t \<noteq> None) t_locs" 
                  using Externaddr_ok__func(12,1,2) 3 fields
                proof(induction "mk_state s f" "strip C")
                  case mk_State_ok
                  show ?case using mk_State_ok(1,5-) proof(induction s)
                    case (mk_Store_ok globalinst_lst globaltype_lst s meminst_lst memtype_lst 
                          tableinst_lst tabletype_lst funcinst_lst functype_lst datainst_lst 
                          datatype_lst eleminst_lst elemtype_lst)
                    have "Funcinst_ok s v_funcinst (functype_lst ! v_funcaddr)"
                      using mk_Store_ok(8,13,18,19) list_all2_nth
                      by fastforce
                    then show ?case using mk_Store_ok(20-)
    proof(induction s v_funcinst "functype_lst ! v_funcaddr")
      case (mk_Funcinst_ok s v_moduleinst C v_func')
      show ?case using mk_Funcinst_ok(3,7-) 
      proof(induction C v_func' "functype_lst ! v_funcaddr")
        case (mk_Func_ok x' C t_1_lst t_2_lst t_lst v_expr)
        have "map LOCAL t_lst = map LOCAL t_locs" using mk_Func_ok(9,10)
          by fast
        then have "t_lst = t_locs"
          using map_LOCAL_inj by presburger
        then show ?case using default_not_bot
          list_all_map_impl[OF mk_Func_ok(3), of "\<lambda> x. default_underscore x \<noteq> None" "\<lambda> x. x"]
          by fastforce
      qed
    qed
                  qed
                qed
               have 5: "wf_funcinst
     \<lparr>funcinst.funcinst_TYPE = mk_functype (mk_list t_1_lst) (mk_list t_2_lst), funcinst_MODULE = mm,
        CODE = v_func\<rparr>" using Externaddr_ok__func(3,1,2,5) fields 
        proof(induction s)
          case (store_case_underscore var_0_lst var_1_lst var_2_lst var_3_lst var_5_lst var_4_lst)
          have "wf_funcinst v_funcinst" using store_case_underscore(1,6,7) list_all_nth
            by fastforce
          then show ?case using store_case_underscore(8-)
            by simp 
        qed
               have 6: "wf_func (func_FUNC x (map LOCAL t_locs) body)" using 5 3
                 by (simp add: wf_funcinst.simps)
                 have 7: "wf_frame \<lparr>LOCALS = vs @ map (\<lambda>t. the (default_underscore t)) t_locs, 
                    frame_MODULE = mm\<rparr>" using Externaddr_ok__func(11) 5 default__is_wf
                   by (metis (mono_tags, lifting) "4" frame_case_underscore funcinst.ext_inject 
                       list_all_append
                       list_all_map_impl wf_funcinst.simps)
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
    then show ?case apply auto subgoal for f 
      proof -
        assume "\<forall>v. admininstr_ref v_ref \<noteq> admininstr_val v"
        then show "admininstr_ref v_ref = admininstr_sc7 admininstr_st7_TRAP"
          using admininstr_val_ref[of v_ref]
          by metis
      qed done
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
        subgoal for vs f
      proof -
        assume assms:
          "Instr_ok2 s C v_instr' (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
          "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         (\<forall>f. State_ok (mk_state s f) (strip C) \<longrightarrow>
              wf_config (mk_config (mk_state s f) [v_instr']) \<longrightarrow>
              wf_state (mk_state s f) \<longrightarrow>
              Ex (Step (mk_config (mk_state s f) (map admininstr_val vs @ [v_instr']))) \<or>
              v_instr' = admininstr_sc7 admininstr_st7_TRAP \<or> (\<exists>v. v_instr' = admininstr_val v))"
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
        subgoal for vs f
        proof -
          assume assms:
          "Instrs_ok2 s' C' instr_1_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
          "(\<forall> vs.
         list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
              not_br_return instr_1_lst \<longrightarrow>
              wf_config (mk_config (mk_state s' f) instr_1_lst) \<longrightarrow>
              wf_state (mk_state s' f) \<longrightarrow>
              Ex (Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_1_lst))) \<or>
              instr_1_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
              (\<exists>vs. instr_1_lst = map admininstr_val vs)))"
          "Instrs_ok2 s' C' instr_2_lst (mk_functype (mk_list t_2_lst') (mk_list t_3_lst))"
          "(\<forall> vs.
          list_all2 Valtype_sub (map typeofval vs) t_2_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
              not_br_return instr_2_lst \<longrightarrow>
              wf_config (mk_config (mk_state s' f) instr_2_lst) \<longrightarrow>
              wf_state (mk_state s' f) \<longrightarrow>
              Ex (Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_2_lst))) \<or>
              instr_2_lst = [admininstr_sc7 admininstr_st7_TRAP] \<or>
              (\<exists>vs. instr_2_lst = map admininstr_val vs)))"
        "wf_store s'"
          "wf_context C'"
          "list_all wf_admininstr instr_1_lst"
          "list_all wf_admininstr instr_2_lst"
          "list_all2 Valtype_sub (map typeofval vs) t_1_lst'"
          "list_all wf_val vs"
          "State_ok (mk_state s' f) (strip C')"
          "not_br_return (instr_1_lst @ instr_2_lst)"
          "wf_config
       (mk_config (mk_state s' f) ( instr_1_lst @ instr_2_lst))"
      "wf_state (mk_state s' f)"
       " \<forall>x. \<not> Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_1_lst @ instr_2_lst)) x"
   " \<forall>vs. instr_1_lst @ instr_2_lst \<noteq> map admininstr_val vs"
          have stok: "Store_ok s'" using assms(11) proof(induction "mk_state s' f" "strip C'")
          qed(auto)
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
                  using True reducible_right stok assms 
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
                              Step.intros(1) assms(15)
                           by fastforce 
                       qed
                next
                  case False
                then obtain vs1 where const: "instr_1_lst = map admininstr_val vs1"
                   using assms False' br_return_contaminate_right
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
                         then show ?thesis using True trap_vals[of "vs @ vs1" "[]"] const mk_Instrtype_sub(21)
                    Step.intros(1)
                           by auto
                       qed
                     next
                       case False
                     then obtain vs2 where "instr_2_lst = map admininstr_val vs2"
                       using mk_Instrtype_sub 1 2 3 br_return_contaminate_left
                       by (metis config_case_0)
                     then show ?thesis using const
                       by (metis \<open>instr_2_lst = map admininstr_val vs2\<close> 
                            local.const mk_Instrtype_sub.prems(17) map_append)
                   qed
                 qed 
              qed qed qed
        qed done 
  next
    case (Instrs_ok2__sub s' C' instr_lst t_1_lst' t_2_lst' t'_1_lst t'_2_lst)
      then show ?case
        apply(auto)
        subgoal for vs f
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
         (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
              wf_config (mk_config (mk_state s' f) instr_lst) \<longrightarrow>
              wf_state (mk_state s' f) \<longrightarrow>
              Ex (Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_lst))) \<or>
              instr_lst = [admininstr_sc7 admininstr_st7_TRAP])"
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
        subgoal for vs f
        proof -
          assume assms:
  "Instrs_ok2 s' C' instr_lst (mk_functype (mk_list t_1_lst') (mk_list t_2_lst'))"
    "wf_context C'"
    "list_all wf_admininstr instr_lst"
    "wf_store s'"
    "\<forall>vs. list_all2 Valtype_sub (map typeofval vs) t_1_lst' \<longrightarrow>
         list_all wf_val vs \<longrightarrow>
         (\<forall>f. State_ok (mk_state s' f) (strip C') \<longrightarrow>
              wf_config (mk_config (mk_state s' f) instr_lst) \<longrightarrow>
              wf_state (mk_state s' f) \<longrightarrow>
              Ex (Step (mk_config (mk_state s' f) (map admininstr_val vs @ instr_lst))) \<or>
              instr_lst = [admininstr_sc7 admininstr_st7_TRAP])"
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
            have stok: "Store_ok s'" using assms(8) proof(induction "mk_state s' f" "strip C'")
            qed(auto)
            have "wf_config (mk_config (mk_state s' f) 
                (map admininstr_val vs2 @  instr_lst))"
              using assms split2
              by (metis config_case_0 list_all_append list_all_map_impl wf_admininstr_val)
            then show ?thesis using assms split2 reducible_left_v[OF True, of vs1] stok
              by auto
          next
            case False
            then show ?thesis using assms
              split1(3) split2(1,3)
              by fastforce
          qed
        qed done
  next
    case (mk_Expr_ok2 s' C' admininstr_lst t_lst)
    then show ?case
      by auto
  qed
qed

end
