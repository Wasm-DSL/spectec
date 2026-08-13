theory Typing_Simplified
	imports Main isabelle_reference_output_wasm2 
begin

(* simplified typing rules that abstract away hypotheses that are superfluous and do
   not force user to case disjunct on exact form of functype, see last few lemmas *)
 

lemma Instr_ok_wf:
  assumes "Instr_ok C e ft"
  shows   "(wf_context C)"
		      "(wf_instr e)"
	using assms
proof (induction)
qed(simp)+

lemma Instrs_ok_wf:
  assumes "Instrs_ok C e ft"
  shows   "(wf_context C)"
		      "(list_all wf_instr e)"
	using assms
proof (induction)
qed(simp)+



lemma Instr_ok2_wf:
  assumes "Instr_ok2 s C e ft"
  shows   "(wf_context C)"
          "wf_store s"
  using assms
proof(induction)
qed(simp)+

lemma Instrs_ok2_wf:
  assumes "Instrs_ok2 s C e ft"
  shows   "(wf_context C)"
          "wf_store s"
  using assms
proof(induction)
qed(simp)+


lemma list_all_drop:
  assumes "list_all (\<lambda> x. P x \<and> Q x) l"
  shows "list_all P l"
  using assms
proof(induction l)
qed(auto)


lemma wf_admininstr_instr:
  assumes "wf_instr e"
  shows "wf_admininstr (admininstr_instr e)"
  using assms
proof(induction e rule:wf_instr.induct)
  case (instr_case_4 v_blocktype instr_lst)
  then show ?case using admininstr_case_4 list_all_drop 
    by (metis admininstr_instr.domintros(5) admininstr_instr.psimps(5))
next
  case (instr_case_5 v_blocktype instr_lst)
  then show ?case  using admininstr_case_5 list_all_drop 
    by (metis admininstr_instr.domintros(6) admininstr_instr.psimps(6))
next
  case (instr_case_6 v_blocktype instr_lst instr_lst_0_lst)
  then show ?case  using admininstr_case_6 list_all_drop 
    by (metis admininstr_instr.domintros(7) admininstr_instr.psimps(7))
qed(simp_all add: wf_admininstr.intros admininstr_instr.domintros admininstr_instr.psimps)+

lemma wf_admininstr_instr_inv:
  assumes "wf_admininstr (admininstr_instr e)"
  shows "wf_instr e"
  using assms

   apply(induction "admininstr_instr e" rule:wf_admininstr.induct;
                      cases e rule:admininstr_instr.cases)
(* This next line can take a little while *)
  apply(simp_all add:admininstr_instr.domintros admininstr_instr.psimps wf_instr.intros)
  done

lemma wf_admininstr_instr_inv_list:
  assumes "list_all wf_admininstr (map admininstr_instr es)"
  shows "list_all wf_instr es"
  using assms proof(induction es)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a es)
  then show ?case using wf_admininstr_instr_inv 
    by simp 
qed

lemma wf_admininstr_val:
  assumes "wf_val v" shows "wf_admininstr (admininstr_val v)"
  using assms proof(induction v)
qed(auto simp add: wf_admininstr.intros admininstr_val.psimps admininstr_val.domintros)
    
lemma wf_admininstr_val_inv:
  assumes "wf_admininstr (admininstr_val v)"
  shows "wf_val v"
proof(cases v)
  case (val_CONST nt val)
  then have "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST nt val))" 
    using admininstr_val.domintros admininstr_val.psimps assms by simp
  then show ?thesis proof (induction "admininstr_sc1 (admininstr_st1_CONST nt val)" 
  rule: wf_admininstr.induct)
    case admininstr_case_13
    then show ?case
      using val_CONST val_case_0 by blast
  qed
next
  case (val_VCONST vt val)
  then have "wf_admininstr (admininstr_sc2 (admininstr_st2_VCONST vt val))" 
    using admininstr_val.domintros admininstr_val.psimps assms by simp
  then show ?thesis proof (induction "admininstr_sc2 (admininstr_st2_VCONST vt val)" 
  rule: wf_admininstr.induct)
    case admininstr_case_20
    then show ?case 
      using val_VCONST val_case_1 by presburger
  qed
next
  case (val_REF_NULL rt)
  then have "wf_admininstr (admininstr_sc4 (admininstr_st4_REF_NULL rt))"
    using admininstr_val.domintros admininstr_val.psimps assms by simp
  then show ?thesis proof (induction "admininstr_sc4 (admininstr_st4_REF_NULL rt)" 
  rule: wf_admininstr.induct)
    case admininstr_case_40
    then show ?case 
      by (simp add: val_REF_NULL val_case_2)
  qed
next
  case (val_REF_FUNC_ADDR addr)
  then have "wf_admininstr (admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR addr))"
    using admininstr_val.domintros admininstr_val.psimps assms by simp
  then show ?thesis proof (induction "admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR addr)" 
  rule: wf_admininstr.induct)
    case admininstr_case_68
    then show ?case 
      by (simp add: val_REF_FUNC_ADDR val_case_3)
  qed
next
  case (val_REF_HOST_ADDR addr)
  then have "wf_admininstr (admininstr_sc7 (admininstr_st7_REF_HOST_ADDR addr))"
    using admininstr_val.domintros admininstr_val.psimps assms by simp
  then show ?thesis proof (induction "admininstr_sc7 (admininstr_st7_REF_HOST_ADDR addr)" 
  rule: wf_admininstr.induct)
    case admininstr_case_69
    then show ?case 
      by (simp add: val_REF_HOST_ADDR val_case_4)
  qed
qed






lemma Instr_ok2_wf_instr:
  assumes "Instr_ok2 s C e ft"
  shows "wf_admininstr e"
  using assms
proof(induction s C e ft rule:Instr_ok2_Instrs_ok2_Expr_ok2.inducts(1)[where ?P2.0 =
    "\<lambda> s C e ft. list_all wf_admininstr e" and ?P3.0 = "\<lambda> s C e rt. True"])
  case (plain C v_instr t_1_lst t_2_lst s)
  then show ?case using wf_admininstr_instr by simp 
next
  case (Instr_ok2__ref s v_ref rt C)
  then show ?case
  proof (induction rule:Ref_ok.induct)
    case (null s rt)
    then show ?case
      by (simp add: admininstr_case_40 admininstr_ref.domintros(1) admininstr_ref.psimps(1))
  next
    case (Ref_ok__func s a ext)
    then show ?case 
      using admininstr_case_68 admininstr_ref.domintros(2) admininstr_ref.psimps(2) by presburger
  next
    case (extern s a)
    then show ?case
      using admininstr_case_69 admininstr_ref.domintros(3) admininstr_ref.psimps(3) by presburger
  qed
qed(simp)+


lemma Instrs_ok2_wf_instr:
  assumes "Instrs_ok2 s C e ft"
  shows "list_all wf_admininstr e"
  using assms
proof(induction s C e ft rule:Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2)[where ?P1.0 =
    "\<lambda> s C e ft. wf_admininstr e" and ?P3.0 = "\<lambda> s C e rt. True"])
  case (plain C v_instr t_1_lst t_2_lst s)
  then show ?case using wf_admininstr_instr by simp 
next
  case (Instr_ok2__ref s v_ref rt C)
  then show ?case
  proof (induction rule:Ref_ok.induct)
    case (null s rt)
    then show ?case
      by (simp add: admininstr_case_40 admininstr_ref.domintros(1) admininstr_ref.psimps(1))
  next
    case (Ref_ok__func s a ext)
    then show ?case 
      using admininstr_case_68 admininstr_ref.domintros(2) admininstr_ref.psimps(2) by presburger
  next
    case (extern s a)
    then show ?case
      using admininstr_case_69 admininstr_ref.domintros(3) admininstr_ref.psimps(3) by presburger
  qed
qed(simp)+

lemma instr_ok_instrs_ok:
  assumes "Instr_ok C e tf"
  shows "Instrs_ok C [e] tf" 
proof(cases tf)
  case (mk_functype x1 x2)
  then show ?thesis 
  proof (cases x1)
    case (mk_list x)
    note outer = mk_list
    then show ?thesis
    proof (cases x2)
      case (mk_list x)
      then show ?thesis 
        using assms Instr_ok_wf Instrs_ok__instr mk_functype outer mk_list by blast
    qed
  qed
qed

lemma instrs_ok_seq:
  assumes "Instrs_ok C es1 (mk_functype t1 t2)"
        "Instrs_ok C es2 (mk_functype t2 t3)" 
      shows "Instrs_ok C (es1 @ es2) (mk_functype t1 t3)" 
proof (cases t1)
  case (mk_list x)
  note outer = mk_list
  then show ?thesis
  proof (cases t2)
    case (mk_list y)
    note middle = mk_list 
    then show ?thesis 
    proof (cases t3) 
      case (mk_list z) 
      then show ?thesis 
        using outer middle Instrs_ok_wf assms
            seq by simp
    qed 
  qed
qed

lemma instr_ok_instr_ok2:
  assumes "Instr_ok C e tf" "wf_store s"
  shows "Instr_ok2 s C (admininstr_instr e) tf"
proof (cases tf)
  case (mk_functype t1 t2)
  then show ?thesis 
  proof (cases t1)
    case (mk_list x)
    note outer = mk_list
    then show ?thesis 
    proof (cases t2)
      case (mk_list y)
      then show ?thesis 
        using plain outer mk_functype Instr_ok_wf assms by simp
    qed
  qed
qed



lemma instr_ok2_instrs_ok2:
  assumes "Instr_ok2 s C e tf"
  shows "Instrs_ok2 s C [e] tf" 
proof(cases tf)
  case (mk_functype x1 x2)
  then show ?thesis 
  proof (cases x1)
    case (mk_list x)
    note outer = mk_list
    then show ?thesis
    proof (cases x2)
      case (mk_list x)
      then show ?thesis 
        using assms Instr_ok2_wf Instr_ok2_wf_instr 
           Instrs_ok2__instr mk_functype outer mk_list by blast
    qed
  qed
qed

lemma instrs_ok2_seq:
  assumes "Instrs_ok2 s C es1 (mk_functype t1 t2)"
        "Instrs_ok2 s C es2 (mk_functype t2 t3)" 
      shows "Instrs_ok2 s C (es1 @ es2) (mk_functype t1 t3)" 
proof (cases t1)
  case (mk_list x)
  note outer = mk_list
  then show ?thesis
  proof (cases t2)
    case (mk_list y)
    note middle = mk_list 
    then show ?thesis 
    proof (cases t3) 
      case (mk_list z) 
      then show ?thesis 
        using outer middle Instrs_ok2_wf Instrs_ok2_wf_instr assms
            Instrs_ok2__seq by simp
    qed 
  qed
qed

lemma instrs_ok_instrs_ok2:
  assumes "Instrs_ok C es tf"
          "wf_store s"
        shows "Instrs_ok2 s C (map admininstr_instr es) tf"
  using assms
proof(induction C es tf rule:Instr_ok_Instrs_ok.inducts(2)[where ?P1.0 = "\<lambda> C e tf. True"])
  case (empty C)
  then show ?case using Instrs_ok2__empty by simp
next
  case (Instrs_ok__instr C v_instr t_1_lst t_2_lst)
  then show ?case using instr_ok_instr_ok2 instr_ok2_instrs_ok2 by simp
next
  case (seq C instr_1_lst t_1_lst t_2_lst instr_2_lst t_3_lst)
  then show ?case using instrs_ok2_seq by simp
next
  case (sub C instr_lst t_1_lst t_2_lst t'_1_lst t'_2_lst)
  then show ?case using Instrs_ok2__sub Instrs_ok2_wf_instr by simp
next
  case (Instrs_ok__frame C instr_lst t_1_lst t_2_lst t_lst)
  then show ?case using Instrs_ok2__frame Instrs_ok2_wf_instr by simp
qed(simp_all)

lemma admininstr_val_ref: shows "admininstr_val (val_ref r) = admininstr_ref r"
proof(cases r)
qed(auto simp add: val_ref.domintros val_ref.psimps admininstr_val.domintros admininstr_val.psimps
    admininstr_ref.domintros admininstr_ref.psimps)

lemma ref_ok_agree: 
  assumes "Ref_ok s r rt" shows "typeofval (val_ref r) = valtype_reftype rt" 
  using assms proof(induction s r rt)
qed(auto simp add: typeofval.domintros typeofval.psimps val_ref.domintros val_ref.psimps 
    valtype_reftype.domintros valtype_reftype.psimps)

lemma instr_ok2__val:
  assumes "Val_ok s v t" "wf_context C" 
  shows "t = typeofval v \<and> Instr_ok2 s C (admininstr_val v) (mk_functype (mk_list []) (mk_list [t]))" 
  using assms proof(induction s v t)
  case (Val_ok__numtype s nt c_t)
  then show ?case using const wf_admininstr_val wf_admininstr_instr_inv
    admininstr_val.psimps admininstr_val.domintros admininstr_instr.domintros admininstr_instr.psimps
    wf_instr.intros typeofval.psimps typeofval.domintros
    by (metis (no_types, lifting) instr_ok_instr_ok2)
next
  case (Val_ok__vectype s vt c_t)
  then show ?case using vconst wf_admininstr_val wf_admininstr_instr_inv typeofval.psimps typeofval.domintros
    admininstr_val.psimps admininstr_val.domintros admininstr_instr.domintros admininstr_instr.psimps
    wf_instr.intros instr_ok_instr_ok2 valtype_vectype.domintros valtype_vectype.psimps vectype.exhaust
    by metis
next
  case (Val_ok__reftype s r rt)
  then show ?case using Instr_ok2__ref admininstr_val_ref typeofval.psimps typeofval.domintros 
    ref_ok_agree
    by metis
qed

end