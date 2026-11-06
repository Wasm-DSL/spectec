 theory Context_Store_Agreement
	imports Main isabelle_reference_output_wasm2 Typing_Simplified
begin

definition t_inst_match :: "res_context \<Rightarrow> res_context \<Rightarrow> bool" where
  "t_inst_match C C' \<equiv> context_TYPES C = context_TYPES C' \<and>
                       context_FUNCS C = context_FUNCS C' \<and>
                       context_GLOBALS C = context_GLOBALS C' \<and>
                       context_TABLES C = context_TABLES C' \<and>
                       context_MEMS C = context_MEMS C' \<and>
                       context_ELEMS C = context_ELEMS C' \<and>
                       context_DATAS C = context_DATAS C'"

lemma t_inst_match_refl: shows "t_inst_match C C" using t_inst_match_def by simp  

lemma t_inst_match_is:
  assumes "t_inst_match C1 C2"
  shows "\<exists>a b c. C2 = \<lparr> context_TYPES = context_TYPES C1,
                       context_FUNCS = context_FUNCS C1,
                       context_GLOBALS = context_GLOBALS C1,
                       context_TABLES = context_TABLES C1,
                       context_MEMS = context_MEMS C1,
                       context_ELEMS = context_ELEMS C1,
                       context_DATAS = context_DATAS C1,
                       context_LOCALS = a,
                       LABELS = b,
                       context_RETURN = c \<rparr>"
  by (metis (full_types) assms unit.exhaust res_context.surjective t_inst_match_def)



lemma Moduleinst_ok_types:
  assumes "Moduleinst_ok s i C"
  shows "TYPES i = context_TYPES C"
  using assms by (induction rule:Moduleinst_ok.induct) simp

lemma context_types_agree:
  assumes "Moduleinst_ok s (frame_MODULE f) C"
          "t_inst_match C C'"
          "proj_uN_0 x < length (context_TYPES C')"
        shows "fun_type (mk_state s f) x (context_TYPES C' ! proj_uN_0 x)"
proof -
  have "TYPES (frame_MODULE f) = context_TYPES C'"
    using assms(1,2) Moduleinst_ok_types t_inst_match_def by metis
  then show ?thesis using assms(3) fun_type_case_0[of x f s] by simp
qed

lemma blocktype_ok_agree:
  assumes "Blocktype_ok C' bt tf"
    "Moduleinst_ok s (frame_MODULE f) C"
    "t_inst_match C C'"
  shows "fun_blocktype (mk_state s f) bt tf"
  using assms
proof(induction C' bt tf rule:Blocktype_ok.induct)
  case (Blocktype_ok__valtype C valtype_opt)
  then show ?case
    by (cases valtype_opt) (auto intro: fun_blocktype.intros)
next
  case (Blocktype_ok__typeidx v_typeidx C' t_1_lst t_2_lst)
  then show ?case using context_types_agree fun_blocktype_case_2 by metis
qed


lemma list_all_nth:
  assumes "list_all P l" "l ! k = x" "k < length l"
  shows "P x" 
  using assms proof (induction l arbitrary: k)
  case Nil
  then show ?case
    by auto
next
  case (Cons a l)
  then show ?case 
proof (cases k)
qed(auto simp add:Cons)
qed


lemma list_all2_nth:
  assumes "list_all2 P l1 l2" "l1 ! k = x1" "l2 ! k = x2" "k < length l1"
  shows "P x1 x2" 
  using assms 
proof (induction l1 arbitrary: l2 k)
  case Nil 
  then show ?case
    by simp
next
  case (Cons a l1)
  note outer = Cons
  then show ?case 
  proof (cases l2)
    case Nil
    then show ?thesis using outer by simp
  next
    case (Cons b list)
    then show ?thesis 
    proof (cases k)
      case 0
      then show ?thesis using outer Cons by simp
    next
      case (Suc nat)
      then show ?thesis using outer Cons by auto
    qed
  qed
qed

lemma list_all2_nth':
  assumes "list_all2 P l1 l2" "l1 ! k = x1" "l2 ! k = x2" "k < length l2"
  shows "P x1 x2" 
  using assms 
proof (induction l1 arbitrary: l2 k)
  case Nil 
  then show ?case
    by simp
next
  case (Cons a l1)
  note outer = Cons
  then show ?case 
  proof (cases l2)
    case Nil
    then show ?thesis using outer by simp
  next
    case (Cons b list)
    then show ?thesis 
    proof (cases k)
      case 0
      then show ?thesis using outer Cons by simp
    next
      case (Suc nat)
      then show ?thesis using outer Cons by auto
    qed
  qed
qed


lemma context_funcs_agree:
  assumes "context_FUNCS C' ! x = tf" 
          "x < length (context_FUNCS C')"
          "fun_funcaddr (mk_state s f) ! x = y"
          "wf_store s" 
          "Moduleinst_ok s (frame_MODULE f) C" 
          "t_inst_match C C'"
        shows "Externaddr_ok s (externaddr_FUNC y) (FUNC tf)"
proof - 
  have eqfuncs: "context_FUNCS C' = context_FUNCS C" using assms t_inst_match_def by simp
  show ?thesis using assms(5,1,2,3,4,6) eqfuncs
    proof (induction s "frame_MODULE f" C rule:Moduleinst_ok.induct)
      case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
              functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
              dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
      show ?case using mk_Moduleinst_ok(30,27,28,29,33) fun_funcaddr.psimps fun_funcaddr.domintros
        list_all2_nth[OF mk_Moduleinst_ok(5)]
        by (metis mk_Moduleinst_ok.hyps(4) moduleinst.select_convs(2) res_context.select_convs(2))
    qed
  qed


lemma Blocktype_ok_replace_agree:
  assumes "Moduleinst_ok s i Cemp" 
          "Moduleinst_ok s i Cemp'"
          "t_inst_match Cemp C" 
          "t_inst_match Cemp' C'"
          "wf_context C'"
          "Blocktype_ok C e tf"   
      shows "Blocktype_ok C' e tf"
  using assms proof (induction s i Cemp rule:Moduleinst_ok.induct)
  case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst functype_F_lst 
          memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst dataaddr_lst 
          datatype_lst elemaddr_lst elemtype_lst)
  show ?case using mk_Moduleinst_ok(27,1-26,28-31)
  proof (induction s " \<lparr>TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, 
        TABLES = tableaddr_lst,
        MEMS = memaddr_lst, ELEMS = elemaddr_lst, DATAS = dataaddr_lst, EXPORTS = exportinst_lst\<rparr>"
     Cemp' rule: Moduleinst_ok.induct)
    case (mk_Moduleinst_ok functype_lst' globaladdr_lst' globaltype_lst' s' funcaddr_lst' 
          functype_F_lst' memaddr_lst' memtype_lst' tableaddr_lst' tabletype_lst' exportinst_lst'
          dataaddr_lst' datatype_lst' elemaddr_lst' elemtype_lst')
    show ?case using mk_Moduleinst_ok(57, 1-56)
    proof (induction C e tf
        rule:Blocktype_ok.induct)
      case (Blocktype_ok__valtype C valtype_opt)
      then show ?case using Blocktype_ok.intros by simp
    next
      case (Blocktype_ok__typeidx v_typeidx C t_1_lst t_2_lst)
      then show ?case using context_types_agree Blocktype_ok.intros t_inst_match_def by simp
    qed
  qed
qed


end