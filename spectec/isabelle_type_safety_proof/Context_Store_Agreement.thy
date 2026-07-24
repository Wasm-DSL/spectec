 theory Context_Store_Agreement
	imports Main isabelle_reference_output_wasm2 
begin

definition t_inst_match :: "res_context \<Rightarrow> res_context \<Rightarrow> bool" where
  "t_inst_match C C' \<equiv> context_TYPES C = context_TYPES C' \<and>
                       context_FUNCS C = context_FUNCS C' \<and>
                       context_GLOBALS C = context_GLOBALS C' \<and>
                       context_TABLES C = context_TABLES C' \<and>
                       context_MEMS C = context_MEMS C' \<and>
                       context_ELEMS C = context_ELEMS C' \<and>
                       context_DATAS C = context_DATAS C'"

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



lemma blocktype_ok_agree:
  assumes "Blocktype_ok C' bt tf"
    "Moduleinst_ok s (frame_MODULE f) C"
    "t_inst_match C C'"
  shows "fun_blocktype (mk_state s f) bt = tf"
  using assms
proof(induction C' bt tf rule:Blocktype_ok.induct)
  case (Blocktype_ok__valtype C valtype_opt)
  then show ?case 
  proof (cases valtype_opt)
    case None
    then show ?thesis using Blocktype_ok__valtype fun_blocktype.domintros 
       fun_blocktype.psimps by auto
  next
    case (Some a)
    then show ?thesis using Blocktype_ok__valtype fun_blocktype.domintros
fun_blocktype.psimps by auto
  qed
next
  case (Blocktype_ok__typeidx v_typeidx C' t_1_lst t_2_lst)
  then have sametypes: "context_TYPES C' = context_TYPES C" using t_inst_match_def by simp
  show ?case using Blocktype_ok__typeidx(5,1,2,3,4,6) fun_blocktype.domintros(3) fun_blocktype.psimps(3)
      fun_type.domintros fun_type.psimps sametypes
  proof (induction s "frame_MODULE f" C rule:Moduleinst_ok.induct)
    case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
          functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
          dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
    then have "TYPES (frame_MODULE f) ! proj_uN_0 v_typeidx = context_TYPES C' ! proj_uN_0 v_typeidx"
      by (metis moduleinst.select_convs(1) res_context.select_convs(1))
    then show ?case using mk_Moduleinst_ok by metis
  qed
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


lemma context_types_agree:
  assumes "Moduleinst_ok s (frame_MODULE f) C" 
          "t_inst_match C C'"
        shows "context_TYPES C' ! proj_uN_0 x = fun_type (mk_state s f) x"
  using assms proof(induction s "frame_MODULE f" C rule:Moduleinst_ok.induct)
  case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
          functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
          dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
  then show ?case using t_inst_match_def fun_type.psimps fun_type.domintros 
    by (metis moduleinst.select_convs(1) res_context.select_convs(1))
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

lemma Externaddr_ok_inj_func:
  assumes "Externaddr_ok s x (FUNC t)"
          "Externaddr_ok s x (FUNC t')"
        shows "t = t'"
  using assms proof (induction s x "FUNC t")
  case (Externaddr_ok__func a s v_funcinst)
  show ?case using Externaddr_ok__func(6,1-5)
  proof (induction s "externaddr_FUNC a" "FUNC t'" rule:Externaddr_ok.induct)
  case (Externaddr_ok__func s v_funcinst')
  then show ?case by simp
next
  case (Externaddr_ok__sub s xt')
  show ?case using Externaddr_ok__sub(3) Externaddr_ok__sub
  proof (induction xt' "FUNC t'" rule:Externtype_sub.induct)
     case (Externtype_sub__func ft_1)
     then show ?case 
       by (metis Functype_sub.cases)
   qed
qed
next
  case (Externaddr_ok__sub s v_externaddr xt')
   show ?case using Externaddr_ok__sub(3) Externaddr_ok__sub
  proof (induction xt' "FUNC t" rule:Externtype_sub.induct)
     case (Externtype_sub__func ft_1)
     then show ?case 
       by (metis Functype_sub.cases)
   qed
 qed

lemma list_all2_eq: 
  assumes "list_all2 P l l1" "list_all2 P l l2" 
    "\<forall> x y1 y2. P x y1 \<longrightarrow> P x y2 \<longrightarrow> y1 = y2"
  shows "l1 = l2" 
  using assms
proof (induction l1 arbitrary:l2)
  case Nil
  then show ?case by fast
next
  case (Cons x xs y ys)
  note outer = Cons
  then show ?case proof (cases l2)
    case Nil
    then show ?thesis using Cons by fast 
  next
    case (Cons a list)
    then show ?thesis using outer by blast
  qed
qed


lemma Externaddr_ok_inj_glob:
  assumes "Externaddr_ok s x (GLOBAL t)"
          "Externaddr_ok s x (GLOBAL t')"
        shows "t = t'"
  using assms proof (induction s x "GLOBAL t")
  case (Externaddr_ok__global a s v_funcinst)
  show ?case using Externaddr_ok__global(6,1-5)
  proof (induction s "externaddr_GLOBAL a" "GLOBAL t'" rule:Externaddr_ok.induct)
  case (Externaddr_ok__global s v_funcinst')
  then show ?case by simp
next
  case (Externaddr_ok__sub s xt')
  show ?case using Externaddr_ok__sub(3) Externaddr_ok__sub
  proof (induction xt' "GLOBAL t'" rule:Externtype_sub.induct)
     case (Externtype_sub__global ft_1)
     then show ?case 
       by (metis Globaltype_sub.cases)
   qed
qed
next
  case (Externaddr_ok__sub s v_externaddr xt')
   show ?case using Externaddr_ok__sub(3) Externaddr_ok__sub
  proof (induction xt' "GLOBAL t" rule:Externtype_sub.induct)
     case (Externtype_sub__global ft_1)
     then show ?case 
       by (metis Globaltype_sub.cases)
   qed
 qed

(* is this still useful? *)
(*
lemma Ref_ok_inj:
  assumes "Ref_ok s r rt" "Ref_ok s r rt'" shows "rt = rt'"
  using assms proof (induction s r rt rule:Ref_ok.induct)
  case (null s rt)
  show ?case using null(2) proof (induction s "ref_REF_NULL rt" rt' rule:Ref_ok.induct)
     case (null s)
     then show ?case by simp
   qed
next
  case (Ref_ok__func s a ext)
  show ?case using Ref_ok__func(4) proof (induction s "REF_FUNC_ADDR a" rt' rule:Ref_ok.induct)
    case (Ref_ok__func s ext)
    then show ?case by simp
  qed
next
  case (extern s a)
  show ?case using extern(2) proof (induction s "REF_HOST_ADDR a" rt' rule:Ref_ok.induct)
    case (extern s)
    then show ?case by simp
  qed
qed *)

lemma Eleminst_ok_inj: assumes "Eleminst_ok s v t" "Eleminst_ok s v t'" shows "t = t'"
  using assms proof(induction s v t rule:Eleminst_ok.induct)
  case (mk_Eleminst_ok s rt ref_lst)
  show ?case using mk_Eleminst_ok(3,1,2) proof (induction s "\<lparr> eleminst_TYPE = rt, 
           eleminst_REFS = ref_lst\<rparr>" t' rule:Eleminst_ok.induct)
    case (mk_Eleminst_ok s rt' ref_lst')
    then show ?case by simp 
  qed
qed

(*
lemma Datainst_ok_inj: assumes "Datainst_ok s v t" "Datainst_ok s v t'" shows "t = t'"
  using assms proof(induction s v t rule:Datainst_ok.induct)
  case (mk_Datainst_ok s b_lst)
  show ?case using mk_Eleminst_ok(3,1,2) proof (induction s "\<lparr> eleminst_TYPE = rt, 
           eleminst_REFS = ref_lst\<rparr>" t' rule:Eleminst_ok.induct)
    case (mk_Eleminst_ok s rt' ref_lst')
    then show ?case by simp 
  qed
qed *)

lemma res_datatype_inj: shows "(x :: res_datatype) = y"
  by (metis res_datatype.exhaust)

lemma context_data_inj: 
  assumes "length (l :: res_datatype list) = length l'" 
  shows "l = l'" 
  using assms proof (induction l arbitrary: l')
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  note outer = Cons
  then show ?case proof (cases l')
    case Nil
    then show ?thesis using Cons by simp
  next
    case (Cons a' list)
    then show ?thesis using outer res_datatype_inj by simp
  qed
qed

lemma Moduleinst_ok_partial_inj:
  assumes "Moduleinst_ok s t C" "Moduleinst_ok s t C'" 
  shows "context_TYPES C = context_TYPES C' \<and>
          context_FUNCS C = context_FUNCS C' \<and> 
          context_GLOBALS C = context_GLOBALS C' \<and> 
          context_ELEMS C = context_ELEMS C' \<and> 
          context_DATAS C = context_DATAS C'"
  using assms proof (induction s t C rule:Moduleinst_ok.induct)
  case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
          functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
          dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
  show ?case using mk_Moduleinst_ok(27,1-26)
  proof (induction s "\<lparr>TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, 
        TABLES = tableaddr_lst,
        MEMS = memaddr_lst, ELEMS = elemaddr_lst, DATAS = dataaddr_lst, 
        EXPORTS = exportinst_lst\<rparr>" C')
    case (mk_Moduleinst_ok functype_lst' globaladdr_lst' globaltype_lst' s funcaddr_lst' 
            functype_F_lst' memaddr_lst' memtype_lst' tableaddr_lst' tabletype_lst' exportinst_lst' 
            dataaddr_lst' datatype_lst' elemaddr_lst' elemtype_lst')
    then show ?case
      using list_all2_eq Externaddr_ok_inj_func  
        Externaddr_ok_inj_glob Eleminst_ok_inj context_data_inj
      by (metis (lifting) moduleinst.ext_inject res_context.select_convs(1,2,3,6,7))
  qed
  
qed

lemma Externaddr_ok__wf_memtype: assumes "Externaddr_ok s v (MEM t)" shows "wf_memtype t"
  using assms proof(induction s v "MEM t" rule:Externaddr_ok.induct)
  case (Externaddr_ok__mem a s v_meminst)
  then show ?case 
    by (metis externtype.distinct(11,5,9) externtype.inject(4) wf_externtype.cases) 
next
  case (Externaddr_ok__sub s v_externaddr xt')
  then show ?case 
    using wf_externtype.simps by blast 
qed

lemma Instr_ok_replace_agree:
  assumes "Moduleinst_ok s i Cemp" 
          "Moduleinst_ok s i Cemp'"
          "t_inst_match Cemp C" 
          "t_inst_match Cemp' C'"
          "context_LOCALS C = context_LOCALS C'"
          "LABELS C = LABELS C'"
          "context_RETURN C = context_RETURN C'"
          "wf_context C'"
          "Instr_ok C e tf"   
      shows "Instr_ok C' e tf"
  using assms assms(1) proof (induction s i Cemp rule:Moduleinst_ok.induct)
  case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst functype_F_lst 
          memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst dataaddr_lst 
          datatype_lst elemaddr_lst elemtype_lst)
  show ?case using mk_Moduleinst_ok(27) mk_Moduleinst_ok
  proof (induction s " \<lparr>TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, 
        TABLES = tableaddr_lst,
        MEMS = memaddr_lst, ELEMS = elemaddr_lst, DATAS = dataaddr_lst, EXPORTS = exportinst_lst\<rparr>"
     Cemp' rule: Moduleinst_ok.induct)
    case (mk_Moduleinst_ok functype_lst' globaladdr_lst' globaltype_lst' s' funcaddr_lst' 
          functype_F_lst' memaddr_lst' memtype_lst' tableaddr_lst' tabletype_lst' exportinst_lst'
          dataaddr_lst' datatype_lst' elemaddr_lst' elemtype_lst')
    show ?case using mk_Moduleinst_ok(61) mk_Moduleinst_ok
    proof (induction C e tf arbitrary:C'
        rule:Instr_ok_Instrs_ok.inducts(1)[where ?P2.0 = "\<lambda> C es tf. 
        (\<forall> C'.
        Moduleinst_ok s'
     \<lparr>TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, TABLES = tableaddr_lst,
        MEMS = memaddr_lst, ELEMS = elemaddr_lst, DATAS = dataaddr_lst, EXPORTS = exportinst_lst\<rparr>
     \<lparr>context_TYPES = functype_lst, context_FUNCS = functype_F_lst, context_GLOBALS = globaltype_lst,
        context_TABLES = tabletype_lst, context_MEMS = memtype_lst, context_ELEMS = elemtype_lst,
        context_DATAS = datatype_lst, context_LOCALS = [], LABELS = [], context_RETURN = None\<rparr> \<longrightarrow>
        Moduleinst_ok s'
     \<lparr>TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, TABLES = tableaddr_lst,
        MEMS = memaddr_lst, ELEMS = elemaddr_lst, DATAS = dataaddr_lst, EXPORTS = exportinst_lst\<rparr>
     \<lparr>context_TYPES = functype_lst', context_FUNCS = functype_F_lst', context_GLOBALS = globaltype_lst',
        context_TABLES = tabletype_lst', context_MEMS = memtype_lst', context_ELEMS = elemtype_lst',
        context_DATAS = datatype_lst', context_LOCALS = [], LABELS = [], context_RETURN = None\<rparr> \<longrightarrow>
        t_inst_match \<lparr>context_TYPES = functype_lst, context_FUNCS = functype_F_lst, 
        context_GLOBALS = globaltype_lst,
        context_TABLES = tabletype_lst, context_MEMS = memtype_lst, context_ELEMS = elemtype_lst,
        context_DATAS = datatype_lst, context_LOCALS = [], LABELS = [], context_RETURN = None\<rparr> C \<longrightarrow> 
        t_inst_match  \<lparr>context_TYPES = functype_lst', context_FUNCS = functype_F_lst', 
        context_GLOBALS = globaltype_lst',
        context_TABLES = tabletype_lst', context_MEMS = memtype_lst', context_ELEMS = elemtype_lst',
        context_DATAS = datatype_lst', context_LOCALS = [], LABELS = [], context_RETURN = None\<rparr> C' \<longrightarrow>
        wf_context C' \<longrightarrow>
        context_LOCALS C = context_LOCALS C' \<longrightarrow>
          LABELS C = LABELS C' \<longrightarrow>
          context_RETURN C = context_RETURN C' \<longrightarrow>
        Instrs_ok C' es tf)"])
      case (block C bt t_1_lst t_2_lst instr_lst)
      then show ?case 
        using 
          isabelle_reference_output_wasm2.block[OF
          Blocktype_ok_replace_agree[OF block(68,60,61,62,66,1)]]
          t_inst_match_def
        using append_res_context_def wf_context.simps by force       
    next
      case (loop C bt t_1_lst t_2_lst instr_lst)
      then show ?case using 
          isabelle_reference_output_wasm2.loop[OF 
            Blocktype_ok_replace_agree[OF loop(68,60,61,62,66,1)]]
          t_inst_match_def
        using append_res_context_def wf_context.simps by force 
    next
      case (res_if C bt t_1_lst t_2_lst instr_1_lst instr_2_lst)
      then show ?case 
        using 
          isabelle_reference_output_wasm2.res_if[OF 
            Blocktype_ok_replace_agree[OF res_if(70,62,63,64,68,1)]]
          t_inst_match_def
        using append_res_context_def wf_context.simps by force 
    next
      case (call x C t_1_lst t_2_lst)
      then show ?case using Moduleinst_ok_partial_inj Instr_ok_Instrs_ok.intros 
        by (metis (no_types, lifting) t_inst_match_def)  

(*      then have 1: "Externaddr_ok s' (externaddr_FUNC (funcaddr_lst ! proj_uN_0 x)) 
                  (FUNC (functype_F_lst ! proj_uN_0 x))"
        using list_all2_nth' t_inst_match_def
        by (metis (no_types, lifting) res_context.select_convs(2)) 
      have 2: "Externaddr_ok s' (externaddr_FUNC (funcaddr_lst' ! proj_uN_0 x)) 
              (FUNC (functype_F_lst' ! proj_uN_0 x))"
        using list_all2_nth' t_inst_match_def call 
        res_context.select_convs(2) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have "Externaddr_ok s' (externaddr_FUNC (funcaddr_lst ! proj_uN_0 x)) 
                  (FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and> 
          Externaddr_ok s' (externaddr_FUNC (funcaddr_lst ! proj_uN_0 x)) 
              (FUNC (context_FUNCS C' ! proj_uN_0 x))"
        using 1 t_inst_match_def call by simp 
      then have 
        "proj_uN_0 x < length (context_FUNCS C') \<and>
         context_FUNCS C' ! proj_uN_0 x = mk_functype (mk_list t_1_lst) (mk_list t_2_lst)"
        using Externaddr_ok_inj_func 2 t_inst_match_def
        using call.hyps(1) call.prems(55,56) mk_Moduleinst_ok.hyps(27,4) mk_Moduleinst_ok.prems(4)
        by auto
      then show ?case
        using isabelle_reference_output_wasm2.call 
        call by simp *)
    next
      case (call_indirect x C lim y t_1_lst t_2_lst)
      then show ?case sorry
    next
      case (ref_func x C ft)
      then show ?case using Moduleinst_ok_partial_inj Instr_ok_Instrs_ok.intros 
        by (metis (no_types, lifting) t_inst_match_def)  
    next
      case (global_get x C v_mut t)
      then show ?case using Moduleinst_ok_partial_inj Instr_ok_Instrs_ok.intros 
        by (metis (no_types, lifting) t_inst_match_def)  
    next
      case (global_set x C t)
      then show ?case using Moduleinst_ok_partial_inj Instr_ok_Instrs_ok.intros 
        by (metis (no_types, lifting) t_inst_match_def)  
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
      then show ?case using Moduleinst_ok_partial_inj Instr_ok_Instrs_ok.intros 
        by (metis (no_types, lifting) t_inst_match_def)  
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
      then show ?case using Moduleinst_ok_partial_inj Instr_ok_Instrs_ok.intros 
        by (metis (no_types, lifting) t_inst_match_def)  
    next
      case (load_val C mt nt v_memarg)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def load_val 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def load_val by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using load_val
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.load_val 
        load_val by simp
    next
      case (load_pack C mt v_memarg v_M v_Inn v_sx)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def load_pack 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def load_pack by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using load_pack 
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.load_pack 
        load_pack by simp
    next
      case (store_val C mt nt v_memarg)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def store_val 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def store_val by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using store_val
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.store_val 
        store_val by simp
    next
      case (store_pack C mt v_memarg v_M v_Inn)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def store_pack 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def store_pack by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using store_pack
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.store_pack 
        store_pack by simp
    next
      case (vload C mt v_memarg v_M v_N v_sx)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def vload 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def vload by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using vload
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.vload 
        vload by simp
    next
      case (vload_splat C mt v_memarg v_n)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def vload_splat 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def vload_splat by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using vload_splat
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.vload_splat
        vload_splat by simp
    next
      case (vload_zero C mt v_memarg v_n)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def vload_zero 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def vload_zero by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using vload_zero
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.vload_zero 
        vload_zero by simp
    next
      case (vload_lane C mt v_memarg v_n v_laneidx)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def vload_lane 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def vload_lane by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using vload_lane
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.vload_lane 
        vload_lane by simp
    next
      case (vstore C mt v_memarg)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def vstore 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def vstore by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using vstore
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.vstore 
        vstore by simp
    next
      case (vstore_lane C mt v_memarg v_n v_laneidx)
      have "Externaddr_ok s' (externaddr_MEM (memaddr_lst' ! 0)) 
              (MEM (memtype_lst' ! 0))"
        using list_all2_nth' t_inst_match_def vstore_lane 
        res_context.select_convs(5) 
        by (metis (no_types, lifting) moduleinst.ext_inject)       
       then have
          "Externaddr_ok s' (externaddr_MEM (memaddr_lst ! 0)) 
              (MEM (context_MEMS C' ! 0))"
         using t_inst_match_def vstore_lane by simp 
      then have 
        "0 < length (context_MEMS C') \<and>
         wf_memtype (context_MEMS C' ! 0)"
        using Externaddr_ok__wf_memtype 
        using vstore_lane
          t_inst_match_def by force
      then show ?case
        using isabelle_reference_output_wasm2.vstore_lane 
        vstore_lane by simp
    next
      case (Instrs_ok__instr C v_instr t_1_lst t_2_lst)                       
      then show ?case using isabelle_reference_output_wasm2.Instrs_ok__instr 
        using mk_Moduleinst_ok.hyps(11,13,14,16,2,22,23,24,25,26,27,3,4,5,6,7,8,9)
          mk_Moduleinst_ok.prems(1,10,11,12,13,14,15,16,17,18,19,2,20,21,22,23,24,25,26,3,4,5,6,7,8,9)
        by blast
          (* this next line can take a wee minute *)
    qed(auto simp add: Instr_ok_Instrs_ok.intros Moduleinst_ok_partial_inj)+
    
    qed
qed

end