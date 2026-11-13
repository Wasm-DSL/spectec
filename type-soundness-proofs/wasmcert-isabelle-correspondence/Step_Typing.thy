(* The typing invariant of the reduction simulation.

   Step_Sim.thy proves the simulation under the locale [sim_inv], which abstracts
   the invariant [Inv] that supplies facts about the redex and the store. Here
   [Inv_typed] instantiates it with SpecTec's own typing, as in the Rocq bridge
   (reduction.v, [Inv]): the store is valid, the frame's module instance is valid
   at a context [C], the locals have the types of the context [C'] the
   instructions are typed in, and [C'] agrees with [C] except for locals, labels
   and return. The label and return arities [ls] and [r] are those of [C'].

   The inversion lemmas come from SpecTec's soundness proof
   (../isabelle/Type_Inversion.thy, imported by Spec_Aux.thy). *)
theory Step_Typing
  imports Step_Sim Config_Typing
begin

section \<open>The invariant\<close>

(* [C'] agrees with the module context [C] on everything but locals, labels and
   return. *)
definition inst_match :: "res_context \<Rightarrow> res_context \<Rightarrow> bool" where
  "inst_match C C' \<longleftrightarrow>
     context_TYPES C' = context_TYPES C \<and> context_FUNCS C' = context_FUNCS C \<and>
     context_GLOBALS C' = context_GLOBALS C \<and> context_TABLES C' = context_TABLES C \<and>
     context_MEMS C' = context_MEMS C \<and> context_ELEMS C' = context_ELEMS C \<and>
     context_DATAS C' = context_DATAS C"

(* The arity of a label or return type. *)
definition rlen :: "resulttype \<Rightarrow> nat" where
  "rlen t = length (proj_list_0 t)"

lemma rlen_mk_list[simp]: "rlen (mk_list ts) = length ts"
  by (simp add: rlen_def)

fun Inv_typed :: "state \<Rightarrow> admininstr list \<Rightarrow> nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "Inv_typed (mk_state s f) es ls r \<longleftrightarrow>
     wf_config (mk_config (mk_state s f) es) \<and> Store_ok s \<and>
     (\<exists>C C' t1 t2. Moduleinst_ok s (frame_MODULE f) C \<and>
        list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C') (LOCALS f) \<and> inst_match C C' \<and>
        Instrs_ok2 s C' es (mk_functype t1 t2) \<and>
        ls = map rlen (LABELS C') \<and> r = map_option rlen (context_RETURN C'))"

(* The contexts of a label body and of a frame body (SpecTec's [label] and [frame]
   typing rules). *)
abbreviation lab_ctx :: "resulttype \<Rightarrow> res_context \<Rightarrow> res_context" where
  "lab_ctx t C \<equiv> append_res_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
      context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
      LABELS = [t], context_RETURN = None\<rparr> C"

abbreviation ret_ctx :: "resulttype \<Rightarrow> res_context \<Rightarrow> res_context" where
  "ret_ctx t C \<equiv> append_res_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
      context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
      LABELS = [], context_RETURN = Some t\<rparr> C"

abbreviation loc_ctx :: "valtype list \<Rightarrow> res_context \<Rightarrow> res_context" where
  "loc_ctx ts C \<equiv> append_res_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
      context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = ts,
      LABELS = [], context_RETURN = None\<rparr> C"

lemma lab_ctx_simps[simp]:
  "LABELS (lab_ctx t C) = t # LABELS C"
  "context_RETURN (lab_ctx t C) = context_RETURN C"
  "context_LOCALS (lab_ctx t C) = context_LOCALS C"
  "inst_match C0 (lab_ctx t C) = inst_match C0 C"
  by (simp_all add: append_res_context_def inst_match_def)

lemma ret_ctx_simps[simp]:
  "LABELS (ret_ctx t C) = LABELS C"
  "context_RETURN (ret_ctx t C) = Some t"
  "context_LOCALS (ret_ctx t C) = context_LOCALS C"
  "inst_match C0 (ret_ctx t C) = inst_match C0 C"
  by (simp_all add: append_res_context_def inst_match_def)

lemma loc_ctx_simps[simp]:
  "LABELS (loc_ctx ts C) = LABELS C"
  "context_RETURN (loc_ctx ts C) = context_RETURN C"
  "context_LOCALS (loc_ctx ts C) = ts @ context_LOCALS C"
  "inst_match C0 (loc_ctx ts C) = inst_match C0 C"
  by (simp_all add: append_res_context_def inst_match_def)

lemma inst_match_refl: "inst_match C C"
  by (simp add: inst_match_def)

section \<open>Store and module instances\<close>

lemma Externaddr_ok_bounds:
  "Externaddr_ok s xa xt \<Longrightarrow>
   (case xa of externaddr_FUNC a \<Rightarrow> a < length (store_FUNCS s)
             | externaddr_GLOBAL a \<Rightarrow> a < length (store_GLOBALS s)
             | externaddr_TABLE a \<Rightarrow> a < length (store_TABLES s)
             | externaddr_MEM a \<Rightarrow> a < length (store_MEMS s))"
  by (induction rule: Externaddr_ok.induct) auto

lemma mem_addrs_bound:
  "list_all2 (\<lambda>a mt. Externaddr_ok s (externaddr_MEM a) (MEM mt)) as mts \<Longrightarrow>
   \<forall>a\<in>set as. a < length (store_MEMS s)"
  by (induction rule: list_all2_induct) (auto dest: Externaddr_ok_bounds)

lemma tab_addrs_bound:
  "list_all2 (\<lambda>a tt. Externaddr_ok s (externaddr_TABLE a) (TABLE tt)) as tts \<Longrightarrow>
   \<forall>a\<in>set as. a < length (store_TABLES s)"
  by (induction rule: list_all2_induct) (auto dest: Externaddr_ok_bounds)

lemma Moduleinst_ok_E:
  assumes "Moduleinst_ok s mi C"
  shows "context_TYPES C = TYPES mi" "length (context_TABLES C) = length (TABLES mi)"
    "length (context_MEMS C) = length (MEMS mi)"
    "\<forall>a\<in>set (MEMS mi). a < length (store_MEMS s)" "\<forall>a\<in>set (TABLES mi). a < length (store_TABLES s)"
    "context_LOCALS C = []" "LABELS C = []" "context_RETURN C = None"
  using assms by (cases rule: Moduleinst_ok.cases; simp add: mem_addrs_bound tab_addrs_bound)+

lemma Ref_ok_func: "Ref_ok s (REF_FUNC_ADDR a) rt \<Longrightarrow> a < length (store_FUNCS s)"
  by (auto elim!: Ref_ok.cases dest!: Externaddr_ok_bounds)

lemma Tableinst_ok_Ref_ok: "Tableinst_ok s t tt \<Longrightarrow> \<exists>rt. list_all (\<lambda>r. Ref_ok s r rt) (REFS t)"
  by (erule Tableinst_ok.cases) auto

lemma Tableinst_ok_refs:
  assumes "Tableinst_ok s t tt" "REF_FUNC_ADDR a \<in> set (REFS t)"
  shows "a < length (store_FUNCS s)"
proof -
  obtain rt where "list_all (\<lambda>r. Ref_ok s r rt) (REFS t)" using Tableinst_ok_Ref_ok[OF assms(1)] by blast
  then have "Ref_ok s (REF_FUNC_ADDR a) rt" using assms(2) by (simp add: list_all_iff)
  then show ?thesis by (rule Ref_ok_func)
qed

lemma wf_store_datas: "wf_store s \<Longrightarrow> list_all wf_datainst (store_DATAS s)"
  by (erule wf_store.cases) simp

lemma wf_byte_lt: "wf_byte b \<Longrightarrow> proj_byte_0 b < 256"
  by (erule wf_byte.cases) simp

lemma wf_datainst_all: "wf_datainst d \<Longrightarrow> list_all wf_byte (datainst_BYTES d)"
  by (erule wf_datainst.cases) simp

lemma wf_datainst_bytes:
  assumes "wf_datainst d" "b \<in> set (datainst_BYTES d)"
  shows "proj_byte_0 b < 256"
proof -
  have "wf_byte b" using wf_datainst_all[OF assms(1)] assms(2) by (simp add: list_all_iff)
  then show ?thesis by (rule wf_byte_lt)
qed

lemma Store_ok_wf: "Store_ok s \<Longrightarrow> wf_store s"
  by (erule Store_ok.cases) simp

lemma Store_ok_state_inv:
  assumes S: "Store_ok s" and M: "Moduleinst_ok s (frame_MODULE f) C"
  shows "state_inv s f"
  unfolding state_inv_def
proof (intro conjI ballI allI impI)
  fix a assume "a \<in> set (MEMS (frame_MODULE f))"
  then show "a < length (store_MEMS s)" using Moduleinst_ok_E(4)[OF M] by blast
next
  fix a assume "a \<in> set (TABLES (frame_MODULE f))"
  then show "a < length (store_TABLES s)" using Moduleinst_ok_E(5)[OF M] by blast
next
  fix t a assume t: "t \<in> set (store_TABLES s)" and a: "REF_FUNC_ADDR a \<in> set (REFS t)"
  obtain tt where "Tableinst_ok s t tt" using Store_ok_elems(2)[OF S t] by blast
  then show "a < length (store_FUNCS s)" using a by (rule Tableinst_ok_refs)
next
  fix d b assume d: "d \<in> set (store_DATAS s)" and b: "b \<in> set (datainst_BYTES d)"
  have "wf_datainst d" using wf_store_datas[OF Store_ok_wf[OF S]] d by (simp add: list_all_iff)
  then show "proj_byte_0 b < 256" using b by (rule wf_datainst_bytes)
qed

lemma Store_ok_mem_pages:
  assumes S: "Store_ok s"
  shows "mem_pages s"
  unfolding mem_pages_def
proof
  fix m assume "m \<in> set (store_MEMS s)"
  then obtain mt where "Meminst_ok s m mt" using Store_ok_elems(3)[OF S] by blast
  then show "\<exists>i j. meminst_TYPE m = PAGE (mk_limits i j) \<and> length (BYTES m) = un i * (64 * Ki)"
    by (cases rule: Meminst_ok.cases) auto
qed

section \<open>Typing of the parts of a configuration\<close>

(* A plain instruction inside a typed admin instruction list. *)
lemma Instrs_ok2_single_plain:
  assumes "Instrs_ok2 s C [a] (mk_functype t1 t2)" "a = admininstr_instr e"
  shows "\<exists>ft. Instr_ok C e ft"
proof -
  obtain tp1 tp2 where "Instr_ok2 s C a (mk_functype tp1 tp2)"
    using inv_one_admininstr[OF assms(1)] by blast
  then show ?thesis using inv_plain assms(2) by blast
qed

lemma Instrs_ok2_mid:
  assumes "Instrs_ok2 s C (es1 @ es @ es2) (mk_functype t1 t2)"
  shows "\<exists>t3 t4. Instrs_ok2 s C es (mk_functype t3 t4)"
proof -
  obtain t3 where "Instrs_ok2 s C (es @ es2) (mk_functype t3 t2)"
    using inv_seq[OF assms HOL.refl] by blast
  then obtain t4 where "Instrs_ok2 s C es (mk_functype t3 t4)"
    using inv_seq[OF _ HOL.refl] by blast
  then show ?thesis by blast
qed

lemma Instrs_ok2_elem_plain:
  assumes "Instrs_ok2 s C es (mk_functype t1 t2)" "admininstr_instr e \<in> set es"
  shows "\<exists>ft. Instr_ok C e ft"
proof -
  obtain xs ys where "es = xs @ [admininstr_instr e] @ ys" using assms(2) by (metis split_list append_Cons append_Nil)
  then obtain t3 t4 where "Instrs_ok2 s C [admininstr_instr e] (mk_functype t3 t4)"
    using Instrs_ok2_mid assms(1) by metis
  then show ?thesis using Instrs_ok2_single_plain by blast
qed

lemma Inv_typedI:
  assumes "wf_config (mk_config (mk_state s f) es)" "Store_ok s" "Moduleinst_ok s (frame_MODULE f) C"
    "list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C') (LOCALS f)" "inst_match C C'"
    "Instrs_ok2 s C' es (mk_functype t1 t2)" "ls = map rlen (LABELS C')" "r = map_option rlen (context_RETURN C')"
  shows "Inv_typed (mk_state s f) es ls r"
proof -
  have "\<exists>C C' t1 t2. Moduleinst_ok s (frame_MODULE f) C \<and>
          list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C') (LOCALS f) \<and> inst_match C C' \<and>
          Instrs_ok2 s C' es (mk_functype t1 t2) \<and>
          ls = map rlen (LABELS C') \<and> r = map_option rlen (context_RETURN C')"
    apply (rule exI[of _ C], rule exI[of _ C'], rule exI[of _ t1], rule exI[of _ t2])
    using assms(3-8) by (intro conjI)
  then show ?thesis using assms(1,2) by simp
qed

lemma Inv_label:
  assumes "Inv_typed z [admininstr_sc7 (LABEL_underscore n ins es)] ls r"
  shows "Inv_typed z es (n # ls) r"
proof (cases z)
  case (mk_state s f)
  from assms mk_state obtain C C' t1 t2 where
    w: "wf_config (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)])" and S: "Store_ok s"
    and M: "Moduleinst_ok s (frame_MODULE f) C"
    and L: "list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C') (LOCALS f)" and m: "inst_match C C'"
    and T: "Instrs_ok2 s C' [admininstr_sc7 (LABEL_underscore n ins es)] (mk_functype t1 t2)"
    and ls: "ls = map rlen (LABELS C')" and r: "r = map_option rlen (context_RETURN C')"
    by auto
  obtain tp1 tp2 where "Instr_ok2 s C' (admininstr_sc7 (LABEL_underscore n ins es)) (mk_functype tp1 tp2)"
    using inv_one_admininstr[OF T] by blast
  then obtain t' t where
    B: "Instrs_ok2 s (lab_ctx (mk_list t') C') es (mk_functype (mk_list []) (mk_list t))" and n: "n = length t'"
    using Type_Inversion.inv_label[OF _ HOL.refl] by blast
  have w': "wf_config (mk_config (mk_state s f) es)" using w by (simp add: wf_config_simps wf_label_iff)
  have L': "list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS (lab_ctx (mk_list t') C')) (LOCALS f)"
    using L by (simp add: append_res_context_def)
  have m': "inst_match C (lab_ctx (mk_list t') C')"
    using m by (simp add: append_res_context_def inst_match_def)
  have ls': "n # ls = map rlen (LABELS (lab_ctx (mk_list t') C'))"
    using ls n by (simp add: append_res_context_def)
  have r': "r = map_option rlen (context_RETURN (lab_ctx (mk_list t') C'))"
    using r by (simp add: append_res_context_def)
  show ?thesis unfolding mk_state by (rule Inv_typedI[OF w' S M L' m' B ls' r'])
qed

lemma Frame_ok_E:
  assumes "Frame_ok s f C'"
  shows "\<exists>C. Moduleinst_ok s (frame_MODULE f) C \<and> inst_match C C' \<and>
    list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C') (LOCALS f) \<and>
    LABELS C' = [] \<and> context_RETURN C' = None"
  using assms
  apply (cases rule: Frame_ok.cases)
  apply (frule Moduleinst_ok_ctx)
  apply (auto simp: inst_match_def append_res_context_def)
  done

lemma Inv_frame:
  assumes "Inv_typed (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)] ls r"
  shows "Inv_typed (mk_state s f') es [] (Some n)"
proof -
  from assms obtain C1 t1 t2 where
    w: "wf_config (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)])" and S: "Store_ok s"
    and T: "Instrs_ok2 s C1 [admininstr_sc8 (FRAME_underscore n f' es)] (mk_functype t1 t2)"
    by auto
  obtain tp1 tp2 where "Instr_ok2 s C1 (admininstr_sc8 (FRAME_underscore n f' es)) (mk_functype tp1 tp2)"
    using inv_one_admininstr[OF T] by blast
  then obtain C' t where F: "Frame_ok s f' C'"
    and E: "Expr_ok2 s (ret_ctx (mk_list t) C') es (mk_list t)" and n: "n = length t"
    using Type_Inversion.inv_frame[OF _ HOL.refl] by blast
  obtain C where M: "Moduleinst_ok s (frame_MODULE f') C" and m: "inst_match C C'"
    and L: "list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C') (LOCALS f')" and lab: "LABELS C' = []"
    using Frame_ok_E[OF F] by blast
  have B: "Instrs_ok2 s (ret_ctx (mk_list t) C') es (mk_functype (mk_list []) (mk_list t))"
    using inv_expr(1)[OF E] .
  have w': "wf_config (mk_config (mk_state s f') es)"
    using w by (simp add: wf_config_simps wf_state_simps wf_frame_iff)
  have L': "list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS (ret_ctx (mk_list t) C')) (LOCALS f')"
    using L by (simp add: append_res_context_def)
  have m': "inst_match C (ret_ctx (mk_list t) C')"
    using m by (simp add: append_res_context_def inst_match_def)
  have ls': "[] = map rlen (LABELS (ret_ctx (mk_list t) C'))"
    using lab by (simp add: append_res_context_def)
  have r': "Some n = map_option rlen (context_RETURN (ret_ctx (mk_list t) C'))"
    using n by (simp add: append_res_context_def)
  show ?thesis by (rule Inv_typedI[OF w' S M L' m' B ls' r'])
qed

lemma Inv_instrs:
  assumes "Inv_typed z (map admininstr_val vs @ es @ es1) ls r"
  shows "Inv_typed z es ls r"
proof (cases z)
  case (mk_state s f)
  from assms mk_state obtain C C' t1 t2 where
    w: "wf_config (mk_config (mk_state s f) (map admininstr_val vs @ es @ es1))" and S: "Store_ok s"
    and M: "Moduleinst_ok s (frame_MODULE f) C"
    and L: "list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C') (LOCALS f)" and m: "inst_match C C'"
    and T: "Instrs_ok2 s C' (map admininstr_val vs @ es @ es1) (mk_functype t1 t2)"
    and ls: "ls = map rlen (LABELS C')" and r: "r = map_option rlen (context_RETURN C')"
    by auto
  obtain t3 t4 where B: "Instrs_ok2 s C' es (mk_functype t3 t4)" using Instrs_ok2_mid[OF T] by blast
  have w': "wf_config (mk_config (mk_state s f) es)" using w by (simp add: wf_config_simps)
  show ?thesis unfolding mk_state by (rule Inv_typedI[OF w' S M L m B ls r])
qed

section \<open>Breaks and returns leaving a label\<close>

(* The last instruction of the values-then-instruction prefix of a label body is
   typed in the label's context. *)
lemma label_prefix_instr:
  assumes "Instr_ok2 s C (admininstr_sc7 (LABEL_underscore n ins ((map admininstr_val vs @ [a]) @ es'))) ft"
    "a = admininstr_instr e"
  shows "\<exists>t' ft'. Instr_ok (lab_ctx (mk_list t') C) e ft'"
proof -
  obtain t' t where
    B: "Instrs_ok2 s (lab_ctx (mk_list t') C) ((map admininstr_val vs @ [a]) @ es') (mk_functype (mk_list []) (mk_list t))"
    using Type_Inversion.inv_label[OF assms(1) HOL.refl] by blast
  have B': "Instrs_ok2 s (lab_ctx (mk_list t') C) (map admininstr_val vs @ [a] @ es') (mk_functype (mk_list []) (mk_list t))"
    using B by simp
  obtain t3 t4 where "Instrs_ok2 s (lab_ctx (mk_list t') C) [a] (mk_functype t3 t4)"
    using Instrs_ok2_mid[OF B'] by blast
  then show ?thesis using Instrs_ok2_single_plain assms(2) by blast
qed

lemma Resulttype_sub_length: "Resulttype_sub (mk_list ts) t \<Longrightarrow> length ts = rlen t"
  by (auto simp: Resulttype_sub.simps rlen_def list_all2_lengthD)

lemma Inv_br:
  assumes "Inv_typed z [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs @
             [admininstr_sc0 (admininstr_st0_BR (mk_uN (x + 1)))] @ es))] ls r"
  shows "x < length ls \<and> ls ! x \<le> length vs"
proof (cases z)
  case (mk_state s f)
  from assms mk_state obtain C' t1 t2 where
    T: "Instrs_ok2 s C' [admininstr_sc7 (LABEL_underscore n ins ((map admininstr_val vs @
             [admininstr_sc0 (admininstr_st0_BR (mk_uN (Suc x)))]) @ es))] (mk_functype t1 t2)"
    and ls: "ls = map rlen (LABELS C')"
    by auto
  obtain tp1 tp2 where I: "Instr_ok2 s C' (admininstr_sc7 (LABEL_underscore n ins ((map admininstr_val vs @
             [admininstr_sc0 (admininstr_st0_BR (mk_uN (Suc x)))]) @ es))) (mk_functype tp1 tp2)"
    using inv_one_admininstr[OF T] by blast
  obtain t' ft where "Instr_ok (lab_ctx (mk_list t') C') (instr_sc0 (BR (mk_uN (Suc x)))) ft"
    using label_prefix_instr[OF I, where e = "instr_sc0 (BR (mk_uN (Suc x)))"] by auto
  then have xl: "x < length (LABELS C')" using Type_Inversion.inv_br[OF _ HOL.refl] by fastforce
  obtain vs1 vs2 where "vs = vs1 @ vs2" "Resulttype_sub (mk_list (map typeofval vs2)) (LABELS C' ! x)"
    using inv_label_const_list_br[OF I HOL.refl] by blast
  then have "ls ! x \<le> length vs" using ls xl Resulttype_sub_length by fastforce
  then show ?thesis using ls xl by simp
qed

lemma Inv_ret:
  assumes "Inv_typed z [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs @
             [admininstr_sc1 admininstr_st1_RETURN] @ es))] ls r"
  shows "\<exists>m. r = Some m \<and> m \<le> length vs"
proof (cases z)
  case (mk_state s f)
  from assms mk_state obtain C' t1 t2 where
    T: "Instrs_ok2 s C' [admininstr_sc7 (LABEL_underscore n ins ((map admininstr_val vs @
             [admininstr_sc1 admininstr_st1_RETURN]) @ es))] (mk_functype t1 t2)"
    and r: "r = map_option rlen (context_RETURN C')"
    by auto
  obtain tp1 tp2 where I: "Instr_ok2 s C' (admininstr_sc7 (LABEL_underscore n ins ((map admininstr_val vs @
             [admininstr_sc1 admininstr_st1_RETURN]) @ es))) (mk_functype tp1 tp2)"
    using inv_one_admininstr[OF T] by blast
  obtain t' ft where "Instr_ok (lab_ctx (mk_list t') C') (instr_sc1 RETURN) ft"
    using label_prefix_instr[OF I, where e = "instr_sc1 RETURN"] by auto
  then obtain tr where R: "context_RETURN C' = Some (mk_list tr)"
    using Type_Inversion.inv_return[OF _ HOL.refl] by fastforce
  obtain vs1 vs2 where "vs = vs1 @ vs2" "Resulttype_sub (mk_list (map typeofval vs2)) (mk_list tr)"
    using inv_label_const_list_return[OF I R] by blast
  then show ?thesis using r R Resulttype_sub_length by fastforce
qed

section \<open>Operand types\<close>


lemma valtype_numtype_ne[simp]: "valtype_numtype nt \<noteq> BOT" "valtype_numtype nt \<noteq> valtype_reftype rt"
  by (cases nt; cases rt; simp)+

lemma valtype_vectype_ne[simp]: "valtype_vectype vt \<noteq> BOT" "valtype_vectype vt \<noteq> valtype_reftype rt"
  "valtype_vectype vt \<noteq> valtype_I32"
  by (cases vt; cases rt; simp)+

lemma valtype_reftype_ne[simp]: "valtype_reftype rt \<noteq> BOT" "valtype_reftype rt \<noteq> valtype_I32"
  by (cases rt; simp)+

lemma valtype_numtype_I32[simp]: "valtype_numtype nt = valtype_I32 \<longleftrightarrow> nt = I32"
  by (cases nt) simp_all

lemma typeofval_ne_BOT: "typeofval v \<noteq> BOT"
  by (cases v) simp_all

(* Values have no proper subtypes other than bottom, which is no value's type. *)
lemma Valtype_sub_typeofval: "Valtype_sub (typeofval v) t \<Longrightarrow> typeofval v = t"
  by (erule Valtype_sub.cases) (simp_all add: typeofval_ne_BOT)

lemma Valtype_sub_ref:
  assumes "Valtype_sub (typeofval v) (valtype_reftype rt)"
  shows "\<exists>vr. tr_val v = V_ref vr"
proof -
  have e: "typeofval v = valtype_reftype rt" using Valtype_sub_typeofval[OF assms] .
  show ?thesis
  proof (cases v)
    case (val_CONST nt c) then show ?thesis using e by simp
  next
    case (val_VCONST vt c) then show ?thesis using e by simp
  qed simp_all
qed

lemma Valtype_sub_I32:
  assumes "Valtype_sub (typeofval v) valtype_I32"
  shows "\<exists>c. v = val_CONST I32 c"
proof -
  have e: "typeofval v = valtype_I32" using Valtype_sub_typeofval[OF assms] .
  show ?thesis
  proof (cases v)
    case (val_REF_NULL rt) then show ?thesis using e by simp
  qed (use e in simp_all)
qed

(* The instruction after a list of values is typed, and when it takes as many
   operands as there are values, the values have its operand types. *)
lemma vals_instr_typed:
  assumes "Instrs_ok2 s C (map admininstr_val vs @ [admininstr_instr e]) (mk_functype t1 t2)"
  shows "\<exists>tp1 tp2. Instr_ok C e (mk_functype (mk_list tp1) tp2) \<and>
           (length tp1 = length vs \<longrightarrow> Resulttype_sub (mk_list (map typeofval vs)) (mk_list tp1))"
proof -
  obtain tm where V: "Instrs_ok2 s C (map admininstr_val vs) (mk_functype t1 tm)"
      and E: "Instrs_ok2 s C [admininstr_instr e] (mk_functype tm t2)"
    using inv_seq[OF assms HOL.refl] by blast
  have sv: "Instrtype_sub (mk_instrtype (mk_list []) (mk_list (map typeofval vs))) (mk_instrtype t1 tm)"
    using inv_const_list[OF V HOL.refl] .
  obtain tp1 tp2 where I2: "Instr_ok2 s C (admininstr_instr e) (mk_functype tp1 tp2)"
      and se: "Instrtype_sub (mk_instrtype tp1 tp2) (mk_instrtype tm t2)"
    using inv_one_admininstr[OF E] by blast
  have I: "Instr_ok C e (mk_functype tp1 tp2)" using inv_plain[OF I2 HOL.refl] .
  obtain l1 where l1: "tp1 = mk_list l1" by (cases tp1)
  obtain l2 where l2: "tp2 = mk_list l2" by (cases tp2)
  have se': "Instrtype_sub (mk_instrtype (mk_list ([] @ l1)) (mk_list l2)) (mk_instrtype tm t2)"
    using se l1 l2 by simp
  have "length l1 = length vs \<longrightarrow> Resulttype_sub (mk_list (map typeofval vs)) (mk_list l1)"
  proof
    assume "length l1 = length vs"
    then have len: "length (map typeofval vs) = length l1" by simp
    show "Resulttype_sub (mk_list (map typeofval vs)) (mk_list l1)"
      using conjunct2[OF produce_consume[OF sv se' len]] .
  qed
  then show ?thesis using I l1 by blast
qed

section \<open>Facts about the redex\<close>

(* Every plain instruction of the configuration is typed in [C']. *)
abbreviation all_typed :: "res_context \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "all_typed C' es \<equiv> \<forall>e. admininstr_instr e \<in> set es \<longrightarrow> (\<exists>ft. Instr_ok C' e ft)"

lemma all_typed_wf: "all_typed C' es \<Longrightarrow> admininstr_instr e \<in> set es \<Longrightarrow> wf_instr e"
  by (blast dest: Instr_ok_wf(2))

lemma option_to_list_case: "option_to_list x = (case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a])"
  by (cases x) simp_all

lemma numtype_Inn_inj: "numtype_Inn a = numtype_Inn b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

lemma wf_load_pack_ext:
  "wf_instr (instr_sc5 (LOAD (numtype_Inn t) (Some (mk_loadop__0 t (mk_loadop_Inn (mk_sz n) sx))) ao)) \<Longrightarrow>
   ext_width_ok (numtype_Inn t) n"
  by (cases t) (auto elim!: wf_LOAD wf_loadopE wf_loadop_InnE fun_sizennE wf_szE
                     simp: ext_width_ok_def numtype_Inn_inj)

lemma wf_store_pack_ext:
  "wf_instr (instr_sc5 (STORE (numtype_Inn t) (Some (mk_sz n)) ao)) \<Longrightarrow> ext_width_ok (numtype_Inn t) n"
  by (cases t) (auto elim!: wf_STORE fun_sizennE wf_szE
                     simp: ext_width_ok_def numtype_Inn_inj option_to_list_case split: option.splits)

lemma wf_vload_zero: "wf_instr (instr_sc6 (VLOAD V128 (Some (vloadop__ZERO (mk_sz N))) ao)) \<Longrightarrow> N = 32 \<or> N = 64"
  by (auto elim!: wf_VLOAD wf_vloadopE wf_szE)

lemma wf_vload_splat:
  "wf_instr (instr_sc6 (VLOAD V128 (Some (SPLAT (mk_sz N))) ao)) \<Longrightarrow> N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64"
  by (auto elim!: wf_VLOAD wf_vloadopE wf_szE)

lemma wf_vload_lane_sz:
  "wf_instr (instr_sc6 (VLOAD_LANE V128 (mk_sz N) ao j)) \<Longrightarrow> N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64"
  by (auto elim!: wf_VLOAD_LANE wf_szE)

lemma wf_vstore_lane_sz:
  "wf_instr (instr_sc6 (VSTORE_LANE V128 (mk_sz N) ao j)) \<Longrightarrow> N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64"
  by (auto elim!: wf_VSTORE_LANE wf_szE)

lemma wf_vload_shape:
  assumes "wf_instr (instr_sc6 (VLOAD V128 (Some (SHAPEX_underscore (mk_sz M) N sx)) ao))"
  shows "(M = 8 \<or> M = 16 \<or> M = 32) \<and> N * (M * 2) = 128"
proof -
  have sz: "M = 8 \<or> M = 16 \<or> M = 32 \<or> M = 64"
    and h: "(of_nat (M * N) :: rat) = of_nat (vsize V128) / of_nat 2" and N1: "1 < N"
    using assms by (auto elim!: wf_VLOAD wf_vloadopE wf_szE)
  have "(of_nat (M * N * 2) :: rat) = of_nat 128" using h by (simp add: field_simps)
  then have "M * N * 2 = 128" by (simp only: of_nat_eq_iff)
  then show ?thesis using sz N1 by auto
qed

lemma lane_bound_rat:
  assumes "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64" "(of_nat j :: rat) < of_nat 128 / of_nat N"
  shows "j < 128 div N"
proof -
  have N0: "(0::rat) < of_nat N" using assms(1) by auto
  have "(of_nat (j * N) :: rat) < of_nat 128" using assms(2) N0 by (simp add: pos_less_divide_eq)
  then have "j * N < 128" by (simp only: of_nat_less_iff)
  moreover have "128 = (128 div N) * N" using assms(1) by auto
  ultimately show ?thesis by (metis mult_less_cancel2)
qed

lemma ro_call_indirect:
  assumes E: "all_typed C' es"
    and m: "length (context_TABLES C') = length (TABLES mi)" "context_TYPES C' = TYPES mi"
  shows "\<forall>i x y. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)] \<longrightarrow>
           un x < length (TABLES mi) \<and> un y < length (TYPES mi)"
proof (intro allI impI)
  fix i x y assume e: "es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)]"
  obtain ft where "Instr_ok C' (instr_sc0 (CALL_INDIRECT x y)) ft" using E e by fastforce
  then show "un x < length (TABLES mi) \<and> un y < length (TYPES mi)"
    using Type_Inversion.inv_call_indirect[OF _ HOL.refl] m by fastforce
qed

lemma ro_table_fill:
  assumes T: "Instrs_ok2 s C' es (mk_functype t1 t2)"
  shows "\<forall>i v n x. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_val v, i32c n,
                         admininstr_sc5 (admininstr_st5_TABLE_FILL x)] \<longrightarrow> (\<exists>vr. tr_val v = V_ref vr)"
proof (intro allI impI)
  fix i v n x
  assume e: "es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_val v, i32c n,
                   admininstr_sc5 (admininstr_st5_TABLE_FILL x)]"
  let ?vs = "[val_CONST I32 i, v, val_CONST I32 (mk_num__0 Inn_I32 n)]"
  have "Instrs_ok2 s C' (map admininstr_val ?vs @ [admininstr_instr (instr_sc5 (TABLE_FILL x))]) (mk_functype t1 t2)"
    using T e by simp
  then obtain tp1 tp2 where I: "Instr_ok C' (instr_sc5 (TABLE_FILL x)) (mk_functype (mk_list tp1) tp2)"
    and R: "length tp1 = length ?vs \<longrightarrow> Resulttype_sub (mk_list (map typeofval ?vs)) (mk_list tp1)"
    using vals_instr_typed by blast
  obtain lim rt where "mk_functype (mk_list [valtype_I32, valtype_reftype rt, valtype_I32]) (mk_list []) =
                       mk_functype (mk_list tp1) tp2"
    using Type_Inversion.inv_table_fill[OF I HOL.refl] by blast
  then have tp1: "tp1 = [valtype_I32, valtype_reftype rt, valtype_I32]" by simp
  have "Valtype_sub (typeofval v) (valtype_reftype rt)" using R tp1 by (simp add: Resulttype_sub.simps)
  then show "\<exists>vr. tr_val v = V_ref vr" by (rule Valtype_sub_ref)
qed

lemma ro_memory_fill:
  assumes T: "Instrs_ok2 s C' es (mk_functype t1 t2)" and W: "wfl es"
  shows "\<forall>i v n. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_val v, i32c n,
                       admininstr_sc7 admininstr_st7_MEMORY_FILL] \<longrightarrow>
           (\<exists>c. v = val_CONST I32 (mk_num__0 Inn_I32 c))"
proof (intro allI impI)
  fix i v n
  assume e: "es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_val v, i32c n,
                   admininstr_sc7 admininstr_st7_MEMORY_FILL]"
  let ?vs = "[val_CONST I32 i, v, val_CONST I32 (mk_num__0 Inn_I32 n)]"
  have "Instrs_ok2 s C' (map admininstr_val ?vs @ [admininstr_instr (instr_sc6 MEMORY_FILL)]) (mk_functype t1 t2)"
    using T e by simp
  then obtain tp1 tp2 where I: "Instr_ok C' (instr_sc6 MEMORY_FILL) (mk_functype (mk_list tp1) tp2)"
    and R: "length tp1 = length ?vs \<longrightarrow> Resulttype_sub (mk_list (map typeofval ?vs)) (mk_list tp1)"
    using vals_instr_typed by blast
  obtain mt where "mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []) =
                   mk_functype (mk_list tp1) tp2"
    using Type_Inversion.inv_memory_fill[OF I HOL.refl] by blast
  then have tp1: "tp1 = [valtype_I32, valtype_I32, valtype_I32]" by simp
  have "Valtype_sub (typeofval v) valtype_I32" using R tp1 by (simp add: Resulttype_sub.simps)
  then obtain c where v: "v = val_CONST I32 c" using Valtype_sub_I32 by blast
  have "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 c))" using W e v by simp
  then obtain u where "c = mk_num__0 Inn_I32 u" by (rule wf_const_i32)
  then show "\<exists>c. v = val_CONST I32 (mk_num__0 Inn_I32 c)" using v by blast
qed

lemma ro_load_pack:
  assumes E: "all_typed C' es"
  shows "\<forall>i t n sx ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
           admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn t) (Some (mk_loadop__0 t (mk_loadop_Inn (mk_sz n) sx))) ao)] \<longrightarrow>
           ext_width_ok (numtype_Inn t) n"
proof (intro allI impI)
  fix i t n sx ao
  assume "es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
           admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn t) (Some (mk_loadop__0 t (mk_loadop_Inn (mk_sz n) sx))) ao)]"
  then have "wf_instr (instr_sc5 (LOAD (numtype_Inn t) (Some (mk_loadop__0 t (mk_loadop_Inn (mk_sz n) sx))) ao))"
    using all_typed_wf[OF E] by simp
  then show "ext_width_ok (numtype_Inn t) n" by (rule wf_load_pack_ext)
qed

lemma ro_vload_shape:
  assumes E: "all_typed C' es"
  shows "\<forall>i M N sx ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
           admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore (mk_sz M) N sx)) ao)] \<longrightarrow>
           (M = 8 \<or> M = 16 \<or> M = 32) \<and> N * (M * 2) = 128"
proof (intro allI impI)
  fix i M N sx ao
  assume "es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
           admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore (mk_sz M) N sx)) ao)]"
  then have "wf_instr (instr_sc6 (VLOAD V128 (Some (SHAPEX_underscore (mk_sz M) N sx)) ao))"
    using all_typed_wf[OF E] by simp
  then show "(M = 8 \<or> M = 16 \<or> M = 32) \<and> N * (M * 2) = 128" by (rule wf_vload_shape)
qed

lemma ro_vload_zero:
  assumes E: "all_typed C' es"
  shows "\<forall>i N ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
           admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop__ZERO (mk_sz N))) ao)] \<longrightarrow> N = 32 \<or> N = 64"
proof (intro allI impI)
  fix i N ao
  assume "es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
           admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop__ZERO (mk_sz N))) ao)]"
  then have "wf_instr (instr_sc6 (VLOAD V128 (Some (vloadop__ZERO (mk_sz N))) ao))"
    using all_typed_wf[OF E] by simp
  then show "N = 32 \<or> N = 64" by (rule wf_vload_zero)
qed

lemma ro_vload_splat:
  assumes E: "all_typed C' es"
  shows "\<forall>i N ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
           admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT (mk_sz N))) ao)] \<longrightarrow>
           N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64"
proof (intro allI impI)
  fix i N ao
  assume "es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
           admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT (mk_sz N))) ao)]"
  then have "wf_instr (instr_sc6 (VLOAD V128 (Some (SPLAT (mk_sz N))) ao))"
    using all_typed_wf[OF E] by simp
  then show "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64" by (rule wf_vload_splat)
qed

lemma ro_vload_lane:
  assumes E: "all_typed C' es"
  shows "\<forall>i c N ao j. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c,
           admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz N) ao j)] \<longrightarrow>
           un j < 128 div N \<and> (N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64)"
proof (intro allI impI)
  fix i c N ao j
  assume e: "es = [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c,
           admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz N) ao j)]"
  obtain ft where I: "Instr_ok C' (instr_sc6 (VLOAD_LANE V128 (mk_sz N) ao j)) ft" using E e by fastforce
  have NN: "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64" by (rule wf_vload_lane_sz[OF Instr_ok_wf(2)[OF I]])
  have "(of_nat (proj_uN_0 j) :: rat) < of_nat 128 / of_nat N"
    using Type_Inversion.inv_vload_lane[OF I HOL.refl] by blast
  then have "un j < 128 div N" using lane_bound_rat[OF NN] by simp
  then show "un j < 128 div N \<and> (N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64)" using NN by blast
qed

lemma wo_local_set:
  assumes E: "all_typed C' es" and l: "length (context_LOCALS C') = length (LOCALS f)"
  shows "\<forall>v x. es = [admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_SET x)] \<longrightarrow> un x < length (LOCALS f)"
proof (intro allI impI)
  fix v x assume e: "es = [admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_SET x)]"
  obtain ft where "Instr_ok C' (instr_sc4 (LOCAL_SET x)) ft" using E e by fastforce
  then show "un x < length (LOCALS f)" using Type_Inversion.inv_local_set[OF _ HOL.refl] l by fastforce
qed

lemma wo_memory_grow:
  assumes E: "all_typed C' es" and l: "length (context_MEMS C') = length (MEMS mi)"
  shows "\<forall>i. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc6 admininstr_st6_MEMORY_GROW] \<longrightarrow>
           0 < length (MEMS mi)"
proof (intro allI impI)
  fix i assume e: "es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc6 admininstr_st6_MEMORY_GROW]"
  obtain ft where "Instr_ok C' (instr_sc6 MEMORY_GROW) ft" using E e by fastforce
  then show "0 < length (MEMS mi)" using Type_Inversion.inv_memory_grow[OF _ HOL.refl] l by fastforce
qed

lemma wo_store_pack:
  assumes E: "all_typed C' es"
  shows "\<forall>i t c n ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) c),
           admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)] \<longrightarrow>
           ext_width_ok (numtype_Inn t) n"
proof (intro allI impI)
  fix i t c n ao
  assume "es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) c),
           admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)]"
  then have "wf_instr (instr_sc5 (STORE (numtype_Inn t) (Some (mk_sz n)) ao))"
    using all_typed_wf[OF E] by simp
  then show "ext_width_ok (numtype_Inn t) n" by (rule wf_store_pack_ext)
qed

lemma wo_vstore_lane:
  assumes E: "all_typed C' es"
  shows "\<forall>i c N ao j. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c,
           admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)] \<longrightarrow>
           un j < 128 div N \<and> (N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64)"
proof (intro allI impI)
  fix i c N ao j
  assume e: "es = [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c,
           admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)]"
  obtain ft where I: "Instr_ok C' (instr_sc6 (VSTORE_LANE V128 (mk_sz N) ao j)) ft" using E e by fastforce
  have NN: "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64" by (rule wf_vstore_lane_sz[OF Instr_ok_wf(2)[OF I]])
  have "(of_nat (proj_uN_0 j) :: rat) < of_nat 128 / of_nat N"
    using Type_Inversion.inv_vstore_lane[OF I HOL.refl] by blast
  then have "un j < 128 div N" using lane_bound_rat[OF NN] by simp
  then show "un j < 128 div N \<and> (N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64)" using NN by blast
qed

section \<open>The assumptions of [sim_inv]\<close>

lemma Inv_wf: "Inv_typed z es ls r \<Longrightarrow> wf_config (mk_config z es)"
  by (cases z) auto

lemma Inv_state: "Inv_typed (mk_state s f) es ls r \<Longrightarrow> state_inv s f \<and> mem_pages s"
  by (auto intro: Store_ok_state_inv Store_ok_mem_pages)

lemma Inv_redex:
  assumes "Inv_typed (mk_state s f) es ls r"
  shows "redex_ok f es \<and> write_ok f es \<and> instrs_typed es"
proof -
  from assms obtain C C' t1 t2 where w: "wf_config (mk_config (mk_state s f) es)"
    and M: "Moduleinst_ok s (frame_MODULE f) C"
    and L: "list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C') (LOCALS f)" and m: "inst_match C C'"
    and T: "Instrs_ok2 s C' es (mk_functype t1 t2)"
    by auto
  have E: "all_typed C' es" using Instrs_ok2_elem_plain[OF T] by blast
  have W: "wfl es" using w by (simp add: wf_config_simps)
  have tl: "length (context_TABLES C') = length (TABLES (frame_MODULE f))"
    "context_TYPES C' = TYPES (frame_MODULE f)"
    "length (context_MEMS C') = length (MEMS (frame_MODULE f))"
    using m Moduleinst_ok_E(1-3)[OF M] by (simp_all add: inst_match_def)
  have ll: "length (context_LOCALS C') = length (LOCALS f)" using L by (rule list_all2_lengthD)
  have "redex_ok f es"
    unfolding redex_ok_def
    using ro_call_indirect[OF E tl(1,2)] ro_table_fill[OF T] ro_memory_fill[OF T W] ro_load_pack[OF E]
      ro_vload_shape[OF E] ro_vload_zero[OF E] ro_vload_lane[OF E] ro_vload_splat[OF E]
    by blast
  moreover have "write_ok f es"
    unfolding write_ok_def
    using wo_local_set[OF E ll] wo_memory_grow[OF E tl(3)] wo_store_pack[OF E] wo_vstore_lane[OF E]
    by blast
  moreover have "instrs_typed es" unfolding instrs_typed_def using E by blast
  ultimately show ?thesis by blast
qed

(* A typed configuration satisfies the invariant at the top level. *)
lemma Config_ok_Inv:
  assumes "Config_ok (mk_config z es) ts"
  shows "Inv_typed z es [] None"
proof -
  obtain s f C where z: "z = mk_state s f" and St: "State_ok (mk_state s f) C"
    and E: "Expr_ok2 s C es ts" and w: "wf_config (mk_config (mk_state s f) es)"
    using assms by (cases rule: Config_ok.cases) auto
  have S: "Store_ok s" and F: "Frame_ok s f C" using St by (auto elim: State_ok.cases)
  obtain C0 where M: "Moduleinst_ok s (frame_MODULE f) C0" and m: "inst_match C0 C"
    and L: "list_all2 (\<lambda>t v. Val_ok s v t) (context_LOCALS C) (LOCALS f)"
    and lab: "LABELS C = []" and ret: "context_RETURN C = None"
    using Frame_ok_E[OF F] by blast
  have T: "Instrs_ok2 s C es (mk_functype (mk_list []) ts)" using inv_expr(1)[OF E] .
  have ls': "[] = map rlen (LABELS C)" and r': "None = map_option rlen (context_RETURN C)"
    using lab ret by simp_all
  show ?thesis unfolding z by (rule Inv_typedI[OF w S M L m T ls' r'])
qed

sublocale sim_all \<subseteq> typed: sim_inv Inv_typed
  by unfold_locales (erule Inv_wf Inv_state Inv_redex Inv_br Inv_ret Inv_label Inv_frame Inv_instrs)+

section \<open>The simulation for typed configurations\<close>

context sim_all
begin

(* Every step of a typed SpecTec configuration is simulated by WasmCert-Isabelle,
   is a named disagreement (in an evaluation context), or is simulated after
   further SpecTec steps (label exits). *)
theorem Step_sim_typed:
  assumes "Step (mk_config z es) (mk_config z' es')" "Config_ok (mk_config z es) ts"
  shows "sim (mk_config z es) (mk_config z' es') \<or> Exc z es z' es' \<or>
         (z' = z \<and> (\<exists>es''. CSteps z es' es'' \<and> wfl es'' \<and> sim (mk_config z es) (mk_config z es'')))"
  using typed.Step_sim[OF assms(1) Config_ok_Inv[OF assms(2)]]
  by (auto simp: Res_def br_pending_def ret_pending_def)

end

(* Same-state SpecTec steps are SpecTec [Steps]. *)
lemma CSteps_Steps:
  assumes "CSteps z a b" "wf_config (mk_config z b)"
  shows "Steps (mk_config z a) (mk_config z b)"
  using assms
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by (rule Steps.intros(1))
next
  case (step a a')
  have st: "Step (mk_config z a) (mk_config z a')" and wa: "wf_config (mk_config z a)"
    and wa': "wf_config (mk_config z a')"
    using step.hyps(1) by (simp_all add: cstep_def)
  show ?case by (rule Steps.intros(2)[OF st step.IH[OF step.prems] wa step.prems wa'])
qed

context sim_all
begin

(* The Rocq bridge's form of the main theorem (reduction.v, [Step_sim_eventually]):
   a step of a typed configuration that is none of the named disagreements, in
   any evaluation context, is simulated by WasmCert-Isabelle, directly or after
   further SpecTec steps. *)
theorem Step_sim_eventually:
  assumes st: "Step (mk_config z es) (mk_config z' es')" and ok: "Config_ok (mk_config z es) ts"
    and nd: "\<not> Exc z es z' es'"
  shows "sim (mk_config z es) (mk_config z' es') \<or>
         (\<exists>c''. Steps (mk_config z' es') c'' \<and> sim (mk_config z es) c'')"
proof -
  have wz: "wf_state z" using ok by (auto elim!: Config_ok.cases simp: wf_config_simps)
  from Step_sim_typed[OF st ok] nd
  consider "sim (mk_config z es) (mk_config z' es')"
    | es'' where "z' = z" "CSteps z es' es''" "wfl es''" "sim (mk_config z es) (mk_config z es'')"
    by blast
  then show ?thesis
  proof cases
    case 1 then show ?thesis by blast
  next
    case (2 es'')
    have "wf_config (mk_config z es'')" using wz 2(3) by (simp add: wf_config_simps)
    then have "Steps (mk_config z es') (mk_config z es'')" using CSteps_Steps 2(2) by blast
    then show ?thesis using 2(1,4) by blast
  qed
qed

end

end
