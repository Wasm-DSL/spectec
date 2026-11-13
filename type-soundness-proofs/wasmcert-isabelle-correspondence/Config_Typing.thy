(* Typing preservation for configurations: if SpecTec types a configuration
   ([Config_ok]), WasmCert-Isabelle types its translation ([config_typing]): the
   translated store is valid ([store_typing]) and the translated thread is typed
   ([thread_typing]).  Isabelle counterpart of ../wasmcert-rocq/config_typing.v.

   WasmCert-Isabelle's [inst_typing], like SpecTec's [Moduleinst_ok], lets the
   context assign supertypes (larger limits) to the tables and memories of an
   instance ([tabi_agree], [memi_agree] use [tab_subtyping], [mem_subtyping]), so
   unlike in the Rocq development no context equivalence is needed.

   The [ext_ok] side condition of [Typing] is lifted to administrative
   instructions ([admin_ext_ok]) and to the function bodies in the store
   ([store_ext_ok]). *)
theory Config_Typing
  imports Typing
begin

section \<open>Side conditions\<close>

primrec admin_ext_ok :: "admininstr \<Rightarrow> bool" and admin_ext_ok7 :: "admininstr_st7 \<Rightarrow> bool"
    and admin_ext_ok8 :: "admininstr_st8 \<Rightarrow> bool" where
  "admin_ext_ok (admininstr_sc0 x) = ext_ok (instr_of_a0 x)"
| "admin_ext_ok (admininstr_sc1 x) = ext_ok (instr_of_a1 x)"
| "admin_ext_ok (admininstr_sc2 x) = ext_ok (instr_of_a2 x)"
| "admin_ext_ok (admininstr_sc3 x) = ext_ok (instr_of_a3 x)"
| "admin_ext_ok (admininstr_sc4 x) = ext_ok (instr_of_a4 x)"
| "admin_ext_ok (admininstr_sc5 x) = ext_ok (instr_of_a5 x)"
| "admin_ext_ok (admininstr_sc6 x) = ext_ok (instr_of_a6 x)"
| "admin_ext_ok (admininstr_sc7 x) = admin_ext_ok7 x"
| "admin_ext_ok (admininstr_sc8 x) = admin_ext_ok8 x"
| "admin_ext_ok7 (LABEL_underscore n ins es) = (list_all ext_ok ins \<and> list_all admin_ext_ok es)"
| "admin_ext_ok7 admininstr_st7_TRAP = True"
| "admin_ext_ok7 (CALL_ADDR a) = True"
| "admin_ext_ok7 (admininstr_st7_REF_HOST_ADDR a) = True"
| "admin_ext_ok7 (admininstr_st7_REF_FUNC_ADDR a) = True"
| "admin_ext_ok7 (admininstr_st7_DATA_DROP x) = True"
| "admin_ext_ok7 (admininstr_st7_MEMORY_INIT x) = True"
| "admin_ext_ok7 admininstr_st7_MEMORY_COPY = True"
| "admin_ext_ok7 admininstr_st7_MEMORY_FILL = True"
| "admin_ext_ok8 (FRAME_underscore n fr es) = list_all admin_ext_ok es"

lemma admin_ext_ok_instr[simp]: "admin_ext_ok (admininstr_instr i) = ext_ok i"
  by (cases i rule: instr.exhaust) (rename_tac x, case_tac x; simp)+

definition func_ext_ok :: "func \<Rightarrow> bool" where
  "func_ext_ok fn = (case fn of func_FUNC _ _ body \<Rightarrow> list_all ext_ok body)"

definition store_ext_ok :: "store \<Rightarrow> bool" where
  "store_ext_ok st = list_all (\<lambda>fi. func_ext_ok (CODE fi)) (store_FUNCS st)"

section \<open>Translation facts\<close>

lemma tr_admins_instrs[simp]: "tr_admins (map admininstr_instr ins) = map Basic (tr_instrs ins)"
  by (simp add: tr_admins_def tr_instrs_def)

lemma tr_admins_append[simp]: "tr_admins (es1 @ es2) = tr_admins es1 @ tr_admins es2"
  by (simp add: tr_admins_def)

lemma tr_admins_single[simp]: "tr_admins [a] = [tr_admin a]"
  by (simp add: tr_admins_def)

lemma tr_admins_Nil[simp]: "tr_admins [] = []"
  by (simp add: tr_admins_def)

lemma tr_store_sel[simp]:
  "s.funcs (tr_store st) = map tr_funcinst (store_FUNCS st)"
  "s.tabs (tr_store st) = map tr_tableinst (store_TABLES st)"
  "s.mems (tr_store st) = map tr_meminst (store_MEMS st)"
  "s.globs (tr_store st) = map tr_globalinst (store_GLOBALS st)"
  "s.elems (tr_store st) = map tr_eleminst (store_ELEMS st)"
  "s.datas (tr_store st) = map tr_datainst (store_DATAS st)"
  by (simp_all add: tr_store_def)

lemma cl_type_tr_funcinst[simp]: "cl_type (tr_funcinst fi) = tr_functype (funcinst_TYPE fi)"
  by (simp add: tr_funcinst_def cl_type_def split: func.splits)

lemma fst_tr_tableinst[simp]: "fst (tr_tableinst ti) = tr_tabletype (tableinst_TYPE ti)"
  by (simp add: tr_tableinst_def)

lemma fst_tr_meminst[simp]: "fst (tr_meminst mi) = tr_memtype (meminst_TYPE mi)"
  by (simp add: tr_meminst_def)

lemma mem_length_tr_meminst[simp]: "mem_length (tr_meminst mi) = length (BYTES mi)"
  by (simp add: tr_meminst_def mem_length_def mem_rep_length.abs_eq)

(* A module context: no locals, labels or return type. *)
lemma tr_context_locals:
  "context_LOCALS C = [] \<Longrightarrow> context_RETURN C = None \<Longrightarrow> LABELS C = [] \<Longrightarrow>
   tr_context (append_res_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
      context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = ts,
      LABELS = ls, context_RETURN = r\<rparr> C)
   = (tr_context C)\<lparr>local := map tr_valtype ts, label := map tr_resulttype ls,
                     return := map_option tr_resulttype r\<rparr>"
  by (cases r) (simp_all add: tr_context_def append_res_context_def)

lemma tr_context_return[simp]:
  "tr_context (append_res_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
      context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
      LABELS = [], context_RETURN = Some r\<rparr> C)
   = (tr_context C)\<lparr>return := Some (tr_resulttype r)\<rparr>"
  by (simp add: tr_context_def append_res_context_def)

section \<open>Limits and external addresses\<close>

lemma limits_compat_refl: "limits_compat l l"
  by (cases "l_max l") (auto simp: limits_compat_def)

lemma limits_compat_trans:
  "limits_compat l1 l2 \<Longrightarrow> limits_compat l2 l3 \<Longrightarrow> limits_compat l1 l3"
  by (auto simp: limits_compat_def pred_option_def split: option.splits)

lemma Limits_sub_tr: "Limits_sub l1 l2 \<Longrightarrow> limits_compat (tr_limits l1) (tr_limits l2)"
  by (erule Limits_sub.cases) (auto simp: limits_compat_def split: option.splits)

(* What an external address of a given type tells about the translated store. *)
fun extaddr_tr :: "store \<Rightarrow> externaddr \<Rightarrow> externtype \<Rightarrow> bool" where
  "extaddr_tr st (externaddr_FUNC a) (FUNC ft) =
     (a < length (store_FUNCS st) \<and> funcinst_TYPE (store_FUNCS st ! a) = ft)"
| "extaddr_tr st (externaddr_GLOBAL a) (GLOBAL gt) =
     (a < length (store_GLOBALS st) \<and> globalinst_TYPE (store_GLOBALS st ! a) = gt)"
| "extaddr_tr st (externaddr_TABLE a) (TABLE tt) =
     (a < length (store_TABLES st) \<and>
      tab_subtyping (tr_tabletype (tableinst_TYPE (store_TABLES st ! a))) (tr_tabletype tt))"
| "extaddr_tr st (externaddr_MEM a) (MEM mt) =
     (a < length (store_MEMS st) \<and>
      mem_subtyping (tr_memtype (meminst_TYPE (store_MEMS st ! a))) (tr_memtype mt))"
| "extaddr_tr st _ _ = False"

lemma tab_subtyping_tr_refl: "tab_subtyping (tr_tabletype tt) (tr_tabletype tt)"
  by (cases tt) (simp add: tab_subtyping_def limits_compat_refl)

lemma tab_subtyping_lim:
  "tab_subtyping A (T_tab l1 r) \<Longrightarrow> limits_compat l1 l2 \<Longrightarrow> tab_subtyping A (T_tab l2 r)"
  by (cases A) (simp add: tab_subtyping_def, metis limits_compat_trans)

lemma mem_subtyping_lim:
  "mem_subtyping A l1 \<Longrightarrow> limits_compat l1 l2 \<Longrightarrow> mem_subtyping A l2"
  by (simp add: mem_subtyping_def) (metis limits_compat_trans)

lemma extaddr_tr_sub: "Externtype_sub xt' xt \<Longrightarrow> extaddr_tr st xa xt' \<Longrightarrow> extaddr_tr st xa xt"
  apply (erule Externtype_sub.cases)
     apply (cases xa; auto elim: Functype_sub.cases)
    apply (cases xa; auto elim: Globaltype_sub.cases)
   apply (cases xa; auto elim!: Tabletype_sub.cases dest!: Limits_sub_tr intro: tab_subtyping_lim)
  apply (cases xa; auto elim!: Memtype_sub.cases dest!: Limits_sub_tr intro: mem_subtyping_lim)
  done

lemma Externaddr_ok_tr: "Externaddr_ok st xa xt \<Longrightarrow> extaddr_tr st xa xt"
  by (induction rule: Externaddr_ok.induct)
     (auto simp: tab_subtyping_tr_refl mem_subtyping_def limits_compat_refl intro: extaddr_tr_sub)

section \<open>Values and references\<close>

termination val_ref by lexicographic_order

lemma Ref_ok_tr: "Ref_ok st r rt \<Longrightarrow> ref_typing (tr_store st) (tr_ref r) (tr_reftype rt)"
  by (erule Ref_ok.cases)
     (auto dest!: Externaddr_ok_tr intro: ref_typing.intros simp: tr_host_def)

lemma Ref_ok_typeof: "Ref_ok st r rt \<Longrightarrow> typeof_ref (tr_ref r) = tr_reftype rt"
  by (erule Ref_ok.cases) (auto simp: typeof_ref_def)

inductive_cases wf_valE: "wf_val v"

lemma Val_ok_tr: "Val_ok st v t \<Longrightarrow> v_typing (tr_store st) (tr_val v) (tr_valtype t)"
  apply (erule Val_ok.cases)
    apply (auto elim!: wf_valE intro: v_typing.intros simp: wf_num_typeof)
    apply (metis v_typing.intros(1) wf_num_typeof)
   apply (simp add: tr_vec_def typeof_vec_def v_typing.intros(2)[of _ "ConstVec128 _", simplified typeof_vec_def, simplified])
  apply (rename_tac r rt, case_tac r; auto dest!: Ref_ok_tr intro!: v_typing.intros(3))
  done

lemma Ref_ok_list_tr:
  "\<forall>r\<in>set rs. Ref_ok st r rt \<Longrightarrow> vr \<in> set rs \<Longrightarrow> ref_typing (tr_store st) (tr_ref vr) (tr_reftype rt)"
  by (blast dest: Ref_ok_tr)

lemma Ref_ok_all_tr:
  "\<forall>r\<in>set rs. Ref_ok st r rt \<Longrightarrow> \<forall>r\<in>set rs. ref_typing (tr_store st) (tr_ref r) (tr_reftype rt)"
  by (blast dest: Ref_ok_tr)

lemma Val_ok_typeof: "Val_ok st v t \<Longrightarrow> typeof (tr_val v) = tr_valtype t"
  apply (erule Val_ok.cases)
    apply (auto elim!: wf_valE simp: typeof_def wf_num_typeof tr_vec_def typeof_vec_def)
  apply (rename_tac r rt, case_tac r; auto dest: Ref_ok_typeof simp: typeof_def typeof_ref_def)
  done

section \<open>Store invariants\<close>

lemma Store_ok_globals:
  "Store_ok st \<Longrightarrow> a < length (store_GLOBALS st) \<Longrightarrow> \<exists>gt. Globalinst_ok st (store_GLOBALS st ! a) gt"
  by (erule Store_ok.cases) (auto simp: list_all2_conv_all_nth)

lemma Store_ok_global_typeof:
  assumes "Store_ok st" "a < length (store_GLOBALS st)"
  shows "typeof (tr_val (VALUE (store_GLOBALS st ! a))) = tg_t (tr_globaltype (globalinst_TYPE (store_GLOBALS st ! a)))"
  using Store_ok_globals[OF assms]
  by (auto elim!: Globalinst_ok.cases dest!: Val_ok_typeof)

section \<open>Module instances and frames\<close>

(* One lemma per component of an instance: SpecTec's address typing gives
   WasmCert's agreement predicate for the translated store. *)
lemma list_all2_funci:
  "list_all2 (\<lambda>a ft. Externaddr_ok st (externaddr_FUNC a) (FUNC ft)) as fts \<Longrightarrow>
   list_all2 (funci_agree (map tr_funcinst (store_FUNCS st))) as (map tr_functype fts)"
  by (auto simp: list_all2_conv_all_nth funci_agree_def dest!: Externaddr_ok_tr)

lemma list_all2_globi:
  assumes "Store_ok st" "list_all2 (\<lambda>a gt. Externaddr_ok st (externaddr_GLOBAL a) (GLOBAL gt)) as gts"
  shows "list_all2 (globi_agree (map tr_globalinst (store_GLOBALS st))) as (map tr_globaltype gts)"
  using assms(2)
proof (induction rule: list_all2_induct)
  case (Cons a as gt gts)
  then have "a < length (store_GLOBALS st)" "globalinst_TYPE (store_GLOBALS st ! a) = gt"
    by (auto dest!: Externaddr_ok_tr)
  with Store_ok_global_typeof[OF assms(1)] Cons show ?case
    by (cases gt) (auto simp: globi_agree_def glob_typing_def tr_globalinst_def)
qed simp

lemma list_all2_tabi:
  "list_all2 (\<lambda>a tt. Externaddr_ok st (externaddr_TABLE a) (TABLE tt)) as tts \<Longrightarrow>
   list_all2 (tabi_agree (map tr_tableinst (store_TABLES st))) as (map tr_tabletype tts)"
  by (auto simp: list_all2_conv_all_nth tabi_agree_def dest!: Externaddr_ok_tr)

lemma list_all2_memi:
  "list_all2 (\<lambda>a mt. Externaddr_ok st (externaddr_MEM a) (MEM mt)) as mts \<Longrightarrow>
   list_all2 (memi_agree (map tr_meminst (store_MEMS st))) as (map tr_memtype mts)"
  by (auto simp: list_all2_conv_all_nth memi_agree_def dest!: Externaddr_ok_tr)

lemma list_all2_elemi:
  assumes "list_all (\<lambda>a. a < length (store_ELEMS st)) as"
          "list_all2 (\<lambda>a et. Eleminst_ok st (store_ELEMS st ! a) et) as ets"
  shows "list_all2 (elemi_agree (tr_store st) (map tr_eleminst (store_ELEMS st))) as (map tr_reftype ets)"
  using assms(2,1)
  by (induction rule: list_all2_induct)
     (auto simp: elemi_agree_def elem_typing_def tr_eleminst_def list_all_iff
           elim!: Eleminst_ok.cases dest!: Ref_ok_all_tr)

lemma list_all2_datai:
  "list_all (\<lambda>a. a < length (store_DATAS st)) as \<Longrightarrow> length as = length dts \<Longrightarrow>
   list_all2 (datai_agree (map tr_datainst (store_DATAS st))) as (map (\<lambda>_. ()) dts)"
  by (auto simp: list_all2_conv_all_nth list_all_iff datai_agree_def data_typing_def)

lemma inst_typingI:
  "\<lbrakk>list_all2 (funci_agree (s.funcs sr)) fs tfs; list_all2 (globi_agree (s.globs sr)) gs tgs;
    list_all2 (tabi_agree (s.tabs sr)) tbs tabs_t; list_all2 (memi_agree (s.mems sr)) ms mems_t;
    list_all2 (elemi_agree sr (s.elems sr)) es elems_t; list_all2 (datai_agree (s.datas sr)) ds datas_t;
    rs = [0..<length fs]\<rbrakk> \<Longrightarrow>
   inst_typing sr \<lparr>inst.types = ts, inst.funcs = fs, inst.tabs = tbs, inst.mems = ms, inst.globs = gs,
                  inst.elems = es, inst.datas = ds\<rparr>
     \<lparr>types_t = ts, func_t = tfs, global = tgs, elem = elems_t, data = datas_t, table = tabs_t,
      memory = mems_t, local = [], label = [], return = None, refs = rs\<rparr>"
  by (simp add: inst_typing.intros)

lemma Moduleinst_ok_tr:
  assumes "Store_ok st" "Moduleinst_ok st mi C"
  shows "inst_typing (tr_store st) (tr_moduleinst mi) (tr_context C)"
  using assms(2)
proof (cases rule: Moduleinst_ok.cases)
  case mk_Moduleinst_ok
  then show ?thesis
    using assms(1)
    by (simp add: tr_moduleinst_def tr_context_def)
       (rule inst_typingI; auto intro: list_all2_funci list_all2_globi list_all2_tabi list_all2_memi
                                       list_all2_elemi list_all2_datai)
qed

lemma Moduleinst_ok_ctx:
  "Moduleinst_ok st mi C \<Longrightarrow> context_LOCALS C = [] \<and> context_RETURN C = None \<and> LABELS C = []"
  by (erule Moduleinst_ok.cases) simp

lemma list_all2_Val_ok_tr:
  "list_all2 (\<lambda>t v. Val_ok st v t) ts vs \<Longrightarrow>
   list_all2 (v_typing (tr_store st)) (map tr_val vs) (map tr_valtype ts)"
  by (auto simp: list_all2_conv_all_nth dest: Val_ok_tr)

lemma frame_typingI:
  "list_all2 (v_typing sr) vs tvs \<Longrightarrow> inst_typing sr i C0 \<Longrightarrow> C = C0\<lparr>local := tvs\<rparr> \<Longrightarrow>
   frame_typing sr \<lparr>f_locs = vs, f_inst = i\<rparr> C"
  using frame_typing.intros[of sr "\<lparr>f_locs = vs, f_inst = i\<rparr>"] by simp

lemma tr_context_frame:
  "context_LOCALS C0 = [] \<Longrightarrow>
   tr_context (append_res_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
      context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = ts,
      LABELS = [], context_RETURN = None\<rparr> C0)
   = (tr_context C0)\<lparr>local := map tr_valtype ts\<rparr>"
  by (simp add: tr_context_def append_res_context_def)

lemma Frame_ok_tr:
  assumes "Store_ok st" "Frame_ok st fr C"
  shows "frame_typing (tr_store st) (tr_frame fr) (tr_context C)"
  using assms(2)
proof (cases rule: Frame_ok.cases)
  case mk_Frame_ok
  then show ?thesis
    apply (clarsimp simp: tr_frame_def)
    apply (rule frame_typingI)
      apply (erule list_all2_Val_ok_tr)
     apply (erule Moduleinst_ok_tr[OF assms(1)])
    apply (simp add: tr_context_frame Moduleinst_ok_ctx)
    done
qed

lemma Frame_ok_return: "Frame_ok st fr C \<Longrightarrow> context_RETURN C = None"
  by (erule Frame_ok.cases) (auto dest: Moduleinst_ok_ctx simp: append_res_context_def)

section \<open>Function instances and the store\<close>

lemma n_zeros_not_bot: "list_all (\<lambda>t. t \<noteq> BOT) ts \<Longrightarrow> n_zeros (map tr_valtype ts) \<noteq> None"
proof (induction ts)
  case (Cons t ts)
  then show ?case
    by (cases t) (auto simp: n_zeros_def bitzero_def split: option.splits)
qed (simp add: n_zeros_def)

(* The body context of a function: locals, one label and the return type over a
   module context. *)
lemma tr_context_func:
  "context_LOCALS C0 = [] \<Longrightarrow>
   tr_context (append_res_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
      context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = ls,
      LABELS = [r], context_RETURN = Some r\<rparr> C0)
   = (tr_context C0)\<lparr>local := map tr_valtype ls, label := [tr_resulttype r] @ label (tr_context C0),
                      return := Some (tr_resulttype r)\<rparr>"
  by (simp add: tr_context_def append_res_context_def)

lemma cl_typingI:
  "inst_typing sr i C0 \<Longrightarrow>
   C0\<lparr>local := t1s @ ts, label := [t2s] @ label C0, return := Some t2s\<rparr> \<turnstile> es : ([] _> t2s) \<Longrightarrow>
   n_zeros ts \<noteq> None \<Longrightarrow> cl_typing sr (Func_native i (t1s _> t2s) ts es) (t1s _> t2s)"
  by (rule cl_typing.intros(1)) auto

lemma map_tr_local[simp]: "map tr_local (map LOCAL ts) = map tr_valtype ts"
  by (induction ts) simp_all

lemma list_all2_in_set1: "list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y. P x y"
  by (induction rule: list_all2_induct) auto

inductive_cases Func_okE: "Func_ok C fn ft"
inductive_cases Expr_okE: "Expr_ok C e rt"

lemma list_all2_ball: "list_all2 P xs ys \<Longrightarrow> \<forall>x\<in>set xs. \<exists>y. P x y"
  by (induction rule: list_all2_induct) auto

(* Every instance in a valid store is valid at some type. *)
lemma Store_ok_all:
  assumes "Store_ok st"
  shows "(\<forall>fi\<in>set (store_FUNCS st). \<exists>ft. Funcinst_ok st fi ft) \<and>
         (\<forall>ti\<in>set (store_TABLES st). \<exists>tt. Tableinst_ok st ti tt) \<and>
         (\<forall>mi\<in>set (store_MEMS st). \<exists>mt. Meminst_ok st mi mt) \<and>
         (\<forall>gi\<in>set (store_GLOBALS st). \<exists>gt. Globalinst_ok st gi gt) \<and>
         (\<forall>ei\<in>set (store_ELEMS st). \<exists>et. Eleminst_ok st ei et)"
  using assms
  by (cases rule: Store_ok.cases) (clarsimp, intro conjI; rule list_all2_ball; assumption)

lemma Store_ok_elems:
  assumes "Store_ok st"
  shows "fi \<in> set (store_FUNCS st) \<Longrightarrow> \<exists>ft. Funcinst_ok st fi ft"
    and "ti \<in> set (store_TABLES st) \<Longrightarrow> \<exists>tt. Tableinst_ok st ti tt"
    and "mi \<in> set (store_MEMS st) \<Longrightarrow> \<exists>mt. Meminst_ok st mi mt"
    and "gi \<in> set (store_GLOBALS st) \<Longrightarrow> \<exists>gt. Globalinst_ok st gi gt"
    and "ei \<in> set (store_ELEMS st) \<Longrightarrow> \<exists>et. Eleminst_ok st ei et"
  using Store_ok_all[OF assms] by auto

lemma Tableinst_ok_tr: "Tableinst_ok st ti tt \<Longrightarrow> tab_agree (tr_store st) (tr_tableinst ti)"
  by (auto elim!: Tableinst_ok.cases Tabletype_ok.cases Limits_ok.cases
           simp: tab_agree_def tr_tableinst_def tab_max_def list_all_iff option.map_comp
                 option.map_id option.pred_set
           dest!: Ref_ok_all_tr)

lemma Meminst_ok_tr: "Meminst_ok st mi mt \<Longrightarrow> mem_agree (tr_meminst mi)"
  by (auto elim!: Meminst_ok.cases Memtype_ok.cases Limits_ok.cases
           simp: mem_size_def mem_max_def Ki64_def Ki_def option.map_comp option.map_id
                 option.pred_set)

lemma Globalinst_ok_tr: "Globalinst_ok st gi gt \<Longrightarrow> glob_agree (tr_store st) (tr_globalinst gi)"
  by (auto elim!: Globalinst_ok.cases simp: glob_agree_def tr_globalinst_def dest!: Val_ok_tr)

lemma Eleminst_ok_tr: "Eleminst_ok st ei et \<Longrightarrow> elem_agree (tr_store st) (tr_eleminst ei)"
  by (auto elim!: Eleminst_ok.cases simp: elem_agree_def tr_eleminst_def list_all_iff dest!: Ref_ok_all_tr)

lemma ctx_return_None: "return C = None \<Longrightarrow> C\<lparr>return := None\<rparr> = C"
  by (cases C) simp

section \<open>Administrative instructions\<close>

lemma e_typing_basic1: "\<C> \<turnstile> [b] : tf \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> [Basic b] : tf"
  using e_typing_thread_typing.intros(1)[where b_es = "[b]"] by simp

lemma e_typing_empty: "\<S>\<bullet>\<C> \<turnstile> [] : ([] _> [])"
  using e_typing_thread_typing.intros(1)[OF b_e_typing.empty] by simp

lemma list_all_admin_ext_ok_instrs[simp]:
  "list_all admin_ext_ok (map admininstr_instr ins) = list_all ext_ok ins"
  by (induction ins) simp_all

context vec_binop_ok
begin

lemma Funcinst_ok_tr:
  assumes "Store_ok st" "Funcinst_ok st fi ft" "func_ext_ok (CODE fi)"
  shows "cl_typing (tr_store st) (tr_funcinst fi) (tr_functype ft)"
  using assms(2)
proof (cases rule: Funcinst_ok.cases)
  case mk_Funcinst_ok
  then obtain mi C fn where fi: "fi = \<lparr>funcinst_TYPE = ft, funcinst_MODULE = mi, CODE = fn\<rparr>"
    and M: "Moduleinst_ok st mi C" and F: "Func_ok C fn ft"
    by blast
  from F obtain x ts e t1 t2 where
    fn: "fn = func_FUNC x (map LOCAL ts) e" and ft: "ft = mk_functype (mk_list t1) (mk_list t2)" and
    nb: "list_all (\<lambda>t. t \<noteq> BOT) ts" and
    E: "Expr_ok (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = t1 @ ts,
           LABELS = [mk_list t2], context_RETURN = Some (mk_list t2)\<rparr> C) e (mk_list t2)"
    by (auto elim!: Func_okE)
  from E have I: "Instrs_ok (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = t1 @ ts,
           LABELS = [mk_list t2], context_RETURN = Some (mk_list t2)\<rparr> C) e
          (mk_functype (mk_list []) (mk_list t2))"
    by (auto elim!: Expr_okE)
  have ext: "list_all ext_ok e"
    using assms(3) by (simp add: fi fn func_ext_ok_def)
  show ?thesis
    using Instr_ok_tr(2)[OF I ext] Moduleinst_ok_ctx[OF M] n_zeros_not_bot[OF nb]
    by (simp add: fi fn ft tr_funcinst_def tr_context_func)
       (rule cl_typingI[OF Moduleinst_ok_tr[OF assms(1) M]]; simp)
qed

lemma Store_ok_tr:
  assumes "Store_ok st" "store_ext_ok st"
  shows "store_typing (tr_store st)"
proof (rule store_typing.intros)
  show "list_all (\<lambda>cl. \<exists>tf. cl_typing (tr_store st) cl tf) (s.funcs (tr_store st))"
    using assms Store_ok_elems(1)[OF assms(1)]
    by (fastforce simp: list_all_iff store_ext_ok_def intro: Funcinst_ok_tr)
  show "list_all (tab_agree (tr_store st)) (s.tabs (tr_store st))"
    using Store_ok_elems(2)[OF assms(1)] by (auto simp: list_all_iff intro: Tableinst_ok_tr)
  show "list_all (\<lambda>m. mem_agree m) (s.mems (tr_store st))"
  proof -
    have "\<forall>mi\<in>set (store_MEMS st). mem_agree (tr_meminst mi)"
      using Store_ok_elems(3)[OF assms(1)] Meminst_ok_tr by blast
    then show ?thesis by (simp add: list_all_iff)
  qed
  show "list_all (glob_agree (tr_store st)) (s.globs (tr_store st))"
    using Store_ok_elems(4)[OF assms(1)] by (auto simp: list_all_iff intro: Globalinst_ok_tr)
  show "list_all (elem_agree (tr_store st)) (s.elems (tr_store st))"
    using Store_ok_elems(5)[OF assms(1)] by (auto simp: list_all_iff intro: Eleminst_ok_tr)
  show "list_all (data_agree (tr_store st)) (s.datas (tr_store st))"
    by (simp add: list_all_iff data_agree_def)
qed

theorem Instr_ok2_tr:
  shows "Instr_ok2 st C a ft \<Longrightarrow> Store_ok st \<Longrightarrow> admin_ext_ok a \<Longrightarrow>
           tr_store st\<bullet>tr_context C \<turnstile> [tr_admin a] : tr_functype ft"
    and "Instrs_ok2 st C es ft \<Longrightarrow> Store_ok st \<Longrightarrow> list_all admin_ext_ok es \<Longrightarrow>
           tr_store st\<bullet>tr_context C \<turnstile> tr_admins es : tr_functype ft"
    and "Expr_ok2 st C es rt \<Longrightarrow> Store_ok st \<Longrightarrow> list_all admin_ext_ok es \<Longrightarrow>
           tr_store st\<bullet>tr_context C \<turnstile> tr_admins es : ([] _> tr_resulttype rt)"
proof (induction rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts)
  case plain then show ?case
    by (auto intro!: e_typing_basic1 dest: Instr_ok_tr(1))
next
  case label then show ?case
    by (auto intro!: e_typing_thread_typing.intros(8) simp: tr_admins_def tr_instrs_def)
next
  case Instr_ok2__frame then show ?case
    by (auto intro!: e_typing_thread_typing.intros(6) e_typing_thread_typing.intros(9)
                     Frame_ok_tr simp: tr_admins_def)
next
  case Instr_ok2__call_addr then show ?case
    by (auto dest!: Externaddr_ok_tr intro!: e_typing_thread_typing.intros(7))
next
  case Instr_ok2__ref then show ?case
    by (auto elim!: Ref_ok.cases intro!: e_typing_basic1 b_e_typing.ref_null
                    e_typing_thread_typing.intros(4) ref_typing.intros dest!: Externaddr_ok_tr
             simp: admininstr_ref.simps)
next
  case Instr_ok2__trap then show ?case
    by (simp add: e_typing_thread_typing.intros(5))
next
  case Instrs_ok2__empty then show ?case
    by (simp add: e_typing_empty)
next
  case Instrs_ok2__instr then show ?case
    by simp
next
  case Instrs_ok2__seq then show ?case
    by (auto intro: e_type_comp_conc)
next
  case Instrs_ok2__sub then show ?case
    by (auto dest!: Resulttype_sub_tr
             intro: e_typing_thread_typing.intros(3)[OF _ instr_subtyping_simple])
next
  case Instrs_ok2__frame then show ?case
    by (simp add: e_weakening)
next
  case mk_Expr_ok2 then show ?case
    by simp
qed

section \<open>Configurations\<close>

theorem Config_ok_tr:
  assumes "Config_ok (mk_config (mk_state st fr) es) (mk_list ts)"
          "store_ext_ok st" "list_all admin_ext_ok es"
  shows "config_typing (tr_store st) (tr_frame fr) (tr_admins es) (map tr_valtype ts)"
  using assms(1)
proof (cases rule: Config_ok.cases)
  case mk_Config_ok
  then obtain C where St: "State_ok (mk_state st fr) C" and E: "Expr_ok2 st C es (mk_list ts)"
    by blast
  from St have S: "Store_ok st" and F: "Frame_ok st fr C"
    by (auto elim: State_ok.cases)
  have "tr_store st\<bullet>tr_context C \<turnstile> tr_admins es : ([] _> map tr_valtype ts)"
    using Instr_ok2_tr(3)[OF E S assms(3)] by simp
  then show ?thesis
    using Store_ok_tr[OF S assms(2)] Frame_ok_tr[OF S F] Frame_ok_return[OF F]
    by (auto intro!: config_typing.intros e_typing_thread_typing.intros(9) simp: ctx_return_None)
qed

end

end
