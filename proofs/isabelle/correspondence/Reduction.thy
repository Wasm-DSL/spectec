(* Reduction: a forward simulation of SpecTec's reduction by WasmCert-Isabelle's.
   Port of ../wasmcert-rocq/reduction.v (in progress).

   A SpecTec step of a configuration is matched by WasmCert reduction steps of its
   translation, ending in the translation of the SpecTec result up to evaluated null
   references ([sim]).  SpecTec's null reference value is the instruction
   [REF.NULL t]; WasmCert-Isabelle reduces the instruction [$Ref_null t] to the value
   [Ref (ConstNull t)] (rule [null]), so WasmCert reaches the translated SpecTec
   result with some nulls already evaluated ([nl]).

   This file covers the plain pure redexes; control flow (labels, frames, br,
   return), the state-reading and state-changing rules, vector instructions and the
   evaluation contexts follow the structure of the Rocq proof and are still to come. *)
theory Reduction
  imports Builtins
begin

section \<open>Configurations up to evaluated nulls\<close>

(* [nl w e]: WasmCert's [w] is [e] with some [$Ref_null t] evaluated. *)
inductive nl :: "e \<Rightarrow> e \<Rightarrow> bool" where
  nl_refl[intro!, simp]: "nl e e"
| nl_null[intro!]: "nl (Ref (ConstNull t)) ($Ref_null t)"
| nl_label: "list_all2 nl es es' \<Longrightarrow> nl (Label n les es) (Label n les es')"
| nl_frame: "list_all2 nl es es' \<Longrightarrow> nl (Frame n f es) (Frame n f es')"

abbreviation nls :: "e list \<Rightarrow> e list \<Rightarrow> bool" where
  "nls \<equiv> list_all2 nl"

lemma nls_refl[simp]: "nls es es"
  by (simp add: list.rel_refl)

(* WasmCert reaches [b] up to evaluated nulls from [a]. *)
definition wsim :: "s \<times> f \<times> e list \<Rightarrow> s \<times> f \<times> e list \<Rightarrow> bool" where
  "wsim a b \<longleftrightarrow> (case b of (St', Fr', es') \<Rightarrow> \<exists>es''. reduce_trans a (St', Fr', es'') \<and> nls es'' es')"

definition sim :: "config \<Rightarrow> config \<Rightarrow> bool" where
  "sim c c' \<longleftrightarrow> wsim (tr_config c) (tr_config c')"

(* A pure step: the store and frame do not matter. *)
definition psim :: "admininstr list \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "psim es es' \<longleftrightarrow> (\<forall>St Fr. wsim (St, Fr, tr_admins es) (St, Fr, tr_admins es'))"

lemma psim_sim: "psim es es' \<Longrightarrow> sim (mk_config (mk_state st fr) es) (mk_config (mk_state st fr) es')"
  by (simp add: psim_def sim_def)

section \<open>WasmCert reduction sequences\<close>

lemma rt_refl[simp]: "reduce_trans a a"
  by (simp add: reduce_trans_def)

lemma rt_step: "reduce St Fr es St' Fr' es' \<Longrightarrow> reduce_trans (St', Fr', es') b \<Longrightarrow> reduce_trans (St, Fr, es) b"
  unfolding reduce_trans_def by (rule converse_rtranclp_into_rtranclp) auto

lemma rt_trans: "reduce_trans a b \<Longrightarrow> reduce_trans b c \<Longrightarrow> reduce_trans a c"
  unfolding reduce_trans_def by (rule rtranclp_trans)

lemma wsim_refl: "nls es' es \<Longrightarrow> wsim (St, Fr, es') (St, Fr, es)"
  unfolding wsim_def using rt_refl by blast

lemma wsim_rt:
  assumes "reduce_trans a b" "wsim b c"
  shows "wsim a c"
proof -
  obtain St' Fr' es' where c: "c = (St', Fr', es')" by (cases c)
  with assms(2) obtain es'' where "reduce_trans b (St', Fr', es'')" "nls es'' es'"
    by (auto simp: wsim_def)
  with rt_trans[OF assms(1)] c show ?thesis by (auto simp: wsim_def)
qed

lemma wsim_step: "reduce St Fr es St' Fr' es' \<Longrightarrow> wsim (St', Fr', es') c \<Longrightarrow> wsim (St, Fr, es) c"
  by (rule wsim_rt[OF rt_step[OF _ rt_refl]])

lemma wsim_basic: "reduce_simple es es' \<Longrightarrow> nls es' es'' \<Longrightarrow> wsim (St, Fr, es) (St, Fr, es'')"
  by (rule wsim_step[OF reduce.basic wsim_refl])

section \<open>Evaluating the null references among values\<close>

lemma tr_admins_append[simp]: "tr_admins (es1 @ es2) = tr_admins es1 @ tr_admins es2"
  by (simp add: tr_admins_def)

lemma tr_admins_Cons[simp]: "tr_admins (e # es) = tr_admin e # tr_admins es"
  by (simp add: tr_admins_def)

lemma tr_admins_Nil[simp]: "tr_admins [] = []"
  by (simp add: tr_admins_def)

lemma null_step: "reduce St Fr (($C* ws) @ [$Ref_null t] @ es) St Fr (($C* ws) @ [Ref (ConstNull t)] @ es)"
  by (rule progress_L0[OF reduce.basic[OF reduce_simple.null]])

lemma eval_val:
  "reduce_trans (St, Fr, ($C* ws) @ tr_admin (admininstr_val v) # es) (St, Fr, ($C* ws) @ ($C (tr_val v)) # es)"
proof (cases v)
  case (val_REF_NULL rt)
  then show ?thesis using rt_step[OF null_step[of St Fr ws "tr_reftype rt" es] rt_refl]
    by (simp add: v_to_e_def)
qed (simp_all add: v_to_e_def tr_vec_def)

lemma eval_vals:
  "reduce_trans (St, Fr, ($C* ws) @ tr_admins (map admininstr_val vs) @ es)
                (St, Fr, ($C* ws) @ ($C* map tr_val vs) @ es)"
proof (induction vs arbitrary: ws)
  case Nil then show ?case by simp
next
  case (Cons v vs)
  have a: "reduce_trans (St, Fr, ($C* ws) @ tr_admins (map admininstr_val (v # vs)) @ es)
                     (St, Fr, ($C* (ws @ [tr_val v])) @ tr_admins (map admininstr_val vs) @ es)"
    using eval_val[of St Fr ws v "tr_admins (map admininstr_val vs) @ es"] by simp
  have b: "reduce_trans (St, Fr, ($C* (ws @ [tr_val v])) @ tr_admins (map admininstr_val vs) @ es)
                     (St, Fr, ($C* ws) @ ($C* map tr_val (v # vs)) @ es)"
    using Cons.IH[of "ws @ [tr_val v]"] by simp
  show ?case by (rule rt_trans[OF a b])
qed

lemma eval_vals0:
  "reduce_trans (St, Fr, tr_admins (map admininstr_val vs) @ es) (St, Fr, ($C* map tr_val vs) @ es)"
  using eval_vals[of St Fr "[]" vs es] by simp

lemma nl_val: "nl ($C (tr_val v)) (tr_admin (admininstr_val v))"
  by (cases v) (auto simp: v_to_e_def tr_vec_def)

lemma nl_val'[simp]: "nl ($C (tr_val v)) (case v of val_REF_NULL rt \<Rightarrow> $Ref_null (tr_reftype rt) | _ \<Rightarrow> $C (tr_val v))"
  using nl_val[of v] by simp

lemma nls_vals: "nls ($C* map tr_val vs) (tr_admins (map admininstr_val vs))"
  by (induction vs) (simp_all add: nl_val)

(* A redex whose operands are values: evaluate their nulls, then reduce. *)
lemma psim_vals:
  assumes "\<And>St Fr. wsim (St, Fr, ($C* map tr_val vs) @ tr_admins es) (St, Fr, tr_admins es')"
  shows "psim (map admininstr_val vs @ es) es'"
  unfolding psim_def tr_admins_append using wsim_rt[OF eval_vals0 assms] by blast

lemma admininstr_val_simps[simp]:
  "admininstr_val (val_CONST nt c) = admininstr_sc1 (admininstr_st1_CONST nt c)"
  by (simp add: admininstr_val.simps)

lemma tr_val_CONST_e[simp]: "($C (tr_val (val_CONST nt c))) = ($EConstNum (tr_num c))"
  by (simp add: v_to_e_def)

lemma v_to_e_num[simp]: "($C (V_num x)) = ($EConstNum x)"
  by (simp add: v_to_e_def)

section \<open>Plain pure redexes\<close>

lemma psim_unreachable: "psim [admininstr_sc0 admininstr_st0_UNREACHABLE] [admininstr_sc7 admininstr_st7_TRAP]"
  unfolding psim_def by (auto intro!: wsim_basic reduce_simple.unreachable)

lemma psim_nop: "psim [admininstr_sc0 admininstr_st0_NOP] []"
  unfolding psim_def by (auto intro!: wsim_basic reduce_simple.nop)

lemma psim_drop: "psim [admininstr_val v, admininstr_sc0 admininstr_st0_DROP] []"
proof -
  have "psim (map admininstr_val [v] @ [admininstr_sc0 admininstr_st0_DROP]) []"
    by (rule psim_vals) (auto intro!: wsim_basic reduce_simple.drop)
  then show ?thesis by simp
qed

termination proj_num__0 by lexicographic_order

lemma int_eq_tr_i32_0: "un u < 2 ^ 32 \<Longrightarrow> int_eq (tr_i32 u) 0 \<longleftrightarrow> un u = 0"
  by (simp add: int_eq_i32_def map_fun_def I32.int_eq_def zero_i32_def of_nat_word_eq_0)

lemma nat_of_int_tr_i32: "un u < 2 ^ 32 \<Longrightarrow> nat_of_int (tr_i32 u) = un u"
  by (simp add: nat_of_int_i32_def map_fun_def unat_of_nat_lt)

lemma tr_i32_bool[simp]: "tr_i32 (mk_uN 1) = wasm_bool True" "tr_i32 (mk_uN 0) = wasm_bool False"
  using tr_i32_res_bool[of True] tr_i32_res_bool[of False] by simp_all

lemma tr_i32_Suc0[simp]: "tr_i32 (mk_uN (Suc 0)) = wasm_bool True"
  using tr_i32_bool(1) by simp

(* An [i32] constant operand. *)
abbreviation i32c :: "uN \<Rightarrow> admininstr" where
  "i32c u \<equiv> admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 u))"

lemma psim_select:
  assumes "un u < 2 ^ 32" "r = (if un u \<noteq> 0 then v1 else v2)"
  shows "psim [admininstr_val v1, admininstr_val v2, i32c u, admininstr_sc0 (admininstr_st0_SELECT ts)]
              [admininstr_val r]"
proof -
  have "psim (map admininstr_val [v1, v2, val_CONST I32 (mk_num__0 Inn_I32 u)] @
              [admininstr_sc0 (admininstr_st0_SELECT ts)]) [admininstr_val r]"
  proof (rule psim_vals)
    fix St Fr
    show "wsim (St, Fr, ($C* map tr_val [v1, v2, val_CONST I32 (mk_num__0 Inn_I32 u)]) @
                      tr_admins [admininstr_sc0 (admininstr_st0_SELECT ts)])
               (St, Fr, tr_admins [admininstr_val r])"
    proof (cases "un u = 0")
      case True then show ?thesis using assms
        by (auto intro!: wsim_basic reduce_simple.select_false simp: int_eq_tr_i32_0 nl_val)
    next
      case False then show ?thesis using assms
        by (auto intro!: wsim_basic reduce_simple.select_true simp: int_eq_tr_i32_0 nl_val)
    qed
  qed
  then show ?thesis by simp
qed

lemma psim_if:
  assumes "un u < 2 ^ 32" "ins = (if un u \<noteq> 0 then ins1 else ins2)"
  shows "psim [i32c u, admininstr_sc0 (admininstr_st0_IFELSE bt ins1 ins2)]
              [admininstr_sc0 (admininstr_st0_BLOCK bt ins)]"
  unfolding psim_def using assms
  by (cases "un u = 0")
     (auto intro!: wsim_basic reduce_simple.if_false reduce_simple.if_true simp: int_eq_tr_i32_0)

lemma psim_br_if:
  assumes "un u < 2 ^ 32" "es' = (if un u \<noteq> 0 then [admininstr_sc0 (admininstr_st0_BR l)] else [])"
  shows "psim [i32c u, admininstr_sc0 (admininstr_st0_BR_IF l)] es'"
  unfolding psim_def using assms
  by (cases "un u = 0")
     (auto intro!: wsim_basic reduce_simple.br_if_false reduce_simple.br_if_true simp: int_eq_tr_i32_0)

lemma psim_br_table:
  assumes "un u < 2 ^ 32" "l = (if un u < length ls then ls ! un u else l')"
  shows "psim [i32c u, admininstr_sc1 (admininstr_st1_BR_TABLE ls l')] [admininstr_sc0 (admininstr_st0_BR l)]"
  unfolding psim_def using assms
  by (cases "un u < length ls")
     (auto intro!: wsim_basic reduce_simple.br_table reduce_simple.br_table_length
           simp: nat_of_int_tr_i32 not_less)

lemma psim_local_tee:
  "psim [admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_TEE x)]
        [admininstr_val v, admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_SET x)]"
proof -
  have "psim (map admininstr_val [v] @ [admininstr_sc4 (admininstr_st4_LOCAL_TEE x)])
             [admininstr_val v, admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_SET x)]"
    by (rule psim_vals) (auto intro!: wsim_basic reduce_simple.local_tee)
  then show ?thesis by simp
qed

lemma psim_trap_vals:
  assumes "vs \<noteq> [] \<or> es \<noteq> []"
  shows "psim (map admininstr_val vs @ [admininstr_sc7 admininstr_st7_TRAP] @ es) [admininstr_sc7 admininstr_st7_TRAP]"
proof (rule psim_vals)
  fix St Fr
  have "Lfilled 0 (LBase (map tr_val vs) (tr_admins es)) [Trap] (($C* map tr_val vs) @ [Trap] @ tr_admins es)"
    by (rule Lfilled.L0) simp
  moreover have "($C* map tr_val vs) @ [Trap] @ tr_admins es \<noteq> [Trap]"
    using assms by (cases vs) (auto simp: tr_admins_def)
  ultimately show "wsim (St, Fr, ($C* map tr_val vs) @ tr_admins ([admininstr_sc7 admininstr_st7_TRAP] @ es))
                        (St, Fr, tr_admins [admininstr_sc7 admininstr_st7_TRAP])"
    by (auto intro!: wsim_basic reduce_simple.trap)
qed

lemma eval_ref:
  "reduce_trans (St, Fr, tr_admin (admininstr_ref r) # es) (St, Fr, Ref (tr_ref r) # es)"
proof (cases r)
  case (ref_REF_NULL rt)
  then show ?thesis using rt_step[OF null_step[of St Fr "[]" "tr_reftype rt" es] rt_refl] by simp
qed simp_all

lemma psim_ref_is_null:
  assumes "b = (\<exists>rt. r = ref_REF_NULL rt)"
  shows "psim [admininstr_ref r, admininstr_sc4 admininstr_st4_REF_IS_NULL]
              [i32c (mk_uN (if b then 1 else 0))]"
  unfolding psim_def
proof (intro allI)
  fix St Fr
  have h: "wsim (St, Fr, Ref (tr_ref r) # [$Ref_is_null]) (St, Fr, tr_admins [i32c (mk_uN (if b then 1 else 0))])"
    using assms
    by (cases r) (auto intro!: wsim_basic reduce_simple.is_null_true reduce_simple.is_null_false
                       simp: is_null_ref_def)
  show "wsim (St, Fr, tr_admins [admininstr_ref r, admininstr_sc4 admininstr_st4_REF_IS_NULL])
                  (St, Fr, tr_admins [i32c (mk_uN (if b then 1 else 0))])"
    using wsim_rt[OF eval_ref[of St Fr r "[$Ref_is_null]"] h] by simp
qed

section \<open>Numeric redexes\<close>

lemma (in builtins) psim_unop:
  assumes "wf_num_underscore nt c1" "fun_unop_underscore nt op c1 (Some cs)" "unop_ext_ok nt op"
    "c \<in> set cs"
  shows "psim [admininstr_sc1 (admininstr_st1_CONST nt c1), admininstr_sc1 (admininstr_st1_UNOP nt op)]
              [admininstr_sc1 (admininstr_st1_CONST nt c)]"
proof -
  have "tr_num c = app_unop (tr_unop op) (tr_num c1)"
    using unop_tr[OF assms(1-3)] assms(4) by (cases cs) auto
  then show ?thesis unfolding psim_def by (auto intro!: wsim_basic reduce_simple.unop)
qed

(* SpecTec never traps on a unary operator. *)
lemma (in builtins) unop_no_trap:
  "wf_num_underscore nt c1 \<Longrightarrow> fun_unop_underscore nt op c1 (Some []) \<Longrightarrow> unop_ext_ok nt op \<Longrightarrow> False"
  using unop_tr by fastforce

lemma (in builtins) psim_binop_val:
  assumes "wf_num_underscore nt c1" "wf_num_underscore nt c2" "fun_binop_underscore nt op c1 c2 (Some cs)"
    "\<not> divzero op c2" "c \<in> set cs"
  shows "psim [admininstr_sc1 (admininstr_st1_CONST nt c1), admininstr_sc1 (admininstr_st1_CONST nt c2),
               admininstr_sc1 (admininstr_st1_BINOP nt op)]
              [admininstr_sc1 (admininstr_st1_CONST nt c)]"
proof -
  have "app_binop (tr_binop op) (tr_num c1) (tr_num c2) = Some (tr_num c)"
    using binop_tr[OF assms(3,1,2)] assms(4,5)
    by (cases "app_binop (tr_binop op) (tr_num c1) (tr_num c2)"; cases cs) auto
  then show ?thesis unfolding psim_def by (auto intro!: wsim_basic reduce_simple.binop_Some)
qed

lemma (in builtins) psim_binop_trap:
  assumes "wf_num_underscore nt c1" "wf_num_underscore nt c2" "fun_binop_underscore nt op c1 c2 (Some [])"
  shows "psim [admininstr_sc1 (admininstr_st1_CONST nt c1), admininstr_sc1 (admininstr_st1_CONST nt c2),
               admininstr_sc1 (admininstr_st1_BINOP nt op)]
              [admininstr_sc7 admininstr_st7_TRAP]"
proof -
  have "app_binop (tr_binop op) (tr_num c1) (tr_num c2) = None"
    using binop_tr[OF assms(3,1,2)]
    by (cases "app_binop (tr_binop op) (tr_num c1) (tr_num c2)") auto
  then show ?thesis unfolding psim_def by (auto intro!: wsim_basic reduce_simple.binop_None)
qed

lemma psim_testop:
  assumes "wf_num_underscore nt c1" "fun_testop_underscore nt op c1 (Some c)"
  shows "psim [admininstr_sc1 (admininstr_st1_CONST nt c1), admininstr_sc1 (admininstr_st1_TESTOP nt op)]
              [admininstr_sc1 (admininstr_st1_CONST I32 c)]"
  unfolding psim_def using testop_tr[OF assms] by (auto intro!: wsim_basic reduce_simple.testop)

lemma (in builtins) psim_relop:
  assumes "wf_num_underscore nt c1" "wf_num_underscore nt c2" "fun_relop_underscore nt op c1 c2 (Some c)"
  shows "psim [admininstr_sc1 (admininstr_st1_CONST nt c1), admininstr_sc1 (admininstr_st1_CONST nt c2),
               admininstr_sc1 (admininstr_st1_RELOP nt op)]
              [admininstr_sc1 (admininstr_st1_CONST I32 c)]"
  unfolding psim_def using relop_tr[OF assms] by (auto intro!: wsim_basic reduce_simple.relop)

lemma (in builtins) psim_cvtop:
  assumes "wf_num_underscore nt1 c1" "wf_cvtop__underscore nt1 nt2 op"
    "fun_cvtop__underscore nt1 nt2 op c1 (Some cs)"
    "es' = (if cs = [] then [admininstr_sc7 admininstr_st7_TRAP] else [admininstr_sc1 (admininstr_st1_CONST nt2 c)])"
    "cs \<noteq> [] \<Longrightarrow> c \<in> set cs"
  shows "psim [admininstr_sc1 (admininstr_st1_CONST nt1 c1), admininstr_sc2 (admininstr_st2_CVTOP nt2 nt1 op)] es'"
proof -
  have m: "map tr_num cs = olist (wc_cvtop nt2 op (tr_num c1))" by (rule cvtop_tr[OF assms(1-3)])
  have ty: "typeof_num (tr_num c1) = tr_numtype nt1" by (rule typeof_tr_num[OF assms(1)])
  show ?thesis
  proof (cases "fst (tr_cvtop op)")
    case Convert
    then show ?thesis using m ty assms(4,5) unfolding psim_def
      by (cases cs; cases "cvt (tr_numtype nt2) (snd (tr_cvtop op)) (tr_num c1)")
         (auto simp: wc_cvtop_def intro!: wsim_basic reduce_simple.convert_Some reduce_simple.convert_None)
  next
    case Reinterpret
    then have "snd (tr_cvtop op) = None" by (cases op rule: tr_cvtop.cases) auto
    then show ?thesis using m ty assms(4,5) Reinterpret unfolding psim_def
      by (cases cs) (auto simp: wc_cvtop_def intro!: wsim_basic reduce_simple.reinterpret)
  qed
qed

section \<open>Labels and frames\<close>

lemma tr_admins_fold[simp]: "map tr_admin es = tr_admins es"
  by (simp add: tr_admins_def)

(* Simp-normal forms after map fusion. *)
lemma tr_admins_map_val[simp]: "tr_admins (map admininstr_val vs) = map (tr_admin \<circ> admininstr_val) vs"
  by (simp add: tr_admins_def)

lemma nls_vals'[simp]: "nls (map (v_to_e \<circ> tr_val) vs) (map (tr_admin \<circ> admininstr_val) vs)"
  using nls_vals[of vs] by (simp add: tr_admins_def)

lemma tr_admins_instrs[simp]:"tr_admins (map admininstr_instr ins) = map Basic (tr_instrs ins)"
  by (simp add: tr_admins_def tr_instrs_def)

lemma eval_vals_label:
  "reduce_trans (St, Fr, [Label n les (tr_admins (map admininstr_val vs) @ es)])
                (St, Fr, [Label n les (($C* map tr_val vs) @ es)])"
  by (rule reduce_trans_label[OF eval_vals0])

lemma eval_vals_frame:
  "reduce_trans (St, Fr0, [Frame n F (tr_admins (map admininstr_val vs) @ es)])
                (St, Fr0, [Frame n F (($C* map tr_val vs) @ es)])"
  by (rule reduce_trans_local[OF eval_vals0])

lemma psim_label_vals:
  "psim [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs))] (map admininstr_val vs)"
  unfolding psim_def
proof (intro allI)
  fix St Fr
  have r: "reduce_trans (St, Fr, tr_admins [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs))])
                        (St, Fr, [Label n (map Basic (tr_instrs ins)) ($C* map tr_val vs)])"
    using eval_vals_label[of St Fr n "map Basic (tr_instrs ins)" vs "[]"] by simp
  show "wsim (St, Fr, tr_admins [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs))])
             (St, Fr, tr_admins (map admininstr_val vs))"
    by (rule wsim_rt[OF r wsim_basic[OF reduce_simple.label_const nls_vals]])
qed

lemma psim_trap_label:
  "psim [admininstr_sc7 (LABEL_underscore n ins [admininstr_sc7 admininstr_st7_TRAP])]
        [admininstr_sc7 admininstr_st7_TRAP]"
  unfolding psim_def by (auto intro!: wsim_basic reduce_simple.label_trap)

lemma psim_frame_vals:
  "psim [admininstr_sc8 (FRAME_underscore n fr (map admininstr_val vs))] (map admininstr_val vs)"
  unfolding psim_def
proof (intro allI)
  fix St Fr
  have r: "reduce_trans (St, Fr, tr_admins [admininstr_sc8 (FRAME_underscore n fr (map admininstr_val vs))])
                        (St, Fr, [Frame n (tr_frame fr) ($C* map tr_val vs)])"
    using eval_vals_frame[of St Fr n "tr_frame fr" vs "[]"] by simp
  show "wsim (St, Fr, tr_admins [admininstr_sc8 (FRAME_underscore n fr (map admininstr_val vs))])
             (St, Fr, tr_admins (map admininstr_val vs))"
    by (rule wsim_rt[OF r wsim_basic[OF reduce_simple.local_const nls_vals]])
qed

lemma psim_trap_frame:
  "psim [admininstr_sc8 (FRAME_underscore n fr [admininstr_sc7 admininstr_st7_TRAP])]
        [admininstr_sc7 admininstr_st7_TRAP]"
  unfolding psim_def by (auto intro!: wsim_basic reduce_simple.local_trap)

lemma nls_append: "nls a b \<Longrightarrow> nls c d \<Longrightarrow> nls (a @ c) (b @ d)"
  by (rule list_all2_appendI)

(* [br 0] at the top of a label: WasmCert's [br] with a context of depth 0. *)
lemma psim_br_zero:
  assumes "n = length vs"
  shows "psim [admininstr_sc7 (LABEL_underscore n ins
                 (map admininstr_val vs' @ map admininstr_val vs @
                  [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))] @ es))]
              (map admininstr_val vs @ map admininstr_instr ins)"
  unfolding psim_def
proof (intro allI)
  fix St Fr
  let ?les = "map Basic (tr_instrs ins)"
  let ?LI = "($C* map tr_val vs') @ (($C* map tr_val vs) @ [$Br 0]) @ tr_admins es"
  have r: "reduce_trans (St, Fr, tr_admins [admininstr_sc7 (LABEL_underscore n ins
                 (map admininstr_val vs' @ map admininstr_val vs @
                  [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))] @ es))])
                        (St, Fr, [Label n ?les ?LI])"
    using eval_vals_label[of St Fr n ?les "vs' @ vs" "[$Br 0] @ tr_admins es"] by simp
  have lf: "Lfilled 0 (LBase (map tr_val vs') (tr_admins es)) (($C* map tr_val vs) @ [$Br 0]) ?LI"
    by (rule Lfilled.L0) simp
  have st: "reduce_simple [Label n ?les ?LI] (($C* map tr_val vs) @ ?les)"
    by (rule reduce_simple.br[OF _ lf]) (simp add: assms)
  show "wsim (St, Fr, tr_admins [admininstr_sc7 (LABEL_underscore n ins
                 (map admininstr_val vs' @ map admininstr_val vs @
                  [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))] @ es))])
             (St, Fr, tr_admins (map admininstr_val vs @ map admininstr_instr ins))"
    by (rule wsim_rt[OF r wsim_basic[OF st]]) (simp add: nls_append nls_vals)
qed

(* [return] at the top of a frame: WasmCert's [return] with a context of depth 0. *)
lemma psim_return_frame:
  assumes "n = length vs"
  shows "psim [admininstr_sc8 (FRAME_underscore n fr
                 (map admininstr_val vs' @ map admininstr_val vs @
                  [admininstr_sc1 admininstr_st1_RETURN] @ es))]
              (map admininstr_val vs)"
  unfolding psim_def
proof (intro allI)
  fix St Fr
  let ?LI = "($C* map tr_val vs') @ (($C* map tr_val vs) @ [$Return]) @ tr_admins es"
  have r: "reduce_trans (St, Fr, tr_admins [admininstr_sc8 (FRAME_underscore n fr
                 (map admininstr_val vs' @ map admininstr_val vs @
                  [admininstr_sc1 admininstr_st1_RETURN] @ es))])
                        (St, Fr, [Frame n (tr_frame fr) ?LI])"
    using eval_vals_frame[of St Fr n "tr_frame fr" "vs' @ vs" "[$Return] @ tr_admins es"] by simp
  have lf: "Lfilled 0 (LBase (map tr_val vs') (tr_admins es)) (($C* map tr_val vs) @ [$Return]) ?LI"
    by (rule Lfilled.L0) simp
  have st: "reduce_simple [Frame n (tr_frame fr) ?LI] ($C* map tr_val vs)"
    by (rule reduce_simple.return[OF _ lf]) (simp add: assms)
  show "wsim (St, Fr, tr_admins [admininstr_sc8 (FRAME_underscore n fr
                 (map admininstr_val vs' @ map admininstr_val vs @
                  [admininstr_sc1 admininstr_st1_RETURN] @ es))])
             (St, Fr, tr_admins (map admininstr_val vs))"
    by (rule wsim_rt[OF r wsim_basic[OF st nls_vals]])
qed

section \<open>Rules that read the state\<close>

termination fun_funcaddr by lexicographic_order

lemma sim_iff: "sim (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es') \<longleftrightarrow>
  wsim (tr_store s, tr_frame f, tr_admins es) (tr_store s', tr_frame f', tr_admins es')"
  by (simp add: sim_def)

lemma tr_frame_sel[simp]:
  "f_locs (tr_frame f) = map tr_val (LOCALS f)" "f_inst (tr_frame f) = tr_moduleinst (frame_MODULE f)"
  by (simp_all add: tr_frame_def)

lemma tr_moduleinst_sel[simp]:
  "inst.types (tr_moduleinst mi) = map tr_functype (TYPES mi)" "inst.funcs (tr_moduleinst mi) = FUNCS mi"
  "inst.tabs (tr_moduleinst mi) = TABLES mi" "inst.mems (tr_moduleinst mi) = MEMS mi"
  "inst.globs (tr_moduleinst mi) = GLOBALS mi" "inst.elems (tr_moduleinst mi) = ELEMS mi"
  "inst.datas (tr_moduleinst mi) = DATAS mi"
  by (simp_all add: tr_moduleinst_def)

lemma tr_store_sel[simp]:
  "s.funcs (tr_store st) = map tr_funcinst (store_FUNCS st)"
  "s.tabs (tr_store st) = map tr_tableinst (store_TABLES st)"
  "s.mems (tr_store st) = map tr_meminst (store_MEMS st)"
  "s.globs (tr_store st) = map tr_globalinst (store_GLOBALS st)"
  "s.elems (tr_store st) = map tr_eleminst (store_ELEMS st)"
  "s.datas (tr_store st) = map tr_datainst (store_DATAS st)"
  by (simp_all add: tr_store_def)

lemma g_val_tr[simp]: "g_val (tr_globalinst gi) = tr_val (VALUE gi)"
  by (cases "globalinst_TYPE gi") (simp add: tr_globalinst_def)

lemma tab_size_tr[simp]: "tab_size (tr_tableinst ti) = length (REFS ti)"
  by (simp add: tr_tableinst_def)

lemma mem_length_tr[simp]: "mem_length (tr_meminst mi) = length (BYTES mi)"
  by (simp add: tr_meminst_def mem_length_def mem_rep_length.abs_eq)

lemma int_of_nat_tr_i32[simp]: "(int_of_nat n :: Wasm_Ast.i32) = tr_i32 (mk_uN n)"
  using int_of_nat_tr32[of "mk_uN n"] by simp

lemma nls_single_val: "nls [$C (tr_val v)] (tr_admins [admininstr_val v])"
  by (simp only: tr_admins_Cons tr_admins_Nil list_all2_Cons list_all2_Nil nl_val simp_thms)

lemma sim_local_get:
  assumes "fun_local (mk_state s f) x v"
  shows "sim (mk_config (mk_state s f) [admininstr_sc4 (admininstr_st4_LOCAL_GET x)])
             (mk_config (mk_state s f) [admininstr_val v])"
proof -
  from assms have x: "un x < length (LOCALS f)" "v = LOCALS f ! un x"
    by (auto elim: fun_local.cases)
  let ?ls = "map tr_val (LOCALS f)"
  have l: "f_locs (tr_frame f) = take (un x) ?ls @ [tr_val v] @ drop (Suc (un x)) ?ls"
    using x id_take_nth_drop[of "un x" ?ls] by simp
  have st: "reduce (tr_store s) (tr_frame f) [$Local_get (un x)] (tr_store s) (tr_frame f) [$C (tr_val v)]"
    by (rule reduce.local_get[OF _ l]) (use x in simp)
  show ?thesis unfolding sim_iff
    using wsim_step[OF st wsim_refl[OF nls_single_val]] by simp
qed

lemma sim_global_get:
  assumes "fun_global (mk_state s f) x gi"
  shows "sim (mk_config (mk_state s f) [admininstr_sc5 (admininstr_st5_GLOBAL_GET x)])
             (mk_config (mk_state s f) [admininstr_val (VALUE gi)])"
proof -
  from assms have x: "GLOBALS (frame_MODULE f) ! un x < length (store_GLOBALS s)"
      "gi = store_GLOBALS s ! (GLOBALS (frame_MODULE f) ! un x)"
    by (auto elim: fun_global.cases)
  have v: "sglob_val (tr_store s) (f_inst (tr_frame f)) (un x) = tr_val (VALUE gi)"
    using x by (simp add: sglob_val_def sglob_def sglob_ind_def)
  show ?thesis unfolding sim_iff
    using wsim_step[OF reduce.global_get[of "tr_store s" "tr_frame f" "un x", unfolded v] wsim_refl[OF nls_single_val]] by simp
qed

lemma sim_ref_func:
  assumes "un x < length (fun_funcaddr (mk_state s f))"
  shows "sim (mk_config (mk_state s f) [admininstr_sc4 (admininstr_st4_REF_FUNC x)])
             (mk_config (mk_state s f) [admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR (fun_funcaddr (mk_state s f) ! un x))])"
  unfolding sim_iff using wsim_step[OF reduce.ref_func[of _ "tr_frame f" "un x"] wsim_refl[of "[Ref (ConstRefFunc (fun_funcaddr (mk_state s f) ! un x))]"]] by simp

lemma sim_table_size:
  assumes "fun_table (mk_state s f) x ti" "length (REFS ti) = n"
  shows "sim (mk_config (mk_state s f) [admininstr_sc5 (admininstr_st5_TABLE_SIZE x)])
             (mk_config (mk_state s f) [i32c (mk_uN n)])"
proof -
  from assms(1) have x: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)"
      "un x < length (TABLES (frame_MODULE f))"
      "ti = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    by (auto elim: fun_table.cases)
  have st: "reduce (tr_store s) (tr_frame f) [$Table_size (un x)] (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (int_of_nat n))]"
    by (rule reduce.table_size[where a = "TABLES (frame_MODULE f) ! un x" and t = "tr_tableinst ti"]) (use x assms(2) in \<open>simp_all add: stab_ind_def\<close>)
  show ?thesis unfolding sim_iff using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_memory_size:
  assumes "fun_mem (mk_state s f) (mk_uN 0) mi" "n * 64 * Ki = length (BYTES mi)"
  shows "sim (mk_config (mk_state s f) [admininstr_sc6 admininstr_st6_MEMORY_SIZE])
             (mk_config (mk_state s f) [i32c (mk_uN n)])"
proof -
  from assms(1) have x: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)"
      "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    by (auto elim: fun_mem.cases)
  have sz: "mem_size (tr_meminst mi) = n"
    using assms(2) by (simp add: mem_size_def Ki64_def Ki_def)
  have st: "reduce (tr_store s) (tr_frame f) [$Memory_size] (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (int_of_nat n))]"
    by (rule reduce.memory_size[where j = "MEMS (frame_MODULE f) ! 0"])
       (use x sz in \<open>simp_all add: smem_ind_def neq_Nil_conv split: list.splits\<close>)
  show ?thesis unfolding sim_iff using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma tb_tf_tr:
  assumes "fun_blocktype (mk_state s f) bt ft"
  shows "tb_tf (tr_moduleinst (frame_MODULE f)) (tr_blocktype bt) = tr_functype ft"
  using assms by (auto elim!: fun_blocktype.cases fun_type.cases simp: tb_tf_def)

lemma sim_block:
  assumes "fun_blocktype (mk_state s f) bt (mk_functype (mk_list t1) (mk_list t2))"
    "length vs = length t1" "n = length t2"
  shows "sim (mk_config (mk_state s f) (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BLOCK bt ins)]))
             (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore n [] (map admininstr_val vs @ map admininstr_instr ins))])"
proof -
  have tf: "tb_tf (f_inst (tr_frame f)) (tr_blocktype bt) = (map tr_valtype t1 _> map tr_valtype t2)"
    using tb_tf_tr[OF assms(1)] by simp
  have st: "reduce (tr_store s) (tr_frame f) (($C* map tr_val vs) @ [$(Block (tr_blocktype bt) (tr_instrs ins))])
              (tr_store s) (tr_frame f) [Label n [] (($C* map tr_val vs) @ ($* tr_instrs ins))]"
    by (rule reduce.block[OF _ tf]) (use assms(2,3) in simp_all)
  have e: "reduce_trans (tr_store s, tr_frame f, tr_admins (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BLOCK bt ins)]))
              (tr_store s, tr_frame f, ($C* map tr_val vs) @ [$(Block (tr_blocktype bt) (tr_instrs ins))])"
    using eval_vals0[of "tr_store s" "tr_frame f" vs "[$(Block (tr_blocktype bt) (tr_instrs ins))]"]
    by (simp add: tr_instrs_def)
  show ?thesis unfolding sim_iff
    by (rule wsim_rt[OF e wsim_step[OF st wsim_refl]])
       (simp add: nl_label nls_append tr_instrs_def)
qed

lemma sim_loop:
  assumes "fun_blocktype (mk_state s f) bt (mk_functype (mk_list t1) (mk_list t2))"
    "length vs = length t1" "k = length vs"
  shows "sim (mk_config (mk_state s f) (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_LOOP bt ins)]))
             (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore k [instr_sc7 (LOOP bt ins)]
                                         (map admininstr_val vs @ map admininstr_instr ins))])"
proof -
  have tf: "tb_tf (f_inst (tr_frame f)) (tr_blocktype bt) = (map tr_valtype t1 _> map tr_valtype t2)"
    using tb_tf_tr[OF assms(1)] by simp
  have st: "reduce (tr_store s) (tr_frame f) (($C* map tr_val vs) @ [$(Loop (tr_blocktype bt) (tr_instrs ins))])
              (tr_store s) (tr_frame f)
              [Label k [$(Loop (tr_blocktype bt) (tr_instrs ins))] (($C* map tr_val vs) @ ($* tr_instrs ins))]"
    by (rule reduce.loop[OF _ tf]) (use assms(2,3) in simp_all)
  have e: "reduce_trans (tr_store s, tr_frame f, tr_admins (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_LOOP bt ins)]))
              (tr_store s, tr_frame f, ($C* map tr_val vs) @ [$(Loop (tr_blocktype bt) (tr_instrs ins))])"
    using eval_vals0[of "tr_store s" "tr_frame f" vs "[$(Loop (tr_blocktype bt) (tr_instrs ins))]"]
    by (simp add: tr_instrs_def)
  show ?thesis unfolding sim_iff
    by (rule wsim_rt[OF e wsim_step[OF st wsim_refl]])
       (simp add: nl_label nls_append tr_instrs_def)
qed

section \<open>Rules that change the state\<close>

termination with_local by lexicographic_order

(* SpecTec's [list_update_func] is list update (a no-op out of range). *)
lemma list_update_func_conv: "list_update_func xs i g = (if i < length xs then xs[i := g (xs ! i)] else xs)"
  by (induction xs i g rule: list_update_func.induct) auto

lemma map_list_update_func: "map h (list_update_func xs i g) = (if i < length xs then (map h xs)[i := h (g (xs ! i))] else map h xs)"
  by (simp add: list_update_func_conv map_update)

lemma tr_globalinst_upd: "tr_globalinst (gi\<lparr>VALUE := v\<rparr>) = (tr_globalinst gi)\<lparr>g_val := tr_val v\<rparr>"
  by (cases "globalinst_TYPE gi") (simp add: tr_globalinst_def)

lemma tr_eleminst_drop: "tr_eleminst (ei\<lparr>eleminst_REFS := []\<rparr>) = (fst (tr_eleminst ei), [])"
  by (simp add: tr_eleminst_def)

lemma tr_datainst_drop: "tr_datainst (di\<lparr>datainst_BYTES := []\<rparr>) = []"
  by (simp add: tr_datainst_def)

lemma sim_local_set:
  assumes "un x < length (LOCALS f)"
  shows "sim (mk_config (mk_state s f) [admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_SET x)])
             (mk_config (with_local (mk_state s f) x v) [])"
proof -
  let ?ls = "map tr_val (LOCALS f)"
  let ?i = "tr_moduleinst (frame_MODULE f)"
  have fr: "tr_frame f = \<lparr>f_locs = take (un x) ?ls @ [?ls ! un x] @ drop (Suc (un x)) ?ls, f_inst = ?i\<rparr>"
    using assms id_take_nth_drop[of "un x" ?ls] by (simp add: tr_frame_def)
  have fr': "tr_frame (f\<lparr>LOCALS := list_update_func (LOCALS f) (un x) (\<lambda>_. v)\<rparr>) =
             \<lparr>f_locs = take (un x) ?ls @ [tr_val v] @ drop (Suc (un x)) ?ls, f_inst = ?i\<rparr>"
    using assms by (simp add: tr_frame_def map_list_update_func upd_conv_take_nth_drop)
  have st: "reduce (tr_store s) (tr_frame f) [$C (tr_val v), $Local_set (un x)]
              (tr_store s) (tr_frame (f\<lparr>LOCALS := list_update_func (LOCALS f) (un x) (\<lambda>_. v)\<rparr>)) []"
    unfolding fr fr' by (rule reduce.local_set) (use assms in simp)
  have e: "reduce_trans (tr_store s, tr_frame f, tr_admins [admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_SET x)])
                        (tr_store s, tr_frame f, [$C (tr_val v), $Local_set (un x)])"
    using eval_val[of "tr_store s" "tr_frame f" "[]" v "[$Local_set (un x)]"] by simp
  show ?thesis unfolding sim_def
    using wsim_rt[OF e wsim_step[OF st wsim_refl[OF nls_refl]]] by (simp add: tr_admins_def)
qed

lemma sim_global_set:
  assumes "fun_with_global (mk_state s f) x v z'"
  shows "sim (mk_config (mk_state s f) [admininstr_val v, admininstr_sc5 (admininstr_st5_GLOBAL_SET x)])
             (mk_config z' [])"
proof -
  from assms obtain s' where z': "z' = mk_state s' f"
      "s' = s\<lparr>store_GLOBALS := list_update_func (store_GLOBALS s) (GLOBALS (frame_MODULE f) ! un x)
                                   (\<lambda>gi. gi\<lparr>VALUE := v\<rparr>)\<rparr>"
    by (auto elim: fun_with_global.cases)
  have upd: "supdate_glob (tr_store s) (f_inst (tr_frame f)) (un x) (tr_val v) = tr_store s'"
    using z'(2)
    by (auto simp: supdate_glob_def update_glob_def sglob_ind_def tr_store_def map_list_update_func
                   tr_globalinst_upd nth_map Let_def list_update_beyond not_less)
  have st: "reduce (tr_store s) (tr_frame f) [$C (tr_val v), $Global_set (un x)] (tr_store s') (tr_frame f) []"
    by (rule reduce.global_set[OF upd])
  have e: "reduce_trans (tr_store s, tr_frame f, tr_admins [admininstr_val v, admininstr_sc5 (admininstr_st5_GLOBAL_SET x)])
                        (tr_store s, tr_frame f, [$C (tr_val v), $Global_set (un x)])"
    using eval_val[of "tr_store s" "tr_frame f" "[]" v "[$Global_set (un x)]"] by simp
  show ?thesis unfolding sim_def
    using wsim_rt[OF e wsim_step[OF st wsim_refl[OF nls_refl]]] z'(1) by (simp add: tr_admins_def)
qed

lemma sim_elem_drop:
  assumes "fun_with_elem (mk_state s f) x [] z'"
  shows "sim (mk_config (mk_state s f) [admininstr_sc6 (admininstr_st6_ELEM_DROP x)]) (mk_config z' [])"
proof -
  from assms obtain s' where z': "z' = mk_state s' f"
      "s' = s\<lparr>store_ELEMS := list_update_func (store_ELEMS s) (ELEMS (frame_MODULE f) ! un x)
                                 (\<lambda>ei. ei\<lparr>eleminst_REFS := []\<rparr>)\<rparr>"
    by (auto elim: fun_with_elem.cases)
  let ?a = "inst.elems (f_inst (tr_frame f)) ! un x"
  have upd: "(tr_store s)\<lparr>s.elems := (s.elems (tr_store s))[?a := (fst ((s.elems (tr_store s)) ! ?a), [])]\<rparr> = tr_store s'"
    using z'(2) by (auto simp: tr_store_def map_list_update_func tr_eleminst_drop nth_map list_update_beyond not_less)
  have st: "reduce (tr_store s) (tr_frame f) [$Elem_drop (un x)] (tr_store s') (tr_frame f) []"
    using reduce.elem_drop[of ?a "tr_frame f" "un x" "tr_store s"] upd by simp
  show ?thesis unfolding sim_def
    using wsim_step[OF st wsim_refl[OF nls_refl]] z'(1) by simp
qed

lemma sim_data_drop:
  assumes "fun_with_data (mk_state s f) x [] z'"
  shows "sim (mk_config (mk_state s f) [admininstr_sc7 (admininstr_st7_DATA_DROP x)]) (mk_config z' [])"
proof -
  from assms obtain s' where z': "z' = mk_state s' f"
      "s' = s\<lparr>store_DATAS := list_update_func (store_DATAS s) (DATAS (frame_MODULE f) ! un x)
                                 (\<lambda>di. di\<lparr>datainst_BYTES := []\<rparr>)\<rparr>"
    by (auto elim: fun_with_data.cases)
  let ?a = "inst.datas (f_inst (tr_frame f)) ! un x"
  have upd: "(tr_store s)\<lparr>s.datas := (s.datas (tr_store s))[?a := []]\<rparr> = tr_store s'"
    using z'(2) by (auto simp: tr_store_def map_list_update_func tr_datainst_drop list_update_beyond not_less)
  have st: "reduce (tr_store s) (tr_frame f) [$Data_drop (un x)] (tr_store s') (tr_frame f) []"
    using reduce.data_drop[of ?a "tr_frame f" "un x" "tr_store s"] upd by simp
  show ?thesis unfolding sim_def
    using wsim_step[OF st wsim_refl[OF nls_refl]] z'(1) by simp
qed

section \<open>Tables and growing\<close>

lemma eval_ref_ws:
  "reduce_trans (St, Fr, ($C* ws) @ tr_admin (admininstr_ref r) # es) (St, Fr, ($C* ws) @ Ref (tr_ref r) # es)"
proof (cases r)
  case (ref_REF_NULL rt)
  then show ?thesis using rt_step[OF null_step[of St Fr ws "tr_reftype rt" es] rt_refl] by simp
qed simp_all

lemma nl_ref: "nl (Ref (tr_ref r)) (tr_admin (admininstr_ref r))"
  by (cases r) auto

lemma nls_single_ref: "nls [Ref (tr_ref r)] (tr_admins [admininstr_ref r])"
  by (simp only: tr_admins_Cons tr_admins_Nil list_all2_Cons list_all2_Nil nl_ref simp_thms)

lemma repeat_replicate[simp]: "repeat n x = replicate n x"
  by (induction n) simp_all

lemma tr_tableinst_snd[simp]: "snd (tr_tableinst ti) = map tr_ref (REFS ti)"
  by (simp add: tr_tableinst_def)

lemma stab_ind_tr: "un x < length (TABLES (frame_MODULE f)) \<Longrightarrow>
  stab_ind (f_inst (tr_frame f)) (un x) = Some (TABLES (frame_MODULE f) ! un x)"
  by (simp add: stab_ind_def)

lemma fun_table_E:
  assumes "fun_table (mk_state s f) x ti"
  obtains "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)"
    "un x < length (TABLES (frame_MODULE f))"
    "ti = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
  using assms by (auto elim: fun_table.cases)

lemma sim_table_get:
  assumes "fun_table (mk_state s f) x ti" "un u < 2 ^ 32"
    "es' = (if un u < length (REFS ti) then [admininstr_ref (REFS ti ! un u)] else [admininstr_sc7 admininstr_st7_TRAP])"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc5 (admininstr_st5_TABLE_GET x)])
             (mk_config (mk_state s f) es')"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)"
      "un x < length (TABLES (frame_MODULE f))" "ti = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using assms(1) by (rule fun_table_E)
  let ?a = "TABLES (frame_MODULE f) ! un x"
  have ld: "load_tabs1 (s.tabs (tr_store s)) ?a (nat_of_int (tr_i32 u)) =
              (if un u < length (REFS ti) then Some (tr_ref (REFS ti ! un u)) else None)"
    using x1 assms(2) by (simp add: load_tabs1_def nat_of_int_tr_i32)
  show ?thesis
  proof (cases "un u < length (REFS ti)")
    case True
    have st: "reduce (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 (tr_i32 u)), $Table_get (un x)]
                (tr_store s) (tr_frame f) [Ref (tr_ref (REFS ti ! un u))]"
      by (rule reduce.table_get[OF stab_ind_tr[OF x1(2)]]) (use ld True in simp)
    show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_single_ref]] True assms(3) by simp
  next
    case False
    have st: "reduce (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 (tr_i32 u)), $Table_get (un x)]
                (tr_store s) (tr_frame f) [Trap]"
      by (rule reduce.table_get_fail[OF stab_ind_tr[OF x1(2)]]) (use ld False in simp)
    show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] False assms(3) by simp
  qed
qed

lemma tr_tableinst_set:
  "i < length (REFS ti) \<Longrightarrow>
   tr_tableinst (ti\<lparr>REFS := list_update_func (REFS ti) i (\<lambda>_. r)\<rparr>) =
     (fst (tr_tableinst ti), take i (map tr_ref (REFS ti)) @ [tr_ref r] @ drop (i + 1) (map tr_ref (REFS ti)))"
  by (simp add: tr_tableinst_def list_update_func_conv map_update upd_conv_take_nth_drop take_map drop_map)

lemma sim_table_set:
  assumes "fun_table (mk_state s f) x ti" "un u < 2 ^ 32"
    "un u < length (REFS ti) \<Longrightarrow> fun_with_table (mk_state s f) x (un u) r z'"
    "c' = (if un u < length (REFS ti) then mk_config z' [] else mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_ref r, admininstr_sc5 (admininstr_st5_TABLE_SET x)]) c'"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)"
      "un x < length (TABLES (frame_MODULE f))" "ti = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using assms(1) by (rule fun_table_E)
  let ?a = "TABLES (frame_MODULE f) ! un x"
  have e: "reduce_trans (tr_store s, tr_frame f, tr_admins [i32c u, admininstr_ref r, admininstr_sc5 (admininstr_st5_TABLE_SET x)])
                        (tr_store s, tr_frame f, [$EConstNum (ConstInt32 (tr_i32 u)), Ref (tr_ref r), $Table_set (un x)])"
    using eval_ref_ws[of "tr_store s" "tr_frame f" "[V_num (ConstInt32 (tr_i32 u))]" r "[$Table_set (un x)]"] by simp
  show ?thesis
  proof (cases "un u < length (REFS ti)")
    case True
    obtain s' where z': "z' = mk_state s' f"
        "s' = s\<lparr>store_TABLES := list_update_func (store_TABLES s) ?a
                                   (\<lambda>t. t\<lparr>REFS := list_update_func (REFS t) (un u) (\<lambda>_. r)\<rparr>)\<rparr>"
      using assms(3)[OF True] by (auto elim: fun_with_table.cases)
    have sto: "store_tabs1 (s.tabs (tr_store s)) ?a (nat_of_int (tr_i32 u)) (tr_ref r) = Some (s.tabs (tr_store s'))"
      using x1 assms(2) True z'(2)
      by (simp add: store_tabs1_def store_tab1_def nat_of_int_tr_i32 tr_store_def map_list_update_func
                    tr_tableinst_set upd_conv_take_nth_drop[symmetric] nth_map)
    have st: "reduce (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 (tr_i32 u)), Ref (tr_ref r), $Table_set (un x)]
                (tr_store s') (tr_frame f) []"
      using reduce.table_set[OF stab_ind_tr[OF x1(2)] sto] by (simp add: tr_store_def z'(2))
    show ?thesis unfolding sim_def
      using wsim_rt[OF e wsim_step[OF st wsim_refl[OF nls_refl]]] True assms(4) z'(1) by simp
  next
    case False
    have sto: "store_tabs1 (s.tabs (tr_store s)) ?a (nat_of_int (tr_i32 u)) (tr_ref r) = None"
      using x1 assms(2) False by (simp add: store_tabs1_def store_tab1_def nat_of_int_tr_i32)
    have st: "reduce (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 (tr_i32 u)), Ref (tr_ref r), $Table_set (un x)]
                (tr_store s) (tr_frame f) [Trap]"
      by (rule reduce.table_set_fail[OF stab_ind_tr[OF x1(2)] sto])
    show ?thesis unfolding sim_def
      using wsim_rt[OF e wsim_step[OF st wsim_refl[OF nls_refl]]] False assms(4) by simp
  qed
qed

(* A failed grow pushes -1. *)
lemma minus_one_tr: "tr_i32 (mk_uN (2 ^ 32 - 1)) = int32_minus_one"
proof -
  have m: "(4294967295 :: 32 word) = - 1"
    by (rule word_unat_eq_iff[THEN iffD2]) (simp add: unat_minus_one_word)
  show ?thesis by (simp add: tr_i32_def int32_minus_one_def m)
qed

lemma fun_inv_signed_minus_one: "fun_inv_signed_underscore 32 (0 - 1) v \<Longrightarrow> v = 2 ^ 32 - 1"
  by (drule fun_inv_signed_eq) simp

lemma sim_table_grow_fail:
  assumes "fun_inv_signed_underscore 32 (0 - 1) v"
  shows "sim (mk_config (mk_state s f) [admininstr_ref r, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_GROW x)])
             (mk_config (mk_state s f) [i32c (mk_uN v)])"
proof -
  have v: "v = 2 ^ 32 - 1" by (rule fun_inv_signed_minus_one[OF assms])
  have e: "reduce_trans (tr_store s, tr_frame f, tr_admins [admininstr_ref r, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_GROW x)])
                        (tr_store s, tr_frame f, [Ref (tr_ref r), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Table_grow (un x)])"
    using eval_ref_ws[of "tr_store s" "tr_frame f" "[]" r "[$EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Table_grow (un x)]"]
    by simp
  have st: "reduce (tr_store s) (tr_frame f) [Ref (tr_ref r), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Table_grow (un x)]
              (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 int32_minus_one)]"
    by (rule reduce.table_grow_fail)
  show ?thesis unfolding sim_def
    using wsim_rt[OF e wsim_step[OF st wsim_refl[OF nls_refl]]] v minus_one_tr by simp
qed

lemma sim_memory_grow_fail:
  assumes "fun_inv_signed_underscore 32 (0 - 1) v" "0 < length (MEMS (frame_MODULE f))"
  shows "sim (mk_config (mk_state s f) [i32c (mk_uN n), admininstr_sc6 admininstr_st6_MEMORY_GROW])
             (mk_config (mk_state s f) [i32c (mk_uN v)])"
proof -
  have v: "v = 2 ^ 32 - 1" by (rule fun_inv_signed_minus_one[OF assms(1)])
  have sm: "smem_ind (f_inst (tr_frame f)) = Some (MEMS (frame_MODULE f) ! 0)"
    using assms(2) by (simp add: smem_ind_def neq_Nil_conv split: list.splits)
  have st: "reduce (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_grow]
              (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 int32_minus_one)]"
    by (rule reduce.memory_grow_fail[OF sm HOL.refl HOL.refl])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] v minus_one_tr by simp
qed

lemma option_to_list_case: "option_to_list x = (case x of None \<Rightarrow> [] | Some y \<Rightarrow> [y])"
  by (cases x) simp_all

lemma tr_tableinst_fst[simp]:
  "fst (tr_tableinst ti) = tr_tabletype (tableinst_TYPE ti)"
  by (simp add: tr_tableinst_def)

lemma grow_tab_tr:
  assumes "fun_growtable t n r (Some t')"
  shows "grow_tab (tr_tableinst t) n (tr_ref r) = Some (tr_tableinst t')"
proof -
  from assms obtain i j rt rs where t: "t = \<lparr>tableinst_TYPE = mk_tabletype (mk_limits i j) rt, REFS = rs\<rparr>"
      and mx: "list_all (\<lambda>j2. length rs + n \<le> un j2) (option_to_list j)"
      and t': "t' = \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN (length rs + n)) j) rt, REFS = rs @ repeat n r\<rparr>"
      and w: "wf_tableinst \<lparr>tableinst_TYPE = mk_tabletype (mk_limits (mk_uN (length rs + n)) j) rt, REFS = rs @ repeat n r\<rparr>"
    by (cases rule: fun_growtable.cases) auto
  have "wf_uN 32 (mk_uN (length rs + n))"
    using w by (auto elim!: wf_tableinst.cases wf_tabletype.cases simp: wf_limits_iff)
  then have lt: "length rs + n < 2 ^ 32" by (simp add: wf_uN_iff)
  have pm: "pred_option (\<lambda>max. length rs + n \<le> max) (map_option un j)"
    using mx by (cases j) (simp_all add: option_to_list_case)
  show ?thesis
    using lt pm unfolding t t'
    by (simp add: grow_tab_def tr_tableinst_def tab_t_lim_def tab_t_reftype_def tab_max_def Let_def)
qed

lemma fun_with_tableinst_E:
  assumes "fun_with_tableinst (mk_state s f) x ti z'"
  obtains "z' = mk_state (s\<lparr>store_TABLES := list_update_func (store_TABLES s) (TABLES (frame_MODULE f) ! un x) (\<lambda>_. ti)\<rparr>) f"
  using assms by (auto elim: fun_with_tableinst.cases)

lemma sim_table_grow:
  assumes "fun_table (mk_state s f) x t" "fun_growtable t n r (Some t')"
    "fun_with_tableinst (mk_state s f) x t' z'" "n < 2 ^ 32"
  shows "sim (mk_config (mk_state s f) [admininstr_ref r, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_GROW x)])
             (mk_config z' [i32c (mk_uN (length (REFS t)))])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)"
      "un x < length (TABLES (frame_MODULE f))" "t = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using assms(1) by (rule fun_table_E)
  obtain z: "z' = mk_state (s\<lparr>store_TABLES := list_update_func (store_TABLES s) (TABLES (frame_MODULE f) ! un x) (\<lambda>_. t')\<rparr>) f"
    using assms(3) by (rule fun_with_tableinst_E)
  let ?a = "TABLES (frame_MODULE f) ! un x"
  let ?s' = "s\<lparr>store_TABLES := list_update_func (store_TABLES s) ?a (\<lambda>_. t')\<rparr>"
  have e: "reduce_trans (tr_store s, tr_frame f, tr_admins [admininstr_ref r, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_GROW x)])
                        (tr_store s, tr_frame f, [Ref (tr_ref r), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Table_grow (un x)])"
    using eval_ref_ws[of "tr_store s" "tr_frame f" "[]" r "[$EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Table_grow (un x)]"]
    by simp
  have g: "grow_tab (s.tabs (tr_store s) ! ?a) (nat_of_int (tr_i32 (mk_uN n))) (tr_ref r) = Some (tr_tableinst t')"
    using grow_tab_tr[OF assms(2)] x1 assms(4) by (simp add: nat_of_int_tr_i32)
  have upd: "(tr_store s)\<lparr>s.tabs := (s.tabs (tr_store s))[?a := tr_tableinst t']\<rparr> = tr_store ?s'"
    using x1 by (simp add: tr_store_def map_list_update_func)
  have st: "reduce (tr_store s) (tr_frame f) [Ref (tr_ref r), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Table_grow (un x)]
              (tr_store ?s') (tr_frame f) [$EConstNum (ConstInt32 (int_of_nat (tab_size (s.tabs (tr_store s) ! ?a))))]"
    using reduce.table_grow[OF stab_ind_tr[OF x1(2)] HOL.refl HOL.refl g] upd by simp
  show ?thesis unfolding sim_def
    using wsim_rt[OF e wsim_step[OF st wsim_refl[OF nls_refl]]] x1 z by simp
qed

lemma tr_byte_0[simp]: "tr_byte (mk_byte 0) = zero_byte"
  by (simp add: byte_of_nat_def zero_byte_def uint8_of_nat.abs_eq zero_uint8.abs_eq)

lemma byte_of_nat_0[simp]: "byte_of_nat 0 = zero_byte"
  using tr_byte_0 by simp

lemma nat_int_add[simp]: "nat (int a + int b) = a + b"
  by simp

lemma tr_meminst_eq:
  "tr_meminst mi = (tr_memtype (meminst_TYPE mi), Abs_mem_rep (map tr_byte (BYTES mi)))"
  by (simp add: tr_meminst_def)

(* Growing memory.  WasmCert adds [n] to the minimum page count; SpecTec recomputes
   it from the byte length.  They agree when the byte length is the minimum page
   count in bytes, which SpecTec's store validity guarantees. *)
lemma mem_grow_tr:
  assumes "fun_growmemory mi n (Some mi')"
    "meminst_TYPE mi = PAGE (mk_limits i j)" "length (BYTES mi) = un i * (64 * Ki)"
  shows "mem_grow (tr_meminst mi) n = Some (tr_meminst mi')"
proof -
  from assms(1) obtain i0 j0 bs where m: "mi = \<lparr>meminst_TYPE = PAGE (mk_limits i0 j0), BYTES = bs\<rparr>"
      "list_all (\<lambda>j7. rat_of_nat (length bs) / rat_of_nat (64 * Ki) + rat_of_nat n \<le> rat_of_nat (un j7)) (option_to_list j0)"
      "rat_of_nat (length bs) / rat_of_nat (64 * Ki) + rat_of_nat n \<le> rat_of_nat (2 ^ 16)"
      "mi' = \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN (nat \<lfloor>rat_of_nat (length bs) / rat_of_nat (64 * Ki) + rat_of_nat n\<rfloor>)) j0),
              BYTES = bs @ repeat (n * (64 * Ki)) (mk_byte 0)\<rparr>"
    by (auto elim!: fun_growmemory.cases)
  have ij: "i0 = i" "j0 = j" using assms(2) m(1) by simp_all
  have len: "length bs = un i * 65536" using assms(3) m(1) by (simp add: Ki_def)
  have q: "rat_of_nat (length bs) / rat_of_nat (64 * Ki) + rat_of_nat n = rat_of_nat (un i + n)"
    using len by (simp add: Ki_def)
  have sz: "mem_size (tr_meminst mi) = un i"
    using len m(1) by (simp add: mem_size_def Ki64_def)
  have mx: "pred_option (\<lambda>max. un i + n \<le> max) (mem_max (tr_meminst mi))"
    using m(1,2) q ij by (cases j) (auto simp: mem_max_def tr_meminst_def option_to_list_case)
  have le: "un i + n \<le> 2 ^ 16" using m(3) q by (simp add: of_nat_le_iff[symmetric] del: of_nat_le_iff)
  show ?thesis
    using sz mx le m(1,4) q ij
    by (simp add: mem_grow_def mem_append_def tr_meminst_def Ki64_def Ki_def mem_rep_append.abs_eq
                  map_replicate)
qed

lemma fun_mem_E:
  assumes "fun_mem (mk_state s f) (mk_uN 0) mi"
  obtains "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
    "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
  using assms by (auto elim: fun_mem.cases)

lemma smem_ind_tr: "0 < length (MEMS (frame_MODULE f)) \<Longrightarrow>
  smem_ind (f_inst (tr_frame f)) = Some (MEMS (frame_MODULE f) ! 0)"
  by (simp add: smem_ind_def neq_Nil_conv split: list.splits)

lemma sim_memory_grow:
  assumes "fun_mem (mk_state s f) (mk_uN 0) m" "fun_growmemory m n (Some m')"
    "fun_with_meminst (mk_state s f) (mk_uN 0) m' z'" "n < 2 ^ 32"
    "meminst_TYPE m = PAGE (mk_limits i j)" "length (BYTES m) = un i * (64 * Ki)"
  shows "sim (mk_config (mk_state s f) [i32c (mk_uN n), admininstr_sc6 admininstr_st6_MEMORY_GROW])
             (mk_config z' [i32c (mk_uN (nat \<lfloor>rat_of_nat (length (BYTES m)) / rat_of_nat (64 * Ki)\<rfloor>))])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "m = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using assms(1) by (rule fun_mem_E)
  let ?a = "MEMS (frame_MODULE f) ! 0"
  let ?s' = "s\<lparr>store_MEMS := list_update_func (store_MEMS s) ?a (\<lambda>_. m')\<rparr>"
  have z: "z' = mk_state ?s' f" using assms(3) by (auto elim: fun_with_meminst.cases)
  have g: "mem_grow (s.mems (tr_store s) ! ?a) (nat_of_int (tr_i32 (mk_uN n))) = Some (tr_meminst m')"
    using mem_grow_tr[OF assms(2,5,6)] x1 assms(4) by (simp add: nat_of_int_tr_i32)
  have upd: "(tr_store s)\<lparr>s.mems := (s.mems (tr_store s))[?a := tr_meminst m']\<rparr> = tr_store ?s'"
    using x1 by (simp add: tr_store_def map_list_update_func)
  have sz: "mem_size (s.mems (tr_store s) ! ?a) = nat \<lfloor>rat_of_nat (length (BYTES m)) / rat_of_nat (64 * Ki)\<rfloor>"
    using x1 assms(6) by (simp add: mem_size_def Ki64_def Ki_def)
  have st: "reduce (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_grow]
              (tr_store ?s') (tr_frame f)
              [$EConstNum (ConstInt32 (int_of_nat (nat \<lfloor>rat_of_nat (length (BYTES m)) / rat_of_nat (64 * Ki)\<rfloor>)))]"
    using reduce.memory_grow[OF smem_ind_tr[OF x1(2)] HOL.refl sz g] upd by simp
  show ?thesis unfolding sim_def
    using wsim_step[OF st wsim_refl[OF nls_refl]] z by simp
qed

section \<open>Calls\<close>

termination fun_funcinst by lexicographic_order

lemma tr_functype_inj: "tr_functype a = tr_functype b \<longleftrightarrow> a = b"
  by (metis of_tr_functype)

lemma cl_type_tr[simp]: "cl_type (tr_funcinst fi) = tr_functype (funcinst_TYPE fi)"
  by (cases "CODE fi") (simp add: tr_funcinst_def cl_type_def)

lemma sim_call:
  assumes "un x < length (fun_funcaddr (mk_state s f))"
  shows "sim (mk_config (mk_state s f) [admininstr_sc1 (admininstr_st1_CALL x)])
             (mk_config (mk_state s f) [admininstr_sc7 (CALL_ADDR (fun_funcaddr (mk_state s f) ! un x))])"
proof -
  have st: "reduce (tr_store s) (tr_frame f) [$(Call (un x))] (tr_store s) (tr_frame f)
              [Invoke (FUNCS (frame_MODULE f) ! un x)]"
    using reduce.call[of "tr_store s" "tr_frame f" "un x"] by (simp add: sfunc_ind_def)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma stab_tr:
  assumes "fun_table (mk_state s f) x ti"
  shows "stab (tr_store s) (f_inst (tr_frame f)) (un x) j =
           (if j < length (REFS ti) then Some (tr_ref (REFS ti ! j)) else None)"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)"
      "un x < length (TABLES (frame_MODULE f))" "ti = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using assms by (rule fun_table_E)
  then show ?thesis by (simp add: stab_def stab_cl_ind_def tab_cl_ind_def)
qed

(* A call through a table entry holding a function of the right type. *)
lemma sim_call_indirect:
  assumes "fun_table (mk_state s f) x ti" "un u < 2 ^ 32" "un u < length (REFS ti)"
    "REFS ti ! un u = REF_FUNC_ADDR a" "a < length (store_FUNCS s)"
    "un y < length (TYPES (frame_MODULE f))"
    "funcinst_TYPE (store_FUNCS s ! a) = TYPES (frame_MODULE f) ! un y"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)])
             (mk_config (mk_state s f) [admininstr_sc7 (CALL_ADDR a)])"
proof -
  have sb: "stab (tr_store s) (f_inst (tr_frame f)) (un x) (nat_of_int (tr_i32 u)) = Some (ConstRefFunc a)"
    using stab_tr[OF assms(1)] assms(2-4) by (simp add: nat_of_int_tr_i32)
  have ty: "cl_type (s.funcs (tr_store s) ! a) = stypes (f_inst (tr_frame f)) (un y)"
    using assms(5-7) by (simp add: stypes_def)
  have st: "reduce (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 (tr_i32 u)), $(Call_indirect (un x) (un y))]
              (tr_store s) (tr_frame f) [Invoke a]"
    by (rule reduce.call_indirect_Some[OF HOL.refl sb HOL.refl ty])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

(* A call through a table entry that is out of range, not a function, or of the
   wrong type traps.  Function addresses in tables are in the store (store
   validity). *)
lemma sim_call_indirect_trap:
  assumes "fun_table (mk_state s f) x ti" "un u < 2 ^ 32"
    "un y < length (TYPES (frame_MODULE f))"
    "\<And>a. un u < length (REFS ti) \<Longrightarrow> REFS ti ! un u = REF_FUNC_ADDR a \<Longrightarrow> a < length (store_FUNCS s)"
    "\<not> (un u < length (REFS ti) \<and> (\<exists>a. REFS ti ! un u = REF_FUNC_ADDR a \<and> a < length (store_FUNCS s) \<and>
           funcinst_TYPE (store_FUNCS s ! a) = TYPES (frame_MODULE f) ! un y))"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  let ?sb = "stab (tr_store s) (f_inst (tr_frame f)) (un x) (nat_of_int (tr_i32 u))"
  have sb: "?sb = (if un u < length (REFS ti) then Some (tr_ref (REFS ti ! un u)) else None)"
    using stab_tr[OF assms(1)] assms(2) by (simp add: nat_of_int_tr_i32)
  have c: "(\<exists>i_cl. ?sb = Some (ConstRefFunc i_cl) \<and> stypes (f_inst (tr_frame f)) (un y) \<noteq> cl_type (s.funcs (tr_store s) ! i_cl))
           \<or> \<not> is_some_const_ref_func ?sb"
  proof (cases "un u < length (REFS ti)")
    case True
    show ?thesis
    proof (cases "REFS ti ! un u")
      case (REF_FUNC_ADDR a)
      have "a < length (store_FUNCS s)" using assms(4)[OF True REF_FUNC_ADDR] .
      moreover have "funcinst_TYPE (store_FUNCS s ! a) \<noteq> TYPES (frame_MODULE f) ! un y"
        using assms(5) True REF_FUNC_ADDR calculation by blast
      ultimately show ?thesis
        using sb True REF_FUNC_ADDR assms(3) by (auto simp: stypes_def tr_functype_inj)
    qed (use sb True in \<open>simp_all add: is_some_const_ref_func_def\<close>)
  qed (use sb in \<open>simp add: is_some_const_ref_func_def\<close>)
  have st: "reduce (tr_store s) (tr_frame f) [$EConstNum (ConstInt32 (tr_i32 u)), $(Call_indirect (un x) (un y))]
              (tr_store s) (tr_frame f) [Trap]"
    using c
  proof
    assume "\<exists>i_cl. ?sb = Some (ConstRefFunc i_cl) \<and> stypes (f_inst (tr_frame f)) (un y) \<noteq> cl_type (s.funcs (tr_store s) ! i_cl)"
    then obtain i_cl where "?sb = Some (ConstRefFunc i_cl)"
        "stypes (f_inst (tr_frame f)) (un y) \<noteq> cl_type (s.funcs (tr_store s) ! i_cl)" by blast
    then show ?thesis by (intro reduce.call_indirect_None[where i_cl = i_cl, OF HOL.refl]) simp
  next
    assume "\<not> is_some_const_ref_func ?sb"
    then show ?thesis by (intro reduce.call_indirect_None[where i_cl = 0, OF HOL.refl]) simp
  qed
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

section \<open>Entering a function\<close>

(* WasmCert-Isabelle leaves the zero of its float and vector types unspecified
   ([instance ..] without a definition of [0]), and initialises a function's
   float and vector locals with it ([bitzero]).  SpecTec initialises them with
   +0.0 and the zero vector.  The locale fixes WasmCert's zeros to those bit
   patterns; this is satisfiable, since nothing else constrains them.  (The Rocq
   bridge has the related disagreement [Call_v128].) *)
locale wasm_zeros =
  assumes zero_f32: "(0 :: Wasm_Ast.f32) = Abs_f32 0"
    and zero_f64: "(0 :: Wasm_Ast.f64) = Abs_f64 0"
    and zero_v128: "(0 :: v128) = Abs_v128 0"

lemma (in wasm_zeros) bitzero_default:
  assumes "fun_default_underscore t (Some v)"
  shows "bitzero (tr_valtype t) = Some (tr_val v)"
  using assms
  by (auto elim!: fun_default_underscore.cases fun_fzero.cases
           simp: bitzero_def bitzero_num_def bitzero_vec_def bitzero_ref_def tr_i32_def tr_i64_def
                 tr_f32_def tr_f64_def tr_vec_def tr_v128_def zero_i32_def zero_i64_def
                 zero_f32 zero_f64 zero_v128)

lemma (in wasm_zeros) n_zeros_defaults:
  assumes "list_all2 (\<lambda>d t. fun_default_underscore t d) ds ts" "list_all (\<lambda>d. d \<noteq> None) ds"
  shows "n_zeros (map tr_valtype ts) = Some (map (tr_val \<circ> the) ds)"
  using assms
proof (induction ds ts rule: list_all2_induct)
  case Nil then show ?case by (simp add: n_zeros_def)
next
  case (Cons d ds t ts)
  then obtain v where d: "d = Some v" by auto
  have "fun_default_underscore t (Some v)" using Cons d by simp
  then have "bitzero (tr_valtype t) = Some (tr_val v)" by (rule bitzero_default)
  then show ?case using Cons.IH Cons.prems d by (simp add: n_zeros_def)
qed

lemma tr_funcinst_func:
  "CODE fi = func_FUNC x (map LOCAL ts) body \<Longrightarrow>
   tr_funcinst fi = Func_native (tr_moduleinst (funcinst_MODULE fi)) (tr_functype (funcinst_TYPE fi))
                                (map tr_valtype ts) (tr_instrs body)"
  by (simp add: tr_funcinst_def comp_def)

lemma (in wasm_zeros) sim_call_addr:
  assumes "a < length (store_FUNCS s)"
    "store_FUNCS s ! a = \<lparr>funcinst_TYPE = mk_functype (mk_list t1) (mk_list t2), funcinst_MODULE = mm,
                         CODE = func_FUNC x (map LOCAL ts) body\<rparr>"
    "list_all2 (\<lambda>d t. fun_default_underscore t d) ds ts" "list_all (\<lambda>d. d \<noteq> None) ds"
    "fr' = \<lparr>LOCALS = vs @ map the ds, frame_MODULE = mm\<rparr>"
    "length vs = length t1" "n = length t2"
  shows "sim (mk_config (mk_state s f) (map admininstr_val vs @ [admininstr_sc7 (CALL_ADDR a)]))
             (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n fr'
                [admininstr_sc7 (LABEL_underscore n [] (map admininstr_instr body))])])"
proof -
  have cl: "s.funcs (tr_store s) ! a = Func_native (tr_moduleinst mm) (map tr_valtype t1 _> map tr_valtype t2)
                                          (map tr_valtype ts) (tr_instrs body)"
    using assms(1,2) tr_funcinst_func[of "store_FUNCS s ! a"] by simp
  have z: "n_zeros (map tr_valtype ts) = Some (map (tr_val \<circ> the) ds)"
    by (rule n_zeros_defaults[OF assms(3,4)])
  have st: "reduce (tr_store s) (tr_frame f) (($C* map tr_val vs) @ [Invoke a]) (tr_store s) (tr_frame f)
              [Frame n \<lparr>f_locs = map tr_val vs @ map (tr_val \<circ> the) ds, f_inst = tr_moduleinst mm\<rparr>
                 [Label n [] ($* tr_instrs body)]]"
    by (rule reduce.invoke_native[OF cl HOL.refl _ HOL.refl _ _ z]) (use assms(6,7) in simp_all)
  have fr: "tr_frame fr' = \<lparr>f_locs = map tr_val vs @ map (tr_val \<circ> the) ds, f_inst = tr_moduleinst mm\<rparr>"
    using assms(5) by (simp add: tr_frame_def)
  have e: "reduce_trans (tr_store s, tr_frame f, tr_admins (map admininstr_val vs @ [admininstr_sc7 (CALL_ADDR a)]))
                        (tr_store s, tr_frame f, ($C* map tr_val vs) @ [Invoke a])"
    using eval_vals0[of "tr_store s" "tr_frame f" vs "[Invoke a]"] by simp
  show ?thesis unfolding sim_def
    using wsim_rt[OF e wsim_step[OF st wsim_refl[OF nls_refl]]] fr by (simp add: tr_instrs_def)
qed

end
