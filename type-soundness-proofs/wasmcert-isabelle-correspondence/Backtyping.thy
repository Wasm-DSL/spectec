(* Typing reflection: WasmCert-Isabelle's basic-instruction typing ([b_e_typing])
   implies SpecTec's instruction typing ([Instrs_ok]) of the back-translation
   ([Backtranslation]).  Isabelle counterpart of ../wasmcert-rocq/backtyping.v.

   One side condition has no Rocq counterpart:
   - [vzero_ok]: WasmCert-Isabelle's [load_vec_t_bounds] bounds the alignment of
     [v128.load32_zero] and [v128.load64_zero] by 16 bytes (its catch-all case),
     where Wasm and SpecTec bound it by 4 and 8 bytes.  WasmCert therefore types
     over-aligned zero-loads that SpecTec rejects; they are excluded.

   For vector instructions this holds relative to [vec_back]: the decoder
   [vec_dec] only produces well-formed instructions ([vec_dec_wf]) that the
   forward translation maps back ([vec_dec_tr]), and [vec_binop_ok]. *)
theory Backtyping
  imports Backtranslation_Props
begin

section \<open>Side condition\<close>

fun vzero_ok :: "b_e \<Rightarrow> bool" where
  "vzero_ok (Load_vec Load_32_zero a off) = (2 ^ a \<le> (4::nat))"
| "vzero_ok (Load_vec Load_64_zero a off) = (2 ^ a \<le> (8::nat))"
| "vzero_ok (Block tb es) = list_all vzero_ok es"
| "vzero_ok (Loop tb es) = list_all vzero_ok es"
| "vzero_ok (If tb es1 es2) = (list_all vzero_ok es1 \<and> list_all vzero_ok es2)"
| "vzero_ok _ = True"

locale vec_back = vec_binop_ok + vec_dec_wf +
  assumes vec_dec_tr: "vec_dec b = Some i \<Longrightarrow> tr_instr i = b"

section \<open>Helpers\<close>

lemma rat_lane_lt_svi[simp]:
  "(rat_of_nat i < 128 / rat_of_nat (bits_of_svi svi)) = (i < vec_i_num svi)"
  by (cases svi) (simp_all add: vec_i_num_def rat_lt_numeral)

lemma of_instrs_Nil[simp]:"of_instrs [] = Some []"
  by (simp add: of_instrs_def)

lemma of_instrs_single[simp]: "(of_instrs [b] = Some ins) = (\<exists>i. of_instr b = Some i \<and> ins = [i])"
  by (auto simp: of_instrs_def split: option.splits)

lemma of_instrs_append:
  "of_instrs (es1 @ es2) = Some ins \<Longrightarrow>
   \<exists>ins1 ins2. ins = ins1 @ ins2 \<and> of_instrs es1 = Some ins1 \<and> of_instrs es2 = Some ins2"
  by (simp only: of_instrs_def those_map_Some list_all2_append1) blast

lemma those_nth:
  "those (map f xs) = Some ys \<Longrightarrow> i < length xs \<Longrightarrow> f (xs ! i) = Some (ys ! i) \<and> length ys = length xs"
  by (auto simp: those_map_Some list_all2_conv_all_nth)

lemma Instrs_ok_single: "Instr_ok C i ft \<Longrightarrow> wf_context C \<Longrightarrow> wf_instr i \<Longrightarrow> Instrs_ok C [i] ft"
  by (cases ft rule: functype.exhaust, rename_tac a b, case_tac a, case_tac b)
     (auto intro: Instr_ok_Instrs_ok.Instrs_ok__instr)

lemma (in vec_dec_wf) back_single:
  assumes "of_instrs [b] = Some ins" "of_context C = Some C'"
          "\<And>i. of_instr b = Some i \<Longrightarrow> wf_context C' \<Longrightarrow> wf_instr i \<Longrightarrow> Instr_ok C' i ft"
  shows "Instrs_ok C' ins ft"
  using assms of_context_wf of_instr_wf Instrs_ok_single by auto

lemma Resulttype_sub_of_ball:
  "\<forall>i\<in>set is. i < n \<and> ts <ts: L ! i \<Longrightarrow> l \<in> set is \<Longrightarrow>
   Resulttype_sub (mk_list (map of_valtype ts)) (mk_list (map of_valtype (L ! l)))"
  by (blast intro: Resulttype_sub_of)

lemma bits_of_tp_div8[simp]: "bits_of_tp tp div 8 = tp_num_length tp"
  by (cases tp) (simp_all add: tp_num_length_def)

lemma wf_context_iff: "wf_context C = (list_all wf_tabletype (context_TABLES C) \<and> list_all wf_memtype (context_MEMS C))"
  by (cases C) (auto elim: wf_context.cases intro: wf_context.intros)

lemma vectype_V128: "(vt :: vectype) = V128"
  by (cases vt) simp

section \<open>Shapes\<close>

lemma of_shape_lane: "valtype_numtype (shunpack (of_shape sv)) = of_valtype (T_num (vec_lane_t sv))"
  by (cases sv; rename_tac x; case_tac x) (simp_all add: vec_lane_t_def)

lemma of_shape_dim: "proj_dim_0 (fun_dim (of_shape sv)) = vec_num sv \<and> wf_dim (fun_dim (of_shape sv))"
  by (cases sv; rename_tac x; case_tac x)
     (simp_all add: vec_num_def vec_i_num_def vec_f_num_def wf_dim_iff)

lemma of_numtype_lane: "of_numtype (vec_lane_t sv) = shunpack (of_shape sv)"
  by (cases sv; rename_tac x; case_tac x) (simp_all add: vec_lane_t_def)

section \<open>Vector instructions\<close>

(* The [V128]-specific rules, for an arbitrary [vectype] (which is always [V128]). *)
lemma vv_rules:
  "wf_context C \<Longrightarrow> wf_instr (instr_sc1 (VVUNOP vt a)) \<Longrightarrow>
     Instr_ok C (instr_sc1 (VVUNOP vt a)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
  "wf_context C \<Longrightarrow> wf_instr (instr_sc2 (VVBINOP vt b)) \<Longrightarrow>
     Instr_ok C (instr_sc2 (VVBINOP vt b)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
  "wf_context C \<Longrightarrow> wf_instr (instr_sc2 (VVTERNOP vt c)) \<Longrightarrow>
     Instr_ok C (instr_sc2 (VVTERNOP vt c))
       (mk_functype (mk_list [valtype_V128, valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
  "wf_context C \<Longrightarrow> wf_instr (instr_sc2 (VVTESTOP vt d)) \<Longrightarrow>
     Instr_ok C (instr_sc2 (VVTESTOP vt d)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]))"
  by (cases vt; auto intro: Instr_ok_Instrs_ok.intros)+

lemma tr_Unop_vec:
  "tr_instr i = Unop_vec op \<Longrightarrow> wf_context C \<Longrightarrow> wf_instr i \<Longrightarrow>
   Instr_ok C i (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
  by (cases i rule: instr.exhaust; rename_tac x; case_tac x)
     (auto intro: vv_rules Instr_ok_Instrs_ok.vunop Instr_ok_Instrs_ok.vextunop Instr_ok_Instrs_ok.vcvtop)

lemma tr_Ternop_vec:
  "tr_instr i = Ternop_vec op \<Longrightarrow> wf_context C \<Longrightarrow> wf_instr i \<Longrightarrow>
   Instr_ok C i (mk_functype (mk_list [valtype_V128, valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
  by (cases i rule: instr.exhaust; rename_tac x; case_tac x) (auto intro: vv_rules)

lemma tr_Test_vec:
  "tr_instr i = Test_vec op \<Longrightarrow> wf_context C \<Longrightarrow> wf_instr i \<Longrightarrow>
   Instr_ok C i (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]))"
  by (cases i rule: instr.exhaust; rename_tac x; case_tac x)
     (auto intro: vv_rules Instr_ok_Instrs_ok.vtestop Instr_ok_Instrs_ok.vbitmask)

lemma tr_Shift_vec:
  "tr_instr i = Shift_vec op \<Longrightarrow> wf_context C \<Longrightarrow> wf_instr i \<Longrightarrow>
   Instr_ok C i (mk_functype (mk_list [valtype_V128, valtype_I32]) (mk_list [valtype_V128]))"
  by (cases i rule: instr.exhaust; rename_tac x; case_tac x) (auto intro: Instr_ok_Instrs_ok.vshiftop)

lemma vshuffle_back:
  assumes wf: "wf_instr (instr_sc3 (VSHUFFLE sh ls))" and "\<forall>l\<in>set ls. un l < 32" "wf_context C"
  shows "Instr_ok C (instr_sc3 (VSHUFFLE sh ls)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
proof -
  from wf have "sh = mk_ishape (X lanetype_I8 (mk_dim 16))" by (auto elim: wf_VSHUFFLE)
  with assms show ?thesis
    by (auto intro!: Instr_ok_Instrs_ok.vshuffle simp: wf_dim_iff list_all_iff)
qed

lemma (in vec_binop_ok) tr_Binop_vec:
  assumes "tr_instr i = Binop_vec op" "binop_vec_wf op" "wf_context C" "wf_instr i"
  shows "Instr_ok C i (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
proof -
  have sh: "vshuffle_ok i"
    using assms(1,2) binop_vec_wf_tr
    by (cases i rule: instr.exhaust; rename_tac x; case_tac x) auto
  show ?thesis
    using assms sh
    by (cases i rule: instr.exhaust; rename_tac x; case_tac x)
       (auto intro: vv_rules Instr_ok_Instrs_ok.vbinop Instr_ok_Instrs_ok.vrelop
                    Instr_ok_Instrs_ok.vswizzle Instr_ok_Instrs_ok.vextbinop Instr_ok_Instrs_ok.vnarrow
                    vshuffle_back simp: list_all_iff)
qed

section \<open>Context lookups\<close>

lemma of_functype_dom_ran: "of_functype tf = mk_functype (mk_list (map of_valtype (tf.dom tf))) (mk_list (map of_valtype (tf.ran tf)))"
  by (cases tf) simp

lemma tr_of_numtype[simp]: "tr_numtype (of_numtype t) = t"
  by (cases t) simp_all

lemma those_of_u32: "those (map of_u32 xs) = Some ys \<Longrightarrow> ys = map mk_uN xs \<and> list_all (\<lambda>x. x < 2 ^ 32) xs"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma ctx_table_back:
  assumes "of_context C = Some C'" "ti < length (table C)" "table C ! ti = T_tab lm tr"
  shows "\<exists>l'. context_TABLES C' ! ti = mk_tabletype l' (of_reftype tr) \<and>
              wf_tabletype (mk_tabletype l' (of_reftype tr)) \<and> ti < length (context_TABLES C')"
proof -
  obtain z where z: "of_limits lm = Some z" "context_TABLES C' ! ti = mk_tabletype z (of_reftype tr)"
                    "length (context_TABLES C') = length (table C)"
    using those_nth[OF of_context_sel(4)[OF assms(1)] assms(2)] assms(3)
    by (auto split: option.splits)
  then show ?thesis
    using assms(2) of_limits_wf[OF z(1)] by (auto intro: wf_tabletype.intros)
qed

lemma ctx_mem_back:
  assumes "of_context C = Some C'" "1 \<le> length (memory C)"
  shows "0 < length (context_MEMS C') \<and> wf_memtype (context_MEMS C' ! 0)"
  using those_nth[OF of_context_sel(5)[OF assms(1)], of 0] assms(2)
  by (auto dest: of_memtype_wf)

section \<open>Memory instructions\<close>

lemma load_pack_back:
  "0 < length (context_MEMS C) \<Longrightarrow> wf_memtype (context_MEMS C ! 0) \<Longrightarrow>
   2 ^ proj_uN_0 (ALIGN m) \<le> M div 8 \<Longrightarrow> wf_context C \<Longrightarrow>
   wf_instr (instr_sc5 (LOAD (numtype_Inn i) (Some (mk_loadop__0 i (mk_loadop_Inn (mk_sz M) sx))) m)) \<Longrightarrow>
   Instr_ok C (instr_sc5 (LOAD (numtype_Inn i) (Some (mk_loadop__0 i (mk_loadop_Inn (mk_sz M) sx))) m))
     (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_Inn i]))"
  by (rule Instr_ok_Instrs_ok.load_pack) auto

lemma store_pack_back:
  "0 < length (context_MEMS C) \<Longrightarrow> wf_memtype (context_MEMS C ! 0) \<Longrightarrow>
   2 ^ proj_uN_0 (ALIGN m) \<le> M div 8 \<Longrightarrow> wf_context C \<Longrightarrow>
   wf_instr (instr_sc5 (STORE (numtype_Inn i) (Some (mk_sz M)) m)) \<Longrightarrow>
   Instr_ok C (instr_sc5 (STORE (numtype_Inn i) (Some (mk_sz M)) m))
     (mk_functype (mk_list [valtype_I32, valtype_Inn i]) (mk_list []))"
  by (rule Instr_ok_Instrs_ok.store_pack) auto

lemmas pack_back = load_pack_back[where i = Inn_I32, simplified] load_pack_back[where i = Inn_I64, simplified]
  store_pack_back[where i = Inn_I32, simplified] store_pack_back[where i = Inn_I64, simplified]

lemma of_memarg_Some: "of_memarg a off = Some m \<Longrightarrow> m = \<lparr>ALIGN = mk_uN a, OFFSET = mk_uN off\<rparr>"
  by (auto simp: of_memarg_def split: option.splits)

lemma size_of_numtype[simp]:
  "isabelle_reference_output_wasm2.size (valtype_numtype (of_numtype t)) = Some (8 * t_num_length t)"
  by (cases t) (simp_all add: t_num_length_def)

lemma bits_of_svi_facts[simp]:
  "bits_of_svi svi div 8 = vec_i_length svi" "128 div bits_of_svi svi = vec_i_num svi"
  by (cases svi; simp add: vec_i_length_def vec_i_num_def)+

(* Table and memory lookups as conditional rewrite rules. *)
lemma wf_tabletype_iff[simp]: "wf_tabletype (mk_tabletype l r) = wf_limits l"
  by (auto elim: wf_tabletype.cases intro: wf_tabletype.intros)

lemma ctx_tables_length[simp]: "of_context C = Some C' \<Longrightarrow> length (context_TABLES C') = length (table C)"
  by (drule of_context_sel(4)) (auto simp: those_map_Some dest: list_all2_lengthD)

lemma ctx_mems_length[simp]: "of_context C = Some C' \<Longrightarrow> length (context_MEMS C') = length (memory C)"
  by (drule of_context_sel(5)) (auto simp: those_map_Some dest: list_all2_lengthD)

lemma ctx_mems_Nil[simp]: "of_context C = Some C' \<Longrightarrow> (context_MEMS C' = []) = (memory C = [])"
  using ctx_mems_length[of C C'] by (cases "memory C"; cases "context_MEMS C'") simp_all

lemma ctx_tables_Nil[simp]: "of_context C = Some C' \<Longrightarrow> (context_TABLES C' = []) = (table C = [])"
  using ctx_tables_length[of C C'] by (cases "table C"; cases "context_TABLES C'") simp_all

lemma ctx_tables_nth[simp]:
  assumes "of_context C = Some C'" "ti < length (table C)"
  shows "context_TABLES C' ! ti =
           mk_tabletype (the (of_limits (tab_t_lim (table C ! ti)))) (of_reftype (tab_t_reftype (table C ! ti)))"
proof -
  obtain lm tr where t: "table C ! ti = T_tab lm tr" by (cases "table C ! ti")
  show ?thesis
    using those_nth[OF of_context_sel(4)[OF assms(1)] assms(2)] t
    by (auto simp: tab_t_lim_def tab_t_reftype_def split: option.splits)
qed

lemma ctx_tables_wf[simp]:
  assumes "of_context C = Some C'" "ti < length (table C)"
  shows "wf_limits (the (of_limits (tab_t_lim (table C ! ti))))"
proof -
  obtain lm tr where t: "table C ! ti = T_tab lm tr" by (cases "table C ! ti")
  show ?thesis
    using those_nth[OF of_context_sel(4)[OF assms(1)] assms(2)] t
    by (auto simp: tab_t_lim_def dest: of_limits_wf split: option.splits)
qed

lemma ctx_tables_wf':
  "of_context C = Some C' \<Longrightarrow> ti < length (table C) \<Longrightarrow> table C ! ti = T_tab lm tr \<Longrightarrow>
   wf_limits (the (of_limits lm))"
  using ctx_tables_wf[of C C' ti] by (simp add: tab_t_lim_def)

lemma ctx_mems_wf[simp]:
  "of_context C = Some C' \<Longrightarrow> i < length (memory C) \<Longrightarrow> wf_memtype (context_MEMS C' ! i)"
  using those_nth[OF of_context_sel(5)] by (auto dest: of_memtype_wf)

lemma ctx_mem_back1:
  "of_context C = Some C' \<Longrightarrow>
   1 \<le> length (memory C) \<longrightarrow> 0 < length (context_MEMS C') \<and> wf_memtype (context_MEMS C' ! 0)"
  using ctx_mem_back by blast

lemma ctx_table_back1:
  "of_context C = Some C' \<Longrightarrow>
   \<forall>ti. ti < length (table C) \<longrightarrow>
     (\<exists>l'. context_TABLES C' ! ti = mk_tabletype l' (of_reftype (tab_t_reftype (table C ! ti))) \<and>
           wf_tabletype (mk_tabletype l' (of_reftype (tab_t_reftype (table C ! ti)))) \<and>
           ti < length (context_TABLES C'))"
proof (intro allI impI)
  fix ti assume "of_context C = Some C'" "ti < length (table C)"
  moreover obtain lm tr where "table C ! ti = T_tab lm tr" by (cases "table C ! ti")
  ultimately show "\<exists>l'. context_TABLES C' ! ti = mk_tabletype l' (of_reftype (tab_t_reftype (table C ! ti))) \<and>
           wf_tabletype (mk_tabletype l' (of_reftype (tab_t_reftype (table C ! ti)))) \<and>
           ti < length (context_TABLES C')"
    using ctx_table_back by (simp add: tab_t_reftype_def)
qed

lemma select_none_back:
  "wf_context C \<Longrightarrow> wf_instr (instr_sc0 (SELECT None)) \<Longrightarrow> is_num_type t \<or> is_vec_type t \<or> t = T_bot \<Longrightarrow>
   Instr_ok C (instr_sc0 (SELECT None))
     (mk_functype (mk_list [of_valtype t, of_valtype t, valtype_I32]) (mk_list [of_valtype t]))"
  apply (cases t; simp add: is_num_type_def is_vec_type_def)
    apply (rule Instr_ok_Instrs_ok.select_impl[OF Valtype_sub.refl]; auto)
   apply (rule Instr_ok_Instrs_ok.select_impl[OF Valtype_sub.refl, where v_vectype = V128]; simp)
  apply (rule Instr_ok_Instrs_ok.select_impl[where t' = valtype_I32 and v_numtype = I32];
         auto intro: Valtype_sub.bot)
  done

lemma vload_back:
  assumes "of_context C = Some C'" "1 \<le> length (memory C)" "load_vec_t_bounds lv a"
          "vzero_ok (Load_vec lv a off)" "wf_context C'"
          "wf_instr (instr_sc6 (VLOAD V128 (of_vloadop lv) \<lparr>ALIGN = mk_uN a, OFFSET = mk_uN off\<rparr>))"
  shows "Instr_ok C' (instr_sc6 (VLOAD V128 (of_vloadop lv) \<lparr>ALIGN = mk_uN a, OFFSET = mk_uN off\<rparr>))
           (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128]))"
proof -
  have M: "0 < length (context_MEMS C')" "wf_memtype (context_MEMS C' ! 0)"
    using assms(1,2) by (simp_all add: Suc_le_eq)
  show ?thesis
    using assms M
    by (cases lv rule: of_vloadop.cases)
       (auto simp: load_vec_t_bounds_def tp_vec_length_def tp_vec_num_def t_vec_length_def
             intro!: Instr_ok_Instrs_ok.vload_val[where mt = "context_MEMS C' ! 0"]
                     Instr_ok_Instrs_ok.vload_pack[where mt = "context_MEMS C' ! 0"]
                     Instr_ok_Instrs_ok.vload_splat[where mt = "context_MEMS C' ! 0"]
                     Instr_ok_Instrs_ok.vload_zero[where mt = "context_MEMS C' ! 0"])
qed

section \<open>Block types\<close>

lemma blocktype_back:
  assumes C: "of_context C = Some C'" and "tb_tf_t C tb = Some tf" "of_blocktype tb = Some bt"
  shows "Blocktype_ok C' bt (of_functype tf)"
proof (cases tb)
  case (Tbf i)
  with assms show ?thesis
    by (cases tf)
       (auto simp: tb_tf_t_def Let_def of_context_sel(1)[OF C] of_context_wf[OF C]
             intro!: Blocktype_ok.Blocktype_ok__typeidx wf_blocktype.intros split: if_splits)
next
  case (Tbv t)
  have "Blocktype_ok C' (underscore_RESULT (map_option of_valtype t))
          (mk_functype (mk_list []) (mk_list (option_to_list (map_option of_valtype t))))"
    using of_context_wf[OF C] by (intro Blocktype_ok.Blocktype_ok__valtype wf_blocktype.intros)
  with Tbv assms show ?thesis
    by (cases t) (auto simp: tb_tf_t_def)
qed

section \<open>Main theorem\<close>

context vec_back
begin

theorem b_e_typing_back_aux:
  "C \<turnstile> es : tf \<Longrightarrow> of_context C = Some C' \<Longrightarrow> of_instrs es = Some ins \<Longrightarrow> list_all vzero_ok es \<Longrightarrow>
   wf_context C' \<Longrightarrow> list_all wf_instr ins \<Longrightarrow> Instrs_ok C' ins (of_functype tf)"
proof (induction arbitrary: C' ins rule: b_e_typing.induct)
  case const_num then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.const)
next
  case const_vec then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.vconst)
next
  case unop then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.unop)
next
  case binop then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.binop)
next
  case testop then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.testop)
next
  case relop then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.relop)
next
  case ref_null then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.ref_null)
next
  case ref_is_null then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.ref_is_null)
next
  case ref_func then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.ref_func simp: idx1_def of_context_sel)
next
  case unop_vec then show ?case by (auto intro!: Instrs_ok_single tr_Unop_vec dest: vec_dec_tr)
next
  case binop_vec then show ?case by (auto intro!: Instrs_ok_single tr_Binop_vec dest: vec_dec_tr)
next
  case ternop_vec then show ?case by (auto intro!: Instrs_ok_single tr_Ternop_vec dest: vec_dec_tr)
next
  case test_vec then show ?case by (auto intro!: Instrs_ok_single tr_Test_vec dest: vec_dec_tr)
next
  case shift_vec then show ?case by (auto intro!: Instrs_ok_single tr_Shift_vec dest: vec_dec_tr)
next
  case splat_vec then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.vsplat simp: of_numtype_lane)
next
  case extract_vec then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.vextract_lane
             simp: of_numtype_lane of_shape_dim split: option.splits)
next
  case replace_vec then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.vreplace_lane simp: of_numtype_lane of_shape_dim)
next
  case convert then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.cvtop)
next
  case reinterpret then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.cvtop)
next
  case unreachable then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.unreachable)
next
  case nop then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.nop)
next
  case drop then show ?case by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.drop)
next
  case select then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.select_expl select_none_back
                     select_none_back[where t = T_bot, simplified])
next
  case (block C tb tn tm es C' ins)
  from block.prems obtain bt es' where ins: "ins = [instr_sc7 (BLOCK bt es')]"
      and bt: "of_blocktype tb = Some bt" and es': "of_instrs es = Some es'"
    by (auto simp: of_instrs_def split: option.splits)
  have C2: "of_context (C\<lparr>label := [tm] @ label C\<rparr>) =
              Some (append_res_context
                \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                 context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                 LABELS = [mk_list (map of_valtype tm)], context_RETURN = None\<rparr> C')"
    using of_context_label[OF block.prems(1)] by simp
  have body: "Instrs_ok (append_res_context
                \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                 context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                 LABELS = [mk_list (map of_valtype tm)], context_RETURN = None\<rparr> C') es'
              (of_functype (tn _> tm))"
    by (rule block.IH[OF C2 es']) (use block.prems in \<open>auto simp: of_context_wf[OF C2] of_instrs_wf[OF es']\<close>)
  show ?case
    using block.prems body blocktype_back[OF block.prems(1) block.hyps(1) bt] ins
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.block simp: wf_context_iff)
next
  case (loop C tb tn tm es C' ins)
  from loop.prems obtain bt es' where ins: "ins = [instr_sc7 (LOOP bt es')]"
      and bt: "of_blocktype tb = Some bt" and es': "of_instrs es = Some es'"
    by (auto simp: of_instrs_def split: option.splits)
  have C2: "of_context (C\<lparr>label := [tn] @ label C\<rparr>) =
              Some (append_res_context
                \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                 context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                 LABELS = [mk_list (map of_valtype tn)], context_RETURN = None\<rparr> C')"
    using of_context_label[OF loop.prems(1)] by simp
  have body: "Instrs_ok (append_res_context
                \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                 context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                 LABELS = [mk_list (map of_valtype tn)], context_RETURN = None\<rparr> C') es'
              (of_functype (tn _> tm))"
    by (rule loop.IH[OF C2 es']) (use loop.prems in \<open>auto simp: of_context_wf[OF C2] of_instrs_wf[OF es']\<close>)
  show ?case
    using loop.prems body blocktype_back[OF loop.prems(1) loop.hyps(1) bt] ins
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.loop simp: wf_context_iff)
next
  case (if_wasm C tb tn tm es1 es2 C' ins)
  from if_wasm.prems obtain bt es1' es2' where ins: "ins = [instr_sc7 (IFELSE bt es1' es2')]"
      and bt: "of_blocktype tb = Some bt" and es1': "of_instrs es1 = Some es1'"
      and es2': "of_instrs es2 = Some es2'"
    by (auto simp: of_instrs_def split: option.splits)
  have C2: "of_context (C\<lparr>label := [tm] @ label C\<rparr>) =
              Some (append_res_context
                \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                 context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                 LABELS = [mk_list (map of_valtype tm)], context_RETURN = None\<rparr> C')"
    using of_context_label[OF if_wasm.prems(1)] by simp
  have body1: "Instrs_ok (append_res_context
                \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                 context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                 LABELS = [mk_list (map of_valtype tm)], context_RETURN = None\<rparr> C') es1'
              (of_functype (tn _> tm))"
    by (rule if_wasm.IH(1)[OF C2 es1'])
       (use if_wasm.prems in \<open>auto simp: of_context_wf[OF C2] of_instrs_wf[OF es1']\<close>)
  have body2: "Instrs_ok (append_res_context
                \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
                 context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
                 LABELS = [mk_list (map of_valtype tm)], context_RETURN = None\<rparr> C') es2'
              (of_functype (tn _> tm))"
    by (rule if_wasm.IH(2)[OF C2 es2'])
       (use if_wasm.prems in \<open>auto simp: of_context_wf[OF C2] of_instrs_wf[OF es2']\<close>)
  show ?case
    using if_wasm.prems body1 body2 blocktype_back[OF if_wasm.prems(1) if_wasm.hyps(1) bt] ins
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.res_if simp: wf_context_iff)
next
  case br then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.br simp: idx1_def of_context_sel)
next
  case br_if then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.br_if simp: idx1_def of_context_sel)
next
  case br_table then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.br_table intro: Resulttype_sub_of
             simp: of_context_sel list_all_iff dest!: those_of_u32 split: option.splits)
       (blast intro: Resulttype_sub_of)
next
  case return then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.return simp: of_context_sel)
next
  case call then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.call simp: idx1_def of_context_sel of_functype_dom_ran)
next
  case call_indirect then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.call_indirect intro: ctx_tables_wf'
             simp: idx2_def of_context_sel tab_t_reftype_def tab_t_lim_def split: option.splits)
next
  case local_get then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.local_get simp: idx1_def of_context_sel)
next
  case local_set then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.local_set simp: idx1_def of_context_sel)
next
  case local_tee then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.local_tee simp: idx1_def of_context_sel)
next
  case global_get then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.global_get
             simp: idx1_def of_context_sel of_globaltype_def)
next
  case global_set then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.global_set
             simp: idx1_def of_context_sel of_globaltype_def is_mut_def)
next
  case load then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.load_val pack_back
             simp: with_memarg_def load_store_t_bounds_def option_projl_def of_pack_def guard_def
                   t_num_length_def
             elim!: of_loadop.elims dest!: of_memarg_Some
             split: option.splits if_splits)
next
  case store then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.store_val pack_back
             simp: with_memarg_def load_store_t_bounds_def of_pack_def guard_def t_num_length_def
             elim!: of_storeop.elims dest!: of_memarg_Some
             split: option.splits if_splits)
next
  case load_vec then show ?case
    by (auto intro!: Instrs_ok_single vload_back simp: with_memarg_def dest!: of_memarg_Some)
next
  case load_lane_vec then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.vload_lane
             simp: with_memarg_def dest!: of_memarg_Some split: option.splits)
next
  case (store_vec C svop a off C' ins) then show ?case
    by (cases svop)
       (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.vstore Instr_ok_Instrs_ok.vstore_lane
             simp: with_memarg_def store_vec_t_bounds_def t_vec_length_def
             dest!: of_memarg_Some split: option.splits)
next
  case memory_size then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.memory_size)
next
  case memory_grow then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.memory_grow)
next
  case table_set then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.table_set simp: idx1_def)
next
  case table_get then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.table_get simp: idx1_def)
next
  case table_size then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.table_size simp: idx1_def)
next
  case table_grow then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.table_grow simp: idx1_def)
next
  case empty then show ?case
    by (auto intro: Instr_ok_Instrs_ok.empty)
next
  case (composition C es t1s t2s e t3s C' ins)
  from composition.prems(2) obtain ins1 ins2 where ins: "ins = ins1 @ ins2"
      "of_instrs es = Some ins1" "of_instrs [e] = Some ins2"
    by (auto dest: of_instrs_append)
  have 1: "Instrs_ok C' ins1 (mk_functype (mk_list (map of_valtype t1s)) (mk_list (map of_valtype t2s)))"
    using composition.IH(1)[of C' ins1] ins composition.prems by simp
  have 2: "Instrs_ok C' ins2 (mk_functype (mk_list (map of_valtype t2s)) (mk_list (map of_valtype t3s)))"
    using composition.IH(2)[of C' ins2] ins composition.prems by simp
  show ?case
    unfolding ins(1) of_functype_simp
    by (rule Instr_ok_Instrs_ok.seq[OF 1 2]) (use ins composition.prems in simp_all)
next
  case (subsumption C es tf1 tf2 tf1' tf2' C' ins)
  have IH: "Instrs_ok C' ins (mk_functype (mk_list (map of_valtype tf1)) (mk_list (map of_valtype tf2)))"
    using subsumption.IH[of C' ins] subsumption.prems by simp
  from subsumption.hyps(2) obtain ts ts' d r where sub: "tf1' = ts @ d" "tf2' = ts' @ r"
      "ts <ts: ts'" "d <ts: tf1" "tf2 <ts: r"
    by (auto simp: instr_subtyping_def)
  have s1: "Instrs_ok C' ins (mk_functype (mk_list (map of_valtype d)) (mk_list (map of_valtype r)))"
    by (rule Instr_ok_Instrs_ok.sub[OF IH Resulttype_sub_of[OF sub(4)] Resulttype_sub_of[OF sub(5)]])
       (use subsumption.prems in simp_all)
  have s2: "Instrs_ok C' ins (mk_functype (mk_list (map of_valtype ts @ map of_valtype d))
                                          (mk_list (map of_valtype ts @ map of_valtype r)))"
    by (rule Instr_ok_Instrs_ok.Instrs_ok__frame[OF s1]) (use subsumption.prems in simp_all)
  have r1: "Resulttype_sub (mk_list (map of_valtype ts @ map of_valtype d)) (mk_list (map of_valtype ts @ map of_valtype d))"
    using Resulttype_sub_of[OF t_list_subtyping_refl[of "ts @ d"]] by simp
  have r2: "Resulttype_sub (mk_list (map of_valtype ts @ map of_valtype r)) (mk_list (map of_valtype ts' @ map of_valtype r))"
    using Resulttype_sub_of[of "ts @ r" "ts' @ r"] sub(3) t_list_subtyping_refl[of r]
    by (simp add: Wasm_Subtyping.t_list_subtyping_def list_all2_appendI)
  show ?case
    unfolding sub(1,2) of_functype_simp map_append
    by (rule Instr_ok_Instrs_ok.sub[OF s2 r1 r2]) (use subsumption.prems in simp_all)
next
  case memory_init then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.memory_init
             simp: idx1_def of_context_sel)
next
  case memory_copy then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.memory_copy)
next
  case memory_fill then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.memory_fill)
next
  case table_init then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.table_init
             simp: idx2_def of_context_sel split: option.splits)
next
  case table_copy then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.table_copy
             simp: idx2_def split: option.splits)
next
  case table_fill then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.table_fill simp: idx1_def)
next
  case elem_drop then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.elem_drop simp: idx1_def of_context_sel)
next
  case data_drop then show ?case
    by (auto intro!: Instrs_ok_single Instr_ok_Instrs_ok.data_drop simp: idx1_def of_context_sel)
qed

(* WasmCert-typed code with a SpecTec counterpart is SpecTec-typed, in the context
   and at the type it translates to. *)
theorem b_e_typing_back:
  assumes "C \<turnstile> es : tf" "of_context C = Some C'" "of_instrs es = Some ins" "list_all vzero_ok es"
  shows "Instrs_ok C' ins (of_functype tf)"
  using b_e_typing_back_aux[OF assms] of_context_wf[OF assms(2)] of_instrs_wf[OF assms(3)] by simp

end

end
