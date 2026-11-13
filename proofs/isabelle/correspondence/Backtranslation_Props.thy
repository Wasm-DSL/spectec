(* Properties of the back-translation [Backtranslation] (WasmCert-Isabelle -> SpecTec).
   Isabelle counterpart of ../wasmcert-rocq/backtranslation_props.v.

   - Well-formedness: whatever the back-translation produces is well-formed in
     SpecTec ([of_context_wf], [of_instr_wf]).
   - Round trips on types.

   For vector instructions this holds relative to [vec_dec_wf], which says the
   decoder [vec_dec] only produces well-formed instructions. *)
theory Backtranslation_Props
  imports Backtranslation Typing
begin

section \<open>Numbers\<close>

lemma of_u32_Some[simp]: "(of_u32 n = Some u) = (n < 2 ^ 32 \<and> u = mk_uN n)"
  by (auto simp: of_u32_def guard_def)

lemma of_u8_Some[simp]: "(of_u8 n = Some u) = (n < 2 ^ 8 \<and> u = mk_uN n)"
  by (auto simp: of_u8_def guard_def)

lemma wf_uN_mk[simp]: "wf_uN N (mk_uN n) = (n \<le> 2 ^ N - 1)"
  by (auto elim: wf_uN.cases intro: wf_uN.intros)

lemma wf_uN_lt: "n < 2 ^ N \<Longrightarrow> wf_uN N (mk_uN n)"
  by simp

lemma of_Inn_Some[simp]:
  "(of_Inn t = Some i) = (t = T_i32 \<and> i = Inn_I32 \<or> t = T_i64 \<and> i = Inn_I64)"
  by (cases t) auto

lemma of_Fnn_Some[simp]:
  "(of_Fnn t = Some f) = (t = T_f32 \<and> f = Fnn_F32 \<or> t = T_f64 \<and> f = Fnn_F64)"
  by (cases t) auto

lemma unat_lt_32: "unat (w :: 32 word) < 2 ^ 32"
  using unat_lt2p[of w] by simp

lemma unat_lt_64: "unat (w :: 64 word) < 2 ^ 64"
  using unat_lt2p[of w] by simp

lemma unat_lt_128: "unat (w :: 128 word) < 2 ^ 128"
  using unat_lt2p[of w] by simp

section \<open>Floats\<close>

termination signif by lexicographic_order
termination expon by lexicographic_order

lemma signif_32[simp]: "signif 32 = Some 23" by (simp add: numeral_eq_Suc)
lemma signif_64[simp]: "signif 64 = Some 52" by (simp add: numeral_eq_Suc)
lemma expon_32[simp]: "expon 32 = Some 8" by (simp add: numeral_eq_Suc)
lemma expon_64[simp]: "expon 64 = Some 11" by (simp add: numeral_eq_Suc)

lemma fun_M_iff: "fun_M N m = (signif N = Some m)"
proof
  assume "fun_M N m" then show "signif N = Some m" by (auto elim: fun_M.cases)
next
  assume h: "signif N = Some m"
  then have "fun_M N (the (signif N))" by (intro fun_M.intros) simp
  with h show "fun_M N m" by simp
qed

lemma fun_E_iff: "fun_E N e = (expon N = Some e)"
proof
  assume "fun_E N e" then show "expon N = Some e" by (auto elim: fun_E.cases)
next
  assume h: "expon N = Some e"
  then have "fun_E N (the (expon N))" by (intro fun_E.intros) simp
  with h show "fun_E N e" by simp
qed

(* A decoded magnitude is well-formed for a format with [M] significand and [E]
   exponent bits. *)
lemma fmag_of_bits_wf:
  assumes "signif N = Some M" "expon N = Some E" "2 \<le> E" "fmag_of_bits M E b = Some x"
          "b < 2 ^ (M + E)"
  shows "wf_fNmag N x"
proof -
  define e m where "e = b div 2 ^ M" and "m = b mod 2 ^ M"
  have m: "m < 2 ^ M" by (simp add: m_def)
  show ?thesis
  proof (cases "e = 0")
    case True
    then have "x = SUBNORM m" using assms(4) by (simp add: fmag_of_bits_def Let_def e_def m_def)
    then show ?thesis
      using m assms(1,2)
      by (auto intro!: wf_fNmag.intros(2)[where v_exp = "2 - 2 ^ (E - 1)"] simp: fun_M_iff fun_E_iff)
  next
    case e0: False
    show ?thesis
    proof (cases "e = 2 ^ E - 1")
      case True
      then have "x = (if m = 0 then res_INF else NAN m)"
        using assms(4) e0 by (auto simp: fmag_of_bits_def Let_def e_def m_def)
      then show ?thesis
        using m assms(1)
        by (auto intro: wf_fNmag.intros(3,4) simp: fun_M_iff)
    next
      case eM: False
      then have b: "x = NORM m (int e - int (2 ^ (E - 1) - 1))"
        using assms(4) e0 by (auto simp: fmag_of_bits_def Let_def e_def m_def)
      have "b < 2 ^ E * 2 ^ M"
        using assms(5) by (simp add: power_add mult.commute)
      then have eE: "e < 2 ^ E"
        by (simp add: e_def less_mult_imp_div_less)
      obtain k where k: "E = Suc (Suc k)"
        using assms(3) by (metis add_2_eq_Suc le_Suc_ex)
      define p :: nat where "p = 2 ^ (E - 1)"
      have p: "2 ^ E = 2 * p" "2 \<le> p"
        by (simp_all add: p_def k)
      have ip: "int (p - 1) = int p - 1" using p by simp
      have "1 \<le> e" "e \<le> 2 * p - 2"
        using e0 eE eM p by linarith+
      then have "2 - int p \<le> int e - int (p - 1)" "int e - int (p - 1) \<le> int p - 1"
        using ip p by linarith+
      then show ?thesis
        using m b assms(1,2)
        by (auto intro!: wf_fNmag.intros(1) simp: fun_M_iff fun_E_iff p_def)
    qed
  qed
qed

lemma fN_of_bits_wf:
  assumes "signif N = Some M" "expon N = Some E" "2 \<le> E" "fN_of_bits M E b = Some x"
  shows "wf_fN N x"
  using assms fmag_of_bits_wf[OF assms(1-3) _ mod_less_divisor[of "2 ^ (M + E)" b]]
  by (auto simp: fN_of_bits_def intro: wf_fN.intros split: if_splits)

lemma of_f32_wf: "of_f32 x = Some f \<Longrightarrow> wf_fN 32 f"
  by (rule fN_of_bits_wf[of 32 23 8]) (simp_all add: of_f32_def)

lemma of_f64_wf: "of_f64 x = Some f \<Longrightarrow> wf_fN 64 f"
  by (rule fN_of_bits_wf[of 64 52 11]) (simp_all add: of_f64_def)

section \<open>Size relations\<close>

(* The generated size relations, as equations. *)
lemma fun_sizenn_iff: "fun_sizenn nt n = (isabelle_reference_output_wasm2.size (valtype_numtype nt) = Some n)"
proof
  assume h: "isabelle_reference_output_wasm2.size (valtype_numtype nt) = Some n"
  then have "fun_sizenn nt (the (isabelle_reference_output_wasm2.size (valtype_numtype nt)))"
    by (intro fun_sizenn.intros) simp
  with h show "fun_sizenn nt n" by simp
qed (auto elim: fun_sizenn.cases)

lemma fun_sizenn1_iff: "fun_sizenn1 nt n = (isabelle_reference_output_wasm2.size (valtype_numtype nt) = Some n)"
proof
  assume h: "isabelle_reference_output_wasm2.size (valtype_numtype nt) = Some n"
  then have "fun_sizenn1 nt (the (isabelle_reference_output_wasm2.size (valtype_numtype nt)))"
    by (intro fun_sizenn1.intros) simp
  with h show "fun_sizenn1 nt n" by simp
qed (auto elim: fun_sizenn1.cases)

lemma fun_sizenn2_iff: "fun_sizenn2 nt n = (isabelle_reference_output_wasm2.size (valtype_numtype nt) = Some n)"
proof
  assume h: "isabelle_reference_output_wasm2.size (valtype_numtype nt) = Some n"
  then have "fun_sizenn2 nt (the (isabelle_reference_output_wasm2.size (valtype_numtype nt)))"
    by (intro fun_sizenn2.intros) simp
  with h show "fun_sizenn2 nt n" by simp
qed (auto elim: fun_sizenn2.cases)

fun lsize_of :: "lanetype \<Rightarrow> nat" where
  "lsize_of lanetype_I32 = 32" | "lsize_of lanetype_I64 = 64" | "lsize_of lanetype_F32 = 32"
| "lsize_of lanetype_F64 = 64" | "lsize_of lanetype_I8 = 8" | "lsize_of lanetype_I16 = 16"

lemma fun_lsize_iff: "fun_lsize lt n = (n = lsize_of lt)"
proof
  show "n = lsize_of lt \<Longrightarrow> fun_lsize lt n"
    by (cases lt) (auto intro: fun_lsize.intros[simplified])
qed (auto elim: fun_lsize.cases)

lemma wf_dim_iff: "wf_dim (mk_dim d) = (d = 1 \<or> d = 2 \<or> d = 4 \<or> d = 8 \<or> d = 16)"
  by (auto elim: wf_dim.cases intro: wf_dim.intros)

(* Introduction rules without the generated existential variables. *)
lemma wf_shapeI: "fun_lsize lt n \<Longrightarrow> wf_dim d \<Longrightarrow> n * proj_dim_0 d = 128 \<Longrightarrow> wf_shape (X lt d)"
  by (rule wf_shape.intros) auto

lemma wf_num_FI:
  "fun_sizenn (numtype_Fnn f) n \<Longrightarrow> wf_fN n x \<Longrightarrow> wf_num_underscore (numtype_Fnn f) (mk_num__1 f x)"
  by (rule wf_num_underscore.intros(2)) auto

lemma wf_shape_of_shape: "wf_shape (of_shape sv)"
  by (cases sv; rename_tac x; case_tac x)
     (auto intro!: wf_shapeI[OF fun_lsize_iff[THEN iffD2, OF HOL.refl]] simp: wf_dim_iff)

section \<open>Well-formedness of the back-translation\<close>

lemma those_map_Some: "(those (map f xs) = Some ys) = list_all2 (\<lambda>x y. f x = Some y) xs ys"
  by (induction xs arbitrary: ys) (auto split: option.splits simp: list_all2_Cons1)

lemma those_list_all:
  "those (map f xs) = Some ys \<Longrightarrow> (\<And>x y. x \<in> set xs \<Longrightarrow> f x = Some y \<Longrightarrow> P y) \<Longrightarrow> list_all P ys"
  unfolding those_map_Some
  by (induction rule: list_all2_induct) auto

lemma of_num_wf:
  assumes "of_num v = Some c"
  shows "wf_num_underscore (of_numtype (typeof_num v)) c"
proof (cases v)
  case (ConstFloat32 x)
  then show ?thesis using assms of_f32_wf[of x]
    by (auto simp: typeof_num_def intro!: wf_num_FI[of Fnn_F32 32, simplified] simp: fun_sizenn_iff)
next
  case (ConstFloat64 x)
  then show ?thesis using assms of_f64_wf[of x]
    by (auto simp: typeof_num_def intro!: wf_num_FI[of Fnn_F64 64, simplified] simp: fun_sizenn_iff)
qed (use assms in \<open>auto intro!: wf_num_underscore.intros(1)
          simp: typeof_num_def of_i32_def of_i64_def unat_lt_32[simplified] unat_lt_64[simplified]
                less_Suc_eq_le[symmetric]\<close>)

lemma of_blocktype_wf: "of_blocktype tb = Some bt \<Longrightarrow> wf_blocktype bt"
  by (cases tb) (auto intro: wf_blocktype.intros)

lemma of_memarg_wf: "of_memarg a off = Some m \<Longrightarrow> wf_memarg m"
  by (auto simp: of_memarg_def intro!: wf_memarg.intros split: option.splits)

lemma of_unop_wf: "of_unop t op = Some u \<Longrightarrow> wf_unop_underscore (of_numtype t) u"
  by (cases t; cases op) (auto intro: wf_unop_underscore.intros)

lemma of_binop_wf: "of_binop t op = Some u \<Longrightarrow> wf_binop_underscore (of_numtype t) u"
  by (cases t; cases op) (auto intro: wf_binop_underscore.intros)

lemma of_testop_wf: "of_testop t = Some u \<Longrightarrow> wf_testop_underscore (of_numtype t) u"
  by (cases t) (auto simp: of_testop_def intro: wf_testop_underscore.intros)

lemma of_relop_wf: "of_relop t op = Some u \<Longrightarrow> wf_relop_underscore (of_numtype t) u"
  by (cases t; cases op) (auto intro: wf_relop_underscore.intros)

(* Conversions: introduction rules without the generated size variables. *)
lemma wf_cvt_extendI:
  "fun_sizenn2 (numtype_Inn i2) n2 \<Longrightarrow> fun_sizenn1 (numtype_Inn i1) n1 \<Longrightarrow> n1 < n2 \<Longrightarrow>
   wf_cvtop__Inn_1_Inn_2 i1 i2 (cvtop__Inn_1_Inn_2_EXTEND s)"
  by (rule wf_cvtop__Inn_1_Inn_2.intros(1)) auto

lemma wf_cvt_wrapI:
  "fun_sizenn2 (numtype_Inn i2) n2 \<Longrightarrow> fun_sizenn1 (numtype_Inn i1) n1 \<Longrightarrow> n1 > n2 \<Longrightarrow>
   wf_cvtop__Inn_1_Inn_2 i1 i2 WRAP"
  by (rule wf_cvtop__Inn_1_Inn_2.intros(2)) auto

lemma wf_cvt_reinterpret01I:
  "fun_sizenn2 (numtype_Fnn f2) n \<Longrightarrow> fun_sizenn1 (numtype_Inn i1) n \<Longrightarrow>
   wf_cvtop__Inn_1_Fnn_2 i1 f2 REINTERPRET"
  by (rule wf_cvtop__Inn_1_Fnn_2.intros(2)) auto

lemma wf_cvt_reinterpret10I:
  "fun_sizenn2 (numtype_Inn i2) n \<Longrightarrow> fun_sizenn1 (numtype_Fnn f1) n \<Longrightarrow>
   wf_cvtop__Fnn_1_Inn_2 f1 i2 cvtop__Fnn_1_Inn_2_REINTERPRET"
  by (rule wf_cvtop__Fnn_1_Inn_2.intros(3)) auto

lemma wf_cvt_promoteI:
  "fun_sizenn2 (numtype_Fnn f2) n2 \<Longrightarrow> fun_sizenn1 (numtype_Fnn f1) n1 \<Longrightarrow> n1 < n2 \<Longrightarrow>
   wf_cvtop__Fnn_1_Fnn_2 f1 f2 PROMOTE"
  by (rule wf_cvtop__Fnn_1_Fnn_2.intros(1)) auto

lemma wf_cvt_demoteI:
  "fun_sizenn2 (numtype_Fnn f2) n2 \<Longrightarrow> fun_sizenn1 (numtype_Fnn f1) n1 \<Longrightarrow> n1 > n2 \<Longrightarrow>
   wf_cvtop__Fnn_1_Fnn_2 f1 f2 DEMOTE"
  by (rule wf_cvtop__Fnn_1_Fnn_2.intros(2)) auto

lemmas wf_cvt_intros = wf_cvt_extendI[OF fun_sizenn2_iff[THEN iffD2] fun_sizenn1_iff[THEN iffD2]]
  wf_cvt_wrapI[OF fun_sizenn2_iff[THEN iffD2] fun_sizenn1_iff[THEN iffD2]]
  wf_cvt_reinterpret01I[OF fun_sizenn2_iff[THEN iffD2] fun_sizenn1_iff[THEN iffD2]]
  wf_cvt_reinterpret10I[OF fun_sizenn2_iff[THEN iffD2] fun_sizenn1_iff[THEN iffD2]]
  wf_cvt_promoteI[OF fun_sizenn2_iff[THEN iffD2] fun_sizenn1_iff[THEN iffD2]]
  wf_cvt_demoteI[OF fun_sizenn2_iff[THEN iffD2] fun_sizenn1_iff[THEN iffD2]]
  wf_cvtop__Inn_1_Fnn_2.intros(1) wf_cvtop__Fnn_1_Inn_2.intros(1,2)

(* [CVTOP nt1 nt2 op] needs [wf_cvtop__underscore nt2 nt1 op]. *)
lemma of_cvtop_wf:
  "of_cvtop t2 op t1 s = Some c \<Longrightarrow>
   wf_cvtop__underscore (of_numtype t1) (of_numtype t2) c \<and> of_numtype t2 \<noteq> of_numtype t1"
  by (erule of_cvtop.elims)
     (auto intro!: wf_cvtop__underscore.intros wf_cvt_intros split: option.splits)

lemma wf_loadop_InnI:
  "fun_sizenn (numtype_Inn i) n \<Longrightarrow> wf_sz s \<Longrightarrow> proj_sz_0 s < n \<Longrightarrow> wf_loadop_Inn i (mk_loadop_Inn s x)"
  by (rule wf_loadop_Inn.intros) auto

lemma wf_sz_bits_of_tp[simp]: "wf_sz (mk_sz (bits_of_tp tp))"
  by (cases tp) (auto intro: wf_sz.intros)

lemma wf_sz_bits_of_svi[simp]: "wf_sz (mk_sz (bits_of_svi svi))"
  by (cases svi) (auto intro: wf_sz.intros)

lemma of_pack_Some: "of_pack t tp = Some i \<Longrightarrow>
   numtype_Inn i = of_numtype t \<and> bits_of_tp tp < the (isabelle_reference_output_wasm2.size (valtype_numtype (of_numtype t)))"
  by (cases t) (auto simp: of_pack_def guard_def t_num_length_def split: if_splits)

lemma wf_loadop_Inn_size:
  "nb < the (isabelle_reference_output_wasm2.size (valtype_numtype (numtype_Inn i))) \<Longrightarrow>
   wf_sz (mk_sz nb) \<Longrightarrow> wf_loadop_Inn i (mk_loadop_Inn (mk_sz nb) x)"
  by (cases i; rule wf_loadop_InnI; simp add: fun_sizenn_iff)

lemma of_loadop_wf:
  "of_loadop t lo = Some lo' \<Longrightarrow> list_all (wf_loadop_underscore (of_numtype t)) (option_to_list lo')"
  apply (cases lo)
   apply simp
  apply (clarsimp dest!: of_pack_Some)
  apply (rule wf_loadop_underscore.intros)
   apply (rule wf_loadop_Inn_size)
  by simp_all

lemma of_vloadop_wf: "pred_option (wf_vloadop_underscore V128) (of_vloadop lv)"
  by (cases lv rule: of_vloadop.cases) (auto intro: wf_vloadop_underscore.intros wf_sz.intros)

lemma of_vec_wf: "wf_uN 128 (of_vec c)"
  by (cases c) (simp add: of_v128_def unat_lt_128[simplified] less_Suc_eq_le[symmetric])

lemma list_all3_single[simp]: "list_all3 R [a] [b] [c] = R a b c"
  by (auto elim: list_all3.cases intro: list_all3.intros)

lemma list_all3_Nil[simp]: "list_all3 R [] [] []"
  by (rule list_all3.intros)

lemma wf_STORE_noneI: "wf_memarg m \<Longrightarrow> wf_instr (instr_sc5 (STORE nt None m))"
  by (rule wf_instr.instr_case_56[where Inn_opt = None and var_0_opt = None]) simp_all

lemma wf_STORE_packI:
  "wf_memarg m \<Longrightarrow> wf_sz (mk_sz nb) \<Longrightarrow>
   nb < the (isabelle_reference_output_wasm2.size (valtype_numtype (numtype_Inn i))) \<Longrightarrow>
   wf_instr (instr_sc5 (STORE (numtype_Inn i) (Some (mk_sz nb)) m))"
  by (rule wf_instr.instr_case_56[where Inn_opt = "Some i" and
        var_0_opt = "Some (the (isabelle_reference_output_wasm2.size (valtype_numtype (numtype_Inn i))))"])
     (cases i; simp add: fun_sizenn_iff)+

lemma of_storeop_wf:
  "of_storeop t so = Some so' \<Longrightarrow> wf_memarg m \<Longrightarrow> wf_instr (instr_sc5 (STORE (of_numtype t) so' m))"
  by (cases so; cases t)
     (auto simp: of_pack_def guard_def t_num_length_def split: if_splits
           intro: wf_STORE_noneI wf_STORE_packI[of _ _ Inn_I32, simplified]
                  wf_STORE_packI[of _ _ Inn_I64, simplified])

lemma of_lane_sx_wf:
  "of_lane_sx sv s = Some s' \<Longrightarrow>
   (fun_lanetype (of_shape sv) \<in> set [lanetype_I32, lanetype_I64, lanetype_F32, lanetype_F64]) = (s' = None)"
  by (cases sv; rename_tac x; case_tac x) (auto simp: of_lane_sx_def split: if_splits)

lemma unat_v128_bound: "unat (Rep_v128 v) \<le> 2 ^ 128 - 1"
  using unat_lt_128[of "Rep_v128 v"] by simp

locale vec_dec_wf =
  assumes vec_dec_wf: "vec_dec b = Some i \<Longrightarrow> wf_instr i"

theorem (in vec_dec_wf) of_instr_wf: "of_instr b = Some i \<Longrightarrow> wf_instr i"
proof (induction b arbitrary: i rule: of_instr.induct)
  case (5 tb es)
  then show ?case
    by (auto intro!: wf_instr.instr_case_4 those_list_all[where f = of_instr]
             dest: of_blocktype_wf split: option.splits)
next
  case (6 tb es)
  then show ?case
    by (auto intro!: wf_instr.instr_case_5 those_list_all[where f = of_instr]
             dest: of_blocktype_wf split: option.splits)
next
  case (7 tb es1 es2)
  then show ?case
    by (auto intro!: wf_instr.instr_case_6 those_list_all[where f = of_instr]
             dest: of_blocktype_wf split: option.splits)
next
  case (10 ls l)
  then show ?case
    by (auto intro!: wf_instr.instr_case_9 those_list_all[where f = of_u32] split: option.splits)
next
  case (24 t so a off)
  then show ?case
    by (auto intro: of_storeop_wf of_memarg_wf simp: with_memarg_def split: option.splits)
next case 1 then show ?case by (auto intro!: wf_instr.instr_case_1)
next case 2 then show ?case by (auto intro!: wf_instr.instr_case_0)
next case 3 then show ?case by (auto intro!: wf_instr.instr_case_2)
next case 4 then show ?case by (auto intro!: wf_instr.instr_case_3)
next case 8 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_7)
next case 9 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_8)
next case 11 then show ?case by (auto intro!: wf_instr.instr_case_12)
next case 12 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_10)
next case 13 then show ?case
    by (auto simp: idx2_def intro!: wf_instr.instr_case_11 split: option.splits)
next case 14 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_42)
next case 15 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_43)
next case 16 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_44)
next case 17 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_45)
next case 18 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_46)
next case 19 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_47)
next case 20 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_48)
next case 21 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_49)
next case 22 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_50)
next case 23 then show ?case
    by (auto simp: with_memarg_def intro!: wf_instr.instr_case_55
             dest: of_loadop_wf of_memarg_wf split: option.splits)
next case 25 then show ?case
    by (auto simp: with_memarg_def of_vloadop_wf intro!: wf_instr.instr_case_57 dest: of_memarg_wf)
next case 26 then show ?case
    by (auto simp: with_memarg_def intro!: wf_instr.instr_case_58 dest: of_memarg_wf
             split: option.splits)
next case 27 then show ?case
    by (auto simp: with_memarg_def intro!: wf_instr.instr_case_59 dest: of_memarg_wf)
next case 28 then show ?case
    by (auto simp: with_memarg_def intro!: wf_instr.instr_case_60 dest: of_memarg_wf
             split: option.splits)
next case 29 then show ?case by (auto intro!: wf_instr.instr_case_61)
next case 30 then show ?case by (auto intro!: wf_instr.instr_case_62)
next case 31 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_65)
next case 32 then show ?case by (auto intro!: wf_instr.instr_case_63)
next case 33 then show ?case by (auto intro!: wf_instr.instr_case_64)
next case 34 then show ?case
    by (auto simp: idx2_def intro!: wf_instr.instr_case_53 split: option.splits)
next case 35 then show ?case
    by (auto simp: idx2_def intro!: wf_instr.instr_case_52 split: option.splits)
next case 36 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_51)
next case 37 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_54)
next case 38 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_66)
next case 39 then show ?case by (auto intro!: wf_instr.instr_case_13 dest: of_num_wf)
next case 40 then show ?case by (auto intro!: wf_instr.instr_case_19 simp: of_vec_wf)
next case 41 then show ?case by (auto intro!: wf_instr.instr_case_14 dest: of_unop_wf)
next case 42 then show ?case by (auto intro!: wf_instr.instr_case_15 dest: of_binop_wf)
next case 43 then show ?case by (auto intro!: wf_instr.instr_case_16 dest: of_testop_wf)
next case 44 then show ?case by (auto intro!: wf_instr.instr_case_17 dest: of_relop_wf)
next case 45 then show ?case by (auto intro!: wf_instr.instr_case_18 dest: of_cvtop_wf)
next case 46 then show ?case by (auto intro!: wf_instr.instr_case_39)
next case 47 then show ?case by (auto intro!: wf_instr.instr_case_41)
next case 48 then show ?case by (auto simp: idx1_def intro!: wf_instr.instr_case_40)
next case 49 then show ?case by (auto dest: vec_dec_wf)
next case 50 then show ?case by (auto dest: vec_dec_wf)
next case 51 then show ?case by (auto dest: vec_dec_wf)
next case 52 then show ?case by (auto dest: vec_dec_wf)
next case 53 then show ?case by (auto dest: vec_dec_wf)
next case 54 then show ?case by (auto intro!: wf_instr.instr_case_32 simp: wf_shape_of_shape)
next case 55 then show ?case
    by (auto intro!: wf_instr.instr_case_33 simp: wf_shape_of_shape dest: of_lane_sx_wf
             split: option.splits)
next case 56 then show ?case by (auto intro!: wf_instr.instr_case_34 simp: wf_shape_of_shape)
qed

lemma (in vec_dec_wf) of_instrs_wf: "of_instrs es = Some ins \<Longrightarrow> list_all wf_instr ins"
  unfolding of_instrs_def by (erule those_list_all) (rule of_instr_wf)

section \<open>Types\<close>

lemma of_valtype_num[simp]: "of_valtype (T_num t) = valtype_numtype (of_numtype t)"
  by (cases t) simp_all

lemma of_valtype_ref[simp]: "of_valtype (T_ref t) = valtype_reftype (of_reftype t)"
  by (cases t) simp_all

lemma of_valtype_vec[simp]: "of_valtype (T_vec t) = valtype_V128"
  by (cases t) simp

lemma of_functype_simp[simp]: "of_functype (t1 _> t2) = mk_functype (mk_list (map of_valtype t1)) (mk_list (map of_valtype t2))"
  by (simp add: of_resulttype_def)

lemma of_resulttype_simp[simp]: "of_resulttype ts = mk_list (map of_valtype ts)"
  by (simp add: of_resulttype_def)

lemma Valtype_sub_of: "t1 <t: t2 \<Longrightarrow> Valtype_sub (of_valtype t1) (of_valtype t2)"
  by (auto simp: t_subtyping_def intro: Valtype_sub.intros)

lemma Resulttype_sub_of: "t1s <ts: t2s \<Longrightarrow> Resulttype_sub (mk_list (map of_valtype t1s)) (mk_list (map of_valtype t2s))"
  by (auto simp: Wasm_Subtyping.t_list_subtyping_def list_all2_map1 list_all2_map2 list_all2_lengthD
           intro!: Resulttype_sub.intros elim!: list_all2_mono intro: Valtype_sub_of)

section \<open>Contexts\<close>

lemma of_limits_wf: "of_limits l = Some l' \<Longrightarrow> wf_limits l'"
  by (auto simp: of_limits_def oopt_def intro!: wf_limits.intros split: option.splits)

lemma of_tabletype_wf: "of_tabletype tt = Some tt' \<Longrightarrow> wf_tabletype tt'"
  by (cases tt) (auto intro: wf_tabletype.intros dest: of_limits_wf)

lemma of_memtype_wf: "of_memtype mt = Some mt' \<Longrightarrow> wf_memtype mt'"
  by (auto simp: of_memtype_def intro: wf_memtype.intros dest: of_limits_wf)

lemma of_context_wf: "of_context C = Some C' \<Longrightarrow> wf_context C'"
  by (auto simp: of_context_def split: option.splits
           intro!: wf_context.intros those_list_all[where f = of_tabletype] those_list_all[where f = of_memtype]
           dest: of_tabletype_wf of_memtype_wf)

lemma of_context_sel:
  assumes "of_context C = Some C'"
  shows "context_TYPES C' = map of_functype (types_t C)"
    and "context_FUNCS C' = map of_functype (func_t C)"
    and "context_GLOBALS C' = map of_globaltype (global C)"
    and "those (map of_tabletype (table C)) = Some (context_TABLES C')"
    and "those (map of_memtype (memory C)) = Some (context_MEMS C')"
    and "context_ELEMS C' = map of_reftype (elem C)"
    and "context_DATAS C' = map (\<lambda>_. OK) (data C)"
    and "context_LOCALS C' = map of_valtype (local C)"
    and "LABELS C' = map of_resulttype (label C)"
    and "context_RETURN C' = map_option of_resulttype (return C)"
  using assms by (auto simp: of_context_def split: option.splits)

(* Pushing a label commutes with the back-translation. *)
lemma of_context_label:
  "of_context C = Some C' \<Longrightarrow>
   of_context (C\<lparr>label := ts # label C\<rparr>) =
     Some (append_res_context
       \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
        context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
        LABELS = [mk_list (map of_valtype ts)], context_RETURN = None\<rparr> C')"
  by (auto simp: of_context_def append_res_context_def split: option.splits)

end
