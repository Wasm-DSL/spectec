(* Completeness of the back-translation: on well-formed SpecTec syntax, back-translating
   the forward translation gives the input back.  Isabelle counterpart of the
   completeness half of ../wasmcert-rocq/backtranslation_props.v. *)
theory Completeness
  imports Backtranslation_Props
begin

section \<open>Types\<close>

lemma of_tr_numtype[simp]: "of_numtype (tr_numtype nt) = nt"
  by (cases nt) simp_all

lemma of_tr_reftype[simp]: "of_reftype (tr_reftype rt) = rt"
  by (cases rt) simp_all

lemma of_tr_valtype[simp]: "of_valtype (tr_valtype t) = t"
  by (cases t) simp_all

lemma map_of_tr_valtype[simp]: "map of_valtype (map tr_valtype ts) = ts"
  by (induction ts) simp_all

lemma of_tr_valtype_comp[simp]: "of_valtype \<circ> tr_valtype = id"
  by (rule ext) simp

(* [of_resulttype] is rewritten to [mk_list (map of_valtype _)]. *)
lemma of_tr_resulttype[simp]: "mk_list (map of_valtype (tr_resulttype r)) = r"
  by (cases r) simp

lemma of_tr_resulttype_comp[simp]: "of_resulttype \<circ> tr_resulttype = id"
  by (rule ext) simp

lemma of_tr_return: "map_option of_resulttype (map_option tr_resulttype r) = r"
  by (cases r) simp_all

lemma of_tr_functype[simp]: "of_functype (tr_functype ft) = ft"
  by (cases ft) simp

lemma map_of_tr_functype[simp]: "map of_functype (map tr_functype fts) = fts"
  by (induction fts) simp_all

lemma of_tr_mut[simp]: "of_mut (tr_mut m) = m"
  apply (cases m)
   apply simp
  apply (rename_tac a, case_tac a)
  apply simp
  done

lemma of_tr_globaltype[simp]: "of_globaltype (tr_globaltype g) = g"
  by (cases g) (simp add: of_globaltype_def)

lemma map_of_tr_globaltype[simp]: "map of_globaltype (map tr_globaltype gs) = gs"
  by (induction gs) simp_all

lemma map_of_tr_reftype[simp]: "map of_reftype (map tr_reftype rs) = rs"
  by (induction rs) simp_all

lemma map_of_tr_resulttype[simp]: "map (\<lambda>x. mk_list (map of_valtype (tr_resulttype x))) rs = rs"
  by (induction rs) simp_all

lemma wf_limits_iff: "wf_limits l = (case l of mk_limits mn mx \<Rightarrow> wf_uN 32 mn \<and> pred_option (wf_uN 32) mx)"
  by (cases l) (auto elim: wf_limits.cases intro: wf_limits.intros)

lemma of_u32_un: "wf_uN 32 u \<Longrightarrow> of_u32 (un u) = Some u"
  by (cases u) (auto simp: of_u32_def)

lemma of_tr_limits: "wf_limits l \<Longrightarrow> of_limits (tr_limits l) = Some l"
  by (cases l; rename_tac mn mx; case_tac mx)
     (auto simp: wf_limits_iff of_limits_def oopt_def of_u32_un)

lemma of_tr_tabletype: "wf_tabletype tt \<Longrightarrow> of_tabletype (tr_tabletype tt) = Some tt"
  by (cases tt) (auto simp: of_tr_limits elim: wf_tabletype.cases)

lemma of_tr_memtype: "wf_memtype mt \<Longrightarrow> of_memtype (tr_memtype mt) = Some mt"
  by (cases mt) (auto simp: of_memtype_def of_tr_limits elim: wf_memtype.cases)

lemma those_map_id: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = Some x) \<Longrightarrow> those (map f xs) = Some xs"
  by (induction xs) auto

lemma map_OK[simp]: "map (\<lambda>_. OK) (xs :: res_datatype list) = xs"
  apply (induction xs)
   apply simp
  apply (rename_tac a xs, case_tac a)
  apply simp
  done

lemma of_tr_context:
  assumes "wf_context C"
  shows "of_context (tr_context C) = Some C"
proof -
  have "list_all wf_tabletype (context_TABLES C)" "list_all wf_memtype (context_MEMS C)"
    using assms by (auto elim: wf_context.cases)
  then have T: "those (map (\<lambda>x. of_tabletype (tr_tabletype x)) (context_TABLES C)) = Some (context_TABLES C)"
        and M: "those (map (\<lambda>x. of_memtype (tr_memtype x)) (context_MEMS C)) = Some (context_MEMS C)"
    by (auto intro!: those_map_id simp: list_all_iff of_tr_tabletype of_tr_memtype)
  show ?thesis
    using T M by (cases C) (simp add: of_context_def tr_context_def comp_def of_tr_return)
qed

section \<open>Numbers\<close>

lemma of_tr_i32: "wf_uN 32 u \<Longrightarrow> of_i32 (tr_i32 u) = u"
  by (cases u) (simp add: of_i32_def tr_i32_def Abs_i32_inverse unat_of_nat_eq)

lemma of_tr_i64: "wf_uN 64 u \<Longrightarrow> of_i64 (tr_i64 u) = u"
  by (cases u) (simp add: of_i64_def tr_i64_def Abs_i64_inverse unat_of_nat_eq)

lemma of_tr_vec: "wf_uN 128 u \<Longrightarrow> of_vec (tr_vec u) = u"
  by (cases u) (simp add: of_v128_def tr_vec_def tr_v128_def Abs_v128_inverse unat_of_nat_eq)

section \<open>Floats\<close>

(* Encoding a well-formed magnitude and decoding it gives it back. *)
lemma fmag_roundtrip:
  assumes "signif N = Some M" "expon N = Some E" "2 \<le> E" "wf_fNmag N x"
  shows "fmag_of_bits M E (fmag_bits M E x) = Some x \<and> fmag_bits M E x < 2 ^ (M + E)"
proof -
  obtain k where k: "E = Suc (Suc k)"
    using assms(3) by (metis add_2_eq_Suc le_Suc_ex)
  define bias :: nat where "bias = 2 ^ (E - 1) - 1"
  have p1: "(1::nat) \<le> 2 ^ k" by simp
  have pk: "(2::nat) ^ (E - 1) = 2 * 2 ^ k" "(2::nat) ^ E = 4 * 2 ^ k" by (simp_all add: k)
  have pE1: "(2::nat) ^ E = 2 * 2 ^ (E - 1)" using pk by linarith
  have pE2: "1 \<le> bias" unfolding bias_def using p1 pk by linarith
  have pE3: "2 ^ E - 1 = 2 * bias + 1" unfolding bias_def using p1 pk by linarith
  note pE = pE1 pE2 pE3
  have pME: "(2::nat) ^ (M + E) = 2 ^ E * 2 ^ M"
    by (simp add: power_add mult.commute)
  show ?thesis
    using assms(4)
  proof (cases rule: wf_fNmag.cases)
    case (fNmag_case_0 e1 m0 m e)
    then have m: "m < 2 ^ M" and e: "2 - int (2 ^ (E - 1)) \<le> e" "e \<le> int (2 ^ (E - 1)) - 1"
      using assms(1,2) by (auto simp: fun_M_iff fun_E_iff)
    have ib: "int bias = int (2 ^ (E - 1)) - 1"
      unfolding bias_def using pk p1 by (simp add: of_nat_diff)
    define be where "be = nat (e + int bias)"
    have be: "1 \<le> be" "be \<le> 2 * bias" "int be = e + int bias"
      using e ib unfolding be_def by auto
    have d: "(be * 2 ^ M + m) div 2 ^ M = be" "(be * 2 ^ M + m) mod 2 ^ M = m"
      using m by simp_all
    have b: "be * 2 ^ M + m < (2 ^ E - 1) * 2 ^ M"
    proof -
      have "be + 1 \<le> 2 ^ E - 1" using be pE by linarith
      then have "(be + 1) * 2 ^ M \<le> (2 ^ E - 1) * 2 ^ M" by (rule mult_right_mono) simp
      then show ?thesis using m by (simp add: algebra_simps)
    qed
    have top: "(2 ^ E - 1) * 2 ^ M \<le> (2::nat) ^ (M + E)"
      by (simp add: pME)
    have enc: "fmag_bits M E x = be * 2 ^ M + m"
      using fNmag_case_0 unfolding bias_def be_def by simp
    have ne: "be \<noteq> 0" "be \<noteq> 2 ^ E - 1" using be pE by linarith+
    have dec: "fmag_of_bits M E (be * 2 ^ M + m) = Some (NORM m e)"
      unfolding fmag_of_bits_def Let_def d bias_def[symmetric] using ne be by auto
    show ?thesis
      using enc dec b top fNmag_case_0 by simp
  next
    case (fNmag_case_1 e1 m0 m e)
    then have m: "m < 2 ^ M" using assms(1) by (auto simp: fun_M_iff)
    have "(2::nat) ^ M \<le> 2 ^ (M + E)" by simp
    with m have mb: "m < 2 ^ (M + E)" by (rule less_le_trans)
    show ?thesis
      using fNmag_case_1 m mb by (auto simp: fmag_of_bits_def Let_def)
  next
    case fNmag_case_2
    have "(2 ^ E - 1) * 2 ^ M < (2::nat) ^ (M + E)"
      by (simp add: pME)
    then show ?thesis
      using fNmag_case_2 pE by (auto simp: fmag_of_bits_def Let_def)
  next
    case (fNmag_case_3 m0 m)
    then have m: "1 \<le> m" "m < 2 ^ M" using assms(1) by (auto simp: fun_M_iff)
    have d: "((2 ^ E - 1) * 2 ^ M + m) div 2 ^ M = 2 ^ E - 1" "((2 ^ E - 1) * 2 ^ M + m) mod 2 ^ M = m"
      using m by simp_all
    have "(2 ^ E - 1) * 2 ^ M + m < (2::nat) ^ (M + E)"
    proof -
      have "(2 ^ E - 1) * 2 ^ M + m < (2 ^ E - 1) * 2 ^ M + 2 ^ M" using m by simp
      also have "\<dots> = 2 ^ E * (2::nat) ^ M"
      proof -
        obtain p where "(2::nat) ^ E = Suc p" using not0_implies_Suc[of "(2::nat) ^ E"] by auto
        then show ?thesis by simp
      qed
      finally show ?thesis by (simp add: pME)
    qed
    moreover have "fmag_of_bits M E ((2 ^ E - 1) * 2 ^ M + m) = Some (NAN m)"
    proof -
      have "(2::nat) ^ E - 1 \<noteq> 0" using pk p1 by linarith
      then show ?thesis unfolding fmag_of_bits_def Let_def d using m by simp
    qed
    ultimately show ?thesis
      using fNmag_case_3 by simp
  qed
qed

lemma fN_roundtrip:
  assumes "signif N = Some M" "expon N = Some E" "2 \<le> E" "wf_fN N x"
  shows "fN_of_bits M E (fN_bits M E x) = Some x \<and> fN_bits M E x < 2 ^ (Suc (M + E))"
  using assms(4)
proof (cases rule: wf_fN.cases)
  case (fN_case_0 y)
  then show ?thesis
    using fmag_roundtrip[OF assms(1-3), of y] by (auto simp: fN_of_bits_def)
next
  case (fN_case_1 y)
  then show ?thesis
    using fmag_roundtrip[OF assms(1-3), of y] by (auto simp: fN_of_bits_def)
qed

lemma of_tr_f32: "wf_fN 32 x \<Longrightarrow> of_f32 (tr_f32 x) = Some x"
  using fN_roundtrip[of 32 23 8 x]
  by (simp add: of_f32_def tr_f32_def Abs_f32_inverse unat_of_nat_eq)

lemma of_tr_f64: "wf_fN 64 x \<Longrightarrow> of_f64 (tr_f64 x) = Some x"
  using fN_roundtrip[of 64 52 11 x]
  by (simp add: of_f64_def tr_f64_def Abs_f64_inverse unat_of_nat_eq)

lemma tr_num0_case: "tr_num (mk_num__0 t x) = (case t of Inn_I32 \<Rightarrow> ConstInt32 (tr_i32 x) | Inn_I64 \<Rightarrow> ConstInt64 (tr_i64 x))"
  by (cases t) simp_all

lemma tr_num1_case: "tr_num (mk_num__1 t x) = (case t of Fnn_F32 \<Rightarrow> ConstFloat32 (tr_f32 x) | Fnn_F64 \<Rightarrow> ConstFloat64 (tr_f64 x))"
  by (cases t) simp_all

lemma valtype_Inn_case: "valtype_Inn t = (case t of Inn_I32 \<Rightarrow> valtype_I32 | Inn_I64 \<Rightarrow> valtype_I64)"
  by (cases t) simp_all

lemma of_tr_num:
  "wf_num_underscore nt c \<Longrightarrow> of_num (tr_num c) = Some c \<and> of_numtype (typeof_num (tr_num c)) = nt"
  by (erule wf_num_underscore.cases)
     (auto simp: typeof_num_def of_tr_i32 of_tr_i64 of_tr_f32 of_tr_f64 fun_sizenn_iff
                 tr_num0_case tr_num1_case valtype_Inn_case numtype_Inn_case numtype_Fnn_case
           split: Inn.splits Fnn.splits)

section \<open>Operators and immediates\<close>

lemma of_tr_u8: "wf_uN 8 u \<Longrightarrow> of_u8 (un u) = Some u"
  by (cases u) (auto simp: of_u8_def)

lemma mk_uN_un[simp]: "mk_uN (un u) = u"
  by (cases u) simp

lemma un_lt_32: "wf_uN 32 u \<Longrightarrow> un u < 4294967296"
  by (cases u) simp

lemma un_lt_8: "wf_uN 8 u \<Longrightarrow> un u < 256"
  by (cases u) simp

lemma vsize_128[simp]: "vsize vt = 128"
  by (cases vt) simp

lemma of_tr_sx[simp]: "of_sx (tr_sx s) = s"
  by (cases s) simp_all

lemma tp_bits_roundtrip: "n = 8 \<or> n = 16 \<or> n = 32 \<Longrightarrow> bits_of_tp (tp_of_bits n) = n"
  by (auto simp: tp_of_bits_def)

lemma svi_bits_roundtrip: "n = 8 \<or> n = 16 \<or> n = 32 \<or> n = 64 \<Longrightarrow> bits_of_svi (svi_of_bits n) = n"
  by (auto simp: svi_of_bits_def)

lemma of_tr_unop:
  "wf_unop_underscore nt op \<Longrightarrow> unop_ext_ok nt op \<Longrightarrow> of_unop (tr_numtype nt) (tr_unop op) = Some op"
  by (erule wf_unop_underscore.cases; rename_tac t x; case_tac t; case_tac x)
     (auto simp: ext_width_ok_def tp_of_bits_def)

lemma of_tr_binop: "wf_binop_underscore nt op \<Longrightarrow> of_binop (tr_numtype nt) (tr_binop op) = Some op"
  by (erule wf_binop_underscore.cases; rename_tac t x; case_tac t; case_tac x) auto

lemma of_tr_relop: "wf_relop_underscore nt op \<Longrightarrow> of_relop (tr_numtype nt) (tr_relop op) = Some op"
  by (erule wf_relop_underscore.cases; rename_tac t x; case_tac t; case_tac x) auto

lemma of_tr_testop: "wf_testop_underscore nt op \<Longrightarrow> of_testop (tr_numtype nt) = Some op"
  by (erule wf_testop_underscore.cases; rename_tac t x; case_tac t; case_tac x) (auto simp: of_testop_def)

lemma of_tr_cvtop:
  "wf_cvtop__underscore nt2 nt1 op \<Longrightarrow>
   of_cvtop (tr_numtype nt1) (fst (tr_cvtop op)) (tr_numtype nt2) (snd (tr_cvtop op)) = Some op"
  by (elim wf_cvtopE wf_cvtop00E wf_cvtop01E wf_cvtop10E wf_cvtop11E fun_sizenn1E fun_sizenn2E)
     (auto simp: numtype_Inn_case numtype_Fnn_case split: Inn.splits Fnn.splits)

lemma of_tr_shape: "wf_shape sh \<Longrightarrow> of_shape (tr_shape sh) = sh"
  by (cases sh, rename_tac lt d, case_tac d, case_tac lt)
     (auto elim!: wf_shapeE simp: fun_lsize_iff wf_dim_iff)

lemma of_tr_lane_sx:
  "(fun_lanetype sh = lanetype_I32 \<or> fun_lanetype sh = lanetype_I64 \<or>
    fun_lanetype sh = lanetype_F32 \<or> fun_lanetype sh = lanetype_F64) = (s = None) \<Longrightarrow>
   of_lane_sx (tr_shape sh) (tr_lane_sx s) = Some s"
  by (cases sh, rename_tac lt d, case_tac lt; case_tac d; cases s) (auto simp: of_lane_sx_def)

lemma of_tr_memarg: "wf_memarg m \<Longrightarrow> of_memarg (tr_align m) (tr_offset m) = Some m"
  by (cases m) (auto elim!: wf_memarg.cases simp: of_memarg_def tr_align_def tr_offset_def of_u32_un)

lemma of_tr_blocktype: "wf_blocktype bt \<Longrightarrow> of_blocktype (tr_blocktype bt) = Some bt"
  by (cases bt) (auto elim!: wf_blocktype.cases simp: of_u32_un un_lt_32 option.map_comp option.map_id)

lemma of_tr_loadop:
  "pred_option (wf_loadop_underscore nt) lo \<Longrightarrow> of_loadop (tr_numtype nt) (tr_loadop lo) = Some lo"
  by (cases lo)
     (auto elim!: wf_loadopE wf_loadop_InnE fun_sizennE wf_szE
           simp: tr_tp_def tp_of_bits_def of_pack_def guard_def t_num_length_def numtype_Inn_case
           split: Inn.splits)

lemma of_tr_storeop:
  "list_all2 (\<lambda>v i. fun_sizenn (numtype_Inn i) v) (option_to_list vo) (option_to_list io) \<Longrightarrow>
   pred_option wf_sz so \<Longrightarrow> (io = None) = (so = None) \<Longrightarrow>
   list_all3 (\<lambda>v i s. nt = numtype_Inn i \<and> proj_sz_0 s < v) (option_to_list vo) (option_to_list io) (option_to_list so) \<Longrightarrow>
   of_storeop (tr_numtype nt) (map_option tr_tp so) = Some so"
  by (cases so; cases io; cases vo)
     (auto elim!: fun_sizennE wf_szE
           simp: tr_tp_def tp_of_bits_def of_pack_def guard_def t_num_length_def numtype_Inn_case
           split: Inn.splits)

lemma of_tr_vloadop: "pred_option (wf_vloadop_underscore vt) lo \<Longrightarrow> of_vloadop (tr_vloadop lo) = lo"
  by (cases lo) (auto elim!: wf_vloadopE wf_szE simp: tpv_of_bits_def svi_of_bits_def)

section \<open>Instructions\<close>

(* Instructions the back-translation reads back exactly: singleton [select]
   annotations and Wasm's sign-extension widths. *)
primrec rt_ok :: "instr \<Rightarrow> bool" and rt_ok7 :: "instr_st7 \<Rightarrow> bool" where
  "rt_ok (instr_sc0 x) = (case x of SELECT (Some ts) \<Rightarrow> length ts = 1 | _ \<Rightarrow> True)"
| "rt_ok (instr_sc1 x) = (case x of UNOP nt op \<Rightarrow> unop_ext_ok nt op | _ \<Rightarrow> True)"
| "rt_ok (instr_sc2 x) = True"
| "rt_ok (instr_sc3 x) = True"
| "rt_ok (instr_sc4 x) = True"
| "rt_ok (instr_sc5 x) = True"
| "rt_ok (instr_sc6 x) = True"
| "rt_ok (instr_sc7 x) = rt_ok7 x"
| "rt_ok7 (IFELSE bt is1 is2) = (list_all rt_ok is1 \<and> list_all rt_ok is2)"
| "rt_ok7 (LOOP bt ins) = list_all rt_ok ins"
| "rt_ok7 (BLOCK bt ins) = list_all rt_ok ins"
| "rt_ok7 (DATA_DROP x) = True"

(* The instructions the translation sends to WasmCert's abstract vector operators. *)
fun vec_instr :: "instr \<Rightarrow> bool" where
  "vec_instr (instr_sc2 _) = True"
| "vec_instr (instr_sc1 (VVUNOP _ _)) = True"
| "vec_instr (instr_sc3 (VSWIZZLE _)) = True"
| "vec_instr (instr_sc3 (VSHUFFLE _ _)) = True"
| "vec_instr (instr_sc3 (VEXTUNOP _ _ _)) = True"
| "vec_instr (instr_sc3 (VEXTBINOP _ _ _)) = True"
| "vec_instr (instr_sc3 (VNARROW _ _ _)) = True"
| "vec_instr (instr_sc3 (VCVTOP _ _ _)) = True"
| "vec_instr _ = False"

(* The vector decoder inverts the vector encoders on well-formed instructions. *)
locale vec_complete =
  assumes vec_dec_complete: "vec_instr i \<Longrightarrow> wf_instr i \<Longrightarrow> of_instr (tr_instr i) = Some i"

theorem (in vec_complete) of_tr_instr: "wf_instr i \<Longrightarrow> rt_ok i \<Longrightarrow> of_instr (tr_instr i) = Some i"
proof (induction rule: wf_instr.induct)
  case (instr_case_3 ts) then show ?case
    by (cases ts) (auto simp: length_Suc_conv)
next
  case (instr_case_4 bt ins)
  then have "those (map (\<lambda>x. of_instr (tr_instr x)) ins) = Some ins"
    by (auto intro!: those_map_id simp: list_all_iff)
  then show ?case using instr_case_4 by (simp add: of_tr_blocktype comp_def)
next
  case (instr_case_5 bt ins)
  then have "those (map (\<lambda>x. of_instr (tr_instr x)) ins) = Some ins"
    by (auto intro!: those_map_id simp: list_all_iff)
  then show ?case using instr_case_5 by (simp add: of_tr_blocktype comp_def)
next
  case (instr_case_6 bt ins1 ins2)
  then have "those (map (\<lambda>x. of_instr (tr_instr x)) ins1) = Some ins1"
            "those (map (\<lambda>x. of_instr (tr_instr x)) ins2) = Some ins2"
    by (auto intro!: those_map_id simp: list_all_iff)
  then show ?case using instr_case_6 by (simp add: of_tr_blocktype comp_def)
next
  case (instr_case_9 ls l)
  then have "those (map (\<lambda>x. of_u32 (un x)) ls) = Some ls"
    by (auto intro!: those_map_id simp: list_all_iff of_u32_un)
  then show ?case using instr_case_9 by (simp add: of_u32_un comp_def)
next
  case (instr_case_13 nt c) then show ?case by (auto dest: of_tr_num)
next
  case (instr_case_14 nt op) then show ?case by (simp add: of_tr_unop)
next
  case (instr_case_15 nt op) then show ?case by (simp add: of_tr_binop)
next
  case (instr_case_16 nt op) then show ?case by (auto dest: of_tr_testop)
next
  case (instr_case_17 nt op) then show ?case by (simp add: of_tr_relop)
next
  case (instr_case_18 nt2 nt1 op) then show ?case by (simp add: of_tr_cvtop)
next
  case (instr_case_19 vt c) then show ?case by (cases vt) (simp add: of_tr_vec)
next
  case instr_case_20 show ?case by (rule vec_dec_complete) (insert instr_case_20, auto intro: wf_instr.intros)
next
  case instr_case_21 show ?case by (rule vec_dec_complete) (insert instr_case_21, auto intro: wf_instr.intros)
next
  case instr_case_22 show ?case by (rule vec_dec_complete) (insert instr_case_22, auto intro: wf_instr.intros)
next
  case instr_case_23 show ?case by (rule vec_dec_complete) (insert instr_case_23, auto intro: wf_instr.intros)
next
  case instr_case_24 show ?case by (rule vec_dec_complete) (insert instr_case_24, auto intro: wf_instr.intros)
next
  case instr_case_25 show ?case by (rule vec_dec_complete) (insert instr_case_25, auto intro: wf_instr.intros)
next
  case instr_case_26 show ?case by (rule vec_dec_complete) (insert instr_case_26, auto intro: wf_instr.intros)
next
  case instr_case_27 show ?case by (rule vec_dec_complete) (insert instr_case_27, auto intro: wf_instr.intros)
next
  case instr_case_28 show ?case by (rule vec_dec_complete) (insert instr_case_28, auto intro: wf_instr.intros)
next
  case instr_case_29 show ?case by (rule vec_dec_complete) (insert instr_case_29, auto intro: wf_instr.intros)
next
  case instr_case_30 show ?case by (rule vec_dec_complete) (insert instr_case_30, auto intro: wf_instr.intros)
next
  case instr_case_31 show ?case by (rule vec_dec_complete) (insert instr_case_31, auto intro: wf_instr.intros)
next
  case instr_case_32 then show ?case by (simp add: of_tr_shape)
next
  case instr_case_33 then show ?case by (simp add: of_tr_shape of_tr_lane_sx of_tr_u8)
next
  case instr_case_34 then show ?case by (simp add: of_tr_shape of_tr_u8)
next
  case instr_case_35 show ?case by (rule vec_dec_complete) (insert instr_case_35, auto intro: wf_instr.intros)
next
  case instr_case_36 show ?case by (rule vec_dec_complete) (insert instr_case_36, auto intro: wf_instr.intros)
next
  case instr_case_37 show ?case by (rule vec_dec_complete) (insert instr_case_37, auto intro: wf_instr.intros)
next
  case instr_case_38 show ?case by (rule vec_dec_complete) (insert instr_case_38, auto intro: wf_instr.intros)
next
  case (instr_case_55 nt lo m) then show ?case
    by (simp add: of_tr_loadop of_tr_memarg with_memarg_def)
next
  case (instr_case_56 vo io so m nt) then show ?case
    using of_tr_storeop[of vo io so nt] of_tr_memarg[of m] by (simp add: with_memarg_def)
next
  case (instr_case_57 vt lo m) then show ?case
    using of_tr_vloadop[of vt lo] of_tr_memarg[of m] by (cases vt) (simp add: with_memarg_def)
next
  case (instr_case_58 s m j vt) then show ?case
    by (cases vt; cases s)
       (auto elim!: wf_szE simp: of_tr_memarg of_tr_u8 with_memarg_def svi_bits_roundtrip)
next
  case (instr_case_59 m vt) then show ?case
    by (cases vt) (simp add: of_tr_memarg with_memarg_def)
next
  case (instr_case_60 s m j vt) then show ?case
    by (cases vt; cases s)
       (auto elim!: wf_szE simp: of_tr_memarg of_tr_u8 with_memarg_def svi_bits_roundtrip)
qed (simp_all add: idx1_def idx2_def of_u32_un un_lt_32)

lemma (in vec_complete) of_tr_instrs:
  "list_all wf_instr ins \<Longrightarrow> list_all rt_ok ins \<Longrightarrow> of_instrs (tr_instrs ins) = Some ins"
  by (auto simp: of_instrs_def tr_instrs_def list_all_iff intro!: those_map_id of_tr_instr)

end
