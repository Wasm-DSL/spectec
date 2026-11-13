(* Soundness of the back-translation: what [Backtranslation] reads back translates
   forward to the WasmCert term it came from.  Isabelle counterpart of the
   [*_sound] lemmas of ../wasmcert-rocq/backtranslation_props.v.

   Everything is exact except at the level of administrative instructions:
   WasmCert-Isabelle's evaluated null [Ref (ConstNull t)] is read back as SpecTec's
   [REF.NULL t], which translates forward to the instruction [$Ref_null t].  So
   [of_admins] and [of_config] are sound up to evaluated nulls ([nl], Reduction.thy).
   WasmCert-Coq has a single null form, so the Rocq lemmas are exact there.

   The holes of the back-translation must invert the holes of the translation
   (locale [back_sound]): [vec_dec] those for vector operators, as in the Rocq
   bridge ([vec_instr_sound]); [of_hostref] [hostref], which the Rocq bridge does
   not need because WasmCert-Coq's external references carry the host address. *)
theory Backtranslation_Sound
  imports Control
begin

(* [vec_dec_wf] (Backtranslation_Props): read-back vector instructions are well-formed. *)
locale back_sound = vec_dec_wf +
  assumes vec_dec_sound: "vec_dec b = Some i \<Longrightarrow> tr_instr i = b"
    and of_hostref_sound: "of_hostref h = Some a \<Longrightarrow> hostref a = h"

section \<open>Lists\<close>

lemma those_map_sound:
  "those (map f xs) = Some ys \<Longrightarrow> (\<And>x y. x \<in> set xs \<Longrightarrow> f x = Some y \<Longrightarrow> g y = x) \<Longrightarrow> map g ys = xs"
  unfolding those_map_Some by (induction rule: list_all2_induct) auto

lemma those_map_rel:
  "those (map f xs) = Some ys \<Longrightarrow> (\<And>x y. x \<in> set xs \<Longrightarrow> f x = Some y \<Longrightarrow> R x (g y)) \<Longrightarrow>
   list_all2 R xs (map g ys)"
  unfolding those_map_Some by (induction rule: list_all2_induct) auto

section \<open>Types\<close>

lemma tr_of_numtype[simp]: "tr_numtype (of_numtype t) = t"
  by (cases t) simp_all

lemma tr_of_reftype[simp]: "tr_reftype (of_reftype t) = t"
  by (cases t) simp_all

lemma tr_of_valtype[simp]: "tr_valtype (of_valtype t) = t"
  by (cases t rule: of_valtype.cases) simp_all

(* [of_resulttype_simp] and [of_functype_simp] (Backtranslation_Props) unfold the
   back-translation of result types to [map of_valtype], so the round trip shows up
   as this composition. *)
lemma tr_valtype_comp_of[simp]: "tr_valtype \<circ> of_valtype = id"
  by (rule ext) simp

lemma tr_of_resulttype[simp]: "tr_resulttype (of_resulttype ts) = ts"
  by simp

lemma tr_of_functype[simp]: "tr_functype (of_functype tf) = tf"
  by (cases tf) simp

lemma tr_of_mut[simp]: "tr_mut (of_mut m) = m"
  by (cases m) simp_all

lemma of_limits_sound: "of_limits l = Some l' \<Longrightarrow> tr_limits l' = l"
  by (cases l) (auto simp: of_limits_def oopt_def split: option.splits)

lemma of_tabletype_sound: "of_tabletype t = Some t' \<Longrightarrow> tr_tabletype t' = t"
  by (cases t) (auto dest: of_limits_sound)

lemma of_memtype_sound: "of_memtype t = Some t' \<Longrightarrow> tr_memtype t' = t"
  by (auto simp: of_memtype_def dest: of_limits_sound)

section \<open>Values\<close>

lemma tr_of_i32[simp]: "tr_i32 (of_i32 i) = i"
  by (simp add: tr_i32_def of_i32_def Rep_i32_inverse)

lemma tr_of_i64[simp]: "tr_i64 (of_i64 i) = i"
  by (simp add: tr_i64_def of_i64_def Rep_i64_inverse)

lemma tr_of_v128[simp]: "tr_v128 (of_v128 v) = v"
  by (simp add: tr_v128_def of_v128_def Rep_v128_inverse)

lemma tr_of_vec[simp]: "tr_vec (of_vec c) = c"
  by (cases c) (simp add: tr_vec_def)

lemma fmag_bits_of_bits: "fmag_of_bits M E b = Some x \<Longrightarrow> fmag_bits M E x = b"
proof -
  assume h: "fmag_of_bits M E b = Some x"
  have b: "b div 2 ^ M * 2 ^ M + b mod 2 ^ M = b" by (rule div_mult_mod_eq)
  show ?thesis
  proof (cases "b div 2 ^ M = 0")
    case True
    then have "b < 2 ^ M" by (simp add: div_eq_0_iff)
    then show ?thesis using h True by (auto simp: fmag_of_bits_def Let_def)
  next
    case False
    show ?thesis
    proof (cases "b div 2 ^ M = 2 ^ E - 1")
      case True
      then show ?thesis using h False b by (auto simp: fmag_of_bits_def Let_def split: if_splits)
    next
      case False': False
      then show ?thesis using h False b by (auto simp: fmag_of_bits_def Let_def)
    qed
  qed
qed

lemma fN_bits_of_bits:
  assumes "fN_of_bits M E b = Some x" "b < 2 ^ Suc (M + E)"
  shows "fN_bits M E x = b"
proof -
  obtain y where y: "fmag_of_bits M E (b mod 2 ^ (M + E)) = Some y"
    and x: "x = (if b div 2 ^ (M + E) = 0 then POS else NEG) y"
    using assms(1) by (auto simp: fN_of_bits_def)
  have fy: "fmag_bits M E y = b mod 2 ^ (M + E)" by (rule fmag_bits_of_bits[OF y])
  have d: "b div 2 ^ (M + E) * 2 ^ (M + E) + b mod 2 ^ (M + E) = b" by (rule div_mult_mod_eq)
  show ?thesis
  proof (cases "b div 2 ^ (M + E) = 0")
    case True
    then show ?thesis using x fy d by simp
  next
    case False
    have "b div 2 ^ (M + E) < 2" using assms(2) by (simp add: div_less_iff_less_mult)
    then have "b div 2 ^ (M + E) = 1" using False by linarith
    then show ?thesis using x fy d False by simp
  qed
qed

lemma tr_of_f32: "of_f32 x = Some y \<Longrightarrow> tr_f32 y = x"
  using fN_bits_of_bits[of 23 8 "unat (Rep_f32 x)" y] unat_lt_32[of "Rep_f32 x"]
  by (simp add: of_f32_def tr_f32_def Rep_f32_inverse)

lemma tr_of_f64: "of_f64 x = Some y \<Longrightarrow> tr_f64 y = x"
  using fN_bits_of_bits[of 52 11 "unat (Rep_f64 x)" y] unat_lt_64[of "Rep_f64 x"]
  by (simp add: of_f64_def tr_f64_def Rep_f64_inverse)

lemma of_num_sound: "of_num c = Some c' \<Longrightarrow> tr_num c' = c"
  by (cases c) (auto dest: tr_of_f32 tr_of_f64)

context back_sound
begin

lemma of_host_sound: "of_host h = Some a \<Longrightarrow> tr_host a = h"
  by (cases h) (auto simp: tr_host_def dest: of_hostref_sound)

lemma of_ref_sound: "of_ref r = Some r' \<Longrightarrow> tr_ref r' = r"
  by (cases r) (auto dest: of_host_sound)

lemma of_val_sound: "of_val v = Some v' \<Longrightarrow> tr_val v' = v"
  by (cases v rule: of_val.cases) (auto dest: of_num_sound of_host_sound)

end

section \<open>Operators\<close>

lemma tr_of_sx[simp]: "tr_sx (of_sx s) = s"
  by (cases s) simp_all

lemma tp_of_bits_tp[simp]: "tp_of_bits (bits_of_tp tp) = tp"
  by (cases tp) (simp_all add: tp_of_bits_def)

lemma svi_of_bits_svi[simp]: "svi_of_bits (bits_of_svi s) = s"
  by (cases s) (simp_all add: svi_of_bits_def)

lemma tr_unop_of_i[simp]: "tr_unop (mk_unop__0 i (of_unop_i u)) = Unop_i u"
  by (cases u) simp_all

lemma tr_unop_of_f[simp]: "tr_unop (mk_unop__1 f (of_unop_f u)) = Unop_f u"
  by (cases u) simp_all

lemma tr_binop_of_i[simp]: "tr_binop (mk_binop__0 i (of_binop_i b)) = Binop_i b"
  by (cases b) simp_all

lemma tr_binop_of_f[simp]: "tr_binop (mk_binop__1 f (of_binop_f b)) = Binop_f b"
  by (cases b) simp_all

lemma tr_relop_of_i[simp]: "tr_relop (mk_relop__0 i (of_relop_i r)) = Relop_i r"
  by (cases r) simp_all

lemma tr_relop_of_f[simp]: "tr_relop (mk_relop__1 f (of_relop_f r)) = Relop_f r"
  by (cases r) simp_all

lemma of_unop_sound: "of_unop t op = Some op' \<Longrightarrow> tr_unop op' = op"
  by (cases op) auto

lemma of_binop_sound: "of_binop t op = Some op' \<Longrightarrow> tr_binop op' = op"
  by (cases op) auto

lemma of_relop_sound: "of_relop t op = Some op' \<Longrightarrow> tr_relop op' = op"
  by (cases op) auto

lemma of_cvtop_sound: "of_cvtop t2 op t1 s = Some c \<Longrightarrow> tr_cvtop c = (op, s)"
  by (induction t2 op t1 s rule: of_cvtop.induct) (auto split: option.splits)

lemma of_memarg_sound: "of_memarg a off = Some m \<Longrightarrow> tr_align m = a \<and> tr_offset m = off"
  by (auto simp: of_memarg_def tr_align_def tr_offset_def split: option.splits)

lemma of_loadop_sound: "of_loadop t lo = Some lo' \<Longrightarrow> tr_loadop lo' = lo"
  by (induction t lo rule: of_loadop.induct) (auto simp: tr_tp_def)

lemma of_storeop_sound: "of_storeop t so = Some so' \<Longrightarrow> map_option tr_tp so' = so"
  by (cases so) (auto simp: tr_tp_def)

lemma tr_of_vloadop[simp]: "tr_vloadop (of_vloadop lv) = lv"
  by (cases lv rule: of_vloadop.cases) (simp_all add: tpv_of_bits_def)

lemma of_blocktype_sound: "of_blocktype tb = Some bt \<Longrightarrow> tr_blocktype bt = tb"
  by (cases tb) (auto simp: option.map_comp comp_def option.map_ident)

lemma tr_of_shape[simp]: "tr_shape (of_shape vs) = vs"
  by (cases vs; rename_tac x; case_tac x) simp_all

lemma of_lane_sx_sound: "of_lane_sx vs s = Some s' \<Longrightarrow> tr_lane_sx s' = s"
  by (cases vs; rename_tac x; case_tac x) (auto simp: of_lane_sx_def split: if_splits)

lemma tr_select_of[simp]: "tr_select (map_option (\<lambda>t. [of_valtype t]) t) = t"
  by (cases t) simp_all

section \<open>Instructions\<close>

theorem (in back_sound) of_instr_sound: "of_instr b = Some i \<Longrightarrow> tr_instr i = b"
proof (induction b arbitrary: i rule: of_instr.induct)
  case (5 tb es)
  then show ?case
    by (auto split: option.splits dest: of_blocktype_sound intro!: those_map_sound[where f = of_instr])
next
  case (6 tb es)
  then show ?case
    by (auto split: option.splits dest: of_blocktype_sound intro!: those_map_sound[where f = of_instr])
next
  case (7 tb es1 es2)
  then show ?case
    by (auto split: option.splits dest: of_blocktype_sound intro!: those_map_sound[where f = of_instr])
next
  case (10 ls l)
  then show ?case by (auto split: option.splits intro!: those_map_sound[where f = of_u32])
next
  case (23 t lo a off)
  then show ?case
    by (auto simp: with_memarg_def split: option.splits dest: of_loadop_sound of_memarg_sound)
next
  case (24 t so a off)
  then show ?case
    by (auto simp: with_memarg_def split: option.splits dest: of_storeop_sound of_memarg_sound)
next case 1 then show ?case by auto
next case 2 then show ?case by auto
next case 3 then show ?case by auto
next case (4 t) then show ?case by auto
next case 8 then show ?case by (auto simp: idx1_def)
next case 9 then show ?case by (auto simp: idx1_def)
next case 11 then show ?case by auto
next case 12 then show ?case by (auto simp: idx1_def)
next case 13 then show ?case by (auto simp: idx2_def split: option.splits)
next case 14 then show ?case by (auto simp: idx1_def)
next case 15 then show ?case by (auto simp: idx1_def)
next case 16 then show ?case by (auto simp: idx1_def)
next case 17 then show ?case by (auto simp: idx1_def)
next case 18 then show ?case by (auto simp: idx1_def)
next case 19 then show ?case by (auto simp: idx1_def)
next case 20 then show ?case by (auto simp: idx1_def)
next case 21 then show ?case by (auto simp: idx1_def)
next case 22 then show ?case by (auto simp: idx1_def)
next case 25 then show ?case by (auto simp: with_memarg_def dest: of_memarg_sound)
next case 26 then show ?case
    by (auto simp: with_memarg_def split: option.splits dest: of_memarg_sound)
next case 27 then show ?case by (auto simp: with_memarg_def dest: of_memarg_sound)
next case 28 then show ?case
    by (auto simp: with_memarg_def split: option.splits dest: of_memarg_sound)
next case 29 then show ?case by auto
next case 30 then show ?case by auto
next case 31 then show ?case by (auto simp: idx1_def)
next case 32 then show ?case by auto
next case 33 then show ?case by auto
next case 34 then show ?case by (auto simp: idx2_def split: option.splits)
next case 35 then show ?case by (auto simp: idx2_def split: option.splits)
next case 36 then show ?case by (auto simp: idx1_def)
next case 37 then show ?case by (auto simp: idx1_def)
next case 38 then show ?case by (auto simp: idx1_def)
next case 39 then show ?case by (auto dest: of_num_sound)
next case 40 then show ?case by auto
next case 41 then show ?case by (auto dest: of_unop_sound)
next case 42 then show ?case by (auto dest: of_binop_sound)
next case (43 t op) then show ?case by (cases op) (auto simp: of_testop_def)
next case 44 then show ?case by (auto dest: of_relop_sound)
next case 45 then show ?case by (auto dest: of_cvtop_sound)
next case 46 then show ?case by auto
next case 47 then show ?case by auto
next case 48 then show ?case by (auto simp: idx1_def)
next case 49 then show ?case by (auto dest: vec_dec_sound)
next case 50 then show ?case by (auto dest: vec_dec_sound)
next case 51 then show ?case by (auto dest: vec_dec_sound)
next case 52 then show ?case by (auto dest: vec_dec_sound)
next case 53 then show ?case by (auto dest: vec_dec_sound)
next case 54 then show ?case by auto
next case 55 then show ?case by (auto split: option.splits dest: of_lane_sx_sound)
next case 56 then show ?case by auto
qed

lemma (in back_sound) of_instrs_sound: "of_instrs es = Some ins \<Longrightarrow> tr_instrs ins = es"
  unfolding of_instrs_def tr_instrs_def by (erule those_map_sound) (rule of_instr_sound)

section \<open>Runtime structures\<close>

lemma tr_of_byte[simp]: "tr_byte (of_byte b) = b"
  unfolding of_byte_def tr_byte.simps byte_of_nat_def by transfer simp

lemma tr_of_local[simp]: "tr_local (of_local t) = t"
  by (simp add: of_local_def)

lemma tr_of_inst[simp]: "tr_moduleinst (of_inst i) = i"
  by (cases i) (simp add: tr_moduleinst_def of_inst_def comp_def)

lemma tr_of_datainst[simp]: "tr_datainst (of_datainst d) = d"
  by (simp add: of_datainst_def tr_datainst_def comp_def)

lemma of_mem_sound: "of_mem m = Some mi \<Longrightarrow> tr_meminst mi = m"
  by (cases m) (auto simp: of_mem_def tr_meminst_def comp_def Rep_mem_rep_inverse dest: of_memtype_sound)

context back_sound
begin

lemma of_cl_sound: "of_cl c = Some fi \<Longrightarrow> tr_funcinst fi = c"
  by (cases c) (auto simp: tr_funcinst_def tr_instrs_def comp_def bind_eq_Some_conv split: option.splits
                     intro!: those_map_sound[where f = of_instr] dest: of_instr_sound)

lemma of_global_sound: "of_global g = Some gi \<Longrightarrow> tr_globalinst gi = g"
  by (cases g) (auto simp: of_global_def tr_globalinst_def dest: of_val_sound)

lemma of_tabinst_sound: "of_tabinst t = Some ti \<Longrightarrow> tr_tableinst ti = t"
  by (cases t) (auto simp: of_tabinst_def tr_tableinst_def split: option.splits
                     dest: of_tabletype_sound of_ref_sound intro!: those_map_sound[where f = of_ref])

lemma of_eleminst_sound: "of_eleminst e = Some ei \<Longrightarrow> tr_eleminst ei = e"
  by (cases e) (auto simp: of_eleminst_def tr_eleminst_def
                     dest: of_ref_sound intro!: those_map_sound[where f = of_ref])

lemma of_store_sound:
  assumes "of_store st = Some st'"
  shows "tr_store st' = st"
proof -
  obtain fs gs ts ms es where
    f: "those (map of_cl (s.funcs st)) = Some fs" and g: "those (map of_global (s.globs st)) = Some gs"
    and t: "those (map of_tabinst (s.tabs st)) = Some ts" and m: "those (map of_mem (s.mems st)) = Some ms"
    and e: "those (map of_eleminst (s.elems st)) = Some es"
    and st': "st' = \<lparr>store_FUNCS = fs, store_GLOBALS = gs, store_TABLES = ts, store_MEMS = ms,
                     store_ELEMS = es, store_DATAS = map of_datainst (s.datas st)\<rparr>"
    using assms by (auto simp: of_store_def split: option.splits)
  have "map tr_funcinst fs = s.funcs st" using f by (rule those_map_sound) (rule of_cl_sound)
  moreover have "map tr_globalinst gs = s.globs st" using g by (rule those_map_sound) (rule of_global_sound)
  moreover have "map tr_tableinst ts = s.tabs st" using t by (rule those_map_sound) (rule of_tabinst_sound)
  moreover have "map tr_meminst ms = s.mems st" using m by (rule those_map_sound) (rule of_mem_sound)
  moreover have "map tr_eleminst es = s.elems st" using e by (rule those_map_sound) (rule of_eleminst_sound)
  moreover have "map tr_datainst (map of_datainst (s.datas st)) = s.datas st" by (simp add: comp_def)
  ultimately show ?thesis using st' by (cases st) (simp add: tr_store_def)
qed

lemma of_frame_sound: "of_frame fr = Some fr' \<Longrightarrow> tr_frame fr' = fr"
  by (cases fr) (auto simp: of_frame_def tr_frame_def dest: of_val_sound intro!: those_map_sound[where f = of_val])

end

section \<open>Administrative instructions and configurations\<close>

lemma of_basic_sound: "of_basic e = Some b \<Longrightarrow> e = Basic b"
  by (cases e) simp_all

lemma of_label_cont_sound:
  assumes "Option.bind (those (map of_basic es0)) of_instrs = Some ins"
    and "\<And>b i. of_instr b = Some i \<Longrightarrow> tr_instr i = b"
  shows "map Basic (tr_instrs ins) = es0"
proof -
  obtain bs where bs: "those (map of_basic es0) = Some bs" and ins: "of_instrs bs = Some ins"
    using assms(1) by (auto simp: bind_eq_Some_conv)
  have "map Basic bs = es0" using bs by (rule those_map_sound) (auto dest: of_basic_sound)
  moreover have "tr_instrs ins = bs"
    using ins unfolding of_instrs_def tr_instrs_def by (rule those_map_sound) (rule assms(2))
  ultimately show ?thesis by simp
qed

(* Sound up to evaluated nulls: [Ref (ConstNull t)] comes back as [$Ref_null t]. *)
theorem (in back_sound) of_admin_sound: "of_admin e = Some a \<Longrightarrow> nl e (tr_admin a)"
proof (induction e arbitrary: a rule: of_admin.induct)
  case (1 b)
  then show ?case by (auto dest: of_instr_sound)
next
  case 2
  then show ?case by auto
next
  case (3 x)
  then show ?case by auto
next
  case (4 n es0 es)
  then obtain ins es' where c: "Option.bind (those (map of_basic es0)) of_instrs = Some ins"
    and e: "those (map of_admin es) = Some es'" and a: "a = admininstr_sc7 (LABEL_underscore n ins es')"
    by (auto split: option.splits)
  have B: "map Basic (tr_instrs ins) = es0" using c of_instr_sound by (rule of_label_cont_sound)
  have L0: "list_all2 nl es (map tr_admin es')" using e by (rule those_map_rel) (rule "4.IH")
  then have L: "nls es (tr_admins es')" by (simp only: tr_admins_def)
  have "nl (Label n es0 es) (Label n es0 (tr_admins es'))" by (rule nl_label[OF L])
  moreover have "tr_admin a = Label n es0 (tr_admins es')" using a B by simp
  ultimately show ?case by simp
next
  case (5 n fr es)
  then obtain fr' es' where f: "of_frame fr = Some fr'"
    and e: "those (map of_admin es) = Some es'" and a: "a = admininstr_sc8 (FRAME_underscore n fr' es')"
    by (auto split: option.splits)
  have F: "tr_frame fr' = fr" using f by (rule of_frame_sound)
  have L0: "list_all2 nl es (map tr_admin es')" using e by (rule those_map_rel) (rule "5.IH")
  then have L: "nls es (tr_admins es')" by (simp only: tr_admins_def)
  have "nl (Frame n fr es) (Frame n fr (tr_admins es'))" by (rule nl_frame[OF L])
  moreover have "tr_admin a = Frame n fr (tr_admins es')" using a F by simp
  ultimately show ?case by simp
next
  case (6 r)
  then obtain r' where r: "of_ref r = Some r'" and a: "a = admininstr_ref r'" by auto
  have tr: "tr_ref r' = r" using r by (rule of_ref_sound)
  show ?case
  proof (cases r')
    case (ref_REF_NULL rt)
    then show ?thesis using a tr by auto
  qed (use a tr in auto)
qed

lemma (in back_sound) of_admins_sound: "of_admins es = Some as' \<Longrightarrow> nls es (tr_admins as')"
  unfolding of_admins_def tr_admins_def by (erule those_map_rel) (rule of_admin_sound)

theorem (in back_sound) of_config_sound:
  assumes "of_config (st, fr, es) = Some c"
  shows "\<exists>st' fr' es'. c = mk_config (mk_state st' fr') es' \<and>
           tr_store st' = st \<and> tr_frame fr' = fr \<and> nls es (tr_admins es')"
  using assms by (auto split: option.splits dest: of_store_sound of_frame_sound of_admins_sound)

section \<open>Well-formedness of what is read back\<close>

lemma of_val_wf: "of_val v = Some v' \<Longrightarrow> wf_val v'"
  by (cases v rule: of_val.cases) (auto intro: wf_val.intros dest: of_num_wf simp: of_vec_wf)

lemma of_inst_wf[simp]: "wf_moduleinst (of_inst i)"
  unfolding of_inst_def by (rule wf_moduleinst.intros) simp

lemma (in back_sound) of_cl_wf: "of_cl c = Some fi \<Longrightarrow> wf_funcinst fi"
  by (cases c) (auto simp: bind_eq_Some_conv split: option.splits
                     intro!: wf_funcinst.intros wf_func.intros those_list_all[where f = of_instr]
                     dest: of_instr_wf)

lemma of_global_wf: "of_global g = Some gi \<Longrightarrow> wf_globalinst gi"
  by (auto simp: of_global_def intro: wf_globalinst.intros dest: of_val_wf)

lemma of_tabinst_wf: "of_tabinst t = Some ti \<Longrightarrow> wf_tableinst ti"
  by (auto simp: of_tabinst_def split: option.splits intro: wf_tableinst.intros dest: of_tabletype_wf)

lemma nat_of_uint8_lt: "nat_of_uint8 b < 256"
proof transfer
  fix w :: "8 word"
  show "unat w < 256" using unat_lt2p[of w] by simp
qed

lemma of_byte_wf[simp]: "wf_byte (of_byte b)"
  unfolding of_byte_def by (rule wf_byte.intros) (use nat_of_uint8_lt[of b] in simp)

lemma of_mem_wf: "of_mem m = Some mi \<Longrightarrow> wf_meminst mi"
  by (auto simp: of_mem_def list_all_iff intro!: wf_meminst.intros dest: of_memtype_wf)

lemma of_datainst_wf[simp]: "wf_datainst (of_datainst d)"
  unfolding of_datainst_def by (rule wf_datainst.intros) (simp add: list_all_iff)

lemma (in back_sound) of_store_wf:
  assumes "of_store st = Some st'"
  shows "wf_store st'"
proof -
  obtain fs gs ts ms es where
    f: "those (map of_cl (s.funcs st)) = Some fs" and g: "those (map of_global (s.globs st)) = Some gs"
    and t: "those (map of_tabinst (s.tabs st)) = Some ts" and m: "those (map of_mem (s.mems st)) = Some ms"
    and st': "st' = \<lparr>store_FUNCS = fs, store_GLOBALS = gs, store_TABLES = ts, store_MEMS = ms,
                     store_ELEMS = es, store_DATAS = map of_datainst (s.datas st)\<rparr>"
    using assms by (auto simp: of_store_def split: option.splits)
  have "list_all wf_funcinst fs" using f by (rule those_list_all) (rule of_cl_wf)
  moreover have "list_all wf_globalinst gs" using g by (rule those_list_all) (rule of_global_wf)
  moreover have "list_all wf_tableinst ts" using t by (rule those_list_all) (rule of_tabinst_wf)
  moreover have "list_all wf_meminst ms" using m by (rule those_list_all) (rule of_mem_wf)
  moreover have "list_all wf_datainst (map of_datainst (s.datas st))" by (simp add: list_all_iff)
  ultimately show ?thesis unfolding st' by (rule wf_store.intros)
qed

lemma of_frame_wf: "of_frame fr = Some fr' \<Longrightarrow> wf_frame fr'"
  by (auto simp: of_frame_def intro!: wf_frame.intros those_list_all[where f = of_val] dest: of_val_wf)

theorem (in back_sound) of_admin_wf: "of_admin e = Some a \<Longrightarrow> wf_admininstr a"
proof (induction e arbitrary: a rule: of_admin.induct)
  case (1 b)
  then show ?case by (auto intro: Control.wf_admininstr_instr dest: of_instr_wf)
next
  case 2
  then show ?case by (auto simp: wf_admininstr_sc_simps)
next
  case (3 x)
  then show ?case by (auto simp: wf_admininstr_sc_simps)
next
  case (4 n es0 es)
  then obtain ins es' where c: "Option.bind (those (map of_basic es0)) of_instrs = Some ins"
    and e: "those (map of_admin es) = Some es'" and a: "a = admininstr_sc7 (LABEL_underscore n ins es')"
    by (auto split: option.splits)
  have "list_all wf_instr ins" using c by (auto simp: bind_eq_Some_conv dest: of_instrs_wf)
  moreover have "wfl es'" using e by (rule those_list_all) (rule "4.IH")
  ultimately show ?case using a by (simp add: wf_label_iff)
next
  case (5 n fr es)
  then obtain fr' es' where f: "of_frame fr = Some fr'"
    and e: "those (map of_admin es) = Some es'" and a: "a = admininstr_sc8 (FRAME_underscore n fr' es')"
    by (auto split: option.splits)
  have "wf_frame fr'" using f by (rule of_frame_wf)
  moreover have "wfl es'" using e by (rule those_list_all) (rule "5.IH")
  ultimately show ?case using a by (simp add: wf_frame_iff)
next
  case (6 r)
  then obtain r' where a: "a = admininstr_ref r'" by auto
  show ?case unfolding a by (cases r') (simp_all add: wf_admininstr_sc_simps)
qed

lemma (in back_sound) of_admins_wf: "of_admins es = Some as' \<Longrightarrow> wfl as'"
  unfolding of_admins_def by (erule those_list_all) (rule of_admin_wf)

theorem (in back_sound) of_config_wf: "of_config (st, fr, es) = Some c \<Longrightarrow> wf_config c"
  by (auto split: option.splits simp: wf_config_simps wf_state_simps
           dest: of_store_wf of_frame_wf of_admins_wf)

(* The Rocq bridge's form ([of_config_sound], backtranslation_props.v), up to
   evaluated nulls. *)
corollary (in back_sound) of_config_sound_wf:
  assumes "of_config (st, fr, es) = Some c"
  shows "\<exists>st' fr' es'. c = mk_config (mk_state st' fr') es' \<and>
           tr_store st' = st \<and> tr_frame fr' = fr \<and> nls es (tr_admins es') \<and> wf_config c"
  using of_config_sound[OF assms] of_config_wf[OF assms] by blast

end
