(* Step_Read: the reduction simulation for SpecTec's state-reading steps
   ([Step_read]).

   [Step_read_sim]: every reading step of a well-formed redex is simulated by
   WasmCert, or is a named disagreement ([Read_exc]), given store validity
   ([state_inv]) and facts about the redex that SpecTec's typing guarantees
   ([redex_ok]). *)
theory Step_Read
  imports Simulation
begin

section \<open>Steps that read the state\<close>

(* Store validity, as far as the simulation of reading steps needs it.  It
   follows from SpecTec's store typing. *)
definition state_inv :: "store \<Rightarrow> frame \<Rightarrow> bool" where
  "state_inv s f \<longleftrightarrow>
     (\<forall>a \<in> set (MEMS (frame_MODULE f)). a < length (store_MEMS s)) \<and>
     (\<forall>a \<in> set (TABLES (frame_MODULE f)). a < length (store_TABLES s)) \<and>
     (\<forall>t \<in> set (store_TABLES s). \<forall>a. REF_FUNC_ADDR a \<in> set (REFS t) \<longrightarrow> a < length (store_FUNCS s)) \<and>
     (\<forall>d \<in> set (store_DATAS s). \<forall>b \<in> set (datainst_BYTES d). proj_byte_0 b < 256)"

(* Facts about the redex that SpecTec's rules leave implicit and its typing
   guarantees. *)
definition redex_ok :: "frame \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "redex_ok f es \<longleftrightarrow>
     (\<forall>i x y. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)] \<longrightarrow>
        un x < length (TABLES (frame_MODULE f)) \<and> un y < length (TYPES (frame_MODULE f))) \<and>
     (\<forall>i v n x. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_val v, i32c n, admininstr_sc5 (admininstr_st5_TABLE_FILL x)] \<longrightarrow>
        (\<exists>vr. tr_val v = V_ref vr)) \<and>
     (\<forall>i v n. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_val v, i32c n, admininstr_sc7 admininstr_st7_MEMORY_FILL] \<longrightarrow>
        (\<exists>c. v = val_CONST I32 (mk_num__0 Inn_I32 c))) \<and>
     (\<forall>i t n sx ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i),
                         admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn t) (Some (mk_loadop__0 t (mk_loadop_Inn (mk_sz n) sx))) ao)] \<longrightarrow>
        ext_width_ok (numtype_Inn t) n) \<and>
     (\<forall>i M N sx ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore (mk_sz M) N sx)) ao)] \<longrightarrow>
        (M = 8 \<or> M = 16 \<or> M = 32) \<and> N * (M * 2) = 128) \<and>
     (\<forall>i N ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop__ZERO (mk_sz N))) ao)] \<longrightarrow>
        N = 32 \<or> N = 64) \<and>
     (\<forall>i c N ao j. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c, admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz N) ao j)] \<longrightarrow>
        un j < 128 div N \<and> (N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64)) \<and>
     (\<forall>i N ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT (mk_sz N))) ao)] \<longrightarrow>
        N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64)"

(* The reading steps where SpecTec and WasmCert disagree: a [table.copy] whose
   source range does not fit the destination table (WasmCert-Isabelle's
   [table.copy] rules, DIFFERENCES.md), and a packed vector load of lanes that
   are not [M]-bit values (SpecTec's [vload_shape_val], DIFFERENCES.md). *)
inductive Read_exc :: "store \<Rightarrow> frame \<Rightarrow> admininstr list \<Rightarrow> admininstr list \<Rightarrow> bool" where
  table_copy_long: "fun_table (mk_state s f) x tx \<Longrightarrow> length (REFS tx) < un u + n \<Longrightarrow>
    Read_exc s f [admininstr_sc1 (admininstr_st1_CONST I32 j), i32c u, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_COPY x y)] es'"
| packed_lanes: "\<not> list_all (wf_uN M) js \<Longrightarrow>
    Read_exc s f [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore (mk_sz M) N sx)) ao)]
      [vc (inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim N)) (map (\<lambda>j. mk_lane__0 J (extend__underscore M (M * 2) sx j)) js))]"

locale sim_all = simd_mem + simd + wasm_zeros

lemma wf_i32_in:
  assumes "wfl es" "admininstr_sc1 (admininstr_st1_CONST I32 i) \<in> set es"
  obtains u where "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32"
proof -
  have "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 i))" using assms by (simp add: list_all_iff)
  then show thesis using wf_const_i32 that by blast
qed

lemma wf_i32_lit: "wf_admininstr (i32c (mk_uN n)) \<Longrightarrow> n < 2 ^ 32"
  by (drule wf_const) simp

lemma jsize_ex: "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64 \<Longrightarrow> \<exists>J. fun_jsize J N"
  using fun_jsize_iff[of Jnn_I8 N] fun_jsize_iff[of Jnn_I16 N] fun_jsize_iff[of Jnn_I32 N] fun_jsize_iff[of Jnn_I64 N]
  by (auto simp: jbits_def)

lemma rat_dim:
  assumes "rat_of_nat M = rat_of_nat 128 / rat_of_nat N" "fun_jsize J N"
  shows "M = 128 div N"
proof -
  have "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64" using assms(2) jbits_cases[of J] by (simp add: fun_jsize_iff)
  then show ?thesis using assms(1) by auto
qed

lemma wf_lane_J:
  assumes "wf_lane_underscore (lanetype_Jnn J) (mk_lane__0 J x)" "fun_jsize J N"
  shows "wf_uN N x"
  using assms(1)
proof (cases rule: wf_lane_underscore.cases)
  case (lane__case_0 w)
  then have "fun_jsize J w" by (auto intro: fun_jsize.intros)
  then show ?thesis using assms(2) lane__case_0 by (simp add: fun_jsize_iff)
qed

lemma wf_vconst: "wf_admininstr (vc c) \<Longrightarrow> wf_uN 128 c"
  by (erule wf_admininstr.cases) auto

lemma fun_table_I: "un x < length (TABLES (frame_MODULE f)) \<Longrightarrow> TABLES (frame_MODULE f) ! un x < length (store_TABLES s) \<Longrightarrow>
  fun_table (mk_state s f) x (store_TABLES s ! (TABLES (frame_MODULE f) ! un x))"
  by (metis fun_table.intros proj_uN_0_un)

context sim_all
begin

theorem Step_read_sim:
  assumes st: "Step_read (mk_config (mk_state s f) es) es'" and w: "wfl es"
    and inv: "state_inv s f" and ok: "redex_ok f es"
  shows "sim (mk_config (mk_state s f) es) (mk_config (mk_state s f) es') \<or> Read_exc s f es es'"
  using st
proof (cases rule: Step_read.cases)
  case (Step_read__block bt ft t1 t2 k vs n ins)
  then show ?thesis using sim_block[of s f bt t1 t2 vs n ins] by simp
next
  case (Step_read__loop bt ft t1 t2 k vs n ins)
  then show ?thesis using sim_loop[of s f bt t1 t2 vs k ins] by simp
next
  case (Step_read__call x)
  then show ?thesis using sim_call[of x s f] by simp
next
  case (call_indirect_call y ft x ti i a)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w call_indirect_call(1) by (auto elim: wf_const_i32)
  have ty: "un y < length (TYPES (frame_MODULE f))" "ft = TYPES (frame_MODULE f) ! un y"
    using call_indirect_call by (auto elim: fun_type.cases)
  show ?thesis using call_indirect_call u ty sim_call_indirect[of s f x ti u a y] by simp
next
  case (call_indirect_trap i x y)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w call_indirect_trap(1) by (auto elim: wf_const_i32)
  have xy: "un x < length (TABLES (frame_MODULE f))" "un y < length (TYPES (frame_MODULE f))"
    using ok call_indirect_trap(1) by (simp_all add: redex_ok_def)
  have xa: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" using inv xy(1) by (simp add: state_inv_def)
  let ?ti = "store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
  have t: "fun_table (mk_state s f) x ?ti" by (rule fun_table_I[OF xy(1) xa])
  have fa: "\<And>a. un u < length (REFS ?ti) \<Longrightarrow> REFS ?ti ! un u = REF_FUNC_ADDR a \<Longrightarrow> a < length (store_FUNCS s)"
    using inv xa by (auto simp: state_inv_def) (metis nth_mem)
  have nb: "\<not> (un u < length (REFS ?ti) \<and> (\<exists>a. REFS ?ti ! un u = REF_FUNC_ADDR a \<and> a < length (store_FUNCS s) \<and>
                funcinst_TYPE (store_FUNCS s ! a) = TYPES (frame_MODULE f) ! un y))"
  proof
    assume h: "un u < length (REFS ?ti) \<and> (\<exists>a. REFS ?ti ! un u = REF_FUNC_ADDR a \<and> a < length (store_FUNCS s) \<and>
                funcinst_TYPE (store_FUNCS s ! a) = TYPES (frame_MODULE f) ! un y)"
    then obtain a where a: "REFS ?ti ! un u = REF_FUNC_ADDR a" "a < length (store_FUNCS s)"
      "funcinst_TYPE (store_FUNCS s ! a) = TYPES (frame_MODULE f) ! un y" by blast
    have hl: "un u < length (REFS ?ti)" using h by blast
    have ft: "fun_type (mk_state s f) y (TYPES (frame_MODULE f) ! un y)" using fun_type.intros[of y f s] xy(2) by simp
    have "Step_read_before_call_indirect_trap (mk_config (mk_state s f)
                 [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y)])"
      by (rule Step_read_before_call_indirect_trap.intros[OF ft t]) (simp_all add: u(1) hl a(1,2) a(3)[symmetric])
    then show False using call_indirect_trap by simp
  qed
  show ?thesis using call_indirect_trap u sim_call_indirect_trap[OF t u(2) xy(2) fa nb] by simp
next
  case (call_addr ds ts a t1 t2 mm fn x ins fr vs k n)
  then show ?thesis using sim_call_addr[of a s t1 t2 mm x ts ins ds fr vs n f] by simp
next
  case (Step_read__ref_func x)
  then show ?thesis using sim_ref_func[of x s f] by simp
next
  case (Step_read__local_get x v)
  then show ?thesis using sim_local_get[of s f x v] by simp
next
  case (Step_read__global_get x gi)
  then show ?thesis using sim_global_get[of s f x gi] by simp
next
  case (table_get_trap x ti i)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w table_get_trap(1) by (auto elim: wf_const_i32)
  show ?thesis using table_get_trap u sim_table_get[of s f x ti u "[admininstr_sc7 admininstr_st7_TRAP]"] by simp
next
  case (table_get_val x ti i)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w table_get_val(1) by (auto elim: wf_const_i32)
  show ?thesis using table_get_val u sim_table_get[of s f x ti u "[admininstr_ref (REFS ti ! un u)]"] by simp
next
  case (Step_read__table_size x ti n)
  then show ?thesis using sim_table_size[of s f x ti n] by simp
next
  case (table_fill_trap x ti i n v)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w table_fill_trap(1) by (auto elim: wf_const_i32)
  obtain vr where vr: "tr_val v = V_ref vr" using ok table_fill_trap(1) by (auto simp: redex_ok_def)
  have "n < 2 ^ 32" using w table_fill_trap(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using table_fill_trap u vr sim_table_fill_trap[of s f x ti v vr u n] by simp
next
  case (table_fill_zero x ti i n v)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w table_fill_zero(1) by (auto elim: wf_const_i32)
  obtain vr where vr: "tr_val v = V_ref vr" using ok table_fill_zero(1) by (auto simp: redex_ok_def)
  show ?thesis using table_fill_zero u vr sim_table_fill_zero[of s f x ti v vr u] by simp
next
  case (table_fill_succ x ti i n v)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w table_fill_succ(1) by (auto elim: wf_const_i32)
  obtain vr where vr: "tr_val v = V_ref vr" using ok table_fill_succ(1) by (auto simp: redex_ok_def)
  have "n < 2 ^ 32" using w table_fill_succ(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using table_fill_succ u vr sim_table_fill_succ[of s f x ti v vr u n] by simp
next
  case (table_copy_trap x tx y ty i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w table_copy_trap(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w table_copy_trap(1) by (auto elim: wf_const_i32)
  have "n < 2 ^ 32" using w table_copy_trap(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using table_copy_trap ui uj sim_table_copy_trap[of s f x tx y ty uj ui n] by simp
next
  case (table_copy_zero x tx y ty i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w table_copy_zero(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w table_copy_zero(1) by (auto elim: wf_const_i32)
  show ?thesis using table_copy_zero ui uj sim_table_copy_zero[of s f x tx y ty uj ui] by simp
next
  case (table_copy_le x tx y ty j i n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w table_copy_le(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w table_copy_le(1) by (auto elim: wf_const_i32)
  have n: "n < 2 ^ 32" using w table_copy_le(1) by (auto dest!: wf_i32_lit)
  show ?thesis
  proof (cases "un ui + n \<le> length (REFS tx)")
    case True
    then show ?thesis using table_copy_le ui uj n sim_table_copy_le[of s f x tx y ty uj ui n] by simp
  next
    case False
    then show ?thesis using table_copy_le ui uj Read_exc.table_copy_long[of s f x tx ui n j y] by simp
  qed
next
  case (table_copy_gt x tx y ty j i n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w table_copy_gt(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w table_copy_gt(1) by (auto elim: wf_const_i32)
  have n: "n < 2 ^ 32" using w table_copy_gt(1) by (auto dest!: wf_i32_lit)
  show ?thesis
  proof (cases "un ui + n \<le> length (REFS tx)")
    case True
    then show ?thesis using table_copy_gt ui uj n sim_table_copy_gt[of s f x tx y ty uj ui n] by (simp del: of_nat_add)
  next
    case False
    then show ?thesis using table_copy_gt ui uj Read_exc.table_copy_long[of s f x tx ui n j y] by simp
  qed
next
  case (table_init_trap x tx y ei i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w table_init_trap(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w table_init_trap(1) by (auto elim: wf_const_i32)
  have "n < 2 ^ 32" using w table_init_trap(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using table_init_trap ui uj sim_table_init_trap[of s f x tx y ei uj ui n] by simp
next
  case (table_init_zero x tx y ei i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w table_init_zero(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w table_init_zero(1) by (auto elim: wf_const_i32)
  show ?thesis using table_init_zero ui uj sim_table_init_zero[of s f x tx y ei uj ui] by simp
next
  case (table_init_succ x tx y ei i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w table_init_succ(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w table_init_succ(1) by (auto elim: wf_const_i32)
  have "n < 2 ^ 32" using w table_init_succ(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using table_init_succ ui uj sim_table_init_succ[of s f x tx y ei uj ui n] by simp
next
  case (load_num_trap mi i nt ao)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w load_num_trap(1) by (auto elim: wf_const_i32)
  show ?thesis using load_num_trap u sim_load_num_trap[of s f mi u ao nt] by simp
next
  case (load_num_val mi i nt c ao)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w load_num_val(1) by (auto elim: wf_const_i32)
  show ?thesis using load_num_val u sim_load_num[of s f mi u nt c ao] by simp
next
  case (load_pack_trap mi i ao n t sx)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w load_pack_trap(1) by (auto elim: wf_const_i32)
  have e: "ext_width_ok (numtype_Inn t) n" using ok load_pack_trap(1) by (simp add: redex_ok_def)
  show ?thesis using load_pack_trap u e sim_load_pack_trap[of s f mi u t n ao sx] by simp
next
  case (load_pack_val mi t i n c ao sx)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w load_pack_val(1) by (auto elim: wf_const_i32)
  have e: "ext_width_ok (numtype_Inn t) n" using ok load_pack_val(1) by (simp add: redex_ok_def)
  show ?thesis using load_pack_val u e sim_load_pack[of s f mi u t n c ao sx] by simp
next
  case (vload_oob mi i ao)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_oob(1) by (auto elim: wf_const_i32)
  show ?thesis using vload_oob u sim_vload_trap[of s f mi u ao] by simp
next
  case (Step_read__vload_val mi i c ao)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w Step_read__vload_val(1) by (auto elim: wf_const_i32)
  show ?thesis using Step_read__vload_val u sim_vload[of s f mi u c ao] by simp
next
  case (vload_shape_oob mi i ao M N sx)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_shape_oob(1) by (auto elim: wf_const_i32)
  have MN: "M = 8 \<or> M = 16 \<or> M = 32" "N * (M * 2) = 128" using ok vload_shape_oob(1) by (simp_all add: redex_ok_def)
  show ?thesis using vload_shape_oob u MN sim_vload_shape_trap[of s f mi u M N ao sx] by (simp add: mult.commute)
next
  case (vload_shape_val J w mi i N M ao js c sx)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_shape_val(1) by (auto elim: wf_const_i32)
  have MN: "M = 8 \<or> M = 16 \<or> M = 32" "N * (M * 2) = 128" using ok vload_shape_val(1) by (simp_all add: redex_ok_def)
  have Jw: "fun_jsize J (M * 2)" using vload_shape_val by simp
  show ?thesis
  proof (cases "list_all (wf_uN M) js")
    case True
    have d: "\<And>k. nat \<lfloor>rat_of_nat (k * M) / 8\<rfloor> = k * (M div 8)" using MN(1) by auto
    have b: "\<And>k. k < length js \<Longrightarrow>
               ibytes_underscore M (js ! k) = list_slice (BYTES mi) (un u + un (OFFSET ao) + k * (M div 8)) (M div 8)"
      using vload_shape_val u d by (simp add: list_alli_iff)
    from sim_vload_shape[OF _ u(2) Jw MN(1) _ MN(2) True b, where s = s and f = f and sx = sx]
    show ?thesis using vload_shape_val u by simp
  next
    case False
    then show ?thesis using vload_shape_val u Read_exc.packed_lanes[of M js s f i N sx ao J] by simp
  qed
next
  case (vload_splat_oob mi i ao N)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_splat_oob(1) by (auto elim: wf_const_i32)
  have NN: "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64" using ok vload_splat_oob(1) by (simp add: redex_ok_def)
  obtain J where J: "fun_jsize J N" using jsize_ex[OF NN] by blast
  show ?thesis using vload_splat_oob u J sim_vload_splat_trap[of s f mi u J N ao] by simp
next
  case (vload_splat_val J w mi i N j ao M c)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_splat_val(1) by (auto elim: wf_const_i32)
  have JN: "fun_jsize J N" using vload_splat_val by simp
  have M: "M = 128 div N" by (rule rat_dim[OF _ JN]) (use vload_splat_val in simp)
  have wj: "wf_uN N j" by (rule wf_lane_J[OF _ JN]) (use vload_splat_val in simp)
  show ?thesis using vload_splat_val u sim_vload_splat[OF _ u(2) JN M wj, of s f mi ao] by simp
next
  case (vload_zero_oob mi i ao N)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_zero_oob(1) by (auto elim: wf_const_i32)
  have N: "N = 32 \<or> N = 64" using ok vload_zero_oob(1) by (simp add: redex_ok_def)
  show ?thesis using vload_zero_oob u sim_vload_zero_trap[OF _ u(2) N, of s f mi ao] by simp
next
  case (vload_zero_val mi i N j ao c)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_zero_val(1) by (auto elim: wf_const_i32)
  have N: "N = 32 \<or> N = 64" using ok vload_zero_val(1) by (simp add: redex_ok_def)
  show ?thesis using vload_zero_val u sim_vload_zero[OF _ u(2) N, of s f mi j ao] by (simp add: extend_def)
next
  case (vload_lane_oob mi i ao N c1 j)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_lane_oob(1) by (auto elim: wf_const_i32)
  have NN: "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64" using ok vload_lane_oob(1) by (simp add: redex_ok_def)
  obtain J where J: "fun_jsize J N" using jsize_ex[OF NN] by blast
  show ?thesis using vload_lane_oob u J sim_vload_lane_trap[of s f mi u J N ao c1 j] by simp
next
  case (vload_lane_val J w mi i N k ao M c c1 j)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w vload_lane_val(1) by (auto elim: wf_const_i32)
  have JN: "fun_jsize J N" using vload_lane_val by simp
  have M: "M = 128 div N" by (rule rat_dim[OF _ JN]) (use vload_lane_val in simp)
  have wk: "wf_uN N k" by (rule wf_lane_J[OF _ JN]) (use vload_lane_val in simp)
  have c1: "wf_uN 128 c1" using w vload_lane_val(1) by (auto dest: wf_vconst)
  have jl: "un j < M" using ok vload_lane_val(1) M by (simp add: redex_ok_def)
  show ?thesis using vload_lane_val u sim_vload_lane[OF _ u(2) JN M c1 wk jl, of s f mi ao] by simp
next
  case (Step_read__memory_size mi n)
  then show ?thesis using sim_memory_size[of s f mi n] by simp
next
  case (memory_fill_trap mi i n v)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w memory_fill_trap(1) by (auto elim: wf_const_i32)
  obtain c where c: "v = val_CONST I32 (mk_num__0 Inn_I32 c)" using ok memory_fill_trap(1) by (auto simp: redex_ok_def)
  have "n < 2 ^ 32" using w memory_fill_trap(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using memory_fill_trap u c sim_memory_fill_trap[of s f mi u n c] by simp
next
  case (memory_fill_zero mi i n v)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w memory_fill_zero(1) by (auto elim: wf_const_i32)
  obtain c where c: "v = val_CONST I32 (mk_num__0 Inn_I32 c)" using ok memory_fill_zero(1) by (auto simp: redex_ok_def)
  show ?thesis using memory_fill_zero u c sim_memory_fill_zero[of s f mi u c] by simp
next
  case (memory_fill_succ mi i n v)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w memory_fill_succ(1) by (auto elim: wf_const_i32)
  obtain c where c: "v = val_CONST I32 (mk_num__0 Inn_I32 c)" using ok memory_fill_succ(1) by (auto simp: redex_ok_def)
  have "n < 2 ^ 32" using w memory_fill_succ(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using memory_fill_succ u c sim_memory_fill_succ[of s f mi u n c] by simp
next
  case (memory_copy_trap mi i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w memory_copy_trap(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w memory_copy_trap(1) by (auto elim: wf_const_i32)
  have "n < 2 ^ 32" using w memory_copy_trap(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using memory_copy_trap ui uj sim_memory_copy_trap[of s f mi uj ui n] by simp
next
  case (memory_copy_zero mi i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w memory_copy_zero(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w memory_copy_zero(1) by (auto elim: wf_const_i32)
  show ?thesis using memory_copy_zero ui uj sim_memory_copy_zero[of s f mi uj ui] by simp
next
  case (memory_copy_le mi j i n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w memory_copy_le(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w memory_copy_le(1) by (auto elim: wf_const_i32)
  have "n < 2 ^ 32" using w memory_copy_le(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using memory_copy_le ui uj sim_memory_copy_le[of s f mi uj ui n] by simp
next
  case (memory_copy_gt mi j i n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w memory_copy_gt(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w memory_copy_gt(1) by (auto elim: wf_const_i32)
  have "n < 2 ^ 32" using w memory_copy_gt(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using memory_copy_gt ui uj sim_memory_copy_gt[of s f mi uj ui n] by (simp del: of_nat_add)
next
  case (memory_init_trap mi x di i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w memory_init_trap(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w memory_init_trap(1) by (auto elim: wf_const_i32)
  have "n < 2 ^ 32" using w memory_init_trap(1) by (auto dest!: wf_i32_lit)
  then show ?thesis using memory_init_trap ui uj sim_memory_init_trap[of s f mi x di uj ui n] by simp
next
  case (memory_init_zero mi x di i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w memory_init_zero(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w memory_init_zero(1) by (auto elim: wf_const_i32)
  show ?thesis using memory_init_zero ui uj sim_memory_init_zero[of s f mi x di uj ui] by simp
next
  case (memory_init_succ mi x di i j n)
  obtain ui where ui: "i = mk_num__0 Inn_I32 ui" "un ui < 2 ^ 32" using w memory_init_succ(1) by (auto elim: wf_const_i32)
  obtain uj where uj: "j = mk_num__0 Inn_I32 uj" "un uj < 2 ^ 32" using w memory_init_succ(1) by (auto elim: wf_const_i32)
  have n: "n < 2 ^ 32" using w memory_init_succ(1) by (auto dest!: wf_i32_lit)
  have d: "di \<in> set (store_DATAS s)" using memory_init_succ by (auto elim!: fun_data_E)
  have "un ui < length (datainst_BYTES di)" using memory_init_succ ui by simp
  then have bt: "proj_byte_0 (datainst_BYTES di ! un ui) < 256" using inv d by (auto simp: state_inv_def)
  show ?thesis using memory_init_succ ui uj n bt sim_memory_init_succ[of s f mi x di uj ui n] by simp
qed

end

end
