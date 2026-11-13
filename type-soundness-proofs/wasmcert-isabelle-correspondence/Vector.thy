(* Vector: the vector instructions in the reduction simulation.

   - Pure vector operators (locale [simd]): one assumption per WasmCert vector
     function, as in the Rocq bridge (see the comment on the locale); the
     simulation lemmas [psim_v*] follow.
   - Vector loads and stores (locale [simd_mem], extending [mem_bytes]): the
     locale gives SpecTec's axiomatised [vbytes_], [lanes_] and [inv_lanes_]
     their definition in the Wasm specification and fixes WasmCert-Isabelle's
     [v128] serialisation to the little-endian layout.  From these, all vector
     loads and stores are proved: whole-vector ([sim_vload], [sim_vstore]),
     zero-extending ([sim_vload_zero]), splat ([sim_vload_splat]), packed
     ([sim_vload_shape]) and lane ([sim_vload_lane], [sim_vstore_lane]), each
     with its trap.  The Rocq bridge assumes these steps ([simd_load_tr], ...).

   Side conditions (see DIFFERENCES.md): stores must be in bounds
   ([Oob_store]); a lane store traps in SpecTec when its bit width overruns
   the memory, so only byte-width overruns are simulated ([Vstore_disagree]);
   packed loads need the loaded lanes to be well formed, which SpecTec's
   [vload_shape_val] does not require. *)
theory Vector
  imports Memory
begin

section \<open>Pure vector instructions\<close>

abbreviation vc :: "uN \<Rightarrow> admininstr" where
  "vc c \<equiv> admininstr_sc2 (admininstr_st2_VCONST V128 c)"

lemma tr_admin_vc[simp]: "tr_admin (vc c) = ($EConstVec (tr_vec c))"
  by simp

(* WasmCert-Isabelle executes every vector operator through an uninterpreted
   function ([app_unop_vec_v], ...) or through the abstract [v128]
   serialisation ([app_splat_vec], ...), and the translation maps each SpecTec
   vector operator to an uninterpreted WasmCert operator ([vec_unop], ...).  So
   their agreement can only be assumed.  There is one assumption per WasmCert
   vector function: a SpecTec step of a well-typed redex is the WasmCert step.
   This is the Rocq bridge's [simd_*_tr], stated for the results.  SpecTec's
   [vunop] and [vbinop] pick any element of a result list (NaN
   nondeterminism), so the assumptions are satisfiable only if those lists are
   singletons, as the [builtins] locale assumes for scalar floats. *)
locale simd =
  assumes vunop_tr: "\<And>c1 i op es' C ft. Step_pure [vc c1, admininstr_instr i] es' \<Longrightarrow>
      tr_instr i = Unop_vec op \<Longrightarrow> Instr_ok C i ft \<Longrightarrow>
      tr_admins es' = [$EConstVec (app_unop_vec op (tr_vec c1))]"
    and vbinop_tr: "\<And>c1 c2 i op es' C ft. Step_pure [vc c1, vc c2, admininstr_instr i] es' \<Longrightarrow>
      tr_instr i = Binop_vec op \<Longrightarrow> Instr_ok C i ft \<Longrightarrow>
      tr_admins es' = (case app_binop_vec op (tr_vec c1) (tr_vec c2) of Some v \<Rightarrow> [$EConstVec v] | None \<Rightarrow> [Trap])"
    and vternop_tr: "\<And>c1 c2 c3 i op es' C ft. Step_pure [vc c1, vc c2, vc c3, admininstr_instr i] es' \<Longrightarrow>
      tr_instr i = Ternop_vec op \<Longrightarrow> Instr_ok C i ft \<Longrightarrow>
      tr_admins es' = [$EConstVec (app_ternop_vec op (tr_vec c1) (tr_vec c2) (tr_vec c3))]"
    and vtestop_tr: "\<And>c1 i op es' C ft. Step_pure [vc c1, admininstr_instr i] es' \<Longrightarrow>
      tr_instr i = Test_vec op \<Longrightarrow> Instr_ok C i ft \<Longrightarrow>
      tr_admins es' = [$EConstNum (ConstInt32 (app_test_vec op (tr_vec c1)))]"
    and vshiftop_tr: "\<And>c1 u i op es' C ft. Step_pure [vc c1, i32c u, admininstr_instr i] es' \<Longrightarrow>
      tr_instr i = Shift_vec op \<Longrightarrow> Instr_ok C i ft \<Longrightarrow>
      tr_admins es' = [$EConstVec (app_shift_vec op (tr_vec c1) (tr_i32 u))]"
    and vsplat_tr: "\<And>nt c i shv es' C ft. Step_pure [admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_instr i] es' \<Longrightarrow>
      tr_instr i = Splat_vec shv \<Longrightarrow> Instr_ok C i ft \<Longrightarrow>
      tr_admins es' = [$EConstVec (app_splat_vec shv (tr_num c))]"
    and vextract_tr: "\<And>c1 i shv sx j es' C ft. Step_pure [vc c1, admininstr_instr i] es' \<Longrightarrow>
      tr_instr i = Extract_vec shv sx j \<Longrightarrow> Instr_ok C i ft \<Longrightarrow>
      tr_admins es' = [$EConstNum (app_extract_vec shv sx j (tr_vec c1))]"
    and vreplace_tr: "\<And>c1 nt c i shv j es' C ft. Step_pure [vc c1, admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_instr i] es' \<Longrightarrow>
      tr_instr i = Replace_vec shv j \<Longrightarrow> Instr_ok C i ft \<Longrightarrow>
      tr_admins es' = [$EConstVec (app_replace_vec shv j (tr_vec c1) (tr_num c))]"

context simd
begin

lemma psim_vunop:
  assumes "Step_pure [vc c1, admininstr_instr i] es'" "tr_instr i = Unop_vec op" "Instr_ok C i ft"
  shows "psim [vc c1, admininstr_instr i] es'"
  unfolding psim_def using vunop_tr[OF assms] assms(2)
  by (auto intro!: wsim_basic[OF reduce_simple.unop_vec])

lemma psim_vbinop:
  assumes "Step_pure [vc c1, vc c2, admininstr_instr i] es'" "tr_instr i = Binop_vec op" "Instr_ok C i ft"
  shows "psim [vc c1, vc c2, admininstr_instr i] es'"
  unfolding psim_def using vbinop_tr[OF assms] assms(2)
  by (auto split: option.splits intro!: wsim_basic intro: reduce_simple.binop_vec_Some reduce_simple.binop_vec_None)

lemma psim_vternop:
  assumes "Step_pure [vc c1, vc c2, vc c3, admininstr_instr i] es'" "tr_instr i = Ternop_vec op" "Instr_ok C i ft"
  shows "psim [vc c1, vc c2, vc c3, admininstr_instr i] es'"
  unfolding psim_def using vternop_tr[OF assms] assms(2)
  by (auto intro!: wsim_basic[OF reduce_simple.ternop_vec])

lemma psim_vtestop:
  assumes "Step_pure [vc c1, admininstr_instr i] es'" "tr_instr i = Test_vec op" "Instr_ok C i ft"
  shows "psim [vc c1, admininstr_instr i] es'"
  unfolding psim_def using vtestop_tr[OF assms] assms(2)
  by (auto intro!: wsim_basic[OF reduce_simple.test_vec])

lemma psim_vshiftop:
  assumes "Step_pure [vc c1, i32c u, admininstr_instr i] es'" "tr_instr i = Shift_vec op" "Instr_ok C i ft"
  shows "psim [vc c1, i32c u, admininstr_instr i] es'"
  unfolding psim_def using vshiftop_tr[OF assms] assms(2)
  by (auto intro!: wsim_basic[OF reduce_simple.shift_vec])

lemma psim_vsplat:
  assumes "Step_pure [admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_instr i] es'" "tr_instr i = Splat_vec shv"
    "Instr_ok C i ft"
  shows "psim [admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_instr i] es'"
  unfolding psim_def using vsplat_tr[OF assms] assms(2)
  by (auto intro!: wsim_basic[OF reduce_simple.splat_vec])

lemma psim_vextract:
  assumes "Step_pure [vc c1, admininstr_instr i] es'" "tr_instr i = Extract_vec shv sx j" "Instr_ok C i ft"
  shows "psim [vc c1, admininstr_instr i] es'"
  unfolding psim_def using vextract_tr[OF assms] assms(2)
  by (auto intro!: wsim_basic[OF reduce_simple.extract_vec])

lemma psim_vreplace:
  assumes "Step_pure [vc c1, admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_instr i] es'"
    "tr_instr i = Replace_vec shv j" "Instr_ok C i ft"
  shows "psim [vc c1, admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_instr i] es'"
  unfolding psim_def using vreplace_tr[OF assms] assms(2)
  by (auto intro!: wsim_basic[OF reduce_simple.replace_vec])

end

section \<open>Vectors as bytes and lanes\<close>

(* The value of a little-endian sequence of [w]-bit lanes. *)
fun vsum :: "nat \<Rightarrow> uN list \<Rightarrow> nat" where
  "vsum w [] = 0"
| "vsum w (i # ns) = un i + 2 ^ w * vsum w ns"

lemma le_bytes_append: "le_bytes (a + b) x = le_bytes a x @ le_bytes b (x div 2 ^ (8 * a))"
proof (rule nth_equalityI)
  fix j assume "j < length (le_bytes (a + b) x)"
  then have j: "j < a + b" by simp
  show "le_bytes (a + b) x ! j = (le_bytes a x @ le_bytes b (x div 2 ^ (8 * a))) ! j"
  proof (cases "j < a")
    case False
    have e: "8 * a + 8 * (j - a) = 8 * j" using False by simp
    have "x div 2 ^ (8 * a) div 2 ^ (8 * (j - a)) = x div 2 ^ (8 * j)"
      by (simp only: div_mult2_eq[symmetric] power_add[symmetric] e)
    then show ?thesis using j False by (simp add: nth_append nth_le_bytes)
  qed (use j in \<open>simp add: nth_append nth_le_bytes\<close>)
qed simp

lemma vsum_lt: "list_all (\<lambda>i. un i < 2 ^ w) ns \<Longrightarrow> vsum w ns < 2 ^ (w * length ns)"
proof (induction ns)
  case (Cons i ns)
  then have i: "un i < 2 ^ w" and v: "vsum w ns + 1 \<le> 2 ^ (w * length ns)" by auto
  have "2 ^ w * (vsum w ns + 1) \<le> 2 ^ w * 2 ^ (w * length ns)" using v by (rule mult_le_mono2)
  then show ?case using i by (simp add: power_add[symmetric] algebra_simps)
qed simp

lemma le_bytes_vsum:
  "list_all (\<lambda>i. un i < 2 ^ (8 * k)) ns \<Longrightarrow>
   le_bytes (k * length ns) (vsum (8 * k) ns) = concat (map (\<lambda>i. le_bytes k (un i)) ns)"
proof (induction ns)
  case (Cons i ns)
  then have i: "un i < 2 ^ (8 * k)" by simp
  have m: "(un i + 2 ^ (8 * k) * vsum (8 * k) ns) mod 2 ^ (8 * k) = un i" using i by simp
  have d: "(un i + 2 ^ (8 * k) * vsum (8 * k) ns) div 2 ^ (8 * k) = vsum (8 * k) ns" using i by simp
  have "le_bytes (k + k * length ns) (un i + 2 ^ (8 * k) * vsum (8 * k) ns) =
        le_bytes k (un i) @ le_bytes (k * length ns) (vsum (8 * k) ns)"
    using le_bytes_append[of k "k * length ns"] le_bytes_mod[of k "un i + 2 ^ (8 * k) * vsum (8 * k) ns"] m d by simp
  then show ?case using Cons by simp
qed (simp add: le_bytes_def)

lemma concat_chunks_take_drop:
  "list_all (\<lambda>x. length x = k) xs \<Longrightarrow> j < length xs \<Longrightarrow> take k (drop (j * k) (concat xs)) = xs ! j"
proof (induction xs arbitrary: j)
  case (Cons x xs) then show ?case by (cases j) auto
qed simp

lemma concat_chunks_update:
  "list_all (\<lambda>x. length x = k) xs \<Longrightarrow> j < length xs \<Longrightarrow> length y = k \<Longrightarrow>
   concat (xs[j := y]) = take (j * k) (concat xs) @ y @ drop (Suc j * k) (concat xs)"
proof (induction xs arbitrary: j)
  case (Cons x xs) then show ?case by (cases j) auto
qed simp

definition jbits :: "Jnn \<Rightarrow> nat" where
  "jbits J = (case J of Jnn_I8 \<Rightarrow> 8 | Jnn_I16 \<Rightarrow> 16 | Jnn_I32 \<Rightarrow> 32 | Jnn_I64 \<Rightarrow> 64)"

termination lanetype_Jnn by lexicographic_order

termination proj_lane__0 by lexicographic_order

lemma fun_jsize_iff: "fun_jsize J w \<longleftrightarrow> w = jbits J"
  by (cases J) (auto simp: jbits_def elim!: fun_jsize.cases fun_lsize.cases intro!: fun_jsize.intros intro: fun_lsize.intros[simplified])

lemma jbits_cases: "jbits J = 8 \<or> jbits J = 16 \<or> jbits J = 32 \<or> jbits J = 64"
  by (cases J) (simp_all add: jbits_def)

lemma svi_of_jbits:
  "vec_i_length (svi_of_bits (jbits J)) = jbits J div 8" "vec_i_num (svi_of_bits (jbits J)) = 128 div jbits J"
  by (cases J; simp add: jbits_def svi_of_bits_def vec_i_length_def vec_i_num_def)+

lemma jbits_div: "jbits J = 8 * (jbits J div 8)" "(jbits J div 8) * (128 div jbits J) = 16" "0 < jbits J div 8"
  by (cases J; simp add: jbits_def)+

section \<open>Vector loads and stores\<close>

(* SpecTec axiomatises [vbytes_], [lanes_] and [inv_lanes_]; the locale gives
   them their definition in the Wasm specification (a vector's bytes are the
   little-endian bytes of its value; its integer lanes are little-endian
   chunks of it).  WasmCert-Isabelle specifies [v128] serialisation only up to
   its length; the locale fixes it to the little-endian layout.  All of this
   is satisfiable. *)
locale simd_mem = mem_bytes +
  assumes vbytes_ibytes: "\<And>c. vbytes_underscore V128 c = ibytes_underscore 128 c"
    and serialise_v128_le: "\<And>v. serialise_v128 v = map Abs_uint8' (word_rsplit_rev (Rep_v128 v))"
    and inv_lanes_def: "\<And>J ns. length ns = 128 div jbits J \<Longrightarrow> list_all (wf_uN (jbits J)) ns \<Longrightarrow>
      inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim (128 div jbits J))) (map (mk_lane__0 J) ns) = mk_uN (vsum (jbits J) ns)"
    and lanes_def: "\<And>J c. wf_uN 128 c \<Longrightarrow>
      \<exists>ns. lanes_underscore (X (lanetype_Jnn J) (mk_dim (128 div jbits J))) c = map (mk_lane__0 J) ns \<and>
           length ns = 128 div jbits J \<and> list_all (wf_uN (jbits J)) ns \<and> vsum (jbits J) ns = un c"

context simd_mem
begin

lemma v128_bytes: "wf_uN 128 c \<Longrightarrow> serialise_v128 (tr_v128 c) = le_bytes 16 (un c)"
  using rsplit_rev_le_bytes[where w = "word_of_nat (un c) :: 128 word" and k = 16]
  by (simp add: serialise_v128_le tr_v128_def Abs_v128_inverse wf_uN_iff unat_of_nat take_bit_eq_mod)

lemma vbytes_le: "wf_uN 128 c \<Longrightarrow> map tr_byte (vbytes_underscore V128 c) = le_bytes 16 (un c)"
  by (simp add: vbytes_ibytes ibytes_tr)

lemma vbytes_tr: "wf_uN 128 c \<Longrightarrow> map tr_byte (vbytes_underscore V128 c) = serialise_v128 (tr_v128 c)"
  by (simp add: vbytes_le v128_bytes)

lemma deserialise_le_bytes: "x < 2 ^ 128 \<Longrightarrow> deserialise_v128 (le_bytes 16 x) = tr_v128 (mk_uN x)"
  using v128_bytes[of "mk_uN x"] v128_roundtrip[of "tr_v128 (mk_uN x)"] by (simp add: wf_uN_iff)

(* The bytes of a vector built from lanes. *)
lemma inv_lanes_bytes:
  assumes "length ns = 128 div jbits J" "list_all (wf_uN (jbits J)) ns"
  shows "inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim (128 div jbits J))) (map (mk_lane__0 J) ns) = mk_uN (vsum (jbits J) ns)"
    "vsum (jbits J) ns < 2 ^ 128"
    "le_bytes 16 (vsum (jbits J) ns) = concat (map (\<lambda>i. le_bytes (jbits J div 8) (un i)) ns)"
proof -
  show "inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim (128 div jbits J))) (map (mk_lane__0 J) ns) = mk_uN (vsum (jbits J) ns)"
    by (rule inv_lanes_def[OF assms])
  have w: "list_all (\<lambda>i. un i < 2 ^ jbits J) ns" using assms(2) by (simp add: wf_uN_iff list_all_iff)
  have "jbits J * length ns = 128" using assms(1) jbits_cases[of J] by auto
  then show "vsum (jbits J) ns < 2 ^ 128" using vsum_lt[OF w] by simp
  have "list_all (\<lambda>i. un i < 2 ^ (8 * (jbits J div 8))) ns" using w jbits_div(1)[of J] by simp
  from le_bytes_vsum[OF this] show "le_bytes 16 (vsum (jbits J) ns) = concat (map (\<lambda>i. le_bytes (jbits J div 8) (un i)) ns)"
    using assms(1) jbits_div[of J] by (simp add: mult.commute)
qed

lemma length_vbytes: "wf_uN 128 c \<Longrightarrow> length (vbytes_underscore V128 c) = 16"
  using arg_cong[OF vbytes_tr, of c length] serialise_v128_len[OF HOL.refl] by simp

lemma v128_size: "nat \<lfloor>rat_of_nat (the (size valtype_V128)) / rat_of_nat 8\<rfloor> = 16"
  by simp

lemma sim_vload:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and c: "wf_uN 128 c"
    and b: "vbytes_underscore V128 c = list_slice (BYTES mi) (un u + un (OFFSET ao))
              (nat \<lfloor>rat_of_nat (the (size valtype_V128)) / rat_of_nat 8\<rfloor>)"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 None ao)])
             (mk_config (mk_state s f) [vc c])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  let ?p = "un u + un (OFFSET ao)"
  have b': "list_slice (BYTES mi) ?p 16 = vbytes_underscore V128 c" using b by (simp only: v128_size)
  have bd: "?p + 16 \<le> length (BYTES mi)"
    using list_slice_bound[of "BYTES mi" ?p 16] b' length_vbytes[OF c] by simp
  have ld: "load_vec Load_128 (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao) =
              Some (serialise_v128 (tr_v128 c))"
    using x1 bd u b' vbytes_tr[OF c]
    by (simp add: load_vec_def load_def t_vec_length_def nat_of_int_tr_i32 tr_offset_def read_bytes_tr)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load_vec Load_128 (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [$EConstVec (ConstVec128 (tr_v128 c))]"
    using reduce.load_vec_Some[OF smem_ind_tr[OF x1(2)] HOL.refl ld] by (simp add: v128_roundtrip)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_vec_def)
qed

lemma sim_vload_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat (the (size valtype_V128)) / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 None ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have ld: "load_vec Load_128 (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao) = None"
    using x1 b u by (simp add: load_vec_def load_def t_vec_length_def nat_of_int_tr_i32 tr_offset_def)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load_vec Load_128 (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.load_vec_None[OF smem_ind_tr[OF x1(2)] HOL.refl ld])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

(* An in-bounds vector store (out of bounds: [Oob_store]). *)
lemma sim_vstore:
  assumes a: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" and u: "un u < 2 ^ 32" and c: "wf_uN 128 c"
    and bd: "un u + un (OFFSET ao) + 16 \<le> length (BYTES (store_MEMS s ! (MEMS (frame_MODULE f) ! 0)))"
    and w: "fun_with_mem (mk_state s f) (mk_uN 0) (un u + un (OFFSET ao))
              (nat \<lfloor>rat_of_nat (the (size valtype_V128)) / rat_of_nat 8\<rfloor>) (vbytes_underscore V128 c) z'"
  shows "sim (mk_config (mk_state s f) [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE V128 ao)])
             (mk_config z' [])"
proof -
  let ?a = "MEMS (frame_MODULE f) ! 0"
  let ?mi = "store_MEMS s ! ?a"
  let ?p = "un u + un (OFFSET ao)"
  let ?bs = "vbytes_underscore V128 c"
  let ?mi' = "?mi\<lparr>BYTES := list_slice_update (BYTES ?mi) ?p 16 ?bs\<rparr>"
  let ?s' = "s\<lparr>store_MEMS := list_update_func (store_MEMS s) ?a (\<lambda>m. m\<lparr>BYTES := list_slice_update (BYTES m) ?p 16 ?bs\<rparr>)\<rparr>"
  have z: "z' = mk_state ?s' f" using w by (auto elim!: fun_with_mem.cases)
  have m0: "0 < length (MEMS (frame_MODULE f))" using w by (auto elim: fun_with_mem.cases)
  have len: "length ?bs = 16" by (rule length_vbytes[OF c])
  have shv: "store (s.mems (tr_store s) ! ?a) (nat_of_int (tr_i32 u)) (tr_offset ao) (store_serialise_vec Store_128 (tr_v128 c))
              (length (store_serialise_vec Store_128 (tr_v128 c))) = Some (tr_meminst ?mi')"
    using a bd u len write_bytes_tr[OF len bd]
    by (simp add: store_def store_serialise_vec_def nat_of_int_tr_i32 tr_offset_def bytes_takefill_def takefill_exact
                  vbytes_tr[OF c, symmetric])
  have upd: "(tr_store s)\<lparr>s.mems := (s.mems (tr_store s))[?a := tr_meminst ?mi']\<rparr> = tr_store ?s'"
    using a by (simp add: tr_store_def map_list_update_func)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstVec (ConstVec128 (tr_v128 c)), $Store_vec Store_128 (tr_align ao) (tr_offset ao)]
              (tr_store ?s') (tr_frame f) []"
    using reduce.store_vec_Some[OF smem_ind_tr[OF m0] HOL.refl HOL.refl shv] upd by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] z by (simp add: tr_vec_def)
qed

lemma sim_vstore_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat (the (size valtype_V128)) / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE V128 ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have shv: "store (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (store_serialise_vec Store_128 (tr_v128 c)) (length (store_serialise_vec Store_128 (tr_v128 c))) = None"
    using x1 b u serialise_v128_len[OF HOL.refl, of "tr_v128 c"]
    by (simp add: store_def store_serialise_vec_def nat_of_int_tr_i32 tr_offset_def)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstVec (ConstVec128 (tr_v128 c)), $Store_vec Store_128 (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.store_vec_None[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl shv])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_vec_def)
qed

(* A load into the low bytes of a zero vector. *)
lemma sim_vload_zero:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and N: "N = 32 \<or> N = 64"
    and j: "wf_uN N j"
    and b: "ibytes_underscore N j = list_slice (BYTES mi) (un u + un (OFFSET ao)) (nat \<lfloor>rat_of_nat N / rat_of_nat 8\<rfloor>)"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop__ZERO (mk_sz N))) ao)])
             (mk_config (mk_state s f) [vc (extend__underscore N 128 isabelle_reference_output_wasm2.U j)])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  let ?p = "un u + un (OFFSET ao)"
  let ?k = "N div 8"
  have jn: "un j < 2 ^ N" using j by (simp add: wf_uN_iff)
  have b': "list_slice (BYTES mi) ?p ?k = ibytes_underscore N j" using b by simp
  have len: "length (ibytes_underscore N j) = ?k" using arg_cong[OF ibytes_tr[OF j], of length] by simp
  have bd: "?p + ?k \<le> length (BYTES mi)" using list_slice_bound[of "BYTES mi" ?p ?k] b' len N by auto
  have tf: "takefill zero_byte 16 (le_bytes ?k (un j)) = le_bytes 16 (un j)"
    by (rule takefill_le_bytes) (use N jn in auto)
  have "(2::nat) ^ N \<le> 2 ^ 128" using N by auto
  then have lt: "un j < 2 ^ 128" using jn by linarith
  have ld: "load_vec (tr_vloadop (Some (vloadop__ZERO (mk_sz N)))) (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0))
              (nat_of_int (tr_i32 u)) (tr_offset ao) = Some (le_bytes 16 (un j))"
    using x1 bd u b' ibytes_tr[OF j] tf N
    by (auto simp: load_vec_def load_def nat_of_int_tr_i32 tr_offset_def read_bytes_tr bytes_takefill_def t_vec_length_def)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load_vec (tr_vloadop (Some (vloadop__ZERO (mk_sz N)))) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [$EConstVec (ConstVec128 (tr_v128 (mk_uN (un j))))]"
    using reduce.load_vec_Some[OF smem_ind_tr[OF x1(2)] HOL.refl ld] deserialise_le_bytes[OF lt] by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]]
    by (simp add: tr_vec_def extend_def del: tr_vloadop.simps)
qed

lemma sim_vload_ext_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32"
    and lv: "\<And>m n off. load_vec (tr_vloadop lo) m n off = map_option g (load m n off k)"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + k"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 lo ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have ld: "load_vec (tr_vloadop lo) (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao) = None"
    using x1 b u by (simp add: lv load_def nat_of_int_tr_i32 tr_offset_def)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load_vec (tr_vloadop lo) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.load_vec_None[OF smem_ind_tr[OF x1(2)] HOL.refl ld])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp del: tr_vloadop.simps)
qed

lemma sim_vload_zero_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and N: "N = 32 \<or> N = 64"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat N / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop__ZERO (mk_sz N))) ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
  by (rule sim_vload_ext_trap[OF m u, where k = "N div 8" and g = "bytes_takefill zero_byte 16"])
     (use N b in \<open>auto simp: load_vec_def t_vec_length_def\<close>)

lemma sim_vload_splat:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and J: "fun_jsize J N"
    and M: "M = 128 div N" and j: "wf_uN N j"
    and b: "ibytes_underscore N j = list_slice (BYTES mi) (un u + un (OFFSET ao)) (nat \<lfloor>rat_of_nat N / rat_of_nat 8\<rfloor>)"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT (mk_sz N))) ao)])
             (mk_config (mk_state s f) [vc (inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) (repeat M (mk_lane__0 J j)))])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have Nj: "N = jbits J" using J by (simp add: fun_jsize_iff)
  let ?p = "un u + un (OFFSET ao)"
  let ?k = "N div 8"
  have b': "list_slice (BYTES mi) ?p ?k = ibytes_underscore N j" using b by simp
  have len: "length (ibytes_underscore N j) = ?k" using arg_cong[OF ibytes_tr[OF j], of length] by simp
  have bd: "?p + ?k \<le> length (BYTES mi)" using list_slice_bound[of "BYTES mi" ?p ?k] b' len jbits_div(3)[of J] Nj by auto
  have w: "length (replicate M j) = 128 div jbits J" "list_all (wf_uN (jbits J)) (replicate M j)"
    using M Nj j by (simp_all add: list_all_iff)
  note lb = inv_lanes_bytes[OF w]
  have c: "inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) (repeat M (mk_lane__0 J j)) = mk_uN (vsum N (replicate M j))"
    using lb(1) M Nj by (simp add: map_replicate)
  have cb: "le_bytes 16 (vsum N (replicate M j)) = concat (replicate M (le_bytes ?k (un j)))"
    using lb(3) Nj by (simp add: map_replicate)
  have ld: "load_vec (Load_splat (svi_of_bits N)) (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao) =
              Some (le_bytes 16 (vsum N (replicate M j)))"
    using x1 bd u b' ibytes_tr[OF j] cb Nj M
    by (simp add: load_vec_def load_def nat_of_int_tr_i32 tr_offset_def read_bytes_tr svi_of_jbits)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load_vec (Load_splat (svi_of_bits N)) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [$EConstVec (ConstVec128 (tr_v128 (mk_uN (vsum N (replicate M j)))))]"
    using reduce.load_vec_Some[OF smem_ind_tr[OF x1(2)] HOL.refl ld] deserialise_le_bytes lb(2) Nj by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] c by (simp add: tr_vec_def)
qed

lemma sim_vload_splat_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and J: "fun_jsize J N"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat N / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT (mk_sz N))) ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  have Nj: "N = jbits J" using J by (simp add: fun_jsize_iff)
  show ?thesis
    by (rule sim_vload_ext_trap[OF m u, where k = "N div 8" and g = "\<lambda>bs. concat (replicate (vec_i_num (svi_of_bits N)) bs)"])
       (use Nj b in \<open>auto simp: load_vec_def svi_of_jbits\<close>)
qed

lemma list_update_func_map: "i < length xs \<Longrightarrow> list_update_func (map g xs) i (\<lambda>_. g y) = map g (xs[i := y])"
  by (simp add: list_update_func_conv map_update)

(* Loading one lane. *)
lemma sim_vload_lane:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and J: "fun_jsize J N"
    and M: "M = 128 div N" and c1: "wf_uN 128 c1" and k: "wf_uN N k" and jl: "un j < M"
    and b: "ibytes_underscore N k = list_slice (BYTES mi) (un u + un (OFFSET ao)) (nat \<lfloor>rat_of_nat N / rat_of_nat 8\<rfloor>)"
  shows "sim (mk_config (mk_state s f) [i32c u, vc c1, admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz N) ao j)])
             (mk_config (mk_state s f) [vc (inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim M))
                (list_update_func (lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) c1) (un j) (\<lambda>_. mk_lane__0 J k)))])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have Nj: "N = jbits J" using J by (simp add: fun_jsize_iff)
  obtain ns where ns: "lanes_underscore (X (lanetype_Jnn J) (mk_dim (128 div jbits J))) c1 = map (mk_lane__0 J) ns"
      "length ns = 128 div jbits J" "list_all (wf_uN (jbits J)) ns" "vsum (jbits J) ns = un c1"
    using lanes_def[OF c1, of J] by blast
  let ?p = "un u + un (OFFSET ao)"
  let ?k = "N div 8"
  let ?f = "\<lambda>i. le_bytes ?k (un i)"
  have b': "list_slice (BYTES mi) ?p ?k = ibytes_underscore N k" using b by simp
  have len: "length (ibytes_underscore N k) = ?k" using arg_cong[OF ibytes_tr[OF k], of length] by simp
  have bd: "?p + ?k \<le> length (BYTES mi)" using list_slice_bound[of "BYTES mi" ?p ?k] b' len jbits_div(3)[of J] Nj by auto
  have jn: "un j < length ns" using jl ns(2) M Nj by simp
  have w': "length (ns[un j := k]) = 128 div jbits J" "list_all (wf_uN (jbits J)) (ns[un j := k])"
    using ns(2,3) k Nj by (auto simp: list_all_iff dest: set_update_subset_insert[THEN subsetD])
  note lb' = inv_lanes_bytes[OF w']
  note lb = inv_lanes_bytes[OF ns(2,3)]
  have c: "inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim M))
             (list_update_func (lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) c1) (un j) (\<lambda>_. mk_lane__0 J k)) =
           mk_uN (vsum N (ns[un j := k]))"
    using lb'(1) ns(1) M Nj jn by (simp add: list_update_func_map)
  have S: "serialise_v128 (tr_v128 c1) = concat (map ?f ns)"
    using v128_bytes[OF c1] lb(3) ns(4) Nj by simp
  have ch: "list_all (\<lambda>x. length x = ?k) (map ?f ns)" by (simp add: list_all_iff)
  have ins: "insert_lane_vec_bs ?k (un j) (le_bytes ?k (un k)) (serialise_v128 (tr_v128 c1)) = le_bytes 16 (vsum N (ns[un j := k]))"
    using concat_chunks_update[OF ch, of "un j" "?f k"] jn lb'(3) S Nj
    by (simp add: insert_lane_vec_bs_def map_update)
  have ld: "load (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (vec_i_length (svi_of_bits N)) = Some (le_bytes ?k (un k))"
    using x1 bd u b' ibytes_tr[OF k] Nj by (simp add: load_def nat_of_int_tr_i32 tr_offset_def read_bytes_tr svi_of_jbits)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstVec (ConstVec128 (tr_v128 c1)),
               $Load_lane_vec (svi_of_bits N) (un j) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [$EConstVec (ConstVec128 (tr_v128 (mk_uN (vsum N (ns[un j := k])))))]"
    using reduce.load_lane_vec_Some[where v = "tr_v128 c1" and i = "un j" and a = "tr_align ao", OF smem_ind_tr[OF x1(2)] HOL.refl ld] ins deserialise_le_bytes lb'(2) Nj
    by (simp add: insert_lane_vec_def svi_of_jbits)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] c by (simp add: tr_vec_def)
qed

lemma sim_vload_lane_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and J: "fun_jsize J N"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat N / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, vc c1, admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz N) ao j)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have Nj: "N = jbits J" using J by (simp add: fun_jsize_iff)
  have ld: "load (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (vec_i_length (svi_of_bits N)) = None"
    using x1 b u Nj by (simp add: load_def nat_of_int_tr_i32 tr_offset_def svi_of_jbits)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstVec (ConstVec128 (tr_v128 c1)),
               $Load_lane_vec (svi_of_bits N) (un j) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.load_lane_vec_None[OF smem_ind_tr[OF x1(2)] HOL.refl ld])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_vec_def)
qed

(* Storing one lane, in bounds.  SpecTec's [vstore_lane_val] has no bounds
   premise ([Oob_store]), and [vstore_lane_oob] tests the lane width in bits
   ([Vstore_disagree]); see DIFFERENCES.md. *)
lemma sim_vstore_lane:
  assumes a: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" and u: "un u < 2 ^ 32" and J: "fun_jsize J N"
    and M: "M = 128 div N" and c: "wf_uN 128 c" and jl: "un j < M"
    and bd: "un u + un (OFFSET ao) + N div 8 \<le> length (BYTES (store_MEMS s ! (MEMS (frame_MODULE f) ! 0)))"
    and w: "fun_with_mem (mk_state s f) (mk_uN 0) (un u + un (OFFSET ao)) (nat \<lfloor>rat_of_nat N / rat_of_nat 8\<rfloor>)
              (ibytes_underscore N (mk_uN (proj_uN_0 (the (proj_lane__0 (lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) c ! un j)))))) z'"
  shows "sim (mk_config (mk_state s f) [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)])
             (mk_config z' [])"
proof -
  have Nj: "N = jbits J" using J by (simp add: fun_jsize_iff)
  obtain ns where ns: "lanes_underscore (X (lanetype_Jnn J) (mk_dim (128 div jbits J))) c = map (mk_lane__0 J) ns"
      "length ns = 128 div jbits J" "list_all (wf_uN (jbits J)) ns" "vsum (jbits J) ns = un c"
    using lanes_def[OF c, of J] by blast
  have jn: "un j < length ns" using jl ns(2) M Nj by simp
  let ?a = "MEMS (frame_MODULE f) ! 0"
  let ?mi = "store_MEMS s ! ?a"
  let ?p = "un u + un (OFFSET ao)"
  let ?k = "N div 8"
  let ?f = "\<lambda>i. le_bytes ?k (un i)"
  let ?bs = "ibytes_underscore N (ns ! un j)"
  have lane: "mk_uN (proj_uN_0 (the (proj_lane__0 (lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) c ! un j)))) = ns ! un j"
    using ns(1) M Nj jn by (cases "ns ! un j") simp
  have wj: "wf_uN N (ns ! un j)" using ns(3) jn Nj by (simp add: list_all_length)
  let ?mi' = "?mi\<lparr>BYTES := list_slice_update (BYTES ?mi) ?p ?k ?bs\<rparr>"
  let ?s' = "s\<lparr>store_MEMS := list_update_func (store_MEMS s) ?a (\<lambda>m. m\<lparr>BYTES := list_slice_update (BYTES m) ?p ?k ?bs\<rparr>)\<rparr>"
  have z: "z' = mk_state ?s' f" using w lane by (auto elim!: fun_with_mem.cases)
  have m0: "0 < length (MEMS (frame_MODULE f))" using w by (auto elim: fun_with_mem.cases)
  have len: "length ?bs = ?k" using arg_cong[OF ibytes_tr[OF wj], of length] by simp
  note lb = inv_lanes_bytes[OF ns(2,3)]
  have ch: "list_all (\<lambda>x. length x = ?k) (map ?f ns)" by (simp add: list_all_iff)
  have sb: "store_serialise_vec (Store_lane (svi_of_bits N) (un j)) (tr_v128 c) = map tr_byte ?bs"
    using concat_chunks_take_drop[OF ch, of "un j"] jn v128_bytes[OF c] lb(3) ns(4) Nj ibytes_tr[OF wj]
    by (simp add: store_serialise_vec_def svi_of_jbits)
  have sv: "store (s.mems (tr_store s) ! ?a) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (store_serialise_vec (Store_lane (svi_of_bits N) (un j)) (tr_v128 c))
              (length (store_serialise_vec (Store_lane (svi_of_bits N) (un j)) (tr_v128 c))) = Some (tr_meminst ?mi')"
    using a bd u len write_bytes_tr[OF len bd] sb
    by (simp add: store_def nat_of_int_tr_i32 tr_offset_def bytes_takefill_def takefill_exact)
  have upd: "(tr_store s)\<lparr>s.mems := (s.mems (tr_store s))[?a := tr_meminst ?mi']\<rparr> = tr_store ?s'"
    using a by (simp add: tr_store_def map_list_update_func)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstVec (ConstVec128 (tr_v128 c)),
               $Store_vec (Store_lane (svi_of_bits N) (un j)) (tr_align ao) (tr_offset ao)]
              (tr_store ?s') (tr_frame f) []"
    using reduce.store_vec_Some[OF smem_ind_tr[OF m0] HOL.refl HOL.refl sv] upd by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] z by (simp add: tr_vec_def)
qed

(* A lane store out of bounds traps in both semantics.  SpecTec also traps
   when only the bit width overruns the memory ([Vstore_disagree]); that step
   is not simulated. *)
lemma sim_vstore_lane_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and J: "fun_jsize J N"
    and c: "wf_uN 128 c" and jl: "un j < 128 div N"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + N div 8"
  shows "sim (mk_config (mk_state s f) [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have Nj: "N = jbits J" using J by (simp add: fun_jsize_iff)
  have "(un j + 1) * (N div 8) \<le> 16"
  proof -
    have "un j + 1 \<le> 128 div N" using jl by simp
    then have "(un j + 1) * (N div 8) \<le> (128 div N) * (N div 8)" by (rule mult_le_mono1)
    then show ?thesis using jbits_div(2)[of J] Nj by (simp add: mult.commute)
  qed
  then have lsv: "length (store_serialise_vec (Store_lane (svi_of_bits N) (un j)) (tr_v128 c)) = N div 8"
    using Nj serialise_v128_len[OF HOL.refl, of "tr_v128 c"]
    by (simp add: store_serialise_vec_def svi_of_jbits algebra_simps)
  have sv: "store (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (store_serialise_vec (Store_lane (svi_of_bits N) (un j)) (tr_v128 c))
              (length (store_serialise_vec (Store_lane (svi_of_bits N) (un j)) (tr_v128 c))) = None"
    using x1 b u lsv by (simp add: store_def nat_of_int_tr_i32 tr_offset_def)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstVec (ConstVec128 (tr_v128 c)),
               $Store_vec (Store_lane (svi_of_bits N) (un j)) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.store_vec_None[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl sv])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_vec_def)
qed

end

section \<open>Packed vector loads\<close>

lemma bit_pow2_minus1: "bit ((2::nat) ^ n - Suc 0) i \<longleftrightarrow> i < n"
  using bit_mask_iff[of n i, where 'a = nat] by (simp add: mask_eq_exp_minus_1)

lemma nat_floor_div8_mult[simp]: "nat \<lfloor>rat_of_nat a * rat_of_nat b / 8\<rfloor> = a * b div 8"
  using nat_floor_div8[of "a * b"] by simp

lemma bit_top_nat: "(x::nat) < 2 ^ Suc n \<Longrightarrow> bit x n \<longleftrightarrow> 2 ^ n \<le> x"
proof -
  assume x: "x < 2 ^ Suc n"
  have "x div 2 ^ n < 2" using x by (simp add: div_less_iff_less_mult mult.commute)
  then have d: "x div 2 ^ n = 0 \<or> x div 2 ^ n = 1" by linarith
  have e: "x div 2 ^ n = 0 \<longleftrightarrow> x < 2 ^ n" by (simp add: div_eq_0_iff)
  show ?thesis
  proof (cases "x div 2 ^ n = 0")
    case True then show ?thesis using e by (simp add: bit_nat_def)
  next
    case False then have "x div 2 ^ n = 1" using d by simp
    then show ?thesis using e False by (simp add: bit_nat_def)
  qed
qed

lemma msb_le_bytes:
  assumes "0 < k" "x < 2 ^ (8 * k)"
  shows "msb_byte (msbyte (le_bytes k x)) \<longleftrightarrow> 2 ^ (8 * k - 1) \<le> x"
proof -
  have l: "last (le_bytes k x) = byte_of_nat (x div 2 ^ (8 * (k - 1)))"
    using assms(1) by (simp add: le_bytes_def last_map)
  have "msb_byte (msbyte (le_bytes k x)) \<longleftrightarrow> bit (Rep_uint8 (byte_of_nat (x div 2 ^ (8 * (k - 1))))) 7"
    by (simp add: msb_byte_def msbyte_def l msb_uint8.rep_eq msb_nth)
  also have "\<dots> \<longleftrightarrow> bit x (8 * k - 1)"
  proof -
    have "8 * (k - 1) + 7 = 8 * k - 1" using assms(1) by simp
    then show ?thesis by (simp add: bit_byte_of_nat_div)
  qed
  also have "\<dots> \<longleftrightarrow> 2 ^ (8 * k - 1) \<le> x"
    by (rule bit_top_nat) (use assms in simp)
  finally show ?thesis .
qed

lemma le_bytes_ones: "le_bytes k (2 ^ (8 * k) - 1) = replicate k negone_byte"
proof (rule nth_equalityI)
  fix j assume "j < length (le_bytes k (2 ^ (8 * k) - 1))"
  then have j: "j < k" by simp
  have "le_bytes k (2 ^ (8 * k) - 1) ! j = negone_byte"
  proof (simp only: nth_le_bytes[OF j], rule byte_eqI)
    fix m :: nat assume m: "m < 8"
    then have "8 * j + m < 8 * k" using j by linarith
    then show "bit (Rep_uint8 (byte_of_nat ((2 ^ (8 * k) - 1) div 2 ^ (8 * j)))) m = bit (Rep_uint8 negone_byte) m"
      using m bit_pow2_minus1[of "8 * k" "8 * j + m"]
      by (simp add: bit_byte_of_nat_div negone_byte_def uminus_uint8.rep_eq one_uint8.rep_eq bit_minus_1_iff)
  qed
  then show "le_bytes k (2 ^ (8 * k) - 1) ! j = replicate k negone_byte ! j" using j by simp
qed simp

lemma takefill_append_replicate: "length xs \<le> n \<Longrightarrow> takefill b n xs = xs @ replicate (n - length xs) b"
  by (induct n arbitrary: xs) (auto simp: Suc_le_length_iff le_Suc_eq split: list.splits)

lemma sign_extend_le_bytes:
  assumes k: "0 < k" and x: "x < 2 ^ (8 * k)"
  shows "sign_extend Wasm_Ast.U (2 * k) (le_bytes k x) = le_bytes (2 * k) x"
    "sign_extend Wasm_Ast.S (2 * k) (le_bytes k x) =
       le_bytes (2 * k) (if x < 2 ^ (8 * k - 1) then x else x + 2 ^ (16 * k) - 2 ^ (8 * k))"
proof -
  have z: "takefill zero_byte (2 * k) (le_bytes k x) = le_bytes (2 * k) x"
    by (rule takefill_le_bytes) (use x in simp_all)
  show "sign_extend Wasm_Ast.U (2 * k) (le_bytes k x) = le_bytes (2 * k) x"
    by (simp add: sign_extend_def bytes_takefill_def z)
  show "sign_extend Wasm_Ast.S (2 * k) (le_bytes k x) =
       le_bytes (2 * k) (if x < 2 ^ (8 * k - 1) then x else x + 2 ^ (16 * k) - 2 ^ (8 * k))"
  proof (cases "x < 2 ^ (8 * k - 1)")
    case True
    then show ?thesis using msb_le_bytes[OF k x] z by (simp add: sign_extend_def bytes_takefill_def)
  next
    case False
    let ?y = "x + 2 ^ (16 * k) - 2 ^ (8 * k)"
    have p: "(2::nat) ^ (16 * k) = 2 ^ (8 * k) * 2 ^ (8 * k)" by (simp add: power_add[symmetric])
    have e: "?y = x + 2 ^ (8 * k) * (2 ^ (8 * k) - 1)" by (simp add: p diff_mult_distrib2)
    have ym: "?y mod 2 ^ (8 * k) = x" using x e by simp
    have yd: "?y div 2 ^ (8 * k) = 2 ^ (8 * k) - 1" using x e by simp
    have "le_bytes (k + k) ?y = le_bytes k x @ replicate k negone_byte"
      using le_bytes_append[of k k ?y] le_bytes_mod[of k ?y] ym yd le_bytes_ones[of k] by simp
    moreover have "takefill negone_byte (2 * k) (le_bytes k x) = le_bytes k x @ replicate k negone_byte"
      by (simp add: takefill_append_replicate)
    ultimately show ?thesis using False msb_le_bytes[OF k x] by (simp add: sign_extend_def bytes_takefill_def mult_2)
  qed
qed

lemma read_bytes_vec_concat:
  assumes "\<And>i. i < length js \<Longrightarrow> read_bytes m (ind + i * len) len = le_bytes len (un (js ! i))"
  shows "read_bytes_vec (length js) len sx m ind = concat (map (\<lambda>j. sign_extend sx (len * 2) (le_bytes len (un j))) js)"
  using assms
proof (induction js arbitrary: ind)
  case (Cons j js)
  have "read_bytes m ind len = le_bytes len (un j)" using Cons.prems[of 0] by simp
  moreover have "read_bytes_vec (length js) len sx m (ind + len) = concat (map (\<lambda>j. sign_extend sx (len * 2) (le_bytes len (un j))) js)"
    by (rule Cons.IH) (use Cons.prems in \<open>fastforce simp: algebra_simps\<close>)
  ultimately show ?case by simp
qed simp

lemma list_alli_aux_iff: "list_alli_aux f n xs \<longleftrightarrow> (\<forall>i < length xs. f (n + i) (xs ! i))"
proof (induction xs arbitrary: n)
  case (Cons x xs) then show ?case by (auto simp: nth_Cons' less_Suc_eq_0_disj)
qed simp

lemma list_alli_iff: "list_alli f xs \<longleftrightarrow> (\<forall>i < length xs. f i (xs ! i))"
  by (simp add: list_alli_def list_alli_aux_iff)

context simd_mem
begin

lemma extend_le_bytes:
  assumes "M = 8 * k" "0 < k" "wf_uN M j"
  shows "le_bytes (2 * k) (un (extend__underscore M (M * 2) sx j)) = sign_extend (tr_sx sx) (2 * k) (le_bytes k (un j))"
    "un (extend__underscore M (M * 2) sx j) < 2 ^ (M * 2)"
proof -
  have j: "un j < 2 ^ (8 * k)" using assms by (simp add: wf_uN_iff)
  have p: "(2::nat) ^ (8 * k * 2) = 2 ^ (16 * k)" by (simp add: mult.commute mult.left_commute)
  show "le_bytes (2 * k) (un (extend__underscore M (M * 2) sx j)) = sign_extend (tr_sx sx) (2 * k) (le_bytes k (un j))"
    using sign_extend_le_bytes[OF assms(2) j] assms(1) p by (cases sx) (simp_all add: extend_def)
  have A: "(2::nat) ^ (8 * k) \<le> 2 ^ (8 * k) * 2 ^ (8 * k)" by simp
  have p2: "(2::nat) ^ (M * 2) = 2 ^ (8 * k) * 2 ^ (8 * k)" by (simp only: assms(1) mult_2_right power_add)
  have p3: "(2::nat) ^ M = 2 ^ (8 * k)" using assms(1) by simp
  have jA: "un j < 2 ^ (8 * k) * 2 ^ (8 * k)" by (rule less_le_trans[OF j A])
  have p4: "(2::nat) ^ (16 * k) = 2 ^ (8 * k) * 2 ^ (8 * k)" by (simp add: power_add[symmetric])
  show "un (extend__underscore M (M * 2) sx j) < 2 ^ (M * 2)"
  proof (cases sx)
    case U then show ?thesis unfolding p2 using jA by (simp add: extend_def)
  next
    case S
    have "un j + 2 ^ (8 * k) * 2 ^ (8 * k) - 2 ^ (8 * k) < 2 ^ (8 * k) * 2 ^ (8 * k)" using j A by linarith
    then show ?thesis unfolding p2 using S jA assms(1) p p4 by (simp add: extend_def)
  qed
qed

(* A packed load: [N] lanes of [M] bits, each sign- or zero-extended to [2 M]
   bits.  SpecTec's [vload_shape_val] does not require the loaded [M]-bit values
   to be [M]-bit values ([wj]); see DIFFERENCES.md. *)
lemma sim_vload_shape:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and J: "fun_jsize J (M * 2)"
    and Ms: "M = 8 \<or> M = 16 \<or> M = 32" and N: "N = length js" "N * (M * 2) = 128"
    and wj: "list_all (wf_uN M) js"
    and b: "\<And>i. i < length js \<Longrightarrow>
              ibytes_underscore M (js ! i) = list_slice (BYTES mi) (un u + un (OFFSET ao) + i * (M div 8)) (M div 8)"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore (mk_sz M) N sx)) ao)])
             (mk_config (mk_state s f) [vc (inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim N))
                (map (\<lambda>j. mk_lane__0 J (extend__underscore M (M * 2) sx j)) js))])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  let ?k = "M div 8"
  let ?p = "un u + un (OFFSET ao)"
  let ?ls = "map (extend__underscore M (M * 2) sx) js"
  have Mk: "M = 8 * ?k" "0 < ?k" using Ms by auto
  have Jw: "jbits J = M * 2" using J by (simp add: fun_jsize_iff)
  have Nd: "N = 128 div jbits J" using N(2) Jw Ms by auto
  have N0: "0 < N" using N(2) by (cases N) auto
  have wfj: "\<And>i. i < length js \<Longrightarrow> wf_uN M (js ! i)" using wj by (simp add: list_all_length)
  have rb: "\<And>i. i < length js \<Longrightarrow> read_bytes (tr_meminst mi) (?p + i * ?k) ?k = le_bytes ?k (un (js ! i))"
  proof -
    fix i assume i: "i < length js"
    show "read_bytes (tr_meminst mi) (?p + i * ?k) ?k = le_bytes ?k (un (js ! i))"
      using b[OF i] ibytes_tr[OF wfj[OF i]] by (simp add: read_bytes_tr)
  qed
  have bd: "?p + N * ?k \<le> length (BYTES mi)"
  proof -
    have i: "N - 1 < length js" using N N0 by simp
    have "length (ibytes_underscore M (js ! (N - 1))) = ?k"
      using arg_cong[OF ibytes_tr[OF wfj[OF i]], of length] by simp
    then have "?p + (N - 1) * ?k + ?k \<le> length (BYTES mi)"
      using list_slice_bound[of "BYTES mi" "?p + (N - 1) * ?k" ?k] b[OF i] Mk(2) by simp
    moreover have "(N - 1) * ?k + ?k = N * ?k" using N0 by (cases N) simp_all
    ultimately show ?thesis by simp
  qed
  have tp: "tp_vec_num (tpv_of_bits M) = N" "tp_vec_length (tpv_of_bits M) = ?k"
    using Ms N(2) by (auto simp: tpv_of_bits_def tp_vec_num_def tp_vec_length_def)
  have wl: "length ?ls = 128 div jbits J" "list_all (wf_uN (jbits J)) ?ls"
    using N Nd Jw extend_le_bytes(2)[OF Mk] wfj by (auto simp: list_all_length wf_uN_iff)
  note lb = inv_lanes_bytes[OF wl]
  have c: "inv_lanes_underscore (X (lanetype_Jnn J) (mk_dim N)) (map (\<lambda>j. mk_lane__0 J (extend__underscore M (M * 2) sx j)) js) =
           mk_uN (vsum (jbits J) ?ls)"
    using lb(1) Nd by (simp add: comp_def)
  have e8: "jbits J div 8 = 2 * ?k" "?k * 2 = 2 * ?k" using Jw Ms by auto
  have cb: "le_bytes 16 (vsum (jbits J) ?ls) = concat (map (\<lambda>j. sign_extend (tr_sx sx) (?k * 2) (le_bytes ?k (un j))) js)"
  proof -
    have "map (\<lambda>i. le_bytes (jbits J div 8) (un i)) ?ls = map (\<lambda>j. sign_extend (tr_sx sx) (?k * 2) (le_bytes ?k (un j))) js"
      using extend_le_bytes(1)[OF Mk] wj e8(1) by (auto simp: list_all_iff e8(2) intro!: map_cong)
    then show ?thesis using lb(3) by (simp only:)
  qed
  have ld: "load_vec (tr_vloadop (Some (SHAPEX_underscore (mk_sz M) N sx))) (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0))
              (nat_of_int (tr_i32 u)) (tr_offset ao) = Some (le_bytes 16 (vsum (jbits J) ?ls))"
    using x1 bd u tp read_bytes_vec_concat[of js "tr_meminst mi" ?p ?k "tr_sx sx", OF rb] cb N(1)
    by (simp add: load_vec_def load_packed_vec_def nat_of_int_tr_i32 tr_offset_def add.assoc)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load_vec (tr_vloadop (Some (SHAPEX_underscore (mk_sz M) N sx))) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [$EConstVec (ConstVec128 (tr_v128 (mk_uN (vsum (jbits J) ?ls))))]"
    using reduce.load_vec_Some[OF smem_ind_tr[OF x1(2)] HOL.refl ld] deserialise_le_bytes lb(2) by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] c by (simp add: tr_vec_def del: tr_vloadop.simps)
qed

lemma sim_vload_shape_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32"
    and Ms: "M = 8 \<or> M = 16 \<or> M = 32" and N: "N * (M * 2) = 128"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat (M * N) / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore (mk_sz M) N sx)) ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have tp: "tp_vec_num (tpv_of_bits M) * tp_vec_length (tpv_of_bits M) = M * N div 8"
    using Ms N by (auto simp: tpv_of_bits_def tp_vec_num_def tp_vec_length_def)
  have ld: "load_vec (tr_vloadop (Some (SHAPEX_underscore (mk_sz M) N sx))) (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0))
              (nat_of_int (tr_i32 u)) (tr_offset ao) = None"
    using x1 b u tp by (simp add: load_vec_def load_packed_vec_def nat_of_int_tr_i32 tr_offset_def)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load_vec (tr_vloadop (Some (SHAPEX_underscore (mk_sz M) N sx))) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.load_vec_None[OF smem_ind_tr[OF x1(2)] HOL.refl ld])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp del: tr_vloadop.simps)
qed

end

end
