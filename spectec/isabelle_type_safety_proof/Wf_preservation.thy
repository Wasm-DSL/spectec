theory Wf_preservation
(* Imported Lemma Formulation, Proofs Added Manually *)
	imports isabelle_reference_output_wasm2 Typing_Simplified helper_lemmas
begin

(* Helper lemmas for the well-formedness proofs below *)

lemma wf_proj_simps:
  "proj_uN_0 (mk_uN n) = n"
  "res_bool True = 1" "res_bool False = 0"
  "size valtype_I32 = Some 32" "size valtype_I64 = Some 64"
  "size valtype_F32 = Some 32" "size valtype_F64 = Some 64" "size valtype_V128 = Some 128"
  "valtype_Inn Inn_I32 = valtype_I32" "valtype_Inn Inn_I64 = valtype_I64"
  "numtype_Inn Inn_I32 = I32" "numtype_Inn Inn_I64 = I64"
  "numtype_Fnn Fnn_F32 = F32" "numtype_Fnn Fnn_F64 = F64"
  "valtype_vectype V128 = valtype_V128"
  "sizenn I32 = 32" "sizenn I64 = 64" "sizenn F32 = 32" "sizenn F64 = 64"
  by (simp_all add: proj_uN_0.psimps proj_uN_0.domintros res_bool.psimps res_bool.domintros
      size.psimps size.domintros valtype_Inn.psimps valtype_Inn.domintros
      numtype_Inn.psimps numtype_Inn.domintros numtype_Fnn.psimps numtype_Fnn.domintros valtype_vectype.psimps valtype_vectype.domintros
      sizenn.psimps sizenn.domintros valtype_numtype.psimps valtype_numtype.domintros)

lemma wf_uN_iff: "wf_uN N (mk_uN i) \<longleftrightarrow> i \<le> 2 ^ N - 1"
  by (simp add: wf_uN.simps wf_proj_simps)

lemma wf_uN_proj_le: "wf_uN N x \<Longrightarrow> proj_uN_0 x \<le> 2 ^ N - 1"
  by (auto elim: wf_uN.cases simp: wf_proj_simps)

lemma wf_uN_lt: "i < 2 ^ N \<Longrightarrow> wf_uN N (mk_uN i)"
  by (simp add: wf_uN_iff)

lemma wf_uN_mod: "wf_uN N (mk_uN (x mod 2 ^ N))"
  by (rule wf_uN_lt) simp

lemma wf_uN_res_bool: "wf_uN 32 (mk_uN (res_bool b))"
  by (cases b) (simp_all add: wf_uN_iff wf_proj_simps)

lemma wf_uN_le_proj: "wf_uN N x \<Longrightarrow> i \<le> proj_uN_0 x \<Longrightarrow> wf_uN N (mk_uN i)"
  using wf_uN_proj_le[of N x] by (simp add: wf_uN_iff wf_proj_simps)

lemma pow_pred_lt: "i < 2 ^ (N - 1) \<Longrightarrow> i < (2::nat) ^ N"
  by (metis diff_le_self less_le_trans one_le_numeral power_increasing)

lemma inv_signed_bound: "fun_inv_signed_underscore N i j \<Longrightarrow> wf_uN N (mk_uN j)"
  by (auto elim!: fun_inv_signed_underscore.cases intro: wf_uN_lt[OF pow_pred_lt] simp: wf_proj_simps)

lemma wf_num_I32: "wf_uN 32 x \<Longrightarrow> wf_num_underscore I32 (mk_num__0 Inn_I32 x)"
  using num__case_0[of Inn_I32 x I32] by (simp add: wf_proj_simps)

lemma wf_fN_fzero: "wf_fN N (fzero M)"
  by (simp add: fzero.psimps fzero.domintros wf_fN.simps wf_fNmag.simps wf_proj_simps)

lemma testop_wf_I32:
  "fun_testop_underscore nt op n = Some r \<Longrightarrow> wf_num_underscore I32 r"
  by (cases "(nt, op, n)" rule: fun_testop_underscore.cases)
     (auto simp: fun_testop_underscore.psimps fun_testop_underscore.domintros
        ieqz_underscore.psimps ieqz_underscore.domintros wf_uN_res_bool wf_num_I32 wf_proj_simps)

(* Inversion lemmas for well-formedness of instructions, specialised per constructor *)
inductive_simps wf_admininstr_sc_simps:
  "wf_admininstr (admininstr_sc0 x)" "wf_admininstr (admininstr_sc1 x)"
  "wf_admininstr (admininstr_sc2 x)" "wf_admininstr (admininstr_sc3 x)"
  "wf_admininstr (admininstr_sc4 x)" "wf_admininstr (admininstr_sc5 x)"
  "wf_admininstr (admininstr_sc6 x)" "wf_admininstr (admininstr_sc7 x)"
  "wf_admininstr (admininstr_sc8 x)"

inductive_simps wf_instr_sc_simps:
  "wf_instr (instr_sc0 x)" "wf_instr (instr_sc1 x)" "wf_instr (instr_sc2 x)"
  "wf_instr (instr_sc3 x)" "wf_instr (instr_sc4 x)" "wf_instr (instr_sc5 x)"
  "wf_instr (instr_sc6 x)" "wf_instr (instr_sc7 x)"

inductive_simps wf_val_simps:
  "wf_val (val_CONST nt c)" "wf_val (val_VCONST vt c)" "wf_val (val_REF_NULL rt)"
  "wf_val (val_REF_FUNC_ADDR a)" "wf_val (val_REF_HOST_ADDR a)"

lemma wf_admininstr_val_iff: "wf_admininstr (admininstr_val v) \<longleftrightarrow> wf_val v"
  using wf_admininstr_val wf_admininstr_val_inv by blast

lemma wf_admininstr_instr_iff: "wf_admininstr (admininstr_instr e) \<longleftrightarrow> wf_instr e"
  using wf_admininstr_instr wf_admininstr_instr_inv by blast

(* Evaluation lemmas for the small total functions on types and sizes *)
lemma type_fun_simps:
  "lanetype_Jnn Jnn_I32 = lanetype_I32" "lanetype_Jnn Jnn_I64 = lanetype_I64"
  "lanetype_Jnn Jnn_I8 = lanetype_I8" "lanetype_Jnn Jnn_I16 = lanetype_I16"
  "Jnn_Inn Inn_I32 = Jnn_I32" "Jnn_Inn Inn_I64 = Jnn_I64"
  "Jnn_packtype I8 = Jnn_I8" "Jnn_packtype I16 = Jnn_I16"
  "lanetype_packtype I8 = lanetype_I8" "lanetype_packtype I16 = lanetype_I16"
  "lanetype_numtype I32 = lanetype_I32" "lanetype_numtype I64 = lanetype_I64"
  "lanetype_numtype F32 = lanetype_F32" "lanetype_numtype F64 = lanetype_F64"
  "lanetype_Fnn Fnn_F32 = lanetype_F32" "lanetype_Fnn Fnn_F64 = lanetype_F64"
  "lanetype_Inn Inn_I32 = lanetype_I32" "lanetype_Inn Inn_I64 = lanetype_I64"
  "valtype_numtype I32 = valtype_I32" "valtype_numtype I64 = valtype_I64"
  "valtype_numtype F32 = valtype_F32" "valtype_numtype F64 = valtype_F64"
  "valtype_Fnn Fnn_F32 = valtype_F32" "valtype_Fnn Fnn_F64 = valtype_F64"
  "psize I8 = 8" "psize I16 = 16"
  "lsize lanetype_I32 = 32" "lsize lanetype_I64 = 64" "lsize lanetype_F32 = 32"
  "lsize lanetype_F64 = 64" "lsize lanetype_I8 = 8" "lsize lanetype_I16 = 16"
  "lsizenn lt = lsize lt"
  "unpack lanetype_I32 = I32" "unpack lanetype_I64 = I64" "unpack lanetype_F32 = F32"
  "unpack lanetype_F64 = F64" "unpack lanetype_I8 = I32" "unpack lanetype_I16 = I32"
  by (simp_all add: lanetype_Jnn.psimps lanetype_Jnn.domintros Jnn_Inn.psimps Jnn_Inn.domintros
      Jnn_packtype.psimps Jnn_packtype.domintros lanetype_packtype.psimps
      lanetype_packtype.domintros lanetype_numtype.psimps lanetype_numtype.domintros
      lanetype_Fnn.psimps lanetype_Fnn.domintros lanetype_Inn.psimps lanetype_Inn.domintros
      valtype_numtype.psimps valtype_numtype.domintros valtype_Fnn.psimps valtype_Fnn.domintros
      psize.psimps psize.domintros lsize.psimps lsize.domintros lsizenn.psimps lsizenn.domintros
      unpack.psimps unpack.domintros wf_proj_simps)

lemma shape_fun_simps:
  "fun_lanetype (X lt d) = lt" "proj_ishape_0 (mk_ishape sh) = sh"
  by (cases d, simp add: fun_lanetype.psimps fun_lanetype.domintros)
     (simp add: proj_ishape_0.psimps proj_ishape_0.domintros)

inductive_simps wf_num_ctor_simps:
  "wf_num_underscore nt (mk_num__0 inn x)" "wf_num_underscore nt (mk_num__1 fnn x)"

inductive_simps wf_lane_ctor_simps:
  "wf_lane_underscore lt (mk_lane__0 j x)" "wf_lane_underscore lt (mk_lane__1 f x)"

lemma wf_num_Inn_iff:
  "wf_num_underscore (numtype_Inn inn) (mk_num__0 inn x) \<longleftrightarrow> wf_uN (sizenn (numtype_Inn inn)) x"
  by (cases inn) (auto simp: wf_num_ctor_simps wf_proj_simps)

lemma wf_num_Fnn_iff:
  "wf_num_underscore (numtype_Fnn fnn) (mk_num__1 fnn x) \<longleftrightarrow> wf_fN (sizenn (numtype_Fnn fnn)) x"
  by (cases fnn) (auto simp: wf_num_ctor_simps)

lemma wf_uN_mod_lt: "0 < N \<Longrightarrow> wf_uN N (mk_uN (n mod N))"
  by (rule wf_uN_lt) (meson less_exp mod_less_divisor order.strict_trans)

lemma unop_I32_wf:
  "wf_num_underscore I32 n \<Longrightarrow> fun_unop__I32 op n \<noteq> None \<Longrightarrow>
   list_all (wf_num_underscore I32) (the (fun_unop__I32 op n))"
  by (cases "(op, n)" rule: fun_unop__I32.cases)
     (auto simp: fun_unop__I32.psimps fun_unop__I32.domintros wf_num_ctor_simps
       wf_proj_simps
       intro!: iclz__is_wf[OF _ HOL.refl] ictz__is_wf[OF _ HOL.refl] ipopcnt__is_wf[OF _ HOL.refl]
         extend___is_wf[OF _ HOL.refl] wrap___is_wf[OF _ HOL.refl])

lemma unop_I64_wf:
  "wf_num_underscore I64 n \<Longrightarrow> fun_unop__I64 op n \<noteq> None \<Longrightarrow>
   list_all (wf_num_underscore I64) (the (fun_unop__I64 op n))"
  by (cases "(op, n)" rule: fun_unop__I64.cases)
     (auto simp: fun_unop__I64.psimps fun_unop__I64.domintros wf_num_ctor_simps
       wf_proj_simps
       intro!: iclz__is_wf[OF _ HOL.refl] ictz__is_wf[OF _ HOL.refl] ipopcnt__is_wf[OF _ HOL.refl]
         extend___is_wf[OF _ HOL.refl] wrap___is_wf[OF _ HOL.refl])

lemma unop_F32_wf:
  "wf_num_underscore F32 n \<Longrightarrow> fun_unop__F32 op n \<noteq> None \<Longrightarrow>
   list_all (wf_num_underscore F32) (the (fun_unop__F32 op n))"
  by (cases "(op, n)" rule: fun_unop__F32.cases)
     (auto simp: fun_unop__F32.psimps fun_unop__F32.domintros wf_num_ctor_simps list.pred_map o_def
       intro!: fabs__is_wf[OF _ HOL.refl] fneg__is_wf[OF _ HOL.refl] fsqrt__is_wf[OF _ HOL.refl]
         fceil__is_wf[OF _ HOL.refl] ffloor__is_wf[OF _ HOL.refl] ftrunc__is_wf[OF _ HOL.refl]
         fnearest__is_wf[OF _ HOL.refl])

lemma unop_F64_wf:
  "wf_num_underscore F64 n \<Longrightarrow> fun_unop__F64 op n \<noteq> None \<Longrightarrow>
   list_all (wf_num_underscore F64) (the (fun_unop__F64 op n))"
  by (cases "(op, n)" rule: fun_unop__F64.cases)
     (auto simp: fun_unop__F64.psimps fun_unop__F64.domintros wf_num_ctor_simps list.pred_map o_def
       intro!: fabs__is_wf[OF _ HOL.refl] fneg__is_wf[OF _ HOL.refl] fsqrt__is_wf[OF _ HOL.refl]
         fceil__is_wf[OF _ HOL.refl] ffloor__is_wf[OF _ HOL.refl] ftrunc__is_wf[OF _ HOL.refl]
         fnearest__is_wf[OF _ HOL.refl])

lemma size_variant_simps:
  "sizenn1 nt = sizenn nt" "sizenn2 nt = sizenn nt"
  "lsizenn1 lt = lsize lt" "lsizenn2 lt = lsize lt"
  by (simp_all add: sizenn1.psimps sizenn1.domintros sizenn2.psimps sizenn2.domintros
      sizenn.psimps sizenn.domintros lsizenn1.psimps lsizenn1.domintros
      lsizenn2.psimps lsizenn2.domintros)

lemma list_underscore_map_option:
  "list_underscore (map_option f x) = map f (option_to_list x)"
  by (cases x) (simp_all add: list_underscore.psimps list_underscore.domintros)

(* setproduct: termination and membership *)
lemma setproduct2_dom: "setproduct2_underscore_dom (w, lss)"
  by (induction lss) (auto intro: setproduct2_underscore.domintros)

lemma setproduct1_dom: "setproduct1_underscore_dom (ws, lss)"
  by (induction ws) (auto intro: setproduct1_underscore.domintros)

lemma setproduct_dom: "setproduct_underscore_dom xss"
  by (induction xss) (auto intro: setproduct_underscore.domintros)

lemmas setproduct_simps =
  setproduct2_underscore.psimps[OF setproduct2_dom] setproduct1_underscore.psimps[OF setproduct1_dom]
  setproduct_underscore.psimps[OF setproduct_dom]

lemma setproduct2_mem: "ys \<in> set (setproduct2_underscore w lss) \<Longrightarrow> \<exists>l\<in>set lss. ys = w # l"
  by (induction lss) (auto simp: setproduct_simps)

lemma setproduct1_mem:
  "ys \<in> set (setproduct1_underscore ws lss) \<Longrightarrow> \<exists>w\<in>set ws. \<exists>l\<in>set lss. ys = w # l"
  by (induction ws) (auto simp: setproduct_simps dest: setproduct2_mem)

lemma setproduct_mem: "ys \<in> set (setproduct_underscore xss) \<Longrightarrow> list_all2 (\<lambda>y xs. y \<in> set xs) ys xss"
  by (induction xss arbitrary: ys) (auto simp: setproduct_simps dest!: setproduct1_mem)

lemma setproduct_list_all:
  assumes "ys \<in> set (setproduct_underscore xss)" "list_all (list_all P) xss"
  shows "list_all P ys"
proof -
  have "list_all2 (\<lambda>y xs. y \<in> set xs) ys xss" by (rule setproduct_mem[OF assms(1)])
  then show ?thesis using assms(2) by (induction rule: list_all2_induct) (auto simp: list_all_iff)
qed

lemma inv_lanes_setproduct_wf:
  "wf_shape sh \<Longrightarrow> list_all (list_all (wf_lane_underscore (fun_lanetype sh))) xss \<Longrightarrow>
   list_all (wf_uN 128) (map (inv_lanes_underscore sh) (setproduct_underscore xss))"
  by (auto simp: list_all_iff[of "wf_uN 128"] intro!: inv_lanes__is_wf[OF _ _ HOL.refl]
      dest: setproduct_list_all)

(* determinism of the signed-integer helper relations *)
lemma signed_det: "fun_signed_underscore N i a \<Longrightarrow> fun_signed_underscore N i b \<Longrightarrow> a = b"
  by (auto elim!: fun_signed_underscore.cases)

lemma iabs_det: "fun_iabs_underscore N i a \<Longrightarrow> fun_iabs_underscore N i b \<Longrightarrow> a = b"
  by (auto elim!: fun_iabs_underscore.cases dest: signed_det)

lemma list_all2_det:
  assumes "list_all2 R xs ls" "list_all2 R ys ls" "\<And>x y l. R x l \<Longrightarrow> R y l \<Longrightarrow> x = y"
  shows "xs = ys"
  using assms
proof (induction xs ls arbitrary: ys rule: list_all2_induct)
  case (Cons x xs l ls)
  from Cons.prems(1) obtain y ys' where ys: "ys = y # ys'" "R y l" "list_all2 R ys' ls"
    by (cases ys) simp_all
  have "x = y" using Cons.prems(2)[OF Cons.hyps(1) ys(2)] .
  moreover have "xs = ys'" using Cons.IH[OF ys(3) Cons.prems(2)] .
  ultimately show ?case using ys(1) by simp
qed simp

lemma iabs_lanes_eq:
  "list_all2 (\<lambda>v l. fun_iabs_underscore N (the (proj_lane__0 l)) v) xs ls \<Longrightarrow>
   list_all2 (\<lambda>v l. fun_iabs_underscore N (the (proj_lane__0 l)) v) ys ls \<Longrightarrow> xs = ys"
  by (erule list_all2_det, assumption, erule (1) iabs_det)

lemma inv_lanes_setproduct_wf':
  "wf_shape sh \<Longrightarrow> list_all (list_all (wf_lane_underscore (fun_lanetype sh))) xss \<Longrightarrow>
   list_all (\<lambda>x. wf_uN 128 (inv_lanes_underscore sh x)) (setproduct_underscore xss)"
  using inv_lanes_setproduct_wf[of sh xss] by (simp add: list.pred_map o_def)

lemma iabs_wf_transfer:
  "list_all2 (\<lambda>v l. fun_iabs_underscore N (the (proj_lane__0 l)) v) xs ls \<Longrightarrow>
   list_all2 (\<lambda>v l. fun_iabs_underscore N (the (proj_lane__0 l)) v) ys ls \<Longrightarrow>
   list_all P xs \<Longrightarrow> list_all P ys"
  by (drule (1) iabs_lanes_eq) simp

lemma inv_signed_det:
  "fun_inv_signed_underscore N i a \<Longrightarrow> fun_inv_signed_underscore N i b \<Longrightarrow> a = b"
  by (auto elim!: fun_inv_signed_underscore.cases)

lemma imin_det: "fun_imin_underscore N sx i j a \<Longrightarrow> fun_imin_underscore N sx i j b \<Longrightarrow> a = b"
  by (auto elim!: fun_imin_underscore.cases dest: signed_det)

lemma imax_det: "fun_imax_underscore N sx i j a \<Longrightarrow> fun_imax_underscore N sx i j b \<Longrightarrow> a = b"
  by (auto elim!: fun_imax_underscore.cases dest: signed_det)

lemma iadd_sat_det:
  "fun_iadd_sat_underscore N sx i j a \<Longrightarrow> fun_iadd_sat_underscore N sx i j b \<Longrightarrow> a = b"
  by (auto elim!: fun_iadd_sat_underscore.cases dest: signed_det inv_signed_det)

lemma isub_sat_det:
  "fun_isub_sat_underscore N sx i j a \<Longrightarrow> fun_isub_sat_underscore N sx i j b \<Longrightarrow> a = b"
  by (auto elim!: fun_isub_sat_underscore.cases dest: signed_det inv_signed_det)

lemma ilt_det: "fun_ilt_underscore N sx i j a \<Longrightarrow> fun_ilt_underscore N sx i j b \<Longrightarrow> a = b"
  by (auto elim!: fun_ilt_underscore.cases dest: signed_det)

lemma igt_det: "fun_igt_underscore N sx i j a \<Longrightarrow> fun_igt_underscore N sx i j b \<Longrightarrow> a = b"
  by (auto elim!: fun_igt_underscore.cases dest: signed_det)

lemma ile_det: "fun_ile_underscore N sx i j a \<Longrightarrow> fun_ile_underscore N sx i j b \<Longrightarrow> a = b"
  by (auto elim!: fun_ile_underscore.cases dest: signed_det)

lemma ige_det: "fun_ige_underscore N sx i j a \<Longrightarrow> fun_ige_underscore N sx i j b \<Longrightarrow> a = b"
  by (auto elim!: fun_ige_underscore.cases dest: signed_det)

lemma list_all3_det:
  assumes "list_all3 R xs as bs" "list_all3 R ys as bs"
          "\<And>x y a b. R x a b \<Longrightarrow> R y a b \<Longrightarrow> x = y"
  shows "xs = ys"
  using assms(1,2)
proof (induction xs arbitrary: ys as bs)
  case Nil
  then show ?case by (auto elim: list_all3.cases)
next
  case (Cons x xs)
  from Cons.prems(1) obtain a as' b bs' where xs: "as = a # as'" "bs = b # bs'" "R x a b"
      "list_all3 R xs as' bs'"
    by (auto elim: list_all3.cases)
  from Cons.prems(2) xs(1,2) obtain y ys' where ys: "ys = y # ys'" "R y a b" "list_all3 R ys' as' bs'"
    by (auto elim: list_all3.cases)
  have "x = y" using assms(3)[OF xs(3) ys(2)] .
  moreover have "xs = ys'" using Cons.IH[OF xs(4) ys(3)] .
  ultimately show ?case using ys(1) by simp
qed

(* Two result lists related to the same inputs by a deterministic relation are equal, so a
   property of one transfers to the other. *)
lemma list_all3_transfer:
  "list_all3 R xs as bs \<Longrightarrow> list_all3 R ys as bs \<Longrightarrow>
   (\<And>x y a b. R x a b \<Longrightarrow> R y a b \<Longrightarrow> x = y) \<Longrightarrow> list_all P xs \<Longrightarrow> list_all P ys"
  using list_all3_det by metis

lemma list_all_zipWith:
  "list_all2 (\<lambda>a b. P (f a b)) xs ys \<Longrightarrow> list_all P (list_zipWith f xs ys)"
  by (induction rule: list_all2_induct) (simp_all add: list_zipWith_def)

lemma inv_lanes_setproduct_mem:
  "v \<in> set (map (inv_lanes_underscore sh) (setproduct_underscore xss)) \<Longrightarrow> wf_shape sh \<Longrightarrow>
   list_all (list_all (wf_lane_underscore (fun_lanetype sh))) xss \<Longrightarrow> wf_uN 128 v"
  using inv_lanes_setproduct_wf[of sh xss] by (auto simp: list_all_iff)

lemma lanes_wf:
  "wf_shape (X lt d) \<Longrightarrow> wf_uN 128 c \<Longrightarrow> list_all (wf_lane_underscore lt) (lanes_underscore (X lt d) c)"
  using lanes__is_wf[of "X lt d" c] by (simp add: shape_fun_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:281.6-281.11 *)
lemma zero_is_wf :
	"(ret_val = (fun_zero v_numtype)) \<Longrightarrow>
	 (wf_num_underscore v_numtype ret_val)"
  by (cases v_numtype)
     (simp_all add: fun_zero.psimps fun_zero.domintros wf_num_underscore.simps wf_uN_iff
       wf_fN_fzero sizenn.psimps sizenn.domintros wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 *)
lemma unop__is_wf :
	"(wf_unop_underscore v_numtype v_unop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 ((fun_unop_underscore v_numtype v_unop_underscore v_num_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the ((fun_unop_underscore v_numtype v_unop_underscore v_num_underscore)))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: num_underscore). (wf_num_underscore v_numtype ret_val)) ret_val_lst"
  by (cases v_numtype)
     (auto simp: fun_unop_underscore.psimps fun_unop_underscore.domintros
       intro: unop_I32_wf unop_I64_wf unop_F32_wf unop_F64_wf)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.6-105.12 *)
lemma iadd__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (iadd_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (simp add: iadd_underscore.psimps iadd_underscore.domintros wf_uN_mod wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.6-107.12 *)
lemma imul__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (imul_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (simp add: imul_underscore.psimps imul_underscore.domintros wf_uN_mod wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
lemma irem__is_wf :
	"(fun_irem_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val_opt = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
  by (auto elim!: fun_irem_underscore.cases intro: wf_uN_le_proj[OF _ diff_le_self] inv_signed_bound
      simp: wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.6-106.12 *)
lemma isub__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (isub_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (simp add: isub_underscore.psimps isub_underscore.domintros wf_uN_mod wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 *)
lemma testop__is_wf :
	"(wf_testop_underscore v_numtype v_testop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 ((fun_testop_underscore v_numtype v_testop_underscore v_num_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((fun_testop_underscore v_numtype v_testop_underscore v_num_underscore)))) \<Longrightarrow>
	 (wf_num_underscore I32 ret_val)"
  by (metis option.collapse testop_wf_I32)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
lemma relop__is_wf :
	"(fun_relop_underscore v_numtype v_relop_underscore v_num_underscore num__0 var_0) \<Longrightarrow>
	 (wf_relop_underscore v_numtype v_relop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype num__0) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_num_underscore I32 ret_val)"
  by (auto elim!: fun_relop_underscore.cases wf_num_underscore.cases
      intro!: wf_num_I32 wf_uN_res_bool
      elim: fun_ilt_underscore.cases fun_igt_underscore.cases fun_ile_underscore.cases
        fun_ige_underscore.cases
      intro: feq__is_wf fne__is_wf flt__is_wf
        fgt__is_wf fle__is_wf fge__is_wf
      simp: ieq_underscore.psimps ieq_underscore.domintros ine_underscore.psimps
        ine_underscore.domintros wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
lemma cvtop___is_wf :
	"(fun_cvtop__underscore numtype_1 numtype_2 v_cvtop__underscore v_num_underscore var_0) \<Longrightarrow>
	 (wf_cvtop__underscore numtype_1 numtype_2 v_cvtop__underscore) \<Longrightarrow>
	 (wf_num_underscore numtype_1 v_num_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the (var_0))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: num_underscore). (wf_num_underscore numtype_2 ret_val)) ret_val_lst"
  by (auto elim!: fun_cvtop__underscore.cases simp: wf_num_ctor_simps list.pred_map o_def
      wf_proj_simps size_variant_simps list_underscore_map_option
      intro!: extend___is_wf[OF _ HOL.refl] wrap___is_wf[OF _ HOL.refl]
        convert___is_wf[OF _ HOL.refl] promote___is_wf[OF _ HOL.refl]
        demote___is_wf[OF _ HOL.refl] trunc___is_wf[OF _ HOL.refl]
        trunc_sat___is_wf[OF _ HOL.refl] reinterpret___is_wf[OF _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.6-133.12 *)
lemma ineg__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (ineg_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (simp add: ineg_underscore.psimps ineg_underscore.domintros wf_uN_mod wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
lemma iabs__is_wf :
	"(fun_iabs_underscore v_N v_iN var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (auto elim!: fun_iabs_underscore.cases simp: wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
lemma imin__is_wf :
	"(fun_imin_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (auto elim!: fun_imin_underscore.cases simp: wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
lemma imax__is_wf :
	"(fun_imax_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (auto elim!: fun_imax_underscore.cases simp: wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
lemma iadd_sat__is_wf :
	"(fun_iadd_sat_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (auto elim!: fun_iadd_sat_underscore.cases intro: inv_signed_bound
      simp: sat_u_underscore.psimps sat_u_underscore.domintros wf_uN_iff wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
lemma isub_sat__is_wf :
	"(fun_isub_sat_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
  by (auto elim!: fun_isub_sat_underscore.cases intro: inv_signed_bound
      simp: sat_u_underscore.psimps sat_u_underscore.domintros wf_uN_iff wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.6-323.15 *)
lemma packnum__is_wf :
	"(wf_num_underscore (unpack v_lanetype) v_num_underscore) \<Longrightarrow>
	 ((packnum_underscore v_lanetype v_num_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((packnum_underscore v_lanetype v_num_underscore)))) \<Longrightarrow>
	 (wf_lane_underscore v_lanetype ret_val)"
  by (cases "(v_lanetype, v_num_underscore)" rule: packnum_underscore.cases)
     (auto simp: packnum_underscore.psimps packnum_underscore.domintros wf_num_ctor_simps
       wf_lane_ctor_simps wf_proj_simps type_fun_simps intro: wrap___is_wf[OF _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:329.6-329.17 *)
lemma unpacknum__is_wf :
	"(wf_lane_underscore v_lanetype v_lane_underscore) \<Longrightarrow>
	 ((unpacknum_underscore v_lanetype v_lane_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((unpacknum_underscore v_lanetype v_lane_underscore)))) \<Longrightarrow>
	 (wf_num_underscore (unpack v_lanetype) ret_val)"
  by (cases "(v_lanetype, v_lane_underscore)" rule: unpacknum_underscore.cases)
     (auto simp: unpacknum_underscore.psimps unpacknum_underscore.domintros wf_num_ctor_simps
       wf_lane_ctor_simps wf_proj_simps type_fun_simps intro: extend___is_wf[OF _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.6-364.14 *)
lemma vvunop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (ret_val = (vvunop_underscore v_vectype v_vvunop v_vec_underscore)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
  by (cases v_vectype; cases v_vvunop)
     (auto simp: vvunop_underscore.psimps vvunop_underscore.domintros
       wf_proj_simps
       intro: inot__is_wf[OF _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.6-366.15 *)
lemma vvbinop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__0) \<Longrightarrow>
	 (ret_val = (vvbinop_underscore v_vectype v_vvbinop v_vec_underscore vec__0)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
  by (cases v_vectype; cases v_vvbinop)
     (auto simp: vvbinop_underscore.psimps vvbinop_underscore.domintros
       wf_proj_simps
       intro: iand__is_wf[OF _ _ HOL.refl] iandnot__is_wf[OF _ _ HOL.refl]
         ior__is_wf[OF _ _ HOL.refl] ixor__is_wf[OF _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:368.6-368.16 *)
lemma vvternop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__0) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__1) \<Longrightarrow>
	 (ret_val = (vvternop_underscore v_vectype v_vvternop v_vec_underscore vec__0 vec__1)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
  by (cases v_vectype; cases v_vvternop)
     (auto simp: vvternop_underscore.psimps vvternop_underscore.domintros
       wf_proj_simps
       intro: ibitselect__is_wf[OF _ _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.13 *)
lemma vunop__is_wf :
	"(fun_vunop_underscore v_shape v_vunop_underscore v_vec_underscore var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vunop_underscore v_shape v_vunop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the (var_0))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: vec_underscore). (wf_uN 128 ret_val)) ret_val_lst"
  apply (erule fun_vunop_underscore.cases)
  apply (auto simp: list.pred_map o_def shape_fun_simps
      intro!: inv_lanes__is_wf[OF _ _ HOL.refl] inv_lanes_setproduct_wf')
  apply (blast intro: iabs_wf_transfer)+
  done

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
lemma vbinop__is_wf :
	"(fun_vbinop_underscore v_shape v_vbinop_underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vbinop_underscore v_shape v_vbinop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the (var_0))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: vec_underscore). (wf_uN 128 ret_val)) ret_val_lst"
  apply (erule fun_vbinop_underscore.cases)
  apply (auto simp: list.pred_map o_def shape_fun_simps
      intro!: inv_lanes__is_wf[OF _ _ HOL.refl] inv_lanes_setproduct_wf' list_all_zipWith)
  apply (blast intro: list_all3_transfer imin_det imax_det iadd_sat_det isub_sat_det ilt_det igt_det ile_det ige_det)+
  done

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.14 *)
lemma vrelop__is_wf :
	"(fun_vrelop_underscore v_shape v_vrelop_underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vrelop_underscore v_shape v_vrelop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
  apply (erule fun_vrelop_underscore.cases)
  apply (auto simp: list.pred_map o_def
      intro!: inv_lanes__is_wf[OF _ _ HOL.refl] list_all_zipWith)
  done

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:385.6-385.15 *)
lemma lcvtop___is_wf :
	"(fun_lcvtop__underscore shape_1 shape_2 v_vcvtop__underscore v_lane_underscore var_0) \<Longrightarrow>
	 (wf_shape shape_1) \<Longrightarrow>
	 (wf_shape shape_2) \<Longrightarrow>
	 (wf_vcvtop__underscore shape_1 shape_2 v_vcvtop__underscore) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype shape_1) v_lane_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the (var_0))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: lane_underscore). (wf_lane_underscore (fun_lanetype shape_2) ret_val)) ret_val_lst"
  apply (erule fun_lcvtop__underscore.cases)
  apply (auto simp: list.pred_map o_def wf_lane_ctor_simps wf_proj_simps type_fun_simps
      shape_fun_simps size_variant_simps list_underscore_map_option
      intro!: extend___is_wf[OF _ HOL.refl] wrap___is_wf[OF _ HOL.refl]
        convert___is_wf[OF _ HOL.refl] promote___is_wf[OF _ HOL.refl]
        demote___is_wf[OF _ HOL.refl] trunc___is_wf[OF _ HOL.refl]
        trunc_sat___is_wf[OF _ HOL.refl])
  done

lemma lcvtop_lanes_wf:
  "list_all2 (\<lambda>v c. fun_lcvtop__underscore (X lt1 d1) (X lt2 d2) op c v) vs cs \<Longrightarrow>
   list_all (\<lambda>v. \<exists>y. v = Some y) vs \<Longrightarrow> list_all (wf_lane_underscore lt1) cs \<Longrightarrow>
   wf_shape (X lt1 d1) \<Longrightarrow> wf_shape (X lt2 d2) \<Longrightarrow>
   wf_vcvtop__underscore (X lt1 d1) (X lt2 d2) op \<Longrightarrow>
   list_all (list_all (wf_lane_underscore lt2)) (map the vs)"
proof (induction rule: list_all2_induct)
  case (Cons v vs c cs)
  then show ?case using lcvtop___is_wf[of "X lt1 d1" "X lt2 d2" op c v "the v"]
    by (auto simp: shape_fun_simps)
qed simp

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:387.6-387.15 *)
lemma vcvtop___is_wf :
	"(fun_vcvtop__underscore shape_1 shape_2 v_vcvtop__underscore v_vec_underscore var_0) \<Longrightarrow>
	 (wf_shape shape_1) \<Longrightarrow>
	 (wf_shape shape_2) \<Longrightarrow>
	 (wf_vcvtop__underscore shape_1 shape_2 v_vcvtop__underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
  apply (erule fun_vcvtop__underscore.cases)
  apply (auto simp: shape_fun_simps intro!: inv_lanes_setproduct_mem)
  subgoal by (rule lcvtop_lanes_wf) (auto intro: lanes_wf)
  subgoal by (rule lcvtop_lanes_wf) (auto intro: lanes_wf list_all_list_slice)
  subgoal by (rule lcvtop_lanes_wf) (auto intro: lanes_wf)
  subgoal
    by (rule list_all_repeat)
       (simp, metis option.distinct(1) option.sel packnum__is_wf zero_is_wf)
  done

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:603.6-603.17 *)
lemma vextunop___is_wf :
	"(fun_vextunop__underscore ishape_1 ishape_2 v_vextunop__underscore v_vec_underscore var_0) \<Longrightarrow>
	 (wf_ishape ishape_1) \<Longrightarrow>
	 (wf_ishape ishape_2) \<Longrightarrow>
	 (wf_vextunop__underscore ishape_1 ishape_2 v_vextunop__underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
  apply (erule fun_vextunop__underscore.cases)
  apply (auto simp: list.pred_map o_def
      intro!: inv_lanes__is_wf[OF _ _ HOL.refl] list_all_zipWith)
  done

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:605.6-605.18 *)
lemma vextbinop___is_wf :
	"(fun_vextbinop__underscore ishape_1 ishape_2 v_vextbinop__underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_ishape ishape_1) \<Longrightarrow>
	 (wf_ishape ishape_2) \<Longrightarrow>
	 (wf_vextbinop__underscore ishape_1 ishape_2 v_vextbinop__underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
  apply (erule fun_vextbinop__underscore.cases)
  apply (auto simp: list.pred_map o_def
      intro!: inv_lanes__is_wf[OF _ _ HOL.refl] list_all_zipWith)
  done

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:628.6-628.16 *)
lemma vshiftop__is_wf :
	"(fun_vshiftop_underscore v_ishape v_vshiftop_underscore v_lane_underscore v_u32 var_0) \<Longrightarrow>
	 (wf_ishape v_ishape) \<Longrightarrow>
	 (wf_vshiftop_underscore v_ishape v_vshiftop_underscore) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype (proj_ishape_0 v_ishape)) v_lane_underscore) \<Longrightarrow>
	 (wf_uN 32 v_u32) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype (proj_ishape_0 v_ishape)) ret_val)"
  by (auto elim!: fun_vshiftop_underscore.cases simp: wf_lane_ctor_simps type_fun_simps
      intro!: ishl__is_wf[OF _ _ HOL.refl] ishr__is_wf[OF _ _ HOL.refl] wf_uN_mod_lt)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.6-7.15 *)
lemma default__is_wf :
	"((default_underscore v_valtype) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((default_underscore v_valtype)))) \<Longrightarrow>
	 (wf_val ret_val)"
  by (cases v_valtype)
     (auto simp: default_underscore.psimps default_underscore.domintros wf_val.simps
       wf_num_underscore.simps wf_uN_iff wf_fN_fzero wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.6-78.10 *)
lemma mem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 (ret_val = (fun_mem v_state v_memidx)) \<Longrightarrow>
	 (wf_meminst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.10-6.19 *)
lemma wf_uN_of_suc_proj: "wf_uN N (mk_uN (Suc (proj_uN_0 l))) \<Longrightarrow> wf_uN N l"
  by (cases l) (simp add: wf_uN_iff wf_proj_simps)

lemma suc32: "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))
  = (32::nat)"
  by (simp add: eval_nat_numeral)

lemma wf_lane_simps:
  "fun_lanetype (X lt d) = lt" "proj_ishape_0 (mk_ishape sh) = sh"
  "unpack (lanetype_numtype nt) = nt"
  by (cases d, simp add: fun_lanetype.psimps fun_lanetype.domintros)
     (simp add: proj_ishape_0.psimps proj_ishape_0.domintros,
      cases nt, simp_all add: unpack.psimps unpack.domintros lanetype_numtype.psimps
        lanetype_numtype.domintros)

lemma list_all_mkseq: "list_all P (mkseq f n) \<longleftrightarrow> (\<forall>k<n. P (f k))"
  by (induction n) (auto simp: less_Suc_eq)

lemma binop_wf_mem:
  "fun_binop_underscore nt op c1 c2 (Some y) \<Longrightarrow> c \<in> set y \<Longrightarrow> wf_num_underscore nt c"
  by (auto elim!: fun_binop_underscore.cases simp: list_all_iff wf_proj_simps)

lemma unop_wf_mem:
  "fun_unop_underscore nt op c1 = Some y \<Longrightarrow> wf_unop_underscore nt op \<Longrightarrow>
   wf_num_underscore nt c1 \<Longrightarrow> c \<in> set y \<Longrightarrow> wf_num_underscore nt c"
  by (metis (no_types, lifting) list_all_iff option.distinct(1) option.sel unop__is_wf)

lemma cvtop_wf_mem:
  "fun_cvtop__underscore nt1 nt2 op c1 (Some y) \<Longrightarrow> wf_cvtop__underscore nt1 nt2 op \<Longrightarrow>
   wf_num_underscore nt1 c1 \<Longrightarrow> c \<in> set y \<Longrightarrow> wf_num_underscore nt2 c"
  by (metis (no_types, lifting) list_all_iff option.distinct(1) option.sel cvtop___is_wf)

lemma vshiftop_lanes_wf:
  "list_all2 (\<lambda>v c'. fun_vshiftop_underscore (mk_ishape sh) op c' n v) vs cs \<Longrightarrow>
   list_all (\<lambda>v. \<exists>y. v = Some y) vs \<Longrightarrow>
   list_all (wf_lane_underscore (fun_lanetype sh)) cs \<Longrightarrow>
   wf_ishape (mk_ishape sh) \<Longrightarrow> wf_vshiftop_underscore (mk_ishape sh) op \<Longrightarrow> wf_uN 32 n \<Longrightarrow>
   list_all (wf_lane_underscore (fun_lanetype sh)) (map the vs)"
proof (induction rule: list_all2_induct)
  case (Cons v vs c cs)
  then show ?case
    using vshiftop__is_wf[of "mk_ishape sh" op c n v "the v"] by (auto simp: wf_proj_simps wf_lane_simps)
qed simp

lemma vv_size: "size (valtype_vectype V128) = Some 128"
  by (simp add: wf_proj_simps)

lemma vvunop_wf: "wf_uN 128 c \<Longrightarrow> wf_uN 128 (vvunop_underscore V128 op c)"
  using vvunop__is_wf[where v_vectype = V128 and v_vec_underscore = c and v_vvunop = op]
  by (simp add: vv_size wf_proj_simps)

lemma vvbinop_wf:
  "wf_uN 128 c1 \<Longrightarrow> wf_uN 128 c2 \<Longrightarrow> wf_uN 128 (vvbinop_underscore V128 op c1 c2)"
  using vvbinop__is_wf[where v_vectype = V128 and v_vec_underscore = c1 and ?vec__0.0 = c2
      and v_vvbinop = op]
  by (simp add: vv_size wf_proj_simps)

lemma vvternop_wf:
  "wf_uN 128 c1 \<Longrightarrow> wf_uN 128 c2 \<Longrightarrow> wf_uN 128 c3 \<Longrightarrow>
   wf_uN 128 (vvternop_underscore V128 op c1 c2 c3)"
  using vvternop__is_wf[where v_vectype = V128 and v_vec_underscore = c1 and ?vec__0.0 = c2
      and ?vec__1.0 = c3 and v_vvternop = op]
  by (simp add: vv_size wf_proj_simps)

lemma vunop_wf_mem:
  assumes "fun_vunop_underscore sh op c1 (Some y)" "wf_shape sh" "wf_vunop_underscore sh op"
          "wf_uN 128 c1" "c \<in> set y"
  shows "wf_uN 128 c"
  using vunop__is_wf[OF assms(1-4) _ HOL.refl] assms(5) by (simp add: list_all_iff)

lemma vbinop_wf_mem:
  assumes "fun_vbinop_underscore sh op c1 c2 (Some y)" "wf_shape sh" "wf_vbinop_underscore sh op"
          "wf_uN 128 c1" "wf_uN 128 c2" "c \<in> set y"
  shows "wf_uN 128 c"
  using vbinop__is_wf[OF assms(1-5) _ HOL.refl] assms(6) by (simp add: list_all_iff)

lemma vrelop_wf:
  assumes "fun_vrelop_underscore sh op c1 c2 (Some y)" "wf_shape sh" "wf_vrelop_underscore sh op"
          "wf_uN 128 c1" "wf_uN 128 c2"
  shows "wf_uN 128 y"
  using vrelop__is_wf[OF assms _ HOL.refl] by simp

lemma lanes_nth_wf:
  "wf_shape (X lt d) \<Longrightarrow> wf_uN 128 c \<Longrightarrow> k < length (lanes_underscore (X lt d) c) \<Longrightarrow>
   wf_lane_underscore lt (lanes_underscore (X lt d) c ! k)"
  by (metis lanes__is_wf list_all_length shape_fun_simps(1))

lemma Step_pure_is_wf_aux:
  assumes "Step_pure es es'" "list_all wf_admininstr es"
  shows "list_all wf_admininstr es'"
  using assms
  apply (induction rule: Step_pure.induct)
  apply (auto simp: wf_admininstr_sc_simps wf_instr_sc_simps wf_val_simps list.pred_map o_def
      wf_num_I32 wf_uN_iff wf_proj_simps wf_lane_simps wf_admininstr_val_iff
      wf_admininstr_instr_iff)
  (* br_succ *)
  subgoal for ins vs l es by (cases l) (simp add: wf_uN_iff wf_proj_simps)
  (* br_table_lt *)
  subgoal by (simp add: list_all_length)
  (* unop, binop, cvtop *)
  subgoal by (blast intro: unop_wf_mem)
  subgoal by (blast intro: binop_wf_mem)
  subgoal by (blast intro: cvtop_wf_mem)
  (* vvunop, vvbinop, vvternop *)
  subgoal by (rule vvunop_wf)
  subgoal by (rule vvbinop_wf)
  subgoal by (rule vvternop_wf)
  (* vunop, vbinop, vrelop *)
  subgoal by (rule vunop_wf_mem)
  subgoal by (rule vbinop_wf_mem)
  subgoal by (rule vrelop_wf)
  (* vshiftop *)
  subgoal for vs Jnn N op n c1
    apply (rule inv_lanes__is_wf[OF _ _ HOL.refl], assumption)
    using vshiftop_lanes_wf[where sh = "X (lanetype_Jnn Jnn) (mk_dim N)" and op = op
        and n = "mk_uN n" and vs = vs and cs = "lanes_underscore (X (lanetype_Jnn Jnn) (mk_dim N)) c1"]
    by (simp add: wf_uN_iff wf_proj_simps wf_lane_simps)
  (* vbitmask *)
  subgoal by (simp only: suc32) (blast intro: wf_num_I32 irev__is_wf[OF _ HOL.refl])
  (* vswizzle, vshuffle *)
  subgoal by (rule inv_lanes__is_wf[OF _ _ HOL.refl]) (auto simp: list_all_mkseq holds_upto_def wf_proj_simps wf_lane_simps)
  subgoal by (rule inv_lanes__is_wf[OF _ _ HOL.refl]) (auto simp: list_all_mkseq holds_upto_def wf_proj_simps wf_lane_simps)
  (* vsplat *)
  subgoal
    by (rule inv_lanes__is_wf[OF _ _ HOL.refl], assumption, (simp add: wf_lane_simps), rule list_all_repeat)
       (metis option.distinct(1) option.sel packnum__is_wf)
  (* extract_lane *)
  subgoal by (metis option.distinct(1) option.sel unpacknum__is_wf lanes_nth_wf wf_lane_simps(3))
  subgoal by (metis option.distinct(1) option.sel unpacknum__is_wf lanes_nth_wf wf_lane_simps(3))
  subgoal by (metis option.distinct(1) option.sel unpacknum__is_wf lanes_nth_wf wf_lane_simps(3))
  subgoal by (metis option.distinct(1) option.sel unpacknum__is_wf lanes_nth_wf wf_lane_simps(3))
  (* replace_lane *)
  subgoal
    apply (rule inv_lanes__is_wf[OF _ _ HOL.refl], assumption, (simp add: wf_lane_simps),
        rule list_all_list_update_func_gen)
    subgoal by (metis lanes__is_wf shape_fun_simps(1))
    subgoal by (metis option.distinct(1) option.sel packnum__is_wf)
    done
  (* vextunop, vextbinop *)
  subgoal by (metis option.distinct(1) option.sel vextunop___is_wf)
  subgoal by (metis option.distinct(1) option.sel vextbinop___is_wf)
  (* vnarrow *)
  subgoal by (rule inv_lanes__is_wf[OF _ _ HOL.refl]) (auto simp: list.pred_map o_def wf_proj_simps wf_lane_simps)
  (* vcvtop *)
  subgoal by (metis option.distinct(1) option.sel vcvtop___is_wf)
  done

(* Well-formedness of pure reduction *)
lemma Step_pure_is_wf :
	"list_all (\<lambda> (var_0 :: admininstr). (wf_admininstr var_0)) var_0 \<Longrightarrow>
	 (Step_pure var_0 var_1) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: admininstr). (wf_admininstr var_1)) var_1"
  using Step_pure_is_wf_aux by blast

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 *)
lemma Step_read_is_wf :
	"(wf_config (mk_config (mk_state s f) es)) \<Longrightarrow>
   Store_ok s \<Longrightarrow>
	 (Step_read (mk_config (mk_state s f) es) var_1) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: admininstr). (wf_admininstr var_1)) var_1"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 *)
lemma Step_is_wf :
	"(wf_config (mk_config (mk_state s f) es)) \<Longrightarrow>
    Store_ok s \<Longrightarrow>
	 (Step (mk_config (mk_state s f) es) var_1) \<Longrightarrow>
	 (wf_config var_1)"
sorry

end