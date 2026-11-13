(* Simulation: the reduction simulation, rule by rule.

   [Step_pure_sim]: every pure SpecTec step of well-formed, well-typed
   instructions is simulated by WasmCert ([psim]), is a label exit that is
   simulated eventually ([Label_exit], see Control.thy), or is one of the
   named pure disagreements ([Pure_exc]: Bad_extend, Divzero_value).

   Still to come: the state-reading and state-changing steps, and the main
   theorem by induction over SpecTec's step relation. *)
theory Simulation
  imports Vector Control Bulk
begin

section \<open>Well-formed operands\<close>

lemma proj_uN_0_un[simp]: "proj_uN_0 u = un u"
  by (cases u) simp

lemma wf_const: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST nt c)) \<Longrightarrow> wf_num_underscore nt c"
  by (simp add: wf_admininstr_sc_simps)

lemma wf_cvtop_admin:
  "wf_admininstr (admininstr_sc2 (admininstr_st2_CVTOP nt2 nt1 op)) \<Longrightarrow> wf_cvtop__underscore nt1 nt2 op"
  by (erule wf_admininstr.cases) simp_all

lemma wf_const_i32:
  assumes "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 c))"
  obtains u where "c = mk_num__0 Inn_I32 u" "un u < 2 ^ 32"
proof (cases c)
  case (mk_num__0 t i)
  then have "I32 = numtype_Inn t" "un i < 2 ^ isz t" using wf_const[OF assms] by simp_all
  then have "t = Inn_I32" "un i < 2 ^ 32" by (cases t; simp)+
  then show ?thesis using that mk_num__0 by simp
next
  case (mk_num__1 t x)
  then have "I32 = numtype_Fnn t" using wf_const[OF assms] by simp
  then show ?thesis by (cases t) simp_all
qed

section \<open>Pure steps\<close>

(* The redex instructions are well typed (from the typing invariant). *)
definition instrs_typed :: "admininstr list \<Rightarrow> bool" where
  "instrs_typed es \<longleftrightarrow> (\<forall>i. admininstr_instr i \<in> set es \<longrightarrow> (\<exists>C ft. Instr_ok C i ft))"

(* SpecTec leaves a label on a break or a return ([br_succ], [return_label]);
   simulated eventually (Control.thy). *)
inductive Label_exit :: "admininstr list \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "Label_exit [admininstr_sc7 (LABEL_underscore n ins ((map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR (mk_uN (x + 1)))]) @ es))]
              (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR (mk_uN x))])"
| "Label_exit [admininstr_sc7 (LABEL_underscore n ins ((map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN]) @ es))]
              (map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN])"

(* The pure steps where SpecTec and WasmCert disagree (as in the Rocq bridge):
   [Bad_extend], a sign extension of a width that is no packed width; and
   [Divzero_value], a division by zero that produces a value. *)
inductive Pure_exc :: "admininstr list \<Rightarrow> admininstr list \<Rightarrow> bool" where
  bad_extend: "\<not> unop_ext_ok nt op \<Longrightarrow>
    Pure_exc [admininstr_sc1 (admininstr_st1_CONST nt c1), admininstr_sc1 (admininstr_st1_UNOP nt op)] es'"
| divzero_value: "divzero op c2 \<Longrightarrow>
    Pure_exc [admininstr_sc1 (admininstr_st1_CONST nt c1), admininstr_sc1 (admininstr_st1_CONST nt c2),
              admininstr_sc1 (admininstr_st1_BINOP nt op)] [admininstr_sc1 (admininstr_st1_CONST nt c)]"

(* The instruction an administrative instruction stands for. *)
fun ainstr :: "admininstr \<Rightarrow> instr" where
  "ainstr (admininstr_sc0 x) = instr_of_a0 x"
| "ainstr (admininstr_sc1 x) = instr_of_a1 x"
| "ainstr (admininstr_sc2 x) = instr_of_a2 x"
| "ainstr (admininstr_sc3 x) = instr_of_a3 x"
| "ainstr (admininstr_sc4 x) = instr_of_a4 x"
| "ainstr (admininstr_sc5 x) = instr_of_a5 x"
| "ainstr (admininstr_sc6 x) = instr_of_a6 x"
| "ainstr (admininstr_sc7 x) = undefined"
| "ainstr (admininstr_sc8 x) = undefined"

locale pure_sim = builtins + simd

context pure_sim
begin

lemma typed_instr: "instrs_typed es \<Longrightarrow> admininstr_instr i \<in> set es \<Longrightarrow> \<exists>C ft. Instr_ok C i ft"
  by (simp add: instrs_typed_def)

lemma psim_vunop_es:
  assumes "Step_pure es es'" "instrs_typed es" "es = [vc c1] @ [admininstr_instr i]" "tr_instr i = Unop_vec op"
  shows "psim es es'"
proof -
  obtain C ft where "Instr_ok C i ft" using typed_instr[OF assms(2), of i] assms(3) by auto
  from psim_vunop[OF _ assms(4) this] show ?thesis using assms(1,3) by simp
qed

lemma psim_vbinop_es:
  assumes "Step_pure es es'" "instrs_typed es" "es = [vc c1, vc c2] @ [admininstr_instr i]" "tr_instr i = Binop_vec op"
  shows "psim es es'"
proof -
  obtain C ft where "Instr_ok C i ft" using typed_instr[OF assms(2), of i] assms(3) by auto
  from psim_vbinop[OF _ assms(4) this] show ?thesis using assms(1,3) by simp
qed

lemma psim_vternop_es:
  assumes "Step_pure es es'" "instrs_typed es" "es = [vc c1, vc c2, vc c3] @ [admininstr_instr i]" "tr_instr i = Ternop_vec op"
  shows "psim es es'"
proof -
  obtain C ft where "Instr_ok C i ft" using typed_instr[OF assms(2), of i] assms(3) by auto
  from psim_vternop[OF _ assms(4) this] show ?thesis using assms(1,3) by simp
qed

lemma psim_vtestop_es:
  assumes "Step_pure es es'" "instrs_typed es" "es = [vc c1] @ [admininstr_instr i]" "tr_instr i = Test_vec op"
  shows "psim es es'"
proof -
  obtain C ft where "Instr_ok C i ft" using typed_instr[OF assms(2), of i] assms(3) by auto
  from psim_vtestop[OF _ assms(4) this] show ?thesis using assms(1,3) by simp
qed

lemma psim_vshiftop_es:
  assumes "Step_pure es es'" "instrs_typed es" "es = [vc c1, i32c u] @ [admininstr_instr i]" "tr_instr i = Shift_vec op"
  shows "psim es es'"
proof -
  obtain C ft where "Instr_ok C i ft" using typed_instr[OF assms(2), of i] assms(3) by auto
  from psim_vshiftop[OF _ assms(4) this] show ?thesis using assms(1,3) by simp
qed

lemma psim_vsplat_es:
  assumes "Step_pure es es'" "instrs_typed es" "es = [admininstr_sc1 (admininstr_st1_CONST nt c)] @ [admininstr_instr i]" "tr_instr i = Splat_vec shv"
  shows "psim es es'"
proof -
  obtain C ft where "Instr_ok C i ft" using typed_instr[OF assms(2), of i] assms(3) by auto
  from psim_vsplat[OF _ assms(4) this] show ?thesis using assms(1,3) by simp
qed

lemma psim_vextract_es:
  assumes "Step_pure es es'" "instrs_typed es" "es = [vc c1] @ [admininstr_instr i]" "tr_instr i = Extract_vec shv sx j"
  shows "psim es es'"
proof -
  obtain C ft where "Instr_ok C i ft" using typed_instr[OF assms(2), of i] assms(3) by auto
  from psim_vextract[OF _ assms(4) this] show ?thesis using assms(1,3) by simp
qed

lemma psim_vreplace_es:
  assumes "Step_pure es es'" "instrs_typed es" "es = [vc c1, admininstr_sc1 (admininstr_st1_CONST nt c)] @ [admininstr_instr i]" "tr_instr i = Replace_vec shv j"
  shows "psim es es'"
proof -
  obtain C ft where "Instr_ok C i ft" using typed_instr[OF assms(2), of i] assms(3) by auto
  from psim_vreplace[OF _ assms(4) this] show ?thesis using assms(1,3) by simp
qed

(* Every pure step of well-formed, well-typed instructions is simulated, is a
   label exit (simulated eventually), or is a named disagreement. *)
theorem Step_pure_sim:
  assumes st: "Step_pure es es'" and w: "wfl es" and ty: "instrs_typed es"
  shows "psim es es' \<or> Pure_exc es es' \<or> Label_exit es es'"
  using st
proof (cases rule: Step_pure.cases)
  case Step_pure__unreachable then show ?thesis using psim_unreachable by simp
next
  case Step_pure__nop then show ?thesis using psim_nop by simp
next
  case (Step_pure__drop v) then show ?thesis using psim_drop by simp
next
  case (select_true c v1 v2 ts)
  obtain u where u: "c = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w select_true(1) by (auto elim: wf_const_i32)
  show ?thesis using select_true u psim_select[of u v1 v1 v2 ts] by simp
next
  case (select_false c v1 v2 ts)
  obtain u where u: "c = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w select_false(1) by (auto elim: wf_const_i32)
  show ?thesis using select_false u psim_select[of u v2 v1 v2 ts] by simp
next
  case (if_true c bt ins1 ins2)
  obtain u where u: "c = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w if_true(1) by (auto elim: wf_const_i32)
  show ?thesis using if_true u psim_if[of u ins1 ins1 ins2 bt] by simp
next
  case (if_false c bt ins1 ins2)
  obtain u where u: "c = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w if_false(1) by (auto elim: wf_const_i32)
  show ?thesis using if_false u psim_if[of u ins2 ins1 ins2 bt] by simp
next
  case (label_vals n ins vs) then show ?thesis using psim_label_vals by simp
next
  case (br_zero n vs ins vs' es0) then show ?thesis using psim_br_zero[of n vs ins vs' es0] by simp
next
  case (br_succ n ins vs l es0)
  then show ?thesis using Label_exit.intros(1)[of n ins vs "un l" es0] by simp
next
  case (br_if_true c l)
  obtain u where u: "c = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w br_if_true(1) by (auto elim: wf_const_i32)
  show ?thesis using br_if_true u psim_br_if[of u "[admininstr_sc0 (admininstr_st0_BR l)]" l] by simp
next
  case (br_if_false c l)
  obtain u where u: "c = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w br_if_false(1) by (auto elim: wf_const_i32)
  show ?thesis using br_if_false u psim_br_if[of u "[]" l] by simp
next
  case (br_table_lt i ls l')
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w br_table_lt(1) by (auto elim: wf_const_i32)
  show ?thesis using br_table_lt u psim_br_table[of u "ls ! un u" ls l'] by simp
next
  case (br_table_ge i ls l')
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w br_table_ge(1) by (auto elim: wf_const_i32)
  show ?thesis using br_table_ge u psim_br_table[of u l' ls l'] by simp
next
  case (frame_vals n vs fr) then show ?thesis using psim_frame_vals by simp
next
  case (return_frame n vs fr vs' es0) then show ?thesis using psim_return_frame[of n vs fr vs' es0] by simp
next
  case (return_label n ins vs es0) then show ?thesis using Label_exit.intros(2)[of n ins vs es0] by simp
next
  case (trap_vals vs es0) then show ?thesis using psim_trap_vals[of vs es0] by simp
next
  case (trap_label n ins) then show ?thesis using psim_trap_label by simp
next
  case (trap_frame n fr) then show ?thesis using psim_trap_frame by simp
next
  case (unop_val nt op c1 r c)
  show ?thesis
  proof (cases "unop_ext_ok nt op")
    case True
    have "wf_num_underscore nt c1" using w unop_val(1) by (simp add: wf_const)
    then show ?thesis using unop_val True psim_unop[of nt c1 op "the r" c] by auto
  qed (use unop_val in \<open>auto intro: Pure_exc.intros\<close>)
next
  case (unop_trap nt op c1 r)
  show ?thesis
  proof (cases "unop_ext_ok nt op")
    case True
    have "wf_num_underscore nt c1" using w unop_trap(1) by (simp add: wf_const)
    then show ?thesis using unop_trap True unop_no_trap[of nt c1 op] by auto
  qed (use unop_trap in \<open>auto intro: Pure_exc.intros\<close>)
next
  case (binop_val nt op c1 c2 r c)
  show ?thesis
  proof (cases "divzero op c2")
    case False
    have w1: "wf_num_underscore nt c1" "wf_num_underscore nt c2" using w binop_val(1) by (simp_all add: wf_const)
    obtain cs where r: "r = Some cs" "c \<in> set cs" using binop_val by auto
    have "fun_binop_underscore nt op c1 c2 (Some cs)" using binop_val r by simp
    from psim_binop_val[OF w1 this False r(2)] show ?thesis using binop_val by simp
  next
    case True then show ?thesis using binop_val by (simp add: Pure_exc.divzero_value)
  qed
next
  case (binop_trap nt op c1 c2 r)
  have w1: "wf_num_underscore nt c1" "wf_num_underscore nt c2" using w binop_trap(1) by (simp_all add: wf_const)
  have "fun_binop_underscore nt op c1 c2 (Some [])" using binop_trap by (cases r) simp_all
  from psim_binop_trap[OF w1 this] show ?thesis using binop_trap by simp
next
  case (Step_pure__testop nt op c1 r c)
  have w1: "wf_num_underscore nt c1" using w Step_pure__testop(1) by (simp add: wf_const)
  have "fun_testop_underscore nt op c1 (Some c)" using Step_pure__testop by (cases r) simp_all
  from psim_testop[OF w1 this] show ?thesis using Step_pure__testop by simp
next
  case (Step_pure__relop nt op c1 c2 r c)
  have w1: "wf_num_underscore nt c1" "wf_num_underscore nt c2" using w Step_pure__relop(1) by (simp_all add: wf_const)
  have "fun_relop_underscore nt op c1 c2 (Some c)" using Step_pure__relop by (cases r) simp_all
  from psim_relop[OF w1 this] show ?thesis using Step_pure__relop by simp
next
  case (cvtop_val nt1 nt2 op c1 r c)
  have w1: "wf_num_underscore nt1 c1" "wf_cvtop__underscore nt1 nt2 op"
    using w cvtop_val(1) by (auto simp: wf_const dest: wf_cvtop_admin)
  obtain cs where r: "r = Some cs" "c \<in> set cs" "cs \<noteq> []" using cvtop_val by auto
  have "fun_cvtop__underscore nt1 nt2 op c1 (Some cs)" using cvtop_val r by simp
  from psim_cvtop[OF w1 this HOL.refl, of c] show ?thesis using cvtop_val r by simp
next
  case (cvtop_trap nt1 nt2 op c1 r)
  have w1: "wf_num_underscore nt1 c1" "wf_cvtop__underscore nt1 nt2 op"
    using w cvtop_trap(1) by (auto simp: wf_const dest: wf_cvtop_admin)
  have "fun_cvtop__underscore nt1 nt2 op c1 (Some [])" using cvtop_trap by (cases r) simp_all
  from psim_cvtop[OF w1 this HOL.refl, of undefined] show ?thesis using cvtop_trap by simp
next
  case (ref_is_null_true r rt) then show ?thesis using psim_ref_is_null[of True r] by simp
next
  case (ref_is_null_false r)
  have "\<not> (\<exists>rt. r = ref_REF_NULL rt)"
    using ref_is_null_false by (auto intro: Step_pure_before_ref_is_null_false.intros)
  then show ?thesis using ref_is_null_false psim_ref_is_null[of False r] by simp
next
  case (Step_pure__vvunop op c1 r c)
  then show ?thesis using psim_vunop_es[OF st ty, of c1 "ainstr (last es)"] by simp
next
  case (Step_pure__vvbinop op c1 c2 r c)
  then show ?thesis using psim_vbinop_es[OF st ty, of c1 c2 "ainstr (last es)"] by simp
next
  case (Step_pure__vvternop op c1 c2 c3 r c)
  then show ?thesis using psim_vternop_es[OF st ty, of c1 c2 c3 "ainstr (last es)"] by simp
next
  case (Step_pure__vvtestop c c1)
  then show ?thesis using psim_vtestop_es[OF st ty, of c1 "ainstr (last es)"] by simp
next
  case (Step_pure__vunop sh op c1 r c)
  then show ?thesis using psim_vunop_es[OF st ty, of c1 "ainstr (last es)"] by simp
next
  case (vunop_trap sh op c1 r)
  then show ?thesis using psim_vunop_es[OF st ty, of c1 "ainstr (last es)"] by simp
next
  case (vbinop_val sh op c1 c2 r c)
  then show ?thesis using psim_vbinop_es[OF st ty, of c1 c2 "ainstr (last es)"] by simp
next
  case (vbinop_trap sh op c1 c2 r)
  then show ?thesis using psim_vbinop_es[OF st ty, of c1 c2 "ainstr (last es)"] by simp
next
  case (vtestop_true cis J N c)
  then show ?thesis using psim_vtestop_es[OF st ty, of c "ainstr (last es)"] by simp
next
  case (vtestop_false c J N)
  then show ?thesis using psim_vtestop_es[OF st ty, of c "ainstr (last es)"] by simp
next
  case (Step_pure__vrelop sh op c1 c2 r c)
  then show ?thesis using psim_vbinop_es[OF st ty, of c1 c2 "ainstr (last es)"] by simp
next
  case (Step_pure__vshiftop J N op n rs cs c1 c)
  then show ?thesis using psim_vshiftop_es[OF st ty, of c1 "mk_uN n" "ainstr (last es)"] by simp
next
  case (Step_pure__vbitmask J w rs cis N c ci)
  then show ?thesis using psim_vtestop_es[OF st ty, of c "ainstr (last es)"] by simp
next
  case (Step_pure__vswizzle cis P M c2 c1 cs c)
  then show ?thesis using psim_vbinop_es[OF st ty, of c1 c2 "ainstr (last es)"] by simp
next
  case (Step_pure__vshuffle P cs N c1 c2 ns c)
  then show ?thesis using psim_vbinop_es[OF st ty, of c1 c2 "ainstr (last es)"] by simp
next
  case (Step_pure__vsplat L c1 c N)
  then show ?thesis using psim_vsplat_es[OF st ty, of "unpack L" c1 "ainstr (last es)"] by simp
next
  case (vextract_lane_num nt N c1 i c2)
  then show ?thesis using psim_vextract_es[OF st ty, of c1 "ainstr (last es)"] by simp
next
  case (vextract_lane_pack c2 pt N c1 i sx)
  then show ?thesis using psim_vextract_es[OF st ty, of c1 "ainstr (last es)"] by simp
next
  case (Step_pure__vreplace_lane L c2 c N c1 i)
  then show ?thesis using psim_vreplace_es[OF st ty, of c1 "unpack L" c2 "ainstr (last es)"] by simp
next
  case (Step_pure__vextunop sh1 sh2 op c1 r c)
  then show ?thesis using psim_vunop_es[OF st ty, of c1 "ainstr (last es)"] by simp
next
  case (Step_pure__vextbinop sh1 sh2 op c1 c2 r c)
  then show ?thesis using psim_vbinop_es[OF st ty, of c1 c2 "ainstr (last es)"] by simp
next
  case (Step_pure__vnarrow J2 v1 J1 v0 cis1 N1 c1 cis2 c2 cjs1 sx cjs2 c N2)
  then show ?thesis using psim_vbinop_es[OF st ty, of c1 c2 "ainstr (last es)"] by simp
next
  case (Step_pure__vcvtop sh1 sh2 op c1 r c)
  then show ?thesis using psim_vunop_es[OF st ty, of c1 "ainstr (last es)"] by simp
next
  case (Step_pure__local_tee v x) then show ?thesis using psim_local_tee by simp
qed

end

end
