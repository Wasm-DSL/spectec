(* Control: breaks and returns out of labels, and the evaluation contexts.
   Port of the "eventually" part of ../wasmcert-rocq/reduction.v.

   SpecTec leaves one label per step on a break or a return ([br_succ],
   [return_label]); WasmCert jumps to the target in one [br] / [return] step.
   The intermediate SpecTec configurations have no WasmCert counterpart, so the
   simulation is restored only eventually, once the break or return reaches its
   target (CompCert's "eventually" diagram).  [br_pending] and [ret_pending]
   describe such a break or return on its way out: SpecTec has moved, WasmCert
   has not (beyond evaluating null references, which [br] and [return] need as
   values).  [label_pending_br], [label_pending_ret] and [frame_pending_ret]
   carry them through one enclosing label or frame; the extra SpecTec steps are
   taken in [CSteps], which keeps the configurations well formed, as SpecTec's
   context rules require.

   Label and return arities are plain numbers here ([ls], [r]); the typing
   invariant of the main theorem will supply them. *)
theory Control
  imports Reduction
begin

section \<open>Well-formedness of SpecTec instruction sequences\<close>

inductive_simps wf_admininstr_sc_simps:
  "wf_admininstr (admininstr_sc0 x)" "wf_admininstr (admininstr_sc1 x)"
  "wf_admininstr (admininstr_sc2 x)" "wf_admininstr (admininstr_sc4 x)" "wf_admininstr (admininstr_sc7 x)"
  "wf_admininstr (admininstr_sc8 x)"

inductive_simps wf_config_simps: "wf_config (mk_config z es)"

abbreviation wfl :: "admininstr list \<Rightarrow> bool" where
  "wfl \<equiv> list_all wf_admininstr"

lemma wf_admininstr_val: "wf_val v \<Longrightarrow> wf_admininstr (admininstr_val v)"
  by (cases v) (auto simp: wf_admininstr_sc_simps elim!: wf_val.cases)

lemma wf_admininstr_val_inv: "wf_admininstr (admininstr_val v) \<Longrightarrow> wf_val v"
  by (cases v) (auto simp: wf_admininstr_sc_simps intro: wf_val.intros)

lemma wf_admininstr_instr: "wf_instr e \<Longrightarrow> wf_admininstr (admininstr_instr e)"
  by (induction e rule: wf_instr.induct) (auto intro!: wf_admininstr.intros simp: list_all_iff)

lemma wfl_vals: "wfl (map admininstr_val vs) \<longleftrightarrow> list_all wf_val vs"
  by (induction vs) (auto intro: wf_admininstr_val dest: wf_admininstr_val_inv)

lemma wfl_instrs: "list_all wf_instr ins \<Longrightarrow> wfl (map admininstr_instr ins)"
  by (induction ins) (auto intro: wf_admininstr_instr)

inductive_simps wf_state_simps: "wf_state (mk_state s f)"

lemma wf_label_iff:
  "wf_admininstr (admininstr_sc7 (LABEL_underscore n ins es)) \<longleftrightarrow> list_all wf_instr ins \<and> wfl es"
  by (simp add: wf_admininstr_sc_simps)

lemma wf_frame_iff:
  "wf_admininstr (admininstr_sc8 (FRAME_underscore n f es)) \<longleftrightarrow> wf_frame f \<and> wfl es"
  by (simp add: wf_admininstr_sc_simps)

lemma wf_br_iff: "wf_admininstr (admininstr_sc0 (admininstr_st0_BR l)) \<longleftrightarrow> wf_uN 32 l"
  by (simp add: wf_admininstr_sc_simps)

lemma wf_return: "wf_admininstr (admininstr_sc1 admininstr_st1_RETURN)"
  by (simp add: wf_admininstr_sc_simps)

section \<open>SpecTec steps that keep the state\<close>

(* SpecTec's context rules need well-formed configurations on both sides, so the
   extra SpecTec steps of the "eventually" simulation are taken in [CSteps]. *)
definition cstep :: "state \<Rightarrow> admininstr list \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "cstep z a b \<longleftrightarrow> Step (mk_config z a) (mk_config z b) \<and> wf_config (mk_config z a) \<and> wf_config (mk_config z b)"

abbreviation CSteps :: "state \<Rightarrow> admininstr list \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "CSteps z \<equiv> (cstep z)\<^sup>*\<^sup>*"

lemma CSteps_one:
  "Step (mk_config z a) (mk_config z b) \<Longrightarrow> wf_state z \<Longrightarrow> wfl a \<Longrightarrow> wfl b \<Longrightarrow> CSteps z a b"
  by (rule r_into_rtranclp) (simp add: cstep_def wf_config_simps)

lemma CSteps_label:
  assumes "CSteps z es es'" "list_all wf_instr ins"
  shows "CSteps z [admininstr_sc7 (LABEL_underscore n ins es)] [admininstr_sc7 (LABEL_underscore n ins es')]"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case (step b c)
  have "Step (mk_config z [admininstr_sc7 (LABEL_underscore n ins b)]) (mk_config z [admininstr_sc7 (LABEL_underscore n ins c)])"
    using step.hyps(2) unfolding cstep_def by - (rule Step.ctxt_label, simp_all)
  then have "cstep z [admininstr_sc7 (LABEL_underscore n ins b)] [admininstr_sc7 (LABEL_underscore n ins c)]"
    using step.hyps(2) assms(2) by (auto simp: cstep_def wf_config_simps wf_label_iff)
  then show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step.IH])
qed simp

lemma CSteps_frame:
  assumes "CSteps (mk_state s f') es es'" "wf_frame f" "wf_frame f'"
  shows "CSteps (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)] [admininstr_sc8 (FRAME_underscore n f' es')]"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case (step b c)
  have "Step (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' b)])
             (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' c)])"
    using step.hyps(2) unfolding cstep_def by - (rule Step.ctxt_frame, simp_all)
  then have "cstep (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' b)] [admininstr_sc8 (FRAME_underscore n f' c)]"
    using step.hyps(2) assms(2,3) by (auto simp: cstep_def wf_config_simps wf_state_simps wf_frame_iff)
  then show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step.IH])
qed simp

lemma CSteps_instrs:
  assumes "CSteps z es es'" "list_all wf_val vs" "wfl es1"
  shows "CSteps z (map admininstr_val vs @ es @ es1) (map admininstr_val vs @ es' @ es1)"
proof (cases "vs = [] \<and> es1 = []")
  case True then show ?thesis using assms(1) by simp
next
  case False
  show ?thesis using assms(1)
  proof (induction rule: rtranclp_induct)
    case (step b c)
    have "Step (mk_config z (map admininstr_val vs @ b @ es1)) (mk_config z (map admininstr_val vs @ c @ es1))"
      using step.hyps(2) False unfolding cstep_def by - (rule Step.ctxt_instrs, simp_all)
    then have "cstep z (map admininstr_val vs @ b @ es1) (map admininstr_val vs @ c @ es1)"
      using step.hyps(2) assms(2,3) by (auto simp: cstep_def wf_config_simps wfl_vals)
    then show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step.IH])
  qed simp
qed

section \<open>Evaluation contexts\<close>

lemma tr_admins_label:
  "tr_admins [admininstr_sc7 (LABEL_underscore n ins es)] = [Label n (map Basic (tr_instrs ins)) (tr_admins es)]"
  by simp

lemma tr_admins_frame:
  "tr_admins [admininstr_sc8 (FRAME_underscore n fr es)] = [Frame n (tr_frame fr) (tr_admins es)]"
  by simp

lemma sim_label:
  assumes "sim (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
  shows "sim (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)])
             (mk_config (mk_state s' f') [admininstr_sc7 (LABEL_underscore n ins es')])"
proof -
  from assms obtain es0 where r: "reduce_trans (tr_store s, tr_frame f, tr_admins es) (tr_store s', tr_frame f', es0)"
    and nn: "nls es0 (tr_admins es')"
    by (auto simp: sim_def wsim_def)
  have "reduce_trans (tr_store s, tr_frame f, [Label n (map Basic (tr_instrs ins)) (tr_admins es)])
                     (tr_store s', tr_frame f', [Label n (map Basic (tr_instrs ins)) es0])"
    by (rule reduce_trans_label[OF r])
  moreover have "nls [Label n (map Basic (tr_instrs ins)) es0] [Label n (map Basic (tr_instrs ins)) (tr_admins es')]"
    using nn by (simp add: nl_label)
  ultimately show ?thesis unfolding sim_def tr_config.simps wsim_def prod.case tr_admins_label by blast
qed

lemma sim_frame:
  assumes "sim (mk_config (mk_state s f') es) (mk_config (mk_state s' f'') es')"
  shows "sim (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)])
             (mk_config (mk_state s' f) [admininstr_sc8 (FRAME_underscore n f'' es')])"
proof -
  from assms obtain es0 where r: "reduce_trans (tr_store s, tr_frame f', tr_admins es) (tr_store s', tr_frame f'', es0)"
    and nn: "nls es0 (tr_admins es')"
    by (auto simp: sim_def wsim_def)
  have "reduce_trans (tr_store s, tr_frame f, [Frame n (tr_frame f') (tr_admins es)])
                     (tr_store s', tr_frame f, [Frame n (tr_frame f'') es0])"
    by (rule reduce_trans_local[OF r])
  moreover have "nls [Frame n (tr_frame f'') es0] [Frame n (tr_frame f'') (tr_admins es')]"
    using nn by (simp add: nl_frame)
  ultimately show ?thesis unfolding sim_def tr_config.simps wsim_def prod.case tr_admins_frame by blast
qed

lemma sim_instrs:
  assumes "sim (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
  shows "sim (mk_config (mk_state s f) (map admininstr_val vs @ es @ es1))
             (mk_config (mk_state s' f') (map admininstr_val vs @ es' @ es1))"
proof -
  from assms obtain es0 where r: "reduce_trans (tr_store s, tr_frame f, tr_admins es) (tr_store s', tr_frame f', es0)"
    and nn: "nls es0 (tr_admins es')"
    by (auto simp: sim_def wsim_def)
  have r1: "reduce_trans (tr_store s, tr_frame f, tr_admins (map admininstr_val vs) @ tr_admins es @ tr_admins es1)
                         (tr_store s, tr_frame f, ($C* map tr_val vs) @ tr_admins es @ tr_admins es1)"
    by (rule eval_vals0)
  have r2: "reduce_trans (tr_store s, tr_frame f, ($C* map tr_val vs) @ tr_admins es @ tr_admins es1)
                         (tr_store s', tr_frame f', ($C* map tr_val vs) @ es0 @ tr_admins es1)"
    by (rule reduce_trans_L0[OF r])
  have nn': "nls (($C* map tr_val vs) @ es0 @ tr_admins es1) (tr_admins (map admininstr_val vs) @ tr_admins es' @ tr_admins es1)"
    by (intro nls_append nls_vals nn nls_refl)
  show ?thesis unfolding sim_def wsim_def tr_config.simps tr_admins_append prod.case
    using rt_trans[OF r1 r2] nn' by blast
qed

section \<open>Breaks and returns on their way out\<close>

lemma lfilled_drop_vals_aux:
  "Lfilled k lh es0 LI \<Longrightarrow> es0 = ($C* (xs @ ys)) @ es \<Longrightarrow> \<exists>lh'. Lfilled k lh' (($C* ys) @ es) LI"
proof (induction k lh es0 LI arbitrary: es rule: Lfilled.induct)
  case (L0 lholed vs es' es0)
  have "Lfilled 0 (LBase (vs @ xs) es') (($C* ys) @ es) (($C* (vs @ xs)) @ (($C* ys) @ es) @ es')"
    by (rule Lfilled.L0) simp
  moreover have "($C* (vs @ xs)) @ (($C* ys) @ es) @ es' = ($C* vs) @ es0 @ es'"
    using L0.prems by simp
  ultimately show ?case by auto
next
  case (LN lholed vs n es' l es'' k es0 lfilledk)
  obtain lh' where "Lfilled k lh' (($C* ys) @ es) lfilledk" using LN.IH LN.prems by blast
  then have "Lfilled (k + 1) (LRec vs n es' lh' es'') (($C* ys) @ es) (($C* vs) @ [Label n es' lfilledk] @ es'')"
    by (rule Lfilled.LN[OF HOL.refl])
  then show ?case by blast
qed

lemma lfilled_drop_vals:
  "Lfilled k lh (($C* (xs @ ys)) @ es) LI \<Longrightarrow> \<exists>lh'. Lfilled k lh' (($C* ys) @ es) LI"
  using lfilled_drop_vals_aux by blast

lemma lfilled_lift:
  assumes "Lfilled k lh es LI"
  shows "Lfilled (Suc k) (LRec [] n les lh []) es [Label n les LI]"
proof -
  have "Lfilled (k + 1) (LRec [] n les lh []) es (($C* []) @ [Label n les LI] @ [])"
    by (rule Lfilled.LN[OF HOL.refl assms])
  then show ?thesis by simp
qed

lemma lfilled_base:
  "Lfilled 0 (LBase [] es') es (es @ es')"
  using Lfilled.L0[OF HOL.refl, of "[]" es' es] by simp

(* WasmCert reaches [LI] from the translation of [es] by pure steps (evaluating
   nulls), in any store and frame. *)
definition preach :: "admininstr list \<Rightarrow> e list \<Rightarrow> bool" where
  "preach es LI \<longleftrightarrow> (\<forall>St Fr. reduce_trans (St, Fr, tr_admins es) (St, Fr, LI))"

lemma preach_label:
  "preach es LI \<Longrightarrow> preach [admininstr_sc7 (LABEL_underscore n ins es)] [Label n (map Basic (tr_instrs ins)) LI]"
  unfolding preach_def using reduce_trans_label by simp

(* A break on its way out.  SpecTec has taken the [br_succ] steps out of the
   innermost [k] labels of [es], leaving [BR l]; WasmCert has not moved: the
   translation of [es] (with its nulls evaluated, [LI]) still has those labels,
   as [lh], around the break [Br (l + k)].  [ls] are the arities of the labels
   that enclose [es], innermost first; [vs_in] are the values beside the
   break, enough for its target label. *)
definition br_pending :: "nat list \<Rightarrow> admininstr list \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "br_pending ls es es' \<longleftrightarrow>
     (\<exists>k lh l vs_out vs_in rest LI. preach es LI \<and>
        Lfilled k lh (($C* map tr_val vs_in) @ [$Br (l + k)]) LI \<and>
        es' = map admininstr_val (vs_out @ vs_in) @ [admininstr_sc0 (admininstr_st0_BR (mk_uN l))] @ rest \<and>
        l < length ls \<and> ls ! l \<le> length vs_in)"

(* The same for a return; [r] is the arity of the enclosing frame. *)
definition ret_pending :: "nat option \<Rightarrow> admininstr list \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "ret_pending r es es' \<longleftrightarrow>
     (\<exists>k lh vs_out vs_in rest LI m. preach es LI \<and>
        Lfilled k lh (($C* map tr_val vs_in) @ [$Return]) LI \<and>
        es' = map admininstr_val (vs_out @ vs_in) @ [admininstr_sc1 admininstr_st1_RETURN] @ rest \<and>
        r = Some m \<and> m \<le> length vs_in)"

(* SpecTec's [br_succ] and [return_label] start a pending break or return. *)
lemma br_exit_pending:
  assumes "x < length ls" "ls ! x \<le> length vs"
  shows "br_pending ls
           [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR (mk_uN (x + 1)))] @ es))]
           (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR (mk_uN x))])"
proof -
  let ?les = "map Basic (tr_instrs ins)"
  let ?I = "($C* map tr_val vs) @ [$Br (x + 1)]"
  have p: "preach (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR (mk_uN (x + 1)))] @ es) (?I @ tr_admins es)"
    unfolding preach_def using eval_vals0 by simp
  have lf: "Lfilled (Suc 0) (LRec [] n ?les (LBase [] (tr_admins es)) []) ?I [Label n ?les (?I @ tr_admins es)]"
    by (rule lfilled_lift[OF lfilled_base])
  show ?thesis unfolding br_pending_def
    apply (rule exI[of _ "Suc 0"], rule exI[of _ "LRec [] n ?les (LBase [] (tr_admins es)) []"], rule exI[of _ x],
           rule exI[of _ "[]"], rule exI[of _ vs], rule exI[of _ "[]"], rule exI[of _ "[Label n ?les (?I @ tr_admins es)]"])
    using preach_label[OF p, of n ins] lf assms by simp
qed

lemma ret_exit_pending:
  assumes "r = Some m" "m \<le> length vs"
  shows "ret_pending r
           [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ es))]
           (map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN])"
proof -
  let ?les = "map Basic (tr_instrs ins)"
  let ?I = "($C* map tr_val vs) @ [$Return]"
  have p: "preach (map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ es) (?I @ tr_admins es)"
    unfolding preach_def using eval_vals0 by simp
  have lf: "Lfilled (Suc 0) (LRec [] n ?les (LBase [] (tr_admins es)) []) ?I [Label n ?les (?I @ tr_admins es)]"
    by (rule lfilled_lift[OF lfilled_base])
  show ?thesis unfolding ret_pending_def
    apply (rule exI[of _ "Suc 0"], rule exI[of _ "LRec [] n ?les (LBase [] (tr_admins es)) []"],
           rule exI[of _ "[]"], rule exI[of _ vs], rule exI[of _ "[]"], rule exI[of _ "[Label n ?les (?I @ tr_admins es)]"],
           rule exI[of _ m])
    using preach_label[OF p, of n ins] lf assms by simp
qed

(* The last [n] values. *)
lemma split_last_vals:
  assumes "n \<le> length vs"
  obtains ex vm where "vs = ex @ vm" "length vm = n"
proof
  show "vs = take (length vs - n) vs @ drop (length vs - n) vs" by simp
  show "length (drop (length vs - n) vs) = n" using assms by simp
qed

lemma reduce_trans_preach:
  "preach es LI \<Longrightarrow> reduce_trans (St, Fr, tr_admins es) (St, Fr, LI)"
  by (simp add: preach_def)

(* A pending break reaches the label around [es]: either it targets that label
   ([br_zero] in SpecTec, one [br] step in WasmCert, which restores the
   simulation), or it leaves it too ([br_succ] in SpecTec, WasmCert still does not
   move). *)
lemma label_pending_br:
  assumes p: "br_pending (n # ls) es es''" and z: "wf_state (mk_state s f)"
    and wi: "list_all wf_instr ins" and w: "wfl es''"
  shows "\<exists>es3. CSteps (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es'')] es3 \<and> wfl es3 \<and>
           (sim (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)]) (mk_config (mk_state s f) es3) \<or>
            br_pending ls [admininstr_sc7 (LABEL_underscore n ins es)] es3)"
proof -
  from p obtain k lh l vs_out vs_in rest LI where
    r: "preach es LI" and lf: "Lfilled k lh (($C* map tr_val vs_in) @ [$Br (l + k)]) LI"
    and e: "es'' = map admininstr_val (vs_out @ vs_in) @ [admininstr_sc0 (admininstr_st0_BR (mk_uN l))] @ rest"
    and l: "l < length (n # ls)" "(n # ls) ! l \<le> length vs_in"
    unfolding br_pending_def by blast
  let ?les = "map Basic (tr_instrs ins)"
  let ?L = "admininstr_sc7 (LABEL_underscore n ins es'')"
  have rl: "preach [admininstr_sc7 (LABEL_underscore n ins es)] [Label n ?les LI]"
    by (rule preach_label[OF r])
  have wv: "list_all wf_val (vs_out @ vs_in)" and wb: "wf_uN 32 (mk_uN l)" and wr: "wfl rest"
    using w e by (simp_all add: wfl_vals wf_br_iff)
  have wl: "wfl [?L]" using wi w by (simp add: wf_label_iff)
  show ?thesis
  proof (cases l)
    case 0
    then have "n \<le> length vs_in" using l by simp
    then obtain ex vm where vs: "vs_in = ex @ vm" "length vm = n" by (rule split_last_vals)
    let ?es3 = "map admininstr_val vm @ map admininstr_instr ins"
    have "Step_pure [admininstr_sc7 (LABEL_underscore n ins
             (((map admininstr_val (vs_out @ ex) @ map admininstr_val vm) @ [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))]) @ rest))]
           ?es3"
      by (rule Step_pure.br_zero) (simp add: vs)
    then have "Step_pure [?L] ?es3" using e 0 vs by simp
    then have st: "Step (mk_config (mk_state s f) [?L]) (mk_config (mk_state s f) ?es3)" by (rule Step.pure)
    have w3: "wfl ?es3" using wv wfl_instrs[OF wi] vs by (simp add: wfl_vals)
    have cs: "CSteps (mk_state s f) [?L] ?es3" by (rule CSteps_one[OF st z wl w3])
    obtain lh' where lf': "Lfilled k lh' (($C* map tr_val vm) @ [$Br k]) LI"
      using lfilled_drop_vals[of k lh "map tr_val ex" "map tr_val vm" "[$Br k]" LI] lf 0 vs by auto
    have br: "reduce_simple [Label n ?les LI] (($C* map tr_val vm) @ ?les)"
      by (rule reduce_simple.br[OF _ lf']) (simp add: vs)
    have "wsim (tr_store s, tr_frame f, tr_admins [admininstr_sc7 (LABEL_underscore n ins es)])
               (tr_store s, tr_frame f, tr_admins ?es3)"
      by (rule wsim_rt[OF reduce_trans_preach[OF rl] wsim_basic[OF br]])
         (simp only: tr_admins_append tr_admins_instrs, intro nls_append nls_vals nls_refl)
    then have "sim (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)]) (mk_config (mk_state s f) ?es3)"
      by (simp only: sim_def tr_config.simps)
    then show ?thesis using cs w3 by blast
  next
    case (Suc l')
    let ?es3 = "map admininstr_val (vs_out @ vs_in) @ [admininstr_sc0 (admininstr_st0_BR (mk_uN l'))]"
    have "Step_pure [admininstr_sc7 (LABEL_underscore n ins
             ((map admininstr_val (vs_out @ vs_in) @ [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 (mk_uN l') + 1)))]) @ rest))]
           ?es3"
      by (rule Step_pure.br_succ)
    then have "Step_pure [?L] ?es3" using e Suc by simp
    then have st: "Step (mk_config (mk_state s f) [?L]) (mk_config (mk_state s f) ?es3)" by (rule Step.pure)
    have "wf_uN 32 (mk_uN l')" using wb Suc by (simp add: wf_uN_iff)
    then have w3: "wfl ?es3" using wv by (simp add: wfl_vals wf_br_iff)
    have cs: "CSteps (mk_state s f) [?L] ?es3" by (rule CSteps_one[OF st z wl w3])
    have lf': "Lfilled (Suc k) (LRec [] n ?les lh []) (($C* map tr_val vs_in) @ [$Br (l' + Suc k)]) [Label n ?les LI]"
      using lfilled_lift[OF lf, of n ?les] Suc by simp
    have "br_pending ls [admininstr_sc7 (LABEL_underscore n ins es)] ?es3"
      unfolding br_pending_def
      apply (rule exI[of _ "Suc k"], rule exI[of _ "LRec [] n ?les lh []"], rule exI[of _ l'], rule exI[of _ vs_out],
             rule exI[of _ vs_in], rule exI[of _ "[]"], rule exI[of _ "[Label n ?les LI]"])
      using rl lf' l Suc by simp
    then show ?thesis using cs w3 by blast
  qed
qed

(* A pending return leaves the label around [es] ([return_label]). *)
lemma label_pending_ret:
  assumes p: "ret_pending r es es''" and z: "wf_state (mk_state s f)"
    and wi: "list_all wf_instr ins" and w: "wfl es''"
  shows "\<exists>es3. CSteps (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es'')] es3 \<and> wfl es3 \<and>
           ret_pending r [admininstr_sc7 (LABEL_underscore n ins es)] es3"
proof -
  from p obtain k lh vs_out vs_in rest LI m where
    r: "preach es LI" and lf: "Lfilled k lh (($C* map tr_val vs_in) @ [$Return]) LI"
    and e: "es'' = map admininstr_val (vs_out @ vs_in) @ [admininstr_sc1 admininstr_st1_RETURN] @ rest"
    and m: "r = Some m" "m \<le> length vs_in"
    unfolding ret_pending_def by blast
  let ?les = "map Basic (tr_instrs ins)"
  let ?L = "admininstr_sc7 (LABEL_underscore n ins es'')"
  let ?es3 = "map admininstr_val (vs_out @ vs_in) @ [admininstr_sc1 admininstr_st1_RETURN]"
  have rl: "preach [admininstr_sc7 (LABEL_underscore n ins es)] [Label n ?les LI]"
    by (rule preach_label[OF r])
  have wv: "list_all wf_val (vs_out @ vs_in)" using w e by (simp add: wfl_vals)
  have wl: "wfl [?L]" using wi w by (simp add: wf_label_iff)
  have "Step_pure [admininstr_sc7 (LABEL_underscore n ins
           ((map admininstr_val (vs_out @ vs_in) @ [admininstr_sc1 admininstr_st1_RETURN]) @ rest))] ?es3"
    by (rule Step_pure.return_label)
  then have "Step_pure [?L] ?es3" using e by simp
  then have st: "Step (mk_config (mk_state s f) [?L]) (mk_config (mk_state s f) ?es3)" by (rule Step.pure)
  have w3: "wfl ?es3" using wv by (simp add: wfl_vals wf_return)
  have cs: "CSteps (mk_state s f) [?L] ?es3" by (rule CSteps_one[OF st z wl w3])
  have lf': "Lfilled (Suc k) (LRec [] n ?les lh []) (($C* map tr_val vs_in) @ [$Return]) [Label n ?les LI]"
    by (rule lfilled_lift[OF lf])
  have "ret_pending r [admininstr_sc7 (LABEL_underscore n ins es)] ?es3"
    unfolding ret_pending_def
    apply (rule exI[of _ "Suc k"], rule exI[of _ "LRec [] n ?les lh []"], rule exI[of _ vs_out],
           rule exI[of _ vs_in], rule exI[of _ "[]"], rule exI[of _ "[Label n ?les LI]"], rule exI[of _ m])
    using rl lf' m by simp
  then show ?thesis using cs w3 by blast
qed

(* A pending return reaches its frame: [return_frame] in SpecTec, one [return]
   step in WasmCert, which restores the simulation. *)
lemma frame_pending_ret:
  assumes p: "ret_pending (Some n) es es''" and z: "wf_state (mk_state s f)"
    and wf': "wf_frame f'" and w: "wfl es''"
  shows "\<exists>es3. CSteps (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es'')] es3 \<and> wfl es3 \<and>
           sim (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)]) (mk_config (mk_state s f) es3)"
proof -
  from p obtain k lh vs_out vs_in rest LI where
    r: "preach es LI" and lf: "Lfilled k lh (($C* map tr_val vs_in) @ [$Return]) LI"
    and e: "es'' = map admininstr_val (vs_out @ vs_in) @ [admininstr_sc1 admininstr_st1_RETURN] @ rest"
    and m: "n \<le> length vs_in"
    unfolding ret_pending_def by blast
  obtain ex vm where vs: "vs_in = ex @ vm" "length vm = n" using split_last_vals[OF m] by blast
  let ?F = "admininstr_sc8 (FRAME_underscore n f' es'')"
  let ?es3 = "map admininstr_val vm"
  have wv: "list_all wf_val (vs_out @ vs_in)" using w e by (simp add: wfl_vals)
  have wl: "wfl [?F]" using wf' w by (simp add: wf_frame_iff)
  have "Step_pure [admininstr_sc8 (FRAME_underscore n f'
           (((map admininstr_val (vs_out @ ex) @ map admininstr_val vm) @ [admininstr_sc1 admininstr_st1_RETURN]) @ rest))] ?es3"
    by (rule Step_pure.return_frame) (simp add: vs)
  then have "Step_pure [?F] ?es3" using e vs by simp
  then have st: "Step (mk_config (mk_state s f) [?F]) (mk_config (mk_state s f) ?es3)" by (rule Step.pure)
  have w3: "wfl ?es3" using wv vs by (simp add: wfl_vals)
  have cs: "CSteps (mk_state s f) [?F] ?es3" by (rule CSteps_one[OF st z wl w3])
  obtain lh' where lf': "Lfilled k lh' (($C* map tr_val vm) @ [$Return]) LI"
    using lfilled_drop_vals[of k lh "map tr_val ex" "map tr_val vm" "[$Return]" LI] lf vs by auto
  have rt: "reduce_trans (tr_store s, tr_frame f, [Frame n (tr_frame f') (tr_admins es)])
                         (tr_store s, tr_frame f, [Frame n (tr_frame f') LI])"
    by (rule reduce_trans_local[OF reduce_trans_preach[OF r]])
  have ret: "reduce_simple [Frame n (tr_frame f') LI] ($C* map tr_val vm)"
    by (rule reduce_simple.return[OF _ lf']) (simp add: vs)
  have "wsim (tr_store s, tr_frame f, tr_admins [admininstr_sc8 (FRAME_underscore n f' es)])
             (tr_store s, tr_frame f, tr_admins ?es3)"
    unfolding tr_admins_frame by (rule wsim_rt[OF rt wsim_basic[OF ret nls_vals]])
  then have "sim (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)]) (mk_config (mk_state s f) ?es3)"
    by (simp only: sim_def tr_config.simps)
  then show ?thesis using cs w3 by blast
qed

end
