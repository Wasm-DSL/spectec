(* Step_Sim: the main simulation theorem, by induction over SpecTec's step
   relation.  WORK IN PROGRESS, not yet in ROOT.

   The invariant is a parameter: the locale [sim_inv] fixes a predicate
   [Inv z es ls r] on configurations ([ls]: the arities of the enclosing labels,
   innermost first; [r]: the return arity of the enclosing frame) and assumes
   only what the simulation needs: well-formedness, store and redex facts,
   the arities of breaks and returns that leave a label, and that [Inv] passes
   to the inner configuration of a label, a frame and an instruction context.
   The typing invariant (SpecTec's [Config_ok]) is to be shown to satisfy these
   assumptions.

   [Step_sim]: a SpecTec step of a configuration satisfying [Inv] is simulated
   by WasmCert, or is a named disagreement in some evaluation context ([Exc]),
   or SpecTec reaches a simulated configuration by further same-state steps, or
   a break or return is still on its way out ([Res]). *)
theory Step_Sim
  imports Step_Read
begin

section \<open>Disagreements of the state-changing steps\<close>

definition store_width :: "numtype \<Rightarrow> sz option \<Rightarrow> nat" where
  "store_width nt so = (case so of None \<Rightarrow> the (size (valtype_numtype nt)) div 8 | Some (mk_sz n) \<Rightarrow> n div 8)"

(* Out-of-bounds stores that SpecTec performs partially ([Oob_store]), and lane
   stores that SpecTec traps on because it adds the lane width in bits
   ([Vstore_disagree]); see DIFFERENCES.md. *)
inductive Write_exc :: "store \<Rightarrow> frame \<Rightarrow> admininstr list \<Rightarrow> state \<Rightarrow> admininstr list \<Rightarrow> bool" where
  store_oob: "fun_mem (mk_state s f) (mk_uN 0) mi \<Longrightarrow> length (BYTES mi) < un u + un (OFFSET ao) + store_width nt so \<Longrightarrow>
    Write_exc s f [i32c u, admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_sc6 (admininstr_st6_STORE nt so ao)] z' []"
| vstore_oob: "fun_mem (mk_state s f) (mk_uN 0) mi \<Longrightarrow> length (BYTES mi) < un u + un (OFFSET ao) + 16 \<Longrightarrow>
    Write_exc s f [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE V128 ao)] z' []"
| vstore_lane_oob: "fun_mem (mk_state s f) (mk_uN 0) mi \<Longrightarrow> length (BYTES mi) < un u + un (OFFSET ao) + N div 8 \<Longrightarrow>
    Write_exc s f [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)] z' []"
| vstore_lane_bits: "fun_mem (mk_state s f) (mk_uN 0) mi \<Longrightarrow> un u + un (OFFSET ao) + N div 8 \<le> length (BYTES mi) \<Longrightarrow>
    Write_exc s f [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)]
      (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP]"

(* All disagreements, in any evaluation context. *)
inductive Exc :: "state \<Rightarrow> admininstr list \<Rightarrow> state \<Rightarrow> admininstr list \<Rightarrow> bool" where
  exc_pure: "Pure_exc es es' \<Longrightarrow> Exc z es z es'"
| exc_read: "Read_exc s f es es' \<Longrightarrow> Exc (mk_state s f) es (mk_state s f) es'"
| exc_write: "Write_exc s f es z' es' \<Longrightarrow> Exc (mk_state s f) es z' es'"
| exc_label: "Exc z es z' es' \<Longrightarrow>
    Exc z [admininstr_sc7 (LABEL_underscore n ins es)] z' [admininstr_sc7 (LABEL_underscore n ins es')]"
| exc_frame: "Exc (mk_state s f') es (mk_state s' f'') es' \<Longrightarrow>
    Exc (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)] (mk_state s' f) [admininstr_sc8 (FRAME_underscore n f'' es')]"
| exc_instrs: "Exc z es z' es' \<Longrightarrow> Exc z (map admininstr_val vs @ es @ es1) z' (map admininstr_val vs @ es' @ es1)"

section \<open>Facts the state-changing steps need\<close>

(* Memories hold their minimum page count in bytes (store validity). *)
definition mem_pages :: "store \<Rightarrow> bool" where
  "mem_pages s \<longleftrightarrow> (\<forall>m \<in> set (store_MEMS s). \<exists>i j. meminst_TYPE m = PAGE (mk_limits i j) \<and> length (BYTES m) = un i * (64 * Ki))"

(* Facts about a state-changing redex that SpecTec's typing guarantees. *)
definition write_ok :: "frame \<Rightarrow> admininstr list \<Rightarrow> bool" where
  "write_ok f es \<longleftrightarrow>
     (\<forall>v x. es = [admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_SET x)] \<longrightarrow> un x < length (LOCALS f)) \<and>
     (\<forall>i. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc6 admininstr_st6_MEMORY_GROW] \<longrightarrow>
        0 < length (MEMS (frame_MODULE f))) \<and>
     (\<forall>i t c n ao. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) c),
                         admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)] \<longrightarrow>
        ext_width_ok (numtype_Inn t) n) \<and>
     (\<forall>i c N ao j. es = [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)] \<longrightarrow>
        un j < 128 div N \<and> (N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64))"

section \<open>Breaks and returns in instruction contexts\<close>

lemma lfilled_wrap:
  assumes "Lfilled k lh es LI"
  obtains lh' where "Lfilled k lh' es (($C* vs) @ LI @ es1)"
  using assms
proof (cases rule: Lfilled.cases)
  case (L0 vs0 es0)
  have "Lfilled 0 (LBase (vs @ vs0) (es0 @ es1)) es (($C* (vs @ vs0)) @ es @ es0 @ es1)"
    using Lfilled.L0[of "LBase (vs @ vs0) (es0 @ es1)" "vs @ vs0" "es0 @ es1" es] by simp
  then show thesis using that L0 by simp
next
  case (LN vs0 n es' l es'' k' lfk)
  have "Lfilled (k' + 1) (LRec (vs @ vs0) n es' l (es'' @ es1)) es (($C* (vs @ vs0)) @ [Label n es' lfk] @ es'' @ es1)"
    by (rule Lfilled.LN) (use LN in simp_all)
  then show thesis using that LN by simp
qed

lemma preach_instrs:
  "preach es LI \<Longrightarrow> preach (map admininstr_val vs @ es @ es1) (($C* map tr_val vs) @ LI @ tr_admins es1)"
  unfolding preach_def
proof (intro allI)
  fix St Fr assume p: "\<forall>St Fr. reduce_trans (St, Fr, tr_admins es) (St, Fr, LI)"
  have "reduce_trans (St, Fr, tr_admins (map admininstr_val vs) @ tr_admins es @ tr_admins es1)
                     (St, Fr, ($C* map tr_val vs) @ tr_admins es @ tr_admins es1)" by (rule eval_vals0)
  moreover have "reduce_trans (St, Fr, ($C* map tr_val vs) @ tr_admins es @ tr_admins es1)
                              (St, Fr, ($C* map tr_val vs) @ LI @ tr_admins es1)"
    using p by (blast intro: reduce_trans_L0)
  ultimately show "reduce_trans (St, Fr, tr_admins (map admininstr_val vs @ es @ es1)) (St, Fr, ($C* map tr_val vs) @ LI @ tr_admins es1)"
    by (simp only: tr_admins_append) (rule rt_trans)
qed

lemma br_pending_instrs:
  assumes "br_pending ls es es''"
  shows "br_pending ls (map admininstr_val vs @ es @ es1) (map admininstr_val vs @ es'' @ es1)"
proof -
  from assms obtain k lh l vs_out vs_in rest LI where
    p: "preach es LI" and lf: "Lfilled k lh (($C* map tr_val vs_in) @ [$Br (l + k)]) LI"
    and e: "es'' = map admininstr_val (vs_out @ vs_in) @ [admininstr_sc0 (admininstr_st0_BR (mk_uN l))] @ rest"
    and l: "l < length ls" "ls ! l \<le> length vs_in"
    unfolding br_pending_def by blast
  obtain lh' where lf': "Lfilled k lh' (($C* map tr_val vs_in) @ [$Br (l + k)]) (($C* map tr_val vs) @ LI @ tr_admins es1)"
    using lfilled_wrap[OF lf] by blast
  show ?thesis unfolding br_pending_def
    apply (rule exI[of _ k], rule exI[of _ lh'], rule exI[of _ l], rule exI[of _ "vs @ vs_out"], rule exI[of _ vs_in],
           rule exI[of _ "rest @ es1"], rule exI[of _ "($C* map tr_val vs) @ LI @ tr_admins es1"])
    using preach_instrs[OF p] lf' e l by simp
qed

lemma ret_pending_instrs:
  assumes "ret_pending r es es''"
  shows "ret_pending r (map admininstr_val vs @ es @ es1) (map admininstr_val vs @ es'' @ es1)"
proof -
  from assms obtain k lh vs_out vs_in rest LI m where
    p: "preach es LI" and lf: "Lfilled k lh (($C* map tr_val vs_in) @ [$Return]) LI"
    and e: "es'' = map admininstr_val (vs_out @ vs_in) @ [admininstr_sc1 admininstr_st1_RETURN] @ rest"
    and m: "r = Some m" "m \<le> length vs_in"
    unfolding ret_pending_def by blast
  obtain lh' where lf': "Lfilled k lh' (($C* map tr_val vs_in) @ [$Return]) (($C* map tr_val vs) @ LI @ tr_admins es1)"
    using lfilled_wrap[OF lf] by blast
  show ?thesis unfolding ret_pending_def
    apply (rule exI[of _ k], rule exI[of _ lh'], rule exI[of _ "vs @ vs_out"], rule exI[of _ vs_in],
           rule exI[of _ "rest @ es1"], rule exI[of _ "($C* map tr_val vs) @ LI @ tr_admins es1"], rule exI[of _ m])
    using preach_instrs[OF p] lf' e m by simp
qed

section \<open>The result of a step\<close>

definition Res :: "state \<Rightarrow> admininstr list \<Rightarrow> state \<Rightarrow> admininstr list \<Rightarrow> nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "Res z es z' es' ls r \<longleftrightarrow>
     sim (mk_config z es) (mk_config z' es') \<or> Exc z es z' es' \<or>
     (z' = z \<and> (\<exists>es''. CSteps z es' es'' \<and> wfl es'' \<and>
        (sim (mk_config z es) (mk_config z es'') \<or> br_pending ls es es'' \<or> ret_pending r es es'')))"

section \<open>The invariant\<close>

locale sim_inv = sim_all +
  fixes Inv :: "state \<Rightarrow> admininstr list \<Rightarrow> nat list \<Rightarrow> nat option \<Rightarrow> bool"
  assumes inv_wf: "\<And>z es ls r. Inv z es ls r \<Longrightarrow> wf_config (mk_config z es)"
    and inv_state: "\<And>s f es ls r. Inv (mk_state s f) es ls r \<Longrightarrow> state_inv s f \<and> mem_pages s"
    and inv_redex: "\<And>s f es ls r. Inv (mk_state s f) es ls r \<Longrightarrow> redex_ok f es \<and> write_ok f es \<and> instrs_typed es"
    and inv_br: "\<And>z n ins vs x es ls r.
      Inv z [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR (mk_uN (x + 1)))] @ es))] ls r \<Longrightarrow>
      x < length ls \<and> ls ! x \<le> length vs"
    and inv_ret: "\<And>z n ins vs es ls r.
      Inv z [admininstr_sc7 (LABEL_underscore n ins (map admininstr_val vs @ [admininstr_sc1 admininstr_st1_RETURN] @ es))] ls r \<Longrightarrow>
      \<exists>m. r = Some m \<and> m \<le> length vs"
    and inv_label: "\<And>z n ins es ls r. Inv z [admininstr_sc7 (LABEL_underscore n ins es)] ls r \<Longrightarrow> Inv z es (n # ls) r"
    and inv_frame: "\<And>s f n f' es ls r. Inv (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)] ls r \<Longrightarrow>
      Inv (mk_state s f') es [] (Some n)"
    and inv_instrs: "\<And>z vs es es1 ls r. Inv z (map admininstr_val vs @ es @ es1) ls r \<Longrightarrow> Inv z es ls r"


sublocale sim_all \<subseteq> pure_sim ..

section \<open>Helpers\<close>

lemma wf_num_Inn_E:
  assumes "wf_num_underscore (numtype_Inn t) c"
  obtains c' where "c = mk_num__0 t c'" "iok t c'"
proof (cases c)
  case (mk_num__0 t' c')
  then have "t' = t" using assms by (cases t; cases t') simp_all
  then show thesis using that mk_num__0 assms by simp
next
  case (mk_num__1 t' x)
  then show thesis using assms by (cases t; cases t') simp_all
qed

lemma fun_mem_I:
  "0 < length (MEMS (frame_MODULE f)) \<Longrightarrow> MEMS (frame_MODULE f) ! 0 < length (store_MEMS s) \<Longrightarrow>
   fun_mem (mk_state s f) (mk_uN 0) (store_MEMS s ! (MEMS (frame_MODULE f) ! 0))"
  by (metis fun_mem.intros proj_uN_0_un un_simp)

lemma state_inv_mem: "state_inv s f \<Longrightarrow> 0 < length (MEMS (frame_MODULE f)) \<Longrightarrow> MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)"
  by (simp add: state_inv_def)

lemma fun_with_mem_E:
  assumes "fun_with_mem (mk_state s f) x i j bs z'"
  shows "un x < length (MEMS (frame_MODULE f))"
  using assms by (auto elim: fun_with_mem.cases)

lemma Label_exit_wf: "Label_exit es es' \<Longrightarrow> wfl es \<Longrightarrow> wfl es'"
  by (erule Label_exit.cases) (auto simp: wf_label_iff wf_br_iff wf_uN_iff)

definition ResC :: "config \<Rightarrow> config \<Rightarrow> nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "ResC c c' ls r = (case (c, c') of (mk_config z es, mk_config z' es') \<Rightarrow> Res z es z' es' ls r)"

context sim_inv
begin

definition InvC :: "config \<Rightarrow> nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "InvC c ls r = (case c of mk_config z es \<Rightarrow> Inv z es ls r)"

lemma Res_sim: "sim (mk_config z es) (mk_config z' es') \<Longrightarrow> Res z es z' es' ls r"
  by (simp add: Res_def)

lemma Res_exc: "Exc z es z' es' \<Longrightarrow> Res z es z' es' ls r"
  by (simp add: Res_def)

section \<open>The main theorem\<close>

lemma Step_sim_aux:
  assumes "Step c c'" "InvC c ls r"
  shows "ResC c c' ls r"
  using assms
proof (induction arbitrary: ls r rule: Step.induct)
  case (pure es es' z)
  have I: "Inv z es ls r" using pure.prems by (simp add: InvC_def)
  have w: "wfl es" using inv_wf[OF I] by (simp add: wf_config_simps)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have ty: "instrs_typed es" using inv_redex[of s f es ls r] I z by simp
  from Step_pure_sim[OF pure.hyps w ty] show ?case
  proof (elim disjE)
    assume "psim es es'" then show ?thesis using z by (simp add: ResC_def Res_sim psim_sim)
  next
    assume "Pure_exc es es'" then show ?thesis by (simp add: ResC_def Res_exc Exc.exc_pure)
  next
    assume le: "Label_exit es es'"
    have w': "wfl es'" by (rule Label_exit_wf[OF le w])
    have "br_pending ls es es' \<or> ret_pending r es es'"
      using le
    proof (cases rule: Label_exit.cases)
      case (1 n ins vs x es0)
      have "x < length ls \<and> ls ! x \<le> length vs" using inv_br I 1 by simp
      then show ?thesis using br_exit_pending[of x ls vs n ins es0] 1 by simp
    next
      case (2 n ins vs es0)
      obtain m where "r = Some m" "m \<le> length vs" using inv_ret I 2 by fastforce
      then show ?thesis using ret_exit_pending[of r m vs n ins es0] 2 by simp
    qed
    then show ?thesis using w' by (auto simp: ResC_def Res_def)
  qed
next
  case (read z es es')
  have I: "Inv z es ls r" using read.prems by (simp add: InvC_def)
  have w: "wfl es" using inv_wf[OF I] by (simp add: wf_config_simps)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have si: "state_inv s f" and ok: "redex_ok f es" using inv_state[of s f es ls r] inv_redex[of s f es ls r] I z by simp_all
  from Step_read_sim[OF read.hyps[unfolded z] w si ok] show ?case
    using z by (auto simp: ResC_def Res_sim intro: Res_exc Exc.exc_read)
next
  case (ctxt_label z es z' es' n ins)
  obtain s f where z: "z = mk_state s f" by (cases z)
  obtain s' f' where z': "z' = mk_state s' f'" by (cases z')
  have I: "Inv (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)] ls r"
    using ctxt_label.prems z by (simp add: InvC_def)
  have R: "Res (mk_state s f) es (mk_state s' f') es' (n # ls) r"
    using ctxt_label.IH[of "n # ls" r] inv_label[OF I] z z' by (simp add: InvC_def ResC_def)
  have wz: "wf_state (mk_state s f)" and wi: "list_all wf_instr ins"
    using inv_wf[OF I] by (simp_all add: wf_config_simps wf_label_iff)
  consider (sim) "sim (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
    | (exc) "Exc (mk_state s f) es (mk_state s' f') es'"
    | (pend) es'' where "s' = s" "f' = f" "CSteps (mk_state s f) es' es''" "wfl es''"
        "sim (mk_config (mk_state s f) es) (mk_config (mk_state s f) es'') \<or>
         br_pending (n # ls) es es'' \<or> ret_pending r es es''"
    using R by (auto simp: Res_def)
  then have "Res (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)]
                 (mk_state s' f') [admininstr_sc7 (LABEL_underscore n ins es')] ls r"
  proof cases
    case sim
    then show ?thesis using sim_label by (simp add: Res_def)
  next
    case exc
    then show ?thesis by (simp add: Res_def Exc.exc_label)
  next
    case (pend es'')
    have csl: "CSteps (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es')]
                                     [admininstr_sc7 (LABEL_underscore n ins es'')]"
      by (rule CSteps_label[OF pend(3) wi])
    have wl: "wfl [admininstr_sc7 (LABEL_underscore n ins es'')]" using pend(4) wi by (simp add: wf_label_iff)
    from pend(5) show ?thesis unfolding pend(1,2)
    proof (elim disjE)
      assume "sim (mk_config (mk_state s f) es) (mk_config (mk_state s f) es'')"
      then have "sim (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)])
                     (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es'')])"
        by (rule sim_label)
      then show "Res (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)]
                     (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es')] ls r"
        using csl wl unfolding Res_def by blast
    next
      assume "br_pending (n # ls) es es''"
      from label_pending_br[OF this wz wi pend(4)] obtain es3 where
        c3: "CSteps (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es'')] es3" and w3: "wfl es3" and
        h3: "sim (mk_config (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)]) (mk_config (mk_state s f) es3) \<or>
             br_pending ls [admininstr_sc7 (LABEL_underscore n ins es)] es3"
        by blast
      have "CSteps (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es')] es3"
        by (rule rtranclp_trans[OF csl c3])
      then show "Res (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)]
                     (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es')] ls r"
        using w3 h3 unfolding Res_def by blast
    next
      assume "ret_pending r es es''"
      from label_pending_ret[OF this wz wi pend(4)] obtain es3 where
        c3: "CSteps (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es'')] es3" and w3: "wfl es3" and
        h3: "ret_pending r [admininstr_sc7 (LABEL_underscore n ins es)] es3"
        by blast
      have "CSteps (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es')] es3"
        by (rule rtranclp_trans[OF csl c3])
      then show "Res (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es)]
                     (mk_state s f) [admininstr_sc7 (LABEL_underscore n ins es')] ls r"
        using w3 h3 unfolding Res_def by blast
    qed
  qed
  then show ?case using z z' by (simp add: ResC_def)
next
  case (ctxt_frame s f' es s' f'' es' f n)
  have I: "Inv (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)] ls r"
    using ctxt_frame.prems by (simp add: InvC_def)
  have R: "Res (mk_state s f') es (mk_state s' f'') es' [] (Some n)"
    using ctxt_frame.IH[of "[]" "Some n"] inv_frame[OF I] by (simp add: InvC_def ResC_def)
  have wz: "wf_state (mk_state s f)" and wf': "wf_frame f'"
    using inv_wf[OF I] by (simp_all add: wf_config_simps wf_frame_iff)
  have wf: "wf_frame f" using wz by (simp add: wf_state_simps)
  consider (sim) "sim (mk_config (mk_state s f') es) (mk_config (mk_state s' f'') es')"
    | (exc) "Exc (mk_state s f') es (mk_state s' f'') es'"
    | (pend) es'' where "s' = s" "f'' = f'" "CSteps (mk_state s f') es' es''" "wfl es''"
        "sim (mk_config (mk_state s f') es) (mk_config (mk_state s f') es'') \<or>
         br_pending [] es es'' \<or> ret_pending (Some n) es es''"
    using R by (auto simp: Res_def)
  then have "Res (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)]
                 (mk_state s' f) [admininstr_sc8 (FRAME_underscore n f'' es')] ls r"
  proof cases
    case sim
    then show ?thesis by (rule Res_sim[OF sim_frame])
  next
    case exc
    then show ?thesis by (rule Res_exc[OF Exc.exc_frame])
  next
    case (pend es'')
    have csf: "CSteps (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es')]
                                     [admininstr_sc8 (FRAME_underscore n f' es'')]"
      by (rule CSteps_frame[OF pend(3) wf wf'])
    have wl: "wfl [admininstr_sc8 (FRAME_underscore n f' es'')]"
      using pend(4) wf' by (simp add: wf_frame_iff)
    from pend(5) show ?thesis unfolding pend(1,2)
    proof (elim disjE)
      assume "sim (mk_config (mk_state s f') es) (mk_config (mk_state s f') es'')"
      then have "sim (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)])
                     (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es'')])"
        by (rule sim_frame)
      then show "Res (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)]
                     (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es')] ls r"
        using csf wl unfolding Res_def by blast
    next
      assume "br_pending [] es es''"
      then show "Res (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)]
                     (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es')] ls r"
        by (simp add: br_pending_def)
    next
      assume "ret_pending (Some n) es es''"
      from frame_pending_ret[OF this wz wf' pend(4)] obtain es3 where
        c3: "CSteps (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es'')] es3" and w3: "wfl es3" and
        h3: "sim (mk_config (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)]) (mk_config (mk_state s f) es3)"
        by blast
      have "CSteps (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es')] es3"
        by (rule rtranclp_trans[OF csf c3])
      then show "Res (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es)]
                     (mk_state s f) [admininstr_sc8 (FRAME_underscore n f' es')] ls r"
        using w3 h3 unfolding Res_def by blast
    qed
  qed
  then show ?case by (simp add: ResC_def)
next
  case (ctxt_instrs z es z' es' vs es1)
  obtain s f where z: "z = mk_state s f" by (cases z)
  obtain s' f' where z': "z' = mk_state s' f'" by (cases z')
  have I: "Inv (mk_state s f) (map admininstr_val vs @ es @ es1) ls r"
    using ctxt_instrs.prems z by (simp add: InvC_def)
  have R: "Res (mk_state s f) es (mk_state s' f') es' ls r"
    using ctxt_instrs.IH[of ls r] inv_instrs[OF I] z z' by (simp add: InvC_def ResC_def)
  have wv: "list_all wf_val vs" and w1: "wfl es1"
    using inv_wf[OF I] by (simp_all add: wf_config_simps wfl_vals)
  consider (sim) "sim (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
    | (exc) "Exc (mk_state s f) es (mk_state s' f') es'"
    | (pend) es'' where "s' = s" "f' = f" "CSteps (mk_state s f) es' es''" "wfl es''"
        "sim (mk_config (mk_state s f) es) (mk_config (mk_state s f) es'') \<or>
         br_pending ls es es'' \<or> ret_pending r es es''"
    using R by (auto simp: Res_def)
  then have "Res (mk_state s f) (map admininstr_val vs @ es @ es1)
                 (mk_state s' f') (map admininstr_val vs @ es' @ es1) ls r"
  proof cases
    case sim
    then show ?thesis by (rule Res_sim[OF sim_instrs])
  next
    case exc
    then show ?thesis by (rule Res_exc[OF Exc.exc_instrs])
  next
    case (pend es'')
    have csi: "CSteps (mk_state s f) (map admininstr_val vs @ es' @ es1) (map admininstr_val vs @ es'' @ es1)"
      by (rule CSteps_instrs[OF pend(3) wv w1])
    have w3: "wfl (map admininstr_val vs @ es'' @ es1)"
      using wv pend(4) w1 by (simp add: wfl_vals)
    from pend(5) show ?thesis unfolding pend(1,2)
    proof (elim disjE)
      assume "sim (mk_config (mk_state s f) es) (mk_config (mk_state s f) es'')"
      then have "sim (mk_config (mk_state s f) (map admininstr_val vs @ es @ es1))
                     (mk_config (mk_state s f) (map admininstr_val vs @ es'' @ es1))"
        by (rule sim_instrs)
      then show "Res (mk_state s f) (map admininstr_val vs @ es @ es1)
                     (mk_state s f) (map admininstr_val vs @ es' @ es1) ls r"
        using csi w3 unfolding Res_def by blast
    next
      assume "br_pending ls es es''"
      then have "br_pending ls (map admininstr_val vs @ es @ es1) (map admininstr_val vs @ es'' @ es1)"
        by (rule br_pending_instrs)
      then show "Res (mk_state s f) (map admininstr_val vs @ es @ es1)
                     (mk_state s f) (map admininstr_val vs @ es' @ es1) ls r"
        using csi w3 unfolding Res_def by blast
    next
      assume "ret_pending r es es''"
      then have "ret_pending r (map admininstr_val vs @ es @ es1) (map admininstr_val vs @ es'' @ es1)"
        by (rule ret_pending_instrs)
      then show "Res (mk_state s f) (map admininstr_val vs @ es @ es1)
                     (mk_state s f) (map admininstr_val vs @ es' @ es1) ls r"
        using csi w3 unfolding Res_def by blast
    qed
  qed
  then show ?case using z z' by (simp add: ResC_def)
next
  case (Step__local_set z v x)
  have I: "Inv z [admininstr_val v, admininstr_sc4 (admininstr_st4_LOCAL_SET x)] ls r" using Step__local_set by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have "un x < length (LOCALS f)" using inv_redex[of s f _ ls r] I z by (simp add: write_ok_def)
  then show ?case using z sim_local_set[of x f s v] by (simp add: ResC_def Res_sim)
next
  case (Step__global_set z x v z')
  obtain s f where z: "z = mk_state s f" by (cases z)
  show ?case using Step__global_set z sim_global_set[of s f x v z'] by (simp add: ResC_def Res_sim)
next
  case (table_set_trap z x ti i rf)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_ref rf, admininstr_sc5 (admininstr_st5_TABLE_SET x)] ls r"
    using table_set_trap by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using inv_wf[OF I] by (auto simp: wf_config_simps elim: wf_const_i32)
  show ?case using table_set_trap z u
      sim_table_set[of s f x ti u rf undefined "mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP]"]
    by (simp add: ResC_def Res_sim)
next
  case (table_set_val z x ti i rf z')
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_ref rf, admininstr_sc5 (admininstr_st5_TABLE_SET x)] ls r"
    using table_set_val by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using inv_wf[OF I] by (auto simp: wf_config_simps elim: wf_const_i32)
  show ?case using table_set_val z u sim_table_set[of s f x ti u rf z' "mk_config z' []"]
    by (simp add: ResC_def Res_sim)
next
  case (table_grow_succeed t n rf t2 z x ti z')
  have I: "Inv z [admininstr_ref rf, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_GROW x)] ls r"
    using table_grow_succeed by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have "n < 2 ^ 32" using inv_wf[OF I] by (auto simp: wf_config_simps dest!: wf_i32_lit)
  then show ?case using table_grow_succeed z sim_table_grow[of s f x t n rf ti z'] by (auto simp: ResC_def Res_sim)
next
  case (table_grow_fail v z rf n x)
  obtain s f where z: "z = mk_state s f" by (cases z)
  show ?case using table_grow_fail z sim_table_grow_fail[of v s f rf n x] by (simp add: ResC_def Res_sim)
next
  case (Step__elem_drop z x z')
  obtain s f where z: "z = mk_state s f" by (cases z)
  show ?case using Step__elem_drop z sim_elem_drop[of s f x z'] by (simp add: ResC_def Res_sim)
next
  case (store_num_trap z mi i nt ao c)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST nt c),
                 admininstr_sc6 (admininstr_st6_STORE nt None ao)] ls r" using store_num_trap by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have w: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 i))" "wf_num_underscore nt c"
    using inv_wf[OF I] by (auto simp: wf_config_simps dest: wf_const)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w(1) by (rule wf_const_i32)
  show ?case using store_num_trap z u w(2) sim_store_num_trap[of s f mi u nt c ao] by (simp add: ResC_def Res_sim)
next
  case (store_num_val z i ao nt bs z' c)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST nt c),
                 admininstr_sc6 (admininstr_st6_STORE nt None ao)] ls r" using store_num_val by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have w: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 i))" "wf_num_underscore nt c"
    using inv_wf[OF I] by (auto simp: wf_config_simps dest: wf_const)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w(1) by (rule wf_const_i32)
  have m0: "0 < length (MEMS (frame_MODULE f))" using store_num_val z by (auto dest!: fun_with_mem_E)
  have a: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" using inv_state[of s f _ ls r] I z m0 state_inv_mem by blast
  let ?mi = "store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
  show ?case
  proof (cases "un u + un (OFFSET ao) + t_num_length (tr_numtype nt) \<le> length (BYTES ?mi)")
    case True
    have fw: "fun_with_mem (mk_state s f) (mk_uN 0) (un u + un (OFFSET ao))
                (nat \<lfloor>rat_of_nat (the (size (valtype_numtype nt))) / rat_of_nat 8\<rfloor>) (nbytes_underscore nt c) z'"
      using store_num_val z u(1) by simp
    have "sim (mk_config (mk_state s f) [i32c u, admininstr_sc1 (admininstr_st1_CONST nt c),
                                         admininstr_sc6 (admininstr_st6_STORE nt None ao)])
              (mk_config z' [])"
      by (rule sim_store_num[OF a u(2) w(2) True fw])
    then show ?thesis using z u(1) by (simp add: ResC_def Res_sim)
  next
    case False
    then have "Write_exc s f [i32c u, admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_sc6 (admininstr_st6_STORE nt None ao)] z' []"
      using fun_mem_I[OF m0 a] by (intro Write_exc.store_oob) (auto simp: store_width_def t_num_length_tr)
    then show ?thesis using store_num_val z u by (simp add: ResC_def Res_exc Exc.exc_write)
  qed
next
  case (store_pack_trap z mi i ao n t c)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) c),
                 admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)] ls r"
    using store_pack_trap by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have w: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 i))" "wf_num_underscore (numtype_Inn t) c"
    using inv_wf[OF I] by (auto simp: wf_config_simps dest: wf_const)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w(1) by (rule wf_const_i32)
  obtain c' where c': "c = mk_num__0 t c'" "iok t c'" using w(2) by (rule wf_num_Inn_E)
  have e: "ext_width_ok (numtype_Inn t) n" using inv_redex[of s f _ ls r] I z by (simp add: write_ok_def)
  show ?case using store_pack_trap z u c' e sim_store_pack_trap[of s f mi u t n ao c'] by (simp add: ResC_def Res_sim)
next
  case (store_pack_val z i ao n bs z' t c)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) c),
                 admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)] ls r"
    using store_pack_val by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have w: "wf_admininstr (admininstr_sc1 (admininstr_st1_CONST I32 i))" "wf_num_underscore (numtype_Inn t) c"
    using inv_wf[OF I] by (auto simp: wf_config_simps dest: wf_const)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using w(1) by (rule wf_const_i32)
  obtain c' where c': "c = mk_num__0 t c'" "iok t c'" using w(2) by (rule wf_num_Inn_E)
  have e: "ext_width_ok (numtype_Inn t) n" using inv_redex[of s f _ ls r] I z by (simp add: write_ok_def)
  have m0: "0 < length (MEMS (frame_MODULE f))" using store_pack_val z by (auto dest!: fun_with_mem_E)
  have a: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" using inv_state[of s f _ ls r] I z m0 state_inv_mem by blast
  let ?mi = "store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
  show ?case
  proof (cases "un u + un (OFFSET ao) + n div 8 \<le> length (BYTES ?mi)")
    case True
    have fw: "fun_with_mem (mk_state s f) (mk_uN 0) (un u + un (OFFSET ao)) (nat \<lfloor>rat_of_nat n / rat_of_nat 8\<rfloor>)
                (ibytes_underscore n (wrap__underscore (the (size (valtype_Inn t))) n c')) z'"
      using store_pack_val.hyps(1,5) z u(1) c'(1) by simp
    have "sim (mk_config (mk_state s f) [i32c u, admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) (mk_num__0 t c')),
                                         admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)])
              (mk_config z' [])"
      by (rule sim_store_pack[OF a u(2) e c'(2) True fw])
    then show ?thesis using z u(1) c'(1) by (simp add: ResC_def Res_sim)
  next
    case False
    then have "Write_exc s f [i32c u, admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) c),
                              admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)] z' []"
      using fun_mem_I[OF m0 a] by (intro Write_exc.store_oob) (auto simp: store_width_def)
    then show ?thesis using store_pack_val z u by (simp add: ResC_def Res_exc Exc.exc_write)
  qed
next
  case (vstore_oob z mi i ao c)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c, admininstr_sc6 (admininstr_st6_VSTORE V128 ao)] ls r"
    using vstore_oob by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using inv_wf[OF I] by (auto simp: wf_config_simps elim: wf_const_i32)
  show ?case using vstore_oob z u sim_vstore_trap[of s f mi u ao c] by (simp add: ResC_def Res_sim)
next
  case (vstore_val z i ao bs z' c)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c, admininstr_sc6 (admininstr_st6_VSTORE V128 ao)] ls r"
    using vstore_val by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using inv_wf[OF I] by (auto simp: wf_config_simps elim: wf_const_i32)
  have wc: "wf_uN 128 c" using inv_wf[OF I] by (auto simp: wf_config_simps dest: wf_vconst)
  have m0: "0 < length (MEMS (frame_MODULE f))" using vstore_val z by (auto dest!: fun_with_mem_E)
  have a: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" using inv_state[of s f _ ls r] I z m0 state_inv_mem by blast
  let ?mi = "store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
  show ?case
  proof (cases "un u + un (OFFSET ao) + 16 \<le> length (BYTES ?mi)")
    case True
    have fw: "fun_with_mem (mk_state s f) (mk_uN 0) (un u + un (OFFSET ao))
                (nat \<lfloor>rat_of_nat (the (size valtype_V128)) / rat_of_nat 8\<rfloor>) (vbytes_underscore V128 c) z'"
      using vstore_val.hyps(1,4) z u(1) by simp
    have "sim (mk_config (mk_state s f) [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE V128 ao)])
              (mk_config z' [])"
      by (rule sim_vstore[OF a u(2) wc True fw])
    then show ?thesis using z u(1) by (simp add: ResC_def Res_sim)
  next
    case False
    then have "Write_exc s f [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE V128 ao)] z' []"
      using fun_mem_I[OF m0 a] by (intro Write_exc.vstore_oob) auto
    then show ?thesis using vstore_val z u by (simp add: ResC_def Res_exc Exc.exc_write)
  qed
next
  case (vstore_lane_oob z mi i ao N c j)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)] ls r"
    using vstore_lane_oob by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using inv_wf[OF I] by (auto simp: wf_config_simps elim: wf_const_i32)
  have wc: "wf_uN 128 c" using inv_wf[OF I] by (auto simp: wf_config_simps dest: wf_vconst)
  have jl: "un j < 128 div N" and NN: "N = 8 \<or> N = 16 \<or> N = 32 \<or> N = 64"
    using inv_redex[of s f _ ls r] I z by (simp_all add: write_ok_def)
  obtain J where J: "fun_jsize J N" using jsize_ex[OF NN] by blast
  show ?case
  proof (cases "length (BYTES mi) < un u + un (OFFSET ao) + N div 8")
    case True
    then show ?thesis using vstore_lane_oob z u J wc jl sim_vstore_lane_trap[of s f mi u J N c j ao] by (simp add: ResC_def Res_sim)
  next
    case False
    then have "Write_exc s f [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)]
                 (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP]"
      using vstore_lane_oob z by (intro Write_exc.vstore_lane_bits) auto
    then show ?thesis using vstore_lane_oob z u by (simp add: ResC_def Res_exc Exc.exc_write)
  qed
next
  case (vstore_lane_val J w z i ao N bs z' M c j)
  have I: "Inv z [admininstr_sc1 (admininstr_st1_CONST I32 i), vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)] ls r"
    using vstore_lane_val by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  obtain u where u: "i = mk_num__0 Inn_I32 u" "un u < 2 ^ 32" using inv_wf[OF I] by (auto simp: wf_config_simps elim: wf_const_i32)
  have wc: "wf_uN 128 c" using inv_wf[OF I] by (auto simp: wf_config_simps dest: wf_vconst)
  have JN: "fun_jsize J N" using vstore_lane_val by simp
  have M: "M = 128 div N" by (rule rat_dim[OF _ JN]) (use vstore_lane_val in simp)
  have jl: "un j < M" using inv_redex[of s f _ ls r] I z M by (simp add: write_ok_def)
  have m0: "0 < length (MEMS (frame_MODULE f))" using vstore_lane_val z by (auto dest!: fun_with_mem_E)
  have a: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" using inv_state[of s f _ ls r] I z m0 state_inv_mem by blast
  let ?mi = "store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
  show ?case
  proof (cases "un u + un (OFFSET ao) + N div 8 \<le> length (BYTES ?mi)")
    case True
    have fw: "fun_with_mem (mk_state s f) (mk_uN 0) (un u + un (OFFSET ao)) (nat \<lfloor>rat_of_nat N / rat_of_nat 8\<rfloor>)
                (ibytes_underscore N (mk_uN (proj_uN_0 (the (proj_lane__0 (lanes_underscore (X (lanetype_Jnn J) (mk_dim M)) c ! un j)))))) z'"
      using vstore_lane_val.hyps(2,8) z u(1) by simp
    have "sim (mk_config (mk_state s f) [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)])
              (mk_config z' [])"
      by (rule sim_vstore_lane[OF a u(2) JN M wc jl True fw])
    then show ?thesis using z u(1) by (simp add: ResC_def Res_sim)
  next
    case False
    then have "Write_exc s f [i32c u, vc c, admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz N) ao j)] z' []"
      using fun_mem_I[OF m0 a] by (intro Write_exc.vstore_lane_oob) auto
    then show ?thesis using vstore_lane_val z u by (simp add: ResC_def Res_exc Exc.exc_write)
  qed
next
  case (memory_grow_succeed m n m2 z mi z')
  have I: "Inv z [i32c (mk_uN n), admininstr_sc6 admininstr_st6_MEMORY_GROW] ls r" using memory_grow_succeed by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have "n < 2 ^ 32" using inv_wf[OF I] by (auto simp: wf_config_simps dest!: wf_i32_lit)
  moreover have fm: "fun_mem (mk_state s f) (mk_uN 0) m" using memory_grow_succeed.hyps(2) z by simp
  have mm: "m \<in> set (store_MEMS s)" by (rule fun_mem_E[OF fm]) (simp add: nth_mem)
  have mp: "mem_pages s" using inv_state[of s f _ ls r] I z by blast
  obtain i j where p: "meminst_TYPE m = PAGE (mk_limits i j)" "length (BYTES m) = un i * (64 * Ki)"
    using mp mm unfolding mem_pages_def by blast
  ultimately show ?case using memory_grow_succeed z sim_memory_grow[of s f m n mi z' i j] by (auto simp: ResC_def Res_sim)
next
  case (memory_grow_fail v z n)
  have I: "Inv z [i32c (mk_uN n), admininstr_sc6 admininstr_st6_MEMORY_GROW] ls r" using memory_grow_fail by (simp add: InvC_def)
  obtain s f where z: "z = mk_state s f" by (cases z)
  have "0 < length (MEMS (frame_MODULE f))" using inv_redex[of s f _ ls r] I z by (simp add: write_ok_def)
  then show ?case using memory_grow_fail z sim_memory_grow_fail[of v f s n] by (simp add: ResC_def Res_sim)
next
  case (Step__data_drop z x z')
  obtain s f where z: "z = mk_state s f" by (cases z)
  show ?case using Step__data_drop z sim_data_drop[of s f x z'] by (simp add: ResC_def Res_sim)
qed

(* The main theorem. *)
theorem Step_sim:
  assumes "Step (mk_config z es) (mk_config z' es')" "Inv z es ls r"
  shows "Res z es z' es' ls r"
  using Step_sim_aux[OF assms(1), of ls r] assms(2) by (simp add: InvC_def ResC_def)

end

end
