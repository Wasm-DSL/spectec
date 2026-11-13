(* WasmCert-Isabelle reduction commutes with evaluating null references.

   WasmCert-Isabelle has two forms of a null reference in the instruction stream:
   the instruction [Basic (Ref_null t)] and the value [Ref (ConstNull t)] it reduces to
   (rule [null]).  Two configurations agree up to evaluated nulls ([nls a b],
   Reduction.thy) when [a] has [Ref (ConstNull t)] in places where [b] has
   [Basic (Ref_null t)].  No reduction rule other than [null] can tell the two forms apart,
   so any run of the less evaluated configuration [b] can be replayed from the more
   evaluated one [a], ending in configurations that again agree up to nulls
   ([nl_reduce_trans]).

   Back-translation identifies the two forms (Backtranslation_Sound.thy), so this is
   what the Rocq bridge's [Step_sim_back] needs in Isabelle: WasmCert-Coq has a
   single null form and needs no such lemma. *)
theory Null_Commute
  imports Reduction
begin

section \<open>Rigid instructions\<close>

(* Instructions that [nl] relates only to themselves. *)
definition rigid :: "e \<Rightarrow> bool" where
  "rigid e \<longleftrightarrow> (\<forall>t. e \<noteq> Basic (Ref_null t)) \<and> (\<forall>n les es. e \<noteq> Label n les es) \<and> (\<forall>n f es. e \<noteq> Frame n f es)"

lemma rigid_simps[simp]:
  "rigid (Basic b) \<longleftrightarrow> (\<forall>t. b \<noteq> Ref_null t)"
  "rigid Trap" "rigid (Invoke i)" "rigid (Ref r)"
  "\<not> rigid (Label n les es)" "\<not> rigid (Frame n f es)"
  by (auto simp: rigid_def)

lemma rigid_v_to_e[simp]: "rigid ($C v)"
  by (cases v) (simp_all add: v_to_e_def)

lemma rigid_vs[simp]: "list_all rigid ($C* vs)"
  by (induction vs) simp_all

lemma nl_rigid: "nl x y \<Longrightarrow> rigid y \<Longrightarrow> x = y"
  by (erule nl.cases) auto

lemma nls_rigid: "nls xs ys \<Longrightarrow> list_all rigid ys \<Longrightarrow> xs = ys"
  by (induction rule: list_all2_induct) (auto dest: nl_rigid)

lemma nl_Label_inv: "nl x (Label n les es) \<Longrightarrow> \<exists>es'. x = Label n les es' \<and> nls es' es"
  by (erule nl.cases) auto

lemma nl_Frame_inv: "nl x (Frame n f es) \<Longrightarrow> \<exists>es'. x = Frame n f es' \<and> nls es' es"
  by (erule nl.cases) auto

lemma nl_null_inv: "nl x (Basic (Ref_null t)) \<Longrightarrow> x = Basic (Ref_null t) \<or> x = Ref (ConstNull t)"
  by (erule nl.cases) auto

lemma nl_Trap_left: "nl Trap y \<Longrightarrow> y = Trap"
  by (erule nl.cases) auto

lemma nls_single: "nls a [y] \<longleftrightarrow> (\<exists>x. a = [x] \<and> nl x y)"
  by (auto simp: list_all2_Cons2)

lemma nls_Label_rigid: "nls a [Label n les es] \<Longrightarrow> list_all rigid es \<Longrightarrow> a = [Label n les es]"
  by (auto simp: nls_single dest!: nl_Label_inv dest: nls_rigid)

lemma nls_Frame_rigid: "nls a [Frame n f es] \<Longrightarrow> list_all rigid es \<Longrightarrow> a = [Frame n f es]"
  by (auto simp: nls_single dest!: nl_Frame_inv dest: nls_rigid)

section \<open>Transitivity\<close>

lemma nl_Label_left: "nl (Label n les es) z \<Longrightarrow> \<exists>es'. z = Label n les es' \<and> nls es es'"
  by (erule nl.cases) auto

lemma nl_Frame_left: "nl (Frame n f es) z \<Longrightarrow> \<exists>es'. z = Frame n f es' \<and> nls es es'"
  by (erule nl.cases) auto

lemma nls_comp_set:
  assumes xy: "nls xs ys" and yz: "nls ys zs"
    and comp: "\<And>a b c. b \<in> set ys \<Longrightarrow> nl a b \<Longrightarrow> nl b c \<Longrightarrow> nl a c"
  shows "nls xs zs"
proof -
  have lx: "length xs = length ys" and lz: "length ys = length zs"
    using xy yz by (simp_all add: list_all2_lengthD)
  have "\<forall>i < length xs. nl (xs ! i) (zs ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length xs"
    have ab: "nl (xs ! i) (ys ! i)" using xy i by (simp add: list_all2_conv_all_nth)
    have bc: "nl (ys ! i) (zs ! i)" using yz i lx by (simp add: list_all2_conv_all_nth)
    have b: "ys ! i \<in> set ys" using i lx by simp
    show "nl (xs ! i) (zs ! i)" by (rule comp[OF b ab bc])
  qed
  then show ?thesis using lx lz by (simp add: list_all2_conv_all_nth)
qed

(* By induction on the middle instruction, so that the induction hypothesis for the
   bodies of labels and frames has the datatype's [x \<in> set es] form. *)
lemma nl_trans: "nl x y \<Longrightarrow> nl y z \<Longrightarrow> nl x z"
proof (induction y arbitrary: x z)
  case (Basic b)
  then show ?case by (auto elim!: nl.cases)
next
  case Trap
  then show ?case by (auto elim!: nl.cases)
next
  case (Invoke i)
  then show ?case by (auto elim!: nl.cases)
next
  case (Label n les es)
  obtain esx where x: "x = Label n les esx" "nls esx es" using nl_Label_inv[OF Label.prems(1)] by blast
  obtain esz where z: "z = Label n les esz" "nls es esz" using nl_Label_left[OF Label.prems(2)] by blast
  have "nls esx esz" by (rule nls_comp_set[OF x(2) z(2)]) (use Label.IH in blast)
  then show ?case using x(1) z(1) by (simp add: nl_label)
next
  case (Frame n f es)
  obtain esx where x: "x = Frame n f esx" "nls esx es" using nl_Frame_inv[OF Frame.prems(1)] by blast
  obtain esz where z: "z = Frame n f esz" "nls es esz" using nl_Frame_left[OF Frame.prems(2)] by blast
  have "nls esx esz" by (rule nls_comp_set[OF x(2) z(2)]) (use Frame.IH in blast)
  then show ?case using x(1) z(1) by (simp add: nl_frame)
next
  case (Ref r)
  then show ?case by (auto elim!: nl.cases)
qed

lemma nls_trans:
  assumes "nls x y" "nls y z"
  shows "nls x z"
  by (rule nls_comp_set[OF assms]) (rule nl_trans)

section \<open>Evaluation contexts\<close>

(* Two evaluation contexts that agree up to evaluated nulls. *)
inductive nlh :: "Lholed \<Rightarrow> Lholed \<Rightarrow> bool" where
  nlh_base: "nls es1 es2 \<Longrightarrow> nlh (LBase vs es1) (LBase vs es2)"
| nlh_rec: "nlh l1 l2 \<Longrightarrow> nls es1 es2 \<Longrightarrow> nlh (LRec vs n les l1 es1) (LRec vs n les l2 es2)"

(* A configuration that agrees with a filled context up to nulls is a filled
   context of the same shape. *)
lemma nls_Lfilled:
  assumes "Lfilled k lh es Ys" "nls Xs Ys"
  shows "\<exists>lh' X0. Lfilled k lh' X0 Xs \<and> nls X0 es \<and> nlh lh' lh"
  using assms
proof (induction arbitrary: Xs rule: Lfilled.induct)
  case (L0 lholed vs es' es)
  obtain X1 X2 X3 where Xs: "Xs = X1 @ X2 @ X3" and n1: "nls X1 ($C* vs)" and n2: "nls X2 es"
    and n3: "nls X3 es'"
    using L0.prems by (auto simp: list_all2_append2)
  have "X1 = $C* vs" using nls_rigid[OF n1] by simp
  then have "Lfilled 0 (LBase vs X3) X2 Xs" using Xs Lfilled.L0[of "LBase vs X3" vs X3 X2] by simp
  moreover have "nlh (LBase vs X3) lholed" using L0.hyps n3 by (simp add: nlh_base)
  ultimately show ?case using n2 by blast
next
  case (LN lholed vs n es' l es'' k es lfilledk)
  obtain X1 x X3 where Xs: "Xs = X1 @ [x] @ X3" and n1: "nls X1 ($C* vs)"
    and nx: "nl x (Label n es' lfilledk)" and n3: "nls X3 es''"
    using LN.prems by (auto simp: list_all2_append2 list_all2_Cons2)
  have X1: "X1 = $C* vs" using nls_rigid[OF n1] by simp
  obtain Xk where x: "x = Label n es' Xk" and nk: "nls Xk lfilledk" using nl_Label_inv[OF nx] by blast
  obtain lh0 X0 where l0: "Lfilled k lh0 X0 Xk" "nls X0 es" "nlh lh0 l" using LN.IH[OF nk] by blast
  have "Lfilled (k + 1) (LRec vs n es' lh0 X3) X0 Xs"
    using Lfilled.LN[of "LRec vs n es' lh0 X3" vs n es' lh0 X3 k X0 Xk] l0(1) Xs X1 x by simp
  moreover have "nlh (LRec vs n es' lh0 X3) lholed" using LN.hyps(1) l0(3) n3 by (simp add: nlh_rec)
  ultimately show ?case using l0(2) by blast
qed

(* Filling contexts that agree up to nulls with contents that agree up to nulls. *)
lemma nlh_Lfilled:
  assumes "Lfilled k lh' X0 Xs" "nlh lh' lh" "Lfilled k lh Y0 Ys" "nls X0 Y0"
  shows "nls Xs Ys"
  using assms
proof (induction arbitrary: lh Ys rule: Lfilled.induct)
  case (L0 lholed vs es' es)
  obtain es2 where lh: "lh = LBase vs es2" "nls es' es2"
    using L0.prems(1) L0.hyps by (auto elim: nlh.cases)
  have "Ys = ($C* vs) @ Y0 @ es2" using L0.prems(2) lh(1) by (auto elim: Lfilled.cases)
  then show ?case using L0.prems(3) lh(2) by (simp add: list_all2_appendI)
next
  case (LN lholed vs n es' l es'' k es lfilledk)
  obtain l2 es2 where lh: "lh = LRec vs n es' l2 es2" "nlh l l2" "nls es'' es2"
    using LN.prems(1) LN.hyps(1) by (auto elim: nlh.cases)
  obtain Yk where Ys: "Ys = ($C* vs) @ [Label n es' Yk] @ es2" and yk: "Lfilled k l2 Y0 Yk"
    using LN.prems(2) lh(1) by (auto elim: Lfilled.cases)
  have "nls lfilledk Yk" by (rule LN.IH[OF lh(2) yk LN.prems(3)])
  then show ?case using Ys lh(3) by (simp add: list_all2_appendI nl_label)
qed

lemma Lfilled_refill: "Lfilled k lh e1 X1 \<Longrightarrow> \<exists>X2. Lfilled k lh e2 X2"
proof (induction rule: Lfilled.induct)
  case (L0 lholed vs es' es)
  then show ?case using Lfilled.L0[of lholed vs es' e2] by blast
next
  case (LN lholed vs n es' l es'' k es lfilledk)
  then obtain x where "Lfilled k l e2 x" by blast
  then have "Lfilled (k + 1) lholed e2 (($C* vs) @ [Label n es' x] @ es'')"
    using Lfilled.LN[OF LN.hyps(1)] by blast
  then show ?case by blast
qed

section \<open>Pure reduction\<close>

lemma rt_basic: "reduce_simple e e' \<Longrightarrow> reduce_trans (s, f, e) (s, f, e')"
  by (rule rt_step[OF reduce.basic rt_refl])

lemma nl_rigid_simple:
  "reduce_simple b b' \<Longrightarrow> nls a b \<Longrightarrow> list_all rigid b \<Longrightarrow>
   \<exists>a'. reduce_trans (s, f, a) (s, f, a') \<and> nls a' b'"
proof -
  assume r: "reduce_simple b b'" and n: "nls a b" and l: "list_all rigid b"
  have "a = b" by (rule nls_rigid[OF n l])
  then have "reduce_trans (s, f, a) (s, f, b')" using rt_basic[OF r] by simp
  then show ?thesis by (intro exI[of _ b']) simp
qed

lemma nl_null_step:
  assumes "nls a [Basic (Ref_null t)]"
  shows "\<exists>a'. reduce_trans (s, f, a) (s, f, a') \<and> nls a' [Ref (ConstNull t)]"
proof -
  obtain x where a: "a = [x]" and n: "nl x (Basic (Ref_null t))" using assms by (auto simp: nls_single)
  from nl_null_inv[OF n] show ?thesis
  proof
    assume "x = Basic (Ref_null t)"
    then show ?thesis using a rt_basic[OF reduce_simple.null[of t]] by (intro exI[of _ "[Ref (ConstNull t)]"]) simp
  next
    assume "x = Ref (ConstNull t)"
    then show ?thesis using a by (intro exI[of _ "[Ref (ConstNull t)]"]) simp
  qed
qed

lemma nl_br:
  assumes "length vs = n" "Lfilled i lh (($C* vs) @ [$Br i]) LI" "nls a [Label n es LI]"
  shows "\<exists>a'. reduce_trans (s, f, a) (s, f, a') \<and> nls a' (($C* vs) @ es)"
proof -
  obtain LIa where a: "a = [Label n es LIa]" and n: "nls LIa LI"
    using assms(3) by (auto simp: nls_single dest!: nl_Label_inv)
  obtain lh' X0 where l: "Lfilled i lh' X0 LIa" and n0: "nls X0 (($C* vs) @ [$Br i])"
    using nls_Lfilled[OF assms(2) n] by blast
  have "X0 = ($C* vs) @ [$Br i]" by (rule nls_rigid[OF n0]) simp
  then have "reduce_simple [Label n es LIa] (($C* vs) @ es)"
    using reduce_simple.br[OF assms(1)] l by simp
  then have "reduce_trans (s, f, a) (s, f, ($C* vs) @ es)" unfolding a by (rule rt_basic)
  then show ?thesis by (intro exI[of _ "($C* vs) @ es"]) simp
qed

lemma nl_return:
  assumes "length vs = n" "Lfilled j lh (($C* vs) @ [$Return]) es" "nls a [Frame n f0 es]"
  shows "\<exists>a'. reduce_trans (s, f, a) (s, f, a') \<and> nls a' ($C* vs)"
proof -
  obtain esa where a: "a = [Frame n f0 esa]" and n: "nls esa es"
    using assms(3) by (auto simp: nls_single dest!: nl_Frame_inv)
  obtain lh' X0 where l: "Lfilled j lh' X0 esa" and n0: "nls X0 (($C* vs) @ [$Return])"
    using nls_Lfilled[OF assms(2) n] by blast
  have "X0 = ($C* vs) @ [$Return]" by (rule nls_rigid[OF n0]) simp
  then have "reduce_simple [Frame n f0 esa] ($C* vs)"
    using reduce_simple.return[OF assms(1)] l by simp
  then have "reduce_trans (s, f, a) (s, f, $C* vs)" unfolding a by (rule rt_basic)
  then show ?thesis by (intro exI[of _ "$C* vs"]) simp
qed

lemma nl_trap:
  assumes "es \<noteq> [Trap]" "Lfilled 0 lh [Trap] es" "nls a es"
  shows "\<exists>a'. reduce_trans (s, f, a) (s, f, a') \<and> nls a' [Trap]"
proof -
  obtain lh' X0 where l: "Lfilled 0 lh' X0 a" and n0: "nls X0 [Trap]"
    using nls_Lfilled[OF assms(2,3)] by blast
  have X0: "X0 = [Trap]" by (rule nls_rigid[OF n0]) simp
  have "a \<noteq> [Trap]"
  proof
    assume "a = [Trap]"
    then have "es = [Trap]" using assms(3) by (auto simp: list_all2_Cons1 dest: nl_Trap_left)
    then show False using assms(1) by simp
  qed
  then have "reduce_simple a [Trap]" using reduce_simple.trap l X0 by simp
  then have "reduce_trans (s, f, a) (s, f, [Trap])" by (rule rt_basic)
  then show ?thesis by (intro exI[of _ "[Trap]"]) simp
qed

lemma nl_reduce_simple:
  "reduce_simple b b' \<Longrightarrow> reduce_simple b b' \<Longrightarrow> nls a b \<Longrightarrow>
   \<exists>a'. reduce_trans (s, f, a) (s, f, a') \<and> nls a' b'"
proof (induction arbitrary: a rule: reduce_simple.induct)
  case null
  show ?case by (rule nl_null_step[OF null.prems(2)])
next
  case (label_const n es vs)
  then have "a = [Label n es ($C* vs)]" by (intro nls_Label_rigid) simp_all
  then show ?case using rt_basic[OF label_const.prems(1)] by (intro exI[of _ "$C* vs"]) simp
next
  case (label_trap n es)
  then have "a = [Label n es [Trap]]" by (intro nls_Label_rigid) simp_all
  then show ?case using rt_basic[OF label_trap.prems(1)] by (intro exI[of _ "[Trap]"]) simp
next
  case br
  show ?case by (rule nl_br[OF br.hyps br.prems(2)])
next
  case (local_const n f0 vs)
  then have "a = [Frame n f0 ($C* vs)]" by (intro nls_Frame_rigid) simp_all
  then show ?case using rt_basic[OF local_const.prems(1)] by (intro exI[of _ "$C* vs"]) simp
next
  case (local_trap n f0)
  then have "a = [Frame n f0 [Trap]]" by (intro nls_Frame_rigid) simp_all
  then show ?case using rt_basic[OF local_trap.prems(1)] by (intro exI[of _ "[Trap]"]) simp
next
  case return
  show ?case by (rule nl_return[OF return.hyps return.prems(2)])
next
  case trap
  show ?case by (rule nl_trap[OF trap.hyps trap.prems(2)])
qed (rule nl_rigid_simple, assumption, assumption, simp add: list_all_iff)+

section \<open>Reduction\<close>

lemma nl_rigid_step:
  "\<lparr>s;f;b\<rparr> \<leadsto> \<lparr>s';f';b'\<rparr> \<Longrightarrow> nls a b \<Longrightarrow> list_all rigid b \<Longrightarrow>
   \<exists>a'. reduce_trans (s, f, a) (s', f', a') \<and> nls a' b'"
proof -
  assume r: "\<lparr>s;f;b\<rparr> \<leadsto> \<lparr>s';f';b'\<rparr>" and n: "nls a b" and l: "list_all rigid b"
  have "a = b" by (rule nls_rigid[OF n l])
  then have "reduce_trans (s, f, a) (s', f', b')" using rt_step[OF r rt_refl] by simp
  then show ?thesis by (intro exI[of _ b']) simp
qed

lemma nl_reduce_aux:
  "\<lparr>s;f;b\<rparr> \<leadsto> \<lparr>s';f';b'\<rparr> \<Longrightarrow> \<lparr>s;f;b\<rparr> \<leadsto> \<lparr>s';f';b'\<rparr> \<Longrightarrow> nls a b \<Longrightarrow>
   \<exists>a'. reduce_trans (s, f, a) (s', f', a') \<and> nls a' b'"
proof (induction arbitrary: a rule: reduce.induct)
  case (basic e e' s f)
  show ?case by (rule nl_reduce_simple[OF basic.hyps basic.hyps basic.prems(2)])
next
  case (label s f es s' f' es' k lholed les les')
  obtain lh' a0 where l: "Lfilled k lh' a0 a" "nls a0 es" "nlh lh' lholed"
    using nls_Lfilled[OF label.hyps(2) label.prems(2)] by blast
  obtain a0' where r: "reduce_trans (s, f, a0) (s', f', a0')" "nls a0' es'"
    using label.IH[OF label.hyps(1) l(2)] by blast
  obtain A' where A': "Lfilled k lh' a0' A'" using Lfilled_refill[OF l(1)] by blast
  have "reduce_trans (s, f, a) (s', f', A')" by (rule reduce_trans_lfilled[OF r(1) l(1) A'])
  moreover have "nls A' les'" by (rule nlh_Lfilled[OF A' l(3) label.hyps(3) r(2)])
  ultimately show ?case by blast
next
  case (local s f es s' f' es' f0 n)
  obtain esa where a: "a = [Frame n f esa]" and n: "nls esa es"
    using local.prems(2) by (auto simp: nls_single dest!: nl_Frame_inv)
  obtain esa' where r: "reduce_trans (s, f, esa) (s', f', esa')" "nls esa' es'"
    using local.IH[OF local.hyps n] by blast
  have "reduce_trans (s, f0, [Frame n f esa]) (s', f0, [Frame n f' esa'])"
    by (rule reduce_trans_local[OF r(1)])
  moreover have "nls [Frame n f' esa'] [Frame n f' es']" using r(2) by (simp add: nl_frame)
  ultimately show ?case using a by blast
qed (rule nl_rigid_step, assumption, assumption, simp add: list_all_iff)+

theorem nl_reduce:
  "\<lparr>s;f;b\<rparr> \<leadsto> \<lparr>s';f';b'\<rparr> \<Longrightarrow> nls a b \<Longrightarrow> \<exists>a'. reduce_trans (s, f, a) (s', f', a') \<and> nls a' b'"
  using nl_reduce_aux by blast

lemma nl_reduce_trans_gen:
  assumes "reduce_trans c c'"
  shows "\<forall>s f b s' f' b' a. c = (s, f, b) \<longrightarrow> c' = (s', f', b') \<longrightarrow> nls a b \<longrightarrow>
           (\<exists>a'. reduce_trans (s, f, a) (s', f', a') \<and> nls a' b')"
  using assms[unfolded reduce_trans_def]
proof (induction rule: rtranclp_induct)
  case base
  show ?case
  proof (intro allI impI)
    fix s f b s' f' b' a
    assume "c = (s, f, b)" "c = (s', f', b')" "nls a b"
    then show "\<exists>a'. reduce_trans (s, f, a) (s', f', a') \<and> nls a' b'" by (intro exI[of _ a]) simp
  qed
next
  case (step y z)
  show ?case
  proof (intro allI impI)
    fix s f b s' f' b' a
    assume c: "c = (s, f, b)" and z: "z = (s', f', b')" and n: "nls a b"
    obtain s1 f1 b1 where y: "y = (s1, f1, b1)" by (cases y)
    obtain a1 where r1: "reduce_trans (s, f, a) (s1, f1, a1)" and n1: "nls a1 b1"
      using step.IH c y n by blast
    have "\<lparr>s1;f1;b1\<rparr> \<leadsto> \<lparr>s';f';b'\<rparr>" using step.hyps(2) y z by simp
    then obtain a' where r2: "reduce_trans (s1, f1, a1) (s', f', a')" and n2: "nls a' b'"
      using nl_reduce n1 by blast
    have "reduce_trans (s, f, a) (s', f', a')" by (rule rt_trans[OF r1 r2])
    then show "\<exists>a'. reduce_trans (s, f, a) (s', f', a') \<and> nls a' b'" using n2 by blast
  qed
qed

(* The commutation lemma. *)
theorem nl_reduce_trans:
  "reduce_trans (s, f, b) (s', f', b') \<Longrightarrow> nls a b \<Longrightarrow>
   \<exists>a'. reduce_trans (s, f, a) (s', f', a') \<and> nls a' b'"
  using nl_reduce_trans_gen by blast

(* The simulation relation is preserved by evaluating nulls in the source. *)
corollary nls_wsim: "wsim (s, f, b) c \<Longrightarrow> nls a b \<Longrightarrow> wsim (s, f, a) c"
proof -
  assume w: "wsim (s, f, b) c" and n: "nls a b"
  obtain s' f' es' where c: "c = (s', f', es')" by (cases c)
  obtain es'' where r: "reduce_trans (s, f, b) (s', f', es'')" and n'': "nls es'' es'"
    using w c by (auto simp: wsim_def)
  obtain a' where r': "reduce_trans (s, f, a) (s', f', a')" and n': "nls a' es''"
    using nl_reduce_trans[OF r n] by blast
  show "wsim (s, f, a) c" using r' nls_trans[OF n' n''] c by (auto simp: wsim_def)
qed

end
