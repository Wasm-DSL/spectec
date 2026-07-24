section \<open>Subtyping Properties\<close>

theory Subtyping_Properties imports Subtyping isabelle_reference_output_wasm2 begin

lemma Valtype_sub_refl:
  "Valtype_sub t t"
  by (metis Valtype_sub.refl)

lemma Resulttype_sub_refl:
  "Resulttype_sub ts ts"
  apply (auto simp add: Resulttype_sub.simps)
  by (metis Valtype_sub_refl list.rel_refl res_list.exhaust)

lemma Instrtype_sub_refl:
  "tf <ti: tf"
proof (cases tf)
  case (mk_instrtype x1 x2)
  then show ?thesis 
  unfolding Instrtype_sub.simps using Resulttype_sub_refl
  apply (auto split: instrtype.splits prod.splits res_list.splits)
  by (metis Resulttype_sub.cases append_Nil)
qed


(*for Seq*)
lemma Resulttype_sub_empty:
  "Resulttype_sub (mk_list []) (mk_list [])"
  by (auto simp add: Resulttype_sub.simps)

lemma Resulttype_sub_append:
assumes "Resulttype_sub (mk_list ts1') (mk_list ts)"
        "Resulttype_sub (mk_list ts2') (mk_list tf1_ran_sub)"
shows   "Resulttype_sub (mk_list (ts1' @ ts2')) (mk_list (ts @ tf1_ran_sub))"
by (cases rule: Resulttype_sub.cases[OF assms(1)];
    cases rule: Resulttype_sub.cases[OF assms(2)];
    auto intro: Resulttype_sub.mk_Resulttype_sub
                 list_all2_appendI)

lemma Resulttype_sub_split_left:
  assumes "Resulttype_sub (mk_list ts) (mk_list (ts1@ts2))"
  shows "\<exists> ts1' ts2'. Resulttype_sub (mk_list ts1') (mk_list ts1) \<and> Resulttype_sub (mk_list ts2') (mk_list ts2) \<and> ts = ts1'@ts2'"
  using assms
  apply (auto simp add: Resulttype_sub.simps)
  by (metis list_all2_append2)

lemma Instrtype_sub_sub_rule:
  assumes
    "Resulttype_sub ts1' ts1"
    "Resulttype_sub ts2 ts2'"
  shows
    "(mk_instrtype ts1 ts2) <ti: (mk_instrtype ts1' ts2')"
proof -
  obtain ts1_l ts2_l ts1'_l ts2'_l where defs:
    "ts1 = mk_list ts1_l"
    "ts2 = mk_list ts2_l"
    "ts1' = mk_list ts1'_l"
    "ts2' = mk_list ts2'_l"
    by (metis proj_list_0.cases)

  have "ts1'_l = [] @ ts1'_l \<and>
        ts2'_l = [] @ ts2'_l \<and>
        Resulttype_sub (mk_list []) (mk_list []) \<and>
        Resulttype_sub (mk_list ts1'_l) (mk_list ts1_l) \<and>
        Resulttype_sub (mk_list ts2_l) (mk_list ts2'_l)"
    using assms defs Resulttype_sub_empty
    by auto

  then show ?thesis using defs unfolding Instrtype_sub.simps
    by fastforce
qed

lemma func_sub_app_single_l:
  assumes "(mk_instrtype (mk_list []) (mk_list [])) <ti: (mk_instrtype (mk_list ts2) (mk_list ts3))"
  shows "(mk_instrtype (mk_list ts1) (mk_list ts2)) <ti: (mk_instrtype (mk_list ts1) (mk_list ts3))"
proof -
  have "Resulttype_sub (mk_list ts2) (mk_list ts3)"
    using assms Instrtype_sub.simps Resulttype_sub.simps Resulttype_sub_split_left Resulttype_sub_refl Resulttype_sub_append
      by simp
  then show ?thesis
    using Resulttype_sub_refl Instrtype_sub_sub_rule
      by force
qed


lemma func_sub_app_single_r:
  assumes "(mk_instrtype (mk_list []) (mk_list [])) <ti: (mk_instrtype (mk_list ts1) (mk_list ts2))"
  shows "(mk_instrtype (mk_list ts2) (mk_list ts3)) <ti: (mk_instrtype (mk_list ts1) (mk_list ts3))"
proof -
  have "Resulttype_sub (mk_list ts1) (mk_list ts2)"
    using assms Instrtype_sub.simps Resulttype_sub.simps Resulttype_sub_split_left Resulttype_sub_refl Resulttype_sub_append
      by simp
  then show ?thesis
    using Resulttype_sub_refl Instrtype_sub_sub_rule
      by force
qed


(*for sub*)
lemma Resulttype_sub_split_right:
  assumes "Resulttype_sub (mk_list (ts1@ts2)) (mk_list ts)"
  shows "\<exists> ts1' ts2'. Resulttype_sub (mk_list ts1) (mk_list ts1') \<and> Resulttype_sub (mk_list ts2) (mk_list ts2') \<and> ts = ts1'@ts2'"
  using assms
  apply (auto simp add: Resulttype_sub.simps)
  by (metis list_all2_append1)

lemma Valtype_sub_trans:
  assumes
    "Valtype_sub t1 t2"
    "Valtype_sub t2 t3"
  shows
    "Valtype_sub t1 t3"
  using assms Valtype_sub.simps
  by auto

lemma Resulttype_sub_trans:
  assumes
    "Resulttype_sub ts1 ts2"
    "Resulttype_sub ts2 ts3"
  shows
    "Resulttype_sub ts1 ts3"
  using Valtype_sub_trans assms
  apply (auto simp add:  Resulttype_sub.simps)
  using list_all2_trans by blast

lemma Instrtype_sub_trans:
  assumes
    "tf1 <ti: tf2"
    "tf2 <ti: tf3"
  shows
    "tf1 <ti: tf3"
proof - 
  obtain tf1_d tf1_r tf2_d tf2_r tf3_d tf3_r where defs:
    "tf1 = mk_instrtype (mk_list tf1_d) (mk_list tf1_r)"
    "tf2 = mk_instrtype (mk_list tf2_d) (mk_list tf2_r)"
    "tf3 = mk_instrtype (mk_list tf3_d) (mk_list tf3_r)"
    by (metis instrtype.exhaust res_list.exhaust)

  obtain ts_12 ts'_12 tf1_dom_sub_12 tf1_ran_sub_12 where defs12:
    "tf2_d = ts_12 @ tf1_dom_sub_12"
    "tf2_r = ts'_12 @ tf1_ran_sub_12"
    "Resulttype_sub (mk_list ts_12) (mk_list ts'_12)"
    "Resulttype_sub (mk_list tf1_dom_sub_12) (mk_list tf1_d)"
    "Resulttype_sub (mk_list tf1_r) (mk_list tf1_ran_sub_12)"
    using assms(1) defs unfolding Instrtype_sub.simps by auto

  obtain ts_23 ts'_23 tf1_dom_sub_23 tf1_ran_sub_23 where defs23:
    "tf3_d = ts_23 @ tf1_dom_sub_23"
    "tf3_r = ts'_23 @ tf1_ran_sub_23"
    "Resulttype_sub (mk_list ts_23) (mk_list ts'_23)"
    "Resulttype_sub (mk_list tf1_dom_sub_23) (mk_list tf2_d)"
    "Resulttype_sub (mk_list tf2_r) (mk_list tf1_ran_sub_23)"
    using assms(2) defs unfolding Instrtype_sub.simps by auto

  obtain tf1_ts_12 tf1_tf_dom_sub_12  where defs_split_12:
    "Resulttype_sub (mk_list tf1_ts_12) (mk_list ts_12)"
    "Resulttype_sub (mk_list tf1_tf_dom_sub_12) (mk_list tf1_dom_sub_12)"  
    "tf1_ts_12@tf1_tf_dom_sub_12 = tf1_dom_sub_23"
    using defs12(1) defs23(4)
    using Resulttype_sub_split_left by blast

  obtain tf1_ts'_12 tf1_tf_ran_sub_12 where  defs_split_23:
    "Resulttype_sub (mk_list ts'_12) (mk_list tf1_ts'_12)"
    "Resulttype_sub (mk_list tf1_ran_sub_12) (mk_list tf1_tf_ran_sub_12)"  
    "tf1_ran_sub_23 = tf1_ts'_12@tf1_tf_ran_sub_12"
    using defs12(2) defs23(5)
    using Resulttype_sub_split_right by blast

  let ?ts = "ts_23@tf1_ts_12"
  let ?ts' = "ts'_23@tf1_ts'_12"
  let ?tf1_dom_sub = "tf1_tf_dom_sub_12"
  let ?tf1_ran_sub = "tf1_tf_ran_sub_12"
  have a: "tf3_d = ?ts @ ?tf1_dom_sub"
    by (simp add: defs_split_12(3) defs23(1))
  have b: "Resulttype_sub (mk_list ?tf1_dom_sub) (mk_list tf1_d)"
    using defs12(4) defs_split_12(2) Resulttype_sub_trans by blast
  have c: "Resulttype_sub (mk_list ?ts) (mk_list ?ts')"
    using Resulttype_sub_trans
      defs12(3) defs23(3)
      list_all2_appendI[of Valtype_sub ts_23 ts'_23 tf1_ts_12 tf1_ts'_12]
    unfolding Resulttype_sub.simps 
    apply simp
    by (metis res_list.inject Resulttype_sub.simps defs_split_12(1) defs12(3) defs_split_23(1) Resulttype_sub_trans)
  have d: "tf3_r = ?ts' @ ?tf1_ran_sub" using defs23(2) defs_split_23(3)
    by auto
  have e: "Resulttype_sub (mk_list tf1_r) (mk_list ?tf1_ran_sub)"
    using defs12(5) defs_split_23(2) Resulttype_sub_trans by blast
  show ?thesis
    using a b c d e defs unfolding Instrtype_sub.simps
    apply (auto split: instrtype.splits)
    by (metis append_assoc)
qed

(*For frame*)
lemma Instrtype_sub_frame_rule:
    "(mk_instrtype (mk_list ts1) (mk_list ts2)) <ti: (mk_instrtype (mk_list (ts@ts1)) (mk_list (ts@ts2)))"
proof -
  have "ts @ ts1 = ts @ ts1 \<and>
        ts @ ts2 = ts @ ts2 \<and>
        Resulttype_sub (mk_list ts) (mk_list ts) \<and>
        Resulttype_sub (mk_list ts1) (mk_list ts1) \<and>
        Resulttype_sub (mk_list ts2) (mk_list ts2)"
    by (metis Resulttype_sub_refl)

  then show ?thesis
    unfolding Instrtype_sub.simps
    by fastforce
qed

definition t_list_subtyping :: "[resulttype, resulttype] \<Rightarrow> bool" ("_ '<ts: _" 60) where
  "t_list_subtyping t1 t2 =
    (case (t1, t2) of
      (mk_list t1s, mk_list t2s) \<Rightarrow> list_all2 Valtype_sub t1s t2s)"

lemma Resulttype_sub_t_list_subtyping:
  "Resulttype_sub rt1 rt2 \<longleftrightarrow> t_list_subtyping rt1 rt2"
  apply auto
  subgoal
    apply (induction rule: Resulttype_sub.induct)
    using t_list_subtyping_def by auto
  subgoal
    unfolding t_list_subtyping_def
    apply (auto split: prod.splits)
    by (metis list_all2_lengthD mk_Resulttype_sub res_list.case res_list.exhaust)
  done

lemma Instrtype_sub_emptyl : 
  assumes "mk_instrtype (mk_list []) (mk_list l) <ti: mk_instrtype t1 t2"
          "mk_instrtype (mk_list []) (mk_list l') <ti: mk_instrtype t2 t3"
        shows "mk_instrtype (mk_list []) (mk_list (l @ l')) <ti: mk_instrtype t1 t3" 
  using assms
proof (induction "mk_instrtype (mk_list []) (mk_list l)" "mk_instrtype t1 t2"
        rule: Instrtype_sub.induct)
  case (mk_Instrtype_sub t1l t1fst t1lst t2l t2fst t2lst)
  note outer_case = mk_Instrtype_sub
  have eqnil1: "t1lst = []" using mk_Instrtype_sub(4)
    by (simp add: Resulttype_sub.simps)
  show ?case using mk_Instrtype_sub(8)
  proof (induction "mk_instrtype (mk_list []) (mk_list l')" "mk_instrtype t2 t3"
          rule: Instrtype_sub.induct)
    case (mk_Instrtype_sub t2l' t2fst' t2lst' t3l t3fst t3lst)
    have eqnil2: "t2lst' = []" using mk_Instrtype_sub(4)
      by (simp add:Resulttype_sub.simps)
    obtain t3fstfst t3fstsnd where "t3fstfst @ t3fstsnd = t3fst" 
        "Resulttype_sub (mk_list t2fst) (mk_list t3fstfst)"
        "Resulttype_sub (mk_list t2lst) (mk_list t3fstsnd)"
      using outer_case(2,7) eqnil2 mk_Instrtype_sub(1,3,6) Resulttype_sub_split_right
      by force
    then show ?case using outer_case mk_Instrtype_sub eqnil1 eqnil2
       isabelle_reference_output_wasm2.mk_Instrtype_sub[of "t1l" "t1l" "[]" "t3l" "t3fstfst"
          "t3fstsnd @ t3lst" "[]" "l @ l'"]
      by (metis Resulttype_sub_append Resulttype_sub_trans append.right_neutral append_assoc)
  qed
qed



lemma produce_consume:
  assumes "mk_instrtype (mk_list []) (mk_list l) <ti: mk_instrtype t1 t2" 
          "mk_instrtype (mk_list (args @ l')) (mk_list res) <ti: mk_instrtype t2 t3" 
          "length l = length l'" 
        shows (* "Resulttype_sub t1 t3" *)
 "(mk_instrtype (mk_list args) (mk_list res) <ti: mk_instrtype t1 t3) \<and> 
  Resulttype_sub (mk_list l) (mk_list l')"
  using assms
proof(induction "mk_instrtype (mk_list []) (mk_list ( l))" "mk_instrtype t1 t2"
      rule: Instrtype_sub.induct)
  case (mk_Instrtype_sub t1l t1fst t1snd t2l t2fst t2snd)
  note outer = mk_Instrtype_sub
  show ?thesis using outer(8) outer
  proof (induction "mk_instrtype (mk_list (args @ l')) (mk_list res)" 
          "mk_instrtype t2 t3" 
         rule: Instrtype_sub.induct)
    case (mk_Instrtype_sub t2l' t2fst' t2snd' t3l t3fst t3snd)
    then obtain t2sndfst t2sndsnd where t2fstsnd:
        "t2snd' = t2sndfst @ t2sndsnd" 
        "Resulttype_sub (mk_list t2sndfst) (mk_list args)"
        "Resulttype_sub (mk_list t2sndsnd) (mk_list l')" 
      by (meson Resulttype_sub_split_left)
    then have lens: "length t2sndsnd = length t2snd" using mk_Instrtype_sub
      by (simp add: Resulttype_sub.simps)
    have "t2l = t2l'" using mk_Instrtype_sub by auto
    then have "t2fst = t2fst' @ t2sndfst" using t2fstsnd(1) lens mk_Instrtype_sub(1,9)
      by (metis append.assoc append_eq_append_conv)
    then have "Resulttype_sub (mk_list t1l) (mk_list (t2fst' @ t2sndfst))"
      using mk_Instrtype_sub 
      by (metis Resulttype_sub_append append.right_neutral)
    then obtain t1fst' t1snd' where t1fstsnd:
      "t1l = t1fst' @ t1snd'" 
      "Resulttype_sub (mk_list t1fst') (mk_list t2fst')"
      "Resulttype_sub (mk_list t1snd') (mk_list t2sndfst)"
      by (meson Resulttype_sub_split_left)
    then have sub1: "Resulttype_sub (mk_list t1fst') (mk_list t3fst)"
      using mk_Instrtype_sub Resulttype_sub_trans by fast
    have sub2: "Resulttype_sub (mk_list t1snd') (mk_list args)"
      using mk_Instrtype_sub t1fstsnd Resulttype_sub_trans 
      using t2fstsnd(2) by blast
    have "Resulttype_sub (mk_list l) (mk_list l')" using t2fstsnd mk_Instrtype_sub
      by (metis Resulttype_sub_trans \<open>t2fst = t2fst' @ t2sndfst\<close> \<open>t2l = t2l'\<close> 
          append.assoc
          append_eq_append_conv)
    then show ?thesis using mk_Instrtype_sub t2fstsnd t1fstsnd sub1 sub2
        isabelle_reference_output_wasm2.mk_Instrtype_sub[
           of t1l t1fst' t1snd' t3l t3fst t3snd args res, OF t1fstsnd(1)]
      by fast
  qed
qed

lemma produce_consume_waste: 
  assumes "mk_instrtype (mk_list []) (mk_list (junk @ l)) <ti: mk_instrtype t1 t2" 
          "mk_instrtype (mk_list (args @ l')) (mk_list res) <ti: mk_instrtype t2 t3" 
          "length l = length l'" 
        shows 
  (* "(mk_instrtype (mk_list args) (mk_list res) <ti: mk_instrtype t1 t3) \<and>  *)
  "Resulttype_sub (mk_list l) (mk_list l')"
  using assms
proof(induction "mk_instrtype (mk_list []) (mk_list (junk @ l))" "mk_instrtype t1 t2"
      rule: Instrtype_sub.induct)
  case (mk_Instrtype_sub t1l t1fst t1snd t2l t2fst t2snd)
  note outer = mk_Instrtype_sub
  show ?thesis using outer(8) outer
  proof (induction "mk_instrtype (mk_list (args @ l')) (mk_list res)" 
          "mk_instrtype t2 t3" 
         rule: Instrtype_sub.induct)
    case (mk_Instrtype_sub t2l' t2fst' t2snd' t3l t3fst t3snd)
    then obtain t2sndfst' t2sndsnd' where t2fstsnd':
        "t2snd' = t2sndfst' @ t2sndsnd'" 
        "Resulttype_sub (mk_list t2sndfst') (mk_list args)"
        "Resulttype_sub (mk_list t2sndsnd') (mk_list l')" 
      by (meson Resulttype_sub_split_left)
    obtain t2sndfst t2sndsnd where t2fstsnd:
       "t2snd = t2sndfst @ t2sndsnd" 
       "Resulttype_sub (mk_list junk) (mk_list t2sndfst)"
       "Resulttype_sub (mk_list l) (mk_list t2sndsnd)" 
      using Resulttype_sub_split_right mk_Instrtype_sub by meson
    then have lens: "length t2sndsnd = length t2sndsnd'" using mk_Instrtype_sub t2fstsnd'
      by (simp add: Resulttype_sub.simps)
    have teq: "t2l = t2l'" using mk_Instrtype_sub by auto
    then have "t2fst @ t2sndfst = t2fst' @ t2sndfst'" using 
        t2fstsnd(1) lens mk_Instrtype_sub(1,9) t2fstsnd'(1)
      by (metis append.assoc append_eq_append_conv)
    then show ?thesis 
      using t2fstsnd t2fstsnd' mk_Instrtype_sub teq 
      by (metis Resulttype_sub_trans append.assoc append_eq_append_conv)
  qed
qed

lemma subtyping_length_l:
  assumes "mk_instrtype (mk_list l1) (mk_list l2) <ti: mk_instrtype (mk_list l3) (mk_list l4)"
  shows "length l1 \<le> length l3"
  using assms
proof (induction "mk_instrtype (mk_list l1) (mk_list l2)" "mk_instrtype (mk_list l3) (mk_list l4)"
        rule:Instrtype_sub.induct)
  case (mk_Instrtype_sub t_lst t_11'_lst t'_lst t_12'_lst) then show ?case 
    by (simp add: Resulttype_sub.simps)
qed


lemma subtyping_length_r:
  assumes "mk_instrtype (mk_list l1) (mk_list l2) <ti: mk_instrtype (mk_list l3) (mk_list l4)"
  shows "length l2 \<le> length l4"
  using assms
proof (induction "mk_instrtype (mk_list l1) (mk_list l2)" "mk_instrtype (mk_list l3) (mk_list l4)"
        rule:Instrtype_sub.induct)
  case (mk_Instrtype_sub t_lst t_11'_lst t'_lst t_12'_lst) then show ?case 
    by (simp add: Resulttype_sub.simps)
qed

lemma produce_consume_arbitrary:
  assumes "mk_instrtype (mk_list []) (mk_list l) <ti: mk_instrtype t1 t2" 
          "mk_instrtype (mk_list (args @ l')) (mk_list res) <ti: mk_instrtype t2 t3"
          "length l \<ge> length l'" 
        shows "\<exists> l1 l2. l = l1 @ l2 \<and> Resulttype_sub (mk_list l2) (mk_list l')"
  using assms
proof - 
  have 
      "l = take (length l - length l') l @ drop (length l - length l') l" 
      "length ((drop (length l - length l') l)) = length l'" 
    using assms(3) by auto
  then show ?thesis using produce_consume_waste assms by metis
qed


end