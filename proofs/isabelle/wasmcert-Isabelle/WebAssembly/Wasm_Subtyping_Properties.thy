section \<open>Subtyping properties\<close>

theory Wasm_Subtyping_Properties imports Wasm_Base_Defs begin

lemma typeof_not_bot:
  "typeof v \<noteq> T_bot"
  unfolding typeof_def
  by (auto split: v.splits)

lemma t_subtyping_refl:
  shows "t_subtyping t t"
  unfolding t_subtyping_def by blast

lemma t_subtyping_trans:
  assumes "t_subtyping t1 t2" "t_subtyping t2 t3"
  shows "t_subtyping t1 t3"
  using assms unfolding t_subtyping_def by blast

lemma t_list_subtyping_refl:
  shows "t_list_subtyping ts ts"
  unfolding t_list_subtyping_def using t_subtyping_refl
  using list.rel_refl by blast

lemma t_list_subtyping_trans:
  assumes "t_list_subtyping ts1 ts2" "t_list_subtyping ts2 ts3"
  shows "t_list_subtyping ts1 ts3"
  using assms unfolding t_list_subtyping_def using t_subtyping_trans
  using list_all2_trans by blast

lemma t_list_subtyping_split1:
  assumes "t_list_subtyping (ts1@ts2) ts"
  shows "\<exists> ts1' ts2'. t_list_subtyping ts1 ts1' \<and> t_list_subtyping ts2 ts2' \<and> ts = ts1'@ts2'"
  using assms unfolding t_list_subtyping_def
  by (meson list_all2_append1)

lemma t_list_subtyping_split2:
  assumes "t_list_subtyping ts (ts1@ts2)"
  shows "\<exists> ts1' ts2'. t_list_subtyping ts1' ts1 \<and> t_list_subtyping ts2' ts2 \<and> ts = ts1'@ts2'"
  using assms unfolding t_list_subtyping_def
  by (meson list_all2_append2)

lemma t_list_subtyping_prepend:
  assumes "t_list_subtyping ts1 ts2"
  shows "t_list_subtyping (ts@ts1) (ts@ts2)"
  using assms unfolding t_list_subtyping_def
  by (simp add: list.rel_refl list_all2_appendI t_subtyping_refl)

lemma t_list_subtyping_append:
  assumes "t_list_subtyping ts1 ts2"
  shows "t_list_subtyping (ts1@ts) (ts2@ts)"
  using assms unfolding t_list_subtyping_def
  by (simp add: list.rel_refl list_all2_appendI t_subtyping_refl)

lemma t_list_subtyping_replace1:
  assumes "t_list_subtyping ts ts'"
          "t_list_subtyping (ts'@ts1) ts2"
  shows "t_list_subtyping (ts@ts1) ts2"
  using assms unfolding t_list_subtyping_def
  by (meson t_list_subtyping_append t_list_subtyping_def t_list_subtyping_trans)

lemma t_list_subtyping_replace2:
  assumes "t_list_subtyping ts ts'"
          "t_list_subtyping (ts1@ts') ts2"
  shows "t_list_subtyping (ts1@ts) ts2"
  using assms unfolding t_list_subtyping_def
  by (meson t_list_subtyping_prepend t_list_subtyping_def t_list_subtyping_trans)

lemma t_list_subtyping_not_bot_eq:
  assumes "t_list_subtyping ts ts'"
          "list_all (\<lambda> t. t \<noteq> T_bot) ts"
  shows "ts = ts'"
proof -
  have "list_all2 (\<lambda>t1 t2. t1 = t2) ts ts'"
    using assms
    unfolding t_list_subtyping_def t_subtyping_def
    by (auto simp add: list_all2_conv_all_nth list_all_length)
  then show ?thesis
    by (simp add: list.rel_eq)
qed

lemma t_list_subtyping_append_type:
  assumes "t_list_subtyping (ts1@ts) ts2"
          "list_all (\<lambda>t. t\<noteq>T_bot) ts"
        shows "\<exists> ts2'. t_list_subtyping ts1 ts2' \<and> ts2=ts2'@ts"
proof -
  obtain ts2' ts' where ts2'_def: "t_list_subtyping ts1 ts2'" "t_list_subtyping ts ts'" "ts2 = ts2'@ts'"
    using assms(1) t_list_subtyping_split1 by metis
  have "ts' = ts"
    using assms(2) ts2'_def(2) t_list_subtyping_not_bot_eq by auto
  then show ?thesis
    using ts2'_def(1) ts2'_def(3) by auto
qed

lemma t_list_subtyping_snoc_left1:
  assumes "t_list_subtyping (ts@[t]) ts'"
          "t \<noteq> T_bot"
        shows "\<exists> ts''. t_list_subtyping ts ts'' \<and> ts' = ts''@[t]"
  using assms t_list_subtyping_append_type by fastforce

lemma t_list_subtyping_snoc_right1:
  assumes "t_list_subtyping ts' (ts@[t])"
        shows "\<exists> ts'' t'. t_list_subtyping ts'' ts \<and> t_subtyping t' t \<and> ts' = ts''@[t']"
  using assms t_list_subtyping_split2[OF assms(1)] t_list_subtyping_def t_subtyping_def
  by (metis list_all2_Cons2 list_all2_Nil2)

lemma t_list_subtyping_snoc_left2:
  assumes "t_list_subtyping (ts@[t1,t2]) ts'"
          "t1 \<noteq> T_bot"
          "t2 \<noteq> T_bot"
  shows "\<exists> ts''. t_list_subtyping ts ts'' \<and> ts' = ts''@[t1,t2]"
  using assms t_list_subtyping_snoc_left1[of "ts@[t1]" t2 ts'] t_list_subtyping_snoc_left1[of "ts" t1]
  by fastforce

lemma t_list_subtyping_snoc_right2:
  assumes "t_list_subtyping ts' (ts@[t1,t2])"
        shows "\<exists> ts'' t1' t2'. t_list_subtyping ts'' ts \<and> t_list_subtyping [t1', t2'] [t1, t2] \<and> ts' = ts''@[t1', t2'] "
  using assms t_list_subtyping_split2[OF assms(1)] t_list_subtyping_def t_subtyping_def
        t_list_subtyping_snoc_right1[of ts' "ts@[t1]" t2] t_list_subtyping_snoc_right1[of _ _ t1]
  by fastforce

lemma t_list_subtyping_snoc_left3:
  assumes "t_list_subtyping (ts@[t1,t2,t3]) ts'"
          "t1 \<noteq> T_bot"
          "t2 \<noteq> T_bot"
          "t3 \<noteq> T_bot"
  shows "\<exists> ts''. t_list_subtyping ts ts'' \<and> ts' = ts''@[t1,t2,t3]"
  using assms t_list_subtyping_snoc_left1[of "ts@[t1,t2]" t3 ts' ] t_list_subtyping_snoc_left2[of "ts" t1 t2]
  by fastforce

lemma instr_subtyping_refl:
  shows "tf <ti: tf"
  unfolding instr_subtyping_def using t_list_subtyping_refl
  by blast

lemma instr_subtyping_trans:
  assumes "instr_subtyping tf1 tf2" "instr_subtyping tf2 tf3"
  shows "instr_subtyping tf1 tf3"
proof -
  thm instr_subtyping_def
  obtain ts_12 ts'_12 tf1_dom_sub_12 tf1_ran_sub_12 where defs12:
    "tf.dom tf2 = ts_12 @ tf1_dom_sub_12"
    "tf.ran tf2 = ts'_12 @ tf1_ran_sub_12"
    "t_list_subtyping ts_12 ts'_12"
    "t_list_subtyping tf1_dom_sub_12 (tf.dom tf1)"
    "t_list_subtyping (tf.ran tf1) tf1_ran_sub_12"
    using assms(1) unfolding instr_subtyping_def by auto
  obtain ts_23 ts'_23 tf1_dom_sub_23 tf1_ran_sub_23 where defs23:
    "tf.dom tf3 = ts_23 @ tf1_dom_sub_23"
    "tf.ran tf3 = ts'_23 @ tf1_ran_sub_23"
    "t_list_subtyping ts_23 ts'_23"
    "t_list_subtyping tf1_dom_sub_23 (tf.dom tf2)"
    "t_list_subtyping (tf.ran tf2) tf1_ran_sub_23"
    using assms(2) unfolding instr_subtyping_def by auto
  obtain tf1_ts_12 tf1_tf_dom_sub_12  where defs_split_12:
    "t_list_subtyping tf1_ts_12 ts_12"
    "t_list_subtyping  tf1_tf_dom_sub_12 tf1_dom_sub_12"  
    "tf1_ts_12@tf1_tf_dom_sub_12 = tf1_dom_sub_23"
    by (metis defs12(1) defs23(4) t_list_subtyping_split2)
  obtain tf1_ts'_12 tf1_tf_ran_sub_12 where  defs_split_23:
    "t_list_subtyping ts'_12 tf1_ts'_12"
    "t_list_subtyping tf1_ran_sub_12 tf1_tf_ran_sub_12"  
    "tf1_ran_sub_23 = tf1_ts'_12@tf1_tf_ran_sub_12"
    by (metis defs12(2) defs23(5) t_list_subtyping_split1)
  let ?ts = "ts_23@tf1_ts_12"
  let ?ts' = "ts'_23@tf1_ts'_12"
  let ?tf1_dom_sub = "tf1_tf_dom_sub_12"
  let ?tf1_ran_sub = "tf1_tf_ran_sub_12"
  have a: "tf.dom tf3 = ?ts @ ?tf1_dom_sub"
    by (simp add: defs_split_12(3) defs23(1))
  have b: "t_list_subtyping ?tf1_dom_sub (tf.dom tf1)"
    using defs12(4) defs_split_12(2) t_list_subtyping_trans by blast
  have c: "t_list_subtyping ?ts ?ts'"
    by (meson defs12(3) defs23(3) list_all2_appendI defs_split_12(1) defs_split_23(1) t_list_subtyping_def t_list_subtyping_trans)
  have d: "tf.ran tf3 = ?ts' @ ?tf1_ran_sub" using defs23(2) defs_split_23(3)
    by auto
  have e: "t_list_subtyping (tf.ran tf1) ?tf1_ran_sub"
    using defs12(5) defs_split_23(2) t_list_subtyping_trans by blast
  show ?thesis
    using a b c d e instr_subtyping_def by blast
qed

lemma instr_subtyping_comp:
  assumes "instr_subtyping (ts1 _> ts2) (ts1' _> ts2')"
          "instr_subtyping (ts2 _> ts3) (ts2' _> ts3')"
        shows "instr_subtyping (ts1 _> ts3) (ts1' _> ts3')"
  using t_list_subtyping_def t_list_subtyping_trans assms  unfolding instr_subtyping_def
  by (metis (mono_tags, lifting) append_eq_append_conv list_all2_lengthD tf.sel(1) tf.sel(2))

lemma instr_subtyping_empty_comp1:
  assumes "instr_subtyping ([] _> []) (ts1' _> ts2')"
          "instr_subtyping ([] _> ts3) (ts2' _> ts3')"
        shows "instr_subtyping ([] _> ts3) (ts1' _> ts3')"
  using assms(1) assms(2) instr_subtyping_comp by blast

lemma instr_subtyping_empty_comp2:
  assumes "instr_subtyping ([] _> []) (ts1' _> ts2')"
          "instr_subtyping (ts2 _> ts3) (ts2' _> ts3')"
        shows "instr_subtyping (ts2 _> ts3) (ts1' _> ts3')"
proof -
  have "t_list_subtyping ts1' ts2'" using assms(1) t_list_subtyping_def unfolding instr_subtyping_def
    by fastforce
  then have "instr_subtyping (ts2' _> ts3') (ts1' _> ts3')"
    unfolding instr_subtyping_def
    by (metis append_Nil t_list_subtyping_refl tf.sel(1) tf.sel(2))
  then show ?thesis using instr_subtyping_trans[OF  assms(2) ] by simp
qed

lemma instr_subtyping_empty_comp3:
  assumes "instr_subtyping ([] _> ts2) (ts1' _> ts2')"
          "instr_subtyping ([] _> []) (ts2' _> ts3')"
        shows "instr_subtyping ([] _> ts2) (ts1' _> ts3')"
proof -
  obtain ts_1 ts'_1 tf1_dom_sub_1 tf1_ran_sub_1 where defs1:
    "tf.dom (ts1' _> ts2') = ts_1 @ tf1_dom_sub_1" 
    "tf.ran (ts1' _> ts2') = ts'_1 @ tf1_ran_sub_1"
    "t_list_subtyping ts_1 ts'_1"
    "t_list_subtyping tf1_dom_sub_1 (tf.dom ([] _> ts2))"
    "t_list_subtyping (tf.ran ([] _> ts2)) tf1_ran_sub_1"
    using assms(1) unfolding instr_subtyping_def by blast
  then have defs1_props:
    "tf1_dom_sub_1 = []"
    "ts1' = ts_1"
    using t_list_subtyping_def  by auto
  
  obtain ts_2 ts'_2 tf1_dom_sub_2 tf1_ran_sub_2 where defs2:
    "tf.dom (ts2' _> ts3') = ts_2 @ tf1_dom_sub_2 "
    "tf.ran (ts2' _> ts3') = ts'_2 @ tf1_ran_sub_2"
    "t_list_subtyping ts_2 ts'_2"
    "t_list_subtyping tf1_dom_sub_2 (tf.dom ([] _> []))"
    "t_list_subtyping (tf.ran ([] _> [])) tf1_ran_sub_2"
    using assms(2) unfolding instr_subtyping_def by blast
  then have defs2_props:
    "tf1_dom_sub_2 = []"
    "tf1_ran_sub_2 = []"
    "ts2' = ts_2" "ts3' = ts'_2"
    using t_list_subtyping_def  by auto
  obtain ts'_1' tf1_ran_sub_1' where defs3:
    "ts3' = ts'_1'@ tf1_ran_sub_1'"
    "t_list_subtyping ts'_1 ts'_1'"
    "t_list_subtyping tf1_ran_sub_1 tf1_ran_sub_1'"
    by (metis defs1(2) defs2(3) defs2_props(3) defs2_props(4) t_list_subtyping_split1 tf.sel(2))
  let ?ts = "ts_1"
  let ?ts' = ts'_1'
  let ?tf1_dom_sub = "tf1_dom_sub_1"
  let ?tf1_ran_sub = "tf1_ran_sub_1'"
  have "tf.dom (ts1' _> ts3') = ?ts @ ?tf1_dom_sub "
    using defs1(1) defs1(4) t_list_subtyping_def by fastforce
  moreover have "tf.ran (ts1' _> ts3') = ?ts' @ ?tf1_ran_sub"
    by (simp add: defs3(1))
  moreover have "t_list_subtyping ?ts ?ts'"
    using defs1(3) defs3(2) t_list_subtyping_trans by blast
  moreover have "t_list_subtyping ?tf1_dom_sub (tf.dom ([] _> ts2))"
    using defs1(4) by blast
  moreover have "t_list_subtyping (tf.ran ([] _> ts2)) ?tf1_ran_sub"
    using defs1(5) defs3(3) t_list_subtyping_trans by blast
  ultimately show "instr_subtyping ([] _> ts2) (ts1' _> ts3')" unfolding instr_subtyping_def by blast
qed

lemma instr_subtyping_empty_comp4:
  assumes "instr_subtyping ([] _> []) (ts1' _> ts2')"
          "instr_subtyping ([] _> ts3) (ts2' _> ts3')"
  shows "instr_subtyping ([] _> ts3) (ts1' _> ts3')"
  using assms(1) assms(2) instr_subtyping_comp by blast

lemma instr_subtyping_concat:
  assumes "instr_subtyping ([] _> ts2) (ts1' _> ts2')"
          "instr_subtyping ([] _> ts3) (ts2' _> ts3')"
  shows "instr_subtyping ([] _> (ts2@ts3)) (ts1' _> ts3')"
proof -
  obtain  ts'_2 tf1_ran_sub_2 where defs1:
    "ts2' = ts'_2 @ tf1_ran_sub_2"
    "t_list_subtyping ts1' ts'_2"
    "t_list_subtyping ts2 tf1_ran_sub_2"
    using instr_subtyping_def
    using assms(1) t_list_subtyping_def by auto
  obtain  ts'_3 tf1_ran_sub_3 where defs2:
  "ts3' = ts'_3 @ tf1_ran_sub_3"
  "t_list_subtyping ts2' ts'_3"
  "t_list_subtyping ts3 tf1_ran_sub_3"
    using instr_subtyping_def
    using assms(2) t_list_subtyping_def by auto
  obtain ts'_2' tf1_ran_sub_2' where defs3:
    "t_list_subtyping ts'_2 ts'_2'"
    "t_list_subtyping tf1_ran_sub_2 tf1_ran_sub_2'"
    "ts'_3 = ts'_2'@tf1_ran_sub_2'"
    using t_list_subtyping_split1 defs1(1) defs2(2)
    by blast
  let ?ts = ts1'
  let ?tf1_dom_sub = "[]"
  let ?ts' = ts'_2'
  let ?tf1_ran_sub = "tf1_ran_sub_2'@tf1_ran_sub_3"
  have "tf.dom (ts1' _> ts3') = ?ts @ ?tf1_dom_sub"
    by simp
  moreover have "tf.ran (ts1' _> ts3') = ?ts' @ ?tf1_ran_sub"
    by (simp add: defs3 defs2(1))
  moreover have "t_list_subtyping ?ts ?ts'"
    using defs3(1) t_list_subtyping_trans defs1 by blast
  moreover have "t_list_subtyping ?tf1_dom_sub (tf.dom ([] _> ts2 @ ts3))"
    using t_list_subtyping_refl by auto
  moreover have "t_list_subtyping (tf.ran ([] _> ts2 @ ts3)) ?tf1_ran_sub"
    by (metis defs3(2) t_list_subtyping_append t_list_subtyping_replace2 t_list_subtyping_trans tf.sel(2) defs1(3) defs2(3))
  ultimately show ?thesis unfolding instr_subtyping_def by blast
qed


lemma instr_subtyping_concat_left:
  assumes "instr_subtyping (ts1 _> []) (ts1' _> ts2')"
          "instr_subtyping (ts2 _> []) (ts2' _> ts3')"
        shows "instr_subtyping ((ts2@ts1) _> []) (ts1' _> ts3')"
proof -
  obtain ts_1 tf1_dom_sub_1 where ts_1_def:
    "ts1'  = ts_1 @ tf1_dom_sub_1"
    "ts_1 <ts: ts2'"
    "tf1_dom_sub_1 <ts: ts1"
    using assms(1) unfolding instr_subtyping_def
    using t_list_subtyping_not_bot_eq by fastforce
  obtain ts_2 tf1_dom_sub_2 where ts_2_def:
     "ts2' = ts_2 @ tf1_dom_sub_2"
     "ts_2 <ts: ts3'"
     "tf1_dom_sub_2 <ts: ts2"
    using assms(2) unfolding instr_subtyping_def using t_list_subtyping_not_bot_eq by fastforce
  obtain "ts_2'" "tf1_dom_sub_2'" where ts_2'_def: "ts_1 = ts_2'@tf1_dom_sub_2'" "ts_2' <ts: ts_2" "tf1_dom_sub_2' <ts: tf1_dom_sub_2"
    using ts_1_def(2) ts_2_def(1)
    by (meson t_list_subtyping_split2)
  let ?ts = ts_2'
  let ?ts' = ts3'
  let ?tf1_dom_sub = "tf1_dom_sub_2'@tf1_dom_sub_1"
  let ?tf1_ran_sub = "[]"
  have "tf.dom (ts1' _> ts3') = ?ts @ ?tf1_dom_sub"
    by (simp add: ts_1_def(1) ts_2'_def(1))
  moreover have "tf.ran (ts1' _> ts3') = ?ts' @ ?tf1_ran_sub" by simp
  moreover have "?ts <ts: ?ts'"
    using t_list_subtyping_trans ts_2'_def(2) ts_2_def(2) by blast
  moreover have "?tf1_dom_sub <ts: tf.dom (ts2 @ ts1 _> [])"
    using t_list_subtyping_prepend t_list_subtyping_replace1 tf.sel(1) ts_1_def(3) ts_2'_def(3) ts_2_def(3) by metis
  moreover have "tf.ran (ts2 @ ts1 _> []) <ts: ?tf1_ran_sub"
    by (simp add: t_list_subtyping_refl)
  ultimately show ?thesis unfolding instr_subtyping_def by blast
qed


lemma t_list_subtyping_instr_subtyping_append:
  assumes "t_list_subtyping (dtf@dp) (rtf)"
          "instr_subtyping (dtf _> rtf) (ts _> ts')"
  shows "t_list_subtyping (ts@dp) (ts')"
proof -
  obtain tsa ts'a tf1_dom_sub tf1_ran_sub where defs:
       "ts = tsa @ tf1_dom_sub"
       "ts' = ts'a @ tf1_ran_sub"
       "t_list_subtyping tsa ts'a"
       "t_list_subtyping tf1_dom_sub dtf"
       "t_list_subtyping rtf tf1_ran_sub"
    using assms unfolding instr_subtyping_def by auto
  have "t_list_subtyping (tf1_dom_sub@dp) (rtf)" using defs(4) assms(1) t_list_subtyping_replace1 by simp
  then have "t_list_subtyping (tf1_dom_sub@dp) (tf1_ran_sub)" using t_list_subtyping_trans[OF _ defs(5)] by simp
  then have "t_list_subtyping (ts'a@(tf1_dom_sub@dp)) (ts'a@tf1_ran_sub)" 
    using t_list_subtyping_prepend by fastforce
  then show ?thesis using t_list_subtyping_replace1 defs(1,2,3) by auto
qed

lemma instr_subtyping_append_split1:
  assumes "([] _> ts) <ti: (ts' _> ts'@ts'')"
  shows "([] _> ts) <ti: ([] _> ts'')"
  using assms unfolding instr_subtyping_def
  using list_all2_lengthD t_list_subtyping_def by fastforce

lemma instr_subtyping_append_split2:
  assumes "(ts _> []) <ti: (ts'@ts'' _> ts')"
  shows "(ts _> []) <ti: (ts'' _> [])" 
  using assms unfolding instr_subtyping_def
    using t_list_subtyping_def
    by (metis append_Nil2 append_eq_append_conv append_eq_append_conv2 list_all2_lengthD tf.sel(1) tf.sel(2))

lemma instr_subtyping_split:
  assumes "instr_subtyping (ts1 _> ts3) (ts1' _> ts3')"
  shows "\<exists> ts2'. ((ts1 _> ts2) <ti: (ts1' _> ts2')) \<and> instr_subtyping (ts2 _> ts3) (ts2' _> ts3')"
  using assms unfolding instr_subtyping_def
  by (metis t_list_subtyping_refl tf.sel(1) tf.sel(2))

lemma instr_subtyping_split_empty1:
  assumes "([] _> ts) <ti: (ts1 _> ts2)"
  shows "\<exists> ts1' ts'. (([] _> ts) <ti: ([] _> ts')) \<and> ts2 = ts1'@ts' \<and> t_list_subtyping ts1 ts1'"
  using assms unfolding instr_subtyping_def
  using t_list_subtyping_def
  by (metis append_eq_append_conv2 list_all2_Nil2 self_append_conv tf.sel(1) tf.sel(2))

lemma instr_subtyping_split_empty2:
  assumes "(ts _> []) <ti: (ts1 _> ts2)"
  shows "\<exists> ts' ts2'. (ts _> []) <ti: (ts' _> []) \<and> ts1 = ts2'@ts' \<and> t_list_subtyping ts2' ts2 \<and> t_list_subtyping ts' ts"
  using assms unfolding instr_subtyping_def
  using t_list_subtyping_def
  by auto

lemma instr_subtyping_append1_type_eq:
  assumes "(ts1 _> ts2@[t1]) <ti: (ts1' _> ts2')"
          "(ts3@[t2] _> ts4) <ti: (ts2' _> ts3')"
          "t1 \<noteq> T_bot"
        shows "t1 = t2"
proof -
  have "(ts1 _> ts2@[t1]) <ti: (ts1' _> ts2')" using assms(1) by blast

  obtain ts2a ts3_dom where  "ts2' = ts2a@ts3_dom" "t_list_subtyping ts3_dom (ts3@[t2])"
    using assms(2) unfolding instr_subtyping_def by auto
  then obtain ts2''' t2' where ts'''_def: "ts2' = ts2'''@[t2']" "t_subtyping t2' t2" 
    using t_list_subtyping_snoc_right1
    by (metis append_assoc)
  obtain ts2'' where ts''_def: "ts2' = ts2''@[t1]"
    by (meson assms(1,3) instr_subtyping_split t_list_subtyping_instr_subtyping_append t_list_subtyping_refl t_list_subtyping_snoc_left1)
  show "t1 = t2" using ts''_def ts'''_def assms(3) t_subtyping_def by blast
qed

lemma instr_subtyping_append2_type_eq:
  assumes "(ts1 _> ts2@[t1,t2]) <ti: (ts1' _> ts2')"
          "(ts3@[t3,t4] _> ts4) <ti: (ts2' _> ts3')"
          "t1 \<noteq> T_bot"
          "t2 \<noteq> T_bot"
        shows "[t1, t2] = [t3, t4]"
proof -
  obtain ts2a ts3_dom where  "ts2' = ts2a@ts3_dom" "t_list_subtyping ts3_dom (ts3@[t3,t4])"
    using assms(2) unfolding instr_subtyping_def by auto
  then obtain ts2''' t34' where ts'''_def: "ts2' = ts2'''@t34'" "t_list_subtyping t34' [t3, t4]" 
    by (metis append.assoc t_list_subtyping_split2)
  obtain ts2'' where ts''_def: "ts2' = ts2''@[t1,t2]"
    using instr_subtyping_split assms(1)
    by (meson assms(3) assms(4) t_list_subtyping_instr_subtyping_append t_list_subtyping_refl t_list_subtyping_snoc_left2)
  then have "t_list_subtyping [t1,t2] [t3, t4]" using ts''_def ts'''_def
    by (simp add: list_all2_lengthD t_list_subtyping_def)
  then show "[t1, t2] = [t3, t4]" using assms(3,4) t_subtyping_def unfolding t_list_subtyping_def
    by fastforce
qed


lemma instr_subtyping_append_type_eq:
  assumes "(ts1 _> ts2@ts) <ti: (ts1' _> ts2')"
          "(ts3@ts' _> ts4) <ti: (ts2' _> ts3')"
          "list_all (\<lambda> t. t\<noteq>T_bot) ts"
          "length ts = length ts'"
        shows "ts=ts'"
proof -
  obtain ts2a ts3_dom where  "ts2' = ts2a@ts3_dom" "t_list_subtyping ts3_dom (ts3@ts')"
    using assms(2) unfolding instr_subtyping_def by auto
  then obtain ts2''' t34' where ts'''_def: "ts2' = ts2'''@t34'" "t_list_subtyping t34' ts'" 
    by (metis append.assoc t_list_subtyping_split2)
  obtain ts2'' where ts''_def: "ts2' = ts2''@ts"
    by (meson assms(1) assms(3) instr_subtyping_split t_list_subtyping_instr_subtyping_append t_list_subtyping_append_type t_list_subtyping_refl)
  then have "t_list_subtyping ts ts'" using ts''_def ts'''_def
    by (simp add: assms(4) list_all2_lengthD t_list_subtyping_def)
  then show "ts = ts'" using assms(3,4) t_subtyping_def
    using t_list_subtyping_not_bot_eq by blast
qed

lemma instr_subtyping_append_t_list_subtyping:
  assumes "(ts1 _> ts2@ts) <ti: (ts1' _> ts2')"
          "(ts3@ts' _> ts4) <ti: (ts2' _> ts3')"
          "length ts = length ts'"
        shows "t_list_subtyping ts ts'"
proof -
  obtain ts2a ts3_dom where  "ts2' = ts2a@ts3_dom" "t_list_subtyping ts3_dom (ts3@ts')"
    using assms(2) unfolding instr_subtyping_def by auto
  then obtain ts2''' ts''' where ts'''_def: "ts2' = ts2'''@ts'''" "t_list_subtyping ts''' ts'" 
    by (metis append.assoc t_list_subtyping_split2)
  obtain ts2'' ts'' where ts''_def: "ts2' = ts2''@ts''" "t_list_subtyping ts ts''"
    by (metis (no_types, lifting) append.assoc assms(1) instr_subtyping_def t_list_subtyping_split1 tf.sel(2))
  show "t_list_subtyping ts ts'" using ts''_def ts'''_def
    by (metis append_eq_append_conv assms(3) list_all2_lengthD t_list_subtyping_def t_list_subtyping_trans)
qed

lemma instr_subtyping_replace1:
  assumes "t_list_subtyping ts ts'"
          "(ts _> t2s) <ti: (t1s' _> t2s')"
        shows "(ts' _> t2s) <ti: (t1s' _> t2s')"
  by (metis (mono_tags, opaque_lifting) assms(1) assms(2) instr_subtyping_comp instr_subtyping_def instr_subtyping_refl instr_subtyping_trans self_append_conv2 t_list_subtyping_refl tf.sel(1) tf.sel(2))

lemma instr_subtyping_replace2:
  assumes "t_list_subtyping ts' ts"
          "(t1s _> ts) <ti: (t1s' _> t2s')"
        shows "(t1s _> ts') <ti: (t1s' _> t2s')"
  using assms(1) assms(2) instr_subtyping_refl
  by (metis (mono_tags, opaque_lifting) instr_subtyping_comp instr_subtyping_def instr_subtyping_trans self_append_conv2 t_list_subtyping_refl tf.sel(1) tf.sel(2))

lemma instr_subtyping_replace3:
  assumes "t_list_subtyping ts' ts"
          "(t1s _> t2s) <ti: (ts _> t2s')"
        shows "(t1s _> t2s) <ti: (ts' _> t2s')"
  using assms(1) assms(2) instr_subtyping_refl instr_subtyping_replace1 instr_subtyping_trans by blast

lemma instr_subtyping_replace4:
  assumes "t_list_subtyping ts ts'"
          "(t1s _> t2s) <ti: (t1s' _> ts)"
        shows "(t1s _> t2s) <ti: (t1s' _> ts')"
  using assms instr_subtyping_refl instr_subtyping_comp instr_subtyping_def instr_subtyping_trans
  by (metis (mono_tags, opaque_lifting) self_append_conv2 t_list_subtyping_refl tf.sel(1) tf.sel(2))


lemma instr_subtyping_drop_append:
  assumes "([] _> ts) <ti: (t1s' _> t2s')"
          "(t1s@ts _> t2s) <ti: (t2s' _> t3s')"
  shows "(t1s _> t2s) <ti: (t1s' _> t3s')"
proof -
  obtain t1s'' ts'' where ts''_def: "t2s' = t1s''@ts''" "t_list_subtyping ts ts''" "t_list_subtyping t1s' t1s''"
    using assms(1) instr_subtyping_def t_list_subtyping_replace2 by fastforce
  then have "(t1s@ts _> t2s) <ti: (t1s''@ts'' _> t3s')"
    using assms(2) by fastforce
  then have 1: "(t1s@ts _> t2s) <ti: (t1s''@ts _> t3s')"
  proof -
    have "\<forall>t ts. ts _> tf.ran t <ti: t \<or> \<not> t_list_subtyping (tf.dom t) ts"
      by (metis append.left_neutral instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
    then show ?thesis
      by (metis (no_types) \<open>t1s @ ts _> t2s <ti: t1s'' @ ts'' _> t3s'\<close> instr_subtyping_trans t_list_subtyping_refl t_list_subtyping_replace2 tf.sel(1) tf.sel(2) ts''_def(2))
  qed
  have 2: "(t1s _> t2s) <ti: (t1s'' _> t3s')"
  proof -
    obtain tsa ts'a tf1_dom_sub tf1_ran_sub where defs:
      "tf.dom (t1s'' @ ts _> t3s') = tsa @ tf1_dom_sub"
      "tf.ran (t1s'' @ ts _> t3s') = ts'a @ tf1_ran_sub"
      "t_list_subtyping tsa ts'a"
      "t_list_subtyping tf1_dom_sub (tf.dom (t1s @ ts _> t2s))"
      "t_list_subtyping (tf.ran (t1s @ ts _> t2s)) tf1_ran_sub"
      using instr_subtyping_def 1 by auto
    have 3: "t_list_subtyping tf1_dom_sub (t1s @ ts)" using defs(4) by fastforce
    obtain tf1_dom' tf1_dom'' where tf_dom_defs:
      "tf1_dom_sub = tf1_dom'@tf1_dom''"
      "t_list_subtyping tf1_dom' t1s"
      "t_list_subtyping tf1_dom'' ts" using defs(4) t_list_subtyping_split2[OF 3] by fastforce
    
    let ?ts = tsa
    let ?ts' = ts'a
    let ?tf1_dom_sub = tf1_dom'
    let ?tf1_ran_sub = tf1_ran_sub
    have "tf.dom (t1s'' _> t3s') = ?ts @ ?tf1_dom_sub"
    proof -
      have "length tf1_dom'' = length ts" using tf_dom_defs(3)
        using list_all2_lengthD t_list_subtyping_def by auto
      then show ?thesis using tf_dom_defs(1) defs(1)
        apply simp
        by (metis (full_types) append.assoc append_eq_append_conv)
    qed
    moreover
    have "tf.ran (t1s'' _> t3s') = ?ts' @ ?tf1_ran_sub" using defs by fastforce
    moreover
    have "t_list_subtyping ?ts ?ts'" using defs by fastforce
    moreover
    have "t_list_subtyping ?tf1_dom_sub (tf.dom (t1s _> t2s))" using tf_dom_defs by fastforce
    moreover
    have "t_list_subtyping (tf.ran (t1s _> t2s)) ?tf1_ran_sub" using defs(5) by fastforce
    ultimately show ?thesis unfolding instr_subtyping_def by blast
  qed
  then show ?thesis using  instr_subtyping_replace3[OF ts''_def(3)]
    by blast
qed

lemma t_list_subtyping_concat:
  assumes "xs <ts: ys" "xs' <ts: ys'"
  shows "xs@xs' <ts: ys@ys'"
  using assms(1) assms(2) t_list_subtyping_prepend t_list_subtyping_replace1 by metis

end