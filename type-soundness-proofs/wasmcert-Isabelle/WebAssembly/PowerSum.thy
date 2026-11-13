theory PowerSum
  imports Main
begin

section\<open>Lemmas about Sums of Powers divided by their Base\<close>

lemma power_sum_div_filter:
  fixes A :: "'a set" and b :: int
  assumes "card (Set.filter (\<lambda>n. f n = 0) A) \<le> 1" "finite A" "b > 1"
  shows "(\<Sum>n\<in>A. b ^ f n) div b = (\<Sum>n\<in>Set.filter (\<lambda>n. f n \<noteq> 0) A. b ^ f n) div b"
proof -
  have *: "(\<Sum>n\<in>A. b ^ f n) =
    (\<Sum>n\<in>Set.filter (\<lambda>n. f n \<noteq> 0) A. b ^ f n)
    + (\<Sum>n\<in>Set.filter (\<lambda>n. f n = 0) A. b ^ f n)"
    apply (subst sum.union_disjoint[of "Set.filter (\<lambda>n. f n \<noteq> 0) A" "Set.filter (\<lambda>n. f n = 0) A", THEN sym])
    using assms apply auto[3]
    apply (rule arg_cong[where f="sum (\<lambda>n. b ^ f n)"]) unfolding Set.filter_eq by auto
  hence "(\<Sum>n\<in>A. b ^ f n) div b =
    (\<Sum>n\<in>Set.filter (\<lambda>n. f n \<noteq> 0) A. b ^ f n) div b
    + (\<Sum>n\<in>Set.filter (\<lambda>n. f n = 0) A. b ^ f n) div b"
    apply (subst *)
    apply (rule div_plus_div_distrib_dvd_left)
    apply (rule dvd_sum)
    by simp
  moreover have "(\<Sum>n\<in>Set.filter (\<lambda>n. f n = 0) A. b ^ f n) div b = 0"
  proof (cases "Set.filter (\<lambda>n. f n = 0) A = {}")
    case False
    hence "0 < card (Set.filter (\<lambda>n. f n = 0) A)"
      apply (subst card_gt_0_iff) using \<open>finite A\<close> by simp
    hence "is_singleton (Set.filter (\<lambda>n. f n = 0) A)"
      unfolding is_singleton_def apply (subst card_1_singleton_iff[THEN sym])
      using \<open>card _ \<le> 1\<close> using False by simp
    then obtain x where x: "Set.filter (\<lambda>n. f n = 0) A = {x}" by (rule is_singletonE)
    hence 0: "f x = 0" by auto
    then show ?thesis unfolding x using \<open>b > 1\<close> by simp
  qed (metis div_0 sum.empty)
  ultimately show ?thesis by presburger
qed

lemma power_sum_div_n0:
  fixes A :: "'a set" and b :: int
  assumes n0: "\<And>n. n \<in> A \<Longrightarrow> f n \<noteq> 0" and "b \<noteq> 0"
  shows "(\<Sum>n\<in>A. b ^ f n) div b = (\<Sum>n\<in>A. b ^ (f n - 1))"
proof -
  have *: "(\<Sum>n\<in>A. b ^ f n) = b * (\<Sum>n\<in>A. b ^ (f n - 1))"
    apply (subst sum_distrib_left)
    apply (subst power_eq_if)
    apply (rule sum.cong)
    apply standard
    using n0 by fastforce
  show ?thesis unfolding * using \<open>b \<noteq> 0\<close> by simp
qed

lemma power_sum_div:
  fixes A :: "'a set" and b :: int
  assumes "card (Set.filter (\<lambda>n. f n = 0) A) \<le> 1" "finite A" "b > 1"
  shows "(\<Sum>n\<in>A. b ^ f n) div b = (\<Sum>n\<in>Set.filter (\<lambda>n. f n \<noteq> 0) A. b ^ (f n - 1))"
  apply (subst power_sum_div_filter[OF assms])
  apply (rule power_sum_div_n0)
  using \<open>b > 1\<close> by auto

lemma "(\<Sum>n = 0..<length X. if X ! n then 2 ^ n else 0) div (2::int)
     = (\<Sum>n = 1..<length X. if X ! n then 2 ^ (n-1) else 0)"
proof -
  let ?A = "Set.filter ((!) X) {0..<length X}"
  let ?b = 2
  let ?f = "\<lambda>x. x"
  have s: "{a \<in> {a \<in> {0..<length X}. X ! a}. ?f a \<noteq> 0} = {a \<in> {1..<length X}. X ! a}" by auto
  have "(\<Sum>n = 0..<length X. if X ! n then 2 ^ n else 0) div (2::int) =
    (\<Sum>n\<in>?A. ?b ^ (?f n)) div 2"
    unfolding Set.filter_eq by (subst sum.inter_filter[symmetric]) auto
  also have "\<dots> = (\<Sum>n\<in>Set.filter (\<lambda>n. ?f n \<noteq> 0) ?A. ?b ^ (?f n - 1))"
    apply (rule power_sum_div)
    apply (rule order.trans[where b="card (Set.filter (\<lambda>n. n = 0) {0..<length X})"])
    apply (rule card_mono)
    by (auto simp: card_le_Suc0_iff_eq)
  also have "\<dots> = (\<Sum>n = 1..<length X. if X ! n then 2 ^ (n-1) else 0)"
    unfolding Set.filter_eq
    apply (subst sum.inter_filter[symmetric])
    unfolding s by auto
  finally show ?thesis .
qed

end
