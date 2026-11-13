section\<open>Numeric WebAssembly Types\<close>

theory Wasm_Type_Abs imports
  Main
  "HOL-Library.Type_Length"
  "Word_Lib.Reversed_Bit_Lists"
  HOL.Rat
  PowerSum
begin

class wasm_base = zero

subsection\<open>Integer\<close>

context len
begin

definition ibits :: "'a itself \<Rightarrow> int \<Rightarrow> bool list" where
  "ibits N i \<equiv> THE l.
    length l = LENGTH('a) \<and>
    i = (\<Sum>n \<in> {0..<LENGTH('a)}. (2 ^ (LENGTH('a) - n - 1)) * (if l ! n then 1 else 0))"

lemma "c dvd a \<Longrightarrow> (\<not> c dvd b) \<Longrightarrow> b div c = 0 \<Longrightarrow> ((a::int) + b) div c = (a::int) div c"
  using div_plus_div_distrib_dvd_left
  by (simp add: div_plus_div_distrib_dvd_left)

lemma ibits_l:
  assumes "0 \<le> i" "i < 2 ^ LENGTH('a)"
  shows "length l = LENGTH('a)
        \<and> i = (\<Sum>n = 0..<LENGTH('a). if l ! n then 2 ^ (LENGTH('a) - n - 1) else 0)
     \<longleftrightarrow> l = bin_to_bl LENGTH('a) i"
proof -
  have gen: "
    0 \<le> i \<Longrightarrow> i < 2 ^ N \<Longrightarrow>
      length l = N
          \<and> i = (\<Sum>n = 0..<N. if l ! n then 2 ^ (N - n - 1) else 0)
       \<longleftrightarrow> l = bin_to_bl N i" for N
  proof (induction N arbitrary: i l)
    case 0
    then show ?case by simp
  next
    case (Suc N)
    have IH: "(length (butlast l) = N \<and> i div 2 =
                  (\<Sum>n = 0..<N. if butlast l ! n then 2 ^ (N - n - 1) else 0))
          \<longleftrightarrow> (butlast l = bin_to_bl N (i div 2))"
      apply (rule Suc.IH[where l="butlast l" and i="i div 2"])
      using Suc.prems by auto

    have sumdiv: "length (butlast l) = N \<Longrightarrow>
        (\<Sum>n = 0..<Suc N. if l ! n then 2 ^ (Suc N - n - 1) else (0::int)) div 2
        = (\<Sum>n = 0..<N. if butlast l ! n then 2 ^ (N - n - 1) else 0)"
    proof -
      assume "length (butlast l) = N"
      let ?h = "\<lambda>n. n - 1"
      have l: "Set.filter (\<lambda>n. Suc N - n - 1 \<noteq> 0) {x \<in> {0..<Suc N}. l ! x} = {x \<in> {0..<N}. l ! x}"
        unfolding Set.filter_eq by auto
      have "(\<Sum>n = 0..<Suc N. if l ! n then 2 ^ (Suc N - n - 1) else (0::int)) div 2 =
        (\<Sum>n = 0..<N. if l ! n then 2 ^ (N - n - 1) else 0)"
        apply (subst sum.inter_filter
            [where P="(!) l", THEN sym, OF finite_atLeastLessThan[of 0 "Suc N"]])
        apply (subst sum.inter_filter
            [where P="\<lambda>n. l ! n", THEN sym, OF finite_atLeastLessThan[of 0 N]])
        apply (subst power_sum_div)
          subgoal
            apply (rule ord_le_eq_trans[where b="card {N}"])
            by (rule card_mono) auto
          apply auto[2]
          apply (subst l) by simp
      also have "\<dots> = (\<Sum>n = 0..<N. if butlast l ! n then 2 ^ (N - n - 1) else 0)"
      proof -
        have "n \<in> {0..<N} \<Longrightarrow> butlast l ! n = l ! n" for n
          apply (rule nth_butlast)
          using \<open>length (butlast l) = N\<close> atLeastLessThan_iff by blast
        thus ?thesis by simp
      qed
      finally show ?thesis .
    qed

    show ?case
      unfolding bin_to_bl_def apply (subst bin_to_bl_aux.simps)
      apply (subst bin_to_bl_aux_alt)
    proof (rule iffI, goal_cases)
      case 1
      hence "length (butlast l) = N" by simp
      moreover have "i div 2 = (\<Sum>n = 0..<N. if butlast l ! n then 2 ^ (N - n - 1) else 0)"
        using sumdiv 1 by fastforce
      ultimately have butlast: "butlast l = bin_to_bl N (i div 2)" using IH by blast
      have last: "last l = odd i"
      proof -
        have set: "{a \<in> {0..<Suc N}. odd (if l ! a then 2 ^ (Suc N - a - 1) else 0)} =
          (if l ! N then {N} else {})"
        proof -
          have "a < Suc N \<Longrightarrow> a \<noteq> N \<Longrightarrow> \<not> odd (if l ! a then 2 ^ (Suc N - a - 1) else 0)" for a
            by simp
          hence "{a \<in> {0..<Suc N}. odd (if l ! a then 2 ^ (Suc N - a - 1) else 0)} =
            {a \<in> {N}. odd (if l ! a then 2 ^ (Suc N - a - 1) else 0)}" by auto
          thus ?thesis apply (cases "l ! N") apply force by force
        qed
        hence "(odd (card {a \<in> {0..<Suc N}. odd (if l ! a then 2 ^ (Suc N - a - 1) else 0)})) =
          last l"
          apply (subst last_conv_nth)
          unfolding set using conjunct1[OF 1] by auto
        then show ?thesis
          apply (subst conjunct2[OF 1])
          apply (subst even_sum_iff)
           apply simp
          by fastforce
      qed
      show ?case
        apply (subst butlast[THEN sym])
        apply (subst last[THEN sym])
        apply (rule append_butlast_last_id[THEN sym])
        using 1 by force
    next
      case 2
      hence
        "length (butlast l) = N"
        "i div 2 = (\<Sum>n = 0..<N. if butlast l ! n then 2 ^ (N - n - 1) else 0)"
        using IH by auto
      from 2 have len: "length l = Suc N" using size_bin_to_bl by fastforce
      have "i = (i div 2) * 2 + (if odd i then 1 else 0)" by presburger
      also have "\<dots> = (\<Sum>n = 0..<N. if l ! n then 2 ^ (Suc N - n - 1) else 0)
                      + (if odd i then 1 else 0)"
        apply (subst \<open>i div 2 = _\<close>)
        apply (subst sum_distrib_right)
        apply (subst if_distrib[where f="\<lambda>x. x * 2"])
        apply (subst power_Suc2[THEN sym])
        apply (subst mult_zero_left)
        apply (subst sum.cong[of
            "{0..<N}" "{0..<N}"
            "\<lambda>n. if butlast l ! n then 2 ^ Suc (N - n - 1) else 0"
            "\<lambda>n. if l ! n then 2 ^ (Suc N - n - 1) else 0"])
        by (auto simp: Suc_diff_Suc len nth_butlast)
      also have "\<dots> = (\<Sum>n = 0..<N. if l ! n then 2 ^ (Suc N - n - 1) else 0)
                      + (if l ! N then 1 else 0)"
      proof -
        have "l ! length (bin_to_bl N (i div 2)) = odd i" unfolding 2 by simp
        thus ?thesis using size_bin_to_bl by auto
      qed
      also have "\<dots> = (\<Sum>n = 0..<Suc N. if l ! n then 2 ^ (Suc N - n - 1) else 0)" by simp
      finally show ?case using len by blast
    qed
  qed
  show ?thesis unfolding bin_to_bl_def using gen[where N="LENGTH('a)", OF assms] by simp
qed

lemma ibits:
  assumes "0 \<le> i" "i < 2 ^ LENGTH('a)"
  shows "ibits N i = bin_to_bl LENGTH('a) i"
  unfolding ibits_def sum_distrib_right if_distrib mult_zero_right mult_1_right
  apply (rule the_equality)
  using ibits_l[OF assms] by auto

definition ibits_inv :: "'a itself \<Rightarrow> bool list \<Rightarrow> int" where
  "ibits_inv N \<equiv> the_inv_into {0 ..< 2^LENGTH('a)} (ibits N)"

lemma ibits_inv:
  assumes "length l = LENGTH('a)"
  shows "ibits_inv N l = bl_to_bin l"
proof -
  have ge0: "0 \<le> bl_to_bin l" using bl_to_bin_ge0 .
  have lt2p: "bl_to_bin l < 2 ^ LENGTH('a)"
    unfolding assms[THEN sym] using bl_to_bin_lt2p .
  show ?thesis
  unfolding ibits_inv_def
  proof (rule the_inv_into_f_eq, goal_cases)
    case 1
    then show ?case
      apply (rule inj_onI)
      apply (subst (asm) ibits)
      apply auto[2]
      apply (subst (asm) ibits)
      apply auto[2]
      by (metis atLeastLessThan_iff bin_bl_bin take_bit_int_eq_self)
  next
    case 2
    then show ?case
      apply (subst ibits)
      using ge0 lt2p apply auto[2]
      unfolding assms[THEN sym]
      by (rule bl_bin_bl)
  next
    case 3
    then show ?case using ge0 lt2p by simp
  qed
qed


lemma half_power:
  "2 ^ LENGTH('a) = 2 * 2 ^ (LENGTH('a) - 1)"
  using power_Suc[of 2 "LENGTH('a) - 1"] by simp

definition signed :: "'a itself \<Rightarrow> int \<Rightarrow> int" where
  "signed _ i \<equiv>
    if 0 \<le> i \<and> i < (2^(LENGTH('a)-1)) then i
    else if 2^(LENGTH('a)-1) \<le> i \<and> i < 2^LENGTH('a) then i - (2^LENGTH('a))
    else 0"

definition signed_inv :: "'a itself \<Rightarrow> int \<Rightarrow> int" where
  "signed_inv N \<equiv> the_inv_into {0 ..< 2^LENGTH('a)} (signed N)"

lemma signed_inj: "inj_on (signed (N::'a itself)) {0 ..< 2^LENGTH('a)}"
proof (rule inj_onI, goal_cases)
  case (1 x y)
  thus ?case unfolding signed_def
  apply (cases "x < (2^(LENGTH('a)-1))")
    subgoal
      apply (cases "y < (2^(LENGTH('a)-1))")
      using atLeastLessThan_iff by simp_all
    apply (cases "y < (2^(LENGTH('a)-1))")
    using atLeastLessThan_iff by simp_all
qed

lemma signed_inv_id:
  assumes "0 \<le> y" "y < 2 ^ (LENGTH('a) - 1)"
  shows "signed N y = y"
  unfolding signed_def half_power using assms by simp

lemma signed_inv_neg:
  assumes "- (2 ^ (LENGTH('a) - 1)) \<le> y" "y < 0"
  shows "signed N (y + (2 ^ LENGTH('a))) = y"
proof -
  let ?x = "y + (2 ^ LENGTH('a))"
  have "(2^(LENGTH('a)-1)) \<le> ?x " using assms(1) unfolding half_power by simp
  moreover have "2^(LENGTH('a)-1) \<le> ?x \<and> ?x < 2^LENGTH('a)"
    using assms(2) calculation by force
  ultimately show ?thesis unfolding signed_def by simp
qed

lemma signed_image: "signed N ` {0 ..< 2^LENGTH('a)} = {-(2^(LENGTH('a)-1)) ..< 2^(LENGTH('a)-1)}"
unfolding image_def proof (intro Set.equalityI Set.subsetI, goal_cases)
  case (1 y)
  then obtain x where x: "x\<in>{0..<2 ^ LENGTH('a)}" "y = signed N x" by blast
  hence xb: "0 \<le> x" "x < 2 ^ LENGTH('a)" by auto
  {
    assume nx: "\<not>x < 2 ^ (LENGTH('a) - 1)"
    hence "2 ^ (LENGTH('a) - 1) \<le> x \<and> x < 2 ^ LENGTH('a)" using xb(2) by fastforce
    hence signed: "signed N x = x - 2 ^ LENGTH('a)" unfolding signed_def using nx by simp
    have "- (2 ^ (LENGTH('a) - 1)) \<le> signed N x"
    proof -
      have "0 \<le> x - 2 * (2 ^ (LENGTH('a) - 1)) + (2 ^ (LENGTH('a) - 1))"
        using nx by linarith
      hence "0 \<le> x - 2 ^ LENGTH('a) + (2 ^ (LENGTH('a) - 1))"
        unfolding half_power .
      hence "- (2 ^ (LENGTH('a) - 1)) \<le> x - 2 ^ LENGTH('a)" by simp
      thus ?thesis by (subst signed)
    qed
    moreover from nx have "signed N x < 2 ^ (LENGTH('a) - 1)"
      using calculation signed xb(2) by force
    ultimately have "signed N x \<in> {- (2 ^ (LENGTH('a) - 1))..<2 ^ (LENGTH('a) - 1)}" by simp
  }
  then show ?case unfolding x(2) signed_def using x(1)
    by (cases "x < 2 ^ (LENGTH('a) - 1)") auto
next
  case (2 y)
  show ?case
  proof (cases "0 \<le> y")
    case True
    have "signed N y = y"
      apply (rule signed_inv_id[OF True])
      using 2 by auto
    moreover have "y < 2 ^ LENGTH('a)" unfolding half_power using "2" by force
    ultimately show ?thesis using True by force
  next
    case False
    have eq: "signed N (y + (2 ^ LENGTH('a))) = y"
      apply (rule signed_inv_neg)
      subgoal using "2" atLeastLessThan_iff by blast
      using False by simp
    have lt: "y + (2 ^ LENGTH('a)) < 2 ^ LENGTH('a)" unfolding half_power using False by auto
    have ge: "0 \<le> y + 2 ^ LENGTH('a)" unfolding half_power using "2" by auto
    show ?thesis
      apply (intro CollectI bexI[where x="y + 2 ^ LENGTH('a)"])
      subgoal using eq[THEN sym] .
      unfolding atLeastLessThan_iff
      using lt ge by blast
  qed
qed

lemma signed_bij:
  "bij_betw (signed N) {0 ..< 2^LENGTH('a)} {-(2^(LENGTH('a)-1)) ..< 2^(LENGTH('a)-1)}"
  by (rule bij_betw_imageI[OF signed_inj signed_image])

lemma signed_inv:
  assumes "- (2^(LENGTH('a)-1)) \<le> i" "i < 2^(LENGTH('a)-1)"
  shows "signed_inv N i = (if 0 \<le> i then i else i + (2^LENGTH('a)))"
proof (cases "0 \<le> i")
  case True
  note val = signed_inv_id[OF True assms(2)]
  show ?thesis unfolding signed_inv_def the_inv_into_def
  proof (rule the_equality, goal_cases)
    case 1
    then show ?case using val unfolding half_power using assms(2) True by auto
  next
    case (2 y)
    hence other: "signed N y = signed N i" using val by simp
    show ?case using inj_onD[OF signed_inj other 2[THEN conjunct1]]
      unfolding half_power using True assms(2) by auto
  qed
next
  case False
  hence False: "i < 0" by simp
  note val = signed_inv_neg[OF assms(1) False]
  show ?thesis unfolding signed_inv_def the_inv_into_def
  proof (rule the_equality, goal_cases)
    case 1
    then show ?case using val unfolding half_power using assms(1) False by auto
  next
    case (2 y)
    hence other: "signed N y = signed N (i + 2 ^ LENGTH('a))" using val by simp
    show ?case using inj_onD[OF signed_inj other 2[THEN conjunct1]]
      unfolding half_power using False assms(1) by auto
  qed
qed

lemma signed_inv_nneg:
  assumes "- (2^(LENGTH('a)-1)) \<le> i" "i < 2^(LENGTH('a)-1)"
  shows "0 \<le> signed_inv N i"
  using signed_inv[OF assms, unfolded half_power]
  apply (cases "0 \<le> i")
  apply presburger
  using assms(1) by force

end

class wasm_int_ops = wasm_base + len +
  fixes int_clz :: "'a \<Rightarrow> 'a"
  fixes int_ctz :: "'a \<Rightarrow> 'a"
  fixes int_popcnt :: "'a \<Rightarrow> 'a"
  fixes int_add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_div_u :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes int_div_s :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes int_rem_u :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes int_rem_s :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes int_and :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_or :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_shl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_shr_u :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_shr_s :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_rotl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_rotr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_eqz :: "'a \<Rightarrow> bool"
  fixes int_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_lt_u :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_lt_s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_gt_u :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_gt_s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_le_u :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_le_s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_ge_u :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_ge_s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_of_nat :: "nat \<Rightarrow> 'a"
  fixes nat_of_int :: "'a \<Rightarrow> nat"
begin
  abbreviation (input)
  int_ne where
    "int_ne x y \<equiv> \<not> (int_eq x y)"

  abbreviation abs_int :: "'a \<Rightarrow> int"
    where "abs_int a \<equiv> int (nat_of_int a)"

  abbreviation rep_int :: "int \<Rightarrow> 'a"
    where "rep_int a \<equiv> int_of_nat (nat a)"

  abbreviation abs_int_bits :: "'a \<Rightarrow> bool list"
    where "abs_int_bits a \<equiv> ibits TYPE('a) (abs_int a)"

  abbreviation rep_int_bits :: "bool list \<Rightarrow> 'a"
    where "rep_int_bits a \<equiv> rep_int (ibits_inv TYPE('a) a)"

  abbreviation abs_int_s :: "'a \<Rightarrow> int"
    where "abs_int_s a \<equiv> signed TYPE('a) (abs_int a)"

  abbreviation rep_int_s :: "int \<Rightarrow> 'a"
    where "rep_int_s a \<equiv> rep_int (signed_inv TYPE('a) a)"
end

definition trunc :: "rat \<Rightarrow> int" where
  "trunc q \<equiv>
    if 0 \<le> q
    then int (THE i::nat. q - 1 < rat_of_nat i \<and> rat_of_nat i \<le> q)
    else - int (THE i::nat. \<bar>q\<bar> - 1 < rat_of_nat i \<and> rat_of_nat i \<le> \<bar>q\<bar>)"

lemma trunc_exists1:
  assumes "0 \<le> q"
  shows "\<exists>!i. q - 1 < rat_of_nat i \<and> rat_of_nat i \<le> q"
proof -
  let ?F = "\<lambda>z. rat_of_int z \<le> q \<and> q < rat_of_int (z + 1)"
  let ?T = "\<lambda>i. q - 1 < rat_of_nat i \<and> rat_of_nat i \<le> q"
  obtain z where z: "?F z" "\<And>z'. ?F z' \<Longrightarrow> ?F z" using floor_exists1[of q] ..
  hence "q - 1 < rat_of_int z" by linarith
  moreover have "rat_of_int z \<le> q" using z(1) by blast
  moreover have "z \<ge> 0" using assms z(1) by linarith
  ultimately have "?T (nat z)" "\<And>i'. ?T i' \<Longrightarrow> i' = (nat z)" using z by auto
  thus ?thesis by blast
qed

lemma trunc: "trunc q = (if 0 \<le> q then \<lfloor>q\<rfloor> else -\<lfloor>-q\<rfloor>)"
proof -
  {
    fix q :: rat assume q: "0 \<le> q"
    have "(THE i::nat. q - 1 < rat_of_nat i \<and> rat_of_nat i \<le> q) = nat \<lfloor>q\<rfloor>"
      apply (rule the1_equality[OF trunc_exists1[OF q]])
      using q floor_less_cancel by force
  }
  thus ?thesis unfolding trunc_def by auto
qed

class wasm_int = wasm_int_ops +
  assumes zero: "nat_of_int (0::'a) = 0"
  assumes add: "int_add (i\<^sub>1::'a) i\<^sub>2 =
    rep_int ((abs_int i\<^sub>1 + abs_int i\<^sub>2) mod (2^LENGTH('a)))"
  assumes sub: "int_sub (i\<^sub>1::'a) i\<^sub>2 =
    rep_int ((abs_int i\<^sub>1 - abs_int i\<^sub>2 + (2^LENGTH('a))) mod (2^LENGTH('a)))"
  assumes mul: "int_mul (i\<^sub>1::'a) i\<^sub>2 =
    rep_int ((abs_int i\<^sub>1 * abs_int i\<^sub>2) mod (2^LENGTH('a)))"
  assumes div_u_0: "i\<^sub>2 = 0 \<Longrightarrow> int_div_u (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes div_u: "i\<^sub>2 \<noteq> 0 \<Longrightarrow> int_div_u (i\<^sub>1::'a) i\<^sub>2 =
    Some (rep_int (trunc (of_int (abs_int i\<^sub>1) / of_int (abs_int i\<^sub>2))))"
  assumes div_s_0: "i\<^sub>2 = 0 \<Longrightarrow> int_div_s (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes div_s_nrep:
    "i\<^sub>2 \<noteq> 0
    \<Longrightarrow> rat_of_int (abs_int_s i\<^sub>1) / of_int (abs_int_s i\<^sub>2) = 2^(LENGTH('a)-1)
    \<Longrightarrow> int_div_s (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes div_s:
    "i\<^sub>2 \<noteq> 0
    \<Longrightarrow> rat_of_int (abs_int_s i\<^sub>1) / of_int (abs_int_s i\<^sub>2) \<noteq> 2^(LENGTH('a)-1)
    \<Longrightarrow> int_div_s (i\<^sub>1::'a) i\<^sub>2 =
            Some (rep_int_s (trunc (of_int (abs_int_s i\<^sub>1) / of_int (abs_int_s i\<^sub>2))))"
  assumes rem_u_0: "i\<^sub>2 = 0 \<Longrightarrow> int_rem_u (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes rem_u: "i\<^sub>2 \<noteq> 0 \<Longrightarrow> int_rem_u (i\<^sub>1::'a) i\<^sub>2 =
    Some (rep_int (abs_int i\<^sub>1 - abs_int i\<^sub>2 * trunc (of_int (abs_int i\<^sub>1) / of_int (abs_int i\<^sub>2))))"
  assumes rem_s_0: "i\<^sub>2 = 0 \<Longrightarrow> int_rem_s (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes rem_s: "i\<^sub>2 \<noteq> 0 \<Longrightarrow> int_rem_s (i\<^sub>1::'a) i\<^sub>2 = Some (rep_int_s (
      abs_int_s i\<^sub>1 - abs_int_s i\<^sub>2 * trunc (of_int (abs_int_s i\<^sub>1) / of_int (abs_int_s i\<^sub>2))))"
  assumes iand: "int_and i\<^sub>1 i\<^sub>2 = rep_int_bits (map2 (\<and>) (abs_int_bits i\<^sub>1) (abs_int_bits i\<^sub>2))"
  assumes ior: "int_or i\<^sub>1 i\<^sub>2 = rep_int_bits (map2 (\<or>) (abs_int_bits i\<^sub>1) (abs_int_bits i\<^sub>2))"
  assumes ixor: "int_xor i\<^sub>1 i\<^sub>2 = rep_int_bits (map2 (\<noteq>) (abs_int_bits i\<^sub>1) (abs_int_bits i\<^sub>2))"
  assumes shl:
    "abs_int_bits i\<^sub>1 = d\<^sub>1 @ d\<^sub>2
    \<Longrightarrow> int k = abs_int i\<^sub>2 mod int (LENGTH('a))
    \<Longrightarrow> length d\<^sub>1 = k
    \<Longrightarrow> length d\<^sub>2 = (LENGTH('a) - k)
    \<Longrightarrow> int_shl i\<^sub>1 i\<^sub>2 = rep_int_bits (d\<^sub>2 @ replicate k False)"
  assumes shr_u:
    "abs_int_bits i\<^sub>1 = d\<^sub>1 @ d\<^sub>2
    \<Longrightarrow> int k = abs_int i\<^sub>2 mod int (LENGTH('a))
    \<Longrightarrow> length d\<^sub>1 = (LENGTH('a) - k)
    \<Longrightarrow> length d\<^sub>2 = k
    \<Longrightarrow> int_shr_u i\<^sub>1 i\<^sub>2 = rep_int_bits (replicate k False @ d\<^sub>1)"
  assumes shr_s:
    "abs_int_bits i\<^sub>1 = d\<^sub>0 # d\<^sub>1 @ d\<^sub>2
    \<Longrightarrow> int k = abs_int i\<^sub>2 mod int (LENGTH('a))
    \<Longrightarrow> length d\<^sub>1 = (LENGTH('a) - k - 1)
    \<Longrightarrow> length d\<^sub>2 = k
    \<Longrightarrow> int_shr_s i\<^sub>1 i\<^sub>2 = rep_int_bits (replicate (k + 1) d\<^sub>0 @ d\<^sub>1)"
  assumes rotl:
    "abs_int_bits i\<^sub>1 = d\<^sub>1 @ d\<^sub>2
    \<Longrightarrow> int k = abs_int i\<^sub>2 mod int (LENGTH('a))
    \<Longrightarrow> length d\<^sub>1 = k
    \<Longrightarrow> length d\<^sub>2 = (LENGTH('a) - k)
    \<Longrightarrow> int_rotl i\<^sub>1 i\<^sub>2 = rep_int_bits (d\<^sub>2 @ d\<^sub>1)"
  assumes rotr:
    "abs_int_bits i\<^sub>1 = d\<^sub>1 @ d\<^sub>2
    \<Longrightarrow> int k = abs_int i\<^sub>2 mod int (LENGTH('a))
    \<Longrightarrow> length d\<^sub>1 = (LENGTH('a) - k)
    \<Longrightarrow> length d\<^sub>2 = k
    \<Longrightarrow> int_rotr i\<^sub>1 i\<^sub>2 = rep_int_bits (d\<^sub>2 @ d\<^sub>1)"
  assumes clz_0: "abs_int_bits i\<^sub>1 = replicate k False \<Longrightarrow> int_clz i\<^sub>1 = int_of_nat k"
  assumes clz_1: "abs_int_bits i\<^sub>1 = replicate k False @ True # d \<Longrightarrow> int_clz i\<^sub>1 = int_of_nat k"
  assumes ctz_0: "abs_int_bits i\<^sub>1 = replicate k False \<Longrightarrow> int_ctz i\<^sub>1 = int_of_nat k"
  assumes ctz_1: "abs_int_bits i\<^sub>1 = d @ True # replicate k False \<Longrightarrow> int_ctz i\<^sub>1 = int_of_nat k"
  assumes popcnt:
    "abs_int_bits i\<^sub>1 = concat bls @ replicate (LENGTH('a) - length (concat bls)) False
    \<Longrightarrow> length bls = k
    \<Longrightarrow> (\<And>bl. bl \<in> set bls \<Longrightarrow> bl = replicate (length bl - 1) False @ [True])
    \<Longrightarrow> int_popcnt i\<^sub>1 = int_of_nat k"
  assumes ieqz: "int_eqz i\<^sub>1 \<longleftrightarrow> abs_int i\<^sub>1 = 0"
  assumes ieq: "int_eq i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int i\<^sub>1 = abs_int i\<^sub>2"
  assumes ilt_u: "int_lt_u i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int i\<^sub>1 < abs_int i\<^sub>2"
  assumes ilt_s: "int_lt_s i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int_s i\<^sub>1 < abs_int_s i\<^sub>2"
  assumes igt_u: "int_gt_u i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int i\<^sub>1 > abs_int i\<^sub>2"
  assumes igt_s: "int_gt_s i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int_s i\<^sub>1 > abs_int_s i\<^sub>2"
  assumes ile_u: "int_le_u i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int i\<^sub>1 \<le> abs_int i\<^sub>2"
  assumes ile_s: "int_le_s i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int_s i\<^sub>1 \<le> abs_int_s i\<^sub>2"
  assumes ige_u: "int_ge_u i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int i\<^sub>1 \<ge> abs_int i\<^sub>2"
  assumes ige_s: "int_ge_s i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int_s i\<^sub>1 \<ge> abs_int_s i\<^sub>2"
begin
  lemma ine: "int_ne i\<^sub>1 i\<^sub>2 \<longleftrightarrow> abs_int i\<^sub>1 \<noteq> abs_int i\<^sub>2" unfolding ieq ..
end

subsection\<open>Float\<close>

class wasm_float = wasm_base +
  fixes float_neg     :: "'a \<Rightarrow> 'a"
  fixes float_abs     :: "'a \<Rightarrow> 'a"
  fixes float_ceil    :: "'a \<Rightarrow> 'a"
  fixes float_floor   :: "'a \<Rightarrow> 'a"
  fixes float_trunc   :: "'a \<Rightarrow> 'a"
  fixes float_nearest :: "'a \<Rightarrow> 'a"
  fixes float_sqrt    :: "'a \<Rightarrow> 'a"
  fixes float_add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_min :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_copysign :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes float_lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes float_gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes float_le :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes float_ge :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  abbreviation (input)
  float_ne where
    "float_ne x y \<equiv> \<not> (float_eq x y)"
end
end