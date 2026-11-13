section\<open>Implementation of arbitrarily-sized WebAssembly Numeric Types using Words\<close>

theory Wasm_Type_Word
  imports
    Wasm_Type_Abs
    "Word_Lib.Signed_Division_Word"
    "Word_Lib.More_Word_Operations"
begin

lemma mult_inv_le: "(a::int) < 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> a * b \<le> -b"
  by (metis add.inverse_inverse mult.commute mult.right_neutral
      mult_minus_right neg_0_less_iff_less neg_le_iff_le pos_mult_pos_ge)

lemma sdiv_nrep: "(i\<^sub>1::'a::len word) = of_int (-(2^(LENGTH('a)-1))) \<and> i\<^sub>2 = of_int (-1)
  \<longleftrightarrow> rat_of_int (sint i\<^sub>1) / of_int (sint i\<^sub>2) = 2^(LENGTH('a)-1)"
proof (rule iffI, goal_cases)
  case 1
  thus ?case by (simp add: sint_int_min)
next
  case 2
  {
    assume i2: "i\<^sub>2 \<noteq> 0"
    hence nz: "rat_of_int (sint i\<^sub>1) \<noteq> 0" using signed_eq_0_iff 2 by force
    from 2 this i2 have "rat_of_int (sint i\<^sub>1) = rat_of_int (sint i\<^sub>2) * 2 ^ (LENGTH('a) - 1)"
      by (metis Word.of_int_sint nonzero_mult_div_cancel_left signed_eq_0_iff times_divide_eq_right)
    hence mul: "sint i\<^sub>1 = sint i\<^sub>2 * (2 ^ (LENGTH('a) - 1))"
      by (subst of_int_eq_iff[THEN sym], subst of_int_mult) simp
    have "sint i\<^sub>1 = - (2 ^ (LENGTH('a) - 1))"
    proof (rule ccontr)
      assume "sint i\<^sub>1 \<noteq> - (2 ^ (LENGTH('a) - 1))"
      hence gt: "sint i\<^sub>1 > - (2 ^ (LENGTH('a) - 1))" using sint_ge[of i\<^sub>1] by linarith
      have "sint i\<^sub>1 \<ge> 0"
      proof (rule ccontr)
        assume "\<not>sint i\<^sub>1 \<ge> 0"
        hence i1_lt_0: "sint i\<^sub>1 < 0" by simp
        have "sint i\<^sub>2 \<noteq> 0" apply (rule ccontr) using mul i1_lt_0 by simp
        {
          assume "sint i\<^sub>2 > 0"
          hence "sint i\<^sub>2 * (2 ^ (LENGTH('a) - 1)) \<ge> (2 ^ (LENGTH('a) - 1))"
            by force
          hence False using gt i1_lt_0 local.mul by linarith
        }
        {
          assume "sint i\<^sub>2 < 0"
          have "sint i\<^sub>2 * (2 ^ (LENGTH('a) - 1)) \<le> -(2 ^ (LENGTH('a) - 1))"
            by (rule mult_inv_le) (simp_all add: \<open>sint i\<^sub>2 < 0\<close>)
          hence False using mul gt by linarith
        }
        then show False using \<open>0 < sint i\<^sub>2 \<Longrightarrow> False\<close> \<open>sint i\<^sub>2 \<noteq> 0\<close> by fastforce
      qed
      hence "sint i\<^sub>1 \<ge> (2 ^ (LENGTH('a) - 1))" using mul
        by (metis div_pos_pos_trivial i2 mult.commute nonzero_mult_div_cancel_left
            of_int_0 sint_lt word_sint.Rep_inverse)
      thus False by (smt (z3) sint_lt)
    qed
    hence "sint i\<^sub>1 = - (2 ^ (LENGTH('a) - 1)) \<and> sint i\<^sub>2 = - 1" using mul
      by (smt (z3) mult_cancel_right1 mult_minus_left
          semiring_1_no_zero_divisors_class.power_not_zero)
  }
  thus ?case
    apply (cases "i\<^sub>2 \<noteq> 0")
      apply (subst word_sint.Rep_inverse[THEN sym])
    using 2 by simp_all
qed

lemma word_of_nat_signed_inv:
  assumes "- (2 ^ (LENGTH('a) - 1)) \<le> i" "i < 2 ^ (LENGTH('a) - 1)"
  shows "(word_of_nat (nat (signed_inv TYPE('a) i)) :: 'a::len word) = word_of_int i"
  apply (subst word_of_int_nat[THEN sym])
  subgoal using signed_inv_nneg[OF assms] by blast
  unfolding signed_inv[OF  assms]
  by (cases "0 \<le> i") auto

lemma int_div_mult_le:
  assumes "0 \<le> (a::int)" "0 \<le> b"
  shows "a div b * b \<le> a"
proof -
  have "a div b * b = int (nat a div nat b * nat b)"
    using assms zdiv_int by fastforce
  moreover note div_mult_le[of "nat a" "nat b"]
  moreover have "a = int (nat a)" using assms(1) by simp
  ultimately show ?thesis by linarith
qed

lemma drop_append2:
  assumes "n \<le> length xs"
  shows "drop n (xs @ ys) = drop n xs @ ys"
proof -
  have "drop (n - length xs) ys = ys" using assms by simp
  thus ?thesis using drop_append by simp
qed

lemma smod_distr: "((i\<^sub>1::'a::len word) - i\<^sub>2 * (i\<^sub>1 sdiv i\<^sub>2)) =
      (word_of_nat (nat (signed_inv TYPE('a) (sint i\<^sub>1 - sint i\<^sub>2 * (sint i\<^sub>1 sdiv sint i\<^sub>2)))))"
proof -
  let ?r = "sint i\<^sub>1 - sint i\<^sub>2 * (sint i\<^sub>1 sdiv sint i\<^sub>2)"
  have r0: "sint i\<^sub>1 = 0 \<Longrightarrow> ?r = 0" by simp
  have rp: "0 < sint i\<^sub>1 \<Longrightarrow> ?r = \<bar>sint i\<^sub>1\<bar> - \<bar>sint i\<^sub>2\<bar> * (\<bar>sint i\<^sub>1\<bar> div \<bar>sint i\<^sub>2\<bar>)"
    unfolding signed_divide_int_def
    by (simp add: linordered_idom_class.abs_sgn)
  have rn: "sint i\<^sub>1 < 0 \<Longrightarrow> ?r = - (\<bar>sint i\<^sub>1\<bar> - \<bar>sint i\<^sub>2\<bar> * (\<bar>sint i\<^sub>1\<bar> div \<bar>sint i\<^sub>2\<bar>))"
    unfolding signed_divide_int_def
    by (simp add: linordered_idom_class.abs_sgn)

  have rhs_nneg: "0 \<le> \<bar>sint i\<^sub>2\<bar> * (\<bar>sint i\<^sub>1\<bar> div \<bar>sint i\<^sub>2\<bar>)"
    using abs_ge_zero div_int_pos_iff zero_le_mult_iff by blast
  hence cmp: "\<bar>sint i\<^sub>1\<bar> - \<bar>sint i\<^sub>2\<bar> * (\<bar>sint i\<^sub>1\<bar> div \<bar>sint i\<^sub>2\<bar>) \<le> \<bar>sint i\<^sub>1\<bar>"
    by simp

  have "i\<^sub>1 - i\<^sub>2 * (i\<^sub>1 sdiv i\<^sub>2) = word_of_int (sint i\<^sub>1 - sint i\<^sub>2 * (sint i\<^sub>1 sdiv sint i\<^sub>2))"
    by (simp add: sdiv_word_def)
  also have "\<dots> = word_of_nat (nat (signed_inv TYPE('a) ?r))"
  proof (subst word_of_nat_signed_inv, goal_cases)
    case 1
    {
      assume "0 < sint i\<^sub>1"
      have "0 \<le> ?r"
        unfolding rp[OF \<open>0 < sint i\<^sub>1\<close>]
        apply (subst diff_ge_0_iff_ge)
        apply (subst mult.commute)
        apply (rule int_div_mult_le)
        using \<open>0 < sint i\<^sub>1\<close> by auto
      have "- (2 ^ (LENGTH('a) - 1)) \<le> ?r"
        apply (rule order.trans[where b=0])
        using \<open>0 \<le> ?r\<close> by auto
    }
    note ineg = this
    {
      assume "sint i\<^sub>1 < 0"
      have le: "\<bar>sint i\<^sub>1\<bar> - \<bar>sint i\<^sub>2\<bar> * (\<bar>sint i\<^sub>1\<bar> div \<bar>sint i\<^sub>2\<bar>) \<le> 2 ^ (LENGTH('a) - 1)"
        apply (rule order.trans[OF cmp])
        by (meson abs_leI le_less minus_le_iff sint_ge sint_lt)
      have "- (2 ^ (LENGTH('a) - 1)) \<le> ?r"
        unfolding rn[OF \<open>sint i\<^sub>1 < 0\<close>] using le by simp
    }
    note ipos = this
    show ?case
      apply (cases "sint i\<^sub>1 < 0")
      using ipos apply blast
      apply (cases "sint i\<^sub>1 = 0")
      using r0 apply simp
      using ineg by linarith
  next
    case 2
    {
      assume "0 < sint i\<^sub>1"
      hence "0 \<le> sint i\<^sub>1" by simp
      have "?r \<le> \<bar>sint i\<^sub>1\<bar>" unfolding rp[OF \<open>0 < sint i\<^sub>1\<close>] using cmp .
      also have "\<dots> < 2 ^ (LENGTH('a) - 1)"
        unfolding abs_of_nonneg[OF \<open>0 \<le> sint i\<^sub>1\<close>]
        by (rule sint_lt)
      finally have "?r < 2 ^ (LENGTH('a) - 1)" .
    }
    note ineg = this
    {
      assume "sint i\<^sub>1 < 0"
      have "0 \<le> \<bar>sint i\<^sub>1\<bar> - \<bar>sint i\<^sub>2\<bar> * (\<bar>sint i\<^sub>1\<bar> div \<bar>sint i\<^sub>2\<bar>)" using cmp
        by (metis abs_ge_zero diff_ge_0_iff_ge int_div_mult_le mult.commute)
      hence "- (\<bar>sint i\<^sub>1\<bar> - \<bar>sint i\<^sub>2\<bar> * (\<bar>sint i\<^sub>1\<bar> div \<bar>sint i\<^sub>2\<bar>)) \<le> 0" by linarith
      hence "?r < (2 ^ (LENGTH('a) - 1))"
        unfolding rn[OF \<open>sint i\<^sub>1 < 0\<close>]
        by (meson le_less_trans zero_less_numeral zero_less_power)
    }
    note ipos = this
    show ?case
      apply (cases "sint i\<^sub>1 < 0")
      using ipos apply blast
      apply (cases "sint i\<^sub>1 = 0")
      using r0 apply simp
      using ineg by linarith
  qed simp
  finally show ?thesis .
qed

lemma bit_of_bl_append_high:
  assumes "length lb \<le> n" "n < LENGTH('a)"
  shows "bit (of_bl (la @ lb) :: 'a::len word) n = bit (of_bl la :: 'a word) (n - length lb)"
  unfolding bit_of_bl_iff using assms by (simp add: less_diff_conv2 nth_append)

lemma word_ctz_0[simp]:
  "word_ctz (0::'a::len word) = LENGTH('a)"
  unfolding word_ctz_def by simp

locale Wasm_Int_Word =
  fixes rep :: "'a :: {len, wasm_base} \<Rightarrow> 'n :: len word"
  fixes abs :: "'n word \<Rightarrow> 'a"
  assumes length[simp]: "LENGTH('a) = LENGTH('n)"
  and abs_rep: "\<And>x. abs (rep x) = x"
  and rep_abs: "\<And>x. rep (abs x) = x"
  and rep_0: "rep 0 = 0"
begin

definition int_clz :: "'n word \<Rightarrow> 'n word" where "int_clz \<equiv> of_nat \<circ> word_clz"
definition int_ctz :: "'n word \<Rightarrow> 'n word" where "int_ctz \<equiv> of_nat \<circ> word_ctz"
definition int_popcnt :: "'n word \<Rightarrow> 'n word" where "int_popcnt \<equiv> of_nat \<circ> pop_count"
definition int_add :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_add \<equiv> (+)"
definition int_sub :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_sub \<equiv> (-)"
definition int_mul :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_mul \<equiv> (*)"
definition int_div_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word option" where
  "int_div_u i\<^sub>1 i\<^sub>2 \<equiv> if i\<^sub>2 = 0 then None else Some (i\<^sub>1 div i\<^sub>2)"
definition int_div_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word option" where
  "int_div_s i\<^sub>1 i\<^sub>2 \<equiv>
    if i\<^sub>2 = 0 \<or> (i\<^sub>1 = of_int (-(2^(LENGTH('n) - 1))) \<and> i\<^sub>2 = of_int (-1))
    then None
    else Some (i\<^sub>1 sdiv i\<^sub>2)"
definition int_rem_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word option" where
  "int_rem_u i\<^sub>1 i\<^sub>2 \<equiv> if i\<^sub>2 = 0 then None else Some (i\<^sub>1 mod i\<^sub>2)"
definition int_rem_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word option" where
  "int_rem_s i\<^sub>1 i\<^sub>2 \<equiv> if i\<^sub>2 = 0 then None else Some (i\<^sub>1 smod i\<^sub>2)"
definition int_and :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_and \<equiv> and"
definition int_or :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_or \<equiv> or"
definition int_xor :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_xor \<equiv> xor"
definition int_shl :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_shl i\<^sub>1 i\<^sub>2 \<equiv> i\<^sub>1 << (unat i\<^sub>2 mod LENGTH('n))"
definition int_shr_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_shr_u i\<^sub>1 i\<^sub>2 \<equiv> i\<^sub>1 >> (unat i\<^sub>2 mod LENGTH('n))"
definition int_shr_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_shr_s i\<^sub>1 i\<^sub>2 \<equiv> i\<^sub>1 >>> (unat i\<^sub>2 mod LENGTH('n))"
definition int_rotl :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_rotl i\<^sub>1 i\<^sub>2 \<equiv> word_rotl (unat i\<^sub>2) i\<^sub>1"
definition int_rotr :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_rotr i\<^sub>1 i\<^sub>2 \<equiv> word_rotr (unat i\<^sub>2) i\<^sub>1"
definition int_eqz :: "'a \<Rightarrow> bool" where "int_eqz a \<equiv> a = 0"
definition int_eq :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_eq \<equiv> (=)"
definition int_lt_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_lt_u \<equiv> (<)"
definition int_lt_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_lt_s \<equiv> (<s)"
definition int_gt_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_gt_u \<equiv> (>)"
definition int_gt_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_gt_s \<equiv> signed.greater"
definition int_le_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_le_u \<equiv> (\<le>)"
definition int_le_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_le_s \<equiv> (\<le>s)"
definition int_ge_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_ge_u \<equiv> (\<ge>)"
definition int_ge_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_ge_s \<equiv> signed.greater_eq"

abbreviation "lift0 \<equiv> abs"
abbreviation "lift1 \<equiv> map_fun rep abs"
abbreviation "liftid1 \<equiv> map_fun id abs"
abbreviation "lift1id \<equiv> map_fun rep id"
abbreviation "lift2 \<equiv> map_fun rep (map_fun rep abs)"
abbreviation "lift2o \<equiv> map_fun rep (map_fun rep (map_option abs))"
abbreviation "lift2id \<equiv> map_fun rep (map_fun rep id)"

definition nat_of_int :: "'a \<Rightarrow> nat" where "nat_of_int \<equiv> lift1id unat"
definition int_of_nat :: "nat \<Rightarrow> 'a" where "int_of_nat \<equiv> liftid1 of_nat"

abbreviation abs_int :: "'a \<Rightarrow> int"
  where "abs_int a \<equiv> int (local.nat_of_int a)"

abbreviation rep_int :: "int \<Rightarrow> 'a"
  where "rep_int a \<equiv> int_of_nat (nat a)"

abbreviation abs_int_bits :: "'a \<Rightarrow> bool list"
  where "abs_int_bits a \<equiv> len.ibits len_of TYPE('a) (abs_int a)"

abbreviation rep_int_bits :: "bool list \<Rightarrow> 'a"
  where "rep_int_bits a \<equiv> rep_int (len.ibits_inv len_of TYPE('a) a)"

lemma abs_int: "abs_int a = uint (rep a)"
  by (simp add: nat_of_int_def)

lemma nonzero: "x \<noteq> 0 \<Longrightarrow> rep x \<noteq> 0"
proof -
  assume "x \<noteq> 0"
  hence "abs (rep x) \<noteq> abs (rep 0)" unfolding abs_rep .
  thus "rep x \<noteq> 0" unfolding rep_0 by force
qed

lemma nonzero_int: "(x::'a) \<noteq> 0 \<Longrightarrow> abs_int x > 0"
proof -
  assume x: "x \<noteq> 0"
  have "abs_int x \<noteq> 0" by (simp add: abs_int nonzero uint_0_iff x)
  thus ?thesis using of_nat_0_le_iff by fastforce
qed

abbreviation "signed' \<equiv> len.signed (len_of :: 'a itself \<Rightarrow> nat)"
abbreviation "signed_inv' \<equiv> len.signed_inv (len_of :: 'a itself \<Rightarrow> nat)"
lemma len_axioms: "class.len (len_of :: 'a itself \<Rightarrow> nat)" by (rule len_class.axioms)
lemmas signed'_def = len.signed_def[OF len_axioms]
lemma signed': "signed TYPE('n) = signed' TYPE('a)"
  unfolding signed_def len.signed_def[OF len_axioms] length ..
lemma signed_inv': "signed_inv TYPE('n) = signed_inv' TYPE('a)"
  unfolding signed_inv_def len.signed_inv_def[OF len_axioms] length signed' ..

abbreviation abs_int_s :: "'a \<Rightarrow> int"
  where "abs_int_s a \<equiv> signed' TYPE('a) (abs_int a)"

abbreviation rep_int_s :: "int \<Rightarrow> 'a"
  where "rep_int_s a \<equiv> rep_int (signed_inv' TYPE('a) a)"

lemma abs_int_s: "abs_int_s x = sint (rep x)"
proof (cases "msb (rep x)")
  case True
  hence sint: "sint (rep x) = uint (rep x) - 2 ^ LENGTH('a)"
    by (simp add: word_sint_msb_eq word_size)
  moreover from this have "2^(LENGTH('a)-1) \<le> (uint (rep x))"
    apply (subst length)
    by (metis True diff_less len_gt_0 less_one not_le not_msb_from_less size_word.rep_eq word_2p_lem)
  ultimately show ?thesis unfolding abs_int using signed'_def length
    linorder_not_less[THEN sym] by (metis uint_lt2p)
next
  case False
  have "sint (rep x) < (2^(LENGTH('a)-1))"
    apply (subst length)
    using sint_lt by blast
  thus ?thesis unfolding abs_int signed'_def sint_eq_uint[OF False] by simp
qed

lemma rep_int_s:
  assumes
    "- (2^(LENGTH('a) - 1)) \<le> i"
    "i < 2^(LENGTH('a) - 1)"
  shows "rep_int_s i = abs (of_int i)"
proof -
  note inv = len.signed_inv[OF len_axioms assms]
  {
    assume "i < 0"
    let ?x = "i + 2^LENGTH('a)"
    have nneg: "0 \<le> ?x" using half_power assms(1)
      by (smt (verit, best) two_less_eq_exp_length)
    have "word_of_nat (nat ?x) = (word_of_int i::'n word)"
      apply (subst word_of_int_nat[OF nneg, THEN sym])
      apply (subst word_uint.Abs_norm[of i, where 'a='n, THEN sym])
      apply (subst mod_add_self2[THEN sym])
      apply (subst word_uint.Abs_norm[where 'a='n])
      apply (subst length)
      ..
    hence "abs (word_of_nat (nat (i + 2^LENGTH('a)))) = abs (word_of_int i)"
      by (rule arg_cong)
  }
  note negcase = this
  show ?thesis
    apply (cases "0 \<le> i")
    subgoal unfolding inv int_of_nat_def by simp
    unfolding inv int_of_nat_def using negcase by simp
qed

lemma abs_int_bits: "abs_int_bits a = to_bl (rep a)"
  apply (subst len.ibits[OF len_axioms])
  unfolding abs_int length
  subgoal by simp
  apply (rule uint_lt2p)
  apply (subst to_bl_eq)
  ..

lemma rep_int_bits:
  assumes "length l = LENGTH('a)"
  shows "rep_int_bits l = abs (of_bl l)"
  apply (subst len.ibits_inv[OF len_axioms assms])
  by (simp add: bl_to_bin_ge0 int_of_nat_def of_bl.abs_eq)

lemma div_rat_int_bounds:
  assumes
    "0 \<le> (L::rat)"
    "b \<noteq> 0"
    "1 \<le> \<bar>b\<bar>"
    "-L \<le> a"
    "a \<le> L"
  shows
    "-L \<le> a / b"
    "a / b \<le> L"
proof -
  have "\<bar>a\<bar> / \<bar>b\<bar> \<le> L / 1"
    apply (rule frac_le[OF \<open>0 \<le> (L::rat)\<close>])
    using \<open>-L \<le> a\<close> \<open>a \<le> L\<close> apply linarith
    apply linarith
    using \<open>1 \<le> \<bar>b\<bar>\<close> .
  hence div: "\<bar>a\<bar> / \<bar>b\<bar> \<le> L" by simp
  {
    assume ab: "0 < a \<and> 0 < b \<or> a < 0 \<and> b < 0"
    have g0: "0 \<le> a / b" using divide_le_0_iff
      unfolding less_eq_rat_def using ab by (simp add: zero_less_divide_iff)
    from g0 \<open>0 \<le> L\<close> have lb: "-L \<le> a / b" by linarith
    have "a / b = \<bar>a\<bar> / \<bar>b\<bar>" using abs_divide abs_of_nonneg g0 by fastforce
    hence ub: "a / b \<le> L" using div by simp
    note lb ub
  }
  note pos = this
  {
    assume ab: "0 < a \<and> b < 0 \<or> a < 0 \<and> 0 < b"
    hence neg: "a / b < 0" by (simp add: divide_less_0_iff)
    have ub: "a / b \<le> L" using neg assms(1) by linarith
    have "a / b = - (\<bar>a\<bar> / \<bar>b\<bar>)"
      unfolding abs_divide[THEN sym] using abs_of_neg[OF neg] by linarith
    hence lb: "-L \<le> a / b" using div by linarith
    note lb ub
  }
  note neg = this
  have zero: "a = 0 \<Longrightarrow> -L \<le> a / b \<and> a / b \<le> L" using \<open>0 \<le> L\<close> by force
  have "-L \<le> a / b \<and> a / b \<le> L"
    apply (cases "a < 0"; cases "b < 0")
      subgoal using pos by blast
      subgoal using neg zero \<open>b \<noteq> 0\<close> by force
      subgoal using neg zero \<open>b \<noteq> 0\<close> by force
      using pos zero \<open>b \<noteq> 0\<close> by force
  thus "-L \<le> a / b" "a / b \<le> L" by simp_all
qed

lemma sdiv_trunc:
  assumes "b \<noteq> 0"
  shows "(a::int) sdiv b = trunc (rat_of_int a / rat_of_int b)"
proof -
  let ?a = "rat_of_int a"
  let ?b = "rat_of_int b"
  show ?thesis
  proof (cases "0 < ?a / ?b")
    case True
    have "\<not>(0 \<le> ?a \<and> ?b \<le> 0 \<or> ?a \<le> 0 \<and> 0 \<le> ?b)"
      unfolding divide_le_0_iff[THEN sym] using True by linarith
    hence sgn: "sgn a = sgn b" using of_int_0_le_iff of_int_le_0_iff by fastforce
    hence "a sdiv b = \<lfloor>rat_of_int a / rat_of_int b\<rfloor>"
      unfolding signed_divide_int_def
      by (auto simp: div_eq_sgn_abs floor_divide_of_int_eq)
    thus ?thesis unfolding trunc using True by simp
  next
    case False
    note res_ge_0 = this
    show ?thesis
    proof (cases "a = 0")
      case False
      have signs: "0 \<le> ?a \<and> ?b \<le> 0 \<or> ?a \<le> 0 \<and> 0 \<le> ?b"
        unfolding divide_le_0_iff[THEN sym] using res_ge_0 by linarith
      hence "sgn a \<noteq> sgn b"
        apply (rule disjE)
        using assms using order_class.order.antisym apply fastforce
        using assms dual_order.antisym by fastforce
      hence sgn: "sgn a * sgn b = -1" unfolding sgn_if using False assms by presburger
      have "\<bar>a\<bar> div \<bar>b\<bar> =  \<lfloor>\<bar>?a\<bar> / \<bar>?b\<bar>\<rfloor>"
        unfolding of_int_abs[THEN sym] floor_divide_of_int_eq ..
      also have "\<dots> = \<lfloor>- (rat_of_int a / rat_of_int b)\<rfloor>"
        apply (cases "?a \<le> 0") using signs by auto
      finally have "a sdiv b = - \<lfloor>- (rat_of_int a / rat_of_int b)\<rfloor>"
        unfolding signed_divide_int_def using sgn by simp
      thus ?thesis unfolding trunc using res_ge_0 by simp
    qed (simp add: trunc)
  qed
qed

lemma trunc_div:
  "trunc (rat_of_nat (nat_of_int i\<^sub>1) / rat_of_nat (nat_of_int i\<^sub>2)) = uint (rep i\<^sub>1 div rep i\<^sub>2)"
  by (simp add: abs_int floor_divide_of_nat_eq trunc uint_div zdiv_int)

lemma mod_distr: "i\<^sub>1 - i\<^sub>2 * (i\<^sub>1 div i\<^sub>2) = word_of_nat (nat (uint i\<^sub>1 - uint i\<^sub>2 * uint (i\<^sub>1 div i\<^sub>2)))"
proof -
  have "i\<^sub>1 - i\<^sub>2 * (i\<^sub>1 div i\<^sub>2) = word_of_int (uint i\<^sub>1 - uint i\<^sub>2 * uint (i\<^sub>1 div i\<^sub>2))" by force
  moreover have "0 \<le> uint i\<^sub>1 - uint i\<^sub>2 * uint (i\<^sub>1 div i\<^sub>2)"
  proof -
    have "uint i\<^sub>2 * uint (i\<^sub>1 div i\<^sub>2) \<le> uint i\<^sub>1"
      unfolding uint_div_distrib
      using div_mult_le[of "nat (uint i\<^sub>1)" "nat (uint i\<^sub>2)"]
      by (metis mult.commute nat_div_distrib nat_le_eq_zle nat_mult_distrib unsigned_greater_eq)
    thus ?thesis by linarith
  qed
  ultimately show ?thesis by (subst (asm) word_of_int_nat)
qed

sublocale Int: wasm_int where
  len_of = len_of and zero = 0 and
  int_clz = "lift1 int_clz" and int_ctz = "lift1 int_ctz" and int_popcnt = "lift1 int_popcnt" and
  int_add = "lift2 int_add" and int_sub = "lift2 int_sub" and int_mul = "lift2 int_mul" and
  int_div_u = "lift2o int_div_u" and int_div_s = "lift2o int_div_s" and
  int_rem_u = "lift2o int_rem_u" and int_rem_s = "lift2o int_rem_s" and
  int_and = "lift2 int_and" and int_or = "lift2 int_or" and int_xor = "lift2 int_xor" and
  int_shl = "lift2 int_shl" and int_shr_u = "lift2 int_shr_u" and int_shr_s = "lift2 int_shr_s" and
  int_rotl = "lift2 int_rotl" and int_rotr = "lift2 int_rotr" and int_eqz = "id int_eqz" and
  int_eq = "lift2id int_eq" and int_lt_u = "lift2id int_lt_u" and int_lt_s = "lift2id int_lt_s" and
  int_gt_u = "lift2id int_gt_u" and int_gt_s = "lift2id int_gt_s" and int_le_u = "lift2id int_le_u" and
  int_le_s = "lift2id int_le_s" and int_ge_u = "lift2id int_ge_u" and int_ge_s = "lift2id int_ge_s" and
  int_of_nat = int_of_nat and nat_of_int = nat_of_int
proof (standard, goal_cases)
  case 1
  show ?case unfolding nat_of_int_def using rep_0 by simp
next
  case (2 i\<^sub>1 i\<^sub>2)
  show ?case unfolding int_add_def int_of_nat_def abs_int by simp
next
  case (3 i\<^sub>1 i\<^sub>2)
  show ?case unfolding int_sub_def int_of_nat_def abs_int by simp
next
  case (4 i\<^sub>1 i\<^sub>2)
  show ?case unfolding int_mul_def int_of_nat_def abs_int by simp
next
  case (5 i\<^sub>2 i\<^sub>1)
  then show ?case unfolding int_div_u_def using rep_0 by simp
next
  case (6 i\<^sub>2 i\<^sub>1)
  hence "abs_int i\<^sub>2 > 0" by (rule nonzero_int)
  hence div: "trunc (rat_of_int (abs_int i\<^sub>1) / rat_of_int (abs_int i\<^sub>2)) = abs_int i\<^sub>1 div abs_int i\<^sub>2"
    apply (subst floor_divide_of_int_eq[THEN sym])
    apply (subst trunc)
    by simp
  have "rep i\<^sub>1 div rep i\<^sub>2 =
      word_of_nat (nat (trunc (rat_of_int (abs_int i\<^sub>1) / rat_of_int (abs_int i\<^sub>2))))"
    apply (subst div)
    apply (rule word_eq_unatI)
    by (simp add: abs_int div_int_pos_iff word_div_def)
  hence "abs (rep i\<^sub>1 div rep i\<^sub>2) =
    rep_int (trunc (rat_of_int (abs_int i\<^sub>1) / rat_of_int (abs_int i\<^sub>2)))"
    apply (subst int_of_nat_def)
    apply (subst map_fun_def, subst o_id, subst comp_def)
    by simp
  thus ?case unfolding int_div_u_def using nonzero[OF 6] by simp
next
  case (7 i\<^sub>2 i\<^sub>1)
  thus ?case unfolding int_div_s_def using rep_0 by force
next
  case (8 i\<^sub>2 i\<^sub>1)
  have "rep i\<^sub>1 = word_of_int (- (2 ^ (LENGTH('n) - 1))) \<and> rep i\<^sub>2 = word_of_int (- 1)"
    apply (rule sdiv_nrep[THEN iffD2, of "rep i\<^sub>1" "rep i\<^sub>2"])
    using 8(2)[unfolded abs_int_s] unfolding length .
  thus ?case unfolding int_div_s_def by simp
next
  case (9 i\<^sub>2 i\<^sub>1)
  have ncond: "\<not>(i\<^sub>2 = 0 \<or> ((rep i\<^sub>1) = of_int (-(2^(LENGTH('n)-1))) \<and> (rep i\<^sub>2) = of_int (-1)))"
    using sdiv_nrep[THEN iffD1] 9(2)[unfolded abs_int_s] 9(1) by force
  have "lift2o int_div_s i\<^sub>1 i\<^sub>2 = lift2o int_div_s (abs (rep i\<^sub>1)) (abs (rep i\<^sub>2))"
    unfolding abs_rep ..
  also have "\<dots> = Some (abs (rep i\<^sub>1 sdiv rep i\<^sub>2))"
    using ncond nonzero abs_rep int_div_s_def by auto
  also have "\<dots> = Some (rep_int_s (trunc (rat_of_int (abs_int_s i\<^sub>1) / rat_of_int (abs_int_s i\<^sub>2))))"
  proof -
    let ?r = "rat_of_int (abs_int_s i\<^sub>1) / rat_of_int (abs_int_s i\<^sub>2)"
    have b0: "(0::rat) \<le> 2 ^ (LENGTH('a) - 1)" by simp
    have b1: "rat_of_int (abs_int_s i\<^sub>2) \<noteq> 0"
      using abs_int_s ncond nonzero signed_eq_0_iff by auto
    have b2: "1 \<le> \<bar>rat_of_int (abs_int_s i\<^sub>2)\<bar>" using b1 by force
    have "- (2 ^ (LENGTH('a) - 1)) \<le> abs_int_s i\<^sub>1"
      apply (subst abs_int_s)
      apply (subst length)
      using sint_ge .
    hence b3: "- (2 ^ (LENGTH('a) - 1)) \<le> rat_of_int (abs_int_s i\<^sub>1)"
      apply (subst of_int_numeral[symmetric])
      apply (subst of_int_power[symmetric])
      apply (subst of_int_minus[symmetric])
      apply (subst of_int_le_iff) .
    have "abs_int_s i\<^sub>1 < 2 ^ (LENGTH('a) - 1)"
      apply (subst abs_int_s)
      apply (subst length)
      using sint_lt .
    hence b4: "rat_of_int (abs_int_s i\<^sub>1) \<le> 2 ^ (LENGTH('a) - 1)" by force
    note bounds = div_rat_int_bounds[OF b0 b1 b2 b3 b4]
    have ubnex: "?r \<noteq> 2^(LENGTH('a) - 1)" using "9"(2) by fastforce
    hence ubr: "?r < 2^(LENGTH('a) - 1)" using bounds(2) by linarith
    have lb: "- (2^(LENGTH('a) - 1)) \<le> trunc ?r" unfolding trunc
      apply (cases "0 \<le> ?r")
      subgoal using bounds(1) by (simp add: le_floor_iff)
      apply (subst if_not_P)
      subgoal by simp
      apply (subst ceiling_def[symmetric])
      apply (rule order.trans[rotated, OF floor_le_ceiling, of "- (2 ^ (LENGTH('a) - 1))"])
      apply (subst le_floor_iff)
      using bounds(1) by simp
    have ubb: "a \<ge> 1 \<Longrightarrow> ?r < 0 \<Longrightarrow> - \<lfloor>- ?r\<rfloor> < a" for a by linarith
    have ub: "trunc ?r < 2^(LENGTH('a) - 1)" unfolding trunc using ubr ubb
      by (cases "0 \<le> ?r") (auto simp: floor_less_iff)
    have div: "rep i\<^sub>1 sdiv rep i\<^sub>2 = of_int (trunc ?r)"
      apply (subst sdiv_word_def)
      apply (subst sdiv_trunc)
      using ncond nonzero apply auto[1]
      unfolding abs_int_s ..
    have "abs (rep i\<^sub>1 sdiv rep i\<^sub>2) = rep_int_s (trunc ?r)"
      unfolding rep_int_s[OF lb ub] div ..
    thus ?thesis by simp
  qed
  finally show ?case .
next
  case (10 i\<^sub>2 i\<^sub>1)
  thus ?case unfolding int_rem_u_def by (simp add: rep_0)
next
  case (11 i\<^sub>2 i\<^sub>1)
  hence some: "lift2o int_rem_u i\<^sub>1 i\<^sub>2 = Some (abs (rep i\<^sub>1 mod rep i\<^sub>2))"
    unfolding int_rem_u_def using nonzero[OF \<open>i\<^sub>2 \<noteq> 0\<close>] by simp
  show ?case unfolding some minus_mult_div_eq_mod[THEN sym] mod_distr abs_int
    using trunc_div[unfolded nat_of_int_def map_fun_def]
    by (simp add: int_of_nat_def)
next
  case (12 i\<^sub>2 i\<^sub>1)
  thus ?case unfolding int_rem_s_def by (simp add: rep_0)
next
  case (13 i\<^sub>2 i\<^sub>1)
  hence nz: "sint (rep i\<^sub>2) \<noteq> 0" using nonzero[OF \<open>i\<^sub>2 \<noteq> 0\<close>] by simp
  have reps: "rep i\<^sub>1 - rep i\<^sub>1 sdiv rep i\<^sub>2 * rep i\<^sub>2 =
    word_of_nat (nat (signed_inv' TYPE('a) (sint (rep i\<^sub>1)
      - sint (rep i\<^sub>2) * (sint (rep i\<^sub>1) sdiv sint (rep i\<^sub>2)))))"
    unfolding mult.commute[of "rep i\<^sub>1 sdiv rep i\<^sub>2"] smod_distr signed_inv' ..
  have some: "lift2o int_rem_s i\<^sub>1 i\<^sub>2 = Some (abs (rep i\<^sub>1 smod rep i\<^sub>2))"
    unfolding int_rem_s_def using nonzero[OF \<open>i\<^sub>2 \<noteq> 0\<close>] by simp
  show ?case
    unfolding some int_rem_s_def smod_word_alt_def abs_int_s sdiv_trunc[OF nz, THEN sym]
      signed_inv reps
    using nz int_of_nat_def by fastforce
next
  case (14 i\<^sub>1 i\<^sub>2)
  then show ?case
    unfolding abs_int_bits
    apply (subst rep_int_bits)
    subgoal by simp
    unfolding bl_word_and[THEN sym] int_and_def by simp
next
  case (15 i\<^sub>1 i\<^sub>2)
  then show ?case
    unfolding abs_int_bits
    apply (subst rep_int_bits)
    subgoal by simp
    unfolding bl_word_or[THEN sym] int_or_def by simp
next
  case (16 i\<^sub>1 i\<^sub>2)
  then show ?case
    unfolding abs_int_bits
    apply (subst rep_int_bits)
    subgoal by simp
    unfolding bl_word_xor[THEN sym] int_xor_def by simp
next
  case (17 i\<^sub>1 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  hence "k = unat (rep i\<^sub>2) mod LENGTH('a)"
    by (simp add: abs_int nat_int.Rep_eqD zmod_int)
  hence "k \<le> LENGTH('a)" by simp
  from 17 have "d\<^sub>2 = drop k (abs_int_bits i\<^sub>1)" by simp
  have *: "(rep i\<^sub>1) << k = of_bl (d\<^sub>2 @ replicate k False)"
    unfolding \<open>d\<^sub>2 = _\<close> abs_int_bits
    apply (subst shiftl_bl)
    apply (subst drop_append2[symmetric])
    using \<open>k \<le> LENGTH('a)\<close> apply fastforce
    by (rule of_bl_drop'[symmetric]) simp
  show ?case
    unfolding int_shl_def
    apply (subst rep_int_bits)
    subgoal unfolding length_append \<open>length d\<^sub>2 = _\<close> length_replicate using \<open>k \<le> _\<close> by simp
    using * unfolding \<open>k = _\<close> by simp
next
  case (18 i\<^sub>1 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  hence "k = unat (rep i\<^sub>2) mod LENGTH('a)"
    by (simp add: abs_int nat_int.Rep_eqD zmod_int)
  hence "k \<le> LENGTH('a)" by simp
  from 18 have "d\<^sub>1 = take (LENGTH('a) - k) (abs_int_bits i\<^sub>1)" by simp
  have *: "(rep i\<^sub>1) >> k = of_bl d\<^sub>1"
    unfolding \<open>d\<^sub>1 = _\<close> bit_drop_bit_eq abs_int_bits length
    by (subst shiftr_bl[symmetric]) simp
  show ?case
    unfolding int_shr_u_def
    apply (subst rep_int_bits)
    subgoal unfolding length_append \<open>length d\<^sub>1 = _\<close> length_replicate using \<open>k \<le> _\<close> by simp
    using * unfolding \<open>k = _\<close> of_bl_rep_False by simp
next
  case (19 i\<^sub>1 d\<^sub>0 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  hence "k = unat (rep i\<^sub>2) mod LENGTH('a)"
    by (simp add: abs_int nat_int.Rep_eqD zmod_int)
  hence "k < LENGTH('a)" by simp
  note bl = \<open>abs_int_bits i\<^sub>1 = _\<close>[unfolded abs_int_bits]
  have "d\<^sub>0 = hd (to_bl (rep i\<^sub>1))" using bl by simp
  have "d\<^sub>1 = drop 1 (take (LENGTH('a) - k) (to_bl (rep i\<^sub>1)))"
    using bl \<open>length d\<^sub>1 = _\<close> by (simp add: drop_take)
  have "(rep i\<^sub>1) >>> k =
    of_bl (replicate k (hd (to_bl (rep i\<^sub>1))) @ take (LENGTH('n) - k) (to_bl (rep i\<^sub>1)))"
    apply (subst sshiftr_bl) unfolding word_msb_alt ..
  also have "\<dots> = of_bl (replicate (k + 1) d\<^sub>0 @ d\<^sub>1)"
  proof -
    let ?taken = "take (LENGTH('n) - k) (to_bl (rep i\<^sub>1))"
    have hd: "[hd (to_bl (rep i\<^sub>1))] = take 1 ?taken"
      using \<open>k < LENGTH('a)\<close> bl by force
    have rest: "?taken = [hd (to_bl (rep i\<^sub>1))] @ drop 1 ?taken"
      unfolding length hd append_take_drop_id ..
    show ?thesis
      apply (rule arg_cong[where f=of_bl])
      unfolding \<open>d\<^sub>0 = _\<close> \<open>d\<^sub>1 = _\<close> replicate_add using rest by simp
  qed
  finally have *: "(rep i\<^sub>1) >>> k = of_bl (replicate (k + 1) d\<^sub>0 @ d\<^sub>1)" .
  show ?case
    unfolding int_shr_s_def
    apply (subst rep_int_bits)
    subgoal unfolding length_append \<open>length d\<^sub>1 = _\<close> length_replicate using \<open>k < _\<close> by simp
    using * unfolding \<open>k = _\<close> by simp
next
  case (20 i\<^sub>1 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  hence k: "k = unat (rep i\<^sub>2) mod LENGTH('a)"
    by (simp add: abs_int nat_int.Rep_eqD zmod_int)
  moreover have "d\<^sub>2 = drop k (to_bl (rep i\<^sub>1))"
    using \<open>abs_int_bits _ = _\<close>[unfolded abs_int_bits] \<open>length d\<^sub>1 = k\<close> by simp
  moreover have "d\<^sub>1 = take k (to_bl (rep i\<^sub>1))"
    using \<open>abs_int_bits _ = _\<close>[unfolded abs_int_bits] \<open>length d\<^sub>1 = k\<close> by simp
  ultimately have *: "word_rotl (unat (rep i\<^sub>2)) (rep i\<^sub>1) = of_bl (d\<^sub>2 @ d\<^sub>1)"
    unfolding word_rotl_dt by simp
  show ?case unfolding int_rotl_def using 20 * by (subst rep_int_bits) (auto simp: k)
next
  case (21 i\<^sub>1 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  hence k: "k = unat (rep i\<^sub>2) mod LENGTH('a)"
    by (simp add: abs_int nat_int.Rep_eqD zmod_int)
  moreover have "d\<^sub>2 = drop (LENGTH('a) - k) (to_bl (rep i\<^sub>1))"
    using \<open>abs_int_bits _ = _\<close>[unfolded abs_int_bits] \<open>length d\<^sub>1 = _\<close> by simp
  moreover have "d\<^sub>1 = take (LENGTH('a) - k) (to_bl (rep i\<^sub>1))"
    using \<open>abs_int_bits _ = _\<close>[unfolded abs_int_bits] \<open>length d\<^sub>1 = _\<close> by simp
  ultimately have *: "word_rotr (unat (rep i\<^sub>2)) (rep i\<^sub>1) = of_bl (d\<^sub>2 @ d\<^sub>1)"
    unfolding word_rotr_dt by simp
  show ?case unfolding int_rotr_def using 21 * by (subst rep_int_bits) (auto simp: k)
next
  case (22 i\<^sub>1 k)
  hence "k = LENGTH('n)"
    apply (subst length_to_bl_eq[symmetric, of "rep i\<^sub>1"])
    unfolding abs_int_bits using length_replicate by simp
  moreover have "rep i\<^sub>1 = 0" using 22 unfolding abs_int_bits by (simp add: to_bl_use_of_bl)
  ultimately show ?case unfolding int_clz_def int_of_nat_def by simp
next
  case (23 i\<^sub>1 k d)
  hence "takeWhile Not (to_bl (rep i\<^sub>1)) = replicate k False"
    unfolding abs_int_bits by (simp add: takeWhile_tail)
  then show ?case unfolding int_clz_def int_of_nat_def word_clz_def by simp
next
  case (24 i\<^sub>1 k)
  hence "k = LENGTH('n)"
    apply (subst length_to_bl_eq[symmetric, of "rep i\<^sub>1"])
    unfolding abs_int_bits using length_replicate by simp
  moreover have "rep i\<^sub>1 = 0" using 24 unfolding abs_int_bits by (simp add: to_bl_use_of_bl)
  ultimately show ?case unfolding int_ctz_def int_of_nat_def by simp
next
  case (25 i\<^sub>1 d k)
  hence "takeWhile Not (rev (to_bl (rep i\<^sub>1))) = replicate k False"
    unfolding abs_int_bits by (simp add: takeWhile_tail)
  then show ?case unfolding int_ctz_def int_of_nat_def word_ctz_def by simp
next
  case (26 i\<^sub>1 bls k)
  from this(3) have "length (filter id (concat bls)) = length bls"
  proof (induction bls)
    case (Cons a bls)
    have "length (filter id a) = 1" by (subst Cons.prems[of a]) auto
    thus ?case unfolding concat.simps filter_append using Cons.IH Cons.prems by fastforce
  qed simp
  hence "pop_count (rep i\<^sub>1) = k"
    apply (subst pop_count_def)
    apply (subst \<open>abs_int_bits i\<^sub>1 = _\<close>[unfolded abs_int_bits])
    unfolding filter_append length_append using \<open>length bls = k\<close> by simp
  then show ?case unfolding int_popcnt_def int_of_nat_def by simp
next
  case (27 i\<^sub>1)
  then show ?case unfolding int_eqz_def abs_int
    using nonzero unsigned_eq_0_iff rep_0 by auto
next
  case (28 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_eq_def abs_int by simp
next
  case (29 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_lt_u_def abs_int word_less_def by simp
next
  case (30 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_lt_s_def abs_int_s word_sless_alt by simp
next
  case (31 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_gt_u_def abs_int word_less_def by simp
next
  case (32 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_gt_s_def abs_int_s word_sless_alt by simp
next
  case (33 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_le_u_def abs_int word_le_def by simp
next
  case (34 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_le_s_def abs_int_s word_sle_eq by simp
next
  case (35 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_ge_u_def abs_int word_le_def by simp
next
  case (36 i\<^sub>1 i\<^sub>2)
  then show ?case unfolding int_ge_s_def abs_int_s word_sle_eq by simp
qed

end

end
