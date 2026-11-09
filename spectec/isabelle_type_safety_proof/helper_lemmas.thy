theory helper_lemmas
    imports Main isabelle_reference_output_wasm2
begin

(* Numeric bridge lemmas.
   For subtraction of naturals, the generated theory now writes
   a - b as nat (int a - int b) (SpecTec subtraction always yields an int). simp first pushes
   int inwards (of_nat_power, of_nat_1, ...), leaving terms such as nat (2 ^ N - 1); nat_bridge
   distributes nat back over them, so goals return to the old nat-only shape. *)
lemmas nat_bridge = nat_diff_distrib' nat_power_eq

lemma nat_int_diff: "nat (int a - int b) = a - b"
  by simp

lemma pow_pred_le_int: "(2::int) ^ (N - Suc 0) \<le> 2 ^ N"
  by (simp add: power_increasing)

lemma pow_pred_lt_int: "(i :: int) < 2 ^ (N - Suc 0) \<Longrightarrow> i < 2 ^ N"
  using pow_pred_le_int[of N] by linarith

lemma nat_sub_le: "0 \<le> (y :: int) \<Longrightarrow> nat (int a - y) \<le> a"
  by (simp add: nat_le_iff)

(* SpecTec's rat division followed by a conversion to nat is generated as nat (floor (m / n));
   for naturals this is ordinary nat division. *)
lemma nat_floor_div_numeral: "nat \<lfloor>(of_nat m :: rat) / numeral k\<rfloor> = m div numeral k"
  using floor_divide_of_nat_eq[where 'a = rat, of m "numeral k"] by simp

(* Page count of a memory of at most 2^32 bytes fits in 32 bits (used for memory.grow) *)
lemma mem_pages_le: "(L :: nat) \<le> 4294967296 \<Longrightarrow> nat \<lfloor>(of_nat L :: rat) / 65536\<rfloor> \<le> 4294967295"
  unfolding nat_floor_div_numeral
  by (rule order_trans[OF div_le_mono[of L 4294967296 65536]]) simp_all

(*Isabelle has an inbuilt equivalent to `list_update_func`.*)
(*If we proved `list_update_func` equivalent, then these lemmas would become trivial*)
lemma list_update_func_length:
  "length (list_update_func xs i f) = length xs"
apply (induction xs arbitrary: i)
apply simp_all
proof -
  fix a xs i
  assume ih: "\<And>i. length (list_update_func xs i f) = length xs"
  show "length (list_update_func (a # xs) i f) = Suc (length xs)"
  proof (cases i)
    case 0
    then show ?thesis
      by simp
  next
    case (Suc n)
    then show ?thesis using ih
      by simp
  qed
qed

lemma list_update_func_nth:
  assumes "i < length xs"
  shows "(list_update_func xs i f) ! i = f (xs ! i)"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc n)
    then show ?thesis using Cons by simp
  qed
qed

lemma list_update_func_nth_neq:
  assumes "i < length xs" "a \<noteq> i"
  shows "(list_update_func xs i f) ! a = xs ! a"
  using assms
proof (induction xs arbitrary: i a)
  case Nil
  then show ?case by simp
next
  case (Cons a' xs)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis using Cons by (cases a; simp)
  next
    case (Suc n)
    then show ?thesis using Cons by (cases a; simp)
  qed
qed

lemma list_all_list_update_func:
  assumes "list_all P xs"
          "i < length xs"
          "P (f (xs ! i))"
  shows "list_all P (list_update_func xs i f)"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis using Cons by simp
  next
    case (Suc n)
    then show ?thesis using Cons by simp
  qed
qed

lemma list_all2_list_update_func:
assumes "i < length xs"
    and "list_all2 P xs ys"
    and "xs' = list_update_func xs i f"
    and untouched: "\<And>x y. P x y \<Longrightarrow> Q x y"
    and updated:   "P (xs ! i) (ys ! i) \<Longrightarrow> Q (f (xs ! i)) (ys ! i)"
shows "list_all2 Q xs' ys"
proof -
  have len_eq: "length xs' = length ys"
    using assms(2,3) list_update_func_length list_all2_lengthD
      by metis
  moreover have "Q (xs' ! j) (ys ! j)" if "j < length xs'" for j
  proof (cases "j = i")
    case True
    then have "xs' ! j = f (xs ! i)" using assms(1,3) list_update_func_nth
      by simp
    moreover have "ys ! j = ys ! i"
      using True by simp
    moreover have "P (xs ! i) (ys ! i)"
      using assms(1,2) list_all2_nthD by auto
    ultimately show ?thesis
      using updated by simp
  next
    case False
    then have "xs' ! j = xs ! j"
      using assms(1,3) list_update_func_nth_neq  by auto
    moreover have "P (xs ! j) (ys ! j)"
      using assms(2,3) list_all2_nthD2 that len_eq
      by auto
    ultimately show ?thesis
      using untouched by simp
  qed
  ultimately show ?thesis unfolding list_all2_conv_all_nth
    by simp
qed


lemma list_update_func_out_of_range:
  assumes "length xs \<le> i"
  shows "list_update_func xs i g = xs"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases i) auto
qed

lemma list_all_list_update_func_gen:
  assumes "list_all P xs"
          "i < length xs \<Longrightarrow> P (g (xs ! i))"
  shows "list_all P (list_update_func xs i g)"
  using assms list_all_list_update_func list_update_func_out_of_range
  by (metis not_le)

lemma list_all_repeat: "P x \<Longrightarrow> list_all P (repeat n x)"
  by (induction n) auto


lemma list_all_list_slice:
  assumes "list_all P l"
  shows "list_all P (list_slice l i j)"
  using assms proof(induction l arbitrary: i j)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case proof(induction i arbitrary:j)
    case 0
    then show ?case proof(induction j) qed(auto)
  next
    case (Suc i)
    then show ?case proof(induction j) qed(auto)
  qed
qed
end