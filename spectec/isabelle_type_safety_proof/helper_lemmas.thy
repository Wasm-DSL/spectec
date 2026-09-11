theory helper_lemmas
    imports Main isabelle_reference_output_wasm2
begin

(*Isabelle has an inbuilt equivalent to `list_update_func`.*)
(*TODO Prove `list_update_func` equivalent; then these lemmas become trivial*)
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

end