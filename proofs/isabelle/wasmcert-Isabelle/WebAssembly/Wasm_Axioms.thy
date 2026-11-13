section \<open>Host Properties\<close>

theory Wasm_Axioms imports Wasm begin

lemma old_mem_size_def:
  shows "mem_size m = length (Rep_mem_rep (snd m)) div Ki64"
  unfolding mem_size_def mem_rep_length_def mem_length_def
  by (simp split: prod.splits)

lemma mem_grow_size:
  assumes "mem_grow m n = Some m'"
  shows "(mem_size m + n) = mem_size m'"
  using assms Abs_mem_rep_inverse
  unfolding mem_grow_def old_mem_size_def mem_append_def mem_rep_append_def bytes_replicate_def
  by (auto simp add: Ki64_def Let_def split: prod.splits if_splits)

lemma mem_grow_max1:
  assumes "mem_grow m n = Some m'"
  shows "mem_max m = mem_max m'"
  using assms Abs_mem_rep_inverse
  unfolding mem_grow_def mem_max_def mem_append_def 
  by (auto simp add: Ki64_def Let_def split: prod.splits if_splits)

lemma mem_grow_max2:
  assumes "mem_grow m n = Some m'"
  shows "pred_option ((\<le>) (mem_size m')) (mem_max m')"
  using assms Abs_mem_rep_inverse
  unfolding mem_grow_def mem_max_def mem_append_def
  by (auto simp add: assms mem_grow_size Let_def split: prod.splits if_splits)

lemma mem_grow_length:
  assumes "mem_grow m n = Some m'"
  shows "(mem_length m + (n * Ki64)) = mem_length m'"
  using assms Abs_mem_rep_inverse
        bytes_replicate_def mem_rep_append.rep_eq mem_rep_length.rep_eq
  unfolding mem_grow_def mem_length_def old_mem_size_def mem_rep_append_def mem_append_def bytes_replicate_def
  by (auto simp add: Let_def split: prod.splits if_splits)

lemma mem_grow_byte_at_m:
  assumes "k < mem_length m"
          "(mem_grow m n) = Some m'"
  shows "byte_at m' k = byte_at m k"
  using assms
  unfolding mem_rep_byte_at.rep_eq mem_length_def mem_rep_length.rep_eq mem_grow_def
            mem_rep_append.rep_eq mem_append_def mem_rep_append_def mem_size_def byte_at_def
  by (auto simp add: Abs_mem_rep_inverse nth_append Let_def split: prod.splits if_splits)

lemma mem_grow_byte_at_m_n:
  assumes "k \<ge> mem_length m"
          "(mem_grow m n) = Some m'"
          "k < mem_length m'"
  shows "byte_at m' k = (zero_byte::byte)"
  using assms
  unfolding mem_rep_byte_at.rep_eq mem_length_def mem_rep_length.rep_eq mem_grow_def
            mem_rep_append.rep_eq mem_append_def mem_rep_append_def mem_size_def byte_at_def
  by (auto simp add: Abs_mem_rep_inverse nth_append Let_def split: prod.splits if_splits)

lemma load_size:
  "(load m n off l = None) = (mem_length m < (off + n + l))"
  unfolding load_def
  by (cases "n + off + l \<le> mem_length m") auto

lemma load_packed_size:
  "(load_packed sx m n off lp l = None) = (mem_length m < (off + n + lp))"
  using load_size
  unfolding load_packed_def
  by (cases "n + off + l \<le> mem_length m") auto  

lemma store_size1:
  "(store m n off v l = None) = (mem_length m < (off + n + l))"
  unfolding store_def
  by (cases "n + off + l \<le> mem_length m") auto

lemma store_size:
  assumes "(store m n off v l = Some m')"
  shows "mem_size m = mem_size m'"
  using assms Abs_mem_rep_inverse mem_rep_length.rep_eq
  unfolding store_def mem_rep_write_bytes_def write_bytes_def 
            bytes_takefill_def
  apply (cases "n + off + l \<le> mem_length m") 
  apply(auto simp add: old_mem_size_def mem_length_def split: prod.splits)
  done

lemma store_max:
  assumes "(store m n off v l = Some m')"
  shows "mem_max m = mem_max m'"
  using assms Abs_mem_rep_inverse
  unfolding store_def mem_max_def write_bytes_def
  by (auto split: if_splits prod.splits)

lemma store_length:
  assumes "(store m n off v l = Some m')"
  shows "mem_length m = mem_length m'"
  using assms Abs_mem_rep_inverse mem_rep_length.rep_eq
  unfolding store_def mem_rep_write_bytes_def write_bytes_def 
            bytes_takefill_def
  apply (cases "n + off + l \<le> mem_length m") 
  apply(auto simp add: old_mem_size_def mem_length_def split: prod.splits)
  done

lemma store_mem_agree:
  assumes "(store m n off v l = Some m')"
          "mem_agree m"
  shows "mem_agree m'"
proof(cases "n + off + l \<le> mem_length m ")
  case True
  then have "fst (m) = fst (m')"
    using assms(1) store_def write_bytes_def by auto
  moreover have "mem_length m' = mem_length m"
    using assms(1) store_length by simp
  ultimately show ?thesis
    using  assms store_max store_size by auto
next
  case False
  then show ?thesis using assms unfolding store_def by simp
qed

lemma store_packed_size1:
  "(store_packed m n off v l = None) = (mem_length m < (off + n + l))"
  using store_size1
  unfolding store_packed_def
  by simp

lemma store_packed_size:
  assumes "(store_packed m n off v l = Some m')"
  shows "mem_size m = mem_size m'"
  using assms store_size
  unfolding store_packed_def
  by simp

lemma store_packed_max:
  assumes "(store_packed m n off v l = Some m')"
  shows "mem_max m = mem_max m'"
  using assms store_max
  unfolding store_packed_def
  by simp

lemma store_packed_length:
  assumes "(store_packed m n off v l = Some m')"
  shows "mem_length m = mem_length m'"
  using assms Abs_mem_rep_inverse mem_rep_length.rep_eq
  unfolding store_def mem_rep_write_bytes_def write_bytes_def store_packed_def
            bytes_takefill_def
  apply (cases "n + off + l \<le> mem_length m") 
  apply(auto simp add: old_mem_size_def mem_length_def split: prod.splits)
  done

lemma store_packed_mem_agree:
  assumes "(store_packed m n off v l = Some m')"
          "mem_agree m"
  shows "mem_agree m'"
proof(cases "n + off + l \<le> mem_length m ")
  case True
  then have "fst (m) = fst (m')"
    using assms(1) store_packed_def store_def write_bytes_def by auto
  moreover have "mem_length m' = mem_length m"
    using assms(1) store_packed_length by simp
  ultimately show ?thesis
    using  assms store_packed_max store_packed_size by auto
next
  case False
  then show ?thesis using assms unfolding store_packed_def store_def by simp
qed

lemma store_grow_mem_agree:
  assumes "(mem_grow m n = Some m')"
          "mem_agree m"
        shows "mem_agree m'"
proof -
  have 0: "m' = (mem_append m (n * Ki64) zero_byte)" "pred_option (\<lambda>max. (mem_size m) + n \<le> max) (mem_max m)"
    using assms  unfolding mem_grow_def apply (simp add:   handy_if_lemma Let_def)
    using assms(1) mem_grow_max1 mem_grow_max2 mem_grow_size by metis
  then have 1: "l_min (fst m') = l_min (fst m) + n" unfolding mem_append_def by (simp add: Ki64_def)
  then have 2: "l_min (fst m) * Ki64 = mem_length m" using assms(2) by simp
  have 3: "l_min (fst m') * Ki64 = mem_length m'" using 0 1 2 assms(2)
    by (simp add: assms(1) distrib_right mem_grow_length)
  have "mem_size m' = mem_size m + n" using 0
    by (simp add: assms(1) mem_grow_size)
  then show ?thesis using 0 3
    using assms(1) mem_grow_max2 by blast
qed

lemma store_tab_list_size:
  assumes "(store_tab_list t n icls = Some t')"
  shows "tab_size t = tab_size t'"
  using assms
  unfolding store_tab_list_def
  by (fastforce split: if_splits)

lemma store_tab_list_max:
  assumes "(store_tab_list t n icls = Some t')"
  shows "tab_max t = tab_max t'"
  using assms
  unfolding store_tab_list_def tab_max_def
  by (metis (mono_tags, lifting) case_prod_conv option.inject option.simps(3) prod.collapse)

lemma wasm_deserialise_num_type:"typeof_num (wasm_deserialise_num bs t) = t"
  unfolding wasm_deserialise_num_def typeof_num_def
  by (simp split: t_num.splits)

axiomatization where
    host_func_apply_preserve_store1:"host_func_apply s (t1s _> t2s) f vs hs (Some (s', vs')) \<Longrightarrow> store_extension s s'"
and host_func_apply_preserve_store2:"host_func_apply s (t1s _> t2s) f vs hs (Some (s', vs')) \<Longrightarrow> store_typing s \<Longrightarrow> store_typing s'"
and host_func_apply_respect_type:"list_all2 (\<lambda>t v. v_typing s v t) t1s vs \<Longrightarrow> host_func_apply s (t1s _> t2s) f vs hs (Some (s', vs')) \<Longrightarrow> list_all2 (\<lambda>t v. v_typing s v t) t2s vs'"

lemma host_func_apply_preserve_store:
  assumes "host_func_apply s (t1s _> t2s) f vs hs (Some (s', vs'))"
          "store_typing s"
  shows "store_extension s s' \<and> store_typing s'"
  using assms host_func_apply_preserve_store1 host_func_apply_preserve_store2
  by blast

end