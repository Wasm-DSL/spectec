theory More_More_Word 
imports 
  Word_Lib.More_Word_Operations 
  Word_Lib.Rsplit 
  Word_Lib.Syntax_Bundles 
begin

unbundle bit_projection_infix_syntax

fun bin_rsplit_rev :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list"
  where "bin_rsplit_rev n m c =
    (if m = 0 \<or> n = 0 then []
     else
      let (a, b) = bin_split n c
      in b # bin_rsplit_rev n (m - n) a)"

lemma bin_rsplit_rev_is:
  "(rev acc)@(bin_rsplit_rev n m c) = rev (bin_rsplit_aux n m c acc)"
proof (induction n m c arbitrary: acc rule: bin_rsplit_rev.induct)
  case (1 n m c)
  consider (1) "m = 0 \<or> n = 0" | (2) "\<not>(m = 0 \<or> n = 0)"
    by blast
  thus ?case
  proof (cases)
    case 1
    thus ?thesis
      by fastforce
  next
    case 2
    obtain a b where a:"(a,b) = bin_split n c"
      by simp
    have "rev (b # acc) @ bin_rsplit_rev n (m - n) a =
            rev (bin_rsplit_aux n (m - n) a (b # acc))"
      using 2 1 a
      by blast
    thus ?thesis
      using 2 a bin_rsplit_aux.elims
      by fastforce
  qed
qed

definition word_rsplit_rev :: "'a::len word \<Rightarrow> 'b::len word list"
  where "word_rsplit_rev w = map word_of_int (bin_rsplit_rev (LENGTH('b)) (LENGTH('a)) (uint w))"

lemma word_rsplit_rev_is: "word_rsplit_rev = rev \<circ> word_rsplit"
  using bin_rsplit_rev_is
  unfolding word_rsplit_def bin_rsplit_def word_rsplit_rev_def comp_def
  by (metis (no_types, opaque_lifting) append_self_conv2 fst_eqD rev_append rev_map snd_eqD)

definition word_rcat_rev :: \<open>'a::len word list \<Rightarrow> 'b::len word\<close>
  where \<open>word_rcat_rev = word_of_int \<circ> horner_sum uint (2 ^ LENGTH('a))\<close>

lemma word_rcat_rev_is: "word_rcat_rev = word_rcat \<circ> rev"
  unfolding word_rcat_def word_rcat_rev_def comp_def
  by simp

lemma word_rcat_rsplit_rev: "word_rcat_rev (word_rsplit_rev w) = w"
  using word_rcat_rsplit[of w]
  by (simp add: word_rcat_rev_is word_rsplit_rev_is)

lemma word_split_rcat_rev_size [OF refl]:
  "word_rcat_rev ws = frcw \<Longrightarrow>
    size frcw = length ws * LENGTH('a) \<Longrightarrow> word_rsplit_rev frcw = ws"
  for ws :: "'a::len word list"
  using word_rsplit_rcat_size[of "rev ws"]
  unfolding word_rcat_rev_is word_rsplit_rev_is
  by fastforce

definition word_list_sign_extend :: "nat \<Rightarrow> ('a::len) word list \<Rightarrow> 'a word list" where
  "word_list_sign_extend l (ws::'a word list) =
     takefill (if msb (last ws) then -1 else 0) l ws"

lemma word_list_sign_extend_is:
  assumes "word_list_sign_extend l ws = ws'"
          "i < l"
  shows "length ws' = l \<and> ((i < length ws \<and> ws!i = ws'!i) \<or> (i \<ge> length ws \<and> ws'!i = (if msb (last ws) then -1 else 0)))"
  using assms length_takefill[of "(if msb (last ws) then -1 else 0)" l ws]
  unfolding word_list_sign_extend_def
  apply (simp split: if_splits)
  apply (metis le_eq_less_or_eq nat_le_linear nth_takefill)
  apply (metis not_le_imp_less nth_takefill)
  done

lemma bit_rcat_rev_iff:
  assumes "((word_rcat_rev (ws::'a::len word list))) = (w::'b::len word)"
  shows "bit w n = (n < LENGTH('b) \<and> n div LENGTH('a) < length ws \<and> ws ! (n div LENGTH('a)) !! (n mod LENGTH('a)))"
proof -
  have 1:"LENGTH('a) = size (hd (rev ws))"
    by (simp add: word_size)

  have 2:"LENGTH('b) = size ((word_rcat_rev ws)::'b::len word)"
    by (simp add: word_size)

  have 3:"((word_rcat_rev ws)::'b::len word) = word_rcat (rev ws)"
    by (metis comp_eq_dest_lhs word_rcat_rev_is)

  show ?thesis
    using test_bit_rcat[OF 1 3] assms
    by (simp add: size_word.rep_eq)
qed

lemma bit_word_scast_iff':
  assumes "(scast (w::'a::len word)) = (w' :: 'b::len word)"
  shows \<open>bit w' n \<longleftrightarrow>
    n < LENGTH('b) \<and> ((LENGTH('a) > n \<and> bit w n) \<or> LENGTH('a) \<le> n \<and> bit w (LENGTH('a) - Suc 0))\<close>
  using assms[symmetric]
  apply simp
  apply transfer
  apply (auto simp add: bit_signed_take_bit_iff le_less min_def)
  done

lemma msb_bl_concat:
  shows "hd (concat (map to_bl (rev (ws@[w::'a::len word])))) = msb (last (ws@[w]))"
proof (induction ws)
  case Nil
  thus ?case
    by (simp add: word_msb_alt)
next
  case (Cons a ws)
  thus ?case
    by simp
qed

lemma hd_to_bl_of_bl:
  assumes "length xs > 0"
          "length (xs@xs') = LENGTH('a::len)"
          "(of_bl (xs @ xs')) = (w::'a word)"
  shows "hd (to_bl w) = hd xs"
  using assms(1,3)
  by simp (metis assms(2) hd_append2 to_bl_use_of_bl word_bl_Rep')

lemma msb_word_rcat_rev:
  assumes "length ws*LENGTH('a::len) = LENGTH('b::len)"
  shows "msb ((word_rcat_rev (ws::'a word list))::'b word) = msb (last ws)"
proof -
  have 1:"0 < length ws"
    using assms
    by fastforce
  then obtain ws' w' where ws_is:"ws = ws'@[w']"
    using rev_exhaust
    by auto
  have "msb ((of_bl (concat (map to_bl (rev ws))))::'b word) = hd (concat (map to_bl (rev (ws'@[w']))))"
    using msb_bl_concat ws_is hd_to_bl_of_bl[of "to_bl w'" "concat (map to_bl (rev ws'))" "_::'b word"]
    apply (simp add: word_msb_alt)
    apply (metis assms length_append_singleton length_rev mult_Suc size_rcat_lem)
    done
  thus ?thesis
    unfolding word_rcat_rev_is word_rcat_bl
    by simp (metis last_snoc word_msb_alt ws_is)
qed

lemma scast_word_rcat_rev_is_word_rcat_rev_word_list_sign_extend:
  assumes "(LENGTH('b::len)) \<ge> (LENGTH('a::len))"
          "l*LENGTH('c::len) = LENGTH('b::len)"
          "(length (ws::('c word) list))*LENGTH('c) = LENGTH('a)"
  shows "(scast::'a word\<Rightarrow>'b word) (word_rcat_rev ws) = (word_rcat_rev::(('c::len word) list)\<Rightarrow>'b word) (word_list_sign_extend l ws)"
proof -
  { fix n
    assume local_assms:"n < LENGTH('b)"
    consider
      (1) "n < LENGTH('a)"
    | (2) "n \<ge> LENGTH('a)"
      by linarith
    hence "bit ((scast::'a word\<Rightarrow>'b word) (word_rcat_rev ws)) n =
            bit ((word_rcat_rev (word_list_sign_extend l ws))::'b word) n"
    proof (cases)
      case 1
      have a:"n < LENGTH('a) \<Longrightarrow> n div LENGTH('c) < length ws"
        using assms
        by (simp add: less_mult_imp_div_less)
      thus ?thesis
        using bit_word_scast_iff'[of "(word_rcat_rev ws)::'a word" "_::'b word" n]
              word_list_sign_extend_is[of l ws _ "(n div LENGTH('c))"]
              bit_rcat_rev_iff assms local_assms 1
        by (fastforce simp add: bit_rcat_rev_iff less_mult_imp_div_less)
    next
      case 2
      hence a:"n div LENGTH('c) \<ge> length ws"
        using assms
        by (metis len_gt_0 td_gal)
      hence "bit ((scast ((word_rcat_rev ws)::'a word))::'b word) n = msb ((word_rcat_rev ws)::'a word)"
        using bit_word_scast_iff'[of "(word_rcat_rev ws)::'a word" "_::'b word" n] 2 local_assms
        by (simp add: msb_word_iff_bit)
      moreover have "bit ((word_rcat_rev (word_list_sign_extend l ws))::'b word) n =  msb ((word_rcat_rev ws)::'a word)"
        using word_list_sign_extend_is[of l ws _ "n div LENGTH('c)"] a 2 local_assms
              bit_rcat_rev_iff[of "(word_list_sign_extend l ws)" "_::'b word" n]
        by (simp add: assms(2,3) less_mult_imp_div_less msb_word_rcat_rev)
      ultimately show ?thesis
        by blast
    qed
  }
  thus ?thesis
    by (simp add: bit_word_eqI)
qed

lemma ucast_word_rcat_rev_is_word_rcat_rev_takefill:
  assumes "(LENGTH('b::len)) \<ge> (LENGTH('a::len))"
          "l*LENGTH('c::len) \<le> LENGTH('b::len)"
          "(length (ws::('c word) list))*LENGTH('c) \<le> LENGTH('a)"
          "length ws \<le> l"
  shows "(ucast::'a word\<Rightarrow>'b word) (word_rcat_rev ws) = (word_rcat_rev::(('c::len word) list)\<Rightarrow>'b word) (takefill 0 l ws)"
proof -
  { fix n
    assume local_assms:"n < LENGTH('b)"
    consider
      (1) "n < (length (ws::('c word) list))*LENGTH('c)"
    | (2) "n \<ge> (length (ws::('c word) list))*LENGTH('c)"
      by linarith
    hence "bit ((ucast::'a word\<Rightarrow>'b word) (word_rcat_rev ws)) n =
            bit ((word_rcat_rev (takefill 0 l ws))::'b word) n"
    proof (cases)
      case 1
      hence a:"n div LENGTH('c) < length ws"
        using assms
        by (simp add: less_mult_imp_div_less)
      thus ?thesis
        using bit_word_ucast_iff[of "(word_rcat_rev ws)::'a word"]
              bit_rcat_rev_iff assms local_assms 1
              length_takefill[of 0 l ws] nth_takefill[of _ l 0 ws]
        apply (simp add: bit_rcat_rev_iff less_mult_imp_div_less split: if_splits)
        using a by auto
    next
      case 2
      hence a:"n div LENGTH('c) \<ge> length ws"
        using assms
        by (metis len_gt_0 td_gal)
      hence "\<not>bit ((ucast ((word_rcat_rev ws)::'a word))::'b word) n"
        using 2 assms(3) 
        by (simp add: bit_word_ucast_iff bit_rcat_rev_iff)
      moreover have "\<not>bit ((word_rcat_rev (takefill 0 l ws))::'b word) n"
        using a bit_rcat_rev_iff[of "(takefill 0 l ws)" "_::'b word" n]
              length_takefill[of 0 l ws] nth_takefill[of _ l 0 ws]
        by simp
      ultimately show ?thesis
        by blast
    qed
  }
  thus ?thesis
    by (simp add: bit_word_eqI)
qed

lemma word_rcat_rev_is_word_rcat_rev_takefill:
  assumes "l*LENGTH('b::len) \<le> (LENGTH('a::len))"
          "length (ws::'b word list) \<le> l"
  shows "((word_rcat_rev::(('b::len word) list)\<Rightarrow>'a word) ws) = 
         (word_rcat_rev::(('b::len word) list)\<Rightarrow>'a word) (takefill 0 l ws)"
  using ucast_word_rcat_rev_is_word_rcat_rev_takefill[OF _ assms(1)] ucast_id
  by (metis assms(1,2) dual_order.trans le_refl mult.commute mult_le_mono2)

lemma ucast_word_rcat_rev_is_word_rcat_rev:
  assumes "(LENGTH('b::len)) \<ge> (LENGTH('a::len))"
          "(length (ws::('c word) list))*LENGTH('c) = LENGTH('a)"
  shows "(ucast::('a word \<Rightarrow> 'b word)) ((word_rcat_rev::(('c::len word) list)\<Rightarrow>'a word) ws) = 
         (word_rcat_rev::(('c::len word) list)\<Rightarrow>'b word) ws"
  using ucast_word_rcat_rev_is_word_rcat_rev_takefill[OF assms(1), of "length ws" ws] assms(2)
  by (simp add: assms(1))

end
