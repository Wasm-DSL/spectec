section \<open>Lemmas for Soundness Proof\<close>

theory Wasm_Properties imports Wasm_Properties_Aux begin

subsection \<open>Preservation\<close>

lemma t_num_cvt: assumes "cvt t sx v = Some v'" shows "t = typeof_num v'"
  using assms
  unfolding cvt_def typeof_num_def
  by (auto split: t_num.splits option.splits)

lemma reduce_inst_is:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "f_inst f = f_inst f'"
  using assms
  by induction auto

lemma reduce_store_extension:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "store_typing s"
          "inst_typing s (f_inst f) \<C>i"
          "s\<bullet>\<C> \<turnstile> es : (ts _> ts')"
          "\<C> = \<C>i\<lparr>local := (map typeof (f_locs f)), label := arb_label, return := arb_return\<rparr>"
  shows "store_extension s s' \<and> store_typing s'"
  using assms
proof (induction arbitrary: \<C>i \<C> ts ts' arb_label arb_return rule: reduce.induct)
  case (invoke_host_Some s i_cl t1s t2s h ves vcs n m hs s' vcs' f)
  thus ?case
    using host_func_apply_preserve_store[OF invoke_host_Some(6)] invoke_host_Some(2,7)
    by blast
next
  case (global_set s f j v s')
  have 1: "v_typing s v (typeof v)"
    by (metis append_eq_Cons_conv e_type_comp_conc1 global_set.prems(3) type_const_v_typing(2))
  have "tg_t (global \<C>i ! j) = typeof v"
       "tg_mut (global \<C>i ! j) = T_mut"
       "j < length (global \<C>i)"
    using types_preserved_global_set_aux(2,3,4)[OF global_set(4)] global_set(5)
    by simp_all
  thus ?case
    using update_glob_store_extension[OF global_set(2,1)]
    by (metis "1" glob_typing_def global_set.prems(2) sglob_def store_typing_imp_glob_agree(2))
next
  case (store_Some t v s i j m k off mem' vs a)
  have "mem_subtyping (fst mem') (fst m)"
    by (metis fst_conv limits_compat_refl mem_subtyping_def option.inject option.simps(3) store_Some.hyps(4) store_def write_bytes_def)
  then show ?case
    using store_size[OF store_Some(4)] store_max[OF store_Some(4)]
          store_mem_agree[OF store_Some(4)]
          store_typing_in_mem_agree store_Some(2,3,5,6)
          store_extension_mem_leq[OF store_Some(5,3), of mem']
        inst_typing_imp_memi_agree memi_agree_def order_refl
    by (metis inst_typing_imp_memi_agree memi_agree_def order_refl)
next
  case (store_packed_Some t v s i j m k off tp mem' vs a)
  have "mem_subtyping (fst mem') (fst m)"
    by (metis fst_conv limits_compat_refl mem_subtyping_def option.sel option.simps(3) store_def store_packed_Some.hyps(4) store_packed_def write_bytes_def)
  then show ?case
    using store_packed_size[OF store_packed_Some(4)] store_packed_max[OF store_packed_Some(4)]
          store_typing_in_mem_agree store_packed_Some(2,3,5,6)
          store_extension_mem_leq[OF store_packed_Some(5,3), of mem']
          store_packed_mem_agree[OF store_packed_Some(4)]
    unfolding store_packed_def
    by (metis inst_typing_imp_memi_agree memi_agree_def order_refl)            
next
  case (store_vec_Some f j s m sv v bs k off mem' a)
  have "mem_subtyping (fst mem') (fst m)"
    by (metis fst_conv limits_compat_refl mem_subtyping_def option.sel option.simps(3) store_def store_vec_Some.hyps(4) write_bytes_def)
  then show ?case
    using store_size[OF store_vec_Some(4)] store_max[OF store_vec_Some(4)]
          store_typing_in_mem_agree store_vec_Some(1,2,5,6)
          store_extension_mem_leq[OF store_vec_Some(5,2), of mem']
          store_mem_agree[OF store_vec_Some(4)]
    by (metis inst_typing_imp_memi_agree memi_agree_def order_refl)
next
  case (memory_grow s i j m n c mem' vs)
  then have 1: "mem_agree mem'"
    using store_grow_mem_agree[OF memory_grow(4)]
    by (metis inst_typing_imp_memi_agree memi_agree_def store_typing_in_mem_agree)
  then have 2: "mem_subtyping (fst mem') (fst m)"
    by (metis Ki64_def memory_grow.hyps(1) memory_grow.hyps(2) memory_grow.hyps(4) memory_grow.prems(1) memory_grow.prems(2) inst_typing_imp_memi_agree le_add1 limits_compat_def limits_compat_refl mem_grow_max1 mem_grow_size mem_max_def mem_size_def mem_subtyping_def memi_agree_def nonzero_mult_div_cancel_right store_typing_in_mem_agree zero_neq_numeral)
  thus ?case
    using store_extension_mem_leq[OF memory_grow(5,2) _ _ mem_grow_max1[OF memory_grow(4)]]
          mem_grow_size[OF memory_grow(4)] mem_grow_max2[OF memory_grow(4)] 1 2
    by auto
next
  case (label s vs es i s' vs' es' k lholed les les')
  show ?case
    using types_exist_lfilled_weak[OF label(2,7)]
          label(4)[OF label(5,6)] label(8)
    by fastforce
next
  case (local s f es s' f' es' f0 n)
  obtain tls \<C>i' where tls_def:"inst_typing s (f_inst f) \<C>i'"
                               "length tls = n"
                               "s\<bullet>\<C>i'\<lparr>local := map typeof (f_locs f),return := Some tls\<rparr> \<turnstile> es : ([] _> tls)"
    using e_type_local[OF local(5)]
    by blast
  thus ?case
    using local(2)[OF local(3) tls_def(1,3), of _  "(label \<C>i')"]
    by force
next
  case (table_set f ti a s n vr tabs')
  have  1: "ref_typing s vr (tab_reftype (s.tabs s ! a))"
  proof -
    have h_table: "(table \<C>!ti) = (table \<C>i!ti)"
      by (simp add: table_set.prems(4))
    have "list_all2 (tabi_agree (tabs s)) (inst.tabs (f_inst f)) (table \<C>i)"
      using inst_typing.simps table_set.prems(2) by auto
    then have "tabi_agree (tabs s) (inst.tabs (f_inst f)!ti) (table \<C>! ti)" 
      by (metis h_table list_all2_nthD option.simps(3) stab_ind_def table_set.hyps(1))
    then have "tab_subtyping (fst ((tabs s)!a)) (table \<C>!ti)"
      using table_set.prems(4) inst_typing_imp_tabi_agree tabi_agree_def table_set.hyps(1) table_set.prems(2)
      by fastforce
    
    then have t1: "tab_reftype (tabs s!a) = tab_t_reftype (table \<C>!ti)"
      using tab_subtyping_def apply simp
      by (metis (mono_tags, lifting) tab_reftype_def tab_t.case tab_t.exhaust tab_t_reftype_def)
    have "ref_typing s vr (typeof_ref vr)"
      using table_set(5) types_preserved_table_set_aux(4) by blast
    then show "ref_typing s vr (tab_reftype (s.tabs s ! a))"
      using t1 types_preserved_table_set_aux(2)[OF table_set(5)] by auto
  qed
  show ?case using store_tabs1_store_extension[OF table_set(2) _ table_set.prems(1) 1]
    using inst_typing_imp_tabi_agree tabi_agree_def table_set.hyps(1) table_set.prems(2) by blast
next
  case (table_grow f ti a s tab sz n vr tab')
  let ?len = "(tab_size tab) + (nat_of_int n)"
  let ?old_limits = "tab_t_lim (fst tab)"
  let ?limits' = "?old_limits\<lparr>l_min:= ?len\<rparr>"
  have 0: "tab' = ((T_tab ?limits' (tab_t_reftype (fst tab))), snd tab @ (replicate (nat_of_int n) vr))"
          "pred_option (\<lambda>max. l_min ?limits' \<le> max) (tab_max tab)"
    using table_grow(4) unfolding grow_tab_def
    by (auto simp add: handy_if_lemma Let_def)

  have 1: "tab_size tab \<le> tab_size tab'" using 0 by simp
  have 2: "tab_max tab = tab_max tab'"
    using 0 tab_max_def tab_t_lim_def by (simp split: prod.splits tab_t.splits)
  have h_tab_agree: "tab_agree s tab" using inst_typing_store_typing_imp_tab_agree table_grow by blast
  have ts1: "l_min (tab_t_lim (fst tab')) = (tab_size tab) + (nat_of_int n)" using 0(1) tab_t_lim_def by simp
  have ts2: "l_min (tab_t_lim (fst tab)) = tab_size tab" 
    using h_tab_agree unfolding tab_agree_def by(simp add: tab_t_lim_def split: prod.splits tab_t.splits)
  have ts3: "l_min (tab_t_lim (fst tab)) \<le> l_min (tab_t_lim (fst tab'))"
    using ts1 ts2 by simp
  have ts4: "pred_option ((\<le>) (l_min (tab_t_lim (fst tab')))) (tab_max tab')"
    using 0 by
      (simp add: tab_t_lim_def tab_max_def split: prod.splits tab_t.splits)
  then have ts5: "limits_compat (tab_t_lim (fst tab')) (tab_t_lim (fst tab))"
    using 0(1) ts3 unfolding limits_compat_def by (simp add: pred_option_def tab_t_lim_def 0(2) split: tab_t.splits option.splits)
  have "tab_t_reftype (fst tab') = tab_t_reftype (fst tab)" using 0 tab_t_reftype_def by simp
  then have 3: "tab_subtyping (fst tab') (fst tab)" unfolding tab_subtyping_def
    using ts5 by (simp add: tab_t_reftype_def tab_t_lim_def split :tab_t.splits)

  have "tab_extension tab tab'" unfolding tab_extension_def using 1 2 3 by simp
  have 6: "s.tabs s ! a = tab" using table_grow by simp
  have 7: "tab_agree s tab'"
  proof -

    have "list_all (\<lambda>vr. ref_typing s vr (tab_t_reftype (fst tab))) (snd tab)"
      using h_tab_agree unfolding tab_agree_def by (simp add: tab_t_reftype_def split: prod.splits tab_t.splits)

    have "s\<bullet>\<C> \<turnstile> [Ref vr, $EConstNum (ConstInt32 n), $Table_grow ti] : ts _> ts'"
      using table_grow by simp
    then have 1: "ref_typing s vr (tab_t_reftype (table \<C>!ti))"
      by (simp add: types_preserved_table_grow_aux(2) types_preserved_table_grow_aux(4))

    have "(tab_t_reftype (table \<C>!ti)) = (tab_t_reftype (table \<C>i!ti))"
      by (simp add: table_grow.prems(4))

    have "list_all2 (tabi_agree (tabs s)) (inst.tabs (f_inst f)) (table \<C>i)"
      using table_grow(6) using inst_typing.simps by auto
   then have "tab_subtyping (fst ((tabs s)!a)) (table \<C>!ti)"
     using inst_typing_imp_tabi_agree tabi_agree_def table_grow.hyps(1) table_grow.prems(2) table_grow.prems(4) by fastforce
   
   then have "ref_typing s vr (tab_reftype (s.tabs s ! a))"
     using types_preserved_table_grow_aux(2)[OF table_grow(7)] using tab_reftype_def
     apply (simp add: typeof_ref_def split: v_ref.splits tab_t.splits)
       apply (metis (mono_tags, lifting) case_prodD ref_typing.intros(1) tab_t.case tab_t.exhaust tab_t_reftype_def tab_subtyping_def)
 
      apply (metis (mono_tags, lifting) "1" old.prod.case  tab_t.case tab_t.exhaust tab_t_reftype_def tab_subtyping_def)
     by (metis (mono_tags, lifting) case_prod_conv ref_typing.intros(3)  tab_t.case tab_t.exhaust tab_t_reftype_def tab_subtyping_def)
    then have t1: "tab_reftype (tabs s!a) = tab_t_reftype (table \<C>!ti)"
      using tab_subtyping_def tab_reftype_def tab_t_reftype_def apply (simp split: tab_t.splits prod.splits)
      using \<open>tab_subtyping (fst (s.tabs s ! a)) (table \<C> ! ti)\<close> by auto
    have "list_all (\<lambda>vr. ref_typing s vr (tab_t_reftype (fst tab))) (replicate (nat_of_int n) vr)"
      using "1" list_all_length t1 tab_reftype_def tab_t_reftype_def table_grow.hyps(2) by fastforce
    have "list_all (\<lambda>vr. ref_typing s vr (tab_t_reftype (fst tab))) (snd tab')"
      by (simp add: "0"(1) \<open>list_all (\<lambda>vr. ref_typing s vr (tab_t_reftype (fst tab))) (replicate (nat_of_int n) vr)\<close> \<open>list_all (\<lambda>vr. ref_typing s vr (tab_t_reftype (fst tab))) (snd tab)\<close>)
    then have "list_all (\<lambda>vr. ref_typing s vr (tab_t_reftype (fst tab'))) (snd tab')"
      by (simp add: "0"(1) tab_t_reftype_def)
    then show "tab_agree s tab'"
      unfolding tab_agree_def tab_t_reftype_def using ts4 ts1
      by (simp add: 0 split: prod.splits tab_t.splits)
  qed
  show ?case using store_extension_tab_leq[OF table_grow.prems(1) 6 1 7 2 3]by blast
next
  case (elem_drop a f x s)
  then have 1: "\<C> \<turnstile> [Elem_drop x] : ts _> ts'"
    using b_e_typing.elem_drop e_type_elem_drop subsumption by blast
  then have 2: "x < length (elem \<C>)" using  b_e_type_elem_drop[OF 1,of x]
    by simp
  then have 3: "x < length (elem \<C>i)" using  elem_drop(5)
    by simp
  have "list_all2 (elemi_agree s (elems s)) (inst.elems (f_inst f)) (elem \<C>i)"
    using elem_drop(3) unfolding inst_typing.simps
    by fastforce
  then have "a < length (elems s)" using elem_drop elemi_agree_def[of s "elems s"]
    using 3
    using list_all2_nthD2 by blast
  then show ?case using elem_drop_store_extension[OF _ elem_drop(2)] by simp
next
  case (data_drop a f x s)
  then have 1: "\<C> \<turnstile> [Data_drop x] : ts _> ts'"
    using b_e_typing.data_drop e_type_data_drop subsumption by blast
  then have 2: "x < length (data \<C>)" using  b_e_type_data_drop[OF 1,of x]
    by simp
  then have 3: "x < length (data \<C>i)" using  data_drop(5)
    by simp
  have "list_all2 (datai_agree (datas s)) (inst.datas (f_inst f)) (data \<C>i)"
    using data_drop(3) unfolding inst_typing.simps
    by fastforce
  then have "a < length (datas s)" using data_drop(1) datai_agree_def 3
    by (simp add: list_all2_conv_all_nth)
  then show ?case using data_drop_store_extension[OF _ data_drop(2)] by simp
qed (auto simp add: store_extension_refl store_extension.intros)+

lemma store_preserved:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "store_typing s"
          "s\<bullet>r \<tturnstile> f;es : ts"
  shows "store_extension s s' \<and> store_typing s'"
proof -
  obtain \<C>i where \<C>i_def:"inst_typing s (f_inst f) \<C>i"
                         "s\<bullet>(\<C>i\<lparr>local := map typeof (f_locs f), return := r\<rparr>) \<turnstile> es : ([] _> ts)"
    using s_type_unfold[OF assms(3)]
    by fastforce
  thus ?thesis
    using reduce_store_extension[OF assms(1,2) \<C>i_def(1,2), of r "label \<C>i"]
    by fastforce
qed

lemma typeof_unop_testop:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum v, $e] : (ts _> ts')"
          "(e = (Unop t uop)) \<or> (e = (Testop t top'))"
  shows "(typeof_num v) = t"
        "e = Unop t uop \<Longrightarrow> unop_t_num_agree uop t"
        "e = Testop t top' \<Longrightarrow> is_int_t_num t"
proof -
  have  "\<C> \<turnstile> [EConstNum v, e] : (ts _> ts')"
    using unlift_b_e assms(1)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum v] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstNum v]"]
    by fastforce
  then have
    "([] _> [T_num (typeof_num v)]) <ti: (ts _> ts'')"
    "([T_num t] _> [T_num (arity_1_result e)]) <ti: (ts'' _> ts')"
    using b_e_type_cnum b_e_type_unop_testop[OF ts''_def(2) assms(2)] by blast+
  then have "T_num t = T_num (typeof_num v)"
    using instr_subtyping_append1_type_eq
    by (metis append_Nil t.distinct(5))
  then show "(typeof_num v) = t"
    by blast
  show 
       "e = Unop t uop \<Longrightarrow> unop_t_num_agree uop t"
       "e = Testop t top' \<Longrightarrow> is_int_t_num t"
    using b_e_type_cnum[OF ts''_def(1)] typeof_def assms(2) b_e_type_unop_testop[OF ts''_def(2)]
    by simp_all
qed

lemma typeof_cvtop:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum v, $e] : (ts _> ts')"
          "e = Cvtop t1 cvtop t sx"
  shows "(typeof_num v) = t"
        "cvtop = Convert \<Longrightarrow> (t1 \<noteq> t) \<and> ((sx = None) = ((is_float_t_num t1 \<and> is_float_t_num t) \<or> (is_int_t_num t1 \<and> is_int_t_num t \<and> (t_num_length t1 < t_num_length t))))"
        "cvtop = Reinterpret \<Longrightarrow> (t1 \<noteq> t) \<and> t_num_length t1 = t_num_length t"
proof -
  have  "\<C> \<turnstile> [EConstNum v, e] : (ts _> ts')"
    using unlift_b_e assms(1)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum v] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstNum v]"]
    by fastforce
  then have
    "([] _> [T_num (typeof_num v)]) <ti: (ts _> ts'')"
    "([T_num t] _> [T_num (arity_1_result e)]) <ti: (ts'' _> ts')"
    using b_e_type_cnum b_e_type_cvtop[OF ts''_def(2) assms(2)] by blast+
  then have "T_num t = T_num (typeof_num v)"
    using instr_subtyping_append1_type_eq
    by (metis append_Nil t.distinct(5))
  then show "(typeof_num v) = t"
    by blast
  show "cvtop = Convert \<Longrightarrow> (t1 \<noteq> t) \<and> (sx = None) = ((is_float_t_num t1 \<and> is_float_t_num t) \<or> (is_int_t_num t1 \<and> is_int_t_num t \<and> (t_num_length t1 < t_num_length t)))"
       "cvtop = Reinterpret \<Longrightarrow> (t1 \<noteq> t) \<and> t_num_length t1 = t_num_length t"
    using b_e_type_cnum[OF ts''_def(1)] typeof_def b_e_type_cvtop[OF ts''_def(2) assms(2)]
    by simp_all
qed

lemma types_preserved_unop_testop_cvtop:
  assumes "\<lparr>[$EConstNum v, $e]\<rparr> \<leadsto> \<lparr>[$EConstNum v']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstNum v, $e] : (ts _> ts')"
          "(e = (Unop t op)) \<or> (e = (Testop t testop))  \<or> (e = (Cvtop t2 cvtop t sx))"
  shows "s\<bullet>\<C> \<turnstile> [$EConstNum v'] : (ts _> ts')"
proof -
  have  "\<C> \<turnstile> [EConstNum v, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum v] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstNum v]"]
    by fastforce
  then have ts''_ts': "[T_num t] _> [T_num (arity_1_result e)] <ti: ts'' _> ts'" "(typeof_num v) = t"
    using  b_e_type_unop_testop(1)[OF ts''_def(2) ] assms(3)
          b_e_type_cvtop(1)[OF ts''_def(2)] apply blast
    using assms(2) assms(3) typeof_cvtop(1) typeof_unop_testop(1) by blast
  then have "([] _> [T_num (arity_1_result e)]) <ti: (ts _> ts')"
    using instr_subtyping_comp b_e_type_cnum[OF  ts''_def(1)] by blast
  moreover
  have "arity_1_result e = typeof_num v'"
    using assms(1,3) calculation(1) ts''_ts'
    apply (cases rule: reduce_simple.cases)
    apply (simp_all add: wasm_reinterpret_def arity_1_result_def wasm_deserialise_num_type t_num_cvt typeof_num_app_testop typeof_num_app_unop)
    done
  hence "\<C> \<turnstile> [EConstNum v'] : ([] _> [T_num (arity_1_result e)])"
    using b_e_typing.const_num
    unfolding typeof_def
    by (metis v.simps(5))
  ultimately
  show "s\<bullet>\<C> \<turnstile> [$EConstNum v'] : (ts _> ts')"
    using e_typing_thread_typing.intros(1)
          b_e_weakening[of \<C> "[EConstNum v']" "[]" "[T_num (arity_1_result e)]" ts]
    by (metis e_typing_thread_typing.intros(3) to_e_list_1)
qed

lemma typeof_binop_relop:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum v1, $EConstNum v2, $e] : (ts _> ts')"
          "e = Binop t bop \<or> e = Relop t rop"
  shows "typeof_num v1 = t"
        "typeof_num v2 = t"
        "e =  Binop t bop \<Longrightarrow> binop_t_num_agree bop t"
        "e = Relop t rop \<Longrightarrow> relop_t_num_agree rop t"
proof -
  have "\<C> \<turnstile> [EConstNum v1, EConstNum v2, e] : (ts _> ts')"
    using unlift_b_e assms(1)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum v1, EConstNum v2] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstNum v1, EConstNum v2]"]
    by fastforce
  then have 1: "[T_num t, T_num t] _> [T_num (arity_2_result e)] <ti: ts'' _> ts'"
                                    "e =  Binop t bop \<Longrightarrow> binop_t_num_agree bop t"
                                    "e = Relop t rop \<Longrightarrow> relop_t_num_agree rop t"
    using assms(2) b_e_type_binop[of \<C> e ts'' ts' t] b_e_type_relop[of \<C> e ts'' ts' t]
    by blast+
  have "[] _> [T_num (typeof_num v1), T_num (typeof_num v2)] <ti: ts _> ts''" using ts''_def
    using b_e_type_value2_nn by blast
  thus "typeof_num v1 = t"
       "typeof_num v2 = t" using 1(1) instr_subtyping_append2_type_eq
    by (metis append.left_neutral list.inject t.distinct(5) t.inject(1))+
  thus "e =  Binop t bop \<Longrightarrow> binop_t_num_agree bop t"
       "e = Relop t rop \<Longrightarrow> relop_t_num_agree rop t"
    using 1 by simp_all
qed

lemma types_preserved_binop_relop:
  assumes "\<lparr>[$EConstNum v1, $EConstNum v2, $e]\<rparr> \<leadsto> \<lparr>[$EConstNum v']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstNum v1, $EConstNum v2, $e] : (ts _> ts')"
          "e = Binop t bop \<or> e = Relop t rop"
  shows "s\<bullet>\<C> \<turnstile> [$EConstNum v'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstNum v1, EConstNum v2, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum v1, EConstNum v2] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstNum v1, EConstNum v2]"]
    by fastforce
  then have 1: "([T_num t,T_num t] _>[T_num (arity_2_result e)]) <ti: (ts'' _> ts')"
    using assms(3) b_e_type_binop[of \<C> e ts'' ts' t] b_e_type_relop[of \<C> e ts'' ts' t]
    by blast
  then have 2: "([] _> [T_num (typeof_num v1), T_num (typeof_num v2)]) <ti: (ts _> ts'')"
    using ts''_def(1)
    using b_e_type_value2_nn by blast
  have "T_num (typeof_num v1) = T_num t" "T_num (typeof_num v2) = T_num t"
    using 1 2  assms(2) assms(3) typeof_binop_relop(1,2) by blast+
  hence "([] _> [T_num (arity_2_result e)]) <ti: (ts _> ts')"
    using b_e_type_cnum 1 2 ts''_def(2)
    by (metis instr_subtyping_comp)
  moreover
  have "arity_2_result e = typeof_num (v')"
    using assms(1,3)
    unfolding arity_2_result_def
    apply (cases rule: reduce_simple.cases)
    apply (simp_all add: typeof_num_app_relop)
     apply (metis typeof_num_app_binop assms(2) typeof_binop_relop(1,2))
    done
  hence "\<C> \<turnstile> [EConstNum v'] : ([] _> [T_num (arity_2_result e)])"
    using b_e_typing.const_num
    unfolding typeof_def
    by (metis v.simps(5))
  ultimately show ?thesis
    using e_typing_thread_typing.intros(1)
          b_e_weakening[of \<C> "[EConstNum v']" "[]" "[T_num (arity_2_result e)]" ts]
          subsumption to_e_list_1
    by metis
qed

lemma types_preserved_unop_vec:
  assumes "\<lparr>[$EConstVec v1, $e]\<rparr> \<leadsto> \<lparr>[$EConstVec v']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstVec v1, $e] : (ts _> ts')"
          "e = Unop_vec op"
  shows "s\<bullet>\<C> \<turnstile> [$EConstVec v'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstVec v1, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:
      "\<C> \<turnstile> [EConstVec v1] : (ts _> ts'')"
      "\<C> \<turnstile> [e] : (ts'' _> ts')"
      "([T_vec T_v128] _> [T_vec T_v128]) <ti: (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstVec v1]"] assms(3) b_e_type_unop_vec[of \<C> e _ ts']
    by fastforce
  have "\<C> \<turnstile> [EConstVec v'] : ([] _> [T_vec T_v128])"
    using b_e_typing.const_vec
    unfolding typeof_def
    by (metis (full_types) t_vec.exhaust)
  thus ?thesis
    using e_typing_thread_typing.intros(1)
    by (metis (full_types) b_e_type_cvec instr_subtyping_comp subsumption t_vec.exhaust to_e_list_1 ts''_def(1) ts''_def(3))
qed

lemma types_preserved_binop_vec:
  assumes "\<lparr>[$EConstVec v1, $EConstVec v2, $e]\<rparr> \<leadsto> \<lparr>[$EConstVec v']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstVec v1, $EConstVec v2, $e] : (ts _> ts')"
          "e = Binop_vec op"
  shows "s\<bullet>\<C> \<turnstile> [$EConstVec v'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstVec v1, EConstVec v2, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstVec v1, EConstVec v2] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
                                        "([T_vec T_v128, T_vec T_v128] _> [T_vec T_v128]) <ti: (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstVec v1, EConstVec v2]"] assms(3)
          b_e_type_binop_vec[of \<C> e _ ts']
    by fastforce
  have "\<C> \<turnstile> [EConstVec v'] : ([] _> [T_vec T_v128])"
    using b_e_typing.const_vec
    unfolding typeof_def
    by (metis (full_types) t_vec.exhaust)
  thus ?thesis
    using e_typing_thread_typing.intros(1)
          b_e_type_value2_vv[OF ts''_def(1)]
    by (metis (full_types) instr_subtyping_comp subsumption t_vec.exhaust to_e_list_1 ts''_def(3))
qed

lemma types_preserved_ternop_vec:
  assumes "\<lparr>[$EConstVec v1, $EConstVec v2,  $EConstVec v3, $e]\<rparr> \<leadsto> \<lparr>[$EConstVec v']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstVec v1, $EConstVec v2, $EConstVec v3, $e] : (ts _> ts')"
          "e = Ternop_vec op"
  shows "s\<bullet>\<C> \<turnstile> [$EConstVec v'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstVec v1, EConstVec v2, EConstVec v3, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstVec v1, EConstVec v2, EConstVec v3] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
                                        "([T_vec T_v128, T_vec T_v128, T_vec T_v128] _> [T_vec T_v128]) <ti: (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstVec v1, EConstVec v2, EConstVec v3]"] assms(3)
          b_e_type_ternop_vec[of \<C> e _ ts']
    by fastforce
  have "\<C> \<turnstile> [EConstVec v'] : ([] _> [T_vec T_v128])"
    using b_e_typing.const_vec
    unfolding typeof_def
    by (metis (full_types) t_vec.exhaust)
  thus ?thesis
    using e_typing_thread_typing.intros(1)
          b_e_type_value3_vvv[OF ts''_def(1)]
    by (metis (full_types) instr_subtyping_comp subsumption t_vec.exhaust to_e_list_1 ts''_def(3))
qed

lemma types_preserved_test_vec:
  assumes "\<lparr>[$EConstVec v1, $e]\<rparr> \<leadsto> \<lparr>[$EConstNum (ConstInt32 n)]\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstVec v1, $e] : (ts _> ts')"
          "e = Test_vec op"
  shows "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n)] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstVec v1, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstVec v1] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
                                        "([T_vec T_v128] _> [T_num T_i32]) <ti: (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstVec v1]"] assms(3)
          b_e_type_test_vec[of \<C> e _ ts']
    by fastforce
  have "\<C> \<turnstile> [EConstNum (ConstInt32 n)] : ([] _> [T_num T_i32])"
    using b_e_typing.const_num[of _ "ConstInt32 n"]
    unfolding typeof_def typeof_num_def
    by simp
  thus ?thesis
    using e_typing_thread_typing.intros(1)
          b_e_type_cnum[OF ts''_def(1)]
    by (metis (full_types) b_e_type_cvec e_typing_thread_typing.intros(3) instr_subtyping_comp t_vec.exhaust to_e_list_1 ts''_def(1) ts''_def(3))
qed

lemma types_preserved_shift_vec:
  assumes "\<lparr>[$EConstVec v1, $EConstNum (ConstInt32 n), $e]\<rparr> \<leadsto> \<lparr>[$EConstVec v']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstVec v1, $EConstNum (ConstInt32 n), $e] : (ts _> ts')"
          "e = Shift_vec op"
  shows "s\<bullet>\<C> \<turnstile> [$EConstVec v'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstVec v1, EConstNum (ConstInt32 n), e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstVec v1, EConstNum (ConstInt32 n)] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
                                        "([T_vec T_v128, T_num T_i32] _> [T_vec T_v128]) <ti: (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstVec v1, EConstNum (ConstInt32 n)]"] assms(3)
          b_e_type_shift_vec[of \<C> e _ ts']
    by fastforce
  have "\<C> \<turnstile> [EConstVec v'] : ([] _> [T_vec T_v128])"
    using b_e_typing.const_vec
    unfolding typeof_def
    by (metis (full_types) t_vec.exhaust)
  thus ?thesis
    using e_typing_thread_typing.intros(1)
          b_e_type_value2_vn[OF ts''_def(1)]
    by (metis e_typing_thread_typing.intros(3) instr_subtyping_comp t_vec.exhaust ts''_def(3) typeof_num_def types_agree_imp_e_typing v.simps(11) v_num.case(1) v_to_e_def v_typing.intros(2))
qed

lemma types_preserved_splat_vec:
  assumes "\<lparr>[$EConstNum v, $e]\<rparr> \<leadsto> \<lparr>[$EConstVec v']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstNum v, $e] : (ts _> ts')"
          "e = Splat_vec sv"
  shows "s\<bullet>\<C> \<turnstile> [$EConstVec v'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstNum v, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum v] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
                                        "([T_num (vec_lane_t sv)] _> [T_vec T_v128]) <ti: (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstNum v]"] assms(3) b_e_type_splat_vec[of \<C> e _ ts']
    by fastforce
  then have "([] _> [T_num (typeof_num v)]) <ti: (ts _> ts'')"
    using b_e_type_cnum by blast
  then have "T_num (typeof_num v) = T_num (vec_lane_t sv)"
    using ts''_def(3) instr_subtyping_append1_type_eq
    by (metis append_Nil t.distinct(5))
  moreover have "\<C> \<turnstile> [EConstVec v'] : ([] _> [T_vec T_v128])"
    using b_e_typing.const_vec
    unfolding typeof_def
    by (metis (full_types) t_vec.exhaust)
  ultimately show ?thesis
    using e_typing_thread_typing.intros(1)
    by (metis (full_types) b_e_type_cnum instr_subtyping_comp subsumption to_e_list_1 ts''_def(1) ts''_def(3))
qed

lemma types_preserved_extract_vec:
  assumes "\<lparr>[$EConstVec v1, $e]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_extract_vec sv sx i v)]\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstVec v1, $e] : (ts _> ts')"
          "e = Extract_vec sv sx i"
  shows "s\<bullet>\<C> \<turnstile> [$EConstNum (app_extract_vec sv sx i v)] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstVec v1, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' ts_id where ts''_def:"\<C> \<turnstile> [EConstVec v1] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
                                        "([T_vec T_v128] _> [T_num (vec_lane_t sv)]) <ti: (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstVec v1]"] assms(3)
          b_e_type_extract_vec[of \<C> e _ ts']
    by fastforce
  have "\<C> \<turnstile> [EConstNum (app_extract_vec sv sx i v)] : ([] _> [T_num (vec_lane_t sv)])"
    using b_e_typing.const_num[of _ "(app_extract_vec sv sx i v)"]
    unfolding typeof_def typeof_num_def app_extract_vec_def vec_lane_t_def
    by (auto simp add: Let_def split: shape_vec.splits shape_vec_i.splits shape_vec_f.splits v_num.splits)
  thus ?thesis
    using e_typing_thread_typing.intros(1)
          b_e_type_cnum[OF ts''_def(1)]
          instr_subtyping_append1_type_eq
    by (metis b_e_type_cvec instr_subtyping_comp subsumption t_vec.exhaust to_e_list_1 ts''_def(1) ts''_def(3))
qed

lemma types_preserved_replace_vec:
  assumes "\<lparr>[$EConstVec v1, $EConstNum v2, $e]\<rparr> \<leadsto> \<lparr>[$EConstVec v']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstVec v1, $EConstNum v2, $e] : (ts _> ts')"
          "e = Replace_vec sv i"
  shows "s\<bullet>\<C> \<turnstile> [$EConstVec v'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstVec v1, EConstNum v2, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' ts_id where ts''_def:"\<C> \<turnstile> [EConstVec v1, EConstNum v2] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
                                        "([T_vec T_v128, T_num (vec_lane_t sv)] _> [T_vec T_v128]) <ti: (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[EConstVec v1, EConstNum v2]"] assms(3)
          b_e_type_replace_vec[of \<C> e _ ts']
    by fastforce
  then have "([] _> [T_vec (typeof_vec v1), T_num (typeof_num v2)]) <ti: (ts _> ts'')"
    using b_e_type_value2_vn by blast
  then have "[T_vec T_v128, T_num (vec_lane_t sv)] =[T_vec (typeof_vec v1), T_num (typeof_num v2)]"
    using ts''_def(3) instr_subtyping_append2_type_eq
    by (metis append_Nil t.distinct(5) t.distinct(9))
  moreover have "\<C> \<turnstile> [EConstVec v'] : ([] _> [T_vec T_v128])"
    using b_e_typing.const_vec
    unfolding typeof_def
    by (metis (full_types) t_vec.exhaust)
  ultimately show ?thesis
    using e_typing_thread_typing.intros(1)
          b_e_type_value2_vn[OF ts''_def(1)] ts''_def(3)
          instr_subtyping_append2_type_eq
    by (metis instr_subtyping_comp subsumption to_e_list_1)
qed

lemma types_preserved_drop:
  assumes "\<lparr>[$C v, $e]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$C v, $e] : (ts _> ts')"
          "(e = (Drop))"
  shows "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
proof -
  have "s\<bullet>\<C> \<turnstile> [$C v, $e] : (ts _> ts')"
    using  assms(2)
    by simp
  then obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts'')" "s\<bullet>\<C> \<turnstile> [$e] : (ts'' _> ts')"
    using e_type_comp[where ?e = "$e" and ?es = "[$C v]"]
    by fastforce
  hence 1: "([] _> [typeof v]) <ti: (ts _> ts'')"
    using type_const_v_typing(1) by blast
  obtain t where t_def: "[t] _> [] <ti: ts'' _> ts'"
    using ts''_def assms(3) b_e_type_drop to_e_list_1 unlift_b_e
    by metis
  then have "t_subtyping t (typeof v)" using t_def 1
    by (metis append_self_conv2 instr_subtyping_append1_type_eq t_subtyping_def typeof_not_bot)
  then have "([typeof v] _> []) <ti: ([t] _> [])"
    unfolding instr_subtyping_def t_list_subtyping_def
    by fastforce
  then have "([typeof v] _> []) <ti: ts'' _> ts'"
    using t_def instr_subtyping_trans by blast
  hence "([] _> []) <ti: (ts _> ts')"
    using ts''_def assms(3) b_e_type_drop to_e_list_1 unlift_b_e
    by (metis "1" instr_subtyping_comp) 
  hence "\<C> \<turnstile> [] : (ts _> ts')"
    using b_e_type_empty
    by simp
  thus ?thesis
    using e_typing_thread_typing.intros(1)
    by fastforce
qed


lemma types_preserved_select:
  assumes "\<lparr>[$C v1, $C v2, $C vn, $e]\<rparr> \<leadsto> \<lparr>[$C v3]\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$C v1, $C v2, $C vn, $e] : (ts _> ts')"
          "(e = Select t_tag)"
        shows "s\<bullet>\<C> \<turnstile> [$C v3] : (ts _> ts')"
proof -
  have "s\<bullet>\<C> \<turnstile> [$C v1, $C v2, $C vn, $e] : (ts _> ts')"
    using  assms(2)
    by simp
  then obtain t1s where t1s_def:"s\<bullet>\<C> \<turnstile> [$C v1, $C v2, $C vn] : (ts _> t1s)" "s\<bullet>\<C> \<turnstile> [$e] : (t1s _> ts')"
    using e_type_comp[where ?e = "$e" and ?es = "[$C v1, $C v2, $C vn]"]
    by fastforce
  then obtain t where t_def:
      "([t, t, (T_num T_i32)] _> [t]) <ti: (t1s _> ts') " 
      "(t_tag = None \<and> (is_num_type t \<or> is_vec_type t \<or> t = T_bot)) \<or> t_tag = Some t"
    using b_e_type_select[of \<C> e t1s] assms
    by (metis to_e_list_1 unlift_b_e)
  have 0: "[] _> [typeof v1, typeof v2, typeof vn]  <ti: ts _> t1s" using t1s_def(1)
      using e_type_consts[ of _ _ "[v1,v2,vn]" ts t1s] store_extension_refl
      by fastforce
  have 1: "[typeof v1, typeof v2, typeof vn] = [t, t, T_num T_i32]" "typeof v1 = t" "typeof v2 = t" "typeof vn = T_num T_i32"
  proof -
    have "list_all (\<lambda>t. t \<noteq> T_bot) [typeof v1, typeof v2, typeof vn]"
      by (simp add: typeof_not_bot)
    then show
      "[typeof v1, typeof v2, typeof vn] = [t, t, T_num T_i32]"
      "typeof v1 = t"
      "typeof v2 = t"
      "typeof vn = T_num T_i32"
      using 0 instr_subtyping_append_type_eq[of "[]" "[]" "[typeof v1, typeof v2, typeof vn]" ts t1s "[]" "[t, t, T_num T_i32]" "[t]" ts'] t_def(1)
      by fastforce+
  qed
  have 2: "typeof v3 = t"
    using assms(1) assms(3) const_typeof e_typing_thread_typing.intros(5) 1
    apply (cases rule: reduce_simple.cases)
    apply fastforce
    apply (metis Cons_eq_append_conv assms(2)  e_type_comp_conc2 type_const_v_typing(2) types_agree_imp_e_typing)
    apply (metis  append_Cons assms(2) e_type_comp_conc1 e_type_value_list(2) eq_Nil_appendI type_const(3))
    by fastforce+
  have 3: "([] _> [t]) <ti: (ts _> ts')" using 0 t_def(1)
    by (metis "1"(1) instr_subtyping_comp)
  have "v_typing s v3 t"
    using assms(1) 2  assms(3)
    apply (cases rule: reduce_simple.cases)
    apply fastforce
    apply (metis Cons_eq_appendI t1s_def(1) append_self_conv2 e_type_comp_conc1 type_const_v_typing(2))
    apply (metis Cons_eq_appendI t1s_def(1) append_self_conv2 e_type_comp_conc1 type_const_v_typing(2))
    by (metis e_typing_thread_typing.intros(5) type_const_v_typing(2))
  hence "s\<bullet>\<C> \<turnstile> [$C v3] : (ts _> ts')"
    using "3" e_typing_thread_typing.intros(3) types_agree_imp_e_typing by blast 
  thus ?thesis
    using e_typing_thread_typing.intros(1)
    by fastforce
qed

lemma types_preserved_block:
  assumes "s\<bullet>\<C> \<turnstile> ($C*vs) @ [$Block tb es] : (ts _> ts')"
          "tb_tf (f_inst f) tb = (tn _> tm)"
          "types_t \<C> = types (f_inst f)"
          "length vs = n"
          "length tn = n"
          "length tm = m"
  shows "s\<bullet>\<C> \<turnstile> [Label m [] (($C*vs) @ ($* es))] : (ts _> ts')"
proof -
  obtain \<C>' where c_def:"\<C>' = \<C>\<lparr>label := [tm] @ label \<C>\<rparr>" by blast
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : (ts _> ts'')" "s\<bullet>\<C> \<turnstile> [$Block tb es] : (ts'' _> ts')"
    using assms(1) e_type_comp[of s \<C> "($C*vs)" "$Block tb es" ts ts']
    by fastforce
  hence "\<C> \<turnstile> [Block tb es] : (ts'' _> ts')"
    using unlift_b_e
    by auto
  then obtain tfn tfm where tf_def:
    "(tn _> tm) = (tfn _> tfm)"
    "tb_tf_t \<C> tb = Some (tfn _> tfm)"
    "(tfn _> tfm) <ti: (ts'' _> ts')"
    "\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es : (tfn _> tfm)"
    using b_e_type_block[of \<C> "Block tb es" ts'' ts' tb es] assms(2,3)
    by (fastforce simp add: tb_tf_def tb_tf_t_def Let_def split: if_splits tb.splits option.splits)
  hence tfn_l:"length tfn = n"
    using assms(5)
    by simp
  obtain tvs' where tvs'_def:"([] _> tvs') <ti: (ts _> ts'')" "length tvs' = n" "s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tvs')"
    using e_type_consts assms ts''_def(1) store_extension_refl
    by fastforce
  have "t_list_subtyping tvs' tn"
    using instr_subtyping_append_t_list_subtyping tvs'_def(1,2) tf_def(1,3)
    by (metis append.left_neutral tf.inject tfn_l)
  hence 1: "s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tn)" "s\<bullet>\<C>' \<turnstile> $*es : (tn _> tm)"
    using tf_def tvs'_def tfn_l ts''_def c_def e_typing_thread_typing.intros(1) tvs'_def
    apply (metis append.left_neutral e_typing_thread_typing.intros(3) instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
    using c_def e_typing_thread_typing.intros(1) tf_def(1) tf_def(4) by blast
  
  hence "s\<bullet>\<C>' \<turnstile> (($C*vs) @ ($* es)) : ([] _> tm)" using e_type_comp_conc
    by simp
  moreover
  have "s\<bullet>\<C> \<turnstile> [] : (tm _> tm)"
    using b_e_type_empty[of \<C> "[]" "[]"]
          e_typing_thread_typing.intros(1)[where ?b_es = "[]"]
          e_typing_thread_typing.intros(3)[of s \<C> "[]" "[]" "[]" "tm"]
    by (metis append.right_neutral b_e_type_empty1 b_e_weakening e_type_empty empty)
  ultimately
  show ?thesis
    using e_typing_thread_typing.intros(8)[of s \<C> "[]" tm _ "($C*vs) @ ($* es)" m]
          tf_def tvs'_def assms(5,6) e_typing_thread_typing.intros(3) c_def
    by (metis 1(1) e_type_consts_typeof instr_subtyping_comp store_extension_refl)
qed

lemma types_preserved_if:
  assumes "\<lparr>[$EConstNum (ConstInt32 n), $If tb e1s e2s]\<rparr> \<leadsto> \<lparr>[$Block tb es']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n), $If tb e1s e2s] : (ts _> ts')"
  shows   "s\<bullet>\<C> \<turnstile> [$Block tb es'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstNum (ConstInt32 n), If tb e1s e2s] : (ts _> ts')"
    using unlift_b_e assms(2)
    by fastforce
  then obtain ts_i where ts_i_def:"\<C> \<turnstile> [EConstNum (ConstInt32 n)] : (ts _> ts_i)" "\<C> \<turnstile> [If tb e1s e2s] : (ts_i _> ts')"
    using b_e_type_comp
    by (metis append_Cons append_Nil)
  then obtain tfn tfm where tf_def:"tb_tf_t \<C> tb = Some (tfn _> tfm)"
                                   "(tfn @ [T_num T_i32] _> tfm) <ti: (ts_i _> ts')"
                                   "(\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> e1s : (tfn _> tfm))"
                                   "(\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> e2s : (tfn _> tfm))"
    using b_e_type_if[of \<C> "If tb e1s e2s"]
    by fastforce
  have 1: "([] _> [T_num T_i32]) <ti: (ts _> ts_i)"
    using ts_i_def(1) b_e_type_cnum
    unfolding typeof_def typeof_num_def
    by fastforce
  moreover
  have "(\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es' : (tfn _> tfm))"
    using assms(1) tf_def
    by (cases rule: reduce_simple.cases, simp_all)
  hence "\<C> \<turnstile> [Block tb es'] : (tfn _> tfm)"
    using tf_def(1) b_e_typing.block
    by simp
  moreover
  have "(tfn _> tfm) <ti: (ts _> ts')"
    using 1 tf_def(2)
    instr_subtyping_drop_append
    by blast
  ultimately
  show ?thesis
    using tf_def(3) e_typing_thread_typing.intros(1,3)
    
    by fastforce
qed

lemma types_preserved_null:
  assumes "\<lparr>[$Ref_null t]\<rparr> \<leadsto> \<lparr>[Ref (ConstNull t)]\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$Ref_null t] : (ts _> ts')"
        shows "s\<bullet>\<C> \<turnstile> [Ref (ConstNull t)] : (ts _> ts')"
proof -
  have 2: "([] _> [T_ref t]) <ti: (ts _> ts')"
    using assms unlift_b_e to_e_list_1 b_e_type_ref_null by metis
  have 3: "s\<bullet>\<C> \<turnstile> [Ref (ConstNull t)] : ([] _> [T_ref t])"
    by (metis e_typing_thread_typing.intros(4) ref_typing.intros(1))
  then have 4: "s\<bullet>\<C> \<turnstile> [Ref (ConstNull t)] : (ts _> ts@[T_ref t])"
    using e_weakening by fastforce
  show ?thesis using 2 3
    using e_typing_thread_typing.intros(3) by blast
qed

lemma types_preserved_is_null:
  assumes "\<lparr>[$C (V_ref v), $Ref_is_null]\<rparr> \<leadsto> \<lparr>[$EConstNum (ConstInt32 n)]\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$C (V_ref v), $Ref_is_null] : (ts _> ts')"
        shows "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n)] : (ts _> ts')"
proof -
  obtain ts1 where ts1_def: "s\<bullet>\<C> \<turnstile> [$C (V_ref v)] : (ts _> ts1)"
                            "s\<bullet>\<C> \<turnstile> [$Ref_is_null] : (ts1 _> ts')"
    by (metis append_Cons append_Nil assms(2) e_type_comp)
  then have 1: "([] _> [typeof (V_ref v)]) <ti: (ts _> ts1)"
    by (simp add: type_const_v_typing(1))
  obtain tr where tr_def: "[T_ref tr] _> [T_num T_i32] <ti: ts1 _> ts'"
    using b_e_type_ref_is_null to_e_list_1 ts1_def(2) unlift_b_e
    by (metis b_e_type_ref_is_null to_e_list_1 ts1_def(2) unlift_b_e)
  have "T_ref tr = typeof (V_ref v)" using instr_subtyping_append1_type_eq
    by (metis "1" append_Nil t.distinct(11) tr_def typeof_not_bot)
  then have 2: "([] _> [T_num T_i32]) <ti: (ts _> ts')"
    using 1 tr_def
    by (metis instr_subtyping_comp)
  have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n)] : ([] _> [T_num T_i32])"
    by (metis const_num e_typing_thread_typing.intros(1) to_e_list_1 typeof_num_def v_num.case(1))
  then show ?thesis using 2
    using e_typing_thread_typing.intros(3) by blast
qed

lemma types_preserved_ref_func:
  assumes
    "j < length (inst.funcs (f_inst f))"
    "(inst.funcs (f_inst f))!j = fa"
    "\<lparr>s;f;[$(Ref_func j)]\<rparr> \<leadsto> \<lparr>s;f;[Ref (ConstRefFunc (fa))]\<rparr>"
    "s\<bullet>\<C> \<turnstile> [$(Ref_func j)] : (ts _> ts')"
    "list_all2 (funci_agree (funcs s)) (inst.funcs (f_inst f)) (func_t \<C>)"
    "store_typing s"
  shows "s\<bullet>\<C> \<turnstile> [Ref (ConstRefFunc (fa))] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [(Ref_func j)] : (ts _> ts')" using assms
    by (metis to_e_list_1 unlift_b_e)
  then have 1: "([] _> [T_ref T_func_ref]) <ti: (ts _> ts')" using b_e_type_ref_func by blast
  have 2: "ref_typing s (ConstRefFunc fa) T_func_ref"
  proof -
    have a: "list_all2 (funci_agree (funcs s)) (inst.funcs (f_inst f)) (func_t \<C>)"
      using assms(5) inst_typing.simps by auto
    have b: "j < length (inst.funcs (f_inst f))"
      using assms(1) assms(2) by fastforce
    have "funci_agree (funcs s) ((inst.funcs (f_inst f))!j) ((func_t \<C>)!j)"
      using list_all2_nthD a b by metis
    then have "fa < length ((funcs s))" unfolding funci_agree_def using assms(1,2) by auto
    then show ?thesis
      by (simp add: ref_typing.intros(2))
  qed
  have "s\<bullet>\<C> \<turnstile> [Ref (ConstRefFunc (fa))] : ([] _> [T_ref T_func_ref])"
    using  typeof_ref_def v_to_e_def 2
    using e_typing_thread_typing.intros(4) by blast
  then show ?thesis using 2
    using "1" e_typing_thread_typing.intros(3) by blast
qed

lemma types_preserved_local_tee:
  assumes "\<lparr>[$C v, $Local_tee i]\<rparr> \<leadsto> \<lparr>[$C v, $C v, $Local_set i]\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$C v, $Local_tee i] : (ts _> ts')"
  shows   "s\<bullet>\<C> \<turnstile> [$C v, $C v, $Local_set i] : (ts _> ts')"
proof -
  have "s\<bullet>\<C> \<turnstile> [$C v, $Local_tee i] : (ts _> ts')"
    using unlift_b_e assms
    by fastforce
  then obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts'')" "s\<bullet>\<C> \<turnstile> [$Local_tee i] : (ts'' _> ts')"
    by (metis append_Cons append_Nil e_type_comp)
  then have 1: "([] _> [typeof v]) <ti: (ts _> ts'')"
    using type_const_v_typing(1) by blast
  obtain t where t_def:"([t] _> [t]) <ti: (ts'' _> ts')" "(local \<C>)!i = t" "i < length(local \<C>)"
    using b_e_type_local_tee[of \<C> "Local_tee i" ts'' ts' i] ts''_def
    by (metis to_e_list_1 unlift_b_e)
  have t_bv:"t = typeof v" using t_def(1) 1 instr_subtyping_append1_type_eq
    by (metis append_self_conv2 typeof_not_bot) 
  have "\<C> \<turnstile> [Local_set i] : ([t,t] _> [t])"
    using t_def b_e_typing.local_set[of i \<C> t]
          b_e_weakening[of \<C> "[Local_set i]" "[t]" "[]" "[t]"]
    by fastforce
  then have 2: "s\<bullet>\<C> \<turnstile> [$Local_set i] : [t, t] _> [t]"
    using e_typing_thread_typing.intros(1) to_e_list_1 by metis
  have "s\<bullet>\<C> \<turnstile> [$C v] : ([t] _> [t,t])"
    using t_bv e_weakening type_const_v_typing(2) types_agree_imp_e_typing
    by (metis Cons_eq_appendI self_append_conv2 ts''_def(1))
  then have 3: "s\<bullet>\<C> \<turnstile> [$C v, $C v] : ([] _> [t,t])"
    using t_bv e_type_comp_conc type_const_v_typing(2) types_agree_imp_e_typing
    by fastforce
  have "s\<bullet>\<C> \<turnstile> [$C v, $C v, $Local_set i] : (ts _> ts@[t])"
    using 2 3
    by (metis Cons_eq_appendI append_Nil2 append_self_conv2 e_type_comp_conc e_weakening)
  moreover have "(ts _> ts@[t]) <ti: (ts _> ts')"
    using 1 t_bv t_def
    by (meson instr_subtyping_comp instr_subtyping_concat instr_subtyping_refl)
  ultimately show ?thesis
    using e_typing_thread_typing.intros(3) by blast
qed

lemma types_preserved_loop:
  assumes "s\<bullet>\<C> \<turnstile> ($C*vs) @ [$Loop tb es] : (ts _> ts')"
          "tb_tf (f_inst f) tb = (t1s _> t2s)"
          "types_t \<C> = types (f_inst f)"
          "length vs = n"
          "length t1s = n"
          "length t2s = m"
  shows "s\<bullet>\<C> \<turnstile> [Label n [$Loop tb es] (($C*vs) @ ($* es))] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : (ts _> ts'')" "s\<bullet>\<C> \<turnstile> [$Loop tb es] : (ts'' _> ts')"
    using assms(1) e_type_comp
    by fastforce
  then have "\<C> \<turnstile> [Loop tb es] : (ts'' _> ts')"
    using unlift_b_e
    by fastforce
  then obtain tfn tfm \<C>' where t_loop:"tb_tf_t \<C> tb = Some (tfn _> tfm)"
                                           "(tfn _> tfm) <ti: (ts'' _> ts')"
                                           "\<C>' = \<C>\<lparr>label := [tfn] @ label \<C>\<rparr>"
                                           "(\<C>' \<turnstile> es : (tfn _> tfm))"
    using b_e_type_loop[of \<C> "Loop tb es" ts'' ts'] assms(3)
    by fastforce
  obtain tvs where tvs_def:"([] _> tvs) <ti: (ts _> ts'') " "length vs = length tvs" "s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tvs)" "tvs = map typeof vs"
    using e_type_consts ts''_def(1) store_extension_refl
    by fastforce
  have tvs_eq1: "tfn = t1s" "tfm = t2s"
    using assms(2-5) t_loop(1,2)
    by (simp_all add: Let_def tb_tf_def tb_tf_t_def split: tb.splits option.splits if_splits)
  have "list_all (\<lambda>t. t \<noteq> T_bot) tvs" using tvs_def(4) typeof_not_bot
    by (simp add: list_all_length)
  then have tvs_eq2: "tvs = tfn"
    using tvs_def t_loop(2) instr_subtyping_append_type_eq[of "[]" "[]" tvs ts ts'' "[]" tfn tfm ts'] assms(4,5) tvs_eq1(1)
    by simp
  have "s\<bullet>\<C> \<turnstile> [$Loop tb es] : (t1s _> t2s)"
    using t_loop b_e_typing.loop e_typing_thread_typing.intros(1) tvs_eq1
    by fastforce
  moreover
  have "s\<bullet>\<C>' \<turnstile> $*es : (t1s _> t2s)"
    using t_loop e_typing_thread_typing.intros(1) tvs_eq1
    by fastforce
  then have "s\<bullet>\<C>' \<turnstile> ($C*vs)@($*es) : ([] _> t2s)"
    using tvs_eq1 tvs_def(3) e_type_comp_conc
    using tvs_eq2 by blast
  ultimately
  have "s\<bullet>\<C> \<turnstile> [Label n [$Loop tb es] (($C*vs) @ ($* es))] : ([] _> t2s)"
    using e_typing_thread_typing.intros(8)[of s \<C> "[$Loop tb es]" t1s t2s "($C*vs) @ ($* es)"]
          t_loop(4) assms(5) t_loop(3) tvs_eq1(1) by blast
  then show ?thesis
    using t_loop e_typing_thread_typing.intros(3) tvs_def(1) tvs_eq1 tvs_eq2 instr_subtyping_comp by blast
qed

lemma types_preserved_label_value:
  assumes "\<lparr>[Label n es0 ($C*vs)]\<rparr> \<leadsto> \<lparr>($C*vs)\<rparr>"
          "s\<bullet>\<C> \<turnstile> [Label n es0 ($C*vs)] : (ts _> ts')"
  shows "s\<bullet>\<C> \<turnstile> ($C*vs) : (ts _> ts')"
proof -
  obtain tls t2s where t2s_def:"([] _> t2s) <ti: (ts _> ts')"
                           "(s\<bullet>\<C> \<turnstile> es0 : (tls _> t2s))"
                           "(s\<bullet>\<C>\<lparr>label := [tls] @ (label \<C>)\<rparr> \<turnstile> ($C*vs) : ([] _> t2s))"
    using assms e_type_label
    by fastforce
  thus ?thesis
    using e_type_consts assms(2) e_typing_thread_typing.intros(3) store_extension_refl
    by meson
qed

lemma types_preserved_br_if:
  assumes "\<lparr>[$EConstNum (ConstInt32 n), $Br_if i]\<rparr> \<leadsto> \<lparr>e\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n), $Br_if i] : (ts _> ts')"
          "e = [$Br i] \<or> e = []"
  shows   "s\<bullet>\<C> \<turnstile> e : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstNum (ConstInt32 n), Br_if i] : (ts _> ts')"
    using unlift_b_e assms(2)
    by fastforce
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum (ConstInt32 n)] : (ts _> ts'')" "\<C> \<turnstile> [Br_if i] : (ts'' _> ts')"
    using b_e_type_comp[of _ "[EConstNum (ConstInt32 n)]" "Br_if i"]
    by fastforce
  then have 1: "([] _> [T_num T_i32]) <ti: (ts _> ts'')"
    by (metis b_e_type_cnum typeof_num_def v_num.case(1))
  obtain ts_b where ts_b_def:"i < length(label \<C>)"
                                        "(ts_b@[T_num T_i32] _> ts_b) <ti: (ts'' _> ts')"
                                        "(label \<C>)!i = ts_b"
    using b_e_type_br_if[of \<C> "Br_if i" ts'' ts' i] ts''_def
    by fastforce
  show ?thesis
    using assms(3)
  proof (rule disjE)
    assume "e = [$Br i]"
    thus ?thesis
      using 1 e_typing_thread_typing.intros(1) b_e_typing.br ts_b_def
      by (metis append_eq_append_conv2 e_typing_thread_typing.intros(3) instr_subtyping_drop_append to_e_list_1)
  next
    assume "e = []"
    thus ?thesis
      using 1 b_e_type_empty ts_b_def(3)
      e_typing_thread_typing.intros(1)[of _ "[]" "(ts _> ts')"]
      by (metis append_Nil2 b_e_weakening e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) instr_subtyping_drop_append instr_subtyping_refl list.simps(8) ts_b_def(2))
  qed
qed

lemma types_preserved_br_table:
  assumes "\<lparr>[$EConstNum (ConstInt32 n), $Br_table is i]\<rparr> \<leadsto> \<lparr>[$Br i']\<rparr>"
          "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n), $Br_table is i] : (ts _> ts')"
          "(i' = (is ! nat_of_int c) \<and> length is > nat_of_int c) \<or> i' = i"
  shows "s\<bullet>\<C> \<turnstile> [$Br i'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [EConstNum (ConstInt32 n), Br_table is i] : (ts _> ts')"
    using unlift_b_e assms(2)
    by fastforce
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum (ConstInt32 n)] : (ts _> ts'')" "\<C> \<turnstile> [Br_table is i] : (ts'' _> ts')"
    using b_e_type_comp[of _ "[EConstNum (ConstInt32 n)]" "Br_table is i"]
    by fastforce
  then have 1: "([] _> [T_num T_i32]) <ti: (ts _> ts'')"
    by (metis b_e_type_cnum typeof_num_def v_num.case(1))
  obtain t1s ts_l t2s where ts_c_def:"list_all (\<lambda>i. i < length(label \<C>) \<and> ts_l <ts: (label \<C>)!i) (is@[i])"
                                        "(t1s @ ts_l @ [T_num T_i32] _> t2s) <ti: (ts'' _> ts')"
                                        "ts_l <ts: label \<C>!i"
    using b_e_type_br_table[of \<C> "Br_table is i" ts'' ts'] ts''_def
    by fastforce
  have 2: "(t1s @ ts_l _> t2s) <ti: (ts _> ts')"
    using ts_c_def(2) 
    instr_subtyping_drop_append[OF 1, of "t1s @ ts_l" t2s ts']
    by simp
  then have "ts_l <ts: label \<C> ! i'"
    by (metis assms(3) list_all_append list_all_length ts_c_def(1) ts_c_def(3))
  then have "t1s @ label \<C> ! i' _> t2s <ti: t1s@ts_l _> t2s"
    using instr_subtyping_refl instr_subtyping_replace3 t_list_subtyping_prepend by blast
  then have "\<C> \<turnstile> [Br i'] : (ts _> ts')"
    using assms(3) ts_c_def(1,2,3) b_e_typing.br[of i' \<C> "label \<C> ! i'" t1s t2s] 1 2
    unfolding list_all_length
    by (metis (no_types, lifting) list.pred_inject(2) list_all_append list_all_length subsumption
        ts_c_def(1))
  thus ?thesis
    using e_typing_thread_typing.intros(1)
    by fastforce
qed

lemma types_preserved_local_const:
  assumes "\<lparr>[Frame n f ($C*vs)]\<rparr> \<leadsto> \<lparr>($C*vs)\<rparr>"
          "s\<bullet>\<C> \<turnstile> [Frame n f ($C*vs)] : (ts _> ts')"
  shows "s\<bullet>\<C> \<turnstile> ($C*vs): (ts _> ts')"
proof -
  obtain tls \<C>i where "(s\<bullet>\<C>i\<lparr>local := (map typeof (f_locs f)), return := Some tls\<rparr> \<turnstile> ($C*vs) : ([] _> tls))"
                   "([] _> tls) <ti: (ts _> ts')"
    using e_type_local[OF assms(2)]
    by blast+
  moreover
  then have "s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> tls)"
    using assms(2) e_type_consts store_extension_refl
    using e_type_consts_typeof by blast
  ultimately
  show ?thesis
    using e_typing_thread_typing.intros(3)
    by fastforce
qed

lemma typing_map_typeof:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> tvs)"
  shows "tvs = map typeof vs"
  using assms
proof (induction vs arbitrary: tvs rule: List.rev_induct)
  case Nil
  hence "\<C> \<turnstile> [] : ([] _> tvs)"
    using unlift_b_e
    by auto
  thus ?case
    using Nil
    using e_type_consts_typeof store_extension_refl by blast
next
  case (snoc a vs)
  obtain tvs' where tvs'_def:"s\<bullet>\<C> \<turnstile> $C*vs: ([] _> tvs')" "s\<bullet>\<C> \<turnstile> [$C a] : (tvs' _> tvs)"
    using snoc(2) e_type_comp
    by fastforce
  hence "tvs' = map typeof vs"
    using snoc(1)
    by fastforce
  moreover
  obtain t where t_def:"tvs = tvs' @ [t]" "s\<bullet>\<C> \<turnstile> [$C a] : ([] _> [t])" "t = typeof a"
    using tvs'_def(2) e_type_consts[of s \<C> "[a]"] store_extension_refl
    by (metis calculation e_type_consts_typeof list.simps(8) list.simps(9) map_append snoc.prems type_const_v_typing(2) types_agree_imp_e_typing)
  ultimately
  show ?case
    using t_def
    by simp
qed

lemma types_preserved_call_indirect_Some:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 c), $(Call_indirect ti j)] : (ts _> ts')"
          "stab s i' ti (nat_of_int c) = Some (ConstRefFunc i_cl)"
          "stypes i' j = tf"
          "cl_type (funcs s!i_cl) = tf"
          "store_typing s"
          "inst_typing s i' \<C>i"
          "\<C> = \<C>i\<lparr>local := tvs, label := arb_labs, return := arb_return\<rparr>"
  shows "s\<bullet>\<C> \<turnstile> [Invoke i_cl] : (ts _> ts')"
proof -
  obtain t1s t2s where tf_def:"tf = (t1s _> t2s)"
    using tf.exhaust by blast
  obtain ts'' where ts''_def:"\<C> \<turnstile> [EConstNum (ConstInt32 c)] : (ts _> ts'')"
                             "\<C> \<turnstile> [Call_indirect ti j] : (ts'' _> ts')"
    using e_type_comp[of s \<C> "[$EConstNum (ConstInt32 c)]" "$(Call_indirect ti j)" ts ts']
          assms(1)
          unlift_b_e[of s \<C> "[EConstNum (ConstInt32 c)]"]
          unlift_b_e[of s \<C> "[Call_indirect ti j]"]
    by auto
  hence "([] _> [T_num T_i32]) <ti: (ts _> ts'')"
    using b_e_type_cnum
    unfolding typeof_def typeof_num_def
    by fastforce
  moreover
  then have t_call_indirect : "j < length (types_t \<C>)"
                         "(t1s @ [T_num T_i32] _> t2s) <ti: (ts'' _> ts')"
                         "types_t \<C> ! j = (t1s _> t2s)"
    using b_e_type_call_indirect[OF ts''_def(2), of ti j] tf_def assms(3,7)
          inst_typing_imp_types_eq[OF assms(6)]
    unfolding stypes_def
    by fastforce+
  moreover
  obtain tf' where tf'_def:"cl_typing s (funcs s!i_cl) tf'"
                           "i_cl < length (funcs s)"
    using assms(2,5,6) stab_typed_some_imp_cl_typed
    by blast
  hence "cl_typing s (funcs s!i_cl) tf"
    using assms(4)
    unfolding cl_typing.simps cl_type_def
    by auto
  hence "s\<bullet>\<C> \<turnstile> [Invoke i_cl] : tf"
    using e_typing_thread_typing.intros(7)[OF tf'_def(2)] cl_type_exists
    by fastforce
  ultimately
  show "s\<bullet>\<C> \<turnstile> [Invoke i_cl] : (ts _> ts')"
    using tf_def e_typing_thread_typing.intros(3) instr_subtyping_drop_append by blast
qed

lemma types_preserved_call_indirect_None:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 c), $(Call_indirect ti j)] : (ts _> ts')"
  shows "s\<bullet>\<C> \<turnstile> [Trap] : (ts _> ts')"
  using e_typing_thread_typing.intros(5)
  by blast

lemma types_preserved_invoke_native:
  assumes "s\<bullet>\<C> \<turnstile> ves @ [Invoke i_cl] : (ts _> ts')"
          "(funcs s!i_cl) = Func_native i (t1s _> t2s) tfs es"
          "ves = $C* vs"
          "length vs = n"
          "length tfs = k"
          "length t1s = n"
          "length t2s = m"
          "n_zeros tfs = Some zs"
          "store_typing s"
  shows "s\<bullet>\<C> \<turnstile> [Frame m \<lparr>f_locs = (vs @ zs), f_inst = i\<rparr> [Label m [] ($*es)]] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> ves : (ts _> ts'')" "s\<bullet>\<C> \<turnstile> [Invoke i_cl] : (ts'' _> ts')"
  using assms(1) e_type_comp
  by fastforce
  have ves_c:"const_list ves"
    using is_const_list[OF assms(3)]
    by simp
  then obtain tvs where tvs_def:"([] _> tvs) <ti: (ts _> ts'')"
                                "length t1s = length tvs"
                                "s\<bullet>\<C> \<turnstile> ves : ([] _> tvs)"
    using ts''_def(1) e_type_const_list[of ves s \<C> ts ts''] assms store_extension_refl
    by fastforce
  then have vs_tvs: "list_all2 (\<lambda> v t. v_typing s v t) vs tvs"
    by (metis (no_types, lifting) assms(3) assms(4) assms(6) e_typing_imp_list_v_typing(1) list_all2_all_nthI list_all_length nth_map typing_map_typeof)
  have 1:"cl_typing s (Func_native i (t1s _> t2s) tfs es) (t1s _> t2s)"
    using store_typing_imp_cl_typing[OF assms(9)] e_type_invoke[OF ts''_def(2)]
          assms(2)
    unfolding cl_type_def
    by fastforce
  obtain \<C>' where ts_c_def:"(t1s _> t2s) <ti: (ts'' _> ts')"
                                "inst_typing s i \<C>'"
                                "(\<C>'\<lparr>local := t1s @ tfs, label := ([t2s] @ (label \<C>')), return := Some t2s\<rparr>  \<turnstile> es : ([] _> t2s))"
    using e_type_invoke[OF ts''_def(2)] cl_typing_native[OF 1] assms(2) cl_type_exists[OF 1]
    by fastforce
  obtain \<C>'' where c''_def:"\<C>'' = \<C>'\<lparr>local := t1s @ tfs, return := Some t2s\<rparr>"
    by blast
  hence "\<C>''\<lparr>label := ([t2s] @ (label \<C>''))\<rparr> = \<C>'\<lparr>local := t1s @ tfs, label := ([t2s] @ (label \<C>')), return := Some t2s\<rparr>"
    by fastforce
  hence 1: "s\<bullet>\<C>'' \<turnstile> [Label m [] ($*es)] : ([] _> t2s)"
    using ts_c_def e_typing_thread_typing.intros(8)[of s \<C>'' "[]" t2s t2s "$*es"]
    apply simp
    by (metis append.right_neutral assms(7) b_e_type_empty b_e_weakening e_type_empty e_typing_thread_typing.intros(1) empty)
  moreover
  have "list_all (\<lambda> t. t \<noteq> T_bot) tvs"
    by (metis (mono_tags, lifting) assms(3) list_all2_lengthD list_all_length nth_map tvs_def(3) typeof_not_bot typing_map_typeof vs_tvs)
  ultimately have t_eqs:"t1s = tvs"
    using tvs_def(1,2) ts_c_def(1) instr_subtyping_append_type_eq
    by (metis append_Nil)
  have 2:"tfs = map typeof zs"
    using n_zeros_typeof assms(8)
    by fast
  have zs_tfs: "list_all2 (\<lambda> v t. v_typing s v t) zs tfs"
    using n_zeroes_v_typing
    using assms(8) by blast
  have "t1s = map typeof vs"
    using typing_map_typeof assms(3) tvs_def t_eqs
    by fastforce
  hence "(t1s @ tfs) = map typeof (vs @ zs)"
    using 2
    by simp
  hence "list_all2 (\<lambda> v t. v_typing s v t) (vs @ zs) (t1s @ tfs)"
    using list_all2_appendI t_eqs vs_tvs zs_tfs by blast
  hence "frame_typing s \<lparr>f_locs = (vs @ zs), f_inst = i\<rparr> (\<C>'\<lparr>local := t1s @ tfs\<rparr>)"
    using frame_typing.intros ts_c_def(2)
    by fastforce
  then have "s\<bullet>Some t2s \<tturnstile> \<lparr> f_locs=(vs @ zs), f_inst=i \<rparr>;([Label m [] ($*es)]) : t2s"
    using e_typing_thread_typing.intros(9) c''_def 1 
    by blast
  thus ?thesis
    using e_typing_thread_typing.intros(3,6) ts_c_def t_eqs(1) assms(2,7) instr_subtyping_comp tvs_def(1) by blast
qed

lemma types_preserved_invoke_host_some:
  assumes "s\<bullet>\<C> \<turnstile> ves @ [Invoke i_cl] : (ts _> ts')"
          "(funcs s!i_cl) = Func_host (t1s _> t2s) (Host_func f)"
          "ves = $C* vcs"
          "length vcs = n"
          "length t1s = n"
          "length t2s = m"
          "host_func_apply s (t1s _> t2s) f vcs hs (Some (s', vcs'))"
          "store_typing s"
  shows "s'\<bullet>\<C> \<turnstile> $C* vcs' : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> $C* vcs : (ts _> ts'')" "s\<bullet>\<C> \<turnstile> [Invoke i_cl] : (ts'' _> ts')"
  using assms(1,3) e_type_comp
  by fastforce
  have ves_c:"const_list ves"
    using is_const_list[OF assms(3)]
    by simp
  then obtain tvs where tvs_def:"([] _> tvs) <ti: (ts _> ts'')"
                                "length t1s = length tvs"
                                "s\<bullet>\<C> \<turnstile> $C* vcs : ([] _> tvs)"
    using ts''_def(1) e_type_const_list[of ves s \<C> ts ts''] assms store_extension_refl
    by fastforce
  hence a:  "(t1s _> t2s) <ti: (ts'' _> ts')"
    using e_type_invoke[OF ts''_def(2)] assms(2,8) cl_typing_host
          store_typing_imp_cl_typing
    by fastforce+
  have "list_all (\<lambda> t. t \<noteq> T_bot) tvs"
    by (metis (mono_tags, lifting) assms(4) assms(5) list_all_length nth_map tvs_def(2) tvs_def(3) typeof_not_bot typing_map_typeof)
  then have b: "tvs = t1s"
    using tvs_def(1,2) a instr_subtyping_append_type_eq
    by (metis append.left_neutral)
  hence c: "list_all2 (\<lambda>t v. typeof v = t) tvs vcs"
           "list_all (\<lambda>v. v_typing s v (typeof v)) vcs"
    using e_typing_imp_list_types_agree[of s \<C> vcs "[]" tvs] assms(3) tvs_def(1,3)
          e_typing_imp_list_v_typing[OF ts''_def(1)]

    by fastforce+
  hence "list_all2 (\<lambda>v t. v_typing s v t) vcs (map typeof vcs)"
    by (simp add: list_all2_all_nthI list_all_length)
  then have "list_all2 (\<lambda>t v. v_typing s v t) tvs vcs"
    using v_typing_typeof
    by (metis (no_types, lifting) c(2) assms(4) assms(5) list_all2_all_nthI list_all_length nth_map tvs_def(2) tvs_def(3) typing_map_typeof)
  hence "list_all2 (\<lambda>t v. v_typing s v t) t1s vcs" using  b by simp
  hence "s'\<bullet>\<C> \<turnstile> $C* vcs' : ([] _> t2s)"
    using list_types_agree_imp_e_typing host_func_apply_respect_type[OF _ assms(7)]
    by (meson assms(7) e_typing_thread_typing_store_extension_inv(1) host_func_apply_preserve_store1)
  then show ?thesis
    using e_typing_thread_typing.intros(3)
    using a b instr_subtyping_comp tvs_def(1) by blast
qed

lemma types_imp_concat:
  assumes "s\<bullet>\<C> \<turnstile> es @ [e] @ es' : (ts _> ts')"
          "\<And>tes tes'. ((s\<bullet>\<C> \<turnstile> [e] : (tes _> tes')) \<Longrightarrow> (s\<bullet>\<C> \<turnstile> [e'] : (tes _> tes')))"
  shows "s\<bullet>\<C> \<turnstile> es @ [e'] @ es' : (ts _> ts')"
proof -
  obtain ts'' where "s\<bullet>\<C> \<turnstile> es : (ts _> ts'')"
                    "s\<bullet>\<C> \<turnstile> [e] @ es' : (ts'' _> ts')"
    using e_type_comp_conc1[of _ _ es "[e] @ es'"] assms(1)
    by fastforce
  moreover
  then obtain ts''' where "s\<bullet>\<C> \<turnstile> [e] : (ts'' _> ts''')" "s\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc1[of _ _ "[e]" es' ts'' ts'] assms
    by fastforce
  ultimately
  show ?thesis
    using assms(2) e_type_comp_conc[of _ _ es ts ts'' "[e']" ts''']
                   e_type_comp_conc[of _ _ "es @ [e']" ts ts''']
    by fastforce
qed

lemma type_const_return:
  assumes "Lfilled i lholed (($C*vs) @ [$Return]) LI"
          "(return \<C>) = Some tcs"
          "length tcs = length vs"
          "s\<bullet>\<C> \<turnstile> LI : (ts _> ts')"
  shows "s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tcs)"
  using assms
proof (induction i arbitrary: ts ts' lholed \<C> LI \<C>')
  case 0
  obtain vs' es' where "LI = (($C*vs') @ (($C*vs) @ [$Return]) @ es')"
    using Lfilled.simps[of 0 lholed "(($C*vs) @ [$Return])" LI] 0(1)
    by fastforce
  then obtain ts'' ts''' where "s\<bullet>\<C> \<turnstile> ($C*vs') : (ts _> ts'')"
                               "s\<bullet>\<C> \<turnstile> (($C*vs) @ [$Return]) : (ts'' _> ts''')"
                               "s\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc2[of s \<C> "($C*vs')" "(($C*vs) @ [$Return])" es'] 0(4)
    by fastforce
  then obtain ts_b where ts_b_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : (ts'' _> ts_b)" "s\<bullet>\<C> \<turnstile> [$Return] : (ts_b _> ts''')"
    using e_type_comp_conc1
    by fastforce
  then obtain ts_c ts'''' where ts_c_def:"(ts_c @ tcs _> ts'''') <ti: (ts_b _> ts''')" "(return \<C>) = Some tcs"
    using 0(2) b_e_type_return[of \<C>] unlift_b_e[of s \<C> "[Return]" "ts_b _> ts'''"]
    by fastforce
  obtain tcs' where "([] _> tcs') <ti: (ts'' _> ts_b)" "length vs = length tcs'" "s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tcs')"
    using e_type_consts[OF ts_b_def(1) store_extension_refl]
    by fastforce
  thus ?case
    using 0(3) ts_c_def
    by (metis append.simps(1) e_typing_thread_typing.intros(3) instr_subtyping_append_t_list_subtyping instr_subtyping_def t_list_subtyping_refl tf.sel)
next
  case (Suc i)
  obtain vs' n l les les' LK where es_def:"lholed = (LRec vs' n les l les')"
                                           "Lfilled i l (($C*vs) @ [$Return]) LK"
                                           "LI = (($C* vs') @ [Label n les LK] @ les')"
    using Lfilled.simps[of "(Suc i)" lholed "(($C*vs) @ [$Return])" LI] Suc(2)
    by fastforce
  then obtain ts'' ts''' where "s\<bullet>\<C> \<turnstile> [Label n les LK] : (ts'' _> ts''')"
    using e_type_comp_conc2[of s \<C> "$C*vs'" "[Label n les LK]" les'] Suc(5)
    by fastforce
  then obtain tls t2s where
       "([] _> t2s) <ti: (ts'' _> ts''')"
       "length tls = n"
       "s\<bullet>\<C> \<turnstile> les : (tls _> t2s)"
       "s\<bullet>\<C>\<lparr>label := [tls] @ label \<C>\<rparr> \<turnstile> LK : ([] _> t2s)"
       "return (\<C>\<lparr>label := [tls] @ label \<C>\<rparr>) = Some tcs"
    using e_type_label[of s \<C> n les LK ts'' ts'''] Suc(3)
    by fastforce
  then show ?case
    using Suc(1) assms(3) es_def(2)
    by blast
qed

lemma types_preserved_return:
  assumes "\<lparr>[Frame n f LI]\<rparr> \<leadsto> \<lparr>($C*vs)\<rparr>"
          "s\<bullet>\<C> \<turnstile> [Frame n f LI] : (ts _> ts')"
          "length vs = n"
          "Lfilled j lholed (($C*vs) @ [$Return]) LI"
  shows "s\<bullet>\<C> \<turnstile> ($C*vs) : (ts _> ts')"
proof -
  obtain tls \<C>' \<C>i where l_def:
                        "inst_typing s (f_inst f) \<C>i"
                        "\<C>' = \<C>i\<lparr>local := (map typeof (f_locs f)), return := Some tls\<rparr>"
                        "s\<bullet>\<C>' \<turnstile> LI : ([] _> tls)"
                        "([] _> tls) <ti: (ts _> ts')"
                        "length tls = n"
    using e_type_local[OF assms(2)]
    by blast
  hence "s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> tls)"
    using type_const_return[OF assms(4) _ _ l_def(3)] assms(3)
    by simp
  thus ?thesis
    using e_typing_thread_typing.intros(3) l_def(4)
    by fastforce
qed

lemma type_const_br:
  assumes "Lfilled i lholed (($C*vs) @ [$Br (i+k)]) LI"
          "length (label \<C>) > k"
          "(label \<C>)!k = tcs"
          "length tcs = length vs"
          "s\<bullet>\<C> \<turnstile> LI : (ts _> ts')"
  shows "s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tcs)"
  using assms
proof (induction i arbitrary: k ts ts' lholed \<C> LI \<C>')
  case 0
  obtain vs' es' where "LI = (vs' @ (($C*vs) @ [$Br (0+k)]) @ es')"
    using Lfilled.simps[of 0 lholed "(($C*vs) @ [$Br (0 + k)])" LI] 0(1)
    by fastforce
  then obtain ts'' ts''' where "s\<bullet>\<C> \<turnstile> vs' : (ts _> ts'')"
                               "s\<bullet>\<C> \<turnstile> (($C*vs) @ [$Br (0+k)]) : (ts'' _> ts''')"
                               "s\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc2[of s \<C> vs' "(($C*vs) @ [$Br (0+k)])" es'] 0(5)
    by fastforce
  then obtain ts_b where ts_b_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : (ts'' _> ts_b)" "s\<bullet>\<C> \<turnstile> [$Br (0+k)] : (ts_b _> ts''')"
    using e_type_comp_conc1
    by fastforce
  then obtain ts_c ts'''' where ts_c_def: "(ts_c @ tcs _> ts'''') <ti: (ts_b _> ts''')" "(label \<C>)!k = tcs"
    using 0(3) b_e_type_br[of \<C> "Br (0 + k)"] unlift_b_e[of s \<C> "[Br (0 + k)]" "ts_b _> ts'''"]
    by fastforce
  obtain tcs' where "([] _> tcs') <ti: (ts'' _> ts_b)" "length vs = length tcs'" "s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tcs')"
    using ts_b_def(1) e_type_consts store_extension_refl
    by fastforce
  thus ?case
    using 0(4) ts_c_def
    by (metis append.simps(1) e_typing_thread_typing.intros(3) instr_subtyping_append_t_list_subtyping instr_subtyping_def t_list_subtyping_refl tf.sel)
next
  case (Suc i k ts ts' lholed \<C> LI)
  obtain vs' n l les les' LK where es_def:"lholed = (LRec vs' n les l les')"
                                           "Lfilled i l (($C*vs) @ [$Br (i + (Suc k))]) LK"
                                           "LI = (($C*vs') @ [Label n les LK] @ les')"
    using Lfilled.simps[of "(Suc i)" lholed "(($C*vs) @ [$Br ((Suc i) + k)])" LI] Suc(2)
    by fastforce
  then obtain ts'' ts''' where "s\<bullet>\<C> \<turnstile> [Label n les LK] : (ts'' _> ts''')"
    using e_type_comp_conc2[of s \<C> "($C*vs')" "[Label n les LK]" les'] Suc(6)
    by fastforce
  moreover
  then obtain lts \<C>'' ts'''' where "s\<bullet>\<C>'' \<turnstile> LK : ([] _> ts'''')" "\<C>'' = \<C>\<lparr>label := [lts] @ (label \<C>)\<rparr>"
                             "length (label \<C>'') > (Suc k)"
                             "(label \<C>'')!(Suc k) = tcs"
    using e_type_label[of s \<C> n les LK ts'' ts'''] Suc(3,4)
    by fastforce
  then show ?case
    using Suc(1) es_def(2) assms(4)
    by fastforce
qed

lemma types_preserved_br:
  assumes "\<lparr>[Label n es0 LI]\<rparr> \<leadsto> \<lparr>($C*vs) @ es0\<rparr>"
          "s\<bullet>\<C> \<turnstile> [Label n es0 LI] : (ts _> ts')"
          "length vs = n"
          "Lfilled i lholed (($C*vs) @ [$Br i]) LI"
  shows "s\<bullet>\<C> \<turnstile> (($C*vs) @ es0) : (ts _> ts')"
proof -
  obtain tls t2s \<C>' where l_def:"([] _> t2s) <ti: (ts _> ts')"
                            "(s\<bullet>\<C> \<turnstile> es0 : (tls _> t2s))"
                            "\<C>' = \<C>\<lparr>label := [tls] @ (label \<C>)\<rparr>"
                            "length (label \<C>') > 0"
                            "(label \<C>')!0 = tls"
                            "length tls = n"
                            "(s\<bullet>\<C>\<lparr>label := [tls] @ (label \<C>)\<rparr> \<turnstile> LI : ([] _> t2s))"
    using e_type_label[of s \<C> n es0 LI ts ts'] assms(2)
    by fastforce
  hence "s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> tls)"
    using assms(3-4) type_const_br[of i lholed "vs" 0 LI \<C>' tls]
    by fastforce
  thus ?thesis
    using l_def(1,2) e_type_comp_conc e_typing_thread_typing.intros(3)
    by blast
qed

lemma store_local_label_empty:
  assumes "inst_typing s i \<C>"
  shows "label \<C> = []" "local \<C> = []"
  using assms
  unfolding inst_typing.simps
  by auto

lemma types_preserved_b_e1:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
          "store_typing s"
          "s\<bullet>\<C> \<turnstile> es : (ts _> ts')"
  shows "s\<bullet>\<C> \<turnstile> es' : (ts _> ts')"
  using assms(1)
proof (cases rule: reduce_simple.cases)
  case (unop c oop)
  thus ?thesis
    using assms(1,3) types_preserved_unop_testop_cvtop
    by simp
next
  case (binop_Some op c1 c2 c)
  thus ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (binop_None op c1 c2)
  then show ?thesis
    by (simp add: e_typing_thread_typing.intros(5))
next
  case (testop c testop)
  then show ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (relop c1 c2 op)
  then show ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (convert_Some t1 v t2 sx v')
  then show ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (convert_None t1 v t2 sx)
  then show ?thesis
    using e_typing_thread_typing.intros(5)
    by simp
next
  case (reinterpret t1 v t2)
  then show ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (unop_vec v op)
  then show ?thesis
    using assms types_preserved_unop_vec
    by simp
next
  case (binop_vec_Some op v1 v2 v)
 then show ?thesis
    using assms types_preserved_binop_vec
    by simp
next
  case (binop_vec_None op v1 v2)
  then show ?thesis
    by (simp add: e_typing_thread_typing.intros(5))
next
  case (ternop_vec v1 v2 v3 op)
 then show ?thesis
    using assms types_preserved_ternop_vec
    by simp
next
  case (test_vec v op)
 then show ?thesis
    using assms types_preserved_test_vec
    by simp
next
  case (shift_vec v n op)
 then show ?thesis
    using assms types_preserved_shift_vec
    by simp
next
  case (splat_vec v sv)
 then show ?thesis
    using assms types_preserved_splat_vec
    by simp
next
  case (extract_vec v sv sx i)
 then show ?thesis
    using assms types_preserved_extract_vec
    by simp
next
  case (replace_vec v vn sv i)
 then show ?thesis
    using assms types_preserved_replace_vec
    by simp
next
  case unreachable
  then show ?thesis
    using e_typing_thread_typing.intros(5)
    by simp
next
  case nop
  then have "\<C> \<turnstile> [Nop] : (ts _> ts')"
    using assms(3) unlift_b_e
    by simp
  then show ?thesis
    by (simp add: b_e_type_nop e_type_empty local.nop(2))
next
  case (drop v)
  then show ?thesis
    using assms(1, 3) types_preserved_drop
    by simp
next
  case (select_false n v1 v2 t_tag)
  then have 1: "\<lparr>[$C v1, $C v2, $C (V_num (ConstInt32 n)), $Select t_tag]\<rparr> \<leadsto> \<lparr>[$C v2]\<rparr>"
    using assms(1)
    by (simp add: v_to_e_def)
  have "s\<bullet>\<C> \<turnstile> [$C v2] : (ts _> ts')" using types_preserved_select[OF 1]
    using assms(3) local.select_false(1) v_to_e_def by auto
  then show ?thesis
    using local.select_false(2) by fastforce
next
  case (select_true n v1 v2 t_tag)
  then have 1: "\<lparr>[$C v1, $C v2, $C (V_num (ConstInt32 n)), $Select t_tag]\<rparr> \<leadsto> \<lparr>[$C v1]\<rparr>"
    using assms(1)
    by (simp add: v_to_e_def)
  have "s\<bullet>\<C> \<turnstile> [$C v1] : (ts _> ts')" using types_preserved_select[OF 1]
    using assms(3) local.select_true(1) v_to_e_def by auto
  then show ?thesis
    using local.select_true(2) by fastforce
next
  case (if_false tf e1s e2s)
  then show ?thesis
    using assms(1, 3) types_preserved_if
    by simp
next
  case (if_true n tf e1s e2s)
  then show ?thesis
    using assms(1, 3) types_preserved_if
    by simp
next
  case (label_const ts es)
  then show ?thesis
    using assms(1, 3) types_preserved_label_value
    by simp
next
  case (label_trap ts es)
  then show ?thesis
    by (simp add: e_typing_thread_typing.intros(5))
next
  case (br vs n i lholed LI es)
  then show ?thesis
    using assms(1, 3) types_preserved_br
    by fastforce
next
  case (br_if_false n i)
  then show ?thesis
    using assms(1, 3) types_preserved_br_if
    by fastforce
next
  case (br_if_true n i)
  then show ?thesis
    using assms(1, 3) types_preserved_br_if
    by fastforce
next
  case (br_table is' c i')
  then show ?thesis
    using assms(1, 3) types_preserved_br_table
    by fastforce
next
  case (br_table_length is' c i')
  then show ?thesis
    using assms(1, 3) types_preserved_br_table
    by fastforce
next
  case (local_const i vs)
  then show ?thesis
    using assms(1, 3) types_preserved_local_const
    by fastforce
next
  case (local_trap i vs)
  then show ?thesis
    by (simp add: e_typing_thread_typing.intros(5))
next
  case (return n j lholed es f)
  then show ?thesis
    using assms(1, 3) types_preserved_return
    by fastforce
next
  case (local_tee v i)
  then show ?thesis
    using assms(1, 3) types_preserved_local_tee
    by simp
next
  case (trap lholed)
  then show ?thesis
    by (simp add: e_typing_thread_typing.intros(5))
next
  case (null t)
  then show ?thesis using assms(1, 3) types_preserved_null by simp
next
  case (is_null_true v_r)
  then show ?thesis unfolding is_null_ref_def using assms(1, 3) wasm_bool_def types_preserved_is_null
    by (simp add: v_to_e_def)
next
  case (is_null_false v_r)
  then show ?thesis using assms(1, 3) wasm_bool_def v_to_e_def
    by (simp add: types_preserved_is_null)
qed

lemma types_preserved_b_e:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
          "store_typing s"
          "s\<bullet>None \<tturnstile> f;es : ts"
  shows "s\<bullet>None \<tturnstile> f;es' : ts"
proof -
  obtain tvs \<C> \<C>i where defs:"list_all2 (\<lambda> v t. v_typing s v t) (f_locs f) tvs"
                             "inst_typing s (f_inst f) \<C>i"
                             "\<C> = \<C>i\<lparr>local := (tvs), return := None\<rparr>"
                             "s\<bullet>\<C> \<turnstile> es : ([] _> ts)"
    using assms(3)
    unfolding thread_typing.simps frame_typing.simps
    by auto
  have "s\<bullet>\<C> \<turnstile> es' : ([] _> ts)"
    using assms(1,2) defs(4) types_preserved_b_e1
    by simp
  thus ?thesis
    using defs
    unfolding thread_typing.simps frame_typing.simps
    by force
qed

lemma types_preserved_store:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k), $C v, $Store t tp a off] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
        "typeof v = T_num t"
proof -
  obtain ts'' ts''' where ts_def:"s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k)] : (ts _> ts'')"
                                 "s\<bullet>\<C> \<turnstile> [$C v] : (ts'' _> ts''')"
                                 "s\<bullet>\<C> \<turnstile> [$Store t tp a off] : (ts''' _> ts')"
    using assms e_type_comp_conc2[of s \<C> "[$EConstNum (ConstInt32 k)]" "[$C v]" "[$Store t tp a off]"]
    by fastforce
  then have "([] _> [T_num T_i32]) <ti: (ts _> ts'')"
    using b_e_type_cnum[of \<C> "EConstNum (ConstInt32 k)" "ts" ts'']
          unlift_b_e[of s \<C> "[EConstNum (ConstInt32 k)]" "(ts _> ts'')"]
    unfolding typeof_def typeof_num_def
    by fastforce
  hence 1: "([] _> [(T_num T_i32), (typeof v)]) <ti: (ts _> ts''')"
    using ts_def(2) store_extension_refl
    using instr_subtyping_concat type_const_v_typing(1) by fastforce
  have 2: "([T_num T_i32, T_num t] _> []) <ti: (ts''' _> ts')"
    using b_e_type_store(1)[of \<C> "Store t tp a off" ts''' ts'] ts_def(3) unlift_b_e[of s \<C> "[Store t tp a off]" "(ts''' _> ts')"]
    by (metis to_e_list_1)
  have 3: "typeof v = T_num t"
    using 1 2 instr_subtyping_append2_type_eq
    by (metis append_butlast_last_id instr_subtyping_append1_type_eq last.simps list.distinct(1) typeof_not_bot)
  have "([] _> []) <ti: (ts _> ts')"
    using 1 2 3
    by (metis instr_subtyping_comp)
  thus "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')" "typeof v = T_num t"
    using b_e_type_empty[of \<C> "ts" "ts'"] e_typing_thread_typing.intros(1) 3
    by fastforce+
qed

lemma types_preserved_store_vec:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $Store_vec sv a off] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
proof -
  obtain ts'' ts''' where ts_def:"s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k)] : (ts _> ts'')"
                                 "s\<bullet>\<C> \<turnstile> [$EConstVec (ConstVec128 v)] : (ts'' _> ts''')"
                                 "s\<bullet>\<C> \<turnstile> [$Store_vec sv a off] : (ts''' _> ts')"
    using assms e_type_comp_conc2[of s \<C> "[$EConstNum (ConstInt32 k)]" "[$EConstVec (ConstVec128 v)]" "[$Store_vec sv a off]"]
    by fastforce
  then have "([] _> [T_num T_i32]) <ti: (ts _> ts'')"
    using b_e_type_cnum[of \<C> "EConstNum (ConstInt32 k)" "ts" ts'']
          unlift_b_e[of s \<C> "[EConstNum (ConstInt32 k)]" "(ts _> ts'')"]
    unfolding typeof_def typeof_num_def
    by fastforce
  hence "([] _> [(T_num T_i32), (T_vec T_v128)]) <ti: (ts _> ts''')"
    using ts_def(2) b_e_type_cvec[of \<C> "EConstVec (ConstVec128 v)" ts'' ts''']
          unlift_b_e[of s \<C> "[EConstVec (ConstVec128 v)]" "(ts'' _> ts''')"]
           store_extension_refl instr_subtyping_concat
          by (metis (mono_tags, lifting) append_Cons append_Nil t_vec.exhaust to_e_list_1)
  hence "([] _> []) <ti: (ts _> ts')"
    using ts_def(3) b_e_type_store_vec[of \<C> "Store_vec sv a off" ts''' ts']
          unlift_b_e[of s \<C> "[Store_vec sv a off]" "(ts''' _> ts')"]
    by (metis instr_subtyping_comp to_e_list_1)
  thus "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    using b_e_type_empty[of \<C> "ts" "ts'"] e_typing_thread_typing.intros(1)
    by fastforce+
qed

lemma types_preserved_memory_size:
  assumes "s\<bullet>\<C> \<turnstile> [$(Memory_size)] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 c)] : (ts _> ts')"
proof -
  have "([] _> [T_num T_i32]) <ti: (ts _> ts')"
    using assms b_e_type_memory_size unlift_b_e[of s \<C> "[Memory_size]"]
    by fastforce
  thus ?thesis
    using b_e_typing.const_num[of \<C> "ConstInt32 c"] e_typing_thread_typing.intros(1,3)
    unfolding typeof_def typeof_num_def
    by fastforce
qed

lemma types_preserved_memory_grow:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 c), $Memory_grow] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 c')] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 c)] : (ts _> ts'')" 
                             "s\<bullet>\<C> \<turnstile> [$Memory_grow] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  have "([] _> [T_num T_i32]) <ti: (ts _> ts'')"
    using b_e_type_cnum[of \<C> "EConstNum (ConstInt32 c)" ts ts'']
          unlift_b_e[of s \<C> "[EConstNum (ConstInt32 c)]"] ts''_def(1)
    unfolding typeof_def typeof_num_def
    by fastforce
  moreover
  hence "([T_num T_i32] _> [T_num T_i32]) <ti: (ts'' _> ts')"
    using ts''_def b_e_type_memory_grow[of _ _ ts'' ts'] unlift_b_e[of s \<C> "[Memory_grow]"]
    by fastforce
  ultimately
  show "s'\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 c')] : (ts _> ts')"
    by (metis const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) instr_subtyping_comp to_e_list_1 typeof_num_def v_num.case(1))
qed

lemmas types_preserved_global_set = types_preserved_global_set_aux

lemma types_preserved_load:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k), $Load t tp a off] : (ts _> ts')"
          "typeof v = T_num t"
  shows "s'\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k)] : (ts _> ts'')" 
                             "s\<bullet>\<C> \<turnstile> [$Load t tp a off] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence "([] _> [(T_num T_i32)]) <ti: (ts _> ts'')"
    using b_e_type_cnum unlift_b_e[of s \<C> "[EConstNum (ConstInt32 k)]"]
    unfolding typeof_def typeof_num_def
    by fastforce
  hence ts_def:"([] _> [T_num t]) <ti: (ts _> ts')" "load_store_t_bounds a (option_projl tp) t" 
    using ts''_def(2) b_e_type_load unlift_b_e[of s \<C> "[Load t tp a off]"] instr_subtyping_comp to_e_list_1
    by metis+
  moreover
  have "v_typing s' v (T_num t)" using v_typing.simps assms(2)
    by (metis t.distinct(3) typeof_def v.exhaust v.simps(10) v.simps(11) v.simps(12))
  ultimately
  show "s'\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
    using e_typing_thread_typing.intros(3) types_agree_imp_e_typing by blast
qed

lemma types_preserved_load_vec:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k), $Load_vec lv a off] : (ts _> ts')"
          "typeof v = T_vec T_v128"
  shows "s'\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k)] : (ts _> ts'')" 
                             "s\<bullet>\<C> \<turnstile> [$Load_vec lv a off] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence "([] _> [(T_num T_i32)]) <ti: (ts _> ts'')"
    using b_e_type_cnum unlift_b_e[of s \<C> "[EConstNum (ConstInt32 k)]"]
    unfolding typeof_def typeof_num_def
    by fastforce
  hence ts_def:"([] _> [(T_vec T_v128)]) <ti: (ts _> ts')" "load_vec_t_bounds lv a" 
    using ts''_def(2) b_e_type_load_vec unlift_b_e[of s \<C> "[Load_vec lv a off]"] instr_subtyping_comp to_e_list_1
    by metis+
  moreover
  have "v_typing s' v (T_vec T_v128)" using v_typing.simps assms(2)
    by (metis (full_types) t.distinct(7) t_vec.exhaust typeof_def v.exhaust v.simps(10) v.simps(12))
  ultimately
  show "s'\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
    using e_typing_thread_typing.intros(3) types_agree_imp_e_typing by blast
qed

lemma types_preserved_load_lane_vec:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $Load_lane_vec svi i a off] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [$EConstVec (ConstVec128 v')] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v)] : (ts _> ts'')" 
                             "s\<bullet>\<C> \<turnstile> [$Load_lane_vec svi i a off] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence "[] _> [(T_num T_i32), (T_vec T_v128)] <ti: (ts _> ts'')"
    using b_e_type_value2_nv unlift_b_e[of s \<C> "[EConstNum (ConstInt32 k), EConstVec (ConstVec128 v)]"]
    unfolding typeof_def typeof_num_def typeof_vec_def
    by fastforce
  hence ts_def:"([] _> [T_vec T_v128]) <ti: (ts _> ts')"
    using ts''_def(2) b_e_type_load_lane_vec unlift_b_e[of s \<C> "[Load_lane_vec svi i a off]"] instr_subtyping_comp to_e_list_1
    by metis+
  then
  show "s'\<bullet>\<C> \<turnstile> [$EConstVec (ConstVec128 v')] : (ts _> ts')"
    by (metis (full_types) const_vec e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) t_vec.exhaust to_e_list_1)
qed

lemma types_preserved_local_get:
  assumes "s\<bullet>\<C> \<turnstile> [$Local_get i] : (ts _> ts')"
          "length vi = i"
          "(local \<C>) = map typeof (vi @ [v] @ vs)"
          "v_typing s v (typeof v)"
          "store_extension s s'"
  shows "s'\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
proof -
  have "(local \<C>)!i = typeof v"
    using assms(2,3)
    by (metis (no_types) append_Cons length_map list.simps(9) map_append nth_append_length)
  hence a: "([] _> [typeof v]) <ti: (ts _> ts')"
    using assms(1) unlift_b_e[of s \<C> "[Local_get i]"] b_e_type_local_get
    by fastforce
  then have "v_typing s v (typeof v)"
    using assms(4) by blast
  thus ?thesis
    using a assms(5) e_typing_thread_typing.intros(3) e_typing_thread_typing_store_extension_inv(1) types_agree_imp_e_typing by fastforce
qed

lemma types_preserved_local_set:
  assumes "s\<bullet>\<C> \<turnstile> [$C v', $Local_set i] : (ts _> ts')"
          "length vi = i"
          "(local \<C>) = map typeof (vi @ [v] @ vs)"
  shows "(s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')) \<and> map typeof (vi @ [v] @ vs) = map typeof (vi @ [v'] @ vs)"
proof -
  have v_type:"(local \<C>)!i = typeof v"
    using assms(2,3)
    by (metis (no_types) append_Cons length_map list.simps(9) map_append nth_append_length)
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$C v'] : (ts _> ts'')" 
                             "s\<bullet>\<C> \<turnstile> [$Local_set i] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence 1: "([] _> [typeof v']) <ti: (ts _> ts'')"
    using e_type_const_new store_extension_refl by blast
  hence "typeof v = typeof v'"
    using v_type b_e_type_local_set[of \<C> "Local_set i" ts'' ts'] ts''_def(2) unlift_b_e[of s \<C> "[Local_set i]"]
    by (metis append_self_conv2 instr_subtyping_append1_type_eq to_e_list_1 typeof_not_bot)
  moreover have "([] _> []) <ti: (ts _> ts')" using 1
    by (metis b_e_type_local_set(1) calculation instr_subtyping_comp to_e_list_1 ts''_def(2) unlift_b_e v_type)
  ultimately show ?thesis
    using b_e_type_empty[of \<C> "ts" "ts'"] e_typing_thread_typing.intros(1)
    by fastforce
qed

lemma types_preserved_local_set':
  assumes "s\<bullet>\<C> \<turnstile> [$C v', $Local_set i] : (ts _> ts')"
          "length vi = i"
          "(local \<C>) = map typeof (vi @ [v] @ vs)"
          "list_all2 (v_typing s) (vi @ [v] @ vs) (local \<C>)"
  shows "(s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')) \<and> map typeof (vi @ [v] @ vs) = map typeof (vi @ [v'] @ vs) \<and> list_all2 (v_typing s) (vi @ [v'] @ vs) (local \<C>)"
proof -
  have v_type:"(local \<C>)!i = typeof v"
    using assms(2,3)
    by (metis (no_types) append_Cons length_map list.simps(9) map_append nth_append_length)
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$C v'] : (ts _> ts'')" 
                             "s\<bullet>\<C> \<turnstile> [$Local_set i] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence 1: "([] _> [typeof v']) <ti: (ts _> ts'')"
    using e_type_const_new store_extension_refl by blast
  hence 2: "typeof v = typeof v'"
    using v_type b_e_type_local_set[of \<C> "Local_set i" ts'' ts'] ts''_def(2) unlift_b_e[of s \<C> "[Local_set i]"]
    by (metis append_self_conv2 instr_subtyping_append1_type_eq to_e_list_1 typeof_not_bot)
  have 3: "([] _> []) <ti: (ts _> ts')" using 1
    by (metis b_e_type_local_set(1) 2 instr_subtyping_comp to_e_list_1 ts''_def(2) unlift_b_e v_type)
  have "v_typing s v' (typeof v')"
    using ts''_def(1) type_const_v_typing(2) by fastforce
  then have "v_typing s v' (local \<C>!i)"
    by (simp add: 2 v_type)
  then have "list_all2 (v_typing s) (vi @ [v'] @ vs) (local \<C>)"
  proof -
    assume v'_typing: "v_typing s v' (local \<C> ! i)"
    have a: "\<And> n. n < length (vi @ [v'] @ vs) \<Longrightarrow> v_typing s ((vi @ [v'] @ vs)!n) (local \<C>!n)"
    proof -
      fix n
      assume n_length: "n < length (vi @ [v'] @ vs)"
      then show "v_typing s ((vi @ [v'] @ vs)!n) (local \<C>!n)"
      proof(cases "n =i")
        case True
        then show ?thesis using v'_typing assms(2) by fastforce
      next
        case False
        then have "((vi @ [v'] @ vs) ! n) = ((vi @ [v] @ vs) ! n)"
          using assms(2) n_length
          by (metis Cons_eq_appendI diffs0_imp_equal not_gr_zero nth_Cons_pos nth_append zero_less_diff)
        then have "v_typing s ((vi @ [v'] @ vs) ! n) = v_typing s ((vi @ [v] @ vs) ! n) "
          by metis
        then show ?thesis
          using assms(4) list_all2_nthD n_length by fastforce
      qed
    qed
    have b: "length (vi @ [v'] @ vs) = length (local \<C>)"
      by (simp add: assms(3))
    then show ?thesis
      using list_all2_all_nthI a b by metis
  qed
  thus ?thesis
    using b_e_type_empty[of \<C> "ts" "ts'"] e_typing_thread_typing.intros(1)
    by (simp add: e_type_empty 1 2 3)
qed

lemma types_preserved_global_get:
  assumes "typeof (sglob_val s i j) = tg_t (global \<C> ! j)"
          "s\<bullet>\<C> \<turnstile> [$Global_get j] : (ts _> ts')"
          "v_typing s (sglob_val s i j) (typeof (sglob_val s i j))"
          "store_extension s s'"
  shows "s'\<bullet>\<C> \<turnstile> [$C sglob_val s i j] : (ts _> ts')"
proof -
  have "([] _> [tg_t (global \<C> ! j)]) <ti: (ts _> ts')"
    using b_e_type_global_get assms(2) unlift_b_e[of _ _ "[Global_get j]"]
    by fastforce
  thus ?thesis
    using assms e_typing_thread_typing.intros(3) e_typing_thread_typing_store_extension_inv(1) types_agree_imp_e_typing by fastforce
qed

lemma types_preserved_memory_init:
  assumes
    "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n), $Memory_init x] : (ts _> ts')"

  shows
    "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2),
           $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 i3),
           $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5),
           $Memory_init x] : (ts _> ts')"
proof -
  have 1: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)] @
          [$Memory_init x] : (ts _> ts')" using assms(1) by auto
  obtain ts'' vs where ts''_def:
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    "($C* vs) = [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)]"
    "s\<bullet>\<C> \<turnstile> $C*vs : (ts _> ts'')"
    "s\<bullet>\<C> \<turnstile> [$Memory_init x] : (ts'' _> ts')"
    using  e_type_comp_conc1[OF 1] v_to_e_def by auto
  have "[] _> [T_num T_i32, T_num T_i32, T_num T_i32] <ti: ts _> ts''"
    using e_typing_imp_list_v_typing(2)[OF ts''_def(3)] unfolding ts''_def(1) by(simp add: typeof_def typeof_num_def)
  moreover have 3: "([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts'' _> ts')"
                   "x < length (data \<C>)"
                   "1 \<le> length (memory \<C>)"
    using e_type_memory_init[OF ts''_def(4)] by simp_all
  ultimately show ts_empty: "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    using e_type_empty instr_subtyping_comp by blast
  then have 4: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2),
           $Store T_i32 (Some Tp_i8) 0 0] : (ts _> ts)"
  proof -
    have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1)] : ([] _> [T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i2)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) append_Cons append_self_conv2 e_weakening
      by metis+
    have b: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2)] : ([] _> [T_num T_i32, T_num T_i32])"
      using e_type_comp_conc[OF a(1,2)] by simp
    have "load_store_t_bounds 0 (Some Tp_i8) T_i32"
      using t_num_length_def is_int_t_num_def load_store_t_bounds_def tp_num_length_def by simp
    then have c: "s\<bullet>\<C> \<turnstile> [$Store T_i32 (Some Tp_i8) 0 0] : ([T_num T_i32, T_num T_i32] _> [])"
      using  e_typing_thread_typing.intros(1) store 3(3) by fastforce
    show ?thesis using e_type_comp_conc[OF b c] e_weakening by fastforce
  qed
  then have 5: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3),
           $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5),
           $Memory_init x] : (ts _> ts)"
  proof -
    have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3)] : ([] _> [T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i4)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i5)] : ([T_num T_i32, T_num T_i32] _> [T_num T_i32, T_num T_i32,T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) append_Cons append_self_conv2 e_weakening
      by metis+
    then have b: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5)] : ([] _> [T_num T_i32, T_num T_i32, T_num T_i32])"
      using e_type_comp_conc[OF e_type_comp_conc[OF a(1,2)] a(3)] by simp
    have c: "s\<bullet>\<C> \<turnstile> [$Memory_init x] : ([T_num T_i32, T_num T_i32,T_num T_i32] _> [])"
      using b_e_typing.memory_init[OF 3(3,2)]
      using e_typing_thread_typing.intros(1) to_e_list_1 by metis
    then show ?thesis using e_type_comp_conc[OF b c] e_weakening by fastforce
  qed
  show "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2),
           $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 i3),
           $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5),
           $Memory_init x] : (ts _> ts')"
    using e_type_comp_conc[OF 4 5] e_type_comp_conc ts_empty by fastforce
qed

lemma types_preserved_memory_copy:
  assumes
    "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n), $Memory_copy] : (ts _> ts')"
  shows
    "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Load T_i32 (Some (Tp_i8, U)) 0 0,
           $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 (i3)),
           $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5), $Memory_copy] : (ts _> ts')"
proof -
  have 1: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)] @
          [$Memory_copy] : (ts _> ts')" using assms(1) by auto
  obtain ts'' vs where ts''_def:
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    "($C* vs) = [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)]"
    "s\<bullet>\<C> \<turnstile> $C*vs : (ts _> ts'')"
    "s\<bullet>\<C> \<turnstile> [$Memory_copy] : (ts'' _> ts')"
    using  e_type_comp_conc1[OF 1] v_to_e_def by auto
  have "[] _> [T_num T_i32, T_num T_i32, T_num T_i32] <ti: ts _> ts''"
    using e_typing_imp_list_v_typing(2)[OF ts''_def(3)] unfolding ts''_def(1) by(simp add: typeof_def typeof_num_def)
  moreover have 3: "([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts'' _> ts')"
                   "1 \<le> length (memory \<C>)"
    using e_type_memory_copy[OF ts''_def(4)] by simp_all
  ultimately show ts_empty: "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    using e_type_empty instr_subtyping_comp by blast
  then have 4: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Load T_i32 (Some (Tp_i8, U)) 0 0,
           $Store T_i32 (Some Tp_i8) 0 0] : (ts _> ts)"
  proof -
    have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1)] : ([] _> [T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i2)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) append_Cons append_self_conv2 e_weakening
      by metis+
    have b: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2)] : ([] _> [T_num T_i32, T_num T_i32])"
      using e_type_comp_conc[OF a(1,2)] by simp
    have load_bounds: "load_store_t_bounds 0 (option_projl (Some (Tp_i8, U))) T_i32"
                      "load_store_t_bounds 0 (Some (Tp_i8)) T_i32"
      using t_num_length_def is_int_t_num_def load_store_t_bounds_def tp_num_length_def option_projl_def
      by (metis (no_types, lifting) One_nat_def dual_order.refl fst_conv less_Suc_numeral option.simps(5) option.simps(9) power_0 pred_numeral_simps(2) t_num.simps(13) tp_num.simps(7) zero_less_numeral)+
    have c: "s\<bullet>\<C> \<turnstile> [$Load T_i32 (Some (Tp_i8, U)) 0 0] : ([T_num T_i32, T_num T_i32] _> [T_num T_i32, T_num T_i32])"
      using  e_typing_thread_typing.intros(1) load 3(2) load_bounds e_weakening[where ?ts = "[T_num T_i32]"] by fastforce
    have d: "s\<bullet>\<C> \<turnstile> [$Store T_i32 (Some Tp_i8) 0 0] : ([T_num T_i32, T_num T_i32] _> [])"
      using  e_typing_thread_typing.intros(1) store 3(2) load_bounds by fastforce
    show ?thesis using e_type_comp_conc[OF e_type_comp_conc[OF b c] d] e_weakening by fastforce
  qed
  then have 5: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3),
           $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5),
           $Memory_copy] : (ts _> ts)"
  proof -
    have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3)] : ([] _> [T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i4)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i5)] : ([T_num T_i32, T_num T_i32] _> [T_num T_i32, T_num T_i32,T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) append_Cons append_self_conv2 e_weakening
      by metis+
    then have b: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5)] : ([] _> [T_num T_i32, T_num T_i32, T_num T_i32])"
      using e_type_comp_conc[OF e_type_comp_conc[OF a(1,2)] a(3)] by simp
    have c: "s\<bullet>\<C> \<turnstile> [$Memory_copy] : ([T_num T_i32, T_num T_i32,T_num T_i32] _> [])"
      using b_e_typing.memory_copy[OF 3(2)]
      using e_typing_thread_typing.intros(1) to_e_list_1 by metis
    then show ?thesis using e_type_comp_conc[OF b c] e_weakening by fastforce
  qed
  show "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Load T_i32 (Some (Tp_i8, U)) 0 0,
           $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 (i3)),
           $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5), $Memory_copy] : (ts _> ts')"
    using e_type_comp_conc[OF 4 5] e_type_comp_conc ts_empty by fastforce
qed

lemma types_preserved_memory_fill:
  assumes
    "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n), $Memory_fill] : ts _> ts'"
  shows
    "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Store T_i32 (Some Tp_i8) 0 0,
           $EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 (i5)),
           $Memory_fill] : ts _> ts'"
proof -
  have 1: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n)] @
          [$Memory_fill] : (ts _> ts')" using assms(1) by auto
  obtain ts'' vs where ts''_def:
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 val), V_num (ConstInt32 n)]"
    "($C* vs) = [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n)]"
    "s\<bullet>\<C> \<turnstile> $C*vs : (ts _> ts'')"
    "s\<bullet>\<C> \<turnstile> [$Memory_fill] : (ts'' _> ts')"
    using  e_type_comp_conc1[OF 1] v_to_e_def by auto
  have "[] _> [T_num T_i32, T_num T_i32, T_num T_i32] <ti: ts _> ts''"
    using e_typing_imp_list_v_typing(2)[OF ts''_def(3)] unfolding ts''_def(1) by(simp add: typeof_def typeof_num_def)
  moreover have 3: "([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts'' _> ts')"
                   "1 \<le> length (memory \<C>)"
    using e_type_memory_fill[OF ts''_def(4)] by simp_all
  ultimately show ts_empty: "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    using e_type_empty instr_subtyping_comp by blast
  then have 4: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Store T_i32 (Some Tp_i8) 0 0] : (ts _> ts)"
  proof -
    have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1)] : ([] _> [T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i2)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) append_Cons append_self_conv2 e_weakening
      by metis+
    have b: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2)] : ([] _> [T_num T_i32, T_num T_i32])"
      using e_type_comp_conc[OF a(1,2)] by simp
    have load_bounds: "load_store_t_bounds 0 (Some (Tp_i8)) T_i32"
      using t_num_length_def is_int_t_num_def load_store_t_bounds_def tp_num_length_def option_projl_def by simp
    have c: "s\<bullet>\<C> \<turnstile> [$Store T_i32 (Some Tp_i8) 0 0] : ([T_num T_i32, T_num T_i32] _> [])"
      using  e_typing_thread_typing.intros(1) store 3(2) load_bounds by fastforce
    show ?thesis using e_type_comp_conc[OF b c] e_weakening by fastforce
  qed
  then have 5: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3),
           $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5),
           $Memory_fill] : (ts _> ts)"
  proof -
    have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3)] : ([] _> [T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i4)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
            "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i5)] : ([T_num T_i32, T_num T_i32] _> [T_num T_i32, T_num T_i32,T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) append_Cons append_self_conv2 e_weakening
      by metis+
    then have b: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5)] : ([] _> [T_num T_i32, T_num T_i32, T_num T_i32])"
      using e_type_comp_conc[OF e_type_comp_conc[OF a(1,2)] a(3)] by simp
    have c: "s\<bullet>\<C> \<turnstile> [$Memory_fill] : ([T_num T_i32, T_num T_i32,T_num T_i32] _> [])"
      using b_e_typing.memory_fill[OF 3(2)]
      using e_typing_thread_typing.intros(1) to_e_list_1 by metis
    then show ?thesis using e_type_comp_conc[OF b c] e_weakening by fastforce
  qed
  show "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Store T_i32 (Some Tp_i8) 0 0,
           $EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 (i5)),
           $Memory_fill] : ts _> ts'"
    using e_type_comp_conc[OF 4 5] e_type_comp_conc ts_empty by fastforce
qed

lemma types_preserved_table_get:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n), $Table_get ti] : ts _> ts'"
          "stab_ind (f_inst f) ti = Some a"
          "load_tabs1 (s.tabs s) a (nat_of_int n) = Some val"
          "store_typing s"
          "inst_typing s (f_inst f) \<C>i"
          "\<C> = \<C>i\<lparr>local := (map typeof (f_locs f)), label := arb_label, return := arb_return\<rparr>"
  shows "s\<bullet>\<C> \<turnstile> [Ref val] : ts _> ts'"
proof -
  obtain ts'' where ts''_def: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n)] : ts _> ts''"
        "s\<bullet>\<C> \<turnstile> [$Table_get ti] : ts'' _> ts'"
    by (metis Cons_eq_append_conv assms(1) e_type_comp_conc1)
  then have 1: "([] _> [T_num T_i32]) <ti: (ts _> ts'')" by (metis e_type_cnum typeof_num_def v_num.case(1))
  then have 2: "([] _> [T_ref (tab_t_reftype (table \<C>!ti))]) <ti: (ts _> ts')"
    by (metis b_e_type_table_get(1) instr_subtyping_comp to_e_list_1 ts''_def(2) unlift_b_e)
  have "ti < length (table \<C>)"
    using assms(1) b_e_type_comp2_unlift b_e_type_table_get(2) by blast
  have "inst_typing s (f_inst f) \<C>i"
    by (simp add: assms(5))
  then have "list_all2 (tabi_agree (tabs s)) (inst.tabs (f_inst f)) (table \<C>i)"
    using inst_typing.cases by fastforce
  then have "tabi_agree (tabs s) ((inst.tabs (f_inst f))!ti) (table \<C>i!ti)"
    by (metis assms(2) list_all2_nthD option.simps(3) stab_ind_def)
  then have "tab_t_reftype (fst ((s.tabs s)!a)) = tab_t_reftype (table \<C>i!ti)"
    by (metis (mono_tags, lifting) assms(2) assms(5) case_prod_unfold inst_typing_imp_tabi_agree split_pairs tab_t.case tab_t.exhaust tab_t_reftype_def tab_subtyping_def tabi_agree_def)
  have "tab_agree s ((s.tabs s)!a)"
  proof -
    have "list_all (tab_agree s) (tabs s)"
      using assms(4) store_typing.simps by blast
    moreover have "a < length (tabs s)"
      using assms(2) assms(5) inst_typing_imp_tabi_agree tabi_agree_def by blast
    then show "tab_agree s ((s.tabs s)!a)"
      using assms(4) store_typing_in_tab_agree by blast
  qed
  then have "list_all (\<lambda> vr. ref_typing s vr (tab_t_reftype (fst ((s.tabs s)!a)))) (snd ((s.tabs s)!a))"
    by (metis (mono_tags, lifting) case_prod_beta' list_all_length tab_agree_def tab_t.case tab_t.exhaust tab_t_reftype_def)
  then have "ref_typing s ((snd ((s.tabs s)!a))!(nat_of_int n)) (tab_t_reftype (fst ((s.tabs s)!a)))"
    by (metis assms(3) list_all_length load_tabs1_def option.simps(3))
  then have "ref_typing s val (tab_t_reftype (fst ((s.tabs s)!a)))"
    by (metis assms(3) load_tabs1_def not_Some_eq option.inject)
  then have "ref_typing s val (tab_t_reftype (table \<C>i!ti))"
    by (simp add: \<open>tab_t_reftype (fst (s.tabs s ! a)) = tab_t_reftype (table \<C>i ! ti)\<close>)
  have "table \<C> = table \<C>i" by (simp add: assms(6))
  then have "ref_typing s val (tab_t_reftype (table \<C>!ti))"
    using \<open>ref_typing s val (tab_t_reftype (table \<C>i ! ti))\<close> by force
  then show "s\<bullet>\<C> \<turnstile> [Ref val] : (ts _> ts')"
    by (metis 2 e_typing_thread_typing.intros(3) e_typing_thread_typing.intros(4))
qed

lemma types_preserved_table_set:
  assumes
    "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n), Ref vr, $Table_set ti] : (ts _> ts')"
  shows
    "s\<lparr>s.tabs := tabs'\<rparr>\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
  using assms(1) types_preserved_table_set_aux(1) by metis

lemma types_preserved_table_copy:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n), $Table_copy x y] : (ts _> ts')"
  shows "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
        "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Table_get y, $Table_set x,
           $EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4),
           $EConstNum (ConstInt32 i5), $Table_copy x y] : (ts _> ts')"
proof -

  have 1: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)] @
          [$Table_copy x y] : (ts _> ts')" using assms(1) by auto
  obtain ts'' vs where ts''_def:
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    "($C* vs) = [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)]"
    "s\<bullet>\<C> \<turnstile> $C*vs : (ts _> ts'')"
    "s\<bullet>\<C> \<turnstile> [$Table_copy x y] : (ts'' _> ts')"
    using  e_type_comp_conc1[OF 1] v_to_e_def by auto
  have 2: "([] _> [T_num T_i32, T_num T_i32, T_num T_i32]) <ti: (ts _> ts'')"
    using e_typing_imp_list_v_typing(2)[OF ts''_def(3)] unfolding ts''_def(1) by(simp add: typeof_def typeof_num_def)
  moreover have 3: "([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts'' _> ts')"
                   "tab_t_reftype (table \<C>!x) = tab_t_reftype (table \<C>!y)"
    using e_type_table_copy[OF ts''_def(4)] by simp_all
  ultimately show ts_empty: "s\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    using e_type_empty instr_subtyping_comp by blast
  have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Table_get y, $Table_set x] : (ts _> ts)"
  proof -
    have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1)] : ([] _> [T_num T_i32])"
      by (metis typeof_num_def types_agree_imp_e_typing v.case(1) v_num.case(1) v_to_e_def v_typing.intros(1))
    have b: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i2)] : ([T_num T_i32] _> [T_num T_i32,T_num T_i32])"
      using typeof_num_def types_agree_imp_e_typing v.case(1) v_num.case(1) v_to_e_def v_typing.intros(1) e_weakening
      by (metis append_Cons append_self_conv2)
    have "\<C> \<turnstile> [Table_get y] : ([T_num T_i32,T_num T_i32] _> [T_num T_i32, T_ref (tab_t_reftype (table \<C>!y))])"
      using b_e_typing.table_get e_type_table_copy ts''_def(4)
      by (metis Cons_eq_appendI append_self_conv2 b_e_weakening)
    then have c: "s\<bullet>\<C> \<turnstile> [$Table_get y] : ([T_num T_i32,T_num T_i32] _> [T_num T_i32, T_ref (tab_t_reftype (table \<C>!y))])"
      using e_typing_thread_typing.intros(1) to_e_list_1 by metis
    have "\<C> \<turnstile> [Table_set x] : ([T_num T_i32, T_ref (tab_t_reftype (table \<C>!y))] _> [])"
      using b_e_typing.table_set e_type_table_copy ts''_def(4) by blast
    then have d: "s\<bullet>\<C> \<turnstile> [$Table_set x] : ([T_num T_i32, T_ref (tab_t_reftype (table \<C>!y))] _> [])"
      using e_typing_thread_typing.intros(1) to_e_list_1 by metis
    have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Table_get y, $Table_set x] : ([] _> [])"
      using a b c d
      by (metis append.left_neutral append_Cons e_type_comp_conc)
    then show ?thesis
      by (metis append.right_neutral e_weakening)
  qed
  moreover have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5), $Table_copy x y] : (ts _> ts')"
  proof -
    have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3)] : ([] _> [T_num T_i32])"
         "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i4)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
         "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i5)] : ([T_num T_i32, T_num T_i32] _> [T_num T_i32, T_num T_i32,T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) append_Cons append_self_conv2 e_weakening
      by metis+
    then have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4), $EConstNum (ConstInt32 i5)] : ([] _> [T_num T_i32, T_num T_i32, T_num T_i32])"
      using e_type_comp_conc[OF e_type_comp_conc[OF a(1,2)] a(3)] by simp
    moreover have "s\<bullet>\<C> \<turnstile> [$Table_copy x y] : (ts@[T_num T_i32, T_num T_i32, T_num T_i32] _> ts)"
      using "3"(1) ts''_def(4)
      by (metis append.right_neutral b_e_weakening e_type_table_copy e_typing_thread_typing.intros(1) table_copy to_e_list_1)
    ultimately show ?thesis
      using ts_empty
      by (metis Cons_eq_appendI append_Nil append_Nil2 e_type_comp_conc e_weakening)
  qed
  ultimately show "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i1), $EConstNum (ConstInt32 i2), $Table_get y, $Table_set x,
           $EConstNum (ConstInt32 i3), $EConstNum (ConstInt32 i4),
           $EConstNum (ConstInt32 i5), $Table_copy x y] : (ts _> ts')"
    using e_type_comp_conc by fastforce
qed

lemma types_preserved_table_grow:
  assumes "s\<bullet>\<C> \<turnstile> [Ref vr, $EConstNum (ConstInt32 n), $Table_grow ti] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 sz)] : (ts _> ts')"
proof -
  have "([] _> [T_num T_i32]) <ti: (ts _> ts')" using types_preserved_table_grow_aux[OF assms]
    by blast
  then show ?thesis
    by (metis e_typing_thread_typing.intros(3) typeof_num_def types_agree_imp_e_typing v.simps(10) v_num.case(1) v_to_e_def v_typing.intros(1))
qed

lemma lholed_same_type:
  assumes "Lfilled k lholed es les"
          "Lfilled k lholed es' les'"
          "s\<bullet>\<C> \<turnstile> les : (ts _> ts')"
          "\<And>arb_labs ts ts'.
           s\<bullet>(\<C>\<lparr>label := arb_labs@(label \<C>)\<rparr>) \<turnstile> es : (ts _> ts')
             \<Longrightarrow> s'\<bullet>(\<C>\<lparr>label := arb_labs@(label \<C>)\<rparr>) \<turnstile> es' : (ts _> ts')"
          "store_extension s s'"
  shows "(s'\<bullet>\<C> \<turnstile> les' : (ts _> ts'))"
  using assms
proof (induction arbitrary: ts ts' es' \<C> les' rule: Lfilled.induct)
  case (L0 lholed vs es' es ts ts' es'')
  obtain ts'' ts''' where "s\<bullet>\<C> \<turnstile> ($C*vs) : (ts _> ts'')"
                          "s\<bullet>\<C> \<turnstile> es : (ts'' _> ts''')"
                          "s\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc2 L0(3)
    by blast
  moreover
  hence "(s'\<bullet>\<C> \<turnstile> es'' : (ts'' _> ts'''))"
    using L0(4)[of "[]" ts'' ts''']
    by fastforce
  ultimately
  have "(s'\<bullet>\<C> \<turnstile> ($C*vs) @ es'' @ es' : (ts _> ts'))"
    using e_type_comp_conc
    by (meson assms(5) e_typing_thread_typing_store_extension_inv(1))
  thus ?case
    using L0 Lfilled.simps[of 0 lholed es'' les']
    by fastforce
next
  case (LN lholed vs n es' l es'' k es lfilledk t1s t2s es''' \<C> les')
  obtain lfilledk' where l'_def:"Lfilled k l es''' lfilledk'" "les' = ($C*vs) @ [Label n es' lfilledk'] @ es''"
    using LN Lfilled.simps[of "k+1" lholed es''' les']
    by fastforce
  obtain ts' ts'' where lab_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : (t1s _> ts')"
                                "s\<bullet>\<C> \<turnstile> [Label n es' lfilledk] : (ts' _> ts'')"
                                "s\<bullet>\<C> \<turnstile> es'' : (ts'' _> t2s)"
  using e_type_comp_conc2[OF LN(5)]
  by blast
  obtain tls ts_c \<C>_int where int_def:"([] _> ts_c) <ti: (ts' _> ts'')"
                                 "length tls = n"
                                 "s\<bullet>\<C> \<turnstile> es' : (tls _> ts_c)"
                                 "\<C>_int = \<C>\<lparr>label := [tls] @ label \<C>\<rparr>"
                                 "s\<bullet>\<C>_int \<turnstile> lfilledk : ([] _> ts_c)"
    using e_type_label[OF lab_def(2)]
    by blast
  have "(\<And>\<C>' arb_labs' ts ts'.
        \<C>' = \<C>_int\<lparr>label := arb_labs' @ label \<C>_int\<rparr> \<Longrightarrow>
        s\<bullet>\<C>' \<turnstile> es : (ts _> ts') \<Longrightarrow>
        (s'\<bullet>\<C>' \<turnstile> es''' : (ts _> ts')))"
  proof -
    fix \<C>'' arb_labs'' tts tts'
    assume "\<C>'' = \<C>_int\<lparr>label := arb_labs'' @ label \<C>_int\<rparr>"
           "s\<bullet>\<C>'' \<turnstile> es : (tts _> tts')"
    thus "(s'\<bullet>\<C>'' \<turnstile> es''' : (tts _> tts'))"
      using LN(6)[of "arb_labs'' @ [tls]" tts tts'] int_def(4)
      by fastforce
  qed
  hence "(s'\<bullet>\<C>_int \<turnstile> lfilledk' : ([] _> ts_c))"
    using LN(3)[OF l'_def(1) int_def(5)] assms(5)
    by blast
  hence "(s'\<bullet>\<C> \<turnstile> [Label n es' lfilledk'] : (ts' _> ts''))"
    using int_def e_typing_thread_typing.intros(3,8) e_typing_thread_typing_store_extension_inv(1)[OF assms(5)]
    by metis
  thus ?case
    using lab_def e_type_comp_conc l'_def(2) e_typing_thread_typing_store_extension_inv(1)[OF assms(5)]
    by blast
qed

lemma reduce_locs_type_preserved:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "store_typing s"
          "inst_typing s (f_inst f) \<C>i"
          "s\<bullet>\<C> \<turnstile> es : (ts _> ts')"
          "\<C> = \<C>i\<lparr>local := (map typeof (f_locs f)), label := arb_label, return := arb_return\<rparr>"
          "list_all2 (v_typing s) (f_locs f) (map typeof (f_locs f))"
  shows "list_all2 (v_typing s') (f_locs f') (map typeof (f_locs f'))"
  using assms
proof(induction arbitrary: \<C>i \<C> ts ts' arb_label arb_return rule: reduce.induct)
  case (invoke_host_Some s i_cl t1s t2s h ves vcs n m hs s' vcs' f)
  then show ?case
    using host_func_apply_preserve_store1 v_typing_list_store_extension_inv by blast 
next
  case (local_set vi j s v vs i v')
  thm types_preserved_local_set[OF local_set(4,1)]
  have local_\<C>: "local \<C> = map typeof (vi @ [v] @ vs)"
    using local_set(5) by simp  
  then have v_typing_\<C>: "list_all2 (v_typing s) (vi @ [v] @ vs) (local \<C>)"
    using local_set(6) by simp
  show ?case
    using types_preserved_local_set'[OF local_set(4,1) local_\<C> v_typing_\<C>] local_\<C> by fastforce
next
  case (global_set s f j v s')
  then have "store_extension s s'"
    using reduce.global_set reduce_store_extension by blast
  then show ?case using global_set(6)
    using v_typing_list_store_extension_inv by blast 
next
  case (store_Some v t f j s m k off mem' a)
  have "funcs (s\<lparr>s.mems := (s.mems s)[j := mem']\<rparr>) = funcs s"
    by simp
  then show ?case using v_typing_funcs_inv
    by (metis (mono_tags, lifting) list_all2_mono store_Some.prems(5))
next
  case (store_packed_Some v t f j s m k off tp mem' a)
  have "funcs (s\<lparr>s.mems := (s.mems s)[j := mem']\<rparr>) = funcs s"
    by simp
  then show ?case using v_typing_funcs_inv
    by (metis (mono_tags, lifting) list_all2_mono store_packed_Some.prems(5))
next
  case (store_vec_Some f j s m sv v bs k off mem' a)
  have "funcs (s\<lparr>s.mems := (s.mems s)[j := mem']\<rparr>) = funcs s"
    by simp
  then show ?case using v_typing_funcs_inv
    by (metis (mono_tags, lifting) list_all2_mono store_vec_Some.prems(5))
next
  case (memory_grow f j s m n c mem')
  have "funcs (s\<lparr>s.mems := (s.mems s)[j := mem']\<rparr>) = funcs s"
    by simp
  then show ?case using v_typing_funcs_inv
    by (metis (mono_tags, lifting) list_all2_mono memory_grow.prems(5))
next
  case (table_set f ti a s n vr tabs')
  have "funcs (s\<lparr>s.tabs := tabs'\<rparr>) = funcs s" by simp
  then show ?case using v_typing_funcs_inv
    by (metis (mono_tags, lifting) list_all2_mono table_set.prems(5))
next
  case (table_grow f ti a s tab sz n vr tab')
  then have "funcs (s\<lparr>s.tabs := (s.tabs s)[a := tab']\<rparr>) = funcs s" by simp
  then show ?case using v_typing_funcs_inv
    by (metis (mono_tags, lifting) list_all2_mono table_grow.prems(5))
next
  case (label s f es s' f' es' k lholed les les')
  then obtain t1s t2s arb_label' \<C>' where \<C>'_def: "s\<bullet>\<C>' \<turnstile> es : t1s _> t2s" "\<C>' = \<C>\<lparr>label := arb_label' @ label \<C>\<rparr>"
    using types_exist_lfilled by metis
  then have "\<C>' = \<C>i\<lparr>local := map typeof (f_locs f), label := arb_label' @ label \<C>, return := arb_return\<rparr>"
    using label(8) by fastforce
  then show ?case using  \<C>'_def label(4)[OF label(5,6)] label.prems(4) label.prems(5) by blast
next
  case (local s f es s' f' es' f0 n)
  thm e_type_local[OF local(5)]
  obtain tls \<C>i' \<C>' where \<C>i'_def:
    "inst_typing s (f_inst f) \<C>i'"
    "length tls = n"
    "s\<bullet>\<C>' \<turnstile> es : ([] _> tls)"
    "([] _> tls) <ti: (ts _> ts')"
    "list_all2 (v_typing s) (f_locs f) (map typeof (f_locs f))"
    "\<C>'=\<C>i'\<lparr>local := map typeof (f_locs f), return := Some tls\<rparr>"
    using e_type_local[OF local(5)] by blast
  then show ?case
    using e_type_local_shallow local.hyps local.prems(1,3,5) store_preserved v_typing_list_store_extension_inv by blast
next
  case (elem_drop a f x s)
  have "funcs (s\<lparr>s.elems := (s.elems s)[a := (fst (s.elems s ! a), [])]\<rparr>) = funcs s"
    by simp
  then show ?case using v_typing_funcs_inv
    by (metis (mono_tags, lifting) elem_drop.prems(5) list_all2_mono)
next
  case (data_drop a f x s)
 have "funcs (s\<lparr>s.datas := (s.datas s)[a := []]\<rparr>) = funcs s"
    by simp
  then show ?case using v_typing_funcs_inv
    by (metis (mono_tags, lifting) data_drop.prems(5) list_all2_mono)
qed blast+

lemma types_preserved_e1:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "store_typing s"
          "inst_typing s (f_inst f) \<C>i"
          "tvs = map typeof (f_locs f)"
          "\<C> = \<C>i\<lparr>local := tvs, label := arb_labs, return := arb_return\<rparr>"
          "s\<bullet>\<C> \<turnstile> es : (ts _> ts')"
          "list_all2 (\<lambda> v t. v_typing s v t) (f_locs f) tvs"
  shows "(s'\<bullet>\<C> \<turnstile> es' : (ts _> ts')) \<and> (tvs = map typeof (f_locs f')) \<and> list_all2 (\<lambda> v t. v_typing s' v t) (f_locs f') tvs"
  using assms
proof (induction arbitrary: tvs \<C> \<C>i ts ts' arb_labs arb_return rule: reduce.induct)
  case (basic e e' s vs i)
  then show ?case
    using types_preserved_b_e1[OF basic(1,2)]
    by fastforce
next
  case (call s f j)
  obtain  tf1 tf2 where l_func_t: "length (func_t \<C>) > j"
                                       "(tf1 _> tf2) <ti: (ts _> ts')"
                                       "((func_t \<C>)!j) = (tf1 _> tf2)"
    using b_e_type_call[of \<C> "Call j" ts ts' j] call(5)
          unlift_b_e[of _ _ "[Call j]" "(ts _> ts')"]
    by fastforce
  have "j < length (func_t \<C>i)"
    using l_func_t(1) call(4)
    by simp
  hence 1:"sfunc_ind (f_inst f) j < length (s.funcs s)"
          "cl_type (s.funcs s ! sfunc_ind (f_inst f) j) = (tf1 _> tf2)"
    using store_typing_imp_func_agree[OF call(1,2)] call(4)
          inst_typing_func_length[OF call(2)] l_func_t(3)
    unfolding funci_agree_def
    by fastforce+
  show ?case
    using e_typing_thread_typing.intros(3)[OF e_typing_thread_typing.intros(7)[OF 1]] l_func_t
          call.prems(3,6)
    by fastforce
next
  case (call_indirect_Some s i' c cl j tf vs)
  thus ?case
    using types_preserved_call_indirect_Some[OF call_indirect_Some(9,2)]
    by blast
next
  case (call_indirect_None s i c cl j vs)
  thus ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (invoke_native cl j t1s t2s ts es ves vcs n k m zs s vs i)
  thus ?case
    using types_preserved_invoke_native
    by fastforce
next
  case (invoke_host_Some s i_cl t1s t2s hf ves vcs n m h hs s' vcs' f)
  thus ?case
    using types_preserved_invoke_host_some[OF invoke_host_Some(11,1,2,3,4,5)] host_func_apply_preserve_store1 v_typing_list_store_extension_inv
    by auto
next
  case (invoke_host_None cl t1s t2s f ves vcs n m s hs vs i)
  thus ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (ref_func fa f j s)
  then have 1: "\<C> \<turnstile> [Ref_func j] : ts _> ts'"

    by (metis to_e_list_1 unlift_b_e)
  then have 2: "j < length (func_t \<C>)"
    by (simp add: b_e_type_ref_func(2))
  have 3: "list_all2 (funci_agree (funcs s)) (inst.funcs (f_inst f)) (func_t \<C>i)"
    using ref_func inst_typing.simps by fastforce
  then have 4: "list_all2 (funci_agree (funcs s)) (inst.funcs (f_inst f)) (func_t \<C>)"
    using ref_func(5) by fastforce
  then have 5: "j < length (inst.funcs (f_inst f))"
    by (simp add: "2" list_all2_lengthD)
  then show ?case using
      types_preserved_ref_func[OF 5 ref_func(1)[symmetric] _ ref_func(6) 4]
      reduce.ref_func[OF ref_func(1), of s] ref_func.prems
      by fastforce
next
  case (local_get vi j i v vs s)
  have 1: "local \<C> = tvs"
    using store_local_label_empty assms(2) local_get
    by fastforce
  have 2: "v_typing s v (typeof v)"
    by (metis local_get.hyps(2) local_get.prems(6) list_all2_Cons1 list_all2_append1 type_const_v_typing(2) types_agree_imp_e_typing)
  then show ?case
    using types_preserved_local_get[OF local_get(7) local_get(1) _ 2 store_extension_refl ] local_get
    by fastforce
next
  case (local_set vi j s v vs v' i)
  have "local \<C> = tvs"
    using store_local_label_empty assms(2) local_set
    by fastforce
  thus ?case
    using local_set types_preserved_local_set
    by (metis f.select_convs(1) types_preserved_local_set')
next
  case (global_get s f j)
  have 0: "length (global \<C>) > j"
    using b_e_type_global_get global_get(5) unlift_b_e[of _ _ "[Global_get j]" "(ts _> ts')"]
    by fastforce
  hence "glob_typing (sglob s (f_inst f) j) ((global \<C>)!j)"
    using global_get(3,4) store_typing_imp_glob_agree[OF global_get(2)]
    by fastforce
  hence "typeof (g_val (sglob s (f_inst f) j)) = tg_t (global \<C> ! j)"
    unfolding glob_typing_def
    by fastforce
  hence 1: "typeof (sglob_val s (f_inst f) j) = tg_t (global \<C> ! j)"
    unfolding sglob_val_def
    by fastforce
  have 2: "v_typing s (sglob_val s (f_inst f) j) (typeof (sglob_val s (f_inst f) j))"
  proof -
    have j_length: "((inst.globs(f_inst f)) ! j) < length (globs s)"
    proof -
      have j_\<C>i: "j < length (global \<C>i)" using 0 global_get(4) by simp
      have "inst_typing s (f_inst f) \<C>i" using global_get by simp
      then have "list_all2 (globi_agree (globs s)) (inst.globs (f_inst f)) (global \<C>i)"
        using inst_typing.simps by auto
      then show ?thesis using j_\<C>i
        using global_get.prems(2) sglob_ind_def store_typing_imp_glob_agree(1) by auto
    qed
    have "list_all (glob_agree s) (globs s)" using global_get(1) store_typing.simps by simp
    then have "glob_agree s ((globs s)!((inst.globs(f_inst f)) ! j))" using j_length
      by (simp add: list_all_length)
    then show ?thesis unfolding glob_agree_def sglob_val_def
      using sglob_def sglob_ind_def v_typing_typeof by fastforce
  qed
  thus ?case
    using global_get(3,5) types_preserved_global_get[OF 1 _ 2 store_extension_refl]
      global_get.prems(6) by blast
next
  case (global_set s i j v s' vs)
  have "funcs s = funcs s'"
    using global_set.hyps supdate_glob_def by fastforce
  then show ?case
    using global_set
    using types_preserved_global_set
    using v_typing_funcs_inv
    by (simp add: list_all2_mono)
next
  case (load_Some s i j m k off t bs vs a)
  then show ?case
    using types_preserved_load(1) wasm_deserialise_num_type
    unfolding typeof_def
    by (metis v.simps(10) v_to_e_def)
next
  case (load_None s i j m k off t vs a)
  then show ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (load_packed_Some s i j m sx k off tp bs vs t a)
  then show ?case
    using types_preserved_load(1) wasm_deserialise_num_type
    unfolding typeof_def
    by (metis v.simps(10) v_to_e_def)
next
  case (load_packed_None s i j m sx k off tp vs t a)
  then show ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (store_Some t v s i j m k off mem' vs a)
  then show ?case
    using types_preserved_store
    by (metis (mono_tags, lifting) list_all2_mono s.select_convs(1) s.surjective s.update_convs(3) v.simps(10) v_to_e_def v_typing_funcs_inv)
next
  case (store_None t v s i j m k off vs a)
  then show ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (store_packed_Some t v s i j m k off tp mem' vs a)
  then show ?case
    using types_preserved_store
    by (metis (mono_tags, lifting) list_all2_mono s.select_convs(1) s.surjective s.update_convs(3) v.simps(10) v_to_e_def v_typing_funcs_inv)
next
  case (store_packed_None t v s i j m k off tp vs a)
  then show ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (load_vec_Some f j s m lv k off bs a)
  then show ?case
    using types_preserved_load_vec(1)
    unfolding typeof_def
    by (metis (mono_tags, lifting) t_vec.exhaust v.simps(11) v_to_e_def)
next
  case (load_vec_None f j s m lv k off a)
  then show ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (load_lane_vec_Some f j s m k off svi bs i v v' a)
  then show ?case
    using types_preserved_load_lane_vec
    by blast
next
  case (load_lane_vec_None f j s m k off svi v i a)
  then show ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (store_vec_Some f j s m sv v bs k off mem' a)
  then show ?case
    using types_preserved_store_vec
    by (simp add: list_all2_mono v_typing_funcs_inv)
next
  case (store_vec_None f j s m sv v bs k off a)
  then show ?case
    using e_typing_thread_typing.intros(5)
    by blast
next
  case (memory_size s i j m n vs)
  then show ?case
    using types_preserved_memory_size
    by fastforce
next
  case (memory_grow s i j m n c mem' vs)
  then show ?case
    using types_preserved_memory_grow
    by (simp add: list_all2_mono v_typing_funcs_inv)
next
  case (memory_grow_fail s i j m n vs c)
  thus ?case
    using types_preserved_memory_grow
    by blast
next
  case (block vs n f tb t1s t2s m s es)
  have "types_t \<C>i = types (f_inst f)"
    using block(6) inst_typing.simps
    by fastforce
  thus ?case
    using block types_preserved_block
    by fastforce
next
  case (loop vs n f tb t1s t2s m s es)
  have "types_t \<C>i = types (f_inst f)"
    using loop(6) inst_typing.simps
    by fastforce
  thus ?case
    using loop types_preserved_loop
    by fastforce
next
  case (label s f es s' f' es' k lholed les les')
  {
    fix \<C>' arb_labs' ts ts'
    assume local_assms:"\<C>' = \<C>\<lparr>label := arb_labs'@(label \<C>), return := (return \<C>)\<rparr>"
    hence "(s\<bullet>\<C>' \<turnstile> es : (ts _> ts')) \<Longrightarrow>
             ((s'\<bullet>\<C>' \<turnstile> es' : (ts _> ts')) \<and> map typeof (f_locs f) = map typeof (f_locs f') \<and> store_extension s s') \<and> list_all2 (v_typing s') (f_locs f') tvs"
      using label(4)[OF label(5,6,7,8)] label(4,5,6,7,8)
            reduce_store_extension[OF label(1,5,6), of \<C>' _ _ "return \<C>'" "label \<C>'"] label(10)
      by fastforce
    hence "(s\<bullet>\<C>\<lparr>label := arb_labs'@(label \<C>)\<rparr> \<turnstile> es : (ts _> ts'))
               \<Longrightarrow> (s'\<bullet>\<C>\<lparr>label := arb_labs'@(label \<C>)\<rparr> \<turnstile> es' : (ts _> ts')) \<and>
                     map typeof (f_locs f) = map typeof (f_locs f') \<and> store_extension s s' \<and> list_all2 (v_typing s') (f_locs f') tvs"
      using local_assms
      by simp
  }
  hence "\<And>arb_labs' ts ts'. s\<bullet>\<C>\<lparr>label := arb_labs'@(label \<C>)\<rparr> \<turnstile> es : (ts _> ts')
                              \<Longrightarrow> (s'\<bullet>\<C>\<lparr>label := arb_labs'@(label \<C>)\<rparr> \<turnstile> es' : (ts _> ts'))"
       "map typeof (f_locs f) = map typeof (f_locs f')"
       "store_extension s s'"
       "list_all2 (v_typing s') (f_locs f') tvs"
    using types_exist_lfilled[OF label(2,9)]
    by auto
  thus ?case
    using lholed_same_type[OF label(2,3,9)] label.prems(3)
    by blast
next
  case (local s f es s' f' es' f0 n)
  obtain \<C>' tls \<C>i' where es_def:"inst_typing s (f_inst f) \<C>i'"
                          "length tls = n"
                          "\<C>' =  \<C>i'\<lparr>local := map typeof (f_locs f), label := label  \<C>i', return := Some tls\<rparr>"
                          "s\<bullet>\<C>' \<turnstile> es : ([] _> tls)"
                          "([] _> tls) <ti: (ts _> ts')"
                          "list_all2 (v_typing s) (f_locs f) (map typeof (f_locs f))"
    using e_type_local[OF local(7)]
    by fastforce
  have a: "list_all2 (v_typing s) (f_locs f) (map typeof (f_locs f))"
    using v_typing_typeof_list
    by (metis e_type_local_shallow frame_typing.simps thread_typing.simps local.prems(5))
  hence 0:"s'\<bullet>\<C>' \<turnstile> es' : ([] _> tls)" "map typeof (f_locs f) = map typeof (f_locs f')"
    using local(2)[OF local(3) es_def(1) _ es_def(3) es_def(4) ]
    by blast+
  then have 1: "list_all2 (v_typing s) (f_locs f) (map typeof (f_locs f))"
    using a by simp
  have "inst_typing s' (f_inst f) \<C>i'"
    using inst_typing_store_extension_inv[OF es_def(1)] reduce_store_extension[OF local(1,3) es_def(1,4,3)]
    by blast
  hence "frame_typing s' f' (\<C>i'\<lparr>local := map typeof (f_locs f)\<rparr>)"
    using 0(2) es_def(6) frame_typing.intros local.hyps reduce_inst_is
      reduce_locs_type_preserved[OF local.hyps local(3) es_def(1) es_def(4) es_def(3)]
    by auto
  hence 1:"s'\<bullet>(Some tls) \<tturnstile> f';es' : tls"
    using 0 e_typing_thread_typing.intros(9) es_def(1,3) reduce_inst_is[OF local(1)]
    by fastforce
  show ?case
    using e_typing_thread_typing.intros(3) e_typing_thread_typing.intros(6)[OF 1 es_def(2)] es_def(5) local(5)
    by (metis e_type_local_shallow local.hyps local.prems(1) local.prems(5) local.prems(6) store_preserved v_typing_list_store_extension_inv)
next
  case (table_get f ti a s n val)
  then show ?case using types_preserved_table_get by blast
next
  case (table_get_fail f ti a s n)
  then show ?case
    using e_typing_thread_typing.intros(5) by blast
next
  case (table_set f ti a s n vr tabs')
  then show ?case using types_preserved_table_set
    by (simp add: list_all2_mono types_preserved_table_set_aux(1) v_typing_funcs_inv)
next
  case (table_set_fail f ti a s n vr)
  then show ?case
    using e_typing_thread_typing.intros(5) by blast
next
  case (table_size f ti a s t n)
  then have "\<C> \<turnstile> [Table_size ti] : (ts _> ts')"
    by (metis to_e_list_1 unlift_b_e)
  then have "([] _> [T_num T_i32]) <ti: (ts _> ts')"
    using b_e_type_table_size by blast
  then have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat n))] : (ts _> ts')"
    by (metis e_typing_thread_typing.intros(3) typeof_num_def types_agree_imp_e_typing v.simps(10) v_num.case(1) v_to_e_def v_typing.intros(1))
  then show ?case
    using table_size.prems(3) table_size.prems(6) by blast
next
  case (table_grow f ti a s tab sz n vr tab')
  then show ?case using types_preserved_table_grow[OF table_grow(9)] v_typing_funcs_inv
    by (simp add: list_all2_mono)
next
  case (table_grow_fail s f vr n ti)
    then show ?case using types_preserved_table_grow[OF table_grow_fail(5)]
      by simp
next
  case (memory_init_trap f ma s m x da dat ndest dest nsrc src nn n)
  then show ?case using e_typing_thread_typing.intros(5) by blast
next
  case (memory_init_done f ma s m x da dat ndest dest nsrc src nn n)
  then show ?case using types_preserved_memory_init by blast
next
  case (memory_init f ma s m x da dat ndest dest nsrc src nn n nn_pred b)
  then show ?case using types_preserved_memory_init(2) by metis
next
  case (memory_copy_trap f ma s m ndest dest nsrc src nn n)
  then show ?case using e_typing_thread_typing.intros(5) by blast
next
  case (memory_copy_done f ma s m ndest dest nsrc src nn n)
  then show ?case using types_preserved_memory_copy by metis
next
  case (memory_copy_1 f ma s m ndest dest nsrc src nn nn_pred n)
  then show ?case using types_preserved_memory_copy by metis
next
  case (memory_copy_2 f ma s m ndest dest nsrc src nn nn_pred n)
  then show ?case using types_preserved_memory_copy by metis
next
  case (memory_fill_trap f ma s m ndest dest nn n val)
  then show ?case using e_typing_thread_typing.intros(5) by blast
next
  case (memory_fill_done f ma s m ndest dest nn n val)
  then show ?case using types_preserved_memory_fill by metis
next
  case (memory_fill f ma s m ndest dest nn n nn_pred val)
  then show ?case using types_preserved_memory_fill by metis
next
  case (table_init_trap f x ta s tab y ea el src n dest)
  then show ?case
    using e_typing_thread_typing.intros(5) by blast
next

  case (table_init_done f x ta s tab ea y el ndest dest nsrc src nn n)
  have 1: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)] @
          [$Table_init x y] : (ts _> ts')" using table_init_done(15) by auto
  obtain ts'' vs where ts''_def:
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    "($C* vs) = [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)]"
    "s\<bullet>\<C> \<turnstile> $C*vs : (ts _> ts'')"
    "s\<bullet>\<C> \<turnstile> [$Table_init x y] : (ts'' _> ts')"
    using  e_type_comp_conc1[OF 1] v_to_e_def by auto
  have "([] _> [T_num T_i32, T_num T_i32, T_num T_i32]) <ti: (ts _> ts'')"
    using e_typing_imp_list_v_typing(2)[OF ts''_def(3)] unfolding ts''_def(1) by(simp add: typeof_def typeof_num_def)
  moreover have "([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts'' _> ts')" using e_type_table_init[OF ts''_def(4)] by simp
  ultimately show ?case
    using e_type_empty instr_subtyping_comp table_init_done.prems(3) table_init_done.prems(6) by blast
next
  case (table_init f x ta s tab ea y el ndest dest nsrc src nn n nn_pred val)
  have 1: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)] @
          [$Table_init x y] : (ts _> ts')" using table_init(16) by auto
  obtain ts'' vs where ts''_def:
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    "($C* vs) = [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n)]"
    "s\<bullet>\<C> \<turnstile> $C*vs : (ts _> ts'')"
    "s\<bullet>\<C> \<turnstile> [$Table_init x y] : (ts'' _> ts')"
    using  e_type_comp_conc1[OF 1] v_to_e_def by auto

  have 2: "([] _> [T_num T_i32, T_num T_i32, T_num T_i32]) <ti: (ts _> ts'')"
    using e_typing_imp_list_v_typing(2)[OF ts''_def(3)] unfolding ts''_def(1) by(simp add: typeof_def typeof_num_def)
  have 3: "[T_num T_i32, T_num T_i32, T_num T_i32] _> [] <ti: ts'' _> ts'"
          "x < length (table \<C>)"
          "y < length (elem \<C>)"
          "tab_t_reftype (table \<C> ! x) = elem \<C> ! y"
    using e_type_table_init[OF ts''_def(4)] by simp_all
  have 4: "[] _> [] <ti: ts _> ts'"
    using "2" "3" instr_subtyping_comp by blast
  have 5: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 dest), $C V_ref val, $Table_set x] : (ts _> ts)"
  proof -
    have y1: "y < length (elem \<C>)"
      using ts''_def e_type_table_init[OF ts''_def(4)] by simp
    then have y2: "y < length (elem \<C>i)"
      using table_init(15) by simp
    then have y3: "y < length (inst.elems (f_inst f))"
      using ts''_def e_type_table_init[OF ts''_def(4)]
      using store_elem_exists table_init.prems(2) by auto
    moreover have y4: "list_all2 (elemi_agree s (s.elems s)) (inst.elems (f_inst f)) (elem \<C>i)"
      using table_init.prems(2) inst_typing.simps by fastforce
    ultimately have y5: "ea < length (elems s)" using elemi_agree_def list_all2_nthD table_init.hyps(3,4)
      by fastforce
    then have el_agree: "elem_agree s el" using store_typing_in_elem_agree[OF table_init(12)]
      using table_init.hyps(4) by blast
    then have h_y: "fst el = (elem \<C> ! y)"
    proof -
      have "elemi_agree s (s.elems s) ((inst.elems (f_inst f))!y) (elem \<C>i!y)"
        using table_init.prems(2) inst_typing.simps list_all2_nthD table_init.hyps(2) y3 y4 by fastforce
      then show ?thesis
        using table_init.prems(2) inst_typing.simps list_all2_nthD table_init.hyps(3,4,5) table_init(15) elem_typing_def elemi_agree_def
        by fastforce
    qed
    have "nsrc < length (snd el)"
      using table_init.hyps(10,8) by auto
    then have h_ref: "ref_typing s val (fst el)"
      by (metis el_agree elem_agree_def list_all_length table_init.hyps(11))
    have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (dest))] : (ts _> ts@[T_num T_i32])"
      by (metis append.right_neutral const_num e_typing_thread_typing.intros(1) e_weakening to_e_list_1 typeof_num_def v_num.case(1))
    moreover
    have "s\<bullet>\<C> \<turnstile> [$C V_ref val] : (ts@[T_num T_i32] _> ts@[T_num T_i32, T_ref (fst el)])"
      using h_ref append_Cons e_typing_thread_typing.intros(3) types_agree_imp_e_typing v_typing.intros(3)
      by (metis append_Nil e_weakening)
    moreover
    have "s\<bullet>\<C> \<turnstile> [$Table_set x] : (ts@[T_num T_i32, T_ref (fst el)] _> ts)"
      using b_e_typing.table_set[OF 3(2) 3(4)] h_y e_weakening e_typing_thread_typing.intros(1) to_e_list_1 by fastforce
    ultimately
    show ?thesis
      by (metis append.left_neutral append_Cons e_type_comp_conc)
  qed
  have 6: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (ndest + 1))), $EConstNum (ConstInt32 (int_of_nat (nsrc + 1))), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_init x y] : (ts _> ts)"
  proof -
    have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (ndest + 1)))] : (ts _> ts@[T_num T_i32])"
      by (metis append.right_neutral const_num e_typing_thread_typing.intros(1) e_weakening to_e_list_1 typeof_num_def v_num.case(1))
    moreover
    have  "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (nsrc + 1)))] : (ts@[T_num T_i32] _> ts@[T_num T_i32, T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) e_weakening
      by (metis append.left_neutral append_Cons)
    moreover
    have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (nn_pred)))] : (ts@[T_num T_i32, T_num T_i32] _> ts@[T_num T_i32, T_num T_i32, T_num T_i32])"
      using const_num e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) to_e_list_1 typeof_num_def v_num.case(1) e_weakening
      by (metis append.left_neutral append_Cons)
    moreover
    have "s\<bullet>\<C> \<turnstile> [$Table_init x y] : (ts@[T_num T_i32, T_num T_i32, T_num T_i32] _> ts)"
      using b_e_typing.table_init[OF 3(2,3)] 3 3(4) 4 e_weakening ts''_def(4)
      by (metis append.right_neutral e_typing_thread_typing.intros(1) to_e_list_1)
    ultimately show ?thesis
      by (metis append_Cons append_Nil e_type_comp_conc)
  qed
  then show ?case using table_init.prems(3) table_init.prems(6) 4  e_type_comp_conc[OF 5 6]
    by (metis append.left_neutral append_Cons append_Nil2 e_type_comp_conc e_type_empty)
next
  case (table_fill_trap f x ta s tab ni i nn n vr)
  then show ?case using e_typing_thread_typing.intros(5) by blast
next
  case (table_fill_done f x ta s tab ni i nn n vr)
  then have 1: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i), $C (V_ref vr), $EConstNum (ConstInt32 n)] @
          [$Table_fill x] : (ts _> ts')" by auto
  obtain ts'' vs where ts''_def:
    "vs = [V_num (ConstInt32 i), V_ref vr, V_num (ConstInt32 n)]"
    "($C* vs) = [$EConstNum (ConstInt32 i), $C (V_ref vr), $EConstNum (ConstInt32 n)]"
    "s\<bullet>\<C> \<turnstile> $C*vs : (ts _> ts'')"
    "s\<bullet>\<C> \<turnstile> [$Table_fill x] : (ts'' _> ts')"
    using  e_type_comp_conc1[OF 1] v_to_e_def by auto
  have 1: "([] _> [T_num T_i32, T_ref (typeof_ref vr), T_num T_i32]) <ti: (ts _> ts'')"
    using e_typing_imp_list_v_typing(2)[OF ts''_def(3)] unfolding ts''_def(1) by(simp add: typeof_def typeof_num_def)
  have 2: "([T_num T_i32, T_ref (tab_t_reftype (table \<C>!x)), T_num T_i32] _> []) <ti: (ts'' _> ts')" using e_type_table_fill
    using ts''_def(4) by blast
  let ?ts = "[T_num T_i32, T_ref (typeof_ref vr), T_num T_i32]"
  let ?ts' = "[T_num T_i32, T_ref (tab_t_reftype (table \<C>!x)), T_num T_i32]"
  have 3: "list_all (\<lambda>t. t \<noteq> T_bot) ?ts" by fastforce
  have "?ts = ?ts'"
    using 1 2 instr_subtyping_append_type_eq[OF _ _ 3, of "[]" "[]" ts ts'' "[]" ?ts'] by auto
  then show ?case
    using 1 2 e_type_empty table_fill_done.prems(3) table_fill_done.prems(6)
    by (metis instr_subtyping_comp)
next
  case (table_fill f x ta s tab ni i nn n nn_pred vr)
  then have 1: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i), $C (V_ref vr), $EConstNum (ConstInt32 n)] @
          [$Table_fill x] : (ts _> ts')" by auto
  obtain ts'' vs where ts''_def:
    "vs = [V_num (ConstInt32 i), V_ref vr, V_num (ConstInt32 n)]"
    "($C* vs) = [$EConstNum (ConstInt32 i), $C (V_ref vr), $EConstNum (ConstInt32 n)]"
    "s\<bullet>\<C> \<turnstile> $C*vs : (ts _> ts'')"
    "s\<bullet>\<C> \<turnstile> [$Table_fill x] : (ts'' _> ts')"
    using  e_type_comp_conc1[OF 1] const_list_split_3 v_to_e_def by auto
  then have t_vs: "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> map typeof vs)"
    using e_type_consts store_extension_refl by blast
  have 2: "([] _> [T_num T_i32, T_ref (typeof_ref vr), T_num T_i32]) <ti: (ts _> ts'')"
    using e_typing_imp_list_v_typing(2)[OF ts''_def(3)] unfolding ts''_def(1)
    using typeof_def typeof_num_def const_list_split_3
    by simp
  have 3: "([T_num T_i32, T_ref (tab_t_reftype (table \<C>!x)), T_num T_i32] _> []) <ti: (ts'' _> ts')" using e_type_table_fill
    using ts''_def(4) by blast
  let ?ts = "[T_num T_i32, T_ref (typeof_ref vr), T_num T_i32]"
  let ?ts' = "[T_num T_i32, T_ref (tab_t_reftype (table \<C>!x)), T_num T_i32]"
  have ts_not_bot: "list_all (\<lambda>t. t \<noteq> T_bot) ?ts" by fastforce
  have ts_eq_ts': "?ts = ?ts'"
    using 2 3 instr_subtyping_append_type_eq[OF _ _ ts_not_bot, of "[]" "[]" ts ts'' "[]" ?ts'] by auto
  then have 4: "([] _> []) <ti: (ts _> ts')"
    by (metis "2" "3" instr_subtyping_comp)
  have 5: "tab_t_reftype (table \<C>!x) = typeof_ref vr"
    using ts_eq_ts' by fastforce
  have 6: "ref_typing s vr (typeof_ref vr)" "s\<bullet>\<C> \<turnstile> [$C (V_ref vr)] : ([] _> [T_ref (typeof_ref vr)])"
  proof -
    have "s\<bullet>\<C> \<turnstile> $C* vs : ([] _> [T_num T_i32, T_ref (typeof_ref vr), T_num T_i32])"
      using t_vs ts''_def(2)
      by (simp add: ts''_def(1) typeof_def typeof_num_def)
    then show "s\<bullet>\<C> \<turnstile> [$C (V_ref vr)] : ([] _> [T_ref (typeof_ref vr)])"
      using const_list_split_3
      using ts''_def(1) by blast
    then show "ref_typing s vr (typeof_ref vr)"
      using const_typeof type_const_v_typing(2) v_typing.simps by fastforce
  qed
  have 7: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i), $C V_ref vr, $Table_set x] : (ts _> ts)"
  proof -
    have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i)] : [] _> [T_num T_i32]"
      by (metis const_num e_typing_thread_typing.intros(1) to_e_list_1 typeof_num_def v_num.case(1))
    then have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i), $C V_ref vr] : [] _> [T_num T_i32, T_ref (typeof_ref vr)]"
      using 6(2) e_type_comp_conc e_typing_thread_typing.intros(3) self_append_conv2 e_weakening append_Cons by metis
    then have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 i), $C V_ref vr] : ts _> ts@[T_num T_i32, T_ref (typeof_ref vr)]"
      using e_typing_thread_typing.intros(3) e_weakening by fastforce
    moreover have "s\<bullet>\<C> \<turnstile> [$Table_set x] : (ts@[T_num T_i32, T_ref (typeof_ref vr)] _> ts)"
      by (metis "5" append.right_neutral b_e_typing.table_set e_type_table_fill e_typing_thread_typing.intros(1) e_weakening to_e_list_1 ts''_def(4))
    ultimately show ?thesis
      by (metis append_Cons append_Nil e_type_comp_conc)
  qed
  have 8: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (ni + 1))), $C V_ref vr,
           $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_fill x] : (ts _> ts)"
  proof -
    have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (ni + 1)))] : [] _> [T_num T_i32]"
      by (metis const_num e_typing_thread_typing.intros(1) to_e_list_1 typeof_num_def v_num.case(1))
    then have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (ni + 1))), $C V_ref vr] : [] _> [T_num T_i32, T_ref (typeof_ref vr)]"
      using 6(2) e_type_comp_conc e_typing_thread_typing.intros(3) self_append_conv2 e_weakening append_Cons by metis
    then have "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (ni + 1))), $C V_ref vr, $EConstNum (ConstInt32 (int_of_nat nn_pred))] : [] _> [T_num T_i32, T_ref (typeof_ref vr), T_num T_i32]"
      by (metis e_weakening append_Cons const_num e_type_comp_conc e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) eq_Nil_appendI to_e_list_1 typeof_num_def v_num.case(1))
    then have a: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 (int_of_nat (ni + 1))), $C V_ref vr, $EConstNum (ConstInt32 (int_of_nat nn_pred))] : ts _> ts@[T_num T_i32, T_ref (typeof_ref vr), T_num T_i32]"
      using e_typing_thread_typing.intros(3) e_weakening by fastforce
    moreover have b: "s\<bullet>\<C> \<turnstile> [$Table_fill x] : (ts@[T_num T_i32, T_ref (typeof_ref vr), T_num T_i32] _> ts)"
      using "2" "4" ts''_def(4)
      by (metis "5" append.right_neutral b_e_typing.table_fill b_e_weakening e_type_table_fill e_typing_thread_typing.intros(1) to_e_list_1)
    show ?thesis using e_type_comp_conc[OF a b] by simp
  qed
  show ?case using e_type_comp_conc[OF 7 8] 4 e_type_comp_conc e_type_empty table_fill.prems(3,6) by fastforce
next
  case (table_copy_trap f x tax s tabx y tay ty taby src n dest)
  then show ?case using e_typing_thread_typing.intros(5) by blast
next
  case (table_copy_done f x tax s tabx y tay ty taby ndest dest nrsc src nn n nsrc)
  then show ?case using types_preserved_table_copy by blast
next
  case (table_copy_1 f x tax s tabx y tay ty taby ndest dest nrsc src nn n nsrc nn_pred)
  then show ?case using types_preserved_table_copy(2) by metis
next
  case (table_copy_2 f x tax s tabx y tay ty taby ndest dest nrsc src nn n nsrc nn_pred)
  then show ?case using types_preserved_table_copy by metis
next
  case (elem_drop a f x s)
  then have "([] _> []) <ti: (ts _> ts')" using e_type_elem_drop by blast
  moreover have "list_all2 (v_typing (s\<lparr>s.elems := (s.elems s)[a := (fst (s.elems s ! a), [])]\<rparr>)) (f_locs f) tvs"
    by (metis elem_drop.hyps(1) elem_drop.hyps elem_drop.prems  reduce.elem_drop reduce_locs_type_preserved)
  ultimately show ?case
    using e_type_empty elem_drop.prems(3) by blast
next
  case (data_drop a f x s)
  then have "([] _> []) <ti: (ts _> ts')" using e_type_data_drop by blast
  moreover have "list_all2 (v_typing (s\<lparr>s.datas := (s.datas s)[a := []]\<rparr>)) (f_locs f) tvs"
    by (metis data_drop.hyps(1) data_drop.hyps data_drop.prems(1) data_drop.prems(2) data_drop.prems(3) data_drop.prems(4) data_drop.prems(5) data_drop.prems(6) reduce.data_drop reduce_locs_type_preserved)
  ultimately show ?case
    using e_type_empty data_drop.prems(3) by blast
qed 

lemma types_preserved_e2:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "store_typing s"
          "frame_typing s f \<C>i"
          "tvs = map typeof (f_locs f)"
          "\<C> = \<C>i\<lparr>label := arb_labs, return := arb_return\<rparr>"
          "s\<bullet>\<C> \<turnstile> es : (ts _> ts')"
  shows "store_extension s s'"
        "store_typing s'"
        "frame_typing s' f' \<C>i"
        "s'\<bullet>\<C> \<turnstile> es' : (ts _> ts')"
proof -
  show store_props: "store_extension s s'"
                    "store_typing s'"
    using assms(3,5,6) reduce_store_extension[OF assms(1,2) _ assms(6)]
    unfolding frame_typing.simps
    using v_typing_typeof_list by blast+
  then have locals_prop: "list_all2 (v_typing s) (f_locs f) tvs"
    by (metis assms(3,4) frame_typing.cases v_typing_typeof_list)
  obtain \<C>i' where \<C>i'_def: "inst_typing s (f_inst f) \<C>i'" "\<C>i = \<C>i'\<lparr>local := tvs\<rparr>"
    using frame_typing.simps assms(3)
    using assms(4) v_typing_typeof_list by blast
  then have \<C>_prop:"\<C> = \<C>i'\<lparr>local := tvs, label := arb_labs, return := arb_return\<rparr>"
    using assms(5)
    by blast
  then have 0: "s'\<bullet>\<C> \<turnstile> es' : ts _> ts'" "tvs = map typeof (f_locs f')" "list_all2 (v_typing s') (f_locs f') tvs"
    using types_preserved_e1[OF assms(1,2) \<C>i'_def(1) assms(4) _ assms(6) locals_prop]
    by simp+
  have 2: "inst_typing s' (f_inst f') \<C>i'"
    by (metis \<C>i'_def(1) assms(1) inst_typing_store_extension_inv reduce_inst_is store_props(1))
  have 1: "list_all2 (v_typing s') (f_locs f') tvs"
    using 0 by simp
  show "frame_typing s' f' \<C>i" "s'\<bullet>\<C> \<turnstile> es' : (ts _> ts')"
    using frame_typing.intros[OF 1 2 ] 0 \<C>i'_def(2) by blast+
qed

lemma types_preserved_e:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "store_typing s"
          "s\<bullet>None \<tturnstile> f;es : ts"
  shows "s'\<bullet>None \<tturnstile> f';es' : ts"
  using assms
proof -
  obtain tvs \<C> \<C>i where defs: "list_all2 (\<lambda> v t. v_typing s v t) (f_locs f) tvs"
                              "tvs = map typeof (f_locs f)"
                              "inst_typing s (f_inst f) \<C>i"
                              "\<C> = \<C>i\<lparr>local := tvs, label := (label \<C>i), return := None\<rparr>"
                              "s\<bullet>\<C> \<turnstile> es : ([] _> ts)"
                              "\<C> = \<C>i\<lparr>local := tvs, return := None\<rparr>"
    using assms(3) v_typing_typeof_list
    unfolding thread_typing.simps frame_typing.simps
    by fastforce
  have 1:"(s'\<bullet>\<C> \<turnstile> es' : ([] _> ts))"
         "(tvs = map typeof (f_locs f'))"
         "list_all2 (\<lambda> v t. v_typing s' v t) (f_locs f') tvs"
    using types_preserved_e1[OF assms(1,2) defs(3,2,4,5,1)]
    by fastforce+

  have 2:"inst_typing s' (f_inst f) \<C>i"
    using store_preserved(1)[OF assms] inst_typing_store_extension_inv[OF defs(3)]
    by blast
  show ?thesis
    using defs e_typing_thread_typing.intros(9)
          assms(1) reduce_inst_is 1 2
    unfolding frame_typing.simps
    apply simp
    apply (metis (full_types))
    done
qed

subsection \<open>Progress\<close>

lemma const_list_no_progress:
  assumes "const_list es"
  shows "\<not>\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
proof -
  {
    assume "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    hence "False"
      using assms
    proof (induction rule: reduce.induct)
      case (basic e e' s vs)
      thus ?thesis
      proof (induction rule: reduce_simple.induct)
        case (trap es lholed)
        show ?case
          using trap(2)
        proof (cases rule: Lfilled.cases)
          case (L0 vs es')
          thus ?thesis
            using trap(3) list_all_append const_list_cons_last(2)[of "($C*vs)" Trap]
            unfolding const_list_def
            by (simp add: is_const_def)
        next
          case (LN vs n es' l es'' k lfilledk)
          thus ?thesis
            by (simp add: is_const_def)
        qed
      qed (fastforce simp add: const_list_cons_last(2) is_const_def const_list_def)+
    next
      case (label s f es s' f' es' k lholed les les')
      show ?case
        using label(2)
      proof (cases rule: Lfilled.cases)
        case (L0 vs es')
        thus ?thesis
          using label(4,5) list_all_append
          unfolding const_list_def
          by fastforce
      next
        case (LN vs n es' l es'' k lfilledk)
        thus ?thesis
          using label(4,5)
          unfolding const_list_def
          by (simp add: is_const_def)
      qed
    qed (fastforce simp add: const_list_cons_last(2) is_const_def const_list_def)+
  }
  thus ?thesis
    by blast
qed

lemma empty_no_progress:
  assumes "es = []"
  shows "\<not>\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
proof -
  {
    assume "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    hence False
      using assms
    proof (induction rule: reduce.induct)
      case (basic e e' s vs)
      thus ?thesis
      proof (induction rule: reduce_simple.induct)
        case (trap es lholed)
        thus ?case
          using Lfilled.simps[of 0 lholed "[Trap]" es]
          by auto
      qed auto
    next
      case (label s f es s' f' es' k lholed les les')
      thus ?case
          using Lfilled.simps[of k lholed es "[]"]
          by auto
    qed auto
  }
  thus ?thesis
    by blast
qed
      
lemma trap_no_progress:
  assumes "es = [Trap]"
  shows "\<not>\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
proof -
  {
    assume "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    hence False
      using assms
    proof (induction rule: reduce.induct)
      case (basic e e' s vs)
      thus ?case
      by (induction rule: reduce_simple.induct) auto
    next
      case (label s f es s' f' es' k lholed les les')
      show ?case
        using label(2)
        proof (cases rule: Lfilled.cases)
          case (L0 vs es')
          show ?thesis
            using L0(2) label(1,4,5) empty_no_progress
            by (auto simp add: Cons_eq_append_conv)
        next
          case (LN vs n es' l es'' k' lfilledk)
          show ?thesis
            using LN(2) label(5)
            by (simp add: Cons_eq_append_conv)
        qed
    qed auto
  }
  thus ?thesis
    by blast
qed

lemma terminal_no_progress:
  assumes "const_list es \<or> es = [Trap]"
  shows "\<not>\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using const_list_no_progress trap_no_progress assms
  by blast

lemma progress_L0:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "\<lparr>s;f;($C*vs)@es@es_c\<rparr> \<leadsto> \<lparr>s';f';($C*vs)@es'@es_c\<rparr>"
proof -
  have "\<And>es. Lfilled 0 (LBase vs es_c) es (($C*vs)@es@es_c)"
    using Lfilled.intros(1)[of "(LBase vs es_c)" vs es_c]
    unfolding const_list_def
    by fastforce
  thus ?thesis
    using assms label
    by blast
qed

lemma progress_L1:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "\<lparr>s;f;($C*vs)@[Label n esl es]@es_c\<rparr> \<leadsto> \<lparr>s';f';($C*vs)@[Label n esl es']@es_c\<rparr>"
proof -
  have "\<And>es. Lfilled 1 (LRec vs n esl (LBase [] []) es_c) es (($C*vs)@[Label n esl es]@es_c)"
    using Lfilled.intros(2)[of "((LRec vs n esl (LBase [] []) es_c))"]
          Lfilled.intros(1)[of "(LBase [] [])"]
    unfolding const_list_def
    by fastforce
  thus ?thesis
    using label assms(1)
    by blast
qed

lemma progress_L0_left:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "\<lparr>s;f;($C*vs)@es\<rparr> \<leadsto> \<lparr>s';f';($C*vs)@es'\<rparr>"
  using assms progress_L0[where ?es_c = "[]"]
  by fastforce

lemma progress_L0_trap:
  assumes "vs \<noteq> [] \<or> es \<noteq> []"
  shows "\<exists>a. \<lparr>s;f;($C*vs)@[Trap]@es\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
proof -
  have "($C*vs) @ [Trap] @ es \<noteq> [Trap]"
    using assms
    by (cases "vs = []") (auto simp add: append_eq_Cons_conv)
  thus ?thesis
    using reduce.intros(1) assms reduce_simple.trap
          Lfilled.intros(1)[ of _ _ es "[Trap]"]
    by blast
qed

lemma progress_LN:
  assumes "(Lfilled j lholed [$Br (j+k)] es)"
          "s\<bullet>\<C> \<turnstile> es : ([] _> ts)"
          "(label \<C>)!k = tvs"
  shows "\<exists>lholed' vs \<C>'. (Lfilled j lholed' (($C*vs)@[$Br (j+k)]) es)
                    \<and> (s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tvs))"
  using assms
proof (induction "[$Br (j+k)]" es arbitrary: k \<C> ts rule: Lfilled.induct)
  case (L0 lholed vs es')
  obtain ts' ts'' where ts_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> ts')"
                                 "s\<bullet>\<C> \<turnstile> [$Br k] : (ts' _> ts'')"
                                 "s\<bullet>\<C> \<turnstile> es' : (ts'' _> ts)"
    using e_type_comp_conc2[OF L0(2)]
    by fastforce
  obtain ts_c ts''' where "ts_c @ tvs _> ts''' <ti: ts' _> ts''"
    using b_e_type_br[of \<C> "Br k" ts' ts''] L0(2,3) ts_def(2) unlift_b_e
    by fastforce
  then obtain ts_c' ts''' where "ts' = ts_c'@ts'''" "t_list_subtyping ts''' (ts_c @ tvs)"
    unfolding instr_subtyping_def
    by auto
  then have "t_list_subtyping ts' (ts_c'@ts_c@tvs)"
    using t_list_subtyping_prepend by blast
  then have "s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> (ts_c'@ts_c@tvs))"
    by (metis append_self_conv2 e_typing_thread_typing.intros(3) instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2) ts_def(1))
  then obtain vs1 vs2 where vs_def:"s\<bullet>\<C> \<turnstile> ($C*vs1) : ([] _> ts_c'@ts_c)"
                                   "s\<bullet>\<C> \<turnstile> ($C*vs2) : (ts_c'@ts_c _> ((ts_c'@ts_c)@tvs))"
                                   "vs = vs1@vs2"
    using e_type_consts_cons ts_def(1)
    by (metis append.assoc)
  hence "s\<bullet>\<C> \<turnstile> ($C*vs2) : ([] _> tvs)"
    using e_type_consts store_extension_refl
    by (meson e_typing_thread_typing.intros(3) instr_subtyping_append_split1) 
  thus ?case
    using Lfilled.intros(1)[of _ _ es' "($C*vs2)@[$Br k]"] vs_def
    by fastforce
next
  case (LN lholed vs n es' l es'' j lfilledk)
  obtain t1s t2s where ts_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> t1s)"
                               "s\<bullet>\<C> \<turnstile> [Label n es' lfilledk] : (t1s _> t2s)"
                               "s\<bullet>\<C> \<turnstile> es'' : (t2s _> ts)"
  using e_type_comp_conc2[OF LN(4)]
  by fastforce
  obtain ts' ts_l where ts_l_def:"s\<bullet>\<C>\<lparr>label := [ts'] @ label \<C>\<rparr> \<turnstile> lfilledk : ([] _> ts_l)"
    using e_type_label[OF ts_def(2)]
    by fastforce
  obtain lholed' vs' \<C>' where lfilledk_def:"Lfilled j lholed' (($C*vs') @ [$Br (j + (1 + k))]) lfilledk"
                                          "s\<bullet>\<C>' \<turnstile> ($C*vs') : ([] _> tvs)"
    using LN(3)[OF _ ts_l_def, of "1 + k"] LN(4,5)
    by fastforce
  thus ?case
    using Lfilled.intros(2)[OF _ lfilledk_def(1)]
    by fastforce
qed

lemma progress_LN_return:
  assumes "(Lfilled j lholed [$Return] es)"
          "s\<bullet>\<C> \<turnstile> es : ([] _> ts)"
          "(return \<C>) = Some tvs"
  shows "\<exists>lholed' vs \<C>'. (Lfilled j lholed' (($C*vs)@[$Return]) es)
                    \<and> (s\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> tvs))"
  using assms
proof (induction "[$Return]" es arbitrary: \<C> ts rule: Lfilled.induct)
  case (L0 lholed vs es')
  obtain ts' ts'' where ts_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> ts')"
                                 "s\<bullet>\<C> \<turnstile> [$Return] : (ts' _> ts'')"
                                 "s\<bullet>\<C> \<turnstile> es' : (ts'' _> ts)"
    using e_type_comp_conc2[OF L0(2)]
    by fastforce
  
  obtain ts_c ts''' where "ts_c @ tvs _> ts''' <ti: ts' _> ts''"
     using b_e_type_return[of \<C> "Return" ts' ts''] L0(2,3) ts_def(2) unlift_b_e
    by fastforce
  then obtain ts_c' ts''' where "ts' = ts_c'@ts'''" "t_list_subtyping ts''' (ts_c @ tvs)"
    unfolding instr_subtyping_def
    by auto
  then have "t_list_subtyping ts' (ts_c'@ts_c@tvs)"
    using t_list_subtyping_prepend by blast
  then have "s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> (ts_c'@ts_c@tvs))"
    by (metis append_self_conv2 e_typing_thread_typing.intros(3) instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2) ts_def(1))
  then obtain vs1 vs2 where vs_def:"s\<bullet>\<C> \<turnstile> ($C*vs1) : ([] _> (ts_c'@ts_c))"
                                   "s\<bullet>\<C> \<turnstile> ($C*vs2) : ((ts_c'@ts_c) _> ((ts_c'@ts_c)@tvs))"
                                   "vs = vs1@vs2"
    using e_type_consts_cons ts_def(1)
    by (metis append.assoc)
  hence "s\<bullet>\<C> \<turnstile> ($C*vs2) : ([] _> tvs)"
    using e_type_consts store_extension_refl
    by (meson e_typing_thread_typing.intros(3) instr_subtyping_append_split1) 
  thus ?case
    using Lfilled.intros(1)[of _ _ es' "($C*vs2)@[$Return]"] vs_def
    by fastforce
next
  case (LN lholed vs n es' l es'' j lfilledk)
  obtain t1s t2s where ts_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> t1s)"
                               "s\<bullet>\<C> \<turnstile> [Label n es' lfilledk] : (t1s _> t2s)"
                               "s\<bullet>\<C> \<turnstile> es'' : (t2s _> ts)"
  using e_type_comp_conc2[OF LN(4)]
  by fastforce
  obtain ts' ts_l where ts_l_def:"s\<bullet>\<C>\<lparr>label := [ts'] @ label \<C>\<rparr> \<turnstile> lfilledk : ([] _> ts_l)"
    using e_type_label[OF ts_def(2)]
    by fastforce
  obtain lholed' vs' \<C>' where lfilledk_def:"Lfilled j lholed' (($C*vs') @ [$Return]) lfilledk"
                                          "s\<bullet>\<C>' \<turnstile> ($C*vs') : ([] _> tvs)"
    using LN(3)[OF ts_l_def] LN(5)
    by fastforce
  thus ?case
    using Lfilled.intros(2) lfilledk_def(1)
    by fastforce
qed

lemma progress_LN1:
  assumes "(Lfilled j lholed [$Br (j+k)] es)"
          "s\<bullet>\<C> \<turnstile> es : (ts _> ts')"
  shows "length (label \<C>) > k"
  using assms
proof (induction "[$Br (j+k)]" es arbitrary: k \<C> ts ts' rule: Lfilled.induct)
  case (L0 lholed vs es')
  obtain ts'' ts''' where ts_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : (ts _> ts'')"
                               "s\<bullet>\<C> \<turnstile> [$Br k] : (ts'' _> ts''')"
                               "s\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc2[OF L0(2)]
    by fastforce
  thus ?case
    using b_e_type_br(1)[of _ "Br k" ts'' ts'''] unlift_b_e
    by fastforce
next
  case (LN lholed vs n es' l es'' k' lfilledk)
  obtain t1s t2s where ts_def:"s\<bullet>\<C> \<turnstile> ($C*vs) : (ts _> t1s)"
                               "s\<bullet>\<C> \<turnstile> [Label n es' lfilledk] : (t1s _> t2s)"
                               "s\<bullet>\<C> \<turnstile> es'' : (t2s _> ts')"
  using e_type_comp_conc2[OF LN(4)]
  by fastforce
  obtain ts'' ts_l where ts_l_def:"s\<bullet>\<C>\<lparr>label := [ts''] @ label \<C>\<rparr> \<turnstile> lfilledk : ([] _> ts_l)"
    using e_type_label[OF ts_def(2)]
    by fastforce
  thus ?case
    using LN(3)[of "1+k"]
    by fastforce
qed

lemma progress_LN2:
  assumes "(Lfilled j lholed e1s lfilled)"
  shows "\<exists>lfilled'. (Lfilled j lholed e2s lfilled')"
  using assms
proof (induction rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  thus ?case
    using Lfilled.intros(1)
    by fastforce
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma progress_label:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "\<lparr>s;f;[Label n les es]\<rparr> \<leadsto> \<lparr>s';f';[Label n les es']\<rparr>"
proof -
  have "Lfilled 1 (LRec [] n les (LBase [] []) []) es [Label n les es]"
    using Lfilled.intros(2) Lfilled.intros(1)[of "(LBase [] [])"]
    by (metis Nil_is_map_conv append_Nil append_Nil2 plus_nat.add_0)
  moreover
  have "Lfilled 1 (LRec [] n les (LBase [] []) []) es' [Label n les es']"
    using Lfilled.intros(2) Lfilled.intros(1)[of "(LBase [] [])"]
    by (metis Nil_is_map_conv append_Nil append_Nil2 plus_nat.add_0)
  ultimately
  show ?thesis
    using reduce.label[OF assms]
    by blast
qed

lemma const_of_const_list:
  assumes "length cs = 1"
          "const_list cs"
  shows "\<exists>v. cs = [$C v]"
  using e_type_const_unwrap assms
  unfolding const_list_def list_all_length
  by (metis append_butlast_last_id append_self_conv2 gr_zeroI last_conv_nth length_butlast
            length_greater_0_conv less_numeral_extra(1,4) zero_less_diff)

lemma const_of_i32:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [(T_num T_i32)])"
  shows "\<exists>c. vs = [V_num (ConstInt32 c)]"
proof -                    
  obtain v where "vs = [v]" "typeof v = T_num T_i32"
    using e_type_consts[OF assms] store_extension_refl
    by (metis assms list.inject list.simps(8) list.simps(9) neq_Nil_conv remdups_adj.cases typing_map_typeof)
  moreover
  hence "s\<bullet>\<C> \<turnstile> [$C v] : ([] _> [(T_num T_i32)])"
    using assms by fastforce
  ultimately
  show ?thesis
    by (simp add: typeof_def typeof_num_i32 split: v.splits)
qed

lemma const_of_i64:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [(T_num T_i64)])"
  shows "\<exists>c. vs = [V_num (ConstInt64 c)]"
proof -                    
  obtain v where "vs = [v]" "typeof v = T_num T_i64"
    using e_type_consts[OF assms] store_extension_refl
    by (metis assms list.inject list.simps(8) list.simps(9) neq_Nil_conv remdups_adj.cases typing_map_typeof)
  moreover
  hence "s\<bullet>\<C> \<turnstile> [$C v] : ([] _> [(T_num T_i64)])"
    using assms by fastforce
  ultimately
  show ?thesis
    by (simp add: typeof_def typeof_num_i64 split: v.splits)
qed

lemma const_of_f32:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [(T_num T_f32)])"
  shows "\<exists>c. vs = [V_num (ConstFloat32 c)]"
proof -                    
  obtain v where "vs = [v]" "typeof v = T_num T_f32"
    using e_type_consts[OF assms] store_extension_refl
    by (metis assms list.inject list.simps(8) list.simps(9) neq_Nil_conv remdups_adj.cases typing_map_typeof)
  moreover
  hence "s\<bullet>\<C> \<turnstile> [$C v] : ([] _> [(T_num T_f32)])"
    using assms by fastforce
  ultimately
  show ?thesis
    by (simp add: typeof_def typeof_num_f32 split: v.splits)
qed

lemma const_of_f64:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [(T_num T_f64)])"
  shows "\<exists>c. vs = [V_num (ConstFloat64 c)]"
proof -                    
  obtain v where "vs = [v]" "typeof v = T_num T_f64"
    using e_type_consts[OF assms] store_extension_refl
    by (metis assms list.inject list.simps(8) list.simps(9) neq_Nil_conv remdups_adj.cases typing_map_typeof)
  moreover
  hence "s\<bullet>\<C> \<turnstile> [$C v] : ([] _> [(T_num T_f64)])"
    using assms by fastforce
  ultimately
  show ?thesis
    by (simp add: typeof_def typeof_num_f64 split: v.splits)
qed

lemma const_of_v128:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [(T_vec T_v128)])"
  shows "\<exists>c. vs = [V_vec (ConstVec128 c)]"
proof -                    
  obtain v where "vs = [v]" "typeof v = T_vec T_v128"
    using e_type_consts[OF assms] store_extension_refl
    by (metis assms list.inject list.simps(8) list.simps(9) neq_Nil_conv remdups_adj.cases typing_map_typeof)
  moreover
  hence "s\<bullet>\<C> \<turnstile> [$C v] : ([] _> [(T_vec T_v128)])"
    using assms by fastforce
  ultimately
  show ?thesis
    by (simp add: typeof_def typeof_vec_def split: v.splits v_vec.splits)
qed

lemma const_of_typed_const_1:
  assumes "s\<bullet>\<C> \<turnstile> $C*cs : ([] _> [t])"
  shows "\<exists>v. cs = [v] \<and> t = typeof v"
  using typing_map_typeof[OF assms]
  by fastforce

lemma progress_testop:
  assumes "s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> [T_num t])"
          "e = Testop t testop"
        shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
proof -
  thm reduce.intros(1)[OF reduce_simple.intros(4)]
  obtain v where v_def: "vs = [v]" "T_num t = typeof v"
    using const_of_typed_const_1[OF assms(1)] by blast
  then obtain v_n where v_n_def: "V_num v_n = v"
    by (metis t.distinct(3) t.simps(5) typeof_def v.exhaust v.simps(11, 12))
  then have "\<lparr>s;f;[$C v] @ [$e]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (app_testop testop v_n)]\<rparr>"
    using reduce.intros(1)[OF reduce_simple.intros(4)]
    using assms(2) v_to_e_def by force
  then show ?thesis
    using v_def(1) by auto
qed

lemma progress_unop:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_num t])"
          "e = Unop t iop"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using reduce.intros(1)[OF reduce_simple.intros(1)] const_of_typed_const_1[OF assms(1)]
      assms(2)
      v_to_e_def
  unfolding typeof_def
  by (fastforce split: v.splits)

lemma progress_relop:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_num t, T_num t])"
          "e = Relop t rop"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using const_of_typed_const_2[OF assms(1)] assms(2) reduce_simple.intros(5) reduce.intros(1)
        v_to_e_def
  unfolding typeof_def
  by (fastforce split: v.splits)

lemma progress_binop:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_num t, T_num t])"
          "e = Binop t fop"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
proof -
  thm const_of_typed_const_2[OF assms(1)]
  obtain v1 v2 where v1_v2_def: "vs = [v1, v2]" "typeof v1 = T_num t \<and> typeof v2 = T_num t"
    using const_of_typed_const_2[OF assms(1)] by fastforce
  then obtain v1_n v2_n where v1_n_v2_n_def: "v1 = V_num v1_n" "v2 = V_num v2_n"
    by (metis t.simps(5,7) typeof_def v.exhaust v.simps(11,12))
  then show ?thesis
  proof(cases "app_binop fop (v1_n) (v2_n)")
    case None
    then have "\<lparr>[$C v1, $C v2] @ [$Binop t fop]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
      using reduce_simple.binop_None v1_n_v2_n_def(1) v1_n_v2_n_def(2) v_to_e_def by fastforce
    then show ?thesis using  assms(2) basic v1_v2_def(1) by fastforce
  next
    case (Some a)
    then have "\<lparr>[$C v1, $C v2] @ [$Binop t fop]\<rparr> \<leadsto> \<lparr>[$EConstNum a]\<rparr>"
      using binop_Some v1_n_v2_n_def(1) v1_n_v2_n_def(2) v_to_e_def by fastforce
    then show ?thesis using assms(2) basic v1_v2_def(1) by fastforce
  qed
qed


lemma progress_ref_is_null:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_ref t])"
          "e = Ref_is_null"
        shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
proof -
  obtain vs' v where vs'_v_def: "vs = vs'@[v]" "typeof v = T_ref t"
    by (metis append.left_neutral assms(1) const_of_typed_const_1)
  then obtain v_r where v_r_def: "v = V_ref v_r" "typeof_ref v_r = t"
     using typeof_ref_def typeof_def
     by (metis t.distinct(3) t.distinct(7) t.inject(3) v.exhaust v.simps(10) v.simps(11) v.simps(12))
  show ?thesis
  proof(cases "is_null_ref v_r")
    case True
    then have "\<lparr>s;f;($C* vs')@ [$C v] @ [$e]\<rparr>  \<leadsto> \<lparr>s;f;($C* vs')@[$EConstNum (ConstInt32 (wasm_bool True))]\<rparr>"
      using assms(2) basic is_null_true progress_L0_left v_r_def(1) v_to_e_def by auto
    then have "\<lparr>s;f;($C* vs) @ [$e]\<rparr>  \<leadsto> \<lparr>s;f;($C* vs')@[$EConstNum (ConstInt32 (wasm_bool True))]\<rparr>"
      by (simp add: vs'_v_def(1))
    then show ?thesis by blast
  next
    case False
    then have "\<lparr>s;f;($C* vs')@ [$C v] @ [$e]\<rparr>  \<leadsto> \<lparr>s;f;($C* vs')@[$EConstNum (ConstInt32 (wasm_bool False))]\<rparr>"
      using assms(2) basic is_null_false progress_L0_left v_r_def(1) v_to_e_def by auto
    then have "\<lparr>s;f;($C* vs) @ [$e]\<rparr>  \<leadsto> \<lparr>s;f;($C* vs')@[$EConstNum (ConstInt32 (wasm_bool False))]\<rparr>"
      by (simp add: vs'_v_def(1))
    then show ?thesis by blast
  qed
qed


lemma progress_unop_vec:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_vec t])"
          "e = Unop_vec op"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using reduce.intros(1)[OF reduce_simple.unop_vec] const_of_typed_const_1[OF assms(1)]
        assms(2)
        v_to_e_def
  unfolding typeof_def
  by (fastforce split: v.splits)

lemma progress_binop_vec:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_vec t, T_vec t])"
          "e = Binop_vec op"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
proof -
  obtain v1 v2 where v1_v2_def: "vs = [v1, v2]" "typeof v1 = T_vec t \<and> typeof v2 = T_vec t"
    using const_of_typed_const_2[OF assms(1)] by fastforce
  then obtain v1_v v2_v where v1_v_v2_v_def: "v1 = V_vec v1_v" "v2 = V_vec v2_v"
    by (metis t.distinct(7) t.simps(5) typeof_def v.exhaust v.simps(10,12))
  then show ?thesis
  proof(cases "app_binop_vec op (v1_v) (v2_v)")
    case None
    then have "\<lparr>[$C v1, $C v2] @ [$Binop_vec  op]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
      using reduce_simple.binop_vec_None v1_v_v2_v_def v_to_e_def by fastforce
    then show ?thesis
      using assms(2) basic v1_v2_def(1) by fastforce
  next
    case (Some a)
    then have "\<lparr>[$C v1, $C v2] @ [$Binop_vec  op]\<rparr> \<leadsto> \<lparr>[$EConstVec a]\<rparr>"
      using reduce_simple.binop_vec_Some v1_v_v2_v_def v_to_e_def by fastforce
    then show ?thesis
      using assms(2) basic v1_v2_def(1) by fastforce
  qed
qed

lemma progress_ternop_vec:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_vec t, T_vec t, T_vec t])"
          "e = Ternop_vec op"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using const_of_typed_const_3[OF assms(1)] assms(2) reduce_simple.ternop_vec reduce.intros(1)
        v_to_e_def
  unfolding typeof_def
  by (fastforce split: v.splits)

lemma progress_test_vec:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_vec t])"
          "e = Test_vec op"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using reduce.intros(1)[OF reduce_simple.test_vec] const_of_typed_const_1[OF assms(1)]
        assms(2)
        v_to_e_def
  unfolding typeof_def
  by (fastforce split: v.splits)

lemma progress_shift_vec:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_vec t, T_num T_i32])"
          "e = Shift_vec op"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using const_of_typed_const_2[OF assms(1)] assms(2) reduce_simple.shift_vec reduce.intros(1)
        v_to_e_def
  unfolding typeof_def typeof_num_def typeof_vec_def
  by (fastforce split: v.splits v_num.splits)

lemma progress_splat_vec:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_num v])"
          "e = Splat_vec sv"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using reduce.intros(1)[OF reduce_simple.splat_vec] const_of_typed_const_1[OF assms(1)]
        assms(2)
        v_to_e_def
  unfolding typeof_def
  by (fastforce split: v.splits)

lemma progress_extract_vec:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_vec v])"
          "e = Extract_vec sv sx i"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using reduce.intros(1)[OF reduce_simple.extract_vec] const_of_typed_const_1[OF assms(1)]
        assms(2)
        v_to_e_def
  unfolding typeof_def
  by (fastforce split: v.splits)

lemma progress_replace_vec:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [T_vec t, T_num t'])"
          "e = Replace_vec sv i"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@([$e])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using const_of_typed_const_2[OF assms(1)] assms(2) reduce_simple.replace_vec reduce.intros(1)
        v_to_e_def
  unfolding typeof_def typeof_num_def typeof_vec_def
  by (fastforce split: v.splits v_num.splits)

lemma progress_b_e:
  assumes "\<C> \<turnstile> b_es : (ts _> ts')"
          "s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> ts)"
          "(\<And>lholed. \<not>(Lfilled 0 lholed [$Return] (($C*vs)@($*b_es))))"
          "\<And> i lholed. \<not>(Lfilled 0 lholed [$Br (i)] (($C*vs)@($*b_es)))"
          "\<not> const_list ($* b_es)"
          "length (local \<C>) = length (f_locs f)"
          "length (memory \<C>) = length (inst.mems (f_inst f))"
          "length (table \<C>) = length (inst.tabs (f_inst f))"
          "(types_t \<C>) = types (f_inst f)"
          "length (func_t \<C>) = length (inst.funcs (f_inst f))"
          "length (elem \<C>) = length (inst.elems (f_inst f))"
          "length (data \<C>) = length (inst.datas (f_inst f))"
  shows "\<exists>a s' f' es'. \<lparr>s;f;($C*vs)@($*b_es)\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using assms
proof (induction b_es "(ts _> ts')" arbitrary: ts ts' vs rule: b_e_typing.induct)
  case (const_num \<C> v)
  then show ?case
    unfolding const_list_def is_const_def
    by simp
next
  case (const_vec \<C> v)
  then show ?case
    unfolding const_list_def is_const_def
    by simp
next
  case (unop t \<C> uu)
  thus ?case
    using progress_unop
    by fastforce
next
  case (binop t \<C> uw)
  thus ?case
    using progress_binop
    by fastforce
next
  case (testop t \<C> uy)
  thus ?case
    using progress_testop
    by fastforce
next
  case (relop t \<C> uz)
  thus ?case
    using progress_relop
    by fastforce
next
  case (ref_null \<C> t)
  then show ?case
    by (metis basic null progress_L0_left to_e_list_1)
next
  case (ref_is_null \<C> t)
  then show ?case
    using progress_ref_is_null
    by fastforce
next
  case (ref_func j \<C>)
  then have "j < length (inst.funcs (f_inst f))" by simp

  obtain fj fi fj' where f_def:"fi = inst.funcs (f_inst f) ! j" "fj = (take j (inst.funcs (f_inst f)))" "fj' = (drop (j+1) (inst.funcs (f_inst f)))"
    by blast
  have j_def:"j < length (inst.funcs (f_inst f))"
    using ref_func.hyps ref_func.prems(9) by metis
  hence fj_len:"length fj = j"
    using f_def(2)
    by fastforce
  hence 1: "inst.funcs (f_inst f) = fj @ [fi] @ fj'"
    by (metis Cons_eq_appendI Suc_eq_plus1 append_eq_conv_conj append_self_conv2 drop_Suc_nth f_def(1) f_def(2) f_def(3) j_def)
  hence 2: "fi = inst.funcs (f_inst f) ! j"
    using f_def(1) by blast
  then have "\<lparr>s;f;[$Ref_func j]\<rparr>  \<leadsto> \<lparr>s;f;[Ref (ConstRefFunc fi)]\<rparr>"
    using reduce.ref_func[OF 2] by simp
  then show ?case
    by (metis progress_L0_left to_e_list_1)
next
  case (unop_vec \<C> op)
  thus ?case
    using progress_unop_vec
    by fastforce
next
  case (binop_vec \<C> op)
  thus ?case
    using progress_binop_vec
    by fastforce
next
  case (ternop_vec \<C> op)
  thus ?case
    using progress_ternop_vec
    by fastforce
next
  case (test_vec \<C> op)
  thus ?case
    using progress_test_vec
    by fastforce
next
  case (shift_vec \<C> op)
  thus ?case
    using progress_shift_vec
    by fastforce
next
  case (splat_vec \<C> sv)
  thus ?case
    using progress_splat_vec
    by fastforce
next
  case (extract_vec i sv sx \<C>)
  thus ?case
    using progress_extract_vec
    by fastforce
next
  case (replace_vec i sv \<C>)
  thus ?case
    using progress_replace_vec
    by fastforce
next
  case (convert t1 t2 sx \<C>)
  obtain v where cs_def:"vs = [V_num v]" "typeof_num v = t2"
    using const_of_typed_const_1 [OF convert(3)]
    by (metis (no_types, lifting) append_self_conv list.simps(9) local.convert(3) map_append t.inject(1) t.simps(5) t.simps(7) type_const_v_typing(2) v_typing.simps)
  thus ?case
  proof (cases "cvt t1 sx v")
    case None
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.convert_None[OF _ None]] cs_def v_to_e_def
      by fastforce
  next
    case (Some a)
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.convert_Some[OF _ Some]] cs_def v_to_e_def
      by fastforce
  qed
next
  case (reinterpret t1 t2 \<C>)
  obtain v where cs_def:"vs = [V_num v]" "typeof_num v = t2"
    using const_of_typed_const_1 [OF reinterpret(3)]
    by (metis e_typing_imp_list_v_typing(1) list.pred_inject(2) reinterpret.prems(1) t.inject(1) t.simps(5) t.simps(7) v_typing.simps)
  thus ?case
    using reduce.intros(1)[OF reduce_simple.reinterpret] v_to_e_def
    by fastforce
next
  case (unreachable \<C> ts ts')
  thus ?case
    using reduce.intros(1)[OF reduce_simple.unreachable] progress_L0
    by fastforce
next
  case (nop \<C>)
  thus ?case
    using reduce.intros(1)[OF reduce_simple.nop] progress_L0
    by fastforce
next
  case (drop \<C> t)
  obtain v where "vs = [v]"
    using const_of_typed_const_1 drop.prems(1) by blast 
  thus ?case
    using reduce.intros(1)[OF reduce_simple.drop] progress_L0
    by fastforce
next
  case (select t_tag t \<C>)
  obtain v1 v2 v3 where cs_def:"s\<bullet>\<C> \<turnstile> [$C v3] : ([] _> [T_num T_i32])"
                               "vs = [v1, v2, v3]"
    using const_list_split_3 select.prems(1) by blast
  obtain c3 where c_def:"v3 = V_num (ConstInt32 c3)"
    using select(4) const_typeof[OF cs_def(1)] typeof_num_i32
    unfolding typeof_def
    by (auto split: v.splits)
  have "\<exists>a s' f' es'. \<lparr>s;f;[$C v1, $C v2, $ EConstNum (ConstInt32 c3), $Select t_tag]\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  proof (cases "int_eq c3 0")
    case True
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.select_false]
      by fastforce
  next
    case False
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.select_true]
      by fastforce
  qed
  thus ?case
    using c_def cs_def v_to_e_def
    by fastforce
next
  case (block \<C> tb tn tm es)
  have "tb_tf (f_inst f) tb = (tn _> tm)"
    using block(1,11)
    by (simp add: tb_tf_def tb_tf_t_def Let_def split: if_splits option.splits tb.splits)
  thus ?case
    using reduce.block e_type_consts[OF block(4)] store_extension_refl
    by (metis block.prems(1) length_map to_e_list_1 typing_map_typeof)
next
  case (loop \<C> tb tn tm es)
  have "tb_tf (f_inst f) tb = (tn _> tm)"
    using loop(1,11)
    by (simp add: tb_tf_def tb_tf_t_def Let_def split: if_splits option.splits tb.splits)
  thus ?case
    using reduce.loop e_type_consts[OF loop(4)] store_extension_refl
    by (metis loop.prems(1) length_map to_e_list_1 typing_map_typeof)
next
  case (if_wasm \<C> tb tn tm es1 es2)
  obtain c1s c2s where cs_def:"s\<bullet>\<C> \<turnstile> $C*c1s : ([] _> tn)"
                              "s\<bullet>\<C> \<turnstile> $C*c2s : ([] _> [T_num T_i32])"
                              "vs = c1s @ c2s"
    using e_type_consts_cons[OF if_wasm(6)] e_typing_imp_list_types_agree list_types_agree_imp_e_typing
    by (metis e_type_consts if_wasm.prems(1) map_append same_append_eq store_extension_refl typing_map_typeof)
  obtain c where c_def: "c2s = [V_num (ConstInt32 c)]"
    using const_of_i32 cs_def
    by fastforce
  have "\<exists>a s' f' es'. \<lparr>s;f;[$ EConstNum (ConstInt32 c), $ If tb es1 es2]\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  proof (cases "int_eq c 0")
    case True
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.if_false]
      by fastforce
  next
    case False
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.if_true]
      by fastforce
  qed
  thus ?case
    using c_def cs_def progress_L0 v_to_e_def
    by fastforce
next
  case (br i \<C> ts t1s t2s)
  thus ?case
    using Lfilled.intros(1)[of _ _ "[]" "[$Br i]"]
    by fastforce
next
  case (br_if j \<C> ts)
  obtain cs1 cs2 where cs_def:"s\<bullet>\<C> \<turnstile> $C*cs1 : ([] _> ts)"
                              "s\<bullet>\<C> \<turnstile> $C*cs2 : ([] _> [T_num T_i32])"
                              "vs = cs1 @ cs2"
    using e_type_consts_cons[OF br_if(3)]
    by (metis br_if.prems(1) e_type_consts map_append same_append_eq store_extension_refl typing_map_typeof)
  obtain c where c_def:"cs2 = [V_num (ConstInt32 c)]"
    using const_of_i32[OF cs_def(2)]
    by blast
  have "\<exists>a s' f' es'. \<lparr>s;f;($C*cs2)@($* [Br_if j])\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  proof (cases "int_eq c 0")
    case True
    thus ?thesis
      using c_def reduce.intros(1)[OF reduce_simple.br_if_false] v_to_e_def
      by fastforce
  next
    case False
    thus ?thesis
      using c_def reduce.intros(1)[OF reduce_simple.br_if_true] v_to_e_def
      by fastforce
  qed
  thus ?case
    using cs_def(3) progress_L0[of _ _"($C*cs2) @ ($* [Br_if j])"]
    by fastforce
next
  case (br_table \<C> ts "is" i' t1s t2s)
  then have 1: "s\<bullet>\<C> \<turnstile> $C* vs : [] _> (t1s @ ts) @ [T_num T_i32]" by simp
  obtain cs1 cs2 where cs_def:"s\<bullet>\<C> \<turnstile> $C*cs1 : ([]_> (t1s @ ts))"
                              "s\<bullet>\<C> \<turnstile> $C*cs2 : ([] _> [T_num T_i32])"
                              "vs = cs1 @ cs2"
    using e_type_consts_cons[OF 1] e_type_consts e_typing_thread_typing.intros(3) instr_subtyping_append_split1 store_extension_refl by blast
  obtain c where c_def:"cs2 = [V_num (ConstInt32 c)]"
    using const_of_i32[OF cs_def(2)]
    by blast
  have "\<exists>a s' f' es'. \<lparr>s;f;[$EConstNum (ConstInt32 c), $Br_table is i']\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  proof (cases "(nat_of_int c) < length is")
    case True
    show ?thesis
      using reduce.intros(1)[OF reduce_simple.br_table[OF True]]
      by fastforce
  next
    case False
    hence "length is \<le> nat_of_int c"
      by fastforce
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.br_table_length]
      by fastforce
  qed
  thus ?case
    using c_def cs_def progress_L0 v_to_e_def
    by fastforce
next
  case (return \<C> ts t1s t2s)
  thus ?case
    using Lfilled.intros(1)[of _ _ "[]" "[$Return]"]
    by fastforce
next
  case (call j \<C>)
  show ?case
    using progress_L0[OF reduce.intros(2)]
    by fastforce
next
  case (call_indirect i \<C> t1s t2s ti uv)
  obtain cs1 cs2 where cs_def:"s\<bullet>\<C> \<turnstile> $C*cs1 : ([]_> t1s)"
                              "s\<bullet>\<C> \<turnstile> $C*cs2 : ([] _> [T_num T_i32])"
                              "vs = cs1 @ cs2"
    using e_type_consts_cons[OF call_indirect.prems(1)] e_type_consts_cons e_type_consts store_extension_refl 
    by (metis call_indirect.prems(1) map_append same_append_eq typing_map_typeof)
  obtain c where c_def:"cs2 = [V_num (ConstInt32 c)]"
    using cs_def(2) const_of_i32
    by fastforce
  consider 
    (1) "\<exists>i_cl tf. stab s (f_inst f) ti (nat_of_int c) = Some (ConstRefFunc i_cl) \<and> stypes (f_inst f) i = tf \<and> cl_type (funcs s!i_cl) = tf"
  | (2) "\<exists>i_cl. stab s (f_inst f) ti (nat_of_int c) = Some (ConstRefFunc i_cl) \<and> stypes (f_inst f) i \<noteq> cl_type (funcs s!i_cl)"
  | (3) "\<not> is_some_const_ref_func(stab s (f_inst f) ti (nat_of_int c))"
    apply(auto simp add: is_some_const_ref_func_def split: v.splits)
    apply(cases "\<exists>i_cl. stab s (f_inst f) ti (nat_of_int c) = Some (ConstRefFunc i_cl)")
     apply fastforce
    by (simp add: is_some_const_ref_func_def split: option.splits v_ref.splits)
  hence "\<exists>a s' f' es'. \<lparr>s;f;[$EConstNum (ConstInt32 c), $(Call_indirect ti i)]\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  proof (cases)
    case 1
    thus ?thesis
      using reduce.intros(3)
      by blast
  next
    case 2
    thus ?thesis
      using reduce.intros(4)
      by blast
  next
    case 3
    thus ?thesis
      using reduce.intros(4)
      by blast
  qed
  then show ?case
    using c_def cs_def progress_L0 v_to_e_def
    by fastforce
next
  case (local_get j \<C> t)
  obtain v vj vj' where v_def:"v = (f_locs f) ! j" "vj = (take j (f_locs f))" "vj' = (drop (j+1) (f_locs f))"
    by blast
  have j_def:"j < length (f_locs f)"
    using local_get(1,7)
    by simp
  hence vj_len:"length vj = j"
    using v_def(2)
    by fastforce
  hence "(f_locs f) = vj @ [v] @ vj'"
    using v_def id_take_nth_drop j_def
    by fastforce
  thus ?case
    using progress_L0[OF reduce.intros(9), OF vj_len] vj_len local_get(6)
    by fastforce
next
  case (local_set j \<C> t)
  obtain v vj vj' where v_def:"v = (f_locs f) ! j" "vj = (take j (f_locs f))" "vj' = (drop (j+1) (f_locs f))"
    by blast
  obtain v' where cs_def: "vs = [v']"
    using local_set(3) const_of_typed_const_1
    by blast
  have j_def:"j < length (f_locs f)"
    using local_set(1,7)
    by simp
  hence vj_len:"length vj = j"
    using v_def(2)
    by fastforce
  hence "vj @ [v] @ vj' = (f_locs f)"
    using v_def id_take_nth_drop j_def
    by fastforce
  thus ?case
    using reduce.intros(10)[OF vj_len, of s v vj' "f_inst f" v'] cs_def
    apply simp
    apply (metis (full_types) f.surjective unit.exhaust)
    done
next
  case (local_tee i \<C> t)
  obtain v where "vs = [v]"
    using local_tee(3) const_of_typed_const_1
    by blast
  thus ?case
    using reduce.intros(1)[OF reduce_simple.local_tee] local_tee(6)
    unfolding const_list_def
    by fastforce
next
  case (global_get j \<C> t)
  thus ?case
    using reduce.intros(11)[of s _ j] progress_L0
    by fastforce
next
  case (global_set j \<C> t)
  obtain v where "vs = [v]"
    using global_set(4) const_of_typed_const_1
    by blast
  thus ?case
    using reduce.intros(12)[of s _ j v _]
    by fastforce
next
  case (load \<C> a tp_sx t off)
  obtain c where c_def: "vs = [V_num (ConstInt32 c)]"
    using const_of_i32 load(3,6) e_type_const_unwrap
    unfolding const_list_def
    by fastforce
  obtain j where mem_some:"smem_ind (f_inst f) = Some j"
    using load(1,8)
    unfolding smem_ind_def
    by (fastforce split: list.splits)
  have "\<exists>a' s' f' es'. \<lparr>s;f;[$EConstNum (ConstInt32 c), $Load t tp_sx a off]\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  proof (cases tp_sx)
    case None
    note tp_none = None
    show ?thesis
    proof (cases "load ((mems s)!j) (nat_of_int c) off (t_num_length t)")
      case None
      show ?thesis
        using reduce.intros(14)[OF mem_some _ None] tp_none load(2)
        by fastforce
    next
      case (Some a)
      show ?thesis
        using reduce.intros(13)[OF mem_some _ Some] tp_none load(2)
        by fastforce
    qed
  next
    case (Some a)
    obtain tp sx where tp_some:"tp_sx = Some (tp, sx)"
      using Some
      by fastforce
    show ?thesis
    proof (cases "load_packed sx ((mems s)!j) (nat_of_int c) off (tp_num_length tp) (t_num_length t)")
      case None
      show ?thesis
        using reduce.intros(16)[OF mem_some _ None] tp_some load(2)
        by fastforce
    next
      case (Some a)
      show ?thesis
        using reduce.intros(15)[OF mem_some _ Some] tp_some load(2)
        by fastforce
    qed
  qed
  then show ?case
    using c_def progress_L0 v_to_e_def
    by fastforce
next
  case (store \<C> a tp t off)
  obtain vs' v where cs_def:"s\<bullet>\<C> \<turnstile> [$C vs'] : ([] _> [T_num T_i32])"
                            "s\<bullet>\<C> \<turnstile> [$C v] : ([] _> [T_num t])"
                            "vs = [vs',v]"
    using const_list_split_2[OF store(3)] e_type_const_unwrap
    unfolding const_list_def v_to_e_def
    by fastforce
  have t_def:"typeof v = T_num t"
    using cs_def(2) b_e_type_cnum[OF unlift_b_e[of s \<C> "[C v]" "([] _> [T_num t])"]] const_typeof
    by fastforce
  obtain j where mem_some:"smem_ind (f_inst f) = Some j"
    using store(1,8)
    unfolding smem_ind_def
    by (fastforce split: list.splits)
  obtain c v_num where c_def:"vs' = V_num (ConstInt32 c)"
                             "v = V_num v_num"
                             "typeof_num v_num = t"
    using const_typeof[OF cs_def(1)] const_typeof[OF cs_def(2)] typeof_num_i32
    unfolding typeof_def
    by (fastforce split: v.splits)
  have "\<exists>a' s' f' es'. \<lparr>s;f;[$EConstNum (ConstInt32 c), $EConstNum v_num, $Store t tp a off]\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  proof (cases tp)
    case None
    note tp_none = None
    show ?thesis
    proof (cases "store (s.mems s ! j) (nat_of_int c) off (bits_num v_num) (t_num_length t)")
      case None
      show ?thesis
        using reduce.intros(18) mem_some None t_def tp_none store(2) c_def(3)
        by blast
    next
      case (Some a)
      show ?thesis
        using reduce.intros(17)[OF _ mem_some _ Some] t_def tp_none store(2) c_def(3)
        by blast
    qed
  next
    case (Some a)
    note tp_some = Some
    show ?thesis
    proof (cases "store_packed (s.mems s ! j) (nat_of_int c) off (bits_num v_num) (tp_num_length a)")
      case None
      show ?thesis
        using reduce.intros(20) mem_some None t_def tp_some store(2) c_def(3)
        by blast
    next
      case (Some a)
      show ?thesis
        using reduce.intros(19) mem_some Some t_def tp_some store(2) c_def(3)
        by blast
    qed
  qed
  then show ?case
    using c_def cs_def progress_L0 v_to_e_def
    by fastforce
next
  case (load_vec \<C> lvop a off)
  obtain c where c_def: "vs = [V_num (ConstInt32 c)]"
    using const_of_i32 load_vec(3,6) e_type_const_unwrap
    unfolding const_list_def
    by fastforce
  obtain j where mem_some:"smem_ind (f_inst f) = Some j"
    using load_vec(1,8)
    unfolding smem_ind_def
    by (fastforce split: list.splits)
  show ?case
  proof (cases "load_vec lvop ((mems s)!j) (nat_of_int c) off")
    case None
    thus ?thesis
      using reduce.load_vec_None[OF mem_some _ None] c_def v_to_e_def
      by fastforce
  next
    case (Some a)
    thus ?thesis
      using reduce.load_vec_Some c_def mem_some v_to_e_def
      by fastforce
  qed
next
  case (load_lane_vec \<C> i svi a off)
  obtain vs' v where cs_def:"s\<bullet>\<C> \<turnstile> [$C vs'] : ([] _> [T_num T_i32])"
                            "s\<bullet>\<C> \<turnstile> [$C v] : ([] _> [T_vec T_v128])"
                            "vs = [vs',v]"
    using const_list_split_2[OF load_lane_vec(3)] e_type_const_unwrap
    unfolding const_list_def
    by fastforce
  obtain c vv where c_is:"vs' = V_num (ConstInt32 c)"
                         "v = V_vec (ConstVec128 vv)"
    using cs_def(1,2) const_of_i32[of _ _ "[vs']"] const_of_v128[of _ _ "[v]"]
    by fastforce
  obtain j where mem_some:"smem_ind (f_inst f) = Some j"
    using load_lane_vec(1,8)
    unfolding smem_ind_def
    by (fastforce split: list.splits)
  thus ?case
  proof (cases "load ((mems s)!j) (nat_of_int c) off (vec_i_length svi)")
    case None
    show ?thesis
      using reduce.load_lane_vec_None[OF mem_some _ None] cs_def(3) c_is v_to_e_def
      by fastforce
  next
    case (Some a)
    show ?thesis
      using reduce.load_lane_vec_Some[OF mem_some _ Some] cs_def(3) c_is v_to_e_def
      by fastforce
  qed
next
  case (store_vec \<C> sv a off)
  obtain vs' v where cs_def:"s\<bullet>\<C> \<turnstile> [$C vs'] : ([] _> [T_num T_i32])"
                            "s\<bullet>\<C> \<turnstile> [$C v] : ([] _> [T_vec T_v128])"
                            "vs = [vs',v]"
    using const_list_split_2[OF store_vec(3)] e_type_const_unwrap
    unfolding const_list_def
    by fastforce
  obtain c vv where c_is:"vs' = V_num (ConstInt32 c)"
                         "v = V_vec (ConstVec128 vv)"
    using cs_def(1,2) const_of_i32[of _ _ "[vs']"] const_of_v128[of _ _ "[v]"]
    by fastforce
  obtain j where mem_some:"smem_ind (f_inst f) = Some j"
    using store_vec(1,8)
    unfolding smem_ind_def
    by (fastforce split: list.splits)
  show ?case
  proof (cases "store ((mems s)!j) (nat_of_int c) off (store_serialise_vec sv vv) (length (store_serialise_vec sv vv))")
    case None
    show ?thesis
      using reduce.store_vec_None[OF mem_some _ _ None] cs_def(3) c_is v_to_e_def
      by fastforce
  next
    case (Some a)
    show ?thesis
      using reduce.store_vec_Some[OF mem_some _ _ Some] cs_def(3) c_is v_to_e_def
      by fastforce
  qed
next
  case (memory_size \<C>)
  obtain j where mem_some:"smem_ind (f_inst f) = Some j"
    using memory_size(1,7)
    unfolding smem_ind_def
    by (fastforce split: list.splits)
  thus ?case
    using progress_L0[OF reduce.memory_size[OF mem_some]]
    by fastforce
next
  case (memory_grow \<C>)
  obtain c where c_def:"vs = [V_num (ConstInt32 c)]"
    using const_of_i32 memory_grow(2,5)
    by fastforce
  obtain j where mem_some:"smem_ind (f_inst f) = Some j"
    using memory_grow(1,7)
    unfolding smem_ind_def
    by (fastforce split: list.splits)
  show ?case
    using reduce.memory_grow_fail[OF mem_some, of _] c_def v_to_e_def
    by fastforce
next
  case (table_set ti \<C> tr)
  obtain n vr where c_def:"vs = [V_num (ConstInt32 n), V_ref vr]"
    by (metis (no_types, lifting) const_list_split_2 const_of_typed_const_2 list.inject local.table_set(3) t.simps(1,5,7,10) type_const_v_typing(2) typeof_num_i32 v_typing.simps)
  then show ?case
  proof(cases "stab_ind (f_inst f) ti")
    case None
    then show ?thesis using reduce.table_set_fail
      using stab_ind_def table_set.hyps(1) table_set.prems(7) by fastforce
  next
    case (Some a)
    then have h1: "stab_ind (f_inst f) ti = Some a" by simp
    then show ?thesis
    proof(cases " store_tabs1 (tabs s) a (nat_of_int n) vr")
      case None
      then have "stab_ind (f_inst f) ti = Some a \<and> store_tabs1 (s.tabs s) a (nat_of_int n) vr = None"
        using h1 by simp
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 n), Ref vr, $Table_set ti]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
        using reduce.table_set_fail by blast
      then show ?thesis using c_def v_to_e_def by auto
    next
      case (Some tabs')
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 n), Ref vr, $Table_set ti]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:= tabs'\<rparr>;f;[]\<rparr>"
        using reduce.table_set h1 by blast
      then show ?thesis using c_def v_to_e_def by auto
    qed
  qed
next
  case (table_get ti \<C> tr)
  obtain n where n_def:"vs = [V_num (ConstInt32 n)]"
    using const_of_i32 table_get.prems(1) by blast
  then show ?case
  proof(cases "stab_ind (f_inst f) ti")
    case None
    then show ?thesis using table_get_fail
      using stab_ind_def table_get.hyps(1) table_get.prems(7) by fastforce
  next
    case (Some a)
    then have h1: "stab_ind (f_inst f) ti = Some a" by blast
    then show ?thesis
    proof(cases "load_tabs1 (tabs s) a (nat_of_int n)")
      case None
      then show ?thesis
        using n_def v_to_e_def reduce.table_get_fail[OF h1 None] by fastforce
    next
      case (Some val)
      then show ?thesis using reduce.table_get h1
        using n_def v_to_e_def by fastforce
    qed
  qed
next
  case (table_size ti \<C>)
  obtain a where a_def: "stab_ind (f_inst f) ti = Some a"
    using stab_ind_def table_size.hyps table_size.prems(7) by auto
  then obtain t n where t_n_def: "(tabs s)!a = t" "tab_size t = n" by auto
  then show ?case using reduce.table_size[OF a_def t_n_def(1,2)]
    by (metis progress_L0_left to_e_list_1)
next
  case (table_grow ti \<C> tr)
  then obtain v1 v2 where cs_def:"s\<bullet>\<C> \<turnstile> [$C v1] : ([] _> [T_ref tr])"
                            "s\<bullet>\<C> \<turnstile> [$C v2] : ([] _> [T_num T_i32])"
                            "vs = [v1,v2]"
    using const_list_split_2[OF table_grow(3)] e_type_const_unwrap
    by blast
  then obtain vr n where "vs = [V_ref vr, V_num (ConstInt32 n)]"
    by (metis const_typeof t.distinct(7) t.inject(1) t.simps(5,7) type_const_v_typing(2) typeof_num_i32 v_typing.simps)
  then show ?case using reduce.table_grow_fail[of s f vr n ti]
    using v_to_e_def by fastforce
next
  case (empty \<C>)
  thus ?case
    unfolding const_list_def
    by simp
next
  case (composition \<C> es t1s t2s e t3s)
  consider (1) "\<not> const_list ($* es)" | (2) "const_list ($* es)" "\<not> const_list ($*[e])"
    using composition(8)
    unfolding const_list_def
    by fastforce
  thus ?case
  proof (cases)
    case 1
    have "(\<And>lholed. \<not> Lfilled 0 lholed [$Return] (($C*vs) @ ($* es)))"
         "(\<And>i lholed. \<not> Lfilled 0 lholed [$Br i] (($C*vs) @ ($* es)))"
    proof safe
      fix lholed
      assume "Lfilled 0 lholed [$Return] (($C*vs) @ ($* es))"
      hence "\<exists>lholed'. Lfilled 0 lholed' [$Return] (($C*vs) @ ($* es @ [e]))"
      proof (cases rule: Lfilled.cases)
        case (L0 vs es')
        thus ?thesis
          using Lfilled.intros(1)[of _ "vs" "es'@ ($*[e])" "[$Return]"]
          by (metis append.assoc map_append)
      qed simp
      thus False
        using composition(6)
        by simp
    next
      fix i lholed
      assume "Lfilled 0 lholed [$Br i] (($C*vs) @ ($* es))"
      hence "\<exists>lholed'. Lfilled 0 lholed' [$Br i] (($C*vs) @ ($* es @ [e]))"
      proof (cases rule: Lfilled.cases)
        case (L0 vs es')
        thus ?thesis
          using Lfilled.intros(1)[of _ "vs" "es'@ ($*[e])" "[$Br i]"]
          by (metis append.assoc map_append)
      qed simp
      thus False
        using composition(7)
        by simp
    qed
    thus ?thesis
      using composition(9,10,11,12,13,14,15) composition(2)[OF composition(5) _ _ 1]
            progress_L0[of s _ "(($C*vs) @ ($* es))" _ _ _ "[]" "[$e]"]
      unfolding const_list_def
      by fastforce
  next
    case 2
    then obtain ves where "($* es) = $C* ves"
      using e_type_const_conv_vs
      by blast
    moreover
    hence "s\<bullet>\<C> \<turnstile> ($C*(vs@ves)) : ([] _> t2s)"
      using composition(5) e_typing_thread_typing.intros(1)[OF composition(1)] e_type_comp_conc
      by fastforce
    ultimately
    show ?thesis
      using composition(4)[of "(vs@ves)"] 2(2) composition
      by fastforce
  qed
next
  case (subsumption \<C> es tf1 tf2 tf1' tf2')
  have 1: "tf1' = map typeof vs"
    using  subsumption(4) typing_map_typeof by fastforce
  then obtain "ts" "tf1_dom_sub" where ts_def: "tf1' = ts @ tf1_dom_sub"  "t_list_subtyping tf1_dom_sub tf1"
    using subsumption(3) unfolding instr_subtyping_def
    by auto
  have tf1_eq: "tf1_dom_sub = tf1"
  proof -
    obtain cs where "map typeof cs = tf1_dom_sub" using 1 ts_def
      by (metis map_eq_append_conv)
    then have "list_all (\<lambda> t. t \<noteq>  T_bot) tf1_dom_sub" using typeof_not_bot
      by (metis (mono_tags, lifting) length_map list_all_length nth_map)
    then show ?thesis using ts_def(2)  t_list_subtyping_not_bot_eq by auto
  qed
  obtain cs1 cs2 where cs_def:"s\<bullet>\<C> \<turnstile> $C*cs1 : ([] _> ts)"
                              "s\<bullet>\<C> \<turnstile> $C*cs2 : (ts _> tf1')"
                              "vs = cs1 @ cs2"
    using e_type_consts_cons[of s \<C> vs ts tf1] subsumption(4) ts_def tf1_eq
    by blast
  then have cs_typeof: "map typeof cs2 = tf1" "map typeof cs1 = ts"
    using typing_map_typeof "1" tf1_eq ts_def(1) by fastforce+
  then have cs2_typing: "s\<bullet>\<C> \<turnstile> $C*cs2 : ([] _> tf1)"
    using cs_def e_type_consts store_extension_refl by blast
  have "(\<And>lholed. \<not> Lfilled 0 lholed [$Return] (($C*cs2) @ ($* es)))"
       "(\<And>i lholed. \<not> Lfilled 0 lholed [$Br i] (($C*cs2) @ ($* es)))"
  proof safe
    fix lholed
    assume "Lfilled 0 lholed [$Return] (($C*cs2) @ ($* es))"
    hence "\<exists>lholed'. Lfilled 0 lholed' [$Return] (($C*cs1) @ ($C*cs2) @ ($* es))"
    proof (cases rule: Lfilled.cases)
      case (L0 vs es')
      thus ?thesis
        using Lfilled.intros(1)[of _ _ "es'" "[$Return]"] lfilled_lfilled_app
        by fastforce
    qed simp
    thus False
      using subsumption(5) cs_def(3)
      by simp
  next
    fix i lholed
    assume "Lfilled 0 lholed [$Br i] (($C* cs2) @ ($* es))"
    hence "\<exists>lholed'. Lfilled 0 lholed' [$Br i] (($C* cs1) @ ($C* cs2) @ ($* es))"
    proof (cases rule: Lfilled.cases)
      case (L0 vs es')
      thus ?thesis
        using Lfilled.intros(1)[of _ _ "es'" "[$Br i]"] lfilled_lfilled_app
        by fastforce
    qed simp
    thus False
      using subsumption(6) cs_def(3)
      by simp
  qed
  hence "\<exists>a s' f' es'. \<lparr>s;f;($C* cs2)@($*es)\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    using subsumption(2)[OF cs2_typing _ _] subsumption(7-)
    by fastforce
  thus ?case
    using progress_L0[of s f "($C* cs2) @ ($* es)" _ _ _ "cs1" "[]"] cs_def(3)
    by fastforce
next
  case (memory_init \<C> x)
  obtain vdest vsrc vn where
    "s\<bullet>\<C> \<turnstile> $C* [vdest] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vsrc] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vn] : ([] _> [T_num T_i32])"
    "vs = [vdest, vsrc, vn]"
    using const_list_split_3[OF memory_init(3)]
    by fastforce
  then obtain dest src n where v_defs:
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 dest)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 src)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 n)] : ([] _> [T_num T_i32])"
    "vdest = V_num (ConstInt32 dest)"
    "vsrc = V_num (ConstInt32 src)"
    "vn = V_num (ConstInt32 n)"
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    using const_of_i32 list.inject
    by metis
  obtain ndest nsrc nn where n_defs:
    "ndest = nat_of_int dest"
    "nsrc = nat_of_int src"
    "nn = nat_of_int n"
    by fastforce
  obtain ma m where m_defs:
    "smem_ind (f_inst f) = Some ma"
    "(mems s)!ma = m"
    using smem_ind_def memory_init.hyps(1) memory_init.prems(6) Suc_le_length_iff
    by (metis One_nat_def list.simps(5))
  obtain da dat where dat_defs:
    "da = (inst.datas (f_inst f))!x"
    "dat = (datas s)!da"
    by auto
  then show ?case
  proof(cases "nsrc+nn > length dat \<or>  ndest+nn > mem_length m")
    case True
    then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
        $Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
        using reduce.memory_init_trap[OF m_defs dat_defs n_defs True] memory_init.hyps(2) memory_init.prems(11)
      by metis
    then have "\<lparr>s;f;($C* vs) @ [$Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
      using v_defs
      by (simp add: v_to_e_def)
    then show ?thesis
      by (metis to_e_list_1)
  next
    case False
    then have h_bounds:"nsrc+nn\<le> length dat"  "ndest+nn \<le> mem_length m"
      by auto
    then show ?thesis
    proof(cases nn)
      case 0
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
        $Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
        using reduce.memory_init_done[OF m_defs dat_defs n_defs h_bounds 0] memory_init.hyps(2) memory_init.prems(11)
        by metis
      then have "\<lparr>s;f;($C* vs) @ [$Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
        using v_defs
        by (simp add: v_to_e_def)
      then show ?thesis
        by (metis to_e_list_1)
    next
      case (Suc nn_pred)
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
        $Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int_of_nat (ndest))),
                         $EConstNum (ConstInt32 (int_of_nat (nat_of_uint8 (dat ! nsrc)))),
                         $Store T_i32 (Some Tp_i8) 0 0,
                         $EConstNum (ConstInt32 (int_of_nat (ndest + 1))),
                         $EConstNum (ConstInt32 (int_of_nat (nsrc + 1))),
                         $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Memory_init x]\<rparr>"
        using reduce.memory_init[OF m_defs dat_defs n_defs h_bounds _, of nn_pred "nat_of_uint8 (dat ! nsrc)"] Suc memory_init.hyps(2) memory_init.prems(11)
        by fastforce
      then have "\<lparr>s;f;($C* vs) @ [$Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int_of_nat (ndest))),
                         $EConstNum (ConstInt32 (int_of_nat (nat_of_uint8 (dat ! nsrc)))),
                         $Store T_i32 (Some Tp_i8) 0 0,
                         $EConstNum (ConstInt32 (int_of_nat (ndest + 1))),
                         $EConstNum (ConstInt32 (int_of_nat (nsrc + 1))),
                         $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Memory_init x]\<rparr>"
        using v_defs
        by (simp add: v_to_e_def)
      then show ?thesis
        by (metis to_e_list_1)
    qed
  qed
next
  case (memory_copy \<C>)
  obtain vdest vsrc vn where
    "s\<bullet>\<C> \<turnstile> $C* [vdest] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vsrc] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vn] : ([] _> [T_num T_i32])"
    "vs = [vdest, vsrc, vn]"
    using const_list_split_3[OF memory_copy(2)]
    by fastforce
  then obtain dest src n where v_defs:
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 dest)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 src)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 n)] : ([] _> [T_num T_i32])"
    "vdest = V_num (ConstInt32 dest)"
    "vsrc = V_num (ConstInt32 src)"
    "vn = V_num (ConstInt32 n)"
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    using const_of_i32 list.inject
    by metis
  obtain ndest nsrc nn where n_defs:
    "ndest = nat_of_int dest"
    "nsrc = nat_of_int src"
    "nn = nat_of_int n"
    by fastforce
  obtain ma m where m_defs:
    "smem_ind (f_inst f) = Some ma"
    "(mems s)!ma = m"
    using smem_ind_def memory_copy.hyps(1) memory_copy.prems(6) Suc_le_length_iff
    by (metis One_nat_def list.simps(5))
  then show ?case
  proof(cases "mem_length m < nsrc + nn \<or> mem_length m < ndest + nn")
    case True
    then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
        $Memory_copy ]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
        using reduce.memory_copy_trap[OF m_defs n_defs True] by metis
    then have "\<lparr>s;f;($C* vs) @ [$Memory_copy]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
      using v_defs
      by (simp add: v_to_e_def)
    then show ?thesis
      by (metis to_e_list_1)
  next
    case False
    then have h_bounds: "nsrc + nn \<le> mem_length m " "ndest + nn \<le> mem_length m"
      using le_def by blast+
    then show ?thesis
    proof(cases nn)
      case 0
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n), $Memory_copy ]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
        using memory_copy_done[OF m_defs n_defs h_bounds 0] by metis
      then have "\<lparr>s;f;($C* vs) @ [$Memory_copy]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
        using v_defs
        by (simp add: v_to_e_def)
      then show ?thesis
        by (metis to_e_list_1)
    next
      case (Suc nn_pred)
      then show ?thesis
      proof(cases "ndest \<le> nsrc")
        case True
        let ?es = "[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src),
                                  $Load T_i32 (Some (Tp_i8, U)) 0 0,
                                  $Store T_i32 (Some Tp_i8) 0 0,
                                  $EConstNum (ConstInt32 (int_of_nat (ndest + 1))),
                                  $EConstNum (ConstInt32 (int_of_nat (nsrc + 1))),
                                  $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Memory_copy]"
        have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n), $Memory_copy ]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>"
          using memory_copy_1[OF m_defs n_defs h_bounds _ True] Suc Suc_eq_plus1 by blast
        then have "\<lparr>s;f;($C* vs) @ [$Memory_copy]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>"
          using v_defs
          by (simp add: v_to_e_def)
        then show ?thesis
          by (metis to_e_list_1)
      next
        case False
        let ?es = "[$EConstNum (ConstInt32 (int_of_nat (ndest + nn_pred))),
                                  $EConstNum (ConstInt32 (int_of_nat (nsrc + nn_pred))),
                                  $Load T_i32 (Some (Tp_i8, U)) 0 0,
                                  $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 dest),
                                  $EConstNum (ConstInt32 src),
                                  $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Memory_copy]"
        have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n), $Memory_copy ]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>"
          using memory_copy_2[OF m_defs n_defs h_bounds _] False Suc Suc_eq_plus1 le_def by blast
        then have "\<lparr>s;f;($C* vs) @ [$Memory_copy]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>"
          using v_defs
          by (simp add: v_to_e_def)
        then show ?thesis
          by (metis to_e_list_1)
      qed
    qed
  qed
next
  case (memory_fill \<C>)
  obtain vdest vval vn where
    "s\<bullet>\<C> \<turnstile> $C* [vdest] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vval] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vn] : ([] _> [T_num T_i32])"
    "vs = [vdest, vval, vn]"
    using const_list_split_3[OF memory_fill(2)]
    by fastforce
  then obtain dest val n where v_defs:
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 dest)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 val)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 n)] : ([] _> [T_num T_i32])"
    "vdest = V_num (ConstInt32 dest)"
    "vval = V_num (ConstInt32 val)"
    "vn = V_num (ConstInt32 n)"
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 val), V_num (ConstInt32 n)]"
    using const_of_i32 list.inject
    by metis
  obtain ndest  nn where n_defs:
    "ndest = nat_of_int dest"
    "nn = nat_of_int n"
    by fastforce
  obtain ma m where m_defs:
    "smem_ind (f_inst f) = Some ma"
    "(mems s)!ma = m"
    using smem_ind_def memory_fill.hyps(1) memory_fill.prems(6) Suc_le_length_iff
    by (metis One_nat_def list.simps(5))
  then show ?case
  proof(cases "mem_length m < ndest + nn")
    case True
    then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n),
        $Memory_fill ]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
        using reduce.memory_fill_trap[OF m_defs n_defs True] by metis
    then have "\<lparr>s;f;($C* vs) @ [$Memory_fill]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
      using v_defs
      by (simp add: v_to_e_def)
    then show ?thesis
      by (metis to_e_list_1)
  next
    case False
    then have h_bounds: "ndest + nn \<le> mem_length m" by auto
    then show ?thesis
    proof(cases nn)
      case 0
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n),
          $Memory_fill ]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
          using reduce.memory_fill_done[OF m_defs n_defs h_bounds 0] by metis
      then have "\<lparr>s;f;($C* vs) @ [$Memory_fill]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
        using v_defs
        by (simp add: v_to_e_def)
      then show ?thesis
        by (metis to_e_list_1)
    next
      case (Suc nn_pred)
      let ?es = "[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val),
                                  $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 (int_of_nat (ndest+1))),
                                  $EConstNum (ConstInt32 val),
                                  $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Memory_fill]"
      have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n),
          $Memory_fill]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>"
          using reduce.memory_fill[OF m_defs n_defs h_bounds] Suc Suc_eq_plus1 by blast
      then have "\<lparr>s;f;($C* vs) @ [$Memory_fill]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>"
        using v_defs
        by (simp add: v_to_e_def)
      then show ?thesis
        by (metis to_e_list_1)
    qed
  qed
next
  case (table_init x \<C> y tr)
  obtain vdest vsrc vn where
    "s\<bullet>\<C> \<turnstile> $C* [vdest] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vsrc] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vn] : ([] _> [T_num T_i32])"
    "vs = [vdest, vsrc, vn]"
    using const_list_split_3[OF table_init(5)]
    by fastforce
  then obtain dest src n where v_defs:
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 dest)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 src)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 n)] : ([] _> [T_num T_i32])"
    "vdest = V_num (ConstInt32 dest)"
    "vsrc = V_num (ConstInt32 src)"
    "vn = V_num (ConstInt32 n)"
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    using const_of_i32 list.inject
    by metis
  obtain ndest nsrc nn where n_defs:
    "ndest = nat_of_int dest"
    "nsrc = nat_of_int src"
    "nn = nat_of_int n"
    by fastforce
  obtain ta tab where tab_defs:
    "stab_ind (f_inst f) x = Some ta"
    "s.tabs s ! ta = tab"
    using stab_ind_def table_init.hyps(1) table_init.prems(7) by auto
  obtain ea el where el_defs:
    "ea = inst.elems (f_inst f) ! y"
    "el = s.elems s ! ea"
    using stab_ind_def table_init.hyps(1) table_init.prems(7) by auto
  show ?case
  proof(cases "length (snd el) < nsrc + nn \<or> length (snd tab) < ndest + nn")
    case True
    then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
        $Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
      using reduce.table_init_trap[OF tab_defs  el_defs n_defs True] table_init.hyps(2) table_init.prems(10)
      by metis
    then have "\<lparr>s;f;($C* vs) @ [$Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
      using v_defs
      by (simp add: v_to_e_def)
    then show ?thesis
      by (metis to_e_list_1)
  next
    case False
    then have h_bounds:"nsrc + nn \<le> length (snd el)" "ndest + nn \<le> tab_size tab"
      by auto
    then show ?thesis
    proof(cases nn)
      case 0
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
        $Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
        using reduce.table_init_done[OF tab_defs  el_defs n_defs h_bounds 0] table_init.hyps(2) table_init.prems(10)
        by metis
      then have "\<lparr>s;f;($C* vs) @ [$Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
        using v_defs
        by (simp add: v_to_e_def)
      then show ?thesis
        by (metis to_e_list_1)
    next
      case (Suc n')
      obtain val where val_def: "val = snd el ! nsrc" by simp
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
          $Table_init x
            y]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $C V_ref val, $Table_set x,
                         $EConstNum (ConstInt32 (int_of_nat (ndest + 1))), $EConstNum (ConstInt32 (int_of_nat (nsrc + 1))),
                         $EConstNum (ConstInt32 (int_of_nat n')), $Table_init x y]\<rparr>"
        using reduce.table_init[OF tab_defs el_defs n_defs h_bounds _ val_def] Suc
        by (metis Suc_eq_plus1 table_init.hyps(1) table_init.prems(9))
      then have "\<lparr>s;f;($C* vs) @ [$Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $C V_ref val, $Table_set x,
                         $EConstNum (ConstInt32 (int_of_nat (ndest + 1))), $EConstNum (ConstInt32 (int_of_nat (nsrc + 1))),
                         $EConstNum (ConstInt32 (int_of_nat n')), $Table_init x y]\<rparr>"
        using v_defs
        by (simp add: v_to_e_def)
      then show ?thesis
          by (metis to_e_list_1)
    qed
  qed  
next
  case (table_copy x \<C> tr y)
  obtain vdest vsrc vn where
    "s\<bullet>\<C> \<turnstile> $C* [vdest] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vsrc] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vn] : ([] _> [T_num T_i32])"
    "vs = [vdest, vsrc, vn]"
    using const_list_split_3[OF table_copy(5)]
    by fastforce
  then obtain dest src n where v_defs:
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 dest)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 src)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 n)] : ([] _> [T_num T_i32])"
    "vdest = V_num (ConstInt32 dest)"
    "vsrc = V_num (ConstInt32 src)"
    "vn = V_num (ConstInt32 n)"
    "vs = [V_num (ConstInt32 dest), V_num (ConstInt32 src), V_num (ConstInt32 n)]"
    using const_of_i32 list.inject
    by metis
  obtain ndest nsrc nn where n_defs:
    "ndest = nat_of_int dest"
    "nsrc = nat_of_int src"
    "nn = nat_of_int n"
    by fastforce
  obtain tax tabx where tabx_defs:
    "stab_ind (f_inst f) x = Some tax"
    "s.tabs s ! tax = tabx"
    using stab_ind_def
    using table_copy.hyps(1) table_copy.prems(7) by fastforce
  obtain tay taby where taby_defs:
    "stab_ind (f_inst f) y = Some tay"
    "s.tabs s ! tay = taby"
    using stab_ind_def
    using table_copy.hyps(3) table_copy.prems(7) by fastforce
  then show ?case
  proof(cases "tab_size tabx < nsrc + nn \<or> tab_size taby < ndest + nn")
    case True
    then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
          $Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>" using table_copy_trap[OF tabx_defs taby_defs n_defs True] by simp
    then have "\<lparr>s;f;($C*vs)@[$Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
      using v_defs by (simp add: v_to_e_def)
    then show ?thesis
      by (metis to_e_list_1)
  next
    case False
    then have h_bounds: "nsrc + nn \<le> tab_size tabx" "ndest + nn \<le> tab_size taby"
      by auto
    then show ?thesis
    proof(cases nn)
      case 0
      then have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
          $Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>" using table_copy_done[OF tabx_defs taby_defs n_defs h_bounds] by simp
      then have "\<lparr>s;f;($C*vs)@[$Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
        using v_defs by (simp add: v_to_e_def)
      then show ?thesis
        by (metis to_e_list_1)
    next
      case (Suc nn_pred)
      then show ?thesis
      proof(cases "ndest \<le> nsrc")
        case True
        let ?es = "[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $Table_get y,
                       $Table_set x, $EConstNum (ConstInt32 (int_of_nat (ndest + 1))),
                       $EConstNum (ConstInt32 (int_of_nat (nsrc + 1))),
                       $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_copy x y]"
        have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
            $Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>" using table_copy_1[OF tabx_defs taby_defs n_defs h_bounds _ True] Suc by simp
        then have "\<lparr>s;f;($C*vs)@[$Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>"
          using v_defs by (simp add: v_to_e_def)
        then show ?thesis
          by (metis to_e_list_1)
      next
        case False
        let ?es = "[$EConstNum (ConstInt32 (int_of_nat (ndest + nn_pred))),
                         $EConstNum (ConstInt32 (int_of_nat (nsrc + nn_pred))), $Table_get y,
                         $Table_set x, $EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src),
                         $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_copy x y]"
        have "\<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),
            $Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>" using table_copy_2[OF tabx_defs taby_defs n_defs h_bounds _] False Suc by simp
        then have "\<lparr>s;f;($C*vs)@[$Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;?es\<rparr>"
          using v_defs by (simp add: v_to_e_def)
        then show ?thesis
          by (metis to_e_list_1)
      qed
    qed
  qed
next
  case (table_fill x \<C> tr)
  obtain vi vvr vn where
    "s\<bullet>\<C> \<turnstile> $C* [vi] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [vvr] : ([] _> [T_ref tr])"
    "s\<bullet>\<C> \<turnstile> $C* [vn] : ([] _> [T_num T_i32])"
    "vs = [vi, vvr, vn]"
    using const_list_split_3[OF table_fill(3)]
    by fastforce
  then obtain i vr n where v_defs:
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 i)] : ([] _> [T_num T_i32])"
    "s\<bullet>\<C> \<turnstile> $C* [V_ref vr] : ([] _> [T_ref tr])"
    "s\<bullet>\<C> \<turnstile> $C* [V_num (ConstInt32 n)] : ([] _> [T_num T_i32])"
    "vi = V_num (ConstInt32 i)"
    "vvr = V_ref vr"
    "vn = V_num (ConstInt32 n)"
    "vs = [V_num (ConstInt32 i), V_ref vr, V_num (ConstInt32 n)]"
    by (metis (no_types, lifting) const_list_split_3 const_of_i32 const_of_typed_const_1 list.inject t.distinct(7) t.simps(7) table_fill.prems(1) type_const_v_typing(2) v_typing.simps)
  obtain ni nn where n_defs:
    "ni = nat_of_int i"
    "nn = nat_of_int n"
    by fastforce
  obtain ta tab where tab_defs:
    "stab_ind (f_inst f) x = Some ta"
    "s.tabs s ! ta = tab"
    using stab_ind_def table_fill.hyps(1) table_fill.prems(7) by fastforce
  then show ?case
  proof(cases "tab_size tab < ni + nn")
    case True
    then show ?thesis
      using reduce.table_fill_trap[OF tab_defs n_defs True] v_to_e_def v_defs(7)
      by fastforce
  next
    case False
    then have h_bounds: "ni + nn \<le> tab_size tab"
      using le_def by blast
    then show ?thesis
    proof(cases nn)
      case 0
      then show ?thesis using reduce.table_fill_done[OF tab_defs n_defs h_bounds] v_to_e_def v_defs(7)
        by fastforce
    next
      case (Suc nat)
      then show ?thesis using reduce.table_fill[OF tab_defs n_defs h_bounds] v_to_e_def v_defs(7)
        by fastforce
    qed
  qed
next
  case (elem_drop x \<C>)
  then show ?case using reduce.elem_drop
    by (metis progress_L0_left to_e_list_1)
next
  case (data_drop x \<C>)
  then show ?case using reduce.data_drop
    by (metis progress_L0_left to_e_list_1)
qed

lemma progress_e:
  assumes "s\<bullet>rs \<tturnstile> f;cs_es : ts'"
          "\<And> k lholed. \<not>(Lfilled k lholed [$Return] cs_es)"
          "\<And> i k lholed. (Lfilled k lholed [$Br (i)] cs_es) \<Longrightarrow> i < k"
          "cs_es \<noteq> [Trap]"
          "\<not> const_list (cs_es)"
          "store_typing s"
  shows "\<exists>a s' f' es'. \<lparr>s;f;cs_es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
proof -
  fix \<C> cs es ts_c
  have prems1:
      "s\<bullet>\<C> \<turnstile> es : (ts_c _> ts') \<Longrightarrow>
       s\<bullet>\<C> \<turnstile> cs_es : ([] _> ts') \<Longrightarrow>
       cs_es = ($C*cs)@es \<Longrightarrow>
       s\<bullet>\<C> \<turnstile> ($C*cs) : ([] _> ts_c) \<Longrightarrow>
       (\<And> k lholed. \<not>(Lfilled k lholed [$Return] cs_es)) \<Longrightarrow>
       (\<And> i k lholed. (Lfilled k lholed [$Br (i)] cs_es) \<Longrightarrow> i < k) \<Longrightarrow>
       cs_es \<noteq> [Trap] \<Longrightarrow>
       \<not> const_list (cs_es) \<Longrightarrow>
       store_typing s \<Longrightarrow>
       length (local \<C>) = length (f_locs f) \<Longrightarrow>
       length (memory \<C>) = length (inst.mems (f_inst f))  \<Longrightarrow>
       length (table \<C>) = length (inst.tabs (f_inst f))  \<Longrightarrow>
       length (func_t \<C>) = length (inst.funcs (f_inst f)) \<Longrightarrow>
       length (elem \<C>) = length (inst.elems (f_inst f)) \<Longrightarrow>
       length (data \<C>) = length (inst.datas (f_inst f)) \<Longrightarrow>
       types_t \<C> = inst.types (f_inst f) \<Longrightarrow>
         \<exists>a s' f' cs_es'. \<lparr>s;f;cs_es\<rparr> \<leadsto> \<lparr>s';f';cs_es'\<rparr>"
   and prems2:
      "s\<bullet>rs \<tturnstile> f;cs_es : ts' \<Longrightarrow>
       (\<And> k lholed. \<not>(Lfilled k lholed [$Return] cs_es)) \<Longrightarrow>
       (\<And> i k lholed. (Lfilled k lholed [$Br (i)] cs_es) \<Longrightarrow> i < k) \<Longrightarrow>
       cs_es \<noteq> [Trap] \<Longrightarrow>
       \<not> const_list (cs_es) \<Longrightarrow>
       store_typing s \<Longrightarrow>
         \<exists>a s' f' cs_es'. \<lparr>s;f;cs_es\<rparr> \<leadsto> \<lparr>s';f';cs_es'\<rparr>"
  proof (induction and s _ f cs_es ts' arbitrary: f ts_c ts' cs_es cs rule: e_typing_thread_typing.inducts)
    case (1 \<C> b_es tf s)
    hence "\<C> \<turnstile> b_es : (ts_c _> ts')"
      using e_type_comp_conc1[of s \<C> "($C*cs)" "($* b_es)" "[]" "ts'"] unlift_b_e
      by (metis typing_map_typeof)
    then show ?case
      using progress_b_e[OF _ 1(4) _ _ _ 1(10,11)] 1 list_all_append
            const_list_def consts_const_list
      by fastforce
  next
    case (2 s \<C> es t1s t2s e t3s)
    show ?case
    proof (cases "const_list es")
      case True
      obtain vcs where t_vcs_is:"es = $C* vcs"
        using True e_type_const_conv_vs
        by auto
      then obtain ts'' where t_ts''_is:"(s\<bullet>\<C> \<turnstile> ($C*(cs@vcs)) : ([] _> ts''))"
        using 2(5,6) True
        by (metis append_assoc e_type_comp_conc1 map_append)
      show ?thesis
        using 2(4)[OF 2(5) _ t_ts''_is] 2(5-19) t_vcs_is
        by auto
    next
      case False
      note outer_False = False
      have "\<exists>ts''. (s\<bullet>\<C> \<turnstile> (($C*cs) @ es) : ([] _> ts''))"
        using 2(5,6)
        by (metis append.assoc e_type_comp_conc1)
      moreover
      have "\<And>k lholed. \<not> Lfilled k lholed [$Return] (($C*cs) @ es)"
      proof -
        {
          assume "\<exists>k lholed. Lfilled k lholed [$Return] (($C*cs) @ es)"
          then obtain k lholed where local_assms:"Lfilled k lholed [$Return] (($C*cs) @ es)"
            by blast
          hence "\<exists>lholed'. Lfilled k lholed' [$Return] (($C*cs) @ es @ [e])"
          proof (cases rule: Lfilled.cases)
            case (L0 vs es')
            obtain lholed' where "lholed' = LBase vs (es'@[e])"
              by blast
            thus ?thesis
              using L0
              by (metis Lfilled.intros(1) append.assoc)
          next
            case (LN vs ts es' l es'' k lfilledk)
            obtain lholed' where "lholed' = LRec vs ts es' l (es''@[e])"
              by blast
            thus ?thesis
              using LN
              by (metis Lfilled.intros(2) append.assoc)
          qed
          hence False
            using 2(6,8)
            by blast
        }
        thus "\<And>k lholed. \<not> Lfilled k lholed [$Return] (($C*cs) @ es)"
          by blast
      qed
      moreover
      have "\<And>i k lholed.  Lfilled k lholed [$Br i] (($C*cs) @ es) \<Longrightarrow> i < k"
      proof -
        {
          assume "\<exists>i k lholed.  Lfilled k lholed [$Br i] (($C*cs) @ es) \<and> \<not>(i < k)"
          then obtain i k lholed where local_assms:"Lfilled k lholed [$Br i] (($C*cs) @ es)" "\<not>(i < k)"
            by blast
          hence "\<exists>lholed'.  Lfilled k lholed' [$Br i] (($C*cs) @ es @ [e]) \<and> \<not>(i < k)"
          proof (cases rule: Lfilled.cases)
            case (L0 vs es')
            obtain lholed' where "lholed' = LBase vs (es'@[e])"
              by blast
            thus ?thesis
              using L0 local_assms(2)
              by (metis Lfilled.intros(1) append.assoc)
          next
            case (LN vs ts es' l es'' k lfilledk)
            obtain lholed' where "lholed' = LRec vs ts es' l (es''@[e])"
              by blast
            thus ?thesis
              using LN local_assms(2)
              by (metis Lfilled.intros(2) append.assoc)
          qed
          hence False
            using 2(6,9)
            by blast
        }
        thus "\<And>i k lholed.  Lfilled k lholed [$Br i] (($C*cs) @ es) \<Longrightarrow> i < k"
          by blast
      qed
      moreover
      note preds = calculation
      show ?thesis
      proof (cases "($C*cs) @ es = [Trap]")
        case True
        thus ?thesis
          using reduce_simple.trap[of _ "(LBase [] [e])"]
                Lfilled.intros(1)[of "LBase [] [e]" "[]" "[e]" "($C*cs) @ es"]
                reduce.intros(1) 2(6,11)
          unfolding const_list_def
          by (metis (full_types) "2.prems"(6) append.left_neutral append_assoc list.simps(8))
      next
        case False
        show ?thesis
          using 2(3)[OF _ _ _ _ _ False _ 2(12, 13, 14, 15)] preds 2(5)
                progress_L0[of s f "(($C*cs) @ es)" _ _ _ "[]" "[e]"]
          apply simp
          apply (metis "2.prems"(2,3,12,13,14,15) consts_app_ex(2) consts_const_list e_type_const_conv_vs outer_False)
          done
      qed
    qed
  next
    case (3 s \<C> es t1s t2s ts)
    thus ?case
      by auto
  next
    case (4 \<S> \<C> v_r)
    then show ?case  using v_to_e_def
      by (metis "4.prems"(7) const_list_def consts_const_list is_const1 list.pred_inject(1,2) list_all_append v.case(3))
  next
    case (5 s \<C>)
    have cs_es_def:"Lfilled 0 (LBase cs []) [Trap] cs_es"
      using Lfilled.intros(1)[ of _ _ "[]" "[Trap]"] 5(2) 
      by fastforce
    thus ?case
      using reduce_simple.trap[OF 5(6) cs_es_def] reduce.intros(1)
      by blast
  next
    case (6 s ts fa es n \<C>)
    consider (1) "(\<And>k lholed. \<not> Lfilled k lholed [$Return] es)"
                 "(\<And>k lholed i. (Lfilled k lholed [$Br i] es) \<Longrightarrow> i < k)"
                 "es \<noteq> [Trap]"
                 "\<not> const_list es"
           | (2) "\<exists>k lholed. Lfilled k lholed [$Return] es"
           | (3) "const_list es \<or> (es = [Trap])"
           | (4) "\<exists>k lholed i. (Lfilled k lholed [$Br i] es) \<and> i \<ge> k"
      using not_le_imp_less
      by blast
    thus ?case
    proof (cases)
      case 1
      obtain s' f'' a where temp1:"\<lparr>s;fa;es\<rparr> \<leadsto> \<lparr>s';f'';a\<rparr>"
        using 6(3)[OF 1(1) _ 1(3,4) 6(11)] 1(2)
        by fastforce
      show ?thesis
        using reduce.intros(39)[OF temp1] progress_L0[where ?vs = cs] 6(5)
        by (meson local progress_L0_left temp1)
    next
      case 2
      then obtain k lholed where local_assms:"(Lfilled k lholed [$Return] es)"
        by blast
      then obtain lholed' vs' \<C>' where lholed'_def:"(Lfilled k lholed' (($C*vs')@[$Return]) es)"
                                                   "s\<bullet>\<C>' \<turnstile> ($C*vs') : ([] _> ts)"
        using progress_LN_return[OF local_assms, of s _ ts ts] s_type_unfold[OF 6(1)]
        by fastforce
      hence temp1:"\<exists>a. \<lparr>[Frame n fa es]\<rparr> \<leadsto> \<lparr>($C*vs')\<rparr>"
        using reduce_simple.return[OF _ lholed'_def(1)]
              e_type_consts[OF lholed'_def(2)] 6(2,3)
        by (metis length_map typing_map_typeof)
      show ?thesis
        using temp1 progress_L0[OF reduce.intros(1)] 6(5)
        by fastforce
    next
      case 3
      then consider (1) "const_list es" | (2) "es = [Trap]"
        by blast
      hence temp1:"\<exists>a. \<lparr>s;f;[Frame n fa es]\<rparr> \<leadsto> \<lparr>s;f;es\<rparr>"
      proof (cases)
        case 1
        have "length es = length ts"
          using s_type_unfold[OF 6(1)] e_type_const_list[OF 1] store_extension_refl
          by (metis "1" e_type_const_conv_vs typing_map_typeof)
        thus ?thesis
          using reduce_simple.local_const reduce.intros(1) 6(2)
          by (metis "1" e_type_const_conv_vs)
      next
        case 2
        thus ?thesis
          using reduce_simple.local_trap reduce.intros(1)
          by fastforce
      qed
      thus ?thesis
        using progress_L0[where ?vs = cs] 6(5)
        by fastforce
    next
      case 4
      then obtain k' lholed' i' where temp1:"Lfilled k' lholed' [$Br (k'+i')] es"
        using le_Suc_ex
        by blast
      obtain \<C>' \<C>j where c_def:"s\<bullet>\<C>' \<turnstile> es : ([] _> ts)"
                               "inst_typing s (f_inst fa) \<C>j"
                               "\<C>' = \<C>j\<lparr>local := (map typeof (f_locs fa)), return := Some ts\<rparr>"
        using 6(1) s_type_unfold
        by metis
      hence "length (label \<C>') = 0"
        using c_def store_local_label_empty 6(12)
        by fastforce
      thus ?thesis 
        using progress_LN1[OF temp1 c_def(1)]
        by linarith
    qed
  next
    case (7 i_cl s tf \<C>)
    obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> ($C*cs) : ([] _> ts'')" "s\<bullet>\<C> \<turnstile> [Invoke i_cl] : (ts'' _> ts')"
      using 7(3,4) e_type_comp_conc1
      by fastforce
    obtain ts_c t1s_dom t1s t2s where cl_def:"(t1s _> t2s) <ti: (ts'' _> ts')"
                                     "cl_type (funcs s!i_cl) = (t1s _> t2s)"
                                     "ts'' = ts_c@t1s_dom"
                                     "t_list_subtyping t1s_dom t1s"
      using e_type_invoke[OF ts''_def(2)] instr_subtyping_def
      by fastforce
    have ts''_typeof: "ts'' = map typeof cs"
      using ts''_def(1) typing_map_typeof by fastforce
    then have ts_c_eq: "t1s = t1s_dom" "ts'' = ts_c@t1s"
    proof -
      have "list_all (\<lambda> t. t \<noteq> T_bot) ts''" using ts''_typeof typeof_not_bot
        by (simp add: list_all_length)
      then have "list_all (\<lambda> t. t \<noteq> T_bot) t1s_dom"
        using cl_def(3) list_all_append by blast
      then show "t1s = t1s_dom"
        using cl_def(4) t_list_subtyping_not_bot_eq by blast
      then show "ts'' = ts_c@t1s" using cl_def(3) by simp
    qed
    obtain vs1 vs2 where vs_def:"s\<bullet>\<C> \<turnstile> $C*vs1 : ([] _> ts_c)"
                                "s\<bullet>\<C> \<turnstile> $C*vs2 : (ts_c _> ts_c @ t1s)"
                                "cs = vs1 @ vs2"
      using e_type_consts_cons ts''_def(1) cl_def(1) ts_c_eq(2) by blast
    have l:"(length vs2) = (length t1s)"
      using e_type_consts vs_def(2) store_extension_refl
      by (metis e_typing_imp_list_types_agree list_all2_lengthD)
    show ?case
    proof (cases "(funcs s!i_cl)")
      case (Func_native x11 x12 x13 x14)
      hence func_native_def:"(funcs s!i_cl) = Func_native x11 (t1s _> t2s) x13 x14"
        using cl_def(2) cl_type_def by fastforce
      have "n_zeros x13 \<noteq> None"
      proof -
        obtain tf where "(cl_typing s (funcs s!i_cl)) tf"
          using 7(10) unfolding store_typing.simps
          using "7.hyps"(1) "7.prems"(8) store_typing_imp_cl_typing by blast
        then show ?thesis unfolding cl_typing.simps
          using Func_native by fastforce
      qed
      then have "\<exists>a a'. \<lparr>s;f;($C*vs2) @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s;f;a\<rparr>"
        using reduce.intros(5)[OF func_native_def] e_type_const_conv_vs l
        unfolding n_zeros_def
        by blast
      thus ?thesis
        using progress_L0 vs_def(3) 7(4)
        by fastforce
    next
      case (Func_host x21 x22)
      hence func_host_def:"(funcs s!i_cl) = Func_host (t1s _> t2s) x22"
        using cl_def(2) cl_type_def by fastforce
      then show ?thesis
      proof(cases x22)
        case (Host_func x1)
        fix hs res
        have "\<exists>s' a a'. \<lparr>s;f;($C*vs2) @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s';f;a\<rparr>"
        proof (cases "host_func_apply s (t1s _> t2s) x1 vs2 hs (Some res)")
          case False
          thus ?thesis
            using reduce.intros(7)[OF func_host_def] l
            by blast
        next
          case True
          then obtain s' vcs' where ha_def:"host_func_apply s (t1s _> t2s) x1 vs2 hs (Some (s', vcs'))"
            by (metis surj_pair)
          have "list_all2 (\<lambda>t v. typeof v = t) t1s vs2"
            using e_typing_imp_list_types_agree vs_def(2)
            by simp
          thus ?thesis
            using reduce.intros(6)[OF _ _ _ _ _ ha_def] l func_host_def True Host_func
                  host_func_apply_respect_type[OF _ ha_def]
            by blast     
        qed
        thus ?thesis
          using vs_def(3) 7(4) progress_L0
          by fastforce
        
      next
        case (Host_ref x2)
        then have "\<exists>s' a a'. \<lparr>s;f;($C*vs2) @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s';f;a\<rparr>"
          using func_host_def invoke_host_None l by blast
        then show ?thesis using reduce.intros(7)[OF func_host_def]
          using "7.prems"(2) progress_L0_left vs_def(3) by fastforce
      qed
      
    qed
  next
    case (8 s \<C> e0s ts t2s es n)
    consider (1) "(\<And>k lholed. \<not> Lfilled k lholed [$Return] es)"
                 "(\<And>k lholed i. (Lfilled k lholed [$Br i] es) \<Longrightarrow> i < k)"
                 "es \<noteq> [Trap]"
                 "\<not> const_list es"
           | (2) "\<exists>k lholed. Lfilled k lholed [$Return] es"
           | (3) "const_list es \<or> (es = [Trap])"
           | (4) "\<exists>k lholed i. (Lfilled k lholed [$Br i] es) \<and> i = k"
           | (5) "\<exists>k lholed i. (Lfilled k lholed [$Br i] es) \<and> i > k"
      using linorder_neqE_nat
      by blast
    thus ?case
    proof (cases)
      case 1
      have temp1:"es = [] @ es" "const_list []"
        unfolding const_list_def
        by auto
      have temp2:"s\<bullet>\<C>\<lparr>label := [ts] @ label \<C>\<rparr> \<turnstile> [] : ([] _> [])"
        using b_e_typing.empty e_typing_thread_typing.intros(1)
        by fastforce
      hence "\<exists>s' f' a. \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';a\<rparr>"
        using 8(5)[OF 8(2) _ _ 1(1) _ 1(3,4), of "[]"]
              1(2,3,4) 8
        unfolding const_list_def
        by auto
      then obtain s' f' a where red_def:"\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';a\<rparr>"
        by blast
      have temp4:"\<And>es. Lfilled 0 (LBase [] []) es es"
        using Lfilled.intros(1)[of "(LBase [] [])" "[]"]
        unfolding const_list_def
        by fastforce
      hence temp5:"Lfilled 1 (LRec cs n e0s (LBase [] []) []) es (($C*cs)@[Label n e0s es])"
        using Lfilled.intros(2)[of "(LRec cs n e0s (LBase [] []) [])" _ n e0s "(LBase [] [])" "[]" 0 es es] 8(8)
        unfolding const_list_def
        by fastforce
      have temp6:"Lfilled 1 (LRec cs n e0s (LBase [] []) []) a (($C*cs)@[Label n e0s a])"
        using temp4 Lfilled.intros(2)[of "(LRec cs n e0s (LBase [] []) [])" _ n e0s "(LBase [] [])" "[]" 0 a a] 8(8)
        unfolding const_list_def
        by fastforce
      show ?thesis
        using label temp5 temp6 8(7) red_def
        by fastforce
    next
      case 2
      then obtain k lholed where "(Lfilled k lholed [$Return] es)"
        by blast
      hence "(Lfilled (k+1) (LRec cs n e0s lholed []) [$Return] (($C*cs)@[Label n e0s es]))"
        using Lfilled.intros(2) 8(8)
        by fastforce
      thus ?thesis
        using 8(10)[of "k+1"] 8(7,9)
      by fastforce
    next
      case 3
      hence temp1:"\<exists>a. \<lparr>s;f;[Label n e0s es]\<rparr> \<leadsto> \<lparr>s;f;es\<rparr>"
        using reduce_simple.label_const reduce_simple.label_trap reduce.intros(1)
        by (metis (full_types) e_type_const_conv_vs)
      show ?thesis
        using progress_L0 8(7) temp1
        by fastforce
    next
      case 4
      then obtain k lholed where lholed_def:"(Lfilled k lholed [$Br (k+0)] es)"
        by fastforce
      then obtain lholed' vs' \<C>' where lholed'_def:"(Lfilled k lholed' (($C*vs')@[$Br (k)]) es)"
                                                   "s\<bullet>\<C>' \<turnstile> $C*vs' : ([] _> ts)"
        using progress_LN[OF lholed_def 8(2), of ts]
        by fastforce
      have "\<exists>es' a. \<lparr>[Label n e0s es]\<rparr> \<leadsto> \<lparr>($C*vs')@e0s\<rparr>"
        using reduce_simple.br[OF _ lholed'_def(1)] 8(3)
              e_type_consts[OF lholed'_def(2)] store_extension_refl
             lholed'_def(2) typing_map_typeof by fastforce
      hence "\<exists>es' a. \<lparr>s;f;[Label n e0s es]\<rparr> \<leadsto> \<lparr>s;f;es'\<rparr>"
        using reduce.intros(1)
        by fastforce
      thus ?thesis
        using progress_L0 8(7,8)
        by fastforce
    next
      case 5
      then obtain i k lholed where lholed_def:"(Lfilled k lholed [$Br i] es)" "i > k"
        using less_imp_add_positive
        by blast
      have k1_def:"Lfilled (k+1) (LRec cs n e0s lholed []) [$Br i] cs_es"
        using 8(7) Lfilled.intros(2)
        by (simp add: lholed_def(1))
      thus ?thesis
        using 8(10)[OF k1_def] lholed_def(2)
        by simp
    qed
  next
    case (9 \<S> f \<C> rs es ts)
    have "length (local \<C>) = length (f_locs f)"
         "length (memory \<C>) = length (inst.mems (f_inst f))"
         "length (table \<C>) = length (inst.tabs (f_inst f))"
         "types_t \<C> = inst.types (f_inst f)"
         "length (elem \<C>) = length (inst.elems (f_inst f))"
         "length (data \<C>) = length (inst.datas (f_inst f))"
      using store_local_label_empty 9(1) store_data_exists store_elem_exists store_mem_exists store_tab_exists store_types_exists
      unfolding frame_typing.simps
      using list_all2_lengthD by fastforce+
    moreover have "length (func_t \<C>) = length (inst.funcs (f_inst f))"
      using "9.hyps"(1) frame_typing.simps inst_typing_func_length by force
    ultimately show ?case
      using 9(3)[OF 9(2) _ _ 9(4) _ 9(6,7,8), of "[]" "[]" f] 9(5)
            e_typing_thread_typing.intros(1)[OF b_e_typing.empty[of "\<C>\<lparr>return := rs\<rparr>"]]
      unfolding const_list_def
      by simp
  qed
  show ?thesis
    using prems2[OF assms]
    by fastforce
qed

lemma progress_e1:
  assumes "s\<bullet>None \<tturnstile> f;es : ts"
  shows "\<not>(Lfilled k lholed [$Return] es)"
proof -
  {
    assume "\<exists>k lholed. (Lfilled k lholed [$Return] es)"
    then obtain k lholed where local_assms:"(Lfilled k lholed [$Return] es)"
      by blast
    obtain \<C> \<C>i where c_def:"inst_typing s (f_inst f) \<C>i"
                   "\<C> = \<C>i\<lparr>local := (map typeof (f_locs f)), return := None\<rparr>"
                   "(s\<bullet>\<C> \<turnstile> es : ([] _> ts))"
      using assms s_type_unfold
      by metis
    have "\<exists>rs. return \<C> = Some rs"
      using local_assms c_def(3)
    proof (induction "[$Return]" es arbitrary: \<C> ts rule: Lfilled.induct)
      case (L0 vs lholed es')
      thus ?case
        using e_type_comp_conc2 unlift_b_e[of s \<C> "[Return]"] b_e_type_return
        by (metis to_e_list_1)
    next
      case (LN vs lholed tls es' l es'' k lfilledk)
      thus ?case
        using e_type_comp_conc2[OF LN(4)] e_type_label[of s \<C> tls es' lfilledk]
        by fastforce
    qed
    hence False
      using c_def(2)
      by fastforce
  }
  thus "\<And> k lholed. \<not>(Lfilled k lholed [$Return] es)"
    by blast
qed

lemma progress_e2:
  assumes "s\<bullet>None \<tturnstile> f;es : ts"
          "store_typing s"
  shows "(Lfilled k lholed [$Br (j)] es) \<Longrightarrow> j < k"
proof -
  {
    assume "(\<exists>i k lholed. (Lfilled k lholed [$Br (i)] es) \<and> i \<ge> k)"
    then obtain j k lholed where local_assms:"(Lfilled k lholed [$Br (k+j)] es)"
      by (metis le_iff_add)
    obtain \<C> \<C>i where c_def:"inst_typing s (f_inst f) \<C>i"
                   "\<C> = \<C>i\<lparr>local := (map typeof (f_locs f)), return := None\<rparr>"
                   "(s\<bullet>\<C> \<turnstile> es : ([] _> ts))"
      using assms s_type_unfold
      by metis
    have "j < length (label \<C>)"
      using progress_LN1[OF local_assms c_def(3)]
      by -
    hence False
      using store_local_label_empty(1)[OF c_def(1)] c_def(2)
      by fastforce
  }
  thus "(\<And> j k lholed. (Lfilled k lholed [$Br (j)] es) \<Longrightarrow> j < k)"
    by fastforce
qed

lemma progress_e3:
  assumes "s\<bullet>None \<tturnstile> f;cs_es : ts'"
          "cs_es \<noteq> [Trap]"
          "\<not> const_list (cs_es)"
          "store_typing s"
  shows "\<exists>a s' f' es'. \<lparr>s;f;cs_es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  using assms progress_e progress_e1 progress_e2
  by fastforce

lemma reduce_simple_not_value:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> $C* vs"
  using assms
proof (induction rule: reduce_simple.induct)
  case (trap lholed es)
  thus ?case
    using Lfilled.simps[of 0] consts_app_ex(2)
    by (metis basic consts_const_list reduce_simple.trap terminal_no_progress)
qed (metis basic consts_const_list reduce_simple.intros terminal_no_progress)+

lemma reduce_not_value:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "es \<noteq> $C* ves"
  using assms
proof (induction es' arbitrary: ves rule: reduce.induct)
  case (basic e e' s vs i)
  thus ?case
    using reduce_simple_not_value
    by fastforce
next
  case (invoke_native s i_cl j t1s t2s ts es ves vcs n k m zs f)
  have "\<not>(is_const (Invoke i_cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (invoke_host_Some s i_cl t1s t2s h ves vcs n m hs s' vcs' f)
  have "\<not>(is_const (Invoke i_cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (invoke_host_None s i_cl t1s t2s f ves vcs n m vs i)
  have "\<not>(is_const (Invoke i_cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (block vs n f tb t1s t2s m s es)
  thus ?case
    by (metis const_list_no_progress consts_const_list reduce.block)
next
  case (loop vs n f tb t1s t2s m s es)
  thus ?case
    by (metis const_list_no_progress consts_const_list reduce.loop)
next
  case (label s vs es i s' vs' es' k lholed les les')
  show ?case
    using label(2,4)
  proof (induction rule: Lfilled.induct)
    case (L0 lholed lvs les' les)
    {
      assume "($C*lvs) @ les @ les' = $C* ves"
      hence "(\<forall>y\<in>set (($C*lvs) @ les @ les'). \<exists>x. y = $C x)"
        by auto
      hence "(\<forall>y\<in>set les. \<exists>x. y = $C x)"
        by simp
      hence "\<exists>vs1. les = $C* vs1"
        unfolding ex_map_conv.
    }
    thus ?case
      using L0(2)
      by (metis consts_app_ex(1) consts_app_ex(2))
  next
    case (LN lvs lholed ln les' l les'' k les lfilledk)
    have "\<not>(is_const (Label ln les' lfilledk))"
      unfolding is_const_def
      by simp
    thus ?case
      using not_const_vs_to_es_list
      by fastforce
  qed
next
  case (call s f j)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.call)
next
  case (call_indirect_Some f i s c i_cl j tf)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.call_indirect_Some)
next
  case (call_indirect_None f i s c i_cl j)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.call_indirect_None)
next
  case (local_get vi j f v vs s)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.local_get)
next
  case (local_set vi j s v vs i v')
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.local_set)
next
  case (global_get s f j)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.global_get)
next
  case (global_set s f j v s')
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.global_set)
next
  case (load_Some f j s m k off t bs a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.load_Some)
next
  case (load_None f j s m k off t a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.load_None)
next
  case (load_packed_Some f j s m sx k off tp t bs a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.load_packed_Some)
next
  case (load_packed_None f j s m sx k off tp t a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.load_packed_None)
next
  case (store_Some v t f j s m k off mem' a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.store_Some)
next
  case (store_None v t f j s m k off a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.store_None)
next
  case (store_packed_Some v t f j s m k off tp mem' a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.store_packed_Some)
next
  case (store_packed_None v t f j s m k off tp a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.store_packed_None)
next
  case (load_vec_Some f j s m lv k off bs a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.load_vec_Some)
next
  case (load_vec_None f j s m lv k off a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.load_vec_None)
next
  case (load_lane_vec_Some f j s m k off svi bs v i a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.load_lane_vec_Some)
next
  case (load_lane_vec_None f j s m k off svi v i a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.load_lane_vec_None)
next
  case (store_vec_Some f j s m sv v bs k off mem' a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.store_vec_Some)
next
  case (store_vec_None f j s m sv v bs k off a)
  then show ?case
  using const_list_no_progress consts_const_list
  by (metis reduce.store_vec_None)
next
  case (table_set f ti a s n vr tabs')
  then show ?case
    by (metis const_list_no_progress consts_const_list reduce.table_set)
next
  case (table_set_fail f ti a s n vr)
  then show ?case
    by (metis const_list_no_progress consts_const_list reduce.table_set_fail)
next
  case (table_size f ti a s t n)
  then show ?case
    by (metis const_list_no_progress consts_const_list reduce.table_size)
next
  case (table_grow f ti a s tab sz n vr tab')
  then show ?case
    by (metis const_list_no_progress consts_const_list reduce.table_grow)
next
  case (table_grow_fail s f vr n ti)
  then show ?case
    by (metis const_list_no_progress consts_const_list reduce.table_grow_fail)
next
  case (memory_init_trap f ma s m x da dat src n dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_init_trap)
next
  case (memory_init_done f ma s m x da dat src dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_init_done)
next
  case (memory_init f ma s m x da dat src n dest b d)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_init)
next
  case (memory_copy_trap f ma s m src n dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_copy_trap)
next
  case (memory_copy_done f ma s m src dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_copy_done)
next
  case (memory_copy_1 f ma s m src n dest sz)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_copy_1)
next
  case (memory_copy_2 f ma s m src n dest sz)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_copy_2)
next
  case (memory_fill_trap f ma s m dest n val)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_fill_trap)
next
  case (memory_fill_done f ma s m dest val)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_fill_done)
next
  case (memory_fill f ma s m dest n val)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.memory_fill)
next
  case (table_init_trap f x ta s tab da y ea el src n dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_init_trap)
next
  case (table_init_done f x ta s tab da y ea el src dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_init_done)
next
  case (table_init f x ta s tab da y ea el src n dest val)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_init)
next
  case (table_fill_trap f x ta s tab i n vr)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_fill_trap)
next
  case (table_fill_done f x ta s tab i vr)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_fill_done)
next
  case (table_fill f x ta s tab i n vr val)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_fill)
next
  case (table_copy_trap f x tax s tabx y tay ty taby src n dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_copy_trap)
next
  case (table_copy_done f x tax s tabx y tay ty taby src dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_copy_done)
next
  case (table_copy_1 f x tax s tabx y tay ty taby src n dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_copy_1)
next
  case (table_copy_2 f x tax s tabx y tay ty taby src n dest)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.table_copy_2)
next
  case (elem_drop x f a s)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.elem_drop)
next
  case (data_drop x f a s)
  then show ?case
    using const_list_no_progress consts_const_list
    by (metis reduce.data_drop)
qed (metis const_list_no_progress consts_const_list  reduce.intros)+

lemma reduce_simple_not_nil:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> []"
  using assms
proof (induction rule: reduce_simple.induct)
  case (trap es lholed)
  thus ?case
    using Lfilled.simps[of 0 lholed "[Trap]"]
    by auto
qed auto

lemma reduce_not_nil:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "es \<noteq> []"
  using assms
proof (induction rule: reduce.induct)
  case (basic e e' s vs)
  thus ?case
    using reduce_simple_not_nil
    by simp
next
  case (label s vs es s' vs' es' k lholed les les')
  thus ?case
    by (metis empty_no_progress reduce.label)
qed auto

lemma reduce_simple_not_trap:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> [Trap]"
  using assms
  by (induction rule: reduce_simple.induct) auto

lemma reduce_not_trap:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "es \<noteq> [Trap]"
  using assms
proof (induction rule: reduce.induct)
  case (basic e e' s vs)
  thus ?case
    using reduce_simple_not_trap
    by simp
next
  case (label s vs es s' vs' es' k lholed les les')
  {
    assume "les = [Trap]"
    hence "Lfilled k lholed es [Trap]"
      using label(2)
      by simp
    hence False
      using lfilled_single reduce_not_nil[OF label(1)] label(4)
      by fastforce
  }
  thus ?case
    by auto
qed auto

lemma reduce_trans_app:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s'';f'';es''\<rparr>"
          "reduce_trans (s'',f'',es'') (s',f',es')"
  shows "reduce_trans (s,f,es) (s',f',es')"
proof -
  have 1:"(\<lambda>(s,f,es) (s',f',es'). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>) (s,f,es) (s'',f'',es'')"
    using assms
    by auto
  thus ?thesis
    using assms converse_rtranclp_into_rtranclp
    unfolding reduce_trans_def
    by (metis (no_types, lifting))
qed

lemma reduce_irrtrans_app:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s'';f'';es''\<rparr>"
          "reduce_irrtrans (s'',f'',es'') (s',f',es')"
  shows "reduce_irrtrans (s,f,es) (s',f',es')"
proof -
  have 1:"(\<lambda>(s,f,es) (s',f',es'). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>) (s,f,es) (s'',f'',es'')"
    using assms
    by auto
  thus ?thesis
    using assms
    unfolding reduce_irrtrans_def
    by (meson tranclp_into_tranclp2)
qed

lemma reduce_length_locals:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "length (f_locs f) = length (f_locs f')"
  using assms
  apply (induction rule: reduce.induct)
  apply auto
  done

lemma reduce_trans_length_locals:
  assumes "reduce_trans (s,f,es) (s',f', es')"
  shows "length (f_locs f) = length (f_locs f')"
  using assms
  unfolding reduce_trans_def
  apply (induction "(s',f', es')" arbitrary: s' f' es' rule: rtranclp_induct)
  apply (auto simp add: reduce_length_locals split: prod.splits)
  done

lemma reduce_trans_inst_is:
  assumes "reduce_trans (s,f,es) (s',f', es')"
  shows "(f_inst f) = (f_inst f')"
  using assms
  unfolding reduce_trans_def
  apply (induction "(s',f', es')" arbitrary: s' f' es' rule: rtranclp_induct)
  apply (auto simp add: reduce_inst_is split: prod.splits)
  done

lemma reduce_trans_app_end:
  assumes "\<lparr>s'';f'';es''\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "reduce_trans (s,f,es) (s'',f'',es'')"
  shows "reduce_trans (s,f,es) (s',f',es')"
proof -
  have 1:"(\<lambda>(s,f,es) (s',f',es'). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>) (s'',f'',es'') (s',f',es')"
    using assms
    by auto
  thus ?thesis
    using assms 
    unfolding reduce_trans_def
    by (simp add: rtranclp.rtrancl_into_rtrancl)
qed

lemma reduce_trans_L0:
  assumes "reduce_trans (s,f,es) (s',f',es')"
  shows "reduce_trans (s,f,($C*ves)@es@es_f) (s',f',($C*ves)@es'@es_f)"
  using assms
  unfolding reduce_trans_def
proof (induction "(s',f',es')" arbitrary: s' f' es' rule: rtranclp_induct)
  case base
  thus ?case
    by (auto split: prod.splits)
next
  case (step y)
  obtain s'' f'' es'' where y_is:"y = (s'', f'',es'')"
    by (cases y) blast
  hence "reduce_trans (s,f,($C*ves)@es@es_f) (s'',f'',($C*ves)@es''@es_f)"
    using step(3)
    unfolding reduce_trans_def
    by simp
  moreover
  have "\<lparr>s'';f'';es''\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    using step(2) y_is
    by blast
  hence "\<lparr>s'';f'';($C*ves)@es''@es_f\<rparr> \<leadsto> \<lparr>s';f';($C*ves)@es'@es_f\<rparr>"
    using progress_L0 is_const_list
    by fastforce
  ultimately
  show ?case
    using y_is reduce_trans_app_end reduce_trans_def
    by auto
qed

lemma reduce_trans_lfilled:
  assumes "reduce_trans (s,f,es) (s',f',es')"
          "Lfilled n lfilled es lfes"
          "Lfilled n lfilled es' lfes'"
  shows "reduce_trans (s,f,lfes) (s',f',lfes')"
  using assms
  unfolding reduce_trans_def
proof (induction "(s',f',es')" arbitrary: s' f' es' lfes' rule: rtranclp_induct)
  case base
  thus ?case
    using lfilled_deterministic
    by blast
next
  case (step y)
  obtain s'' f'' es'' where y_is:"y = (s'', f'',es'')"
    by (cases y) blast
  then obtain lfes'' where lfes'':"Lfilled n lfilled es'' lfes''"
                                  "reduce_trans (s,f,lfes) (s'',f'',lfes'')"
    using step(3,4) progress_LN2
    unfolding reduce_trans_def
    by simp metis
  moreover
  have 1:"\<lparr>s'';f'';es''\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    using step(2) y_is
    by blast
  hence "\<lparr>s'';f'';lfes''\<rparr> \<leadsto> \<lparr>s';f';lfes'\<rparr>"
    using step(5) lfes''(1) reduce.label
    by blast
  ultimately
  show ?case
    using y_is reduce_trans_app_end reduce_trans_def
    by auto
qed

lemma reduce_trans_label:
  assumes "reduce_trans (s,f,es) (s',f',es')"
  shows "reduce_trans (s,f,[Label n les es]) (s',f',[Label n les es'])"
  using assms
  unfolding reduce_trans_def
proof (induction "(s',f',es')" arbitrary: s' f' es' rule: rtranclp_induct)
  case base
  thus ?case
    by auto
next
  case (step y)
  obtain s'' f'' es'' where y_is:"y = (s'', f'',es'')"
    by (cases y) blast
  hence "reduce_trans (s,f,[Label n les es]) (s'',f'',[Label n les es''])"
    using step(3)
    unfolding reduce_trans_def
    by simp
  moreover
  have 1:"\<lparr>s'';f'';es''\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    using step(2) y_is
    by blast
  have "\<lparr>s'';f'';[Label n les es'']\<rparr> \<leadsto> \<lparr>s';f';[Label n les es']\<rparr>"
    using reduce.label[OF 1] Lfilled.intros(2)[of _ _ n les "LBase [] []" "[]" 0]
    by (simp add: "1" progress_label)
  ultimately
  show ?case
    using y_is reduce_trans_app_end reduce_trans_def
    by auto
qed

lemma reduce_trans_consts:
  assumes "reduce_trans (s, f, $C*ves) (s', f', $C*ves')"
  shows "s = s' \<and> f = f' \<and> ves = ves'"
  using assms
  unfolding reduce_trans_def
proof (induction "(s, f, $C*ves)" rule: converse_rtranclp_induct)
  case base
  thus ?case
    using inj_basic_econst
    by auto
next
  case (step y)
  thus ?case
    using const_list_no_progress is_const_list
    by auto
qed

lemma reduce_trans_local:
  assumes "reduce_trans (s,f,es) (s',f',es')"
  shows "reduce_trans (s,f0,[Frame n f es]) (s',f0,[Frame n f' es'])"
  using assms
  unfolding reduce_trans_def
proof (induction "(s',f',es')" arbitrary: s' f' es' rule: rtranclp_induct)
  case base
  thus ?case
    by auto
next
  case (step y)
  obtain s'' f'' es'' where y_is:"y = (s'', f'',es'')"
    by (cases y) blast
  hence "reduce_trans (s,f0,[Frame n f es]) (s'',f0,[Frame n f'' es''])"
    using step(3)
    unfolding reduce_trans_def
    by simp
  moreover
  have 1:"\<lparr>s'';f'';es''\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    using step(2) y_is
    by blast
  have "\<lparr>s'';f0;[Frame n f'' es'']\<rparr> \<leadsto> \<lparr>s';f0;[Frame n f' es']\<rparr>"
    using reduce.local[OF 1]
    by blast
  ultimately
  show ?case
    using y_is reduce_trans_app_end reduce_trans_def
    by auto
qed

lemma reduce_trans_compose:
  assumes "reduce_trans (s,f,es) (s'',f'',es'')"
          "reduce_trans (s'',f'',es'') (s',f',es')"
  shows "reduce_trans (s,f,es) (s',f',es')"
  using assms
  unfolding reduce_trans_def
  by auto

lemma reduce_trans_to_trap_not_nil:
  assumes "reduce_trans (s,f,es) (s',f',[Trap])"
  shows "es \<noteq> []"
  using assms
  unfolding reduce_trans_def
proof (induction "(s, f, es)" arbitrary: s' f' rule: converse_rtranclp_induct)
  case base
  thus ?case
    by blast
next
  case (step z)
  thus ?case
    by (simp add: reduce_not_nil split: prod.splits)
qed

lemma reduce_trans_to_trap_L0:
  assumes "reduce_trans (s,f,es) (s',f',[Trap])"
  shows "reduce_trans (s,f,($C*ves)@es@esc) (s',f',[Trap])"
proof (cases "ves = [] \<and> esc = []")
  case True
  thus ?thesis
    using assms
    by simp
next
  case False
  have 1:"reduce_trans (s,f,($C*ves)@es@esc) (s',f',($C*ves)@[Trap]@esc)"
    using reduce_trans_L0[OF assms]
    by blast
  have 2:"($C*ves)@[Trap]@esc \<noteq> [Trap]"
    by (simp add: False append_eq_Cons_conv)
  show ?thesis
    using reduce.basic[OF reduce_simple.trap[OF 2, of "LBase ves esc"], of s' f'] Lfilled.simps[of 0]
          reduce_trans_app_end[OF _ 1]
    by simp
qed

lemma reduce_trans_to_trap_label:
  assumes "reduce_trans (s,f,es) (s',f',[Trap])"
  shows "reduce_trans (s,f,[Label n esc es]) (s',f',[Trap])"
proof -
  have "reduce_trans (s,f,[Label n esc es]) (s',f',[Label n esc [Trap]])"
    using assms reduce_trans_label
    by blast
  thus ?thesis
    using reduce.basic[OF reduce_simple.label_trap] reduce_trans_app_end
    by blast
qed

lemma reduce_trans_to_trap_local:
  assumes "reduce_trans (s,f,es) (s',f',[Trap])"
  shows "reduce_trans (s,ff,[Frame n f es]) (s',ff,[Trap])"
proof -
  have "reduce_trans (s,ff,[Frame n f es]) (s',ff,[Frame n f' [Trap]])"
    using reduce_trans_local[OF assms]
    by blast
  thus ?thesis
    using reduce.basic[OF reduce_simple.local_trap] reduce_trans_app_end
    by blast
qed

lemma reduce_trans_trap_LN:
  assumes "Lfilled n lfilled [Trap] esl"
  shows "reduce_trans (s,f,esl) (s,f,[Trap])"
  using assms
proof (induction "[Trap]" esl rule: Lfilled.induct)
  case (L0 lholed vs es')
  thus ?case
    using reduce_trans_to_trap_L0[of s f "[Trap]" s f vs es']
    unfolding reduce_trans_def
    by simp
next
  case (LN lholed vs n es' l es'' k lfilledk)
  thus ?case
    using reduce_trans_to_trap_L0 reduce_trans_to_trap_label
    by blast
qed

lemma reduce_trans_to_trap_LN:
  assumes "reduce_trans (s,f,es) (s',f',[Trap])"
          "Lfilled n lfilled es esl"
  shows "reduce_trans (s,f,esl) (s',f',[Trap])"
proof -
  obtain esl' where esl'_is:"Lfilled n lfilled [Trap] esl'"
    using assms(2) progress_LN2
    by blast
  have "reduce_trans (s,f,esl) (s',f',esl')"
    using reduce_trans_lfilled[OF assms] esl'_is
    by blast
  thus ?thesis
    using reduce_trans_trap_LN esl'_is reduce_trans_compose
    by blast
qed

end
