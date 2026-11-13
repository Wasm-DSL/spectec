section \<open>Auxiliary Type System Properties\<close>

theory Wasm_Properties_Aux imports Wasm_Axioms Wasm_Subtyping_Properties begin

lemma b_e_weakening:
  assumes "\<C> \<turnstile> es : (t1s _> t2s)"
  shows "\<C> \<turnstile> es : (ts @ t1s _> ts @ t2s)"
proof -
  have "instr_subtyping (t1s _> t2s) (ts @ t1s _> ts @ t2s)"
    unfolding instr_subtyping_def using t_list_subtyping_refl
    by (metis tf.sel(1) tf.sel(2))
  then show ?thesis
    using assms subsumption by blast
qed

lemma e_weakening:
  assumes "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s)"
  shows "\<S>\<bullet>\<C> \<turnstile> es : (ts @ t1s _> ts @ t2s)"
proof -
  have "instr_subtyping (t1s _> t2s) (ts @ t1s _> ts @ t2s)"
    unfolding instr_subtyping_def using t_list_subtyping_refl
    by (metis tf.sel(1) tf.sel(2))
  then show ?thesis
    using assms e_typing_thread_typing.intros(3) by blast
qed

lemma typeof_num_i32:
  assumes "typeof_num v = T_i32"
  shows "\<exists>c. v = ConstInt32 c"
  using assms
  unfolding typeof_num_def
  by (cases v) auto

lemma typeof_num_i64:
  assumes "typeof_num v = T_i64"
  shows "\<exists>c. v = ConstInt64 c"
  using assms
  unfolding typeof_num_def
  by (cases v) auto

lemma typeof_num_f32:
  assumes "typeof_num v = T_f32"
  shows "\<exists>c. v = ConstFloat32 c"
  using assms
  unfolding typeof_num_def
  by (cases v) auto

lemma typeof_num_f64:
  assumes "typeof_num v = T_f64"
  shows "\<exists>c. v = ConstFloat64 c"
  using assms
  unfolding typeof_num_def
  by (cases v) auto

lemma typeof_num_app_unop:
  assumes "typeof_num v = t"
  shows "typeof_num (app_unop op v) = t"
  using assms
  unfolding typeof_num_def app_unop_def app_unop_i_v_def app_unop_f_v_def app_extend_s_def wasm_deserialise_num_def
  by (simp split: unop.splits unop_i.splits unop_f.splits v.splits v_num.splits)

lemma typeof_num_app_testop:
  shows "typeof_num (app_testop op v) = T_i32"
  unfolding typeof_num_def app_testop_def
  by (auto split: v_num.splits)

lemma typeof_num_app_binop:
  assumes "typeof_num v1 = t"
          "typeof_num v2 = t"
          "(app_binop op v1 v2) = Some v"
  shows "typeof_num v = t"
  using assms
  unfolding typeof_num_def app_binop_def app_binop_i_v_def app_binop_f_v_def
  by (auto split: binop.splits binop_i.splits binop_f.splits v_num.splits)

lemma typeof_num_app_relop:
  shows "typeof_num (app_relop op v1 v2) = T_i32"
  unfolding typeof_num_def app_relop_def app_relop_i_v_def app_relop_f_v_def
  by (auto split: relop.splits relop_i.splits relop_f.splits v_num.splits)

lemma exists_v_typeof_num: "\<exists>v v. typeof_num v = t"
  unfolding typeof_num_def
  by (metis t_num.exhaust v_num.simps(17,18,19,20))

lemma local_set_access: 
  assumes "j < Suc (length vi + length vs)"
          "j \<noteq> length vi"
  shows "(vi @ [v] @ vs) ! j = (vi @ [v'] @ vs) ! j"
proof -
  consider (1) "j < length vi" | (2) "j \<ge> length (vi @ [v])" "j \<ge> length (vi @ [v'])"
    using assms(2)
    by fastforce
  thus ?thesis
    using assms(1)
    apply (cases)
    apply (simp add: nth_append)
    apply (simp add: nth_append)
    done
qed

lemma lfilled_collapse1:
  assumes "Lfilled n lholed (($C*vs)@es) LI"
          "length vs \<ge> l"
  shows "\<exists>lholed'. Lfilled n lholed' (($C*(drop (length vs - l) vs))@es) LI"
  using assms(1)
proof (induction "($C*vs)@es" LI rule: Lfilled.induct)
  case (L0 lholed vs' es')
  obtain vs1 vs2 where "vs = vs1@vs2" "length vs2 = l"
    using assms
    by (metis append_take_drop_id diff_diff_cancel length_drop)
  thus ?case
    using Lfilled.intros(1)[of _ "vs'@vs1" es' "($C* vs2)@es"]
    by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma lfilled_collapse2:
  assumes "Lfilled n lholed (es@es') LI"
  shows "\<exists>lholed'. Lfilled n lholed' es LI"
  using assms
proof (induction "es@es'" LI rule: Lfilled.induct)
  case (L0 vs lholed es')
  thus ?case
    using Lfilled.intros(1)
    by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma lfilled_collapse3:
  assumes "Lfilled k lholed [Label n les es] LI"
  shows "\<exists>lholed'. Lfilled (Suc k) lholed' es LI"
  using assms
proof (induction "[Label n les es]" LI rule: Lfilled.induct)
  case (L0 lholed vs es')
  have "Lfilled 0 (LBase [] []) es es"
    using Lfilled.intros(1)
    by (simp add: Lfilled_exact.L0 Lfilled_exact_imp_Lfilled)
  thus ?case
    using Lfilled.intros(2) L0
    by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma unlift_b_e: assumes "\<S>\<bullet>\<C> \<turnstile> $*b_es : tf" shows "\<C> \<turnstile> b_es : tf"
using assms proof (induction "\<S>" "\<C>" "($*b_es)" "tf" arbitrary: b_es)
  case (1 \<C> b_es tf \<S>)
  then show ?case
    using inj_basic map_injective
    by auto
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  obtain es' e' where "es' @ [e'] = b_es"
    using 2(5)
    by (simp add: snoc_eq_iff_butlast)
  then show ?case using 2
    using b_e_typing.composition
    by fastforce
next                            
  case (3 \<S> \<C> tf tf')
  then show ?case
    using b_e_typing.subsumption
    by blast
qed auto

lemma stab_some_length:
  assumes "stab s i ti c = Some (ConstRefFunc i_cl)"
          "inst_typing s i \<C>"
          "store_typing s"
        shows "i_cl < length (funcs s)"
proof -
  obtain k where k_is:
     "length (inst.tabs i) > ti"
     "k =(inst.tabs i)!ti "
     "c < tab_size (s.tabs s ! k)"
     "snd (s.tabs s ! k) ! c = (ConstRefFunc i_cl)"
    using stab_unfold[OF assms(1)]
    by blast
  have "k < length (tabs s)"
    using assms(2) k_is(1,2,3)
    unfolding inst_typing.simps
    by (metis inst.select_convs(3) list_all2_nthD tabi_agree_def)
  hence "tab_agree s ((tabs s)!k)"
    using assms(3)
    unfolding store_typing.simps list_all_length
    by blast
  hence "ref_typing s (snd (s.tabs s ! k)!c) (tab_reftype (s.tabs s ! k))"
    by (metis (mono_tags, lifting) tab_agree_def case_prod_unfold k_is(3) list_all_length tab_reftype_def tab_t.case tab_t.exhaust)
  thus ?thesis
    by (simp add: k_is(4) ref_typing.simps)
qed

lemma stab_typed_some_imp_cl_typed:
  assumes "stab s i ti c = Some (ConstRefFunc i_cl)"
          "inst_typing s i \<C>"
          "store_typing s"
  shows "i_cl < length (funcs s) \<and> (\<exists>tf. cl_typing s (funcs s!i_cl) tf)"
  using stab_some_length[OF assms] assms(3)
  unfolding store_typing.simps
  by (simp add: list_all_length)

lemma b_e_type_empty: "(\<C> \<turnstile> [] : (ts _> ts')) = (instr_subtyping ([] _> []) (ts _> ts'))"
proof (safe)
  assume "\<C> \<turnstile> [] : (ts _> ts')"
  thus "(instr_subtyping ([] _> []) (ts _> ts'))"
  proof(induction "[]::(b_e list)" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
    case (empty \<C>)
    then show ?case
      using instr_subtyping_refl by metis
  next
    case (composition \<C> es t1s t2s e t3s)
    then show ?case
      by auto
  next
    case (subsumption \<C> tf)
    thm tf.collapse
    then show ?case using instr_subtyping_trans by metis
  qed
next
  assume "(instr_subtyping ([] _> []) (ts _> ts'))"
  thus "\<C> \<turnstile> [] : (ts _> ts')"
    using b_e_typing.empty b_e_typing.subsumption
    by metis
qed

lemma b_e_type_empty1[dest]: assumes "\<C> \<turnstile> [] : (ts _> ts')" shows "instr_subtyping ([] _> []) (ts _> ts')"
  using assms
proof(induction "[]::(b_e list)" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  case (subsumption \<C> tf)
  then show ?case
    using b_e_type_empty b_e_typing.subsumption by blast
qed (auto simp add: instr_subtyping_refl)+

lemma e_type_empty: "(\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')) = (instr_subtyping ([] _> []) (ts _> ts'))"
proof (safe)
  assume "\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
  thus "(instr_subtyping ([] _> []) (ts _> ts'))"
    using unlift_b_e by force
next
  assume "instr_subtyping ([] _> []) (ts _> ts')"
  thus "\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
    by (metis e_typing_thread_typing.intros(1) empty list.simps(8) subsumption)
qed

lemma e_type_empty1[dest]: assumes "\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')" shows "instr_subtyping ([] _> []) (ts _> ts')"
  using assms e_type_empty by fastforce

lemma b_e_type_cnum:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = EConstNum v_n"
  shows "instr_subtyping ([] _> [T_num (typeof_num v_n)]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  case (const_num \<C> v)
  then show ?case
    by (simp add: instr_subtyping_refl)
next
  case (composition \<C> es t1s t2s e t3s)
  then have "instr_subtyping ([] _> [T_num (typeof_num v_n)]) (t2s _> t3s)"
    by (metis last_ConsL last_snoc)
  moreover have "instr_subtyping ([] _> []) (t1s _> t2s)"
    using composition.hyps(1) composition.hyps(5) by fastforce
  ultimately show ?case
    using instr_subtyping_comp by blast
next
  case (subsumption \<C> tf)
  then show ?case
    by (metis instr_subtyping_trans)
qed (auto)+

lemma e_type_cnum:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$e] : (ts _> ts')"
          "e = EConstNum v_n"
  shows "instr_subtyping ([] _> [T_num (typeof_num v_n)]) (ts _> ts')"
  using assms
proof(induction  "\<S>" "\<C>" "[$e]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case
    using b_e_type_cnum by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 e_type_empty1 instr_subtyping_comp last_snoc)
next
  case (3 \<S> \<C> tf)
  then show ?case
    by (metis instr_subtyping_trans)
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms(1) assms(2) b_e_type_cnum to_e_list_1 unlift_b_e)
qed

lemma b_e_type_cvec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = EConstVec v_v"
  shows "instr_subtyping ([] _> [T_vec (typeof_vec v_v)]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  case (subsumption \<C> tf)
  then show ?case 
    by (metis instr_subtyping_trans)
qed (auto simp add: instr_subtyping_refl instr_subtyping_empty_comp1)

lemma e_type_cvec:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$e] : (ts _> ts')"
          "e = EConstVec v_n"
  shows "instr_subtyping ([] _> [T_vec (typeof_vec v_v)]) (ts _> ts')"
  using assms
proof(induction  "\<S>" "\<C>" "[$e]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case
    using b_e_type_cvec
    by (metis (full_types) e_typing_thread_typing.intros(1) t_vec.exhaust to_e_list_1 unlift_b_e)
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 e_type_empty1 instr_subtyping_comp last_snoc)
next
  case (3 \<S> \<C> tf)
  then show ?case
    by (metis instr_subtyping_trans)
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis (full_types) assms(1) assms(2) b_e_type_cvec t_vec.exhaust to_e_list_1 unlift_b_e)
qed

lemma e_type_cref:
  assumes "\<S>\<bullet>\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Ref v_r"
  shows "instr_subtyping ([] _> [T_ref (typeof_ref v_r)]) (ts _> ts')"
  using assms
proof (induction "\<S>" "\<C>" "[e]" "(ts _> ts')" arbitrary: ts ts')
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis butlast.simps(2) butlast_snoc e_type_empty1 instr_subtyping_comp last_ConsL last_snoc)
next
  case (3 \<S> \<C> tf)
  then show ?case
    by (metis instr_subtyping_trans)
next
  case (4 \<S> v_r t \<C>)
  then have h1: "ref_typing \<S> v_r t" by simp
  then have "t = typeof_ref v_r"
  proof(induction "\<S>" "v_r" "t" rule: ref_typing.induct)
  qed (fastforce simp add: typeof_ref_def)+
  then show ?case
    using "4.hyps"(2) "4.prems"
    by (simp add: instr_subtyping_refl)
qed (auto)

lemma type_const:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
  shows "instr_subtyping ([] _> [typeof v]) (ts _> ts')"
        "(\<forall> f. v = V_ref (ConstRefFunc f) \<longrightarrow> f < length (funcs \<S>))"
        "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts@[typeof v])"
proof -
  show "instr_subtyping ([] _> [typeof v]) (ts _> ts')"
    
    using assms e_type_cnum e_type_cvec e_type_cref typeof_def v_to_e_def by (auto split: v.splits)+

  have "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')" using assms by simp
  then show 2: "(\<forall>f. v = V_ref (ConstRefFunc f) \<longrightarrow> f < length (funcs \<S>))"
  proof (induction "\<S>" "\<C>" "[$C v]" "(ts _> ts')" arbitrary: ts ts')
  qed (auto simp add: ref_typing.simps v_to_e_def)

  show "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts@[typeof v])" 
  proof(cases v)
    case (V_num x1)
    then show ?thesis
      by (metis v_to_e_def append_Nil2 b_e_weakening const_num e_typing_thread_typing.intros(1) to_e_list_1 typeof_def v.simps(10))
  next
    case (V_vec x2)
    then show ?thesis using v_to_e_def
      by (metis append.right_neutral b_e_weakening const_vec e_typing_thread_typing.intros(1) to_e_list_1 typeof_def v.simps(11))
  next
    case (V_ref x3)
    then have "ref_typing \<S> x3 (typeof_ref x3)"
    proof(cases x3)
      case (ConstNull x1)
      then show ?thesis using v_to_e_def V_ref typeof_def
        by (simp add: ref_typing.intros(1) typeof_ref_def)
    next
      case (ConstRefFunc x2)
      then have "x2 < length (s.funcs \<S>)" using 2 V_ref by blast
      then show ?thesis using ref_typing.intros(2) V_ref typeof_ref_def
        by (simp add: ConstRefFunc)
    next
      case (ConstRefExtern x3)
      then show ?thesis using v_to_e_def V_ref typeof_def
        by (simp add: ref_typing.intros(3) typeof_ref_def)
    qed
    then show ?thesis
      using V_ref typeof_def[of v] v_to_e_def[of v] e_typing_thread_typing.intros(4)
      by (metis append.right_neutral e_weakening v.simps(12))
  qed
qed

lemma v_typing_typeof:
  assumes "v_typing s v t"
  shows "typeof v = t"
  using assms
  apply(simp add: typeof_def v_typing.simps split: v.splits t.splits)
  using ref_typing.simps typeof_ref_def by fastforce

lemma v_typing_typeof_list:
  assumes "list_all2 (\<lambda> v t. v_typing s v t) vs ts"
  shows "map typeof vs = ts"
  using assms
proof(induction vs arbitrary: ts)
  case Nil
  then show ?case
    by fastforce
next
  case (Cons a vs)
  then show ?case
    by (metis list.simps(9) list_all2_Cons1 v_typing_typeof)
qed


lemma type_const_v_typing:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
  shows
    "instr_subtyping ([]_>[typeof v]) (ts _> ts')"
    "v_typing \<S> v (typeof v)"
  using assms
proof -
  show "instr_subtyping ([]_>[typeof v]) (ts _> ts')" using type_const(1) assms by simp
next
  have h1: "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts@[typeof v])"
    using assms type_const by auto
  then show "v_typing \<S> v (typeof v)"
  proof(induction "\<S>" "\<C>" "[$C v]" "(ts _> ts@[typeof v])"  arbitrary: ts)
    case (1 \<C> b_es \<S>)
    then show ?case using v_to_e_def
      apply(auto split: v.splits)
      using b_e_type_cnum b_e_type_cvec  v_typing.simps typeof_def by fastforce+
  next
    case (2 \<S> \<C> es t1s t2s e)
    then show ?case
    proof(cases v)
      case (V_num x1)
      then show ?thesis
        by (metis v_typing.intros(1) v_typing_typeof)
    next
      case (V_vec x2)
      then show ?thesis
        by (metis v_typing.intros(2) v_typing_typeof)
    next
      case (V_ref x3)
      have "ref_typing \<S> x3 (typeof_ref x3)" using type_const(2)[OF h1] ref_typing.intros
        by (metis "2.hyps"(3) "2.hyps"(5) V_ref append1_eq_conv append_Nil type_const(2) typeof_ref_def v_ref.exhaust v_ref.simps(10) v_ref.simps(11) v_ref.simps(12))
      then show ?thesis using V_ref by (simp add: typeof_def v_typing.simps)
    qed  
      
  next
    case (3 \<S> \<C> tf)
    then show ?case
    proof(cases v)
      case (V_num x1)
      then show ?thesis using b_e_type_cnum b_e_type_cvec  v_typing.simps typeof_def
        by fastforce
    next
      case (V_vec x2)
      then show ?thesis using b_e_type_cnum b_e_type_cvec  v_typing.simps typeof_def
        by fastforce
    next
      case (V_ref x3)
      then show ?thesis
      proof(cases x3)
        case (ConstNull x1)
        then show ?thesis
          by (metis V_ref ref_typing.simps v_typing.intros(3) v_typing_typeof)
      next
        case (ConstRefFunc x2)
        then show ?thesis using type_const(2)
          by (metis "3.hyps"(1) V_ref ref_typing.simps v_typing.intros(3) v_typing_typeof)
      next
        case (ConstRefExtern x3)
        then show ?thesis
          by (metis V_ref ref_typing.intros(3) v_typing.intros(3) v_typing_typeof)
      qed
    qed
  qed (auto simp add: typeof_def v_to_e_def v_typing.simps  split: v.splits)+
qed

lemma b_e_type_composition_aux_lemma:
  assumes
    "\<C> \<turnstile> [] : t1s _> t2s"
    "tf <ti: (t2s _> t3s)"
  shows
    "tf <ti: (t1s _> t3s)"
  using assms
  using instr_subtyping_empty_comp2 instr_subtyping_refl instr_subtyping_trans by blast

lemma b_e_type_load:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Load t tp_sx a off"
  shows "instr_subtyping ([T_num T_i32] _> [T_num t]) (ts _> ts') \<and> length (memory \<C>) \<ge> 1"
        "load_store_t_bounds a (option_projl tp_sx) t"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_store:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Store t tp a off"
    shows "instr_subtyping ([T_num T_i32, T_num t] _> []) (ts _> ts')"
          "length (memory \<C>) \<ge> 1"
          "load_store_t_bounds a tp t"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_load_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Load_vec lv a off"
  shows "instr_subtyping ([T_num T_i32] _> [T_vec T_v128]) (ts _> ts') \<and> length (memory \<C>) \<ge> 1"
        "load_vec_t_bounds lv a"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_load_lane_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Load_lane_vec svi i a off"
  shows "instr_subtyping ([T_num T_i32, T_vec T_v128] _> [T_vec T_v128]) (ts _> ts') \<and> length (memory \<C>) \<ge> 1"
        "i < vec_i_num svi \<and> 2^a \<le> (vec_i_length svi)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_store_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Store_vec sv a off"
    shows "instr_subtyping ([T_num T_i32, T_vec T_v128] _> []) (ts _> ts')"
          "length (memory \<C>) \<ge> 1"
          "store_vec_t_bounds sv a"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_memory_size:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Memory_size"
  shows "instr_subtyping ([] _> [T_num T_i32]) (ts _> ts') \<and> length (memory \<C>) \<ge> 1"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_memory_grow:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Memory_grow"
  shows "instr_subtyping ([T_num T_i32] _> [T_num T_i32]) (ts _> ts')  \<and> length (memory \<C>) \<ge> 1"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_memory_init:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Memory_init x"
  shows "(([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> length (memory \<C>) \<ge> 1 \<and> x < length (data \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_memory_copy:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Memory_copy"
  shows "(([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> length (memory \<C>) \<ge> 1"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_memory_fill:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Memory_fill"
  shows "(([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> length (memory \<C>) \<ge> 1"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_table_get:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Table_get ti"
  shows "\<exists> tr. instr_subtyping ([T_num T_i32] _> [T_ref tr]) (ts _> ts') \<and> (tab_t_reftype ((table \<C>)!ti)) = tr" "ti < length(table \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_table_init:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Table_init x y"
  shows "instr_subtyping ([T_num T_i32, T_num T_i32, T_num T_i32] _> []) (ts _> ts')" "x < length (table \<C>)" "y < length (elem \<C>)" "tab_t_reftype (table \<C>!x) = (elem \<C>!y)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_table_fill:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Table_fill x"
  shows "\<exists> tr. instr_subtyping ([T_num T_i32, T_ref tr, T_num T_i32] _> []) (ts _> ts') \<and> x < length (table \<C>) \<and> tab_t_reftype (table \<C>!x) = tr"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_table_copy:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Table_copy x y"
  shows "instr_subtyping ([T_num T_i32, T_num T_i32, T_num T_i32] _> []) (ts _> ts')" "x < length (table \<C>)" "y < length (table \<C>)" "tab_t_reftype (table \<C>!x) = tab_t_reftype (table \<C>!y)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_elem_drop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Elem_drop x"
  shows "instr_subtyping ([] _> []) (ts _> ts')" "x < length (elem \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_data_drop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Data_drop x"
  shows "instr_subtyping ([] _> []) (ts _> ts')" "x < length (data \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_nop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Nop"
  shows "instr_subtyping ([] _> []) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

definition arity_2_result :: "b_e \<Rightarrow> t_num" where
  "arity_2_result op2 = (case op2 of
                           Binop t _ \<Rightarrow> t
                         | Relop t _ \<Rightarrow> T_i32)"

lemma b_e_type_binop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Binop t bop"
  shows "instr_subtyping ([T_num t,T_num t] _> [T_num (arity_2_result e)]) (ts _> ts')" 
        "binop_t_num_agree bop t"
  using assms  unfolding arity_2_result_def
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_relop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Relop t rop"
  shows "instr_subtyping ([T_num t,T_num t] _> [T_num (arity_2_result e)]) (ts _> ts')" 
        "relop_t_num_agree rop t"
  using assms b_e_type_composition_aux_lemma  unfolding arity_2_result_def
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl, metis instr_subtyping_trans)

lemma b_e_type_drop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Drop"
  shows "\<exists> t. instr_subtyping ([t] _> []) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  case (drop \<C> t)
  then show ?case
    using instr_subtyping_refl by blast
next
  case (composition \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 b_e_type_empty1 b_e_type_composition_aux_lemma last_snoc)
next
  case (subsumption \<C> tf1 tf2 tf1' tf2')
  then show ?case
    using instr_subtyping_trans by blast
qed (auto simp add: instr_subtyping_refl)

definition arity_1_result :: "b_e \<Rightarrow> t_num" where
  "arity_1_result op1 = (case op1 of
                           Unop t _ \<Rightarrow> t
                         | Testop t _ \<Rightarrow> T_i32
                         | Cvtop t1 _ _ _ \<Rightarrow> t1)"

lemma b_e_type_unop_testop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Unop t uop \<or> e = Testop t top'"
  shows "instr_subtyping ([T_num t] _> [T_num (arity_1_result e)]) (ts _> ts')"
        "e = Unop t uop \<Longrightarrow> unop_t_num_agree uop t"
        "e = Testop t top' \<Longrightarrow> is_int_t_num t"
  using assms
  unfolding arity_1_result_def
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_cvtop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Cvtop t1 cvtop t sx"
  shows "instr_subtyping ([T_num t] _> [T_num (arity_1_result e)]) (ts _> ts')"
        "cvtop = Convert \<Longrightarrow> (t1 \<noteq> t) \<and> (sx = None) = ((is_float_t_num t1 \<and> is_float_t_num t) \<or> (is_int_t_num t1 \<and> is_int_t_num t \<and> (t_num_length t1 < t_num_length t)))"
        "cvtop = Reinterpret \<Longrightarrow> (t1 \<noteq> t) \<and> t_num_length t1 = t_num_length t"
  using assms
  unfolding arity_1_result_def
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_ref_null:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Ref_null t"
  shows " instr_subtyping ([] _> [T_ref t]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_ref_is_null:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Ref_is_null"
  shows "\<exists> tr. instr_subtyping ([T_ref tr] _> [T_num T_i32]) (ts _> ts')"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_ref_func:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Ref_func i"
  shows "instr_subtyping ([] _> [T_ref T_func_ref]) (ts _> ts')"
        "i < length (func_t \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_unop_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Unop_vec op"
  shows "instr_subtyping ([T_vec T_v128] _> [T_vec T_v128]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_binop_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Binop_vec op"
  shows "instr_subtyping ([T_vec T_v128, T_vec T_v128] _> [T_vec T_v128]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_ternop_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Ternop_vec op"
  shows "instr_subtyping ([T_vec T_v128, T_vec T_v128, T_vec T_v128] _> [T_vec T_v128]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_test_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Test_vec op"
  shows "instr_subtyping ([T_vec T_v128] _> [T_num T_i32]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_shift_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Shift_vec op"
  shows  "instr_subtyping ([T_vec T_v128, T_num T_i32] _> [T_vec T_v128]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_splat_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Splat_vec sv"
  shows "instr_subtyping ([T_num (vec_lane_t sv)] _> [T_vec T_v128]) (ts _> ts')"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_extract_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Extract_vec sv sx i"
  shows "instr_subtyping ([T_vec T_v128] _> [T_num (vec_lane_t sv)]) (ts _> ts')"  "i < vec_num sv" "(sx = U \<or> vec_length sv \<le> 2)"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_replace_vec:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Replace_vec sv i"
  shows "instr_subtyping ([T_vec T_v128, T_num (vec_lane_t sv)] _> [T_vec T_v128]) (ts _> ts')"  "i < vec_num sv"
  using assms
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_select:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Select t_tag"
  shows "\<exists>t. instr_subtyping ([t,t,T_num T_i32] _> [t]) (ts _> ts') \<and> ((t_tag = None \<and> (is_num_type t \<or> is_vec_type t \<or> t = T_bot)) \<or> t_tag = Some t)"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_call:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Call i"
  shows  "i < length (func_t \<C>)"
         "\<exists> tf1 tf2. instr_subtyping (tf1 _> tf2) (ts _> ts') \<and> (func_t \<C>)!i = (tf1 _> tf2)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_call_indirect:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Call_indirect ti i"
  shows "i < length (types_t \<C>)"
        "ti < length (table \<C>)"
        "\<exists> tf1 tf2. instr_subtyping (tf1@[T_num T_i32] _> tf2) (ts _> ts') \<and> (types_t \<C>)!i = (tf1 _> tf2)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_local_get:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Local_get i"
  shows "\<exists>t.  instr_subtyping ([] _> [t]) (ts _> ts') \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_local_set:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Local_set i"
  shows "\<exists>t. instr_subtyping ([t] _> []) (ts _> ts') \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_local_tee:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Local_tee i"
  shows "\<exists>t. instr_subtyping ([t] _> [t]) (ts _> ts') \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_global_get:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Global_get i"
  shows "\<exists>t. instr_subtyping ([] _> [t]) (ts _> ts') \<and> tg_t((global \<C>)!i) = t" "i < length(global \<C>)"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_global_set:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Global_set i"
  shows "\<exists>t. instr_subtyping ([t] _> []) (ts _> ts') \<and> (global \<C>)!i = \<lparr>tg_mut = T_mut, tg_t = t\<rparr> \<and> i < length(global \<C>)"
  using assms is_mut_def
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl apply fastforce
  using instr_subtyping_trans by blast

lemma b_e_type_block:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Block tb es"
  shows "\<exists>tfn tfm. (tb_tf_t \<C> tb) = Some (tfn _> tfm) \<and> instr_subtyping (tfn _> tfm) (ts _> ts') \<and>
                        (\<C>\<lparr>label :=  [tfm] @ label \<C>\<rparr> \<turnstile> es : (tfn _> tfm))"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_loop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Loop tb es"
  shows "\<exists>tfn tfm. (tb_tf_t \<C> tb) = Some (tfn _> tfm) \<and> instr_subtyping (tfn _> tfm) (ts _> ts') \<and>
                        (\<C>\<lparr>label :=  [tfn] @ label \<C>\<rparr> \<turnstile> es : (tfn _> tfm))"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_if:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = If tb es1 es2"
  shows "\<exists>tfn tfm. (tb_tf_t \<C> tb) = Some (tfn _> tfm) \<and> instr_subtyping (tfn@[T_num T_i32] _> tfm) (ts _> ts') \<and>
                        (\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es1 : (tfn _> tfm)) \<and>
                        (\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es2 : (tfn _> tfm))"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_br:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br i"
        shows "i < length(label \<C>)"
              "\<exists>ts_c ts'' ts'''. instr_subtyping (ts_c@ts'' _> ts''') (ts _> ts')  \<and> (label \<C>)!i = ts''"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_br_if:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br_if i"
        shows "i < length(label \<C>)"
              "\<exists>ts''. instr_subtyping (ts''@[T_num T_i32] _> ts'') (ts _> ts') \<and> (label \<C>)!i = ts'' "
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_br_table:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br_table is i"
  shows "\<exists>ts'' t1s t2s. list_all (\<lambda>i. i < length(label \<C>) \<and> ts'' <ts: (label \<C>)!i) (is@[i]) \<and> instr_subtyping (t1s@ts''@[T_num T_i32] _> t2s) (ts _> ts')"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_return:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Return"
        shows "\<exists>ts_c ts'' ts'''. instr_subtyping (ts_c@ts'' _> ts''') (ts _> ts') \<and> (return \<C>) = Some ts''"
  using assms
  apply (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  apply (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma)
  using instr_subtyping_refl instr_subtyping_trans b_e_type_composition_aux_lemma by blast+

lemma b_e_type_comp:
  assumes "\<C> \<turnstile> es@[e] : (t1s _> t4s)"
  shows "\<exists>ts'. (\<C> \<turnstile> es : (t1s _> ts')) \<and> (\<C> \<turnstile> [e] : (ts' _> t4s))"
proof (cases es rule: List.rev_cases)
  case Nil
  then show ?thesis
    using assms b_e_typing.empty b_e_weakening
    by fastforce
next
  case (snoc es' e')
  show ?thesis using assms snoc
  proof(induction "es@[e]" "(t1s _> t4s)" arbitrary: t1s t4s)
    case (subsumption \<C> tf1 tf2 tf1' tf2')

    then show ?case using instr_subtyping_split
      by (meson b_e_typing.subsumption)
  qed auto
qed

lemma b_e_type_table_set:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Table_set ti"
  shows
    "\<exists>tr. (([T_num T_i32, T_ref tr] _> []) <ti: (ts _> ts')) \<and> tr = tab_t_reftype (table \<C>!ti)"
    "ti < length (table \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_table_grow:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Table_grow ti"
  shows
    "\<exists>tr. (([T_ref tr, T_num T_i32] _> [T_num T_i32]) <ti: (ts _> ts')) \<and> tr = tab_t_reftype (table \<C>!ti)"
    "ti < length (table \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_table_size:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Table_size ti"
  shows
    "([] _> [T_num T_i32]) <ti: (ts _> ts')"
    "ti < length (table \<C>)"
  using assms
proof (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
qed (auto simp add: instr_subtyping_refl b_e_type_composition_aux_lemma, metis instr_subtyping_trans)

lemma b_e_type_comp2_unlift:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$e1, $e2] : (t1s _> t2s)"
  shows "\<exists>ts'. (\<C> \<turnstile> [e1] : (t1s _> ts')) \<and> (\<C> \<turnstile> [e2] : (ts' _> t2s))"
  using assms
        unlift_b_e[of \<S> \<C> "([e1, e2])" "(t1s _> t2s)"]
        b_e_type_comp[of \<C> "[e1]" e2 t1s t2s]
  by simp

lemma b_e_type_comp2_relift:
  assumes "\<C> \<turnstile> [e1] : (t1s _> ts')" "\<C> \<turnstile> [e2] : (ts' _> t2s)"
  shows "\<S>\<bullet>\<C> \<turnstile> [$e1, $e2] : (ts@t1s _> ts@t2s)"
  using assms
        b_e_typing.composition[OF assms]
        e_typing_thread_typing.intros(1)[of \<C> "[e1, e2]" "(t1s _> t2s)"]
        e_typing_thread_typing.intros(3)[of \<S> \<C> "([$e1,$e2])" t1s t2s ts]
  by (metis Cons_eq_append_conv e_weakening to_e_list_2)

lemma b_e_type_value2_nn:
  assumes "\<C> \<turnstile> [EConstNum v1, EConstNum v2] : (t1s _> t2s)"
  shows "instr_subtyping ([] _> [T_num (typeof_num v1), T_num (typeof_num v2)]) (t1s _> t2s)"
proof -
  obtain ts' where ts'_def:"\<C> \<turnstile> [EConstNum v1] : (t1s _> ts')"
                           "\<C> \<turnstile> [EConstNum v2] : (ts' _> t2s)"
    using b_e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR list.distinct(1))
  have "instr_subtyping ([] _> [T_num (typeof_num v1)])  (t1s _> ts')"
    unfolding typeof_def
    using b_e_type_cnum b_e_type_cvec ts'_def(1)
    by (auto split: v.splits)
  moreover have "instr_subtyping ([] _> [T_num (typeof_num v2)])  (ts' _> t2s)"
    unfolding typeof_def
    using b_e_type_cnum b_e_type_cvec ts'_def(2)
    by (auto split: v.splits)
  thus ?thesis
    using calculation instr_subtyping_concat by fastforce
qed

lemma b_e_type_value2_vv:
  assumes "\<C> \<turnstile> [EConstVec v1, EConstVec v2] : (t1s _> t2s)"
  shows "instr_subtyping ([] _> [T_vec (typeof_vec v1), T_vec (typeof_vec v2)]) (t1s _> t2s)"
proof -
  obtain ts' where ts'_def:"\<C> \<turnstile> [EConstVec v1] : (t1s _> ts')"
                           "\<C> \<turnstile> [EConstVec v2] : (ts' _> t2s)"
    using b_e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR list.distinct(1))
  have "instr_subtyping ([] _> [T_vec (typeof_vec v1)])  (t1s _> ts')"
    unfolding typeof_def
    using b_e_type_cnum b_e_type_cvec ts'_def(1)
    by (auto split: v.splits)
  moreover have "instr_subtyping ([] _> [T_vec (typeof_vec v2)])  (ts' _> t2s)"
    unfolding typeof_def
    using b_e_type_cnum b_e_type_cvec ts'_def(2)
    by (auto split: v.splits)
  ultimately show ?thesis
    using instr_subtyping_concat
    by fastforce
qed

lemma b_e_type_value2_vn:
  assumes "\<C> \<turnstile> [EConstVec v1, EConstNum v2] : (t1s _> t2s)"
  shows "instr_subtyping ([] _> [T_vec (typeof_vec v1), T_num (typeof_num v2)]) (t1s _> t2s)"
proof -
  obtain ts' where ts'_def:"\<C> \<turnstile> [EConstVec v1] : (t1s _> ts')"
                           "\<C> \<turnstile> [EConstNum v2] : (ts' _> t2s)"
    using b_e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR list.distinct(1))
  have "instr_subtyping ([] _> [T_vec (typeof_vec v1)]) (t1s _> ts')"
    unfolding typeof_def
    using b_e_type_cnum b_e_type_cvec ts'_def(1)
    by (auto split: v.splits)
  thus ?thesis
    using b_e_type_cnum ts'_def(2)
    using instr_subtyping_concat by fastforce
qed

lemma b_e_type_value2_nv:
  assumes "\<C> \<turnstile> [EConstNum v1, EConstVec v2] : (t1s _> t2s)"
  shows "instr_subtyping ([] _> [T_num (typeof_num v1), T_vec (typeof_vec v2)]) (t1s _> t2s)"
proof -
  obtain ts' where ts'_def:"\<C> \<turnstile> [EConstNum v1] : (t1s _> ts')"
                           "\<C> \<turnstile> [EConstVec v2] : (ts' _> t2s)"
    using b_e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR list.distinct(1))
  have "instr_subtyping ([] _> [T_num (typeof_num v1)]) (t1s _> ts')"
    unfolding typeof_def
    using b_e_type_cnum b_e_type_cvec ts'_def(1)
    by (auto split: v.splits)
  thus ?thesis
    using b_e_type_cvec ts'_def(2) instr_subtyping_concat
    by fastforce
qed

lemma b_e_type_value3_nnn:
  assumes "\<C> \<turnstile> [EConstNum v1, EConstNum v2, EConstNum v3] : (t1s _> t2s)"
  shows "instr_subtyping ([] _> [T_num (typeof_num v1), T_num (typeof_num v2), T_num (typeof_num v3)]) (t1s _> t2s)"
proof -
  obtain ts' ts'' where ts'_def:"\<C> \<turnstile> [EConstNum v1] : (t1s _> ts')"
                                "\<C> \<turnstile> [EConstNum v2] : (ts' _> ts'')"
                                "\<C> \<turnstile> [EConstNum v3] : (ts'' _> t2s)"
    using b_e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR list.distinct(1))
  have "instr_subtyping ([] _> [T_num (typeof_num v1)]) (t1s _> ts')"
    using b_e_type_cnum ts'_def(1)
    by fastforce
  then have "instr_subtyping ([] _> [T_num (typeof_num v1), T_num (typeof_num v2)]) (t1s _> ts'')"
    using b_e_type_cnum ts'_def(2) instr_subtyping_concat
    by fastforce
  thus ?thesis
    using b_e_type_cnum ts'_def(2,3) instr_subtyping_concat
    by fastforce
qed


lemma b_e_type_value3_vvv:
  assumes "\<C> \<turnstile> [EConstVec v1, EConstVec v2, EConstVec v3] : (t1s _> t2s)"
  shows "instr_subtyping ([] _> [T_vec (typeof_vec v1), T_vec (typeof_vec v2), T_vec (typeof_vec v3)]) (t1s _> t2s)"
proof -
  obtain ts' ts'' where ts'_def:"\<C> \<turnstile> [EConstVec v1] : (t1s _> ts')"
                                "\<C> \<turnstile> [EConstVec v2] : (ts' _> ts'')"
                                "\<C> \<turnstile> [EConstVec v3] : (ts'' _> t2s)"
    using b_e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR list.distinct(1))
  have "instr_subtyping ([] _> [T_vec (typeof_vec v1)]) (t1s _> ts')"
    using b_e_type_cvec ts'_def(1)
    by fastforce
  then have "instr_subtyping ([] _> [T_vec (typeof_vec v1), T_vec (typeof_vec v2)]) (t1s _> ts'')"
    using b_e_type_cvec ts'_def(2) instr_subtyping_concat
    by fastforce
  thus ?thesis
    using b_e_type_cvec ts'_def(2,3) instr_subtyping_concat
    by fastforce
qed

lemma e_type_comp:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@[e] : (t1s _> t3s)"
  shows "\<exists>ts'. (\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts')) \<and> (\<S>\<bullet>\<C> \<turnstile> [e] : (ts' _> t3s))"
proof (cases es rule: List.rev_cases)
  case Nil
  thus ?thesis
    using assms e_typing_thread_typing.intros(1)
    by (metis b_e_type_empty1 b_e_weakening e_type_empty empty self_append_conv self_append_conv2)
next
  case (snoc es' e')
  show ?thesis using assms snoc
  proof (induction "es@[e]" "(t1s _> t3s)" arbitrary: t1s t3s)
    case (1 \<C> b_es \<S>)
    obtain es'' e'' where b_e_defs:"($* (es'' @ [e''])) = ($* b_es)"
      using 1(1,2)
      by (metis Nil_is_map_conv append_is_Nil_conv not_Cons_self2 rev_exhaust)
    hence "($*es'') = es" "($e'') = e"
      using 1(2) inj_basic map_injective
      by auto
    moreover
    have "\<C> \<turnstile> (es'' @ [e'']) : (t1s _> t3s)" using 1(1)
      using inj_basic map_injective b_e_defs
      by blast
    then obtain t2s where "\<C> \<turnstile> es'' : (t1s _> t2s)" "\<C> \<turnstile> [e''] : (t2s _> t3s)"
      using b_e_type_comp
      by blast
    ultimately
    show ?case
      using e_typing_thread_typing.intros(1)
      by fastforce
  next
    case (3 \<S> \<C> t1s t2s ts)
    thus ?case
      using e_typing_thread_typing.intros(3)  instr_subtyping_split
      by metis
  qed auto
qed

lemma e_type_comp_conc:
  assumes "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s)"
          "\<S>\<bullet>\<C> \<turnstile> es' : (t2s _> t3s)"
  shows "\<S>\<bullet>\<C> \<turnstile> es@es' : (t1s _> t3s)"
  using assms(2)
proof (induction es' arbitrary: t3s rule: List.rev_induct)
  case Nil
  hence "instr_subtyping ([] _> []) (t2s _> t3s)"
    using unlift_b_e[of _ _ "[]"] b_e_type_empty[of _ t2s t3s]
    by fastforce
  then show ?case
    using Nil assms(1) e_typing_thread_typing.intros(2)
    by (metis append_Nil2 e_typing_thread_typing.intros(3) instr_subtyping_comp instr_subtyping_empty_comp3 instr_subtyping_refl)
next
  case (snoc x xs)
  then obtain ts' where "\<S>\<bullet>\<C> \<turnstile> xs : (t2s _> ts')" "\<S>\<bullet>\<C> \<turnstile> [x] : (ts' _> t3s)"
    using e_type_comp[of _ _ xs x]
    by fastforce
  then show ?case
    using snoc(1)[of ts'] e_typing_thread_typing.intros(2)[of _ _ "es @ xs" t1s ts' x t3s]
    by simp
qed

lemma b_e_type_comp_conc:
  assumes "\<C> \<turnstile> es : (t1s _> t2s)"
          "\<C> \<turnstile> es' : (t2s _> t3s)"
  shows "\<C> \<turnstile> es@es' : (t1s _> t3s)"
proof -
  fix \<S>
  have 1:"\<S>\<bullet>\<C> \<turnstile> $*es : (t1s _> t2s)"
    using e_typing_thread_typing.intros(1)[OF assms(1)]
    by fastforce
  have 2:"\<S>\<bullet>\<C> \<turnstile> $*es' : (t2s _> t3s)"
    using e_typing_thread_typing.intros(1)[OF assms(2)]
    by fastforce
  show ?thesis
    using e_type_comp_conc[OF 1 2]
    by (simp add:  unlift_b_e)
qed

lemma e_type_comp_conc1:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@es' : (ts _> ts')"
  shows "\<exists>ts''. (\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts'')) \<and> (\<S>\<bullet>\<C> \<turnstile> es' : (ts'' _> ts'))"
  using assms
proof (induction es' arbitrary: ts ts' rule: List.rev_induct)
  case Nil
  thus ?case
    using b_e_type_empty[of _ ts' ts'] e_typing_thread_typing.intros(1)
    by (metis append_Nil2 b_e_weakening empty list.simps(8))
next
  case (snoc x xs)
  then show ?case
    using e_type_comp[of \<S> \<C> "es @ xs" x ts ts'] e_typing_thread_typing.intros(2)[of \<S> \<C> xs _ _ x ts']
    by fastforce
qed

lemma e_type_comp_conc2:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@es'@es'' : (t1s _> t2s)"
  shows "\<exists>ts' ts''. (\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts'))
                     \<and> (\<S>\<bullet>\<C> \<turnstile> es' : (ts' _> ts''))
                     \<and> (\<S>\<bullet>\<C> \<turnstile> es'' : (ts'' _> t2s))"
proof -
  obtain ts' where "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts')" "\<S>\<bullet>\<C> \<turnstile> es'@es'' : (ts' _> t2s)"
    using assms(1) e_type_comp_conc1
    by fastforce
  moreover
  then obtain ts'' where "\<S>\<bullet>\<C> \<turnstile> es' : (ts' _> ts'')" "\<S>\<bullet>\<C> \<turnstile> es'' : (ts'' _> t2s)"
    using e_type_comp_conc1
    by fastforce
  ultimately
  show ?thesis
    by fastforce
qed

lemma b_e_type_value_list_n:
  assumes "(\<C> \<turnstile> es@[EConstNum v] : (ts _> ts'@[t]))"
  shows "(\<C> \<turnstile> es : (ts _> ts'))"
        "(T_num (typeof_num v) = t)"
proof -
  obtain ts'' where ts''_def: "(\<C> \<turnstile> es : (ts _> ts''))" "(\<C> \<turnstile> [EConstNum v] : (ts'' _> ts' @ [t]))"
    using b_e_type_comp assms
    by blast
  then have  1: "instr_subtyping ([] _> [T_num (typeof_num v)]) (ts'' _> ts' @ [t])"
    using b_e_type_cnum[of \<C> "EConstNum v" "ts''" "ts' @ [t]"] by auto
  then have 2: "t_list_subtyping ts'' ts'" unfolding instr_subtyping_def
    by (metis append.right_neutral append1_eq_conv list_all2_Cons1 list_all2_Nil t_list_subtyping_def t_list_subtyping_replace2 tf.sel(1) tf.sel(2))
  then have 3: "instr_subtyping (ts _> ts'') (ts _> ts')"
    by (metis append.left_neutral instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
  show "T_num (typeof_num v) = t" using 1 t_list_subtyping_def unfolding instr_subtyping_def
    by (simp add: list_all2_Cons1 t_subtyping_def)
  show "(\<C> \<turnstile> es : (ts _> ts'))" using ts''_def(1) 3
    using subsumption by blast
qed

lemma b_e_type_value_list_v:
  assumes "(\<C> \<turnstile> es@[EConstVec v] : (ts _> ts'@[t]))"
  shows "(\<C> \<turnstile> es : (ts _> ts'))"
        "(T_vec (typeof_vec v) = t)"
proof -
  obtain ts'' where ts''_def: "(\<C> \<turnstile> es : (ts _> ts''))" "(\<C> \<turnstile> [EConstVec v] : (ts'' _> ts' @ [t]))"
    using b_e_type_comp assms
    by blast
  then have  1: "instr_subtyping ([] _> [T_vec (typeof_vec v)]) (ts'' _> ts' @ [t])"
    using b_e_type_cvec[of \<C> "EConstVec v" "ts''" "ts' @ [t]"] by auto
  then have 2: "t_list_subtyping ts'' ts'" unfolding instr_subtyping_def
    by (metis append.right_neutral append1_eq_conv list_all2_Cons1 list_all2_Nil t_list_subtyping_def t_list_subtyping_replace2 tf.sel(1) tf.sel(2))
  then have 3: "instr_subtyping (ts _> ts'') (ts _> ts')"
    by (metis append.left_neutral instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
  show "T_vec (typeof_vec v) = t" using 1 t_list_subtyping_def unfolding instr_subtyping_def
    by (simp add: list_all2_Cons1 t_subtyping_def)
  show "(\<C> \<turnstile> es : (ts _> ts'))" using ts''_def(1) 3
    using subsumption by blast
qed

lemma e_type_value_list:
  assumes "(s\<bullet>\<C> \<turnstile> es@[$C v] : (ts _> ts'@[t]))"
  shows "(s\<bullet>\<C> \<turnstile> es : (ts _> ts'))"
        "((typeof v) = t)"
proof -
  obtain ts'' where h: "(s\<bullet>\<C> \<turnstile> es : (ts _> ts''))" "(s\<bullet>\<C> \<turnstile> [$C v] : (ts'' _> ts' @ [t]))"
    using b_e_type_comp assms
    by (meson e_type_comp)
  then have  1: "instr_subtyping ([] _> [typeof v]) (ts'' _> ts' @ [t])"
    using type_const_v_typing(1) by auto
  then have 2: "t_list_subtyping ts'' ts'" unfolding instr_subtyping_def
    by (metis append.right_neutral append1_eq_conv list_all2_Cons1 list_all2_Nil t_list_subtyping_def t_list_subtyping_replace2 tf.sel(1) tf.sel(2))
  then have 3: "instr_subtyping (ts _> ts'') (ts _> ts')"
    by (metis append.left_neutral instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
  have  4: "instr_subtyping ([] _> [typeof v]) (ts' _> ts' @ [t])"
    using 1 2 unfolding instr_subtyping_def
    by (metis append.right_neutral append1_eq_conv list_all2_Cons1 list_all2_Nil t_list_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
  show "(s\<bullet>\<C> \<turnstile> es : (ts _> ts'))"
    using 1 2 3 h e_typing_thread_typing.intros(3)  by blast
  show "typeof v = t"
    using 4 t_list_subtyping_def t_subtyping_def typeof_def unfolding instr_subtyping_def
    apply auto
    by (metis append1_eq_conv h(2) list_all2_Cons1 list_all2_Nil t.distinct(11) t.distinct(5) t.distinct(9) type_const_v_typing(2) v_typing.simps)
qed

lemma e_type_label:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Label n es0 es] : (ts _> ts')"
  shows "\<exists>tls t2s. instr_subtyping ([] _> t2s) (ts _> ts')
                \<and> length tls = n
                \<and> (\<S>\<bullet>\<C> \<turnstile> es0 : (tls _> t2s))
                \<and> (\<S>\<bullet>\<C>\<lparr>label := [tls] @ (label \<C>)\<rparr> \<turnstile> es : ([] _> t2s))"
  using assms
proof (induction "\<S>" "\<C>" "[Label n es0 es]" "(ts _> ts')" arbitrary: ts ts' es0 es)
  case (1 \<C> b_es \<S>)
  then show ?case
    by (simp add: map_eq_Cons_conv)
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 e_type_empty instr_subtyping_comp last_snoc)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (8 \<S> \<C> t2s)
  then show ?case
    using instr_subtyping_refl by blast
qed blast

lemma e_type_invoke:
  assumes "s\<bullet>\<C> \<turnstile> [Invoke i_cl] : (t1s' _> t2s')"
  shows "\<exists>t1s t2s. instr_subtyping (t1s _> t2s) (t1s' _> t2s')
                         \<and> cl_type ((funcs s)!i_cl) = (t1s _> t2s)
                         \<and> i_cl < length (funcs s)"
  using assms
proof (induction "s" "\<C>" "[Invoke i_cl]" "(t1s' _> t2s')" arbitrary: t1s' t2s')
  case (1 \<C> b_es \<S>)
  thus ?case
    by auto
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  have "\<C> \<turnstile> [] : (t1s _> t2s)"
    using 2(1,5) unlift_b_e
    by (metis Nil_is_map_conv append_Nil butlast_snoc)
  thus ?case
    using 2
    by (metis append.left_neutral append1_eq_conv b_e_type_empty b_e_type_composition_aux_lemma)
next
  case (3 \<S> \<C> t1s t2s ts)
  thus ?case
    using instr_subtyping_trans by blast
next
  case (7 \<S> \<C>)
  thus ?case
    using instr_subtyping_refl by blast
qed blast

lemma e_type_memory_init:
  assumes "s\<bullet>\<C> \<turnstile> [$Memory_init x] : (ts _> ts')"
  shows "(([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> length (memory \<C>) \<ge> 1 \<and> x < length (data \<C>)"
  using assms
proof (induction s \<C> "[$Memory_init x]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case using b_e_type_memory_init
    by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis e_type_empty instr_subtyping_empty_comp2 last_snoc self_append_conv2)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms b_e_type_memory_init to_e_list_1 unlift_b_e)
qed

lemma e_type_memory_copy:
  assumes "s\<bullet>\<C> \<turnstile> [$Memory_copy] : (ts _> ts')"
  shows "(([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> length (memory \<C>) \<ge> 1"
  using assms
proof (induction s \<C> "[$Memory_copy]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case using b_e_type_memory_copy
    by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis e_type_empty instr_subtyping_empty_comp2 last_snoc self_append_conv2)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms b_e_type_memory_copy to_e_list_1 unlift_b_e)
qed

lemma e_type_memory_fill:
  assumes "s\<bullet>\<C> \<turnstile> [$Memory_fill] : (ts _> ts')"
  shows "(([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> length (memory \<C>) \<ge> 1"
  using assms
proof (induction s \<C> "[$Memory_fill]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case using b_e_type_memory_fill
    by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis e_type_empty instr_subtyping_empty_comp2 last_snoc self_append_conv2)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms b_e_type_memory_fill to_e_list_1 unlift_b_e)
qed

lemma e_type_table_init:
  assumes "s\<bullet>\<C> \<turnstile> [$Table_init x y] : (ts _> ts')"
  shows "(([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> x < length (table \<C>) \<and> y < length (elem \<C>) \<and> tab_t_reftype (table \<C>!x) = (elem \<C>!y)"
  using assms
proof (induction s \<C> "[$Table_init x y]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case using b_e_type_table_init
    by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis e_type_empty instr_subtyping_empty_comp2 last_snoc self_append_conv2)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms b_e_type_table_init to_e_list_1 unlift_b_e)
qed

lemma e_type_table_fill:
  assumes "s\<bullet>\<C> \<turnstile> [$Table_fill x] : (ts _> ts')"
  shows "\<exists> tr. (([T_num T_i32, T_ref tr, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> x < length (table \<C>) \<and> tab_t_reftype (table \<C>!x) = tr"
  using assms
proof (induction s \<C> "[$Table_fill x]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case using b_e_type_table_fill
    by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis e_type_empty instr_subtyping_empty_comp2 last_snoc self_append_conv2)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms b_e_type_table_fill to_e_list_1 unlift_b_e)
qed

lemma e_type_table_copy:
  assumes "s\<bullet>\<C> \<turnstile> [$Table_copy x y] : (ts _> ts')"
  shows "(([T_num T_i32, T_num T_i32, T_num T_i32] _> []) <ti: (ts _> ts')) \<and> x < length (table \<C>) \<and> y < length (table \<C>) \<and> tab_t_reftype (table \<C>!x) = tab_t_reftype (table \<C>!y)"
  using assms
proof (induction s \<C> "[$Table_copy x y]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case using b_e_type_table_copy
    by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 e_type_empty1 instr_subtyping_empty_comp2 last_snoc)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms b_e_type_table_copy to_e_list_1 unlift_b_e)
qed

lemma e_type_elem_drop:
  assumes "s\<bullet>\<C> \<turnstile> [$Elem_drop x] : (ts _> ts')"
  shows "(([] _> []) <ti: (ts _> ts')) \<and> x < length (elem \<C>)"
  using assms
proof (induction s \<C> "[$Elem_drop x]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case using b_e_type_elem_drop
    by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 e_type_empty1 instr_subtyping_empty_comp2 last_snoc)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms b_e_type_elem_drop to_e_list_1 unlift_b_e)
qed

lemma e_type_data_drop:
  assumes "s\<bullet>\<C> \<turnstile> [$Data_drop x] : (ts _> ts')"
  shows "(([] _> []) <ti: (ts _> ts')) \<and> x < length (data \<C>)"
  using assms
proof (induction s \<C> "[$Data_drop x]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case using b_e_type_data_drop
    by fastforce
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 e_type_empty1 instr_subtyping_empty_comp2 last_snoc)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using instr_subtyping_trans by blast
next
  case (9 \<S> f \<C> rs es ts)
  then show ?thesis
    by (metis assms b_e_type_data_drop to_e_list_1 unlift_b_e)
qed

lemma cl_typing_native:
  assumes "cl_typing s (Func_native i tf ts es) tf'"
  shows "\<exists>t1s t2s \<C>i. tf = tf' \<and> tf = (t1s _> t2s) \<and> inst_typing s i \<C>i
         \<and> (\<C>i\<lparr>local := t1s @ ts, label := ([t2s] @ (label \<C>i)), return := Some t2s\<rparr>  \<turnstile> es : ([] _> t2s))"
  using assms
  unfolding cl_typing.simps
  by blast

lemma cl_typing_host:
  assumes "cl_typing s (Func_host tf f) tf'"
  shows "tf = tf'"
  using assms
  unfolding cl_typing.simps
  by blast

lemma s_type_unfold:
  assumes "s\<bullet>rs \<tturnstile> f;es : ts"
  shows "\<exists>\<C>i. inst_typing s (f_inst f) \<C>i
              \<and> (s\<bullet>\<C>i\<lparr>local := (map typeof (f_locs f)), return := rs\<rparr> \<turnstile> es : ([] _> ts))
              \<and> list_all2 (\<lambda> v t. v_typing s v t) (f_locs f) (map typeof (f_locs f))"
proof -
  obtain \<C> where C_def: "frame_typing s f \<C>"
                            "s\<bullet>\<C>\<lparr>return := rs\<rparr> \<turnstile> es : ([] _> ts)"            
    using assms thread_typing.cases
    by metis
  then obtain \<C>' tvs where C'_def: 
      "list_all2 (\<lambda> v t. v_typing s v t) (f_locs f) tvs"
      "inst_typing s (f_inst f) \<C>'"
      "\<C>'\<lparr>local := tvs\<rparr> = \<C>"
    by (metis frame_typing.simps)

  have "tvs = map typeof (f_locs f)" using C'_def(1) v_typing_typeof_list
    by fastforce
  then show ?thesis
    using C'_def(1,2,3) C'_def(3) C_def(2) by blast
qed

lemma e_type_local:
  assumes "s\<bullet>\<C> \<turnstile> [Frame n f es] : (ts _> ts')"
  shows "\<exists>tls \<C>i. inst_typing s (f_inst f) \<C>i
                \<and> length tls = n
                \<and> (s\<bullet>\<C>i\<lparr>local := (map typeof (f_locs f)), return := Some tls\<rparr> \<turnstile> es : ([] _> tls))
                \<and> (([] _> tls) <ti: (ts _> ts'))
                \<and> list_all2 (v_typing s) (f_locs f) (map typeof (f_locs f))"
  using assms
  apply (induction "s" "\<C>" "[Frame n f es]" "(ts _> ts')" arbitrary: ts ts', auto)
  using instr_subtyping_empty_comp2 instr_subtyping_refl instr_subtyping_trans s_type_unfold by blast+

lemma e_type_local_shallow:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Frame n f es] : (ts _> ts')"
  shows "\<exists>tls. length tls = n \<and> (([] _> tls) <ti: (ts _> ts')) \<and> (\<S>\<bullet>(Some tls) \<tturnstile> f;es : tls)"
  using assms
  apply (induction "\<S>" "\<C>" "[Frame n f es]" "(ts _> ts')" arbitrary: ts ts', auto)
  using instr_subtyping_empty_comp2 instr_subtyping_refl instr_subtyping_trans s_type_unfold by blast+

lemma e_type_const_unwrap:
  assumes "is_const e"
  shows "\<exists>v. e = $C v"
  using assms
proof (cases e)
  case (Basic x1)
  then show ?thesis
    using assms
  proof (cases x1)
    case (EConstNum x26)
      then show ?thesis
        by (metis Basic v.simps(10) v_to_e_def)
    next
      case (EConstVec x27)
      then show ?thesis
        by (metis Basic v.simps(11) v_to_e_def)
    qed  (simp_all add: is_const_def)
  next
    case (Ref x6)
    then show ?thesis
      by (metis v.simps(12) v_to_e_def)
qed (simp_all add: is_const_def)

lemma is_const1:
  "is_const ($C x)"
  unfolding is_const_def
  using v_to_e_def
  by (simp split: v.splits)

lemma is_const_list1':
  assumes "ves = map (\<lambda> x. $C x) vs"
  shows "const_list ves"
  unfolding const_list_def using assms is_const1
  by (simp add: list.pred_True list.pred_map list_all_cong)

lemma is_const_list1_num:
  assumes "ves = map (Basic \<circ> EConstNum) vs"
  shows "const_list ves"
  using assms
proof (induction vs arbitrary: ves)
  case Nil
  then show ?case
    unfolding const_list_def
    by simp
next
  case (Cons a vs)
  then obtain ves' where "ves' = map (Basic \<circ> EConstNum) vs"
    by blast
  moreover
  have "is_const ((Basic \<circ> EConstNum) a)"
    unfolding is_const_def
    by simp
  ultimately
  show ?case
    using Cons
    unfolding const_list_def
    by auto
qed

lemma is_const_list1_vec:
  assumes "ves = map (Basic \<circ> EConstVec) vs"
  shows "const_list ves"
  using assms
proof (induction vs arbitrary: ves)
  case Nil
  then show ?case
    unfolding const_list_def
    by simp
next
  case (Cons a vs)
  then obtain ves' where "ves' = map (Basic \<circ> EConstVec) vs"
    by blast
  moreover
  have "is_const ((Basic \<circ> EConstVec) a)"
    unfolding is_const_def
    by simp
  ultimately
  show ?case
    using Cons
    unfolding const_list_def
    by auto
qed

lemma is_const_list:
  assumes "ves = $C* vs"
  shows "const_list ves"
  using assms is_const_list1' by blast

lemma consts_const_list:
  shows "const_list ($C* vs)"
  using is_const_list
  by auto

lemma const_list_cons_last:
  assumes "const_list (es@[e])"
  shows "const_list es"
        "is_const e"
  using assms list_all_append[of is_const es "[e]"]
  unfolding const_list_def
  by auto

lemma consts_cons_last:
  assumes "es@[e] = $C* ves"
  shows "const_list es"
        "is_const e"
  using assms is_const_list const_list_cons_last
  by blast+

lemma consts_cons_last2:
  assumes "es@[e,e'] = $C* ves"
  shows "const_list es"
        "is_const e"
        "is_const e'"
  apply (metis assms const_list_def is_const_list list_all_append)
  apply (metis assms const_list_def consts_const_list
      list.pred_inject(2) list_all_append)+
  done

lemma consts_cons_last3:
  assumes "es@[e,e',e''] = $C* ves"
  shows "const_list es"
        "is_const e"
        "is_const e'"
        "is_const e'"
  apply (metis assms const_list_def is_const_list list_all_append)
  apply (metis assms const_list_def consts_const_list
      list.pred_inject(2) list_all_append)+
  done

lemma consts_cons:
  assumes "e#es = $C* ves"
  shows "\<exists>ves. es = $C* ves"
        "is_const e"
  apply (metis assms map_eq_Cons_conv)
  apply (metis assms const_list_def consts_const_list
      list.pred_inject(2) list_all_append)+
  done

lemma consts_app_ex:
  assumes "es@es' = $C* ves"
  shows "\<exists>ves'. es = $C*ves'"
        "\<exists>ves''. es' = $C*ves''"
  using assms
proof (induction es arbitrary: ves)
  case Nil
  fix ves
  assume "[] @ es' = $C* ves"
  thus "\<exists>ves'. [] = $C*ves'"
       "\<exists>ves''. es' = $C*ves''"
    by auto
next
  case (Cons a es)
  fix ves
  assume "(\<And>ves. es @ es' = $C* ves \<Longrightarrow> \<exists>ves'. es = $C* ves')"
         "(\<And>ves. es @ es' = $C* ves \<Longrightarrow> \<exists>ves''. es' = $C* ves'')"
         "(a # es) @ es' = $C* ves"
  thus "\<exists>ves'. a # es = $C* ves'"
       "\<exists>ves''. es' = $C* ves''"
    using map_eq_Cons_D[of "(\<lambda>v. $C v)" ves a]
    by (metis append_Cons list.simps(9),(metis append_Cons))
qed

lemma consts_app_snoc:
  assumes "es @ es' = ($C* ves) @ [e]"
  shows "(es = ($C* ves) @ [e] \<and> es' = []) \<or>
           (\<exists>ves' ves''. es = ($C* ves') \<and> es' = ($C* ves'')@[e] \<and> ves = ves'@ves'')"
proof (cases es' rule: rev_cases)
  case Nil
  thus ?thesis
    using assms
    by simp
next
  case (snoc ys y)
  then obtain ves' ves'' where "es = ($C* ves') \<and> ys = ($C* ves'') \<and> y = e"
    using assms
    using consts_app_ex
    by (metis append.assoc butlast_snoc snoc_eq_iff_butlast)
  moreover
  hence "ves = ves'@ves''"
    using assms snoc map_injective[OF _ inj_basic_econst]
    by auto
  ultimately
  show ?thesis
    using snoc
    by auto
qed

lemma consts_app_snoc3:
  assumes "es @ es' @ es'' = ($C* ves) @ [e]"
  shows "(es = ($C* ves) @ [e] \<and> es' = [] \<and> es'' = []) \<or> 
         (\<exists>ves' ves''. es = ($C*ves') \<and> es' = ($C* ves'') @ [e] \<and> es'' = [] \<and> ves = ves'@ves'') \<or>
           (\<exists>ves' ves'' ves'''. es = ($C* ves') \<and> es' = ($C* ves'') \<and> es'' = ($C* ves''')@[e] \<and> ves = ves'@ves''@ves''')"
proof -
  consider (1) "es @ es' = ($C* ves) @ [e]" "es'' = []"
         | (2) "(\<exists>ves' ves''.
                  es @ es' = ($C* ves') \<and>
                  es'' = ($C* ves'') @ [e] \<and>
                  ves = ves' @ ves'')"
    using assms consts_app_snoc[of "es@es'" "es''" ves e]
    by fastforce
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using consts_app_snoc[OF 1(1)]
      by blast
  next
    case 2
    thus ?thesis
      using consts_app_ex[of es es']
      by (metis (no_types, lifting) append.assoc inj_basic_econst map_append map_injective)
  qed
qed

lemma consts_app_snoc_1:
  assumes "($C* ves) @ es = ($C* ves') @ [$C v, e]"
          "\<not>is_const e"
  shows "(es = [e] \<and> ves = ves' @ [v]) \<or>
         (\<exists>ves''. es = ($C*ves'')@[$C v, e] \<and> ves' = ves@ves'')"
proof -
  consider (1) "($C* ves) = ($C* ves' @ [v]) @ [e]" "es = []"
         | (2) "(\<exists>ves'a ves''. ($C* ves) = ($C* ves'a) \<and> es = ($C* ves'') @ [e] \<and> ves' @ [v] = ves'a @ ves'')"
    using consts_app_snoc[of "$C*ves" es "ves'@[v]" e] assms
    by fastforce
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis
      using consts_cons_last(2)[of "($C* ves' @ [v])" e] assms(2)
      by metis
  next
    case 2
    then obtain ves'a ves'' where
         "($C* ves) = ($C* ves'a)"
         "es = ($C* ves'') @ [e]"
         "ves' @ [v] = ves'a @ ves''"
      by blast
    thus ?thesis
      apply (cases ves'' rule : rev_cases)
       apply (auto simp add: inj_basic_econst)
      done
  qed
qed

lemma consts_app_snoc_2:
  assumes "($C* ves) @ es = ($C* ves') @ [$C v1, $C v2, e]"
          "\<not>is_const e"
  shows "(es = [e] \<and> ves = ves' @ [v1, v2]) \<or>
         (es = [$C v2, e] \<and> ves = ves'@[v1]) \<or>
         (\<exists>ves''. es = ($C*ves'')@[$C v1, $C v2, e] \<and> ves' = ves@ves'')"
proof -
  consider (1) "es = [e] \<and> ves = (ves' @ [v1]) @ [v2]"
         | (2) ves'' where "(es = ($C* ves'') @ [$C v2, e] \<and>  ves' @ [v1] = ves @ ves'')"
  using consts_app_snoc_1[of ves es "ves'@[v1]" v2 e] assms
  by fastforce
  thus ?thesis
  proof cases
    case 2
    thus ?thesis
      apply (cases ves'' rule: rev_cases)
       apply simp_all
      done
  qed simp_all
qed

lemma consts_app_snoc_3:
  assumes "($C* ves) @ es = ($C* ves') @ [$C v1, $C v2, $C v3, e]"
          "\<not>is_const e"
  shows "(es = [e] \<and> ves = ves' @ [v1, v2, v3]) \<or>
         (es = [$C v3, e] \<and> ves = ves' @ [v1, v2]) \<or>
         (es = [$C v2, $C v3, e] \<and> ves = ves'@[v1]) \<or>
         (\<exists>ves''. es = ($C*ves'')@[$C v1, $C v2, $C v3, e] \<and> ves' = ves@ves'')"
proof -
  consider (1) "es = [e] \<and> ves = (ves' @ [v1,v2,v3])"
         | (2) "es = [$C v3, e] \<and> ves = (ves' @ [v1,v2])"
         | (3) ves'' where "es = (($C* ves'') @ [$C v2, $C v3, e]) \<and> (ves' @ [v1]) = ves @ ves''"
  using consts_app_snoc_2[of ves es "ves'@[v1]"] assms
  by fastforce
  thus ?thesis
  proof cases
    case 3
    thus ?thesis
      apply (cases ves'' rule: rev_cases)
       apply simp_all
      done
  qed simp_all
qed

lemma consts_app_app_consts:
  assumes "es @ es' = ($C* ves') @ ($C* ves'') @ [e]"
          "\<not>is_const e"
  shows "(es  = ($C* ves') @ ($C* ves'') @ [e] \<or> es' = []) \<or>
         (\<exists>ves_p1 ves_p2. es' = ($C*ves_p2)@[e] \<and> ves'' = ves_p1@ves_p2 \<and> es = ($C*ves')@($C*ves_p1)) \<or>
         (\<exists>ves_p1 ves_p2. es' = ($C*ves_p2)@($C*ves'')@[e] \<and> ves' = ves_p1@ves_p2 \<and> es = ($C*ves_p1))"
proof -
  have 1:"es @ es' = ($C* (ves'@ves'')) @ [e]"
    using assms(1)
    by simp
  consider (a) "es = ($C* ves' @ ves'') @ [e] \<and> es' = []"
         | (b) ves'a ves''a where "es = $C* ves'a"
                                   "es' = ($C* ves''a) @ [e]"
                                   "ves' @ ves'' = ves'a @ ves''a"
    using consts_app_snoc[OF 1]
    by (metis assms(2) consts_cons_last(2))
  thus ?thesis
  proof cases
    case a
    thus ?thesis
      by simp
  next
    case b
    thus ?thesis
      unfolding append_eq_append_conv2
      by safe auto
  qed
qed

lemma consts_app_app_consts1:
  assumes "($C* ves) @ es = ($C* ves') @ ($C* ves'') @ [e]"
          "\<not>is_const e"
  shows "(\<exists>ves_p1 ves_p2. es = ($C*ves_p2)@[e] \<and> ves'' = ves_p1@ves_p2 \<and> ves = ves'@ves_p1) \<or>
         (\<exists>ves_p1 ves_p2. es = ($C*ves_p2)@($C*ves'')@[e] \<and> ves' = ves_p1@ves_p2 \<and> ves = ves_p1)"
  using consts_app_app_consts[OF assms]
  apply safe
  apply simp_all
  apply (metis append_assoc assms(2) consts_cons_last(2))
  apply (metis append_Nil2 append_assoc assms(1) assms(2) consts_cons_last(2))
  apply (metis inj_basic_econst map_append map_injective)
  apply (metis inj_basic_econst map_injective)
  done

lemma consts_app_snoc_0_const_list:
  assumes "es @ es' = ($C* ves') @ [e]"
          "\<not>is_const e"
          "\<not> const_list es"
  shows "es' = []"
  using consts_app_snoc[of es es' "ves'" e] assms is_const_list
  apply simp
  apply safe
   apply blast
  apply blast
  done

lemma consts_app_snoc_1_const_list:
  assumes "es @ es' = ($C* ves') @ [$C v, e]"
          "\<not>is_const e"
          "\<not> const_list es"
  shows "es' = []"
  using consts_app_snoc[of es es' "ves'@[v]" e] assms is_const_list
  apply simp
  apply safe
   apply blast
  apply blast
  done

lemma consts_app_snoc_2_const_list:
  assumes "es @ es' = ($C* ves') @ [$C v1, $C v2, e]"
          "\<not>is_const e"
          "\<not> const_list es"
  shows "es' = []"
  using consts_app_snoc[of es es' "ves'@[v1,v2]" e] assms is_const_list
  apply simp
  apply safe
   apply blast
  apply blast
  done

lemma consts_app_snoc_3_const_list:
  assumes "es @ es' = ($C* ves') @ [$C v1, $C v2, $C v3, e]"
          "\<not>is_const e"
          "\<not> const_list es"
  shows "es' = []"
  using consts_app_snoc[of es es' "ves'@[v1,v2,v3]" e] assms is_const_list
  apply simp
  apply safe
   apply blast
  apply blast
  done

lemma consts_app:
  assumes "es @ es' = ($C* ves) @ es''"
  shows "(\<exists>ves' ves''. es = ($C* ves') \<and> es' = ($C* ves'')@es'' \<and> ves = ves'@ves'') \<or>
           (\<exists>es_1 es_2. es = ($C* ves)@es_1 \<and> es' = es_2 \<and> es'' = es_1@es_2)"
proof -
  obtain us where us_def:"(es = ($C* ves) @ us \<and> us @ es' = es'') \<or> (es @ us = ($C* ves) \<and> es' = us @ es'')"
    using append_eq_append_conv2[of es es' "($C* ves)" es''] assms
    by blast
  show ?thesis
  proof -
    obtain vvs :: "e list \<Rightarrow> v list" where
      f2: "\<forall>es esa vs. es @ esa \<noteq> $C* vs \<or> es = $C* vvs es"
      by (metis consts_app_ex(1))
    obtain vvsa :: "e list \<Rightarrow> v list" where
      f3: "\<forall>x1. (\<exists>v3. x1 = $C* v3) = (x1 = $C* vvsa x1)"
      by moura
    moreover
    { assume "ves \<noteq> vvs es @ vvsa us"
      then have "$C* ves \<noteq> $C* vvs es @ vvsa us"
        using inj_basic_econst map_injective by blast
      then have "es @ us \<noteq> $C* ves \<or> es' \<noteq> us @ es''"
        using f3 f2 by (metis (no_types) consts_app_ex(2) map_append) }
    ultimately show ?thesis
      using f2 us_def by (metis (no_types) consts_app_ex(2))
  qed
qed

lemma not_const_vs_to_es_list:
  assumes "~(is_const e)"
  shows "vs1 @ [e] @ vs2 \<noteq> $C* vs"
proof -
  fix vs
  {
    assume a: "vs1 @ [e] @ vs2 = $C* vs"
    hence "(\<forall>y\<in>set (vs1 @ [e] @ vs2). \<exists>x. y = $C x)"
      by auto
    hence False
      using assms
      unfolding is_const_def
      by (metis a append_Cons assms consts_app_ex(2) consts_cons(2))
  }
  thus "vs1 @ [e] @ vs2 \<noteq> $C* vs"
    by fastforce
qed

lemma e_type_const:
  assumes "is_const e"
          "\<S>\<bullet>\<C> \<turnstile> [e] : (ts _> ts')"
          "store_extension \<S> \<S>'"
  shows  "\<exists>t. (([] _> [t]) <ti: (ts _> ts')) \<and> (\<S>'\<bullet>\<C>' \<turnstile> [e] : ([] _> [t]))"
  using assms
proof (cases e)
  case (Basic x1)
  then show ?thesis
    using assms
  proof (cases x1)
    case (EConstNum x26)
      then have "([] _> [T_num (typeof_num x26)]) <ti: (ts _> ts')"
        by (metis (no_types) Basic assms(2) b_e_type_cnum list.simps(8,9) unlift_b_e)
      moreover
      have "\<S>'\<bullet>\<C>' \<turnstile> [e] : ([] _> [T_num (typeof_num x26)])"
        using Basic EConstNum b_e_typing.intros(1) e_typing_thread_typing.intros(1)
        by fastforce
      ultimately
      show ?thesis
        by auto
  next
    case (EConstVec x27)
      then have "([] _> [T_vec (typeof_vec x27)]) <ti: (ts _> ts')"
        by (metis (no_types) Basic assms(2) b_e_type_cvec list.simps(8,9) unlift_b_e)
      moreover
      have "\<S>'\<bullet>\<C>' \<turnstile> [e] : ([] _> [T_vec (typeof_vec x27)])"
        using Basic EConstVec b_e_typing.intros(2) e_typing_thread_typing.intros(1)
        by fastforce
      ultimately
      show ?thesis
        by auto
    qed  (simp_all add: is_const_def)
next
  case (Ref x6)
  have 1: "\<S>\<bullet>\<C> \<turnstile> [e] : (ts _> ts')" by (simp add: assms)
  then have 2: "([] _> [T_ref (typeof_ref x6)]) <ti: (ts _> ts')" using e_type_cref
    by (simp add: Ref)
  moreover have 3: "ref_typing \<S> x6 ((typeof_ref x6))"
    using 1
  proof(induction "\<S>" "\<C>" "[e]" "(ts _> ts')" arbitrary: ts ts')
    case (4 \<S> v_r t \<C>)
    then show ?case
      using Ref e_type_cref e_typing_thread_typing.intros(4)
      by (metis e.inject(5) t.inject(3) typeof_def v.simps(12) v_typing.intros(3) v_typing_typeof)
  qed (fastforce simp add: Ref)+
  show ?thesis
  proof(cases x6)
    case (ConstNull x1)
    then show ?thesis
      using Ref calculation e_typing_thread_typing.intros(4) ref_typing.intros(1) typeof_ref_def by auto
  next
    case (ConstRefFunc x2)
    obtain f where hf: "x6 = (ConstRefFunc f)" "length (funcs \<S>) > f"
      using 1 type_const ConstRefFunc 3 ref_typing.simps by auto
    moreover have "length (funcs \<S>) \<le> length (funcs \<S>')" using assms(3)
      using store_extension.simps by auto
    moreover have "ref_typing \<S>' x6 ((typeof_ref x6))"
      using calculation(3) 3 ref_typing.simps by fastforce
    then show ?thesis
      using "2" Ref e_typing_thread_typing.intros(4) by blast
  next
    case (ConstRefExtern x3)
    then show ?thesis
      by (metis "3" Ref calculation e_typing_thread_typing.intros(4) ref_typing.simps v_ref.distinct(5))
  qed
qed (simp_all add: is_const_def)

lemma const_typeof_num:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$EConstNum v] : ([] _> [t])"
  shows "T_num (typeof_num v) = t"
  using assms
proof -
  have "\<C> \<turnstile> [EConstNum v] : ([] _> [t])"
    using unlift_b_e assms
    by fastforce
  thus ?thesis
    by (induction "[EConstNum v]" "([] _> [t])" rule: b_e_typing.induct, auto, (metis append_Nil b_e_type_value_list_n(2))+)
qed

lemma const_typeof_vec:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$EConstVec v] : ([] _> [t])"
  shows "T_vec (typeof_vec v) = t"
  using assms
proof -
  have "\<C> \<turnstile> [EConstVec v] : ([] _> [t])"
    using unlift_b_e assms
    by fastforce
  thus ?thesis
    by (induction "[EConstVec v]" "([] _> [t])" rule: b_e_typing.induct, auto, (metis append_Nil b_e_type_value_list_v(2))+)
qed

lemma const_typeof:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
  shows "(typeof v) = t"
  using assms
  by (metis e_type_value_list(2) self_append_conv2)

lemma e_type_const_list:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : (ts _> ts')"
          "store_extension \<S> \<S>'"
  shows   "\<exists>tvs. (([] _> tvs) <ti: (ts _> ts')) \<and>  length vs = length tvs \<and> (\<S>'\<bullet>\<C>' \<turnstile> vs : ([] _> tvs))"
  using assms
proof (induction vs arbitrary: ts ts' rule: List.rev_induct)
  case Nil
  have "\<S>'\<bullet>\<C>' \<turnstile> [] : ([] _> [])"
    using b_e_type_empty[of \<C>' "[]" "[]"] e_typing_thread_typing.intros(1) e_type_empty instr_subtyping_refl by fastforce
  thus ?case
    using Nil
    by (metis b_e_type_empty list.map(1) list.size(3) unlift_b_e)
next
  case (snoc x xs)
  hence v_lists:"list_all is_const xs" "is_const x"
  unfolding const_list_def
  by simp_all
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> xs : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [x] : (ts'' _> ts')"
    using snoc(3) e_type_comp
    by fastforce
  then obtain ts_b where ts_b_def:"(([] _> ts_b) <ti: (ts _> ts''))" "length xs = length ts_b" "\<S>'\<bullet>\<C>' \<turnstile> xs : ([] _> ts_b)"
    using snoc(1) v_lists(1)
    unfolding const_list_def
    using snoc.prems(3) by blast
  then obtain t where t_def:"(([] _> [t]) <ti: (ts'' _> ts')) " "\<S>'\<bullet>\<C>' \<turnstile> [x] : ([] _> [t])"
    using e_type_const v_lists(2) ts''_def
    using append_assoc snoc.prems(3) by blast
  moreover
  then have "length (ts_b@[t]) = length (xs@[x])"
    using ts_b_def(2)
    by simp
  moreover
  have "\<S>'\<bullet>\<C>' \<turnstile> (xs@[x]) : ([] _> ts_b@[t])"
    using ts_b_def(3) t_def e_typing_thread_typing.intros(2,3)
    by (metis append_Nil2 e_weakening)
  ultimately
  show ?case
    by (metis instr_subtyping_concat ts_b_def(1))
qed

lemma global_extension_refl:
  shows "global_extension g g"
  unfolding global_extension_def
  by auto

lemma limits_compat_refl:
  shows "limits_compat l l"
  unfolding limits_compat_def
  by (metis option.exhaust option.pred_inject(1) option.pred_inject(2) option.simps(5) order_class.order_eq_iff)

lemma mem_extension_refl:
  shows "mem_extension m m"
  unfolding mem_extension_def mem_subtyping_def
  using limits_compat_refl
  by auto

lemma tab_subtyping_refl:
  shows "tab_subtyping t t"
proof(cases t)
  case (T_tab x1 x2)
  then show ?thesis unfolding tab_subtyping_def using limits_compat_refl by simp
qed

lemma tab_extension_refl:
  shows "tab_extension t t"
  unfolding tab_extension_def
  using limits_compat_def limits_compat_refl tab_subtyping_def tab_subtyping_refl by auto

lemma elem_extension_refl:
  shows "elem_extension el el"
  unfolding elem_extension_def by simp

lemma data_extension_refl:
  shows "data_extension d d"
  unfolding data_extension_def by simp

lemma store_extension_refl:
  shows "store_extension s s"
  using global_extension_refl mem_extension_refl tab_extension_refl elem_extension_refl data_extension_refl
  store_extension.intros[of
    "funcs s" "funcs s"
    "tabs s" "tabs s"
    "mems s" "mems s"
    "globs s" "globs s"
    "elems s" "elems s"
    "datas s" "datas s"
    "[]" "[]" "[]" "[]" "[]" "[]"]
  apply (simp)
  by (metis list_all2_refl old.unit.exhaust s.surjective)

lemma instr_subtyping_append1:
  assumes "(([] _> [t]) <ti: (ts1 _> ts2@[t']))"
  shows "(([] _> []) <ti: (ts1 _> ts2))"
  using assms unfolding instr_subtyping_def
  by (metis append.right_neutral append1_eq_conv list_all2_Cons1 list_all2_Nil t_list_subtyping_def tf.sel(1) tf.sel(2))

lemma e_type_const_list_snoc:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : ([] _> ts@[t])"
  shows "\<exists>vs1 v2. (\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts))
                   \<and> (\<S>\<bullet>\<C> \<turnstile> [v2] : (ts _> ts@[t]))
                   \<and> (vs = vs1@[v2])
                   \<and> const_list vs1
                   \<and> is_const v2"
  using assms
proof -
  obtain tvs where tvs_def: "[] _> tvs <ti: [] _> ts @ [t] \<and> length vs = length tvs \<and> \<S>\<bullet>\<C> \<turnstile> vs : [] _> tvs"
    using e_type_const_list[OF assms(1,2) store_extension_refl] by blast
  then have "vs \<noteq> []"
    using instr_subtyping_def t_list_subtyping_def by auto
  then obtain vs' v where vs_def:"vs = vs'@[v]"
    by (meson rev_exhaust)
  hence consts_def:"const_list vs'" "is_const v"
    using assms(1)
    unfolding const_list_def
    by auto
  obtain ts' t' where ts'_def:"\<S>\<bullet>\<C> \<turnstile> vs' : ([] _> ts')" "\<S>\<bullet>\<C> \<turnstile> [v] : (ts' _> ts@[t])" "\<S>\<bullet>\<C> \<turnstile> [v] : ([] _> [t'])"
    using vs_def assms(2) e_type_comp[of \<S> \<C> vs' v "[]" "ts@[t]"]
    e_type_const consts_def(2) store_extension_refl by blast
  have 1: "\<S>\<bullet>\<C> \<turnstile> [v] : ([] _> [t])"
    using assms(2) const_typeof consts_def(2) e_type_const_unwrap e_type_value_list(2) ts'_def(3) vs_def by blast
  obtain c where c_def: "v = $C c"
    using e_type_const_unwrap consts_def(2)
    by fastforce
  thus ?thesis using ts'_def vs_def consts_def
    by (metis "1" c_def append.right_neutral assms(2) e_type_value_list(1) e_weakening)
qed
    
lemma e_type_const_list_cons:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : ([] _> (ts1@ts2))"
  shows "\<exists>vs1 vs2. (\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts1))
                   \<and> (\<S>\<bullet>\<C> \<turnstile> vs2 : (ts1 _> (ts1@ts2)))
                   \<and> vs = vs1@vs2
                   \<and> const_list vs1
                   \<and> const_list vs2"
  using assms
proof (induction "ts1@ts2" arbitrary: vs ts1 ts2 rule: List.rev_induct)
  case Nil
  thus ?case
    using e_type_const_list store_extension_refl
    using const_list_def e_type_empty instr_subtyping_refl by auto
next
  case (snoc t ts)
  note snoc_outer = snoc
  show ?case
  proof (cases ts2 rule: List.rev_cases)
    case Nil
    have "\<S>\<bullet>\<C> \<turnstile> [] : (ts1 _> ts1 @ [])"
      using b_e_typing.empty b_e_weakening e_typing_thread_typing.intros(1)
      by (metis append_self_conv b_e_type_empty e_type_empty)
    then show ?thesis
      using snoc(3,4) Nil
      unfolding const_list_def
      by auto
  next
    case (snoc ts2' a)
    obtain vs1 v2 where vs1_def:"(\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts1 @ ts2'))"
                                "(\<S>\<bullet>\<C> \<turnstile> [v2] : (ts1 @ ts2' _> ts1 @ ts2' @[t]))"
                                "(vs = vs1@[v2])"
                                "const_list vs1"
                                "is_const v2"
                                "ts = ts1 @ ts2'"
      using e_type_const_list_snoc[OF snoc_outer(3), of \<S> \<C> "ts1@ts2'" t]
            snoc_outer(2,4) snoc
      by fastforce
    show ?thesis
      using snoc_outer(1)[OF vs1_def(6,4,1)] snoc_outer(2) vs1_def(3,5)
            e_typing_thread_typing.intros(2)[OF _ vs1_def(2), of _ ts1]
            snoc
      unfolding const_list_def
      by fastforce
  qed
qed

lemma e_type_const_conv_vs:
  assumes "const_list ves"
  shows "\<exists>vs. ves = $C* vs"
  using assms
proof (induction ves)
  case Nil
  thus ?case
    by simp
next
  case (Cons a ves)
  thus ?case
  using e_type_const_unwrap
  unfolding const_list_def
  by (metis (no_types, lifting) list.pred_inject(2) list.simps(9)) 
qed

lemma e_type_consts:
  assumes "\<S>\<bullet>\<C> \<turnstile> ($C*vs) : (ts _> ts')"
          "store_extension \<S> \<S>'"
  shows   "(([] _> (map typeof vs)) <ti: (ts _> ts')) \<and> (\<S>'\<bullet>\<C>' \<turnstile> ($C*vs) : ([] _> (map typeof vs)))"
  using assms
proof (induction vs arbitrary: ts ts' rule: List.rev_induct)
  case Nil
  have "\<S>'\<bullet>\<C>' \<turnstile> [] : ([] _> [])"
    using b_e_type_empty[of \<C>' "[]" "[]"] e_typing_thread_typing.intros(1)
    by (simp add: e_type_empty instr_subtyping_refl)
  thus ?case
    using Nil
    apply simp
    by (metis b_e_type_empty list.map(1) unlift_b_e)
next
  case (snoc x xs)
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> ($C*xs) : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [$C x] : (ts'' _> ts')"
    using snoc(2) e_type_comp
    by fastforce
  hence ts_b_def:"(([] _> map typeof xs) <ti: (ts _> ts''))"
                 "\<S>'\<bullet>\<C>' \<turnstile> ($C*xs) : ([] _> (map typeof xs))"
    using snoc(1)
    using snoc.prems(2)
    by blast+
  then obtain t where t_def:"(([] _> map typeof xs@[t]) <ti: (ts _> ts'))" "\<S>'\<bullet>\<C>' \<turnstile> [$C x] : ([] _> [t])"
    using e_type_const[of "$C x"] ts''_def
    unfolding is_const_def
    using append_assoc is_const1 is_const_def snoc.prems(2)
    using instr_subtyping_concat by blast
  moreover
  have "\<S>'\<bullet>\<C>' \<turnstile> $C*(xs@[x]) : ([] _> (map typeof xs)@[t])"
    using ts_b_def(2) t_def e_type_comp_conc e_weakening by fastforce
  ultimately
  show ?case
    using const_typeof[OF t_def(2)]
    by simp
qed

lemma e_type_const_new:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
          "store_extension \<S> \<S>'"
  shows  "(([] _> [typeof v]) <ti: (ts _> ts')) \<and> (\<S>'\<bullet>\<C>' \<turnstile> [$C v] : ([] _> [typeof v]))"
  using assms e_type_consts[of \<S> \<C> "[v]" ts ts']
  by fastforce

lemma e_type_consts_typeof:
  assumes "\<S>\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> ts)"
          "store_extension \<S> \<S>'"
  shows   "map typeof vs = ts"
  using assms
proof (induction vs arbitrary: ts rule: List.rev_induct)
  case Nil
  then show ?case
    by (metis append_Nil e_type_consts list.ctr_transfer(1) list.pred_inject(1) t_list_subtyping_instr_subtyping_append t_list_subtyping_not_bot_eq t_list_subtyping_refl v_typing_typeof_list)
next
  case (snoc x xs)
  obtain ts' where ts'_def:"\<S>\<bullet>\<C> \<turnstile> ($C*xs) : ([] _> ts')" "\<S>\<bullet>\<C> \<turnstile> [$C x] : (ts' _> ts)"
    using snoc(2) e_type_comp
    by fastforce
  then have 1: "map typeof xs = ts'"
    using snoc.IH snoc.prems(2) by blast
  have 2: "([] _> [typeof x]) <ti: (ts' _> ts)"
    using ts'_def type_const_v_typing(1) by metis
  obtain ts'' where ts''_def: "ts=ts''@[typeof x]" "t_list_subtyping ts' ts''"
    by (metis "2" append_Nil t_list_subtyping_instr_subtyping_append t_list_subtyping_refl t_list_subtyping_snoc_left1 typeof_not_bot)
  have "ts' = ts''" using 1 ts''_def(2) unfolding t_list_subtyping_def
    using e_type_value_list(1) e_typing_thread_typing.intros(2) snoc.IH snoc.prems(2) ts''_def(1) ts'_def(1) ts'_def(2) by blast
  then have "ts = ts'@[typeof x]"
    using ts''_def(1) by auto
  then show ?case
    by (simp add: "1")
qed

lemma e_type_consts_cons:
  assumes "\<S>\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> (ts1@ts2))"
  shows "\<exists>vs1 vs2. (\<S>\<bullet>\<C> \<turnstile> $C* vs1 : ([] _> ts1))
                   \<and> (\<S>\<bullet>\<C> \<turnstile> $C* vs2 : (ts1 _> (ts1@ts2)))
                   \<and> vs = vs1@vs2"
  using e_type_const_list_cons[OF is_const_list assms]
  by (metis (no_types, lifting) append_eq_map_conv)

lemma types_exist_lfilled:
  assumes "Lfilled k lholed es lfilled"
          "\<S>\<bullet>\<C> \<turnstile> lfilled : (ts _> ts')"
  shows "\<exists>t1s t2s \<C>' arb_label. (\<S>\<bullet>\<C>\<lparr>label := arb_label@(label \<C>)\<rparr> \<turnstile> es : (t1s _> t2s))"
  using assms
proof (induction arbitrary: \<C> ts ts' rule: Lfilled.induct)
  case (L0 lholed vs es' es)
  hence "\<S>\<bullet>(\<C>\<lparr>label := label \<C>\<rparr>) \<turnstile> ($C*vs) @ es @ es' : (ts _> ts')"
    by simp
  thus ?case
    using e_type_comp_conc2
    by (metis append_Nil)
next
  case (LN lholed vs n es' l es'' k es lfilledk)
  obtain ts'' ts''' where "\<S>\<bullet>\<C> \<turnstile> [Label n es' lfilledk]  : (ts'' _> ts''')"
    using e_type_comp_conc2[OF LN(4)]
    by fastforce
  then obtain t1s t2s ts where test:"\<S>\<bullet>\<C>\<lparr>label := [ts] @ (label \<C>)\<rparr> \<turnstile> lfilledk  : (t1s _> t2s)"
    using e_type_label
    by metis
  show ?case
    using LN(3)[OF test(1)]
    by simp (metis append.assoc append_Cons append_Nil)
qed

lemma types_exist_lfilled_weak:
  assumes "Lfilled k lholed es lfilled"
          "\<S>\<bullet>\<C> \<turnstile> lfilled : (ts _> ts')"
  shows "\<exists>t1s t2s \<C>' arb_label arb_return. (\<S>\<bullet>\<C>\<lparr>label := arb_label, return := arb_return\<rparr> \<turnstile> es : (t1s _> t2s))"
proof -
  have "\<exists>t1s t2s \<C>' arb_label. (\<S>\<bullet>\<C>\<lparr>label := arb_label, return := (return \<C>)\<rparr> \<turnstile> es : (t1s _> t2s))"
    using types_exist_lfilled[OF assms]
    by fastforce
  thus ?thesis
    by fastforce
qed

lemma global_extension_trans:
  assumes "global_extension g g''"
          "global_extension g'' g'"
  shows "global_extension g g'"
  using assms
  unfolding global_extension_def
  by auto

lemma limits_compat_trans:
  assumes "limits_compat l l'"
          "limits_compat l' l''"
        shows "limits_compat l l''"
  using assms
  unfolding limits_compat_def
  by (auto split:option.splits simp add: pred_option_def)

lemma mem_extension_trans:
  assumes "mem_extension m m''"
          "mem_extension m'' m'"
  shows "mem_extension m m'"
  using assms
  unfolding mem_extension_def mem_subtyping_def
  using limits_compat_trans
  by auto

lemma tab_subtyping_trans:
  assumes "tab_subtyping t t'"
          "tab_subtyping t' t''"
        shows "tab_subtyping t t''"
  using assms
  unfolding tab_subtyping_def
  by (auto simp add: limits_compat_trans split: tab_t.splits)


lemma tab_extension_trans:
  assumes "tab_extension t t''"
          "tab_extension t'' t'"
  shows "tab_extension t t'"
  using assms limits_compat_trans tab_subtyping_trans
  unfolding tab_extension_def
  by auto

lemma elem_extension_trans:
  assumes "elem_extension es es''"
          "elem_extension es'' es'"
  shows "elem_extension es es'"
  using assms unfolding elem_extension_def by auto


lemma data_extension_trans:
  assumes "data_extension es es''"
          "data_extension es'' es'"
  shows "data_extension es es'"
  using assms unfolding data_extension_def by auto

lemma store_extension_trans:
  assumes "store_extension s s''"
          "store_extension s'' s'"
        shows "store_extension s s'"
proof -
  obtain cls ts ms gs es ds ts'' ms'' gs'' es'' ds'' cls''_rest ts''_rest ms''_rest gs''_rest es''_rest ds''_rest where s_is:
    "s = \<lparr>s.funcs = cls, s.tabs = ts, s.mems = ms, s.globs = gs, s.elems = es, s.datas = ds\<rparr>"
    "s'' = \<lparr>s.funcs = cls@cls''_rest, s.tabs = ts''@ts''_rest, s.mems = ms''@ms''_rest, s.globs = gs''@gs''_rest, s.elems = es''@es''_rest, s.datas = ds''@ds''_rest\<rparr>"
    "list_all2 tab_extension ts ts''"
    "list_all2 mem_extension ms ms''"
    "list_all2 global_extension gs gs''"
    "list_all2 elem_extension es es''"
    "list_all2 data_extension ds ds''"
    using assms(1)
    by (cases rule: store_extension.cases) blast
  obtain cls'_rest ts' ts'_rest ms' ms'_rest gs' gs'_rest es' es'_rest ds' ds'_rest where s'_is:
    "s' = \<lparr>s.funcs = cls@cls''_rest@cls'_rest, s.tabs = ts'@ts'_rest, s.mems = ms'@ms'_rest, s.globs = gs'@gs'_rest, s.elems = es'@es'_rest, s.datas = ds'@ds'_rest\<rparr>"
    "list_all2 tab_extension (ts''@ts''_rest) ts'"
    "list_all2 mem_extension (ms''@ms''_rest) ms'"
    "list_all2 global_extension (gs''@gs''_rest) gs'"
    "list_all2 elem_extension (es''@es''_rest) es'"
    "list_all2 data_extension (ds''@ds''_rest) ds'"
    using assms(2) s_is(2)
    apply (cases rule: store_extension.cases)
    apply (metis (no_types, lifting) append.assoc s.ext_inject)
    done
  obtain ts'_' ts'_rest_' ms'_' ms'_rest_' gs'_' gs'_rest'_' es'_' es'_rest'_' ds'_' ds'_rest'_' where s'_is_alt:
    "ts' = ts'_'@ts'_rest_'"
    "ms' = ms'_'@ms'_rest_'"
    "gs' = gs'_'@gs'_rest'_'"
    "es' = es'_'@es'_rest'_'"
    "ds' = ds'_'@ds'_rest'_'"
    "list_all2 tab_extension ts'' ts'_'"
    "list_all2 mem_extension ms'' ms'_'"
    "list_all2 global_extension gs'' gs'_'"
    "list_all2 elem_extension es'' es'_'"
    "list_all2 data_extension ds'' ds'_'"
    using s'_is
          list_all2_append1[of tab_extension "ts''" "ts''_rest" ts']
          list_all2_append1[of mem_extension "ms''" "ms''_rest" ms']
          list_all2_append1[of global_extension "gs''" "gs''_rest" gs']
          list_all2_append1[of elem_extension "es''" "es''_rest" es']
          list_all2_append1[of data_extension "ds''" "ds''_rest" ds']
    apply simp
    apply (metis (no_types, lifting))
    done
  have
    "list_all2 tab_extension ts ts'_'"
    "list_all2 mem_extension ms ms'_'"
    "list_all2 global_extension gs gs'_'"
    "list_all2 elem_extension es es'_'"
    "list_all2 data_extension ds ds'_'"
    using s_is(3,4,5,6,7) s'_is_alt list_all2_trans tab_extension_trans mem_extension_trans global_extension_trans elem_extension_trans data_extension_trans
    by blast+
  thus ?thesis
    using s'_is s'_is_alt
    by (simp add: s_is store_extension.simps) blast
qed

lemma global_extension_update:
  assumes "g_mut g = T_mut"
          "typeof (g_val g) = typeof v"
  shows "global_extension g (g\<lparr>g_val := v\<rparr>)"
  using assms
  unfolding global_extension_def
  by auto

lemma inst_typing_glob_length:
  assumes "inst_typing s i \<C>"
  shows "length (global \<C>) = length (inst.globs i)"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by force

lemma inst_typing_func_length:
  assumes "inst_typing s i \<C>"
  shows "length (func_t \<C>) = length (inst.funcs i)"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by force

lemma store_typing_imp_glob_agree:
  assumes "inst_typing s i \<C>"
          "j < length (global \<C>)"
  shows "(sglob_ind i j) < length (globs s)"
        "glob_typing (sglob s i j) ((global \<C>)!j)"
proof -
  show "glob_typing (sglob s i j) ((global \<C>)!j)"
       "(sglob_ind i j) < length (globs s)"
    using assms
    unfolding inst_typing.simps sglob_def sglob_ind_def list_all2_conv_all_nth
    by (metis globi_agree_def inst.select_convs(5) t_context.select_convs(3))+
qed

lemma inst_typing_imp_memi_agree:
  assumes "inst_typing s i \<C>"
          "(smem_ind i) = Some k"
  shows "memi_agree (mems s) k (hd (memory \<C>))"
proof -
  show "memi_agree (mems s) k (hd (memory \<C>))"
    using assms
    unfolding inst_typing.simps smem_ind_def
    apply (simp split: list.splits)
    apply (metis list.sel(1) list_all2_Cons1)
    done
qed

lemma inst_typing_imp_tabi_agree:
  assumes "inst_typing s i \<C>"
          "(stab_ind i ti) = Some k"
  shows "tabi_agree (tabs s) k ((table \<C>)!ti)"
proof -
  show "tabi_agree (tabs s) k ((table \<C>)!ti)"
    using assms
    unfolding inst_typing.simps stab_ind_def
    by (metis handy_if_lemma inst.select_convs(3) list_all2_lengthD list_all2_nthD2 t_context.select_convs(6))
qed

lemma inst_typing_store_typing_imp_tab_agree:
  assumes "inst_typing s i \<C>"
          "store_typing s"
          "(stab_ind i ti) = Some k"
  shows "tab_agree s (tabs s!k)"
proof -
  have "tabi_agree (tabs s) k ((table \<C>)!ti)"
    using assms inst_typing_imp_tabi_agree by simp
  then have "k < length (tabs s)"
    using tabi_agree_def by blast
  then show "tab_agree s (tabs s!k)" using assms(2) store_typing.simps
    by (simp add: list_all_length)
qed

lemma inst_typing_imp_types_eq:
  assumes "inst_typing s i \<C>"
          "j < length (types_t \<C>)"
  shows "(types_t \<C>)!j = (types i)!j"
  using assms
  unfolding inst_typing.simps
  by auto

lemma cl_type_exists:
  assumes "cl_typing s cl tf"
  shows "tf = cl_type cl"
  using assms
  unfolding cl_type_def
  by (induction) auto

lemma store_typing_imp_cl_typing:
  assumes "store_typing s"
          "j < length (funcs s)"
  shows "cl_typing s (funcs s!j) (cl_type (funcs s!j))"
  using assms cl_type_exists
  unfolding store_typing.simps list_all_length
  by auto

lemma store_typing_imp_func_agree:
  assumes "store_typing s"
          "inst_typing s i \<C>"
          "j < length (inst.funcs i)"
  shows "funci_agree (funcs s) (sfunc_ind i j) ((func_t \<C>)!j)"
        "cl_typing s (sfunc s i j) ((func_t \<C>)!j)"
proof -
  show 1:"funci_agree (funcs s) (sfunc_ind i j) ((func_t \<C>)!j)"
    using assms(2,3) list_all2_nthD
    unfolding inst_typing.simps sfunc_ind_def
    by fastforce
  hence "\<exists>t. cl_typing s (sfunc s i j) t"
    using assms
    unfolding store_typing.simps sfunc_ind_def sfunc_def funci_agree_def
    by (simp add: list_all_length)
  thus "cl_typing s (sfunc s i j) ((func_t \<C>)!j)"
    using cl_type_exists 1
    unfolding funci_agree_def sfunc_def
    by auto
qed

lemma store_mem_exists:
  assumes "inst_typing s i \<C>"
  shows "length (memory \<C>) = length (inst.mems i)"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by fastforce

lemma store_tab_exists:
  assumes "inst_typing s i \<C>"
  shows "length (table \<C>) = length (inst.tabs i)"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by fastforce


lemma store_types_exists:
  assumes "inst_typing s i \<C>"
  shows "types_t \<C> = inst.types i"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by fastforce

lemma store_elem_exists:
  assumes "inst_typing s i \<C>"
  shows "length (elem \<C>) = length (inst.elems i)"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by fastforce

lemma store_data_exists:
  assumes "inst_typing s i \<C>"
  shows "length (data \<C>) = length (inst.datas i)"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by fastforce

lemma globi_agree_store_extension:
  assumes "list_all2 (globi_agree (globs s)) (inst.globs i) (global \<C>)"
          "store_extension s s'"
  shows "list_all2 (globi_agree (globs s')) (inst.globs i) (global \<C>)"
proof -
  have "\<And>tg i. i < length (globs s) \<Longrightarrow> glob_typing ((globs s)!i) tg \<Longrightarrow> glob_typing ((globs s')!i) tg"
    using assms
    unfolding glob_typing_def store_extension.simps global_extension_def list_all2_conv_all_nth
    by (metis nth_append s.select_convs(4))
  moreover
  have "length (globs s) \<le> length (globs s')"
    using assms(2) list_all2_lengthD
    unfolding store_extension.simps
    by fastforce
  ultimately
  show ?thesis
    using assms(1)
    unfolding list_all2_conv_all_nth globi_agree_def
    by force
qed

lemma tab_typing_extension:
  assumes "tab_extension tabinst tabinst'"
          "tab_subtyping (fst tabinst) tt"
  shows   "tab_subtyping (fst tabinst') tt"
  using assms
proof -
  have h1: "tab_size tabinst \<le> tab_size tabinst'"
           "tab_max tabinst = tab_max tabinst'"
           "tab_subtyping (fst tabinst') (fst tabinst)"

    using tab_extension_def assms(1) by auto
  have h2: "(limits_compat (tab_t_lim (fst tabinst)) (tab_t_lim tt)) \<and> (tab_t_reftype (fst tabinst)) = tab_t_reftype tt"
    using assms(2) unfolding tab_subtyping_def tab_t_reftype_def
    by (auto simp add: tab_t.exhaust tab_t_lim_def split: tab_t.splits)
  moreover have "tab_t_reftype tt = tab_reftype tabinst'" using h1(3)
    using h2 tab_reftype_def tab_t_reftype_def tab_subtyping_def
    by (metis (mono_tags, lifting) case_prodD tab_t.case tab_t.exhaust)
  moreover have "limits_compat (tab_t_lim (fst tabinst')) (tab_t_lim (fst tabinst))"
    using h1(3) unfolding tab_subtyping_def using tab_t_lim_def
    by (metis (no_types, lifting) case_prodD tab_t.case tab_t.exhaust)
  moreover have "(limits_compat (tab_t_lim (fst tabinst')) (tab_t_lim tt))"
    using h2 limits_compat_trans h1(3) calculation(3) unfolding tab_subtyping_def
    by blast
  ultimately show ?thesis
    by (metis (mono_tags, lifting) old.prod.case tab_reftype_def tab_t.case tab_t.exhaust tab_t_lim_def tab_t_reftype_def tab_subtyping_def)
qed


lemma tabi_agree_store_extension1:
  assumes "list_all2 (tabi_agree (tabs s)) (inst.tabs i) (table \<C>)"
          "store_extension s s'"
          "ti < length (inst.tabs i)"
          "inst.tabs i ! ti < length (s.tabs s)"
        shows   " tabi_agree (tabs s') (inst.tabs i ! ti) (table \<C>! ti)"
proof -
  let ?tabinst = "((tabs s)!(inst.tabs i ! ti))"
  let ?tabinst' = "((tabs s')!(inst.tabs i ! ti))"
  have h0: "tabi_agree (tabs s) ((inst.tabs i)!ti) (table \<C>! ti)"
    using assms(1) assms(3) list_all2_nthD by blast
  have h1: "tab_extension ?tabinst ?tabinst'"
    using assms(2) unfolding store_extension.simps
    by (metis assms(4) list_all2_lengthD list_all2_nthD nth_append s.select_convs(2))
  have h2: "tab_subtyping (fst ?tabinst) (table \<C>!ti)"
    by (meson assms(1) assms(3) list_all2_conv_all_nth tabi_agree_def)
  have h3: "tab_subtyping (fst ?tabinst') (table \<C>!ti)" using h1 h2 tab_typing_extension by simp
  obtain clss' clss'' where 1:"list_all2 tab_extension (tabs s) clss'"
                            "(tabs s') = clss'@clss''"
    using assms(2) store_extension.simps by auto
  then have "length (tabs s) \<le> length (tabs s')"
    by (simp add: list_all2_lengthD)
  moreover have "((inst.tabs i)!ti) < length (tabs s)" using h0 tabi_agree_def
    by auto
  moreover have h4: "((inst.tabs i)!ti) < length (tabs s')"
    using calculation(1) calculation(2) by fastforce
  show ?thesis using h4 h3 tabi_agree_def[of "s.tabs s'" "(inst.tabs i ! ti)" "table \<C>!ti"]
    by simp
qed

lemma tabi_agree_store_extension:
  assumes "list_all2 (tabi_agree (tabs s)) (inst.tabs i) (table \<C>)"
          "store_extension s s'"
  shows "list_all2 (tabi_agree (tabs s')) (inst.tabs i) (table \<C>)"
proof -
  obtain clss' clss'' where 1:"list_all2 tab_extension (tabs s) clss'"
                            "(tabs s') = clss'@clss''"
    using assms(2)
    unfolding store_extension.simps
    by auto
  have "list_all2 (tabi_agree (tabs s)) (inst.tabs i) (table \<C>)"
    using assms 1 by simp
  have h1: "\<And> ti. ti < length (inst.tabs i) \<Longrightarrow> inst.tabs i ! ti < length (s.tabs s)"
    by (meson assms(1) list_all2_conv_all_nth tabi_agree_def)
  have h2: "\<And> idx. idx < length (s.tabs s) \<Longrightarrow>
    tab_extension  ((tabs s)!idx) (clss'!idx) "
    using "1"(1) list_all2_nthD by blast
  then have "\<And> ti. ti < length (inst.tabs i) \<Longrightarrow> tabi_agree clss' (inst.tabs i ! ti) (table \<C>! ti)"
  proof -
    fix ti
    assume hti: "ti < length (inst.tabs i)"
    then have "inst.tabs i ! ti < length (s.tabs s)"
      using h1 by blast
    then show "tabi_agree clss' (inst.tabs i ! ti) (table \<C>! ti)"
      using tabi_agree_store_extension1[OF assms(1) assms(2) hti]
      by (metis "1"(1) "1"(2) list_all2_lengthD nth_append tabi_agree_def)
  qed
  then have "list_all2 (tabi_agree clss') (inst.tabs i) (table \<C>)"
    by (meson assms(1) list_all2_conv_all_nth)
  thus ?thesis
    using 1(2) nth_append[of clss' clss'']
    unfolding list_all2_conv_all_nth tabi_agree_def
    by auto
qed

lemma mem_extension_typing:
  assumes "mem_subtyping (fst m) mt"
          "mem_extension m m'"
        shows "mem_subtyping (fst m') mt"
proof -
  obtain lims rep lmin lmax lims' rep' lmin' lmax'
    where defs: "m = (lims , rep)"
                "m' = (lims', rep')"
                "lmin = l_min lims"
                "lmax = l_max lims"
                "lmin' = l_min lims'"
                "lmax' = l_max lims'"
    by fastforce
  then have "(mem_max m) = (mem_max m')"
    using assms(2)
    using mem_extension_def by blast
  then have "mem_size m \<le> mem_size m'"
    using assms(2) mem_extension_def by blast
  
  moreover have "limits_compat lims mt" using assms(1) defs(1) unfolding mem_subtyping_def by simp
  moreover have "limits_compat lims' lims" using defs assms(2) unfolding mem_extension_def mem_subtyping_def by simp
  ultimately show ?thesis unfolding mem_subtyping_def using defs limits_compat_trans by auto
qed

lemma memi_agree_store_extension:
  assumes "list_all2 (memi_agree (mems s)) (inst.mems i) (memory \<C>)"
          "store_extension s s'"
  shows "list_all2 (memi_agree (mems s')) (inst.mems i) (memory \<C>)"
proof -
  obtain mss' mss'' where 1:"list_all2 mem_extension (mems s) mss'"
                            "(mems s') = mss'@mss''"
    using assms(2)
    unfolding store_extension.simps
    by auto
  have "list_all2 (memi_agree mss') (inst.mems i) (memory \<C>)"
    using assms 1(1) mem_extension_typing
    unfolding store_extension.simps list_all2_conv_all_nth mem_extension_def memi_agree_def
              mem_subtyping_def limits_compat_def
    by (metis dual_order.trans mem_max_def)
  thus ?thesis
    using 1(2) nth_append[of mss' mss'']
    unfolding list_all2_conv_all_nth memi_agree_def
    by auto
qed

lemma ref_typing_store_extension_inv:
  assumes "store_extension s s'"
          "ref_typing s vr \<C>"
        shows "ref_typing s' vr \<C>"
  using assms ref_typing.simps store_extension.simps by fastforce

lemma elemi_agree_store_extension:
  assumes "list_all2 (elemi_agree s (elems s)) (inst.elems i) (elem \<C>)"
          "store_extension s s'"
  shows "list_all2 (elemi_agree s' (elems s')) (inst.elems i) (elem \<C>)"
proof -
  obtain ess' ess'' where 1: "list_all2 elem_extension (elems s) ess'"
                             "elems s' = ess'@ess''"
    using assms(2)
    unfolding store_extension.simps by auto
  have "\<And> n. n < length (inst.elems i) \<Longrightarrow> (elemi_agree s' (elems s')) (inst.elems i!n) (elem \<C>!n)"
  proof -
    fix n
    assume n_len: "n < length (inst.elems i)"
    then have "(elemi_agree s (elems s)) (inst.elems i!n) (elem \<C>!n)"
      using assms list_all2_nthD by blast
    then have 2: "((inst.elems i!n) < length (elems s) \<and> elem_typing s ((elems s)!(inst.elems i!n)) (elem \<C>!n))"
      unfolding elemi_agree_def by simp
    then have 3: "(inst.elems i!n) < length (elems s')"
      using 1 list_all2_lengthD by fastforce
    have 4: "((elems s')!(inst.elems i!n)) = ess'!(inst.elems i!n)"
      by (metis 1 2 list_all2_lengthD nth_append)
    then have 5: "elem_extension (elems s!(inst.elems i!n)) (ess'!(inst.elems i!n))"
      by (simp add: 1 2 list_all2_nthD)
    then have "elem_typing s' ((elems s')!(inst.elems i!n)) (elem \<C>!n)"
    proof -
      have 6: "fst (ess' ! (inst.elems i ! n)) = elem \<C> ! n" using 2 4 5 unfolding elem_extension_def
        by (simp add: elem_typing_def)
      have 7: "(snd (s.elems s' ! (inst.elems i ! n))) = [] \<or> (snd (s.elems s' ! (inst.elems i ! n))) = (snd (s.elems s ! (inst.elems i ! n)))"
        using "4" "5" elem_extension_def by auto
      then have "list_all (\<lambda> vr. ref_typing s vr (elem \<C> ! n)) (snd (s.elems s' ! (inst.elems i ! n)))"
        
        using "2" elem_typing_def by auto
      then have "list_all (\<lambda> vr. ref_typing s' vr (elem \<C> ! n)) (snd (s.elems s' ! (inst.elems i ! n)))"
        using assms(2)
        by (simp add: list_all_length ref_typing_store_extension_inv)
      then show ?thesis using 4 6 7 unfolding elem_typing_def
         by metis
     qed
    then show "(elemi_agree s' (elems s')) (inst.elems i!n) (elem \<C>!n)"
      using "3" elemi_agree_def by blast
  qed
  then show ?thesis using assms
    by (simp add: list_all2_conv_all_nth)
qed


lemma datai_agree_store_extension:
  assumes "list_all2 (datai_agree (datas s)) (inst.datas i) (data \<C>)"
          "store_extension s s'"
  shows "list_all2 (datai_agree (datas s')) (inst.datas i) (data \<C>)"
proof -
  obtain dss' dss'' where 1: "list_all2 data_extension (datas s) dss'"
                             "datas s' = dss'@dss''"
    using assms(2)
    unfolding store_extension.simps by auto
  then have "length (datas s)  = length (dss')"
    using list_all2_conv_all_nth by blast
  then have "length (datas s) \<le> length (datas s')"
    by (simp add: "1"(2))
  then show ?thesis
    by (metis assms(1) data_typing_def datai_agree_def list_all2_mono order_less_le_trans)
qed

lemma inst_typing_store_extension_inv:
  assumes "inst_typing s i \<C>"
          "store_extension s s'" 
    shows "inst_typing s' i \<C>"
proof -
  have 0:"types i = types_t \<C>"
         "list_all2 (funci_agree (funcs s)) (inst.funcs i) (func_t \<C>)"
         "list_all2 (globi_agree (globs s)) (inst.globs i) (global \<C>)"
         "list_all2 (tabi_agree (tabs s)) (inst.tabs i) (table \<C>)"
         "list_all2 (memi_agree (mems s)) (inst.mems i) (memory \<C>)"
         "list_all2 (elemi_agree s (elems s)) (inst.elems i) (elem \<C>)"
         "list_all2 (datai_agree (datas s)) (inst.datas i) (data \<C>)"
         "(local \<C>) = []" "(label \<C>) = []" "(return \<C>) = None"
    using assms(1)
    unfolding inst_typing.simps
    by auto
  have 1:"list_all2 (funci_agree (funcs s')) (inst.funcs i) (func_t \<C>)"
    using 0(2) assms(2)
    unfolding list_all2_conv_all_nth funci_agree_def store_extension.simps
    by (metis length_append nth_append s.select_convs(1) trans_less_add1)
  have 2:"list_all2 (globi_agree (globs s')) (inst.globs i) (global \<C>)"
    using globi_agree_store_extension 0(3) assms(2)
    by blast
  have 3:"list_all2 (tabi_agree (tabs s')) (inst.tabs i) (table \<C>)"
    using tabi_agree_store_extension 0(4) assms(2)
    by blast
  have 4:"list_all2 (memi_agree (mems s')) (inst.mems i) (memory \<C>)"
    using memi_agree_store_extension 0(5) assms(2)
    by blast
  have 5:"list_all2 (elemi_agree s' (elems s')) (inst.elems i) (elem \<C>)"
    using elemi_agree_store_extension 0(6) assms(2)
    by blast
  have 6:"list_all2 (datai_agree (datas s')) (inst.datas i) (data \<C>)"
    using datai_agree_store_extension 0(7) assms(2)
    by blast
  show ?thesis
    using 1 2 3 4 5 6 assms(1) inst_typing.simps
    by auto
qed

lemma v_typing_store_extension_inv:
  assumes "v_typing s v t"
          "store_extension s s'"
        shows "v_typing s' v t"
  using assms
proof(cases v)
  case (V_num x1)
  then show ?thesis using v_typing.simps
    using assms(1) by fastforce
next
  case (V_vec x2)
  then show ?thesis using v_typing.simps
    using assms(1) by fastforce
next
  case (V_ref x3)
  then show ?thesis
  proof(cases x3)
    case (ConstNull x1)
    then show ?thesis 
      using V_ref assms(1) ref_typing.simps v_typing.simps by fastforce
  next
    case (ConstRefFunc x2)
    then have "ref_typing s (ConstRefFunc x2) T_func_ref"
      using V_ref assms(1) ref_typing.simps v_typing.simps by auto
   then have "ref_typing s' (ConstRefFunc x2) T_func_ref"
     using assms(2) ref_typing.simps store_extension.simps by fastforce
    then show ?thesis
      by (metis ConstRefFunc V_ref assms(1) v_typing.intros(3) v_typing_typeof)
  next
    case (ConstRefExtern x3)
    then show ?thesis
      by (metis V_ref assms(1) ref_typing.intros(3) v_typing.intros(3) v_typing_typeof)
  qed
qed

lemma v_typing_funcs_inv:
  assumes "v_typing s v t"
          "funcs s = funcs s'"
        shows "v_typing s' v t"
proof(cases v)
  case (V_num x1)
  then show ?thesis
    using assms(1) v_typing.simps by auto
next
  case (V_vec x2)
  then show ?thesis
    using assms(1) v_typing.simps by auto
next
  case (V_ref x3)
  then show ?thesis
    using assms ref_typing.simps v_typing.simps
    by (auto split: v_ref.splits)
qed

lemma v_typing_list_store_extension_inv:
  assumes "list_all2 (\<lambda> v t. v_typing s v t) vs ts"
          "store_extension s s'"
        shows "list_all2 (\<lambda> v t. v_typing s' v t) vs ts"
  using assms
proof(induction vs arbitrary: ts)
  case Nil
  then show ?case
    by fastforce
next
  case (Cons a vs)
  then show ?case
    by (metis list_all2_mono v_typing_store_extension_inv)
qed

lemma frame_typing_store_extension_inv:
  assumes "frame_typing s f \<C>"
          "store_extension s s'" 
    shows "frame_typing s' f \<C>"
  using assms inst_typing_store_extension_inv v_typing_list_store_extension_inv
  unfolding frame_typing.simps
  by fastforce

lemma cl_typing_store_extension_inv:
  assumes "store_extension s s'"
          "cl_typing s cl tf"
  shows "cl_typing s' cl tf"
proof (cases cl)
  case (Func_native x11 x12 x13 x14)
  thus ?thesis
    using assms
    unfolding cl_typing.simps
    by (simp, metis (no_types, lifting) inst_typing_store_extension_inv)
next
  case (Func_host x21 x22)
  thus ?thesis
    using assms
    unfolding cl_typing.simps
    by auto
qed

lemma bitzero_v_typing:
  assumes "bitzero t = Some v"
  shows "v_typing s v t"
proof(cases t)
  case (T_num x1)
  then show ?thesis using assms unfolding bitzero_def
    by (metis bitzero_def bitzero_typeof option.inject t.simps(16) v_typing.intros(1) v_typing_typeof)
next
  case (T_vec x2)
  then show ?thesis using assms unfolding bitzero_def
    using assms bitzero_typeof typeof_def v_typing.simps by fastforce
next
  case (T_ref x3)
  then show ?thesis using assms unfolding bitzero_def
    by (metis (mono_tags, lifting) bitzero_ref_def option.sel ref_typing.intros(1) t.simps(18) t_ref.exhaust t_ref.simps(3) t_ref.simps(4) v_typing.intros(3))
next
  case T_bot
  then show ?thesis using assms bitzero_def by fastforce
qed

lemma n_zeroes_v_typing:
  "(n_zeros ts) = Some vs \<Longrightarrow> list_all2 (\<lambda> v t. v_typing s v t) vs ts"
proof(induction ts arbitrary: vs)
  case Nil
  then show ?case
    by (simp add: n_zeros_def)
next
  case (Cons t ts)
  then obtain v vs' where v_defs:
    "bitzero t = Some v"
    "those (map bitzero ts) = Some vs'"
    "vs = v#vs'"
    unfolding n_zeros_def using those.simps
    by (auto split: prod.splits option.splits)
  then have "n_zeros ts = Some vs'" using n_zeros_def by simp
  then show ?case
    using Cons bitzero_v_typing[OF v_defs(1)] v_defs
    by (simp add: bitzero_v_typing n_zeros_def)
qed

lemma e_typing_thread_typing_store_extension_inv:
  assumes"store_extension s s'"
  shows "s\<bullet>\<C> \<turnstile> es : tf \<Longrightarrow> s'\<bullet>\<C> \<turnstile> es : tf"
        "s\<bullet>rs \<tturnstile> f;es : ts \<Longrightarrow> s'\<bullet>rs \<tturnstile> f;es : ts"
  using assms
proof (induction s \<C> es tf and s rs f es ts rule: e_typing_thread_typing.inducts)

  case (4 \<S> v_r \<C>)
  then show ?case
    using ref_typing_store_extension_inv e_typing_thread_typing.intros(4) by auto
next
  case (7 i \<S> tf \<C>)
  have "i < length (s.funcs s')"
    using 7(1,3)
    unfolding store_extension.simps
    by auto
  moreover
  have "s.funcs \<S> ! i = s.funcs s' ! i"
    using 7(1,3)
    unfolding store_extension.simps
    by (metis nth_append s.select_convs(1))
  ultimately
  show ?case
    using e_typing_thread_typing.intros(7) 7(2)
    by simp
next
  case (8 \<C> \<S> bs n)
  thus ?case
    using e_typing_thread_typing.intros(8)
    unfolding store_extension.simps
    by (auto simp add: list_all2_lengthD)
next
  case (9 \<S> f \<C> rs es ts)
  thus ?case
    using frame_typing_store_extension_inv
          e_typing_thread_typing.intros(9)
    by blast
qed (auto simp add: e_typing_thread_typing.intros)

lemma tab_agree_store_extension_inv:
  assumes "store_extension s s'"
          "tab_agree s t"
        shows "tab_agree s' t"
  using assms
proof -
  obtain lims tr elems where t_def: "t = (T_tab lims tr, elems)"
    by (metis old.prod.exhaust tab_t.exhaust)
  then have "l_min lims = (tab_size t) \<and>
              pred_option (\<lambda> max. tab_size t \<le> max) (tab_max t) \<and>
              list_all (\<lambda> vr. ref_typing s vr tr) elems" using assms(2) tab_agree_def by simp
  then have "l_min lims = (tab_size t) \<and>
            pred_option (\<lambda> max. tab_size t \<le> max) (tab_max t) \<and>
            list_all (\<lambda> vr. ref_typing s' vr tr) elems" using ref_typing_store_extension_inv
    by (meson assms(1) list_all_length)
  then show ?thesis using t_def tab_agree_def by auto
qed


lemma glob_agree_store_extension_inv:
  assumes "store_extension s s'"
          "glob_agree s g"
        shows "glob_agree s' g"
proof -
  obtain t where t_def: "(v_typing s (g_val g) t)" using assms(2) glob_agree_def by auto
  then have "v_typing s' (g_val g) t"
    using assms(1) ref_typing_store_extension_inv v_typing.simps by auto
  then show ?thesis
    using glob_agree_def by blast
qed

lemma store_typing_in_mem_agree:
  assumes "store_typing s"
          "j < length (s.mems s)"
          "s.mems s ! j = m"
  shows "mem_agree m"
  using assms
  by (auto simp add: store_typing.simps list_all_length)

lemma store_typing_in_tab_agree:
  assumes "store_typing s"
          "j < length (s.tabs s)"
          "s.tabs s ! j = t"
  shows "tab_agree s t"
  using assms
  by (auto simp add: store_typing.simps list_all_length)

lemma store_typing_in_elem_agree:
  assumes "store_typing s"
          "j < length (elems s)"
          "s.elems s ! j = el"
  shows "elem_agree s el"
  using assms
  by (auto simp add: store_typing.simps list_all_length)

lemma store_extension_mem_leq:
  assumes "store_typing s"
          "s.mems s ! j = m"
          "mem_size m \<le> mem_size m'"
          "mem_agree m'"
          "mem_max m = mem_max m'"
          "mem_subtyping (fst m') (fst m)"
  shows "store_extension s (s\<lparr>s.mems := (s.mems s)[j := m']\<rparr>)"
        "store_typing (s\<lparr>s.mems := (s.mems s)[j := m']\<rparr>)"
proof -
  obtain s' where s'_def:"s' = (s\<lparr>s.mems := (s.mems s)[j := m']\<rparr>)"
    by blast
  have 0:"funcs s = funcs s'"
         "tabs s = tabs s'"
         "globs s = globs s'"
         "elems s = elems s'"
         "datas s = datas s'"
    using s'_def
    by simp_all
  then have "mem_extension m m'"
    using assms(3,5,6)
    unfolding mem_extension_def mem_subtyping_def
    by simp
  hence h_mems: "list_all2 mem_extension (mems s) (mems s')"
    using assms(2) s'_def
    by (simp, metis list.rel_refl list_all2_update_cong list_update_id mem_extension_refl)
  thus sh1:"store_extension s (s\<lparr>s.mems := (s.mems s)[j := m']\<rparr>)"
    using store_extension.intros[OF _
                                    list_all2_refl[OF tab_extension_refl]
                                    _
                                    list_all2_refl[OF global_extension_refl]
                                    list_all2_refl[OF elem_extension_refl]
                                    list_all2_refl[OF data_extension_refl],
                                 of _ _ _ _ _ _  _ _ "[]" "[]" "[]" "[]" "[]"]
          s'_def 0
    by (metis (full_types) 0 append_Nil2 unit.exhaust s.surjective)

  have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (s.funcs s')"
    using assms(1) cl_typing_store_extension_inv[OF sh1] 0(1)
    unfolding store_typing.simps list_all_length
    by (metis s'_def)
  moreover
  have "list_all (tab_agree s') (s.tabs s')"
    by (metis (no_types, lifting) "0"(2) assms(1) list.pred_mono_strong s'_def sh1 store_typing.cases tab_agree_store_extension_inv)
  moreover
  have "list_all (glob_agree s') (s.globs s')"
    using glob_agree_store_extension_inv[OF sh1]
    by (metis "0"(3) assms(1) list_all_length s'_def store_typing.cases)
  moreover
  have "list_all (elem_agree s') (s.elems s')"
    using ref_typing_store_extension_inv elem_agree_def
     by (metis (no_types, lifting) "0"(4) assms(1) list_all_length s'_def sh1 store_typing.cases)
  moreover
  have "list_all (data_agree s') (s.datas s')"
    by (simp add: data_agree_def list_all_length)
  ultimately
  show "store_typing (s\<lparr>s.mems := (s.mems s)[j := m']\<rparr>)"
    using store_typing.simps tab_agree_store_extension_inv[OF sh1]
    unfolding s'_def list_all_length
    apply (simp add: store_typing.simps)
    by (metis assms(1) assms(4) nth_list_update_eq nth_list_update_neq store_typing_in_mem_agree)
qed

lemma ref_typing_update_store:
  assumes "ref_typing s vr tr"
          "funcs s = funcs s'"
  shows "ref_typing s' vr tr"
  using assms
  by (simp add: ref_typing.simps)

lemma tab_agree_update_store:
  assumes "tab_agree s t"
          "funcs s = funcs s'"
        shows "tab_agree s' t"
proof(cases t)
  case (Pair a b)
  then show ?thesis
  proof(cases a)
    case (T_tab x1 x2)
    then show ?thesis using assms Pair unfolding tab_agree_def using ref_typing_update_store[of s _ _ s']
      by (simp add: list_all_length)
  qed  
qed

lemma store_extension_tab_leq:
  assumes "store_typing s"
          "s.tabs s ! j = t"
          "tab_size t \<le> tab_size t'"
          "tab_agree s t'"
          "tab_max t = tab_max t'"
          "tab_subtyping (fst t') (fst t)"
  shows "store_extension s (s\<lparr>s.tabs := (s.tabs s)[j := t']\<rparr>)"
        "store_typing (s\<lparr>s.tabs := (s.tabs s)[j := t']\<rparr>)"
proof -
  obtain s' where s'_def:"s' = (s\<lparr>s.tabs := (s.tabs s)[j := t']\<rparr>)"
    by blast
  have 0:"funcs s = funcs s'"
         "mems s = mems s'"
         "globs s = globs s'"
         "elems s = elems s'"
         "datas s = datas s'"
    using s'_def
    by simp_all
  have "tab_extension t t'"
    using assms(3,5,6)
    unfolding tab_extension_def
    by simp
  hence "list_all2 tab_extension (tabs s) (tabs s')"
    using assms(2) s'_def
    by (simp, metis list.rel_refl list_all2_update_cong list_update_id tab_extension_refl)
  thus sh1:"store_extension s (s\<lparr>s.tabs := (s.tabs s)[j := t']\<rparr>)"
    using store_extension.intros[OF _
                                    _
                                    list_all2_refl[OF mem_extension_refl]
                                    list_all2_refl[OF global_extension_refl]
                                    list_all2_refl[OF elem_extension_refl]
                                    list_all2_refl[OF data_extension_refl],
                                 of _ _ _ _ _ _ _ _ "[]" "[]" "[]" "[]" "[]" "[]"]
          s'_def
    by (metis (full_types) 0 append_Nil2 unit.exhaust s.surjective)

  have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (s.funcs s')"
    using assms(1) cl_typing_store_extension_inv[OF sh1] 0(1)
    unfolding store_typing.simps list_all_length
    by (metis s'_def)
  moreover
  have "list_all mem_agree (s.mems s')"
    using 0(2) assms(1) store_typing.cases
    by fastforce
  moreover
  have "list_all (glob_agree s') (s.globs s')"
    using glob_agree_store_extension_inv[OF sh1]
    by (metis "0"(3) assms(1) list_all_length s'_def store_typing.cases)
  moreover
  have "list_all (elem_agree s') (s.elems s')"
    using ref_typing_store_extension_inv elem_agree_def
     by (metis (no_types, lifting) "0"(4) assms(1) list_all_length s'_def sh1 store_typing.cases)
  moreover
  have "list_all (data_agree s') (s.datas s')"
    by (simp add: data_agree_def list_all_length)
  ultimately
  show "store_typing (s\<lparr>s.tabs := (s.tabs s)[j := t']\<rparr>)"
    using store_typing.simps tab_agree_store_extension_inv[OF sh1]
    unfolding s'_def list_all_length store_extension_refl
    apply (simp add: store_typing.simps)
    by (metis assms(1) assms(4) nth_list_update_eq nth_list_update_neq store_typing_in_tab_agree)
qed

lemma update_glob_store_extension:
  assumes "store_typing s"
          "supdate_glob s i j v = s'"
          "(globs s)!sglob_ind i j = g"
          "g_mut g = T_mut"
          "v_typing s v (typeof (g_val g))"
  shows "store_extension s s'"
        "store_typing s'"
proof -
  obtain k where k_def:"k = (sglob_ind i j)"
    by blast
  hence s'_def:"s' = s\<lparr>s.globs := (s.globs s)[k := (s.globs s ! k)\<lparr>g_val := v\<rparr>]\<rparr>"
    using assms(2)
    unfolding supdate_glob_def sglob_ind_def update_glob_def
    by metis
  have 1:"(funcs s) = (funcs s')"
         "(tabs s) = (tabs s')"
         "(mems s) = (mems s')"
         "elems s = elems s'"
         "datas s = datas s'"
    using s'_def mem_extension_refl list_all2_refl
    by auto
  have "typeof (g_val g) = typeof v"
  proof(cases v)
    case (V_num x1)
    then show ?thesis using assms(5)
      by (simp add: typeof_def v_typing.simps)
  next
    case (V_vec x2)
    then show ?thesis using assms(5)
      by (simp add: typeof_def v_typing.simps)
  next
    case (V_ref x3)
    then show ?thesis
      by (metis assms(5) const_typeof e_typing_thread_typing.intros(4) v.simps(12) v.simps(7) v.simps(9) v_to_e_def v_typing.simps)
  qed
  then have "global_extension ((globs s)!k) ((globs s')!k)"
    using global_extension_update assms(3,4,5) s'_def
    by (simp, metis global.surjective global.update_convs(2) k_def length_list_update nth_equalityI nth_list_update nth_list_update_neq)
  hence "list_all2 global_extension (globs s) (globs s')"
    using s'_def global_extension_refl
    by (simp, metis list_all2_refl list_all2_update_cong list_update_id list_update_overwrite)
  thus sh1:"store_extension s s'"
    using store_extension.intros[OF _
                                    list_all2_refl[OF tab_extension_refl]
                                    list_all2_refl[OF mem_extension_refl]
                                    _
                                    list_all2_refl[OF elem_extension_refl]
                                    list_all2_refl[OF data_extension_refl],
                                 of _ _ _ _ _ _ _ _ _ "[]" "[]" "[]" "[]" "[]"]
          s'_def
    by (metis (full_types) 1 append_Nil2 unit.exhaust s.surjective)
  have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (s.funcs s')"
    using assms(1) cl_typing_store_extension_inv[OF sh1] 1(1)
    unfolding store_typing.simps list_all_length
    by fastforce
  moreover
  have "list_all (tab_agree s') (s.tabs s')"
    by (metis (no_types, lifting) 1(2) assms(1) list.pred_mono_strong sh1 store_typing.cases tab_agree_store_extension_inv)
  moreover
  have "list_all (glob_agree s') (s.globs s')"
  proof -
    have "\<And> n. n < length (s.globs s') \<Longrightarrow> glob_agree s' (s.globs s'!n)"
    proof -
      fix n
      assume hn: " n < length (s.globs s')"
      then show "glob_agree s' (s.globs s'!n)"
      proof(cases "n=k")
        case True
        then show ?thesis
          by (metis (no_types, lifting) assms(5) glob_agree_def glob_agree_store_extension_inv global.select_convs(2) global.surjective global.update_convs(2) hn length_list_update nth_list_update_eq s'_def s.select_convs(4) s.surjective s.update_convs(4) sh1)
      next
        case False
        then show ?thesis
          by (metis hn assms(1) glob_agree_store_extension_inv length_list_update list_all_length nth_list_update_neq s'_def s.select_convs(4) s.surjective s.update_convs(4) sh1 store_typing.cases)
      qed
    qed
    then show ?thesis using list_all_length by auto
  qed
  moreover
  have "list_all (elem_agree s') (s.elems s')"
    using ref_typing_store_extension_inv elem_agree_def
    by (metis (no_types, lifting) "1"(4) assms(1) list_all_length sh1 store_typing.cases)
  moreover
  have "list_all (data_agree s') (s.datas s')"
    by (simp add: data_agree_def list_all_length)
  ultimately
  show "store_typing s'"
    using 1(3) assms(1) store_typing.simps
    by auto
qed

lemma elem_drop_store_extension:
  assumes "a < length (elems s)"
          "store_typing s"
          "s' = s\<lparr>s.elems := (s.elems s)[a := (fst (s.elems s ! a), [])]\<rparr>"
  shows "store_extension s s'"
        "store_typing s'"
proof -
  have 0: "(funcs s) = (funcs s')"
          "(tabs s) = (tabs s')"
          "(mems s) = (mems s')"
          "(globs s) = (globs s')"
          "datas s = datas s'"
    using assms(3)
    by fastforce+
  have 1: "list_all2 elem_extension (elems s) (elems s')" unfolding elem_extension_def
    apply (simp add: assms(3))
    by (metis (mono_tags, lifting) list.rel_refl list_all2_update_cong list_update_id fst_conv snd_conv)
  then show sh1: "store_extension s s'"
    using store_extension.intros[OF 0(1) list_all2_refl[OF tab_extension_refl]
                                      list_all2_refl[OF mem_extension_refl]
                                      list_all2_refl[OF global_extension_refl]
                                      1 
                                      list_all2_refl[OF data_extension_refl]
                                      , of "tabs s" "mems s" "globs s" "datas s" "[]" "[]" "[]" "[]" "[]" "[]"]
    apply simp
    using 0
    by (metis (full_types) old.unit.exhaust s.surjective)
  have "list_all (elem_agree s) (elems s)" using assms(2) unfolding store_typing.simps by simp
  then have "list_all (elem_agree s') (elems s')"
    using ref_typing_store_extension_inv[OF sh1] unfolding elem_agree_def assms(3) using assms(1) snd_conv
    nth_list_update_eq[OF assms(1)]
    by (simp add: list_all_length nth_list_update)
  moreover
  have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (s.funcs s')"
    using cl_typing_store_extension_inv[OF sh1] 0(1)
    unfolding store_typing.simps list_all_length
    by (metis assms(2) store_typing_imp_cl_typing)
  moreover
  have "list_all mem_agree (s.mems s')" 
    using "0"(3) assms(2) store_typing.simps by fastforce
  moreover
  have "list_all (glob_agree s') (s.globs s')"
    by (metis "0"(4) assms(2) glob_agree_store_extension_inv list_all_length sh1 store_typing.cases)
  moreover
  have "list_all (data_agree s') (s.datas s')"
    by (simp add: data_agree_def list_all_length)
  ultimately
  show"store_typing s'"
     using assms(2) 0 unfolding store_typing.simps
     by (metis (no_types, lifting) list.pred_mono_strong tab_agree_update_store)
qed

lemma data_drop_store_extension:
  assumes "a < length (datas s)"
          "store_typing s"
          "s' = s\<lparr>s.datas := (s.datas s)[a := []]\<rparr>"
  shows "store_extension s s'"
        "store_typing s'"
proof -
  have 0: "(funcs s) = (funcs s')"
          "(tabs s) = (tabs s')"
          "(mems s) = (mems s')"
          "(globs s) = (globs s')"
          "elems s = elems s'"
    using assms(3)
    by fastforce+
  have 1: "list_all2 data_extension (datas s) (datas s')" unfolding elem_extension_def
    unfolding assms(3) using data_extension_def apply simp
    by (metis list_all2_refl list_all2_update_cong list_update_id)
  then show sh1: "store_extension s s'"
    using store_extension.intros[OF 0(1) list_all2_refl[OF tab_extension_refl]
                                      list_all2_refl[OF mem_extension_refl]
                                      list_all2_refl[OF global_extension_refl]
                                      list_all2_refl[OF elem_extension_refl] 
                                      1
                                      , of "tabs s" "mems s" "globs s" "elems s" "[]" "[]" "[]" "[]" "[]" "[]"]
    apply simp
    using 0
    by (metis (full_types) old.unit.exhaust s.surjective)
  have "list_all (elem_agree s) (elems s)" using assms(2) unfolding store_typing.simps by simp
  then have "list_all (elem_agree s') (elems s')"
    by (metis "0"(5) elem_agree_def list.pred_mono_strong ref_typing_store_extension_inv sh1)
  moreover
  have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (s.funcs s')"
    using cl_typing_store_extension_inv[OF sh1] 0(1)
    unfolding store_typing.simps list_all_length
    by (metis assms(2) store_typing_imp_cl_typing)
  moreover
  have "list_all mem_agree (s.mems s')" 
    using "0"(3) assms(2) store_typing.simps by fastforce
  moreover
  have "list_all (glob_agree s') (s.globs s')"
    by (metis "0"(4) assms(2) glob_agree_store_extension_inv list_all_length sh1 store_typing.cases)
  moreover
  have "list_all (data_agree s') (s.datas s')"
    by (simp add: data_agree_def list_all_length)
  ultimately
  show"store_typing s'"
     using assms(2) 0 unfolding store_typing.simps
     by (metis (no_types, lifting) list.pred_mono_strong tab_agree_update_store)
qed

lemma types_agree_imp_e_typing:
  assumes "v_typing \<S> v t"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
  using assms
proof(induction)
  case (1 s vn)
  then show ?case
    using const_num e_typing_thread_typing.intros(1) v_to_e_def by fastforce
next
  case (2 s vv)
  then show ?case
    by (metis const_vec e_typing_thread_typing.intros(1) to_e_list_1 v.simps(11) v_to_e_def)
next
  case (3 s vr t)
  then show ?case
    by (simp add: e_typing_thread_typing.intros(4) v_to_e_def)
qed

lemma list_types_agree_imp_e_typing:
  assumes "list_all2 (\<lambda>t v. v_typing \<S> v t) ts vs"
  shows "\<S>\<bullet>\<C> \<turnstile> $C* vs : ([] _> ts)"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  thus ?case
    using b_e_typing.empty e_typing_thread_typing.intros(1)
    by fastforce
next
  case (Cons t ts v vs)
  hence "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
    using types_agree_imp_e_typing
    by fastforce
  thus ?case
    using e_typing_thread_typing.intros(3)[OF Cons(3), of "[t]"] e_type_comp_conc
    using Cons.IH e_weakening by fastforce
qed

lemma e_typing_imp_list_types_agree:
  assumes "\<S>\<bullet>\<C> \<turnstile> ($C* vs) : (ts' _> ts'@ts)"
  shows "list_all2 (\<lambda>t v. typeof v = t) ts vs"
proof -
  have "[] _> map typeof vs <ti: ts' _> ts' @ ts"
    using assms e_type_consts store_extension_refl by blast
  then have "[] _> map typeof vs <ti: [] _>  ts"
    using instr_subtyping_append_split1 by blast
  then have "t_list_subtyping (map typeof vs) ts"
    unfolding instr_subtyping_def
    by (simp add: t_list_subtyping_def)
  then have "list_all2 (\<lambda>v t. typeof v = T_bot \<or> typeof v = t) vs ts"
    unfolding t_list_subtyping_def t_subtyping_def
    by (simp add: list.rel_map(1))
  then show ?thesis using typeof_not_bot
    by (simp add: list_all2_conv_all_nth)
qed

lemma e_typing_imp_list_v_typing:
  assumes "\<S>\<bullet>\<C> \<turnstile> $C* vs : (ts _> ts')"
  shows
    "list_all (\<lambda> v. v_typing \<S> v (typeof v)) vs"
    "([] _> (map typeof vs)) <ti: (ts _> ts')"
  using assms
proof(induction vs arbitrary: ts ts' rule: rev_induct)
  case (snoc x xs)
  {
    case 1
      have "\<S>\<bullet>\<C> \<turnstile> $C* xs @ [x] : ts _> ts'"
        using "1" by auto
      then have "\<S>\<bullet>\<C> \<turnstile> ($C* xs) @ [$C x] : ts _> ts'" by simp
      then obtain ts'' where
         "\<S>\<bullet>\<C> \<turnstile> ($C* xs) : ts _> ts''"
         "\<S>\<bullet>\<C> \<turnstile> [$C x] : ts'' _> ts'"
        using e_type_comp by blast
      then show ?case
        by (simp add: snoc.IH type_const_v_typing(2))
  next
    case 2
    then show ?case
      using e_type_consts store_extension_refl by blast
  }
qed auto

lemma lfilled_deterministic:
  assumes "Lfilled k lfilled es les"
          "Lfilled k lfilled es les'"
  shows "les = les'"
  using assms
proof (induction arbitrary: les' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  thus ?case
    by (fastforce simp add: Lfilled.simps[of 0])
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  thus ?case
    unfolding Lfilled.simps[of "(k + 1)"]
    by fastforce
qed

lemma types_preserved_global_set_aux:
  assumes "s\<bullet>\<C> \<turnstile> [$C v, $Global_set j] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
        "tg_t (global \<C> ! j) = typeof v"
        "tg_mut (global \<C> ! j) = T_mut"
        "j < length(global \<C>)"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts'')" 
                             "s\<bullet>\<C> \<turnstile> [$Global_set j] : (ts'' _> ts')"
                             "\<C> \<turnstile> [Global_set j] : (ts'' _> ts')"
    using e_type_comp assms unlift_b_e
    by (metis append_Cons append_Nil to_e_list_1)
  hence 1: "([] _> [typeof v]) <ti: (ts _> ts'')"
    using e_type_const_new store_extension_refl by blast
  obtain t where t_def: "([t] _> []) <ti: (ts'' _> ts')" "global \<C> ! j = \<lparr>tg_mut = T_mut, tg_t = t\<rparr>" "j < length (global \<C>)"
    using b_e_type_global_set ts''_def(3) by blast
  have 2: "t = typeof v" "([typeof v] _> []) <ti: (ts'' _> ts')"
  proof -
    obtain ts''' where ts'''_def: "ts'' = ts'''@[typeof v]"
      using 1
      by (metis append_Nil instr_subtyping_append_t_list_subtyping instr_subtyping_refl t_list_subtyping_instr_subtyping_append t_list_subtyping_snoc_left1 typeof_not_bot)
    then have "([t] _> [])  <ti: (ts'''@[typeof v] _> ts')"
      using 1
      using t_def(1) by blast
    then have "([t] _> [])  <ti: ([typeof v] _> [])"
      using ts'''_def unfolding instr_subtyping_def
      using t_def(1) t_list_subtyping_def
      by (metis append1_eq_conv append_Nil list_all2_Cons2 list_all2_Nil2 tf.sel(1) tf.sel(2))
    then show "t = typeof v"
      unfolding instr_subtyping_def t_list_subtyping_def
      using t_subtyping_def typeof_not_bot
      by simp
    then show "([typeof v] _> []) <ti: (ts'' _> ts')"
      using t_def(1) by blast
  qed
  then have 3: "([] _> []) <ti: (ts _> ts')"
    using "1" instr_subtyping_comp by blast
  show "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')" "tg_t (global \<C> ! j) = typeof v" "tg_mut (global \<C> ! j) = T_mut" "j < length(global \<C>)"
    using 1 2 3 e_type_empty  t_def by fastforce+
qed

lemma store_tabs1_store_extension:
  assumes "store_tabs1 (s.tabs s) a k vr = Some tabs'"
          "a < length (s.tabs s)"
          "store_typing s"
          "ref_typing s vr (tab_reftype (tabs s!a))"
    shows
          "store_typing (s\<lparr>s.tabs := tabs'\<rparr>)"
          "store_extension s (s\<lparr>s.tabs := tabs'\<rparr>)"
  using assms
proof -
  let ?tab = "tabs s ! a"
  obtain tab' where tab'_def:
    "Some tab' = (store_tab1 ((tabs s)!a) k vr)" 
    "tabs' = (take a (tabs s)) @ [tab'] @ (drop (a+1) (tabs s))"
      using assms(1) unfolding store_tabs1_def
      by (simp split: option.splits)
    have 0: "tab_agree s (tabs s!a)"
      by (metis assms(1,2,3) option.simps(3) store_tabs1_def store_typing_in_tab_agree)
    have 1: "snd tab' = (snd (tabs s!a))[k := vr]"
      by (metis Suc_eq_plus1 append_Cons append_Nil option.inject option.simps(3) snd_conv store_tab1_def tab'_def(1) upd_conv_take_nth_drop)
    have 2: "fst tab' = fst (tabs s!a)"
      by (metis fst_conv option.inject option.simps(3) store_tab1_def tab'_def(1))
    have 3: "tab_agree s ((tabs s)!a)"
      by (simp add: \<open>tab_agree s (s.tabs s ! a)\<close>)
    obtain lims tr elems lims' tr' elems' where defs:
      "(tabs s)!a= (T_tab lims tr, elems)"
      "tab'= (T_tab lims' tr', elems')"
      by (metis prod.collapse tab_t.exhaust)
    then have defs_props: "lims' = lims" "tr' = tr" "elems' = elems[k := vr]"
      using "1" "2" defs by fastforce+
    have a: "l_min lims' = tab_size tab'"
    proof -
      have "tab_size tab' = tab_size ?tab"
        by (simp add: "1")
      moreover have "tab_size ?tab = l_min lims" using 0 defs(1) unfolding tab_agree_def
        by auto
      moreover have "l_min lims' = l_min lims" using defs_props by simp
      ultimately show ?thesis by simp
    qed
    have b: "pred_option ((\<le>) (tab_size tab')) (tab_max tab')"
    proof -
      have "tab_max tab' = tab_max ?tab"
        by (simp add: "2" split_beta tab_max_def)
      moreover have "(tab_size tab') = (tab_size (tabs s ! a))"
        using "1" by auto
      moreover have "pred_option ((\<le>) (tab_size ?tab)) (tab_max ?tab)"
        using 0 unfolding tab_agree_def
        by (metis (mono_tags, lifting) case_prod_beta tab_t.case tab_t.exhaust)
      ultimately show ?thesis by simp
    qed
    have c: "list_all (\<lambda>vr. ref_typing s vr tr') elems'"
    proof -
      have "list_all (\<lambda>vr. ref_typing s vr tr) elems" using 0 unfolding tab_agree_def
        using defs(1) by fastforce 
      moreover have "ref_typing s vr tr"
      proof -
        have "tr = tab_reftype (tabs s!a)" using defs(1) tab_reftype_def by simp
        then show ?thesis using assms(4) by simp
      qed
      moreover have "list_all (\<lambda>vr. ref_typing s vr tr) elems'"
        by (metis calculation(1) calculation(2) defs_props(3) length_list_update list_all_length nth_list_update_eq nth_list_update_neq)
      then show ?thesis using defs_props(2) by simp
    qed
    have "list_all2 tab_extension (tabs s) tabs'"
    proof -
      have "tab_extension (?tab) tab'"
        by (simp add: "1" "2" case_prod_beta' tab_extension_def tab_max_def tab_subtyping_refl)
      then show "list_all2 tab_extension (tabs s) tabs'"
        using assms(2)
        by (metis (no_types, opaque_lifting) Suc_eq_plus1 append_Cons append_Nil assms(1) list_all2_refl list_all2_update_cong list_update_id not_None_eq store_tabs1_def tab'_def(2) tab_extension_refl upd_conv_take_nth_drop)
    qed
    then have s0:"store_extension s (s\<lparr>s.tabs := tabs'\<rparr>)"
    proof - 
      let ?s = "s\<lparr>s.tabs := tabs'\<rparr>"
      have s1: "funcs s = funcs ?s" by simp
      have s2: "list_all2 tab_extension (tabs s) (tabs ?s)"
        using \<open>list_all2 tab_extension (s.tabs s) tabs'\<close> by auto
      have s3: "list_all2 mem_extension (mems s) (mems ?s)" using mem_extension_refl
        by (simp add: list.rel_refl)

      have s4: "list_all2 global_extension (globs s) (globs ?s)"
        by (simp add: global_extension_refl list.rel_refl)
      have s5: "list_all2 elem_extension (s.elems s) (s.elems ?s)"
        by (simp add: elem_extension_refl list.rel_refl)
      have s6: "list_all2 data_extension (s.datas s) (s.datas ?s)"
        by (simp add: data_extension_refl list.rel_refl)
      then show ?thesis
        using store_extension.intros[OF s1 s2 s3 s4 s5 s6, of "[]" "[]" "[]" "[]" "[]" "[]"]
        apply simp
        by (metis old.unit.exhaust s.surjective s.update_convs(2))
    qed

    have t1: "tab_agree s tab'" unfolding tab_agree_def using a b c defs(2) by fastforce
    have t2: "tab_subtyping (fst tab') (fst (s.tabs s ! a))"
      by (simp add: "2" tab_subtyping_refl)
    have t3: "tab_size (s.tabs s ! a) \<le> tab_size tab'"
      by (simp add: "1")
    have t4: "tab_max (s.tabs s ! a) = tab_max tab'"
      by (simp add: "2" case_prod_beta' tab_max_def)
    then have "tab_agree (s\<lparr>s.tabs := tabs'\<rparr>) tab'" using t1 tab_agree_update_store by auto
    then have "list_all (tab_agree (s\<lparr>s.tabs := tabs'\<rparr>)) tabs'"
      using s0 tab'_def
      by simp (metis append_take_drop_id assms(3) list_all_append list_all_length
          store_typing_in_tab_agree tab_agree_store_extension_inv)
    show "store_typing (s\<lparr>s.tabs := tabs'\<rparr>)"
         "store_extension s (s\<lparr>s.tabs := tabs'\<rparr>)"
      using store_extension_tab_leq[OF assms(3) _ t3 t1 t4 t2, of a]
      apply (metis Suc_eq_plus1 append.simps(1) append.simps(2) assms(2) tab'_def(2) upd_conv_take_nth_drop)
      by (simp add: \<open>store_extension s (s\<lparr>s.tabs := tabs'\<rparr>)\<close>)
qed

lemma types_preserved_table_set_aux:
  assumes "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n), Ref vr, $Table_set ti] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
        "tab_t_reftype (table \<C> ! ti) = typeof_ref vr"
        "ti < length (table \<C>)"
        "ref_typing s vr (typeof_ref vr)"
proof -
  obtain ts1 ts2 where ts_def:"s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n)] : (ts _> ts1)" 
                              "s\<bullet>\<C> \<turnstile> [Ref vr] : (ts1 _> ts2)"
                             "s\<bullet>\<C> \<turnstile> [$Table_set ti] : (ts2 _> ts')"
    by (metis (no_types, opaque_lifting) append_Cons assms e_type_comp_conc2 self_append_conv2)
  hence 1: "([] _> [T_num T_i32]) <ti: (ts _> ts1)"
    by (metis e_type_cnum typeof_num_def v_num.case(1))
  hence 2: "([] _> [T_ref (typeof_ref vr)]) <ti: (ts1 _> ts2)"
    using e_type_cref ts_def(2) by blast
  hence 3: "([] _> [T_num T_i32, T_ref (typeof_ref vr)]) <ti: (ts _> ts2)"
    using "1" instr_subtyping_concat by fastforce
  then obtain ts2' where ts2'_def: "ts2 = ts2'@[T_num T_i32, T_ref (typeof_ref vr)]"
    by (metis Cons_eq_append_conv t.distinct(11) t.simps(9) t_list_subtyping_instr_subtyping_append t_list_subtyping_refl t_list_subtyping_snoc_left2)
  have 4: "s\<bullet>\<C> \<turnstile> [$C (V_ref vr)] : (ts1 _> ts2)"
    by (simp add: ts_def(2) v_to_e_def)
  have 5: "ref_typing s vr (typeof_ref vr)"
    by (metis "4" t.inject(3) type_const_v_typing(2) typeof_def v.distinct(3) v.inject(3) v.simps(12) v.simps(9) v_typing.simps)
  have 6: "\<C> \<turnstile> [Table_set ti] : (ts2 _> ts')"
    using ts_def(3) unlift_b_e by force
  then obtain tr where tr_def: "[T_num T_i32, T_ref tr] _> [] <ti: ts2 _> ts'" "tab_t_reftype (table \<C> ! ti) = tr"
    using b_e_type_table_set[OF 6] by blast
  obtain ts2'' ts2''_last2 where ts2''_def: "ts2 = ts2''@ts2''_last2" "t_list_subtyping ts2''_last2 [T_num T_i32, T_ref tr]"
    using instr_subtyping_split_empty2[OF tr_def(1)] by blast
  then have 7: "t_subtyping (last ts2) (T_ref tr)"
    by (metis "2" append_butlast_last_id instr_subtyping_append1_type_eq last.simps last_appendR list.distinct(1) t_subtyping_def tr_def(1) ts2'_def)
  have 8: "last ts2 = T_ref (typeof_ref vr)" using ts2'_def
    by simp
  have 9: "tr = typeof_ref vr" using 7 8 t_subtyping_def by simp
  then have "([] _> []) <ti: (ts _> ts')"
    using b_e_type_table_set[OF 6]
    using "3" instr_subtyping_comp tr_def by blast
  then show "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
        "tab_t_reftype (table \<C> ! ti) = typeof_ref vr"
        "ti < length (table \<C>)"
        "ref_typing s vr (typeof_ref vr)"
    using e_type_empty b_e_type_table_set(2) tr_def 5 6 9 by blast+
qed

lemma types_preserved_table_grow_aux:
  assumes "s\<bullet>\<C> \<turnstile> [Ref vr, $EConstNum (ConstInt32 n), $Table_grow ti] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [] : (ts@[T_num T_i32] _> ts')"
        "tab_t_reftype (table \<C> ! ti) = typeof_ref vr"
        "ti < length (table \<C>)"
        "ref_typing s vr (typeof_ref vr)"
        "[] _> [T_num T_i32] <ti: (ts _>ts')"
proof -
  obtain ts1 ts2 where ts_def:"s\<bullet>\<C> \<turnstile> [Ref vr] : (ts _> ts1)" 
                                   "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n)] : (ts1 _> ts2)"
                             "s\<bullet>\<C> \<turnstile> [$Table_grow ti] : (ts2 _> ts')"
    by (metis (no_types, opaque_lifting) append_Cons assms e_type_comp_conc2 self_append_conv2)
  hence 1: "([] _> [T_ref (typeof_ref vr)]) <ti: (ts _> ts1)"
    by (metis e_type_cref)
  hence 2: "([] _> [T_num T_i32]) <ti: (ts1 _> ts2)" 
    using e_type_cnum ts_def(2)
    by (metis typeof_num_def v_num.case(1))
  hence 3: "([] _> [T_ref (typeof_ref vr), T_num T_i32]) <ti: (ts _> ts2)"
    using 1 instr_subtyping_concat by fastforce
  have 4: "s\<bullet>\<C> \<turnstile> [$EConstNum (ConstInt32 n)] : (ts1 _> ts2)"
    by (simp add: ts_def(2) v_to_e_def)
  have 5: "ref_typing s vr (typeof_ref vr)"
    by (metis t.inject(3) ts_def(1) type_const_v_typing(2) typeof_def v.distinct(3) v.inject(3) v.simps(12) v.simps(9) v_to_e_def v_typing.simps)
  
  have 6: "\<C> \<turnstile> [Table_grow ti] : (ts2 _> ts')"
    using ts_def(3) unlift_b_e by force
  have 7:
    "([T_ref (typeof_ref vr), T_num T_i32] _> [T_num T_i32]) <ti: (ts2 _> ts')"
    "tab_t_reftype (table \<C> ! ti) = typeof_ref vr"
  proof -
    obtain tr where tr_def:
      "([T_ref tr, T_num T_i32] _> [T_num T_i32]) <ti: (ts2 _> ts')"
      "tr = tab_t_reftype (table \<C> ! ti)"
      using b_e_type_table_grow[OF 6]
      by fastforce
    obtain ts2' ts2'_last2 where ts2'_def: "ts2 = ts2'@ts2'_last2" "t_list_subtyping [T_ref (typeof_ref vr), T_num T_i32] ts2'_last2"
      using instr_subtyping_def 3 by auto
    obtain ts2'' ts2''_last2 where ts2''_def: "ts2 = ts2''@ts2''_last2" "t_list_subtyping ts2''_last2 [T_ref tr, T_num T_i32]"
      using instr_subtyping_def tr_def(1) by auto
    have "length ts2'_last2 = length ts2''_last2" using ts2'_def(2) ts2''_def(2) t_list_subtyping_def
      by (metis One_nat_def Suc_1 length_Cons list.size(3) list_all2_lengthD)
    then have "ts2'_last2 = ts2''_last2" using ts2'_def(1) ts2''_def(1) by auto
    then have "T_ref tr = T_ref (typeof_ref vr)" using ts2'_def(2) ts2''_def(2) t_list_subtyping_def
      by (metis append_eq_append_conv append_self_conv2 list.inject list_all2_lengthD t.distinct(11) t.distinct(5) t_list_subtyping_snoc_left2)
    then show "tab_t_reftype (table \<C> ! ti) = typeof_ref vr"
      using tr_def(2) by fastforce
    then show "([T_ref (typeof_ref vr), T_num T_i32] _> [T_num T_i32]) <ti: (ts2 _> ts')"
      using tr_def(1) tr_def(2) by metis
  qed
  then have 8: "([T_ref (typeof_ref vr), T_num T_i32] _> [T_num T_i32]) <ti: (ts2 _> ts')"
    using b_e_type_table_grow[OF 6]
    by fastforce
  then show
    "s'\<bullet>\<C> \<turnstile> [] : (ts@[T_num T_i32] _> ts')"
    "tab_t_reftype (table \<C> ! ti) = typeof_ref vr"
    "ti < length (table \<C>)"
    "ref_typing s vr (typeof_ref vr)"
    "([] _> [T_num T_i32]) <ti: (ts _>ts')"
    apply (metis "3" append_Nil2 e_type_empty e_typing_thread_typing.intros(3) e_weakening instr_subtyping_comp instr_subtyping_concat instr_subtyping_refl)
    using 3 5 6 7 8 instr_subtyping_comp b_e_type_table_grow(2) by blast+
qed


lemma list_all2_snoc1:
  assumes "list_all2 f (es@[e]) es'"
  shows "\<exists>es'1 e'. es' = es'1@[e'] \<and> list_all2 f es es'1 \<and> f e e'"
proof -
  have "list_all2 f (e#(rev es)) (rev es')"
    using assms list_all2_rev
    by (metis rev.simps(2) rev_rev_ident)
  thus ?thesis
    by (metis list_all2_Cons1 list_all2_rev1 rev_eq_Cons_iff)
qed

lemma lfilled_lfilled_app:
  assumes "Lfilled k lholed es LI"
          "Lfilled k lholed es' LI'"
  shows "\<exists>lholed'. Lfilled k lholed' es (($C*vcs)@LI) \<and> Lfilled k lholed' es' (($C*vcs)@LI')"
  using assms
proof (induction k lholed es LI arbitrary: es' vcs LI' rule: Lfilled.induct)
  case (L0 lholed vs_l0 es_l0 es)
  obtain lholed' where lholed'_def:"lholed' = LBase (vcs @ vs_l0) es_l0"
    by blast
  have 1:"LI' = ($C* vs_l0) @ es' @ es_l0"
    using L0 Lfilled.simps
    by blast
  have "Lfilled 0 (LBase (vcs @ vs_l0) es_l0) es (($C* vcs @ vs_l0) @ es @ es_l0)"
       "Lfilled 0 (LBase (vcs @ vs_l0) es_l0) es' (($C* vcs @ vs_l0) @ es' @ es_l0)"
    using Lfilled.intros(1)
    by blast+
  thus ?case
    using 1
    by auto
next
  case (LN lholed vs n es'_ln l es'' k es lfilledk)
  obtain lholed' where lholed'_def:"lholed' = LRec (vcs @ vs) n es'_ln l es''"
    by blast
  obtain lfilledk' where lfilledk'_def:"LI' = ($C*vs) @ [Label n es'_ln lfilledk'] @ es''"
                                       "Lfilled k l es' lfilledk'"
    using LN(1,4) Lfilled.simps[of "(k + 1)" lholed es' LI']
    by fastforce
  have "Lfilled (k + 1) lholed' es (($C* vcs @ vs) @ [Label n es'_ln lfilledk] @ es'')"
       "Lfilled (k + 1) lholed' es' (($C* vcs @ vs) @ [Label n es'_ln lfilledk'] @ es'')"
    using Lfilled.intros(2)[OF lholed'_def] LN(2) lfilledk'_def(2)
    by blast+
  thus ?case
    using lfilledk'_def(1)
    by auto
qed

lemma lfilled_single:
  assumes "Lfilled k lholed es [e]"
          "\<And> a b c. e \<noteq> Label a b c"
  shows "(es = [e] \<and> lholed = LBase [] [] \<and> k = 0) \<or> es = []"
  using assms
proof (cases rule: Lfilled.cases)
  case (L0 vs es')
  thus ?thesis
    by (metis (no_types, lifting) Cons_eq_append_conv append_is_Nil_conv list.map_disc_iff)
next
  case (LN vs n es' l es'' k lfilledk)
  assume "(\<And>a b c. e \<noteq> Label a b c)"
  thus ?thesis
    using LN(2)
    unfolding Cons_eq_append_conv
    by fastforce
qed

lemma lfilled_eq:
  assumes "Lfilled j lholed es LI"
          "Lfilled j lholed es' LI"
  shows "es = es'"
  using assms
proof (induction arbitrary: es' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  thus ?case
    using Lfilled.simps[of 0, simplified]
    by auto
next
  case (LN lholed vs n les' l les'' k les lfilledk)
  thus ?case
    using Lfilled.simps[of "(k+1)" "LRec vs n les' l les''" es' "(($C*vs) @ [Label n les' lfilledk] @ les'')", simplified]
    by auto
qed

lemma const_list_split_2:
  assumes "s\<bullet>\<C> \<turnstile> ($C*vs) : ([] _> [t1, t2])"
  shows "\<exists>c1 c2. (s\<bullet>\<C> \<turnstile> [$C c1] : ([] _> [t1]))
                 \<and> (s\<bullet>\<C> \<turnstile> [$C c2] : ([] _> [t2]))
                 \<and> vs = [c1, c2]"
proof -
  have map_typeof_vs_is: "map typeof vs = [t1, t2]"
    using e_type_consts_typeof[OF assms store_extension_refl[of s]] by simp
  hence l_cs:"length vs = 2"
    using length_map[of typeof vs]
    by simp
  then obtain c1 c2 where "vs!0 = c1" "vs!1 = c2"
    by fastforce
  hence "vs = [c1, c2]"
    using l_cs
    by (metis One_nat_def Suc_1 less_2_cases_iff less_one list_exhaust_size_eq0 list_exhaust_size_gt0 nth_Cons_0 nth_Cons_Suc size_Cons_lem_eq)
  thus ?thesis
    using assms e_type_comp[of s \<C> "[$C c1]" "$C c2", of "[]" "[t1, t2]"]
          e_type_const_new store_extension_refl map_typeof_vs_is by auto
qed

lemma const_list_split_3:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [t1, t2, t3])"
  shows "\<exists>c1 c2 c3. (s\<bullet>\<C> \<turnstile> [$C c1] : ([] _> [t1]))
                    \<and> (s\<bullet>\<C> \<turnstile> [$C c2] : ([] _> [t2]))
                    \<and> (s\<bullet>\<C> \<turnstile> [$C c3] : ([] _> [t3]))
                    \<and> vs = [c1, c2, c3]"
proof -
  have map_typeof_vs_is: "map typeof vs = [t1, t2, t3]"
    using e_type_consts_typeof[OF assms] store_extension_refl[of s]
    by simp
  hence l_cs:"length vs = 3"
    using length_map[of typeof vs]
    by simp
  then obtain c1  vs' where "vs = c1#vs'"
    by (metis Suc_length_conv numeral_3_eq_3)
  moreover obtain c2 vs'' where "vs' = c2#vs''"
    using calculation l_cs
    by (metis length_Suc_conv list.inject numeral_3_eq_3)
  moreover obtain c3 where "vs'' = [c3]"
    using calculation l_cs
    by (metis length_Suc_conv list.inject list_exhaust_size_eq0 numeral_3_eq_3)
  ultimately have "vs = [c1, c2, c3]" by simp
  thus ?thesis
    using assms e_type_comp_conc2[of s \<C> "[$C c1]" "[$C c2]" "[$C c3]" "[]" "[t1,t2,t3]"]
          e_type_const_new[of _ _ c1] e_type_const_new[of _ _ c2] e_type_const_new[of _ _ c3]
          store_extension_refl map_typeof_vs_is
    by fastforce
qed

lemma const_of_typed_const_2:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [t1,t2])"
  shows "\<exists>v1 v2. vs = [v1, v2] \<and> typeof v1 = t1 \<and> typeof v2 = t2"
  using const_list_split_2[OF assms] const_list_def e_type_const_unwrap
        const_typeof
  by auto

lemma const_of_typed_const_3:
  assumes "s\<bullet>\<C> \<turnstile> $C*vs : ([] _> [t,t,t])"
  shows "\<exists>v1 v2 v3. vs = [v1, v2, v3] \<and> typeof v1 = t \<and> typeof v2 = t \<and> typeof v3 = t"
  using const_list_split_3[OF assms] const_list_def e_type_const_unwrap
        const_typeof
  by auto

end