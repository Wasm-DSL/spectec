
theory store_extension_typing
(* Imported Code *)
	imports isabelle_reference_output_wasm2
begin

lemma store_extension_wf:
  assumes "Extend_store s s'"
  shows "wf_store s'"
  using assms
proof cases
  case mk_Extend_store
  then show ?thesis by simp
qed

(*

lemma store_extension_externaddrok:
  assumes "Externaddr_ok s a ext"
          "wf_store s'"
          "Extend_store s s'"
        shows "Externaddr_ok s' a ext"
  using assms
proof (induction rule:Externaddr_ok.induct)
  case (Externaddr_ok__global a s v_globalinst)
  show ?case using assms(3)
  proof cases
    case mk_Extend_store
    then have ext: "Extend_globalinst (store_GLOBALS s ! a) (store_GLOBALS s' ! a)" 
      using mk_Extend_store Extend_store.simps
      by (meson Externaddr_ok__global.hyps(1) Externaddr_ok__global.prems(2) holds_upto_def)
    have alen: "a < length (store_GLOBALS s')" using mk_Extend_store 
    by (metis Extend_store.simps Externaddr_ok__global.hyps(1) Externaddr_ok__global.prems(2)
        holds_upto_def)
    show ?thesis using ext
    proof cases
      case (mk_Extend_globalinst ft mm fc)
      then show ?thesis using 
          alen mk_Extend_store(20) Externaddr_ok.Externaddr_ok__global 
          local.Externaddr_ok__global
      by fastforce
    qed
  qed
next
 case (Externaddr_ok__mem a s v_meminst)
  show ?case using assms(3)
  proof cases
    case mk_Extend_store
    then have ext: "Extend_meminst (store_MEMS s ! a) (store_MEMS s' ! a)" 
      using mk_Extend_store Extend_store.simps
      by (meson Externaddr_ok__mem.hyps(1) Externaddr_ok__mem.prems(2) holds_upto_def)
    have alen: "a < length (store_MEMS s')" using mk_Extend_store 
    by (metis Extend_store.simps Externaddr_ok__mem.hyps(1) Externaddr_ok__mem.prems(2)
        holds_upto_def)
    show ?thesis using ext
    proof cases
      case (mk_Extend_meminst ft mm fc)
      then show ?thesis using 
          alen mk_Extend_store(20) Externaddr_ok.Externaddr_ok__mem 
          local.Externaddr_ok__mem
      by fastforce
    qed
  qed
next

  case (Externaddr_ok__func s v_funcinst)
  show ?case using assms(3)
  proof cases
    case mk_Extend_store
    then have ext: "Extend_funcinst (store_FUNCS s ! a) (store_FUNCS s' ! a)" 
      using mk_Extend_store Extend_store.simps
      by (meson Externaddr_ok__func.hyps(1) Externaddr_ok__func.prems(2) holds_upto_def)
    have alen: "a < length (store_FUNCS s')" using mk_Extend_store 
    by (metis Extend_store.simps Externaddr_ok__func.hyps(1) Externaddr_ok__func.prems(2)
        holds_upto_def)
    show ?thesis using ext
    proof cases
      case (mk_Extend_funcinst ft mm fc)
      then show ?thesis using 
          alen mk_Extend_store(20) Externaddr_ok.Externaddr_ok__func 
          local.Externaddr_ok__func 
      by fastforce
    qed
  qed
next
  case (Externaddr_ok__sub xt')
  then show ?thesis 
  using Externtype_sub.cases Functype_sub.simps by fastforce
qed

*)

lemma store_extension_externaddrok_func:
  assumes "Externaddr_ok s (externaddr_FUNC a) (FUNC ext)"
          "Extend_store s s'"
        shows "Externaddr_ok s' (externaddr_FUNC a) (FUNC ext)"
  using assms
proof (induction "s" "externaddr_FUNC a" "FUNC ext" rule:Externaddr_ok.induct)
  case (Externaddr_ok__func s v_funcinst)
  show ?case using assms(2)
  proof cases
    case mk_Extend_store
    then have ext: "Extend_funcinst (store_FUNCS s ! a) (store_FUNCS s' ! a)" 
      using mk_Extend_store Extend_store.simps
      by (meson Externaddr_ok__func.hyps(1) Externaddr_ok__func.prems holds_upto_def)
    have alen: "a < length (store_FUNCS s')" using mk_Extend_store 
    by (metis Extend_store.simps Externaddr_ok__func.hyps(1) Externaddr_ok__func.prems
        holds_upto_def)
    show ?thesis using ext
    proof cases
      case (mk_Extend_funcinst ft mm fc)
      then show ?thesis using 
          alen mk_Extend_store(20) Externaddr_ok.Externaddr_ok__func 
          local.Externaddr_ok__func 
      by fastforce
    qed
  qed
next
  case (Externaddr_ok__sub xt')
  then show ?thesis 
  using Externtype_sub.cases Functype_sub.simps by fastforce
qed


lemma store_extension_refok:
  assumes "Ref_ok s r rt"
          "Extend_store s s'"
        shows "Ref_ok s' r rt"
  using assms
proof cases
  case null
  then show ?thesis using store_extension_wf
  using Ref_ok.null assms(2) by blast 
next
  case (Ref_ok__func a ext)
  then show ?thesis using store_extension_externaddrok_func
  by (meson Ref_ok.simps assms(2) store_extension_wf)
next
  case (extern a)
  then show ?thesis using Ref_ok.extern store_extension_wf assms(2) by blast
qed


lemma store_extension_valok:
  assumes "Val_ok s v t"
          "wf_store s'" 
          "Extend_store s s'"
        shows "Val_ok s' v t"
  using assms
proof cases
  case (Val_ok__numtype nt c_t)
  then show ?thesis using Val_ok.Val_ok__numtype assms(2) by presburger
next
  case (Val_ok__vectype vt c_t)
  then show ?thesis using Val_ok.Val_ok__vectype assms(2) by presburger
next
  case (Val_ok__reftype r rt)
  then show ?thesis using store_extension_refok Val_ok.Val_ok__reftype assms(2,3) by blast
qed

lemma Limits_sub_grow:
  assumes "n \<le> n'"
          "wf_limits (mk_limits (mk_uN n) (map_option mk_uN m_opt))"
          "wf_limits (mk_limits (mk_uN n') (map_option mk_uN m_opt))"
  shows "Limits_sub (mk_limits (mk_uN n') (map_option mk_uN m_opt))
                    (mk_limits (mk_uN n) (map_option mk_uN m_opt))"
proof (cases m_opt)
  case None
  then show ?thesis using assms by (auto intro: Limits_sub.eps)
next
  case (Some m)
  then show ?thesis
    using assms Limits_sub.max[where ?n_1.0 = n' and ?n_2.0 = n and ?m_1.0 = m and m_2_opt = "Some m"]
    by simp
qed

lemma store_extension_externaddrok:
  assumes "Externaddr_ok s xa xt"
          "Extend_store s s'"
  shows "Externaddr_ok s' xa xt"
  using assms
proof (induction rule: Externaddr_ok.induct)
  case (Externaddr_ok__global a s v_globalinst)
  from Externaddr_ok__global.prems show ?case
  proof cases
    case mk_Extend_store
    have alen: "a < length (store_GLOBALS s')"
      using mk_Extend_store(2) Externaddr_ok__global(1) unfolding holds_upto_def by blast
    have "Extend_globalinst v_globalinst (store_GLOBALS s' ! a)"
      using mk_Extend_store(3) Externaddr_ok__global(1,2) unfolding holds_upto_def by blast
    then have "globalinst_TYPE (store_GLOBALS s' ! a) = globalinst_TYPE v_globalinst"
      by (cases rule: Extend_globalinst.cases) auto
    then show ?thesis
      using Externaddr_ok.Externaddr_ok__global[OF alen HOL.refl mk_Extend_store(20)]
        Externaddr_ok__global(4) by metis
  qed
next
  case (Externaddr_ok__func a s v_funcinst)
  from Externaddr_ok__func.prems show ?case
  proof cases
    case mk_Extend_store
    have alen: "a < length (store_FUNCS s')"
      using mk_Extend_store(11) Externaddr_ok__func(1) unfolding holds_upto_def by blast
    have "Extend_funcinst v_funcinst (store_FUNCS s' ! a)"
      using mk_Extend_store(12) Externaddr_ok__func(1,2) unfolding holds_upto_def by blast
    then have "funcinst_TYPE (store_FUNCS s' ! a) = funcinst_TYPE v_funcinst"
      by (cases rule: Extend_funcinst.cases) auto
    then show ?thesis
      using Externaddr_ok.Externaddr_ok__func[OF alen HOL.refl mk_Extend_store(20)]
        Externaddr_ok__func(4) by metis
  qed
next
  case (Externaddr_ok__mem a s v_meminst)
  from Externaddr_ok__mem.prems show ?case
  proof cases
    case mk_Extend_store
    have alen: "a < length (store_MEMS s')"
      using mk_Extend_store(5) Externaddr_ok__mem(1) unfolding holds_upto_def by blast
    have "Extend_meminst v_meminst (store_MEMS s' ! a)"
      using mk_Extend_store(6) Externaddr_ok__mem(1,2) unfolding holds_upto_def by blast
    then show ?thesis
    proof cases
      case (mk_Extend_meminst v_n n' b_lst b'_lst m_opt)
      have wfl: "wf_limits (mk_limits (mk_uN v_n) (map_option mk_uN m_opt))"
                "wf_limits (mk_limits (mk_uN n') (map_option mk_uN m_opt))"
        using mk_Extend_meminst(5,6) by (auto elim: wf_meminst.cases wf_memtype.cases)
      then have wfe: "wf_externtype (MEM (PAGE (mk_limits (mk_uN v_n) (map_option mk_uN m_opt))))"
                "wf_externtype (MEM (PAGE (mk_limits (mk_uN n') (map_option mk_uN m_opt))))"
        by (auto intro: wf_externtype.intros wf_memtype.intros)
      have lsub: "Limits_sub (mk_limits (mk_uN n') (map_option mk_uN m_opt))
                             (mk_limits (mk_uN v_n) (map_option mk_uN m_opt))"
        using Limits_sub_grow[OF mk_Extend_meminst(3) wfl] .
      have "Externaddr_ok s' (externaddr_MEM a)
              (MEM (PAGE (mk_limits (mk_uN n') (map_option mk_uN m_opt))))"
        using Externaddr_ok.Externaddr_ok__mem[OF alen HOL.refl mk_Extend_store(20)]
          mk_Extend_meminst(2) wfe(2) by fastforce
      then show ?thesis
        using Externaddr_ok.Externaddr_ok__sub[OF _ _ mk_Extend_store(20) wfe(1) wfe(2)]
          Externtype_sub__mem[OF mk_Memtype_sub[OF lsub] wfe(2,1)] wfe wfl mk_Extend_meminst(1)
        by (auto intro: wf_memtype.intros)
    qed
  qed
next
  case (Externaddr_ok__table a s v_tableinst)
  from Externaddr_ok__table.prems show ?case
  proof cases
    case mk_Extend_store
    have alen: "a < length (store_TABLES s')"
      using mk_Extend_store(8) Externaddr_ok__table(1) unfolding holds_upto_def by blast
    have "Extend_tableinst v_tableinst (store_TABLES s' ! a)"
      using mk_Extend_store(9) Externaddr_ok__table(1,2) unfolding holds_upto_def by blast
    then show ?thesis
    proof cases
      case (mk_Extend_tableinst v_n n' ref_lst ref'_lst m_opt rt)
      have wfl: "wf_limits (mk_limits (mk_uN v_n) (map_option mk_uN m_opt))"
                "wf_limits (mk_limits (mk_uN n') (map_option mk_uN m_opt))"
        using mk_Extend_tableinst(5,6) by (auto elim: wf_tableinst.cases wf_tabletype.cases)
      then have wfe: "wf_externtype (TABLE (mk_tabletype (mk_limits (mk_uN v_n) (map_option mk_uN m_opt)) rt))"
                "wf_externtype (TABLE (mk_tabletype (mk_limits (mk_uN n') (map_option mk_uN m_opt)) rt))"
        by (auto intro: wf_externtype.intros wf_tabletype.intros)
      have lsub: "Limits_sub (mk_limits (mk_uN n') (map_option mk_uN m_opt))
                             (mk_limits (mk_uN v_n) (map_option mk_uN m_opt))"
        using Limits_sub_grow[OF mk_Extend_tableinst(3) wfl] .
      have "Externaddr_ok s' (externaddr_TABLE a)
              (TABLE (mk_tabletype (mk_limits (mk_uN n') (map_option mk_uN m_opt)) rt))"
        using Externaddr_ok.Externaddr_ok__table[OF alen HOL.refl mk_Extend_store(20)]
          mk_Extend_tableinst(2) wfe(2) by fastforce
      then show ?thesis
        using Externaddr_ok.Externaddr_ok__sub[OF _ _ mk_Extend_store(20) wfe(1) wfe(2)]
          Externtype_sub__table[OF mk_Tabletype_sub[OF lsub] wfe(2,1)] wfe wfl mk_Extend_tableinst(1)
        by (auto intro: wf_tabletype.intros)
    qed
  qed
next
  case (Externaddr_ok__sub s v_externaddr xt' xt)
  then show ?case
    using Externaddr_ok.Externaddr_ok__sub store_extension_wf by blast
qed

lemma store_extension_Moduleinst_ok:
  assumes "Moduleinst_ok s i ts"
          "Extend_store s s'"
shows     "Moduleinst_ok s' i ts"
  using assms(1)
proof cases
  case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst funcaddr_lst functype_F_lst
      memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst dataaddr_lst datatype_lst
      elemaddr_lst elemtype_lst)
  note mi = this
  from assms(2) show ?thesis
  proof cases
    case mk_Extend_store
    note es = this
    have ext: "\<And>xa xt. Externaddr_ok s xa xt \<Longrightarrow> Externaddr_ok s' xa xt"
      using store_extension_externaddrok assms(2) by blast
    have "\<And>v. Exportinst_ok s v \<Longrightarrow> Exportinst_ok s' v"
    proof -
      fix v
      assume "Exportinst_ok s v"
      then show "Exportinst_ok s' v"
        using ext es(20) by (cases rule: Exportinst_ok.cases) (auto intro: Exportinst_ok.intros)
    qed
    then have "list_all (\<lambda>v. Exportinst_ok s' v) exportinst_lst"
      using mi(12) list.pred_mono_strong by blast
    moreover have "list_all (\<lambda>v. v < length (store_DATAS s')) dataaddr_lst"
      using mi(14) es(14) unfolding holds_upto_def by (auto simp: list.pred_set)
    moreover have "list_all2 (\<lambda>v t. Datainst_ok s' (store_DATAS s' ! v) t) dataaddr_lst datatype_lst"
    proof -
      have "\<And>v t. v < length (store_DATAS s) \<Longrightarrow> Datainst_ok s (store_DATAS s ! v) t \<Longrightarrow>
              Datainst_ok s' (store_DATAS s' ! v) t"
      proof -
        fix v t
        assume a: "v < length (store_DATAS s)" "Datainst_ok s (store_DATAS s ! v) t"
        then have "Extend_datainst (store_DATAS s ! v) (store_DATAS s' ! v)"
          using es(15) unfolding holds_upto_def by blast
        then show "Datainst_ok s' (store_DATAS s' ! v) t"
          using a(2) es(20)
          by (auto elim!: Extend_datainst.cases Datainst_ok.cases intro!: Datainst_ok.intros)
      qed
      then show ?thesis
        using mi(14,15)
        by (auto simp: list_all2_conv_all_nth list_all_length)
    qed
    moreover have "list_all (\<lambda>v. v < length (store_ELEMS s')) elemaddr_lst"
      using mi(17) es(17) unfolding holds_upto_def by (auto simp: list.pred_set)
    moreover have "list_all2 (\<lambda>v t. Eleminst_ok s' (store_ELEMS s' ! v) t) elemaddr_lst elemtype_lst"
    proof -
      have "\<And>v t. v < length (store_ELEMS s) \<Longrightarrow> Eleminst_ok s (store_ELEMS s ! v) t \<Longrightarrow>
              Eleminst_ok s' (store_ELEMS s' ! v) t"
      proof -
        fix v t
        assume a: "v < length (store_ELEMS s)" "Eleminst_ok s (store_ELEMS s ! v) t"
        then have "Extend_eleminst (store_ELEMS s ! v) (store_ELEMS s' ! v)"
          using es(18) unfolding holds_upto_def by blast
        then show "Eleminst_ok s' (store_ELEMS s' ! v) t"
          using a(2) es(20) store_extension_refok[OF _ assms(2)]
          by (auto elim!: Extend_eleminst.cases Eleminst_ok.cases intro!: Eleminst_ok.intros
              simp: list.pred_set)
      qed
      then show ?thesis
        using mi(17,18)
        by (auto simp: list_all2_conv_all_nth list_all_length)
    qed
    moreover have "list_all2 (\<lambda>a t. Externaddr_ok s' (externaddr_GLOBAL a) (GLOBAL t)) globaladdr_lst globaltype_lst"
      by (rule list_all2_mono[OF mi(5)]) (rule ext)
    moreover have "list_all2 (\<lambda>a t. Externaddr_ok s' (externaddr_FUNC a) (FUNC t)) funcaddr_lst functype_F_lst"
      by (rule list_all2_mono[OF mi(7)]) (rule ext)
    moreover have "list_all2 (\<lambda>a t. Externaddr_ok s' (externaddr_MEM a) (MEM t)) memaddr_lst memtype_lst"
      by (rule list_all2_mono[OF mi(9)]) (rule ext)
    moreover have "list_all2 (\<lambda>a t. Externaddr_ok s' (externaddr_TABLE a) (TABLE t)) tableaddr_lst tabletype_lst"
      by (rule list_all2_mono[OF mi(11)]) (rule ext)
    ultimately show ?thesis
      unfolding mi(1,2)
      using mi(3,4,6,8,10,13,16,19,20,21,23-28) es(20)
      by (intro Moduleinst_ok.intros) simp_all
  qed
qed

lemma store_extension_Frame_ok:
  assumes "Frame_ok s f C"
          "Extend_store s s'"
  shows   "Frame_ok s' f C"
  using assms
proof (induction rule: Frame_ok.induct)
  case (mk_Frame_ok s v_moduleinst C t_lst val_lst)
  have wfs': "wf_store s'" using store_extension_wf[OF mk_Frame_ok.prems] .
  have "list_all2 (\<lambda>t v. Val_ok s' v t) t_lst val_lst"
    by (rule list_all2_mono[OF mk_Frame_ok(3)])
       (rule store_extension_valok[OF _ wfs' mk_Frame_ok.prems])
  moreover have "Moduleinst_ok s' v_moduleinst C"
    using store_extension_Moduleinst_ok[OF mk_Frame_ok(1) mk_Frame_ok.prems] .
  ultimately show ?case
    using mk_Frame_ok(2,5,6,7) wfs' by (intro Frame_ok.intros) simp_all
qed

lemma store_extension_typing_all:
  shows "Instr_ok2 s C e tf \<Longrightarrow> Extend_store s s' \<Longrightarrow> Instr_ok2 s' C e tf"
    and "Instrs_ok2 s C es tf \<Longrightarrow> Extend_store s s' \<Longrightarrow> Instrs_ok2 s' C es tf"
    and "Expr_ok2 s C es rt \<Longrightarrow> Extend_store s s' \<Longrightarrow> Expr_ok2 s' C es rt"
proof (induction rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts)
  case plain
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.plain)
next
  case label
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.label)
next
  case Instr_ok2__frame
  then show ?case
    using store_extension_wf store_extension_Frame_ok
    by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__frame)
next
  case Instr_ok2__call_addr
  then show ?case
    using store_extension_wf store_extension_externaddrok
    by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__call_addr)
next
  case Instr_ok2__ref
  then show ?case
    using store_extension_wf store_extension_refok
    by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__ref)
next
  case Instr_ok2__trap
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__trap)
next
  case Instrs_ok2__empty
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__empty)
next
  case Instrs_ok2__instr
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__instr)
next
  case Instrs_ok2__seq
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__seq)
next
  case Instrs_ok2__sub
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__sub)
next
  case Instrs_ok2__frame
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__frame)
next
  case mk_Expr_ok2
  then show ?case
    using store_extension_wf by (blast intro: Instr_ok2_Instrs_ok2_Expr_ok2.mk_Expr_ok2)
qed

lemma store_extension_typing:
  assumes "Instrs_ok2 s C es tf"
          "Extend_store s s'"
  shows   "Instrs_ok2 s' C es tf"
  using store_extension_typing_all(2)[OF assms] .

lemma store_extension_Funcinst_ok:
assumes "Funcinst_ok s i ts"
        "Extend_store s s'"
shows   "Funcinst_ok s' i ts"
proof -
  have s'_wf: "wf_store s'" using assms(2) store_extension_wf by simp
  show ?thesis using assms(1)
  proof (cases rule: Funcinst_ok.cases)
    case (mk_Funcinst_ok v_moduleinst C v_func)
    have "Moduleinst_ok s' v_moduleinst C"
      using mk_Funcinst_ok assms(2) store_extension_Moduleinst_ok by blast
    then show ?thesis using mk_Funcinst_ok s'_wf
      by (auto intro: Funcinst_ok.intros)
  qed
qed

lemma store_extension_Globalinst_ok:
  assumes "Globalinst_ok s i ts"
          "Extend_store s s'"
  shows   "Globalinst_ok s' i ts"
proof -
  have s'_wf: "wf_store s'" using assms(2) store_extension_wf by simp
  from assms(1) show ?thesis
  proof (cases rule: Globalinst_ok.cases)
    case (mk_Globalinst_ok v_mut t v_val)
    have "Val_ok s' v_val t"
      using s'_wf assms(2) store_extension_valok local.mk_Globalinst_ok(4)
      by blast
    then show ?thesis
      using mk_Globalinst_ok s'_wf
      by (auto intro: Globalinst_ok.intros)
  qed
qed

lemma store_extension_Tableinst_ok:
assumes "Tableinst_ok s i ts"
        "Extend_store s s'"
shows   "Tableinst_ok s' i ts"
proof -
  have s'_wf: "wf_store s'" using assms(2) store_extension_wf by simp
  show ?thesis using assms(1)
  proof (cases rule: Tableinst_ok.cases)
    case (mk_Tableinst_ok v_n m_opt rt ref_lst)
    have "list_all (\<lambda>v_ref. Ref_ok s' v_ref rt) ref_lst" using assms(2) store_extension_refok mk_Tableinst_ok
      by (simp add: list.pred_mono_strong)
    then show ?thesis using mk_Tableinst_ok s'_wf
      by (auto intro: Tableinst_ok.intros)
  qed
qed

lemma store_extension_Meminst_ok:
assumes "Meminst_ok s i ts"
        "Extend_store s s'"
shows   "Meminst_ok s' i ts"
proof -
  have s'_wf: "wf_store s'" using assms(2) store_extension_wf by simp
  show ?thesis using assms(1) Meminst_ok.simps s'_wf
    by auto
qed

lemma store_extension_Eleminst_ok:
assumes "Eleminst_ok s i ts"
        "Extend_store s s'"
shows   "Eleminst_ok s' i ts"
proof -
  have s'_wf: "wf_store s'" using assms(2) store_extension_wf by simp
  show ?thesis using assms(1)
  proof (cases rule: Eleminst_ok.cases)
    case (mk_Eleminst_ok ref_lst)
    have "list_all (\<lambda>v_ref. Ref_ok s' v_ref ts) ref_lst" using assms(2) store_extension_refok mk_Eleminst_ok
      by (simp add: list.pred_mono_strong)
    then show ?thesis using mk_Eleminst_ok s'_wf
      by (auto intro: Eleminst_ok.intros)
  qed
qed

lemma store_extension_Datainst_ok:
assumes "Datainst_ok s i ts"
        "Extend_store s s'"
shows   "Datainst_ok s' i ts"
proof -
  have s'_wf: "wf_store s'" using assms(2) store_extension_wf by simp
  show ?thesis using assms(1) Datainst_ok.simps s'_wf
    by auto
qed

end
