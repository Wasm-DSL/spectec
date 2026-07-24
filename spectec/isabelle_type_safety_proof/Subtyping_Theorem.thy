section \<open>Subtyping Theorem\<close>

theory Subtyping_Theorem imports Subtyping Typing_Simplified Subtyping_Properties begin



lemma Instrs_ok_frame_sub :
  assumes "Resulttype_sub (mk_list ts) (mk_list ts')" 
          "Instrs_ok C e (mk_functype (mk_list t1) (mk_list t2))" 
        shows "Instrs_ok C e (mk_functype (mk_list (ts @ t1)) (mk_list (ts' @ t2)))"
  using assms
proof -
  assume "Resulttype_sub (mk_list ts) (mk_list ts')" 
         "Instrs_ok C e (mk_functype (mk_list t1) (mk_list t2))"
  then have "Instrs_ok C e (mk_functype (mk_list (ts @ t1)) (mk_list (ts @ t2)))"
    using Instrs_ok__frame Instrs_ok_wf by simp
  then show ?thesis
    by (meson sub Resulttype_sub_append Resulttype_sub_refl assms(1) Instrs_ok_wf)
qed


lemma Instrs_ok_subtyping :
  assumes "mk_instrtype t1s t2s <ti: mk_instrtype t1s' t2s'"
          "Instrs_ok C e (mk_functype t1s t2s)"
        shows "Instrs_ok C e (mk_functype t1s' t2s')"
  using assms
proof (cases)
  case (mk_Instrtype_sub t1l' t1fst t1lst t2l' t2fst t2lst t1l t2l)
  have "wf_context C" using assms(2) Instrs_ok_wf by auto
  then have "Instrs_ok C e (mk_functype (mk_list t1lst) (mk_list t2lst))"
    using Instrs_ok__frame assms(2) 
    using sub local.mk_Instrtype_sub(1,2,8,9)
    using Instrs_ok_wf by blast  
  then show ?thesis 
    using Instrs_ok_frame_sub[OF mk_Instrtype_sub(7)] 
    using local.mk_Instrtype_sub(3,4,5,6) by presburger
  qed



lemma Instrs_ok2_frame_sub :
  assumes "Resulttype_sub (mk_list ts) (mk_list ts')" 
          "Instrs_ok2 s C e (mk_functype (mk_list t1) (mk_list t2))" 
        shows "Instrs_ok2 s C e (mk_functype (mk_list (ts @ t1)) (mk_list (ts' @ t2)))"
  using assms
proof -
  assume "Resulttype_sub (mk_list ts) (mk_list ts')" 
         "Instrs_ok2 s C e (mk_functype (mk_list t1) (mk_list t2))"
  then have "Instrs_ok2 s C e (mk_functype (mk_list (ts @ t1)) (mk_list (ts @ t2)))"
    using Instrs_ok2__frame Instrs_ok2_wf Instrs_ok2_wf_instr by simp
  then show ?thesis
    by (meson Instrs_ok2__sub Resulttype_sub_append Resulttype_sub_refl assms(1) Instrs_ok2_wf(1,2)
        Instrs_ok2_wf_instr)
qed


lemma Instrs_ok2_subtyping :
  assumes "mk_instrtype t1s t2s <ti: mk_instrtype t1s' t2s'"
          "Instrs_ok2 s C e (mk_functype t1s t2s)"
        shows "Instrs_ok2 s C e (mk_functype t1s' t2s')"
  using assms
proof (cases)
  case (mk_Instrtype_sub t1l' t1fst t1lst t2l' t2fst t2lst t1l t2l)
  have "wf_store s" "wf_context C" using assms(2) Instrs_ok2_wf by auto
  then have "Instrs_ok2 s C e (mk_functype (mk_list t1lst) (mk_list t2lst))"
    using Instrs_ok2__frame assms(2) 
    using Instrs_ok2__sub local.mk_Instrtype_sub(1,2,8,9)
    using Instrs_ok2_wf_instr by blast  
  then show ?thesis 
    using Instrs_ok2_frame_sub[OF mk_Instrtype_sub(7)] 
    using local.mk_Instrtype_sub(3,4,5,6) by presburger
  qed

end