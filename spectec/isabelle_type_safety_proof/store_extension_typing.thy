
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

(* This lemma will probably be useful later: *)
(* lemma store_extension_typing:
  assumes "Instrs_ok2 s C es tf"
          "Extend_store s s'"
shows     "Instrs_ok2 s' C es tf"
  sorry *)


(* A few attempts at proving this lemma, MEM is the annoying case *)
(* For now I was able to get away with using just the FUNC case, see stricter lemma below *)
(*
lemma store_extension_externaddrok:
  assumes "Externaddr_ok s r rt"
         (* "wf_store s'" *) 
          "Extend_store s s'"
        shows "Externaddr_ok s' r rt"
  using assms
proof cases
  case (Externaddr_ok__global a v_globalinst)
  show ?thesis using assms(2)
  proof cases
    case mk_Extend_store
    then have ext: "Extend_globalinst (store_GLOBALS s ! a) (store_GLOBALS s' ! a)" by (meson holds_upto_def local.Externaddr_ok__global(3))
    have alen: "a < length (store_GLOBALS s')" using mk_Extend_store by (meson holds_upto_def local.Externaddr_ok__global(3))
    show ?thesis using ext
    proof cases
      case (mk_Extend_globalinst v_mut v_val val' t)
      then show ?thesis using 
          alen mk_Extend_store(20) Externaddr_ok.Externaddr_ok__global 
          local.Externaddr_ok__global(1,2,4,6) by fastforce
    qed
  qed
next
  case (Externaddr_ok__mem a v_meminst)
  show ?thesis using assms(2)
  proof cases
    case mk_Extend_store
    then have ext: "Extend_meminst (store_MEMS s ! a) (store_MEMS s' ! a)" by (meson holds_upto_def local.Externaddr_ok__mem(3))
    have alen: "a < length (store_MEMS s')" using mk_Extend_store by (meson holds_upto_def local.Externaddr_ok__mem(3))
    show ?thesis using ext
    proof cases
      case (mk_Extend_meminst v_n n' b_lst b'_lst m_opt)
      then show ?thesis using 
          alen mk_Extend_store(20) Externaddr_ok.Externaddr_ok__mem local.Externaddr_ok__mem(1,2,4,6)
        
        
    qed
  qed
    
next
  case (Externaddr_ok__table a v_tableinst)
  then show ?thesis sorry
next
  case (Externaddr_ok__func a v_funcinst)
  then show ?thesis sorry
next
  case (Externaddr_ok__sub xt')
  then show ?thesis sorry
qed
 *)
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

end