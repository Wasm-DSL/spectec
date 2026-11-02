theory Wf_preservation
(* Imported Lemma Formulation, Proofs Added Manually *)
	imports isabelle_reference_output_wasm2
begin

(* Well-formedness lemmas whose statements in the regenerated theory differ from the ones
   proved here. The helpers and the lemmas whose statements are unchanged now live in
   Generated_Wf_Lemmas. *)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/1-syntax.spectec:281.6-281.11 *)
lemma zero_is_wf :
	"(ret_val = (fun_zero v_numtype)) \<Longrightarrow>
	 (wf_num_underscore v_numtype ret_val)"
  by (cases v_numtype)
     (simp_all add: fun_zero.psimps fun_zero.domintros wf_num_underscore.simps wf_uN_iff
       wf_fN_fzero sizenn.psimps sizenn.domintros wf_proj_simps)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 *)
lemma unop__is_wf :
	"(wf_unop_underscore v_numtype v_unop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 ((fun_unop_underscore v_numtype v_unop_underscore v_num_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the ((fun_unop_underscore v_numtype v_unop_underscore v_num_underscore)))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: num_underscore). (wf_num_underscore v_numtype ret_val)) ret_val_lst"
  by (cases v_numtype)
     (auto simp: fun_unop_underscore.psimps fun_unop_underscore.domintros
       intro: unop_I32_wf unop_I64_wf unop_F32_wf unop_F64_wf)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 *)
lemma testop__is_wf :
	"(wf_testop_underscore v_numtype v_testop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 ((fun_testop_underscore v_numtype v_testop_underscore v_num_underscore) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((fun_testop_underscore v_numtype v_testop_underscore v_num_underscore)))) \<Longrightarrow>
	 (wf_num_underscore I32 ret_val)"
  by (metis option.collapse testop_wf_I32)

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.6-364.14 *)
lemma vvunop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (ret_val = (vvunop_underscore v_vectype v_vvunop v_vec_underscore)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
  by (cases v_vectype; cases v_vvunop)
     (auto simp: vvunop_underscore.psimps vvunop_underscore.domintros
       wf_proj_simps
       intro: inot__is_wf[OF _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.6-366.15 *)
lemma vvbinop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__0) \<Longrightarrow>
	 (ret_val = (vvbinop_underscore v_vectype v_vvbinop v_vec_underscore vec__0)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
  by (cases v_vectype; cases v_vvbinop)
     (auto simp: vvbinop_underscore.psimps vvbinop_underscore.domintros
       wf_proj_simps
       intro: iand__is_wf[OF _ _ HOL.refl] iandnot__is_wf[OF _ _ HOL.refl]
         ior__is_wf[OF _ _ HOL.refl] ixor__is_wf[OF _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/3-numerics.spectec:368.6-368.16 *)
lemma vvternop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__0) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__1) \<Longrightarrow>
	 (ret_val = (vvternop_underscore v_vectype v_vvternop v_vec_underscore vec__0 vec__1)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
  by (cases v_vectype; cases v_vvternop)
     (auto simp: vvternop_underscore.psimps vvternop_underscore.domintros
       wf_proj_simps
       intro: ibitselect__is_wf[OF _ _ _ HOL.refl])

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.6-78.10 *)
lemma mem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 (ret_val = (fun_mem v_state v_memidx)) \<Longrightarrow>
	 (wf_meminst ret_val)"
sorry

(* Well-Formedness Lemma Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 *)
lemma Step_read_is_wf :
	"(wf_config (mk_config (mk_state s f) es)) \<Longrightarrow>
   Store_ok s \<Longrightarrow>
	 (Step_read (mk_config (mk_state s f) es) var_1) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: admininstr). (wf_admininstr var_1)) var_1"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 *)
lemma Step_is_wf :
	"(wf_config (mk_config (mk_state s f) es)) \<Longrightarrow>
    Store_ok s \<Longrightarrow>
	 (Step (mk_config (mk_state s f) es) var_1) \<Longrightarrow>
	 (wf_config var_1)"
sorry

end
