(* Agreement of the two type systems: on well-formed SpecTec instruction sequences and
   contexts, SpecTec's typing and WasmCert-Isabelle's typing of the translation
   coincide.  Isabelle counterpart of [Instrs_ok_iff] in ../wasmcert-rocq/backtyping.v.

   Side conditions:
   - [ext_ok], [rt_ok]: the sign-extension widths are Wasm's and [select]
     annotations are singletons (SpecTec types neither, but its well-formedness
     allows them);
   - [vzero_ok] of the translation: zero-loads are aligned as Wasm requires
     (WasmCert-Isabelle accepts larger alignments);
   - the vector-operator hypotheses of [vec_iff]. *)
theory Typing_Iff
  imports Backtyping Completeness
begin

locale vec_iff = vec_back + vec_complete

theorem (in vec_iff) Instrs_ok_iff:
  assumes "wf_context C" "list_all wf_instr ins" "list_all ext_ok ins" "list_all rt_ok ins"
          "list_all vzero_ok (tr_instrs ins)"
  shows "Instrs_ok C ins ft \<longleftrightarrow> tr_context C \<turnstile> tr_instrs ins : tr_functype ft"
proof
  assume "Instrs_ok C ins ft"
  then show "tr_context C \<turnstile> tr_instrs ins : tr_functype ft"
    using Instr_ok_tr(2) assms(3) by blast
next
  assume "tr_context C \<turnstile> tr_instrs ins : tr_functype ft"
  from b_e_typing_back[OF this of_tr_context[OF assms(1)] of_tr_instrs[OF assms(2,4)] assms(5)]
  show "Instrs_ok C ins ft" by simp
qed

(* WasmCert-typed code with a SpecTec counterpart is SpecTec-typed, in the context
   and at the type it translates to. *)
corollary (in vec_back) be_typing_of:
  "C \<turnstile> es : tf \<Longrightarrow> of_context C = Some C' \<Longrightarrow> of_instrs es = Some ins \<Longrightarrow> list_all vzero_ok es \<Longrightarrow>
   Instrs_ok C' ins (of_functype tf)"
  by (rule b_e_typing_back)

end
