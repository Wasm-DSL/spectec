(* Typing preservation: SpecTec instruction typing ([Instr_ok], [Instrs_ok]) implies
   WasmCert-Isabelle's basic-instruction typing ([b_e_typing]) of the translation.
   Isabelle counterpart of ../wasmcert-rocq/typing.v.

   Two side conditions have no Rocq counterpart:
   - [ext_ok]: SpecTec's well-formedness puts no bound on the width [n] of the
     sign-extension operator [UNOP Inn (EXTEND n)], so SpecTec types e.g.
     [i32.extend32_s], which is not a Wasm instruction.  WasmCert-Isabelle only
     types [Extend_s tp] when the packed width is below the operand width.  The
     theorem is stated for code whose extension operators are Wasm's
     (8 or 16 bits, or 32 bits at i64);
   - [binop_vec_wf]: WasmCert-Isabelle types a binary vector operator only if the
     uninterpreted predicate [binop_vec_wf] holds of it.  The operators the
     translation picks ([vec_binop]) are assumed to satisfy it exactly when SpecTec
     can type the instruction: always, except for shuffles, whose lane indices
     SpecTec's typing (not its well-formedness) bounds by 32 ([vshuffle_ok]).
     The converse direction is needed for back-typing ([Backtyping]). *)
theory Typing
  imports Spec_Aux
begin

section \<open>Side conditions\<close>

definition ext_width_ok :: "numtype \<Rightarrow> nat \<Rightarrow> bool" where
  "ext_width_ok nt n = (n = 8 \<or> n = 16 \<or> (n = 32 \<and> nt = I64))"

fun unop_ext_ok :: "numtype \<Rightarrow> unop_underscore \<Rightarrow> bool" where
  "unop_ext_ok nt (mk_unop__0 _ (EXTEND n)) = ext_width_ok nt n"
| "unop_ext_ok nt _ = True"

primrec ext_ok :: "instr \<Rightarrow> bool" and ext_ok7 :: "instr_st7 \<Rightarrow> bool" where
  "ext_ok (instr_sc0 x) = True"
| "ext_ok (instr_sc1 x) = (case x of UNOP nt op \<Rightarrow> unop_ext_ok nt op | _ \<Rightarrow> True)"
| "ext_ok (instr_sc2 x) = True"
| "ext_ok (instr_sc3 x) = True"
| "ext_ok (instr_sc4 x) = True"
| "ext_ok (instr_sc5 x) = True"
| "ext_ok (instr_sc6 x) = True"
| "ext_ok (instr_sc7 x) = ext_ok7 x"
| "ext_ok7 (IFELSE bt is1 is2) = (list_all ext_ok is1 \<and> list_all ext_ok is2)"
| "ext_ok7 (LOOP bt ins) = list_all ext_ok ins"
| "ext_ok7 (BLOCK bt ins) = list_all ext_ok ins"
| "ext_ok7 (DATA_DROP x) = True"

fun vshuffle_ok :: "instr \<Rightarrow> bool" where
  "vshuffle_ok (instr_sc3 (VSHUFFLE sh ls)) = list_all (\<lambda>l. un l < 32) ls"
| "vshuffle_ok _ = True"

locale vec_binop_ok =
  assumes binop_vec_wf_tr: "binop_vec_wf (vec_binop i) = vshuffle_ok i"

section \<open>Inversion of well-formedness\<close>

inductive_cases wf_LOAD: "wf_instr (instr_sc5 (LOAD nt lo ao))"
inductive_cases wf_STORE: "wf_instr (instr_sc5 (STORE nt so ao))"
inductive_cases wf_VLOAD: "wf_instr (instr_sc6 (VLOAD vt lo ao))"
inductive_cases wf_VLOAD_LANE: "wf_instr (instr_sc6 (VLOAD_LANE vt s ao j))"
inductive_cases wf_VSTORE_LANE: "wf_instr (instr_sc6 (VSTORE_LANE vt s ao j))"
inductive_cases wf_VEXTRACT_LANE: "wf_instr (instr_sc3 (VEXTRACT_LANE sh s j))"
inductive_cases wf_VREPLACE_LANE: "wf_instr (instr_sc3 (VREPLACE_LANE sh j))"
inductive_cases wf_VSPLAT: "wf_instr (instr_sc3 (VSPLAT sh))"
inductive_cases wf_VSHUFFLE: "wf_instr (instr_sc3 (VSHUFFLE sh ls))"
inductive_cases wf_CONST: "wf_instr (instr_sc1 (res_CONST nt c))"
inductive_cases wf_UNOP: "wf_instr (instr_sc1 (UNOP nt op))"
inductive_cases wf_BINOP: "wf_instr (instr_sc1 (BINOP nt op))"
inductive_cases wf_TESTOP: "wf_instr (instr_sc1 (TESTOP nt op))"
inductive_cases wf_RELOP: "wf_instr (instr_sc1 (RELOP nt op))"
inductive_cases wf_CVTOP: "wf_instr (instr_sc1 (CVTOP nt1 nt2 op))"

inductive_cases wf_shapeE: "wf_shape sh"
inductive_cases wf_dimE: "wf_dim d"
inductive_cases wf_szE: "wf_sz s"
inductive_cases fun_lsizeE: "fun_lsize lt n"
inductive_cases fun_sizennE: "fun_sizenn nt n"
inductive_cases wf_loadopE: "wf_loadop_underscore nt lo"
inductive_cases wf_loadop_InnE: "wf_loadop_Inn t lo"
inductive_cases wf_vloadopE: "wf_vloadop_underscore vt lo"

section \<open>Operators\<close>

lemma typeof_tr_num0: "typeof_num (tr_num (mk_num__0 t x)) = tr_numtype (numtype_Inn t)"
  by (cases t) (simp_all add: typeof_num_def)

lemma typeof_tr_num1: "typeof_num (tr_num (mk_num__1 t x)) = tr_numtype (numtype_Fnn t)"
  by (cases t) (simp_all add: typeof_num_def)

lemma wf_num_typeof: "wf_num_underscore nt c \<Longrightarrow> typeof_num (tr_num c) = tr_numtype nt"
  by (erule wf_num_underscore.cases) (simp_all add: typeof_tr_num0 typeof_tr_num1)

lemma const_typing:
  "wf_num_underscore nt c \<Longrightarrow> \<C> \<turnstile> [EConstNum (tr_num c)] : ([] _> [T_num (tr_numtype nt)])"
  by (metis b_e_typing.const_num wf_num_typeof)

lemma wf_unop_agree:
  "wf_unop_underscore nt op \<Longrightarrow> unop_ext_ok nt op \<Longrightarrow> unop_t_num_agree (tr_unop op) (tr_numtype nt)"
  apply (erule wf_unop_underscore.cases)
   apply (rename_tac t x, case_tac t; case_tac x;
          auto simp: unop_t_num_agree_def is_int_t_num_def ext_width_ok_def tp_of_bits_def
                     t_num_length_def tp_num_length_def)
  apply (rename_tac t x, case_tac t; case_tac x; simp add: unop_t_num_agree_def is_float_t_num_def)
  done

lemma wf_binop_agree: "wf_binop_underscore nt op \<Longrightarrow> binop_t_num_agree (tr_binop op) (tr_numtype nt)"
  by (erule wf_binop_underscore.cases; rename_tac t x; case_tac t; case_tac x;
      simp add: binop_t_num_agree_def is_int_t_num_def is_float_t_num_def)

lemma wf_relop_agree: "wf_relop_underscore nt op \<Longrightarrow> relop_t_num_agree (tr_relop op) (tr_numtype nt)"
  by (erule wf_relop_underscore.cases; rename_tac t x; case_tac t; case_tac x;
      simp add: relop_t_num_agree_def is_int_t_num_def is_float_t_num_def)

lemma wf_testop_int: "wf_testop_underscore nt op \<Longrightarrow> is_int_t_num (tr_numtype nt)"
  by (erule wf_testop_underscore.cases; rename_tac t x; case_tac t; simp add: is_int_t_num_def)

inductive_cases fun_sizenn1E: "fun_sizenn1 nt n"
inductive_cases fun_sizenn2E: "fun_sizenn2 nt n"
inductive_cases wf_cvtopE: "wf_cvtop__underscore nt1 nt2 op"
inductive_cases wf_cvtop00E: "wf_cvtop__Inn_1_Inn_2 t1 t2 op"
inductive_cases wf_cvtop01E: "wf_cvtop__Inn_1_Fnn_2 t1 t2 op"
inductive_cases wf_cvtop10E: "wf_cvtop__Fnn_1_Inn_2 t1 t2 op"
inductive_cases wf_cvtop11E: "wf_cvtop__Fnn_1_Fnn_2 t1 t2 op"

(* [CVTOP nt1 nt2 op] converts from [nt2] to [nt1]; its well-formedness is
   [wf_cvtop__underscore nt2 nt1 op]. *)
lemma wf_cvtop_typing:
  assumes "wf_cvtop__underscore nt2 nt1 op"
  shows "\<C> \<turnstile> [Cvtop (tr_numtype nt1) (fst (tr_cvtop op)) (tr_numtype nt2) (snd (tr_cvtop op))]
             : ([T_num (tr_numtype nt2)] _> [T_num (tr_numtype nt1)])"
  using assms
  by (elim wf_cvtopE wf_cvtop00E wf_cvtop01E wf_cvtop10E wf_cvtop11E fun_sizenn1E fun_sizenn2E)
     (auto intro!: b_e_typing.convert b_e_typing.reinterpret
           simp: is_int_t_num_def is_float_t_num_def t_num_length_def numtype_Inn_case
                 numtype_Fnn_case
           split: Inn.splits Fnn.splits)

lemma shape_lane_t: "vec_lane_t (tr_shape sh) = tr_numtype (shunpack sh)"
  by (cases sh, rename_tac lt d, case_tac lt; case_tac d; simp add: vec_lane_t_def)

lemma wf_shape_num:
  "wf_shape sh \<Longrightarrow> vec_num (tr_shape sh) = proj_dim_0 (fun_dim sh)"
  by (elim wf_shapeE fun_lsizeE wf_dimE, rename_tac d, case_tac d)
     (auto simp: vec_num_def vec_i_num_def vec_f_num_def)

(* Lane widths that SpecTec allows ([wf_sz]). *)
lemma wf_sz_cases: "wf_sz (mk_sz n) \<Longrightarrow> n = 8 \<or> n = 16 \<or> n = 32 \<or> n = 64"
  by (erule wf_szE) auto

lemma svi_of_bits_facts:
  "n = 8 \<or> n = 16 \<or> n = 32 \<or> n = 64 \<Longrightarrow>
   vec_i_length (svi_of_bits n) = n div 8 \<and> vec_i_num (svi_of_bits n) = 128 div n"
  by (auto simp: svi_of_bits_def vec_i_length_def vec_i_num_def)

lemma size_numtype_div8: "the (isabelle_reference_output_wasm2.size (valtype_numtype nt)) div 8 = t_num_length (tr_numtype nt)"
  by (cases nt) (simp_all add: t_num_length_def)

(* Only packed lanes (i8, i16) carry a signedness in SpecTec; WasmCert accepts a
   signed extraction only for lanes of at most 2 bytes. *)
lemma extract_sx_ok:
  "(fun_lanetype sh = lanetype_I32 \<or> fun_lanetype sh = lanetype_I64 \<or>
    fun_lanetype sh = lanetype_F32 \<or> fun_lanetype sh = lanetype_F64) = (sx_opt = None) \<Longrightarrow>
   tr_lane_sx sx_opt = Wasm_Ast.U \<or> vec_length (tr_shape sh) \<le> 2"
  by (cases sh, rename_tac lt d, case_tac lt; case_tac d; cases sx_opt;
      simp add: vec_length_def vec_i_length_def vec_f_length_def)

lemma Suc0_le_length[simp]: "(Suc 0 \<le> length xs) = (xs \<noteq> [])"
  by (cases xs) auto

lemma memory_tr_nonempty: "0 < length (context_MEMS C) \<Longrightarrow> 1 \<le> length (memory (tr_context C))"
  by (simp add: tr_context_def Suc_le_eq)

lemma instr_subtyping_simple:
  "t1' <ts: t1 \<Longrightarrow> t2 <ts: t2' \<Longrightarrow> (t1 _> t2) <ti: (t1' _> t2')"
  unfolding instr_subtyping_def
  by (rule exI[of _ "[]"], rule exI[of _ "[]"], rule exI[of _ t1'], rule exI[of _ t2'])
     (simp add: Wasm_Subtyping.t_list_subtyping_def)

section \<open>Main theorem\<close>

context vec_binop_ok
begin

theorem Instr_ok_tr:
  shows "Instr_ok C i ft \<Longrightarrow> ext_ok i \<Longrightarrow>
           tr_context C \<turnstile> [tr_instr i] : tr_functype ft"
    and "Instrs_ok C ins ft \<Longrightarrow> list_all ext_ok ins \<Longrightarrow>
           tr_context C \<turnstile> tr_instrs ins : tr_functype ft"
proof (induction rule: Instr_ok_Instrs_ok.inducts)
  case nop then show ?case by (simp add: b_e_typing.nop)
next
  case unreachable then show ?case by (simp add: b_e_typing.unreachable)
next
  case drop then show ?case by (simp add: b_e_typing.drop)
next
  case select_expl then show ?case by (simp add: b_e_typing.select)
next
  case (select_impl t t')
  then show ?case
    by (auto elim!: Valtype_sub.cases intro!: b_e_typing.select
             simp: is_num_type_def is_vec_type_def split: numtype.splits vectype.splits)
next
  case block then show ?case
    by (auto intro!: b_e_typing.block simp: Blocktype_ok_tr tr_instrs_def)
next
  case loop then show ?case
    by (auto intro!: b_e_typing.loop simp: Blocktype_ok_tr tr_instrs_def)
next
  case res_if then show ?case
    by (auto intro!: b_e_typing.if_wasm simp: Blocktype_ok_tr tr_instrs_def)
next
  case br then show ?case
    by (auto intro!: b_e_typing.br simp: tr_context_def tr_resulttype_proj)
next
  case br_if then show ?case
    by (auto intro!: b_e_typing.br_if simp: tr_context_def tr_resulttype_proj)
next
  case br_table then show ?case
    by (auto intro!: b_e_typing.br_table simp: tr_context_def list_all_iff Resulttype_sub_tr)
next
  case call then show ?case
    by (auto intro!: b_e_typing.call simp: tr_context_def)
next
  case call_indirect then show ?case
    by (auto intro!: b_e_typing.call_indirect simp: tr_context_def)
next
  case return then show ?case
    by (auto intro!: b_e_typing.return simp: tr_context_def)
next
  case const then show ?case
    by (auto elim!: wf_CONST intro!: const_typing)
next
  case unop then show ?case
    by (auto elim!: wf_UNOP intro!: b_e_typing.unop simp: wf_unop_agree)
next
  case binop then show ?case
    by (auto elim!: wf_BINOP intro!: b_e_typing.binop simp: wf_binop_agree)
next
  case testop then show ?case
    by (auto elim!: wf_TESTOP intro!: b_e_typing.testop simp: wf_testop_int)
next
  case relop then show ?case
    by (auto elim!: wf_RELOP intro!: b_e_typing.relop simp: wf_relop_agree)
next
  case cvtop then show ?case
    by (auto elim!: wf_CVTOP simp: wf_cvtop_typing)
next
  case ref_null then show ?case by (simp add: b_e_typing.ref_null)
next
  case ref_func then show ?case
    by (auto intro!: b_e_typing.ref_func simp: tr_context_def)
next
  case ref_is_null then show ?case by (simp add: b_e_typing.ref_is_null)
next
  case vconst then show ?case
    by (simp add: tr_vec_def b_e_typing.const_vec[of _ "ConstVec128 _", simplified typeof_vec_def, simplified])
next
  case Instr_ok__vvunop then show ?case by (simp add: b_e_typing.unop_vec)
next
  case Instr_ok__vvbinop then show ?case by (simp add: b_e_typing.binop_vec binop_vec_wf_tr)
next
  case Instr_ok__vvternop then show ?case by (simp add: b_e_typing.ternop_vec)
next
  case Instr_ok__vvtestop then show ?case by (simp add: b_e_typing.test_vec)
next
  case vunop then show ?case by (simp add: b_e_typing.unop_vec)
next
  case vbinop then show ?case by (simp add: b_e_typing.binop_vec binop_vec_wf_tr)
next
  case vtestop then show ?case by (simp add: b_e_typing.test_vec)
next
  case vrelop then show ?case by (simp add: b_e_typing.binop_vec binop_vec_wf_tr)
next
  case vshiftop then show ?case by (simp add: b_e_typing.shift_vec)
next
  case vbitmask then show ?case by (simp add: b_e_typing.test_vec)
next
  case vswizzle then show ?case by (simp add: b_e_typing.binop_vec binop_vec_wf_tr)
next
  case vshuffle then show ?case
    by (auto elim!: wf_VSHUFFLE intro!: b_e_typing.binop_vec simp: binop_vec_wf_tr list_all_iff)
next
  case vsplat then show ?case
    by (simp add: shape_lane_t[symmetric] b_e_typing.splat_vec)
next
  case vextract_lane then show ?case
    apply (elim wf_VEXTRACT_LANE)
    apply (simp only: tr_instr.simps tr_st3.simps tr_functype.simps tr_resulttype.simps
                      list.map tr_valtype.simps tr_valtype_numtype shape_lane_t[symmetric])
    apply (rule b_e_typing.extract_vec)
     apply (simp add: wf_shape_num)
    apply (erule extract_sx_ok)
    done
next
  case vreplace_lane then show ?case
    apply (simp add: shape_lane_t[symmetric])
    apply (rule b_e_typing.replace_vec)
    by (auto elim!: wf_VREPLACE_LANE simp: wf_shape_num)
next
  case vextunop then show ?case by (simp add: b_e_typing.unop_vec)
next
  case vextbinop then show ?case by (simp add: b_e_typing.binop_vec binop_vec_wf_tr)
next
  case vnarrow then show ?case by (simp add: b_e_typing.binop_vec binop_vec_wf_tr)
next
  case vcvtop then show ?case by (simp add: b_e_typing.unop_vec)
next
  case local_get then show ?case
    by (auto intro!: b_e_typing.local_get simp: tr_context_def)
next
  case local_set then show ?case
    by (auto intro!: b_e_typing.local_set simp: tr_context_def)
next
  case local_tee then show ?case
    by (auto intro!: b_e_typing.local_tee simp: tr_context_def)
next
  case global_get then show ?case
    by (auto intro!: b_e_typing.global_get simp: tr_context_def)
next
  case global_set then show ?case
    by (auto intro!: b_e_typing.global_set simp: tr_context_def is_mut_def)
next
  case table_get then show ?case
    by (auto intro!: b_e_typing.table_get simp: tr_context_def tab_t_reftype_def)
next
  case table_set then show ?case
    by (auto intro!: b_e_typing.table_set simp: tr_context_def tab_t_reftype_def)
next
  case table_size then show ?case
    by (auto intro!: b_e_typing.table_size simp: tr_context_def)
next
  case table_grow then show ?case
    by (auto intro!: b_e_typing.table_grow simp: tr_context_def tab_t_reftype_def)
next
  case table_fill then show ?case
    by (auto intro!: b_e_typing.table_fill simp: tr_context_def tab_t_reftype_def)
next
  case table_copy then show ?case
    by (auto intro!: b_e_typing.table_copy simp: tr_context_def tab_t_reftype_def)
next
  case table_init then show ?case
    by (auto intro!: b_e_typing.table_init simp: tr_context_def tab_t_reftype_def)
next
  case elem_drop then show ?case
    by (auto intro!: b_e_typing.elem_drop simp: tr_context_def)
next
  case memory_size then show ?case
    by (auto intro!: b_e_typing.memory_size simp: tr_context_def)
next
  case memory_grow then show ?case
    by (auto intro!: b_e_typing.memory_grow simp: tr_context_def)
next
  case memory_fill then show ?case
    by (auto intro!: b_e_typing.memory_fill simp: tr_context_def)
next
  case memory_copy then show ?case
    by (auto intro!: b_e_typing.memory_copy simp: tr_context_def)
next
  case memory_init then show ?case
    by (auto intro!: b_e_typing.memory_init simp: tr_context_def)
next
  case data_drop then show ?case
    by (auto intro!: b_e_typing.data_drop simp: tr_context_def)
next
  case load_val then show ?case
    by (auto intro!: b_e_typing.load
             simp: memory_tr_nonempty load_store_t_bounds_def option_projl_def tr_align_def
                   size_numtype_div8)
next
  case load_pack then show ?case
    by (auto elim!: wf_LOAD wf_loadopE wf_loadop_InnE fun_sizennE wf_szE intro!: b_e_typing.load
             simp: memory_tr_nonempty load_store_t_bounds_def option_projl_def tr_align_def
                   tr_tp_def tp_of_bits_def tp_num_length_def t_num_length_def is_int_t_num_def
                   numtype_Inn_case split: Inn.splits)
next
  case store_val then show ?case
    by (auto intro!: b_e_typing.store
             simp: memory_tr_nonempty load_store_t_bounds_def tr_align_def size_numtype_div8)
next
  case store_pack then show ?case
    by (auto elim!: wf_STORE fun_sizennE wf_szE intro!: b_e_typing.store
             simp: memory_tr_nonempty load_store_t_bounds_def tr_align_def tr_tp_def tp_of_bits_def
                   tp_num_length_def t_num_length_def is_int_t_num_def numtype_Inn_case
             split: Inn.splits)
next
  case vload_val then show ?case
    by (auto intro!: b_e_typing.load_vec
             simp: memory_tr_nonempty load_vec_t_bounds_def t_vec_length_def tr_align_def)
next
  case vload_pack then show ?case
    by (auto elim!: wf_VLOAD wf_vloadopE wf_szE intro!: b_e_typing.load_vec
             simp: memory_tr_nonempty load_vec_t_bounds_def tr_align_def tpv_of_bits_def
                   tp_vec_length_def tp_vec_num_def)
next
  case vload_splat then show ?case
    by (auto elim!: wf_VLOAD wf_vloadopE dest!: wf_sz_cases svi_of_bits_facts
             intro!: b_e_typing.load_vec simp: memory_tr_nonempty load_vec_t_bounds_def tr_align_def)
next
  case vload_zero then show ?case
    by (auto elim!: wf_VLOAD wf_vloadopE dest!: wf_sz_cases intro!: b_e_typing.load_vec
             simp: memory_tr_nonempty load_vec_t_bounds_def t_vec_length_def tr_align_def)
next
  case vload_lane then show ?case
    by (auto elim!: wf_VLOAD_LANE dest!: wf_sz_cases
             intro!: b_e_typing.load_lane_vec
             simp: memory_tr_nonempty tr_align_def svi_of_bits_def vec_i_length_def vec_i_num_def
                   rat_lt_numeral)
next
  case vstore then show ?case
    by (auto intro!: b_e_typing.store_vec
             simp: memory_tr_nonempty store_vec_t_bounds_def t_vec_length_def tr_align_def)
next
  case vstore_lane then show ?case
    by (auto elim!: wf_VSTORE_LANE dest!: wf_sz_cases
             intro!: b_e_typing.store_vec
             simp: memory_tr_nonempty store_vec_t_bounds_def tr_align_def svi_of_bits_def
                   vec_i_length_def vec_i_num_def rat_lt_numeral)
next
  case empty then show ?case by (simp add: tr_instrs_def b_e_typing.empty)
next
  case Instrs_ok__instr then show ?case by (simp add: tr_instrs_def)
next
  case seq then show ?case by (auto simp: tr_instrs_def intro: b_e_type_comp_conc)
next
  case sub then show ?case
    by (auto dest!: Resulttype_sub_tr intro: b_e_typing.subsumption[OF _ instr_subtyping_simple])
next
  case Instrs_ok__frame then show ?case by (simp add: b_e_weakening)
qed

end

end
