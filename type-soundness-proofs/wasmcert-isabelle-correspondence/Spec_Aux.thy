(* Auxiliary facts about the SpecTec-generated theory.

   The Isabelle backend emits helper functions as
   [function (sequential, domintros)] without termination proofs, so their
   equations are only available as conditional [psimps].  All of them are
   non-recursive; proving termination yields the unconditional [simps].

   SpecTec's own soundness proof (../isabelle/Type_Inversion.thy) provides the
   typing inversion lemmas that the reduction simulation needs (Step_Typing.thy).
   It is imported here because it already proves termination of [valtype_numtype],
   [numtype_Inn] and [size]: proving it again would give two facts named
   [size.simps] etc. that clash when theories are merged. *)
theory Spec_Aux
  imports Translation "../isabelle/Type_Inversion"
begin

(* Type_Inversion's subtyping notation for SpecTec result types; WasmCert uses the
   same syntax for its own list subtyping. *)
no_notation Subtyping_Properties.t_list_subtyping ("_ '<ts: _" 60)
no_notation Instrtype_sub ("_ '<ti: _" 60)

termination proj_uN_0 by lexicographic_order
termination proj_list_0 by lexicographic_order
termination proj_dim_0 by lexicographic_order
termination proj_ishape_0 by lexicographic_order
termination valtype_reftype by lexicographic_order
termination valtype_vectype by lexicographic_order
termination valtype_Inn by lexicographic_order
termination numtype_Fnn by lexicographic_order
termination unpack by lexicographic_order
termination shunpack by lexicographic_order
termination fun_dim by lexicographic_order
termination fun_lanetype by lexicographic_order
termination vsize by lexicographic_order
termination proj_sz_0 by lexicographic_order
termination psize by lexicographic_order
termination typeofval by lexicographic_order

(* The generated theory writes natural-number subtraction as [nat (int a - int b)]. *)
lemma nat_int_diff[simp]: "nat (int a - int b) = a - b"
  by (cases "b \<le> a") auto

lemma nat_int_diff1[simp]: "nat (int a - 1) = a - 1"
  using nat_int_diff[of a 1] by simp

lemma nat_pow2_minus1[simp]: "nat ((2::int) ^ N - 1) = 2 ^ N - 1"
proof -
  have "(2::int) ^ N - 1 = int (2 ^ N - 1)" by (simp add: of_nat_diff)
  then show ?thesis by (simp only: nat_int)
qed

(* Alignment bounds are compared in [rat]: [2^a <= size / 8]. *)
lemma rat_align_le[simp]: "((2::rat) ^ a * 8 \<le> rat_of_nat y) = (2 ^ a \<le> y div 8)"
proof -
  have "(2::rat) ^ a * 8 = rat_of_nat (2 ^ a * 8)" by simp
  then have "((2::rat) ^ a * 8 \<le> rat_of_nat y) = (2 ^ a * 8 \<le> y)" by (simp only: of_nat_le_iff)
  then show ?thesis by (simp add: less_eq_div_iff_mult_less_eq)
qed

lemma rat_lt_numeral: "(rat_of_nat i < numeral k) = (i < numeral k)"
  by (metis of_nat_less_iff of_nat_numeral)

(* Lane indices are bounded in [rat]: [i < 128 / N]. *)
lemma rat_lane_lt[simp]:
  "n = 8 \<or> n = 16 \<or> n = 32 \<or> n = 64 \<Longrightarrow> (rat_of_nat i < 128 / rat_of_nat n) = (i < 128 div n)"
  by (elim disjE) (simp_all add: rat_lt_numeral)

lemma rat_pow2_le_numeral[simp]: "((2::rat) ^ a \<le> numeral n) = ((2::nat) ^ a \<le> numeral n)"
proof -
  have "(2::rat) ^ a = rat_of_nat (2 ^ a)" "(numeral n :: rat) = rat_of_nat (numeral n)" by simp_all
  then show ?thesis by (simp only: of_nat_le_iff)
qed

(* SpecTec's optional-argument encodings ([option_to_list], [list_all3]). *)
lemma list_all2_option_to_list:
  "list_all2 R (option_to_list a) (option_to_list b) =
     (case (a, b) of (None, None) \<Rightarrow> True | (Some x, Some y) \<Rightarrow> R x y | _ \<Rightarrow> False)"
  by (cases a; cases b; simp)

lemma list_all3_option_to_list:
  "list_all3 R (option_to_list a) (option_to_list b) (option_to_list c) =
     (case (a, b, c) of (None, None, None) \<Rightarrow> True | (Some x, Some y, Some z) \<Rightarrow> R x y z
      | _ \<Rightarrow> False)"
  by (cases a; cases b; cases c;
      auto elim: list_all3.cases intro: list_all3.intros)

lemma list_all_option_to_list[simp]: "list_all P (option_to_list x) = pred_option P x"
  by (cases x) simp_all

lemma set_option_to_list[simp]: "set (option_to_list x) = set_option x"
  by (cases x) simp_all

lemma map_option_un_mk_uN[simp]: "map_option un (map_option mk_uN x) = x"
  by (cases x) simp_all

(* The simplifier fuses [map f (map g xs)] into [map (f \<circ> g) xs]. *)
lemma un_comp_mk_uN[simp]: "un \<circ> mk_uN = id"
  by (rule ext) simp

lemma tr_local_comp_LOCAL[simp]: "tr_local \<circ> LOCAL = tr_valtype"
  by (rule ext) simp

lemma tr_admin_comp_instr[simp]: "tr_admin \<circ> admininstr_instr = Basic \<circ> tr_instr"
  by (rule ext) simp

lemma list_all2_option_to_list_single[simp]:
  "list_all2 R (option_to_list a) [y] = (\<exists>x. a = Some x \<and> R x y)"
  by (cases a) simp_all

lemma list_all3_option_to_list_single[simp]:
  "list_all3 R (option_to_list a) [y] [z] = (\<exists>x. a = Some x \<and> R x y z)"
  by (cases a) (auto elim: list_all3.cases intro: list_all3.intros)

(* Inn/Fnn injections as case distinctions, for proofs that split on the subtype. *)
lemma numtype_Inn_case: "numtype_Inn t = (case t of Inn_I32 \<Rightarrow> I32 | Inn_I64 \<Rightarrow> I64)"
  by (cases t) simp_all

lemma numtype_Fnn_case: "numtype_Fnn t = (case t of Fnn_F32 \<Rightarrow> F32 | Fnn_F64 \<Rightarrow> F64)"
  by (cases t) simp_all

lemma proj_uN_0_un[simp]: "proj_uN_0 x = un x"
  by (cases x) simp

lemma proj_list_0_simp[simp]: "proj_list_0 (mk_list l) = l"
  by simp

section \<open>Types\<close>

lemma tr_valtype_numtype[simp]: "tr_valtype (valtype_numtype nt) = T_num (tr_numtype nt)"
  by (cases nt) simp_all

lemma tr_valtype_reftype[simp]: "tr_valtype (valtype_reftype rt) = T_ref (tr_reftype rt)"
  by (cases rt) simp_all

lemma tr_valtype_vectype[simp]: "tr_valtype (valtype_vectype vt) = T_vec T_v128"
  by (cases vt) simp_all

lemma tr_valtype_Inn[simp]: "tr_valtype (valtype_Inn t) = T_num (tr_numtype (numtype_Inn t))"
  by (cases t) simp_all

lemma tr_resulttype_mk_list[simp]: "tr_resulttype (mk_list l) = map tr_valtype l"
  by simp

lemma tr_resulttype_proj: "tr_resulttype r = map tr_valtype (proj_list_0 r)"
  by (cases r) simp

lemma Valtype_sub_tr: "Valtype_sub t1 t2 \<Longrightarrow> tr_valtype t1 <t: tr_valtype t2"
  by (induction rule: Valtype_sub.induct) (simp_all add: t_subtyping_def)

lemma Resulttype_sub_tr:
  "Resulttype_sub (mk_list t1) t2 \<Longrightarrow> map tr_valtype t1 <ts: tr_resulttype t2"
proof (induction "mk_list t1" t2 rule: Resulttype_sub.induct)
  case (mk_Resulttype_sub t_2_lst)
  then show ?case
    by (simp add: Wasm_Subtyping.t_list_subtyping_def list.rel_map list_all2_mono Valtype_sub_tr)
qed

section \<open>Contexts\<close>

lemma tr_context_sel[simp]:
  "types_t (tr_context C) = map tr_functype (context_TYPES C)"
  "func_t (tr_context C) = map tr_functype (context_FUNCS C)"
  "global (tr_context C) = map tr_globaltype (context_GLOBALS C)"
  "elem (tr_context C) = map tr_reftype (context_ELEMS C)"
  "data (tr_context C) = map (\<lambda>_. ()) (context_DATAS C)"
  "table (tr_context C) = map tr_tabletype (context_TABLES C)"
  "memory (tr_context C) = map tr_memtype (context_MEMS C)"
  "local (tr_context C) = map tr_valtype (context_LOCALS C)"
  "label (tr_context C) = map tr_resulttype (LABELS C)"
  "return (tr_context C) = map_option tr_resulttype (context_RETURN C)"
  "refs (tr_context C) = [0..<length (context_FUNCS C)]"
  by (simp_all add: tr_context_def)

(* The context of a block body: one label is pushed, nothing else changes. *)
lemma tr_context_label[simp]:
  "tr_context (append_res_context
     \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
      context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
      LABELS = [ts], context_RETURN = None\<rparr> C)
   = (tr_context C)\<lparr>label := tr_resulttype ts # label (tr_context C)\<rparr>"
  by (simp add: tr_context_def append_res_context_def)

lemma Blocktype_ok_tr:
  "Blocktype_ok C bt (mk_functype (mk_list t1) (mk_list t2)) \<Longrightarrow>
   tb_tf_t (tr_context C) (tr_blocktype bt) = Some (map tr_valtype t1 _> map tr_valtype t2)"
  by (erule Blocktype_ok.cases)
     (auto simp: tb_tf_t_def tr_context_def split: option.splits)

end
