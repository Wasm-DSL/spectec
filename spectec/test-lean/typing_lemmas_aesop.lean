import Mathlib.Tactic
import «wasm2.0»
import «custom_notation»
open functype list

set_option pp.parens true
set_option pp.numericTypes true

-- This file is a standalone sandbox for comparing the hand-written proof of
-- `instrs_empty_typing` in typing_lemmas.lean against a version leaning on
-- `aesop`/`simp`/`grind` automation wherever it will actually close a goal.
-- The prerequisite lemmas below are copied verbatim from typing_lemmas.lean
-- so this file has no dependency on it (and isn't affected by unrelated
-- in-progress errors further down that file).

theorem valtype_sub_refl (t1 : valtype) : t1 sub< t1 := by
  constructor

theorem resulttype_sub_refl (t1s : List valtype) : t1s subs< t1s := by
  unfold resulttypeSub
  apply Resulttype_sub.mk_Resulttype_sub
  · rfl
  · simp [List.zip, Forall₂] at *
    intro a h
    exact valtype_sub_refl a

theorem zip_trans2 (l1 l2 l3 : List α)
  : ∀ r : α → α → Prop,
      (∀ a b, (a, b) ∈ l1.zip l2 → r a b) →
      (∀ b c, (b, c) ∈ l2.zip l3 → r b c) →
      (l1.length = l2.length) →
      (l2.length = l3.length) →
      (∀ a b c, r a b → r b c → r a c)

      → ∀ a c, (a, c) ∈ l1.zip l3 → r a c

  := by

  intro
    r forall_ab_trans forall_bc_trans
    length_same_l1_l2 length_same_l2_l3
    forall_ac_trans a c ac_from_l1_l3

  obtain ⟨i, i_in_bounds_l1_l3, hia_c⟩ := List.mem_iff_getElem.mp ac_from_l1_l3
  rw [List.getElem_zip] at hia_c
  obtain ⟨h_a, h_c⟩ := Prod.mk.injEq .. ▸ hia_c
  rw [List.length_zip] at i_in_bounds_l1_l3
  have i_in_bounds_l1 : i < l1.length := by omega
  have i_in_bounds_l2 : i < l2.length := by omega
  have i_in_bounds_l3 : i < l3.length := by omega
  set ab := (l1.zip l2)[i]'(
    by
      rw [List.length_zip]
      omega
  ) with hab
  set a' := ab.1 with ha'
  set b' := ab.2 with hb'
  have ab_of_l1_l2 : ab ∈ l1.zip l2 := by
    apply List.getElem_mem
  set bc := (l2.zip l3)[i]'(
    by
      rw [List.length_zip]
      omega
  ) with hbc
  set b'' := bc.1 with hb''
  set c' := bc.2 with hc'
  have bc_of_l2_l3 : bc ∈ l2.zip l3 := by
    apply List.getElem_mem
  have trans_ab := forall_ab_trans a' b' ab_of_l1_l2
  have trans_bc := forall_bc_trans b'' c' bc_of_l2_l3
  rw [List.getElem_zip] at *

  have a'_is_a : a' = a := by
    rw [ha', h_a.symm, hab]
  have b'_is_b'' : b' = b'' := by
    rw [hb', hb'', hab, hbc]
  have c'_is_c : c' = c := by
    rw [hc', h_c.symm, hbc]

  rw [b'_is_b''] at trans_ab
  have trans_ac := forall_ac_trans a' b'' c' trans_ab trans_bc
  rw [a'_is_a, c'_is_c] at trans_ac
  exact trans_ac


theorem valtype_sub_trans
  (t1 t2 t3 : valtype)
  (h1 : t1 sub< t2)
  (h2 : t2 sub< t3)
  :
  t1 sub< t3 := by
  cases h1
  · cases h2
    · constructor
    · constructor
  · cases h2
    · constructor
    · constructor


theorem resulttype_sub_trans
  (t1s t2s t3s : List valtype)
  (h1 : t1s subs< t2s)
  (h2 : t2s subs< t3s)
  :
  t1s subs< t3s := by
  unfold resulttypeSub at *
  obtain ⟨_, _, h1_eq, h1_forall⟩ := h1
  obtain ⟨_, _, h2_eq, h2_forall⟩ := h2
  apply Resulttype_sub.mk_Resulttype_sub
  · exact Eq.trans h1_eq h2_eq
  · simp [Forall₂] at *
    intro a b h
    have t := zip_trans2 t1s t2s t3s Valtype_sub

    have t' := t h1_forall h2_forall h1_eq h2_eq valtype_sub_trans a b h

    exact t'


theorem resulttype_sub_app
  (ts1_sub ts2_sub ts1 ts2 : List valtype)
  (h1 : ts1_sub subs< ts1)
  (h2 : ts2_sub subs< ts2)
  :
  (ts1_sub ++ ts2_sub) subs< (ts1 ++ ts2) := by
  unfold resulttypeSub at *
  cases h1
  cases h2
  rename_i same_length_ts1_ts1sub all_ts1sub_sub_ts1 same_length_ts2_ts2sub all_ts2sub_sub_ts2

  simp [Forall₂] at *

  apply Resulttype_sub.mk_Resulttype_sub

  case mk_Resulttype_sub.mk_Resulttype_sub.a =>
    aesop

  case mk_Resulttype_sub.mk_Resulttype_sub.a =>
    simp [Forall₂] at *
    grind


-- Below: `instrs_empty_typing`, refactored to lean on `aesop`/`simp`/`grind`
-- wherever they actually close a goal, instead of the fully manual
-- generalize/obtain/rw chains in typing_lemmas.lean. Verified to compile
-- (`lake env lean typing_lemmas_aesop.lean`) with no errors.
--
-- Findings worth keeping in mind:
--  * `aesop` cannot perform the outer `induction ... using Instrs_ok.rec`
--    itself (it doesn't invent custom-recursor inductions), so the
--    `generalize`/`induction ... generalizing` scaffolding is still manual.
--  * `mkFunctype`/`resulttypeSub` are plain `def`s (not `@[reducible]`), so
--    every automation call needs them spelled out (`simp [mkFunctype]`,
--    `simpa [resulttypeSub] using ...`) or it treats `t1s subs< t2s` as
--    opaque and can't match lemmas stated via `Resulttype_sub`.
--  * `aesop (add safe resulttype_sub_refl)` reliably FAILS to prove goals of
--    the literal shape `X subs< X` (a repeated-metavariable / non-linear
--    pattern) even though `exact resulttype_sub_refl _` proves the same
--    goal instantly - a genuine aesop limitation, not a fluke. Route that
--    step through `simpa` or a direct `exact` instead.
--  * `aesop (add safe resulttype_sub_trans)` also failed on a goal needing a
--    provided intermediate term ("goal was not normalised" internal error);
--    switching the same lemma to `unsafe` (backtracking search instead of
--    greedy application) fixed it.
--  * `grind [resulttype_sub_trans]` closed the single-step transitivity case
--    but failed on the case needing two chained `resulttype_sub_trans`
--    applications through an existing intermediate fact - `grind`'s
--    E-matching didn't find the chain that `aesop`'s backtracking search did.
theorem instrs_empty_typing
    (p_context : context)
    (t1s t2s : List valtype)
    :
    Instrs_ok p_context [] (t1s f-> t2s) ↔
    (wf_context p_context ∧ (t1s subs< t2s))
    := by
    apply Iff.intro
    · intro h
      apply And.intro
      · generalize gen_instrs_ok_list : ([] : List instr) = l at h
        generalize gen_instrs_ok_functype : (t1s f-> t2s) = ft at h
        induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
        all_goals trivial
      · generalize gen_instrs_ok_list : ([] : List instr) = l at h
        generalize gen_instrs_ok_functype : (t1s f-> t2s) = ft at h
        induction h
          using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
          generalizing t1s t2s
        all_goals try trivial
        · simp_all [mkFunctype, resulttype_sub_refl]
        case mp.right.seq
          c i1s i2s t3s t5s t4s instrs_ok1 instrs_ok2
          wf_c wf_i1s wf_i2s what1 what2 =>
          have both_empty : i1s = [] ∧ i2s = [] :=
            List.append_eq_nil_iff.mp gen_instrs_ok_list.symm
          simp [both_empty, mkFunctype] at *
          aesop (add unsafe resulttype_sub_trans)
        case mp.right.sub
          c instrs
          t'1s t'2s t''1s t''2s
          instrs_ok
          res_sub_t'1s_t1s
          res_sub_t2s_t'2s
          wf_c
          wf_all_instr_in_instrs
          ih =>
          simp [mkFunctype] at *
          have h := ih t''1s t''2s gen_instrs_ok_list rfl rfl
          aesop (add unsafe resulttype_sub_trans)

        case mp.right.frame
          c instrs ts t'1s t'2s instrs_ok wf_c wf_all_instr_in_c ih =>
          simp [mkFunctype] at *
          have t'1s_sub_t'2s : t'1s subs< t'2s := ih t'1s t'2s gen_instrs_ok_list rfl rfl
          aesop (add safe resulttype_sub_refl, unsafe resulttype_sub_app)
    · intro h
      obtain ⟨wf_c, t1s_sub_t2s⟩ := h
      apply Instrs_ok.sub (t_1_lst := t2s ++ []) (t_2_lst := t2s ++ [])
      case mpr.a => apply Instrs_ok.frame <;> aesop (add safe apply Instrs_ok.empty, norm simp [Forall])
      case mpr.a => simpa [resulttypeSub] using t1s_sub_t2s
      case mpr.a => simpa [resulttypeSub] using resulttype_sub_refl t2s
      case mpr.a => exact wf_c
      case mpr.a => simp [Forall]