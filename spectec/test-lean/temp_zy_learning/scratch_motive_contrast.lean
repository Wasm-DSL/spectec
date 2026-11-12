import Mathlib.Tactic
import «typing_lemmas»
open functype list

/- ════════════════════════════════════════════════════════════════════════
   ORIGINAL approach: induct directly on the SPECIFIC goal
   (Instrs_ok c (i :: is) (ts1 f-> ts3) → ...), using `generalize` +
   `induction ... using` to let Lean auto-infer motive_2 from the goal.
   ════════════════════════════════════════════════════════════════════════ -/
theorem original_style
  (c : context) (i : instr) (is : List instr) (ts1 ts3 : List valtype)
  :
  Instrs_ok c (i :: is) (ts1 f-> ts3)
  → ∃ ts2, Instr_ok c i (ts1 f-> ts2) ∧ Instrs_ok c is (ts2 f-> ts3)
  := by
  intros instrs_ok
  generalize instrs_eq : (i :: is) = instrs at instrs_ok
  generalize ft_eq : (ts1 f-> ts3) = ft at instrs_ok
  induction instrs_ok using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  case seq C i_list is_list t1_lst t3_lst t2_lst h1 h2 wf_c' wf1 wf2 ih1 ih2 =>
    -- THIS is the "before" proof state -- look at ih1's type.
    trace_state
    sorry
  all_goals sorry

/- ════════════════════════════════════════════════════════════════════════
   FIXED approach: first prove a MAXIMALLY GENERAL auxiliary lemma, whose
   own statement is quantified over the induction target's own indices
   (instrs, ft) rather than over the outer i/is/ts1/ts3. Then the ORIGINAL
   theorem is a one-line corollary.
   ════════════════════════════════════════════════════════════════════════ -/
theorem instrs_seq_typing_inversion_general
  (c : context) :
  ∀ (instrs : List instr) (ft : functype), Instrs_ok c instrs ft →
    ∀ (a : instr) (b : List instr), instrs = a :: b →
      ∀ (t1' t3' : List valtype), ft = (t1' f-> t3') →
        ∃ ts2, Instr_ok c a (t1' f-> ts2) ∧ Instrs_ok c b (ts2 f-> t3')
  := by
  intro instrs ft h
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  <;> try trivial
  case empty =>
    intro a b hab
    exact absurd hab (by simp)
  case instr C v_instr t1_lst t2_lst instr_ok wf_c' wf_i' =>
    sorry
  case seq C i_list is_list t1_lst t3_lst t2_lst h1 h2 wf_c' wf1 wf2 ih1 ih2 =>
    -- THIS is the "after" proof state -- look at ih1's type (BEFORE we even
    -- destructure anything else), and compare to the trace above.
    trace_state
    intro a b hab t1' t3' hft
    unfold mkFunctype at hft
    injection hft with heq1 heq2
    injection heq1 with t1'_eq'
    injection heq2 with t3'_eq'
    subst t1'_eq'; subst t3'_eq'
    cases i_list with
    | nil => sorry
    | cons hd tl =>
      simp only [List.cons_append] at hab
      injection hab with a_eq b_eq
      -- THE PAYOFF: ih1 can be applied to hd/tl DIRECTLY, because it's
      -- genuinely quantified over i_list's own head/tail -- not gated on
      -- i_list equaling the whole original i :: is.
      obtain ⟨ts2', instr_hd, instrs_tl⟩ := ih1 hd tl rfl t1_lst t2_lst rfl
      refine ⟨ts2', ?_, ?_⟩
      · subst a_eq; exact instr_hd
      · subst b_eq
        exact Instrs_ok.seq C tl is_list ts2' t3_lst t2_lst instrs_tl h2 wf_c'
          (fun x hx => wf1 x (List.mem_cons_of_mem hd hx))
          wf2
  case sub => intro a b hab t1' t3' hft; sorry
  case frame => intro a b hab t1' t3' hft; sorry

theorem instrs_seq_typing_inversion_fixed
  (c : context) (i : instr) (is : List instr) (ts1 ts3 : List valtype) :
  Instrs_ok c (i :: is) (ts1 f-> ts3) →
  ∃ ts2, Instr_ok c i (ts1 f-> ts2) ∧ Instrs_ok c is (ts2 f-> ts3)
  := fun h => instrs_seq_typing_inversion_general c (i :: is) (ts1 f-> ts3) h i is rfl ts1 ts3 rfl
