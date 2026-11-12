import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON I5 (capstone): the fix for I2/I3's narrow-ih problem, and where
   every earlier lesson in this guide actually came from.

   This mirrors -- deliberately, on a fresh minimal toy -- the exact
   mechanism you already saw fully verified in `scratch_ih_trace_toy.lean`
   and `scratch_motive_contrast.lean` from earlier this session, applied
   to the REAL `Instr_ok`/`Instrs_ok` proof in `typing_lemmas.lean`
   (`instrs_seq_typing_inversion`). If you haven't looked at those two
   files, this lesson is their "from scratch, one concept at a time"
   version; if you have, this is the same result rebuilt with the full
   R1-R6 + I1-I4 vocabulary now in hand. -/

mutual
inductive StepOk : Nat → Prop where
  | step (n : Nat) : n ≠ 0 → StepOk n

inductive SeqOk : List Nat → Prop where
  | empty : SeqOk []
  | single (n : Nat) : StepOk n → SeqOk [n]
  | seq (xs ys : List Nat) : SeqOk xs → SeqOk ys → SeqOk (xs ++ ys)
end

/- GOAL: given `SeqOk (n :: ns)`, recover `StepOk n ∧ SeqOk ns` -- i.e. "peel
   the head off a proven sequence." -/

/- ─── ATTEMPT 1: induct directly on the specific goal (I2/I3's trap) ─── -/
theorem attempt1 (n : Nat) (ns : List Nat) :
    SeqOk (n :: ns) → StepOk n ∧ SeqOk ns := by
  intro h
  generalize eq1 : (n :: ns) = xs at h
  induction h using SeqOk.rec (motive_1 := fun _ _ => True) with
  | step n _ => trivial
  | empty => simp_all
  | single n' step => simp_all; exact SeqOk.empty
  | seq xs' ys' hxs hys ihxs ihys =>
    -- print the ih and see I2's exact problem, live:
    trace_state
    -- ihxs : n :: ns = xs' → StepOk n ∧ SeqOk ns   (an I2-style narrow ih --
    --   only fires if xs' happens to BE the whole original list)
    cases xs' with
    | nil =>
      simp only [List.nil_append] at eq1
      -- ihys IS usable here, because in THIS branch xs'=[] happens to
      -- make its gate satisfiable -- but that's luck of the branch, not
      -- something you could count on in general (see the `cons` branch).
      exact ihys eq1
    | cons hd tl =>
      -- STUCK the same way the real `case seq`'s `cons` branch was stuck:
      -- ihxs needs `n :: ns = hd :: tl`, which has nothing to do with
      -- what you actually know here (that xs' = hd :: tl came from
      -- case-splitting, unrelated to the outer n/ns).
      sorry

/- ─── ATTEMPT 2: state a properly GENERAL auxiliary lemma first ───
   Same fix as `instrs_seq_typing_inversion_general` in `typing_lemmas.lean`:
   quantify the head/tail INSIDE the statement, ahead of the induction,
   so the auto-inferred motive is general from the start (I3's lesson:
   `induction using` reverse-engineers motive_2 from whatever the goal
   looks like AT THE MOMENT you call it -- so make the goal already
   general). -/
theorem general :
    ∀ (xs : List Nat), SeqOk xs →
      ∀ (n : Nat) (ns : List Nat), xs = n :: ns →
        StepOk n ∧ SeqOk ns
  := by
  intro xs h
  induction h using SeqOk.rec (motive_1 := fun _ _ => True) with
  | step n _ => trivial
  | empty => intro n ns hcontra; exact absurd hcontra (by simp)
  | single n' step =>
    intro n ns heq
    injection heq with n_eq ns_eq
    subst n_eq; subst ns_eq
    exact ⟨step, .empty⟩
  | seq xs' ys' hxs hys ihxs ihys =>
    trace_state
    -- ihxs : ∀ (n : ℕ) (ns : List ℕ), xs' = n :: ns → StepOk n ∧ SeqOk ns
    -- GENUINELY about xs' own structure now -- compare directly to
    -- attempt1's `ihxs` above.
    intro n ns heq
    cases xs' with
    | nil =>
      simp only [List.nil_append] at heq
      exact ihys n ns heq
    | cons hd tl =>
      simp only [List.cons_append] at heq
      injection heq with hd_eq tl_eq
      subst hd_eq
      obtain ⟨stepHd, seqTl⟩ := ihxs hd tl rfl
      exact ⟨stepHd, tl_eq ▸ SeqOk.seq tl ys' seqTl hys⟩

theorem attempt2_fixed (n : Nat) (ns : List Nat) :
    SeqOk (n :: ns) → StepOk n ∧ SeqOk ns
  := fun h => general (n :: ns) h n ns rfl

#print axioms attempt2_fixed

/- ─── Under the hood, tying it all together ───
   `general`'s proof term is a `SeqOk.rec` application with BOTH motives
   supplied (`motive_1 := fun _ _ => True` for StepOk, the real one
   auto-inferred for SeqOk from `general`'s own fully-general statement)
   -- and `attempt2_fixed` is nothing more than `general` applied to the
   SPECIFIC values `(n :: ns)`, `n`, `ns`, `rfl` -- no induction of its
   own at all. This is the exact shape `instrs_seq_typing_inversion`
   should end up with too, once restructured the same way. -/
set_option pp.proofs true in
#print general

/- ─── Where to go next ───
   `attempt2_fixed`/`general` here are, line for line, the same shape as
   `instrs_seq_typing_inversion`/`instrs_seq_typing_inversion_general` in
   `typing_lemmas.lean` -- `StepOk`~`Instr_ok`, `SeqOk`~`Instrs_ok`, and the
   `seq`/`cons` branch is where all the real content lives in both. Go
   re-read that theorem now with this guide's full vocabulary: R1-R3 for
   what the raw `Instr_ok.rec`/`Instrs_ok.rec` minor premises and ih's
   actually are, R4 for why `context`/`functype` show up as leading
   motive arguments, R5-R6 for why there are two motives and how their
   ih's interleave, I1-I2 for why `generalize`+`induction` behaves the
   way it does with `instrs_eq`/`ft_eq`, and I3-I5 for exactly why the
   original proof's `ih_i_list`/`ih_is_list` were too narrow, and exactly
   what change fixes it. -/
