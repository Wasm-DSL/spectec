import Mathlib.Tactic
set_option pp.proofs true

inductive Bleh : Prop where
  | bleh : Bleh

#check @Bleh.rec

/- ════════════════════════════════════════════════════════════════════════
   TOY VERSION: minimal mutual pair mirroring Instr_ok/Instrs_ok's shape.
   StepOk ~ Instr_ok (single item), SeqOk ~ Instrs_ok (list, with an
   append-based `seq` constructor -- that's the one that matters here).
   Small enough to prove COMPLETELY, no sorries, so you can see the whole
   mechanism end to end.
   ════════════════════════════════════════════════════════════════════════ -/
mutual
inductive StepOk : Nat → Prop where
  | step (n : Nat) : n ≠ 0 → StepOk n

inductive SeqOk : List Nat → Prop where
  | empty : SeqOk []
  | single (n : Nat) : StepOk n → SeqOk [n]
  | seq (xs ys : List Nat) : SeqOk xs → SeqOk ys → SeqOk (xs ++ ys)
end

-- STAGE 0: the raw recursor -- two motives, one per mutual member.
#check @SeqOk.rec

/- ────────────────────────────────────────────────────────────────────────
   STAGE 1 (toy): ORIGINAL approach -- induct directly on the goal-specific
   derivation. Trace (a) before induction, (b) raw ih before simp, (c) ih
   after simp_all.
   ──────────────────────────────────────────────────────────────────────── -/
theorem toy_original (n : Nat) (ns : List Nat) :
    SeqOk (n :: ns) → StepOk n ∧ SeqOk ns := by
  intro seqOk
  generalize list_eq : (n :: ns) = xs at seqOk

  dbg_trace "=== TOY (a) BEFORE induction ==="
  trace_state

  induction seqOk using SeqOk.rec (motive_1 := fun _ _ => True)
  <;> try trivial
  case single n' stepOk _ih =>
    simp_all
    exact SeqOk.empty
  case seq xs' ys' seqOk_xs seqOk_ys ih_xs ih_ys =>

    dbg_trace "=== TOY (b) RAW ih, BEFORE simp_all ==="
    trace_state

    simp_all

    dbg_trace "=== TOY (c) ih AFTER simp_all ==="
    trace_state
    -- Same shape of problem as the real proof: ih_xs/ih_ys are gated on
    -- `ys' = []` / `xs' = []` respectively -- only useful in the
    -- degenerate case where one side is the WHOLE original list.
    sorry

/- ────────────────────────────────────────────────────────────────────────
   STAGE 2 (toy): FIXED approach -- state a fully general auxiliary lemma
   FIRST (quantified over the recursion target's own head/tail), so the
   auto-inferred motive is properly general from the start. This one we
   can actually FINISH -- no sorries.
   ──────────────────────────────────────────────────────────────────────── -/
theorem toy_general :
    ∀ (xs : List Nat), SeqOk xs →
      ∀ (n : Nat) (ns : List Nat), xs = n :: ns →
        StepOk n ∧ SeqOk ns
  := by
  intro xs h
  induction h using SeqOk.rec (motive_1 := fun _ _ => True)
  <;> try trivial
  case empty =>
    intro n ns hcontra
    exact absurd hcontra (by simp)
  case single n' stepOk _ih =>
    intro n ns heq
    injection heq with n_eq ns_eq
    subst n_eq; subst ns_eq
    exact ⟨stepOk, SeqOk.empty⟩
  case seq xs' ys' seqOk_xs seqOk_ys ih_xs ih_ys =>

    dbg_trace "=== TOY STAGE 2: ih_xs/ih_ys already general ==="
    trace_state

    intro n ns heq
    cases xs' with
    | nil =>
      simp only [List.nil_append] at heq
      exact ih_ys n ns heq
    | cons hd tl =>
      simp only [List.cons_append] at heq
      injection heq with hd_eq tl_eq
      subst hd_eq
      obtain ⟨stepOk_hd, seqOk_tl⟩ := ih_xs hd tl rfl
      exact ⟨stepOk_hd, tl_eq ▸ SeqOk.seq tl ys' seqOk_tl seqOk_ys⟩

theorem toy_fixed (n : Nat) (ns : List Nat) :
    SeqOk (n :: ns) → StepOk n ∧ SeqOk ns
  := fun h => toy_general (n :: ns) h n ns rfl

#print axioms toy_fixed
