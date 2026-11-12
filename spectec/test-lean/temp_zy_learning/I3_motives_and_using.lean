import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON I3: explicit motives, `induction ... using`, and a real
   boundary between what `induction` will accept and what `apply` will.

   Real world: BoundedBasket from R4 -- a basket indexed by its own
   declared pear count. -/

inductive BoundedBasket : Nat → Type where
  | empty : BoundedBasket 0
  | addPear : BoundedBasket n → BoundedBasket (n + 1)

/- `induction b` on a `b : BoundedBasket n` normally auto-infers the
   motive from your current goal -- you never see it happen, and (as the
   NEXT section shows) you generally can't ask `induction using` to use
   an explicit one instead, even a correct one. -/
theorem auto_infers_fine (n : Nat) (b : BoundedBasket n) :
    n = n := by
  induction b using BoundedBasket.rec with
  | empty => rfl
  | addPear rest ih => rfl

/- ─── The real boundary, empirically ───
   `induction ... using` needs the motive to be a genuine METAVARIABLE it
   can solve by matching against your goal -- supply an already-CONCRETE
   motive (even a perfectly correct one) and it refuses outright. `apply`
   on the raw recursor, by contrast, is ordinary function application
   with full unification, and accepts a concrete motive just fine. This
   is the exact wall hit in the real `instrs_seq_typing_inversion` proof
   earlier this session. -/

-- ATTEMPT A: `induction ... using` with an explicit motive -- FAILS.
-- (Left commented out because it's a genuine elaboration error, not a
-- `sorry` -- uncomment to see the real message yourself.)
-- theorem attempt_A (n : Nat) (b : BoundedBasket n) : n = n := by
--   induction b using BoundedBasket.rec (motive := fun n _ => n = n) with
--     ...
-- -- error: Expected resulting type of eliminator to be an application of
-- -- one of its parameters (the motive), but found  n = n
-- -- (Lean expected a still-flexible motive it could solve; handing it an
-- -- already-fixed one collapses the "conclusion" to a closed term the
-- -- elaborator can no longer adjust to match your goal.)
#check BoundedBasket.rec
-- ATTEMPT B: same motive, via `apply` on the raw recursor -- WORKS.
theorem attempt_B (n : Nat) (b : BoundedBasket n) : n = n := by
  apply BoundedBasket.rec (motive := fun n _ => n = n) (t := b)
  · rfl
  · intro n rest ih
    rfl

theorem attempt_B2 (n : Nat) (b : BoundedBasket n) : n = n := by
  revert b
  apply BoundedBasket.rec
  · rfl
  · intro n rest ih
    rfl

#print axioms attempt_B

/- ─── Under the hood ───
   `attempt_B` was built with `apply`, not `induction` -- but it's still
   nothing more than a direct `BoundedBasket.rec` application, motive and
   all, exactly as written. Confirm: -/
set_option pp.proofs true in
#print attempt_B
set_option pp.proofs true in
#print auto_infers_fine
-- Compare the two: `auto_infers_fine` (built via `induction using`, no
-- explicit motive) and `attempt_B` (built via `apply`, explicit motive)
-- should print essentially the SAME shape of `BoundedBasket.rec`
-- application -- confirming that `induction`'s auto-inferred motive
-- really was `fun n _ => n = n` all along; you just never had to write
-- it by hand.

/- Why this matters in practice: sometimes the motive you WANT is a
   genuinely more general statement than your current goal happens to be
   -- e.g. "for ANY head/tail decomposition of this list, not just the
   one my outer variables happen to name." `induction using` can't be
   handed that kind of motive directly; you either (a) restate your GOAL
   in the fully general form FIRST so the auto-inferred motive comes out
   general on its own (the fix used in the real proof), or (b) drop down
   to `apply Foo.rec (motive := ...) (t := ...)` and handle every
   resulting goal yourself, losing the convenient `case name =>` syntax
   `induction` gives you for free. Approach (a) is almost always nicer --
   Lesson I5 builds it out fully on a mutual example. -/
