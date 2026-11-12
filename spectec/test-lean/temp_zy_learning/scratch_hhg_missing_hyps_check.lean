import Mathlib.Tactic

/- Checking two passages from the Hitchhiker's Guide to Logical Verification
   against real, compiled Lean output, to see whether the book's printed
   subgoals omit hypotheses that are actually present.

   `Even` is renamed `EvenPred` throughout only because `Even` already
   exists in Mathlib (as `∃ r, n = r + r`) and would clash with our own
   from-scratch definition. -/

inductive EvenPred : Nat → Prop where
  | zero    : EvenPred 0
  | add_two : ∀ k : Nat, EvenPred k → EvenPred (k + 2)

/- ═══════════════════════════════════════════════════════════════════════
   PASSAGE 1

   "If the goal has the form h : Even n ⊢ P n, applying induction on h
   will produce the following subgoals:
       ⊢ P 0          k : N, hk : P k ⊢ P (k + 2)"

   HHG's printed subgoals list NO hypotheses about `n` at all -- as if
   `n` simply vanished. Let's check directly. ═══════════════════════════ -/

example (n : Nat) (h : EvenPred n) (P : Nat → Prop) : P n := by
  induction h with
  | zero =>
    trace_state
    sorry
  | add_two k hk ih =>
    trace_state
    sorry

/- ═══════════════════════════════════════════════════════════════════════
   PASSAGE 2

   "... we need to replace 2 * n + 1 by a variable m and add an equation
   m = 2 * n + 1 as a hypothesis:
       m : 2 * n + 1, hev : Even m ⊢ False
   ... now induction produces two subgoals:
       m n : N, hm : 0 = 2 * n + 1 ⊢ False
       m : 2 * n + 1, ih : m = 2 * n + 1 → False, hm : m + 2 = 2 * n + 1 ⊢ False"

   Here HHG DOES list `m` in the first subgoal, but the second subgoal's
   line has no separate `n`, and reuses the letter `m` for what should be
   a brand-new variable (the constructor's own argument, elsewhere called
   `k`). Let's check exactly what real Lean produces, with `m`/`n`/`hm`
   named exactly as HHG names them (except the constructor-bound variable,
   which we name `k` to avoid exactly the confusing reuse of `m`). ═════ -/

theorem a1 (n m : Nat) (hm : m = 2 * n + 1) (hev : EvenPred m) : False := by
  induction hev with
  | zero =>
    trace_state
    sorry
  | add_two k hk ih =>
    trace_state
    sorry


theorem a2 (n m : Nat) (hm : m = 2 * n + 1) (hev : EvenPred m) : False := by
  induction hev generalizing n with
  | zero =>
    trace_state
    sorry
  | add_two k hk ih =>
    trace_state
    apply ih (n-1)
    cases n with
    | zero => simp [Nat.ctor_eq_zero] at *
    | succ n' =>
      simp [Nat.succ_eq_add_one] at *
      linarith


theorem Not_Even_two_mul_add_one (m n : Nat) (hm : m = 2 * n + 1) : ¬ EvenPred m :=
  by
  intro h
  induction h generalizing n with
  | zero => linarith
  | add_two k hk ih =>
  apply ih (n - 1)
  cases n with
    | zero => simp [Nat.ctor_eq_zero] at *
    | succ n' =>
      simp [Nat.succ_eq_add_one] at *
      linarith
