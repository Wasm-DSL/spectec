import Mathlib.Tactic

inductive EvenPred : Nat → Prop where
  | zero : EvenPred 0
  | add_two : ∀ k : Nat, EvenPred k → EvenPred (k + 2)

#check @EvenPred.rec
-- Real output goes here once compiled.

example (n : Nat) (h : EvenPred n) (P : Nat → Prop) : P n := by
  induction h with
  | zero => sorry
  | add_two k hk ih =>
    trace_state
    sorry

-- Confirm the real compiled proof term, to see EXACTLY what motive got
-- inferred and how the minor premises look:
example (n : Nat) (h : EvenPred n) (P : Nat → Prop)
    (hzero : P 0) (hstep : ∀ k, EvenPred k → P k → P (k + 2)) : P n := by
  induction h with
  | zero => exact hzero
  | add_two k hk ih => exact hstep k hk ih

set_option pp.proofs true in
example (n : Nat) (h : EvenPred n) (P : Nat → Prop)
    (hzero : P 0) (hstep : ∀ k, EvenPred k → P k → P (k + 2)) : P n := by
  induction h with
  | zero => exact hzero
  | add_two k hk ih => exact hstep k hk ih
