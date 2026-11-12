import Mathlib.Tactic

inductive EvenPred : Nat → Prop where
  | zero : EvenPred 0
  | add_two : ∀ k : Nat, EvenPred k → EvenPred (k + 2)

theorem even_ind_demo (n : Nat) (h : EvenPred n) (P : Nat → Prop)
    (hzero : P 0) (hstep : ∀ k, EvenPred k → P k → P (k + 2)) : P n := by
  induction h with
  | zero => exact hzero
  | add_two k hk ih => exact hstep k hk ih

set_option pp.proofs true in
#print even_ind_demo
