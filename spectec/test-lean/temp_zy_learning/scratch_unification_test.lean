import Mathlib.Tactic

inductive EvenPred : Nat → Prop where
  | zero : EvenPred 0
  | add_two : ∀ k : Nat, EvenPred k → EvenPred (k + 2)

-- (1) Is `motive (k+2) ...` baked into the recursor's TYPE regardless of
-- any goal? Check it in total isolation, no tactic, no goal in sight.
#check @EvenPred.rec
-- If this line alone already shows `motive (k + 2) ...`, that confirms
-- it's fixed at DECLARATION time, not derived from any later goal.

-- (2) Does motive-inference in `induction h` find occurrences of `n`
-- SYNTACTICALLY, or up to DEFINITIONAL EQUALITY (i.e. via something
-- unification-flavored, like `kabstract`)?

-- (2a) Hide `n` behind a @[reducible] alias -- reducible defs are
-- unfolded by defeq-checking machinery by default.
@[reducible] def Id1 (n : Nat) : Nat := n

example (n : Nat) (h : EvenPred n) (P : Nat → Prop) : P (Id1 n) := by
  induction h with
  | zero => sorry
  | add_two k hk ih => trace_state; sorry

-- (2b) Hide `n` behind a PLAIN (non-reducible) def instead.
def Id2 (n : Nat) : Nat := n

example (n : Nat) (h : EvenPred n) (P : Nat → Prop) : P (Id2 n) := by
  induction h with
  | zero => sorry
  | add_two k hk ih => trace_state; sorry
