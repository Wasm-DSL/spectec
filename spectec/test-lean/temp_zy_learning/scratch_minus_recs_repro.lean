import Mathlib.Tactic

-- Minimal reproduction of the fun_minus_recs shape: two MUTUALLY inductive
-- types, where one's constructor mentions ¬ (its sibling) -- a negative
-- occurrence of a type in the SAME mutual group, not of itself directly.
mutual
inductive Helper : Nat → Prop where
  | mk (n : Nat) : Main n → Helper n     -- mentions Main POSITIVELY: fine on its own

inductive Main : Nat → Prop where
  | base : Main 0
  | bad (n : Nat) : ¬ Helper n → Main n  -- mentions ¬ Helper: Helper occurs as the
                                          -- ARGUMENT of a function type (¬P = P → False)
end
