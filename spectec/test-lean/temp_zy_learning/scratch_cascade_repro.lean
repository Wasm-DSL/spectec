import Mathlib.Tactic

-- Category A: the root cause (already verified separately) -- reproduced
-- here again just to keep both categories in one file for comparison.
mutual
inductive Helper : Nat → Prop where
  | mk (n : Nat) : Main n → Helper n
inductive Main : Nat → Prop where
  | base : Main 0
  | bad (n : Nat) : ¬ Helper n → Main n   -- (kernel) non positive occurrence
end

-- Category B: a SEPARATE, later mutual block that references a name from
-- the FAILED block above. `Helper`/`Main` never got defined, so `Uses`
-- referencing `Main` here hits "unknown identifier" -> autoImplicit ->
-- "Function expected", cascading independently of the positivity check.
mutual
inductive UsesA : Nat → Prop where
  | fromMain (n : Nat) : Main n → UsesA n   -- Main is UNDEFINED (block above failed)
inductive UsesB : Nat → Prop where
  | fromA (n : Nat) : UsesA n → UsesB n
end
