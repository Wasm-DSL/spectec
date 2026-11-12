/-
FOLLOW-UP CHECK for bug.lean: does the same-named-case clash still break
`induction ... using` when the two inductives are declared separately
(not bundled inside one `mutual ... end` block)?

Answer: no. `A` and `B` here both have a case named `frame` (bare, unprefixed,
unlike bug_repro_fix_check.lean) with different field counts, exactly like
bug.lean's repro -- the only change is dropping the `mutual`/`end` wrapper.
This compiles with only linter warnings, no error.

This matches bug.lean's own root-cause analysis: `getAltNumFields`'s ambiguous
search is over `elimInfo.altsInfo`, which is built by walking every
constructor of every type *in the mutual block being eliminated*. A standalone
`A.rec` only ever has `A`'s own constructors in scope, so there is no second
`frame` to collide with -- Lean's ordinary (non-mutual) `induction` a case
name lookup is already scoped to the one type being inducted on.

Practically: backend.ml's fix (Whole_file_analyses.gather_colliding_relation_case_names)
only needs to check for name collisions *within each RecD/mutual group*, not
across the whole spec -- which is what it already does. A `frame` case in one
relation and an unrelated `frame` case in a relation from a different, never
-bundled mutual block are fine as-is and don't need renaming.
-/

-- Same clashing short name "frame", but A and B are declared as two
-- separate (non-mutual) inductives, not bundled in one `mutual ... end` block.
inductive A : Nat → Prop where
  | mk    : A 0
  | frame : ∀ n1 n2 n3 n4 n5 : Nat, A n1 → A n1   -- 6 fields

inductive B : Nat → Prop where
  | base  : B 0
  | frame : ∀ n : Nat, B n → B n                   -- 2 fields

example (n : Nat) (h : A n) : True := by
  induction h using A.rec
  all_goals sorry
