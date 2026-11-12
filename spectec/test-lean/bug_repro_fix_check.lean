/-
FIX CHECK for bug.lean.

This is bug.lean's own minimal repro (`A`/`B`, both with a `frame` case,
6 fields vs 2 fields, `A` declared first) with exactly the fix backend.ml now
applies: each colliding case id gets its own inductive's name prepended
(`frame` -> `A_frame` / `B_frame`), the same transformation
create_relations_inductive_case performs for Instr_ok2.frame / Instrs_ok2.frame
in the real spec (see whole_file_analyses.gather_colliding_relation_case_names).

Root cause recap (see bug.lean for the full trace): `induction ... using`
resolves each alternative's expected binder count via `getAltNumFields`, which
searches `elimInfo.altsInfo` -- built by walking every constructor of every
type in the *whole mutual block* -- by bare, unqualified constructor name.
With two constructors both named `frame`, that search returns the first match
by declaration order regardless of which alternative is actually being
processed, so `Instrs_ok2.frame` (10 fields) wrongly gets `introN 14`
(the first, unrelated `Instr_ok2.frame`'s field count) and crashes.

Once the names no longer collide, `elimInfo.altsInfo`'s per-name lookup is
unambiguous again, `getAltNumFields` returns the correct count for whichever
alternative is being processed, and `introN` stops over/under-asking for
binders. Compare against bug.lean, unmodified: that file reproduces the crash
with the *same* structure (mutual block, first type's case has more fields
than the second type's same-named case) using bare `frame` for both. Here,
renaming to `A_frame` / `B_frame` is the only change, and it's enough on its
own -- confirming the fix is exactly "make the mutual-block-wide constructor
namespace unique," not something about `motive_2`, `True`, or `Nat`.

Result: only linter warnings (unused binder names, `sorry`) below, no error.
-/

mutual
inductive A : Nat → Prop where
  | mk    : A 0
  | A_frame : ∀ n1 n2 n3 n4 n5 : Nat, A n1 → A n1   -- 6 fields; declared FIRST

inductive B : Nat → Prop where
  | base  : B 0
  | B_frame : ∀ n : Nat, B n → B n                   -- 2 fields; declared SECOND
end

example (n : Nat) (h : A n) : True := by
  induction h using A.rec (motive_2 := fun _ _ => True)
  all_goals sorry
