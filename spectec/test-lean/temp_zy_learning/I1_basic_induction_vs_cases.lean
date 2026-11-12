import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON I1: `induction` vs `cases` -- what each one actually does under
   the hood, in terms of the recursors from the R-series.

   Real world: same PearStack from R3 -- empty, or one more pear on a
   smaller stack. -/

inductive PearStack where
  | empty
  | onePear (rest : PearStack)

/- `cases s` case-splits on WHICH constructor built `s`, giving you the
   raw fields -- nothing more. `induction s` does the same case-split,
   but ALSO hands you an "ih": the same goal, already proven for the
   smaller sub-piece. That's the entire difference, and it's EXACTLY the
   `.rec` vs `.casesOn` distinction from R3, just invoked through a
   tactic instead of written as a raw term application. -/

theorem cases_has_no_ih (s : PearStack) : True := by
  cases s with
  | empty => trivial
  | onePear rest =>
    -- try uncommenting the next line -- there's no `ih` in scope to find:
    -- exact ih
    trivial

theorem induction_has_ih (s : PearStack) : True := by
  induction s with
  | empty => trivial
  | onePear rest ih =>
    -- `ih : True` is genuinely available here (trivial content in this
    -- example since the goal is just `True`, but the BINDING exists --
    -- that's the point).
    trivial

/- Let's make the ih's presence matter, with a real (non-trivial) goal:
   every PearStack, by construction, has a non-negative pear count. Not
   a deep fact for `Nat`, but structured so `cases` genuinely CAN'T do it
   in one step (no way to talk about "the count for the smaller stack")
   while `induction` can. -/
def pearCount : PearStack → Nat
  | .empty => 0
  | .onePear rest => pearCount rest + 1

theorem count_pos_or_zero (s : PearStack) : pearCount s = 0 ∨ pearCount s > 0 := by
  induction s with
  | empty => left; rfl
  | onePear rest ih =>
    -- `ih : pearCount rest = 0 ∨ pearCount rest > 0` -- USE it to avoid
    -- re-deriving anything about `rest` from scratch:
    right
    rw [pearCount] at *
    simp

/- ─── Confirm this is literally `.rec`/`.casesOn` under the hood ───
   `#print` the compiled proof term for each theorem above and look at
   which eliminator got used. -/
set_option pp.proofs true in
#print cases_has_no_ih
set_option pp.proofs true in
#print induction_has_ih
/- `cases_has_no_ih`'s proof term is built via `PearStack.casesOn`.
   `induction_has_ih`'s is built via `PearStack.rec` (or a closely related
   `brecOn`-based recursor Lean sometimes prefers internally for
   efficiency -- the concept is identical either way: minor premises PLUS
   ih's, not just minor premises). This is the same relationship as R1's
   `match` example, just now via tactics instead of surface pattern
   syntax: `cases`/`induction` are FRONT-ENDS that build a `.casesOn`/
   `.rec` application for you, so you don't have to write the raw
   `PearStack.rec (motive := ...) ... ...` term by hand every time. -/

/- One more angle on the same point: build `induction_has_ih`'s theorem
   by hand, with the raw recursor, and confirm it's the SAME proof. -/
theorem induction_has_ih_manual (s : PearStack) : True :=
  PearStack.rec (motive := fun _ => True) trivial (fun _rest _ih => trivial) s

#print axioms induction_has_ih_manual
#print PearStack.casesOn
set_option pp.explicit true
#print PearStack.casesOn
