import Mathlib.Tactic

/- What goes wrong when I2's fixes are skipped -- companion file to
   I2_generalizing.lean, Q4. Both theorems below are genuinely stuck
   (real `sorry`s, not just inelegant proofs) -- confirmed by compiling. -/

inductive PearStack where
  | empty
  | onePear (rest : PearStack)

def pearCount : PearStack → Nat
  | .empty => 0
  | .onePear rest => pearCount rest + 1

/- ═══ Broken companion to `with_extra_fact`: what if the h/fixed
   connection is thrown away (e.g. via `clear`) before inducting? ═══

   Note the target here is `n = pearCount fixed`, NOT the tautological
   `n = 0 ∨ n > 0` from the original -- that one holds for every `n`
   regardless of any hypothesis, so losing `h` wouldn't actually break
   anything visibly. `n = pearCount fixed` is a real claim (false for,
   say, n := 5, fixed := .empty), so losing the connection truly strands
   you. -/
theorem with_extra_fact_BROKEN (fixed : PearStack) (n : Nat) (h : pearCount fixed = n) :
    n = pearCount fixed := by
  clear h
  induction fixed with
  | empty =>
    trace_state
    -- n : ℕ ⊢ n = pearCount PearStack.empty
    -- i.e. ⊢ n = 0, for a COMPLETELY ARBITRARY n. Obviously false in
    -- general (n could be 5, 100, anything) -- genuinely unprovable,
    -- not just inconvenient.
    sorry
  | onePear rest ih =>
    trace_state
    -- ih : n = pearCount rest ⊢ n = pearCount rest.onePear
    -- even granting ih, this doesn't follow: n = pearCount rest tells
    -- you nothing about how n relates to pearCount rest + 1.
    sorry

/- ═══ Broken companion to `narrow_ih_demo`: PearStack's constructors
   only ever have ONE recursive field, so a narrow ih there can always
   be resolved anyway (injection+subst peels exactly one layer, always
   cleanly, regardless of depth) -- it never actually gets you stuck.
   To see a genuinely UNPROVABLE narrow ih -- the real
   `instrs_seq_typing_inversion` shape -- you need a BRANCHING
   structure. `List.append` is the smallest one that reproduces it. ═══ -/
theorem list_narrow_ih_BROKEN (xs : List Nat) :
    xs = [1, 2] → xs.length = 2 := by
  intro hxs
  generalize eq1 : xs = ys at hxs ⊢
  induction ys with
  | nil => exact absurd hxs.symm (by simp)
  | cons y tl ih =>
    trace_state
    cases tl with
    | nil => simp_all
    | cons y2 tl2 =>
      trace_state
      -- REAL captured ih: `ih : xs = y2 :: tl2 → y2 :: tl2 = [1, 2] → (y2 :: tl2).length = 2`
      -- REAL captured hxs: `hxs : y :: y2 :: tl2 = [1, 2]` (after cases)
      -- `ih` is gated on `xs = y2 :: tl2` -- i.e. the WHOLE original list
      -- equaling just its own tail. That's not what `hxs` gives us
      -- (hxs relates xs to the FULL y :: y2 :: tl2, not to y2 :: tl2 alone).
      -- There is no way to satisfy ih's premise here -- genuinely stuck,
      -- exactly the shape of the real `seq`/`cons` trap from I5's
      -- `attempt1`.
      sorry

/- ═══ Two ways to actually solve `list_narrow_ih_BROKEN` ═══ -/

-- Fix 1 -- the I5-style fix: restate the claim as a fully GENERAL
-- auxiliary lemma, quantifying the outer `n1`/`n2` (I5's `n`/`ns`)
-- INSIDE the statement, ahead of the induction, so the ih that comes
-- out is genuinely about `tl` itself -- never gated on the original
-- `xs` at all, because nothing here ever mentions `xs`.
theorem list_length_two_general :
    ∀ (ys : List Nat), ∀ (n1 n2 : Nat), ys = [n1, n2] → ys.length = 2 := by
  intro ys
  induction ys with
  | nil =>
    intro n1 n2 h
    simp at h
  | cons y tl ih =>
    intro n1 n2 h
    -- REAL captured ih: `∀ n1 n2, tl = [n1, n2] → tl.length = 2` --
    -- genuinely about `tl`, no outer `xs` in sight to gate anything on.
    trace_state
    cases tl with
    | nil => simp at h
    | cons y2 tl2 =>
      cases tl2 with
      | nil => simp_all
      | cons y3 tl3 => simp at h

-- `list_narrow_ih_BROKEN`'s original goal, recovered as a one-line
-- corollary -- exactly `attempt2_fixed := fun h => general (n :: ns) h n ns rfl`
-- from I5, just with `xs`/`1`/`2` in place of `n :: ns`/`n`/`ns`.
theorem list_narrow_ih_FIXED (xs : List Nat) : xs = [1, 2] → xs.length = 2 :=
  fun h => list_length_two_general xs 1 2 h

-- Fix 2 -- the simpler observation this toy example invites, that the
-- REAL `instrs_seq_typing_inversion` doesn't have the luxury of: since
-- `hxs` already pins `xs` down to one EXACT, fully concrete list, no
-- induction is needed at all -- `subst` and you're done. `generalize`
-- + `induction` was never the right tool here in the first place; it
-- was only ever useful for DEMONSTRATING the trap.
theorem list_narrow_ih_trivial_fix (xs : List Nat) : xs = [1, 2] → xs.length = 2 := by
  intro hxs
  subst hxs
  rfl
