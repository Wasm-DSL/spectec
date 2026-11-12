import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   PART 1: a crash course on `revert`

   `revert h` takes a hypothesis OUT of the local context and reattaches
   it to the goal as the antecedent of an implication (or, for a plain
   variable rather than a proof, as a `∀`). It is exactly the inverse of
   `intro` -- `intro` moves a leading `∀`/`→` out of the goal and into
   context; `revert` moves something FROM context back INTO the goal. ═══ -/

-- 1.1 -- the simplest possible case: revert one ordinary hypothesis.
example (n : Nat) (h : n > 0) : n ≠ 0 := by
  trace_state
  -- n : ℕ, h : n > 0 ⊢ n ≠ 0
  revert h
  trace_state
  -- n : ℕ ⊢ n > 0 → n ≠ 0        -- `h` is gone from context, folded
  --                                 into the goal as an antecedent
  intro h
  trace_state
  -- n : ℕ, h : n > 0 ⊢ n ≠ 0     -- back to exactly where we started
  omega

-- 1.2 -- reverting several hypotheses at once builds a chain of nested
-- implications, in the SAME order you name them.
example (a b : Nat) (h1 : a > 0) (h2 : b > 0) : a + b > 0 := by
  revert h1 h2
  trace_state
  -- a b : ℕ ⊢ a > 0 → b > 0 → a + b > 0
  omega

-- 1.3 -- THE crucial subtlety: reverting a plain VARIABLE also reverts
-- anything ELSE whose type depends on it, automatically -- even things
-- you never named. This is the exact mechanism that made `hm` disappear
-- in the `Even`/`generalizing` discussion.
example (n : Nat) (hn : n > 0) (m : Nat) (hm : m = n + 1) : m > 1 := by
  trace_state
  -- n : ℕ, hn : n > 0, m : ℕ, hm : m = n + 1 ⊢ m > 1
  revert n
  trace_state
  -- BOTH hn and hm got swept along too, even though only `n` was named
  -- -- because both of their TYPES mention `n`. `m` stays exactly where
  -- it is, since nothing we reverted depends on IT.
  intro n hn hm
  omega

-- 1.4 -- `revert` really is exactly the inverse of `intro`: reverting
-- then immediately re-introducing the SAME name gets you back to a
-- state that finishes the same way.
example (n : Nat) (h : n > 0) : n ≠ 0 := by
  revert h
  intro h
  omega

/- ═══════════════════════════════════════════════════════════════════════
   PART 2: `induction ... generalizing x` versus manual
   `revert x; induction ... <;> intro x ...`
   ═══════════════════════════════════════════════════════════════════════ -/

inductive EvenPred : Nat → Prop where
  | zero    : EvenPred 0
  | add_two : ∀ k : Nat, EvenPred k → EvenPred (k + 2)

-- Version A: using `generalizing`.
theorem versionA (n m : Nat) (hm : m = 2 * n + 1) (hev : EvenPred m) : False := by
  induction hev generalizing n with
  | zero =>
    trace_state
    exact absurd hm (by omega)
  | add_two k hk ih =>
    trace_state
    exact ih (n - 1) (by omega)

-- Version B: a NAIVE manual attempt -- revert n, induct, and reintroduce
-- ONLY n. This does NOT match version A: watch `hm` get left behind,
-- still folded into the goal as an un-introduced implication.
theorem versionB (n m : Nat) (hm : m = 2 * n + 1) (hev : EvenPred m) : False := by
  revert n
  induction hev with
  | zero =>
    intro n
    trace_state
    -- ⊢ 0 = 2 * n + 1 → False   -- `hm` never got its own name back!
    intro hm
    exact absurd hm (by omega)
  | add_two k hk ih =>
    intro n
    trace_state
    intro hm
    exact ih (n - 1) (by omega)

-- Version C: the CORRECT manual equivalent -- reintroduce n AND hm,
-- since `revert n` swept `hm` along too (exactly Part 1.3's lesson,
-- applied here).
theorem versionC (n m : Nat) (hm : m = 2 * n + 1) (hev : EvenPred m) : False := by
  revert n
  induction hev <;> intro n hm
  case zero =>
    trace_state
    exact absurd hm (by omega)
  case add_two k hk ih =>
    trace_state
    exact ih (n - 1) (by omega)

-- Confirm versionA and versionC are genuinely the SAME proof term, not
-- just similarly-shaped goals along the way.
example : versionA = versionC := rfl
