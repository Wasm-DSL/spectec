-- Two standard ways to recover `fun_minus` (the broken relation from
-- scratch_minus_recs_pipeline_repro.lean / repro2.lean) without hitting the
-- strict positivity error, while keeping exactly the same input/output
-- behaviour. See that file + the accompanying discussion for the original:
--
--   inductive fun_minus_before_fun_minus_case_3 : List tag → List Nat → Prop
--   inductive fun_minus : List tag → List Nat → Option (List tag × List Nat) → Prop
--     -- case_3 negates fun_minus_before_..., which itself still contains a
--     -- live reference to fun_minus -> non strictly positive.
--
-- The root cause: fun_minus's "keep" clause destructures the recursive
-- call's *value* (var_0 ≠ none, then Option.get! var_0) instead of just
-- using it structurally, so the auxiliary "before" guard can't safely drop
-- the reference to fun_minus, and negating it is what breaks positivity.
--
-- Both fixes below sidestep the problem the same fundamental way: they
-- never declare a *value-producing* function as an `inductive ... Prop`
-- in the first place, so there's nothing for the positivity checker to
-- reject.

inductive tag : Type where
  | LEFT : tag
  | RIGHT (_ : Nat) : tag
deriving Inhabited, BEq, DecidableEq, Repr

-- ===========================================================================
-- Method 1 -- just write it as an ordinary structurally-recursive `def`.
--
-- This is the "obvious" fix for this particular function: it's genuinely
-- structurally recursive (both lists shrink by exactly one element per
-- step), so Lean's own equation compiler can compile it directly, no
-- relation/graph encoding needed at all. This is what `hint(recfunc)` was
-- meant to enable for `minus_recs` in the real pipeline.
-- ===========================================================================

def minusFn : List tag → List Nat → Option (List tag × List Nat)
  | [], [] => some ([], [])
  | tag.LEFT :: ts, _ :: ns => minusFn ts ns
  | tag.RIGHT x :: ts, n :: ns =>
    match minusFn ts ns with
    | some (ts', ns') => some (tag.RIGHT x :: ts', n :: ns')
    | none => none
  | _, _ => none

#eval minusFn [tag.LEFT, tag.RIGHT 7, tag.LEFT, tag.RIGHT 9] [1, 2, 3, 4]
-- some ([tag.RIGHT 7, tag.RIGHT 9], [2, 4])
#eval minusFn [tag.LEFT] [1, 2]
-- none (mismatched lengths)

-- ===========================================================================
-- Method 2 -- Bove-Capretta: split into a value-free "domain" predicate,
-- then recurse on a *proof* of that predicate.
--
-- In Lean 4 specifically, the domain predicate has to be built from `Acc`
-- (built-in, single-constructor) rather than a hand-rolled multi-constructor
-- Prop -- Lean only allows eliminating into actual data (not just another
-- Prop) from a Prop with exactly one constructor, which is precisely what
-- `Acc` is engineered for. (A naive 3-constructor `MinusDom` Prop compiles
-- fine on its own, but then trying to pattern-match on a proof of it to
-- produce a `List tag × List Nat` fails with "recursor can only eliminate
-- into Prop".)
--
-- This is the more general technique -- it still works even when the
-- recursion isn't obviously structural to Lean's equation compiler (e.g.
-- nested/mutual/nonstandard recursion schemes), whereas Method 1 only works
-- because this particular function happens to be simply structural.
-- ===========================================================================

-- "p is the direct recursive sub-call target reached from q"
def MinusStep (p q : List tag × List Nat) : Prop :=
  ∃ t n, q = (t :: p.1, n :: p.2)

theorem minusStep_wf : WellFounded MinusStep := by
  apply Subrelation.wf (r := InvImage Nat.lt (fun p => p.1.length))
  · rintro p q ⟨t, n, rfl⟩
    simp [InvImage]
  · exact InvImage.wf _ Nat.lt_wfRel.wf

def minusOfAcc : (p : List tag × List Nat) → Acc MinusStep p → Option (List tag × List Nat)
  | ([], []), _ => some ([], [])
  | (tag.LEFT :: ts, _ :: ns), acc =>
      minusOfAcc (ts, ns) (acc.inv ⟨_, _, rfl⟩)
  | (tag.RIGHT x :: ts, n :: ns), acc =>
      match minusOfAcc (ts, ns) (acc.inv ⟨_, _, rfl⟩) with
      | some (ts', ns') => some (tag.RIGHT x :: ts', n :: ns')
      | none => none
  | (_ :: _, []), _ => none
  | ([], _ :: _), _ => none

def minusBC (ts : List tag) (ns : List Nat) : Option (List tag × List Nat) :=
  minusOfAcc (ts, ns) (minusStep_wf.apply (ts, ns))

#eval minusBC [tag.LEFT, tag.RIGHT 7, tag.LEFT, tag.RIGHT 9] [1, 2, 3, 4]
-- some ([tag.RIGHT 7, tag.RIGHT 9], [2, 4]) -- same as minusFn
#eval minusBC [tag.LEFT] [1, 2]
-- none -- same as minusFn

-- Both methods agree with each other on a spread of inputs, and by
-- construction both agree with what fun_minus's clauses were meant to say.
#eval decide (minusFn [] [] = minusBC [] [])
#eval decide (minusFn [tag.LEFT] [5,6] = minusBC [tag.LEFT] [5,6])
#eval decide (minusFn [tag.RIGHT 1, tag.RIGHT 2] [10,20] = minusBC [tag.RIGHT 1, tag.RIGHT 2] [10,20])
#eval decide (minusFn [tag.LEFT, tag.RIGHT 3] [1] = minusBC [tag.LEFT, tag.RIGHT 3] [1])
