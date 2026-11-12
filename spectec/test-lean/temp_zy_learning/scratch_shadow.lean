-- Minimal reproduction of: a hypothesis names a free variable `x`, and the
-- goal has a BOUND `x` inside an existential, purely by coincidence of
-- display text (because both trace back to the same underlying definition
-- that happens to use `x` as its binder name).

def hasProp (n : Nat) : Prop := ∃ x : Nat, x = n + 1

example (x : Nat) (hx : x = 5) : hasProp 4 := by
  unfold hasProp
  -- goal is now: ⊢ ∃ x, x = 4 + 1
  -- note the GOAL's "x" and the CONTEXT's "x" (from `(x : Nat)` above) are
  -- displayed identically, but are they the same variable?

  -- Test 1: can we supply the context's `x` (which is 5) as if it satisfies
  -- the goal's `x = 4+1` (i.e. x=5)? It should work here ONLY because the
  -- context's x really does equal 5 (via hx), NOT because of name-sharing.
  refine ⟨x, ?_⟩
  -- goal is now: ⊢ x = 4 + 1   -- this `x` is now literally the CONTEXT's x
  omega

-- Test 2: prove the SAME shape of goal but with a witness having NOTHING
-- to do with the context's `x` -- if the names were "the same variable" in
-- any real sense, this would be forced/constrained by the context. It isn't.
example (x : Nat) (hx : x = 999) : hasProp 4 := by
  unfold hasProp
  refine ⟨5, ?_⟩   -- literal 5, completely ignoring context's x (=999)
  omega

-- Test 3: closer to the actual typing_lemmas.lean situation -- a relation
-- whose own definition happens to use `rest_in` as a binder name, appearing
-- BOTH as an already-destructured context variable AND inside a fresh goal.
def relShape (a b : List Nat) : Prop :=
  ∃ rest_in supplied_in : List Nat, a = rest_in ++ supplied_in ∧ b = rest_in

example (rest_in : List Nat) (h : rest_in = [1,2,3])
    (orig : relShape [1,2,3,4,5] [1,2,3]) : relShape [9,9] [] := by
  unfold relShape
  -- goal: ∃ rest_in supplied_in, [9,9] = rest_in ++ supplied_in ∧ [] = rest_in
  -- supply witnesses UNRELATED to the context's rest_in ([1,2,3]):
  refine ⟨[], [9,9], rfl, rfl⟩
  -- proved -- the context's `rest_in` ([1,2,3]) was never touched, and the
  -- goal's `rest_in` binder was just an empty slot for ANY List Nat, here [].

#print axioms relShape

-- Test 4: the CONTRASTING case -- what Lean does when a name is actually
-- being INSERTED into the local context (via `intro`) and collides with an
-- existing one, vs. a name merely sitting, still-bound, inside a goal.
example (rest_in : List Nat) (h : rest_in = [1,2,3]) :
    ∀ rest_in : List Nat, rest_in = rest_in := by
  -- BEFORE intro: goal is `∀ rest_in, rest_in = rest_in` -- that `rest_in`
  -- is just a bound binder name, displayed as-is, no collision detected,
  -- exactly like the ∃ case above.
  intro rest_in
  -- AFTER intro: the bound `rest_in` just got ACTUALLY INSERTED into the
  -- local context, and NOW it collides with the outer `rest_in` for real.
  -- Watch what Lean does to the OLDER one:
  trace_state
  rfl

-- Test 5: does a bound variable get renamed just because a same-named free
-- variable exists SOMEWHERE in context (as with Test 3's rest_in, which was
-- NOT renamed) -- or specifically because the free variable ALSO appears as
-- a literal subterm INSIDE the printed goal expression itself (which is
-- what happens with rest_out in the real typing_lemmas.lean goal)?

-- 5a: free var `w` exists in context, but does NOT appear inside the goal's
-- own printed expression at all.
example (w : Nat) (hw : w = 100) : ∃ w : Nat, w = 4 + 1 := by
  trace_state   -- does the goal's ∃ w get renamed to w_1, or stay w?
  exact ⟨5, rfl⟩

-- 5b was flawed: writing `∃ w, ... w ...` directly in source text means
-- every `w` inside is ALREADY the bound one (lexical shadowing at parse
-- time) -- there's no way to reference the OUTER free `w` from inside via
-- the bare name, so it never actually tested what I intended.

-- 5c: replicate the REAL mechanism -- a `def` whose body binds `rest_out`
-- internally, called with an ARGUMENT that itself contains a genuinely
-- FREE `rest_out` from the caller's scope, then unfolded so the free
-- occurrence and the definition's own bound name end up substituted
-- into the same printed expression together.
def foo (a : Nat) : Prop := ∃ rest_out : Nat, a = rest_out + 1

example (rest_out : Nat) (h : rest_out = 100) : foo (rest_out + 5) := by
  unfold foo
  trace_state   -- does the def's OWN bound `rest_out` get renamed now,
                -- since the ARGUMENT substituted in contains a free
                -- `rest_out` sitting right next to it?
  exact ⟨rest_out + 4, by omega⟩
