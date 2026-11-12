import Mathlib.Tactic   -- only needed for Experiment 5's `List.reverseRecOn`

-- Three reasons you end up supplying a motive explicitly instead of letting `induction`
-- infer it for you, each demonstrated below:
--   Situation A (Experiments 1, 2, 4): the type is part of a `mutual` block, so the
--     combined recursor needs a motive for every sibling type, not just the one you care
--     about — plug the ones you don't need with something trivial (`fun _ _ => True`).
--   Situation B (Experiment 5): the type's DEFAULT recursion order doesn't match how your
--     proof needs to consume the structure — reach for an alternate eliminator (with its
--     own motive) built for the traversal you actually need.
--   Situation C (Experiment 6): the motive Lean auto-infers from your goal is too WEAK,
--     because some other variable that also needs to vary across the recursive calls got
--     left out of it — fix with `induction ... generalizing`.

-- Toy model of `Instr_ok` / `Instrs_ok` (wasm2.0.lean), minimal enough to poke at directly.
-- `A` stands in for `Instr_ok` (single-instruction typing), `B` stands in for `Instrs_ok`
-- (instruction-*sequence* typing). They are declared together in one `mutual ... end` block,
-- exactly like the real ones, because `B.single` recurses into `A` and (in the real spec)
-- `A`'s block/loop/if cases recurse back into `B`.
mutual
inductive A : List Nat → Prop where
  | base : A []            -- a constructor with a plain (non-recursive-into-A) index: []
  | wrap : A [1] → A [2]   -- recursive into A, index is a literal list, not built from A/B

inductive B : List Nat → Prop where
  | empty : B []
      -- index term: `[]`, a bare constructor application (List.nil). Easy to match against.
  | single : A l → B l
      -- recurses into the SIBLING type A, not into B itself — this is why the combined
      -- recursor `B.rec` needs a motive for A too, even though we only care about B.
  | seq : B l1 → B l2 → B (l1 ++ l2)
      -- index term: `l1 ++ l2`, an application of the ORDINARY FUNCTION `List.append`.
      -- Not a constructor application — this is the one that causes all the trouble below.
end


-- ============================================================================
-- Experiment 1: plain `induction` refuses outright on a mutual-inductive target.
-- ============================================================================
-- Lean's `induction` compiles to the full recursor `B.rec`, which (because A/B are mutual)
-- requires motives for BOTH types simultaneously. `induction` won't guess a placeholder
-- motive for the sibling `A` on your behalf, so it just refuses and points you at `cases`.
example (h : B ([] : List Nat)) : True := by
  induction h  -- error: "The `induction` tactic does not support the type `B` because
               --         it is mutually inductive. Hint: Consider using `cases` instead"
  trivial


-- ============================================================================
-- Experiment 2: `cases` accepts the mutual type, but then chokes on the `seq` case.
-- ============================================================================
-- `cases` compiles to `B.casesOn` (one-step split, no induction hypothesis, so it never
-- needs a sibling motive — that's why it's accepted here where `induction` wasn't).
-- But it still has to reconcile our concrete index `[]` against every constructor's own
-- declared index term. For `empty` (index `[]`) and `single` (index `l`, already a
-- variable) this is trivial. For `seq` (index `l1 ++ l2`) it is NOT: `List.append` is not
-- a constructor, so there is no injectivity/no-confusion principle telling Lean how (or
-- whether) `[] = l1 ++ l2` can hold. It can neither ratify nor discard the branch, so:
example (h : B ([] : List Nat)) : True := by
  cases h
  -- error on the `seq` alternative: "Dependent elimination failed: Failed to solve
  --   equation  [] = l1✝.append l2✝"
  all_goals trivial


-- ============================================================================
-- Experiment 3: contrast — if the index is ALREADY a bare variable, there is nothing to
-- solve at all, so `cases` (and even real `induction`, given a motive for A) works fine.
-- ============================================================================
-- No unification is attempted here: each branch just SUBSTITUTES `l` by that constructor's
-- own index term (`[]`, `l` itself, or `l1 ++ l2`) — a free rename, not an equation to prove.
example (l : List Nat) (h : B l) : l = l := by
  cases h with
  | empty => trivial
  | single _ => trivial
  | seq _ _ => trivial   -- `l` has simply become `l1 ++ l2` in this branch; nothing to check
  -- (uncomment to see it really does work with induction too, given a dummy motive for A)
  -- induction h using B.rec (motive_1 := fun _ _ => True) with
  -- | empty => trivial | single _ _ => trivial | seq _ _ ih1 ih2 => trivial
  -- | base => trivial | wrap _ _ => trivial


-- ============================================================================
-- Experiment 4: the actual fix — turn Experiment 2's situation into Experiment 3's.
-- ============================================================================
-- Two DIFFERENT techniques are stacked here — don't conflate them:
--
--   (i) `generalize hl0 : [] = l at h` replaces the concrete index `[]` inside `h`'s type
--   by a FRESH VARIABLE `l`, keeping the old value around separately as an ordinary
--   hypothesis `hl0 : [] = l`. This is a PREREQUISITE step — it doesn't touch any motive
--   at all, it just turns a non-variable index into a variable one so that induction can
--   be attempted in the first place (Experiment 3's precondition). This is NOT the same
--   move as Situation C's `generalizing` clause below in Experiment 6 — that one keeps an
--   ALREADY-variable parameter general across the recursion; this one converts a fixed
--   literal into a variable to begin with. Lean-side counterpart of Coq's
--   `dependent induction`, which does the same "generalize indices into equalities" move
--   internally.
--
--   (ii) `(motive_1 := fun _ _ => True)` is SITUATION A: `B.rec` is the combined
--   recursor for the mutual pair `A`/`B`, so it demands a motive for `A` too, even though
--   this proof has nothing to say about `A`-derivations. `fun _ _ => True` is the
--   cheapest possible `Sort`-valued placeholder (`True : Prop`, and `Prop = Sort 0`), so
--   every obligation attached to `A`'s constructors (`base`, `wrap`) collapses to
--   something `trivial` closes with zero work — see the `| base =>` / `| wrap _ _ =>`
--   cases below.
#check B.rec
#check A.rec

example (h : B ([] : List Nat)) : True := by
  generalize hl0 : ([] : List Nat) = l at h
  -- Now `h : B l` — exactly Experiment 3's shape — so `induction` (using the combined
  -- recursor, with a throwaway motive for the sibling `A`) goes through with no
  -- unification failure: the `seq` case's goal is stated generically over `l1 ++ l2`,
  -- never forced to equal `[]` at the elaborator level.
  induction h using B.rec (motive_1 := fun _ _ => True) with
  | empty => trivial
  | single _ _ => trivial
  | seq hb1 hb2 ih1 ih2 =>
      -- Here `hl0` has been substituted along with `l`, so it now reads
      -- `hl0 : [] = l1 ++ l2`. This is just an ordinary PROPOSITION now — nothing the
      -- elaborator needed to solve automatically, only something *we* discharge by hand
      -- using the real fact about `List.append`, exactly mirroring Coq's
      -- `destruct_list_eq` / `empty_append` lemma.
      obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp hl0.symm
      trivial
  | base => trivial
  | wrap _ _ => trivial


-- ============================================================================
-- Experiment 5 (SITUATION B): the default recursion order is the wrong shape.
-- ============================================================================
-- `List.rec`'s default motive/recursor only supports LEFT-to-right induction (`cons`
-- peels off the FIRST element). The real Coq proof `construct_ais_vals` needs the
-- opposite: `induction v_vals using last_ind` peels off the LAST element each step.
-- No amount of `motive_1 :=`-style plugging fixes this — the type's own `List.rec` is
-- simply the wrong eliminator for that proof shape. Fix: use a DIFFERENT eliminator
-- built for that traversal (Mathlib's `List.reverseRecOn`), and let Lean infer or supply
-- ITS motive instead of `List.rec`'s.
#check @List.reverseRecOn
-- {motive : List α → Sort u} → (l : List α) →
--   motive [] → ((l : List α) → (a : α) → motive l → motive (l ++ [a])) → motive l
-- ^ same overall SHAPE as List.rec (a motive, a `[]` base case, a step case, a final
--   answer) — just built around `l ++ [a]` instead of `a :: l`.
example (l : List Nat) : l.reverse.reverse = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
      -- here the IH `ih : xs.reverse.reverse = xs` is about the list with its LAST
      -- element `x` already stripped off — exactly the shape `construct_ais_vals` needs
      -- when consuming `v_vals`/`ts` from the right.
      simp [ih]


example (l : List Nat) : l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp

-- ============================================================================
-- Experiment 6 (SITUATION C): the auto-inferred motive is too WEAK.
-- ============================================================================
-- When you write `induction l`, Lean builds the motive by abstracting your CURRENT GOAL
-- over `l`. If some other variable (`n` here) that also needs to change across the
-- recursive calls is left OUT of that abstraction — because it just happens to already
-- be fixed/shared in your current goal — the resulting IH is too specific to apply at
-- the recursive call. `generalizing` folds that variable into the motive too, with no
-- manual motive-writing required. This is exactly the pattern behind the real proofs'
-- `specialize (IHHempty1 t1s t_2_lst ...)` lines — applying the Coq IH at DIFFERENT
-- arguments than the ones in the original goal only works because the induction was
-- general enough over those arguments in the first place.
example (l : List Nat) (n : Nat) : l.length + n = n + l.length := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
      -- `ih : ∀ n, t.length + n = n + t.length` — genuinely usable at whatever `n` shows
      -- up here, not frozen at the outer goal's original `n`.
      simp only [List.length_cons]; omega

-- Contrast: WITHOUT `generalizing n`, the motive Lean infers is only
--   `fun l => l.length + n = n + l.length`  (for the SAME fixed outer `n` throughout),
-- so `ih` in the `cons` case would be `t.length + n = n + t.length` — true, but only ever
-- usable at that one `n`, not a genuine induction hypothesis you could reuse elsewhere.
-- Uncomment to see it still happens to go through here (this particular goal doesn't
-- NEED the extra generality) — but in general, dropping `generalizing` is exactly what
-- produces the "my IH isn't strong enough" experience.
-- example (l : List Nat) (n : Nat) : l.length + n = n + l.length := by
--   induction l with
--   | nil => simp
--   | cons a t ih => simp only [List.length_cons]; omega
