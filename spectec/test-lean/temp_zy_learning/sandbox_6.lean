/-
  Investigating how Lean `structure` interacts with `deriving Inhabited, BEq,
  DecidableEq, ReflBEq, LawfulBEq`, to check whether structures can be
  classified by the same self-nesting / bad-type-reference analysis the
  backend already applies to `inductive` (VariantT) types, rather than being
  blanket-downgraded unconditionally.
-/

/- ── 1. Baseline: a plain, non-nested structure ─────────────────────────── -/
-- Expectation: succeeds trivially, same as a simple inductive.
structure Plain where
  x : Nat
  y : Bool
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

#check (inferInstance : DecidableEq Plain)


/- ── 2. Structure referencing an already-bad (non-DecidableEq) type ────── -/
-- Mirrors `typ_refs_bad_type`: a field of a type that itself lacks
-- DecidableEq because IT nests itself under a container.
inductive SelfNested where
  | leaf
  | node (children : List SelfNested)
deriving Inhabited, BEq  -- can't add DecidableEq here -- known nested-inductive limitation

structure WrapsBadType where
  inner : SelfNested
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

#check (inferInstance : DecidableEq WrapsBadType)


/- ── 3. Can a `structure` be directly self-referential at all? ─────────── -/
-- Does Lean's `structure` command even permit a field whose type mentions
-- the structure itself, the way `inductive` permits `node : List T → T`?
structure DirectlyRecursive where
  val : Nat
  children : List DirectlyRecursive
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

#check (inferInstance : DecidableEq DirectlyRecursive)


/- ── 4. Same self-nesting shape, but as `inductive` not `structure` ────── -/
-- For direct comparison against #3's error message -- is this the same
-- underlying "nested inductive" limitation, or something structure-specific?
inductive InductiveSelfNested where
  | leaf (val : Nat)
  | node (children : List InductiveSelfNested)
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

#check (inferInstance : DecidableEq InductiveSelfNested)
