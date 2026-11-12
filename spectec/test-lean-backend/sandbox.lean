inductive Color where
  | red   : Color
  | green : Color
  | blue  : Color

class Warmth (c : Color) where
  warm : Bool

instance : Warmth .red   where warm := true
instance : Warmth .green where warm := false
instance : Warmth .blue  where warm := false

def isWarm (c : Color) [Warmth c] : Bool :=
  match c with
  | .red => true               -- deconstructs; c = .red, inst still fine
  | _    => Warmth.warm c      -- catch-all; uses [Warmth c] from outer scope

#eval isWarm .red    -- true
#eval isWarm .green  -- false
#eval isWarm .blue   -- false


-- ===========================================================
-- Scenario 1: X : Type never deconstructed → REMOVE from match
-- ===========================================================

-- Uncomment to see the error (failed to synthesize BEq α✝):
-- def disjoint_broken (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
--   match X, var_0_lst with
--   | _, []          => true
--   | _, w :: w'_lst => (!List.contains w'_lst w) && disjoint_broken X w'_lst

def disjoint_ (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
  match var_0_lst with          -- X removed
  | []          => true
  | w :: w'_lst => (!List.contains w'_lst w) && disjoint_ X w'_lst

#eval disjoint_ Nat [1, 2, 3]  -- true
#eval disjoint_ Nat [1, 2, 1]  -- false


-- ===========================================================
-- Scenario 2: var_0_lst deconstructed in at least one arm → KEEP in match
-- ===========================================================
-- var_0_lst above is deconstructed into [] and w :: w'_lst — so it stays.
-- Standalone example:

def sum_list (var_0_lst : List Nat) : Nat :=
  match var_0_lst with          -- deconstructed → kept
  | []      => 0
  | n :: t  =>
    let x := n
    x + sum_list t

#eval sum_list [1, 2, 3, 4]    -- 10


-- ===========================================================
-- Scenario 3: pass-through arg, different names per clause → REMOVE + RENAME
-- ===========================================================
-- Two IL clauses name the first arg differently ('w_lst' vs 'w_lst2'),
-- but neither deconstructs it. The naive generated match has var_0 in it
-- with different pattern-bound names per arm.

-- Step A — original generated match (compiles, but var_0 should be dropped):
-- def concat_ (X : Type) (var_0 : List X) (var_1 : List (List X)) : List X :=
--   match var_0, var_1 with
--   | w_lst,  []            => w_lst
--   | w_lst2, w' :: w''_lst => concat_ X (w_lst2 ++ w') w''_lst

-- Step B — drop var_0 but forget to rename (broken):
-- def concat_ (X : Type) (var_0 : List X) (var_1 : List (List X)) : List X :=
--   match var_1 with
--   | []            => w_lst    -- ERROR: w_lst no longer in scope
--   | w' :: w''_lst => concat_ X (w_lst2 ++ w') w''_lst  -- ERROR: w_lst2 no longer in scope

-- Step C — drop var_0 AND rename w_lst → var_0, w_lst2 → var_0 (fixed):
def concat_ (X : Type) (var_0 : List X) (var_1 : List (List X)) : List X :=
  match var_1 with
  | []            => var_0                       -- w_lst  → var_0
  | w' :: w''_lst => concat_ X (var_0 ++ w') w''_lst  -- w_lst2 → var_0

#eval concat_ Nat [0] [[1, 2], [3]]  -- [0, 1, 2, 3]


def myfunc (x: Nat) : Prop :=
  match x with
  | 0 => true -> let x := false; x -> true -> true
  | _ => false -> false


-- ===========================================================
-- Scenario 4: RulePr in a def match arm body
-- ===========================================================
-- In the IL, a def clause can carry a RulePr premise — an inductive relation
-- invoked as a guard.  append_prems_to_term renders it as a function arrow:
--
--   def $f(x) = result
--     -- MyRel: (x, result)
--
-- generates:  | x_pat => MyRel x result → [result]
--
-- The match arm body has type  MyRel x result → List Nat  instead of  List Nat.
-- Lean accepts this: a Prop-valued arrow in a term position is fine.

inductive IsPositive : Nat → Prop where
  | pos : n > 0 → IsPositive n

-- Hypothetical backend output for a def with a RulePr premise:
def f_RulePr (x : Nat) : Prop :=
  match x with
  | 0     => True                     -- no premise, base case
  | n + 1 => True -> True -> let x := n; IsPositive (n + 1) → True  -- RulePr: IsPositive (n+1)

-- Lean accepts the mixed return (True vs Prop-valued arrow) because both
-- elaborate to Prop.  In practice the right-hand side of → would be the
-- actual function result type, making the whole thing a function type.


-- ===========================================================
-- Scenario 5: IterPr in a def match arm body
-- ===========================================================
-- An IterPr premise is a starred/plus-iterated check over a list.
-- append_prems_to_term renders it via create_iter_prem, which produces a
-- BoundedForall (∀ elem ∈ list, P elem).
--
--   def $g(xs) = result
--     -- (Wf: x)* {x <- xs}
--
-- generates:  | xs_pat => (∀ x ∈ xs, WfProp x) → result

inductive WfNat : Nat → Prop where
  | wf : n < 100 → WfNat n

-- Hypothetical backend output for a def with an IterPr premise:
def g_IterPr (xs : List Nat) : Prop :=
  match xs with
  | []     => True                               -- no premise on empty list
  | _ :: _ => (∀ x ∈ xs, WfNat x) → True       -- IterPr: (WfNat: x)* {x <- xs}


-- ===========================================================
-- Scenario 6: NegPr in a def match arm body
-- ===========================================================
-- A NegPr wraps an inner premise and negates it.  create_prem renders it
-- as  ¬ (inner_prem_term).
--
--   def $h(x) = result
--     -- not (x = 0)
--
-- generates:  | x_pat => ¬ (x = 0) → result
--
-- In practice the WasmSpec uses ElsePr (-- otherwise) for fallback arms
-- rather than an explicit NegPr, but NegPr is grammatically valid in a def.

def h_NegPr (x : Nat) : Prop :=
  match x with
  | 0     => True              -- base case, no premise
  | n + 1 => ¬ (n + 1 = 0) → True   -- NegPr (IfPr (x ≠ 0))
