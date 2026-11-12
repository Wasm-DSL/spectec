-- ============================================================
-- PART 1: a simple, non-nested type -- deriving DecidableEq just works.
-- ============================================================
set_option trace.Elab.Deriving.beq true
set_option trace.Elab.Deriving.decEq true
inductive Color where
  | red | green | blue
  deriving BEq, DecidableEq, ReflBEq, LawfulBEq

-- `decide` can prove concrete (in)equality goals, because DecidableEq
-- gives you `Decidable (a = b)` directly.
example : Color.red ≠ Color.blue := by decide

-- `==` and `=` are provably connected -- but only because we ALSO derived
-- LawfulBEq explicitly (it is not automatic from DecidableEq alone; see the
-- next section, where dropping it breaks this exact proof).
example (a b : Color) (h : a == b) : a = b := eq_of_beq h


-- ============================================================
-- PART 2: same shape, but ONLY `deriving BEq`. No DecidableEq, no LawfulBEq.
-- ============================================================

inductive Shade where
  | light | dark
  deriving BEq

#eval (Shade.light == Shade.light)   -- true, `==` still computes fine
#eval (Shade.light == Shade.dark)    -- false

-- This should fail: no LawfulBEq Shade instance exists to bridge `==` to `=`.
-- example (a b : Shade) (h : a == b) : a = b := eq_of_beq h

-- This should fail too: no Decidable (a = b) instance exists.
-- example : Shade.light ≠ Shade.dark := by decide


-- ============================================================
-- PART 3: a NESTED inductive type (Tree contains itself wrapped in List).
-- This is the exact shape lean4#2329 is about.
-- ============================================================

inductive Tree where
  | leaf : Nat → Tree
  | node : List Tree → Tree
  deriving BEq   -- works: BEq's deriving handler does support nesting

#eval Tree.node [Tree.leaf 1, Tree.leaf 2] == Tree.node [Tree.leaf 1, Tree.leaf 2]  -- true

-- Uncomment this to see the deriving handler fail on the SAME type for DecidableEq
-- (this is the real error, from actually running it):
--   error: None of the deriving handlers for class `DecidableEq` applied to `Tree2`
-- inductive Tree2 where
--   | leaf : Nat → Tree2
--   | node : List Tree2 → Tree2
--   deriving BEq, DecidableEq


-- ============================================================
-- PART 4: DecidableEq CAN be written by hand for a nested type like Tree --
-- Lean's automatic deriving handler is what can't do it, not the kernel/
-- termination checker. This is the manual-derivation route discussed on
-- PR #192 (a hand-written structural version here; the recursor-based
-- version raoxiaojia proposed there is another way to get the same result).
-- ============================================================

mutual
def decEqTree : (t1 t2 : Tree) → Decidable (t1 = t2)
  | .leaf n1, .leaf n2 =>
    if h : n1 = n2 then isTrue (by rw [h])
    else isFalse (fun heq => h (by injection heq))
  | .leaf _, .node _ => isFalse (fun h => by injection h)
  | .node _, .leaf _ => isFalse (fun h => by injection h)
  | .node l1, .node l2 =>
    match decEqTreeList l1 l2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun heq => h (by injection heq))

def decEqTreeList : (l1 l2 : List Tree) → Decidable (l1 = l2)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by injection h)
  | _ :: _, [] => isFalse (fun h => by injection h)
  | t1 :: l1, t2 :: l2 =>
    match decEqTree t1 t2, decEqTreeList l1 l2 with
    | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
    | isFalse h1, _ => isFalse (fun h => by injection h; contradiction)
    | isTrue _, isFalse h2 => isFalse (fun h => by injection h; contradiction)
end

instance : DecidableEq Tree := decEqTree

-- Now `decide` works on Tree, even though `deriving DecidableEq` couldn't
-- have produced this instance automatically:
example : Tree.node [Tree.leaf 1, Tree.leaf 2] ≠ Tree.node [Tree.leaf 1, Tree.leaf 3] := by decide
example : Tree.node [Tree.leaf 1, Tree.leaf 2] = Tree.node [Tree.leaf 1, Tree.leaf 2] := by decide
