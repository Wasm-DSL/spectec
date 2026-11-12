import Mathlib.Tactic

inductive PearStack where
  | empty
  | onePear (rest : PearStack)

noncomputable def pearCount_direct : PearStack → Nat := fun s =>
  PearStack.rec (motive := fun _pearstack => Nat) 0 (fun _rest ih => ih + 1) s

def s0 : PearStack := .empty
def s1 : PearStack := PearStack.onePear s0
def s2 : PearStack := PearStack.onePear s1
def s3 : PearStack := PearStack.onePear s2

def stackOf3 := PearStack.onePear (PearStack.onePear (PearStack.onePear .empty))

example : stackOf3 = s3 := rfl

-- Step 0: delta-unfold pearCount_direct + beta-substitute s := s3
example : pearCount_direct s3
        = PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s3
        := rfl

-- Step 1: iota-reduction on s3 = onePear s2.
-- The minor premise (fun _rest ih => ih + 1) gets applied to TWO arguments:
-- the raw field `s2`, AND the recursive `.rec` call on `s2` (the ih) --
-- NOT to the original s3, and NOT to just one argument.
example : PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s3
        = (fun _rest ih => ih + 1) s2
            (PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s2)
        := rfl

-- Step 1b: beta-reduce that application (the lambda ignores _rest, uses ih)
example : (fun _rest ih => ih + 1) s2
            (PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s2)
        = (PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s2) + 1
        := rfl

-- Step 2: same move, one level down, on s2 = onePear s1
example : PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s2
        = (PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s1) + 1
        := rfl

-- Step 3: same move, on s1 = onePear s0
example : PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s1
        = (PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s0) + 1
        := rfl

-- Step 4: s0 = .empty -- iota picks the FIRST minor premise directly (0
-- fields, so no wrapper application at all, just the bare value `0`)
example : PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) s0
        = 0
        := rfl

-- Fully chained, confirming the whole thing end to end:
example : pearCount_direct stackOf3 = 3 := rfl

-- And the literal substituted arithmetic chain, all in one:
example : pearCount_direct s3 = ((0 + 1) + 1) + 1 := rfl
