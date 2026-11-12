import Mathlib.Tactic

inductive FruitKind where
  | apple
  | pear
  | banana

noncomputable def isSoft_direct : FruitKind → Bool := fun f =>
  FruitKind.rec (motive := fun _ => Bool) true true false f

-- Step 1: unfold `isSoft_direct` (delta-reduction) and apply the lambda
-- to `.apple` (beta-reduction). Confirm this is DEFINITIONALLY equal --
-- `rfl` only succeeds if these are the same term up to computation.
example : isSoft_direct .apple
        = FruitKind.rec (motive := fun _ => Bool) true true false .apple
        := rfl

-- Step 2: the recursor applied to a literal constructor reduces to that
-- constructor's own minor premise (iota-reduction). Confirm directly:
example : FruitKind.rec (motive := fun _ => Bool) true true false .apple
        = true
        := rfl

-- And chained straight through, confirming the whole thing end to end:
example : isSoft_direct .apple = true := rfl
