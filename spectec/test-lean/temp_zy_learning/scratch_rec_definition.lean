import Mathlib.Tactic

inductive FruitKind where
  | apple
  | pear
  | banana

-- Does FruitKind.rec have a printable body, like an ordinary `def`?
#print FruitKind.rec

-- Compare directly to an ordinary def, which DOES have a body:
def isSoft : FruitKind → Bool
  | .apple => true
  | .pear => true
  | .banana => false

#print isSoft

-- What does Lean call FruitKind.rec, structurally? Check its `#check` and
-- whether `#print` treats it differently from a `theorem`/`def`.
#check @FruitKind.rec
