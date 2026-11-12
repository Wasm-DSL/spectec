import Mathlib.Tactic

inductive FruitKind where
  | apple
  | pear
  | banana

#print FruitKind.recOn
#print FruitKind.casesOn

-- Now a RECURSIVE type, so we can see how casesOn handles a constructor
-- that has a recursive field (does it get an ih slot or not?)
inductive PearStack where
  | empty
  | onePear (rest : PearStack)

#print PearStack.rec
#print PearStack.recOn
#print PearStack.casesOn
