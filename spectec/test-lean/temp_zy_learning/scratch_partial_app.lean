import Mathlib.Tactic

inductive FruitKind where
  | apple
  | pear
  | banana

-- ═══ Part 1: watch the TYPE narrow, one argument at a time ═══

#check @FruitKind.rec
-- @FruitKind.rec : {motive : FruitKind → Sort u_1} →
--   motive FruitKind.apple → motive FruitKind.pear → motive FruitKind.banana →
--   (t : FruitKind) → motive t

#check @FruitKind.rec (motive := fun _ => Bool)
-- supplying `motive` peels off the FIRST binder, and substitutes
-- `motive := fun _ => Bool` into everything after it -- ordinary Pi-type
-- instantiation, nothing recursor-specific yet.

#check @FruitKind.rec (motive := fun _ => Bool) true
-- second binder peeled off (needed type `Bool`, `true` supplied).

#check @FruitKind.rec (motive := fun _ => Bool) true true
-- third binder peeled off.

#check @FruitKind.rec (motive := fun _ => Bool) true true false
-- fourth binder peeled off. What's LEFT at this point?

#check @FruitKind.rec (motive := fun _ => Bool) true true false .apple
-- fifth and FINAL argument -- the major premise. THIS is the one that
-- triggers iota-reduction, not merely "peels off an arrow."

-- ═══ Part 2: can you apply arguments directly to the raw Pi-TYPE
-- expression itself, instead of to `FruitKind.rec`? ═══

#check
  (
    {motive : FruitKind → Sort 1} →
      motive FruitKind.apple → motive FruitKind.pear → motive FruitKind.banana →
      (t : FruitKind) → motive t
  )
  (motive := fun _ => Bool) true true false FruitKind.apple

-- Even dropping the named-argument syntax entirely -- pure positional
-- application of the same expression:
#check
  (
    {motive : FruitKind → Sort 1} →
      motive FruitKind.apple → motive FruitKind.pear → motive FruitKind.banana →
      (t : FruitKind) → motive t
  )
  (fun _ => Bool) true true false FruitKind.apple
