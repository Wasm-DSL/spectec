import Mathlib.Tactic

-- Are Exists/And/Or/True/False/Eq genuinely `inductive`, with real
-- recursors generated the SAME way as FruitKind/PearStack?
#print Exists
#print And
#print Or
#print True
#print False
#print Eq

#check @Exists.rec
#check @And.rec
#check @Or.rec
#check @True.rec
#check @False.rec
#check @Eq.rec

-- Now the introduction/elimination rules for → and ∀ themselves.
-- There's no name to #print -- they're not constants at all.
-- The ONLY way to produce a proof of P → Q is `fun (h : P) => ...`,
-- and the ONLY way to use one is application.
example (P Q : Prop) (f : P → Q) (p : P) : Q := f p     -- elimination = application
example (P Q : Prop) (h : P → P) : P → P := fun p => h p -- introduction = fun

-- Confirm `∀`/`→` really are the SAME primitive, just notation:
example : (∀ (_ : Nat), Bool) = (Nat → Bool) := rfl
