import Mathlib.Tactic

inductive EvenPred : Nat → Prop where
  | zero : EvenPred 0
  | add_two : ∀ k : Nat, EvenPred k → EvenPred (k + 2)

-- ═══ Part 1: use EvenPred.rec directly, non-idiomatically ═══

@[reducible] def P (n : Nat) : Prop := n % 2 = 0

theorem proof_zero : P 0 := by decide

theorem proof_add_two : ∀ k : Nat, EvenPred k → P k → P (k + 2) :=
  fun k _ ih => by omega

theorem h0 : EvenPred 0 := EvenPred.zero
theorem h2 : EvenPred 2 := EvenPred.add_two 0 h0
theorem h4 : EvenPred 4 := EvenPred.add_two 2 h2

#check EvenPred.rec

theorem four_mod_two_direct : P 4 :=
  EvenPred.rec (motive := fun n _ => P n) proof_zero proof_add_two h4

#print axioms four_mod_two_direct

-- ═══ Part 2: step-by-step reduction, mirroring the PearStack style ═══

example :
    EvenPred.rec (motive := fun n _ => P n) proof_zero proof_add_two h4
  = proof_add_two 2 h2
      (EvenPred.rec (motive := fun n _ => P n) proof_zero proof_add_two h2)
  := rfl

example :
    proof_add_two 2 h2
      (EvenPred.rec (motive := fun n _ => P n) proof_zero proof_add_two h2)
  = proof_add_two 2 h2
      (proof_add_two 0 h0
        (EvenPred.rec (motive := fun n _ => P n) proof_zero proof_add_two h0))
  := rfl

example :
    proof_add_two 2 h2
      (proof_add_two 0 h0
        (EvenPred.rec (motive := fun n _ => P n) proof_zero proof_add_two h0))
  = proof_add_two 2 h2 (proof_add_two 0 h0 proof_zero)
  := rfl

example : four_mod_two_direct = proof_add_two 2 h2 (proof_add_two 0 h0 proof_zero) := rfl

-- ═══ Part 3: the honest caveat -- Prop is proof-irrelevant, so ANY proof
-- of `P 4` is `rfl`-equal to any other, regardless of how it was built.
-- The chain above is a TRUE description of the intended reduction path,
-- but its `rfl`s succeeding doesn't, by itself, prove THIS is the unique
-- path -- it would succeed just as well against an unrelated proof. ═══

example : four_mod_two_direct = (by decide : P 4) := rfl
example : four_mod_two_direct = (rfl : (4:Nat) % 2 = 0) := rfl
-- Both proofs of `P 4` -- built via completely different means -- are
-- `rfl`-equal to the recursor-built one. Definitional equality of PROOFS
-- carries no information here beyond "both inhabit `P 4`".

-- ═══ Part 4: a Sort-valued (not Prop-valued) sibling, so the chain below
-- is actually conclusive -- no proof irrelevance to hide behind.
--
-- Important real discovery along the way: you CANNOT just retarget
-- `EvenPred.rec` itself at `Bool` -- try it and Lean rejects it with
-- "Bool has type Type ... but is expected to have type Prop". Check its
-- real signature:
--
--   @EvenPred.rec : ∀ {motive : (a : ℕ) → EvenPred a → Prop}, ...
--
-- `motive` is hard-restricted to `Prop`, not `Sort u`. This is the
-- SUBSINGLETON ELIMINATION restriction from the reference-manual material
-- earlier this session: `EvenPred` has TWO constructors, so it fails the
-- "at most one constructor" condition and is NOT a subsingleton -- so,
-- exactly like `Or.rec` (also two constructors, also Prop-restricted),
-- "large elimination" into Type/Bool/Nat is disallowed. To get a genuinely
-- conclusive reduction demo we need a type with the IDENTICAL shape, just
-- declared in `Type` instead of `Prop`: ═══

inductive EvenWitness : Nat → Type where
  | zero : EvenWitness 0
  | add_two : ∀ k : Nat, EvenWitness k → EvenWitness (k + 2)

#check @EvenWitness.rec
-- @EvenWitness.rec : {motive : (a : ℕ) → EvenWitness a → Sort u_1} → ...
-- unrestricted, because EvenWitness was never in Prop to begin with.

def w0 : EvenWitness 0 := EvenWitness.zero
def w2 : EvenWitness 2 := EvenWitness.add_two 0 w0
def w4 : EvenWitness 4 := EvenWitness.add_two 2 w2

noncomputable def evenFlag : {n : Nat} → EvenWitness n → Bool :=
  fun {_n} h => EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) h

#reduce evenFlag w4   -- true, via genuine kernel computation, not proof irrelevance

example :
    EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w4
  = (fun _k _ ih => ih) 2 w2
      (EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w2)
  := rfl

example :
    (fun _k _ ih => ih) 2 w2
      (EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w2)
  = EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w2
  := rfl

example :
    EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w2
  = (fun _k _ ih => ih) 0 w0
      (EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w0)
  := rfl

example :
    (fun _k _ ih => ih) 0 w0
      (EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w0)
  = EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w0
  := rfl

example :
    EvenWitness.rec (motive := fun _ _ => Bool) true (fun _k _ ih => ih) w0
  = true
  := rfl

example : evenFlag w4 = true := rfl
