import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON R4: INDICES -- when the type itself is parametrized by a value
   that changes from constructor to constructor.

   Real world: a BoundedBasket n is a basket that carries, IN ITS OWN
   TYPE, exactly how many pears it holds. `BoundedBasket 0` is the type
   of empty baskets; `BoundedBasket 3` is the type of baskets with
   exactly 3 pears; you cannot even STATE "a BoundedBasket 3" that turns
   out to secretly hold 5 pears -- the count is baked into which type you
   have, not just a field inside a single fixed type (contrast with R2's
   `Basket`, where `empty` and `withPears 3` were both just plain
   `Basket`s). This is exactly the same idea as Wasm's own indexed
   families we looked at much earlier this session (recursor motives for
   `Vec`), just with fresh flavor text. -/

inductive BoundedBasket : Nat → Type where
  | empty : BoundedBasket 0
  | addPear : BoundedBasket n → BoundedBasket (n + 1)

#check @BoundedBasket.rec
/- Real output (names may vary slightly):
     BoundedBasket.rec.{u} :
       {motive : (n : Nat) → BoundedBasket n → Sort u} →
       motive 0 BoundedBasket.empty →
       ({n : Nat} → (rest : BoundedBasket n) → motive n rest → motive (n + 1) (BoundedBasket.addPear rest)) →
       {n : Nat} → (t : BoundedBasket n) → motive n t

   The single biggest change from R3: `motive` now takes the INDEX as an
   extra LEADING argument, before the subject:
     motive : (n : Nat) → BoundedBasket n → Sort u
   instead of just `BoundedBasket n → Sort u`. That's because "the answer
   you want" is allowed to depend not just on WHICH basket you have, but
   on WHAT ITS INDEX IS -- and since the index can differ across
   constructors, the recursor has to let your motive see it explicitly.

   Look at each minor premise's CONCLUSION:
     - `empty`'s:    motive 0       BoundedBasket.empty
     - `addPear`'s:  motive (n + 1) (BoundedBasket.addPear rest)
   Each one has the index SPECIALIZED to exactly what that constructor
   forces it to be -- `0` for `empty` (since `empty : BoundedBasket 0`
   literally says so), `n + 1` for `addPear` (matching `addPear : ... →
   BoundedBasket (n + 1)`). You never get to choose the index yourself in
   a minor premise's conclusion -- it's dictated by the constructor's own
   declared type.

   And the ih, `motive n rest`, is index-aware too: it's the answer for
   the SMALLER basket `rest`, at ITS OWN (smaller) index `n` -- not at
   `n + 1`. This all lines up with the constructor's own signature,
   field-for-field, index-for-index -- there's no independent "index
   logic," it's mechanically read off exactly what you wrote in the
   `inductive` block. -/

noncomputable def pearCount_direct : {n : Nat} → BoundedBasket n → Nat := fun {n} b =>
  BoundedBasket.rec (motive := fun n _ => Nat) 0 (fun {n} _rest ih => ih + 1) b

def basketOf3 : BoundedBasket 3 :=
  .addPear (.addPear (.addPear .empty))

#reduce pearCount_direct basketOf3

/- Executable, dbg_trace-visible equivalent. Note `n` is written EXPLICIT
   here (not `{n}`) -- pattern-matching directly on an IMPLICIT index
   inside a bare `def | pat => ...` runs into real elaborator friction in
   Lean 4 (a well-known rough edge with dependent pattern matching); an
   explicit index sidesteps it entirely and is just as instructive. -/
def pearCount (n : Nat) : BoundedBasket n → Nat
  | .empty => 0
  | .addPear rest =>
    let ih := pearCount _ rest
    dbg_trace s!"  -> addPear branch at index n={n}: ih={ih}, returning {ih + 1}"
    ih + 1

#eval pearCount 3 basketOf3

/- A motive that GENUINELY uses the index: prove, for every n and every
   BoundedBasket n, that recursively counting really does give back n.
   This is a real induction PROOF (Prop-valued motive), not just a
   Nat-valued computation -- previewing what Lesson I-series (`induction`
   tactic) will build on top of exactly this recursor. Proofs never need
   `noncomputable` -- kernel type-checking, not compilation, is all a
   proof needs. -/
theorem pearCount_eq_index : ∀ (n : Nat) (b : BoundedBasket n), pearCount n b = n := by
  intro n b
  induction b with
  | empty => rfl
  | addPear rest ih => simp [pearCount, ih, dbgTrace]

#print axioms pearCount_eq_index
