import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON R6 (capstone): INDICES + MUTUAL RECURSION together.

   No new mechanic here -- R4 (indices) and R5 (mutual) just COMBINE
   exactly as you'd predict. This is deliberately shaped to match
   Instr_ok/Instrs_ok's real structure from `wasm2.0.lean`: TWO mutually
   defined relations, each indexed by a value that varies per rule.

   Real world: a TypedBasket is indexed by its OWN declared capacity (a
   Nat, like R4's BoundedBasket) -- but a basket can also hold a
   TypedGift, and a TypedGift is indexed by the capacity of what it
   wraps. Both indexed, both mutual. -/

mutual
inductive TypedBasket : Nat → Type where
  | empty : TypedBasket 0
  | addFruit (rest : TypedBasket n) : TypedBasket (n + 1)
  | addGift (gift : TypedGift n) (rest : TypedBasket m) : TypedBasket (n + m)

inductive TypedGift : Nat → Type where
  | wrap (contents : TypedBasket n) : TypedGift n
end

#check @TypedBasket.rec
/- Real output (reformatted for readability):
   TypedBasket.rec :
     {motive_1 : (n : Nat) → TypedBasket n → Sort u} →
     {motive_2 : (n : Nat) → TypedGift n → Sort u} →
     motive_1 0 TypedBasket.empty →
     ({n : Nat} → (rest : TypedBasket n) → motive_1 n rest →
        motive_1 (n+1) (TypedBasket.addFruit rest)) →
     ({n m : Nat} → (gift : TypedGift n) → (rest : TypedBasket m) →
        motive_2 n gift → motive_1 m rest →
        motive_1 (n+m) (TypedBasket.addGift gift rest)) →
     ({n : Nat} → (contents : TypedBasket n) → motive_1 n contents →
        motive_2 n (TypedGift.wrap contents)) →
     {n : Nat} → (t : TypedBasket n) → motive_1 n t

   Every piece is exactly what R4 and R5 each predicted on their own,
   just stacked: TWO motives (mutual, from R5), each now taking an INDEX
   as a leading argument (from R4), and each minor premise's conclusion
   has BOTH its index specialized (0, n+1, n+m, ...) AND draws its ih's
   from whichever motive matches each recursive field's own type. Nothing
   here required a new rule -- it's the R4 rule and the R5 rule applied
   together, field by field, exactly as declared. -/

/- Quick concrete check: total fruit count should just be the index
   itself (every constructor's index literally tracks the running fruit
   total by construction) -- a nice sanity check that indices, ih's, and
   mutual recursion are all lining up correctly together. -/
mutual
def basketCount {n : Nat} : TypedBasket n → Nat
  | .empty => 0
  | .addFruit rest => let ih := basketCount rest; dbg_trace s!"  -> addFruit: ih={ih}"; ih + 1
  | .addGift gift rest =>
    let giftIh := giftCount gift
    let restIh := basketCount rest
    dbg_trace s!"  -> addGift: giftIh={giftIh}, restIh={restIh}"
    giftIh + restIh

def giftCount {n : Nat} : TypedGift n → Nat
  | .wrap contents => let ih := basketCount contents; dbg_trace s!"  -> wrap: ih={ih}"; ih
end

def sample3 : TypedBasket 2 :=
  .addFruit (.addGift (.wrap (.addFruit .empty)) .empty)
-- inner addFruit(empty) : TypedBasket 1, wrapped as TypedGift 1,
-- addGift with an empty (TypedBasket 0) rest : TypedBasket (1+0),
-- outer addFruit : TypedBasket (1+0+1) = TypedBasket 2.

#eval basketCount sample3

/- First attempt (deliberately left as a comment, worth reading): setting
   `motive_2 := fun n _ => ∀ (g : TypedGift n), giftCount g = n` -- i.e.
   making motive_2 IGNORE its own TypedGift subject and instead quantify
   a fresh, unrelated `g` inside -- reproduces the EXACT "goal doesn't
   depend on its own recursion target" anti-pattern from way earlier this
   session (the whole `instrs_seq_typing_inversion` saga). It breaks for
   the identical reason: in the `wrap` case you only have an `ih` about
   THIS branch's own `contents`, but the goal ends up being about some
   totally unrelated, freshly-quantified `g` -- nothing connects them.

   The fix is the same lesson from that saga, applied here: let the
   motive genuinely depend on its own subject. -/
theorem basketCount_eq_index : ∀ {n : Nat} (b : TypedBasket n), basketCount b = n := by
  intro n b
  induction b using TypedBasket.rec (motive_2 := fun n g => giftCount g = n) with
  | empty => rfl
  | addFruit rest ih => simp [basketCount, ih, dbgTrace]
  | addGift gift rest giftIh restIh => simp [basketCount, giftIh, restIh, dbgTrace]
  | wrap contents ih => simp [giftCount, ih, dbgTrace]

#print axioms basketCount_eq_index

/- ─── Now go look at the REAL thing ───
   You already have `spectec/test-lean/wasm2.0.lean` open. With everything
   from R1-R6, try this yourself in a scratch file that imports it:
     #check @Instr_ok.rec
     #check @Instrs_ok.rec
   You'll see the exact same shape: two motives (Instr_ok ~ motive_1,
   Instrs_ok ~ motive_2 -- matching the `#check @Instrs_ok.rec` output
   from many messages ago this session), each carrying `context`/
   `functype`-typed indices, with minor premises built field-by-field
   from each rule's own premises exactly the way R1-R6 built theirs. -/
