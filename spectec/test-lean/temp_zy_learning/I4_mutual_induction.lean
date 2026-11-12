import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON I4: `induction ... using` on a MUTUAL recursor -- you must
   supply a value (even if trivial) for every OTHER motive in the group,
   and get one `case` per constructor across the WHOLE mutual group, not
   just the type you're inducting on.

   Real world: FruitBasket/GiftWrap from R5. -/

mutual
inductive FruitBasket where
  | empty
  | addFruit (kind : String) (rest : FruitBasket)
  | addGift  (gift : GiftWrap) (rest : FruitBasket)

inductive GiftWrap where
  | wrap (contents : FruitBasket) : GiftWrap
end

mutual
def fruitCount : FruitBasket → Nat
  | .empty => 0
  | .addFruit _ rest => fruitCount rest + 1
  | .addGift gift rest => giftCount gift + fruitCount rest

def giftCount : GiftWrap → Nat
  | .wrap contents => fruitCount contents
end

/- `induction b` on `b : FruitBasket` needs a value for BOTH motive_1
   (FruitBasket) and motive_2 (GiftWrap) -- even though you're only
   inducting on a FruitBasket, the recursor is shared, so Lean needs to
   know what to do with the GiftWrap side too. If you genuinely don't
   care about GiftWrap's own answer, stub it with something trivial
   (`True`, as in every earlier lesson) -- Lean auto-infers the REAL
   motive (motive_1, here) from your goal, same as always; only the
   OTHER one(s) need your help. -/
theorem count_nonneg (b : FruitBasket) : fruitCount b ≥ 0 := by
  induction b using FruitBasket.rec (motive_2 := fun _ => True) with
  | empty => exact Nat.zero_le _
  | addFruit kind rest ih => exact Nat.zero_le _
  | addGift gift rest giftIh ih => exact Nat.zero_le _
  | wrap contents ih => trivial
/- FOUR cases, not one-per-FruitBasket-constructor (three) -- the fourth,
   `wrap`, belongs to GiftWrap, the OTHER type in the mutual group. This
   is because it's ALL ONE shared recursor: every constructor of EVERY
   type in the `mutual` block gets a case, whether or not you personally
   care about that type's own motive. `motive_2`'s cases (`wrap`, here)
   just get whatever trivial content you supplied for `motive_2` as
   their goal. -/

/- ─── A genuinely mutual PROOF, both motives doing real work ─── -/
theorem count_matches (b : FruitBasket) (g : GiftWrap) :
    fruitCount b = fruitCount b ∧ giftCount g = giftCount g := by
  constructor
  · induction b using FruitBasket.rec (motive_2 := fun g => giftCount g = giftCount g) with
    | empty => rfl
    | addFruit kind rest ih => rfl
    | addGift gift rest giftIh restIh => rfl
    | wrap contents ih => rfl
  · induction g using GiftWrap.rec (motive_1 := fun b => fruitCount b = fruitCount b) with
    | empty => rfl
    | addFruit kind rest ih => rfl
    | addGift gift rest giftIh restIh => rfl
    | wrap contents ih => rfl
/- ─── Under the hood ───
   `count_nonneg` only inducted on `b : FruitBasket`, and never even
   named `motive_2`'s cases' logic explicitly beyond a `trivial` -- but
   the compiled term still had to supply values for the FULL, shared
   recursor, both motives at once: -/
set_option pp.proofs true in
#print count_nonneg
-- Look for `motive_2` in the printed type -- it's set to `fun _ => True`
-- (exactly what you passed), and the `wrap` case's own argument is a
-- function producing `trivial : True`, sitting right alongside the
-- three FruitBasket-motive arguments, all as siblings of ONE
-- `FruitBasket.rec` application.

/- ─── `apply` translations ───
   Both recursors are literally the SAME shape as I3's single-motive
   examples, just with an extra `{motive_2 : GiftWrap → Sort u_1}` binder
   spliced in right after `motive_1` -- confirm via `#check @FruitBasket.rec`.
   `apply`'s peeling still goes left to right: `motive_1` gets solved by
   unifying against the (reverted) goal exactly as before, but NOTHING in
   either goal below ever mentions `GiftWrap`, so `motive_2` can NEVER be
   inferred from unification -- it has to be supplied by hand one way or
   another, no matter which tactic drives the recursor. -/

-- "args" version: supply everything explicitly, no `revert` needed.
theorem count_nonneg_apply_args (b : FruitBasket) : fruitCount b ≥ 0 := by
  apply FruitBasket.rec
    (motive_1 := fun b => fruitCount b ≥ 0)
    (motive_2 := fun _ => True)
    (t := b)
  · exact Nat.zero_le _
  · intro kind rest ih; exact Nat.zero_le _
  · intro gift rest giftIh ih; exact Nat.zero_le _
  · intro contents ih; trivial

-- "bare" version: `revert b` lets `apply` infer `motive_1` and `t` from
-- the goal's own Pi-shape, same as I3 -- but `motive_2` is STILL
-- unconstrained, so `apply` turns it into its own extra goal (right where
-- it sits in the recursor's argument list, i.e. before the four case
-- goals) instead of erroring outright. Target it BY NAME with `case`
-- rather than by bullet position, since its position is easy to
-- misjudge:
theorem count_nonneg_apply_bare (b : FruitBasket) : fruitCount b ≥ 0 := by
  revert b
  #check FruitBasket.rec
  apply FruitBasket.rec
  case motive_2 => exact fun _ => True
  · exact Nat.zero_le _
  · intro kind rest ih; exact Nat.zero_le _
  · intro gift rest giftIh ih; exact Nat.zero_le _
  · intro contents ih; trivial

-- Same recipe for the genuinely-mutual proof, once per recursor call.
theorem count_matches_apply_args (b : FruitBasket) (g : GiftWrap) :
    fruitCount b = fruitCount b ∧ giftCount g = giftCount g := by
  constructor
  · apply FruitBasket.rec
      (motive_1 := fun b => fruitCount b = fruitCount b)
      (motive_2 := fun g => giftCount g = giftCount g)
      (t := b)
    · rfl
    · intro kind rest ih; rfl
    · intro gift rest giftIh restIh; rfl
    · intro contents ih; rfl
  · apply GiftWrap.rec
      (motive_1 := fun b => fruitCount b = fruitCount b)
      (motive_2 := fun g => giftCount g = giftCount g)
      (t := g)
    · rfl
    · intro kind rest ih; rfl
    · intro gift rest giftIh restIh; rfl
    · intro contents ih; rfl

theorem count_matches_apply_bare (b : FruitBasket) (g : GiftWrap) :
    fruitCount b = fruitCount b ∧ giftCount g = giftCount g := by
  constructor
  · revert b
    apply FruitBasket.rec
    case motive_2 => exact fun g => giftCount g = giftCount g
    · rfl
    · intro kind rest ih; rfl
    · intro gift rest giftIh restIh; rfl
    · intro contents ih; rfl
  · revert g
    apply GiftWrap.rec
    case motive_1 => exact fun b => fruitCount b = fruitCount b
    · rfl
    · intro kind rest ih; rfl
    · intro gift rest giftIh restIh; rfl
    · intro contents ih; rfl

/- Note we called TWO different recursors here (`FruitBasket.rec` and
   `GiftWrap.rec`) for the two halves of the proof -- and BOTH accepted
   the SAME four case names (`empty`, `addFruit`, `addGift`, `wrap`),
   because -- as R5 showed via `#check` on both -- they share the exact
   same minor premises, only their FINAL conclusion (which motive gets
   the bare `(t : _) → motive_k t` treatment) differs. Which one you
   invoke just tells Lean which type's value you're actually
   case-splitting; the case list is identical either way. -/
