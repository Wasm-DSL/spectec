import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON R5: MUTUAL RECURSION -- two types whose definitions genuinely
   refer to EACH OTHER.

   Real world: a FruitBasket holds a sequence of items, where each item
   is EITHER a loose fruit, OR a GiftWrap -- and a GiftWrap, in turn,
   wraps up an entire FruitBasket inside it (gift baskets containing gift
   baskets). Neither type can be defined first in isolation -- Lean needs
   `mutual ... end` to declare them together. -/

mutual
inductive FruitBasket where
  | empty
  | addFruit (kind : String) (rest : FruitBasket)
  | addGift  (gift : GiftWrap) (rest : FruitBasket)

inductive GiftWrap where
  | wrap (contents : FruitBasket) : GiftWrap
end

/- Because these are genuinely mutual, Lean generates ONE recursor per
   type in the group, but they SHARE the same set of motive parameters
   and the same set of minor premises -- only the FINAL conclusion
   differs (which type's recursor you asked for). Let's look at both. -/

#check @FruitBasket.rec
#check @GiftWrap.rec
/- Real output (abbreviated types shown, exact form may wrap differently):

   FruitBasket.rec :
     {motive_1 : FruitBasket → Sort u} → {motive_2 : GiftWrap → Sort u} →
     motive_1 FruitBasket.empty →
     ((kind : String) → (rest : FruitBasket) → motive_1 rest →
        motive_1 (FruitBasket.addFruit kind rest)) →
     ((gift : GiftWrap) → (rest : FruitBasket) → motive_2 gift → motive_1 rest →
        motive_1 (FruitBasket.addGift gift rest)) →
     ((contents : FruitBasket) → motive_1 contents →
        motive_2 (GiftWrap.wrap contents)) →
     (t : FruitBasket) → motive_1 t

   GiftWrap.rec : <the exact same 4 arguments above> →
     (t : GiftWrap) → motive_2 t

   Notice TWO motives now: `motive_1` for FruitBasket, `motive_2` for
   GiftWrap -- one per type declared in the `mutual` block, in
   declaration order. And notice the KEY new thing, in the `addGift`
   minor premise:
     (gift : GiftWrap) → (rest : FruitBasket) → motive_2 gift → motive_1 rest → ...
   `addGift`'s constructor has TWO recursive-ish fields: `gift : GiftWrap`
   and `rest : FruitBasket` -- but they're recursive into DIFFERENT types
   in the mutual group! So each gets its OWN ih, drawn from the motive
   that matches ITS OWN type: `gift`'s ih is `motive_2 gift` (since gift
   is a GiftWrap), `rest`'s ih is `motive_1 rest` (since rest is a
   FruitBasket). This is the general rule for mutual recursors: a
   recursive field's ih always comes from whichever motive matches THAT
   field's own type -- not necessarily the motive of the type you're
   defining the minor premise for.

   Also notice WHERE the ih's land: BOTH raw fields (`gift`, `rest`) come
   first, in the constructor's own declared order -- THEN both ih's come
   afterward, ALSO in that same relative order (`motive_2 gift` before
   `motive_1 rest`). This differs from R3, where the field and its ih sat
   right next to each other -- that was just because R3's constructor had
   only ONE recursive field, so "grouped" and "interleaved" looked
   identical. The real, general rule (confirmed by the printed type
   above, not assumed): ALL of a constructor's own fields/premises appear
   first, in the order you wrote them -- THEN, for every one of those
   that turned out to be recursive, an ih gets appended afterward, in
   that same relative order. -/

noncomputable def fruitCount_direct : FruitBasket → Nat := fun b =>
  FruitBasket.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    0
    (fun _kind _rest ih => ih + 1)
    (fun _gift _rest giftIh restIh => giftIh + restIh)
    (fun _contents contentsIh => contentsIh)
    b

def sample : FruitBasket :=
  .addFruit "apple"
    (.addGift (.wrap (.addFruit "pear" (.addFruit "banana" .empty)))
      (.addFruit "kiwi" .empty))
-- one loose apple, then a wrapped gift box containing a pear+banana basket,
-- then one more loose kiwi. Total loose+wrapped fruit: 4.

#reduce fruitCount_direct sample

/- Executable, dbg_trace-visible equivalent. Since fruitCount (over
   FruitBasket) and giftCount (over GiftWrap) call EACH OTHER, they must
   be declared together with `mutual ... end` too -- exactly mirroring
   the inductive types themselves. -/
mutual
def fruitCount : FruitBasket → Nat
  | .empty => dbg_trace "  -> empty basket: 0"; 0
  | .addFruit kind rest =>
    let ih := fruitCount rest
    dbg_trace s!"  -> addFruit '{kind}': rest had {ih}, so total = {ih + 1}"
    ih + 1
  | .addGift gift rest =>
    let giftIh := giftCount gift
    let restIh := fruitCount rest
    dbg_trace s!"  -> addGift: gift contributes {giftIh}, rest contributes {restIh}"
    giftIh + restIh

def giftCount : GiftWrap → Nat
  | .wrap contents =>
    let ih := fruitCount contents
    dbg_trace s!"  -> wrap: forwarding the {ih} fruits inside"
    ih
end

#eval (do
  IO.println "fruitCount sample:"
  IO.println s!"  final result = {fruitCount sample}"
  : IO Unit)
/- Watch the trace: the `wrap` branch (the GiftWrap side) fires in the
   MIDDLE of the `addGift` branch's own work, recursing all the way down
   into the nested basket via `fruitCount` again before coming back up --
   real back-and-forth between the two functions (and, underneath, the
   two motives), not just two independent recursions running side by
   side. -/
