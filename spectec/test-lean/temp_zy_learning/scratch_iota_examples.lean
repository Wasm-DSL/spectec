import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   Iota-reduction, worked from simplest to most complex, each step a
   verified `rfl`. Mirrors the official rule (Lean reference manual,
   "Inductive Types" §4.4.3.1.2, "Reduction"):

     "When the recursor's major premise is a constructor with no
      recursive parameters, the recursor application reduces to an
      application of the constructor's minor premise to the
      constructor's arguments. If there are recursive parameters, then
      these arguments to the minor premise are found by applying the
      recursor to the recursive occurrence." -/

-- ═══ 1. No recursion, no fields, no index (Bool) ═══
-- iota just SELECTS the matching minor premise -- nothing else to do,
-- because the constructor carries no arguments at all.
example : Bool.rec (motive := fun _ => Nat) 10 20 true  = 20 := rfl
example : Bool.rec (motive := fun _ => Nat) 10 20 false = 10 := rfl

-- ═══ 2. No recursion, but WITH a field (Bool → Nat, no self-reference) ═══
inductive Basket where
  | empty
  | withPears (count : Nat)

-- minor premise for `withPears` gets its field applied directly -- no ih,
-- since `count : Nat` doesn't mention `Basket` itself.
example : Basket.rec (motive := fun _ => Nat) 0 (fun count => count * 2)
            (Basket.withPears 5)
        = (fun count => count * 2) 5
        := rfl
example : (fun count => count * 2) 5 = 10 := rfl

-- ═══ 3. Recursion, no index (PearStack, self-referential field) ═══
-- Same type as R3. Here the minor premise's SECOND argument (the ih) is
-- itself a NEW recursor application, built by the rule on the spot.
inductive PearStack where
  | empty
  | onePear (rest : PearStack)

example (rest : PearStack) :
    PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1)
      (PearStack.onePear rest)
  = (fun _rest ih => ih + 1) rest
      (PearStack.rec (motive := fun _ => Nat) 0 (fun _rest ih => ih + 1) rest)
  := rfl
-- ^ THIS is the general schema: `T.rec ms (Ctor a) = m_Ctor a (T.rec ms a)`
--   for a single self-referential field `a`.

example :

    PearStack.rec
      (motive := fun _ => Nat)
      0
      (fun _rest ih => ih + 1)

      (PearStack.onePear (PearStack.onePear (PearStack.onePear PearStack.empty)))

  = (fun _rest ih => ih + 1)
      (PearStack.onePear (PearStack.onePear PearStack.empty))
      (PearStack.rec
        (motive := fun _ => Nat)
        0
        (fun _rest ih => ih + 1)

        (PearStack.onePear (PearStack.onePear PearStack.empty)))

  := rfl

example :

    (fun _rest ih => ih + 1)
      (PearStack.onePear (PearStack.onePear PearStack.empty))
      (PearStack.rec
        (motive := fun _ => Nat)
        0
        (fun _rest ih => ih + 1)

        (PearStack.onePear (PearStack.onePear PearStack.empty)))

  = (fun _rest ih => ih + 1)
      (PearStack.onePear (PearStack.onePear PearStack.empty))
      ((fun _rest ih => ih + 1)
        (PearStack.onePear PearStack.empty)
        (PearStack.rec
          (motive := fun _ => Nat)
          0
          (fun _rest ih => ih + 1)

          (PearStack.onePear PearStack.empty)))

  := rfl

example :

    (fun _rest ih => ih + 1)
      (PearStack.onePear (PearStack.onePear PearStack.empty))
      ((fun _rest ih => ih + 1)
        (PearStack.onePear PearStack.empty)
        (PearStack.rec
          (motive := fun _ => Nat)
          0
          (fun _rest ih => ih + 1)

          (PearStack.onePear PearStack.empty)))

  = (fun _rest ih => ih + 1)
      (PearStack.onePear (PearStack.onePear PearStack.empty))
      ((fun _rest ih => ih + 1)
        (PearStack.onePear PearStack.empty)
        ((fun _rest ih => ih + 1)
          PearStack.empty
          (PearStack.rec
            (motive := fun _ => Nat)
            0
            (fun _rest ih => ih + 1)

            PearStack.empty)))

  := rfl

example :

    (fun _rest ih => ih + 1)
      (PearStack.onePear (PearStack.onePear PearStack.empty))
      ((fun _rest ih => ih + 1)
        (PearStack.onePear PearStack.empty)
        ((fun _rest ih => ih + 1)
          PearStack.empty
          (PearStack.rec
            (motive := fun _ => Nat)
            0
            (fun _rest ih => ih + 1)

            PearStack.empty)))

  = (fun _rest ih => ih + 1)
      (PearStack.onePear (PearStack.onePear PearStack.empty))
      ((fun _rest ih => ih + 1)
        (PearStack.onePear PearStack.empty)
        ((fun _rest ih => ih + 1)
          PearStack.empty
          0))

  := rfl

-- ═══ 4. Recursion + a NON-recursive field together (List) ═══
-- `cons` has TWO fields: `head : α` (not recursive) and `tail : List α`
-- (recursive). iota hands the minor premise the field for `head` plainly,
-- but for `tail` it hands BOTH `tail` itself AND `List.rec ... tail` (ih).
example (n : Nat) (tail : List Nat) :
    List.rec (motive := fun _ => Nat) 0 (fun head _tail ih => head + ih)
      (List.cons n tail)
  = (fun head _tail ih => head + ih) n tail
      (List.rec (motive := fun _ => Nat) 0 (fun head _tail ih => head + ih) tail)
  := rfl

-- ═══ 5. Recursion + an INDEX that changes across the recursive call
--        (EvenOddList, straight from the Lean reference manual's own
--        example of "Recursor with parameters and indices") ═══
inductive EvenOddList (α : Type) : Bool → Type where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (!isEven)

#check @EvenOddList.rec
/- Real output:
   EvenOddList.rec.{u} {α : Type} {motive : (isEven : Bool) → EvenOddList α isEven → Sort u}
     (nil : motive true EvenOddList.nil)
     (cons : {isEven : Bool} → (head : α) → (tail : EvenOddList α isEven) →
       motive isEven tail → motive (!isEven) (EvenOddList.cons head tail))
     {isEven : Bool} (t : EvenOddList α isEven) : motive isEven t         -/

-- named separately (instead of inline) purely so we can re-apply it
-- explicitly on the RHS below via `@` -- an implicit-binder lambda
-- applied bare outside `.rec` can't have `isEven` inferred, since the
-- (deliberately trivial) motive here doesn't mention it at all.
def evenOddMinor {isEven : Bool} (head : Nat) (_tail : EvenOddList Nat isEven)
    (ih : Nat) : Nat := head + ih

example (isEven : Bool) (head : Nat) (tail : EvenOddList Nat isEven) :
    EvenOddList.rec (motive := fun _ _ => Nat) 0 evenOddMinor
      (EvenOddList.cons head tail)
  = @evenOddMinor isEven head tail
      (EvenOddList.rec (motive := fun _ _ => Nat) 0 evenOddMinor tail)
  := rfl
-- Same schema as List, PLUS: the index `isEven` silently flips to `!isEven`
-- in the RESULT type at each step -- iota doesn't touch that computation
-- itself (that's just the motive being applied to a different index by
-- ordinary function application); iota only decides WHICH minor premise
-- fires and how to build its ih argument(s).

-- ═══ 6. Recursion across a MUTUAL pair (two motives, ih from the OTHER
--        type) -- reusing FruitBasket/GiftWrap from R5/I4. ═══
mutual
inductive FruitBasket where
  | empty
  | addFruit (kind : String) (rest : FruitBasket)
  | addGift  (gift : GiftWrap) (rest : FruitBasket)

inductive GiftWrap where
  | wrap (contents : FruitBasket) : GiftWrap
end

example (gift : GiftWrap) (rest : FruitBasket) :
    FruitBasket.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
      0
      (fun _kind _rest ih => ih)
      (fun _gift _rest giftIh restIh => giftIh + restIh)
      (fun _contents ih => ih)
      (FruitBasket.addGift gift rest)
  = (fun _gift _rest giftIh restIh => giftIh + restIh) gift rest
      (GiftWrap.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
        0 (fun _kind _rest ih => ih)
        (fun _gift _rest giftIh restIh => giftIh + restIh)
        (fun _contents ih => ih) gift)
      (FruitBasket.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
        0 (fun _kind _rest ih => ih)
        (fun _gift _rest giftIh restIh => giftIh + restIh)
        (fun _contents ih => ih) rest)
  := rfl
-- `addGift`'s TWO recursive fields (`gift : GiftWrap`, `rest : FruitBasket`)
-- each get their OWN ih -- but `gift`'s ih is built by calling the OTHER
-- type's recursor (`GiftWrap.rec`, using motive_2), while `rest`'s ih
-- calls `FruitBasket.rec` (motive_1) again. Both share the SAME bundle of
-- four minor premises (three for FruitBasket's constructors, one for
-- GiftWrap's single `wrap` constructor -- matching I4's "four cases"
-- observation), because it's genuinely ONE shared recursor underneath
-- both `.rec` names.
