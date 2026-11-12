import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON R2: constructors that carry DATA, but still no self-reference.

   Real world: a basket is either totally empty, or it holds SOME NUMBER
   of pears (we're not yet tracking individual pears, just a count).

   (Reminder from R1: any raw `.rec`/`.recOn` application must be marked
   `noncomputable` and inspected via `#reduce`, not `#eval` -- the
   compiler only knows how to run `match`-compiled code. Every lesson
   from here on follows that same two-track pattern without re-explaining
   it each time.) -/

inductive Basket where
  | empty
  | withPears (count : Nat)

#check @Basket.rec
/- Real output:
     Basket.rec.{u} : {motive : Basket → Sort u} →
       motive Basket.empty →
       ((count : Nat) → motive (Basket.withPears count)) →
       (t : Basket) → motive t

   Compare to R1. The `empty` minor premise is exactly like before: just
   `motive Basket.empty`, no arguments, because `empty` carries no data.

   But the `withPears` minor premise is now a FUNCTION:
     (count : Nat) → motive (Basket.withPears count)
   Read this as: "I will hand you the ACTUAL count field this basket was
   built with. Using that, you must produce a `motive`-shaped answer for
   the basket `withPears count` -- the specific basket built from THAT
   count, not baskets in general."

   General rule (R1 extended): a minor premise's argument list mirrors,
   one-for-one, the constructor's OWN argument list. A field of type X
   becomes a plain argument of type X in the minor premise. -/

noncomputable def pearCount_direct : Basket → Nat := fun b =>
  Basket.rec (motive := fun _basket => Nat) 0 (fun count => count) b

#reduce pearCount_direct .empty
#reduce pearCount_direct (.withPears 7)

def pearCount : Basket → Nat
  | .empty => dbg_trace "  -> empty branch, no data to inspect"; 0
  | .withPears count =>
    dbg_trace s!"  -> withPears branch, count field = {count}"
    count

#eval pearCount .empty
#eval pearCount (.withPears 7)

/- What if a constructor has MULTIPLE fields? Same rule, just more
   arguments in the minor premise, in the same order as the constructor. -/
inductive PricedBasket where
  | empty
  | withPears (count : Nat) (pricePerPear : Nat)

#check @PricedBasket.rec
-- (count : Nat) → (pricePerPear : Nat) → motive (PricedBasket.withPears count pricePerPear)
-- -- two fields in, two plain arguments in the minor premise, same order.

def totalPrice : PricedBasket → Nat
  | .empty => 0
  | .withPears count pricePerPear =>
    dbg_trace s!"  -> count={count}, pricePerPear={pricePerPear}, total={count * pricePerPear}"
    count * pricePerPear

#eval totalPrice (.withPears 5 3)
