import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   How a real `cases` tactic call actually compiles down to a
   `PearStack.casesOn` application -- and a genuinely surprising asymmetry
   with `induction` on the exact same setup, worth inspecting closely. ═══ -/

inductive PearStack where
  | empty
  | onePear (rest : PearStack)

/- ═══ Part 1: `cases`, compiled ═══ -/

theorem cases_demo (s : PearStack) (P : PearStack → Prop)
    (hempty : P PearStack.empty) (honePear : ∀ rest, P (PearStack.onePear rest)) : P s := by
  cases s with
  | empty => exact hempty
  | onePear rest => exact honePear rest

set_option pp.proofs true in
set_option pp.explicit true in
#print cases_demo
/- Real output:

theorem cases_demo : ∀ (s : PearStack) (P : PearStack → Prop),
  P PearStack.empty → (∀ (rest : PearStack), P rest.onePear) → P s :=
fun s P hempty honePear =>
  @PearStack.casesOn (fun t => @Eq PearStack s t → P s) s
    (fun h => @Eq.ndrec PearStack PearStack.empty (fun s => P s) hempty s
                (@Eq.symm PearStack s PearStack.empty h))
    (fun rest h =>
      @Eq.ndrec PearStack rest.onePear (fun s => P s) (honePear rest) s
        (@Eq.symm PearStack s rest.onePear h))
    (@Eq.refl PearStack s)

   This is genuinely more elaborate than the "obvious" guess
   (`@PearStack.casesOn (fun t => P t) s hempty honePear`). Reading it
   piece by piece:

   * The MOTIVE handed to `.casesOn` is NOT `fun t => P t`. It's
     `fun t => (s = t) → P s` -- an equation between `t` (whichever
     branch we're in) and the ORIGINAL `s`, gating a conclusion that's
     still stated in terms of `s`, not `t`.

   * The FINAL argument to `.casesOn` is `@Eq.refl PearStack s`, i.e.
     `s = s` -- this instantiates that gate trivially, for the ONE
     branch that's actually true.

   * Each branch function receives that equation as `h`, and uses
     `Eq.ndrec`/`Eq.symm` (the ordinary `▸` rewrite, spelled out in
     full) to transport the branch's own fact (`hempty : P
     PearStack.empty`, or `honePear rest : P rest.onePear`) ALONG the
     equation, turning it into the thing actually needed: `P s`.

   In short: `cases` doesn't directly ask `.casesOn` to conclude `P t`
   for whichever `t` it lands on -- it asks `.casesOn` to conclude
   "IF `s` turns out to equal `t`, THEN `P s`", supplies the trivial
   proof that `s` equals itself, and lets each branch's `Eq.ndrec`
   silently rewrite the specific pattern back into `s`'s own place.
   This is the exact SAME generalize-with-an-equation technique from
   the HHG "Induction Pitfalls" discussion earlier this session --
   `cases`'s own elaborator is doing it internally, automatically, even
   though the surface syntax never mentions an equation at all. -/

/- ═══ Part 2: `induction`, on the EXACT same setup -- compare ═══ -/

theorem induction_demo (s : PearStack) (P : PearStack → Prop)
    (hempty : P PearStack.empty)
    (honePear : ∀ rest, P rest → P (PearStack.onePear rest)) : P s := by
  induction s with
  | empty => exact hempty
  | onePear rest ih => exact honePear rest ih

set_option pp.proofs true in
set_option pp.explicit true in
#print induction_demo
/- Real output:

theorem induction_demo : ∀ (s : PearStack) (P : PearStack → Prop),
  P PearStack.empty → (∀ (rest : PearStack), P rest → P rest.onePear) → P s :=
fun s P hempty honePear => @PearStack.rec (fun s => P s) hempty (fun rest ih => honePear rest ih) s

   No equation, no `Eq.ndrec`, no `Eq.refl` -- just a direct
   `@PearStack.rec (fun s => P s) hempty (fun rest ih => honePear rest ih) s`
   application, exactly the "obvious" shape. Same source-level setup
   (a bare variable `s` eliminated, appearing directly in the target
   `P s`), same tactic-block structure -- but `induction`'s elaborator
   takes the direct path here, while `cases`'s takes the
   generalize-with-an-equation path. Both are completely valid: verify
   this yourself by checking that BOTH compile clean and that
   `cases_demo`/`induction_demo` both genuinely prove `∀ s P, P empty →
   (...) → P s` -- they just reach it via visibly different terms. -/
