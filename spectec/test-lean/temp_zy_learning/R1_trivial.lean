import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON R1: the simplest possible recursor.

   An inductive type with THREE constructors, none of which carry any data,
   and none of which refer back to the type itself.

   Real world: a fruit in your basket is EITHER an apple, a pear, or a
   banana. That's the whole story -- there's nothing else to say about
   which one it is.
   ═══════════════════════════════════════════════════════════════════════ -/

inductive FruitKind where
  | apple
  | pear
  | banana

/- Lean auto-generates several things when you write `inductive`. The one
   we care about is `.rec` -- the RECURSOR. Let's look at its type. -/
#check @FruitKind.rec

/- Real output:
     FruitKind.rec.{u} : {motive : FruitKind → Sort u} →
       motive FruitKind.apple → motive FruitKind.pear → motive FruitKind.banana →
       (t : FruitKind) → motive t

   Read this as a recipe for building a function OUT OF FruitKind:
     - `motive : FruitKind → Sort u`
         "motive" is the RETURN TYPE you want, as a function of WHICH
         FruitKind you were given. `Sort u` is Lean's umbrella for "any
         type, or Prop" -- `u` is a placeholder for whichever universe
         level actually gets used at each call site.
     - `motive FruitKind.apple`
         "if I hand you specifically an apple, give me back a `motive
         apple`-shaped answer." This is called a MINOR PREMISE -- one per
         constructor, and it's the piece the person calling `.rec` has to
         supply.
     - Two more minor premises, same idea, for `pear` and `banana`.
     - `(t : FruitKind) → motive t`
         "then, given ANY FruitKind t (called the MAJOR PREMISE), I'll
         give you back a `motive t`-shaped answer" -- i.e. `.rec`, once
         you've supplied the three answers above, becomes an actual
         function `FruitKind → (motive of your choice)`.

   Why THREE minor premises? Because there are THREE constructors. This
   will be the single most important fact in the whole guide: a recursor
   always has exactly one minor premise per constructor of the type. -/

/- ─── A real gotcha worth hitting immediately, empirically ───
   You might expect you can just write a `.rec` application and `#eval`
   it. Try it (this version is deliberately marked `noncomputable`,
   because IT MUST BE -- try removing that keyword and re-running this
   file to see the real error Lean gives). -/
noncomputable def isSoft_direct : FruitKind → Bool := fun f =>
  FruitKind.rec (motive := fun _fruitkind => Bool) true true false f

-- `#eval isSoft_direct .apple` would fail here with:
--   "code generator does not support recursor `FruitKind.rec` yet"
-- WHY: `.rec` is a KERNEL-level proof/type-theory tool. Lean's COMPILER
-- (the part that turns definitions into actually-runnable code for
-- `#eval`) does NOT know how to generate code for a raw, hand-written
-- `.rec` application -- only for `match`/structural-recursion syntax,
-- which the compiler specially recognizes and turns into DIFFERENT,
-- compiler-blessed elimination code under the hood. So: `.rec` terms are
-- always valid and kernel-checkable (they're just ordinary terms), but
-- not always *executable* via `#eval`.
--
-- What DOES work regardless: `#reduce`, which asks the KERNEL to reduce
-- the term directly (bypassing the compiler entirely). No dbg_trace
-- output (kernel reduction doesn't do IO), but you get the real value:
#reduce isSoft_direct .apple
#reduce isSoft_direct .pear
#reduce isSoft_direct .banana

/- To actually WATCH the dispatch happen step by step, write the
   equivalent using `match` -- which the compiler DOES know how to turn
   into real, runnable, dbg_trace-friendly code. -/
def isSoft : FruitKind → Bool
  | .apple  => dbg_trace "  -> ran the APPLE branch"; true
  | .pear   => dbg_trace "  -> ran the PEAR branch"; true
  | .banana => dbg_trace "  -> ran the BANANA branch"; false

#eval (do
  IO.println "isSoft .apple:"
  IO.println s!"  result = {isSoft .apple}"
  IO.println "isSoft .pear:"
  IO.println s!"  result = {isSoft .pear}"
  IO.println "isSoft .banana:"
  IO.println s!"  result = {isSoft .banana}"
  : IO Unit)
/- Each block above prints EXACTLY ONE dbg_trace line -- confirming,
   concretely, that dispatch really is "look at which constructor this
   is, run the ONE matching branch." `match` isn't a separate primitive
   from `.rec` conceptually -- it's compiler-supported surface syntax
   that gets elaborated down to the SAME underlying eliminator idea
   (technically `casesOn` here, since there's no genuine recursion yet --
   see R3 for where that distinction starts to matter). Confirm by
   printing the compiled definition: -/
#print isSoft
-- The body should show a `casesOn`-style match, not literal `.rec` --
-- that's the compiler-blessed path, generated automatically for you.

/- `.recOn` and `.casesOn` are close cousins, auto-generated alongside
   `.rec`. `.recOn` is `.rec` with the major premise moved to be the
   FIRST explicit argument -- same content, different argument order,
   and it has the EXACT SAME "code generator doesn't support it directly"
   limitation as `.rec`. `.casesOn`, however, genuinely IS directly
   `#eval`-able -- because it carries no ih-machinery at all (irrelevant
   in this lesson since nothing recurses yet, but it becomes the key
   distinction starting in R3). Confirm: -/
#check @FruitKind.recOn
#check @FruitKind.casesOn

def isSoft_casesOn : FruitKind → Bool := fun f =>
  FruitKind.casesOn (motive := fun _ => Bool) f true true false

#eval isSoft_casesOn .apple  -- works directly, no `noncomputable` needed!
