import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON R3: a constructor field that refers back to the SAME type.

   This is the single most important step in the whole guide -- it's
   where "induction hypotheses" are born.

   Real world: a PearStack is either empty, or one more pear placed on
   top of some (smaller) PearStack. -/

inductive PearStack where
  | empty
  | onePear (rest : PearStack)

#check @PearStack.rec
/- Real output:
     PearStack.rec.{u} : {motive : PearStack → Sort u} →
       motive PearStack.empty →
       ((rest : PearStack) → motive rest → motive (PearStack.onePear rest)) →
       (t : PearStack) → motive t

   Compare carefully to R2's `withPears` minor premise, which was:
     (count : Nat) → motive (withPears count)
   and THIS one:
     (rest : PearStack) → motive rest → motive (onePear rest)

   There's an EXTRA piece: `motive rest`, sitting between the field and
   the conclusion. This is new precisely because `rest`'s type is
   `PearStack` -- the SAME type we're defining the recursor for. Whenever
   a constructor field's type is (an occurrence of) the type itself, the
   recursor's minor premise gets an EXTRA argument of type `motive <that
   field>`, right after the field itself.

   This extra argument is universally called the INDUCTION HYPOTHESIS
   ("ih"): "here's the answer I've ALREADY worked out for the smaller
   PearStack `rest` -- now use it (or not) to produce the answer for the
   bigger one, `onePear rest`." The recursor doesn't just hand you raw
   data anymore; for self-referential fields, it hands you a
   PRE-COMPUTED RESULT for that smaller piece, worked out one level down. -/

noncomputable def pearCount_direct : PearStack → Nat := fun s =>
  PearStack.rec (motive := fun _pearstack => Nat) 0 (fun _rest ih => ih + 1) s

def stackOf3 := PearStack.onePear (PearStack.onePear (PearStack.onePear .empty))

#reduce pearCount_direct stackOf3   -- kernel-reduces to 3, no trace output

/- To WATCH the ih actually arrive at each level, write the equivalent as
   an ordinary recursive `def` -- the recursive call `pearCount rest` IS
   the ih, just phrased as a normal function call instead of an explicit
   `.rec` argument. Same concept, compiler-supported, dbg_trace-friendly. -/
def pearCount : PearStack → Nat
  | .empty => 0
  | .onePear rest =>
    let ih := pearCount rest
    dbg_trace s!"  -> onePear branch: ih (count for `rest`) = {ih}, so I return {ih + 1}"
    ih + 1

#eval (do
  IO.println "pearCount stackOf3:"
  IO.println s!"  final result = {pearCount stackOf3}"
  : IO Unit)
/- Watch the trace: it fires THREE times, from the INNERMOST call
   outward, with ih going 0 → 1 → 2, before the final `+1` gives 3. Lean
   had to fully resolve the innermost `.empty` first (getting 0), then
   use THAT as the ih to handle the next `onePear` layer (getting 1), and
   so on outward -- exactly the same evaluation order `pearCount_direct`
   goes through internally, just now visible. -/

/- Contrast with `.casesOn`, which has NO ih at all -- it only hands you
   the raw field, never a pre-computed answer for it. -/
#check @PearStack.casesOn
-- (rest : PearStack) → motive (onePear rest)      -- no `motive rest` here!
/- `casesOn` is for when you want to know WHICH constructor built a value
   and grab its raw fields, but don't need (or want) a recursive answer
   about those fields. `rec` is for when you genuinely need to recurse.
   And unlike `.rec`, `.casesOn` genuinely IS directly `#eval`-able (no
   ih-machinery to trip up the compiler): -/
def isEmpty : PearStack → Bool := fun s =>
  PearStack.casesOn (motive := fun _ => Bool) s true (fun _rest => false)

#eval isEmpty stackOf3
#eval isEmpty .empty
