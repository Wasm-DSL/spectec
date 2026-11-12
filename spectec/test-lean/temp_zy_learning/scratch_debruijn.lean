import Lean
open Lean Meta

def consEx {α : Type} (x : α) (xs : List α) : List α := x :: xs

-- A raw dumper that shows the ACTUAL Expr constructors, with bvar indices
-- printed as bare numbers -- exactly what's stored on disk / in memory,
-- with no name resolution or pretty-printing magic applied.
partial def dump : Expr → String
  | .bvar n => s!"(bvar {n})"
  | .fvar id => s!"(fvar {id.name})"
  | .sort _ => "(sort)"
  | .const n _ => s!"(const {n})"
  | .app f a => s!"(app {dump f} {dump a})"
  | .forallE n t b _ => s!"(forallE {n} :: {dump t} => {dump b})"
  | .lam n t b _ => s!"(lam {n} :: {dump t} => {dump b})"
  | e => s!"(other {e})"

-- Example 1: dump consEx's RAW, un-opened declaration type.
-- Nothing has called forallBoundedTelescope yet -- this is exactly what's
-- stored in the environment for the `consEx` declaration.
#eval show MetaM Unit from do
  let ci ← getConstInfo ``consEx
  IO.println s!"[raw] pretty-printed : {ci.type}"
  IO.println s!"[raw] dump           : {dump ci.type}"

-- Example 2: show that the SAME variable alpha gets a DIFFERENT bvar index
-- depending on how many binders separate its use-site from its binding-site.
-- Manually peel one layer at a time WITHOUT forallBoundedTelescope, using the
-- raw constructor, to see the index change.
#eval show MetaM Unit from do
  let ci ← getConstInfo ``consEx
  match ci.type with
  | .forallE _ _ b1 _ =>  -- b1 = the type of `x`, with alpha still open above it
    IO.println s!"[peel] type of x (alpha here)      : {dump b1}"
    match b1 with
    | .forallE _ xTy b2 _ =>  -- b2 = the type of `xs`, alpha AND x now open above it
      IO.println s!"[peel] x's own type (bvar to alpha) : {dump xTy}"
      IO.println s!"[peel] type of xs (alpha here)      : {dump b2}"
      match b2 with
      | .forallE _ xsTy retTy _ =>
        IO.println s!"[peel] xs's own type (bvar to alpha): {dump xsTy}"
        IO.println s!"[peel] return type (alpha here)     : {dump retTy}"
      | _ => pure ()
    | _ => pure ()
  | _ => pure ()

-- Example 3: prove #0 is meaningless on its own -- construct a bare loose bvar
-- Expr with NO enclosing binder, and show what happens when you interrogate it.
#eval show MetaM Unit from do
  let looseVar : Expr := .bvar 0
  IO.println s!"[loose] the raw Expr itself: {dump looseVar}"
  IO.println s!"[loose] pretty-printer's rendering: {looseVar}"
  try
    let t ← inferType looseVar
    IO.println s!"[loose] inferType succeeded (unexpected!): {t}"
  catch e =>
    let msg ← e.toMessageData.toString
    IO.println s!"[loose] inferType FAILED as expected: {msg}"

-- Example 4: for contrast, show what forallBoundedTelescope's substitution
-- actually replaces bvar 0 / bvar 1 / bvar 2 WITH -- confirming they all
-- become the SAME fvar (since they all refer to the same alpha), despite
-- having had three different bvar indices at their three use-sites.
#eval show MetaM Unit from do
  let ci ← getConstInfo ``consEx
  forallBoundedTelescope ci.type (some 1) fun fvars restTy => do
    IO.println s!"[contrast] alpha's fvar : {fvars[0]!}"
    IO.println s!"[contrast] restTy dump  : {dump restTy}"
