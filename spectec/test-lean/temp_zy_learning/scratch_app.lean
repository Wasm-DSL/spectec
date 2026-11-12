import Lean
open Lean Meta

def consEx {α : Type} (x : α) (xs : List α) : List α := x :: xs

-- Fuller dumper: this time show universe levels on `const`, and the
-- component pieces of `app` labeled explicitly (function vs argument).
partial def dump : Expr → String
  | .bvar n => s!"(bvar {n})"
  | .fvar id => s!"(fvar {id.name})"
  | .sort u => s!"(sort {u})"
  | .const n us => s!"(const {n} levels={us})"
  | .app f a => s!"(app fn={dump f} arg={dump a})"
  | .forallE n t b _ => s!"(forallE {n} :: {dump t} => {dump b})"
  | .lam n t b _ => s!"(lam {n} :: {dump t} => {dump b})"
  | e => s!"(other {e})"

-- Example A: re-dump just the `List α` subterm, fully labeled.
#eval show MetaM Unit from do
  let ci ← getConstInfo ``consEx
  match ci.type with
  | .forallE _ _ (.forallE _ _ (.forallE _ xsTy _ _) _) _ =>
    IO.println s!"[A] xs's type (List alpha) raw  : {dump xsTy}"
    IO.println s!"[A] pretty-printed              : {xsTy}"
  | _ => pure ()

-- Example B: what List itself actually is, looked up directly.
#eval show MetaM Unit from do
  let ci ← getConstInfo ``List
  IO.println s!"[B] List's own type: {ci.type}"

-- Example C: a TWO-argument application (List.cons α x), to show that
-- multi-arg application is just NESTED single-arg `app` nodes (currying),
-- not one `app` node with an argument array.
#eval show MetaM Unit from do
  let ci ← getConstInfo ``consEx
  -- reach the body (not just the type) to find a real List.cons application
  match ci.value! with
  | .lam _ _ (.lam _ _ (.lam _ _ body _) _) _ =>
    IO.println s!"[C] consEx's body (x :: xs) raw : {dump body}"
    IO.println s!"[C] pretty-printed               : {body}"
  | _ =>
    IO.println "[C] shape didn't match, dumping whole value:"
    IO.println (dump ci.value!)
