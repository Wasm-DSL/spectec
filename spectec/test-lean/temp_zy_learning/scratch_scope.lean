import Lean
open Lean Meta

def consEx {α : Type} (x : α) (xs : List α) : List α := x :: xs

-- Measure how many local declarations are visible before / during / after
-- a forallBoundedTelescope call, to see the "extend, then restore" bracket
-- shape directly, as numbers.
#eval show MetaM Unit from do
  let ci ← getConstInfo ``consEx
  let before ← getLCtx
  IO.println s!"[bracket] BEFORE  : {before.decls.size} decls"
  forallBoundedTelescope ci.type (some 3) fun fvars _ => do
    let during ← getLCtx
    IO.println s!"[bracket] DURING  : {during.decls.size} decls (fvars={fvars.size})"
  let after ← getLCtx
  IO.println s!"[bracket] AFTER   : {after.decls.size} decls"

-- Now the exception-safety test: throw INSIDE the callback, catch OUTSIDE,
-- and check the context was still cleaned up -- i.e. the extension isn't
-- undone by a manual "pop" step at the end of a happy path, it's undone by
-- the combinator itself no matter how the callback exits.
#eval show MetaM Unit from do
  let ci ← getConstInfo ``consEx
  let before ← getLCtx
  IO.println s!"[exn-safety] BEFORE : {before.decls.size} decls"
  try
    forallBoundedTelescope ci.type (some 3) fun fvars _ => do
      let during ← getLCtx
      IO.println s!"[exn-safety] DURING : {during.decls.size} decls (fvars={fvars.size})"
      throwError "deliberate failure mid-callback"
  catch e =>
    let msg ← e.toMessageData.toString
    IO.println s!"[exn-safety] caught : {msg}"
  let after ← getLCtx
  IO.println s!"[exn-safety] AFTER  : {after.decls.size} decls  -- restored even though callback threw!"
