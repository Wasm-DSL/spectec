import Lean
open Lean Meta

-- Our own plain functions, to avoid compiler `borrowed`/universe-level noise
-- that Nat.add / List.cons carry in their real, low-level declared types.
def addTwo (a b : Nat) : Nat := a + b
def consEx {α : Type} (x : α) (xs : List α) : List α := x :: xs

-- Example 1: open ZERO binders of a 2-arg function type.
#eval show MetaM Unit from do
  let ty ← inferType (mkConst ``addTwo)
  IO.println s!"[ex1] full ty          = {ty}"
  forallBoundedTelescope ty (some 0) fun fvars restTy => do
    IO.println s!"[ex1] fvars (0 opened) = {fvars}"
    IO.println s!"[ex1] restTy           = {restTy}"

-- Example 2: open exactly ONE binder of addTwo : Nat → Nat → Nat
#eval show MetaM Unit from do
  let ty ← inferType (mkConst ``addTwo)
  forallBoundedTelescope ty (some 1) fun fvars restTy => do
    IO.println s!"[ex2] fvars (1 opened) = {fvars}"
    IO.println s!"[ex2] restTy           = {restTy}"
    let fv := fvars[0]!
    let decl ← fv.fvarId!.getDecl
    IO.println s!"[ex2] fvar {fv} -> userName={decl.userName}, type={decl.type}"

-- Example 3: a DEPENDENT type -- consEx : {α : Type} → α → List α → List α
-- Opening just the implicit {α} binder shows later binders getting SUBSTITUTED.
#eval show MetaM Unit from do
  let ty ← inferType (mkConst ``consEx)
  IO.println s!"[ex3] full ty              = {ty}"
  forallBoundedTelescope ty (some 1) fun fvars restTy => do
    IO.println s!"[ex3] fvars (1 opened)     = {fvars}"
    IO.println s!"[ex3] restTy (α replaced!) = {restTy}"

-- Example 4: open ALL THREE binders of consEx at once.
#eval show MetaM Unit from do
  let ty ← inferType (mkConst ``consEx)
  forallBoundedTelescope ty (some 3) fun fvars restTy => do
    IO.println s!"[ex4] fvars (3 opened) = {fvars}"
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      IO.println s!"[ex4]   fvar {fv} -> userName={decl.userName}, type={decl.type}"
    IO.println s!"[ex4] restTy = {restTy}"

-- Example 5: PROVE the scoping claim -- smuggle an fvar out of the callback via a Ref,
-- then try to use it AFTER forallBoundedTelescope has returned and popped the context.
#eval show MetaM Unit from do
  let fvarRef ← IO.mkRef (none : Option Expr)
  let ty ← inferType (mkConst ``addTwo)
  forallBoundedTelescope ty (some 1) fun fvars _ => do
    IO.println s!"[ex5] inside callback: inferType succeeds = {← inferType fvars[0]!}"
    fvarRef.set (some fvars[0]!)
  -- callback has returned -- local context has been restored to what it was before
  let some fv ← fvarRef.get | return
  IO.println s!"[ex5] outside callback, trying to reuse fvar {fv} ..."
  try
    let t ← inferType fv
    IO.println s!"[ex5] inferType succeeded (unexpected!): {t}"
  catch e =>
    let msg ← e.toMessageData.toString
    IO.println s!"[ex5] inferType FAILED as expected: {msg}"
