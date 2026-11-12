import Lean
open Lean Meta Elab Tactic

partial def dump : Expr → String
  | .bvar n => s!"(bvar {n})"
  | .fvar id => s!"(fvar {id.name})"
  | .sort _ => "(sort)"
  | .const n _ => s!"(const {n})"
  | .app f a => s!"(app {dump f} {dump a})"
  | .forallE n t b _ => s!"(forallE {n} :: {dump t} => {dump b})"
  | .lam n t b _ => s!"(lam {n} :: {dump t} => {dump b})"
  | e => s!"(other {e})"

-- A custom tactic that dumps the CURRENT goal's local context + remaining
-- goal type, so we can watch `intro` mutate the proof state step by step.
elab "dumpGoal" lbl:str : tactic => do
  let g ← getMainGoal
  g.withContext do
    logInfo s!"--- {lbl.getString} ---"
    let lctx ← getLCtx
    for decl in lctx do
      logInfo s!"  local hyp: {decl.userName} : {decl.type}   (fvarId={decl.fvarId.name})"
    let ty ← g.getType
    logInfo s!"  remaining goal type (raw)    : {dump ty}"
    logInfo s!"  remaining goal type (pretty) : {ty}"

theorem addComm' : ∀ (a b : Nat), a + b = b + a := by
  dumpGoal "before any intro"
  intro a
  dumpGoal "after `intro a`"
  intro b
  dumpGoal "after `intro b`"
  exact Nat.add_comm a b

-- The finished proof term itself -- is it a bare Expr.lam chain, structurally
-- identical to what we saw for `consEx`'s BODY in scratch_app.lean?
#print addComm'
