import TypeProgress
open Lean Elab Command

/-! bundle31 axiom audit: for every theorem defined in the project modules, the axioms it depends
on; report every theorem that depends on `sorryAx`, and the axioms of the main theorems. -/

def projMods : List Name := [`«wasm2.0», `HelperLemmas, `Subtyping, `TypingLemmas,
  `TypePreservationPure, `ExtensionLemmas, `TypePreservation, `TypeProgress]

run_cmd do
  let env ← getEnv
  let mut nThm : Nat := 0
  let mut sorried : Array Name := #[]
  let mut perMod : Std.HashMap Name Nat := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if !projMods.contains m then continue
    if let .thmInfo _ := ci then
      nThm := nThm + 1
      perMod := perMod.insert m ((perMod.getD m 0 : Nat) + 1)
      let axs ← liftCoreM (collectAxioms n)
      if axs.contains ``sorryAx then sorried := sorried.push n
  logInfo m!"theorems in project modules: {nThm}; per module: {perMod.toList}"
  logInfo m!"theorems depending on sorryAx: {sorried.size}: {sorried.toList.take 200}"
  for main in [`TLC.t_preservation, `TLC.t_progress] do
    if env.contains main then
      let axs ← liftCoreM (collectAxioms main)
      logInfo m!"axioms of {main} ({axs.size}): {axs.toList}"
