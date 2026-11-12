import «wasm2.0»
open Lean Elab Command

/-! bundle32 axiom check: for every theorem defined in module `wasm2.0`, the axioms it depends on
(written as TSV to the file named by env var AX_OUT); summary of `sorryAx` dependents. -/

run_cmd do
  let env ← getEnv
  let mut nThm : Nat := 0
  let mut sorried : Array Name := #[]
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if m != `«wasm2.0» then continue
    if let .thmInfo _ := ci then
      nThm := nThm + 1
      let axs ← liftCoreM (collectAxioms n)
      if axs.contains ``sorryAx then sorried := sorried.push n
      let names := (axs.map toString).qsort (· < ·)
      lines := lines.push s!"{n}\t{String.intercalate "," names.toList}"
  let out ← IO.getEnv "AX_OUT"
  IO.FS.writeFile (out.getD "ax.tsv") (String.intercalate "\n" ((lines.qsort (· < ·)).toList) ++ "\n")
  logInfo m!"theorems in module wasm2.0: {nThm}; depending on sorryAx: {sorried.size}: {sorried.toList.take 50}"
