import TypeProgress
open Lean Elab Command

/-! bundle33 cause probe (NEW build only): for every theorem and definition of the 9 project modules, which of the
constants its value refers to directly are in the set S read from CAUSE_SET (one name per line: the NEW declarations
whose type changed, or that exist only in NEW). Output: name, number of such references, up to 4 of them. -/

def projMods : List Name := [`ExtendedDeriveDecEq, `«wasm2.0», `HelperLemmas, `Subtyping, `TypingLemmas,
  `TypePreservationPure, `ExtensionLemmas, `TypePreservation, `TypeProgress]


run_cmd do
  let env ← getEnv
  let setFile ← IO.getEnv "CAUSE_SET"
  let txt ← IO.FS.readFile (setFile.getD "set.txt")
  -- compared as printed strings, exactly as EnvDump33 printed the names (private and hygienic names have
  -- numeric components, so parsing the strings back into `Name`s would not round-trip)
  let mut S : Std.HashSet String := {}
  for l in txt.splitOn "\n" do
    if l != "" then S := S.insert l
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if !projMods.contains m then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let used := v.getUsedConstants
    let hits := used.filter (fun c => S.contains (toString c))
    let ex := String.intercalate "," ((hits.toList.take 4).map toString)
    lines := lines.push s!"{m}\t{n}\t{hits.size}\t{ex}"
  let out ← IO.getEnv "CAUSE_OUT"
  IO.FS.writeFile (out.getD "cause.tsv") (String.intercalate "\n" ((lines.qsort (· < ·)).toList) ++ "\n")
  logInfo m!"set size {S.size}; values scanned {lines.size}"
