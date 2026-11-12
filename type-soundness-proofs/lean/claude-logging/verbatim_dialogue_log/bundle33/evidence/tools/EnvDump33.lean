import TypeProgress
open Lean Elab Command

/-! bundle33 environment dump: every constant defined in the 9 project modules, with its kind, a hash of
its type and of its value (Expr hashes ignore binder names), and, for theorems, its axioms. With
DUMP_MODE=old, the old constructor names `wf_instr.instr_case_K` / `wf_admininstr.admininstr_case_K` (and the
same constructors of the auxiliary `wf_instr.below` / `wf_admininstr.below`)
(K >= 20) are first renamed to K-1 (and the removed EXTEND case 19 to `..._case_19_EXTEND_removed`), so that the old and new dumps can be compared by meaning. -/

def projMods : List Name := [`ExtendedDeriveDecEq, `«wasm2.0», `HelperLemmas, `Subtyping, `TypingLemmas,
  `TypePreservationPure, `ExtensionLemmas, `TypePreservation, `TypeProgress]

def shiftCtor (pre : Name) (fam : String) (s : String) : Option Name :=
  if s.startsWith (fam ++ "_case_") then
    match (s.drop (fam.length + 6)).toString.toNat? with
    | some k => if k ≥ 20 then some (.str pre s!"{fam}_case_{k-1}")
      else if k == 19 then some (.str pre s!"{fam}_case_19_EXTEND_removed") else none
    | none => none
  else none

def renameName : Name → Option Name
  | .str p s =>
    if p == `wf_instr || p == `wf_instr.below then shiftCtor p "instr" s
    else if p == `wf_admininstr || p == `wf_admininstr.below then shiftCtor p "admininstr" s
    else none
  | _ => none

def ren (old : Bool) (e : Expr) : Expr :=
  if !old then e else e.replace fun x => match x with
    | .const n ls => (renameName n).map fun n' => .const n' ls
    | _ => none

run_cmd do
  let env ← getEnv
  let old := (← IO.getEnv "DUMP_MODE") == some "old"
  let mut lines : Array String := #[]
  let mut nThm : Nat := 0
  let mut sorried : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if !projMods.contains m then continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom" | .inductInfo _ => "induct"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
    let nm := if old then (renameName n).getD n else n
    let th := (ren old ci.type).hash
    let vh := match ci.value? (allowOpaque := true) with
      | some v => toString (ren old v).hash
      | none => "-"
    let mut axs := "-"
    if let .thmInfo _ := ci then
      nThm := nThm + 1
      let a ← liftCoreM (collectAxioms n)
      if a.contains ``sorryAx then sorried := sorried.push n
      axs := String.intercalate "," ((a.map toString).qsort (· < ·)).toList
    lines := lines.push s!"{m}\t{kind}\t{nm}\t{th}\t{vh}\t{axs}"
  let out ← IO.getEnv "DUMP_OUT"
  IO.FS.writeFile (out.getD "dump.tsv") (String.intercalate "\n" ((lines.qsort (· < ·)).toList) ++ "\n")
  logInfo m!"mode old={old}; constants dumped: {lines.size}; theorems: {nThm}; depending on sorryAx: {sorried.size}: {sorried.toList.take 50}"
  for main in [`TLC.t_preservation, `TLC.t_progress] do
    if env.contains main then
      let a ← liftCoreM (collectAxioms main)
      logInfo m!"axioms of {main} ({a.size}): {a.toList}"
