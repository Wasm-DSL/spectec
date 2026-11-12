import TypeProgress
open Lean Elab Command

/-! bundle33 inductive-metadata dump (complements EnvDump33, which hashes types/values only): for every
inductive, constructor and recursor of the 9 project modules, the structural metadata Lean keeps: parameters,
indices, constructor list, constructor index and field count, recursor motives/minors/rules. DUMP_MODE=old maps
the old wf_instr/wf_admininstr case names by meaning (same renaming as EnvDump33). -/

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

def rn (old : Bool) (n : Name) : Name := if old then (renameName n).getD n else n

run_cmd do
  let env ← getEnv
  let old := (← IO.getEnv "DUMP_MODE") == some "old"
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if !projMods.contains m then continue
    match ci with
    | .inductInfo v =>
      let cs := String.intercalate "," (v.ctors.map (fun c => toString (rn old c)))
      lines := lines.push s!"{m}\tinduct\t{rn old n}\tparams={v.numParams} indices={v.numIndices} nctors={v.ctors.length} nested={v.numNested} rec={v.isRec} reflexive={v.isReflexive} all={v.all.length}\t{cs}"
    | .ctorInfo v =>
      lines := lines.push s!"{m}\tctor\t{rn old n}\tinduct={rn old v.induct} cidx={v.cidx} params={v.numParams} fields={v.numFields}\t-"
    | .recInfo v =>
      lines := lines.push s!"{m}\trec\t{rn old n}\tparams={v.numParams} indices={v.numIndices} motives={v.numMotives} minors={v.numMinors} rules={v.rules.length} k={v.k}\t-"
    | _ => pure ()
  let out ← IO.getEnv "DUMP_OUT"
  IO.FS.writeFile (out.getD "indmeta.tsv") (String.intercalate "\n" ((lines.qsort (· < ·)).toList) ++ "\n")
  logInfo m!"mode old={old}; inductive/constructor/recursor entries: {lines.size}"
