import Lean
open Lean

/-!
Kernel replay of the 8 project modules (`wasm2.0` and the 7 downstream proof modules) with every
`Inhabited` instance made opaque (bundle31 generalization of the bundle23 audit).

* Instances defined in `wasm2.0` (the derived `instInhabited…`) are re-added as axioms.
* Instances from core that `wasm2.0` refers to (`instInhabitedNat`, …) are replaced, inside
  `wasm2.0`'s terms only, by fresh axioms `_audit.<name>` of the same type.
* Every theorem of `wasm2.0` is then re-checked by the kernel. A theorem fails exactly when its proof
  needs the value of some `default` (for example `Option.get! none = 0`, or `(default : val) = …`).
Everything else (definitions, inductives) is re-added unchanged apart from that renaming.
-/

def isInstType (t : Expr) : Bool := t.getForallBody.getAppFn.isConstOf ``Inhabited

structure MD where
  constants : Array ConstantInfo

def auditMain (oleanPaths : List System.FilePath) (outPath : System.FilePath) : IO Unit := do
  let env0 ← importModules #[{module := `Mathlib.Tactic}, {module := `ExtendedDeriveDecEq}] {} (trustLevel := 1024)
  let mut consts : Array ConstantInfo := #[]
  for p in oleanPaths do
    let (md, _region) ← readModuleData p
    consts := consts ++ md.constants
  let md : MD := {constants := consts}
  let mut byName : Std.HashMap Name ConstantInfo := {}
  for c in md.constants do byName := byName.insert c.name c
  -- canonical group name for inductive families (ctors/recs map to their inductive group)
  let mut canon : Std.HashMap Name Name := {}
  for c in md.constants do
    match c with
    | .inductInfo v => for n in v.all do canon := canon.insert n v.all.head!
    | _ => pure ()
  for c in md.constants do
    match c with
    | .ctorInfo v => canon := canon.insert c.name (canon.getD v.induct v.induct)
    | .recInfo v => canon := canon.insert c.name (canon.getD v.all.head! v.all.head!)
    | _ => pure ()
  -- external Inhabited instances referenced by the module
  let mut ext : NameSet := {}
  for c in md.constants do
    let es := [c.type] ++ (match c.value? (allowOpaque := true) with | some v => [v] | none => [])
    for e in es do
      for n in e.getUsedConstants do
        if !byName.contains n then
          if let some ci := env0.find? n then
            if isInstType ci.type then ext := ext.insert n
  let ren (e : Expr) : Expr := e.replace fun x => match x with
    | .const n ls => if ext.contains n then some (.const (`_audit ++ n) ls) else none
    | _ => none
  let mut kenv := env0.toKernelEnv
  for n in ext.toList do
    let ci := (env0.find? n).get!
    match Kernel.Environment.addDeclWithoutChecking kenv (.axiomDecl {name := `_audit ++ n, levelParams := ci.levelParams, type := ci.type, isUnsafe := false}) with
    | .ok k => kenv := k
    | .error _ => throw (IO.userError s!"could not add audit axiom for {n}")
  -- dependency-ordered replay
  let mut failures : Array (Name × String) := #[]
  let mut nThm := 0
  let mut nInst := 0
  let mut order : Array Name := #[]
  -- iterative DFS producing a topological order of canonical names
  let deps (n : Name) : List Name := Id.run do
    let ci := byName[n]!
    let grp : List Name := match ci with | .inductInfo v => v.all | _ => [n]
    let mut out : List Name := []
    for g in grp do
      let gi := byName[g]!
      let mut es : List Expr := [gi.type]
      if let some v := gi.value? (allowOpaque := true) then es := v :: es
      if let .inductInfo iv := gi then
        for ct in iv.ctors do es := byName[ct]!.type :: es
      for e in es do
        for d in e.getUsedConstants do
          if byName.contains d then
            let cd := canon.getD d d
            if cd != n then out := cd :: out
    return out
  let mut visited : NameSet := {}
  for c0 in md.constants do
    let root := canon.getD c0.name c0.name
    if visited.contains root then continue
    let mut stack : List (Name × Bool) := [(root, false)]
    while !stack.isEmpty do
      let (n, post) := stack.head!
      stack := stack.tail!
      if post then
        order := order.push n
      else if !visited.contains n then
        visited := visited.insert n
        stack := (n, true) :: stack
        for d in deps n do
          if !visited.contains d then stack := (d, false) :: stack
  for n in order do
    let ci := byName[n]!
    let decl? : Option (Declaration × Bool) := match ci with
      | .inductInfo v =>
        let types := v.all.map fun t =>
          let tv := byName[t]!
          let ctors := match tv with
            | .inductInfo iv => iv.ctors.map fun ct => ({name := ct, type := ren byName[ct]!.type} : Constructor)
            | _ => []
          ({name := t, type := ren tv.type, ctors} : InductiveType)
        some (.inductDecl v.levelParams v.numParams types v.isUnsafe, false)
      | .defnInfo v =>
        if isInstType v.type then
          some (.axiomDecl {name := v.name, levelParams := v.levelParams, type := ren v.type, isUnsafe := false}, false)
        else
          some (.defnDecl {v with type := ren v.type, value := ren v.value}, false)
      | .thmInfo v => some (.thmDecl {v with type := ren v.type, value := ren v.value}, true)
      | .opaqueInfo v => some (.opaqueDecl {v with type := ren v.type, value := ren v.value}, false)
      | .axiomInfo v => some (.axiomDecl {v with type := ren v.type}, false)
      | _ => none
    match decl? with
    | none => pure ()
    | some (d, check) =>
      if let .defnInfo v := ci then
        if isInstType v.type then nInst := nInst + 1
      if check then
        nThm := nThm + 1
        match Kernel.Environment.addDeclCore kenv 0 d none with
        | .ok k => kenv := k
        | .error ex =>
          let msg := (← (ex.toMessageData {}).toString)
          failures := failures.push (n, (msg.take 600).toString)
          match Kernel.Environment.addDeclWithoutChecking kenv d with
          | .ok k => kenv := k
          | .error _ => throw (IO.userError s!"cannot add {n} even without checking")
      else
        match Kernel.Environment.addDeclWithoutChecking kenv d with
        | .ok k => kenv := k
        | .error ex => throw (IO.userError s!"cannot add {n}: {← (ex.toMessageData {}).toString}")
  let mut out := s!"module constants: {md.constants.size}; replayed groups: {order.size}; theorems checked: {nThm}; module Inhabited instances made opaque: {nInst}; external instances made opaque: {ext.toList}\n"
  out := out ++ s!"theorems needing a default value: {failures.size}\n"
  for (n, m) in failures do out := out ++ s!"--- {n}\n{m}\n"
  IO.FS.writeFile outPath out
  IO.println out
def mods : List String := ["AuditCtl33", "wasm2.0", "HelperLemmas", "Subtyping", "TypingLemmas", "TypePreservationPure", "ExtensionLemmas", "TypePreservation", "TypeProgress"]
def runAll : IO Unit := do
  let bd ← IO.getEnv "AUDIT_BUILD"
  let out ← IO.getEnv "AUDIT_OUT"
  auditMain (mods.map fun m => System.FilePath.mk (bd.get! ++ "/" ++ m ++ ".olean")) (out.get!)
#eval runAll
