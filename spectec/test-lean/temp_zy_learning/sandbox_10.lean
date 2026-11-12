/-
  sandbox_10.lean -- ExtendedDeriveDecEq.lean, pasted verbatim below, with a
  `dbg_trace` inserted after essentially every meaningful computational step
  (every `let`, every branch taken, every loop iteration) so you can watch
  the whole algorithm unfold step by step for six worked examples: Shape
  (simple), Tree (nested), Even/Odd (mutual), Expr/Stmt (nested+mutual), and
  Rose (polymorphic+nested).

  TWO NECESSARY ADJUSTMENTS FROM "every line has a #print":
  1. `#print` is a top-level COMMAND -- it cannot appear inside a function
     body's `do`-block (confirmed empirically earlier this session: writing
     `#print x` inside a `do` block is a hard parse error, "unexpected
     token '#print'; expected term"). `dbg_trace` is the correct substitute:
     it works as an ordinary statement in ANY monad (confirmed: it's one of
     the reserved leading tokens `do`-notation recognizes,
     `Lean/Parser/Do.lean`'s `notFollowedByRedefinedTermToken` list), and
     its output streams to the same terminal/build-log channel we've used
     to capture `trace[...]` output all session. Only the true top-level
     spots below (after each generated `def`/`instance` is actually
     registered) use real `#print`.
  2. "Every line" here means every meaningful computational step -- blank
     lines, comments, and a `structure`'s field *declarations* (you can't
     print in the middle of declaring a field) have nothing to introspect,
     so those are skipped; every `let`, `if`, `match` branch, and loop body
     gets a trace point.

  RUNNING THIS FILE: `lake env lean sandbox_10.lean` from test-lean/ (or
  `lake build sandbox_10` once it's added to lakefile.lean's globs). Output
  is voluminous by design -- pipe through `grep` for the function/example
  you care about, e.g. `grep '\[analyzeRecursor\]'` or `grep '=== Tree '`.

  Printing note: `FieldInfo`/`CtorInfo`/`RecursorAnalysis` only `deriving
  Repr` (not `ToString`), so those need `reprStr v`, not plain `s!"{v}"`
  (confirmed empirically: plain interpolation fails to synthesize
  `ToString` for a Repr-only structure). Everything else here (`Expr`,
  `Name`, `Nat`, `Bool`, `Term`, `Ident`) has ordinary `ToString`.
-/

import Lean
import Lean.Elab.Deriving.Util
import Lean.Meta.Constructions.CasesOnSameCtor
import Lean.Meta.Constructions.CtorIdx

open Lean Meta Elab Command Term Parser.Term

namespace DecEqMutual.Derive

-- ── mkFieldId ──────────────────────────────────────────────────────────
private def mkFieldId (prefix_ : String) (i : Nat) : Ident :=
  dbg_trace s!"[mkFieldId] IN  prefix_={prefix_} i={i}";
  let result := mkIdent (.mkSimple s!"{prefix_}{i}")
  dbg_trace s!"[mkFieldId] OUT result={result}";
  result

/-- Info about one field of a constructor. -/
structure FieldInfo where
  type : Expr
  recursiveMotiveIdx : Option Nat  -- which motive provides IH, if any
  isProp : Bool := false           -- true for Prop-typed fields (skip via proof irrelevance)
deriving Repr, Inhabited

/-- Info about one constructor. -/
structure CtorInfo where
  name : Name
  typeIdx : Nat            -- motive index this constructor belongs to
  fields : Array FieldInfo
deriving Repr, Inhabited

/-- Analysis of a mutual inductive block, including auxiliary container types. -/
structure RecursorAnalysis where
  typeNames : Array Name           -- user type names, fully qualified (for lookups)
  defBaseNames : Array Name        -- user type names, namespace-stripped (for def generation)
  numUserTypes : Nat
  numMotives : Nat                 -- total motives including auxiliary
  motiveDomainStxs : Array Term    -- domain type syntax per motive (delab'd)
  motiveIndNames : Array Name     -- inductive name underlying each motive
  motiveIndexBinderStxs : Array (Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
  paramBinderStxs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  instBinderStxs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  ctorsByType : Array (Array CtorInfo)  -- motive idx → constructors
  isPrivate : Bool                 -- source inductive is `private` — emit `private def`

-- ── computeIsRecursive ────────────────────────────────────────────────
/-- Compute which motives are part of a recursive call cycle (Floyd-Warshall). -/
private def computeIsRecursive (analysis : RecursorAnalysis) : Array Bool := Id.run do
  let n := analysis.numMotives
  dbg_trace s!"[computeIsRecursive] IN  numMotives={n}"
  let mut reach := Array.replicate n (Array.replicate n false)
  for i in [:n] do
    for ctor in analysis.ctorsByType[i]! do
      for field in ctor.fields do
        if let some j := field.recursiveMotiveIdx then
          dbg_trace s!"[computeIsRecursive] direct edge: motive {i} (ctor {ctor.name}) → motive {j}"
          reach := reach.modify i (·.set! j true)
  dbg_trace s!"[computeIsRecursive] reach after direct-edge pass: {reach}"
  for k in [:n] do
    for i in [:n] do
      for j in [:n] do
        if reach[i]![k]! && reach[k]![j]! then
          if !reach[i]![j]! then
            dbg_trace s!"[computeIsRecursive] closure adds: {i} → {j} (via {k})"
          reach := reach.modify i (·.set! j true)
  dbg_trace s!"[computeIsRecursive] reach after closure: {reach}"
  let result := (Array.range n).map fun i => reach[i]![i]!
  dbg_trace s!"[computeIsRecursive] OUT isRecursive={result}"
  return result

-- ── extractBinderInfos ────────────────────────────────────────────────
/-- Store the first `n` binder infos from a forall type to be used for
    reconstructing the binder style later. -/
private def extractBinderInfos (type : Expr) (n : Nat) : Array BinderInfo := Id.run do
  dbg_trace s!"[extractBinderInfos] IN  type={type} n={n}"
  let mut result : Array BinderInfo := #[]
  let mut rest := type
  for i in [:n] do
    match rest with
    | .forallE _name _domain body binfo =>
      dbg_trace s!"[extractBinderInfos] binder {i}: name={_name} domain={_domain} binfo={repr binfo}"
      result := result.push binfo
      rest := body
    | _ =>
      dbg_trace s!"[extractBinderInfos] ran out of foralls early at i={i}, breaking"
      break
  dbg_trace s!"[extractBinderInfos] OUT result={repr result}"
  return result

-- ── isPropInductive ───────────────────────────────────────────────────
/-- Is the inductive `indName` Prop-valued (i.e. its resultant sort is `Prop`)? -/
private def isPropInductive (indName : Name) : MetaM Bool := do
  dbg_trace s!"[isPropInductive] IN  indName={indName}"
  let indVal ← getConstInfoInduct indName
  let body := indVal.type.getForallBody
  dbg_trace s!"[isPropInductive] indVal.type={indVal.type}"
  dbg_trace s!"[isPropInductive] getForallBody={body}"
  let result := match body with
    | .sort l => l.isZero
    | _ => false
  dbg_trace s!"[isPropInductive] OUT result={result}"
  return result

-- ── motiveDecEqName ───────────────────────────────────────────────────
/-- Name for the decEq function of a given motive.
    Uses namespace-stripped `defBaseNames` so that `def <name>` inside the
    current namespace produces correctly single-prefixed constants. -/
private def motiveDecEqName (analysis : RecursorAnalysis) (motiveIdx : Nat) : Name :=
  dbg_trace s!"[motiveDecEqName] IN  motiveIdx={motiveIdx} numUserTypes={analysis.numUserTypes}";
  if motiveIdx < analysis.numUserTypes then
    dbg_trace s!"[motiveDecEqName] branch: user type";
    let result := analysis.defBaseNames[motiveIdx]! ++ `decEq
    dbg_trace s!"[motiveDecEqName] OUT result={result}";
    result
  else
    dbg_trace s!"[motiveDecEqName] branch: auxiliary motive";
    -- Numeric name component (`.mkNum`) avoids collision with user-defined names,
    -- since users cannot create numeric name components in normal code.
    let result := analysis.defBaseNames[0]! ++ `_auxDecEq ++ .mkNum .anonymous motiveIdx
    dbg_trace s!"[motiveDecEqName] OUT result={result}";
    result

-- ── analyzeRecursor ───────────────────────────────────────────────────
/-- Analyze the recursor of a mutual inductive block to extract all
    information needed for generating DecidableEq definitions. -/
def analyzeRecursor (indName : Name) : MetaM RecursorAnalysis := do
  dbg_trace s!"[analyzeRecursor] IN  indName={indName}"
  -- The recursor's type signature encodes everything we need:
  --   rec.{u} : (params...) → (motives...) → (minors...) → (target) → result
  let indVal ← getConstInfoInduct indName
  let typeNames := indVal.all.toArray
  dbg_trace s!"[analyzeRecursor] indVal.all (typeNames)={typeNames}"
  let numUserTypes := typeNames.size
  dbg_trace s!"[analyzeRecursor] numUserTypes={numUserTypes}"
  let firstType := typeNames[0]!
  dbg_trace s!"[analyzeRecursor] firstType={firstType}"
  let recName := mkRecName firstType
  dbg_trace s!"[analyzeRecursor] recName={recName}"
  let recVal ← getConstInfoRec recName
  let numParams := recVal.numParams
  let numMotives := recVal.numMotives
  let numMinors := recVal.numMinors
  dbg_trace s!"[analyzeRecursor] numParams={numParams} numMotives={numMotives} numMinors={numMinors}"
  dbg_trace s!"[analyzeRecursor] recVal.type={recVal.type}"

  -- The recursor makes all params explicit, losing the original
  -- implicit/instImplicit distinction. Read it from the inductive type itself.
  let origBinderInfos := extractBinderInfos indVal.type numParams
  dbg_trace s!"[analyzeRecursor] origBinderInfos={repr origBinderInfos}"

  let (paramBinderStxs, instBinderStxs, motiveDomainStxs, motiveIndNames,
       motiveIndexBinderStxs, ctorsByType) ←
    -- Open the first `numParams` binders of the recursor type.
    -- For each param, restore its original binder info and
    -- generate syntax: {α : Type} for type params, [DecidableEq α] for
    -- type params that admit DecidableEq, [inst : Class] for instances
    -- which needs to be categorised back to instance binders.
    forallBoundedTelescope recVal.type (some numParams) (fun paramVars restType0 => do
      dbg_trace s!"[analyzeRecursor:params] paramVars={paramVars} restType0={restType0}"
      let mut paramBinderStxs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      let mut instBinderStxs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]

      for i in [:numParams] do
        let v := paramVars[i]!
        -- LocalDecl gives us userName and type for this fvar;
        -- binderInfo is ignored (recursor makes all params explicit).
        let ldecl ← v.fvarId!.getDecl
        let nameId := mkIdent ldecl.userName
        let binfo := if i < origBinderInfos.size then origBinderInfos[i]! else .implicit
        dbg_trace s!"[analyzeRecursor:params] param {i}: userName={ldecl.userName} type={ldecl.type} binfo={repr binfo}"
        let typeStx ← withOptions (fun o => pp.fullNames.set o true) <|
          PrettyPrinter.delab ldecl.type
        dbg_trace s!"[analyzeRecursor:params] param {i}: delaborated typeStx={typeStx}"

        if binfo == .instImplicit then
          dbg_trace s!"[analyzeRecursor:params] param {i}: is instImplicit → instBinderStxs"
          instBinderStxs := instBinderStxs.push (← `(bracketedBinder| [$typeStx]))
        else
          dbg_trace s!"[analyzeRecursor:params] param {i}: forwarding as implicit type param → paramBinderStxs"
          -- Type/value param: forward as {name : Type}
          paramBinderStxs := paramBinderStxs.push (← `(bracketedBinder| {$nameId : $typeStx}))
          -- For params that admit DecidableEq, add [DecidableEq name]
          -- (uses mkAppM + isTypeCorrect, matching the standard deriving infrastructure,
          -- which is more robust than a simple isSort check)
          try
            let c ← mkAppM ``DecidableEq #[v]
            let ok ← isTypeCorrect c
            dbg_trace s!"[analyzeRecursor:params] param {i}: DecidableEq probe c={c} isTypeCorrect={ok}"
            if ok then
              let decEqType ← `(DecidableEq $nameId)
              dbg_trace s!"[analyzeRecursor:params] param {i}: adding instance requirement {decEqType}"
              instBinderStxs := instBinderStxs.push (← `(bracketedBinder| [$decEqType]))
          catch e =>
            let msg ← e.toMessageData.toString
            dbg_trace s!"[analyzeRecursor:params] param {i}: DecidableEq probe failed ({msg}), skipping"
            pure ()

      dbg_trace s!"[analyzeRecursor:params] OUT paramBinderStxs={paramBinderStxs} instBinderStxs={instBinderStxs}"

      -- After params, the recursor has one motive per type in the mutual block.
      -- Each motive has type:  (i₁ : I₁) → ... → (iₖ : Iₖ) → T params i₁...iₖ → Sort u
      -- We peel all forall binders: the last one's domain is the inductive type
      -- application (giving us `domainStx`), and the preceding binders are index
      -- binders (giving us `indexBinderStxs` for each motive).
      forallBoundedTelescope restType0 (some numMotives) (fun motiveVars restType => do
        dbg_trace s!"[analyzeRecursor:motives] motiveVars={motiveVars} restType={restType}"
        let motiveDomainInfo ← motiveVars.mapM fun mv => do
          let mType ← inferType mv
          dbg_trace s!"[analyzeRecursor:motives] motive var {mv}: type={mType}"
          forallTelescope mType fun fvars _sortBody => do
            if fvars.isEmpty then throwError "unexpected motive type (no binders): {mType}"
            let mainFvar := fvars.back!
            let domain ← inferType mainFvar
            dbg_trace s!"[analyzeRecursor:motives] fvars={fvars} mainFvar={mainFvar} domain={domain}"
            let .const indName _ := domain.getAppFn
              | throwError "derive_deceq: expected motive domain to be a named type, got {domain}"
            let numIndices := fvars.size - 1
            dbg_trace s!"[analyzeRecursor:motives] indName={indName} numIndices={numIndices}"
            -- Use deterministic index names to avoid collisions when
            -- multiple indices delab to the same auto-name (e.g. both `a✝`)
            let indexNames := (Array.range numIndices).map fun i =>
              mkIdent (.mkSimple s!"_idx{i}")
            let mut indexBinderStxs : Array (TSyntax ``bracketedBinder) := #[]
            for i in [:numIndices] do
              let idxType ← inferType fvars[i]!
              let typeStx ← withOptions (fun o => pp.fullNames.set o true) <|
                PrettyPrinter.delab idxType
              dbg_trace s!"[analyzeRecursor:motives] index {i}: name={indexNames[i]!} type={typeStx}"
              indexBinderStxs := indexBinderStxs.push
                (← `(bracketedBinder| {$(indexNames[i]!) : $typeStx}))
            -- Build domain syntax from indName + params + fresh index names
            -- (avoids delab collision issues)
            let domainStx ← do
              if numIndices == 0 then
                dbg_trace s!"[analyzeRecursor:motives] numIndices=0 → delaborate domain directly"
                withOptions (fun o => pp.fullNames.set o true) <|
                  PrettyPrinter.delab domain
              else
                dbg_trace s!"[analyzeRecursor:motives] numIndices>0 → hand-assemble domain syntax"
                let indNameId := mkIdent indName
                -- domain.getAppArgs gives [param₁, ..., paramₖ, idx₁, ..., idxₙ]
                let domainArgs := domain.getAppArgs
                let numDomainParams := domainArgs.size - numIndices
                let mut argStxs : Array Term := #[]
                for i in [:numDomainParams] do
                  let argStx ← withOptions (fun o => pp.fullNames.set o true) <|
                    PrettyPrinter.delab domainArgs[i]!
                  argStxs := argStxs.push argStx
                for i in [:numIndices] do
                  argStxs := argStxs.push ⟨indexNames[i]!.raw⟩
                `($indNameId $argStxs*)
            dbg_trace s!"[analyzeRecursor:motives] OUT domainStx={domainStx} indName={indName} indexBinderStxs={indexBinderStxs}"
            return (domainStx, indName, indexBinderStxs)
        let motiveDomainStxs := motiveDomainInfo.map (·.1)
        let motiveIndNames := motiveDomainInfo.map (·.2.1)
        let motiveIndexBinderStxs := motiveDomainInfo.map (·.2.2)
        dbg_trace s!"[analyzeRecursor:motives] ALL motiveDomainStxs={motiveDomainStxs} motiveIndNames={motiveIndNames}"

        -- After motives, the recursor has one minor per constructor across all
        -- types in the mutual block.  Each minor has type:
        --   (implicit-binders...) → (field₁ : T₁) → (ih₁ : motive field₁) →
        --     (field₂ : T₂) → ... → motive_j (Ctor ...)
        -- where the leading implicit binders are either ctor indices or
        -- genuinely free implicit user fields (see step (c) below).
        --
        -- For each minor we:
        --   (a) Identify which motive (= which type) it belongs to, by checking
        --       which motive fvar appears in the return type.
        --   (b) Extract the constructor name from the return type's ctor application.
        --   (c) Classify each binder as an IH (explicit, type head is a motive),
        --       a data field (explicit non-IH, or implicit binder that is neither
        --       fixed in the ctor's return type nor referenced by another user
        --       binder), or an index (everything else — skipped).
        --   (d) Map each IH back to the data field it provides a recursive proof for.
        --   (e) Flag Prop-typed fields (compared by proof irrelevance, not structurally).
        let ctorsByType ←
          forallBoundedTelescope restType (some numMinors) (fun minorVars _ => do
            dbg_trace s!"[analyzeRecursor:minors] minorVars={minorVars}"
            let mut ctorsByType : Array (Array CtorInfo) := .replicate numMotives #[]

            for minorIdx in [:numMinors] do
              let minorType ← inferType minorVars[minorIdx]!
              dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: type={minorType}"
              let result ←
                forallTelescopeReducing minorType (fun fvars retType => do
                  dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: fvars={fvars} retType={retType}"
                  -- (a) Which type does this constructor belong to?
                  let motiveFvar := retType.getAppFn
                  let typeIdx ← motiveVars.findIdxM? fun mv => return mv == motiveFvar
                  let some typeIdx := typeIdx
                    | throwError "derive_deceq: minor's return type doesn't reference any known motive"
                  dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: (a) typeIdx={typeIdx}"
                  -- (b) Extract constructor name from return type: `motive_j (Ctor ...)`.
                  let .app _ ctorApp := retType
                    | throwError "derive_deceq: unexpected recursor return type shape: {retType}"
                  let .const ctorName _ := ctorApp.getAppFn
                    | throwError "derive_deceq: expected constructor application, got {ctorApp}"
                  dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: (b) ctorName={ctorName}"

                  -- (c) Classify each binder:
                  --       IH         — explicit, type head is a motive fvar.
                  --       data field — explicit non-IH, or implicit binder that
                  --                    is neither fixed in the ctor's own return
                  --                    type nor referenced by another user
                  --                    binder (a genuinely free implicit field).
                  --       index      — implicit binder fixed in the return type
                  --                    or determined by another binder (skip).
                  -- Walk the ctor's own type to get "is fixed in ctor's true
                  -- return type" per user binder. The minor's retType always
                  -- mentions every user binder via the ctor application, so
                  -- it cannot be used for the "is index" decision; we need
                  -- the ctor's own return type — e.g. an indexed `T (n+1)`
                  -- (where `n` is fixed by the index) vs a non-indexed `T`
                  -- (where no binder is fixed by the return).
                  let ctorConstInfo ← getConstInfoCtor ctorName
                  let ctorFixedFlags ← forallTelescopeReducing ctorConstInfo.type
                    fun ctorFvars ctorRetType => do
                      let mut flags : Array Bool := #[]
                      for cf in ctorFvars[numParams:] do
                        flags := flags.push (ctorRetType.containsFVar cf.fvarId!)
                      pure flags
                  dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: (c) ctorFixedFlags={ctorFixedFlags}"

                  let mut fieldTypes : Array Expr := #[]
                  let mut fieldVars : Array Expr := #[]
                  let mut ihVars : Array Expr := #[]
                  let mut userBinderIdx : Nat := 0
                  for x in fvars do
                    let ldecl ← x.fvarId!.getDecl
                    let xType ← inferType x
                    let isIH := ldecl.binderInfo == .default
                      && motiveVars.any (· == xType.getAppFn)
                    if isIH then
                      dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: binder {x} classified IH (type {xType})"
                      ihVars := ihVars.push x
                      continue
                    -- User binder: index into ctorFixedFlags by position
                    let isFixedInCtorReturn :=
                      ctorFixedFlags[userBinderIdx]?.getD false
                    userBinderIdx := userBinderIdx + 1
                    if ldecl.binderInfo == .default then
                      -- Explicit data field. Reject higher-order recursive
                      -- arguments — DecidableEq on a function space is
                      -- undecidable in general.
                      if xType.isForall then
                        let codomainHead := xType.getForallBody.getAppFn
                        if let .const cname _ := codomainHead then
                          if indVal.all.any (· == cname) then
                            throwError "\
                              derive_deceq: constructor {ctorName} has a \
                              higher-order recursive argument of type{indentExpr xType}\n\
                              DecidableEq on a function space is not decidable."
                      dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: binder {x} classified EXPLICIT FIELD (type {xType})"
                      fieldTypes := fieldTypes.push xType
                      fieldVars := fieldVars.push x
                    else
                      -- Implicit user binder: skip if fixed in ctor's own
                      -- return type (index unified by motive) or referenced in
                      -- another user binder's type (subst chain unifies it).
                      -- Otherwise it's a genuinely free user field — an
                      -- implicit binder that doesn't appear anywhere else,
                      -- e.g. `mk : {x : T} → Nat → T` — that must be
                      -- compared just like an explicit field.
                      let mut referenced := isFixedInCtorReturn
                      if !referenced then
                        for y in fvars do
                          if y == x then continue
                          let yLdecl ← y.fvarId!.getDecl
                          let yType ← inferType y
                          if yLdecl.binderInfo == .default
                              && motiveVars.any (· == yType.getAppFn) then
                            continue
                          if yType.containsFVar x.fvarId! then
                            referenced := true
                            break
                      dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: implicit binder {x} isFixedInCtorReturn={isFixedInCtorReturn} referenced={referenced}"
                      if !referenced then
                        dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: binder {x} classified FREE IMPLICIT FIELD"
                        fieldTypes := fieldTypes.push xType
                        fieldVars := fieldVars.push x
                      else
                        dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: binder {x} classified INDEX (skipped)"

                  dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: (c) fieldTypes={fieldTypes} fieldVars={fieldVars} ihVars={ihVars}"

                  -- (d) Map each IH to the data field it provides a recursive proof for.
                  --     IH type is `motive_j field_k`, so we match `field_k` against
                  --     our collected fieldVars to find the index.
                  let numFields := fieldTypes.size
                  let mut ihMotiveIndices := Array.replicate numFields (none : Option Nat)
                  for ihVar in ihVars do
                    let ihType ← inferType ihVar
                    let ihMotiveFvar := ihType.getAppFn
                    let ihMotiveIdx ← motiveVars.findIdxM? fun mv =>
                      return mv == ihMotiveFvar
                    let .app _ fieldFvar := ihType | continue
                    for fIdx in [:numFields] do
                      if fieldVars[fIdx]! == fieldFvar then
                        dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: (d) IH {ihVar} → field {fIdx} recurses via motive {ihMotiveIdx}"
                        ihMotiveIndices := ihMotiveIndices.set! fIdx ihMotiveIdx
                        break

                  -- (e) Flag Prop-typed fields (compared by proof irrelevance, not structurally)
                  let mut propFlags := Array.replicate numFields false
                  for i in [:numFields] do
                    let p ← Meta.isProp fieldTypes[i]!
                    dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: (e) field {i} isProp={p}"
                    propFlags := propFlags.set! i p

                  let fields := (Array.range numFields).map fun i =>
                    { type := fieldTypes[i]!,
                      recursiveMotiveIdx := ihMotiveIndices[i]!,
                      isProp := propFlags[i]! : FieldInfo }
                  dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: OUT fields={reprStr fields}"

                  return (ctorName, typeIdx, fields))

              let (ctorName, typeIdx, fields) := result
              dbg_trace s!"[analyzeRecursor:minors] minor {minorIdx}: pushing CtorInfo name={ctorName} typeIdx={typeIdx}"
              ctorsByType := ctorsByType.modify typeIdx
                (·.push { name := ctorName, typeIdx, fields })

            dbg_trace s!"[analyzeRecursor:minors] OUT ctorsByType={reprStr ctorsByType}"
            return ctorsByType)

        return (paramBinderStxs, instBinderStxs, motiveDomainStxs, motiveIndNames,
                motiveIndexBinderStxs, ctorsByType)))

  let ns ← getCurrNamespace
  dbg_trace s!"[analyzeRecursor] currNamespace={ns}"
  -- Demangle private names so the emitted `def` name matches what Lean
  -- will re-mangle under `private def` (see `isPrivate` below).
  let defBaseNames := typeNames.map fun n =>
    (Lean.privateToUserName? n |>.getD n).replacePrefix ns .anonymous
  let isPrivate := Lean.isPrivateName firstType
  dbg_trace s!"[analyzeRecursor] defBaseNames={defBaseNames} isPrivate={isPrivate}"
  let finalAnalysis : RecursorAnalysis :=
    { typeNames, defBaseNames, numUserTypes, numMotives,
      motiveDomainStxs, motiveIndNames, motiveIndexBinderStxs,
      paramBinderStxs, instBinderStxs, ctorsByType, isPrivate }
  dbg_trace s!"[analyzeRecursor] OUT numMotives={finalAnalysis.numMotives} numUserTypes={finalAnalysis.numUserTypes} motiveDomainStxs={finalAnalysis.motiveDomainStxs}"
  return finalAnalysis

-- ── mkIfSubstChain ────────────────────────────────────────────────────
/-- Generate the `if`/`subst` comparison chain used by the standard
    `DecidableEq` deriver. Each field is compared in sequence; after `subst h`,
    types of subsequent fields are unified, which is what makes index-changing
    recursion elaborate correctly when later field types depend on earlier
    equalities. -/
private def mkIfSubstChain (analysis : RecursorAnalysis)
    : List (Ident × Ident × Option Nat × Bool) → TermElabM Term
  | [] =>
    dbg_trace s!"[mkIfSubstChain] base case: empty list → isTrue rfl";
    `(isTrue rfl)
  | (a, b, motiveIdx, isProof) :: rest => do
    dbg_trace s!"[mkIfSubstChain] IN  head=({a},{b},{motiveIdx},{isProof}) rest.length={rest.length}"
    let rhs ← withFreshMacroScope do
      if isProof then
        dbg_trace s!"[mkIfSubstChain] branch: isProof=true → proof-irrelevance shortcut"
        `(have h : @$a = @$b := rfl; by subst h; exact $(← mkIfSubstChain analysis rest))
      else
        dbg_trace s!"[mkIfSubstChain] branch: real comparison, building rest first"
        let sameCtor ← mkIfSubstChain analysis rest
        dbg_trace s!"[mkIfSubstChain] rest built: {sameCtor}"
        `(if h : @$a = @$b then
           by subst h; exact $sameCtor
          else
           isFalse (by intro heq; injection heq; apply h _; assumption))
    dbg_trace s!"[mkIfSubstChain] rhs (before recursive-instance wrap)={rhs}"
    -- For recursive fields, create a local Decidable instance so that
    -- `if h : @a = @b` can find the decision procedure.
    if let some j := motiveIdx then
      let decEqId := mkIdent (motiveDecEqName analysis j)
      dbg_trace s!"[mkIfSubstChain] field is recursive via motive {j} ({decEqId}) → wrapping with local instance"
      let result ← `(let inst := $decEqId @$a @$b; $rhs)
      dbg_trace s!"[mkIfSubstChain] OUT result={result}"
      return result
    else
      dbg_trace s!"[mkIfSubstChain] field is non-recursive, no wrap needed. OUT result={rhs}"
      return rhs

-- ── mkSameCtorAlt ─────────────────────────────────────────────────────
/-- Generate the lambda for one constructor's same-constructor comparison.
    Opens the constructor type to classify each field as fixed (appears in return type,
    shared between both sides) or free (gets separate a/b variables). This handles
    index-changing recursion where free index variables must be compared and subst'd
    before recursive fields can be compared (since their types may differ). -/
private def mkSameCtorAlt
    (analysis : RecursorAnalysis)
    (ctor : CtorInfo)
    : TermElabM Term := do
  dbg_trace s!"[mkSameCtorAlt] IN  ctor.name={ctor.name} ctor.fields={reprStr ctor.fields}"
  let ctorConstInfo ← getConstInfoCtor ctor.name
  let indVal ← getConstInfoInduct ctorConstInfo.induct
  dbg_trace s!"[mkSameCtorAlt] ctorConstInfo.type={ctorConstInfo.type}"
  forallTelescopeReducing ctorConstInfo.type (fun fvars returnType => do
    let returnType ← Core.betaReduce returnType
    let numParams := indVal.numParams
    let numFields := ctorConstInfo.numFields
    dbg_trace s!"[mkSameCtorAlt] fvars={fvars} returnType={returnType} numParams={numParams} numFields={numFields}"

    if numFields == 0 then
      dbg_trace s!"[mkSameCtorAlt] numFields=0 → trivial isTrue rfl shortcut"
      return ← `(fun () => isTrue rfl)

    let mut ctorArgs1 : Array Term := #[]
    let mut ctorArgs2 : Array Term := #[]
    -- (a, b, recursiveMotiveIdx?, isProp). A None index tries to resolve deceq by existing instances.
    let mut todo : Array (Ident × Ident × Option Nat × Bool) := #[]
    -- Index into ctor.fields (recursor-derived), for recursiveness/isProp info.
    -- Advances for every binder the analyzer recorded a FieldInfo for —
    -- every explicit binder plus any implicit binder that is a genuinely
    -- free user field.
    let mut fieldIdx : Nat := 0

    for i in [:numFields] do
      let x := fvars[numParams + i]!
      let ldecl ← x.fvarId!.getDecl
      let isExplicit := ldecl.binderInfo == .default
      let isFixed := returnType.containsFVar x.fvarId!
      let fi := mkFieldId "f" i
      let gi := mkFieldId "g" i
      dbg_trace s!"[mkSameCtorAlt] field {i}: x={x} isExplicit={isExplicit} isFixed={isFixed} fi={fi} gi={gi}"

      -- Fixed binders are unified between both sides by the motive, so the
      -- minor lambda takes them only once (as `_`). Free binders appear twice.
      if isFixed then
        dbg_trace s!"[mkSameCtorAlt] field {i}: fixed → binding `_` once"
        ctorArgs1 := ctorArgs1.push (← `(_))
      else
        dbg_trace s!"[mkSameCtorAlt] field {i}: free → binding {fi} (side 1) and {gi} (side 2)"
        ctorArgs1 := ctorArgs1.push ⟨fi.raw⟩
        ctorArgs2 := ctorArgs2.push ⟨gi.raw⟩

      -- Does this binder have a `FieldInfo` entry in `ctor.fields`?
      -- Mirror the analyzer's classification:
      --   explicit                                     → yes
      --   implicit + fixed (appears in return type)    → no (index)
      --   implicit + free + referenced in another user → no (determined)
      --   implicit + free + not referenced anywhere    → yes (user field)
      let hasFieldInfo ←
        if isExplicit then pure true
        else if isFixed then pure false
        else do
          let mut referenced := false
          for j in [:numFields] do
            if j == i then continue
            let y := fvars[numParams + j]!
            let yType ← inferType y
            if yType.containsFVar x.fvarId! then
              referenced := true
              break
          pure (!referenced)
      dbg_trace s!"[mkSameCtorAlt] field {i}: hasFieldInfo={hasFieldInfo}"

      if hasFieldInfo then
        let field := ctor.fields[fieldIdx]!
        dbg_trace s!"[mkSameCtorAlt] field {i}: consuming ctor.fields[{fieldIdx}]={reprStr field}"
        fieldIdx := fieldIdx + 1
        if !isFixed then
          if !field.isProp then
            dbg_trace s!"[mkSameCtorAlt] field {i}: pushing to todo as REAL comparison (motiveIdx={field.recursiveMotiveIdx})"
            todo := todo.push (fi, gi, field.recursiveMotiveIdx, false)
          else
            dbg_trace s!"[mkSameCtorAlt] field {i}: pushing to todo as PROOF (proof-irrelevance shortcut)"
            todo := todo.push (fi, gi, none, true)
      else if !isFixed then
        -- Free implicit index binder (determined by another user binder):
        -- plain decEq; the subst chain unifies it with the other field.
        let xType ← inferType x
        let isProof ← Meta.isProp xType
        dbg_trace s!"[mkSameCtorAlt] field {i}: no FieldInfo, free implicit index, isProof={isProof}"
        if !isProof then
          dbg_trace s!"[mkSameCtorAlt] field {i}: pushing to todo as non-recursive comparison"
          todo := todo.push (fi, gi, none, false)

    dbg_trace s!"[mkSameCtorAlt] final todo={todo} ctorArgs1={ctorArgs1} ctorArgs2={ctorArgs2}"
    if ctorArgs1.isEmpty then
      dbg_trace s!"[mkSameCtorAlt] ctorArgs1 empty → trivial isTrue rfl shortcut"
      return ← `(fun () => isTrue rfl)
    let rhs ← mkIfSubstChain analysis todo.toList
    let result ← `(@fun $ctorArgs1:term* $ctorArgs2:term* => $rhs)
    dbg_trace s!"[mkSameCtorAlt] OUT result={result}"
    return result)

-- ── mkDecEqFunc ───────────────────────────────────────────────────────
/-- Generate a `def` command for a DecEq function (user or auxiliary motive). -/
private def mkDecEqFunc
    (analysis : RecursorAnalysis)
    (sameCtorNames : Array Name)
    (isRecursive : Array Bool)
    (motiveIdx : Nat)
    : TermElabM (TSyntax `command) := do
  dbg_trace s!"[mkDecEqFunc] IN  motiveIdx={motiveIdx}"
  let domainStx := analysis.motiveDomainStxs[motiveIdx]!
  let defId := mkIdent (motiveDecEqName analysis motiveIdx)
  let aId := mkIdent `a
  let bId := mkIdent `b
  dbg_trace s!"[mkDecEqFunc] domainStx={domainStx} defId={defId}"

  let indName := analysis.motiveIndNames[motiveIdx]!
  let ctorIdxId := mkIdent (mkCtorIdxName indName)
  let sameCtorId := mkIdent sameCtorNames[motiveIdx]!
  let ctors := analysis.ctorsByType[motiveIdx]!
  dbg_trace s!"[mkDecEqFunc] indName={indName} ctorIdxId={ctorIdxId} sameCtorId={sameCtorId} ctors.size={ctors.size}"

  -- Short-circuits for degenerate inductives that break the standard
  -- casesOnSameCtor + ctorIdx path.
  let indexBinders := analysis.motiveIndexBinderStxs[motiveIdx]!
  let mainBinderStx ← `(bracketedBinder| ($aId $bId : $domainStx))
  let allBinderStxs := analysis.paramBinderStxs ++ analysis.instBinderStxs
    ++ indexBinders ++ #[mainBinderStx]
  dbg_trace s!"[mkDecEqFunc] indexBinders={indexBinders} allBinderStxs={allBinderStxs}"

  -- Empty inductive — no inhabitant exists, so `nomatch` either argument.
  if ctors.isEmpty then
    dbg_trace s!"[mkDecEqFunc] SHORT-CIRCUIT: empty inductive → nomatch"
    return ←
      if analysis.isPrivate then
        `(command| private def $defId
            $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := nomatch $aId)
      else
        `(command| def $defId
            $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := nomatch $aId)

  -- Prop-valued inductive — all inhabitants are definitionally equal
  -- by proof irrelevance, so `rfl : a = b` type-checks.
  if ← isPropInductive indName then
    dbg_trace s!"[mkDecEqFunc] SHORT-CIRCUIT: Prop-valued → isTrue rfl"
    return ←
      if analysis.isPrivate then
        `(command| private def $defId
            $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := isTrue rfl)
      else
        `(command| def $defId
            $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := isTrue rfl)

  dbg_trace s!"[mkDecEqFunc] no short-circuit, building real comparison for {ctors.size} constructors"
  let mut alts : Array Term := #[]
  for ctor in ctors do
    let alt ← mkSameCtorAlt analysis ctor
    dbg_trace s!"[mkDecEqFunc] alt for {ctor.name}: {alt}"
    alts := alts.push alt

  -- For indexed types, casesOnSameCtor's motive has implicit index binders
  -- that Lean can't always infer. Provide the motive explicitly, using the
  -- same index binder names that appear in domainStx so references resolve.
  let sameCtorCall ← do
    if indexBinders.isEmpty then
      dbg_trace s!"[mkDecEqFunc] not indexed, no explicit motive needed"
      if ctors.size ≤ 1 then
        dbg_trace s!"[mkDecEqFunc] single constructor → 'same ctor' hypothesis is rfl"
        `($sameCtorId $aId $bId rfl $alts:term*)
      else
        dbg_trace s!"[mkDecEqFunc] multiple constructors → 'same ctor' hypothesis is h"
        `($sameCtorId $aId $bId h $alts:term*)
    else
      dbg_trace s!"[mkDecEqFunc] indexed → building explicit motive"
      let aM := mkIdent `a_m
      let bM := mkIdent `b_m
      let aT : Term := ⟨aM.raw⟩
      let bT : Term := ⟨bM.raw⟩
      -- Use _ for domain type — Lean infers it from casesOnSameCtor's motive type.
      -- This avoids macro hygiene issues where domainStx's index names are in a
      -- different scope than the motive lambda's implicit binders.
      let mut motive ←
        `(fun ($aM $bM : _) (_hm : _) => Decidable ($aT = $bT))
      for _ in [:indexBinders.size] do
        motive ← `(fun {_} => $motive)
      dbg_trace s!"[mkDecEqFunc] built motive={motive}"
      if ctors.size ≤ 1 then
        `($sameCtorId (motive := $motive) $aId $bId rfl $alts:term*)
      else
        `($sameCtorId (motive := $motive) $aId $bId h $alts:term*)
  dbg_trace s!"[mkDecEqFunc] sameCtorCall={sameCtorCall}"

  let body : Term ←
    if ctors.size ≤ 1 then
      dbg_trace s!"[mkDecEqFunc] body: single-constructor shortcut, no ctorIdx dispatch needed"
      pure sameCtorCall
    else
      dbg_trace s!"[mkDecEqFunc] body: multi-constructor, building ctorIdx dispatch"
      `(match decEq ($ctorIdxId $aId) ($ctorIdxId $bId) with
        | .isTrue h => $sameCtorCall
        | .isFalse h => isFalse (fun h' => h (congrArg $ctorIdxId h')))
  dbg_trace s!"[mkDecEqFunc] body={body}"

  let termSuffix ← if isRecursive[motiveIdx]!
    then
      dbg_trace s!"[mkDecEqFunc] isRecursive[{motiveIdx}]=true → termination_by structural a"
      `(Parser.Termination.suffix| termination_by structural $aId)
    else
      dbg_trace s!"[mkDecEqFunc] isRecursive[{motiveIdx}]=false → no termination suffix"
      `(Parser.Termination.suffix|)
  let finalCmd ←
    if analysis.isPrivate then
      `(command| private def $defId $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := $body
        $termSuffix:suffix)
    else
      `(command| def $defId $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := $body
        $termSuffix:suffix)
  dbg_trace s!"[mkDecEqFunc] OUT finalCmd=\n{finalCmd}"
  return finalCmd

-- ── deriveForGroup ────────────────────────────────────────────────────
/-- Main entry point: derive DecidableEq for all types in a mutual group. -/
def deriveForGroup (firstName : Name) : CommandElabM Unit := do
  dbg_trace s!"[deriveForGroup] IN  firstName={firstName}"
  Deriving.withoutExposeFromCtors firstName <| do
  let analysis ← liftTermElabM <| MetaM.run' <| analyzeRecursor firstName
  dbg_trace s!"[deriveForGroup] analysis received: numMotives={analysis.numMotives} numUserTypes={analysis.numUserTypes}"

  trace[DecEqMutual.derive] "Types: {analysis.typeNames}"
  trace[DecEqMutual.derive] "Motives: {analysis.numMotives} (user: {analysis.numUserTypes})"
  trace[DecEqMutual.derive] "Params: {analysis.paramBinderStxs.size}, Insts: {analysis.instBinderStxs.size}"
  for i in [:analysis.numMotives] do
    for c in analysis.ctorsByType[i]! do
      trace[DecEqMutual.derive] "  motive[{i}] ctor {c.name}, nfields={c.fields.size}"

  -- Generate `casesOnSameCtor` helpers for each non-`Prop` motive.
  -- Prop-valued inductives short-circuit to `isTrue rfl` in `mkDecEqFunc`,
  -- so they never need a same-constructor helper.
  let sameCtorNames ← liftTermElabM <| MetaM.run' <| do
    let mut names : Array Name := #[]
    for i in [:analysis.numMotives] do
      let indName := analysis.motiveIndNames[i]!
      if ← isPropInductive indName then
        dbg_trace s!"[deriveForGroup:sameCtorNames] motive {i} ({indName}) is Prop → placeholder .anonymous"
        names := names.push .anonymous
      else
        let sameCtorName ← mkFreshUserName (indName ++ `match_on_same_ctor)
        dbg_trace s!"[deriveForGroup:sameCtorNames] motive {i} ({indName}) → generating {sameCtorName}"
        mkCasesOnSameCtor sameCtorName indName
        names := names.push sameCtorName
    return names
  dbg_trace s!"[deriveForGroup] sameCtorNames={sameCtorNames}"

  -- Generate decEq functions for ALL motives (user + auxiliary)
  let isRecursive := computeIsRecursive analysis
  dbg_trace s!"[deriveForGroup] isRecursive={isRecursive}"
  let mut defs : Array Syntax := #[]
  for i in [:analysis.numMotives] do
    let defCmd ← liftTermElabM <| mkDecEqFunc analysis sameCtorNames isRecursive i
    trace[DecEqMutual.derive] "Generated def:\n{defCmd}"
    defs := defs.push defCmd

  -- Wrap in mutual block
  let mutualStx := Lean.mkNode ``Lean.Parser.Command.mutual
    #[mkAtom "mutual", mkNullNode defs, mkAtom "end"]
  dbg_trace s!"[deriveForGroup] mutualStx built, {defs.size} defs bundled"

  trace[DecEqMutual.derive] "Elaborating mutual block..."
  withEnableInfoTree false do
    elabCommand mutualStx
  dbg_trace s!"[deriveForGroup] mutual block elaborated successfully"

  -- Register DecidableEq instances only for user types, using the standard
  -- deriving infrastructure (handles instance naming, private ctors, etc.).
  -- Each type gets its own Context so instance names don't collide.
  for i in [:analysis.numUserTypes] do
    let typeName := analysis.typeNames[i]!
    dbg_trace s!"[deriveForGroup:instances] registering instance for user type {i}: {typeName}"
    let instanceCmds ← liftTermElabM do
      let instName ← Deriving.mkInstName ``DecidableEq typeName
      let typeInfo ← getConstInfoInduct typeName
      let auxFunName := motiveDecEqName analysis i
      dbg_trace s!"[deriveForGroup:instances] instName={instName} auxFunName={auxFunName}"
      let derivCtx : Deriving.Context :=
        { instName, typeInfos := #[typeInfo],
          auxFunNames := #[auxFunName], usePartial := false }
      Deriving.mkInstanceCmds derivCtx `DecidableEq #[typeName] (useAnonCtor := false)
    for cmd in instanceCmds do
      trace[DecEqMutual.derive] "Registering instance: {cmd}"
      elabCommand cmd

  -- ── csimp optimization for auxiliary types ──────────────────────────
  -- For nested containers (List, Array, Option, ...) the mutual block
  -- generates its own comparison functions that bypass the container's
  -- existing DecidableEq instance. This can miss C-optimized paths
  -- (e.g. Array.isEqv). For each auxiliary, emit:
  --   def _real := inferInstance   (computable, delegates to stdlib)
  --   @[csimp] theorem : @auxFun = @_real
  --
  -- NOTE: This optimization currently DOES NOT WORK for intra-mutual-block
  -- calls. csimp rewrites call sites in *downstream* compilations, but the
  -- only callers of auxiliary functions are inside the same mutual block,
  -- compiled before the csimp lemmas are registered. For the optimization
  -- to work, it would need to be applied to the main user-type DecEq
  -- function itself (not just the auxiliaries).
  --
  -- Auxiliary names use numeric Name components (.mkNum) that surface
  -- syntax cannot reference, so we build these declarations programmatically.
  let ns ← getCurrNamespace
  for i in [analysis.numUserTypes:analysis.numMotives] do
    -- motiveDecEqName returns namespace-stripped names; the mutual block's
    -- `def` prepends the current namespace once, giving the actual constant.
    let auxFunName := ns ++ motiveDecEqName analysis i
    let realName := auxFunName ++ `_real
    let csimpName := auxFunName ++ `_csimp
    dbg_trace s!"[deriveForGroup:csimp] auxiliary motive {i}: auxFunName={auxFunName} realName={realName} csimpName={csimpName}"
    -- synthInstance may fail for custom containers without stdlib DecidableEq;
    -- in that case we skip the optimization (our generated function still works).
    try liftTermElabM do
      let auxInfo ← getConstInfo auxFunName
      let auxType := auxInfo.type
      let uParams := auxInfo.levelParams
      let lvls := uParams.map mkLevelParam
      dbg_trace s!"[deriveForGroup:csimp] auxType={auxType}"
      -- _real: synthesize the stdlib DecidableEq instance at the same type
      let realVal ← Meta.forallTelescope auxType fun xs bodyType => do
        let inst ← Meta.synthInstance bodyType
        dbg_trace s!"[deriveForGroup:csimp] synthesized stdlib instance: {inst}"
        Meta.mkLambdaFVars xs inst
      addAndCompile (.defnDecl {
        name := realName
        levelParams := uParams
        type := auxType
        value := realVal
        hints := .abbrev
        safety := .safe
      })
      dbg_trace s!"[deriveForGroup:csimp] registered {realName}"
      -- Prove: @auxFun = @_real  (by repeated funext + Subsingleton.elim)
      let auxConst := Lean.mkConst auxFunName lvls
      let realConst := Lean.mkConst realName lvls
      let proof ← Meta.forallTelescope auxType fun xs _ => do
        let lhsApp := mkAppN auxConst xs
        let rhsApp := mkAppN realConst xs
        let mut p ← Meta.mkAppM ``Subsingleton.elim #[lhsApp, rhsApp]
        for x in xs.reverse do
          p ← Meta.mkLambdaFVars #[x] p
          p ← Meta.mkAppM ``funext #[p]
        return p
      let eqType ← Meta.mkEq auxConst realConst
      addDecl (.thmDecl {
        name := csimpName
        levelParams := uParams
        type := eqType
        value := proof
      })
      Lean.Compiler.CSimp.add csimpName .global
      trace[DecEqMutual.derive] "csimp: {auxFunName} → {realName}"
    catch e =>
      let msg ← e.toMessageData.toString
      dbg_trace s!"[deriveForGroup:csimp] SKIPPED for {auxFunName}: {msg}"
      trace[DecEqMutual.derive] "csimp: skipped {auxFunName} (no stdlib instance)"

initialize registerTraceClass `DecEqMutual.derive

syntax (name := deriveDecEqCmd) "derive_deceq " ident+ : command

@[command_elab deriveDecEqCmd]
def elabDeriveDecEq : CommandElab := fun stx => do
  dbg_trace s!"[elabDeriveDecEq] IN  stx={stx}"
  let idents := stx[1].getArgs
  dbg_trace s!"[elabDeriveDecEq] idents={idents}"
  if idents.isEmpty then
    throwError "derive_deceq requires at least one type name"
  if idents.size > 1 then
    dbg_trace s!"[elabDeriveDecEq] more than one ident given ({idents.size}), warning and using only the first"
    logWarning "derive_deceq: only the first type name is needed; \
      all types in the mutual block are derived automatically. Ignoring extra names."
  let firstName ← resolveGlobalConstNoOverload idents[0]!
  dbg_trace s!"[elabDeriveDecEq] resolved firstName={firstName}, calling deriveForGroup"
  deriveForGroup firstName

end DecEqMutual.Derive

/- ══════════════════════════════════════════════════════════════════════
   SIX WORKED EXAMPLES
   ══════════════════════════════════════════════════════════════════════ -/

-- NOTE: `set_option trace.DecEqMutual.derive true` is deliberately NOT used
-- here. Unlike sandbox_5.lean (which imports ExtendedDeriveDecEq as a
-- separate, precompiled module, so its `initialize registerTraceClass`
-- has already run by the time sandbox_5 sets the option), everything here
-- is pasted into ONE file -- the `initialize` block's effect isn't visible
-- to later commands within that SAME file's own elaboration pass, so the
-- option name isn't recognized yet (confirmed: `set_option
-- trace.DecEqMutual.derive true` here fails with "Unknown option"). Not a
-- problem in practice: `dbg_trace` already prints everything, and more
-- granularly, than the `trace[DecEqMutual.derive] ...` calls would anyway.

-- ── Example 1: Shape — simple, no nesting, no mutual recursion ────────
#eval dbg_trace "=== Shape (simple) ==="; (0 : Nat)
inductive Shape where
  | circle (radius : Nat)
  | square (side : Nat)

derive_deceq Shape

-- ── Example 2: Tree — nested (self-recursion through List) ────────────
#eval dbg_trace "=== Tree (nested) ==="; (0 : Nat)
inductive Tree where
  | leaf (n : Nat)
  | node (children : List Tree)

derive_deceq Tree

-- ── Example 3: Even/Odd — mutual, no nesting ───────────────────────────
#eval dbg_trace "=== Even/Odd (mutual) ==="; (0 : Nat)
mutual
inductive Even where
  | zero
  | succ (n : Odd) : Even
inductive Odd where
  | succ (n : Even) : Odd
end

derive_deceq Even

-- ── Example 4: Exp/Stm — nested AND mutual ─────────────────────────────
-- Named `Exp`/`Stm` rather than `Expr`/`Stmt` deliberately: `Expr` collides
-- with `Lean.Expr` (in scope via `open Lean` at the top of this file,
-- needed for ExtendedDeriveDecEq's own code) and fails with "ambiguous
-- identifier" -- confirmed empirically hitting this exact error on the
-- first attempt.
#eval dbg_trace "=== Exp/Stm (nested + mutual) ==="; (0 : Nat)
mutual
inductive Exp where
  | lit (n : Nat)
  | app (f : Exp) (args : List Stm)
inductive Stm where
  | expr (e : Exp)
  | block (stmts : List Stm)
end

derive_deceq Exp

-- ── Example 5: Rose — polymorphic AND nested ───────────────────────────
#eval dbg_trace "=== Rose (polymorphic + nested) ==="; (0 : Nat)
inductive Rose (α : Type) where
  | node (val : α) (children : List (Rose α))

derive_deceq Rose

/- ══════════════════════════════════════════════════════════════════════
   TOP-LEVEL INTROSPECTION: real `#print` (a command, works fine here,
   outside any function body) on everything just generated.
   ══════════════════════════════════════════════════════════════════════ -/

#print Shape.decEq
#print axioms Shape.decEq

#print Tree.decEq
#print Tree.decEq.eq_1
#print axioms Tree.decEq

#print Even.decEq
#print Odd.decEq

#print Exp.decEq
#print Stm.decEq

#print Rose.decEq

-- sanity checks: the generated instances actually work end to end
example : Tree.node [Tree.leaf 1, Tree.leaf 2] ≠ Tree.node [Tree.leaf 1, Tree.leaf 3] := by decide
example : Rose.node 1 [Rose.node 2 []] = Rose.node 1 [Rose.node 2 []] := by decide
