/-
  Verbatim copy of raoxiaojia/Extended-derive-deceq (Apache-2.0), pulled in for
  sandbox_5.lean's walkthrough of how it derives DecidableEq for nested
  inductive types. Source: https://github.com/raoxiaojia/Extended-derive-deceq
  Referenced from leanprover/lean4#2329 and Wasm-DSL/spectec#192.
-/

/-
  ExtendedDeriveDecEq: Computable DecidableEq for nested inductive types.

  Uses an O(n) construction based on `ctorIdx` + `casesOnSameCtor`. For each type
  with k constructors, we generate one lambda per constructor (same-ctor
  comparison), then dispatch cross-constructor disequality in O(1) via
  `congrArg ctorIdx`. This avoids the O(n²) match arms that a naive
  pattern-match approach would produce.

  Generates a `mutual ... end` block of comparison functions, elaborated
  normally to produce kernel-verified proofs and compiled code without
  unsafe bridges.

  Assumptions about Lean's recursor shape:

  1. The recursor type is the forall chain
     `params → motives → minors → indices → major → result`; we only need to
     peel `numParams`, `numMotives`, and `numMinors` binders, which are
     partitioned cleanly at the front.

  2. For nested container types (e.g. `List Expr`), the kernel generates
     auxiliary motives with their own minors (e.g. `List.nil`, `List.cons`).

  Approach:
  1. Analyze the recursor to discover the full mutual block structure.
  2. Generate `casesOnSameCtor` helpers for each non-`Prop` motive
     (`Prop`-valued inductives short-circuit in step 3).
  3. For each motive, generate a comparison function. Most motives use
     `ctorIdx` dispatch with a `casesOnSameCtor` body; empty inductives
     emit `nomatch`, and `Prop`-valued inductives emit `isTrue rfl`.
  4. Wrap all defs in `mutual ... end` for the equation compiler.
  5. Register DecidableEq instances for user types.
-/
import Lean
import Lean.Elab.Deriving.Util
import Lean.Meta.Constructions.CasesOnSameCtor
import Lean.Meta.Constructions.CtorIdx

open Lean Meta Elab Command Term Parser.Term

namespace DecEqMutual.Derive

private def mkFieldId (prefix_ : String) (i : Nat) : Ident :=
  mkIdent (.mkSimple s!"{prefix_}{i}")

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

/-- Compute which motives are part of a recursive call cycle (Floyd-Warshall). -/
private def computeIsRecursive (analysis : RecursorAnalysis) : Array Bool := Id.run do
  let n := analysis.numMotives
  let mut reach := Array.replicate n (Array.replicate n false)
  for i in [:n] do
    for ctor in analysis.ctorsByType[i]! do
      for field in ctor.fields do
        if let some j := field.recursiveMotiveIdx then
          reach := reach.modify i (·.set! j true)
  for k in [:n] do
    for i in [:n] do
      for j in [:n] do
        if reach[i]![k]! && reach[k]![j]! then
          reach := reach.modify i (·.set! j true)
  return (Array.range n).map fun i => reach[i]![i]!

/-- Store the first `n` binder infos from a forall type to be used for
    reconstructing the binder style later. -/
private def extractBinderInfos (type : Expr) (n : Nat) : Array BinderInfo := Id.run do
  let mut result : Array BinderInfo := #[]
  let mut rest := type
  for _ in [:n] do
    match rest with
    | .forallE _name _domain body binfo =>
      result := result.push binfo
      rest := body
    | _ => break
  return result

/-- Is the inductive `indName` Prop-valued (i.e. its resultant sort is `Prop`)? -/
private def isPropInductive (indName : Name) : MetaM Bool := do
  let indVal ← getConstInfoInduct indName
  return match indVal.type.getForallBody with
    | .sort l => l.isZero
    | _ => false

/-- Name for the decEq function of a given motive.
    Uses namespace-stripped `defBaseNames` so that `def <name>` inside the
    current namespace produces correctly single-prefixed constants. -/
private def motiveDecEqName (analysis : RecursorAnalysis) (motiveIdx : Nat) : Name :=
  if motiveIdx < analysis.numUserTypes then
    analysis.defBaseNames[motiveIdx]! ++ `decEq
  else
    -- Numeric name component (`.mkNum`) avoids collision with user-defined names,
    -- since users cannot create numeric name components in normal code.
    analysis.defBaseNames[0]! ++ `_auxDecEq ++ .mkNum .anonymous motiveIdx

/-- Analyze the recursor of a mutual inductive block to extract all
    information needed for generating DecidableEq definitions. -/
def analyzeRecursor (indName : Name) : MetaM RecursorAnalysis := do
  -- The recursor's type signature encodes everything we need:
  --   rec.{u} : (params...) → (motives...) → (minors...) → (target) → result
  let indVal ← getConstInfoInduct indName
  let typeNames := indVal.all.toArray
  let numUserTypes := typeNames.size
  let firstType := typeNames[0]!
  let recName := mkRecName firstType
  let recVal ← getConstInfoRec recName
  let numParams := recVal.numParams
  let numMotives := recVal.numMotives
  let numMinors := recVal.numMinors

  -- The recursor makes all params explicit, losing the original
  -- implicit/instImplicit distinction. Read it from the inductive type itself.
  let origBinderInfos := extractBinderInfos indVal.type numParams

  let (paramBinderStxs, instBinderStxs, motiveDomainStxs, motiveIndNames,
       motiveIndexBinderStxs, ctorsByType) ←
    -- Open the first `numParams` binders of the recursor type.
    -- For each param, restore its original binder info and
    -- generate syntax: {α : Type} for type params, [DecidableEq α] for
    -- type params that admit DecidableEq, [inst : Class] for instances
    -- which needs to be categorised back to instance binders.
    forallBoundedTelescope recVal.type (some numParams) (fun paramVars restType0 => do
      let mut paramBinderStxs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      let mut instBinderStxs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]

      for i in [:numParams] do
        let v := paramVars[i]!
        -- LocalDecl gives us userName and type for this fvar;
        -- binderInfo is ignored (recursor makes all params explicit).
        let ldecl ← v.fvarId!.getDecl
        let nameId := mkIdent ldecl.userName
        let binfo := if i < origBinderInfos.size then origBinderInfos[i]! else .implicit
        let typeStx ← withOptions (fun o => pp.fullNames.set o true) <|
          PrettyPrinter.delab ldecl.type

        if binfo == .instImplicit then
          -- Instance param: forward as [TypeStx]
          instBinderStxs := instBinderStxs.push (← `(bracketedBinder| [$typeStx]))
        else
          -- Type/value param: forward as {name : Type}
          paramBinderStxs := paramBinderStxs.push (← `(bracketedBinder| {$nameId : $typeStx}))
          -- For params that admit DecidableEq, add [DecidableEq name]
          -- (uses mkAppM + isTypeCorrect, matching the standard deriving infrastructure,
          -- which is more robust than a simple isSort check)
          try
            let c ← mkAppM ``DecidableEq #[v]
            if (← isTypeCorrect c) then
              let decEqType ← `(DecidableEq $nameId)
              instBinderStxs := instBinderStxs.push (← `(bracketedBinder| [$decEqType]))
          catch _ => pure ()

      -- After params, the recursor has one motive per type in the mutual block.
      -- Each motive has type:  (i₁ : I₁) → ... → (iₖ : Iₖ) → T params i₁...iₖ → Sort u
      -- We peel all forall binders: the last one's domain is the inductive type
      -- application (giving us `domainStx`), and the preceding binders are index
      -- binders (giving us `indexBinderStxs` for each motive).
      forallBoundedTelescope restType0 (some numMotives) (fun motiveVars restType => do
        let motiveDomainInfo ← motiveVars.mapM fun mv => do
          let mType ← inferType mv
          forallTelescope mType fun fvars _sortBody => do
            if fvars.isEmpty then throwError "unexpected motive type (no binders): {mType}"
            let mainFvar := fvars.back!
            let domain ← inferType mainFvar
            let .const indName _ := domain.getAppFn
              | throwError "derive_deceq: expected motive domain to be a named type, got {domain}"
            let numIndices := fvars.size - 1
            -- Use deterministic index names to avoid collisions when
            -- multiple indices delab to the same auto-name (e.g. both `a✝`)
            let indexNames := (Array.range numIndices).map fun i =>
              mkIdent (.mkSimple s!"_idx{i}")
            let mut indexBinderStxs : Array (TSyntax ``bracketedBinder) := #[]
            for i in [:numIndices] do
              let idxType ← inferType fvars[i]!
              let typeStx ← withOptions (fun o => pp.fullNames.set o true) <|
                PrettyPrinter.delab idxType
              indexBinderStxs := indexBinderStxs.push
                (← `(bracketedBinder| {$(indexNames[i]!) : $typeStx}))
            -- Build domain syntax from indName + params + fresh index names
            -- (avoids delab collision issues)
            let domainStx ← do
              if numIndices == 0 then
                withOptions (fun o => pp.fullNames.set o true) <|
                  PrettyPrinter.delab domain
              else
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
            return (domainStx, indName, indexBinderStxs)
        let motiveDomainStxs := motiveDomainInfo.map (·.1)
        let motiveIndNames := motiveDomainInfo.map (·.2.1)
        let motiveIndexBinderStxs := motiveDomainInfo.map (·.2.2)

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
            let mut ctorsByType : Array (Array CtorInfo) := .replicate numMotives #[]

            for minorIdx in [:numMinors] do
              let minorType ← inferType minorVars[minorIdx]!
              let result ←
                forallTelescopeReducing minorType (fun fvars retType => do
                  -- (a) Which type does this constructor belong to?
                  let motiveFvar := retType.getAppFn
                  let typeIdx ← motiveVars.findIdxM? fun mv => return mv == motiveFvar
                  let some typeIdx := typeIdx
                    | throwError "derive_deceq: minor's return type doesn't reference any known motive"
                  -- (b) Extract constructor name from return type: `motive_j (Ctor ...)`.
                  let .app _ ctorApp := retType
                    | throwError "derive_deceq: unexpected recursor return type shape: {retType}"
                  let .const ctorName _ := ctorApp.getAppFn
                    | throwError "derive_deceq: expected constructor application, got {ctorApp}"

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
                      if !referenced then
                        fieldTypes := fieldTypes.push xType
                        fieldVars := fieldVars.push x

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
                        ihMotiveIndices := ihMotiveIndices.set! fIdx ihMotiveIdx
                        break

                  -- (e) Flag Prop-typed fields (compared by proof irrelevance, not structurally)
                  let mut propFlags := Array.replicate numFields false
                  for i in [:numFields] do
                    propFlags := propFlags.set! i (← Meta.isProp fieldTypes[i]!)

                  let fields := (Array.range numFields).map fun i =>
                    { type := fieldTypes[i]!,
                      recursiveMotiveIdx := ihMotiveIndices[i]!,
                      isProp := propFlags[i]! : FieldInfo }

                  return (ctorName, typeIdx, fields))

              let (ctorName, typeIdx, fields) := result
              ctorsByType := ctorsByType.modify typeIdx
                (·.push { name := ctorName, typeIdx, fields })

            return ctorsByType)

        return (paramBinderStxs, instBinderStxs, motiveDomainStxs, motiveIndNames,
                motiveIndexBinderStxs, ctorsByType)))

  let ns ← getCurrNamespace
  -- Demangle private names so the emitted `def` name matches what Lean
  -- will re-mangle under `private def` (see `isPrivate` below).
  let defBaseNames := typeNames.map fun n =>
    (Lean.privateToUserName? n |>.getD n).replacePrefix ns .anonymous
  let isPrivate := Lean.isPrivateName firstType
  return { typeNames, defBaseNames, numUserTypes, numMotives,
           motiveDomainStxs, motiveIndNames, motiveIndexBinderStxs,
           paramBinderStxs, instBinderStxs, ctorsByType, isPrivate }

/-- Generate the `if`/`subst` comparison chain used by the standard
    `DecidableEq` deriver. Each field is compared in sequence; after `subst h`,
    types of subsequent fields are unified, which is what makes index-changing
    recursion elaborate correctly when later field types depend on earlier
    equalities. -/
private def mkIfSubstChain (analysis : RecursorAnalysis)
    : List (Ident × Ident × Option Nat × Bool) → TermElabM Term
  | [] => `(isTrue rfl)
  | (a, b, motiveIdx, isProof) :: rest => do
    let rhs ← withFreshMacroScope do
      if isProof then
        `(have h : @$a = @$b := rfl; by subst h; exact $(← mkIfSubstChain analysis rest))
      else
        let sameCtor ← mkIfSubstChain analysis rest
        `(if h : @$a = @$b then
           by subst h; exact $sameCtor
          else
           isFalse (by intro heq; injection heq; apply h _; assumption))
    -- For recursive fields, create a local Decidable instance so that
    -- `if h : @a = @b` can find the decision procedure.
    if let some j := motiveIdx then
      let decEqId := mkIdent (motiveDecEqName analysis j)
      `(let inst := $decEqId @$a @$b; $rhs)
    else
      return rhs

/-- Generate the lambda for one constructor's same-constructor comparison.
    Opens the constructor type to classify each field as fixed (appears in return type,
    shared between both sides) or free (gets separate a/b variables). This handles
    index-changing recursion where free index variables must be compared and subst'd
    before recursive fields can be compared (since their types may differ). -/
private def mkSameCtorAlt
    (analysis : RecursorAnalysis)
    (ctor : CtorInfo)
    : TermElabM Term := do
  let ctorConstInfo ← getConstInfoCtor ctor.name
  let indVal ← getConstInfoInduct ctorConstInfo.induct
  forallTelescopeReducing ctorConstInfo.type (fun fvars returnType => do
    let returnType ← Core.betaReduce returnType
    let numParams := indVal.numParams
    let numFields := ctorConstInfo.numFields

    if numFields == 0 then return ← `(fun () => isTrue rfl)

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

      -- Fixed binders are unified between both sides by the motive, so the
      -- minor lambda takes them only once (as `_`). Free binders appear twice.
      if isFixed then
        ctorArgs1 := ctorArgs1.push (← `(_))
      else
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

      if hasFieldInfo then
        let field := ctor.fields[fieldIdx]!
        fieldIdx := fieldIdx + 1
        if !isFixed then
          if !field.isProp then
            todo := todo.push (fi, gi, field.recursiveMotiveIdx, false)
          else
            todo := todo.push (fi, gi, none, true)
      else if !isFixed then
        -- Free implicit index binder (determined by another user binder):
        -- plain decEq; the subst chain unifies it with the other field.
        let xType ← inferType x
        let isProof ← Meta.isProp xType
        if !isProof then
          todo := todo.push (fi, gi, none, false)

    if ctorArgs1.isEmpty then return ← `(fun () => isTrue rfl)
    let rhs ← mkIfSubstChain analysis todo.toList
    `(@fun $ctorArgs1:term* $ctorArgs2:term* => $rhs))

/-- Generate a `def` command for a DecEq function (user or auxiliary motive). -/
private def mkDecEqFunc
    (analysis : RecursorAnalysis)
    (sameCtorNames : Array Name)
    (isRecursive : Array Bool)
    (motiveIdx : Nat)
    : TermElabM (TSyntax `command) := do
  let domainStx := analysis.motiveDomainStxs[motiveIdx]!
  let defId := mkIdent (motiveDecEqName analysis motiveIdx)
  let aId := mkIdent `a
  let bId := mkIdent `b

  let indName := analysis.motiveIndNames[motiveIdx]!
  let ctorIdxId := mkIdent (mkCtorIdxName indName)
  let sameCtorId := mkIdent sameCtorNames[motiveIdx]!
  let ctors := analysis.ctorsByType[motiveIdx]!

  -- Short-circuits for degenerate inductives that break the standard
  -- casesOnSameCtor + ctorIdx path.
  let indexBinders := analysis.motiveIndexBinderStxs[motiveIdx]!
  let mainBinderStx ← `(bracketedBinder| ($aId $bId : $domainStx))
  let allBinderStxs := analysis.paramBinderStxs ++ analysis.instBinderStxs
    ++ indexBinders ++ #[mainBinderStx]

  -- Empty inductive — no inhabitant exists, so `nomatch` either argument.
  if ctors.isEmpty then
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
    return ←
      if analysis.isPrivate then
        `(command| private def $defId
            $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := isTrue rfl)
      else
        `(command| def $defId
            $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := isTrue rfl)

  let mut alts : Array Term := #[]
  for ctor in ctors do
    alts := alts.push (← mkSameCtorAlt analysis ctor)

  -- For indexed types, casesOnSameCtor's motive has implicit index binders
  -- that Lean can't always infer. Provide the motive explicitly, using the
  -- same index binder names that appear in domainStx so references resolve.
  let sameCtorCall ← do
    if indexBinders.isEmpty then
      if ctors.size ≤ 1 then
        `($sameCtorId $aId $bId rfl $alts:term*)
      else
        `($sameCtorId $aId $bId h $alts:term*)
    else
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
      if ctors.size ≤ 1 then
        `($sameCtorId (motive := $motive) $aId $bId rfl $alts:term*)
      else
        `($sameCtorId (motive := $motive) $aId $bId h $alts:term*)

  let body : Term ←
    if ctors.size ≤ 1 then
      pure sameCtorCall
    else
      `(match decEq ($ctorIdxId $aId) ($ctorIdxId $bId) with
        | .isTrue h => $sameCtorCall
        | .isFalse h => isFalse (fun h' => h (congrArg $ctorIdxId h')))

  let termSuffix ← if isRecursive[motiveIdx]!
    then `(Parser.Termination.suffix| termination_by structural $aId)
    else `(Parser.Termination.suffix|)
  if analysis.isPrivate then
    `(command| private def $defId $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := $body
      $termSuffix:suffix)
  else
    `(command| def $defId $[$allBinderStxs:bracketedBinder]* : Decidable ($aId = $bId) := $body
      $termSuffix:suffix)

/-- Main entry point: derive DecidableEq for all types in a mutual group. -/
def deriveForGroup (firstName : Name) : CommandElabM Unit := do
  Deriving.withoutExposeFromCtors firstName <| do
  let analysis ← liftTermElabM <| MetaM.run' <| analyzeRecursor firstName

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
        names := names.push .anonymous
      else
        let sameCtorName ← mkFreshUserName (indName ++ `match_on_same_ctor)
        mkCasesOnSameCtor sameCtorName indName
        names := names.push sameCtorName
    return names

  -- Generate decEq functions for ALL motives (user + auxiliary)
  let isRecursive := computeIsRecursive analysis
  let mut defs : Array Syntax := #[]
  for i in [:analysis.numMotives] do
    let defCmd ← liftTermElabM <| mkDecEqFunc analysis sameCtorNames isRecursive i
    trace[DecEqMutual.derive] "Generated def:\n{defCmd}"
    defs := defs.push defCmd

  -- Wrap in mutual block
  let mutualStx := Lean.mkNode ``Lean.Parser.Command.mutual
    #[mkAtom "mutual", mkNullNode defs, mkAtom "end"]

  trace[DecEqMutual.derive] "Elaborating mutual block..."
  withEnableInfoTree false do
    elabCommand mutualStx

  -- Register DecidableEq instances only for user types, using the standard
  -- deriving infrastructure (handles instance naming, private ctors, etc.).
  -- Each type gets its own Context so instance names don't collide.
  for i in [:analysis.numUserTypes] do
    let typeName := analysis.typeNames[i]!
    let instanceCmds ← liftTermElabM do
      let instName ← Deriving.mkInstName ``DecidableEq typeName
      let typeInfo ← getConstInfoInduct typeName
      let auxFunName := motiveDecEqName analysis i
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
    -- synthInstance may fail for custom containers without stdlib DecidableEq;
    -- in that case we skip the optimization (our generated function still works).
    try liftTermElabM do
      let auxInfo ← getConstInfo auxFunName
      let auxType := auxInfo.type
      let uParams := auxInfo.levelParams
      let lvls := uParams.map mkLevelParam
      -- _real: synthesize the stdlib DecidableEq instance at the same type
      let realVal ← Meta.forallTelescope auxType fun xs bodyType => do
        let inst ← Meta.synthInstance bodyType
        Meta.mkLambdaFVars xs inst
      addAndCompile (.defnDecl {
        name := realName
        levelParams := uParams
        type := auxType
        value := realVal
        hints := .abbrev
        safety := .safe
      })
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
    catch _ =>
      trace[DecEqMutual.derive] "csimp: skipped {auxFunName} (no stdlib instance)"

initialize registerTraceClass `DecEqMutual.derive

syntax (name := deriveDecEqCmd) "derive_deceq " ident+ : command

@[command_elab deriveDecEqCmd]
def elabDeriveDecEq : CommandElab := fun stx => do
  let idents := stx[1].getArgs
  if idents.isEmpty then
    throwError "derive_deceq requires at least one type name"
  if idents.size > 1 then
    logWarning "derive_deceq: only the first type name is needed; \
      all types in the mutual block are derived automatically. Ignoring extra names."
  let firstName ← resolveGlobalConstNoOverload idents[0]!
  deriveForGroup firstName

end DecEqMutual.Derive
