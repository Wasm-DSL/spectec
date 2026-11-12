/-
  sandbox_8.lean

  A from-scratch, MUCH simpler re-implementation of the same idea as
  `ExtendedDeriveDecEq.lean`, deliberately built to exercise every piece of
  metaprogramming syntax that came up while reading that file (and a couple
  more that show up naturally once you're building something similar).

  Instead of deriving `DecidableEq` for nested/mutual inductive types, this
  derives a much simpler thing: for a plain (non-nested, non-mutual, possibly
  polymorphic) inductive type `T`, generate

    def T.ctorName {params...} (x : T params...) : String := <name of x's constructor>

  and register it as an instance of a toy class `HasCtorName`. This needs
  just enough recursor/constructor analysis to require the same toolkit
  (telescopes, quotation, raw syntax assembly, name mangling, tracing, csimp,
  the Deriving infrastructure, ...) without the real file's complexity
  (motives-per-mutual-member, index binders, IH bookkeeping, casesOnSameCtor).

  Every section below is commented with (a) which real snippet in
  `ExtendedDeriveDecEq.lean` it corresponds to, and (b) what the construct
  does. Every generated declaration is exercised at the bottom of the file
  and its actual output is captured in a trailing comment -- run
  `lake env lean sandbox_8.lean` yourself to reproduce it.
-/

-- ── §0. Imports and namespace open ──────────────────────────────────────
-- cf. ExtendedDeriveDecEq.lean lines 41-46: pulling in the compiler's own
-- internals as an ordinary library, and opening their namespaces so `MetaM`,
-- `elabCommand`, `mkIdent`, etc. don't need full qualification everywhere.
import Lean
open Lean Meta Elab Command Term

namespace CtorNameDerive
-- cf. line 48/738 `namespace DecEqMutual.Derive ... end DecEqMutual.Derive`:
-- every name defined below (helper functions AND generated declarations)
-- lives under this prefix unless explicitly qualified away.

-- ── §1. Trace class registration ────────────────────────────────────────
-- cf. line 723: `initialize registerTraceClass \`DecEqMutual.derive`.
-- Verified fact from the audit: `set_option trace.X true` for a class
-- registered via `initialize` in THIS SAME file does not take effect until
-- the file is compiled and re-imported (the option registration is a
-- module-load-time effect, not a same-pass one) -- exactly why the real
-- project keeps ExtendedDeriveDecEq.lean and sandbox_5.lean separate. So:
-- `trace[CtorNameDerive.derive]` calls below will run (harmlessly, as
-- no-ops) but won't print anything when this file is elaborated standalone.
-- If you want to see them fire, split this file the same way the real repo
-- does and `set_option trace.CtorNameDerive.derive true` in the importer.
initialize registerTraceClass `CtorNameDerive.derive

-- ── §2. Bookkeeping structures with `deriving Repr, Inhabited` ─────────
-- cf. lines 54-58, 61-65: `structure FieldInfo where ... deriving Repr, Inhabited`
-- This is the *ordinary* `deriving` you already know from generated Lean
-- output -- just applied to the tool's own internal analysis data instead
-- of to a spectec-generated type. `Repr` lets us `#eval`/log the structure
-- for debugging; `Inhabited` gives it a placeholder default value.
structure CtorRecord where
  name      : Name
  numFields : Nat
deriving Repr, Inhabited

structure TypeAnalysis where
  typeName        : Name
  baseName        : Name             -- namespace-stripped, for building the generated def's name
  isPrivate       : Bool
  paramBinderStxs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  domainStx       : Term             -- syntax for `T param₁ ... paramₙ`
  ctors           : Array CtorRecord
deriving Repr

-- ── §3. Pattern-match-or-throw, `let mut`/ranges/arrays, telescopes ────
-- cf. lines 130-392 `analyzeRecursor`, simplified drastically: no motives,
-- no mutual block, no IH/index bookkeeping -- just "how many fields does
-- each constructor have, and what are this type's own parameters".
def analyzeType (indName : Name) : MetaM TypeAnalysis := do
  let indVal ← getConstInfoInduct indName
  -- cf. line 316 `if indVal.all.any ...`: reject the shapes this toy
  -- doesn't handle, with a clear message -- same spirit as the real file's
  -- guardrails (e.g. line 317-320's higher-order-argument rejection).
  if indVal.all.length > 1 then
    throwError "derive_ctor_name: {indName} is part of a mutual block \
      ({indVal.all}) -- this toy deriver only handles single, standalone types"

  let numParams := indVal.numParams
  -- cf. line 145 `extractBinderInfos`: the real file reads each param's
  -- ORIGINAL binder info (implicit vs explicit vs instance-implicit) off
  -- the inductive type itself, since the recursor makes every param
  -- explicit and loses that distinction. This toy always emits `{α : Type}`
  -- uniformly (every example type below only has plain `Type`-sorted
  -- params), so that extra bookkeeping step is skipped here.

  -- cf. lines 154-182 `forallBoundedTelescope ... numParams`: open exactly
  -- the parameter binders, build `{α : Type}`-style syntax for each, and
  -- (cf. lines 174-182 `mkAppM` + `isTypeCorrect`) probe whether each
  -- parameter itself already has some other instance available -- here,
  -- as a much simpler stand-in for the real file's `[DecidableEq α]`
  -- threading, we just check `Inhabited α` and log the result via `trace`.
  let (paramBinderStxs, domainStx) ←
    forallBoundedTelescope indVal.type (some numParams) fun paramVars _ => do
      let mut paramBinderStxs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      for i in [:numParams] do
        let v := paramVars[i]!
        let ldecl ← v.fvarId!.getDecl
        let nameId := mkIdent ldecl.userName
        -- cf. lines 165-166: pretty-print the parameter's type back to
        -- syntax with fully-qualified names switched on.
        let typeStx ← withOptions (fun o => pp.fullNames.set o true) <|
          PrettyPrinter.delab ldecl.type
        paramBinderStxs := paramBinderStxs.push (← `(bracketedBinder| {$nameId : $typeStx}))
        -- probe: does `Inhabited <param>` type-check?
        try
          let c ← mkAppM ``Inhabited #[v]
          if ← isTypeCorrect c then
            trace[CtorNameDerive.derive] "param {ldecl.userName} admits Inhabited"
        catch _ => pure ()
      -- cf. lines 217-228: rebuild `T param₁ ... paramₙ` as syntax from the
      -- inductive's name plus the freshly-opened parameter fvars.
      let indNameId := mkIdent indName
      let mut argStxs : Array Term := #[]
      for i in [:numParams] do
        let argStx ← withOptions (fun o => pp.fullNames.set o true) <|
          PrettyPrinter.delab paramVars[i]!
        argStxs := argStxs.push argStx
      let domainStx ← `($indNameId $argStxs*)      -- bare splice, cf. §7 below
      return (paramBinderStxs, domainStx)

  -- cf. lines 251-379 (drastically simplified): for each constructor, just
  -- count its non-parameter fields via `forallTelescopeReducing`.
  let mut ctors : Array CtorRecord := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let numFields ← forallTelescopeReducing ctorInfo.type fun fvars _ =>
      pure (fvars.size - numParams)
    ctors := ctors.push { name := ctorName, numFields }

  -- cf. lines 384-389: demangle a `private` name so the generated `def`'s
  -- name matches what Lean will re-mangle it to under `private def`.
  let ns ← getCurrNamespace
  let baseName := (Lean.privateToUserName? indName |>.getD indName).replacePrefix ns .anonymous
  let isPrivate := Lean.isPrivateName indName

  return { typeName := indName, baseName, isPrivate, paramBinderStxs, domainStx, ctors }

-- ── §4. Building the comparison-free "which constructor" function ──────
-- cf. `mkSameCtorAlt`/`mkDecEqFunc` (lines 425-595), simplified: no
-- same-constructor unification needed, just "ignore every field, return
-- the constructor's base name as a string".
def mkCtorNameFunc (analysis : TypeAnalysis) : TermElabM (TSyntax `command) := do
  let fnId := mkIdent (analysis.baseName ++ `ctorName)
  let xId := mkIdent `x

  -- Empty inductive: cf. lines 528-536, `nomatch` short-circuit.
  if analysis.ctors.isEmpty then
    let binders := analysis.paramBinderStxs
    return ←
      if analysis.isPrivate then
        `(command| private def $fnId $[$binders:bracketedBinder]* ($xId : $analysis.domainStx) : String :=
            nomatch $xId)
      else
        `(command| def $fnId $[$binders:bracketedBinder]* ($xId : $analysis.domainStx) : String :=
            nomatch $xId)

  -- Non-empty: one `fun` per constructor, ignoring all of its fields via a
  -- splice of `_` wildcards (cf. §7's `$xs:term*`, mirroring the real
  -- file's own use of a bare splice for a variable number of arguments),
  -- applied through `T.casesOn`.
  let mut minors : Array Term := #[]
  for ctor in analysis.ctors do
    let wildcards : Array Term := Array.replicate ctor.numFields (← `(_))
    let nameLit := Syntax.mkStrLit ctor.name.getString!
    -- A nullary constructor's minor premise has type `motive Ctor` directly
    -- (no binders to open), so it's just the literal -- not a `fun`. The
    -- `⟨nameLit.raw⟩` coercion (cf. line 227, 565-566, and the earlier
    -- audit's §"anonymous-constructor coercion") re-tags the `StrLit`
    -- syntax as a plain `Term`, matching the other branch's type.
    let minor ←
      if ctor.numFields == 0
      then pure (⟨nameLit.raw⟩ : Term)
      else `(fun $wildcards:term* => $nameLit)
    minors := minors.push minor

  let casesOnId := mkIdent (analysis.typeName ++ `casesOn)
  let body ← `($casesOnId (motive := fun _ => String) $xId $minors:term*)

  let binders := analysis.paramBinderStxs
  if analysis.isPrivate then
    `(command| private def $fnId $[$binders:bracketedBinder]* ($xId : $analysis.domainStx) : String := $body)
  else
    `(command| def $fnId $[$binders:bracketedBinder]* ($xId : $analysis.domainStx) : String := $body)

-- ── §5. A toy typeclass, mirroring how the real file registers instances ─
class HasCtorName (α : Type) where
  ctorName : α → String

-- ── §6. Raw syntax assembly + the Deriving infrastructure ──────────────
def deriveCtorName (indName : Name) : CommandElabM Unit := do
  let analysis ← liftTermElabM <| MetaM.run' <| analyzeType indName
  -- cf. line 602-607: trace what was found before generating anything.
  trace[CtorNameDerive.derive] "Type: {analysis.typeName}, private={analysis.isPrivate}"
  for c in analysis.ctors do
    trace[CtorNameDerive.derive] "  ctor {c.name}, nfields={c.numFields}"

  let defCmd ← liftTermElabM <| mkCtorNameFunc analysis
  trace[CtorNameDerive.derive] "Generated def:\n{defCmd}"

  -- cf. lines 632-638: wrap in `mutual ... end` via raw syntax-tree
  -- assembly (`mkAtom`/`mkNullNode`/`Lean.mkNode`) rather than quotation --
  -- done here even for a single def, matching the real file's blanket
  -- approach (it always wraps, whether or not the group is genuinely
  -- mutually recursive).
  let mutualStx := Lean.mkNode ``Lean.Parser.Command.mutual
    #[mkAtom "mutual", mkNullNode #[defCmd], mkAtom "end"]
  withEnableInfoTree false do
    elabCommand mutualStx

  -- cf. lines 640-655: register the instance via the shared Deriving
  -- infrastructure, exactly the machinery every `deriving Foo` handler
  -- (including stock `deriving BEq`) uses under the hood, applied here to
  -- OUR OWN toy class instead of a class core already knows about.
  let instanceCmds ← liftTermElabM do
    let instName ← Deriving.mkInstName ``HasCtorName indName
    let typeInfo ← getConstInfoInduct indName
    let derivCtx : Deriving.Context :=
      { instName, typeInfos := #[typeInfo],
        auxFunNames := #[analysis.baseName ++ `ctorName], usePartial := false }
    -- cf. `` ``DecidableEq `` at line 652: double-backtick resolves the name
    -- via normal lookup; a single backtick (as used two lines up would be
    -- wrong here) is taken completely literally, with no namespace search --
    -- it would produce the unresolved name `HasCtorName` instead of the
    -- real `CtorNameDerive.HasCtorName`.
    --
    -- `useAnonCtor := true` here, UNLIKE the real file's `false` at line
    -- 652: `DecidableEq` is a plain `def`/`abbrev` (a function type), so its
    -- instance body is just the function itself; `HasCtorName` is a
    -- one-method `class` (i.e. really a one-field `structure`), so its
    -- instance body needs the anonymous-constructor wrapper `⟨...⟩` around
    -- the function -- `mkInstanceCmds` inserts that wrapping for you when
    -- told to.
    Deriving.mkInstanceCmds derivCtx ``HasCtorName #[indName] (useAnonCtor := true)
  for cmd in instanceCmds do
    trace[CtorNameDerive.derive] "Registering instance: {cmd}"
    elabCommand cmd

-- ── §7. Custom command syntax + command elaborator ──────────────────────
-- cf. lines 725-736: `syntax ... : command` + `@[command_elab ...]`, the
-- two-step form (grammar rule, then attach an elaborator by name) rather
-- than the one-step `elab "..." : command => do ...` shorthand -- kept
-- identical to the real file's style deliberately.
syntax (name := deriveCtorNameCmd) "derive_ctor_name " ident+ : command

@[command_elab deriveCtorNameCmd]
def elabDeriveCtorName : CommandElab := fun stx => do
  -- cf. line 729: `stx[1].getArgs` unpacks the `ident+` repetition node.
  let idents := stx[1].getArgs
  if idents.isEmpty then
    throwError "derive_ctor_name requires at least one type name"
  -- cf. line 735: resolve the user-typed identifier to an actual Name.
  for identStx in idents do
    let name ← resolveGlobalConstNoOverload identStx
    deriveCtorName name

end CtorNameDerive

-- ═══════════════════════════════════════════════════════════════════════
-- §8. The running example itself
-- ═══════════════════════════════════════════════════════════════════════

open CtorNameDerive (HasCtorName)

-- A plain, mixed-arity enum (cf. `sx`/`sz`-style types from the Rocq/Lean
-- backend discussion earlier in this session).
inductive Coin where
  | heads
  | tails
  | edge (spins : Nat)

derive_ctor_name Coin
-- Real captured trace (via `set_option trace.CtorNameDerive.derive true`,
-- split across two files the way §1 explains is required):
--   [CtorNameDerive.derive] Type: Coin, private=false
--   [CtorNameDerive.derive]   ctor Coin.heads, nfields=0
--   [CtorNameDerive.derive]   ctor Coin.tails, nfields=0
--   [CtorNameDerive.derive]   ctor Coin.edge, nfields=1
--   [CtorNameDerive.derive] Generated def:
--       def Coin.ctorName (x : Coin) : String :=
--         Coin.casesOn (motive := fun _ => String) x "heads" "tails" fun _ => "edge"
--   [CtorNameDerive.derive] Registering instance: instance instHasCtorNameCoin :
--       CtorNameDerive.HasCtorName (@Coin) := ⟨Coin.ctorName⟩

#eval Coin.ctorName .heads          -- "heads"
#eval Coin.ctorName (.edge 3)       -- "edge"
#eval HasCtorName.ctorName Coin.tails   -- "tails" (via the registered instance; `.tails`
                                         -- can't be used here since `HasCtorName.ctorName`
                                         -- is generic across every instance, so its argument's
                                         -- type isn't known until the argument itself is)

-- An empty inductive -- exercises the `nomatch` short-circuit.
inductive Never where

derive_ctor_name Never
-- Generates: def Never.ctorName (x : Never) : String := nomatch x
#check @Never.ctorName   -- Never → String

-- A private type -- exercises `private def` + name-demangling.
private inductive Mood where
  | happy
  | sad

derive_ctor_name Mood
-- Generates a `private def Mood.ctorName ...` (only visible in this file/module).
#eval Mood.ctorName .happy   -- "happy"

-- A polymorphic wrapper -- exercises the parameter-binder splice
-- (`$[$binders:bracketedBinder]*`) with a genuinely non-empty binder array.
inductive Box (α : Type) where
  | mk (a : α)

derive_ctor_name Box
-- Real captured trace:
--   [CtorNameDerive.derive] param α admits Inhabited
--   [CtorNameDerive.derive] Type: Box, private=false
--   [CtorNameDerive.derive]   ctor Box.mk, nfields=1
--   [CtorNameDerive.derive] Generated def:
--       def Box.ctorName {α : Type} (x : Box α) : String :=
--         Box.casesOn (motive := fun _ => String) x fun _ => "mk"
--   [CtorNameDerive.derive] Registering instance:
--       instance instHasCtorNameBox {α} [CtorNameDerive.HasCtorName α] :
--           CtorNameDerive.HasCtorName (@Box α) := ⟨Box.ctorName⟩
--
-- That registered instance is a good, honest gotcha to notice: it has a
-- `[HasCtorName α]` PREMISE that `Box.ctorName`'s own body never actually
-- needs (it ignores the field entirely). `Deriving.mkInstanceCmds` is
-- generic, shared infrastructure -- it doesn't know THIS particular class's
-- method ignores its argument, so it defaults to the same "thread an
-- instance constraint through every type parameter" policy that genuinely
-- IS required for e.g. `deriving BEq`/`DecidableEq`. The `#eval`s below call
-- `Box.ctorName` directly (which works fine, unconditionally); going through
-- the class instance instead -- `HasCtorName.ctorName (Box.mk (3 : Nat))`
-- -- would fail to synthesize, since no `HasCtorName Nat` was ever derived.
#eval Box.ctorName (Box.mk (3 : Nat))     -- "mk"
#eval Box.ctorName (Box.mk "hello")       -- "mk"

-- ═══════════════════════════════════════════════════════════════════════
-- §9. Raw `Declaration` construction + `csimp`
-- ═══════════════════════════════════════════════════════════════════════
-- cf. lines 683-719: install a function via the low-level Expr/Declaration
-- API (bypassing quotation/elabCommand entirely -- this is one level lower
-- than everything in §3-§6, which all went through `` `(command| ...) ``),
-- then swap it for a differently-implemented-but-equal version via
-- `@[csimp]`. The real file's equality proof uses `Subsingleton.elim`
-- specifically because `Decidable p` is a subsingleton (proof irrelevance
-- on `p : Prop` makes any two `isTrue`s equal); `Nat` is NOT a subsingleton
-- (`0 ≠ 1`), so here the swap is proved by plain `rfl` instead -- the right
-- tool once both sides are closed, concrete computations that reduce to the
-- same normal form.

-- "slow": recomputed by walking Coin's constructor list every call, rather
-- than being a precomputed literal (a stand-in for the real file's
-- "generated the honest way, but slower than the stdlib path" functions).
def Coin.numCtorsSlow (_ : Unit) : Nat := Id.run do
  let mut n := 0
  for _ in [`Coin.heads, `Coin.tails, `Coin.edge] do
    n := n + 1
  return n

-- cf. lines 688-699 (`realVal`/`addAndCompile (.defnDecl {...})`): install
-- the "fast" version directly from an `Expr`, computed via `MetaM`
-- reflection over the real environment, never going through the parser.
#eval show MetaM Unit from do
  let indVal ← getConstInfoInduct ``Coin
  let n := indVal.ctors.length
  let ty := Expr.forallE `_ (Expr.const ``Unit []) (Expr.const ``Nat []) .default
  let val ← Meta.withLocalDecl `_ .default (Expr.const ``Unit []) fun fv =>
    Meta.mkLambdaFVars #[fv] (Lean.mkNatLit n)
  Lean.addAndCompile (.defnDecl {
    name := `Coin.numCtorsFast
    levelParams := []
    type := ty
    value := val
    hints := .abbrev
    safety := .safe
  })

#eval Coin.numCtorsFast ()   -- 3
#eval Coin.numCtorsSlow ()   -- 3 (same value, different implementation)

-- cf. lines 700-717 (`Subsingleton.elim` + `funext`, `addDecl (.thmDecl {...})`):
-- prove the two implementations agree. Ordinary `theorem` syntax suffices
-- here (no need for raw `.thmDecl` construction) since, unlike the real
-- file, this proof obligation is simple enough to state directly.
theorem Coin.numCtorsSlow_eq_fast : Coin.numCtorsSlow = Coin.numCtorsFast := rfl

-- cf. line 718: register the csimp rewrite -- "when compiling/evaluating
-- code, replace calls to `numCtorsSlow` with calls to `numCtorsFast`",
-- without affecting which theorem the kernel actually checked.
#eval show MetaM Unit from do
  Lean.Compiler.CSimp.add ``Coin.numCtorsSlow_eq_fast .global
  IO.println "csimp registered: Coin.numCtorsSlow → Coin.numCtorsFast"
