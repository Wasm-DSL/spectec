/-
  sandbox_9.lean -- one minimal, independent, runnable example per
  metaprogramming construct, each grounded in an everyday grocery/kitchen
  item instead of an abstract name. No shared "running example" -- each
  numbered block stands alone and can be read (or deleted) independently.
  Every `#eval`/output shown in a trailing comment was actually captured by
  running `lake env lean sandbox_9.lean` -- run it yourself to reproduce.
-/
import Lean
open Lean Meta Elab Command Term

-- ── 1. Trace classes ────────────────────────────────────────────────────
-- A trace class is a named, toggleable logging channel. `trace[...]` needs
-- a monad with tracing support (like `MetaM`), not the bare `Id` monad --
-- verified: swapping in `Id.run do` here fails with
-- `failed to synthesize instance MonadTrace Id`.
initialize registerTraceClass `kitchen.log

#eval show MetaM Unit from do
  trace[kitchen.log] "adding up the basket"
  IO.println s!"{(3 : Nat) + 4}"   -- 7
-- NOTE: `set_option trace.kitchen.log true` only takes effect for code
-- compiled in a DIFFERENT file that imports this one (verified earlier this
-- session) -- registration is a module-load-time effect, not visible within
-- the same top-to-bottom elaboration pass. So the trace line above runs,
-- but silently, here.

-- ── 2. Custom syntax + command elaborator ───────────────────────────────
-- Adds a brand-new command `yell "..."` that shouts a string in uppercase.
syntax (name := yellCmd) "yell " str : command

@[command_elab yellCmd]
def elabYell : CommandElab := fun stx => do
  -- `Syntax.isStrLit?` extracts the literal string from a `str`-category
  -- node (there's no plain `.getString` on raw `Syntax` -- verified).
  let s := stx[1].isStrLit?.getD ""

  logInfo s.toUpper

yell "fresh apples"   -- logs: FRESH APPLES

-- ── 3. throwError / logWarning / resolveGlobalConstNoOverload ──────────
syntax (name := greetCmd) "greet " ident+ : command

@[command_elab greetCmd]
def elabGreet : CommandElab := fun stx => do
  let names := stx[1].getArgs
  if names.isEmpty then throwError "greet needs at least one name"
  if names.size > 1 then logWarning "only greeting the first name, ignoring the rest"
  let resolved ← resolveGlobalConstNoOverload names[0]!
  logInfo s!"hello, {resolved}!"

def grocer : String := "the grocer"
greet grocer         -- logs: hello, grocer!

-- ── 4a. Quotation + bracket-splice `$[$xs:cat]*` ────────────────────────
-- Builds a function with as many `Nat` parameters as items you name.
elab "mk_price_fn " nm:ident " for " items:ident+ : command => do
  let binders ← items.mapM fun a => `(bracketedBinder| ($a : Nat))
  let cmd ← `(command| def $nm $[$binders:bracketedBinder]* : Nat := 0)
  elabCommand cmd

-- `set_option ... in` has to scope the INVOCATION below (where the unused
-- params actually get bound), not the command's own definition above.
set_option linter.unusedVariables false in
mk_price_fn basketPrice for apple banana cherry
#check @basketPrice   -- basketPrice : Nat → Nat → Nat → Nat
#eval basketPrice 2 1 3   -- 0 (the function body is just `0`)
-- ── 4b. Quotation + bare splice `$xs:cat*` ──────────────────────────────
-- Splices an already-built array of terms into an existing "many"-argument slot.
def appleCount : Nat := 3
def bananaCount : Nat := 4

def spliceApp (f : Ident) (extra : Array Term) : TermElabM Term := `($f $extra:term*)

elab "mk_total" : command => do
  let cmd ← liftTermElabM do
    -- The generated def's name MUST come from `mkIdent`, spliced in via
    -- `$nm` -- writing `def basketTotal` literally inside the quotation
    -- instead makes Lean's hygiene machinery treat it as a fresh, private,
    -- auto-renamed binding (verified: produces an unfindable name like
    -- `basketTotal._@._stdin.NNN._hygCtx._hyg.2`, and the later `#eval
    -- basketTotal` fails with "unknown identifier").
    let nm := mkIdent `basketTotal
    let a ← `(appleCount)
    let b ← `(bananaCount)
    let body ← spliceApp (mkIdent ``Nat.add) #[a, b]
    `(command| def $nm : Nat := $body)
  elabCommand cmd

mk_total
#eval basketTotal   -- 7

-- ── 5. nomatch ───────────────────────────────────────────────────────────
inductive EmptyFruitBowl where   -- zero constructors: no bowl can ever exist

def eatFrom (bowl : EmptyFruitBowl) : String := nomatch bowl
#check @eatFrom   -- eatFrom : EmptyFruitBowl → String (compiles: vacuously handled)

-- ── 6. MetaM / lifting / `<|` / `|>.` ───────────────────────────────────
def totalCost (apples bananas : Nat) : Nat := apples + bananas

#eval show MetaM Unit from do
  let ty ← Meta.inferType (Expr.const ``totalCost [])
  IO.println s!"totalCost's type is: {ty}"   -- Nat -> Nat -> Nat

#eval (· + 1) <| (· * 2) <| 3        -- one more than double 3 apples: 7
#eval 3 |>.succ |>.succ              -- 3 apples, plus one, plus one: 5

-- ── 7. `TSyntax `` ``cat`` -- a syntax value tagged with its category ────
def mkAppleBinder : TermElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
  `(bracketedBinder| (apple : Nat))

#eval show TermElabM Unit from do
  let b ← mkAppleBinder
  -- `logInfo`/trace pretty-print a FULL command/term nicely (see §4b's
  -- generated defs above), but a bare binder FRAGMENT (not embedded in a
  -- surrounding `fun`/`def`) has no working pretty-printer entry point on
  -- its own -- verified: `logInfo m!"{b}"` here gives "failed to pretty
  -- print term". Plain `toString` always works, showing the raw parse tree:
  IO.println (toString b)

-- ── 8. `let mut` + `[:n]` range + Array ops ─────────────────────────────
def basketPrices : Array Nat := #[2, 1, 3]   -- apple, banana, cherry
def sumBasket : Nat := Id.run do
  let mut total := 0
  for i in [:basketPrices.size] do
    total := total + basketPrices[i]!
  return total
#eval sumBasket   -- 6

-- ── 9. Raw syntax assembly: mkAtom / mkNullNode / Lean.mkNode ──────────
elab "declare_dozen" : command => do
  let nm := mkIdent `dozenEggs   -- (same hygiene reason as §4b -- must go via mkIdent)
  let d ← `(command| def $nm : Nat := 12)
  let wrapped := Lean.mkNode ``Lean.Parser.Command.mutual
    #[mkAtom "mutual", mkNullNode #[d], mkAtom "end"]
  elabCommand wrapped

declare_dozen
#eval dozenEggs   -- 12

-- ── 10. Quotations chosen via ordinary if/then/else ─────────────────────
def mkPriceTag (onSale : Bool) : TermElabM Term :=
  if onSale then `("SALE!") else `("full price")

#eval show TermElabM Unit from do
  IO.println s!"{← mkPriceTag true} / {← mkPriceTag false}"   -- "SALE!" / "full price"

-- ── 11. `private def` + `Lean.privateToUserName?` + `|>.getD` ──────────
private def secretRecipe : String := "grandma's secret chili"

run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if (n.toString.splitOn "secretRecipe").length > 1 then
      IO.println s!"mangled={n}, demangled={Lean.privateToUserName? n |>.getD n}"
      -- mangled=_private._stdin.0.secretRecipe, demangled=secretRecipe

-- ── 12. Pattern-match-or-throw: `let .ctor x := e | throwError ...` ────
def priceOf (item : String) : Option Nat :=
  if item = "apple" then some 2 else if item = "banana" then some 1 else none

#eval show MetaM Unit from do
  let some p := priceOf "apple"
    | throwError "no price on file for that item"
  IO.println s!"apple costs {p}"   -- apple costs 2

-- ── 13. Anonymous-constructor coercion `⟨...⟩` ──────────────────────────
structure Basket where
  items : List String

#eval (⟨["apple", "banana"]⟩ : Basket).items   -- ["apple", "banana"]

-- ── 14. String interpolation `s!"..."` ──────────────────────────────────
#eval s!"You have {3} apples and {2} bananas"

-- ── 15. Telescopes: open a function's binders as free variables ────────
def totalPrice (apples oranges : Nat) : Nat := apples + oranges

#eval show MetaM Unit from do
  let ty ← Meta.inferType (Expr.const ``totalPrice [])
  Meta.forallTelescope ty fun fvars _body => do
    logInfo m!"fvars: {fvars} | _body: {_body}"
    for fv in fvars do
      let n ← fv.fvarId!.getUserName
      let t ← Meta.inferType fv
      IO.println s!"binder {n} : {t}"   -- binder apples : Nat / binder oranges : Nat

-- ── 16. `mkAppM` (+ `isTypeCorrect`, + failure via `try`/`catch`) ───────
#eval show MetaM Unit from do
  let e ← Meta.mkAppM ``List.length #[toExpr [3]]
  IO.println s!"type-correct: {← Meta.isTypeCorrect e}"   -- true
  try
    let _ ← Meta.mkAppM ``String.append #[toExpr (3 : Nat), toExpr "apple"]
    IO.println "no exception"
  catch ex =>
    IO.println s!"mkAppM threw: {← ex.toMessageData.toString}"   -- Application type mismatch...

-- ── 17. `withOptions` + `PrettyPrinter.delab` ───────────────────────────
#eval show MetaM Unit from do
  let e := Expr.const ``List.length []
  let stx ← withOptions (fun o => pp.fullNames.set o true) <| PrettyPrinter.delab e
  IO.println s!"delab'd: {stx}"   -- delab'd: `List.length

-- ── 18. Name construction: mkIdent / ++ / .mkNum / .anonymous ──────────
#eval toString (`apple ++ `count)                          -- "apple.count"
#eval toString (`basket ++ Name.mkNum .anonymous 3)         -- "basket.3"
#eval toString (mkIdent (.mkSimple "granny_smith"))         -- "`granny_smith"

-- ── 19. `addAndCompile` with a raw `Declaration` (bypasses the parser) ──
#eval show MetaM Unit from do
  Lean.addAndCompile (.defnDecl {
    name := `dozenEggsRaw
    levelParams := []
    type := Expr.const ``Nat []
    value := Lean.mkNatLit 12
    hints := .abbrev
    safety := .safe
  })
#eval dozenEggsRaw   -- 12

-- ── 20. `Lean.Compiler.CSimp.add` ───────────────────────────────────────
def dozenSlow : Nat := Id.run do    -- "recount the eggs one at a time"
  let mut n := 0
  for _ in [:12] do n := n + 1
  return n

def twelve : Nat := 12

-- `by decide` doesn't work here (verified: `Nat`-range `for` loops compile
-- through well-founded recursion, whose reduction gets stuck at the kernel
-- level before reaching `isTrue`/`isFalse`); `by native_decide` instead
-- COMPILES and RUNS the check, sidestepping that reduction issue.
theorem dozenSlow_eq_twelve : dozenSlow = twelve := by native_decide

#eval show MetaM Unit from do
  Lean.Compiler.CSimp.add ``dozenSlow_eq_twelve .global
  IO.println "csimp registered: dozenSlow → twelve"

-- ── 21. The `Deriving.*` infrastructure, applied to a tiny custom class ─
class Yummy (α : Type) where
  yum : α → Bool

inductive Apple where
  | apple

-- Hand-written, not derived from anything -- the point here is just
-- registering it as a real instance via the SAME shared plumbing every
-- `deriving Foo` handler (including stock `deriving BEq`) uses.
def appleYum (_ : Apple) : Bool := true

#eval show CommandElabM Unit from do
  let cmds ← liftTermElabM do
    let instName ← Deriving.mkInstName ``Yummy ``Apple
    let typeInfo ← getConstInfoInduct ``Apple
    let ctx : Deriving.Context :=
      { instName, typeInfos := #[typeInfo], auxFunNames := #[``appleYum], usePartial := false }
    Deriving.mkInstanceCmds ctx ``Yummy #[``Apple] (useAnonCtor := true)
  for c in cmds do elabCommand c

#eval Yummy.yum Apple.apple   -- true

-- ── 22. `deriving Repr, Inhabited` on thetool's OWN data (not spec output) ─
structure GroceryItem where
  name  : String
  price : Nat
deriving Repr, Inhabited

#eval (default : GroceryItem)                          -- { name := "", price := 0 }
#eval ({ name := "apple", price := 2 } : GroceryItem)   -- { name := "apple", price := 2 } (via Repr)
