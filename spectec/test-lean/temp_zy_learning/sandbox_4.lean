/-
  What `deriving BEq` actually runs, walked through on a toy type.

  Source: Lean.Elab.Deriving.BEq, at
    ~/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Elab/Deriving/BEq.lean
  (open that file locally to follow along -- every function named below lives there.)

  `trace.Elab.Deriving.beq`, turned on below, is the handler's OWN built-in trace
  point (BEq.lean:211/220, `trace[Elab.Deriving.beq] "\n{cmds}"`) -- it prints
  exactly the `mutual ... end` + `instance ...` commands the handler generated,
  right before elaborating them. This is not something we're bolting on; it's
  the mechanism's own self-report. Hover/click into the `#eval`-less block below,
  or run this file (e.g. `lake env lean sandbox_4.lean` from test-lean/), and
  look at the Lean output / Info view for the trace message.
-/

set_option trace.Elab.Deriving.beq true

inductive Expr where
  | lit : Nat → Expr
  | neg : Expr → Expr
  | add : Expr → Expr → Expr
  deriving BEq

/-
  STEP BY STEP, matching BEq.lean's own functions:

  1. `mkBEqInstanceHandler` (BEq.lean:237) is the function registered against the
     class name `BEq` (BEq.lean:246, `registerDerivingHandler `BEq
     mkBEqInstanceHandler`). Lean calls it because `deriving BEq` names that
     class. It just checks `Expr` is actually an inductive, then calls
     `mkBEqInstance`.

  2. `mkContext ``BEq "beq" ``Expr` (BEq.lean:227) inspects `Expr` via
     `getConstInfoInduct` and computes:
       - `instName := instBEqExpr`        (the eventual `instance` name)
       - `auxFunNames := [instBEqExpr.beq]`  (name of the Bool-valued function
         that does the actual work -- one name per type in the group; `Expr`
         is alone, so just one)
       - `usePartial := indVal.isNested || typeInfos.size > 1 || ...`
         For `Expr`, `isNested = false` (no field wraps `Expr` in a container)
         and there's only one type in the block, so `usePartial = false`
         -- this is the flag that decides `def` vs `partial def` below.

  3. `mkBEqHeader` -> `mkHeader `BEq 2 indVal` (Util.lean:175) builds the
     function's own signature: 2 target binders, arity 2, since BEq compares a
     PAIR of values -- `(x✝ : Expr) (x✝¹ : Expr)`.

  4. `mkMatch` (BEq.lean:179) picks `mkMatchOld` here (3 constructors is far
     below `deriving.beq.linear_construction_threshold` = 10, the point where
     it would switch to the `ctorIdx`+`casesOnSameCtor` strategy instead --
     the same strategy the `Extended-derive-deceq` package used for
     `DecidableEq`). `mkMatchOld` (BEq.lean:33) builds one match alternative
     per constructor, via `mkAlts`:
       - `lit` has one field, `Nat`, which is NOT `Expr` itself -> emits
         `a == b` (relies on Nat's own, already-existing `BEq` instance).
       - `neg` has one field OF TYPE `Expr` itself -> emits a RECURSIVE call
         to the very function being defined: `instBEqExpr.beq a b`.
       - `add` has two `Expr` fields -> two recursive calls, `&&`-combined.
       - after all constructors, `mkElseAlt` (BEq.lean:38) appends the
         catch-all `| _, _ => false` for the "different constructors" case.

  5. `mkAuxFunction` (BEq.lean:186) wraps that match in
     `def instBEqExpr.beq (x✝ : Expr) (x✝¹ : Expr) : Bool := <the match>`
     (plain `def`, since `usePartial = false`).

  6. `mkMutualBlock` (BEq.lean:200) wraps it in `mutual ... end` (a mutual
     block of size 1 here, since `Expr` isn't part of a user `mutual` group --
     the machinery always uses `mutual` uniformly, whether there's 1 type or many).

  7. `mkBEqInstanceCmds` (BEq.lean:209) appends the actual
     `instance instBEqExpr : BEq Expr := ⟨instBEqExpr.beq⟩`, tying the Bool
     function to the typeclass.

  8. `mkBEqInstance` (BEq.lean:225) elaborates all of that (`cmds.forM
     elabCommand`) -- i.e. runs it exactly as if you'd typed it yourself,
     right where `deriving BEq` appeared.

  VERIFY: with tracing on above, Lean prints the exact generated code. It reads:

    mutual
      set_option match.ignoreUnusedAlts✝ true
      def instBEqExpr.beq (x✝ : @Expr✝) (x✝¹ : @Expr✝) : Bool✝ :=
        match x✝, x✝¹ with
        | @Expr.lit a✝, @Expr.lit b✝ => a✝ == b✝
        | @Expr.neg a✝¹, @Expr.neg b✝¹ => instBEqExpr.beq a✝¹ b✝¹
        | @Expr.add a✝² a✝³, @Expr.add b✝² b✝³ =>
            instBEqExpr.beq a✝² b✝² && instBEqExpr.beq a✝³ b✝³
        | _, _ => false✝
    end,
    instance instBEqExpr : BEq✝ (@Expr✝) :=
      ⟨instBEqExpr.beq⟩

  matching steps 4-7 above field for field: `lit` uses `==` on its Nat field,
  `neg`/`add` recurse via `instBEqExpr.beq`, and there's the `_, _ => false`
  catch-all. (The `✝`s are Lean printing hygienic/inaccessible names; ignore them.)
-/

#eval Expr.add (Expr.lit 1) (Expr.neg (Expr.lit 2)) == Expr.add (Expr.lit 1) (Expr.neg (Expr.lit 2))  -- true
#eval Expr.add (Expr.lit 1) (Expr.lit 2) == Expr.lit 1                                                -- false


/-
  Now the NESTED case, to see `usePartial` actually flip to `true`.
  `ExprN.list : List ExprN → ExprN` wraps `ExprN` in `List` -- this is exactly
  `indVal.isNested`.
-/

inductive ExprN where
  | lit : Nat → ExprN
  | list : List ExprN → ExprN
  deriving BEq

/-
  VERIFY: the traced output this time is

    mutual
      set_option match.ignoreUnusedAlts✝ true
      partial def instBEqExprN.beq (x✝ : @ExprN✝) (x✝¹ : @ExprN✝) : Bool✝ :=
        let localinst✝ : BEq✝ (@ExprN✝) := ⟨instBEqExprN.beq⟩;
        match x✝, x✝¹ with
        | @ExprN.lit a✝, @ExprN.lit b✝ => a✝ == b✝
        | @ExprN.list a✝¹, @ExprN.list b✝¹ => a✝¹ == b✝¹
        | _, _ => false✝
    end,
    instance instBEqExprN : BEq✝ (@ExprN✝) :=
      ⟨instBEqExprN.beq⟩

  Two differences from `Expr`, both explained by `usePartial = true`:

  - `partial def` instead of `def`: the `list` field's type is `List ExprN`,
    not `ExprN` itself, so `mkMatchOld` does NOT emit a direct recursive call
    -- it falls into the generic "unrelated type, use its own `==`" branch,
    emitting plain `a✝¹ == b✝¹`. That `==` resolves to `List`'s own generic
    `BEq` instance, which internally recurses element-by-element back into
    `BEq ExprN` -- a call Lean's structural-recursion checker can't see
    through `List`'s opaque instance to verify as decreasing. `partial`
    is what lets the definition go through without that termination proof.

  - the extra `let localinst✝ : BEq ExprN := ⟨instBEqExprN.beq⟩` line: since
    the instance for `ExprN` isn't registered globally until AFTER this
    `def` finishes elaborating, but the body needs a `BEq ExprN` instance
    available *right now* (for `List`'s generic instance to recurse into),
    the handler locally/temporarily binds the function being defined as its
    own instance -- self-referential, and only sound because `partial`
    already gave up on a termination guarantee.

  This is the exact mechanism behind everything discussed earlier: `BEq`
  quietly falls back to `partial` for nested types, while `DecidableEq`'s
  handler has no analogous fallback (a `partial` `Decidable` wouldn't make
  sense -- you can't have an unproven "proof"), so it just refuses outright,
  which is the error you already saw:
  `None of the deriving handlers for class 'DecidableEq' applied to 'Tree2'`.
-/

#eval ExprN.list [ExprN.lit 1, ExprN.lit 2] == ExprN.list [ExprN.lit 1, ExprN.lit 2]  -- true
#eval ExprN.list [ExprN.lit 1] == ExprN.lit 1                                        -- false
