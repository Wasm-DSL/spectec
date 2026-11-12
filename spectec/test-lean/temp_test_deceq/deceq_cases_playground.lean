/-
  Playground: hand-written `DecidableEq` instances illustrating the 11
  strategies `ExtendedDeriveDecEq.lean` uses, built up step by step.

  Companion to the chat walkthrough of that file. Every section below is
  real, compiling Lean (no `sorry`), with a couple of `#guard`s so you can
  see it actually deciding equality correctly, not just type-checking.
  Comments cite the exact lines in ExtendedDeriveDecEq.lean responsible for
  that piece of strategy, so you can flip back and forth.

  Things to try breaking, to build intuition:
    - Toy.decEqManual: swap `x1 = x2` for `x1 = y2` and see what goes wrong.
    - Tree.decEqManual / ListTree.decEqManual: delete one `termination_by
      structural` and watch Lean fall back to (or fail at) well-founded
      recursion instead.
    - Vec.decEqManual: try writing it as one joint `match a, b with`
      instead of nested matches, and see the index-unification error this
      file's comments describe.
    - Bounded.decEqManual: change `isTrue (by subst hn; rfl)` to try and
      compare `h1`/`h2` explicitly -- there's nothing meaningful to compare.
    - Flip on either `set_option trace...` line below and re-elaborate a
      `derive_deceq` / `deriving DecidableEq` line further down to watch
      the real generator work on these exact shapes.
-/

import ExtendedDeriveDecEq

-- set_option trace.DecEqMutual.derive true      -- ExtendedDeriveDecEq's own trace
-- set_option trace.Elab.Deriving.decEq true     -- Lean core's plain `deriving DecidableEq` trace

/- ═══════════════════════════════════════════════════════════════════════
   Case 1 — too many constructors: the `ctorIdx` shortcut
   Case 2 — comparing fields once you're inside a same-constructor case
   ═══════════════════════════════════════════════════════════════════════ -/

/-- Every inductive type gets `T.ctorIdx : T → Nat` for free (0,1,2,... in
    declaration order) -- see `Lean.Meta.Constructions.CtorIdx`, imported
    at ExtendedDeriveDecEq.lean:44. Comparing tags first, before any field,
    is exactly `mkDecEqFunc`'s dispatch at lines 583-585:
      match decEq (ctorIdx a) (ctorIdx b) with
      | isTrue h  => <same-ctor comparison, via casesOnSameCtor>
      | isFalse h => isFalse (fun h' => h (congrArg ctorIdx h')) -/
inductive Numtype | I32 | I64 | F32 | F64
deriving Repr

/-- Matching `a, b, heq` together (not just `a, b`) lets Lean's equation
    compiler silently discard the N² - N "different constructor" cases on
    its own: once two constructors don't match, `heq`'s type collapses to
    an obviously-uninhabited equality between different Nat literals, and
    the compiler treats that branch as unreachable. Only N cases to write,
    by hand, with vanilla `match` -- no need to invoke `casesOnSameCtor`'s
    own metaprogram to get this. -/
def Numtype.decEqManual (a b : Numtype) : Decidable (a = b) :=
  match decEq a.ctorIdx b.ctorIdx with
  | isFalse hne => isFalse (fun heq => hne (congrArg Numtype.ctorIdx heq))
  | isTrue heq =>
    match a, b, heq with
    | .I32, .I32, _ => isTrue rfl
    | .I64, .I64, _ => isTrue rfl
    | .F32, .F32, _ => isTrue rfl
    | .F64, .F64, _ => isTrue rfl

instance : DecidableEq Numtype := Numtype.decEqManual
#guard decide (Numtype.I32 = Numtype.I32)
#guard !decide (Numtype.I32 = Numtype.I64)

/-- Case 2's field-by-field chain: check a field, `subst` the proof of
    equality into everything downstream, then check the next field. Any
    mismatch closes via `injection` (constructors never collide). This is
    `mkIfSubstChain`, lines 399-411 (base case `isTrue rfl` at 401). -/
inductive Toy | NOP | PAIR (x : Nat) (y : Nat)

def Toy.decEqManual (a b : Toy) : Decidable (a = b) :=
  match decEq a.ctorIdx b.ctorIdx with
  | isFalse hne => isFalse (fun heq => hne (congrArg Toy.ctorIdx heq))
  | isTrue heq =>
    match a, b, heq with
    | .NOP, .NOP, _ => isTrue rfl                          -- 0 fields: mkSameCtorAlt line 436
    | .PAIR x1 y1, .PAIR x2 y2, _ =>
      if hx : x1 = x2 then
        by subst hx
           exact (if hy : y1 = y2 then isTrue (by subst hy; rfl)
                  else isFalse (by intro heq2; injection heq2; contradiction))
      else
        isFalse (by intro heq2; injection heq2; contradiction)

instance : DecidableEq Toy := Toy.decEqManual
#guard decide (Toy.PAIR 1 2 = Toy.PAIR 1 2)
#guard !decide (Toy.PAIR 1 2 = Toy.PAIR 1 3)
#guard !decide (Toy.NOP = Toy.PAIR 1 2)

/- ═══════════════════════════════════════════════════════════════════════
   Case 3 — fields that don't need comparing: "fixed" (indexed) fields
   ═══════════════════════════════════════════════════════════════════════
   Not used by any of wasm2.0.lean's 13 derive_deceq types (none of them
   are indexed families) -- included because the algorithm supports it
   generally. The "fixed vs free" test is `let isFixed :=
   returnType.containsFVar x.fvarId!`, line 452.

   Try it: writing this as ONE joint `match a, b with` (binding the tail
   length as, say, `k1` and `k2` separately) fails with a genuine type
   mismatch -- Lean's pattern-match unifier doesn't automatically solve
   `k1 + 1 =?= k2 + 1` down to `k1 = k2` the way plain term elaboration
   would. Matching `a` first, then `b` against a's now-pinned index (as
   below), sidesteps the issue entirely. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (x : α) (k : Nat) (xs : Vec α k) : Vec α (k + 1)

def Vec.decEqManual [DecidableEq α] : {n : Nat} → (a b : Vec α n) → Decidable (a = b)
  | _, .nil, b =>
    match b with
    | .nil => isTrue rfl
  | _, .cons x1 _k xs1, b =>
    match b with
    | .cons x2 _ xs2 =>
      if hx : x1 = x2 then
        by subst hx
           exact (match Vec.decEqManual xs1 xs2 with
                  | isTrue hxs => isTrue (by subst hxs; rfl)
                  | isFalse hxs => isFalse (by intro heq; injection heq; contradiction))
      else
        isFalse (by intro heq; injection heq; contradiction)
termination_by n _ _ => n

instance [DecidableEq α] : DecidableEq (Vec α n) := Vec.decEqManual
#guard decide (Vec.cons 1 1 (Vec.cons 2 0 Vec.nil) = Vec.cons 1 1 (Vec.cons 2 0 Vec.nil))
#guard !decide (Vec.cons 1 1 (Vec.cons 2 0 Vec.nil) = Vec.cons 1 1 (Vec.cons 3 0 Vec.nil))

/- ═══════════════════════════════════════════════════════════════════════
   Case 4 — recursive fields: using the Induction Hypothesis
   ═══════════════════════════════════════════════════════════════════════
   Direct self-reference (no container in between). The IH is discovered
   by `analyzeRecursor`'s isIH test (line 300) and linked back to its
   field at lines 347-361; the generated code then calls the sibling
   function directly rather than doing a typeclass lookup -- see
   `mkIfSubstChain`'s `let inst := $decEqId @$a @$b`, lines 412-416. -/
inductive Expr | Lit (n : Nat) | Neg (e : Expr) | Add (l : Expr) (r : Expr)

def Expr.decEqManual (a b : Expr) : Decidable (a = b) :=
  match decEq a.ctorIdx b.ctorIdx with
  | isFalse hne => isFalse (fun heq => hne (congrArg Expr.ctorIdx heq))
  | isTrue heq =>
    match a, b, heq with
    | .Lit n1, .Lit n2, _ =>
      if hn : n1 = n2 then isTrue (by subst hn; rfl)
      else isFalse (by intro heq2; injection heq2; contradiction)
    | .Neg e1, .Neg e2, _ =>
      match Expr.decEqManual e1 e2 with              -- direct recursive call, not `if h : e1 = e2`
      | isTrue he => isTrue (by subst he; rfl)
      | isFalse he => isFalse (by intro heq2; injection heq2; contradiction)
    | .Add l1 r1, .Add l2 r2, _ =>
      match Expr.decEqManual l1 l2 with
      | isTrue hl =>
        by subst hl
           exact (match Expr.decEqManual r1 r2 with
                  | isTrue hr => isTrue (by subst hr; rfl)
                  | isFalse hr => isFalse (by intro heq2; injection heq2; contradiction))
      | isFalse hl => isFalse (by intro heq2; injection heq2; contradiction)

instance : DecidableEq Expr := Expr.decEqManual
#guard decide (Expr.Add (.Lit 1) (.Neg (.Lit 2)) = Expr.Add (.Lit 1) (.Neg (.Lit 2)))
#guard !decide (Expr.Add (.Lit 1) (.Neg (.Lit 2)) = Expr.Add (.Lit 1) (.Neg (.Lit 3)))

/- ═══════════════════════════════════════════════════════════════════════
   Case 5 — self-recursion *through* a container: hidden motive + `mutual`
   ═══════════════════════════════════════════════════════════════════════
   `Tree.rec` secretly has a second motive for `List Tree`, folded in by
   Lean itself when it elaborates `inductive Tree`. `Tree.decEqManual` and
   `ListTree.decEqManual` need each other, so both must live in one
   `mutual` block (deriveForGroup builds exactly this: 626-634, elaborated
   as one unit at 638). Try deleting either `termination_by structural`
   line -- this is the same failure mode as the Tree/`.map` experiment
   from the chat: direct pattern-matched recursion needs it spelled out
   once the shape gets nested like this. -/
inductive Tree | leaf | node (children : List Tree)

mutual
  def Tree.decEqManual (a b : Tree) : Decidable (a = b) :=
    match decEq a.ctorIdx b.ctorIdx with
    | isFalse hne => isFalse (fun heq => hne (congrArg Tree.ctorIdx heq))
    | isTrue heq =>
      match a, b, heq with
      | .leaf, .leaf, _ => isTrue rfl
      | .node cs1, .node cs2, _ =>
        match ListTree.decEqManual cs1 cs2 with
        | isTrue hcs => isTrue (by subst hcs; rfl)
        | isFalse hcs => isFalse (by intro heq2; injection heq2; contradiction)
  termination_by structural a

  def ListTree.decEqManual (a b : List Tree) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; injection h)
    | _ :: _, [] => isFalse (by intro h; injection h)
    | t1 :: ts1, t2 :: ts2 =>
      match Tree.decEqManual t1 t2 with               -- recurses into motive₀ (Tree)
      | isTrue ht =>
        by subst ht
           exact (match ListTree.decEqManual ts1 ts2 with   -- recurses into motive₁ (itself)
                  | isTrue hts => isTrue (by subst hts; rfl)
                  | isFalse hts => isFalse (by intro heq2; injection heq2; contradiction))
      | isFalse ht => isFalse (by intro heq2; injection heq2; contradiction)
  termination_by structural a
end

instance : DecidableEq Tree := Tree.decEqManual
#guard decide (Tree.node [Tree.leaf, Tree.node [Tree.leaf]] = Tree.node [Tree.leaf, Tree.node [Tree.leaf]])
#guard !decide (Tree.node [Tree.leaf] = Tree.node [Tree.leaf, Tree.leaf])

/- ═══════════════════════════════════════════════════════════════════════
   Case 6 — mutual recursion between *different* user types
   ═══════════════════════════════════════════════════════════════════════
   No two of wasm2.0.lean's 13 target types are mutually defined this way
   -- included for completeness. `indVal.all` (line 134) is what makes
   `analyzeRecursor` discover *both* A and B as user types in one pass. -/
mutual
  inductive A | mk (b : B)
  inductive B | mk (a : Option A)
end

mutual
  def A.decEqManual (a b : A) : Decidable (a = b) :=
    match a, b with
    | .mk b1, .mk b2 =>
      match B.decEqManual b1 b2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; injection heq; contradiction)
  termination_by structural a

  def B.decEqManual (a b : B) : Decidable (a = b) :=
    match a, b with
    | .mk oa1, .mk oa2 =>
      match OptionA.decEqManual oa1 oa2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; injection heq; contradiction)
  termination_by structural a

  def OptionA.decEqManual (a b : Option A) : Decidable (a = b) :=
    match a, b with
    | none, none => isTrue rfl
    | none, some _ => isFalse (by intro h; injection h)
    | some _, none => isFalse (by intro h; injection h)
    | some a1, some a2 =>
      match A.decEqManual a1 a2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; injection heq; contradiction)
  termination_by structural a
end

instance : DecidableEq A := A.decEqManual
instance : DecidableEq B := B.decEqManual
#guard decide (A.mk (B.mk none) = A.mk (B.mk none))
#guard !decide (A.mk (B.mk none) = A.mk (B.mk (some (A.mk (B.mk none)))))

/- ═══════════════════════════════════════════════════════════════════════
   Case 7 — type parameters needing `[DecidableEq α]`
   ═══════════════════════════════════════════════════════════════════════
   None of the 13 target types are generic -- included for completeness.
   The probe "can I even ask for DecidableEq of this parameter" is lines
   177-182 (`mkAppM \`\`DecidableEq #[v]; isTypeCorrect`); the resulting
   `[DecidableEq α]` binder threads through every generated def via
   `analysis.instBinderStxs`, folded into `allBinderStxs` at line 525. -/
inductive GTree (α : Type) | leaf (v : α) | node (children : List (GTree α))

mutual
  def GTree.decEqManual [DecidableEq α] (a b : GTree α) : Decidable (a = b) :=
    match decEq a.ctorIdx b.ctorIdx with
    | isFalse hne => isFalse (fun heq => hne (congrArg GTree.ctorIdx heq))
    | isTrue heq =>
      match a, b, heq with
      | .leaf v1, .leaf v2, _ =>
        if hv : v1 = v2 then isTrue (by subst hv; rfl)
        else isFalse (by intro heq2; injection heq2; contradiction)
      | .node cs1, .node cs2, _ =>
        match ListGTree.decEqManual cs1 cs2 with
        | isTrue hcs => isTrue (by subst hcs; rfl)
        | isFalse hcs => isFalse (by intro heq2; injection heq2; contradiction)
  termination_by structural a

  def ListGTree.decEqManual [DecidableEq α] (a b : List (GTree α)) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; injection h)
    | _ :: _, [] => isFalse (by intro h; injection h)
    | t1 :: ts1, t2 :: ts2 =>
      match GTree.decEqManual t1 t2 with
      | isTrue ht =>
        by subst ht
           exact (match ListGTree.decEqManual ts1 ts2 with
                  | isTrue hts => isTrue (by subst hts; rfl)
                  | isFalse hts => isFalse (by intro heq2; injection heq2; contradiction))
      | isFalse ht => isFalse (by intro heq2; injection heq2; contradiction)
  termination_by structural a
end

instance [DecidableEq α] : DecidableEq (GTree α) := GTree.decEqManual
#guard decide (GTree.node [GTree.leaf (1 : Nat), GTree.leaf 2] = GTree.node [GTree.leaf 1, GTree.leaf 2])
#guard !decide (GTree.node [GTree.leaf (1 : Nat)] = GTree.node [GTree.leaf 2])

/- ═══════════════════════════════════════════════════════════════════════
   Case 8 — fields that are proofs, not data
   ═══════════════════════════════════════════════════════════════════════
   None of the 13 target types embed a Prop-typed field -- included for
   completeness. The flag is `Meta.isProp fieldTypes[i]!`, line 366; the
   "no branching, just rfl" handling is lines 404-405 in mkIfSubstChain. -/
inductive Bounded | mk (n : Nat) (h : n < 100)

def Bounded.decEqManual (a b : Bounded) : Decidable (a = b) :=
  match a, b with
  | .mk n1 h1, .mk n2 h2 =>
    if hn : n1 = n2 then
      isTrue (by subst hn; rfl)   -- h1, h2 never compared: proof irrelevance
    else
      isFalse (by intro heq; injection heq; contradiction)

instance : DecidableEq Bounded := Bounded.decEqManual
-- two DIFFERENT proof terms for the same fact -- still equal:
#guard decide (Bounded.mk 5 (by omega) = Bounded.mk 5 (by decide))

/- ═══════════════════════════════════════════════════════════════════════
   Case 9 — degenerate whole-type shortcuts
   ═══════════════════════════════════════════════════════════════════════ -/

-- (9a) zero constructors -- lines 529-536 (`nomatch $aId`)
inductive Void2
def Void2.decEqManual (_a _b : Void2) : Decidable (_a = _b) := nomatch _a

-- (9b) a Prop, not a Type -- lines 540-547 (`isTrue rfl`, checked BEFORE
-- looking at constructors at all)
inductive IsPositive : Nat → Prop | mk (n : Nat) (h : n > 0) : IsPositive n
def IsPositive.decEqManual {n : Nat} (a b : IsPositive n) : Decidable (a = b) := isTrue rfl

-- (9c) exactly one constructor -- `state`/`config` in wasm2.0.lean are
-- shaped like this for real. No ctorIdx call anywhere: line 559 passes a
-- literal `rfl` in place of the tag-match proof.
inductive Pair2 | mk (a : Nat) (b : Nat)
def Pair2.decEqManual (a b : Pair2) : Decidable (a = b) :=
  match a, b with
  | .mk a1 b1, .mk a2 b2 =>
    if ha : a1 = a2 then
      by subst ha
         exact (if hb : b1 = b2 then isTrue (by subst hb; rfl)
                else isFalse (by intro heq; injection heq; contradiction))
    else
      isFalse (by intro heq; injection heq; contradiction)

instance : DecidableEq Pair2 := Pair2.decEqManual
#guard decide (Pair2.mk 1 2 = Pair2.mk 1 2)
#guard !decide (Pair2.mk 1 2 = Pair2.mk 1 3)

/- ═══════════════════════════════════════════════════════════════════════
   Case 10 — the csimp cleanup pass
   ═══════════════════════════════════════════════════════════════════════
   Swap `ListTree.decEqManual` for the standard library's own
   `List`-DecidableEq at *compile* time (never touches the kernel-checked
   proof). `csimp` only accepts "bare constant = bare constant" (that's
   what fails if you try to write `@f = @(g applied-to-stuff)` directly),
   which is exactly why the real file's csimp section first binds the
   found instance to its own fresh name (`_real`, lines 674-699) before
   proving the two constants equal via `Subsingleton.elim` (line 706) and
   registering the swap (`Compiler.CSimp.add`, line 718). -/
def ListTree_real : (a b : List Tree) → Decidable (a = b) := instDecidableEqList

theorem ListTree_decEqManual_eq_real : @ListTree.decEqManual = @ListTree_real :=
  funext fun _ => funext fun _ => Subsingleton.elim _ _

attribute [csimp] ListTree_decEqManual_eq_real

-- now actually runs via the stdlib's List comparison, not ListTree.decEqManual:
#eval decide (Tree.node [Tree.leaf] = Tree.node [Tree.leaf])

/- ═══════════════════════════════════════════════════════════════════════
   Case 11 — only the user's types get a public instance
   ═══════════════════════════════════════════════════════════════════════
   The registration loop only ranges over `[:analysis.numUserTypes]`
   (line 643) -- for Tree that's just index 0 (Tree itself), never the
   hidden List-Tree motive at index 1. Contrast with the csimp loop right
   after it, which *does* range over the auxiliaries: `[numUserTypes:
   numMotives]`, line 675. -/
example : DecidableEq Tree := inferInstance   -- fine: instTree registered above
example : DecidableEq A := inferInstance       -- fine: numUserTypes = 2 for the A/B group
-- `ListTree.decEqManual` itself was never registered as a `DecidableEq
-- (List Tree)` instance -- only `List`'s own generic instance is, which
-- is a different (if, post-Case-10, computationally identical) thing.

/- ═══════════════════════════════════════════════════════════════════════
   Bonus — watch the real generator do this on the exact same shapes
   ═══════════════════════════════════════════════════════════════════════
   Uncomment a `set_option trace...` line near the top of this file, then
   re-elaborate (save the file / re-run `lake env lean` on it) to see the
   actual generated `mutual` block for each of these. -/

inductive TinyEnum | Red | Green | Blue
deriving Inhabited, BEq, DecidableEq    -- plain `deriving` already works: no self-recursion

inductive TinyTree | leaf | node (children : List TinyTree)
deriving Inhabited, BEq
-- deriving DecidableEq                 -- uncomment: fails outright, exactly like `SmallInstr` did
derive_deceq TinyTree                   -- this is the one that actually has to work
example : DecidableEq TinyTree := inferInstance
