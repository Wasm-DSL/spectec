/-
  How Extended-derive-deceq derives DecidableEq for `Tree` (the same nested
  type from sandbox_3.lean), step by step, with every claim checked against
  real captured output.

  RUNNING THIS FILE: both this file and ExtendedDeriveDecEq.lean (the package
  it imports) are registered in lakefile.lean's `lean_lib` globs, so the normal
  workflow applies -- `lake build sandbox_5` from test-lean/, or just open it
  in the IDE.

  `set_option trace.DecEqMutual.derive true` below turns on the package's own
  built-in trace point (`trace[DecEqMutual.derive] ...`, called throughout
  ExtendedDeriveDecEq.lean's `deriveForGroup`/`mkDecEqFunc`) -- it prints
  exactly what the tool generated, before elaborating it. Everything under
  "REAL OUTPUT" below is that trace, captured by actually running this file --
  not paraphrased.
-/

import ExtendedDeriveDecEq

set_option trace.DecEqMutual.derive true

inductive Tree where
  | leaf : Nat → Tree
  | node : List Tree → Tree
  deriving BEq

derive_deceq Tree

/-
  ============================================================================
  REAL OUTPUT (captured by running this exact file):
  ============================================================================

  [DecEqMutual.derive] Types: [Tree]
  [DecEqMutual.derive] Motives: 2 (user: 1)
  [DecEqMutual.derive] Params: 0, Insts: 0
  [DecEqMutual.derive]   motive[0] ctor Tree.leaf, nfields=1
  [DecEqMutual.derive]   motive[0] ctor Tree.node, nfields=1
  [DecEqMutual.derive]   motive[1] ctor List.nil, nfields=0
  [DecEqMutual.derive]   motive[1] ctor List.cons, nfields=2
  [DecEqMutual.derive] Generated def:
      def Tree.decEq (a b : Tree) : Decidable (a = b) :=
        match decEq (Tree.ctorIdx a) (Tree.ctorIdx b) with
        | .isTrue h =>
          Tree.match_on_same_ctor a b h
            (@fun f0 g0 =>
              if h : @f0 = @g0 then by subst h; exact isTrue rfl
              else isFalse (by intro heq; injection heq; apply h _; assumption))
            @fun f0 g0 =>
              let inst := Tree._auxDecEq.1 @f0 @g0;
              if h : @f0 = @g0 then by subst h; exact isTrue rfl
              else isFalse (by intro heq; injection heq; apply h _; assumption)
        | .isFalse h => isFalse (fun h' => h (congrArg Tree.ctorIdx h'))
      termination_by structural a
  [DecEqMutual.derive] Generated def:
      def Tree._auxDecEq.1 (a b : List Tree) : Decidable (a = b) :=
        match decEq (List.ctorIdx a) (List.ctorIdx b) with
        | .isTrue h =>
          List.match_on_same_ctor a b h (fun () => isTrue rfl)
            @fun f0 f1 g0 g1 =>
              let inst := Tree.decEq @f0 @g0;
              if h : @f0 = @g0 then by subst h;
                exact
                  let inst := Tree._auxDecEq.1 @f1 @g1;
                  if h : @f1 = @g1 then by subst h; exact isTrue rfl
                  else isFalse (by intro heq; injection heq; apply h _; assumption)
              else isFalse (by intro heq; injection heq; apply h _; assumption)
        | .isFalse h => isFalse (fun h' => h (congrArg List.ctorIdx h'))
      termination_by structural a
  [DecEqMutual.derive] Elaborating mutual block...
  [DecEqMutual.derive] Registering instance:
      instance instDecidableEqTree : DecidableEq (@Tree) := Tree.decEq
  [DecEqMutual.derive] csimp: Tree._auxDecEq.1 → Tree._auxDecEq.1._real

  ============================================================================
  MY EARLIER EXPLANATION, MATCHED SENTENCE BY SENTENCE AGAINST THAT OUTPUT:
  ============================================================================

  "The key trick, stated plainly in its own README: read the recursor, not
  the source syntax."

    -- `Types: [Tree]` / `Motives: 2 (user: 1)`: TWO motives came out of
       analyzing @Tree.rec, even though this file only ever wrote one
       `inductive Tree`. `List Tree` was never declared with its own
       `DecidableEq`-deriving anything -- the second motive was read
       straight off Tree's recursor, not off any source-level declaration.

  "Lean's kernel already correctly builds a full recursor for nested/mutual
  inductive blocks (that's the "mutual" half of #2329, separately fixed in
  #2591) -- and critically, for a nested container field like List Expr, the
  kernel's recursor construction itself generates auxiliary "motives" and
  "minors" for List as part of that recursor."

    -- `motive[1] ctor List.nil, nfields=0` / `motive[1] ctor List.cons,
       nfields=2`: this is that auxiliary motive, printed directly --
       @Tree.rec's own type already contains a minor for `List.nil` and one
       for `List.cons`, exactly as if `List Tree` were a third constructor-
       bearing type in the mutual group.

  "So the auxiliary function the builtin handler was missing is already
  implicitly described, structurally, inside the recursor Lean built for
  you -- you just have to go read it back out."

    -- and indeed a second `Generated def:` appears below for
       `Tree._auxDecEq.1 : (a b : List Tree) → Decidable (a = b)` -- exactly
       the missing "compare two `List Tree`s" function, generated without
       ever writing `inductive List ...` ourselves.

  "analyzeRecursor peels apart the recursor's type signature (params →
  motives → minors → target → result) via repeated forallBoundedTelescope
  calls, and for every motive (one per type in the mutual block, plus one
  per auxiliary container type like List Expr) works out its domain type,
  and for every minor (one per constructor across the whole block) works
  out which motive it belongs to, which constructor it corresponds to, and
  classifies each of its binders as: an induction hypothesis (recursive
  field), a genuine data field, or an index."

    -- `Params: 0, Insts: 0` (Tree has no type parameters, so no param/
       instance binders were needed) plus all four `motive[i] ctor ...,
       nfields=n` lines together ARE this per-motive, per-constructor
       analysis, printed. `motive[0] ctor Tree.node, nfields=1` records
       that `node`'s one field (`List Tree`) is a data field whose
       comparison routes to motive[1] -- visible in the generated body as
       `Tree._auxDecEq.1 @f0 @g0`, not a bare index or a direct `Tree`-typed
       IH.

  "This is the "structure" the type wants but that the source-syntax-based
  builtin handler can't see for auxiliary types, because they don't have a
  Lean-syntax declaration to inspect at all -- they only exist inside the
  recursor."

    -- there is, again, no `inductive`/`deriving` line anywhere above for
       `List Tree`. `deriving DecidableEq` on `Tree` directly (the builtin
       handler) would have nothing to inspect for this case and fails
       exactly as reproduced in sandbox_3.lean; `derive_deceq` doesn't need
       a declaration because it never looks at declarations, only recursors.

  "computeIsRecursive runs a Floyd–Warshall reachability pass over which
  motives call which (via the IH links found in step 1) to know precisely
  which of the generated functions are actually part of a recursive cycle
  -- so termination_by structural only gets attached where truly needed,
  rather than everywhere (which would otherwise produce spurious
  warnings)."

    -- both `Tree.decEq` and `Tree._auxDecEq.1` end in
       `termination_by structural a`: motive[0] (Tree) reaches motive[1]
       (List Tree, via `node`'s field) and motive[1] reaches motive[0] back
       (via `cons`'s head field) and itself (via `cons`'s tail) -- a genuine
       cycle, so both legitimately need the annotation. (Had there been a
       third, non-recursive motive -- say a plain `String` field -- its
       generated function would have no `termination_by` line at all.)

  "mkDecEqFunc generates one comparison function per motive (both user
  types and auxiliary container types) using an O(constructors) construction
  rather than the naive O(constructors²) pairwise match: it uses ctorIdx (a
  value telling you which constructor a term uses) plus casesOnSameCtor (a
  Lean-provided combinator that, given ctorIdx a = ctorIdx b, lets you
  assume both sides use the same constructor and just compare fields
  pairwise) -- so cross-constructor disequality is dispatched in O(1) via
  congrArg ctorIdx, and same-constructor equality is one lambda per
  constructor built by mkSameCtorAlt, which itself builds a chain of
  if h : field_a = field_b then ... else isFalse ... (via mkIfSubstChain),
  substituting each proven-equal field before comparing the next -- this is
  what correctly threads dependent/indexed fields through."

    -- every clause of this sentence is a line in `Tree.decEq`'s body:
         match decEq (Tree.ctorIdx a) (Tree.ctorIdx b) with      -- ctorIdx dispatch
         | .isTrue h =>
           Tree.match_on_same_ctor a b h  (...) (...)            -- casesOnSameCtor
             -- the two `@fun f0 g0 => if h : @f0 = @g0 then ... else isFalse ...`
             -- lambdas are mkSameCtorAlt's output, one per constructor
             -- (leaf, node), each an mkIfSubstChain if/subst/isFalse chain
         | .isFalse h => isFalse (fun h' => h (congrArg Tree.ctorIdx h'))
             -- exactly "cross-constructor disequality... O(1) via congrArg ctorIdx"
       `Tree._auxDecEq.1`'s `cons` case shows the "substituting each proven-
       equal field before comparing the next" part concretely: it first
       `subst`s the proof that the two heads (`f0`/`g0`) are equal, and only
       *then*, inside that `exact`, compares the tails (`f1`/`g1`) -- one
       field at a time, exactly the described chain.

  "All the generated defs (user types and auxiliaries) get wrapped in one
  mutual ... end block and elaborated together via elabCommand, exactly the
  way you'd write a hand-rolled mutual block yourself (this is the same
  pattern I built by hand for Tree/decEqTreeList in your sandbox file)."

    -- "Elaborating mutual block..." fires once, after *both* `Generated
       def:` blocks -- `Tree.decEq` and `Tree._auxDecEq.1` are elaborated
       together, matching that they call each other (`Tree.decEq`'s `node`
       case calls `Tree._auxDecEq.1`; `Tree._auxDecEq.1`'s `cons` case calls
       back into `Tree.decEq`). This is structurally identical to the
       `mutual def decEqTree ... def decEqTreeList ... end` block you wrote
       by hand in sandbox_3.lean Part 4 -- same two functions, same mutual
       recursion, generated instead of hand-written.

  "Deriving.mkInstanceCmds then registers the actual instance : DecidableEq
  Foo := ... for each user type (not the internal auxiliaries) using Lean's
  own standard deriving-infrastructure helper, so the result looks and
  behaves like any other derived instance."

    -- "Registering instance: instance instDecidableEqTree : DecidableEq
       (@Tree) := Tree.decEq" -- exactly one instance registered, for `Tree`
       only. No matching "instance ... : DecidableEq (List Tree)" line
       anywhere -- `Tree._auxDecEq.1` stays an internal helper, never
       promoted to its own typeclass instance, exactly as described.

  "There's also a csimp optimization attempt for the efficiency concern
  raised in PR #3160 (that a naive generated List/Array comparison bypasses
  the standard library's possibly-more-efficient instance): it tries to
  register, for each auxiliary container function, a @[csimp] theorem
  saying "this generated function equals the real inferred instance"
  (proved trivially via Subsingleton.elim, since any two Decidable-proofs
  of the same proposition are equal)."

    -- "csimp: Tree._auxDecEq.1 → Tree._auxDecEq.1._real" is that attempt
       firing, for the one auxiliary (`List Tree`'s comparison) -- there's
       no such line for `Tree.decEq` itself, since csimp optimization only
       targets the auxiliary container functions, not user types.

  "The author is upfront in both the README and the issue comment that this
  doesn't actually work for calls from inside the same mutual block --
  csimp only rewrites downstream call sites, and the only callers of the
  auxiliary functions are inside that same block, compiled before the
  csimp lemma exists."

    -- can't be seen from the trace alone (csimp application happens later,
       at *compile* time for anything that calls `Tree._auxDecEq.1` -- and
       per this sentence, `Tree.decEq`'s own call to it, sitting right
       there in the mutual block above, predates the csimp lemma and so
       never gets rewritten). Consistent with the trace: the mutual block
       is elaborated as one unit before the csimp registration line even
       runs, so by construction nothing inside it could have been rewritten
       by a csimp lemma that doesn't exist yet.

  "So the efficiency gap PR #3160 got stuck on is acknowledged as still
  open here too, not solved."

    -- borne out here too: `Tree.decEq`'s `node` case still calls the
       generated `Tree._auxDecEq.1` directly, not whatever the "real",
       possibly more efficient `DecidableEq (List Tree)` instance would
       have done.
-/

example : Tree.node [Tree.leaf 1, Tree.leaf 2] ≠ Tree.node [Tree.leaf 1, Tree.leaf 3] := by decide
example : Tree.node [Tree.leaf 1, Tree.leaf 2] = Tree.node [Tree.leaf 1, Tree.leaf 2] := by decide
