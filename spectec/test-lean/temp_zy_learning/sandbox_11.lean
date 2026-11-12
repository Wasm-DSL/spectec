/-
  sandbox_11.lean -- a worked reference for the "nested inductive datatypes
  cannot have indices" Lean kernel restriction that spectec's Lean backend
  works around by generating a non-inductive `def Forall`/`Forall₂`/... (see
  backend.ml's comment above `create_iter_prem`, citing these two threads):

    - Wasm-DSL/spectec PR #192 (the Lean backend's own author's working
      notes), which hit this via a real generated relation:
        `Forall (fun comptype' => Comptype_sub C v_comptype comptype') comptype'_lst`
      inside a `mutual` block containing `Subtype_ok2`/`Comptype_sub`.

    - leanprover/lean4#1964, "Nested inductives cannot have indices" -- the
      underlying kernel issue PR #192 links to, with its own minimal repro
      using `Prod` (`×`) instead of `Forall`:
        succeeds: Foo1 : Nat -> Nat -> Type | bar1 : forall a b, (Foo1 a b × Foo1 a b) -> Foo1 a b
        fails:    Foo2 : Nat -> Nat -> Type | bar2 : forall a b c, (Foo2 a c × Foo2 b c) -> Foo2 a c

  Both examples wrap a currently-being-elaborated (mutual/self-recursive)
  type inside ANOTHER, already-defined inductive type (`Forall`, `Prod`).
  Reading the two side by side raised the question this file answers: what,
  exactly, is common to `Forall`/`List` and `Prod`/`Box` that makes this
  fail, what's different between them, and does a plain DIRECT (unwrapped)
  reference to a mutual sibling have the same problem at all?

  THE THREE FACTORS THAT TURNED OUT TO MATTER (rows below), CROSSED WITH
  THREE FAMILIES OF "does the recursive/mutual type appear wrapped inside
  something else" (columns below):

  ┌────────────────────────────────┬──────────────┬────────────────┬────────────────┐
  │                                 │ Direct        │ Forall / List   │ Prod / Box      │
  │                                 │ (no wrapper)  │ (walks a        │ (fixed, small,  │
  │                                 │               │  variable-      │  statically-    │
  │                                 │               │  length list)   │  known # slots) │
  ├────────────────────────────────┼──────────────┼────────────────┼────────────────┤
  │ 1. Nested type NOT part of the │ safe          │ safe            │ safe            │
  │    same simultaneous/mutual    │ (moot --      │ (pull the       │ (pull the       │
  │    elaboration (declared and   │ always safe   │ sibling out of  │ sibling out of  │
  │    finished beforehand)        │ regardless)   │ the `mutual`    │ the `mutual`    │
  │                                 │               │ block)          │ block)          │
  ├────────────────────────────────┼──────────────┼────────────────┼────────────────┤
  │ 2. IS part of the same mutual  │ safe          │ FAILS           │ FAILS           │
  │    elaboration, AND captures a │ (direct       │ (predicate      │ (the value      │
  │    variable from outside its   │ recursion     │ closes over a   │ plugged in      │
  │    own local scope             │ never cares)  │ variable beyond │ depends on a    │
  │                                 │               │ its own loop    │ local variable, │
  │                                 │               │ parameter)      │ full stop)      │
  ├────────────────────────────────┼──────────────┼────────────────┼────────────────┤
  │ 3. IS part of the same mutual  │ safe          │ safe            │ FAILS           │
  │    elaboration, AND uses the   │ (direct       │ (Forall/List    │ (must exactly   │
  │    constructor's own params in │ recursion     │ never looks at  │ reproduce the   │
  │    the "wrong order" (doesn't  │ never cares)  │ the enclosing   │ conclusion,     │
  │    match the conclusion)       │               │ conclusion at   │ order included) │
  │                                 │               │ all)            │                 │
  └────────────────────────────────┴──────────────┴────────────────┴────────────────┘

  Row 1 is the shared PREREQUISITE for rows 2 and 3 to even be reachable --
  for both Forall/List and Prod/Box, none of this ever triggers unless the
  wrapped type is still "in progress" (self-recursive, or a `mutual`
  sibling) at the point of wrapping.

  Rows 2 and 3 are NOT the same condition wearing two hats: Forall/List
  cares ONLY about row 2 (captured variables), never row 3 (order/
  conclusion-matching is simply not a concept it applies -- confirmed below
  by giving the enclosing type its OWN, totally unrelated conclusion index
  and watching Lean not care). Prod/Box cares ONLY about row 3 -- self-
  nesting (Foo1..Foo5-style) doesn't even have a "captured variable" failure
  mode distinct from row 3, since there's no lambda/closure involved at all,
  only a same-scope mismatch against the conclusion; row 2's Prod/Box cell
  below instead uses a DIFFERENT, sibling-nesting shape (a genuinely
  separate mutual type wrapped in `Box`) to demonstrate that ANY local
  variable at all is unsafe there, order notwithstanding.

  Every example below is a complete, standalone, minimally-sized unit
  (its own `namespace ... end` so nothing leaks across cells), tagged with
  its exact observed result. Run with:
    lake env lean sandbox_11.lean
  from this directory. Every "fails" example is INTENTIONAL -- this file is
  a reference of known successes and failures, not something meant to
  compile clean end to end. Lean processes top-level commands independently,
  so one namespace failing doesn't stop the rest of the file from being
  checked and reported.
-/

/- Shared helpers, used across multiple cells below (this mirrors how
   spectec's actual codegen has exactly ONE global `Forall`/`Forall₂`/...
   used by every relation, rather than one per use site). -/

inductive Forall {α : Type} (P : α → Prop) : List α → Prop where
  | nil  : Forall P []
  | cons {x : α} {xs : List α} : P x → Forall P xs → Forall P (x :: xs)

inductive Box (p : Prop) : Prop where
  | mk : p → Box p

/- ══════════════════════════════════════════════════════════════════════
   ROW 1 -- nested type NOT part of the same mutual elaboration.
   Prerequisite check: with this row satisfied, nothing else in rows 2/3
   can bite, no matter how "dangerous" the values plugged in look.
   ══════════════════════════════════════════════════════════════════════ -/

namespace Row1_Direct
-- Not even a meaningful test on its own (direct recursion never fails
-- regardless of row 1), included only so the grid has all nine cells.
inductive B : Nat → Nat → Prop where
  | zero (q : Nat) : B 0 q
  | succ (p q : Nat) : B p q → B (p + 1) q

inductive A : Prop where
  | mk (c : Nat) : B 0 c → B 1 c → A   -- succeeds: B is a plain, ordinary,
                                         -- already-known type from A's POV
end Row1_Direct

namespace Row1_ForallList
-- `B` genuinely has indices (two non-uniformly-instantiated constructors,
-- like Comptype_sub having one rule per subtyping case) and the predicate
-- captures `c` from A's own argument list -- the row-2 "dangerous" shape --
-- but `B` is declared to completion BEFORE `A`, no `mutual` connecting them.
inductive B : Nat → Nat → Prop where
  | zero (q : Nat) : B 0 q
  | succ (p q : Nat) : B p q → B (p + 1) q

inductive A : Prop where
  | mk (c : Nat) (xs : List Nat) : Forall (fun n => B n c) xs → A
  -- succeeds: this is the EXACT shape that fails in Row2_ForallList below,
  -- differing only in whether `B`/`A` share a `mutual` block.
end Row1_ForallList

namespace Row1_ProdBox
-- Same idea via `Box`: `B` finished-and-compiled before `A`, capturing `c`
-- inside `Box` is harmless once `B` isn't "still in progress."
inductive B : Nat → Nat → Prop where
  | zero (q : Nat) : B 0 q
  | succ (p q : Nat) : B p q → B (p + 1) q

inductive A : Prop where
  | mk (c : Nat) : Box (B 0 c) → A   -- succeeds
end Row1_ProdBox

/- ══════════════════════════════════════════════════════════════════════
   ROW 2 -- same mutual elaboration, captures a variable from outside its
   own local scope (outside the predicate lambda, for Forall/List; or, for
   Prod/Box, a genuinely different sibling type applied to any local var
   at all -- self-nesting has no analogous cell, see the note above).
   ══════════════════════════════════════════════════════════════════════ -/

namespace Row2_Direct
mutual
  inductive A : Prop where
    | mk (c : Nat) : B 0 c → A   -- uses `c` freely, no container at all

  inductive B : Nat → Nat → Prop where
    | zero (q : Nat) : B 0 q
    | succ (p q : Nat) : B p q → B (p + 1) q
end
-- succeeds: direct recursive/mutual arguments never care what values they
-- get applied to, captured or not -- this is the ordinary shape behind
-- ordinary rules like transitivity (`R a b -> R b c -> R a c`).
end Row2_Direct

namespace Row2_ForallList
mutual
  inductive A : Prop where
    | mk (c : Nat) (xs : List Nat) : Forall (fun n => B n c) xs → A
    -- `n` is the loop's own bound element (safe on its own); `c` is NOT --
    -- it's bound in A.mk's own argument list, outside this lambda.

  inductive B : Nat → Nat → Prop where
    | zero (q : Nat) : B 0 q
    | succ (p q : Nat) : B p q → B (p + 1) q
end
-- fails: (kernel) invalid nested inductive datatype 'Forall', nested
-- inductive datatypes parameters cannot contain local variables.
--
-- This is the PR #192 shape exactly: `Comptype_sub C v_comptype comptype'`
-- inside `Forall`, where `C`/`v_comptype` play the role of `c` here --
-- fixed once per Subtype_ok2 rule instance, then threaded into every
-- application inside the `Forall`, alongside the one thing that's actually
-- being walked (`comptype'`, playing the role of `n`).
end Row2_ForallList

namespace Row2_ProdBox
mutual
  inductive A : Prop where
    | mk (c : Nat) : Box (B 0 c) → A   -- captures `c`, no lambda involved
                                         -- at all -- Box wraps the
                                         -- application directly

  inductive B : Nat → Nat → Prop where
    | zero (q : Nat) : B 0 q
    | succ (p q : Nat) : B p q → B (p + 1) q
end
-- fails: (kernel) invalid nested inductive datatype 'Box', nested
-- inductive datatypes parameters cannot contain local variables.
--
-- Same error family as Row2_ForallList, via a completely different (no
-- lambda, no loop) route -- confirms this isn't specifically about closures
-- capturing variables; it's about local variables reaching a nested
-- occurrence's argument slots by ANY route, while that occurrence's own
-- type is still mid-elaboration.
end Row2_ProdBox

/- ══════════════════════════════════════════════════════════════════════
   ROW 3 -- same mutual elaboration, uses the constructor's own parameters
   in the "wrong order" / doesn't exactly reproduce the conclusion.
   ══════════════════════════════════════════════════════════════════════ -/

namespace Row3_Direct
mutual
  inductive A : Prop where
    | mk (c : Nat) : B 0 c → B 1 c → A
    -- two DIRECT hypotheses, deliberately using DIFFERENT first arguments
    -- (0 vs 1) -- as "mismatched" as it gets, still no container involved.

  inductive B : Nat → Nat → Prop where
    | zero (q : Nat) : B 0 q
    | succ (p q : Nat) : B p q → B (p + 1) q
end
-- succeeds: exactly the shape ordinary chaining/transitivity rules rely on.
end Row3_Direct

namespace Row3_ForallList
mutual
  inductive A : Nat → Prop where
    | mk (m : Nat) (xs : List Nat) : Forall (fun n => B n n) xs → A (m + 1)
    -- A's OWN conclusion uses `m`; the Forall-predicate uses `n`, which has
    -- nothing whatsoever to do with `m`, or with `A`'s conclusion `A (m+1)`.

  inductive B : Nat → Nat → Prop where
    | zero (q : Nat) : B 0 q
    | succ (p q : Nat) : B p q → B (p + 1) q
end
-- succeeds: Forall/List never looks at the enclosing conclusion at all --
-- the ONLY question it ever asks is "does the predicate stay inside its
-- own loop-bound element," a question with no notion of "order" to violate.
end Row3_ForallList

namespace Row3_ProdBox
-- This is leanprover/lean4#1964's own minimal pair, verbatim (the one PR
-- #192 links to as the root cause) -- self-nesting via `×` (`Prod`),
-- rather than a two-type mutual pair, but the exact same underlying
-- restriction, now demonstrably the SAME issue as Row2_ProdBox above.

inductive Foo1 : Nat → Nat → Type where
  | bar1 : ∀ (a b : Nat), (Foo1 a b × Foo1 a b) → Foo1 a b
  -- succeeds: BOTH nested copies equal `Foo1 a b`, matching each other AND
  -- the conclusion `Foo1 a b` exactly -- order included.

inductive Foo2 : Nat → Nat → Type where
  | bar2 : ∀ (a b c : Nat), (Foo2 a c × Foo2 b c) → Foo2 a c
  -- fails: (kernel) invalid nested inductive datatype 'Prod', nested
  -- inductive datatypes parameters cannot contain local variables.
  --
  -- The two nested copies (`Foo2 a c`, `Foo2 b c`) disagree with EACH
  -- OTHER (a vs b in the first slot) -- and even fixing just one of them to
  -- literally match the conclusion isn't enough, per Foo5 below: what's
  -- actually required is that EVERY nested occurrence, independently,
  -- reproduces the conclusion `Foo2 a c` exactly.

inductive Foo5 : Nat → Nat → Type where
  | bar5 : ∀ (a b : Nat), (Foo5 b a × Foo5 b a) → Foo5 a b
  -- fails, for the same reason, despite the two nested copies agreeing
  -- with EACH OTHER (both `Foo5 b a`): neither one matches the conclusion
  -- `Foo5 a b` -- the arguments are swapped. Proves self-consistency between
  -- multiple nested copies isn't the rule; matching the conclusion is.
end Row3_ProdBox
