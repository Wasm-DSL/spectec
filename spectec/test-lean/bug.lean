/-
BUG REPORT: `induction ... using Foo.rec` fails with `introN failed: no additional
binders or `let` bindings in the goal to introduce` when two *different* types in
the same `mutual` block happen to declare a constructor with the same short name.

Toolchain tested: leanprover/lean4:v4.32.0 (also present in v4.30.0-rc2).

## Symptom

Running the example below produces:

```
error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

case frame
n : Nat
h : A n
⊢ ∀ (n : Nat), B n → True → True
```

even though the printed goal is a perfectly well-formed Pi-type with exactly as
many binders as `introN` should be asking for.

## Root cause

In `Lean/Elab/Tactic/Induction.lean`, `evalAlts`'s loop over "remaining"
(not explicitly named via `case ... =>`) alternatives reads:

```lean
for { name := altName, info, mvarId := altMVarId } in alts do
  let numFields ← getAltNumFields elimInfo altName    -- (a)
  let mut (_, altMVarId) ← altMVarId.introN numFields
  ...
```

`info` is already destructured from the very same loop binding and carries the
*correct*, positionally-assigned `ElimAltInfo.numFields` for this exact
alternative (set once, per-position, in `mkElimApp`). But line (a) discards
`info.numFields` and instead calls:

```lean
def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError "Unknown alternative name `{altName}`"
```

`elimInfo.altsInfo` is built by walking *every* constructor of *every* type in
the mutual block, keyed only by short constructor name — with no
qualification for which type in the group it belongs to. When two types in
the same `mutual` block each have a constructor called `frame` (as happens
for `Instr_ok2.frame` and `Instrs_ok2.frame` in this project's
`typing_lemmas.lean`/`wasm2.0.lean`), this linear search silently returns the
*first* match by declaration order, regardless of which alternative is
actually being processed.

Concretely, in this project:
  - `Instr_ok2.frame`  (the `FRAME_` administrative-instruction case) has **14** fields.
  - `Instrs_ok2.frame` (the stack-framing/subsumption rule)          has **10** fields.
`Instr_ok2` is declared first, so its `frame` is found first. When the tactic
reaches `Instrs_ok2.frame`'s actual goal (10 layers), it wrongly calls
`introN 14`, asking for 4 more binders than exist, and crashes.

The minimal example below reproduces the same class of failure with plain
`Nat`-indexed toy types and no project dependencies. `A.frame` (6 fields,
declared first) shadows `B.frame` (2 fields, declared second) in the lookup,
so processing `B`'s `frame` case over-asks `introN` and crashes exactly the
same way.

(Swapping which one has more fields, or giving them different names, makes
the bug disappear — consistent with this being a first-match-wins name
collision, not something about `True`, `Nat`, or motive content.)

## Suggested fix

Line (a) should just use `info.numFields` directly — it's already correct
and already in scope — rather than re-deriving it via a name search that
isn't guaranteed to be unique across a `mutual` block.

## Status

Not yet found filed under leanprover/lean4 as of 2026-08-04 (searched
`introN`, `getAltNumFields`, `altsInfo`, and various phrasings of "mutual
induction duplicate constructor name" via the GitHub search API and the web/
Zulip archive). The closest related discussion is an old Zulip thread about
`induction` not supporting multi-motive mutual recursors *at all*, which is
a different, older, since-resolved limitation (this codebase's `induction
... using Foo.rec (motive_2 := ...)` works fine here whenever there's no
name collision).
-/

mutual
inductive A : Nat → Prop where
  | mk    : A 0
  | frame : ∀ n1 n2 n3 n4 n5 : Nat, A n1 → A n1   -- 6 fields; declared FIRST

inductive B : Nat → Prop where
  | base  : B 0
  | frame : ∀ n : Nat, B n → B n                   -- 2 fields; declared SECOND
end

example (n : Nat) (h : A n) : True := by
  induction h using A.rec (motive_2 := fun _ _ => True)
  all_goals sorry
