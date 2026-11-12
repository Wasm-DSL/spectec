# Digest: prior Lean translation attempts in `spectec/test-lean/`

Produced by a research subagent in session 1 (resumed once after a crash).
Pure read-only research; nothing in `spectec/test-lean/` was modified.
Full file paths below are absolute under `/home/zhengyew/spectec/spectec/test-lean/`.

This is **prior art for the exact same task**, so it's unusually
high-value — read this before starting Phase 2/3 (filling in proofs).

---

## 1. What was already attempted (Rocq lemma → Lean status)

### A. `typing_lemmas.lean` (2071 lines, hand-written, the pre-existing file
in `test-lean/` proper — NOT the same as `test-lean/test-lean-claude/`)

Imports `Mathlib.Tactic`, `wasm2.0`, `custom_notation`; `open functype list`.

**Complete/proved (no sorry):**
- `to_mathlib_forall₂` / `from_mathlib_forall₂` — bridge between the
  SpecTec-Lean-backend's own zip-based `Forall₂` def and Mathlib's real
  `List.Forall₂`, given a length-equality hypothesis. Once bridged,
  Mathlib's whole `Forall₂` lemma library (`forall₂_take_append`,
  `Forall₂.length_eq`, ...) becomes usable. **High-value reusable idiom.**
- `zip_self_both_sides_equal`, `zip_trans` (generic zip-relation
  transitivity helper via `List.mem_iff_getElem` + `List.getElem_zip`)
- `valtype_sub_refl`, `valtype_sub_trans` (trivial: `Valtype_sub` has
  `refl`/`bot` constructors)
- `resulttype_sub_refl`, `resulttype_sub_trans`, `resulttype_sub_app` (uses
  `zip_trans`)
- `instrs_empty_typing` (iff): `Instrs_ok p_context [] (t1s f-> t2s) ↔
  wf_context p_context ∧ (t1s subs< t2s)` — proved via `induction h using
  Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)` with `generalize` on both
  the instr-list and functype indices first.
- `ais_empty_typing` — the `Instrs_ok2`/store-carrying analogue, same
  technique via `Instrs_ok2.rec (motive_1 := ..., motive_3 := ...)`.
- `ai_principal_typing` (a giant `def`, ~340 lines, one match-arm per
  `admininstr` constructor — canonical/principal functype+side-conditions
  for every administrative instruction). `instr_principal_typing` wraps it
  for plain `instr` via a dummy empty store.
- `instr_typing_inversion` — `Instr_ok c instr (t1s f-> t2s) →
  instr_principal_typing c instr (t1s f-> t2s)`, one case per constructor.
- `principal_typing_conversion` — links `instr_principal_typing` and
  `ai_principal_typing` via `admininstr_instr`.
- `ai_typing_inversion` — depends on `instrtype_sub_refl` (which was itself
  `sorry` at the time — so this theorem, while written, wasn't closed
  end-to-end back then; check current status).
- `ainstr_ok_context_store_wf`, `construct_ais_typing_single`,
  `construct_ai_const_I32`, `construct_ais_subtyping`, `inst_match` (def),
  `ainstrs_ok_context_store_wf`, `construct_ais_compose`, `Vals_ok` (def),
  `Val_ok_non_bot`, `construct_ai_val` — all proved, supporting infra.
- `instr_subtyping_strengthen2` — proved (via `to_mathlib_forall₂` +
  `List.forall₂_take_append`/`forall₂_drop_append`).
- `instrs_single_typing_inversion`, `ais_single_typing_inversion'`,
  `ais_single_typing_inversion` — proved, chaining the above.

**Four live `sorry`s (as of that session):**
1. `instrtype_sub_refl` (~line 1112-1117):
   `theorem instrtype_sub_refl (ft : functype) : ft instrsub< ft := by sorry`
2. `instr_subtyping_weaken2` (~line 1536-1543):
   `((tx1 f-> ty1) instrsub< (tx2 f-> ty2)) → (ty2 subs< ty2_sup) →
   ((tx1 f-> ty1) instrsub< (tx2 f-> ty2_sup))`, `:= by sorry`
3. `instrtype_sub_trans` (~line 1545-1556):
   `(ft1 instrsub< ft2) → (ft2 instrsub< ft3) → (ft1 instrsub< ft3)`, `sorry`
4. `instrs_seq_typing_inversion` (lines 2002-2071) — **stated FALSE**, see
   §3 below.

`def instrtype_sub` (~lines 1042-1053):
```lean
def instrtype_sub (original_ft contextualized_ft : functype) : Prop :=
  match original_ft, contextualized_ft with
  | mk_functype (mk_list original_input_type) (mk_list original_output_type),
    mk_functype (mk_list actual_supplied_input_type) (mk_list actual_needed_output_type) =>
    ∃ (rest_in rest_out supplied_in needed_out : List valtype),
      actual_supplied_input_type = rest_in ++ supplied_in
      ∧ actual_needed_output_type = rest_out ++ needed_out
      ∧ (rest_in subs< rest_out)
      ∧ (supplied_in subs< original_input_type)
      ∧ (original_output_type subs< needed_out)
infix:20 "instrsub<" => instrtype_sub
```

### B. `custom_notation.lean` (15 lines, full contents)
```lean
import «wasm2.0»
def mkFunctype (tf1 tf2 : List valtype) : functype :=
    functype.mk_functype (list.mk_list tf1) (list.mk_list tf2)
def resulttypeSub (t1s t2s : List valtype) : Prop :=
    Resulttype_sub (list.mk_list t1s) (list.mk_list t2s)
infix:67 "f->" => mkFunctype
infix:50 "sub<" => Valtype_sub
infix:40 "subs<" => resulttypeSub
infix:30 "ftsub<" => Functype_sub
def prepend_label (C : context) (t : resulttype) : context :=
    { C with LABELS := t :: C.LABELS }
```

### C. `typing_lemmas_aesop.lean` (222 lines) vs `typing_lemmas_OLD.lean` (1864 lines)

`typing_lemmas_aesop.lean` is a standalone sandbox (doesn't import
`typing_lemmas.lean`) comparing hand-written vs `aesop`/`simp`/`grind`
automated proofs of `instrs_empty_typing`. Concrete aesop/grind findings
quoted in §2.

`typing_lemmas_OLD.lean` vs current: current added the Mathlib-`Forall₂`
bridge and `ais_single_typing_inversion'`, and expanded (but did not close)
`instrs_seq_typing_inversion`. Sorry count went 12 (OLD) → 19 (current).

### D. `test-lean-claude/` subfolder — a full previous Claude session's
from-scratch translation attempt (separate strategy from `typing_lemmas.lean`:
new, self-contained files against `wasm2.0.lean` directly, matching Rocq/
Isabelle *statements* with Lean-idiomatic proofs, with provenance doc
comments)

| File | Status | Contents |
|---|---|---|
| `Extension.lean` | 0 sorry | `extend_globalinst_refl`, `extend_funcinst_refl`, `extend_datainst_refl`, `extend_eleminst_refl`, `extend_tableinst_refl`, `extend_meminst_refl`, `extend_store_refl` (+ `forall_range_lt`/`forall_range_refl`/`forall_range_refl_noWf` helpers). Matches Rocq `extension_lemmas.v:926-1627` and Isabelle `Properties.thy:6-81`, both fully proved on both sides. **No transitivity lemma for any `Extend_*` exists in Rocq or Isabelle either** — flagged as possibly needed later if `store_extension_reduce` ever chains multiple steps. |
| `Subtyping.lean` | 0 sorry | `limits_sub_refl`, `limits_sub_trans`, `functype_sub_eq`, `globaltype_sub_eq`, `externtype_sub_refl`, `externtype_sub_trans`, `externtype_global_eq`, `externtype_func_eq`. Matches Rocq `extension_lemmas.v:285-412`. Not covered by Isabelle. |
| `InstrtypeSub.lean` | **0 sorry — directly closes 3 of the 4 `typing_lemmas.lean` sorries** | Re-derives `valtype_sub_refl/trans`, `forall2_valtype_sub_refl/trans`, `resulttype_sub_refl/trans/app` locally, plus new: `resulttype_sub_split`/`resulttype_sub_split_sup` (splitting `Resulttype_sub` of a concat at a given length, via `List.take`/`List.drop`/`List.zip_append` — Rocq needed hand-rolled induction; Lean's library handles directly). Then **`instrtype_sub_refl`** (Rocq `subtyping.v:420`), **`instrtype_sub_trans`** (Rocq `subtyping.v:434`, ported Rocq's own witness-construction strategy), **`instr_subtyping_weaken2`** (one-shot via `resulttype_sub_split` + `resulttype_sub_trans`). Ready to paste into `typing_lemmas.lean`'s sorries as proof bodies verbatim. |
| `CounterexampleCheck.lean` | 0 sorry (a disproof) | Proves `instrs_seq_typing_inversion` is false as literally stated — see §3. |
| `SeqTypingInversion.lean` | 0 sorry | The corrected restatement — see §3. Not a drop-in fix (changes the theorem's type). |
| `MemoryWriteAxioms.lean` | 0 sorry, introduces 2 new axioms | Ports Rocq's own `axioms.v` `ibytes_len'`/`nbytes_len'` into Lean (`ibytes_len`, `nbytes_len`), plus a reusable `splice_length_ge` list-algebra lemma. Gets partway to closing 2 of `StoreExtension.lean`'s 7 remaining sorries but hits a second, **Rocq-unprecedented** wall (needs `Forall wf_byte` of written bytes, no axiom for that anywhere) — flagged as a human decision, unresolved. |
| `StoreExtension.lean` | 16/23 `Step` cases real, 7 sorry | `store_extension_reduce`: induction on `Step` (wasm2.0.lean:11106-11205, 23 constructors), matching Isabelle's `reduce_store_extension` (only proves 1/23: `pure`). Proves: `pure`, `read`, 3 congruence cases (`ctxt_label`/`ctxt_frame`/`ctxt_instrs`, free via IH), `local_set`, `elem_drop`, `data_drop`, `table_set_val`, and 7 trap/failure variants via shared lemma `store_extension_same_state`. Remaining 7 sorries: `global_set` (needs real mutability typing), `table_grow_succeed`/`memory_grow_succeed` (need grow-function postconditions — a `Store_ok`/`Moduleinst_ok`/`Table_ok` typing invariant not ported), `store_num_val`/`store_pack_val`/`vstore_val`/`vstore_lane_val` (need byte-length + wf facts about `nbytes_`/`ibytes_`/`vbytes_`, opaque axioms in `wasm2.0.lean:3626-3681`). Self-contained: duplicates `Extension.lean`'s lemmas rather than importing (cross-file-import limitation, see §2). **This is the Lean counterpart of Rocq's `store_extension_reduce` — see `digest_type_preservation.md` #8 in this same directory for the Rocq original, which is itself only Admitted for the SIMD cases; the Lean attempt's 7 gaps are a DIFFERENT, larger set (typing-infra-dependent, not SIMD) since it wasn't built on top of a ported `Store_ok`/`Moduleinst_ok`.** |
| `00_sanity.lean` | trivial | Import-path sanity check. |

### E. Tangential (backend-codegen investigations, not proof translation)
- `sidecond_vs_totalize.lean` — confirms the Lean backend compiles
  side-condition-bearing definitions (like `minus_recs`) via `Option.map`/
  fold-into-`IterE` ("Totalize style"), not naive premise-currying. Low
  relevance to lemma translation; useful for reading opaque `.map`-chained
  defs in `wasm2.0.lean`.

---

## 2. Key Lean idioms/patterns that worked

- **Mathlib-`Forall₂` bridge**: `wasm2.0.lean`'s own `Forall₂` is a
  zip-based custom `def`, not Mathlib's inductive `List.Forall₂`. Given a
  length-equality hypothesis (always available from `Resulttype_sub`'s
  constructor), convert once via `List.forall₂_iff_zip`
  (`to_mathlib_forall₂`/`from_mathlib_forall₂`), then use Mathlib's whole
  `Forall₂` lemma library instead of re-deriving by hand.
- **`Instrs_ok.rec`/`Instrs_ok2.rec` custom-motive induction with
  `motive_1 := fun _ _ _ _ => True`**: mutually-defined relations need a
  motive for every sibling; set irrelevant motives to `True` so
  `all_goals trivial`/`try trivial` skips irrelevant cases.
- **Generalize indices inside the induction, not as outer theorem args**:
  state as `h : Instrs_ok C instr_lst ft → instr_lst = [] → ∀ t1 t2, ft =
  mkFunctype t1 t2 → ...` and induct on `h`, quantifying `t1 t2` *inside*
  — fixing them outside produces wrong IHs. Called out as a standing
  technique, recurring in every lemma of `SeqTypingInversion.lean`.
- **`generalize ... at h` before inducting on an equality-constrained
  index** (e.g. `generalize gen_instrs_ok_list : ([] : List instr) = l at
  h`) — standard way to induct while an index is fixed to a specific shape.
- **`Forall P xs` needs `simp [Forall]`, not bare `simp`**, to unfold —
  bare `simp` silently leaves it untouched.
- **Avoid `omega` directly on values typed via backend numeric `abbrev`s**
  (`n`, `m`, `N`, etc.) — `omega` doesn't see through plain `abbrev`s used
  as a *stated* hypothesis type, fails with misleading "possible
  counterexample ↑x ≥ 0". Fix: `subst`/`rw` to bare `Nat` first, or
  annotate `: Nat` explicitly.
- **Don't shadow backend abbrev names (`n`, `m`, ...) as local variable
  names** via `obtain`/`intro` — legal but confuses elaboration downstream.
- **Reconstruct a `cases`-destructured hypothesis rather than keeping the
  old name** if you need the packaged form again later in the same branch.
- **Prefer a small `eq`-style helper for single-constructor relations**
  (e.g. `Functype_sub a b → a = b` via `cases h; rfl`) over nested `cases`.
- **`generalize h : tables[a] = ti at hwf_old ⊢` before `obtain`/`cases` on
  a raw indexing expression** — destructuring `GetElem` directly once the
  context has a nontrivial `omega`-derived index proof can silently fail to
  narrow the type, or hit "Dependent elimination failed."
- **Never leave a constructor-call argument as `_` if a later `by` block
  references its pinned value** — elaboration order can leave the
  metavariable unresolved when the `by` block runs.
- **`subst` direction ambiguity** when both sides of an equation are
  pre-existing locals (`hx : x = i`, both already bound) can eliminate the
  *outer* variable instead of the fresh one — use `rw [hx]` on the goal
  instead of blind `subst` when you need to keep a specific local's name.
- **`conv`/`conv_lhs` is unavailable** in this project setup (confirmed:
  "unknown tactic" even with Mathlib imported) — use `calc` with a
  targeted `rw` on one side instead.
- **Aesop/grind findings** (from `typing_lemmas_aesop.lean`'s header):
  - `aesop` cannot invent the outer `induction ... using Instrs_ok.rec`
    itself — generalize/induction scaffolding must stay manual.
  - `mkFunctype`/`resulttypeSub` are plain (non-`@[reducible]`) `def`s —
    every automation call needs them spelled out (`simp [mkFunctype]`).
  - `aesop (add safe resulttype_sub_refl)` **reliably fails** on goals of
    shape `X subs< X` (non-linear pattern) even though `exact
    resulttype_sub_refl _` closes it instantly — genuine limitation.
  - `aesop (add safe resulttype_sub_trans)` failed with "goal was not
    normalised" — switching to `unsafe` fixed it.
  - `grind [resulttype_sub_trans]` closed single-step transitivity but
    failed when two chained applications through an intermediate fact were
    needed — `aesop`'s backtracking found the chain, `grind` didn't.
- **Cross-file imports between sibling files under a folder like
  `test-lean-claude/` do NOT work** unless the file is registered in the
  project's `lakefile.lean` `lean_lib` globs — `lean`'s import resolution
  only searches prebuilt `.olean`s via `LEAN_PATH`, never compiles a
  sibling `.lean` source on demand. **Practical consequence: add every new
  file to `lakefile.lean`'s globs (session 1 already does this — see
  NOTES.md) rather than assuming a bare `import SiblingFile` will work.**

---

## 3. Most important finding: `instrs_seq_typing_inversion` is FALSE as stated

`typing_lemmas.lean`'s statement (lines 2002-2071):
```lean
Instrs_ok c (i :: is) (ts1 f-> ts3)
→ ∃ ts2, Instr_ok c i (ts1 f-> ts2) ∧ Instrs_ok c is (ts2 f-> ts3)
```
i.e. claims any cons'd-sequence typing splits into a *singular*-instruction
typing (`Instr_ok`) for the head plus a sequence typing for the tail.

**This is false, not just hard.** `Instrs_ok`'s `frame` rule
(wasm2.0.lean:10043-10047) can prepend an arbitrary shared prefix to both
sides of an already-derived sequence typing, but `Instr_ok` (singular) has
no such rule — e.g. `const`'s rule (wasm2.0.lean:9676-9679) fixes the input
type to literal `[]` unconditionally. Concretely:
`Instrs_ok C [CONST I32 c] ([I32] f-> [I32,I32])` is derivable (build
`[] f-> [I32]` via `.instr`, then `.frame`-prepend `[I32]`), but no `ts2`
satisfies `Instr_ok C (CONST I32 c) ([I32] f-> ts2)` since `const` forces
the input to `[]`. Verified with a compiling Lean counterexample in
`CounterexampleCheck.lean` (both halves proved directly, no `sorry`). No
unsound proof was actually completed using the false statement (it's
`sorry`'d exactly where this bites).

**The fix, confirmed by Rocq precedent**: Rocq's `typing_lemmas.v:1080` has
the analogous `ais_seq_typing_inversion`, stated with the *sequence-level*
judgment on a singleton instead of singular `Instr_ok`/`Instr_ok2`.
`SeqTypingInversion.lean` proves the corrected version in full (0 sorry):
```lean
theorem instrs_seq_typing_inversion_fixed {C : context} {i : instr} {is : List instr}
    {ts1 ts3 : List valtype} (h : Instrs_ok C (i :: is) (mkFunctype ts1 ts3)) :
    ∃ ts2, Instrs_ok C [i] (mkFunctype ts1 ts2) ∧ Instrs_ok C is (mkFunctype ts2 ts3)
```
via induction on `Instrs_ok` (`Instrs_ok.rec (motive_1 := fun _ _ _ _ =>
True)`), following Rocq's `empty`/`instr`/`seq`/`sub`/`frame` case
structure, with `seq`'s 3-way list-split via two purpose-built helpers
`instrs_ok_widen_in`/`instrs_ok_widen_out` (contravariant/covariant
`Instrs_ok.sub` wrappers) plus `instrs_ok_nil_sub`/`instrs_ok_nil_refl`.

A second candidate fix (restate via `instr_principal_typing`/`instrsub<`,
matching `ai_typing_inversion`'s own idiom) was considered but not pursued
since fix #1 has direct Rocq precedent.

**IMPORTANT — this needs a decision, not just a proof paste**: this is a
*statement change* for whatever port of `typing_lemmas.v`'s
`Instr_seq_typing_inversion`-equivalent the current session writes — when
you reach this lemma in the Rocq `typing_lemmas.v` digest, state it in the
Rocq-faithful sequence-level form from the start (matching `typing_lemmas.v:
1080`'s `ais_seq_typing_inversion`), not in the singular `Instr_ok` form
that the old `typing_lemmas.lean` mistakenly used.

---

## 4. Documented Lean-elaboration bugs on the auto-generated backend output

### Bug 1 — `induction ... using Foo.rec` crashes when two DIFFERENT types
in the same `mutual` block share a constructor short name
(documented+fixed in `bug.lean` / `bug_repro_fix_check.lean`)

Toolchain: `leanprover/lean4:v4.32.0` (also reproduced on v4.30.0-rc2).

**Symptom**: `Tactic introN failed: There are no additional binders or let
bindings in the goal to introduce`, even though the printed goal has
exactly as many binders as expected.

**Root cause** (traced into Lean's own source,
`Lean/Elab/Tactic/Induction.lean`, `evalAlts`): per-alternative binder
count is re-derived via `getAltNumFields`, a linear search over
`elimInfo.altsInfo` keyed **only by bare, unqualified constructor short
name** — not by which type in the mutual block it belongs to. When two
types in one `mutual` block each declare a same-named constructor, this
returns the *first* match by declaration order regardless of which
alternative is being processed.

**Concretely hits this project**: `Instr_ok2.frame` (14 fields) and
`Instrs_ok2.frame` (10 fields) — both in `wasm2.0.lean`'s mutual block,
`Instr_ok2` declared first. Any `induction ... using
Instr_ok2.rec`/`Instrs_ok2.rec` reaching `Instrs_ok2.frame`'s case wrongly
gets `introN 14` and crashes.

**Confirmed fix**: rename colliding case IDs so they're unique across the
whole mutual block (e.g. `frame` → `A_frame`/`B_frame`) — per the repro
file's comment, the real backend codegen (`backend.ml`, presumably via
something like `gather_colliding_relation_case_names`) is believed to
already do this in the actual generated `wasm2.0.lean`, but **this should
be verified against whatever `wasm2.0.lean` you're actually using** (e.g.
`grep -n "| frame"` across `Instr_ok2`/`Instrs_ok2`'s blocks) rather than
assumed. Not yet reported upstream to leanprover/lean4.

**Practical implication**: if `induction ... using` over a `wasm2.0.lean`
mutual relation gives a mysterious `introN failed`, check this class of bug
(same-named constructors across the mutual group) before assuming your own
tactic usage is wrong.

### Bug/limitation 2 — Forall/Forall₂/Mathlib-redirect kernel restriction
(documented in `forall_postmortem.lean`)

Investigates why `wasm2.0.lean`'s `Forall`/`Forall₂`/`Forall₃` are the
backend's own hand-rolled, zip-based `def`s rather than Mathlib's real
inductive versions, and why an attempt to redirect codegen to emit
Mathlib's versions was fully reverted. Quoted "biggest lesson":

> "the project's golden-file test (`dune runtest`) only ever diffs
> generated text against a fixture — it never invokes the Lean kernel at
> all. It is structurally incapable of catching this whole class of bug...
> Every real problem found in this investigation was found by manually
> running the complete, real spec's output through `lake env lean` against
> actual Mathlib — not by the golden-file test... Any future attempt at
> this MUST budget for that full real-spec check as a required step."

Underlying restriction: a self-/mutually-recursive `inductive` nested
inside a pre-existing container type (`List`, Mathlib's `List.Forall₂`,
`Prod`, even `∧`) can fail with `(kernel) invalid nested inductive datatype
... nested inductive datatypes parameters cannot contain local variables`,
depending on shape (safe iff the predicate only uses the walked element
itself for List/Forall-style; safe iff every nested occurrence reproduces
the enclosing constructor's conclusion exactly for Prod/Box-style). Real
spec relations `wf_instr`, `wf_admininstr`, `fun_utf8` are self-referencing
and trip this — confirmed genuine kernel errors on the real full-spec
output, not caught by the small dune golden test.

**Practical implication**: `wasm2.0.lean`'s custom `Forall`/`Forall₂`/
`Forall₃` are intentional/load-bearing, not an oversight — this is why the
Mathlib-bridge idiom (§2) exists. Do not try to redirect codegen or locally
substitute Mathlib's `List.Forall₂` without re-reading this file in full
and `sandbox_11.lean` (the cited authoritative worked reference, NOT read
by the digesting agent — flagged gap) first.

Also: `src/middlend/sideconditions.ml` already emits a separate
`List.length xs₁ = List.length xs₂` premise at every `Forall₂`/`Forall₃`
call site unconditionally (505 such premises confirmed) — length info is
already available at call sites even without baking it into `Forall₂`'s
own definition.

---

## 5. Status/progress as of the last `test-lean-claude/` session (direct quotes)

From `logs/STATUS.md`:
> "Headline results... 1. Every `sorry` in `test-lean/typing_lemmas.lean`
> (4 clusters) has a fix in this folder — 3 drop-in, 1
> (`instrs_seq_typing_inversion`) a corrected restatement needing your
> decision. 2. `StoreExtension.lean`'s `store_extension_reduce` is 16/23
> real (Isabelle: 1/23). All 7 remaining cases are now *confirmed* blocked
> (not just unchecked), for concrete, documented reasons. 3.
> `MemoryWriteAxioms.lean` ports Rocq's own length axioms and gets 2 of
> those 7 cases down to needing one more (Rocq-unprecedented) axiom —
> flagged as a decision, not added unilaterally."

From `PROGRESS.md`:
> "**Net result: every `sorry` in `typing_lemmas.lean`, as of this
> session's survey, now has a corresponding proof or fix sitting in this
> folder.**"

Priority-ordered "Not yet started" (from `PROGRESS.md`):
1. The remaining 7 `store_extension_reduce` leaf cases — all confirmed
   genuinely blocked: 4 memory-write cases need `Forall wf_byte` of
   written bytes (no precedent anywhere — `ibytes__is_wf`/`nbytes__is_wf`
   are themselves `sorry`); `table_grow_succeed`/`memory_grow_succeed`
   need a table/memory's declared minimum related to actual current length
   (a `Store_ok`/`Moduleinst_ok`-level invariant, absent from purely
   structural `wf_tableinst`/`wf_meminst`); `global_set` needs mutability
   typing. **None reachable without porting `Store_ok`/`Moduleinst_ok`/
   `Table_ok`/`Global_ok`** — "a real dependency, not a gap in effort."
2. `helper_lemmas.v` — judged **low-value to port wholesale**: "almost
   entirely generic list-algebra Rocq had to hand-roll that Lean's
   List/Mathlib API already provides natively... only worth revisiting if
   a specific named lemma turns out to be needed by something else." (NOTE
   — session 1's own independent digest of `helper_lemmas.v`, see
   `NOTES.md`, reaches a similar conclusion re: mathcomp artifacts, but the
   user's task explicitly wants lemma-for-lemma fidelity where possible,
   so treat "low value" as "prove quickly via mathlib, still port the
   statement" rather than "skip entirely.")
3. `typing_lemmas.v`/`subtyping.v` remainder — "mostly `ais_*`-level
   (administrative-instruction) versions of lemmas already covered at the
   `instr`/surface level, or Rocq-specific plumbing (`Externaddr_invert_*`,
   `minst_invert_*`) tied to module-instantiation typing not yet touched —
   lower priority until/unless `Store_ok`/`Moduleinst_ok` get ported."
4. Full Preservation/Progress — explicitly deferred: "1000+ line, deeply
   case-heavy proofs; realistic only after `Instrs_ok2`/`Store_ok`/
   `Moduleinst_ok` (the typing side of `B-soundness.spectec`) are ported,
   which is a substantially bigger scaffolding effort than anything
   attempted in this folder so far." (Session 1 note: per
   `digest_type_preservation.md`, `Store_ok`/`Moduleinst_ok`-equivalents
   ARE already present in `wasm2.0.lean` as backend output — the "porting"
   needed is of the Rocq LEMMAS about them, not the definitions.)

Working conventions (quoted, `PROGRESS.md`'s closing section):
> "Every constant/lemma we reference from `wasm2.0.lean` is looked up by
> exact `grep -n` before use — never assumed from memory of the
> Rocq/Isabelle version, since field names, argument order, and
> Forall-vs-holds_upto representational choices differ."

From `logs/FINAL_REPORT.md`:
> "**Status at time of writing**: not stopped due to any error or
> blocker — this report was written as a deliberate checkpoint after the
> tractable, well-scoped work ran out and the remaining candidates all
> require either a maintainer decision (on `typing_lemmas.lean`) or a
> substantially larger scoping/porting effort (typing infrastructure) that
> didn't seem prudent to start without pausing to report first."

Two explicit open decisions left for a human (`logs/FINAL_REPORT.md`):
> "**A third memory-write axiom.** ... Adding that as a third axiom felt
> like it crossed from 'replicate Rocq's trusted base' into 'invent what I
> need,' so I stopped there."
> "**`instrs_seq_typing_inversion`** in `typing_lemmas.lean` is provably
> false as written... you should check whether anything downstream already
> calls the old (false) shape and would need adjusting."

Scope decision that shaped the whole prior effort (`logs/DECISIONS.md`,
2026-09-22 ~23:00, marked `[REVIEW]`):
> "Decided to build new, from-scratch Lean proofs in this folder against
> the existing `wasm2.0.lean`/`typing_lemmas.lean`, rather than trying to
> literally transliterate Rocq/Isabelle tactic-by-tactic... instead each
> Lean lemma reproduces the same theorem statement... with whatever
> Lean-idiomatic proof closes it. Provenance is recorded in each theorem's
> doc comment and in `PROGRESS.md`'s table, so the mapping stays
> auditable."

**This matches session 1's/the user's own stated approach exactly** (proof
method is free to differ, signature must match) — continue this
methodology: verify Rocq/Lean shapes via `grep`, not memory; record
provenance (source file:line) in every ported theorem's doc comment.

---

## 6. Explicit warnings / "don't do X" (consolidated)

1. **Don't assume a `Step` case's difficulty by analogy with a
   similar-looking case** — the prior session initially wrote off 16 of 23
   `store_extension_reduce` cases by analogy with `global_set`; 9 turned
   out trivial on direct inspection. "When a pattern seems to generalize
   from one instance, check the others directly before writing them all
   off as equally hard."
2. **Don't blind-`subst` an equation between two pre-existing locals** —
   direction is ambiguous, can eliminate the wrong variable silently.
3. **Don't rely on bare `simp` to unfold `Forall`/`abbrev`** — need
   `simp [Forall]`; don't use `omega` directly on abbrev-typed hypotheses.
4. **Don't shadow backend-abbrev names (`n`, `m`, `N`, ...) as locals.**
5. **Don't `import` a sibling `.lean` file unless it's registered in
   `lakefile.lean`'s globs** — fails with `unknown module prefix`.
   (Session 1 already adds new files to the globs as created — keep doing
   this rather than relying on bare cross-file imports.)
6. **Don't redirect the Lean backend's codegen to use Mathlib's
   `Forall`/`Forall₂`** without re-reading `forall_postmortem.lean` in
   full + `sandbox_11.lean` first — tried before, broke on real
   self-referencing relations, fully reverted. (Not directly relevant
   unless you end up touching backend codegen, which is out of scope for
   this proof-porting task anyway — `wasm2.0.lean` is not ours to edit.)
7. **Don't trust a dune/golden-file text-diff test as evidence that
   generated Lean typechecks** — always run through `lake env lean`/
   `lake build` against Mathlib (session 1 already does this).
8. **Don't add new `axiom`s beyond Rocq's own trusted base (`axioms.v`'s 2
   axioms)** without flagging it as a decision to the user — treat
   "replicate Rocq's trusted base" vs "invent what I need" as a bright
   line the prior session deliberately didn't cross.
9. **If `introN failed` on `induction ... using` over a mutual relation
   with no obvious cause, check for colliding constructor short-names
   first** (Bug 1 above).
10. When you reach the Rocq `typing_lemmas.v` analogue of
    `instrs_seq_typing_inversion` (likely `Instr_seq_typing_inversion` for
    the static side, `ais_seq_typing_inversion` at `typing_lemmas.v:1080`
    for the administrative side), **state it in the Rocq-faithful
    sequence-level form from the start** (see §3) — don't repeat the old
    file's mistake of stating it with singular `Instr_ok` on the head.

---

## Coverage notes (what the digesting agent actually read)

Read in full: `typing_lemmas.lean` (2071 lines), `custom_notation.lean`,
`typing_lemmas_aesop.lean`, all of `test-lean-claude/` proper
(`00_sanity.lean`, `CounterexampleCheck.lean`, `Extension.lean`,
`InstrtypeSub.lean`, `MemoryWriteAxioms.lean`, `SeqTypingInversion.lean`,
`StoreExtension.lean`, `Subtyping.lean`), `PROGRESS.md`,
`logs/{STATUS,DECISIONS,FINAL_REPORT}.md`, `bug.lean`,
`bug_repro_fix_check.lean`, `sidecond_vs_totalize.lean`.

Diffed (not fully read): `typing_lemmas_OLD.lean` vs current.

Partially read: `forall_postmortem.lean` (the "SHORT REPORT" section in
full, per the file's own header; the "LONG TECHNICAL GUIDE" continuation
only to ~line 200 of ~32K). `sandbox_11.lean` (cited as the authoritative
worked reference for Bug 2) was **not read at all** — flagged gap if full
technical detail on the kernel nested-inductive restriction is ever needed.

**Not read**: `wasm2.0.lean`, `wasm2.0_OLD.lean`, `wasm2.0_OLD2.lean`,
`wasm2.0_tier1.lean` in `spectec/test-lean/` (the old copies — note this is
a *different* directory from our `spectec/src/test-lean-claude/wasm2.0.lean`,
which session 1 has separately inspected directly, see NOTES.md). Anything
above about `wasm2.0.lean`'s structure (e.g. `Step`'s 23 constructors at
lines 11106-11205 — NOTE these line numbers are for the OLD copy in
`test-lean/`, cross-check against ours) is inferred secondhand from the
other files' doc comments/grep citations, not read directly by this agent.
