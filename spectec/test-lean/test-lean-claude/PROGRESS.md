# test-lean-claude: progress tracker

Goal (from user request): translate as much as possible of the partially-completed
Rocq (`rocq-backend-proof` branch, `spectec/test-rocq/theories/`) and Isabelle
(`isabelle-mech-backend` branch, `spectec/isabelle_type_safety_proof/`) Wasm 2.0
type-safety proofs into Lean, against the SpecTec-generated `test-lean/wasm2.0.lean`
model. Everything lives under `test-lean/test-lean-claude/` — nothing outside that
folder is to be modified (see `safety-checks/`).

This file is the master index. `logs/STATUS.md` has the live resume point for
picking work back up after an interruption. `logs/DECISIONS.md` has a timestamped
log of judgment calls, doubts, and anything the user should sanity-check.

## Source material (fetched to scratchpad, not in this repo)

* Rocq: `/tmp/claude-1002/-home-zhengyew-spectec/b969a412-0af9-4d68-9416-80317d7b03e1/scratchpad/rocq_proof/`
  (`axioms.v`, `extension_lemmas.v`, `helper_lemmas.v`, `helper_tactics.v`,
  `subtyping.v`, `type_preservation_pure.v`, `type_preservation.v`,
  `type_progress.v`, `typing_lemmas.v`)
* Isabelle: `/tmp/claude-1002/-home-zhengyew-spectec/b969a412-0af9-4d68-9416-80317d7b03e1/scratchpad/isabelle_proof/`
  (`Context_Store_Agreement.thy`, `Properties.thy`, `store_extension_typing.thy`,
  `Subtyping_Properties.thy`, `Subtyping_Theorem.thy`, `Subtyping.thy`,
  `Type_Inversion.thy`, `Typing_Simplified.thy`, `Wasm2_Type_Soundness.thy`)

**Caution**: this scratchpad directory is session-scoped and may not survive
indefinitely. If it's gone on resume, the source files need re-fetching from
GitHub (URLs in the original task description / git history) before continuing
any lemma that isn't already ported.

## Already existing (not written by this effort — for context only)

`test-lean/typing_lemmas.lean` (human-written, pre-existing) already covers:
`valtype_sub_refl/trans`, `resulttype_sub_refl/trans/app`, `instrs_empty_typing`,
`ai_principal_typing` (canonical-form/inversion for all admininstr cases),
`instr_typing_inversion`, `ai_typing_inversion`, and an incomplete
`instrs_seq_typing_inversion`. See prior conversation summary for a known bug in
its `BR_TABLE` case of `ai_principal_typing` (∀-scoping drops the default-label
subtyping requirement when the explicit target list is empty) — not yet fixed,
out of scope for this folder unless asked.

## Files in this folder

| File | Status | Rocq source | Isabelle source | Notes |
|---|---|---|---|---|
| `Extension.lean` | ✅ compiles, 0 sorry | `extension_lemmas.v:926-1627` (`extend_*_refl_0`, `extend_*_refl`, `Extend_store_refl`) | `Properties.thy:6-81` (`*_extension_refl`, `store_extension_refl`) | Store/instance extension reflexivity, all 6 instance kinds + store-wide. No transitivity lemma exists in either source, so none attempted. |
| `Subtyping.lean` | ✅ compiles, 0 sorry | `extension_lemmas.v:285-412` (`limits_sub_refl/trans`, `externtype_sub_refl/trans`, `externtype_global_eq`, `externtype_func_eq`) | not directly covered | Limits/externtype subtyping refl+trans+injectivity. |
| `StoreExtension.lean` | ✅ compiles, **16/23** `Step` cases real (only 7 remain `sorry`) | `type_preservation.v` `store_extension_reduce` (mostly proved — has the *real* target signature with `Instrs_ok2` preconditions, not replicated here) | `Properties.thy:84-164` `reduce_store_extension` (1/23 proved there: `pure`) | Proved by genuine induction on `Step`. Real: `pure`, `read`, `local_set`, `elem_drop`, `data_drop`, `table_set_val`, the 3 congruence cases, and **7 trap/failure variants that also turned out to leave `z` unchanged** (`table_set_trap`, `table_grow_fail`, `store_num_trap`, `store_pack_trap`, `vstore_oob`, `vstore_lane_oob`, `memory_grow_fail`) — found by checking each case's actual `Step` constructor directly rather than assuming "mutates the store ⇒ needs typing" by analogy with `global_set` (that assumption was wrong for most of these — see `logs/DECISIONS.md`). Still `sorry`: `global_set` (genuinely needs mutability typing), `table_grow_succeed`/`memory_grow_succeed` (need the grow-functions' postcondition), `store_num_val`/`store_pack_val`/`vstore_val`/`vstore_lane_val` (need a length-preservation fact about `nbytes_`/`ibytes_`/`vbytes_`, not yet checked). **Self-contained**: duplicates `Extension.lean`'s reflexivity lemmas rather than importing them — see file header and `logs/DECISIONS.md` for why cross-file imports don't work here. |
| `InstrtypeSub.lean` | ✅ compiles, **0 sorry** | `subtyping.v:114,132,242,344,389,420,434` (`resulttype_sub_refl/_trans/_app/_split/_split_sup`, `instrtype_sub_refl`, `instrtype_sub_trans` — all fully proved here, matching Rocq's fully-proved reference) | not directly covered | **Directly and completely closes THREE live `sorry`s in the pre-existing, human-written `test-lean/typing_lemmas.lean`**: `instrtype_sub_refl` (line 1112), `instrtype_sub_trans` (line 1545), `instr_subtyping_weaken2` (line 1536) — not edited there, out of scope, but proof bodies here should paste in directly, see file header. Initially judged `instrtype_sub_trans` too costly (needs a `take`/`drop` list-splitting lemma pair Rocq itself flagged as confusing) and left it `sorry`, then revisited and completed it — see `logs/DECISIONS.md` for the full account of the reversal. This is the single highest-value result in this folder so far: a genuine bugfix/completion for 3 of the 4 sorries in the user's own frontier proof file (the 4th, `instrs_seq_typing_inversion`, is a different story — see below). |
| `CounterexampleCheck.lean` | ✅ compiles, 0 sorry (it's a disproof, not a development) | n/a | n/a | Empirically verifies that `typing_lemmas.lean`'s `instrs_seq_typing_inversion` is FALSE as stated. See "✅ Resolved" section below. |
| `SeqTypingInversion.lean` | ✅ compiles, **0 sorry** | `typing_lemmas.v:1080` `ais_seq_typing_inversion` (the analogous, correctly-stated lemma used as the reference) | not directly covered | **The fourth and last `sorry`-cluster in `typing_lemmas.lean` closed** — but as a *corrected restatement*, not a drop-in proof (see "✅ Resolved" section below). Re-derives `Valtype_sub`/`Resulttype_sub` refl/trans/app locally (duplication, same reason as `InstrtypeSub.lean`) plus the genuinely new pieces: `instrs_ok_nil_sub`/`instrs_ok_nil_refl` (empty-sequence characterization) and `instrs_ok_widen_in`/`instrs_ok_widen_out` (contravariant/covariant `Instrs_ok.sub` wrappers), then `instrs_ok_cons_gen`/`instrs_seq_typing_inversion_fixed`. |
| `MemoryWriteAxioms.lean` | ✅ compiles, 0 sorry (introduces 2 new `axiom`s) | `axioms.v` `nbytes_len'`/`ibytes_len'` (ported directly) | not directly covered | Confirms and *partially* resolves the `store_num_val`/`store_pack_val` blocker from item 1 below: the length fact is provable given the same axioms Rocq's own trusted base already needs (kept, with a general reusable splice-length lemma, `splice_length_ge`), but closing the actual `Step` cases needs a *second*, unprecedented fact (`Forall wf_byte` of the written bytes) that Rocq has no axiom for either — judged a step too far to invent unilaterally, so `store_num_val`/`store_pack_val` remain `sorry` in `StoreExtension.lean`. See `logs/DECISIONS.md` (`~01:15-01:25`) for the full account, including exactly what a third axiom would need to say if you want to close these yourself. |

## ✅ Resolved — `instrs_seq_typing_inversion` fixed and fully proved

`typing_lemmas.lean`'s `instrs_seq_typing_inversion` (lines 2002-2071) is, as
literally stated, **false** (not just hard/incomplete) — verified with a
compiling Lean counterexample in `CounterexampleCheck.lean`. Its conclusion
uses singular `Instr_ok` for the head instruction, but `Instrs_ok`'s `frame`
rule can produce sequence typings no single `Instr_ok` derivation can match
(e.g. `CONST`'s rule fixes its input type to `[]` unconditionally, so
`Instrs_ok C [CONST I32 c] ([I32] f-> [I32,I32])`, derivable via `frame`, has
no matching `Instr_ok` witness at all).

Rocq's `typing_lemmas.v` has the analogous lemma stated correctly
(`ais_seq_typing_inversion`, line 1080), using the sequence-level judgment on
a singleton (`Instrs_ok2 ... [v_ai] ...`) instead — confirming the right fix.
**`SeqTypingInversion.lean` now has this corrected lemma
(`instrs_seq_typing_inversion_fixed`) fully proved, 0 sorry**, by induction
on `Instrs_ok` (using the `Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)`
trick to skip the ~70 irrelevant `Instr_ok` cases), following Rocq's
case structure (`empty`/`instr`/`seq`/`sub`/`frame`) with the `seq` case's
3-way list-split (`i1 = []` vs `i1 = hd::tl`) handled via `Instrs_ok.sub`
input/output-widening lemmas built for the purpose
(`instrs_ok_widen_in`/`instrs_ok_widen_out`). See `logs/DECISIONS.md`'s
`2026-09-23 ~00:05`/`~00:15`/`~00:50` entries for the full account.

**Still needs a human decision before pasting into `typing_lemmas.lean`**:
the corrected statement changes the theorem's *type* (sequence-level
`Instrs_ok c [i] (...)` instead of singular `Instr_ok c i (...)`), so
whoever maintains that file needs to check downstream call sites (if any
exist yet) expect this shape, or adjust them — this isn't a drop-in proof
swap like `InstrtypeSub.lean`'s three fixes, it's a statement change.

## Suggested immediate follow-up (cheap, high value, needs the user)

`InstrtypeSub.lean`'s `instrtype_sub_refl`/`instrtype_sub_trans`/
`instr_subtyping_weaken2` proofs are all complete (0 sorry) and should be
pasted into `test-lean/typing_lemmas.lean` in place of its `sorry`s at lines
1112-1117, 1536-1543, and 1545-1556 (that file already has its own
`instrtype_sub` def and `subs<` notation, so only the proof *bodies* need
copying, not the surrounding statements) — this is outside this folder's
scope to do automatically, flagging for the user to action or explicitly
authorize. `instrs_seq_typing_inversion` (see "✅ Resolved" above) is a
separate, bigger action: it needs the *statement* changed, not just the
proof, so it's a decision for whoever maintains that file rather than a
drop-in paste.

**Net result: every `sorry` in `typing_lemmas.lean`, as of this session's
survey, now has a corresponding proof or fix sitting in this folder.**

## Not yet started (rough priority order)

1. **The remaining 7 leaf cases of `store_extension_reduce`** — checked all
   of them directly; **all 7 are now confirmed genuinely blocked**, not just
   unchecked (this was itself worth doing, given how wrong the *previous*
   "these all need typing" assumption turned out to be for the other 16 —
   see `logs/DECISIONS.md`):
   - `store_num_val`/`store_pack_val`/`vstore_val`/`vstore_lane_val`: all go
     through `with_mem`'s splice (`(take nat ++ new) ++ drop (nat+nat_0)`).
     **Update**: the length side of this is now actually solved for the
     `nbytes_`/`ibytes_` cases (`MemoryWriteAxioms.lean`, porting Rocq's own
     `axioms.v` axioms for exactly this) — but a *second*, unprecedented gap
     (needing `Forall wf_byte` of the written bytes, which Rocq's axioms
     don't cover either) blocks actually closing `store_num_val`/
     `store_pack_val`. `vstore_val`/`vstore_lane_val` (via `vbytes_`) have
     *neither* gap addressed — no Rocq precedent exists for `vbytes_` at
     all, so even the length axiom would be a new invention there. See
     `MemoryWriteAxioms.lean`'s header and `logs/DECISIONS.md`
     (`~01:15-01:25`) for the complete account and exactly what a third
     axiom would need to say if you want to finish these yourself.
   - `table_grow_succeed`/`memory_grow_succeed`: checked `fun_growtable`
     directly (`wasm2.0.lean:9216-9239`) — it's a real, non-opaque inductive
     (not axiomatized), and its successful-growth case *does* hand over
     `wf_tableinst` of both the old and new table for free. But the
     `Extend_tableinst` obligation needs `old_min ≤ new_min` (the table
     *type's* declared minimum), and nothing here relates a table's
     declared minimum to its actual current `REFS` length — that
     relationship is a `Table_ok`-style *typing* invariant belonging to the
     module-instantiation layer (`Store_ok`/`Moduleinst_ok`), not something
     `wf_tableinst` (a purely structural predicate) enforces. Confirms this
     needs the same typing infra as `global_set`, just via a different
     invariant.
   - `global_set`: needs mutability typing, as already documented.

   None of these 7 are reachable without porting `Store_ok`/`Moduleinst_ok`/
   `Table_ok`/`Global_ok` (or, for the memory cases, adding a new axiom) —
   this is a real dependency, not a gap in effort.
2. **`helper_lemmas.v` (657 lines, 46 decls, 0 Admitted)** — surveyed
   (declaration names only): almost entirely generic list-algebra Rocq had
   to hand-roll (`take`/`drop`/`zip`/list-update lemmas) that Lean's
   `List`/Mathlib API already provides natively — e.g. `resulttype_sub_split`
   above needed none of Rocq's `drop_size_cat`/`take_size_cat`/etc., just
   `List.zip_append`. Judged low-value to port wholesale; only worth
   revisiting if a *specific* named lemma from it turns out to be needed by
   something else (as happened, productively, with `subtyping.v`).
3. `typing_lemmas.v` (Rocq) and `subtyping.v` (Rocq) — the highest-value
   items originally listed here have now been addressed: `instrtype_sub_*`
   and the `instrs_seq_typing_inversion` fix are done (`InstrtypeSub.lean`,
   `SeqTypingInversion.lean`). What's left in these two files is mostly
   `ais_*`-level (administrative-instruction) versions of lemmas already
   covered at the `instr`/surface level, or Rocq-specific plumbing
   (`Externaddr_invert_*`, `minst_invert_*`) tied to module-instantiation
   typing not yet touched here — lower priority until/unless
   `Store_ok`/`Moduleinst_ok` get ported (see item 4).
4. Full `store_extension_reduce`'s remaining 7 cases (see item 1), then
   `type_preservation_pure.v`'s `t_pure_preservation`, then eventually
   `type_preservation.v`'s `t_preservation` and `type_progress.v`'s `t_progress`
   — these are the real end-goal theorems but are 1000+ line, deeply
   case-heavy proofs; realistic only after `Instrs_ok2`/`Store_ok`/
   `Moduleinst_ok` (the typing side of `B-soundness.spectec`) are ported,
   which is a substantially bigger scaffolding effort than anything
   attempted in this folder so far.

## Working conventions established so far

* Every constant/lemma we reference from `wasm2.0.lean` is looked up by exact
  `grep -n` before use — never assumed from memory of the Rocq/Isabelle
  version, since field names, argument order, and Forall-vs-holds_upto
  representational choices differ.
* `Forall P xs` (the SpecTec-Lean-backend's own `def`, not `List.Forall`)
  needs `simp [Forall]` (not bare `simp`) to unfold — bare `simp` leaves it
  untouched and any `simpa`/`omega` against it silently fails or produces a
  confusing residual goal.
* Avoid `omega` on any value whose stated type is one of the backend's numeric
  type *abbreviations* (`n`, `m`, `N`, etc., all `abbrev X : Type := Nat`) —
  `omega` does not unfold plain `abbrev`s used as a hypothesis's stated type
  and fails with a confusing "possible counterexample ↑x ≥ 0" (looks like a
  coercion issue but isn't one). Fix: `subst`/`rw` the way to a bare goal
  first, or state the have/intro with `: Nat` explicitly instead of the
  abbrev name, then use `omega`/`Nat.le_trans`/`Nat.le_refl` directly.
* Do not reuse `n`/`m` (or other backend type-abbrev names) as *local
  variable* names via `obtain`/`intro` — shadowing them is legal Lean but
  produces confusing downstream elaboration; use `nb`/`mb` etc. instead.
* When a `cases h with | ctor args => ...` destructures a hypothesis you'll
  need again in unmodified form later in the same branch, reconstruct it with
  the constructor applied to the extracted pieces (e.g.
  `wf_store.store_case_ funcs globals ... hfuncs ...`) rather than trying to
  keep the original hypothesis name alive — `cases` consumes it.
* Prefer extracting a small `eq`-style helper lemma (e.g. `functype_sub_eq`,
  `globaltype_sub_eq`) over chained chained `cases` when a relation is
  "reflexivity-only" (single self-referential constructor) — much less
  fragile than tracking variable identification through nested `cases`.
