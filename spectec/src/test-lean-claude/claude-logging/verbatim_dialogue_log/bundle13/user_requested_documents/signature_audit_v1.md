# Signature audit v1 — Lean vs. current Rocq (`rocq-backend-proof-final`)

Full manual hypothesis-by-hypothesis / conclusion-by-conclusion comparison of every
`theorem`/`axiom`/`def` in the 6 Lean files against the current
`spectec/test-rocq/theories/*.v` source, restricted to declarations that carry an explicit
"Rocq `<file>.v[:line]` `<name>`" doc-comment citation. Proof *tactics* were never compared
(irrelevant under proof irrelevance); only statement content.

**Summary**: ~325 top-level Lean declarations across the 6 files; of these, roughly 260 carry
an explicit Rocq citation and were in scope. Every cited declaration was checked. **12
genuine signature mismatches** were found (missing/extra hypotheses or conclusion content
that differs from current Rocq, not already covered by an in-file "deliberate
representational difference" comment). In addition, **20 stale/orphaned citations** were
found (the cited Rocq name no longer exists in the current source — informational, listed
separately since these are not "wrong" per se, just unverifiable against a live target).
`Subtyping.lean` and `TypePreservationPure.lean` came back **completely clean** — 0
mismatches, 0 orphans.

---

## Mismatches (hypothesis/conclusion content differs from current Rocq)

| # | Lean location | Rocq location | Mismatch | Suggested fix |
|---|---|---|---|---|
| 1 | `HelperLemmas.lean:192-194` `list_slice_update_length` | `helper_lemmas.v:325-326` `list_slice_update_length` | Lean has an **extra hypothesis** `n = l'.length` that current (and even pre-resync) Rocq does not have — Rocq's version is unconditional. Root cause: Lean's `list_slice_update` (`HelperLemmas.lean:45-46`) is defined via `take`/`append`/`drop`, which is only length-preserving when `n = update_l.length`; Rocq's actual recursive `list_slice_update` (`wasm.v:66-74`) uses a different early-stopping algorithm that is unconditionally length-preserving. | Either redefine `list_slice_update` to match Rocq's real recursive algorithm (then drop the hypothesis and prove unconditionally), or at minimum flag the `def` itself as a non-equivalent simplification. Target statement: `theorem list_slice_update_length {α : Type} (l l' : List α) (i n : Nat) : (list_slice_update l i n l').length = l.length` |
| 2 | `TypingLemmas.lean:376-377` `ai_principal_typing`, `GLOBAL_SET` case | `typing_lemmas.v:498-501` (`ai_principal_typing`, `admininstr_GLOBAL_SET` case) | Lean existentially quantifies over **any** `m : «mut»` in the looked-up globaltype. Rocq requires the mutability to be **exactly** `Some MUT` (mirroring `Instr_ok`'s `global_set` constructor at `wasm.v:15041-15046`, which is likewise pinned to `mk_globaltype (Some MUT) t`). As stated, Lean's `ai_principal_typing` would consider `GLOBAL_SET` on an **immutable** global well-typed — a genuine soundness-relevant gap. | `\| admininstr.GLOBAL_SET x => ∃ (t : valtype), v_ft = mkFunctype [t] [] ∧ v_C.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype (some r_MUT.MUT) t)` (drop the `m` existential, hard-code `some r_MUT.MUT`). |
| 3 | `TypingLemmas.lean:353-354` `ai_principal_typing`, `RETURN` case | `typing_lemmas.v:433-437` (`ai_principal_typing`, `admininstr_RETURN` case) | Lean is **missing a conjunct**: Rocq's case has 3 conjuncts (`v_ft = ...`, `context_RETURN = Some ...`, **and** `Instr_ok v_C RETURN ((t++t_lst):->t')`); Lean only has the first two. The dropped conjunct effectively supplies `wf_context v_C ∧ wf_instr RETURN`, which nothing else in the Lean case provides. | Add a third conjunct requiring `Instr_ok v_C instr.RETURN (mkFunctype (t1s ++ ts) t2s)` (or, more directly, `wf_context v_C ∧ wf_instr instr.RETURN`, which is what the extra `Instr_ok` premise reduces to here). |
| 4 | `TypingLemmas.lean:446-449` `ai_principal_typing`, `FRAME_` case | `typing_lemmas.v:614-619` (`ai_principal_typing`, `FRAME_` case) | Lean pattern-matches `admininstr.FRAME_ _ f admininstrs` — the arity argument `v_n` is **discarded via `_`** — and the case's conjunction has only 3 conjuncts. Rocq's case has a **4th conjunct** `v_n = |t|` (the frame's declared arity must match the result-type length). Lean cannot even state this constraint as currently written since `v_n` isn't bound. Note `LABEL_`'s sibling case (line 441-445) correctly binds and uses its analogous arity variable `n_` — this looks like a straightforward omission, not a deliberate choice. | Rename the pattern to bind the arity, e.g. `\| admininstr.FRAME_ v_n f admininstrs => ∃ (ts : List valtype) (c' : context), v_ft = mkFunctype [] ts ∧ Frame_ok v_S f c' ∧ Expr_ok2 v_S {c' with RETURN := some (list.mk_list ts)} admininstrs (list.mk_list ts) ∧ ts.length = v_n` |
| 5 | `TypingLemmas.lean:418-421` `ai_principal_typing`, `STORE`-packed case | `typing_lemmas.v:556-568` (`ai_principal_typing`, `admininstr_STORE` cases) | Content genuinely diverges, but **likely in Lean's favor**: Lean's packed-`STORE` case requires `nt = numtype_Inn inntype`, so it's vacuously `False` for `F32`/`F64` (packed float stores excluded). Current Rocq's F32/F64 exclusion arms are **commented out** (`typing_lemmas.v:562-563`), so Rocq's *current* `ai_principal_typing` text no longer excludes packed float stores. However Rocq's own `Instr_ok`'s `store_pack` constructor (`wasm.v:15176-15183`) is typed `(v_Inn : Inn)`, which can **never** be instantiated at F32/F64 — so `Instr_ok` itself still forbids packed float stores. This makes current Rocq's `ai_principal_typing` internally **inconsistent with its own `Instr_ok`** for this case, while Lean's (stricter) reading is the one that actually agrees with `Instr_ok`. | **No Lean change recommended.** This is very likely a live upstream Rocq bug/WIP-leftover (commented-out exclusion arms), not a Lean porting mistake — Lean's own doc comment already flags this as unresolved; this audit confirms which side is right. Worth reporting upstream rather than "fixing" Lean to match. |
| 6 | `TypePreservation.lean:77-81` `store_extension_reduce` | `type_preservation.v:437-444` `store_extension_reduce` | Lean is **missing the first hypothesis** `wf_config (config.mk_config (state.mk_state s f) ais)`. Rocq's signature has 6 hypotheses (`wf_config`, `Step`, `Moduleinst_ok`, `Instrs_ok2`, `inst_match`, `Store_ok`); Lean has only the last 5. `wf_config` exists as a real predicate in `wasm2.0.lean:11029`. | Add `wf_config (config.mk_config (state.mk_state s f) ais) →` as the first hypothesis. |
| 7 | `TypePreservation.lean:95-100` `t_read_preservation` | `type_preservation.v:1661-1669` `t_read_preservation` | Same class of bug as #6: Lean is missing the first hypothesis `wf_config (config.mk_config (state.mk_state v_s v_f) v_ais)` that Rocq has. | Add `wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →` as the first hypothesis. |
| 8 | `TypePreservation.lean:105-109` `step_moduleinst` | `type_preservation.v:3120-3128` `step_moduleinst` | Same class of bug again: missing first hypothesis `wf_config (config.mk_config (state.mk_state v_s v_f) v_ais)`. | Add `wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →` as the first hypothesis. |
| 9 | `TypePreservation.lean:118-124` `t_preservation_type` | `type_preservation.v:3137-3148` `t_preservation_type` | Same class of bug again: missing first hypothesis `wf_config (config.mk_config (state.mk_state v_s v_f) v_ais)`. This is the lemma the file's own doc comment calls "the central preservation lemma for the whole `Step` relation" — high-value fix. | Add `wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →` as the first hypothesis. |
| 10 | `ExtensionLemmas.lean:155-158` `s_invert_mems` | `extension_lemmas.v:106-116` `s_invert_mems` | Lean **hard-codes** the memory's declared-maximum field as always present: `... (some (uN.mk_uN v_m)) ...`. Rocq's `v_m : Option N` is a genuine option (`option_map (fun m => mk_uN m) v_m`), and the final `2^16` cap conjunct is scoped to `option_to_list v_m` (vacuous when no max is declared). Lean's version silently excludes memories with no declared maximum. | Existentially bind `v_m : Option Nat` instead of `Nat`, and rewrite the type/cap conjuncts to route through `v_m.map uN.mk_uN` and `Forall (...) v_m.toList` (or equivalent), matching Rocq's `option_map`/`option_to_list` shape. |
| 11 | `ExtensionLemmas.lean:161-164` `s_invert_tables` | `extension_lemmas.v:175-187` `s_invert_tables` | Same class of bug as #10: Lean hard-codes the table's declared-maximum as `some (uN.mk_uN v_m)`; Rocq's `v_m : Option N` via `option_map` is genuinely optional. | Same fix pattern as #10, applied to `s_invert_tables`. |
| 12 | `ExtensionLemmas.lean:547-555` `memory_grow_mem_extension` | `extension_lemmas.v:1753-1768` `memory_grow_mem_extension` | Same class of bug again, on **both** the pre- and post-grow memtype: Lean hard-codes `some (uN.mk_uN v_j)`; Rocq's `v_j_opt : Option N` is generic (the max, if any, is carried through unchanged by `memory.grow` and the bound check `Forall (fun v_j => v_i + v_n ≤ v_j) v_j_opt` is vacuous when there is none). Lean's version cannot express growing a memory that has no declared maximum. | Existentially bind `v_j : Option Nat`, thread it through both the precondition and the postcondition memtype literal, and restate the bound check as `Forall (fun j => v_i + v_n ≤ j) v_j` (or equivalent). Note: `table_grow_table_extension`/`construct_tableinsts_grow`/`construct_meminsts_grow` in the same file already do this correctly with a genuine `Option uN`/`Option u32` parameter — this lemma is the outlier. |

All 12 are new findings (not previously called out in any in-file doc comment), **except #5**,
which the `ai_principal_typing` doc comment already flags as an open/unresolved discrepancy —
this audit resolves which side is authoritative (Lean, not current Rocq).

---

## Stale / orphaned Rocq citations (name no longer exists upstream — informational only)

These are Lean doc-comments citing a Rocq declaration name that no longer exists anywhere in
the current `test-rocq/theories/`. In every case checked, the underlying *mathematical
content* is still true (either provable directly, or derivable by combining current
surviving lemmas) — so these are **not** flagged as mismatches per the task's rubric, but the
citations are dead and can't be re-verified against a live target. Most predate the recent
resync (they trace to a large `nat`→`N` refactor commit `72eaba0b4`, well before
`rocq-backend-proof-final`).

**`HelperLemmas.lean`** (19 orphaned; all in the `helper_lemmas.v` section, lines ~60-348):
`leadd`, `list_update_func_split`, `list_update_func_split_strong`, `length_app_lt`,
`Forall2_nth` (+ `Forall2_nth2`) — content now split across surviving `Forall2_seq_size` +
`Forall2_size`, jointly equivalent but no single current lemma matches — `Forall2_lookup` (+
`Forall2_lookup2`, same situation as `Forall2_nth`), `lookup_list_update_func`,
`Forall2_forall2`, `Forall2_forall2weak`/`weak2`/`weak3`/`weak4`, `Forall2_list_update_func`
(the `α→α` direction only — its `β→β` sibling `Forall2_list_update_func2` correctly survives
and is separately ported), `Forall2_list_update`, `Forall2_list_update2`,
`Forall2_list_update_both`, `add_false`, `concat_cancel_last_n` (content verified identical to
the surviving `size_eq_cat`, already noted as such in Lean's own doc comment), `ltsize`.

**`TypePreservation.lean`** (1 orphaned): `num_default_is_well_formed`
(`TypePreservation.lean:45`) cites `type_preservation.v:28`, but the Rocq lemma there is
**entirely commented out** (`type_preservation.v:74-84`), not merely `Admitted`. This also
means the file's own header claim ("of the 13 declarations, only 3 lemmas are `Admitted`...
everything else... is fully `Qed`-proved in Rocq") is **inaccurate** for this declaration — it
isn't even stated in current Rocq, let alone `Qed`'d.

---

## Declarations skipped (out of scope, by design)

- **SIMD/vector**: `VCONST` case of `ai_principal_typing`, the `_ => True` catch-all covering
  `VVUNOP`/`VVBINOP`/`VVTERNOP`/`VVTESTOP`/`VUNOP`/`VBINOP`/`VTESTOP`/`VRELOP`/`VSHIFTOP`/
  `VBITMASK`/`VSWIZZLE`/`VSHUFFLE`/`VSPLAT`/`VEXTRACT_LANE`/`VREPLACE_LANE`/`VEXTUNOP`/
  `VEXTBINOP`/`VNARROW`/`VCVTOP`/`VLOAD`/`VLOAD_LANE`/`VSTORE`/`VSTORE_LANE` (`TypingLemmas.lean`);
  `vbytes_len'`, `vbytes_inv`, `lanes_len` axioms (`HelperLemmas.lean`). Not checked, per
  instructions.
- **`type_progress.v`**: entirely out of scope — no `TypeProgress.lean` exists in this
  project, 0 declarations checked or skipped from it (nothing to skip).
- **Non-cited plumbing/scaffolding declarations** (no "Rocq `<file>.v` `<name>`" doc-comment,
  so not audit targets per the task's own scoping rule): e.g. `instrs_ok_nil_sub_gen`,
  `instrs_ok_cons_gen`, `ais_ok_cons_gen`, `instrs_single_typing_inversion_gen`,
  `ais_single_typing_inversion'_gen` (`TypingLemmas.lean`); `forall_range_lt`,
  `forall_range_refl`, `forall_range_refl_noWf`, `to_mathlib_forall₂`, `from_mathlib_forall₂`
  (`HelperLemmas.lean`/`ExtensionLemmas.lean`); `forall2_valtype_sub_refl`,
  `forall2_valtype_sub_trans` (`Subtyping.lean`); `wf_admininstr_ref`, `wf_instr_admininstr`
  (`TypingLemmas.lean`, explicitly marked "Helper", no Rocq citation).
- **Already-known/self-documented deviations, re-verified but not re-flagged** (task rubric:
  don't flag documented deliberate representational choices): `Vals_ok`'s length-strengthening
  and its downstream use in `Vals_ok_non_bot`/`ais_vals_typing_inversion`/`construct_ais_vals`
  (`TypingLemmas.lean`); `construct_meminsts_grow`'s already-flagged hard-coded-`Option`
  parameter (`ExtensionLemmas.lean`, same bug class as findings #10-12 above, but this one
  instance was already caught and documented); `Val_ok_store`/`funcinst_same` orphaned
  citations (`ExtensionLemmas.lean`, already self-flagged as "not found... flagged, not
  removed"); the pervasive `Nat`-for-`Rocq`-`N`/`Q` and zip-based-`Forall₂`-for-inductive-
  `Forall2` conventions used project-wide.

## Files audited, fully clean

- **`Subtyping.lean`** (46 declarations, 0 sorry): every cited declaration checked
  hypothesis-by-hypothesis against `subtyping.v`. **0 mismatches, 0 orphaned citations.**
  Line numbers have drifted from the cited ones (file content shifted) but every statement's
  content matches exactly.
- **`TypePreservationPure.lean`** (30 declarations): every cited declaration checked against
  `type_preservation_pure.v`, including the previously-fixed
  `Step_pure__testop_preserves`/`Step_pure__relop_preserves` `wf_admininstr` hypotheses
  (confirmed present and correctly positioned). **0 mismatches, 0 orphaned citations.**

---

## Safety check

```
$ bash /home/zhengyew/spectec/spectec/src/test-lean-claude/claude-logging/safety-checks/check.sh
```

Ran at `20260930T145632Z`. The "Any changes outside `spectec/src/test-lean-claude/`" section
listed a large number of files (`spectec/test-lean/todaywasm*.lean`,
`spectec/wasm{1,2,3}.0*_ast_*.il` intermediate-pass dumps, `spectec/diegowasm*.lean`,
`spectec/check_wasm2.0.*`, `spectec/test-rocq/_opam/`, `specification/bleh/`, etc.) — **all of
these are pre-existing untracked/modified scratch and build-artifact files from before this
session started**, confirmed via `find ... -newermt '-30 minutes'` returning zero matches
against a sample of them (none touched in the last 30 minutes). This session's tool calls
outside `spectec/src/test-lean-claude/` were exclusively `Read` and read-only `Bash`
(`grep`/`git show`/`git log`/`git diff`, all non-mutating). The only file this session wrote
anywhere is this report itself, at
`spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle13/user_requested_documents/signature_audit_v1.md`
— inside the permitted directory. **No modifications outside `spectec/src/test-lean-claude/`
are attributable to this session.**
