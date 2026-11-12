# Proof dependencies — consolidated update v5 (bundle16)

Written for: a future Claude session (primary audience). Supersedes
`bundle15/user_requested_documents/proof_dependencies_v4.md` as the reference to
read going forward (v4 kept, untouched, as historical record). The dependency
*shape* is unchanged; what changed is that almost all of it is now discharged.

## File-level dependency graph (unchanged in shape since bundle3)

```
                              ┌── TypePreservationPure → TypePreservation
HelperLemmas → Subtyping → TypingLemmas ─┤
                              └── ExtensionLemmas ──┘   (Extension feeds both
                                                          Preservation and,
                                                          separately, Progress)
                                        │
                                        └── TypeProgress   (needs TypingLemmas +
                                                             ExtensionLemmas +
                                                             Subtyping + Axioms,
                                                             NOT Preservation;
                                                             not started, out of
                                                             current scope)
```

## Within-file status, ground truth as of bundle16 (direct grep, 2026-10-02)

| File | Decls | Still `sorry` | Of which *genuine* | Status |
|---|---:|---:|---:|---|
| `HelperLemmas.lean` | 62 | 15 | 0 | Unchanged count since bundle15, but 6 new "Template B" lemmas were added. All 15 remaining are the dead `nat→N`-refactor cluster, confirmed again unreferenced by any live signature. Several are *unprovable as stated* (they derive a length equality from the zip-based `Forall₂`); their usable variants now exist under different names. Not blocking anything. |
| `Subtyping.lean` | 47 | 0 | 0 | Fully done since bundle10. |
| `TypingLemmas.lean` | 81 | 0 | 0 | Fully done since bundle10. |
| `TypePreservationPure.lean` | 30 | 7 | 5 | Down from 10. The `select` cluster (`_preserves_helper`, `_true_`, `_false_`) landed this bundle. 5 genuine remain (`br_zero`, `br_succ`, `br_table_lt`, `br_table_ge`, `return_label`) + 2 deliberate permanent gaps (`return_frame_preserves`, `t_pure_preservation` — both Rocq-`Admitted`). |
| `ExtensionLemmas.lean` | 129 | 2 | **0** | Was 76 at bundle15 start, 50 at bundle15 end, **2 now**. Both remaining are signature defects, not proof gaps — see `extension_lemmas_triage_v2.md`. 37 new helper lemmas were added (Templates B and C plus bare-variable inverters). |
| `TypePreservation.lean` | 17 | 3 | **0** | Was 12 at bundle15 start, 8 at bundle15 end, 4 after `step_moduleinst`/`t_preservation_vs_type`, **3 now**. All three remaining are the deliberate Rocq-`Admitted` SIMD gaps (`store_extension_reduce`, `t_read_preservation`, `t_preservation_type`). **`t_preservation` — the top-level theorem — is proved.** |

**Total across the project: 366 declarations, 27 still `sorry`**, of which
**5 are genuine remaining work** (all in `TypePreservationPure.lean`),
**5 are deliberate permanent gaps mirroring Rocq `Admitted`s**
(`TypePreservationPure`: `return_frame_preserves`, `t_pure_preservation`;
`TypePreservation`: `store_extension_reduce`, `t_read_preservation`,
`t_preservation_type`), **2 are unprovable-as-stated / dropped-upstream
signatures** in `ExtensionLemmas.lean`, and **15 are the dead `HelperLemmas`
cluster**. (Was 83 at bundle16's start.)

## Dependency closure of the top-level theorem

`t_preservation` (proved) composes exactly:

```
t_preservation
├── store_extension_reduce            ← DELIBERATE GAP (Rocq Admitted, SIMD)
├── reduce_inst_unchanged             ← proved (bundle16)
├── Extend_store_moduleinst           ← proved (bundle16)
├── t_preservation_vs_type            ← proved (bundle16)
│   └── t_preservation_vs_type'       ← proved (bundle16)
│       └── Extend_store_vals         ← proved (bundle16)
├── t_preservation_type               ← DELIBERATE GAP (Rocq Admitted, SIMD)
│   ├── t_pure_preservation           ← DELIBERATE GAP (Rocq Admitted)
│   ├── t_read_preservation           ← DELIBERATE GAP (Rocq Admitted, SIMD)
│   └── Extend_store_ais              ← proved (bundle16)
├── Step_is_wf                        ← `sorry` in wasm2.0.lean (GENERATED FILE,
│                                        outside the editable directory; a
│                                        pre-existing upstream gap, not ours)
└── inst_t_context_local_empty        ← proved (bundle15)
```

So: **every lemma on the critical path that is provable *and* inside the
editable directory is now proved.** What remains between here and an
unconditional `t_preservation` is (a) the 3 Rocq-`Admitted` SIMD gaps, (b) the
5 genuine `TypePreservationPure` lemmas that feed `t_pure_preservation`, and
(c) `Step_is_wf`, which lives in the generated `wasm2.0.lean` and is therefore
out of bounds.

## What's now unblocked and ready

- **Nothing in `ExtensionLemmas.lean` is blocked.** Everything it can supply,
  it supplies.
- **`TypePreservationPure.lean`'s 5 genuine targets are the only remaining
  genuine work**, and they are mutually independent (none depends on another).
  Each needs the same typing-inversion + subtyping-composition machinery, which
  is fully present — see `proof_prioritization_v6.md` for per-lemma routes.
- `type_progress.v` (not started, out of current scope) — unchanged; note that
  it depends on `ExtensionLemmas.lean`, which is now essentially complete, so
  that avenue is now much cheaper than it was.
