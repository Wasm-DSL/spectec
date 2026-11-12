# Proof dependencies — consolidated update v6 (bundle18)

Written for: a future Claude session (primary audience). Supersedes
`bundle16/user_requested_documents/proof_dependencies_v5.md` (kept untouched). The
file-level graph is unchanged. What changed is the lemma-level picture around the top-level
theorem, and the measured `sorry` dependencies.

## File-level graph (unchanged)

```
                              ┌── TypePreservationPure ─┐
HelperLemmas → Subtyping → TypingLemmas ─┤                         ├→ TypePreservation
                              └── ExtensionLemmas ──────┘
(all import the generated wasm2.0.lean; HelperLemmas also imports Mathlib.Tactic)
```

## Lemma-level: what `t_preservation` rests on (bundle18)

```
t_preservation
├── store_extension_reduce            (PROVED bundle18; no Step_is_wf)
│   └── store_extension_reduce_aux (induction on Step)
│       ├── global_set_store_ok / table_set_store_ok / table_grow_store_ok
│       │   elem_drop_store_ok / data_drop_store_ok
│       │     └── minst_invert_*, Store_ok_parts/of_parts, Extend_store_of_parts,
│       │         *_extension (ExtensionLemmas), construct_* (ExtensionLemmas)
│       ├── with_mem_store_ok → mem_store_extension (PROVED) ← splice_eq_list_slice_update
│       │     + nbytes__is_wf / ibytes__is_wf / vbytes__is_wf / wrap___is_wf (generated)
│       └── memory_grow_store_ok → construct_meminsts_grow (generalized), memory_grow_mem_extension,
│             rat_to_nat_natCast (UNPROVABLE: opaque rat_to_nat)
├── t_preservation_type (PROVED, via t_preservation_type_aux)
│   ├── Step_is_wf (generated; FALSE in a corner case)
│   ├── t_pure_preservation (PROVED) ── Step_pure_is_wf (generated; believed true)
│   └── t_read_preservation (SORRY — the remaining work)
├── t_preservation_vs_type, reduce_inst_unchanged, Extend_store_moduleinst (PROVED)
└── Step_is_wf (again, for the post-config's wf)
```

## Measured transitive `sorry` dependencies (end of bundle18)

From the `#sorry_deps` meta-program (code in `insights_for_next_turn.md` §6):

| Theorem | Depends on (declarations whose body is `sorry`) |
|---|---|
| `store_extension_reduce` | `rat_to_nat_natCast`, `ibytes__is_wf`, `nbytes__is_wf`, `vbytes__is_wf`, `wrap___is_wf` |
| `t_pure_preservation` | `Step_pure_is_wf` |
| `t_preservation_type` | `Step_is_wf`, `Step_pure_is_wf`, `t_read_preservation` |
| `t_preservation` | all of the above (8 declarations) |

No custom `axiom` (e.g. `HelperLemmas.nbytes_len`) is on the preservation path
(`#print axioms TLC.t_preservation` = `propext, sorryAx, Classical.choice, Quot.sound`).

## What `t_read_preservation` will need (inputs already available)

`Step_read_is_wf` (generated) for the reduct's wf; `ainstrs_ok_context_store_wf`;
`construct_ais_trap`; `ais_empty_typing`; `ais_args{1,2,3}_typing` and the `inv_*` operator
inversions (`TypePreservation.lean`, shared-helpers section); `construct_ai_const_I32`,
`construct_ai_val`, `construct_ai_ref`, `construct_ais_compose`, `construct_ais_subtyping`,
`construct_ais_vals`, `ais_vals_typing_inversion`, `construct_instrs_from_ais`
(`TypingLemmas`); `bt_inversion`, `minst_invert_*`, `lookup_global`, `s_invert_*`,
`Externaddr_invert_*`, `tableinst_ok_invert` (`ExtensionLemmas`);
`Step_read__vload_preserves`, `Step_read__vload_lane_preserves`, `externtype_table_sub_inv`,
`getElem?_eq_some_bang`, `Moduleinst_ok_lengths` (`TypePreservation`).
Missing, to be written: `instrtype_sub_prefix` (prefix weakening), a general-`nt` constant
constructor, the remaining `inv_*` operator inversions (`TABLE_FILL`, `TABLE_COPY`,
`TABLE_INIT`, `MEMORY_FILL`, `MEMORY_COPY`, `MEMORY_INIT`, `LOAD`, `TABLE_GET`, …), and
`Val_ok` of `default_` values (for `call_addr`).
