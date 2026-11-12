# Proof prioritization — update v7 (bundle18)

Written for: a future Claude session (primary audience) and the user.
Supersedes `bundle16/user_requested_documents/proof_prioritization_v6.md` (kept untouched).
v6's remaining list (the 5 genuine `TypePreservationPure` proofs, the SIMD gaps, and the
"deliberate gaps mirroring Rocq `Admitted`") is **done**: bundle17 found that upstream has
no `Admitted` preservation lemmas, and bundle18 proved everything except the items below.

## Direct answer to "what's left?"

18 `sorry` declarations project-wide (26 at bundle18's start):

| # | Item | Kind | Action |
|---|---|---|---|
| 1 | `TypePreservation.t_read_preservation` | **genuine proof**, about 47 small cases | Do next. Full plan in `bundle18/.../insights_for_next_turn.md` §3. |
| 2 | `TypePreservation.rat_to_nat_natCast` | **unprovable as the model stands** (`rat_to_nat` is `opaque`) | User decision: give `rat_to_nat` a real definition in the Lean backend (e.g. `r.floor.toNat`), then prove it in one line. |
| 3-17 | 15 `HelperLemmas` lemmas (`list_update_func_split*`, `Forall2_*`, `lookup_list_update_func`) | dead (rule 1); mostly false for the zip-based `Forall₂` | Ask the user, then delete, or add `hlen` premises if ever needed. |
| 18 | `ExtensionLemmas.Val_ok_store` | dead (rule 1); no current upstream counterpart | Same as above. |

Plus generated-file `sorry`s that the preservation chain uses (not ours to prove; see
`for-claude/is_wf_theorems.md`):
- `Step_pure_is_wf`: believed true, `Qed` upstream.
- `Step_is_wf`, `Step_read_is_wf`: **false** in one corner case, see below.
- `nbytes__is_wf`, `ibytes__is_wf`, `vbytes__is_wf`, `wrap___is_wf`: opaque byte functions,
  believed true.

## Priority order for the next session

1. **`t_read_preservation`**, in this order (cheap to expensive). Leave a `sorry` per
   unfinished case and keep the build green:
   - the 15 trap cases, then the 6 zero cases;
   - single-constant results (`table_size`, `memory_size`, `load_num_val`, `load_pack_val`)
     and the 5 vector-load value cases (two lemmas already exist);
   - `local_get` (needs a decision on the locals-length deviation, see insights §3),
     `global_get` (use `lookup_global`), `table_get_val`, `ref_func`;
   - the 8 sequence cases (`*_fill_succ`, `*_copy_le/gt`, `*_init_succ`): write
     `instrtype_sub_prefix` first;
   - `block`, `loop`; then `call`, `call_indirect_call`;
   - `call_addr` last (the biggest).
2. **Doc-comment cleanup** in `TypePreservation.lean` (stale "Admitted" claims, listed in
   insights §5). Cheap and prevents confusion.
3. **Progress** (`type_progress.v`), as planned in bundle16's v6.

## Blocking or "unprovable/false" items (reported to the user, bundle18)

- **`rat_to_nat` opaque**: item 2 above.
- **Corner-case falsity**: on a memory of exactly 2^16 pages, `memory.fill`/`copy`/`init`
  with `i = 2^32 - 1`, `n = 1` push `CONST I32 2^32`, which is not well-formed. So
  `Step_read_is_wf`, `Step_is_wf`, `t_read_preservation` and `t_preservation` are false
  there, in Rocq too. This is a spec issue. Proofs should take wf of the reduct from
  `Step_read_is_wf` / `Step_is_wf`, exactly as Rocq does.
