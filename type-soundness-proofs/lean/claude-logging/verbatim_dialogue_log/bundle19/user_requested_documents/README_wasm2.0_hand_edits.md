# `wasm2.0_hand_edits.patch`: the bundle19 hand-edits to `wasm2.0.lean`

The bundle19 proofs live inside the generated `wasm2.0.lean`, the same way the Rocq proofs
live inside the generated `wasm.v`. Regenerating the file erases them. This patch lets you
put them back.

## What the patch contains

It is a unified diff from the file you generated for bundle19 (the one with the non-opaque
`rat_to_nat`; md5 `7d2167da7174a58377a7c6c43bd8cfc1`) to the current file. All changes are
inside `wasm2.0.lean`:

1. **89 proofs.** Each is a `sorry` replaced by a proof, one for every `*_is_wf` theorem
   whose Rocq counterpart in `wasm.v` is `Qed`. The other 63 `*_is_wf` theorems are
   `Admitted` in Rocq and stay `sorry` in Lean.
2. **Five helper-lemma blocks.** Each one starts with the comment
   `/-! Hand-written helper lemmas for the *_is_wf proofs below (bundle19; not generated). -/`
   and sits just before the first theorem that uses it: `fzero_is_wf`, `iadd__is_wf`,
   `vunop__is_wf`, `store_is_wf` and `Step_pure_is_wf`.
3. **`Step_read_is_wf` and `Step_is_wf` are moved and re-signed.** Both now sit after
   `inductive Store_ok` and take an extra `Store_ok (fun_store z)` premise. This copies the
   hand-edit in Rocq's `wasm.v`. Each carries a `Hand-edited (bundle19)` comment.
   - `Step_is_wf` is proved.
   - `Step_read_is_wf` stays `sorry`, as in Rocq. It is false in the
     memory.fill/copy/init `2^32` corner case (blocking issue 2).

## Re-applying after you regenerate

Run this from the repository root:

```sh
P=spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle19/user_requested_documents/wasm2.0_hand_edits.patch
patch -p1 --dry-run < "$P"   # check first
patch -p1 < "$P"
```

`git apply "$P"` works too. The patch has no blob hashes, so `git apply --3way` cannot
fall back to a three-way merge.

If the generator has changed text near a hunk, the hunk may be rejected. In that case:
- `patch -p1 --merge < "$P"` leaves conflict markers you can resolve by hand.
- Or apply it to a copy of the old generated file and merge it into the new one.

If a theorem's statement changes, its proof may need adjusting.

I tested the patch on a copy of the generated file. Both `patch -p1` and `git apply`
reproduce the current `wasm2.0.lean` byte for byte.

## A design choice for later

Keeping hand proofs in a generated file means re-applying them after every regeneration.
Rocq has the same issue. Two more durable options, if you want one:
- The backend leaves out (or marks) the theorems that are proved by hand, and the proofs
  live in a separate file.
- The backend emits these proofs itself, for the theorems it can.

Neither is needed now.
