# `wasm2.0_hand_edits.patch` (bundle21): the hand-edits to the generated `wasm2.0.lean`

Written for: you (the user) and future sessions, for the next time `wasm2.0.lean` is regenerated.
This supersedes `bundle19/user_requested_documents/wasm2.0_hand_edits.patch` (kept unchanged).

## What the patch is

A unified diff from the `wasm2.0.lean` you regenerated on 2026-10-15 (after merging upstream
`rocq-backend-proof` `6582b3a39` and spec commit `4cf9f29c5`; 14,698 lines, byte-identical to what
`_build/default/src/exe-spectec/main.exe <the 12 wasm-2.0 .spectec files> --lean -o …` produces
today) to the hand-edited file. All changes are inside `wasm2.0.lean`:

1. **The bundle19 hand-edits, re-applied.** The bundle19 patch applied to your regenerated file
   with no rejected hunk (3 hunks needed fuzz, only because source-location comments moved):
   - 89 proofs of `*_is_wf` theorems whose Rocq counterpart is `Qed`;
   - five helper-lemma blocks headed `Hand-written helper lemmas … (bundle19; not generated)`;
   - `Step_read_is_wf` and `Step_is_wf` moved after `inductive Store_ok` and given the extra
     `Store_ok (fun_store z)` premise, mirroring the hand-edit in Rocq's `wasm.v`.
2. **One bundle19 proof adjusted** to the new spec: `vshiftop__is_wf`. `$vshiftop_` now passes the
   shift amount reduced modulo the lane size, so its well-formedness is proved from `k % L < L < 2^L`
   instead of the old `u32` premise.
3. **New in bundle21: `Step_read_is_wf` is proved** (it is `Qed` in Rocq since `6582b3a39`), with a
   sixth helper-lemma block headed `Hand-written helper lemmas … (bundle21; not generated)` just
   before it.

After the patch, the only `sorry`s left in `wasm2.0.lean` are the 62 `*_is_wf` theorems about
functions that are `opaque` in Lean (`Axiom`s in Rocq), exactly Rocq's `Admitted` set minus
`res_list_eq_dec` (which Lean derives automatically).

## Re-applying after you regenerate

From the repository root:

```sh
P=spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/user_requested_documents/wasm2.0_hand_edits.patch
patch -p1 --dry-run < "$P"   # check first
patch -p1 < "$P"
```

`git apply "$P"` works too when nothing near a hunk changed. If the generator changed text near a
hunk, `patch` may need fuzz or reject the hunk; `patch -p1 --merge < "$P"` leaves conflict markers
to resolve by hand. If a theorem's statement changed, its proof may need adjusting (as happened to
`vshiftop__is_wf` this time).
