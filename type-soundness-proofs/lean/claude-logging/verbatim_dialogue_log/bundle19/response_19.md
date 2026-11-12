All 89 theorems in `wasm2.0.lean` that Rocq proves are now proved in Lean, and so is `t_read_preservation`. `TypePreservation.lean` has no `sorry` left. Preservation now rests only on 33 generated theorems that Rocq also leaves `Admitted`.

**`wasm2.0.lean`**
- 89 `*_is_wf` theorems are proved: every one whose counterpart in `wasm.v` is `Qed`.
- The 63 still `sorry` are exactly the 63 `*_is_wf` theorems `Admitted` in `wasm.v`. (Rocq's one other `Admitted`, `res_list_eq_dec`, is derived automatically in Lean.)
- The proofs use 54 helper lemmas in five blocks. Each block is marked "Hand-written helper lemmas … (bundle19; not generated)".

**Your three points**
1. **`rat_to_nat`:** your definition works. `rat_to_nat_natCast` is now one line (`by simp [rat_to_nat]`).
2. **Corner case:** left alone. `Step_read_is_wf` stays `sorry`.
3. **`Vals_ok`:** that worked, so I didn't need to add the length fact separately.
   - `t_read_preservation` now takes `Vals_ok v_s v_f.LOCALS v_C'.LOCALS` instead of the bare `Forall₂`.
   - It's a documented deviation, like `funcinst_same`'s `hlen`.
   - Its only caller already had the `Vals_ok`, so nothing else changed.

**Remaining `sorry`s for preservation**

I traced `t_preservation`'s dependencies transitively. It depends on 33 `sorry`s, and all 33 are `Admitted` in Rocq too:
- **`Step_read_is_wf`:** your issue 2.
- **32 theorems saying a numeric operation returns a well-formed value.** The operations are:
  - integer: `iand_`, `ior_`, `ixor_`, `iandnot_`, `inot_`, `ibitselect_`, `iclz_`, `ictz_`, `ipopcnt_`, `irev_`, `ishl_`, `ishr_`
  - conversion: `extend__`, `wrap__`, `convert__`, `demote__`, `promote__`, `reinterpret__`, `trunc__`, `trunc_sat__`
  - float: `fabs_`, `fneg_`, `fsqrt_`, `fceil_`, `ffloor_`, `ftrunc_`, `fnearest_`
  - vector and bytes: `lanes_`, `inv_lanes_`, `nbytes_`, `ibytes_`, `vbytes_`

These 32 can't be proved in Lean, because all of these functions are `opaque` in the generated file. That's the same situation `rat_to_nat` was in, with the same fix: generate real definitions. None of them is false: each holds if the opaque function returns 0, an empty list, `none`, or infinity for floats.

These 32 are newly on the dependency list. Until now, `t_pure_preservation` reached them only through `Step_pure_is_wf`'s own `sorry`. Now that `Step_pure_is_wf` is proved, 29 of them show up directly, because its proof uses them, as Rocq's does.

**Design decisions**
1. **`Step_read_is_wf` and `Step_is_wf` signatures.** I copied Rocq's hand-edit: both now sit after `Store_ok` and take a `Store_ok (fun_store z)` premise.
   - Without the premise, `Step_read_is_wf` would stay false even after your spec fix. `table.size` and `memory.size` need the store's size bounds.
   - `Step_is_wf` is proved. Its `read` case calls `Step_read_is_wf`.
2. **The proofs live in the generated file**, as in Rocq, so regenerating erases them.
   - `bundle19/user_requested_documents/wasm2.0_hand_edits.patch` re-applies them, and the README next to it has the steps.
   - I tested it on a copy of your generated file: `patch -p1` and `git apply` both reproduce the current file exactly.

There are no new blocking issues. One question from bundle18 is still open: can I delete the 16 unused `sorry`s (15 in `HelperLemmas`, plus `Val_ok_store`)?

**Safety and logging**
- `lake build` is clean (3005 jobs). The safety check shows nothing outside `test-lean-claude` changed relative to the baseline.
- The `bundle19` folder has the prompt, this response, the model info, and the patch with its README. `NOTES.md`, `SUMMARY.md` and `is_wf_theorems.md` are updated.
