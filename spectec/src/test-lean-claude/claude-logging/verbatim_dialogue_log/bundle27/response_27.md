# Response 27 (verbatim)

---

Mostly yes. `todaywasm2.0_shouldwork` (byte-identical to yesterday's `_withoutwfopt.lean`) fixes both generator problems. Two issues remain: the `Step_read`/`Step` hand edit is still needed, and the four previously unprovable vector theorems still need their proofs finished. Everything was done on scratchpad copies; the repo is untouched.

| Earlier issue | In `shouldwork` | How I checked |
|---|---|---|
| **Missing length premises** (`DefToRel`'s new lists unconstrained) | Fixed | 285 `\|var_k_lst\| = …` premises (old model 283, regenerated model 0). Lists paired by `Forall₂`/`₃` with no length premise: 15 of 408, the same 15 as the run-twice model (old model 13; regenerated model 171). |
| **Four unprovable theorems** (`vunop__is_wf`, `vbinop__is_wf`, `vcvtop___is_wf`, `Step_pure_is_wf`'s `vshiftop` case) | The missing premise is back, e.g. `(List.length var_2_lst) = (List.length lane_1_lst)` on `fun_vunop_`'s ABS case | Their counterexamples relied on that premise being absent. The three vector theorems are still `sorry` (that work was stopped), so they are not proved yet. |
| **Packed-store size bound** (STORE in `wf_instr`) and **`fun_allocmodule` exports** | Fixed: their `↔ none` and length premises are back | Same counts |
| **`fzero_is_wf` false at `N = 0`** | Fixed: the theorem is gone and `fun_fzero` carries `wf_fN v_N …` as a premise | Generated `sorry`s: 89, down from 90 |
| **`Step_read_is_wf` / `Step_is_wf` false as generated** (2^32-entry table + `table.size`) | **Not fixed.** The signatures are still unedited; this isn't a pass-order issue | Read the signatures |
| **`disjoint_` wart**, and `fun_with_*` not checking the store address | Unchanged (minor) | — |

The file compiles on its own with 0 errors (about 16 s). Then I ported yesterday's merged proofs onto it with the same merge script, including the `Step_read` hand edit: 80 of 87 compile unchanged. The 7 failures are all small mechanical breaks:
- **4 binder renames from the second `Sideconditions` run:** `Step_pure_is_wf`, `iswf_store_I32_8`, `Step_read_is_wf`, `Step_is_wf`. These are the same 4 that failed on the run-twice model.
- **3 from `fzero` becoming a relation:**
  - `iswf_fzero_32` and `iswf_fzero_64` still call the deleted `fzero` function. They need restating over `fun_fzero`.
  - `default__is_wf` now has to invert `fun_default_` first.

So I think this is the right generator configuration. What's left is proof work in `wasm2.0.lean`:
1. Re-apply the `Store_ok` hand edit.
2. Fix the 7 broken proofs.
3. Finish the three vector theorems and close `Step_pure_is_wf`'s `hlen` gap using the restored length premises.

Before step 3 is done, I can't fully promise those four close, because the counterexamples no longer apply but the proofs haven't been written. Downstream, progress proofs will also need `fun_default_` and `fun_fzero` witnesses where they used to compute `default_`.

The results are in `/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/expC/` (`compile.log`, and `merged/compile.log` for the port).
