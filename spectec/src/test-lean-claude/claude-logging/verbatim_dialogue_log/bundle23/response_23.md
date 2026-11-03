# Response 23 (verbatim)

The final reply of the bundle23 turn: the answer to mid-turn inputs 4-5 (the Isabelle upstream check).
Earlier replies within the turn are in `response_23_midturn2_status.md` and
`response_23_after_interrupt.md`.

---

Upstream has the same `fzero_is_wf` problem. It has the same length change in the generated text, but there it does no harm; the length problem is Lean-only.

I checked the branch tip `f46398ece` (2026-10-29, "regen thy file with side conditions added to funcs") against its previous version `53dbd75`. It's a comparison of the source text only; I didn't run Isabelle.

**`fzero_is_wf` is false upstream too**
- The lemma is the same: `"(ret_val = (fzero v_N)) ⟹ (wf_fN v_N ret_val)"`, with no premise on `N`, left as `sorry`.
- The definitions match the new Lean model:
  - `fun_M` and `fun_E` are relations that need `signif N ≠ None` and `expon N ≠ None`;
  - `wf_fNmag … (SUBNORM m)` needs both;
  - `wf_fN N (POS x)` needs `wf_fNmag N x`.
- So `wf_fN 0 (fzero 0)` is false there for the same reason. The Lean counterexample carries over unchanged.
- Upstream's own proof of `wf_fN N (fzero M)`, in `Wf_preservation.thy`, was written for the previous output, where `fun_M` was a function. It won't work against the new definitions.

**Length conditions: same change, but harmless in Isabelle**
- Upstream lost the same premises. The previous output had 283 premises of the form `length var_k_lst = …`, the same number as your old Lean model. The current one has 0. `fun_vbinop_` case 8 (MIN) matches the new Lean rule premise for premise.
- Isabelle doesn't need them. It relates those lists with HOL's built-in `list_all2` and the file's own inductive `list_all3`/`list_all4`, and all of these force equal lengths. So in Isabelle:
  - `vunop` (ABS), `vbinop`, `vcvtop`, `Step_pure` `vshiftop`, `utf8` and the `allocmodule` exports still determine their result lists;
  - the STORE case still enforces the packed-size bound, because `list_all2` over `option_to_list` makes the two options both `Some` or both `None`.
- What breaks Lean is that its `Forall₂`/`Forall₃` are zip-based and don't check lengths. Making them check lengths, as `list_all2` and Rocq's `Forall2` do, would match Lean to both other backends and remove the four length gaps. The other fix is to have the generator emit the 283 premises again.

**Upstream hasn't redone its Isabelle proofs for the new output yet.** `Wf_preservation.thy` was last changed at 04:36 that day, and the regeneration came at 11:13. It still uses `vvunop_underscore`, `vvbinop_underscore` and `sizenn`, which the new output no longer defines. All 90 wf lemmas in the reference output are `sorry`.

**Where things stand**
- Both background workflows are stopped and no Lean process of mine is running.
- The repo is untouched: `wasm2.0.lean` is still your regenerated file.
- All work is saved outside the repo, in `/home/zhengyew/.claude/projects/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/saved_work_bundle23/`, which has a `README.md` index. It contains:
  - the merged candidate (85 of 90 proved, compiles);
  - each agent's files and the counterexamples;
  - the audit, the downstream-impact cascade results (not yet read) and the staged bundle23 logs.
- The downloaded Isabelle files are in `scratchpad/isabelle_dl/` inside that folder.

Nothing else is running; I'll wait for your next instruction.
