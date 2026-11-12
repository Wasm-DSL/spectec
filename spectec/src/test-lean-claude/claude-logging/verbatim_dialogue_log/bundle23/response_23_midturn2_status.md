# Interim status reply to mid-turn input 2 (verbatim)

Its last line was followed directly by tool calls (the round-2 relaunch).

---

Nothing in the repo has changed yet. All work is in a scratch copy, and the logs are staged in the scratchpad, because this turn only `wasm2.0.lean` may change.

**Done so far**
- **Read the log.** I read every prompt, response and model-info file of bundles 1–22, plus the key documents. I'm following the safety and logging rules.
- **Proofs: 85 of the 90 `sorry`s are proved** in a merged copy, which compiles with no errors.
  - Helpers sit directly above their first user and are marked `HELPER LEMMA CREATED BY CLAUDE`. A script checked the placement.
  - The hand edits to `Step_read_is_wf` and `Step_is_wf` are made as in `OLD_wasm2.0.lean`, and both are proved. Without the edits, both statements are false; I checked a counterexample in Lean.
- **No proof uses `Inhabited.default` values.** I checked this by re-running the kernel with every `Inhabited` instance made opaque. The same check finds 11 such theorems in the old model.

**Findings that need your decision**
1. **Length conditions are no longer generated.** Since `Sideconditions` now runs before `DefToRel`, the lists that `DefToRel` creates get no length premise. The old model had 283 such premises; the new one has none.
   - Lean's `Forall₂` is zip-based, so these relations now allow extra junk elements.
   - As a result, `vunop__is_wf`, `vbinop__is_wf`, `vcvtop___is_wf` and one case of `Step_pure_is_wf` cannot be proved as generated. I checked a counterexample witness for each in Lean.
   - Packed-store well-formedness no longer bounds the size, and module allocation can add junk exports.
   - Fix: emit those length premises again, or make `Forall₂`/`Forall₃` require equal lengths.
2. **`fzero_is_wf` is false.** `wf_fN 0 (fzero 0)` doesn't hold, because the old proof needed `Option.get! none = 0`. Fix: give it a premise on `N`.

**Left to do**
1. Restart the second round, which the restart cut off. It proves every case of the three vector theorems and leaves one `have hlen … := sorry` per affected case, as `Step_pure_is_wf` already has.
2. Final assembly and compile, then re-run the default-value and placement checks.
3. Write `wasm2.0.lean`, the only repo write, and run the check that nothing else changed.
4. Compile the other proof files against the new model to estimate the breakage.
5. Write the report. I'll ask whether to copy the staged logs into `claude-logging/`.

Continuing with step 1 now. I'm relaunching round 2 and telling the agents to pick up their own partial files:
