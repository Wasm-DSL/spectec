# Response 25 (verbatim)

---

I added a second `Sideconditions` entry to `all_passes`, directly after `DefToRel`, in a throwaway copy of the generator. Your repository's `main.ml` was not touched.

**1. Copy the generator into the scratchpad.** I copied `spectec/src` (without `test-lean-claude` and `temp_zy_dev`), `dune-project` and `spec` to `/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/expB/spectec`. I built it there with `dune build --root . src/exe-spectec/main.exe`, using your opam switch and with the dune cache disabled.

**2. Check the copy.** The unmodified copy, run as `main.exe ../specification/wasm-2.0/*.spectec --lean -o gen_unmodified.lean`, reproduced your regenerated `wasm2.0.lean` byte for byte. So the copy matches your setup.

**3. Make the one-line change.** This is the only difference from your `main.ml`:
```ocaml
let all_passes = [
  ...
  Sub;
  Sideconditions;
  DefToRel;
  Sideconditions; (* EXPERIMENT: again, for the iterations DefToRel introduces *)
  AliasDemut;
  ...
```
Then I rebuilt and regenerated into `/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/expB/gen_twice.lean`.

**Why one list entry is enough:**
- The pipeline loops over `all_passes` and runs every entry whose pass has been switched on. Which passes are on is recorded as a set (`selected_passes`), with no limit of one run per pass. The `Rocq | Lean` branch already switches on `Sideconditions`, so it runs at both positions.
- The second run gets the same `~on_defs:!sideconditions_on_defs` (true), because it goes through the same `run_pass` case.
- It needs no record of what already has side conditions. The pass removes structural duplicates within each rule (`reduce_prems`, which compares with `Il.Eq.eq_prem` and ignores positions and notes). Everything the first run added is therefore dropped as a duplicate, and only premises for `DefToRel`'s new iterations survive.

**Side effects of the hack, if you adopt it as is:**
- `--rocq` gets the extra run too, since it shares the branch.
- `pass_argspec` is mapped over `all_passes`, so a duplicate `--sideconditions` flag appears in the help text. It still parses and generation worked.
- The `--print-all-il-to` dumps are numbered differently after `DefToRel`, because `pass_count` counts the extra run.

A cleaner version would be a separate pass entry, such as `SideconditionsPost` sharing the same transform, or running `Sideconditions` a second time inside the `DefToRel` case.

**How I checked the result:**
- A Python script compared each constructor's premises in `gen_twice.lean` against your regenerated file. That gave the counts I reported earlier: 284 length premises back, 0 duplicates, 0 premises lost, 100 constructors reordered.
- `gen_twice.lean` compiled with the serialized, memory-capped `lean`.
- The 85 merged proofs were then run against it: 81 compile unchanged.
