# Reply to mid-turn input 4 (verbatim)

Yes. Here is everything, grouped by what needs your attention.

**Needs your decision (upstream; I have not touched them)**
1. **No `$invoke` configuration is ever `Config_ok`.** SpecTec's `middlend/sideconditions.ml` hoists a
   `|addrs| > 0` premise out of an iteration in `Moduleinst_ok`. As a result, the empty module instance
   that `fun_invoke` builds can never be typed. This affects Lean, Rocq and Isabelle alike.
   Preservation and progress therefore say nothing about the very first configuration of an
   invocation. They do apply from the callee's frame onward.
2. **`Globaltype_ok` admits only mutable globals** in all three backends; the spec says `MUT? t`.
   Stores with immutable globals are never `Store_ok`.
3. **Progress is false in two cases, in Rocq as in Lean:**
   - `VLOAD (SHAPE 64 X 1)`;
   - `VCVTOP F32→I16 TRUNC_SAT … ZERO`.

   The Lean model now *proves* both counterexamples. Those two subcases stay `sorry`, as Rocq
   `admit`s them. The fix is on the spec side.
4. **A spec typo, copied faithfully by every backend:** `vstore_lane-oob` adds `N` bits where it
   should add `N/8` bytes. It does not affect preservation or progress.

**Errors found and fixed**
- Two ported axioms, `ibytes_len'` and `ibytes_len''`, were **inconsistent**: each derived `False`.
  They misread Rocq's `|x| = q`, which Rocq floors. I restated them with `rat_to_nat`, and fixed
  `ibytes_inv`'s premise the same way. Nothing had used them, and preservation's axioms are
  unchanged.
- Four unused `s_invert_*` lemmas were **vacuous** under the zip-based `Forall₂`. They now carry the
  length.
- **Tooling problems, none of which reached the Lean code:**
  - The usage limit killed the first wave of audit agents. I relaunched more economically, with
    pre-extracted side-by-side signatures and at most 3 agents at a time.
  - Concurrent safety checks raced on a one-second filename, which made one check falsely report a
    difference. I rewrote the helper script to use unique filenames; every check has verified clean.
  - Two of my merge scripts had bugs: one regex swallowed newlines, and one read a stale chunk.
    Validation caught both before anything reached the repo.

**Design choices worth a look**
1. `TypeProgress.lean` imports `TypePreservation`, although Rocq's progress file doesn't import the
   preservation files. This lets it reuse Lean-only helpers.
2. Rocq proves `t_progress_be`/`t_progress_e` with one induction each. I split them into **90 case
   lemmas** whose statements were generated mechanically from Lean's own recursors. The two
   theorems are each one recursor application, and the cases can be proved and checked separately.
3. Where Lean's zip-based `Forall₂` would make a Rocq statement false or vacuous, I added a length
   premise or conjunct (5 progress lemmas). Two degenerate lemmas are NOT PORTED (`Forall2_size_eq`,
   `Forall2_seq_size`). Smaller choices:
   - `const_es_exists` uses `∃` instead of Rocq's `sig`;
   - the two decidability lemmas became `def … : Decidable …`.

   All of this is listed in `progress_port_deviations.md`.
4. I added the 12 progress-only axioms of `axioms.v`, with a consistency argument.
5. I renamed one Lean-only preservation helper, `wf_config_frame` → `wf_config_wf_frame`, so the Rocq
   progress lemma of that name keeps its name.
6. **Process choices:**
   - Sonnet proved the 188 small helper lemmas; Opus handles the instruction cases.
   - Proofs are validated in a scratch copy and merged into the repo only at the end, so modules
     aren't rebuilt under the running agents. Recovery checkpoints are in `bundle20/checkpoints/`.

**Status:** 249/280 progress targets are proved and compile together, with no failures so far. 11
case batches remain (31 instruction cases), and I'll keep going unless you say otherwise.
