# Progress port: status at the end of bundle20

Written for: the user and future sessions. Companion to `progress_port_deviations.md` (which
lists every deviation from Rocq) and `preservation_audit_report.md`.

## Headline

**Progress (`TLC.t_progress`) is fully ported and proved, except for the same two subcases that
Rocq `admit`s.** Those two subcases are false as the spec stands.

```lean
theorem t_progress (s : store) (f : frame) (es : List admininstr) (ts : resulttype) :
    Config_ok (config.mk_config (state.mk_state s f) es) ts →
    terminal_form es ∨
      ∃ (s' : store) (f' : frame) (es' : List admininstr),
        Step (config.mk_config (state.mk_state s f) es) (config.mk_config (state.mk_state s' f') es')
```

This is Rocq `type_progress.v:6064` `t_progress`, and it is equivalent to Isabelle's `progress`
(`Progress.thy:1116`). `terminal_form es` means `const_list es = true ∨ es = [TRAP]`, and
`const_es_exists`/`v_to_e_const` show `const_list es` ⇔ `∃ vs, es = map admininstr_val vs`.

## Numbers

| | count |
|---|---|
| `TypeProgress.lean` | 8005 lines, 280 theorems, 23 defs |
| Rocq declarations covered | all 223 in `type_progress.v`. The NOT-PORTED ones are justified in place: 9 Ltacs, 2 Schemes, `instr_eqb`/`eqinstrP`, `length_size`, `Forall2_size_eq`. |
| proof targets (`sorry` bodies after the signature phase) | 280 |
| proved | **280** (100%) |
| remaining `sorry` tokens | **2**: the two known-false subcases below |
| declaration headers changed by the proof phase | 0 (all 301 headers byte-identical to the audited signatures; each proof was also checked with a `type_of% … = type_of% … := rfl` guard) |
| `lake build` | clean (3006 jobs) |

## The two remaining `sorry`s (deliberate, as in Rocq)

1. `t_progress_be_vload_pack`, in the in-bounds `VLOAD V128 (SHAPE 64 X 1)` branch (Rocq: `admit`
   at v:5208). The instruction is well formed, but `vload-shape-val` needs a `Jnn` of size 128,
   so no rule applies. This is proved in Lean as `vload_shape64_stuck`, together with
   `vload_shape64_wf`.
2. `t_progress_be_vcvtop`, in the `F32 X 4 → I16 X 8 TRUNC_SAT … ZERO` branch (Rocq: `admit` at
   v:4319). `$lcvtop__` defines `TRUNC_SAT` only for `Inn` destinations. Proved in Lean as
   `vcvtop_trunc_sat_i16_stuck` (+ `vcvtop_trunc_sat_i16_wf_instr`).

So `t_progress` is **false** in these two corner cases, in Rocq and Lean alike. The fix belongs in
the spec: give these instructions a reduction, or rule them out in validation.

## Trust boundary (`#print axioms` / `#sorry_deps`, full output in `agent_logs/progress_trust_boundary.txt`)

- **`sorryAx`** comes from 59 declarations:
  - the two subcases above;
  - `Step_read_is_wf` (the known memory.fill/copy/init 2^32 corner case, awaiting your spec fix);
  - 56 generated numeric `*_is_wf` theorems about functions that are `opaque` in Lean and
    `Axiom`s in Rocq, all `Admitted` in Rocq.
- **Project axioms used (17):** `ibits_inv`, `feq_bit`, `fne_bit`, `flt_bit`, `fgt_bit`,
  `fle_bit`, `fge_bit`, `ishl_wf`, `ishr_wf`, `trunc_sat_total`, `demote_nonempty`,
  `promote_nonempty`, `nbytes_inv`, `ibytes_inv`, `vbytes_inv`, `lanes_len`, `truncz_quot`.
  - Every one mirrors an axiom of Rocq's `axioms.v`, which Rocq's progress proof also uses.
  - All constrain only opaque functions and are jointly satisfiable (argument in the
    `HelperLemmas.lean` axiom block).
  - The two formerly inconsistent axioms (`ibytes_len'`, `ibytes_len''`, fixed this bundle)
    are **not** used.
- `t_preservation`'s boundary is unchanged: no project axiom; the same 33 generated `sorry`s.

## Coverage caveats (inherited, see the preservation report)

`t_progress` has `Config_ok` as its hypothesis, so it inherits the two upstream artifacts found
this bundle:
- it says nothing about `$invoke`'s initial configuration (the `Moduleinst_ok` non-emptiness
  premise);
- it says nothing about stores with immutable globals (`Globaltype_ok`).

Neither makes it false. The machine-checked witness `preservation_nonvacuity_witness.lean` also
shows that the hypothesis of `t_progress` is satisfiable.

## How it was built (so it can be maintained)

1. **Definitions:** ported by hand and sanity-checked by evaluation.
2. **Lemma signatures:** 6 parallel translators, each Lean-checked. Each chunk was then checked
   against Rocq by an independent auditor (1 problem in 190, fixed).
3. **The 90 case lemmas of `t_progress_be`/`t_progress_e`:** generated mechanically from the
   minor premises Lean prints for `Instrs_ok.rec` / `Instrs_ok2.rec`. The motives are Rocq's
   `P`/`P0`/`P1` as named defs. `t_progress_be`/`t_progress_e` are each one recursor application.
4. **Proofs:** 43 batches.
   - Helper lemmas were proved by Sonnet agents; the instruction cases and the main theorems by
     Opus agents.
   - Every agent ported its Rocq proof in a scratch file with a verbatim copy of the header and an
     `rfl` guard.
   - The main thread spliced the tactic blocks into the file and validated after every few batches.
5. All agents worked read-only on the repo and logged their safety checks (all verified). Their logs
   are in `bundle20/agent_logs/` (`psig-*`, `prove-*`), and the full structured results are in
   `progress_signatures_results.json` and `progress_proofs_results.json`.

## Suggested follow-ups

1. Decide on the spec fixes:
   - the two stuck vector instructions above;
   - the 2^32 bulk-memory corner case (`Step_read_is_wf`);
   - the two SpecTec middle-end artifacts (preservation report B and C).
2. Optional cleanup pass. The preservation report §5.4 lists the doc staleness (old Rocq line
   numbers, stale headers). The progress proofs already carry many comments that cite the Rocq
   step they port.
3. If you regenerate `wasm2.0.lean`, re-apply `bundle19/…/wasm2.0_hand_edits.patch`, then rebuild.
   Both proofs are stated against the generated definitions, so a change to the generator may
   need case-level touch-ups. The per-case structure keeps those local.
