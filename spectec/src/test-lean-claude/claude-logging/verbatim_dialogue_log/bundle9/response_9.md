## Caught up, resynced-check done, `Vals_ok` fixed, and a big unblock in `TypingLemmas.lean`

### 1. Caught up on bundles 3-8

Read every prompt/response, `bundle3/updated_documents/*`, `bundle8/vals_ok_non_bot_analysis.md`, and the living `NOTES.md`/`is_wf_theorems.md` in full. Picked up the standing rules (safety boundary + periodic checks, verbatim logging for every exchange) and I'm continuing them as `bundle9`.

Headline of what happened in bundles 3-8, for reference: bundle3 verified your manual re-sync to `a8b585cdb` was correct and cataloged what changed (SIMD closed in both Preservation files, `extension_lemmas.v` renamed wholesale, `type_progress.v` arrived); bundles 4-7 worked through `ExtensionLemmas.lean`'s rename pass and a long tail of `TypingLemmas.lean`/`HelperLemmas.lean`/`Subtyping.lean` lemmas; bundle8 ported `ai_principal_typing` (the ~340-line central definition) plus `instr_typing_inversion`/`ai_typing_inversion` from your own `spectec/test-lean/typing_lemmas.lean`, found and fixed a real bug in it (`BR_TABLE` parenthesization), and flagged the `Vals_ok_non_bot` representation gap for your decision rather than guessing.

### 2. Rocq upstream: small delta, nothing to update

Live `rocq-backend-proof` HEAD is `58af2e2f9` ("Some more cases done") — already what's merged into `lean-backend`. Diffed against the `a8b585cdb` baseline bundles 3-8 worked from: only `type_progress.v` (2 more SIMD lane-cases closed: VUNOP, VTESTOP) and `wasm.v` changed (one lemma closed; comments reference a **not-yet-pushed** `wf_counterexamples.v` claiming 6 `*_is_wf` theorems are provably FALSE — `fone_is_wf`, `utf8_is_wf`, `Step_pure_is_wf`, `Step_read_is_wf`, `runelem_is_wf`, `rundata_is_wf`. Worth flagging to whoever's running the parallel `*_is_wf` audit; nothing in our project currently depends on any of these). **None of our 6 ported files needed updating** — confirmed by direct diff that nothing in their corresponding Rocq sources changed. Full detail in `bundle9/user_requested_documents/rocq_changes_summary.md`.

Also produced consolidated (not just another addendum-on-addendum) updates: `proof_dependencies_v2.md` and `proof_prioritization_v2.md`, reflecting everything actually done through bundle8 plus this bundle, with ground truth taken from a direct `sorry` grep rather than reconstructed from memory.

### 3. `Vals_ok_non_bot`: implemented your Option 2 + 3 combination

- **Option 3**: added `to_mathlib_forall₂`/`from_mathlib_forall₂` to `HelperLemmas.lean` (now imports `Mathlib.Tactic`), bridging this project's zip-based `Forall₂` to Mathlib's inductive `List.Forall₂` given a length hypothesis.
- **Option 2**: redefined `Vals_ok` to bake in `v_ts.length = v_vals.length` alongside the existing `Forall₂` conjunct. Checked all 6 call sites across the project — all were still `sorry`, so nothing broke.
- `Vals_ok_non_bot` now routes through the length-carrying `Vals_ok` (a deliberate, documented deviation from Rocq's literal bare-`Forall2` signature — `Vals_ok` is exactly the Lean stand-in for what Rocq's inductive `Forall2` gives for free) and is proved via the bridge, mirroring Rocq's own induction structure.

Full writeup with the "what was deliberately not done" list: `bundle9/user_requested_documents/vals_ok_non_bot_resolution.md`.

### 4. `instr_of` transcribed — and it unblocked almost everything left in `TypingLemmas.lean`

`instr_of`'s ~50-case body (the other half of Tier C, alongside `ai_principal_typing` which bundle8 closed) turned out to be a gift: `wasm2.0.lean` already has the exact inverse, `admininstr_instr : instr → admininstr`, fully generated. Read it off directly and wrote `instr_of` as its case-for-case mirror (62 cases + a `none` catch-all for the 6 admin-only forms), plus a round-trip sanity lemma.

That one definition cascaded into closing almost everything else still open in the file this bundle: `instrs_single_typing_inversion`, `ais_single_typing_inversion'`/`ais_single_typing_inversion`, `ai_val_principal_typing_inversion`, `ais_single_ref_typing_inversion`, `ais_single_val_typing_inversion`, `construct_ai_maybe`, `construct_ais_vals'`. **`TypingLemmas.lean`'s real-`sorry` count: 17 → 2.**

**Found and fixed a real bug along the way**: `ai_principal_typing` (bundle8's port) was missing its case for `admininstr.REF_HOST_ADDR`, silently falling into the catch-all `| _ => True` — meaning it was vacuously satisfiable for any functype in that case, when Rocq actually requires `[] -> [EXTERNREF]`. Nothing had exercised that case until this bundle's `ai_val_principal_typing_inversion` did. Fixed the missing case and the one proof (`ai_typing_inversion`'s `ref` branch) that had been silently relying on the bug via a bare `trivial`. Flagged prominently in `NOTES.md` since it's the kind of thing worth double-checking if `ai_principal_typing` is ever touched again.

The two remaining `sorry`s (`ais_vals_typing_inversion`, `construct_ais_vals`) are deliberately left — the latter is the single longest/most intricate proof in the Rocq file (~125 lines, `last_ind` over two lists at once), and I'd rather hand you a clean, fully-verified state than a rushed attempt at the hardest lemma in the file. They're next in line per the updated prioritization doc.

### Verified throughout

`lake build` run after every lemma (not just at the end) — clean at every checkpoint, 3005 jobs, exit 0. Safety check re-run clean: everything touched is inside `spectec/src/test-lean-claude/`.

### What's next

Per `proof_prioritization_v2.md`: finish the last 2 `TypingLemmas.lean` lemmas, then `TypePreservationPure.lean`'s 27 now-fully-unblocked lemmas (Tier D there), with `ExtensionLemmas.lean`'s independent 76-lemma track available in parallel. I'll continue unless you'd like to redirect.
