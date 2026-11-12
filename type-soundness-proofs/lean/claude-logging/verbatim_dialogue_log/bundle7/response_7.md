## Continued Phase 2: the "easy Tier B" construction/injectivity cluster in `TypingLemmas.lean`

Re-verified the live GitHub branch first (`gh api` failed silently in this
environment for an unrelated reason — a sandboxing/network quirk, not a
credentials problem, confirmed via `gh auth status` also going silent;
switched to plain `curl` against the public GitHub REST API, which works
fine). Live `rocq-backend-proof` HEAD is still `a8b585cdb536b2b2e53ff45fa8010de88f05a042`,
unchanged since the resync — confirmed again via `git ls-tree`/`git show`
against the commit object (already present locally from the prior bundle's
fetch), so no new upstream Rocq changes to reconcile this turn.

Per the user's refined strategy guidance this turn (fall back to reading the
actual Rocq tactic proof, tactic-for-tactic, when a Lean proof is proving
harder than expected, rather than re-deriving from first principles blind) —
pulled `typing_lemmas.v` at the live commit via `git show a8b585cdb...:...`
into a scratch file and read the real Rocq proofs for every lemma tackled
this turn before writing the Lean version. This paid off immediately on
`construct_ais_subtyping`: the naive plan (chain `resulttype_sub_trans`
through the `instrtype_sub` existential) doesn't typecheck because the
"extra" prefix pieces (`ts_sub`/`ts`) aren't literally equal, only
subtype-related — Rocq's actual proof uses `Instrs_ok2__frame` to add the
`ts_sub` prefix first (matching `ts_sub` on *both* sides), then a single
`Instrs_ok2__sub` step folds in the two `ResulttypeSub` facts via
`resulttype_sub_app`. Ported that exact structure directly.

**15 lemmas proved this turn**, all in `TypingLemmas.lean`, all verified via
`lake build` (exit 0, zero errors) before being reported:

- `construct_instrs_typing_single`, `construct_ais_typing_single` — direct
  from `instr_ok_context_wf`/`ainstr_ok_context_store_wf` (bundle5) feeding
  straight into the `instr`/`Instrs_ok2.instr` constructors.
- `instrs_empty_typing`, and a newly-added `ais_empty_typing` (present in
  Rocq at `typing_lemmas.v:333` but missing from this file's signature list
  entirely — added it since several lemmas below need it) — both proved by
  relocating them to just after `ais_ok_widen_out`/`instrs_ok_widen_in`
  (the bundle6 seq-typing-inversion scaffolding they depend on), then: ⇒
  direction via `*_ok_context_wf` + `*_ok_nil_sub`, ⇐ direction via
  `*_ok_nil_refl` (reflexive `t f-> t`) widened on the input side by
  `*_ok_widen_in` — exactly mirroring Rocq's own `frame`-then-`sub` proof.
- `construct_ais_subtyping` / `construct_ais_instrtype_sub` (Rocq keeps two
  identically-stated lemmas; the latter is now a one-line alias of the
  former) — the `frame`-then-`sub` proof described above.
- `injective_valtype_numtype` and `injective_admininstr_instr` — both by
  `cases a <;> cases b <;> simp_all [defn]`, matching Rocq's
  `destruct x1; destruct x2; try discriminate; auto` exactly. The second one
  is a 68×68-constructor case split (`instr` has 68 constructors); it
  compiled in ~26s with zero issues, no special handling needed.
- `construct_ais_compose` — direct `Instrs_ok2.seq` application using
  `ainstrs_ok_context_store_wf` for the two wellformedness bundles, same
  shape as Rocq's `eapply Instrs_ok2__seq; eauto`.
- `construct_ai_const_I32`, `construct_ai_ref`, `construct_ai_val`,
  `adminval_val_ref` — built from `wf_instr`'s/`Instr_ok`'s exact premise
  shapes read directly out of `wasm2.0.lean` (`instr_case_13`/`_20` for
  `CONST`/`VCONST`, `Instr_ok.const`/`.vconst`/`.ref_null`). Found a genuine
  simplification over the Rocq proof here: Rocq's `construct_ai_ref` has to
  case-split `Ref_ok` into `null`/`func`/`extern` because Rocq's own
  `Instr_ok2__ref` constructor only covers the `FUNC_ADDR`/`HOST_ADDR`
  forms (routing `REF_NULL` through the "plain" `instr` path instead) — but
  this backend's generated `Instr_ok2.ref` constructor is fully generic over
  *any* `ref` value, so the Lean proof is just one direct constructor
  application, no case split needed.
- `construct_ais_trap` — `Instr_ok2.trap` here is already generic over the
  target functype (unlike Rocq's `Instrs_ok2__seq`-based decomposition
  through an empty tail), so `construct_ais_typing_single` closes it
  directly after destructuring the functype into its two `List valtype`s.
- `resulttype_sub_single_inversion` — one line: since `Forall₂` in this file
  is the zip-based `def` (not Rocq's inductive `Forall2`), `[t1].zip [t2] =
  [(t1,t2)]` and the fact is extracted by `simp`-closed membership.
- `Val_ok_non_bot`, `Ref_ok_non_bot` — case-split on the relevant inductive
  (`Val_ok`/`Ref_ok`) then `cases` the underlying `numtype`/`vectype`/
  `reftype` value and `simp` the defining equation; both types' `valtype_*`
  maps never produce `BOT`, so every case closes.

**One real representation-gap finding, left `sorry` with a documented
reason (not force-fit)**: `Vals_ok_non_bot`. Rocq's `Forall2` is an
*inductive* relation that forces `v_ts.length = v_val.length`; this file's
`Forall₂` is the zip-based `def` (`∀ p ∈ v_ts.zip v_val, P p`), which does
**not** force equal length. As literally stated the lemma is false when
`v_ts` is strictly longer than `v_val` (e.g. `v_ts := [BOT]`, `v_val := []`:
the zip is `[]`, so the hypothesis holds vacuously, but the conclusion
`Forall (· ≠ BOT) [BOT]` is false). Same class of gap as the previously-
flagged `funcinst_same` issue (bundle3's resync notes) — recorded in the
theorem's doc comment rather than attempted with a wrong/overfit proof.

**Left for a future bundle, correctly gated on harder blockers** (not
attempted this turn, per the "reassess prioritization" fallback guidance):
`construct_ai_maybe` (needs `instr_of`'s real ~50-case body, still `sorry`),
`ai_val_principal_typing_inversion` (needs `ai_principal_typing`'s real
~57-case body, still `sorry`), `ais_vals_typing_inversion`/
`construct_ais_vals`/`construct_ais_vals'` (the Rocq proofs for these route
through per-value typing-inversion machinery that itself needs either
`ai_principal_typing` or a length-carrying strengthening of `Vals_ok_non_bot`
above — genuinely blocked on the same two upstream gaps, not just "hard").

**Verified**: full project `lake build` exits 0 with zero errors. Safety
check re-run clean (only the same pre-existing untracked scratch files
outside `spectec/src/test-lean-claude/` that have shown up in every prior
bundle's check — nothing new, nothing written outside the target directory
this turn).

Current `sorry` tally: `TypingLemmas.lean` **20** (down from 35),
`HelperLemmas.lean` 29, `Subtyping.lean` 32, `TypePreservationPure.lean` 33,
`ExtensionLemmas.lean` 79, `TypePreservation.lean` 17. (Note: these baseline
counts are slightly different from the numbers reported at the end of
bundle6 — a plain `grep -c sorry` recount at the start of this turn came out
a bit higher across several files than what was previously stated; nothing
in the actual `.lean` sources changed between bundles 6 and 7 other than
this turn's own edits, so the bundle6 figures were very likely just a
manual-count discrepancy, not evidence of lost work. Treating this turn's
`grep -c` numbers as the authoritative baseline going forward.)

## What's next

The remaining Tier B items are now genuinely blocked on the two big Tier C
definitions (`instr_of`, `ai_principal_typing`), so the next unblocked work
is either: (a) tackling `instr_of`'s ~50-case body directly (a large but
*mechanical* transcription job, unlike `ai_principal_typing`'s proof-shaped
50-case body), which would unblock `construct_ai_maybe` and a chunk of the
`ais_*_typing_inversion` family, or (b) moving to `ExtensionLemmas.lean`'s
still-`sorry`'d inversion lemmas (tier #7), which don't depend on either
blocker. Leaning towards (a) next since it directly unblocks the largest
number of currently-stuck lemmas, but will reassess after inspecting
`instr_of`'s actual Rocq case list once more (per this turn's own
guidance) before committing.
