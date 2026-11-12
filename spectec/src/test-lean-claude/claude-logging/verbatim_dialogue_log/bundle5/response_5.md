## Continued Phase 2 proof-filling

Re-checked the live GitHub branch first — still `a8b585cdb`, unchanged.

Per `proof_prioritization_addendum.md`'s corrected Tier B, worked through:

**`HelperLemmas.lean`'s corrected tier-0 cluster** — filled in real proofs
(all `by`-tactic, no more `sorry`) for `length_same_split_zero`,
`length_app_both_nil`, `length_app_nil`, `split_append_last`,
`split_append_1`, `split_append_2`, `split_append_left_1`, `empty_append`,
`option_orElse_none`, `option_none_orElse`, `option_some_orElse`,
`add_sub`, `add_sub'`, `sizecat_le1`, `sizecat_le2`, `drop_size_cat`,
`take_size_cat`, and `size_eq_cat` — 18 lemmas total, mostly `omega`,
`simp`, and small structural inductions, plus one `List.reverse`-based
injectivity trick for the `split_append_*` family. Left the lemmas the
2026-09-24 resync found removed from upstream `helper_lemmas.v` (`leadd`,
`add_false`, `concat_cancel_last_n`, the `Forall2_*`/`list_update_func_*`
families, `ltsize`, etc.) as `sorry` — deprioritized per the addendum, not
blocking anything, and no longer a real Rocq lemma to be faithful to.

**`Subtyping.lean`'s `instr_subtyping_strengthen2`** — the mirror image of
the already-proved `instr_subtyping_weaken2` (strengthens the *input* side
of an `instrtype_sub` fact via `resulttype_sub_split_sup`, dual to
weakening the *output* side via `resulttype_sub_split_sup'`). Proved
directly by transcribing `instr_subtyping_weaken2`'s proof structure to the
dual case, rather than needing to look up a prior session's version.

**`TypingLemmas.lean`'s `inst_match` cluster** (Tier B #3) — all 6 lemmas
(`construct_inst_match_label`/`_return`/`_local`/`_local_label_return`/
`_local_return`, `construct_inst_prepend_label`) turned out to be fully
*definitional*: `inst_match` deliberately excludes LOCALS/LABELS/RETURN
(per its own doc comment), and every one of these lemmas only modifies one
of those three excluded fields via `upd_label`/`upd_return`/`upd_local`/
`prepend_label` — so each proof is just `fun h => h`, relying on Lean
unfolding both sides to the same underlying 7-field conjunction.

**`TypingLemmas.lean`'s wellformedness-projection lemmas** (Tier B #4) —
`instr_ok_context_wf`, `ainstr_ok_context_store_wf`, `instrs_ok_context_wf`,
`ainstrs_ok_context_store_wf`. Less trivial than the digest's "one-line
inversion" description suggested: `Instr_ok`'s 72 constructors and 4 of
`Instr_ok2`'s 6 constructors bake in the needed `wf_*` facts directly
(closed by a uniform `cases h <;> exact ⟨by assumption, ...⟩` — `assumption`
searches by type, so it's robust without needing to name every
constructor's arguments), but `Instr_ok2`'s `plain` and `ref` constructors
don't directly hand over `wf_admininstr` — `plain` only gives `wf_instr`
(the *static* instruction's wellformedness) and `ref` gives nothing
`admininstr`-shaped at all. Added two small helper lemmas to bridge these:
`wf_admininstr_ref` (all three `wf_admininstr` cases for
`REF_NULL`/`REF_FUNC_ADDR`/`REF_HOST_ADDR` turn out to have no premises at
all, so this is `cases v_ref <;> constructor`) and `wf_instr_admininstr`
(`wf_instr v_instr → wf_admininstr (admininstr_instr v_instr)`, proved by
case-splitting both the instruction and its wellformedness fact in lockstep
across all ~72 cases, since `wf_instr` and `wf_admininstr` turn out to
carry identical premises for corresponding constructors — both generated
from the same EL-spec rule). `Instrs_ok`/`Instrs_ok2`'s 5-constructor
`Forall`-combination proofs needed one real debugging round: my first
attempt used `rename_i` to grab trailing hypotheses without naming every
constructor argument, which silently mis-bound hypotheses (Lean's `rename_i`
didn't behave the way I'd assumed) and produced several genuine type
errors, caught immediately by `lake build`. Fixed by naming every
constructor argument explicitly instead — safer but required getting
`Instrs_ok2`'s exact binder count right (one subtlety: the leading `store`
parameter does *not* get a fresh pattern name the way `context` does, an
asymmetry I only found by reading the elaborator's exact "N provided, M
expected" counts and adjusting).

**Verified** after each file and again at the end: full project `lake
build` from `spectec/src/test-lean-claude` exits 0 with zero errors — this
includes catching and fixing the `rename_i` mistake above before reporting
anything as done. Safety check re-run clean throughout.

Current `sorry` tally per file (for tracking momentum across sessions):
`HelperLemmas.lean` 28, `Subtyping.lean` 29, `TypingLemmas.lean` 43 (down
from 53 — 10 real proofs plus 2 new helper lemmas this turn),
`TypePreservationPure.lean` 29, `ExtensionLemmas.lean` 76 (up from before
the resync since several lemmas gained restated premises that are still
`sorry`-bodied, and 6 new lemmas were added — this number reflects
signature *count*, not difficulty; most of these are still genuinely easy
per the prioritization doc), `TypePreservation.lean` 12.

## What's next

Continuing down the corrected Tier B list: the context-update
`_is_same_as_append`/`_unchanged` lemmas (#5) are next, followed by the
higher-value `instrs_seq_typing_inversion`/`ais_seq_typing_inversion`/
`ais_composition_typing` cluster (#6, flagged as already proved in a prior
session's `SeqTypingInversion.lean`).
