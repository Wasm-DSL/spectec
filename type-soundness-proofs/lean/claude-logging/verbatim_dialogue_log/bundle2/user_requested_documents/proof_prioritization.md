# Proof prioritization

Written for: a future Claude session deciding what to work on next
(primary audience — this is meant to be followed roughly top-to-bottom),
and the user (to see and second-guess the reasoning).

Same staleness caveat as `proof_dependencies.md` applies: this ordering
is scoped to the **local, stale checkout** of `spectec/test-rocq/theories/`
(git `5b03ae067`, 2026-07-01) that this project's 6 Lean files were built
against. `type_progress.v` (real, ~4260 lines upstream) and substantial
upstream growth in every other file are handled as a separate, explicitly
deferred tier (Tier H) pending a user decision — see the end-of-session
report.

## Factors considered, and how they're weighted

1. **Dependencies** (from `proof_dependencies.md`): a lemma cannot be
   *proved* before its dependencies are proved, though it CAN be
   *stated* earlier (already done, Phase 1). This is the hard constraint;
   everything else below is a tie-breaker among lemmas that are
   currently unblocked.
2. **Ease**: informed by the per-lemma difficulty notes already recorded
   in the `digest_*.md` files (which quote Rocq proof length and tactic
   complexity as a proxy) and by this session's own direct experience
   substituting proofs (some "hard-looking" lemmas turned out to compile
   on the first try once the underlying definitions lined up; that's
   weighted in too — see the explicit "already done" callouts).
3. **Importance to the intuition** (from `rocq_proof_intuition.md`):
   weighted toward lemmas that *unblock the most other work*, not just
   lemmas that are conceptually central in the abstract. `ai_principal_typing`
   is the clearest example — it's genuinely hard/tedious, but it blocks
   roughly half of `TypingLemmas.lean` and transitively all of
   `TypePreservationPure.lean`, so it's prioritized far above where its
   raw difficulty alone would place it.
4. **Other factors** (each explicitly flagged where it applies below):
   - **Free reuse**: a lemma already fully proved (this session, or a
     prior session's file with a confirmed-isomorphic definition) costs
     nothing — do these first, always, regardless of any other ranking.
   - **Mirroring the original author's own priorities**: the git history
     (§2 of the intuition doc) shows the human author converged on
     almost exactly this same file order by trial, which is independent
     evidence this ordering is right, not just internally consistent.
   - **"Close a file" motivation**: finishing the last `sorry` in a file
     is disproportionately valuable for morale/validation/regression-
     testing purposes even when the marginal lemma isn't otherwise
     special — flagged wherever it applies (mirrors how the original
     author visibly treated "zero admits" as its own milestone).
   - **Deliberately-permanent gaps**: SIMD/vector-instruction cases are
     excluded from all tiers below (never prioritized) — both Rocq's
     source and this project's `sorry`s already reflect this, and the
     intuition doc's finding (the `lane_`-union encoding issue) suggests
     these may not be closable without a generator change regardless of
     effort spent.

---

## Tier A — already done this session (listed for completeness / to avoid re-doing)

No action needed; listed so a fresh session doesn't waste time re-deriving these.

1. `Subtyping.lean`: `valtype_sub_refl`, `valtype_sub_trans`,
   `forall2_valtype_sub_refl`, `forall2_valtype_sub_trans`,
   `resulttype_sub_refl`, `resulttype_sub_size_eq`, `resulttype_sub_trans`,
   `resulttype_sub_app`, `resulttype_sub_split_sup`,
   `resulttype_sub_split_sup'`, `instrtype_sub_refl`, `instrtype_sub_trans`,
   `instr_subtyping_weaken2`.
2. `ExtensionLemmas.lean`: `func_extension_refl0`/`refl`,
   `table_extension_refl0`/`refl`, `mem_extension_refl0`/`refl`,
   `global_extension_refl_0`/`refl`, `elem_extension_refl0`/`refl`,
   `data_extension_refl0`/`refl`, `store_extension_refl`, plus the new
   supporting `forall_range_lt`/`forall_range_refl`/`forall_range_refl_noWf`.

## Tier B — do next: free/near-free, no blockers, high leverage

Ordered within the tier by ease (easiest first) — all are genuinely
independent of each other, so any order is fine, but easiest-first builds
momentum and reduces risk of getting stuck early.

1. **`Subtyping.lean`: `instr_subtyping_strengthen2`.** Justification:
   direct mirror-image of the already-proved `instr_subtyping_weaken2`
   (dual split lemma — `resulttype_sub_split_sup` instead of `_sup'`,
   same proof shape). Should take minutes, not a fresh derivation.
2. **`HelperLemmas.lean`: the tier-0 cluster** (`leadd`,
   `length_app_lt`, `length_same_split_zero`, `length_app_both_nil`,
   `length_app_nil`, `split_append_*`, `empty_append`, `sizecat_le1`/`_le2`,
   `drop_size_cat`/`take_size_cat`, `add_sub`/`add_sub'`, `add_false`,
   `option_orElse_*`). Justification: per the file's own digest, these
   are exactly the kind of fact Lean's `List`/`Nat` API and `omega`/`simp`
   already cover natively (Rocq had to hand-roll them partly to bridge
   two parallel Coq list libraries, a problem that doesn't exist in
   Lean) — expect most of these to be short, and they unblock nothing but
   cost little, so a good warm-up/confidence-building batch.
3. **`TypingLemmas.lean` tier 10: `inst_match` cluster** (`construct_inst_match_label`/
   `_return`/`_local`/`_local_label_return`/`_local_return`,
   `construct_inst_prepend_label`). Justification: pure record-field
   equality bookkeeping, genuinely independent of `ai_principal_typing`,
   and needed later by `TypePreservation.lean`'s composition lemmas — get
   it out of the way early since it's cheap and definitely needed.
4. **`TypingLemmas.lean` tier 2: wellformedness-projection lemmas**
   (`instr_ok_context_wf`, `ainstr_ok_context_store_wf`,
   `instrs_ok_context_wf`, `ainstrs_ok_context_store_wf`). Justification:
   trivial one-line `inversion`-shaped facts per Rocq, independent of
   `ai_principal_typing`, and needed by `type_preservation_pure.v`'s
   `resolve_wfness` pattern (every `Step_pure__*` proof in Tier E starts
   by extracting these facts) — high leverage relative to cost.
5. **`TypingLemmas.lean` tier 1: context-update `_is_same_as_append`/`_unchanged` lemmas.**
   Justification: mostly `rfl`/definitional per the digest (Lean's
   `context.LABELS` being a plain list field collapses several of these
   to trivial facts that needed more machinery in Rocq's generic `@@`
   typeclass) — should be some of the cheapest real lemmas in the whole
   project.
6. **`TypingLemmas.lean` tier 5b: `instrs_seq_typing_inversion`,
   `ais_seq_typing_inversion`, `ais_composition_typing`.** Justification:
   **highest-value item in this tier** — not blocked by `ai_principal_typing`
   at all, and a prior Lean session's `SeqTypingInversion.lean` already
   has a complete, compiling proof of the `Instrs_ok`-only version
   (`instrs_seq_typing_inversion_fixed`) using this exact sequence-level
   statement shape (confirmed correct — the naive singular-`Instr_ok`
   version is provably FALSE, see `rocq_proof_intuition.md` §4). Port
   that proof for the surface-level lemma, then adapt the same technique
   (swap `Instrs_ok`/`Instr_ok` for `Instrs_ok2`/`Instr_ok2` throughout)
   for the administrative-level `ais_seq_typing_inversion`. This also
   directly matters for the intuition doc's point that this is "the
   single biggest land-mine" already found and fixed in this whole
   project — closing it for real (not just correctly stating it)
   completes that story.
7. **`ExtensionLemmas.lean` tier 1: `Store_ok`/`Extend_store` inversion
   lemmas** (`Val_ok_store`, `s_invert_funcs`/`_globals`/`_mems`/`_tables`,
   `se_invert_funcs`/`_tables`/`_mems`/`_store_globals`/`_elems`/`_datas`).
   Justification: mechanical single-constructor inversions, independent
   of everything else in the file, needed by almost every later lemma in
   `ExtensionLemmas.lean` (tiers 2 and up) — get this scaffolding in
   place early.
8. **`ExtensionLemmas.lean` tier 3: the 7 per-instruction "extension
   fact" lemmas** (`global_set_global_extension`, `store_none_mem_extension`,
   `memory_grow_mem_extension`, `table_set_table_extension`,
   `table_grow_table_extension`, `elem_drop_elem_extension`,
   `data_drop_data_extension`) **and Tier 10: the 7 mirror-image
   `construct_*` lemmas.** Justification: genuinely independent of
   everything else in the file (need only the corresponding `Extend_*inst`/
   `*_ok` constructor directly); per the git-history investigation, this
   was where the *original author* spent the bulk of a single, focused
   four-month-later session ("extension lemmas done — except meminst
   grow," the file's single largest commit) — i.e. independently
   confirmed as the load-bearing, worth-prioritizing content of this
   file, not just scaffolding around it. Also directly what
   `type_preservation.v`'s `store_extension_reduce` needs, one case per
   store-mutating instruction — finishing this tier makes real progress
   on that much later, much harder lemma "for free" once reached.
9. **`TypingLemmas.lean` tier 6: `construct_instrs_typing_single`,
   `construct_ais_typing_single`, `construct_ais_subtyping`,
   `construct_ais_instrtype_sub`, `construct_ais_compose`.**
   Justification: pure construction-direction lemmas needing only
   `Instrs_ok`/`Instrs_ok2`'s own constructors + already-proved
   `Subtyping.lean` facts — not blocked by `ai_principal_typing`, and
   `construct_ais_compose` in particular is flagged in the digest as
   "heavily reused... to glue partial typing derivations back together"
   — high downstream leverage for cheap cost.
10. **`TypingLemmas.lean` tier 7: `construct_ai_const_I32`,
    `construct_ai_ref`, `construct_ai_val`, `adminval_val_ref`.**
    Justification: simple, need only `Instr_ok2`'s constructors directly.

## Tier C — the single highest-leverage blocker: `ai_principal_typing`/`instr_of` bodies

11. **`TypingLemmas.lean`: transcribe `instr_of`'s real body** (a ~50-case
    match, `admininstr` constructor ↦ `Some` of the corresponding `instr`
    constructor, or `None` for purely-administrative forms). Justification:
    mechanical (direct 1:1 constructor mapping, exhaustively listed in
    the digest), low *conceptual* difficulty but real *transcription*
    effort — do this before #12 since `ai_principal_typing`'s own gap
    doesn't need `instr_of`, but several other tier-6b lemmas
    (`construct_ai_maybe`) do, and it's a smaller, self-contained task
    to warm up on before the much bigger #12.
12. **`TypingLemmas.lean`: transcribe `ai_principal_typing`'s real body**
    (a ~57-case match giving each `admininstr` constructor's principal
    functype). Justification: **this is the single most important piece
    of remaining structural work in the entire project.** It's not a
    proof (no tactics, just a `Prop`-valued pattern match), so the
    "difficulty" is pure careful transcription against the digest's full
    per-constructor case list — a large, bounded, mechanical task with no
    open mathematical questions, ideal for a long uninterrupted session.
    Its importance is disproportionate to its own difficulty: per
    `proof_dependencies.md`, it directly blocks `instr_typing_inversion`,
    `ai_typing_inversion`, and transitively `ais_single_typing_inversion`
    and everything in `TypePreservationPure.lean` that needs "what type
    does this admin-instruction have" (i.e. nearly all 28 `Step_pure__*`
    lemmas). Completing this single definition is likely to unblock more
    subsequent proof work than any other action available.

## Tier D — medium-hard proofs unblocked by Tier C

13. **`instr_typing_inversion`.** Justification: now provable; per the
    digest, "medium-high tedium, low conceptual difficulty (mechanical
    unfolding)" — a good first target once Tier C lands, to validate
    that the transcribed `ai_principal_typing`/`instr_of` bodies are
    actually correct (any transcription slip will likely surface here
    first, as a case that won't close).
14. **`ai_typing_inversion`.** Justification: "the master per-instruction
    inversion lemma," per the digest the single longest/highest-difficulty
    proof in `typing_lemmas.v` (57-way case split) — do this right after
    #13 while the `ai_principal_typing` case structure is freshest.
15. **`instrs_single_typing_inversion`, `ais_single_typing_inversion'`,
    `ais_single_typing_inversion`.** Justification: chain directly off
    #13/#14, individually not too hard per the digest.
16. **`TypingLemmas.lean` tier 8/9: `value_extra`, `Vals_ok`,
    `Val_ok_non_bot`, `Vals_ok_non_bot`, `Ref_ok_non_bot`,
    `ais_vals_typing_inversion`, `construct_ais_vals`/`_vals'`.**
    Justification: `construct_ais_vals` is flagged in the digest as the
    single longest/most intricate proof in the whole file (~125 lines in
    Rocq, `last_ind` over two lists simultaneously) — attempt last within
    this tier, after the easier `Val_ok_non_bot` family building up to it.

## Tier E — `TypePreservationPure.lean`'s 28 lemmas, now unblocked

17. Work through the 28 `Step_pure__*_preserves` lemmas **in Rocq's own
    file order** (this matches increasing difficulty per the digest:
    `nop`/`drop` trivial → `select`/`if` medium → `label_vals`/`br_zero`
    medium → `br_succ`/`br_table_lt`/`br_table_ge` the hardest three in
    the file → `frame_vals`/`return_label` medium → `unop`/`binop`/
    `testop`/`relop`/`cvtop_val` a repetitive medium cluster →
    `local_tee` medium-high → `ref_is_null_*` medium-high). Justification
    for file-order rather than re-sorting by difficulty: several lemmas
    explicitly build on the immediately-preceding one in Rocq
    (`select_true`/`false_preserves` both need `select_preserves_helper`,
    etc.) — file order already respects that local dependency structure.
18. **Make a real, dedicated attempt at `Step_pure__return_frame_preserves`**
    before treating it as permanently `sorry`. Justification (the single
    most important "other factor" callout in this whole document): per
    the commit-history investigation, this lemma is `Admitted` in Rocq
    **not because it's intrinsically hard**, but because a working proof
    existed once and was lost to the `Admin_instrs_ok`→`Instrs_ok2`
    rename during the July 1 repair, and the author never revisited it.
    The Lean proof is free to use different tactics entirely, so this
    project isn't even bound by whatever made the Rocq repair
    inconvenient — this is plausibly one of the more tractable "hard"
    lemmas in the whole project despite its Rocq status, and worth real
    effort before deferring it.
19. **`t_pure_preservation`** (master theorem, minus SIMD cases).
    Justification: pure dispatch once all 26 non-SIMD lemmas above exist
    — should be mechanical case-matching, no new mathematical content.

## Tier F — `ExtensionLemmas.lean` remainder

20. **Add the missing `Limits_sub`/`Externtype_sub` supporting cluster**
    (`limits_sub_refl`, `limits_sub_trans`, `functype_sub_eq`,
    `globaltype_sub_eq`, `externtype_sub_refl`, `externtype_sub_trans`,
    `externtype_global_eq`, `externtype_func_eq`) as new lemmas in
    `ExtensionLemmas.lean`. Justification: **free reuse** — a prior Lean
    session already has complete, compiling proofs of exactly these
    facts (misattributed to a stale/nonexistent Rocq line range, but the
    underlying relations `Limits_sub`/`Externtype_sub`/`Tabletype_sub`/
    `Memtype_sub` genuinely exist in `wasm2.0.lean` and the proofs should
    port with minimal adaptation, same as Tier A) — and they directly
    unblock #21.
21. **`minst_invert_*` family** (7 lemmas). Justification: needs #20 for
    the tables/mems cases; otherwise straightforward constructor
    inversion.
22. **Resolve the `funcinst_same` representational gap**, then
    `store_extension_ref`/`_refs`/`_val`/`_vals`. Justification: this is
    a genuine small *design decision*, not just proof effort — the
    zip-based `Forall₂` doesn't force equal-length the way Rocq's
    inductive `Forall2` does, so `funcinst_same` needs either an added
    length hypothesis or a different proof strategy at each call site.
    Worth resolving early in this tier since several later lemmas
    (`store_extension_ref` onward) depend on it, and the fix likely
    generalizes to any other place in the project using `Forall₂` the
    same way — flag any recurrence for a possible shared lemma.
23. **`addrs_*_extension`/`addrss_*_extension`** (8 lemmas). Justification:
    mechanical, needs only Tier B's #7 (`se_invert_*`).
24. **`store_extension_exts`, `_eleminst`, `_eleminsts'`/`_eleminsts`,
    `_datainsts'`/`_datainsts`, culminating in `store_extension_moduleinst`.**
    Justification: the file's "key assembly lemma," needs #21 and #23.
25. **`store_extension_funcinst`/`_globalinst`/`_tableinst`/`_meminst`
    (+ list-lifted versions), `store_extension_externaddrs_func`.**
    Justification: needs #24 (for funcinst) or #22 (for the others).
26. **`store_extension_ais`** (capstone, custom mutual induction).
    Justification: needs #22, #24, #25 — genuinely the hardest lemma
    left in this file, save for last within the tier.
27. **Attempt the memory-growth arithmetic gap** in
    `construct_meminsts_grow` (bounding growth against the 2^16-page
    ceiling) — the Rocq counterpart's own remaining `admit`.
    Justification ("close a file" factor): per the intuition doc, this
    is *ordinary unfinished arithmetic*, not a structural blocker — the
    Rocq author simply never found the route (`TODO - Find some way of
    showing lim_old + v_n <= 2^16` — the growth check is only a `≤`
    postcondition, and if the operation itself already validated it
    before mutating, the bound should just be a restatement of an
    existing hypothesis; worth a fresh look rather than assuming Rocq's
    difficulty transfers). Closing this would make `ExtensionLemmas.lean`
    the second fully-`sorry`-free file in the project (after whichever of
    `HelperLemmas.lean`/`Subtyping.lean` finishes first) — genuine
    validation value, mirroring how the original author treated "zero
    admits" milestones.

## Tier G — `TypePreservation.lean`, mostly composition

28. **`zero_is_well_formed`, `num_default_is_well_formed`,
    `inst_t_context_local_empty`, `inst_t_context_labels_empty`.**
    Justification: independent, trivial per the digest — free wins,
    do whenever convenient, no ordering constraint among them.
29. **`t_preservation_vs_type'`, `t_preservation_vs_type`.**
    Justification: needs `TypingLemmas.lean`'s `Vals_ok` (Tier D done)
    and `ExtensionLemmas.lean`'s `store_extension_vals` (Tier F #22 done).
30. **`reduce_inst_unchanged`.** Justification: independent, trivial
    induction per the digest — do any time, no blockers.
31. **`store_extension_reduce`** (minus SIMD cases). Justification:
    needs Tier F's #8 (the 7 per-instruction extension facts) almost
    entirely — this is where that early investment pays off directly;
    per the digest, "massive induction... dozens of named case blocks,"
    but each case should now just be "apply the matching Tier-F lemma."
32. **`t_read_preservation`** (minus SIMD cases). Justification: needs
    all of Tier D (the typing-inversion machinery) — the single largest
    lemma in the file by Rocq line count (~1400 lines), but structurally
    the same "invert typing, reconstruct typing" pattern as Tier E,
    just for `Step_read` instead of `Step_pure`.
33. **`step_moduleinst`.** Justification: needs #30, #31, and
    `store_extension_moduleinst` (Tier F #24).
34. **`t_preservation_type`** (minus SIMD cases). Justification: needs
    Tier E's `t_pure_preservation`, #32, and `store_extension_ais`
    (Tier F #26) — the last major lemma before the capstone, gated on
    essentially everything else in this document being done first.
35. **`t_preservation`** (the capstone). Justification: per both the
    digest and the intuition doc, this is *pure composition* of #31,
    #29, #34, #30, and `store_extension_moduleinst` — no case analysis
    of its own in Rocq. Should be the easiest lemma to close once
    everything feeding it exists, despite being "the ultimate goal of
    the project" by the Rocq author's own comment.

## Tier H — explicitly deferred pending a user decision (not otherwise prioritized)

36. **Re-sync the local `spectec/test-rocq/theories/` checkout against
    the live `rocq-backend-proof` branch HEAD**, or otherwise obtain the
    current version of `extension_lemmas.v` (+3435 lines at HEAD),
    `type_preservation.v` (+2752 lines, now includes vector-instruction
    cases the local snapshot lacks), `wasm.v` (+9182 lines — the base
    spec itself has grown substantially), and the others. This is a
    **prerequisite decision**, not a proof-priority item — see the
    end-of-session report. Not undertaken by this session because it
    would mean modifying files outside `spectec/src/test-lean-claude/`,
    which is outside this project's safety boundary without explicit
    user authorization.
37. **Port `type_progress.v`** (Progress, the other half of type safety;
    ~4260 lines upstream, does not exist in the local checkout at all).
    This is a large, mostly-fresh undertaking — a new file, a new
    dependency chain (presumably needing everything `type_preservation.v`
    needs, plus its own machinery), and per the intuition doc, the
    single most incomplete file in the whole upstream development (30+
    TODOs, 6 `admit`s, all apparently tracing to one generator-level
    `lane_`-union encoding gap). Blocked on #36 (can't port a file this
    project doesn't have a copy of), and, once unblocked, deserves its
    own dedicated prioritization pass — flagged here rather than
    pre-planned in detail, since its actual shape/difficulty can't be
    assessed from the current local checkout.
