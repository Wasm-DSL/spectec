# Resync impact report

Written for: a future Claude session continuing this project (primary
audience), and the user (to see the evidence behind the report-back in
`response_3.md`).

This is the master document for bundle3's update pass. It covers (1)
verification that the user's manual re-sync was done correctly, (2) exactly
what changed in the Rocq source between the stale checkout our Phase-1 work
was built against and the current one, and (3) the concrete implications for
`NOTES.md`, `is_wf_theorems.md`, and the three bundle2
`user_requested_documents/` (which are **not** rewritten — see the shorter
addenda alongside this file, and the "don't touch previous bundles" instruction).

## 1. Verification that the re-sync was done correctly

The user's commit `b78d56eeb` ("merge with rocq-backend-proof, change in
typefamilyremoval.ml") merges `26d40070b` (prior `lean-backend` tip) with
`a8b585cdb` ("Vector Instructions for Preservation proven, and most
well-formedness lemmas done.").

Checked (read-only, all commands run from repo root, nothing mutated):

- `gh api repos/Wasm-DSL/spectec/branches/rocq-backend-proof --jq '.commit.sha'`
  → `a8b585cdb536b2b2e53ff45fa8010de88f05a042` — **exactly** the second parent
  of the merge commit, and (checking the API's own returned commit date,
  2026-09-22T22:56:23Z, against "now") **still the current tip** — no further
  upstream commits since. So the merge target was the right one, and it's
  still current as of this check.
- `grep -rl` for `<<<<<<<`/`=======`/`>>>>>>>` across
  `spectec/test-rocq/theories/`, `spectec/src/backend-rocq/`,
  `spectec/src/frontend/elab.ml`, `spectec/src/middlend/typefamilyremoval.ml`,
  `specification/wasm-2.0/` → none found.
- `git status --porcelain` on those same paths → clean except two new
  untracked files (`spectec/test-rocq/_CoqProject`,
  `spectec/test-rocq/test-rocq.opam`) that look like local Rocq/opam project
  config, not conflict artifacts.
- Line counts of every file in `spectec/test-rocq/theories/` were sanity
  checked against the merge's own diffstat and are internally consistent
  (e.g. `type_progress.v` is present and 4260 lines, matching the diffstat's
  "+4260" for a brand-new file).

**Conclusion: the re-sync was done correctly.** `spectec/test-rocq/theories/`
is now byte-identical to the live GitHub `rocq-backend-proof` branch HEAD, and
that HEAD hasn't moved since. Since this check found nothing wrong, per the
user's own instruction ("if not, stop here and report") there was nothing to
stop for — proceeding to items 2–4 was correct.

## 2. On "why would the local checkout matter, shouldn't you read the git repo I gave you"

The user's question here is fair and the honest answer is: it *shouldn't*
have mattered, in the sense that reading `spectec/test-rocq/theories/`
directly via the `Read`/`Bash` tools **is** "looking at the git repository
you gave me" — there was never a separate live-vs-local distinction *within*
that repo. What actually happened (per `bundle2/response_2.md`) is that the
**local working copy of that directory in this repo** was simply behind the
**live upstream `rocq-backend-proof` branch on GitHub** — two different
copies of the same conceptual file, one stale. Reading "the git repository I
gave you" was always correct procedure; the problem was that copy hadn't been
kept in sync with upstream, not a misunderstanding about which repo to read.
Now that the user has manually merged upstream in, both are the same again —
this whole distinction is currently moot, and will only resurface if upstream
moves again in the future without another manual re-sync. (Per the user's
explicit instruction to prioritize the live GitHub source going forward, item
1's `gh api` check above is the pattern to repeat if that's ever in doubt
again: cheap, read-only, no local git state mutation.)

## 3. What actually changed (2026-07-01 `5b03ae067` → 2026-09-22 `a8b585cdb`)

Verified directly by diffing the two commit objects (both already present
locally in this repo's object store — no fetch needed) and extracting every
`Lemma`/`Theorem`/`Corollary`/`Definition`/`Fixpoint`/`Axiom` name from each
file at both revisions.

### 3a. Preservation's SIMD gap is now closed — the single biggest change

| File | Old `Admitted` count | New `Admitted` count |
|---|---|---|
| `type_preservation_pure.v` | 2 | **0** |
| `type_preservation.v` | 3 | **0** |

`type_preservation_pure.v` grew from 29 to 76 declarations — the ~47 new ones
are almost entirely `ais_v*_typing_inversion` and `Step_pure__v*_preserves`
lemmas (one pair per vector instruction family: vbinop, vunop, vrelop,
vtestop, vshiftop, vbitmask, vsplat, vextract_lane, vreplace_lane, vcvtop,
vextunop, vextbinop, vnarrow, vswizzle, vshuffle, vvunop, vvbinop, vvternop,
vvtestop), plus `const_result_typing`/`vconst_result_typing`/`vec_preserves_1/2/3`
as shared helpers. `type_preservation.v` grew from 13 to 37, adding the
`Step_read`/`Step` analogues for vector loads/stores
(`ais_vload_typing_inversion`, `ais_vload_lane_typing_inversion`,
`Step_read__vload_preserves`, `Step_read__vload_lane_preserves`,
`ais_vstore_typing_inversion`, `ais_vstore_lane_typing_inversion`,
`Step__vstore_preserves`, `Step__vstore_lane_preserves`, `vec_store_preserves_2`,
`mem_store_extension`) plus some `wf_context_*`/`wf_store_mem_update*`/
`wf_*insts_preserves` bookkeeping lemmas.

**Consequence**: `NOTES.md`'s TODO item "e. Deliberately-kept gaps (mirror
Rocq, do not 'fix')" listing `t_pure_preservation`'s and
`t_preservation_type`'s SIMD cases is now **wrong as a permanent statement**
— those Rocq gaps no longer exist. Our `sorry`s there are currently just
ordinary unfinished Phase-2 work, not "faithful mirrors of an upstream gap."
This is real new porting work (~50+ new lemma signatures + real proofs to
add to `TypePreservationPure.lean` and `TypePreservation.lean`), not
optional.

### 3b. `extension_lemmas.v` — comprehensive rename, not just growth

Every name our `ExtensionLemmas.lean` was ported against is gone from the
current source, replaced with a converging-on-Lean-style naming:

| Old Rocq name (what we ported against) | New Rocq name |
|---|---|
| `store_extension_refl` | `Extend_store_refl` |
| `func_extension_refl0` / `func_extension_refl` | `extend_funcinst_refl_0` / `extend_func_refl` |
| `table_extension_refl0` / `_refl` | `extend_tableinst_refl_0` / `extend_table_refl` |
| `mem_extension_refl0` / `_refl` | `extend_meminst_refl_0` / `extend_mem_refl` |
| `global_extension_refl_0` / `_refl` | `extend_globalinst_refl_0` / `extend_global_refl` |
| `elem_extension_refl0` / `_refl` | `extend_eleminst_refl_0` / `extend_elem_refl` |
| `data_extension_refl0` / `_refl` | `extend_datainst_refl_0` / `extend_data_refl` |
| `store_extension_ais` | `Extend_store_ais` |
| `store_extension_moduleinst` | `Extend_store_moduleinst` |
| `store_extension_funcinst`/`_globalinst`/`_tableinst`/`_meminst` (+ list forms) | `Extend_store_funcinst`/`_globalinst`/`_tableinst`/`_meminst` (+ list forms) |
| `store_extension_ref`/`_refs`/`_val`/`_vals` | `Extend_store_ref`/`_refs`/`_val`/`_vals` (+ new `_refs'`) |
| `store_extension_exts`/`_eleminst`/`_eleminsts`/`_eleminsts'`/`_datainsts`/`_datainsts'` | `Extend_store_exts`/`_eleminst`/`_eleminsts`/`_eleminsts'`/`_datainsts`/`_datainsts'` |
| `store_extension_externaddrs_func` | `Extend_store_externaddrs_func` |
| `Val_ok_store` | *(removed — no direct replacement found; check `Extend_store_val`/`_vals` for the same role)* |
| `funcinst_same` | *(removed — the representational-gap workaround `proof_prioritization.md` Tier F #22 flagged may no longer be needed at all; check the new proof of `Extend_store_funcinst`/`_ref` to see how the author resolved it upstream)* |

This is our own `NOTES.md`'s naming-resolution note in reverse: previously we
reasoned "Rocq says `Store_extension` but that name doesn't exist anywhere —
it must mean `Extend_store`" (true, but for the *old* checkout). Now the
*current* checkout has moved even closer to the Lean-generated names
directly. **Every extension-lemma name cited in `proof_prioritization.md`
Tiers A, B(#7,#8), F is stale** — the underlying math/proofs likely still
port fine (same relations, same facts), but a rename pass over
`ExtensionLemmas.lean` is needed to stay faithful to "signatures must be
directly from the Rocq proof." This is mechanical (search-and-replace guided
by the table above) but should happen before further `ExtensionLemmas.lean`
work, to avoid compounding the staleness.

Also added (genuinely new content, not renames): `limits_sub_refl`/`_trans`,
`externtype_sub_refl`/`_trans`, `externtype_func_eq`/`_global_eq` — these are
**exactly** the lemmas `proof_prioritization.md` Tier F #20 said we'd need to
add "from scratch" citing a prior Lean session's reuse-only proofs; they now
have real Rocq statements to port against directly, which is strictly better
than porting against inferred/reused Lean-only versions. Also added:
`Externaddr_invert_funcs`/`_globals`/`_mems`/`_tables` (a new inversion
family, likely slots into Tier B/F's inversion-lemma cluster),
`holds_upto_*`/`update_holds_upto_*`/`pagediv*`/`iota_snocN`/`nth_iotaN`/
`size_iotaN`/`repeat_forall`/`Qfloor_add_Z`/`Zle_Nle` (arithmetic/list
machinery, mostly in service of the still-open `construct_meminsts_grow`
growth bound — see below), and `list_update_func_subst`/`_unchanged`,
`forall_preserved_bytes`, `invert_meminst`.

### 3c. The one remaining Preservation-side gap: `construct_meminsts_grow`

`extension_lemmas.v` now has exactly 1 `Admitted` (up from 0 — this lemma
simply didn't exist as a named target before, or existed elsewhere/differently;
either way it's the sole remaining gap in that file), at the lemma
`construct_meminsts_grow: forall s ts ma b_lst (lim_old : Q) (v_n : N) v_j_opt minsts, ...`
— the `lim_old + v_n <= 2^16` memory-growth bound, exactly matching
`proof_prioritization.md` Tier F #27's description. The new `pagediv`/
`update_holds_upto_le`/`_lt` machinery added alongside it (per 3b) looks
purpose-built to close this — worth attempting fresh with these available,
per Tier F #27's original reasoning ("ordinary unfinished arithmetic, not a
structural blocker").

### 3d. `type_progress.v` has arrived

4260 lines, previously nonexistent in `theories/` (a 3131-line staging draft
existed at the old commit under `folder-to-exclude/`, not yet in the
compiled build). Full structural digest in
`claude-logging/for-claude/digest_type_progress.md`. Headline facts:

- Depends on `wasm`, `helper_lemmas`, `helper_tactics`, `typing_lemmas`,
  `extension_lemmas`, `subtyping`, `axioms` — **not** on
  `type_preservation`/`type_preservation_pure`. Progress and Preservation
  are parallel, not sequential — corrects `proof_prioritization.md` Tier H
  #37's guess that Progress would need "everything `type_preservation.v`
  needs, plus its own machinery."
- 108 top-level Lemma/Theorem declarations, exactly **1** fully `Admitted`
  (`t_progress_be`, containing 5 separate `admit.` sites internally), the
  rest `Qed`-proved.
- All 5 `admit.` sites are, per the author's own inline comments, the exact
  same `lane_`-union generator-encoding obstacle diagnosed (before this file
  was even available to read) in `rocq_proof_intuition.md` via commit-history
  archaeology — now directly confirmed, not just inferred. One of the 5
  (a `VLOAD` + oversized `SPLAT` memarg case) reads more like a possible
  under-constrained typing rule than a proof-tactic gap — flagged as worth a
  closer look if/when this file is actively worked on, separate from the
  other 4 which are squarely the lane-encoding issue.
- Since our Lean port is free to use a different proof strategy per the
  original task instructions, and the obstacle is specifically about how
  *Rocq's* `lane_` union type collapses information — **it's worth checking
  early whether the Lean `lane_`/`Jnn`-equivalent encoding in `wasm2.0.lean`
  has the same collapse before assuming this gap is permanent for us too.**
  If it doesn't, this could be a case where the Lean port closes something
  Rocq structurally can't — flagged as a genuine opportunity, not just a
  gap to mirror.

### 3e. Smaller changes

- `axioms.v`: 2 → 9 axioms. `nbytes_len`/`ibytes_len` (the two we already
  ported) are **byte-for-byte unchanged** (only whitespace reformatting) —
  our existing port of those two remains correct as-is. 7 new axioms added:
  `nbytes_len'`, `ibytes_len'`, `ibytes_len''`, `vbytes_len'`, `truncz_quot`,
  `lanes_len`, `nbytes_inv`, `ibytes_inv`, `vbytes_inv` — all vector/SIMD or
  inverse-bijection facts, needed by the new vector preservation lemmas in
  3a. Should be ported alongside that work, into `HelperLemmas.lean`
  (alongside the existing two).
- `helper_lemmas.v`: 850 → 657 lines, 63 → 53 declarations. **Removed**:
  `add_false`, `concat_cancel_last_n`, `Forall2_forall2`/`weak`/`weak2`/`weak3`/
  `weak4`, `Forall2_list_update`/`2`/`_both`/`_func`, `Forall2_lookup`/`2`,
  `Forall2_nth`/`2`, `Forall_nth'`, `leadd`, `length_app_lt`,
  `list_update_func_split`/`_strong`, `list_update_map`, `lookup_list_update_func`,
  `lt_irrefl`, `ltsize`, `repeat_size` (24 total). **Added**: `add_subBN`/`'`,
  `append_label`/`_local`/`_return`, `cvt_succ`/`'`, `Forall2_seq_size`/`_size`/
  `_size2`, `id_succ_N`, `prepend_local`/`_return`, `sizecat'`, `sizeN_inj` (14
  total). Net: several lemmas our `HelperLemmas.lean` Phase-1 skeleton
  already stubbed (see `proof_prioritization.md` Tier B #2's "tier-0
  cluster") no longer exist upstream at all — they should either be dropped
  from our port target list (if genuinely unused by anything downstream) or
  independently justified as still-useful even though Rocq removed them
  (unlikely to be worth the effort given the project's "lemma-for-lemma"
  mandate).
- `subtyping.v`: 914 → 1006 lines, purely additive (`cvt_N_to_ssrnat`,
  `cvt_ssrnat_to_N_le`, `size0nil'`) — no renames, no removals, our existing
  `Subtyping.lean` port (including the already-proved Tier A lemmas) is
  unaffected.
- `typing_lemmas.v`: 2222 → 2384 lines, 81 → 75 declarations. **Removed**:
  the entire `fun_*idx__nat`/`fun_nat__*idx`/`fun_u32__nat`/`fun_nat__u32`
  index-conversion family (14 lemmas) — likely folded into base-spec
  machinery given how much `wasm.v` itself grew. **Added**:
  `ai_typing_inversion'`, `construct_instr_from_ai`/`_single`,
  `construct_instrs_from_ais`, `revert_to_instr_from_ai`/`_instrs_from_ais`,
  `seq_mid_not_null`, `wf_admininstr_instr` — worth checking whether any of
  our stubbed `TypingLemmas.lean` signatures reference the removed
  `fun_*idx` family (if so, they need re-deriving against whatever
  `wasm2.0.lean` now provides for index conversion instead).
- `helper_tactics.v`: 410 → 452 lines (Ltac only, per project convention
  this is not ported 1:1 regardless — no action needed).
- `specification/wasm-2.0/*.spectec` and the OCaml backend/frontend/middlend
  files also changed in this merge — these are the SpecTec pipeline that
  *generates* `wasm2.0.lean` and (separately) `wasm.v`; they explain *why*
  `wasm.v` grew so much (9182-line diff) but are not something this project
  ports directly. `wasm2.0.lean` itself was **not** touched by this merge
  (confirmed: absent from the merge diffstat) — the parallel `*_is_wf` audit
  effort's file is unaffected by this resync.

## 4. What this means for the three bundle2 documents (not rewritten — see addenda)

- `rocq_proof_intuition.md`: core narrative (staging-directory workflow, file
  build order, the `lane_`-union diagnosis) holds up and is now *more*
  strongly evidenced (3d above). The one correction: it characterized SIMD
  gaps as spanning Preservation *and* Progress; they now only span Progress.
  See `rocq_proof_intuition_addendum.md`.
- `proof_dependencies.md`: file-level linear chain is still right for the 6
  already-ported files; `type_progress.v` slots in as a *parallel* branch off
  `typing_lemmas`/`extension_lemmas`/`subtyping`/`axioms`, not downstream of
  `type_preservation`. See `proof_dependencies_addendum.md`.
- `proof_prioritization.md`: several tiers reference now-stale names
  (extension lemmas) or now-removed lemmas (helper_lemmas tier-0 cluster);
  Tier H #36 is now done; #37 is unblocked with a real digest available; and
  a large new body of closed-upstream Preservation/SIMD work (3a) needs a
  new tier. See `proof_prioritization_addendum.md` for the concrete tier-by-
  tier deltas.

## 5. Safety

All of the above was produced via read-only inspection (`git show`/`diff`/
`status` against already-local commit objects, `gh api` for the live branch
tip check, `grep`/`wc`/`awk` on scratch copies under `/tmp/rocq_diff/`) plus
writes confined to `spectec/src/test-lean-claude/claude-logging/`. Nothing
outside `spectec/src/test-lean-claude/` was written or mutated. Safety check
re-run after this bundle, see `claude-logging/safety-checks/`.
