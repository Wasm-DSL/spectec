## Context absorption

Read every file under `spectec/src/test-lean-claude/claude-logging/`
(`README.md`, `safety-checks/check.sh` + latest check output, both
`for-claude/` and `for-humans/` notes, `is_wf_theorems.md`, and the full
`verbatim_dialogue_log/bundle1` and `bundle2` — prompts, responses,
modelinfo files, and bundle2's three `user_requested_documents/`) before
doing anything else, per your instruction to pick this up cold and behave as
the same standing session. Adopting its standing rules from here on:

- **Safety constraint**: never modify anything outside
  `spectec/src/test-lean-claude/` (reading outside it is fine and was used
  extensively this turn — see below); run the periodic safety-check script
  and log its output; any agent I spawn must be told the same rule.
- **Logging obligation**: every exchange, including mid-process ones, gets
  its own `bundleN/` with verbatim `prompt_N.md`, `response_N.md`, and a
  `response_N_modelinfo.md` — this is bundle3, for this exchange.

### Item 1 — did the re-sync go correctly? Yes.

Verified via `gh api repos/Wasm-DSL/spectec/branches/rocq-backend-proof` (the
**live** GitHub branch, not the local checkout — per your instruction) that
its current HEAD is `a8b585cdb536b2b2e53ff45fa8010de88f05a042`, exactly the
second parent of your merge commit `b78d56eeb`, and that this is still the
tip (no commits landed after it). Checked for merge-conflict markers and a
clean `git status` across every path the merge touched — none found. Your
merge is correct and complete: `spectec/test-rocq/theories/` is now
byte-identical to the live upstream HEAD.

### Item 2 — on your question, and being well-positioned to resume

You're right that "read the git repository you gave me" was always the
correct instruction — there was never a real live-vs-local *tooling*
distinction, just a stale *copy*: the previous session found the working
copy of `spectec/test-rocq/theories/` in this repo had fallen behind the
`rocq-backend-proof` branch on GitHub (frozen at a July commit while GitHub
had moved on by ~3 months). Reading "the repo you gave me" was and is
correct; the problem was that the copy hadn't been kept in sync, not a
misdirected read. That's now resolved by your merge, confirmed identical to
live via the `gh api` check above (no local `git fetch` needed — read-only,
via the GitHub API, per your instruction to check the live source). I'm
well-positioned to resume porting: the local checkout is current, complete
(`type_progress.v` now present, previously entirely missing), and I didn't
need to write anything outside `spectec/src/test-lean-claude/` to do any of
this checking.

### Item 3 — updates based on the live Rocq proof

Diffed the old checkout (`5b03ae067`, what our 6 already-ported Lean files
were built against) against the new one (`a8b585cdb`) precisely — both
commit objects were already present locally, so this was a direct `git
show`/`diff`, no fetch needed. Full evidence and findings in
`bundle3/updated_documents/resync_impact_report.md`; short, pointed addenda
to each of bundle2's three documents (not touching the originals, per your
instruction) in the same folder. Also updated `for-claude/NOTES.md` in place
(it's living project documentation, not part of the verbatim dialogue log,
so updating it directly — rather than versioning it into bundle3 — matches
how the project already treats that directory) and added
`for-claude/digest_type_progress.md` (new file, digesting the previously-
unavailable Progress file).

**Headline findings** (detail + evidence in the impact report):

1. **Preservation's SIMD/vector gap is closed upstream** —
   `type_preservation_pure.v` and `type_preservation.v` both went from
   several `Admitted` lemmas (all SIMD, matching the July commit-message —
   "Vector Instructions for Preservation proven") to zero, with ~90 new
   fully-proved vector lemmas added. Our project's `sorry`s there are no
   longer "faithful mirrors of a permanent Rocq gap" — they're just
   unfinished Phase-2 work now, and there's real Rocq content to port
   against.
2. **`extension_lemmas.v` was renamed wholesale** — every
   `store_extension_*`/`*_extension_refl*` name our `ExtensionLemmas.lean`
   was ported against is gone, replaced by `Extend_store_*`/`extend_*_refl*`
   (converging toward the auto-generated Lean file's own naming). The
   underlying facts still hold; the names in our file are now stale relative
   to "signatures must be directly from the Rocq proof."
3. **`type_progress.v` exists now** (4260 lines) — the Progress half of type
   safety, previously unavailable. Digested; it depends on
   `helper_lemmas`/`typing_lemmas`/`extension_lemmas`/`subtyping`/`axioms`
   only, **not** on either Preservation file (corrects a guess in
   `proof_prioritization.md`). It has exactly one remaining gap
   (`t_progress_be`, 5 `admit.` sites), and the source's own comments confirm
   — word for word — the `lane_`-union generator-bug diagnosis the previous
   session reached via commit-history archaeology before this file was even
   available to read.
4. A handful of `helper_lemmas.v` lemmas our `HelperLemmas.lean` had already
   stubbed no longer exist upstream at all (24 removed, including 3 that
   `proof_prioritization.md` Tier B #2 flagged as "do next"); `axioms.v`
   grew from 2 to 9 (our existing two are byte-identical, still correct);
   `typing_lemmas.v` dropped an index-conversion helper family and added a
   few new construction/inversion lemmas; `subtyping.v` only grew
   additively, no changes needed there.
5. One real Preservation-side gap remains upstream:
   `construct_meminsts_grow` (the memory-growth bound,
   `proof_prioritization.md` Tier F #27) — still `Admitted`, but new
   supporting arithmetic lemmas were added alongside it, suggesting it's
   closer to closable than before.

None of this needed writing anything outside
`spectec/src/test-lean-claude/` — all verification was read-only (`gh api`,
`git show`/`diff`/`status` against local objects, scratch-only `grep`/`awk`
under `/tmp/rocq_diff/`, which is outside the repo entirely and not part of
this project's tracked tree).

### Everything still builds; safety check clean

No `.lean` files were touched this turn (this was a documentation/analysis
pass, not a coding one), so `lake build`'s last-known-good state from bundle2
is unaffected. Safety check re-run just now: the only paths outside
`spectec/src/test-lean-claude/` reported are the same pre-existing untracked
scratch files visible in the conversation's opening `git status` (e.g.
`spectec/blahblah.lean`, `spectec/wasm2.0.v`, `spectec/1---`, etc.) — nothing
from this session.

## What's next

Per the addenda's suggested revised ordering: a small rename pass over
`ExtensionLemmas.lean`'s existing lemma names (cheap, unblocks clean further
work there), then resume Phase 2 roughly per `proof_prioritization.md`'s
original tiers with the corrections applied — including two genuinely new
bodies of work this resync unlocked: porting the now-real vector-instruction
preservation lemmas (proposed "Tier E2"), and starting on `type_progress.v`
(proposed "Tier I"), which per the corrected dependency graph can proceed in
parallel with Preservation work rather than after it. I'll continue into
that unless you'd like to redirect me.
