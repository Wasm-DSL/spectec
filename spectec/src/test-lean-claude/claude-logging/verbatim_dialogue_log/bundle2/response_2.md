## Done — plus one important finding that needs your input

### Logging practice

`bundle1/response_1_modelinfo.md` is filled in (model identity, session
identity, environment, token-usage figures I could observe — with honest
gaps flagged where something isn't exposed to me, like reasoning-effort
level). `bundle2/` now has this exchange's `prompt_2.md` (verbatim) and
will get this `response_2.md` + `response_2_modelinfo.md`. I'll keep this
going for every future exchange, including mid-process ones, until you
say stop.

### Proof reuse (comb + substitute)

Read the prior sessions' completed Lean files in full
(`InstrtypeSub.lean`, `Extension.lean`, `Subtyping.lean`,
`SeqTypingInversion.lean` from `test-lean/test-lean-claude/`) and
substituted in everything that matched. Confirmed compiling now, with
real proofs (no longer `sorry`):

- **`Subtyping.lean`**: `valtype_sub_refl`/`_trans`, `resulttype_sub_refl`/
  `_trans`/`_app`/`_split_sup`/`_split_sup'`, `instrtype_sub_refl`,
  **`instrtype_sub_trans`** (the hardest lemma in the file — compiled on
  the first try once ported), `instr_subtyping_weaken2`.
- **`ExtensionLemmas.lean`**: the full reflexivity family for all 6
  store-component extension relations plus `store_extension_refl` itself
  (13 lemmas total).

While doing this I found and fixed a **real bug in my own Phase-1
stubs**: I'd stated `func_extension_refl0`/`table_extension_refl0`/etc.
without the `wf_*` well-formedness hypotheses that `Extend_funcinst`/
`Extend_tableinst`/etc.'s actual constructors require (confirmed by
reading `wasm2.0.lean` directly) — unprovable as originally stated. Fixed
the signatures, then proved them for real. I also confirmed something I'd
only flagged as an open question before: `Func_extension`/`Store_extension`
(the names Rocq's `extension_lemmas.v` uses) genuinely don't exist
anywhere in the Rocq sources under any declaration form — likely stale
names from before a backend regeneration — so using `Extend_funcinst`/
`Extend_store` (the names that actually exist) was the right call.

### The four requested documents

All written to
`claude-logging/verbatim_dialogue_log/bundle2/user_requested_documents/`:

- **`rocq_proof_intuition.md`** — combines my own reading of the source
  with a dedicated commit-history investigation (33 commits, single
  author, Mar–Sep 2026) I had a background agent run against the live
  GitHub branch. Covers: the staging-directory workflow the author used
  (`folder-to-exclude/`, never in the compiled build until a file is
  trustworthy), the actual build order (helper/subtyping → typing →
  *pure* preservation → extension+axioms → full preservation → progress,
  dead last by 4+ months), a July generator-rename incident that's the
  direct origin of one of our `sorry`s, and — importantly — a diagnosed
  generator-level bug (not a proof-difficulty issue) behind every
  remaining SIMD gap in the upstream Progress file.
- **`proof_dependencies.md`** — full dependency graph, file-level (a
  strict linear chain, confirming there's really only one sensible
  build order) and within-file (tiered by what blocks what).
- **`proof_prioritization.md`** — the requested ordering with
  justification for every item, organized into 8 tiers from "already
  done" through "deferred pending your input."

### The important finding: our local Rocq checkout is stale

While researching this, I discovered **our local
`spectec/test-rocq/theories/` is frozen at commit `5b03ae067`
(2026-07-01)**, while the live `rocq-backend-proof` branch has moved to
`a8b585cdb` (2026-09-22). Diffing the two directly:

```
 extension_lemmas.v   | 3435 +++++---
 type_preservation.v  | 2752 +++---
 type_progress.v      | 4260 +++++++++   (missing locally — entirely)
 wasm.v                | 9182 +++++++++++++++-----
 (+ smaller changes to every other file)
```

**`type_progress.v` — the Progress half of type safety — doesn't exist
in our local checkout at all.** It's real and substantial upstream
(4260 lines), and per the commit history it's the file the original
author struggled with most (30+ TODOs, 6 remaining `admit`s, all tracing
to one diagnosed generator bug in how SIMD lane types get encoded).
Everything else we have locally is also significantly behind — in
particular `extension_lemmas.v` (which we've been actively working from)
is missing whatever was added in the July 22 "done except meminst grow"
commit and later.

I have **not** touched anything to fix this — re-syncing the checkout
means modifying files outside `spectec/src/test-lean-claude/`, which is
outside my authorized boundary without your say-so. I've filed this as
Tier H in the prioritization doc (explicitly deferred) rather than acting
on it. **This is a decision I need from you**: should I (a) leave the
local checkout as-is and keep working from what we have, (b) re-sync it
to current upstream HEAD, or (c) something else (e.g. you handle the
sync)? This affects both correctness (some of what I've already ported
may be incomplete relative to upstream) and scope (whether Progress is
part of this project going forward).

### Everything still builds clean

Full `lake build` from `spectec/src/test-lean-claude` succeeds; safety
check confirms nothing outside that directory has been touched.
