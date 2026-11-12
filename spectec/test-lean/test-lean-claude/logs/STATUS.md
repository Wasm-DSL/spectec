# Live status (always overwritten — this is the resume point)

Last updated: 2026-09-23 ~01:25 UTC, by Claude (autonomous run per user's
mid-task instruction to keep working through usage/context limits without
stopping to ask — see `logs/DECISIONS.md` for the full instruction text).

**A full session report has been written to `logs/FINAL_REPORT.md` — read
that first**, it's the intended entry point for the user on return. This
file is the lower-level "what do I do next" resume pointer.

## Headline results (see `FINAL_REPORT.md` for the full write-up)
1. Every `sorry` in `test-lean/typing_lemmas.lean` (4 clusters) has a fix in
   this folder — 3 drop-in, 1 (`instrs_seq_typing_inversion`) a corrected
   restatement needing your decision.
2. `StoreExtension.lean`'s `store_extension_reduce` is 16/23 real (Isabelle:
   1/23). All 7 remaining cases are now *confirmed* blocked (not just
   unchecked), for concrete, documented reasons.
3. `MemoryWriteAxioms.lean` ports Rocq's own length axioms and gets 2 of
   those 7 cases down to needing one more (Rocq-unprecedented) axiom —
   flagged as a decision, not added unilaterally.

## What's done and verified (all confirmed via `lake env lean
test-lean-claude/<File>.lean` from `spectec/test-lean/`, each exiting with no
output = 0 errors)

* `Extension.lean` — 0 sorry.
* `Subtyping.lean` — 0 sorry.
* `StoreExtension.lean` — 16/23 `Step` cases real, 7 remain `sorry`.
* `InstrtypeSub.lean` — 0 sorry.
* `CounterexampleCheck.lean` — 0 sorry.
* `SeqTypingInversion.lean` — 0 sorry.
* `MemoryWriteAxioms.lean` — 0 sorry (2 new `axiom`s, both Rocq-precedented).
* Safety check passes as of the last run (`check-20260923T000650Z.txt`).

## What's in progress / next
No file is currently mid-edit / broken; all seven `.lean` files compile
clean. Everything remaining needs either your input (the two flagged
decisions) or a substantially bigger scoping/porting effort
(`Store_ok`/`Moduleinst_ok`/`Table_ok`/`Global_ok`) that wasn't started —
see `PROGRESS.md`'s "Not yet started" section if picking that up.

## How to resume if this session was cut off mid-file
1. Read `logs/FINAL_REPORT.md` first.
2. Read `PROGRESS.md` top-to-bottom for the full per-file table and priority list.
3. Read `logs/DECISIONS.md`'s last several entries if more detail is needed.
4. Run `bash spectec/test-lean/test-lean-claude/safety-checks/check.sh` from
   `/home/zhengyew/spectec` before writing anything.
5. Recompile every file in `PROGRESS.md`'s table before trusting its
   "✅ compiles" status.

## Cadence
No fixed check-in interval (not a `/loop`). Worked continuously this
session; this checkpoint reflects a natural pause after the tractable work
ran out — see `FINAL_REPORT.md` for why.
