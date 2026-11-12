# Decision / doubt log (append-only, newest at bottom)

Format: `## <UTC timestamp>` then a short note. Anything the user should
double-check on return is marked **[REVIEW]**.

## 2026-09-22 ~22:50 — task start
Set up `test-lean-claude/` with `safety-checks/` (baseline git-status snapshot
+ `check.sh` that diffs current `git status --porcelain` against baseline and
fails if anything *outside* `test-lean-claude/` changed). Verified `lake env
lean test-lean-claude/00_sanity.lean` (a throwaway file, later left in place)
successfully imports `wasm2.0.lean` and `custom_notation.lean` from a
subfolder — confirms Lean's module resolution doesn't care about physical
directory nesting, only that the package root is on the search path, so no
`lakefile.lean` edits are needed (and none were made — that file is outside
`test-lean-claude/` anyway).

## 2026-09-22 ~23:00 — scope decision
**[REVIEW]** Decided to build new, from-scratch Lean proofs in this folder
against the *existing* `wasm2.0.lean`/`typing_lemmas.lean`, rather than trying
to literally transliterate Rocq/Isabelle tactic-by-tactic. The three
proof assistants have different automation (Rocq: `ssreflect`/custom tactics
like `ineq_to_prop`; Isabelle: `metis`/`auto`; Lean: `omega`/`simp`/`aesop`),
so a line-by-line port isn't meaningful — instead each Lean lemma reproduces
the *same theorem statement* (checked against the generated `wasm2.0.lean`
constructor shapes directly, not against Rocq/Isabelle syntax) with whatever
Lean-idiomatic proof closes it. Provenance (which Rocq/Isabelle lemma this
corresponds to, by name + line number) is recorded in each theorem's doc
comment and in `PROGRESS.md`'s table, so the mapping stays auditable.

## 2026-09-22 ~23:05 — Extension.lean complete
`Extension.lean` compiles with 0 errors, 0 `sorry`. Covers all 6
`extend_*_refl` (globalinst, funcinst, datainst, eleminst, tableinst,
meminst) plus the store-wide `Extend_store` reflexivity, matching Rocq
`extension_lemmas.v` and Isabelle `Properties.thy`'s fully-proved reflexivity
lemmas exactly (both sources treat these as trivial/complete, no Admitted/
sorry on either side, so this Lean version being fully real is expected, not
a case of "lucky first try on something hard").

**[REVIEW]** Neither Rocq nor Isabelle has a *transitivity* lemma for any
`Extend_*` relation anywhere in the fetched source files (checked via
`grep -rn "trans" *.v | grep -i extend`, zero hits). I did not attempt one
either. If a future step (e.g. `store_extension_reduce`) turns out to need
transitivity to chain multiple reduction steps, that would be genuinely new
work beyond both source developments — flagging this now so it isn't
mistaken later for a missed/incomplete port.

## 2026-09-22 ~23:10-23:20 — Subtyping.lean, omega/abbrev gotcha
Hit a real Lean quirk worth recording since it'll recur: the backend's
numeric type abbreviations (`abbrev n : Type := Nat`, `abbrev m : Type :=
Nat`, likely also `N` etc.) are *not* transparent to `omega` — a hypothesis
or goal stated as `x : n` (rather than `x : Nat`) makes `omega` fail with a
misleading "counterexample ↑x ≥ 0" message that looks like a coercion bug but
is actually just omega refusing to look past the abbrev. Worked around by
avoiding `omega` in favor of `subst`/`rw`/`Nat.le_trans`/`Nat.le_refl`
wherever the values in play are typed via one of these abbrevs. Recorded as a
standing convention in `PROGRESS.md`.

`Subtyping.lean` (limits/externtype subtyping refl+trans+injectivity, 6
theorems) now compiles with 0 errors, 0 sorry, on the first attempt after
fixing the omega issue and one shadowing issue (`obtain ⟨m⟩ := u` shadowing
the `m` abbrev — renamed to `mb`/`nb`).

## 2026-09-22 ~23:25 — mid-turn instruction received
User sent a message (arrived mid-tool-call) saying they'll be away and I
should run autonomously until usage/context limits, log doubts/decisions here
and in `logs/STATUS.md`, not block on questions I can't get answered, and
write a final report in this folder if/when I do stop. Set up `PROGRESS.md` +
`logs/` in response; continuing to keep both updated as the primary
continuity mechanism (no reliable way to "schedule" a wake-up outside of the
`/loop` skill, which this session wasn't invoked under, so continuity relies
on this log plus whatever context-window/session persistence the harness
already provides). Everything from this point on in the log happened after
this instruction, under the "keep working autonomously" directive.

## 2026-09-22 ~23:35 — StoreExtension.lean, and a real limit hit
Wrote `StoreExtension.lean`: `store_extension_reduce`, an induction on `Step`
(`wasm2.0.lean:11106-11205`, 23 constructors) matching Isabelle's
`reduce_store_extension` (`Properties.thy:84-164`) case-for-case. Proved
`pure`, `read` (Isabelle leaves `read` `sorry` even though it's exactly as
trivial as `pure` — flagging this as likely just an oversight there, not a
real difficulty), and all 3 congruence cases (`ctxt_label`/`ctxt_frame`/
`ctxt_instrs`) via the auto-generated induction hypothesis — 5/23 real,
beating Isabelle's 1/23. The other 18 (store-mutating leaf cases) are a
single `sorry` catch-all: confirmed by inspecting `Step.global_set`'s
constructor that these genuinely need typing hypotheses (e.g. mutability of
the global being set) that the reduction rule itself doesn't carry — so
completing them isn't just "more of the same," it needs `Instrs_ok2`/typing
infra ported first, which is a materially bigger task. Recorded as the
current top priority in `PROGRESS.md`.

**[REVIEW — technical gotcha, will recur]** `import` between two files in
`test-lean-claude/` **does not work**: `lake env lean` errors with `unknown
module prefix 'test-lean-claude'`. Root cause: `test-lean/lakefile.lean`
(outside this folder, not editable) only registers `wasm2.0`/
`custom_notation`/`typing_lemmas`/`ExtendedDeriveDecEq`/`sandbox_5`/
`sandbox_10` as buildable `lean_lib` modules with prebuilt `.olean`s; nothing
under `test-lean-claude/` has one, and `lean`'s import resolution only
searches for `.olean` files (via `LEAN_PATH`), never falls back to compiling
a sibling `.lean` source on demand. I considered manually building an
`.olean` into `.lake/build/lib/lean/` to fix this, but that directory is
*outside* `test-lean-claude/`, so writing there — even though it's a build
cache, gitignored, and touches nothing pre-existing — would trip the safety
check's letter if not its spirit; decided against it out of caution. Fix
adopted instead: every file in this folder only imports `wasm2.0`/
`custom_notation` directly and duplicates whatever small lemmas it needs from
sibling files (currently: `Extension.lean`'s 6 `extend_*_refl` lemmas +
3 helpers, duplicated into `StoreExtension.lean`). This is genuine,
acknowledged duplication, not an oversight — recorded here and in
`PROGRESS.md`'s table so it isn't mistaken for one later.

## 2026-09-22 ~23:40-23:55 — InstrtypeSub.lean: scoped down, then finished anyway
Set out to close two live `sorry`s in the pre-existing `test-lean/
typing_lemmas.lean` (`instrtype_sub_refl` line 1112, `instrtype_sub_trans`
line 1545), found via `grep -n sorry` there (this also **corrected** a stale
note carried over from before this folder existed, which had claimed
`instrtype_sub_trans` was already proved — it is not, in the file's current
state as of this session).

Proved `instrtype_sub_refl` immediately (trivial given `resulttype_sub_refl`,
re-derived from `wasm2.0.lean`'s `Resulttype_sub`/`Valtype_sub` directly since
`typing_lemmas.lean`'s own copy isn't in an importable module — see the
cross-file-import limitation above). Looked at Rocq's `instrtype_sub_trans`
(`subtyping.v:434`) for the proof strategy and initially judged it too costly
to port: it needs a "split a `Resulttype_sub` of a concatenation" lemma pair
(`resulttype_sub_split`/`_split_sup`, `subtyping.v:344-420`) involving
`take`/`drop` index arithmetic, and Rocq's own author left an ASCII diagram
in a comment explaining the construction — a signal it wasn't easy even for
them. Initially left it `sorry` with that reasoning documented.

**[REVIEW]** On reflection, decided the "too costly" judgment call deserved a
real attempt rather than a guess, since the two split lemmas are actually
just "`Resulttype_sub` is `length`-equality plus pointwise `Valtype_sub`
across a `List.zip`" restated across `List.take`/`List.drop`, which Lean's
`List.zip_append` (a library lemma taking a length-equality hypothesis) handles
directly — no manual induction needed, unlike Rocq's from-scratch treatment.
Wrote `resulttype_sub_split` and `resulttype_sub_split_sup`, both compiled
clean on a very small number of fixups, then assembled `instrtype_sub_trans`
following Rocq's construction (their variable names mapped in the theorem's
own doc comment) — **it compiled clean, 0 sorry, first full attempt**. This
whole file (`InstrtypeSub.lean`) is now sorry-free and both proofs are ready
to paste into `typing_lemmas.lean` verbatim (flagged in `PROGRESS.md`'s
"suggested immediate follow-up" — not done automatically, editing that file
is outside this folder's scope unless the user asks).

Net effect: this is the single highest-value result in this folder so far —
a genuine, complete fix for two `sorry`s in the user's own hand-written
proof frontier, not just a from-scratch translation exercise.

One other reusable technical note: `conv_lhs` is **unavailable** even with
`wasm2.0.lean` (and hence Mathlib, transitively) imported — confirmed via an
isolated repro (`import «wasm2.0»`, bare `conv_lhs => rfl` on a trivial goal,
"unknown tactic"). Worked around throughout by using `calc` with a targeted
`rw` on one side of an explicit equation instead of `conv`/`conv_lhs`.
Recording this since it'll otherwise cost a repeat diagnosis later.

## 2026-09-22 ~23:55 — instr_subtyping_weaken2 closed too; a THIRD `sorry` fixed
`instr_subtyping_weaken2` (`typing_lemmas.lean:1536-1543`) turned out to be a
direct one-shot application of `resulttype_sub_split` + `resulttype_sub_trans`
(both already built for `instrtype_sub_trans` above) — added to
`InstrtypeSub.lean`, compiles clean, 0 sorry. `InstrtypeSub.lean` now closes
**three** of the pre-existing file's `sorry`s (`instrtype_sub_refl`,
`instrtype_sub_trans`, `instr_subtyping_weaken2`), all ready to paste in.

## 2026-09-23 ~00:05 — **[REVIEW — IMPORTANT, please read]** found a likely-FALSE
## theorem statement in `typing_lemmas.lean`, verified with a Lean counterexample
Looked at the file's one remaining `sorry` cluster, `instrs_seq_typing_inversion`
(lines 2002-2071 — the `seq`/`sub`/`frame` cases, plus a lot of commented-out
WIP in `seq`), to judge whether it was worth attempting after the run of
successes above. It is stated as:

    Instrs_ok c (i :: is) (ts1 f-> ts3)
    → ∃ ts2, Instr_ok c i (ts1 f-> ts2) ∧ Instrs_ok c is (ts2 f-> ts3)

i.e. "any typing of a cons'd instruction sequence splits into a typing of the
head *instruction* (`Instr_ok`, singular) and a typing of the tail sequence."

**This looks false as stated**, and I built and compiled a concrete Lean
counterexample confirming it (`test-lean-claude/CounterexampleCheck.lean`,
0 errors — both examples in that file typecheck). The issue: `Instrs_ok`
(the *sequence*-level judgment) has a `frame` rule
(`wasm2.0.lean:10043-10047`) that can prepend an arbitrary shared prefix
`t_lst` to both sides of an already-derived sequence typing. `Instr_ok` (the
*singular*-instruction judgment) has **no such rule** — e.g. its `const` case
(`wasm2.0.lean:9676-9679`) fixes the input type to the literal empty list,
unconditionally, no flexibility.

Concretely: `Instrs_ok C [CONST I32 c] ([I32] f-> [I32,I32])` is derivable
(build `Instrs_ok C [CONST I32 c] ([] f-> [I32])` via `.instr`, then prepend
`[I32]` via `.frame`) — but there is **no** `ts2` for which
`Instr_ok C (CONST I32 c) ([I32] f-> ts2)` holds, since `const`'s rule forces
the input to be `[]`, not `[I32]`. So for this `i`/`is`/`ts1`/`ts3` instance,
the theorem's existential has no witness, even though its hypothesis is
satisfiable. `CounterexampleCheck.lean` proves both halves directly: (a) the
frame-derived `Instrs_ok` fact type-checks as claimed, (b) `¬ ∃ ts2,
Instr_ok C (CONST I32 c) ([I32] f-> ts2)` — the second one closes by a bare
`cases h` after unfolding, i.e. Lean confirms there is *no* matching
constructor case at all.

**Why this hasn't caused a problem yet**: the theorem's proof is `sorry`'d
exactly in the cases (`seq`, and by extension the commented-out WIP) where
this gap would bite, so no unsound proof has actually been completed — the
file is safe, just permanently stuck on this lemma as stated.

**Two candidate fixes** (not chosen between — flagging both for the user,
this is a judgment call about what the lemma is *for* downstream, which I
don't have visibility into):
1. Weaken the conclusion to `Instrs_ok c [i] (ts1 f-> ts2)` (sequence-level,
   not singular) instead of `Instr_ok c i (ts1 f-> ts2)` — lets the
   singleton wrap its own `frame`/`sub`. Likely provable by a real induction
   on `Instrs_ok` now (unlike the original), since every case has a genuine
   way to discharge it.
2. Match the file's own established idiom elsewhere (`ai_typing_inversion`,
   line 1119) and state it via *principal* typing +  `instrsub<` instead of
   raw `Instr_ok`: `∃ ts1' ts2', instr_principal_typing c i (ts1' f-> ts2')
   ∧ ((ts1' f-> ts2') instrsub< (ts1 f-> ts2)) ∧ Instrs_ok c is (ts2 f-> ts3)`.

Did not attempt either fix or the underlying proof — this needs a decision
from whoever is driving `typing_lemmas.lean` about which shape the downstream
callers of `instrs_seq_typing_inversion` (if any exist yet) actually need,
which I have no visibility into from this folder alone. Recording this as
the most important open finding from this session.

## 2026-09-23 ~00:15 — candidate fix #1 confirmed correct by Rocq precedent (not proved)
Went looking in Rocq's `typing_lemmas.v` for anything analogous, and found
`ais_seq_typing_inversion` (line 1080) — the *administrative*-instruction
counterpart of exactly this lemma. Its conclusion is stated as
`Instrs_ok2 v_S v_C [v_ai] (t1s :-> t3s)` — i.e. **the sequence-level
judgment applied to a singleton list**, not a singular per-instruction
judgment. This is exactly "candidate fix #1" from the entry above, now
upgraded from "a guess" to "confirmed by the one mature reference
implementation that has the analogous lemma at all." High confidence that's
the right restatement for `instrs_seq_typing_inversion` too.

Read through Rocq's ~45-line proof (`dependent induction` on `Instrs_ok2`,
with a 3-way `destruct`+`discriminate` on how `[v_ai]++v_ais` splits across
the `seq` rule's two sub-lists) to sanity-check the corrected lemma is
actually provable, not just non-obviously-false. Worked out the Lean proof
sketch for the trickiest sub-case (the `seq` case where the cons'd head `i`
falls inside the *first* half, which is `[]`): the `Instrs_ok C []
(t1 f-> t2)` premise gives (via the already-established `instrs_empty_typing`
characterization in `typing_lemmas.lean`) `t1 subs< t2`; applying the IH to
the *second* half's own derivation yields `Instrs_ok C [i] (t2 f-> ts2')`;
composing these via `Instrs_ok.sub` (widening the input side from `t2` down
to `t1` using the subtyping fact, with `resulttype_sub_refl` on the output
side) yields `Instrs_ok C [i] (t1 f-> ts2')` — the piece actually needed.
The other `seq` sub-case (head falls in a *nonempty* first half) is
symmetric-ish but needs its own IH application and a bit more bookkeeping.

**Did not attempt the full Lean proof [at first].** Rocq's version, even with
its own custom `destruct_list_eq` automation and mathcomp's
`cats0`/`cat0s`/`catA` lemma set doing a lot of the list-algebra for free,
still runs ~45 careful lines for the `seq` case alone, plus `sub`/`frame`
cases each needing their own `Forall_app`-style side-condition splitting.
Initially judged this a genuinely large proof (not a `InstrtypeSub.lean`-style
quick win) rather than something to force through under the time budget then
available — recorded the proof sketch above so a future attempt would have a
running start instead of restarting from the false statement.

## 2026-09-23 ~00:50 — attempted it anyway; it worked, 0 sorry
Given the proof sketch above was already fairly complete, decided the
remaining work (writing it out formally, handling `sub`/`frame`) was worth a
real attempt rather than stopping at "here's a sketch." Wrote
`SeqTypingInversion.lean`:

* `instrs_ok_nil_sub_gen`/`instrs_ok_nil_sub`: the "→" direction of
  `instrs_empty_typing`'s characterization (re-derived locally, matching what
  `typing_lemmas.lean` already has proved under that name but in a
  non-importable module). Compiled clean on the first *structurally correct*
  attempt — needed one real fix: `induction h using Instrs_ok.rec` requires
  generalizing *both* indices (`instr_lst` and `ft`) to plain variables before
  inducting, or the tactic fails with "Index in target's type is not a
  variable." My first draft only generalized `instr_lst`, leaving `ft`
  fixed — fixed by restating the goal as `instr_lst = [] → ∀ t1 t2, ft =
  mkFunctype t1 t2 → ...` (quantifying `t1 t2` *inside*, exactly the same
  fix needed for the `nil`-case lemma) rather than fixing them as outer
  theorem arguments — otherwise the induction hypotheses come out asking to
  prove facts about the *wrong* (outer, unrelated) `t1 t2` for every nested
  sub-derivation. This generalize-everything-inside-the-motive pattern
  recurred for every lemma in this file — recording it as a standing
  technique, not a one-off.
* `instrs_ok_nil_refl`, `instrs_ok_widen_in`, `instrs_ok_widen_out`: small
  helpers, `Instrs_ok.frame`/`Instrs_ok.sub` wrappers, straightforward.
* `instrs_ok_cons_gen`/`instrs_seq_typing_inversion_fixed`: the main event,
  following Rocq's case structure exactly (`empty` impossible, `instr` base
  case via `instrs_ok_nil_refl`, `seq` 3-way split on whether the cons'd head
  lands in the first or second half of the append via `cases i1`, `sub`/
  `frame` composing the IH with `instrs_ok_widen_in`/`_out` or
  `Instrs_ok.frame` respectively). **Compiled clean, 0 sorry**, after fixing
  one nasty bug (see next paragraph).

**[REVIEW — subtle bug, worth remembering]** Hit a genuinely confusing
`subst`-direction bug: inside a nested nested `by` block proving
`Forall wf_instr [i]` (`i` bound by an *outer* `intro`), I wrote
`intro x hx; simp at hx; subst hx` where `hx : x ∈ [i]` simplifies to
`x = i`. `subst hx` is ambiguous about *which* side to eliminate when both
are plain local variables — it silently chose to eliminate `i` (the
*outer*, already-in-use variable) rather than `x` (the freshly-introduced
one), replacing every occurrence of `i` in the surrounding context with `x`.
The next line's plain reference to `i` then failed with "unknown identifier
`i`" — genuinely surprising, since `i` had been valid on the *previous*
line. Fix: never blind-`subst` an equation between two pre-existing locals
when you need to keep one of them under its original name — use `rw [hx]`
(rewriting the *goal*, leaving the context's names alone) instead. Happened
identically in three separate places in this file (`seq`'s `nil` sub-case,
`sub`, `frame`) since they all share the same "prove `Forall P [i]` via
`intro x hx`" idiom — fixed all three the same way once diagnosed.

**Net result: `instrs_seq_typing_inversion_fixed` is a complete, 0-sorry
proof of the corrected lemma.** This closes the last open `sorry`-cluster in
`typing_lemmas.lean`'s current content — though, unlike `InstrtypeSub.lean`'s
three fixes, this one changes the theorem's *statement* (sequence-level
conclusion instead of singular `Instr_ok`), so it needs a maintainer
decision before going in, not just a copy-paste. See `PROGRESS.md`'s
"✅ Resolved" section.

## 2026-09-23 ~01:00-01:05 — StoreExtension.lean: 7/23 → 16/23, a wrong assumption caught
Went back to `StoreExtension.lean`'s single `sorry` catch-all (16 leaf cases)
having previously written it off as "these all need `Instrs_ok2`/typing
infra" by generalizing from the one case I'd actually checked in detail
(`global_set`, which genuinely does). **That generalization was wrong.**
Checked `local_set`'s actual `Step` constructor and `with_local`'s
definition directly: `with_local` only ever touches the *frame*
(`state.mk_state s {f with LOCALS := ...}` — `s` passed through completely
unchanged), so it's exactly as trivial as `pure`/`read`. Added
`store_extension_local_set`, compiled clean immediately.

That prompted a full re-read of all 23 `Step` constructors (rather than
relying on memory/assumption), which turned up **seven more** cases whose
own conclusion keeps the state `z` completely unchanged — every trap/failure
variant (`table_set_trap`, `table_grow_fail`, `store_num_trap`,
`store_pack_trap`, `vstore_oob`, `vstore_lane_oob`, `memory_grow_fail`): a
trap or a failed operation, by construction, never touches the store.
Factored the shared proof into one reusable `store_extension_same_state`
lemma and wired all seven in with one line each.

Also completed `table_set_val` (single-slot table write via `with_table`'s
doubly-nested `List.modify`): length-preserving, and `wf_tableinst` doesn't
constrain `REFS` at all (only `TYPE`), so — like `elem_drop`/`data_drop` —
no typing hypothesis needed. This one took real iteration (see below) but
got there.

**[REVIEW]** Net effect: `StoreExtension.lean` went from 7/23 to **16/23**
real cases in this pass, driven entirely by *checking things directly
instead of extrapolating from one example*. The remaining 7
(`global_set`, `table_grow_succeed`, `store_num_val`/`store_pack_val`/
`vstore_val`/`vstore_lane_val`, `memory_grow_succeed`) are genuinely
different in kind (real typing or postcondition facts needed), not just
unchecked — but that conclusion is now based on actually reading each one's
constructor, not on analogy. Recorded as a general lesson in
`PROGRESS.md`/here: when a pattern seems to generalize from one instance,
check the *others* directly before writing them all off as equally hard.

## 2026-09-23 ~01:10 — confirmed the remaining 7 `store_extension_reduce` cases are genuinely blocked
Before moving on, checked each of the 7 still-`sorry` cases directly rather
than leaving the earlier ("plausibly easy, plausibly not") hedge in place —
worth doing given how wrong the *previous* blanket assumption turned out to
be for 9 of the other 16. Result: all 7 really are blocked, for two distinct
reasons, not just "not yet tried":
* `store_num_val`/`store_pack_val`/`vstore_val`/`vstore_lane_val` need
  `nbytes_`/`ibytes_`/`vbytes_`'s output length to match the write size —
  checked these three functions directly (`wasm2.0.lean:3626-3681`): they're
  `hint(builtin)` **opaque axioms**, same category as `rat_to_nat` from the
  Task 1 report, and their (also `sorry`'d) `_is_wf` theorems assert only
  `Forall wf_byte`, no length fact. Nothing to prove this from without
  adding a new axiom.
* `table_grow_succeed`/`memory_grow_succeed` need a table/memory's declared
  minimum size to relate to its actual current length — checked
  `fun_growtable` directly (`wasm2.0.lean:9216-9239`, a real non-opaque
  inductive, not an axiom) and confirmed it hands over `wf_tableinst` of
  both old and new tables for free, but `wf_tableinst` itself never relates
  declared-minimum to actual length — that's a `Table_ok`-style *typing*
  invariant belonging to `Store_ok`/`Moduleinst_ok`, not ported here.

Recorded in `PROGRESS.md` item 1 so this doesn't get re-attempted without
first porting that typing layer.

## 2026-09-23 ~01:15-01:25 — MemoryWriteAxioms.lean: found Rocq's own axioms, then hit a second wall
Went back to check one specific claim from the entry above more rigorously:
is the `nbytes_`/`ibytes_`/`vbytes_` length gap *really* unfixable, or just
unfixed? Checked Rocq's `axioms.v` directly (27 lines, 0 declarations by the
earlier decl-count survey — hadn't actually opened it before this). It
answers the question directly: Rocq **also** cannot derive this and
resolves it by declaring `Axiom nbytes_len`/`ibytes_len` (plus rational-
division variants) from scratch, no proof. This is good confirmation that
the earlier "confirmed blocked" call was right, and also handed over the
exact fact needed, precedented in the reference implementation's own
trusted base.

Wrote `MemoryWriteAxioms.lean` with the Lean equivalents (`ibytes_len`,
`nbytes_len`, matching Rocq's shape and using `rat_to_nat` where Rocq uses
`Q` directly) plus a genuinely useful general lemma, `splice_length_ge`:
`with_mem`'s write, `(l.take nat ++ new) ++ l.drop (nat+nat_0)`, never
*shrinks* `l` as long as `new.length ≥ nat_0` — true unconditionally,
regardless of whether the write is actually in-bounds, because
`List.take`/`List.drop` clamp gracefully at the edges. (I'd initially
worried `store_pack_val`'s `Step` rule looks under-specified — no explicit
"in bounds" hypothesis unlike its `_trap` sibling — but this lemma shows it
doesn't matter for the *length* side of the obligation either way; whether
that's a real spec gap for other purposes is a separate question, not one I
chased further.)

**Then hit a second, unprecedented wall**: closing the actual `Step` case
also needs `wf_meminst` of the *written* bytes (not just their length) —
`Extend_meminst`'s constructor requires `wf_meminst` on both old and new
values, and `meminst`'s wf predicate, unlike `tableinst`'s, *does* constrain
its data (`Forall wf_byte BYTES`). Getting `Forall wf_byte b_lst` needs
either a third new axiom or invoking the generated file's own
`ibytes__is_wf`/`nbytes__is_wf` — both already `sorry`, and even the latter
needs a `wf_uN` precondition not available here either way. **Rocq's
`axioms.v` has nothing for this** — only the length facts. Decided this
crosses from "faithfully replicate Rocq's trusted base" into "invent what my
specific proof needs," which felt like the wrong line to cross unilaterally
— left `store_pack_val`/`store_num_val` `sorry`, kept the axioms and
`splice_length_ge` since they're real and reusable regardless. Flagging for
you: if you're comfortable with a third axiom here (`Forall wf_byte
(ibytes_ ...)` unconditionally, dropping the `wf_uN` precondition the
generated file's own sorry'd version has), these two cases would likely
close quickly from this point — the length side is already fully done.

**Technical notes from `table_set_val`'s iteration** (useful if this pattern
recurs for the remaining memory-write cases): destructuring a raw
`GetElem`/list-index expression like `tables[a]` directly via `obtain
⟨lim, rt⟩ := tables[a]` is unreliable once the surrounding proof context has
picked up a nontrivial (`omega`-derived, or otherwise non-atomic) index
proof — it can silently fail to narrow the type (leaving later references at
the wrong, undestructured type) or hit "Dependent elimination failed" when
later `cases`d. The reliable fix used throughout: `generalize h : tables[a]
= ti at hwf_old ⊢` first (turning it into a *genuine local variable* `ti`),
*then* `obtain`/`cases` on `ti`/`hwf_old` normally — this is exactly the
pattern that already worked cleanly everywhere else in this session
(`extend_tableinst_refl` etc.), the difference being those cases destructured
a bound *variable* from the start, never a raw indexing expression. Also:
when a constructor call has a metavariable (`_`) argument whose *value* a
later explicit proof-argument needs to reference (e.g. a length equality
about the exact new list), spell the argument out explicitly rather than
leaving it as `_` — `exact`'s left-to-right elaboration can process a later
`by` block before the trailing unification that would have pinned the
metavariable down, leaving that `by` block staring at an unresolved
metavariable instead of the real goal.
