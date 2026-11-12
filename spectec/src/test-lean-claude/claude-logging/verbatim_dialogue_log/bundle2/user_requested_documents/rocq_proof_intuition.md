# The Rocq proof's intuition: how it was built, and why

Written for: the user (to understand the Rocq author's process and
priorities) and a future Claude session working on this Lean port (to
guide proof strategy — this doubles as a working reference, not just an
explainer).

Sources: direct reading of `spectec/test-rocq/theories/*.v` throughout
this session (see the `digest_*.md` files in `claude-logging/for-claude/`
for structural detail on every declaration), plus a dedicated commit-
history investigation of the `rocq-backend-proof` branch on
`Wasm-DSL/spectec` (33 commits, single author, Mar–Sep 2026) done for this
document. Where I quote a commit message or code comment, it's copied
directly from the repository; everything else is my own synthesis.

---

## 1. What's actually being proven, and why the file layout looks the way it does

The end goal is **type safety for WebAssembly 2.0**, stated the standard
syntactic way (Wright & Felleisen-style): if a configuration is
well-typed and it steps, the result is still well-typed at the same type
(**preservation**), and if a configuration is well-typed and not already
a value/trap, it can step (**progress**). Preservation lives in
`type_preservation.v` (theorem `t_preservation`); progress lives in a
file called `type_progress.v` that **does not currently exist in this
session's `theories/` copy** (see §5 — it's real, it's just not in the
Rocq checkout this Lean port is working from; more on that below).

Everything before those two capstone files exists purely to make their
proofs possible. Reading the files in the order they're imported in
(`wasm.v` → `helper_lemmas.v`/`helper_tactics.v` → `subtyping.v` →
`typing_lemmas.v` → `type_preservation_pure.v` → `extension_lemmas.v` →
`axioms.v` → `type_preservation.v`) traces a path from "generic
list-algebra plumbing" up through "what does it mean for one Wasm type to
be a subtype of another" up through "what's the *shape* of every
instruction's type" up through "reduction preserves typing, ignoring the
store" up through "the store only ever grows/is-consistent" up to the
final composition. This is not an accident of alphabetical ordering or
generator output order — it's the actual **dependency graph of the
mathematics**, and (this is the useful bit) it's *also*, almost exactly,
**the order the author actually built it in**, per the git history. That
convergence is worth trusting: it means the "natural" mathematical
dependency order and the "practical, an experienced Rocq engineer's
actual workflow" order agree here, which is a good sign for planning the
Lean port the same way.

## 2. The development timeline, and what it reveals about difficulty

One author throughout (`DCupello1`/`DCupello`, same email
`dc1020@ic.ac.uk` — a handle change, not a different person), 33 commits,
2026-03-10 through 2026-09-22 (about 6.5 months of calendar time, though
very unevenly distributed — see the phase breakdown below). No PR, no
code review; this is unreviewed in-progress branch work as of the last
commit inspected.

**The single most useful discovery**: every hand-written file was staged
in a sibling directory, `spectec/test-rocq/folder-to-exclude/`, before
being "graduated" into the real, Dune-compiled `theories/` directory. `
folder-to-exclude/` has no `dune` file of its own, so Dune silently skips
it — it's a workbench for files that don't compile yet or whose story
isn't coherent yet. The author's loop, visible directly via
`git log --numstat -M` (which catches file moves as renames): write/repair
in the excluded folder → once it compiles and reads coherently, move it
into `theories/` in the same commit that calls it "done" or "in
progress" → occasionally move a *finished-looking* file back out for a
big rework. **This happened exactly once**, to `type_preservation.v` (see
below), and it's the single strongest piece of evidence for how this
author thinks about "done": being in `theories/` is a claim that the file
actually compiles and can be trusted, not a claim about narrative
completeness. That's a good discipline to borrow for the Lean side too —
don't let a broken experimental file block `lake build` for the finished
ones (this project already does something like this implicitly, since
every file we've written so far builds clean; keep it that way rather
than ever leaving something half-migrated in a file that's wired into
`lakefile.lean`'s globs).

Reconstructing *when each file first became build-real* (which is a much
more meaningful "when was X tackled" signal than raw creation timestamps,
since every file nominally "exists" as a stub from commit 1):

| Order | File(s) | Graduated | Commit message (verbatim) |
|---|---|---|---|
| 1 | `helper_tactics.v`, `helper_lemmas.v`, `subtyping.v` | 2026-03-10 (never staged — already complete on arrival) | "Port proofs from wasm2.0, works up to subtyping file." |
| 2 | `typing_lemmas.v` | 2026-04-13 | "typing inversion lemmas ported, preservation in progress." |
| 3 | `type_preservation_pure.v` | 2026-04-22 | "type preservation pure done" |
| 4 | `extension_lemmas.v` + `axioms.v` (together, same commit) | 2026-04-28 | "Wasm 2.0 store extension done" |
| 5 | `type_preservation.v` | 2026-05-04 | "Type preservation done for Wasm 2.0" |
| — | *(`type_preservation.v` demoted back to staging for a rework)* | 2026-07-29 | "Preservation in progress" |
| — | *(re-promoted)* | 2026-08-24 | "Type preservation basically done (without wfness lemmas done)" |
| 6, last | `type_progress.v` | 2026-09-21 | "Type progress basically done as well" |

This gives an almost textbook **difficulty ordering**: generic
infrastructure and subtyping first (these were already solved, ported
wholesale from a pre-existing, non-generated Wasm 2.0 Rocq proof the
author calls "wasm2.0" — more on that source below); then instruction
*typing* (what type does each instruction have, and its inversion
lemmas); then the *easy half* of preservation (pure/store-independent
reduction); then the store-extension machinery and its trusted axioms;
then the *full* preservation theorem (which needs everything before it);
and **progress dead last, by more than four months**, and — as of that
history — still the most incomplete file by a wide margin (30+ TODO
comments, 6 `admit`s, versus a handful of TODOs and at most 2 `admit`s
anywhere else). The intuition: **preservation only needs to reason
forward one step at a time along a single, already-known-well-typed
reduction**; **progress needs to reason about every well-typed term and
show a reduction always exists**, which is structurally a much larger
case analysis with more opportunities for the generated encoding to not
quite line up with what the proof needs (see §5's SIMD/lane discussion —
this is exactly where progress bites hardest).

### The other formative event: five weeks of silent generator churn, then a scramble

Between June 1 and June 29, there's a run of commits that are *nothing
but* "Update rocq output" (the generated `wasm.v`/`wasm1.v` being
regenerated as the SpecTec compiler itself kept evolving upstream). Then,
on **July 1**, two same-day commits: `dac300994` "Repaired typing
lemmas" and `5b03ae067` "Repaired preservation pure (except return
frame)". Diffing shows the actual cause: the generated relation
**`Admin_instrs_ok` was silently renamed to `Instrs_ok2`** somewhere in
that five-week window, breaking every downstream lemma statement that
mentioned it by name. `typing_lemmas.v` needed a near-full rewrite
(541 insertions / 437 deletions) to recover, including new helper lemmas
(`instr_ok_context_wf`, `ainstr_ok_context_store_wf`,
`instrs_ok_context_wf`) that didn't exist before the break. In the course
of repairing `type_preservation_pure.v`, the author **could not
immediately re-close one lemma** — `Step_pure__return_frame_preserves`'s
finished proof body got commented out and replaced with bare `Admitted.`,
and the commit message says so explicitly: "except return frame." **This
is the direct origin of the gap this Lean port has been faithfully
mirroring** (see `TypePreservationPure.lean`'s `Step_pure__return_frame_preserves`)
— it is not a fundamentally hard lemma, it's a lemma whose proof existed
once and got lost to generator churn, and the author never found the time
to redo it. Worth knowing: **the Lean version's `sorry` here might
actually be tractable** — it's not a structural gap like the SIMD ones,
just an abandoned repair.

**Lesson for the Lean port**: expect `wasm2.0.lean` to change under this
project (the user warned about this explicitly at task start — a
parallel effort is auditing its `*_is_wf` theorems), and expect that
churn to occasionally *rename* things, not just fill in `sorry`s. When a
file that built cleanly yesterday suddenly doesn't, check for a rename
first before assuming a logic error.

### The `type_preservation.v` staging round-trip

`type_preservation.v` was declared "done" on 2026-05-04, then on
**2026-07-29** was *physically demoted back into `folder-to-exclude/`*
for a 966-line rewrite (commit message: the deliberately unglamorous
"Preservation in progress", in contrast to May's "done"), sitting outside
the compiled tree for almost a month, before returning on **2026-08-24**
with a message that's careful to hedge exactly what's still missing:
"Type preservation basically done (**without wfness lemmas done**)."
Then two more rounds ("Removed some admits, only one left" on Aug 27;
vector-instruction work on Sep 22) brought it to **zero `admit`s** by the
last commit inspected. The file is, structurally, the capstone this
whole development points at, and its history shows that even after a
first "done," the author came back and found it wasn't trustworthy enough
to leave in the build — a useful reminder that "the signatures typecheck
and there's a `Qed`" isn't automatically "this is right"; getting the
*well-formedness side-conditions* threaded through correctly took a
second, deliberate pass.

## 3. Where "wasm2.0" — the seed of this whole proof — comes from

The very first commit's message is "Port proofs from wasm2.0, works up to
subtyping file," implying a pre-existing, presumably hand-written (not
SpecTec-generated) Wasm 2.0 Rocq type-safety proof that this whole
`rocq-backend-proof` branch is adapting to work against the
*generator's* output instead. I could not find that source anywhere
reachable from the public `Wasm-DSL/spectec` repository (checked every
plausibly-named branch) — my working conclusion is it's the author's own
prior/private work (plausibly thesis or research code) that predates and
sits outside this repo. **Practical implication**: `helper_lemmas.v` and
`subtyping.v` in particular read as *mature, reused* code — general
list/arithmetic facts and a clean subtyping algebra that isn't
Wasm-2.0-specific in any deep way — rather than code written fresh
against this specific generated encoding. That's consistent with what
this session already found when digesting `helper_lemmas.v`: many of its
lemmas are pure Coq-list-library-bridging artifacts (mathcomp `seq` vs.
stdlib `List`) with literally no Lean counterpart needed, because they
exist to paper over a mismatch between *two Coq list libraries*, not to
capture anything Wasm-specific.

There's also a directly preceding, closely related piece of the same
author's work worth knowing about: **PR #222** ("[IL Semantics]
Meta-theory in rocq", opened 2026-02-14, about 3.5 weeks before this
branch starts), doing *generic IL-level* (not Wasm-specific) meta-theory
in Rocq — syntax, substitution, reduction, typing for SpecTec's
intermediate language itself. That PR's own checklist, quoted directly:

> "TODO:
> - [x] Port Syntax, Env and Subst in Rocq
>   - [ ] Handle capture avoidance in Rocq
> - [x] Port Numerics using regularly used number types in rocq
>   - [ ] Figure out how to convert reals to rationals.
> - [x] Port Reduction in Rocq
>   - [x] Handle Iter expressions
>   - [ ] Matching
> - [x] Port typing in Rocq
>   - [ ] Make subtyping into coinduction?
> - [ ] (More to do)"

and its comment thread shows genuine back-and-forth with **Andreas
Rossberg** (the WebAssembly/SpecTec spec author, `COLLABORATOR`
association on the repo) — DCupello1 asking what a couple of
generator-emitted reduction relations with no rules were supposed to mean
(`Step_path`/`Step_iter`/`Step_exppull`), Rossberg replying "Oops, yeah,
seems like I forgot to add the actual rules... Maybe there would be a
warning when a relation has no rules. :)" and then fixing it upstream the
same day; and separately catching an actual bug in a structural-subtyping
reduction rule in the spec itself, with Rossberg acknowledging "it looks
like I screwed up gathering the e's" and fixing it. **The takeaway**: the
mechanization effort has, at least once, directly improved the upstream
spec's correctness, not just consumed it — this proof work is adversarial
in the good sense, a genuine correctness check on the generator and the
spec, not merely downstream of them. If the Lean session ever hits a
generated definition that looks flatly wrong (not just incomplete), it's
worth checking whether it's a known/reported spec bug before assuming the
Lean port needs to work around it silently.

One more piece of context: the umbrella PR for the Rocq backend *itself*
(the code generator, not the proofs) is **PR #207** ("Rocq backend",
opened 2025-11-19, still open as of the investigation, explicitly "Not
meant to be merged" — a tracking issue). Its checklist includes "Port
proofs of Wasm 1.0 and 2.0" as the very item this `rocq-backend-proof`
branch executes, and its earlier, struck-through notes hint at
generator-level friction encountered before any proof work started: "Only
works after some changes to the spec (only really problems with partial
functions). Also only works for deftorel without fallthrough semantics,
Getting issues with not having strictly positive inductive types when it
comes to recursive functions." Worth remembering that the Lean backend is
presumably going through, or has gone through, an analogous set of
generator-level growing pains — some of what looks like "the Lean output
is weird here" may be a known, already-being-worked-on generator
limitation rather than something this proof-porting effort needs to
route around cleverly.

## 4. Per-file intuition (why each file is shaped the way it is)

This section restates the structural digests already in
`claude-logging/for-claude/digest_*.md` but through the lens of *why*,
not just *what* — useful both to explain the proof to a human and to
guide how the Lean version's proofs should be attacked.

### `helper_lemmas.v` / `helper_tactics.v` — generic plumbing, low churn, basically finished from day one

These read as a grab-bag of list/option/arithmetic facts (`list_update`,
`In2`, `Forall2_*` interactions, `prepend_label`/`lookup_label_*`) that
have nothing conceptually to do with Wasm — they're the kind of thing
that shows up in *any* mechanized language-metatheory development that
manipulates typing contexts as lists. The git history bears this out:
barely touched after day one except small accretive additions whenever a
later file needed one more helper. **Intuition for the Lean port**: this
is exactly the kind of file where Lean's own standard library and
Mathlib already provide most of the underlying facts (`List.take`/`drop`/
`zip` lemmas, etc.), so expect many of these lemmas to become one-liners
via `simp`/`omega`, even though Rocq had to hand-roll them (partly
because Rocq splits its list reasoning across two parallel libraries,
`mathcomp`'s `seq` and stdlib's `List`, and this file bridges between
them — a problem Lean doesn't have at all, since it has one list type).

### `subtyping.v` — the algebra everything else leans on, also basically finished from day one

The core insight of this file is that Wasm's instruction-typing judgment
needs *stack-polymorphic* ("frame rule") subtyping: an instruction typed
`t1 -> t2` can be used anywhere `t1s ++ t1 -> t2s ++ t2` is expected (the
untouched prefix `t1s`/`t2s` just rides along). `subtyping.v` builds this
up in careful layers: pointwise value/result-type subtyping first (small,
almost trivial, `Valtype_sub` has exactly two cases — reflexivity and "BOT
is a subtype of everything"), then the harder `instrtype_sub` relation
(defined directly as an existential-split formula, not an inductive
relation — a deliberate representation choice that makes the "frame rule"
composable via ordinary list algebra rather than needing an extra
subtyping-composition induction), then an entire **composition algebra**
(`instrtype_sub_compose`, `_compose_le`, `_compose_ge`, and half a dozen
variants) whose whole purpose is to let later files chain two adjacent
instructions' types together without re-deriving the frame-rule
bookkeeping by hand every time. **This is the most reusable, best-tested
part of the whole development** (confirmed both by git history — barely
touched after creation — and by this session's own experience: three of
this file's hardest lemmas, `instrtype_sub_refl`/`_trans`/
`instr_subtyping_weaken2`, were already fully proved by a *previous* Lean
session working from a structurally-identical hand-rolled `instrtype_sub`
definition, and all three ported into this project's `Subtyping.lean`
essentially unchanged this session).

### `typing_lemmas.v` — "what is the type of this instruction," decomposed once, used everywhere

The single biggest design decision in this file is `ai_principal_typing`:
rather than write ~57 separate named inversion lemmas (one per
`admininstr` constructor), the author wrote **one big definition** that
pattern-matches on the instruction and states its principal (most
specific) type as an existential/equality `Prop`, then proved exactly two
"soundness" theorems (`instr_typing_inversion`, `ai_typing_inversion`)
connecting that definition to the real inductive typing judgments. Every
later file that needs to know "if this instruction typechecks, what did
its type have to look like" goes through `ai_principal_typing` via
automation (`unfold_principal_typing`/`resolve_all_pt`), not through
separate per-instruction lemmas. The intuition: this is a **classic
functional/relational duality trick** — a big pattern match is much
easier to state completely and correctly (the type-checker forces
exhaustiveness) than 57 separate lemma statements are to keep mutually
consistent by hand, at the cost of needing generic automation to actually
*use* it. This is exactly why this project's `TypingLemmas.lean` mirrors
the same one-big-definition shape rather than decomposing it (see the
file's own TODO about still needing to transcribe the ~57-case body).

The file also contains a second architectural theme worth flagging: a
large family of "sequence/composition" lemmas (`instrs_seq_typing_inversion`,
`ais_composition_typing`, `construct_ais_compose`, etc.) that let you
split a typed instruction *sequence* apart (or glue two typed sequences
back together) without losing well-typedness. **This is where the biggest
land-mine in the whole port was found and fixed**: an earlier Lean
attempt mis-stated the sequence-splitting lemma using *singular*
`Instr_ok` for the head instruction rather than the sequence-level
`Instrs_ok`, and that statement is provably *false* (a compiling
counterexample exists — `CONST`'s rule fixes its input type to `[]`
unconditionally, so it can't absorb an arbitrary shared prefix the way a
`frame`-widened sequence can). Rocq's own `ais_seq_typing_inversion`
(`typing_lemmas.v:1080`) uses the correct sequence-level form; this
project's `TypingLemmas.lean` states it that way from the start. This is
a good example of *why* fidelity to the Rocq statement (not just "porting
something that feels similar") matters — the wrong-looking-almost-right
version is actually unsound to build on.

### `type_preservation_pure.v` — preservation for the store-independent half of reduction, one lemma per rule

Unlike `typing_lemmas.v`'s "one big definition," this file is genuinely
**one lemma per reduction rule** (28 of them, `Step_pure__*_preserves`),
each roughly "if this admin-instruction-sequence typechecks and it
pure-reduces to that one, that one typechecks too." The intuition for why
this file exists *separately* from full preservation: **`Step_pure` never
touches the store**, so its preservation proof never needs
`Store_extension`/`Store_ok` reasoning at all — it's purely a fact about
the typing judgment being closed under a fixed, finite set of local
rewriting rules (constant folding, branching bookkeeping, `select`/`if`/
`local.tee` desugaring). Splitting this out lets the author finish (and,
per the commit history, genuinely *did* finish — "type preservation pure
done" on day one of this file, modulo the later `return_frame` regression
already discussed) a large, self-contained chunk of the overall
preservation proof before ever having to think about store extension at
all. **This is the cleanest, most mechanical file to work on next** in
this Lean port — every proof obligation is "invert the typing derivation
for the LHS, reconstruct one for the RHS," a bounded, repetitive pattern.

### `extension_lemmas.v` — "the store only ever grows, consistently," proven component by component

This file's core relation (`Extend_store` in the Lean encoding; the
now-stale `Store_extension` name in the Rocq source — see the naming note
in `ExtensionLemmas.lean`) captures "store `s'` is a valid successor of
store `s`": every existing index still resolves to something that's a
valid extension of what it used to be, and new indices beyond the old
length are unconstrained. The file's shape mirrors that structure
directly: reflexivity of extension for each of the 6 store-component
kinds (funcs/globals/tables/mems/elems/datas) individually, then lifted
to the whole store; then a `Store_extension`-preserves-`X_ok` lemma for
every typing judgment that could be invalidated by a store growing
(`Ref_ok`, `Val_ok`, `Externaddr_ok`, `Moduleinst_ok`, ..., culminating in
`store_extension_ais`, admin-instruction typing survives store extension);
then, in a mirror-image final section, one "construct" lemma **per
store-mutating Wasm instruction** (`global.set`, `table.set`/`grow`,
`memory.store`/`grow`, `elem.drop`, `data.drop`) proving that
instruction's specific mutation actually produces a valid extension.
**This last section is the direct ingredient `type_preservation.v`'s
`store_extension_reduce` needs, one case per store-mutating instruction**
— which is exactly the shape that theorem's proof takes (see
`digest_type_preservation.md`'s account of it). The commit history shows
this file's substance was mostly written in one enormous sitting four
months after the file was created (`+1816/-1073` on 2026-07-22, the
commit literally titled "extension lemmas done - except meminst grow") —
i.e. this is a file that sat as scaffolding for a long time before being
filled in properly, and even then, one genuinely hard arithmetic fact
(bounding memory growth against the 2^16-page hard ceiling) was never
closed, and is still `admit`ed at HEAD. That specific gap (`extension_lemmas.v`
around line 3026, `TODO - Find some way of showing lim_old + v_n <= 2 ^
16`) is **not a structural blocker** — it's an unfinished-but-plausible
arithmetic lemma, and worth prioritizing early in the Lean port to get a
"fully closed" file (mirrors how the original author treated "zero
admits" as a milestone for `type_preservation.v`).

### `axioms.v` — the two (Lean: currently ported) facts this whole edifice is willing to just assume

Small, and deliberately so — this is the file that names the escape
hatches. Every axiom in it is preceded by a comment explaining, in terms
of the *specification's* meaning (not the generated Coq's), why the fact
is true but not mechanically derivable from what the generator emits.
Quoting the style directly (these exact three exist in the version of
`axioms.v` this Lean port has already read and ported the first two of):

> `(* nbytes_/ibytes_ and their inverses inv_nbytes_/inv_ibytes_ are
> uninterpreted Axioms in wasm.v. In the specification they are mutually
> inverse bijections between values and byte sequences of the right
> width. *)`

The commit history shows this file grew substantially in its very last
commit (2026-09-22, `+32/-0`), adding **five more axioms specifically to
support SIMD/vector reasoning** (`vbytes_len'`, `ibytes_len''`,
`truncz_quot`, `lanes_len`, plus inverse-bijection axioms for
`nbytes_`/`ibytes_`/`vbytes_`) — i.e. as the author pushed preservation
and progress further into vector-instruction territory, more primitives
needed hand-supplied characterizing facts. **This is a live signal for
the Lean port**: if/when this project's own proofs start needing to
reason about `wasm2.0.lean`'s vector/SIMD-related opaque definitions
(`vbytes_`, `lanes_`, etc.), expect to need analogous hand-written
`axiom`s here too, following the same discipline — characterize the
*spec-level meaning*, don't try to derive it from the generated encoding
alone.

### `type_preservation.v` — the composition, not a new proof technique

As covered in §2 (the staging round-trip), and per this project's own
`digest_type_preservation.md`: this file's own genuinely novel content is
smaller than it might look — the three big lemmas
(`store_extension_reduce`, `t_read_preservation`, `t_preservation_type`)
are each "induct on the reduction relation, dispatch each case to
something already proved elsewhere" (mostly `extension_lemmas.v`'s
per-instruction "construct" lemmas, or `type_preservation_pure.v`'s
`t_pure_preservation`), and the capstone `t_preservation` itself is *pure
composition* of five already-proved facts, no case analysis of its own.
The intuition: **this file is where everything else gets assembled, not
where the hard mathematics lives** — which is exactly why, in the current
state of the Rocq proof, its only remaining gaps (as of the version this
project has been reading) are the SIMD-only cases inherited from its
dependencies, not anything intrinsic to the assembly itself.

### `type_progress.v` — not present in this Lean port's Rocq checkout, but real and instructive

This file exists on the live `rocq-backend-proof` branch (graduated into
the real build 2026-09-21, per the commit history) but **is not among the
9 files this Lean-porting session found in its local
`spectec/test-rocq/theories/` checkout** — the checkout this project has
been working from appears to predate that graduation, or is otherwise out
of sync with the live branch. This is worth flagging to the user
directly (see the end-of-session report) since it means **Progress is a
real, substantially-developed part of this proof that the Lean port
hasn't attempted at all yet**, not something out of scope by design.

Its content and gaps are, per the commit-history investigation, the most
instructive part of the whole codebase for understanding *why* a
generated-Coq encoding can genuinely resist a proof, independent of
effort. All 6 of its `admit`s trace to one root cause, diagnosed in the
author's own comments: the generated `lane_` type has three separate
constructors (`mk_lane__0`/`mk_lane__1`/`mk_lane__2`, one per source-spec
injection `num_`/`pack_`/`iN`), and the spec-level subtyping between those
source types is **not preserved** by the generated encoding — so, given a
well-formed `lane_` value, its "true" constructor can't always be
recovered from the one available well-formedness fact
(`lanes__is_wf`). Quoting the author's own diagnosis directly (this is
about as clear a bug report against a code generator as a human proof can
produce):

> "the spectec subtyping between `num_`/`pack_`/`iN` and `lane_` is not
> preserved by the Coq encoding. So `proj_lane__2 l <> None` is not
> derivable, and no axiom can repair it: `vextract_lane_num` wants the
> `mk_lane__0` form of the very same list that `vtestop_true` wants in
> `mk_lane__2` form."

**This is a generator-level modeling gap, not a proof-effort gap** — and
it will very likely recur *identically* in whatever the SpecTec Lean
backend does for the analogous lane/SIMD types, unless the Lean backend
happens to generate a single canonical lane representation (worth
checking, if/when this port reaches SIMD territory). This is exactly the
kind of thing the SIMD-related `sorry`s already being carried through
this Lean port (in `TypePreservationPure.lean`, `TypePreservation.lean`)
are silently consistent with — they may turn out to be unclosable for the
*same underlying reason*, not just "nobody got to it yet."

## 5. What this means for how the Lean port should proceed (synthesis)

1. **The dependency order this project already chose for its 6 Lean
   files matches the Rocq author's own actual build order almost
   exactly** (helper lemmas/subtyping → typing lemmas → pure preservation
   → extension lemmas → axioms → full preservation) — this is strong
   independent confirmation that the ordering is right, not an
   accident. Keep working in that order for proofs, not just for the
   initial signature-sketching pass.
2. **Pure preservation (`type_preservation_pure.v`) is genuinely the
   easiest substantial chunk of real mathematics in the whole
   development** (one bounded, repetitive pattern per lemma, no store
   reasoning) — after the "reuse already-proved lemmas" pass documented
   in this bundle's other files, this is where fresh proof effort should
   go next.
3. **`subtyping.v`/`extension_lemmas.v`'s reflexivity/composition-algebra
   families are the most mechanically re-derivable content in the whole
   proof** (confirmed twice now: once by git history showing they were
   barely touched after being ported from prior art, once by this
   session directly reusing a previous Lean attempt's proofs of exactly
   these lemmas with almost no adaptation).
4. **Expect the target (`wasm2.0.lean`) to change under this project**,
   sometimes via outright renames, not just `sorry` fills — the Rocq
   history shows this is a real, recurring failure mode for a
   proof-on-top-of-a-generator project, not a hypothetical risk.
5. **`Step_pure__return_frame_preserves`'s `sorry` is plausibly tractable**
   — its Rocq counterpart isn't `admit`ed because it's hard, it's
   `Admitted` because a working proof got lost to a rename and was never
   redone. Worth a real attempt rather than assuming it's stuck.
6. **The remaining `extension_lemmas.v` gap (memory-growth page-count
   bound) is ordinary unfinished arithmetic**, not a structural
   obstruction — good, achievable target for "get this file to zero
   `sorry`s."
7. **SIMD-related gaps (both the ones already being carried in this
   port's `type_preservation_pure.v`/`type_preservation.v`, and
   everything in `type_progress.v` once it's ported) may be
   fundamentally blocked by a generator-level lane-type encoding issue**,
   not a proof-difficulty issue — don't sink disproportionate effort into
   these without first checking whether the analogous problem exists (or
   has already been solved) in `wasm2.0.lean`'s own lane-type encoding.
8. **`type_progress.v` needs to be fetched/re-synced and ported** — it's
   real, substantial, and currently entirely missing from this project's
   scope. This is probably the single most important actionable finding
   in this whole document; see `proof_prioritization.md` for how it's
   weighted into the ordering.
