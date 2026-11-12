# Rocq/spec changes from the `rocq-backend-proof-final` merge (bundle13)

Written for: a future Claude session and the user. Covers the bundle13
request: summarize what changed in the `8ac6699ac` merge of
`rocq-backend-proof-final` into `lean-backend`, and what (if anything) it
requires of `spectec/src/test-lean-claude/`. Supersedes bundle9's
`rocq_changes_summary.md` as the doc to read for "what changed since we last
looked," but does not restate its content (that covered a different, earlier
delta) — read both if you need the full history.

## Headline: one real (now-fixed) build break, one now-provable lemma, everything else out of scope

The merge (`da555377a` → `95c256c2c`, 15 files, +8249/-3961, dominated by a
9623-line diff in the auto-generated `wasm.v`) is **almost entirely a SIMD/
vector-instruction restructuring** (`vloadop`, `vextunop_`/`vextbinop_`,
`vcvtop` all reshaped to be indexed by shape pairs, `VEXTUNOP`/`VEXTBINOP`/
`VCVTOP` argument order swapped, three `Step_pure/vcvtop-*` rules collapsed
into one). **This project's Lean ports deliberately and explicitly exclude
SIMD from scope** (stated in `TypePreservationPure.lean`'s and
`TypePreservation.lean`'s own header comments), and a grep confirms zero
occurrences of any SIMD instruction/type name (`VEXTUNOP`, `VCVTOP`, `VLOAD`,
`vextunop_`, `vloadop`, etc.) anywhere in the 6 Lean files — so essentially
all of the merge's line-count is irrelevant to us by construction, not by
oversight.

Of the small remainder (non-SIMD, in scope):

1. **A real build break, found and fixed**: `nbytes_`/`ibytes_`/`fbytes_`/
   `vbytes_` (the byte-encoding opaques in the regenerated `wasm2.0.lean`)
   became **total** (`List byte`, not `Option (List byte)`). Root cause
   traced to a commit outside the 15-file diff shown above (it's baked into
   the already-merged `wasm.v`/`undep.ml`): `853b8863c` "Made wfopt be an
   optin hint for functions" (2026-09-28, 162 new lines in `C-hints.spectec`
   + 38-line `undep.ml` change) — functions now only get an `Option`-wrapped
   return type when explicitly hinted `wfopt`, rather than by some prior
   default, and `nbytes_`/`ibytes_`/`fbytes_`/`vbytes_` don't carry that
   hint. Three `HelperLemmas.lean` axioms (`nbytes_len`, `nbytes_len'`,
   `nbytes_inv`) were written against the old partial signature and had a
   `nbytes_ ... ≠ none` guard plus `Option.get!` wrapper that no longer
   type-checked — `lake build` failed with 5 real errors before the fix.
   Fixed by dropping the guard and the `Option.get!` on `nbytes_`
   specifically (`size` itself is still `Option Nat`, unaffected — it
   presumably does carry the `wfopt` hint). **`lake build` is 100% clean
   after this fix** (0 errors, only the pre-existing `sorry` warnings) — this is
   strong evidence that nothing else broke, since every one of our 6 files
   imports `wasm2.0.lean` transitively and would fail to elaborate against
   any other incompatible regenerated signature.
2. **`construct_meminsts_grow` (`ExtensionLemmas.lean`) is no longer
   permanently blocked.** See §2 below — this was the one item our own
   prior-bundle docs had flagged as "the sole remaining Preservation-side
   gap," and the merge closes it upstream.
3. Everything else checked (axioms.v's 9 new axioms, `Datainst_ok`/
   `Eleminst_ok`'s new `< 2^32` length bound, `typing_lemmas.v`'s tactic-only
   change) is either out of scope or requires no textual signature change —
   see §3.

## 1. Where the changes actually are (file-by-file)

Diffed `da555377a..95c256c2c` directly (the pre-merge tip vs. the tip of
`rocq-backend-proof-final` that got merged in):

```
 specification/wasm-2.0/1-syntax.spectec            |   75 +-   (SIMD type restructuring)
 specification/wasm-2.0/3-numerics.spectec          |  104 +-   (SIMD op restructuring)
 specification/wasm-2.0/5-runtime-aux.spectec       |    1 +    ($growmemory bound — see §2)
 specification/wasm-2.0/8-reduction.spectec         |   29 +-   (SIMD reduction rules)
 specification/wasm-2.0/B-soundness.spectec         |    2 +    (Datainst_ok/Eleminst_ok bound — see §3)
 specification/wasm-2.0/C-hints.spectec             |  163 +    (codegen display hints only)
 spectec/src/backend-rocq/print.ml                  |   12 +-   (Rocq backend only)
 spectec/src/middlend/undep.ml                      |  197 +-   (shared codegen pass)
 spectec/test-rocq/theories/axioms.v                |   45 +-   (9 new axioms — see §3)
 spectec/test-rocq/theories/extension_lemmas.v      |   59 +-   (construct_meminsts_grow — see §2)
 spectec/test-rocq/theories/type_preservation.v     |   25 +-   (growmemory case only — see §2)
 spectec/test-rocq/theories/type_preservation_pure.v|   16 +-   (SIMD-only + one dispatch renumber)
 spectec/test-rocq/theories/type_progress.v         | 1853 +-   (out of scope — no TypeProgress.lean exists)
 spectec/test-rocq/theories/typing_lemmas.v         |    6 +-   (tactic-only, no signature change)
 spectec/test-rocq/theories/wasm.v                  | 9623 +-   (mostly SIMD; regenerates wasm2.0.lean)
```

Read in full: `1-syntax.spectec`, `3-numerics.spectec`, `5-runtime-aux.spectec`,
`8-reduction.spectec`, `B-soundness.spectec` (spec sources — small enough to
read directly), and all 5 non-`type_progress.v`/`wasm.v` theory files. Did
**not** line-by-line read `type_progress.v` (1853 lines, confirmed
irrelevant — no Lean port exists) or `wasm.v` (9623 lines, auto-generated;
validated indirectly via `lake build` + targeted spot-checks instead, see
§4). Did not read `C-hints.spectec` (display/codegen hints only, no semantic
content) or the two `.ml` backend files (OCaml codegen internals, not spec
content — their effects are what produced the regenerated `wasm2.0.lean`,
which was checked directly).

## 2. `construct_meminsts_grow`: now provable, still `sorry`

**Old status** (per our own bundle3-era doc comment): "Still `Admitted` in
the current upstream Rocq source — the sole remaining Preservation-side gap
... the `lim_old + v_n ≤ v_j` memory-growth bound." **New status**: Rocq's
`construct_meminsts_grow` is now fully `Qed`'d (`extension_lemmas.v`'s
`admit. (* TODO - Find some way of showing lim_old + v_n <= 2^16 *)` is
gone). The fix, traced through the diff:

- `5-runtime-aux.spectec`'s `$growmemory` gained a new side condition:
  `-- if i' <= $(2^16)` (the hard 65536-page/4GiB memory cap). This bound
  previously existed nowhere in the operational semantics of `memory.grow`
  itself — it was only implicitly needed downstream.
- Why it's needed: `Meminst_ok` requires `Memtype_ok`, which requires
  `Limits_ok v_limits (2^16)` (confirmed directly in the regenerated
  `wasm2.0.lean`, `Memtype_ok`/`Limits_ok`, lines ~11616-11647) — i.e. every
  valid memory instance's page count is capped at 2^16 by construction. Post
  `memory.grow`, proving the *new* memory instance is still `Meminst_ok`
  requires exactly this cap on `lim_old + v_n`. Before this merge nothing
  supplied it; the fix supplies it directly at the reduction-rule level.
- `extension_lemmas.v`'s `construct_meminsts_grow` gained a matching new
  premise (`(lim_old + v_n ≤ 2^16)%Q` in Rocq's `Q`-valued formulation) and
  its proof now derives the needed `N.leb`-form bound from it via
  `Qfloor`/`Zdiv` conversions instead of hitting the `admit`.
- `type_preservation.v`'s `store_extension_reduce` growmemory case was
  updated to thread this same bound through from `$growmemory`'s own
  premise to the `construct_meminsts_grow` call site. `store_extension_reduce`
  **remains `Admitted` overall** (unrelated, purely SIMD cases elsewhere in
  the same lemma) — so this doesn't unblock our `TypePreservation.lean`'s
  `store_extension_reduce sorry`, which correctly stays as a deliberate gap
  mirroring Rocq's own.

**Action taken**: added a matching `lim_old + v_n ≤ 2 ^ 16` hypothesis to
`ExtensionLemmas.lean`'s `construct_meminsts_grow` (Nat-valued, consistent
with this lemma's pre-existing, unaffected-by-this-resync choice to state
`lim_old` as `Nat` rather than Rocq's `Q` — see the in-file comment).
Rebuilt clean. **Proof body deliberately left `sorry`, not attempted this
bundle**: Rocq's own proof route is pure `Q`/`Z` rational-conversion
bookkeeping with no Lean counterpart to mirror (this codebase's `lim_old` is
already plain `Nat`, so none of that machinery is even meaningful here), and
more importantly the *outer* induction Rocq uses (`induction Hold` on the
`Forall2` witness, walking the list structurally) doesn't have a direct
analogue: this codebase's `Forall₂` is a zip-based `def`
(`∀ p ∈ l1.zip l2, P p.1 p.2`), not Rocq's inductive relation, so it doesn't
support the same case-by-case structural induction without first
establishing `s.MEMS.length = ts.length` separately (the identical class of
gap already solved once for `Vals_ok`/`Vals_ok_non_bot` in bundle9 — see
`HelperLemmas.lean`'s `to_mathlib_forall₂`/`from_mathlib_forall₂` bridge).
**This is now flagged as a genuine target in the updated prioritization doc
(`proof_prioritization_v4.md`), not a permanent gap** — but it needs that
length-matching prerequisite worked out first, so it's appropriately ranked
alongside the file's other index/list-update lemmas rather than treated as
low-hanging fruit.

**Separately noticed while reading this lemma (pre-existing, NOT caused by
this merge)**: the Lean signature hard-codes the declared memory maximum as
always present (`some (uN.mk_uN v_j)` in three places), where Rocq's actual
parameter is `v_j_opt : option u32` — a real memory can have *no* declared
maximum. This predates the current resync (present already in the version
this session inherited) and isn't touched here, but is worth fixing whenever
this lemma gets its real proof, since the `None` case is a legitimate input
this signature currently can't even state. Flagged in the prioritization doc.

## 3. Everything else checked, and why no action was needed

- **`axioms.v`'s 9 new axioms** (`ibits_inv`, `feq_bit`/`fne_bit`/`flt_bit`/
  `fgt_bit`/`fle_bit`/`fge_bit`, `ishl_wf`/`ishr_wf`,
  `trunc_sat_total`/`demote_nonempty`/`promote_nonempty`): grepped their use
  sites across all of `spectec/test-rocq/theories/*.v` — **every single one
  is consumed exclusively inside `type_progress.v`** (lines 1687-4306, e.g.
  `ishl_wf`/`ishr_wf` for I64 shift totality, `feq_bit`..`fge_bit` for float
  `RELOP` result well-formedness, `trunc_sat_total` etc. for `CVTOP`
  totality). Since no `TypeProgress.lean` exists, none of these need adding
  to `HelperLemmas.lean` right now.
- **`Datainst_ok`/`Eleminst_ok` gained a `< 2^32` length bound**
  (`B-soundness.spectec`: `-- if |b*| < $(2^32)` / `-- if |ref*| < $(2^32)`).
  Confirmed present correctly in the regenerated `wasm2.0.lean`
  (`Datainst_ok`/`Eleminst_ok`, lines ~14204-14225: `List.length b_lst <
  2^32` / `List.length ref_lst < 2^32`). Since these are auto-generated
  `inductive` predicates and `ExtensionLemmas.lean`'s `construct_datainsts`/
  `construct_eleminsts`/`Extend_store_eleminst`/etc. only ever reference
  `Datainst_ok`/`Eleminst_ok` as opaque predicate applications (never
  unfold their definition in a stated signature), **no textual Lean
  signature needs to change** — the new bound is automatically inherited.
  It will matter once someone actually writes these lemmas' (currently
  `sorry`) proof bodies, not before.
- **`typing_lemmas.v`'s only change** (`wf_admininstr_instr`'s two proof
  branches collapsed from two explicit `econstructor; eauto` bullets to one
  `all: try (econstructor; eauto)`) is **purely a Rocq tactic-script
  simplification** — the lemma's statement is byte-for-byte unchanged. Our
  `TypingLemmas.lean` already ports the underlying fact as
  `instr_of_admininstr_instr` with an entirely different (and already
  complete) proof (`cases i <;> rfl`), so this is a non-event for us.
- **`type_preservation_pure.v`'s other change**: the numeric-conversion
  helper lemmas' argument types were renamed (`wasm.vextunop_` →
  `wasm.vextunop__`, `wasm.vcvtop` → `wasm.vcvtop__`, etc. — purely
  following the SIMD type restructuring from §1) and
  `t_pure_preservation`'s dispatch case-numbers shifted (`24: ... local_tee`
  → `22: ...`, three `vcvtop_preserves` bullets collapsed to one) because
  three `vcvtop-full`/`-half`/`-zero` step rules merged into one. Both are
  SIMD-internal; `t_pure_preservation` is deliberately `sorry`'d in our port
  (mirrors Rocq's own SIMD-caused `Admitted`) regardless of exactly how many
  SIMD cases precede which non-SIMD one in the case list.
- **`wasm2.0.lean` regeneration: verified byte-for-byte, not just
  spot-checked** (the user manually regenerated it and asked for
  double-checking). Found the Lean backend's actual CLI invocation
  (`_build/default/src/exe-spectec/main.exe <all 12 wasm-2.0 .spectec files
  in order> --lean -o <file>` — the `--lean` target auto-enables the same
  pass pipeline as `--rocq`: `HandleExplicitIgnores`, `Sideconditions`,
  `Totalize`, `Else`, `TypeFamilyRemoval`, `Undep`, `Uncaseremoval`, `Sub`,
  `SubExpansion`, `ImproveIds`, `AliasDemut`, `DefToRel`, `Ite`, `ElseSimp`,
  `PatSimp`, `LetIntroMech`) and **ran it independently** against the
  already-merged spec sources, output to a scratch file (never touching the
  real one). `diff` against the committed `spectec/src/test-lean-claude/
  wasm2.0.lean`: **zero lines of difference, byte-for-byte identical**
  (both 14760 lines). This is a much stronger confirmation than spot-
  checking individual definitions — the user's manual regeneration exactly
  reproduces what the toolchain itself produces from the current merged
  spec, full stop. (Before finding the exact invocation, also spot-checked
  a handful of definitions directly — `vsize`, the `ishape`/`fshape`/
  `pshape` restructuring, `vloadop_`/`vextunop__`/`vextbinop__`/`vcvtop__`,
  and the `Datainst_ok`/`Eleminst_ok` bound — all present and correct, now
  superseded by the exhaustive diff.)

## 4. Signature audit

Per the bundle13 request ("a dedicated signature audit against live Rocq
would probably be worthwhile"), a full systematic pass comparing every
Lean `theorem`/`axiom` signature in the 6 files against its named Rocq
counterpart (hypothesis-by-hypothesis, SIMD/`type_progress.v` excluded) was
dispatched as a background research task. See
`signature_audit_v1.md` in this same `user_requested_documents/` folder for
the full report (produced by that task, not hand-written in this document —
check its own header for exactly what was and wasn't covered). Findings
from it, if any beyond what's already fixed above, are triaged in
`proof_prioritization_v4.md` and/or fixed directly, per whatever landed by
the time this bundle closed — check this document's own bundle for whether
that happened synchronously or needs a follow-up bundle.
