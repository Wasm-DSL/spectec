# Minimal reproduction of the `undep.ml` optional-marker bug

Generated and verified against the actual `./spectec` binary (built 2026-09-17),
using the same pass sequence as `test-lean-backend/diag.sh`. Nothing outside
this directory was modified — see the end of this file.

## `bug_example.spectec` — confirmed bug, minimal reproduction

```
syntax marker = MARK
syntax thing = THING marker? nat
relation Thing_ok: thing : OK
rule Thing_ok:
  THING MARK? n : OK
  -- if $(n > 0)
```

Expected (per spec text): `Thing_ok` should hold for `THING n` (marker
absent) and `THING MARK n` (marker present) alike, for any `n > 0`.

Verified via `il_dump/bug_04-typefamily-removal.il` vs.
`il_dump/bug_05-remove-indexed-types.il` (before/after the `Undep` pass):

```
;; before (pass 04):
(TupE (IterE (CaseE (Atom MARK) (TupE)) Opt) (VarE "n"))

;; after (pass 05):
(TupE (OptE (CaseE (Atom MARK) (TupE))) (VarE "n"))
```

Final Lean output (`bug_example.lean`):

```lean
inductive Thing_ok : thing → Prop where
  | mk_Thing_ok (n : Nat) :
    n > 0 →
    Thing_ok (thing.THING (some marker.MARK) n)
```

`thing.THING none n` is permanently unprovable via `Thing_ok`, for any `n`.
This is the same bug as `Reftype_ok`/`Fieldtype_ok`/`Globaltype_ok`/etc. in
the real wasm-2.0/3.0 specs, isolated to its smallest form. Root cause:
`src/middlend/undep.ml`'s `t_exp`, the `IterE (e1, (Opt, [])) -> OptE (Some e1)`
case, fires because `MARK` is a literal token (no bound variable), which is
indistinguishable to that check from a genuinely-resolved case.

## `legitimate_example.spectec` — attempted "safe" counterexample, did NOT reproduce the same code path

```
syntax tag = SMALL | BIG
syntax marker = X
def $extra(tag) : marker?
def $extra(SMALL) = eps
def $extra(BIG) = X
```

Hypothesis going in: a `def` clause whose own pattern already fully
determines the optional's presence (no real alternative being discarded)
would hit the *same* `IterE(<literal>, (Opt, []))` shape as `bug_example`,
but safely, since forcing it doesn't lose a real derivation.

**This hypothesis was wrong.** Checked `il_dump2/leg_04-typefamily-removal.il`
vs. `il_dump2/leg_05-remove-indexed-types.il` — identical before and after,
and neither contains an `IterE` around the optional at all:

```
(DefD (ExpA (CaseE (Atom SMALL) (TupE))) (OptE))
(DefD (ExpA (CaseE (Atom BIG) (TupE))) (OptE (CaseE (Atom X) (TupE))))
```

A bare term (`X`) or `eps` placed directly into an `Option`-typed return slot
elaborates straight to `OptE`/`(OptE)` at pass 00, via ordinary subtyping
coercion — it never goes through `IterE` at all, so `Undep`'s rewrite never
gets a chance to touch it (correctly or not). The resulting Lean is exactly
right:

```lean
def extra (v_tag : tag) : Option marker :=
  match v_tag with
  | tag.SMALL => none
  | tag.BIG => some marker.X
```

**Conclusion from this experiment**: `IterE(<literal-payload>, (Opt/List, []))`
appears to arise *only* from an explicit `X?`/`X*` written directly in spec
source (as in `bug_example.spectec`, and as in the real `NULL?`/`MUT?`/
`FINAL?` cases) — never from ordinary elaboration of an already-determined
value. Since spectec's own convention is that a spec author only writes `?`
at all when they mean "matches either way" (if they wanted one fixed outcome
they'd write the bare literal or `eps`, as `legitimate_example.spectec`
does, successfully), this suggests the `t_exp` rewrite may have **no
legitimate firing case** within ordinary rule/def bodies — every real
trigger looks like it's a genuine spec-author choice being incorrectly
collapsed, not a flattening residual being correctly resolved. This is a
stronger, empirically-grounded version of the "likely unintentional, not an
accepted tradeoff" conclusion reached by static analysis alone.

(Caveat: this rules out the specific construction tried here — an ordinary
`def` clause's directly-returned value — not every conceivable code path.
`typefamilyremoval.ml`'s own internal term construction, run before `Undep`,
was not independently exercised by this experiment.)
