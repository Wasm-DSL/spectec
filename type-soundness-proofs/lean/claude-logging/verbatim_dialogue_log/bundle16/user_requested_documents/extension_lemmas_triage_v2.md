# `ExtensionLemmas.lean` triage — update v2 (bundle16)

Written for: a future Claude session (primary audience) and the user.
Supersedes `bundle15/user_requested_documents/extension_lemmas_triage_v1.md`
(kept untouched as the historical record). v1 was a *forward-looking* triage of
76 `sorry`s into Trivial/Easy/Moderate/Hard tiers. This is its **closeout**:
the file now has **2** `sorry`s left, and neither is a difficulty problem.

## Headline

| | v1 (bundle15 start) | bundle15 end | **v2 (bundle16 end)** |
|---|---:|---:|---:|
| `ExtensionLemmas.lean` `sorry`s | 76 | 50 | **2** |
| declarations in file | 92 | 92 | **129** (+37 new helper lemmas) |

Everything v1 classified as Trivial, Easy, Moderate **or Hard** is now proved,
including all three lemmas bundle15 flagged and reverted, both `_grow`-suffixed
`construct_*` lemmas, and `Extend_store_ais` (v1's single hardest entry).

## The two remaining `sorry`s — both signature problems, not proof problems

### 1. `Val_ok_store` (line ~136)

```lean
theorem Val_ok_store (f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 : _) (v : val) (t : valtype) :
    Val_ok (store.MKstore f1 g1 t1 m1 e1 d1) v t ↔ Val_ok (store.MKstore f1 g2 t2 m2 e2 d2) v t
```

**Not provable as stated, and it is not in the current upstream at all.**
`Val_ok`'s every constructor carries a `wf_store s` premise, and `wf_store`
constrains *all six* store fields — not just `FUNCS`. So the right-to-left
direction needs `wf_store (MKstore f1 g1 t1 m1 e1 d1)`, which the statement
does not supply and which is genuinely independent of
`wf_store (MKstore f1 g2 t2 m2 e2 d2)`. The underlying *intent* (`Val_ok`
only reads `FUNCS`) is true; the `wf_store` side conditions are what break the
literal `↔`. A future session that actually needs this fact should add
`wf_store` premises for both stores (then it is a short proof: `cases` the
`Val_ok`, re-apply the constructor, and route the `Ref_ok`/`Externaddr_ok`
`FUNCS` lookups through unchanged). **Do not "fix" it speculatively** — nothing
in the project depends on it, and upstream dropped it.

### 2. `funcinst_same` (line ~1054)

```lean
theorem funcinst_same (f1 f2 : List funcinst) : Forall₂ Extend_funcinst f1 f2 → f1 = f2
```

**Not provable as stated.** This codebase's generated `Forall₂` is the
*zip-based* `def` `∀ p ∈ xs.zip ys, P p.1 p.2`, which does **not** force
`f1.length = f2.length` (Rocq's inductive `Forall2` does). So
`Forall₂ Extend_funcinst [a] []` holds vacuously while `[a] ≠ []`. Also not
found under this name in the current upstream.

What *is* now available and is what callers actually wanted:
`extend_funcinst_eq : Extend_funcinst f1 f2 → f1 = f2` (the single-instance
fact, proved — `Extend_funcinst` is reflexivity-only), plus
`HelperLemmas.Forall2_nth_of_length` to go index-by-index when a length
hypothesis is in hand. If a future session needs the list version, state it as
`Forall₂ Extend_funcinst f1 f2 → f1.length = f2.length → f1 = f2` and prove it
by `List.ext_getElem!`-style index extensionality over
`Forall2_nth_of_length` + `extend_funcinst_eq`.

## What happened to v1's three shared "templates"

- **Template A** (index-update `holds_upto` monotonicity, 7 lemmas): complete.
  bundle15 did 4, bundle16 did the last 3 (`store_none_mem_extension`,
  `table_set_table_extension` was already done, `table_grow_table_extension`).
  Key helper: `getElem!_modify_eq_or_ne` (HelperLemmas, bundle15).
- **Template B** (the `Forall₂`/list-index position-correlation bridge the
  `construct_*` family needed): **built this bundle**, in `HelperLemmas.lean`:
  `mem_modify`, `mem_zip_modify`, `mem_zip_modify₂`, `mem_zip_modify_right`,
  `mem_zip_getElem!`, `Forall2_nth_of_length`. All 7 `construct_*` lemmas are
  now proved. Note this is *not* a port of `Forall2_nth` (which stays `sorry`
  because its Rocq statement derives the length equality — see above); it is
  the same fact with the length passed in.
- **Template C** (the missing `Externaddr_ok` chain-peel inversions): **built
  this bundle** — `Externaddr_invert_funcs`/`_tables`/`_mems`/`_globals`, ported
  from `extension_lemmas.v:1065-1159`, which had *no* Lean counterpart before.
  This was the keystone: it unblocked `Extend_store_ref` (and its whole
  `_refs`/`_refs'`/`_val`/`_vals` cascade), all four `minst_invert_*`, all four
  `addrs_*_extension`, all four `addrss_*_extension`, `Extend_store_exts`,
  `Extend_store_moduleinst`, `Extend_store_funcinst(s)` and ultimately
  `Extend_store_ais`. v1 predicted it would drop ~9 lemmas a tier; in practice
  it directly or transitively unblocked ~30.

## New infrastructure added to `ExtensionLemmas.lean` this bundle

Grouped by why it exists. All are proof-engineering helpers with no Rocq
counterpart *by name* (Rocq inlines each via `inversion`/`econstructor`); they
exist because Lean's `cases` cannot invert a hypothesis whose inductive index
is an opaque term. See `insights_for_next_turn.md` §2 for the full rationale.

- **Chain-peel (Template C)**: `Externaddr_invert_funcs`, `_tables`, `_mems`,
  `_globals` (+ four `private ..._aux` lemmas carrying the equational encoding
  of Rocq's `dependent induction`).
- **`Extend_store` field accessors**: `Extend_store_wf_store`,
  `Extend_store_wf_store'`.
- **Single-instance consequences of `Extend_*inst`**: `extend_funcinst_eq`,
  `extend_globalinst_type_eq`, `extend_tableinst_sub`, `extend_meminst_sub`,
  `extend_meminst_bytes`.
- **Bare-variable `*_ok` inverters**: `funcinst_ok_invert`,
  `globalinst_ok_invert`, `meminst_ok_invert`, `meminst_ok_raw`,
  `tableinst_ok_invert`, `eleminst_ok_invert`, `limits_ok_invert`,
  `Store_ok_globalinst`, `Ref_ok_wf_store`, `Val_ok_wf_val`,
  `wf_tableinst_parts`, `wf_meminst_parts`.
- **Transport-across-extension steps**: `Extend_store_externaddr`,
  `Extend_store_eleminst_ext`, `Extend_store_datainst_ext`,
  `Extend_store_frame`.
- **`construct_*` rebuild steps**: `eleminst_ok_drop`, `datainst_ok_drop`,
  `globalinst_ok_set`, `tableinst_ok_set`, `meminst_ok_store`.
