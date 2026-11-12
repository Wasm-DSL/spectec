# ExtensionLemmas.lean sorry triage (v1)

Scope: all 76 `:= sorry` theorems in `ExtensionLemmas.lean`, each checked against its
Rocq counterpart in `test-rocq/theories/extension_lemmas.v` (line numbers below refer to
that file unless noted). Read-only triage — no proofs written, no files modified outside
this report.

Key representational facts used throughout (see task brief for full detail):
- This codebase's `Forall₂ P l1 l2 := ∀ t ∈ l1.zip l2, P t.1 t.2` (zip-based `def`, not
  length-forcing). **Consequence that cuts the other way from the usual warning**: a
  *pointwise lift* (`Forall₂ R l1 l2 → (∀ a b, R a b → R' a b) → Forall₂ R' l1 l2`) is
  **trivial** in this representation — no induction, no length fact needed — even though
  Rocq proves the analogous fact by `induction`/`List.Forall2_impl` on its inductive
  `Forall2`. This flips a lot of lemmas that look like they need "point 1's" induction
  warning into genuinely Trivial/Easy lifts. The warning still applies at full force to
  lemmas whose Rocq proof correlates a *specific list index* (e.g. matching `list_update_func`
  at position `tba`/`ga`/`ma`/`da`/`ea`) against the `Forall₂` structure — those genuinely
  need an index/length bridge this codebase doesn't yet have for free (see Template B below).
- `list_update_func := List.modify` in this codebase (not a bespoke recursive def like
  Rocq's) — so Lean core's `List.getElem_modify_eq` / `List.getElem?_modify_ne` etc. (in
  `Init/Data/List/Nat/Modify.lean`) directly give the "updated index" / "untouched index"
  facts Rocq builds by hand via `list_update_func_subst`/`list_update_func_unchanged`
  (`helper_lemmas.v`). This makes the whole `*_extension` family (global_set/store_none/
  memory_grow/table_set/table_grow/elem_drop/data_drop) noticeably easier in Lean than in
  Rocq.
- `Extend_meminst`/`Extend_tableinst`'s Lean constructors (`wasm2.0.lean:14624`,`14646`)
  carry the declared-max `Option m` field as a **shared, unsplit parameter** on both sides
  (pre/post), unlike Rocq where `option_map`/`invert_opt_map_some/none` forces an explicit
  `None`/`Some` case split to apply the constructor. So the `_grow`/`_set` extension lemmas
  do **not** need an Option split to invoke `Extend_meminst`/`Extend_tableinst` — downgrades
  them from the "Option ⇒ at least Easy/Moderate" floor to plain Easy once the index split
  is done. (The genuine Option-floor cases are `s_invert_mems`/`s_invert_tables`, where the
  goal itself reconstructs the Option existential.)
- **Missing shared infra** (not itself part of the 76, but blocks/slows several of them):
  Rocq's `Externaddr_invert_funcs`/`_tables`/`_mems`/`_globals` (`extension_lemmas.v:1065-1159`,
  a dependent induction peeling `Externaddr_ok`'s `sub` constructor down to a base
  func/table/mem/global fact plus an accumulated `Externtype_sub`) have **no Lean
  counterpart anywhere in this codebase** (confirmed by grep). Every lemma below that needs
  to invert an `Externaddr_ok` hypothesis built through a `sub`-chain has to either inline
  this induction or (better) have it ported first as new standalone infra. Flagged per-lemma
  below as "chain-peel".
- `HelperLemmas.lean`'s own `Forall2_nth`/`Forall2_lookup`/`Forall2_forall2*` (lines
  136-187) are **themselves still `sorry`** — a few lemmas below (`lookup_global`,
  `store_typed_exterval_types`) lean on this shape of fact. Noted per-lemma; these are easy
  bridging facts to prove directly via the zip-based `Forall₂` def if hit, but they are
  current gaps outside `ExtensionLemmas.lean` itself.

## Table

Line numbers are the `theorem` line in `ExtensionLemmas.lean`.

| Line | Theorem | Difficulty | Justification | Same-file dependencies |
|---|---|---|---|---|
| 135 | `Val_ok_store` | Hard (flagged) | No current Rocq counterpart found (doc comment says so); claim is swap-invariance of `Val_ok` across non-`FUNCS` fields, but `Val_ok`/`Ref_ok`/`Externaddr_ok`'s `sub` case bakes in `wf_store`, which depends on *all* fields — provability as stated is unclear without extra hypotheses. | none — standalone (but provability itself is in question) |
| 141 | `s_invert_funcs` | Easy | Invert `Store_ok`'s single constructor (zip-based `Forall₂ Funcinst_ok` falls out directly), then pointwise-invert `Funcinst_ok`'s single constructor per element. | none — standalone |
| 145 | `s_invert_globals` | Easy | Same shape as `s_invert_funcs`; `Val_ok s v_val t` is already a field of `Globalinst_ok`'s constructor, no extra derivation. | none — standalone |
| 162 | `s_invert_mems` | Moderate | Option-valued max field reconstruction (genuine floor case per rubric point 2); Lean's `pagediv` is plain `Nat` division (`b_lst.length / (64*Ki)`, no `Q`/`Z` floor juggling like Rocq) so the arithmetic itself is easy, but assembling the existential + `≤ 2^16` bound from `Memtype_ok`/`Limits_ok` inversion is real work. | none — standalone |
| 172 | `s_invert_tables` | Moderate | Same Option-field floor case as `s_invert_mems`; `Forall (Ref_ok s · rt) ref_lst` is directly available as a `Tableinst_ok` field so that part is free. | none — standalone |
| 185 | `se_invert_funcs` | Trivial | `Extend_store`'s own constructor (`wasm2.0.lean:14717`) literally carries this exact `holds_upto` triple as a field — `cases h; exact` the matching field. | none — standalone |
| 191 | `se_invert_tables` | Trivial | Same as `se_invert_funcs`, different field. | none — standalone |
| 197 | `se_invert_mems` | Trivial | Same. | none — standalone |
| 203 | `se_invert_store_globals` | Trivial | Same. | none — standalone |
| 209 | `se_invert_elems` | Trivial | Same. | none — standalone |
| 215 | `se_invert_datas` | Trivial | Same. | none — standalone |
| 227 | `limits_sub_refl` | Easy | Case split on declared-max `Option` (None/Some), mirrors the already-proved `extend_tableinst_refl_0`/`extend_meminst_refl_0` pattern in this same file (lines 365-376, 385-396). | none — standalone |
| 230 | `limits_sub_trans` | Easy | `Limits_sub` has 2 constructors (`max`/`eps`); in Lean, `cases` on both hypotheses auto-discharges the impossible cross cases (constructors pin down the shared middle `limits` value), leaving 2 real cases + `Nat.le_trans`. | none — standalone |
| 234 | `externtype_sub_refl` | Easy | 4-way case split on `externtype`; `table`/`mem` cases reuse `limits_sub_refl`. | `limits_sub_refl` |
| 237 | `externtype_sub_trans` | Easy | Same shape as `limits_sub_trans` lifted one level; `cases` auto-discharges cross cases since the middle `externtype` is shared; reuses `limits_sub_trans`. | `limits_sub_trans` |
| 243 | `externtype_global_eq` | Trivial | One inversion through `Globaltype_sub`'s single reflexivity-only constructor. | none — standalone |
| 248 | `externtype_func_eq` | Trivial | Same via `Functype_sub`. | none — standalone |
| 259 | `minst_invert_functypes` | Trivial | Direct field equality out of `Moduleinst_ok` + `inst_match`, one inversion. | none — standalone |
| 264 | `minst_invert_funcs` | Moderate | Needs the missing `Externaddr_invert_funcs`-style chain-peel (see note above) to turn the `Moduleinst_ok`-provided `Forall₂ Externaddr_ok` into the existential-with-bound-and-lookup shape; combines via `externtype_sub_trans`. | `externtype_sub_refl`, `externtype_sub_trans` |
| 275 | `minst_invert_tables` | Moderate | Same chain-peel pattern as `minst_invert_funcs`, table-flavored. | `externtype_sub_refl`, `externtype_sub_trans` |
| 284 | `minst_invert_globals` | Moderate | Same chain-peel pattern, global-flavored. | `externtype_sub_refl`, `externtype_sub_trans` |
| 293 | `minst_invert_mems` | Moderate | Same chain-peel pattern, mem-flavored. | `externtype_sub_refl`, `externtype_sub_trans` |
| 300 | `minst_invert_elems` | Easy | `ELEMS` field of `Moduleinst_ok` already stores exactly `Forall₂ (Eleminst_ok s (lookup ...))`, no `Externaddr_ok`/chain involved — direct extraction. | none — standalone |
| 306 | `minst_invert_datas` | Easy | Same shape as `minst_invert_elems` for `DATAS`. | none — standalone |
| 315 | `lookup_global` | Moderate | Combines `minst_invert_globals` with an index-bound lookup into the resulting `Forall₂`; Rocq uses `Forall2_size`/`Forall2_size2`, whose Lean analogues (`HelperLemmas.Forall2_nth`/`Forall2_lookup`) are themselves still `sorry` — doable directly via the zip def but adds friction. | `minst_invert_globals`, `externtype_global_eq` |
| 323 | `bt_inversion` | Moderate | Case split on `blocktype` shape, unfolds `fun_blocktype`/`fun_type`, threads `inst_match` equalities through; genuinely multi-step but no deep induction. | none — standalone |
| 330 | `tc_func_reference2` | Trivial | One inversion of `Moduleinst_ok`, then direct equality. | none — standalone |
| 335 | `store_typed_exterval_types` | Easy | Forward construction (not inversion) via `Externaddr_ok`'s `func` base constructor given the bound+lookup; needs a zip-membership step for the `Store_ok`-derived pointwise fact (same shape of friction as `lookup_global`, smaller). | none — standalone |
| 496 | `funcinst_same` | Hard (flagged unprovable) | Doc comment explicitly states this is **not provable as stated** without an extra length hypothesis, because zip-based `Forall₂` doesn't force `f1.length = f2.length`; deliberately left `sorry`. No Rocq counterpart found either. Needs a signature revisit, not a proof attempt. | none — standalone |
| 502 | `Extend_store_ref` | Easy | 3-case inversion of `Ref_ok`; `null`/`extern` trivial, `func` case needs `Extend_store_externaddrs_func`. | `Extend_store_externaddrs_func` |
| 505 | `Extend_store_refs` | Trivial | Pointwise lift through zip-based `Forall₂` (no induction needed — see note above). | `Extend_store_ref` |
| 512 | `Extend_store_refs'` | Trivial | Pointwise lift through `List.Forall` (`Forall.imp`-style). | `Extend_store_ref` |
| 516 | `Extend_store_val` | Trivial | 3-case inversion of `Val_ok`; two trivial cases, one calls `Extend_store_ref`. | `Extend_store_ref` |
| 519 | `Extend_store_vals` | Trivial | Pointwise lift through zip-based `Forall₂`. | `Extend_store_val` |
| 522 | `config_same` | Trivial | Structure-equality injection. | none — standalone |
| 526 | `config_same2` | Trivial | `congrArg`/`subst` the other way. | none — standalone |
| 539 | `global_set_global_extension` | Easy | Two-case split on index via `List.getElem_modify_eq`/`_ne` (Template A, below); untouched case reuses the already-proved `extend_globalinst_refl_0`; updated case is a direct `Extend_globalinst` constructor application with trivial arithmetic. | (uses already-proved `extend_globalinst_refl_0`, not itself sorry'd) |
| 549 | `store_none_mem_extension` | Easy | Template A index split; untouched case reuses already-proved `extend_meminst_refl_0`; updated case needs a small new "wf_byte preserved under `list_slice_update`" helper, provable the same way as the already-proved `list_slice_update_length` (`HelperLemmas.lean:230-234`, `induction ... using list_slice_update.induct; simp_all`). | none — standalone (may want a small new HelperLemmas addition, not itself blocking) |
| 567 | `memory_grow_mem_extension` | Easy | Template A index split; no Option-split needed (see note above); updated case is plain `Nat` inequalities (`v_i ≤ v_i + v_n`, `List.length_append`/`List.length_replicate`). | (uses already-proved `extend_meminst_refl_0`) |
| 581 | `table_set_table_extension` | Easy | Template A index split; untouched case reuses already-proved `extend_tableinst_refl_0`. | (uses already-proved `extend_tableinst_refl_0`) |
| 591 | `table_grow_table_extension` | Easy | Template A index split; no Option-split needed; plain length arithmetic. | (uses already-proved `extend_tableinst_refl_0`) |
| 604 | `elem_drop_elem_extension` | Easy | Template A index split; untouched case reuses already-proved `extend_eleminst_refl_0` (no `wf_*` premise at all for this one). | (uses already-proved `extend_eleminst_refl_0`) |
| 611 | `data_drop_data_extension` | Easy | Template A index split; untouched case reuses already-proved `extend_datainst_refl_0`. | (uses already-proved `extend_datainst_refl_0`) |
| 618 | `update_global_unchanged` | Trivial | Record-field projection equalities after `subst`; length fact is literally the already-proved `List.length_modify` (`HelperLemmas.lean:224`). | none — standalone |
| 628 | `addrs_store_funcs_extension` | Moderate | Needs the missing chain-peel (Template B, below) to invert `Externaddr_ok`, then a `holds_upto` lookup at the resolved index. | none — standalone (benefits from a shared chain-peel helper) |
| 634 | `addrs_tables_extension` | Hard | Same chain-peel as above **plus** nested `Limits_sub`/Option case-splitting to reconstruct the table extension fact (Rocq itself marks this `(* TODO improve this lemma proof later*)` — the longest/densest proof in the `addrs_*` family). | none — standalone |
| 640 | `addrs_store_globals_extension` | Moderate | Chain-peel, but goal shape is simpler than tables/mems (no nested `Limits_sub`). | none — standalone |
| 646 | `addrs_mems_extension` | Hard | Same complexity class as `addrs_tables_extension` (nested Option/`Limits_sub` nesting). | none — standalone |
| 652 | `addrss_store_funcs_extension` | Easy | Pointwise lift over `Forall₂`: the two `holds_upto` hypotheses don't vary per list element, so each element just re-invokes `addrs_store_funcs_extension` directly — no induction/length bridge needed despite Rocq inducting on the list. | `addrs_store_funcs_extension` |
| 658 | `addrss_tables_extension` | Easy | Same pointwise-lift shape. | `addrs_tables_extension` |
| 664 | `addrss_store_globals_extension` | Easy | Same pointwise-lift shape. | `addrs_store_globals_extension` |
| 670 | `addrss_mems_extension` | Easy | Same pointwise-lift shape. | `addrs_mems_extension` |
| 680 | `Extend_store_exts` | Moderate | Induction over a native `List` (fine), but each `Exportinst_ok`'s `Externaddr_ok` needs the same chain-peel pattern as the `addrs_*` family (5-way case split: global/mem/table/func/sub) before dispatching to the per-kind lemma. | `addrs_store_globals_extension`, `addrs_mems_extension`, `addrs_tables_extension`, `addrs_store_funcs_extension` |
| 683 | `Extend_store_eleminst` | Easy | Invert `Eleminst_ok`, `Forall.imp` the `Ref_ok` list via `Extend_store_ref`, pass through `wf_store'`. | `Extend_store_ref` |
| 689 | `Extend_store_eleminsts'` | Easy | Pointwise lift using an `se_invert_elems`-style `holds_upto` lookup (index bound already given by hypothesis) + `Extend_store_eleminst`. | `Extend_store_eleminst`, `se_invert_elems` |
| 695 | `Extend_store_eleminsts` | Trivial | Pointwise lift over zip-based `Forall₂`. | `Extend_store_eleminst` |
| 701 | `Extend_store_datainsts'` | Easy | Same shape as `Extend_store_eleminsts'`; `Datainst_ok` is content-independent so reconstruction is even lighter. | `se_invert_datas` |
| 706 | `Extend_store_datainsts` | Trivial | `Datainst_ok` is content/byte-independent (only needs `wf_store s'` + a length fact already available) — direct reconstruction, no real use of the `Extend_store` hypothesis beyond `wf_store'`. | none — standalone |
| 713 | `Extend_store_moduleinst` | Moderate | "The key assembly lemma" — reconstructs all ~15 `Moduleinst_ok` fields by calling out to the `addrss_*`/`Extend_store_exts`/`Extend_store_eleminsts'`/`Extend_store_datainsts'` lemmas; each piece is already handled elsewhere, this is assembly work, not new math. | `addrss_store_globals_extension`, `addrss_store_funcs_extension`, `addrss_mems_extension`, `addrss_tables_extension`, `Extend_store_exts`, `Extend_store_eleminsts'`, `Extend_store_datainsts'` |
| 719 | `Extend_store_funcinst` | Easy | Invert `Funcinst_ok`, reconstruct via `Extend_store_moduleinst`. | `Extend_store_moduleinst` |
| 722 | `Extend_store_funcinsts` | Trivial | Pointwise lift. | `Extend_store_funcinst` |
| 726 | `Extend_store_globalinst` | Trivial | Invert `Globalinst_ok`, reconstruct via `Extend_store_val`. | `Extend_store_val` |
| 729 | `Extend_store_globalinsts` | Trivial | Pointwise lift. | `Extend_store_globalinst` |
| 733 | `Extend_store_tableinst` | Easy | Invert `Tableinst_ok`, `Forall.imp` the `REFS` list via `Extend_store_ref`. | `Extend_store_ref` |
| 736 | `Extend_store_tableinsts` | Trivial | Pointwise lift. | `Extend_store_tableinst` |
| 740 | `Extend_store_meminst` | Trivial | Invert/reconstruct directly — `Meminst_ok`'s length/`Memtype_ok` facts are unaffected by store extension, only `wf_store s'` needs threading through. | none — standalone |
| 743 | `Extend_store_meminsts` | Trivial | Pointwise lift. | `Extend_store_meminst` |
| 751 | `Extend_store_externaddrs_func` | Easy | Essentially `addrs_store_funcs_extension`'s `func` case, restated ergonomically; reuses `se_invert_funcs` for the `holds_upto` witnesses needed by `addrs_store_funcs_extension`. | `addrs_store_funcs_extension`, `se_invert_funcs` |
| 767 | `Extend_store_ais` | Hard | **THE big theorem.** Rocq proves it via a custom `Scheme ais_ok_ind'` mutual induction over `Instrs_ok2`/`Expr_ok2`/`Instr_ok2` with a long constructor list (mostly `econstructor; eauto`, but several real cases: Frame-instr needs `Extend_store_moduleinst` + `Extend_store_vals`, Call-addr needs `Extend_store_externaddrs_func`, Ref needs `Extend_store_ref`). Needs a Lean mutual-induction principle over these three relations (however many admin-instruction constructors they have) — genuinely new infrastructure/large case count, not a short proof regardless of representation. | `Extend_store_moduleinst`, `Extend_store_vals`, `Extend_store_externaddrs_func`, `Extend_store_ref` |
| 782 | `construct_tableinsts` | Moderate | Rocq's proof structurally inducts on the `Forall2 Tableinst_ok` witness to correlate it with the specific `list_update_func` index `tba` (Template B gap, point 1 of the rubric); needs an index/length bridge this codebase doesn't yet have packaged. Plus a nested `Forall`-update at ref-index `i`. | none — standalone (benefits from a shared index-bridge helper) |
| 793 | `construct_tableinsts_grow` | Hard | Same Template B gap as `construct_tableinsts`, **plus** an `Option` max-field case split (genuine floor case — the conclusion's `tabletype` literally carries `j_opt` through unsplit, but the inner `wf_tableinst` reconstruction does split), bound arithmetic (`v_r.length + v_n ≤ v_j`), and a nested `Forall` over `List.replicate`. | none — standalone |
| 807 | `construct_globalinsts` | Moderate | Same Template B gap, otherwise the lightest of the `construct_*` family (direct `VALUE`-field swap, `Val_ok` already given). | none — standalone |
| 818 | `construct_meminsts` | Moderate | Same Template B gap; internal reasoning is easy since it reuses already-proved `list_slice_update_length` plus the same wf_byte-preservation helper noted for `store_none_mem_extension`. | none — standalone |
| 849 | `construct_meminsts_grow` | Hard | **Explicitly flagged in-file** as "a genuine target... not yet attempted for real" — Template B gap plus combining two bound hypotheses (`lim_old + v_n ≤ v_j`, `lim_old + v_n ≤ 2^16`) plus `Option`/wf reconstruction mirroring `construct_tableinsts_grow`'s complexity. (Silver lining: Lean's arithmetic is plain `Nat` division, not Rocq's `Q`/`Z`-floor bookkeeping, which was most of what made the Rocq proof long — but the structural gap and bound-combination work remain.) | none — standalone |
| 863 | `construct_datainsts` | Moderate | Same Template B gap; reconstruction itself is trivial (`BYTES := []` always satisfies `Datainst_ok`). | none — standalone |
| 869 | `construct_eleminsts` | Moderate | Same Template B gap; reconstruction trivial (`REFS := []`, vacuous `Forall`). | none — standalone |

## Trivial-tier suggested proof order

**Standalone, zero same-file dependencies — start here, any order (15 lemmas):**
`se_invert_funcs` (185), `se_invert_tables` (191), `se_invert_mems` (197),
`se_invert_store_globals` (203), `se_invert_elems` (209), `se_invert_datas` (215),
`externtype_global_eq` (243), `externtype_func_eq` (248), `minst_invert_functypes` (259),
`tc_func_reference2` (330), `config_same` (522), `config_same2` (526),
`update_global_unchanged` (618), `Extend_store_datainsts` (706), `Extend_store_meminst` (740).

**Trivial but gated on an Easy-tier sibling landing first (do the sibling, then these
drop out in one line each):**
- `Extend_store_refs`, `Extend_store_refs'`, `Extend_store_val`, `Extend_store_vals` — all
  gated on `Extend_store_ref` (Easy; itself only gated on `Extend_store_externaddrs_func`,
  which is Easy once `addrs_store_funcs_extension` exists).
- `Extend_store_eleminsts` — gated on `Extend_store_eleminst` (Easy).
- `Extend_store_funcinsts` — gated on `Extend_store_funcinst` (Easy, gated on
  `Extend_store_moduleinst`, Moderate).
- `Extend_store_globalinst`, `Extend_store_globalinsts` — gated on `Extend_store_val`.
- `Extend_store_tableinsts` — gated on `Extend_store_tableinst` (Easy).
- `Extend_store_meminsts` — gated on `Extend_store_meminst` (Trivial, standalone — do this
  one first and `Extend_store_meminsts` is immediately next).

Practical ordering if doing a single pass: all 15 standalone Trivials → all 27 Easy →
remaining 10 gated Trivials fall out alongside/just after their Easy sibling → Moderate →
Hard. `Extend_store_moduleinst` and `Extend_store_ais` should be done last among
non-Hard/Hard items since so much else (directly or via `Extend_store_funcinst`) hangs off
`Extend_store_moduleinst`, and `Extend_store_ais` is the single biggest lift in the file.

## Shared proof templates (so these aren't re-derived per-lemma)

**Template A — "index-update `holds_upto` monotonicity"** (7 lemmas: `global_set_global_extension`,
`store_none_mem_extension`, `memory_grow_mem_extension`, `table_set_table_extension`,
`table_grow_table_extension`, `elem_drop_elem_extension`, `data_drop_data_extension`).
Shape: given `l' = list_update_func l idx f` (i.e. `l.modify idx f`), prove
`holds_upto (fun a => Extend_X (l[a]!) (l'[a]!)) l.length`. In Lean this is:
1. `intro a ha` (from `Forall`/`List.range` membership), get `a < l.length`.
2. `by_cases h : a = idx`.
3. `a ≠ idx` branch: `l'[a]! = l[a]!` via `List.getElem!_modify_ne`-family lemma (check exact
   core name — the non-`!` versions `getElem?_modify_ne`/`getElem_modify` exist for sure in
   `Init/Data/List/Nat/Modify.lean`, may need a one-line bridge to the `!` form via
   `getElem!_pos`), then apply the already-proved `extend_X_refl_0` lemma.
4. `a = idx` branch: `l'[idx]! = f (l[idx]!)` via `List.getElem!_modify_eq`-family, rewrite
   using the `lookup_total l idx = ...` hypothesis, then apply the `Extend_X` constructor
   directly with simple `Nat`/`List.length` arithmetic (`Nat.le_add_right`,
   `List.length_append`, `List.length_replicate`, or `Nat.le_refl` for the non-growing ones).
No Option-split needed for any of these (see note at top). Worth writing this once as a
private local lemma/tactic combinator before doing all 7, rather than re-deriving per lemma.

**Template B — "`Forall₂`/`Forall` structural position-correlation gap"** (12 lemmas:
`construct_tableinsts`, `construct_tableinsts_grow`, `construct_globalinsts`,
`construct_meminsts`, `construct_meminsts_grow`, `construct_datainsts`, `construct_eleminsts`,
plus arguably `s_invert_mems`/`s_invert_tables`/`minst_invert_funcs`/`_tables`/`_globals`/`_mems`
for a related but distinct reason). Rocq proves these by `induction` directly on a
`List.Forall2`/`Forall2` witness, walking it in lockstep with `list_update_func`'s recursive
definition to identify "this is position `tba`". This codebase's zip-based `Forall₂` doesn't
support that walk directly. `HelperLemmas.lean` already has the needed bridge
(`to_mathlib_forall₂`/`from_mathlib_forall₂`, lines 508-525, **already proved**) to convert a
zip-based `Forall₂` plus an explicit length hypothesis into Mathlib's inductive
`List.Forall2`, which *does* support `induction`. The missing piece for all `construct_*`
lemmas is establishing `s.TABLES.length = ts.length` etc. up front (not given directly as a
hypothesis in any of the 5 `construct_*` signatures — needs deriving from the `Forall₂`
hypothesis itself, which is exactly what the still-`sorry` `HelperLemmas.Forall2_nth`/
`Forall2_lookup` would give for free, or can be derived ad hoc). **Recommendation**: port
`HelperLemmas.Forall2_nth` (or a minimal variant) for real before attempting any
`construct_*` lemma — it unblocks all 7 at once rather than re-solving the same
length-derivation sub-problem 7 times.

**Template C — "`Externaddr_ok` sub-chain peel"** (9 lemmas: `minst_invert_funcs`,
`minst_invert_tables`, `minst_invert_globals`, `minst_invert_mems`, `addrs_store_funcs_extension`,
`addrs_tables_extension`, `addrs_store_globals_extension`, `addrs_mems_extension`,
`Extend_store_exts`). Rocq has dedicated `Externaddr_invert_funcs`/`_tables`/`_mems`/`_globals`
lemmas (`extension_lemmas.v:1065-1159`) that peel `Externaddr_ok`'s `sub` constructor via
`dependent induction` down to a base case plus an accumulated `Externtype_sub` (composed via
`externtype_sub_trans`). **None of these four helper lemmas exist in the Lean codebase at
all** (not even as additional `sorry`s — a clean grep for `Externaddr_invert` returns
nothing). **Recommendation**: port these four as new standalone lemmas (same shape as the
Rocq originals — a straightforward `induction`/`cases` on `Externaddr_ok` since Lean's
`Externaddr_ok` is directly inductive, not zip-based) before attempting any of the 9 lemmas
above — this is likely what turns `addrs_tables_extension`/`addrs_mems_extension` from Hard
back down to Moderate, and the four `minst_invert_*`/4 `addrs_*` lemmas from Moderate to
Easy.

## Summary counts

- **Trivial: 25** (15 standalone / immediately startable; 10 gated on an Easy sibling)
- **Easy: 27**
- **Moderate: 17**
- **Hard: 7** (`Val_ok_store`, `funcinst_same` — both flagged as likely unprovable/uncertain
  as currently stated rather than merely "long"; `addrs_tables_extension`,
  `addrs_mems_extension`, `Extend_store_ais`, `construct_tableinsts_grow`,
  `construct_meminsts_grow`)
- Total: 76

Immediately startable (Trivial, zero same-file dependencies): `se_invert_funcs`,
`se_invert_tables`, `se_invert_mems`, `se_invert_store_globals`, `se_invert_elems`,
`se_invert_datas`, `externtype_global_eq`, `externtype_func_eq`, `minst_invert_functypes`,
`tc_func_reference2`, `config_same`, `config_same2`, `update_global_unchanged`,
`Extend_store_datainsts`, `Extend_store_meminst` — 15 lemmas.
