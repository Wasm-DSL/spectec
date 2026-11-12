# Digest: `subtyping.v` (914 lines) + `extension_lemmas.v` (2045 lines)

Produced by a research subagent in session 1 (resumed once after a crash).
Both files read in full (extension_lemmas.v truly ends at line 2045 with
`Qed.`, despite `wc -l` reporting 2044 due to no trailing newline). Pure
read-only research, nothing modified.

**IMPORTANT CAVEAT (from the digesting agent)**: both files
`Require Import wasm ...`. The actual *definitions* of core relations used
here — `Valtype_sub`, `Resulttype_sub`, `Store_extension` (+ constructor
`mk_Store_extension`), `Func_extension`, `Table_extension`, `Mem_extension`,
`Global_extension`, `Elem_extension`, `Data_extension`, `Store_ok`,
`Module_instance_ok`, `Val_ok`, `Ref_ok`, `Externaddrs_ok`,
`Admin_instrs_ok`/`Thread_ok`/`Admin_instr_ok`, `Limits_sub`,
`Memtype_sub`, `Tabletype_ok`, `inst_match`, `Blocktype_ok` — live in
`wasm.v` (or `typing_lemmas.v`/`type_preservation_pure.v`), NOT in these
two files. Where this digest states something about their shape, it is
**inferred** from usage (`inversion`, `econstructor`, `mk_Store_extension`
application), not copied from source. Cross-check against the `wasm.v`
digest (`digest_wasm_v.md` in this same directory) and `wasm2.0.lean`
directly before finalizing Lean signatures.

---

# FILE 1: `subtyping.v` (914 lines)

## Preamble (1-27)
```coq
From Stdlib Require Import List Bool Nat Arith.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.

Notation "tf1 :-> tf2" := (mk_functype (mk_list _ tf1) (mk_list _ tf2)) (at level 40).
Notation "t1 <tv: t2" := (Valtype_sub t1 t2) (at level 30).
Definition Resulttype_subtype ts1 ts2 := Resulttype_sub (mk_list _ ts1) (mk_list _ ts2).
Notation "ts1 <ts: ts2" := (Resulttype_subtype ts1 ts2) (at level 60).

Definition instrtype_sub tf tf' : Prop :=
  match tf, tf' with
  | ts11 :-> ts12, ts21 :-> ts22 =>
      exists ts_sub ts ts11_sub ts12_sup,
      ts21 = ts_sub ++ ts11_sub /\
      ts22 = ts ++ ts12_sup /\
      (ts_sub <ts: ts) /\
      (ts11_sub <ts: ts11) /\
      (ts12 <ts: ts12_sup)
  end.
Notation "tf1 <ti: tf2" := (instrtype_sub tf1 tf2) (at level 60).
```

**Key structural point**: `instrtype_sub` (`<ti:`) is a **defined** Prop
(existential-split formula), NOT an inductive relation. `tf <ti: tf'`
(`ts11:->ts12 <ti: ts21:->ts22`) holds iff `ts21` splits as `ts_sub ++
ts11_sub` and `ts22` as `ts ++ ts12_sup` with `ts_sub <ts: ts` (frame/prefix
compatible), `ts11_sub <ts: ts11` (contravariant: sub's remaining domain
suffix ≥ tf's domain), `ts12 <ts: ts12_sup` (covariant: tf's codomain is a
sub-result-type of the remaining codomain suffix). Standard width/depth +
frame-rule subtyping for Wasm stack-polymorphic instruction typing.
`Resulttype_subtype`/`<ts:` wraps the base `Resulttype_sub` (on `mk_list`
values) to operate on plain `seq valtype`/`list valtype`.

**Port note**: since `instrtype_sub` is a plain `def ... : Prop` (not
inductive), the Lean port is a `def` too, exactly matching
`typing_lemmas.lean`'s old `def instrtype_sub` from
`digest_prior_lean_attempts.md` §1A — **compare that old def's shape
against this Rocq original carefully**: the old Lean `instrtype_sub` used
variable names `original_ft`/`contextualized_ft`/`rest_in`/`rest_out`/
`supplied_in`/`needed_out` with 5 conjuncts; this Rocq original uses
`ts_sub`/`ts`/`ts11_sub`/`ts12_sup` with the same 5-conjunct shape — they
look structurally equivalent (both: split each side of the "bigger"
functype into a shared/frame part and a to-be-subtyped part, contravariant
domain check, covariant codomain check) but **verify the exact conjunct
correspondence field-by-field before assuming the old Lean def is right**,
since variable roles (which side is domain vs frame) need care.

## List-size helper
`size_length : forall {A : Type} (xs : seq A), size xs = length xs.` (29) — trivial.

## Valtype subtyping — refl/trans/inversion
- `valtype_sub_refl : forall t, (t <tv: t).` (33) — `apply refl` (a
  constructor of `Valtype_sub` named `refl`).
- `valtype_sub_trans: forall t1 t2 t3, t1 <tv: t2 -> t2 <tv: t3 -> t1 <tv: t3.` (39)
- `valtype_sub_non_bot: forall v t, (t <tv: v) -> (t <> BOT) -> v = t.` (49) —
  non-BOT case forces equality (BOT = universal-subtype bottom of `Valtype_sub`).
- `resulttype_sub_non_bot : forall v_ts v_ts2, Forall (fun v_t => v_t <> BOT)
  v_ts -> v_ts <ts: v_ts2 -> v_ts = v_ts2.` (60)

## Resulttype (list) subtyping — refl/size/trans/app-split
- `resulttype_sub_refl : forall ts, ts <ts: ts.` (79)
- `resulttype_sub_size_eq: forall ts1 ts2, ts1 <ts: ts2 -> size ts1 = size ts2.`
  (88) — confirms `Resulttype_sub` packages an explicit size-equality
  alongside pointwise `Forall2`.
- `resulttype_sub_trans: forall ts1 ts2 ts3, ts1 <ts: ts2 -> ts2 <ts: ts3 ->
  ts1 <ts: ts3.` (97)
- `resulttype_sub_app_trans: forall ts_sub ts ts1 ts2, ts_sub <ts: ts ->
  (ts ++ ts1) <ts: ts2 -> (ts_sub ++ ts1) <ts: ts2.` (122)
- `all2_cat' : forall A f l1 l2 l3 l4, size l1 = size l2 -> all2 f (l1++l3)
  (l2++l4) -> all2 f l1 l2 /\ all2 f l3 l4.` (152) — general mathcomp helper.
- `all2_cat : forall A f l1 l2 l3 l4, all2 f l1 l2 -> all2 f l3 l4 -> all2 f
  (l1++l3) (l2++l4).` (167) — converse.
- `resulttype_sub_app: forall ts1_sub ts2_sub ts1 ts2, (ts1_sub <ts: ts1) ->
  (ts2_sub <ts: ts2) -> (ts1_sub++ts2_sub) <ts: (ts1++ts2).` (188)
- `Forall2_app': forall {A B} R l1 l2 l1' l2', size l1 = size l1' -> Forall2
  R (l1++l2) (l1'++l2') -> Forall2 R l1 l1' /\ Forall2 R l2 l2'.` (219) —
  general list lemma, not subtyping-specific.
- `resulttype_sub_app': forall ts1_sub ts2_sub ts1 ts2, size ts1_sub = size
  ts1 -> (ts1_sub++ts2_sub) <ts: (ts1++ts2) -> (ts1_sub <ts: ts1) /\
  (ts2_sub <ts: ts2).` (238) — inverse of `resulttype_sub_app`.
- `Forall2_take`/`Forall2_drop` (255, 264) — `Forall2 R l1 l2 -> Forall2 R
  (take n l1) (take n l2)` / `drop` analog.
- `resulttype_sub_split: forall ts1 ts2 n, (ts1 <ts: ts2) -> ((take n ts1)
  <ts: (take n ts2)) /\ ((drop n ts1) <ts: (drop n ts2)).` (273)
- `drop_size_cat`/`take_size_cat` (297, 307) — standard list facts, comment
  notes "here for compatibility reasons" (i.e. duplicated from
  helper_lemmas.v-style content for local convenience).
- `resulttype_sub_split_sup: forall ts ts1 ts2, ts <ts: (ts1++ts2) ->
  ((take (size ts1) ts) <ts: ts1) /\ ((drop (size ts1) ts) <ts: ts2).` (318)
  — splits a subtype of a concatenation by the sup-side's first-piece size.
- `resulttype_sub_split_sup': forall ts ts1 ts2, (ts1++ts2) <ts: ts ->
  (ts1 <ts: (take (size ts1) ts)) /\ (ts2 <ts: (drop (size ts1) ts)).` (334)
  — dual (concatenation on the *sub* side). **These 4 split lemmas are the
  ones `InstrtypeSub.lean` (per `digest_prior_lean_attempts.md`) already
  ported and proved (0 sorry) using `List.take`/`List.drop`/
  `List.zip_append` directly — reuse those proofs.**

## `instrtype_sub` core — reflexivity, transitivity, PreOrder instances
- `instrtype_sub_refl: forall tf, tf <ti: tf.` (349) — witnesses `[], [],
  ts1, ts2`; pointwise refl `Forall2`. **Matches `InstrtypeSub.lean`'s
  already-proved `instrtype_sub_refl` — reuse.**
- `instrtype_sub_trans: forall tf1 tf2 tf3, tf1 <ti: tf2 -> tf2 <ti: tf3 ->
  tf1 <ti: tf3.` (363-436) — **hardest/longest lemma in this cluster**
  (~73 lines). Destructures both existential witnesses, has an explicit
  ASCII-art diagram (376-389) for the "sandwich" argument aligning the two
  split-witnesses' overlapping regions via `take`/`drop` of length
  `List.length ts_H12`, then `resulttype_sub_app`/`_trans`/`_split`. **Also
  already ported (0 sorry) in `InstrtypeSub.lean`, per the prior-attempts
  digest — reuse that proof, which ported Rocq's own witness-construction
  strategy.**
- `Instance valuetype_sub_preorder: RelationClasses.PreOrder Valtype_sub.` (439)
- `Instance resulttype_sub_preorder: RelationClasses.PreOrder Resulttype_sub.`
  (447) — registered on the underlying `Resulttype_sub`, not
  `Resulttype_subtype` directly.
- `Instance instrtype_sub_preorder: RelationClasses.PreOrder instrtype_sub.` (455)
  (All three `#[global] Instance` for Coq's generalized-rewriting; in Lean,
  optional — could skip or use a lightweight `Preorder`-style bundling; not
  load-bearing for the proof content itself, low priority to port formally.)

## Empty-resulttype edge cases
- `resulttype_sub_empty : forall ts, (ts <ts: []) -> (ts = []).` (462) — via `size0nil`.
- `resulttype_empty_sub : forall ts, ([] <ts: ts) -> (ts = []).` (473) — dual.

## `instrtype_sub` composition/algebra — the "frame rule" toolkit (load-bearing for instruction typing downstream)
- `instrtype_sub_compose : forall ts1 ts2 ts3 txs tys tzs, ((ts1:->ts2) <ti:
  (txs:->tys)) -> ((ts2:->ts3) <ti: (tys:->tzs)) -> ((ts1:->ts3) <ti:
  (txs:->tzs)).` (485) — "vertical" composition sharing middle type.
- `instrtype_sub_compose_le` (510) — general form allowing a "leftover
  prefix" `ts3` on the second composition's domain; long `take`/`drop`/
  `cat_take_drop` bookkeeping.
- `instrtype_sub_compose_ge` (578) — dual (leftover prefix on codomain side).
- `instrtype_sub_compose_eq` (636) — one-liner, derived from `compose_le`
  with `ts3 := []`.
- `instrtype_sub_compose_le'` (646) — restates `compose_le` with an
  explicit size-inequality split.
- `instrtype_sub_compose_ge'` (662) — dual of `compose_le'`.
- `instrtype_sub_compose1` (679) — one-liner from `compose_le` (drops
  extra `<ts:` conclusion).
- `instrtype_sub_compose0` (688) — special case of `compose1` with `ts3 :=
  []`; semantically same as `instrtype_sub_compose` but different route/name.
- `instrtype_sub_compose2` (697) — one-liner from `compose_ge`.
- `instrtype_sub_cancel_left : forall t ts1 ts2 txs tys, (((t::ts1) :->
  (t::ts2)) <ti: (txs:->tys)) -> ((ts1:->ts2) <ti: (txs:->tys)).` (706) —
  cancels a shared leading element via `instrtype_sub_trans` with trivial
  `[t]:->[t]`.
- `instrtype_sub_empty : forall txs tys, (([]:->[]) <ti: (txs:->tys)) ->
  (txs <ts: tys).` (720) — inversion.
- `instrtype_sub_sub_empty : forall txs tys, ((txs:->tys) <ti: ([]:->[])) ->
  (txs = [] /\ tys = []).` (732) — inversion.
- `instrtype_sub_sub_empty1`/`_sub_empty2` (747, 761) — partial-empty variants.
- `instrtype_sub_iff_resulttype_sub : forall ts1 ts2 ts3, (ts1 <ts: ts2) <->
  ((ts3:->ts1) <ti: (ts3:->ts2)).` (775) — resulttype subtyping ≡
  instrtype subtyping with identical shared domain, both directions.
- `instrtype_sub_iff_resulttype_sub' : forall ts1 ts2 ts3, (ts1 <ts: ts2)
  <-> ((ts2:->ts3) <ti: (ts1:->ts3)).` (807) — dual, domain-contravariance,
  shared codomain.
- `instrtype_sub_extend : forall t1s t2s txs tys tzs, (t1s:->t2s) <ti:
  (txs:->tys) -> exists t3s, ((t3s++t1s):->tzs) <ti: (txs:->tzs).` (837) —
  existence of a framing prefix making arbitrary target codomain `tzs` work.
- `instrtype_sub_add_same : forall ts1 ts2 ts3, (ts1:->ts2) <ti:
  ((ts3++ts1):->(ts3++ts2)).` (856) — explicit "frame rule": prepending
  same `ts3` to both sides preserves subtyping.
- `resulttype_sub_cons: forall t t' ts ts', (t::ts) <ts: (t'::ts') -> (t
  <tv: t') /\ (ts <ts: ts').` (867) — cons-inversion.
- `instr_subtyping_strengthen2: forall tx1 ty1 tx2 ty2 ts, ((tx1:->ty1) <ti:
  (tx2:->ty2)) -> (ts <ts: tx2) -> ((tx1:->ty1) <ti: (ts:->ty2)).` (878) —
  domain-strengthening via extra resulttype subtyping; uses
  `resulttype_sub_split_sup`. **Already proved in `typing_lemmas.lean`**
  per `digest_prior_lean_attempts.md` §1A.
- `instr_subtyping_weaken2: forall tx1 ty1 tx2 ty2 ts, ((tx1:->ty1) <ti:
  (tx2:->ty2)) -> (ty2 <ts: ts) -> ((tx1:->ty1) <ti: (tx2:->ts)).`
  (898-914, LAST declaration in file) — dual codomain-weakening, via
  `resulttype_sub_split_sup'`. **Already ported+proved in
  `InstrtypeSub.lean` — was one of the 4 `typing_lemmas.lean` sorries;
  reuse.**

## Overall subtyping.v structure to mirror
(1) refl/trans/inversion for `Valtype_sub`/`Resulttype_sub` (base relations
from `wasm.v`); (2) list-algebra plumbing (`_app`, `_app'`, `_split`,
`_split_sup`, `_split_sup'`, take/drop); (3) `instrtype_sub` def + its own
refl/trans (trans is the hardest, ~60 lines, explicit diagram); (4)
PreOrder typeclass registrations (3 instances, low priority to port
formally); (5) empty-resulttype edge cases; (6) the large composition
algebra (`compose`, `compose_le`, `compose_ge`, 6 derived variants) — the
proof-engineering core reused throughout type-preservation; (7)
iff-characterizations tying `<ti:` back to `<ts:`; (8) two final
framing/strengthen-weaken lemmas.

---

# FILE 2: `extension_lemmas.v` (2045 lines, ends `Qed.` at line 2045)

## Preamble (1-11)
Imports `wasm helper_lemmas helper_tactics typing_lemmas subtyping
type_preservation_pure` — i.e. this file is downstream of ALL of those
(including `type_preservation_pure.v`!). mathcomp ssreflect suite.

## `option_map` helpers
`invert_opt_map_some`/`invert_opt_map_none` (12, 16) — trivial.

## `Store_ok` inversion (per-component wellformedness; store-swap invariance for `Val_ok`)
- `Val_ok_store: forall f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 v t, Val_ok {|
  store_FUNCS:=f1; store_GLOBALS:=g1; ...|} v t <-> Val_ok {|
  store_FUNCS:=f1; store_GLOBALS:=g2; ...|} v t.` (20) — `Val_ok` for a
  value at a valtype depends **only on `store_FUNCS`** (funcref validity
  needs the func list; nothing else).
- `s_invert_funcs: forall s, Store_ok s -> exists fts, List.Forall2 (fun f
  t => exists minst v_func, f = {|funcinst_TYPE:=t; funcinst_MODULE:=minst;
  CODE:=v_func|}) (store_FUNCS s) fts.` (57)
- `s_invert_globals` (89), `s_invert_mems` (121, encodes memory page-count
  invariant `v_n = byte-length / 64KiB` and hard cap `v_m <= 2^16` pages),
  `s_invert_tables` (172) — analogous per-component inversion.

## `Store_extension` component-wise inversion — THE central structural pattern
- `se_invert_funcs: forall s s', Store_extension s s' -> exists fs' fs2,
  Forall2 Func_extension (store_FUNCS s) fs' /\ store_FUNCS s' = fs' ++
  fs2.` (211)
- Same pattern for `se_invert_tables`/`_mems`/`_store_globals`/`_elems`/
  `_datas` (224, 238, 252, 266, 280).

**Inferred shape of `Store_extension`** (from these 6 lemmas + from
`store_extension_refl`'s explicit `mk_Store_extension` application with 14
args at line 771-773): single constructor `mk_Store_extension` taking old
store `s`, new store `s'`, and for each of 6 component kinds (FUNCS,
GLOBALS, TABLES, MEMS, ELEMS, DATAS) a pair of lists `(xs', xs2)` — the
"extended-prefix" and "appended-suffix" — with `store_X s' = xs' ++ xs2`
and `Forall2 X_extension (store_X s) xs'`. **I.e.: a store extends another
iff each of its 6 component lists is (pointwise extension of the old list)
followed by (arbitrary brand-new entries)**. This is the load-bearing
invariant every later lemma exploits: lookups into the old-index range land
in the `xs'` prefix (extension-related to old entry); new indices beyond
old length are in `xs2` (unconstrained). **Cross-check this inferred shape
against `wasm2.0.lean`'s `Extend_store` (line 12460, already confirmed by
session 1 in NOTES.md) — the Lean backend's version uses `Forall (fun a =>
a < length ... ) (List.range (length s.X))` + pointwise `Extend_Xinst`
indexed by position, which is a DIFFERENT but likely equivalent
encoding (index-bound + pointwise-at-index, vs prefix-Forall2 + suffix-append)
— verify equivalence before assuming lemmas transfer directly.**

Helper tactics `invert_funcs`/`invert_tables`/`invert_mems`/`invert_elems`/
`invert_datas` (461-529) — not lemmas, Ltac sugar.

## `Module_instance_ok`/`inst_match` interaction with store contents
- `minst_invert_functypes` (294) — trivial.
- `minst_invert_funcs` (303), `minst_invert_tables` (325, involves
  `Limits_sub` — context may present widened limits vs the concrete table),
  `minst_invert_globals` (350), `minst_invert_mems` (373, involves
  `Memtype_sub`), `minst_invert_elems` (395), `minst_invert_datas` (426).

## Misc lookup/inversion lemmas
- `lookup_global` (532) — long, chains `Forall2_nth` twice through
  module-instance and store-global relations.
- `bt_inversion` (572) — the computable elaboration function
  `fun_blocktype` agrees with the declarative `Blocktype_ok` relation's
  chosen functype.
- `tc_func_reference2` (600) — trivial.
- `store_typed_exterval_types` (611).

## Extension relations are reflexive per store-component kind
- `func_extension_refl0`/`func_extension_refl` (629, 636) — trivial/pointwise.
- `table_extension_refl0` (646) — nontrivial: needs an `assert (exists n,
  option_map mk_uN n = u32_opt)` case-split to convert the max-limit field.
- `table_extension_refl` (663).
- `mem_extension_refl0`/`mem_extension_refl` (673, 689) — same
  `u32_opt`/`mk_uN` case-split pattern.
- `global_extension_refl_0` (699) — proof `econstructor; eq_to_prop; by
  right.` → `Global_extension` has ≥2 constructors, refl picks the
  `right`/second (likely "value possibly changed under MUT_MUT" disjunct,
  here with value equal).
- `global_extension_refl` (710).
- `elem_extension_refl0` (725) — proof `econstructor; eq_to_prop; by
  left.` → `Elem_extension` also ≥2 constructors, refl picks `left`/first.
- `elem_extension_refl` (735).
- `data_extension_refl0`/`data_extension_refl` (746, 756) — same `by left` pattern.
- `store_extension_refl: forall s, Store_extension s s.` (767) — **the
  store-level reflexivity lemma**, instantiates `mk_Store_extension s s
  (store_FUNCS s) [] (store_GLOBALS s) [] ... (store_DATAS s) []` (new-prefix
  = old list, new-suffix = `[]` for every component), via `cats0` + the 6
  `*_extension_refl` lemmas. **Already matched, per
  `digest_prior_lean_attempts.md`, by `Extension.lean`'s
  `extend_globalinst_refl`/`extend_funcinst_refl`/`extend_datainst_refl`/
  `extend_eleminst_refl`/`extend_tableinst_refl`/`extend_meminst_refl`/
  `extend_store_refl` — ALL 0 sorry, matches Rocq `extension_lemmas.v:
  926-1627` per that digest (NOTE: those Rocq line numbers cited in the old
  digest don't match THIS digest's `767` for `store_extension_refl` — likely
  version drift between when that old note was written and this file's
  current state; re-verify signatures via grep, not memory, before reuse,
  per the project's own stated convention). Reuse those Lean proofs.**
  **IMPORTANT — no explicit `store_extension_trans` (transitivity) lemma
  found anywhere in this file.** Transitivity of `Store_extension` is not
  proved as a standalone theorem here; downstream preservation-proof usages
  seem to re-derive extension facts directly per reduction step rather than
  composing two `Store_extension` proofs. Check the other files (typing_lemmas.v/
  type_preservation.v, already digested — search their digests) for whether
  such a lemma exists before assuming it's absent from the whole
  development; if genuinely absent, the Lean port doesn't need it either
  (matches `Extension.lean`'s own note that no transitivity was attempted,
  flagged as possibly needed if `store_extension_reduce` ever chains steps).
- `funcinst_same: forall f1 f2, Forall2 Func_extension f1 f2 -> f1 = f2.`
  (787) — `Func_extension` forces literal equality (funcs immutable once
  allocated, no mutable fields) — pointwise-extended implies list-equal.
  Used pervasively downstream to erase func-extension side conditions.

## `Store_extension` preserves `Ref_ok`/`Val_ok` (+ pointwise-list lifts)
- `store_extension_ref` (796) — case-split on `Ref_ok` constructors; uses
  `funcinst_same` + index-into-`fs'++fs2` `lookup_app` step (lands in `fs'`
  prefix).
- `store_extension_refs` (819) — via `List.Forall2_impl`.
- `store_extension_val` (833) — analogous to `store_extension_ref`.
- `store_extension_vals` (854) — pointwise-list lift.
- `config_same`/`config_same2` (869, 877) — record-injectivity helpers,
  not extension-specific.

## Extension facts produced by specific store-mutating operations (one pair per Wasm store-mutating instruction)
- `global_set_global_extension` (885) — `global.set` on a `MUT_MUT` slot
  satisfies `Global_extension` pointwise.
- `store_none_mem_extension` (916) — `memory.store` (in-place byte-slice
  overwrite via `list_slice_update`, memtype unchanged).
- `memory_grow_mem_extension` (950) — `memory.grow` (append `v_n`
  zero-pages, bump min-limit, checked against max `v_j`).
- `table_set_table_extension` (990) — `table.set` (single-slot ref update).
- `table_grow_table_extension` (1030) — `table.grow` (append `n` copies of
  `ref`, bump min-limit).
- `elem_drop_elem_extension` (1075) — `elem.drop` clears an elem segment's
  REFS to `[]`.
- `data_drop_data_extension` (1098) — `data.drop` analogue.
- `update_global_unchanged` (1121) — frame lemma: updating only
  `store_GLOBALS` leaves every other component (and globals-length)
  literally unchanged.

**These 7 lemmas are exactly the per-instruction store-extension facts that
`StoreExtension.lean` (per `digest_prior_lean_attempts.md`) already ported:
`local_set` (n/a here, not a store op — table.set covers table_set_val
etc.), `elem_drop`, `data_drop`, `table_set_val` match directly. The prior
attempt's remaining 7 sorries (`global_set`, `table_grow_succeed`,
`memory_grow_succeed`, `store_num_val`/`store_pack_val`/`vstore_val`/
`vstore_lane_val`) correspond to `global_set_global_extension`,
`table_grow_table_extension`, `memory_grow_mem_extension`,
`store_none_mem_extension`-family — THESE ROCQ LEMMAS ARE FULLY PROVED
HERE, so the Lean port CAN close those gaps now by porting this file's
actual proofs, rather than treating them as blocked-on-missing-typing-infra
as the prior attempt concluded. Re-read `StoreExtension.lean`'s specific
blockers against these exact Rocq statements before assuming they still
apply — the prior session may not have had this file's content available.**

## `Externaddrs_ok` preserved by store extension (single-index and list forms)
`addrs_store_funcs_extension` (1137), `addrs_tables_extension` (1170, also
re-derives limits validity via `leq_trans`), `addrs_store_globals_extension`
(1221), `addrs_mems_extension` (1262, `leq_trans` limits argument),
`addrss_store_funcs_extension` (1310, pointwise-list lift; note double-s
naming = pluralized), `addrss_tables_extension` (1329),
`addrss_store_globals_extension` (1348), `addrss_mems_extension` (1370).

## `Store_extension` preserves `Export_instance_ok`/`Element_instance_ok`/`Data_instance_ok`/`Module_instance_ok`
- `store_extension_exts` (1391) — induction over export list, case-splits
  4 externval kinds, dispatches to `addrs_*_extension`.
- `store_extension_eleminst` (1415) — single eleminst; REFS stay `Ref_ok`
  via `store_extension_ref`.
- `store_extension_eleminsts'` (1436) — address-based version (module
  instance ELEMS fields addressed by index), uses `Forall2_nth2` +
  `lookup_app`.
- `store_extension_eleminsts` (1496) — direct-value pointwise-list version.
- `store_extension_datainsts'` (1513) — address-based; note
  `Data_instance_ok`'s proof is just `destruct...; econstructor` — i.e.
  content-independent/always-true.
- `store_extension_datainsts` (1547) — direct-value version.
- `store_extension_moduleinst: forall v_S v_S' v_i v_C, Store_extension
  v_S v_S' -> Module_instance_ok v_S v_i v_C -> Module_instance_ok v_S'
  v_i v_C.` (1560) — **the key assembly lemma**: reconstructs
  `Module_instance_ok` via `mk_Module_instance_ok` from
  `store_extension_eleminsts'`, `store_extension_datainsts'`, the 4
  `addrss_*_extension` lemmas, and `store_extension_exts`. **This is used
  by `type_preservation.v`'s `step_moduleinst` (#11 in
  `digest_type_preservation.md`) — direct dependency, port this before that.**

## `Store_extension` preserves `*_instance_ok` (function/global/table/memory instance typing)
`store_extension_funcinst`/`_funcinsts` (1590, 1601, via
`store_extension_moduleinst`), `store_extension_globalinst`/`_globalinsts`
(1615, 1626, via `store_extension_val`), `store_extension_tableinst`/
`_tableinsts` (1640, 1658, via `store_extension_ref`, uses
`invert_tables`/`invert_funcs` tactics), `store_extension_meminst`/
`_meminsts` (1672, 1683, trivial — doesn't depend on other components),
`store_extension_externaddrs_func` (1697 — second, more ergonomic
tactic-based proof of essentially `addrs_store_funcs_extension`'s func
case, preferred form downstream).

## Mutual induction scheme + the big `Admin_instrs_ok`/`Thread_ok`/`Admin_instr_ok` monotonicity theorem
```coq
Scheme ais_ok_ind' := Induction for Admin_instrs_ok Sort Prop
  with thread_ok_ind' := Induction for Thread_ok Sort Prop
  with ai_ok_ind' := Induction for Admin_instr_ok Sort Prop.
```
(1718) — custom mutual induction principle over the three mutually-inductive
administrative typing judgments. **NOTE**: `wasm2.0.lean` apparently names
these differently (`Instr_ok2`/`Instrs_ok2`/`Expr_ok2` per session 1's
NOTES.md, not `Admin_instr_ok`/`Admin_instrs_ok`/`Thread_ok`) — build the
exact 3-way correspondence (which Lean judgment ↔ which Rocq judgment)
before porting; likely `Admin_instr_ok`↔`Instr_ok2`,
`Admin_instrs_ok`↔`Instrs_ok2`, `Thread_ok`↔ something involving `Frame_ok`
(a frame+its typing, given the "callee Thread_ok/Frame_ok" language from
`digest_type_preservation.md`'s case #10 write-up) — **needs direct
confirmation**, don't assume.

- `store_extension_ais: forall s s' c ais ft, Store_extension s s' ->
  Store_ok s -> Store_ok s' -> Admin_instrs_ok s c ais ft ->
  Admin_instrs_ok s' c ais ft.` (1724) — **THE big monotonicity theorem**:
  admin-instruction-sequence typing preserved under store extension (given
  both stores well-formed). Proved via `ais_ok_ind'` with 3 simultaneous
  motives (each: ∀ target store s', requiring `Store_ok s`, `Store_ok s'`,
  `Store_extension s s'`, concluding analogous fact for `s'`). Most cases:
  `intros; econstructor; eauto` (direct IH). Explicit extra cases: (a)
  reusing `HType` directly; (b) `Thread_ok`/frame case, needs
  `store_extension_moduleinst` on frame's module instance +
  `store_extension_vals` on locals; (c) 2 `Admin_instr_ok` cases
  (func-call-style, referencing `Externaddrs_ok`), via
  `store_extension_externaddrs_func`. **This is presumably the Rocq source
  of `store_extension_ais` used inside `type_preservation.v`'s
  `t_preservation_type` (`Context Instrs` case, congruence via
  `store_extension_ais` per `digest_type_preservation.md` #12) — direct
  dependency, confirmed cross-file link.**

## "construct_*" lemmas — complementary direction (pre-mutation typing witness + fresh `Ref_ok`/`Val_ok` for new payload → post-mutation typing witness)
These pair with the extension-fact lemmas above to reconstruct `Store_ok`
after each store-mutating reduction step, in the external preservation
proof (`type_preservation.v`'s `store_extension_reduce`, per
`digest_type_preservation.md` #8 — **these ARE the "helper lemmas" that
digest cites by name**: `global_set_global_extension`,
`table_set_table_extension`, `table_grow_table_extension`,
`elem_drop_elem_extension`, `store_none_mem_extension`,
`memory_grow_mem_extension`, `data_drop_data_extension` — confirmed
exact-name match to lines 885, 990, 1030, 1075, 916, 950, 1098 above):
- `construct_tableinsts` (1776) — `table.set` preserves table typedness at
  unchanged type list `ts`.
- `construct_tableinsts_grow` (1817) — `table.grow` preserves typedness,
  updates the type list too (min bumped by `v_n`, checked against max).
- `construct_globalinsts` (1893) — `global.set` preserves global typedness
  (type list unchanged, mutable globals don't change globaltype).
- `construct_meminsts` (1919) — `memory.store` preserves typedness (memtype
  unchanged; length invariance via `list_slice_update_length`).
- `construct_meminsts_grow` (1946) — `memory.grow` preserves typedness,
  updates type list too; byte-length arithmetic via `mulnDl`/`Nat.div_mul`.
- `construct_datainsts` (2002) — `data.drop` preserves data typedness
  trivially (`Data_instance_ok` has no content constraint).
- `construct_eleminsts` (2025-2045, LAST declaration in file) — `elem.drop`
  preserves element typedness trivially.

## Overall extension_lemmas.v structure to mirror
Everything downstream of an (externally-defined, in `wasm.v`)
`Store_extension` relation (single constructor, per-component
prefix-extended + suffix-appended shape, see above). Port order: (1)
`Store_ok`/`Store_extension` inversion lemmas (`se_invert_*`, `s_invert_*`)
— critical scaffolding, translate first; (2) `Module_instance_ok`/
`inst_match` lookup-inversion lemmas (reuse subtyping.v's `Limits_sub`/
`Memtype_sub` machinery for tables/mems); (3) reflexivity of each
component-level extension relation, then `Store_extension` itself (no
transitivity lemma in this file — check elsewhere, see note above); (4)
monotonicity of `Ref_ok`/`Val_ok`/`Vals_ok` under extension; (5)
per-operation "mutation yields extension" lemmas (7 lemmas, one per
store-mutating instruction — already portable, closes prior attempt's
open sorries, see note above); (6) monotonicity of `Externaddrs_ok`,
`Export_instance_ok`, `Element_instance_ok`, `Data_instance_ok`, → capstone
`store_extension_moduleinst` → `store_extension_funcinst`/`globalinst`/
`tableinst`/`meminst`; (7) capstone `store_extension_ais` (custom
`Scheme`-generated mutual induction over `Admin_instrs_ok`/`Thread_ok`/
`Admin_instr_ok`); (8) dual "construct_*" family (7 lemmas, mirrors section
5 exactly) — given pre-mutation typing + fresh `Ref_ok`/`Val_ok`,
reconstruct post-mutation typing. **Sections 5+7+8 together are exactly the
three ingredients `type_preservation.v`'s `store_extension_reduce` (Admitted
only for SIMD, per `digest_type_preservation.md` #8) needs per
reduction rule — this file supplies essentially all of it for non-SIMD
cases.**
