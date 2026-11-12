# Digest: `typing_lemmas.v` (2222 lines) + `type_preservation_pure.v` (947 lines)

Produced by a research subagent in session 1 (resumed once after a crash).
Both files read in full, sequentially, no gaps. Pure read-only research,
nothing modified.

---

# FILE 1: `test-rocq/theories/typing_lemmas.v` (2222 lines)

## Overall organization (NOT one inversion lemma per instruction constructor)

1. ONE big case-exhaustive `Definition ai_principal_typing` (+ surface
   wrapper `instr_principal_typing`) gives, for every admininstr/instr
   constructor, its exact ("principal") type as an existential/equality
   Prop mirroring each typing rule's premises verbatim.
2. Two "soundness" theorems connect this definition to the real inductive
   typing judgments: `instr_typing_inversion` (surface `Instr_ok`, exact
   match) and `ai_typing_inversion` (administrative `Instr_ok2`, match up
   to `<ti:` subtyping slack, since `Instr_ok2` bakes in width/depth
   subsumption).
3. All later per-instruction-shape facts used elsewhere (esp.
   `type_preservation_pure.v`) are obtained by **unfolding this definition
   via automation** (`unfold_principal_typing`, `resolve_all_pt`), not via
   separate named lemmas per instruction.
4. The file also proves generic *structural* lemmas (empty/single/seq/
   append composition, inversion+construction, both directions) for each
   of the four typing judgment families: `Instr_ok`/`Instrs_ok` (surface,
   no store) and `Instr_ok2`/`Instrs_ok2` (administrative, with store) —
   proved once per judgment-shape, independent of instruction category.
5. A few extra specialized inversion lemmas exist only for `val`/`ref`
   administrative forms (constantly used, representing "the stack").
6. The back half (~1960-2222) is pure Ltac automation infra (no more
   Lemma/Definition) — the proof engine (`construct_ais_typing`,
   `invert_ais_typing`, `typing_inversion`, `join_subtyping_*`,
   `resolve_subtyping`, etc.) that `type_preservation_pure.v` (and
   presumably `type_preservation.v`) is built on top of. **This Ltac layer
   does not need 1:1 porting** — in Lean, expand the automation into
   explicit proof steps per lemma, or write Lean tactic macros if a
   pattern recurs often enough to be worth it (judgment call, not
   required for fidelity since only signatures must match).

## Header/imports (1-11)
`wasm helper_lemmas helper_tactics subtyping`; mathcomp `all_ssreflect
all_algebra`; RecordUpdate.

## uN-family coercions (12-71)
Repeated bidirectional `nat <-> X` coercion pattern for `u32`, `labelidx`,
`localidx`, `globalidx`, `memidx`, `tableidx`, `idx`; `fun_res_list__list`/
`fun_list__res_list` coercions for `list`↔`res_list`; `functype_from_lists`;
**`Notation "tf1 :-> tf2" := (mk_functype (mk_list _ tf1) (mk_list _ tf2))
(at level 40)`** — the pervasive functype-arrow notation used everywhere.
(Lean equivalent already exists per `custom_notation.lean`'s `f->` /
`mkFunctype`, see `digest_prior_lean_attempts.md`.)

## Context update helpers (76-172)
`upd_label`, `upd_local`, `upd_return`, `upd_local_return`,
`upd_local_label_return` (all trivial record-update `Definition`s), plus:
- `upd_label_overwrite`, `upd_label_is_same_as_append`,
  `upd_local_is_same_as_append`, `upd_local_return_is_same_as_append`,
  `upd_return_is_same_as_append` — all `reflexivity`/trivial, relate the
  `upd_*` defs to the generic `@@`-append-typeclass operations.
- `upd_label_unchanged: LABELS C = lab -> upd_label C lab = C.`
- `upd_label_unchanged_typing` (iff): `Instrs_ok2 v_S v_C v_admininstrs
  v_funcontext_type <-> Instrs_ok2 v_S (upd_label v_C (LABELS v_C))
  v_admininstrs v_funcontext_type.` (NOTE: this exact lemma name matches
  the file `spectec/test-rocq/upd_label_unchanged_typing_verified_walkthrough.md`
  sitting at the top of `test-rocq/` — that file is likely a detailed
  worked explanation of this specific lemma, worth reading if porting it.)

## `instr_of : admininstr -> option instr` (174-245)
Exhaustive-ish match, ~50 "plain" admininstr constructors → `Some
<corresponding instr>`; catchall `None` for purely-administrative forms
(val, ref, LABEL_, FRAME_, CALL_ADDR, REF_FUNC_ADDR, REF_HOST_ADDR, TRAP).

## Context/store well-formedness projections (247-278)
- `instr_ok_context_wf : Instr_ok v_C v_instr v_ft -> wf_context v_C /\ wf_instr v_instr.`
- `ainstr_ok_context_store_wf : Instr_ok2 v_S v_C v_ainstr v_ft -> wf_context v_C /\ wf_store v_S /\ wf_admininstr v_ainstr.`
- `instrs_ok_context_wf : Instrs_ok v_C v_instrs v_ft -> wf_context v_C /\ List.Forall wf_instr v_instrs.`
- `ainstrs_ok_context_store_wf : Instrs_ok2 v_S v_C v_ainstrs v_ft -> wf_context v_C /\ wf_store v_S /\ List.Forall wf_admininstr v_ainstrs.`
All four: trivial `inversion`-based base wellformedness-extraction lemmas
for the 4 typing judgments (surface single/list, administrative single/list).

## Composition/empty-typing lemmas (280-424)
- `instrs_empty_typing` (iff): `Instrs_ok v_C [] (t1s :-> t2s) <-> wf_context
  v_C /\ t1s <ts: t2s.` Forward: dependent induction, chains
  `resulttype_sub_trans`/`resulttype_sub_app`. Backward: `sub`+`frame`+`empty`.
- `ai_principal_typing (v_S: store) (v_C: context) v_ai v_ft : Prop` **THE
  central definition of the file** (427-673) — see full per-constructor
  breakdown in the raw digest text if needed when actually porting; key
  entries include NOP/UNREACHABLE/DROP/SELECT/BLOCK/LOOP/IFELSE/BR/BR_IF/
  BR_TABLE/CALL/CALL_INDIRECT/RETURN/CONST/UNOP/BINOP/TESTOP/RELOP/CVTOP/
  VCONST/REF_NULL/REF_FUNC/REF_IS_NULL/LOCAL_GET,SET,TEE/GLOBAL_GET,SET/
  TABLE_GET,SET,SIZE,GROW,FILL,COPY,INIT/ELEM_DROP/LOAD/STORE/MEMORY_SIZE,
  GROW,FILL,COPY,INIT/DATA_DROP/REF_FUNC_ADDR/REF_HOST_ADDR/CALL_ADDR/
  LABEL_/FRAME_/TRAP. **Most SIMD ops are commented out / fall to the final
  catchall `_ => True`** (vacuous, no real inversion info extracted for
  SIMD) — consistent with type_preservation.v's SIMD gaps.
  BLOCK's label uses output type t'; **LOOP's label uses input type t**
  (important asymmetry to preserve exactly).
- `instr_principal_typing (v_C : context) v_instr v_ft : Prop :=
  ai_principal_typing default_val v_C (admininstr_instr v_instr) v_ft.`
  (surface wrapper, store irrelevant, dummy `default_val` store plugged in
  — Lean equivalent needs a `[Inhabited store]` or explicit dummy value).

## Master inversion theorems (679-850)
- `instr_typing_inversion: Instr_ok v_C v_instr (t1s :-> t2s) ->
  instr_principal_typing v_C v_instr (t1s :-> t2s).` EXACT match (no
  subtyping slack at single-instruction level). Medium-high tedium proof
  (mechanical unfolding + manual sub-proofs for SELECT/CONST/VCONST/
  TABLE_INIT/LOAD-None/LOAD-Some/STORE-Some).
- `ai_typing_inversion: Instr_ok2 v_S v_C v_ai (t1s :-> t2s) -> exists
  t1s' t2s', ai_principal_typing v_S v_C v_ai (t1s' :-> t2s') /\ ((t1s' :->
  t2s') <ti: (t1s :-> t2s)).` **THE master per-instruction inversion
  lemma**, administrative level, up to `<ti:` subtyping. `dependent
  induction` + 57-way `destruct v_instr` (LOAD singled out with extra
  ~25-line I32/I64-extension sub-proof), generic automation for most
  branches, hand blocks for BR/VCONST/TABLE_INIT, separate top-level
  administrative cases `label`/`frame`/`call_addr`/`ref`/`trap`. **Highest
  difficulty/longest proof in the "inversion" family.**

## Single/seq/append composition, both directions (852-1218)
- `split_single_append` (generic list helper)
- `instrs_single_typing_inversion`, `ais_single_typing_inversion'`,
  `ais_single_typing_inversion` (composes previous two via
  `instrtype_sub_trans`) — **`ais_single_typing_inversion` is the
  single most-used lemma downstream** in `type_preservation_pure.v`.
- `ais_single_ref_typing_inversion`, `val_ref_null_is_ref`,
  `ais_single_val_typing_inversion` (case-splits on 5 `wasm.val`
  constructors)
- `instrs_seq_typing_inversion` (surface, 1056-1119): `Instrs_ok v_C
  ([v_instr] ++ v_instrs) (t1s :-> t2s) -> exists t3s, Instrs_ok v_C
  v_instrs (t3s :-> t2s) /\ Instrs_ok v_C [v_instr] (t1s :-> t3s).`
  **THIS IS THE ROCQ-FAITHFUL SHAPE** — note both conjuncts are `Instrs_ok`
  (sequence-level), NOT `Instr_ok` (singular) on the head. See
  `digest_prior_lean_attempts.md` §3/§6#10 — the old `typing_lemmas.lean`
  mis-stated this with singular `Instr_ok` on the head and the statement
  was FALSE; when porting THIS lemma, use the sequence-level form shown
  here, matching `SeqTypingInversion.lean`'s already-proved
  `instrs_seq_typing_inversion_fixed`.
- `ais_seq_typing_inversion` (administrative analog, 1121-1182) — same
  correct sequence-level shape. **This is presumably the exact Rocq source
  of the "fix" the prior Lean session ported, confirming
  `SeqTypingInversion.lean`'s restatement is the right target.**
- `ais_composition_typing` (1184-1218): generalizes singleton to arbitrary
  prefix `v_ais1`, induction on `v_ais1`, base case via `ais_empty_typing`.

## Ltac automation, first layer (1220-1334)
`do_instr_typing_inversion`, `do_instrs_typing_inversion`,
`do_ai_typing_inversion`, `do_ais_typing_inversion`, top-level dispatcher
`typing_inversion` — used pervasively (dozens of call sites) downstream.
Not for 1:1 porting; represents proof-search dispatch logic.

## More inversion/construction + automation (1335-1595)
- `ai_val_principal_typing_inversion`
- `unfold_instrtype_sub` (Ltac) — reveals `<ti:` (instrtype_sub)'s
  definitional shape: existential composition of a "frame" list + two
  `<ts:` (resulttype_sub) facts + one equation (width+depth subtyping,
  defined in `subtyping.v`).
- `injective_admininstr_instr`
- `construct_instrs_typing_single`, `construct_ais_typing_single`
  (construction direction, surface/administrative)
- `construct_ais_subtyping` (subsumption/weakening construction)
- `injective_valtype_numtype`
- `construct_ais_compose` — construction-direction dual of
  `ais_composition_typing`; heavily reused downstream to glue partial
  typing derivations back together.
- `construct_ai_const_I32`, `construct_ai_ref`, `adminval_val_ref`,
  `construct_ai_val`
- `construct_ai_maybe`: `((instr_of ai) <> None) -> wf_store v_S ->
  (Instr_ok v_C (the (instr_of ai)) (t1 :-> t2)) -> Instr_ok2 v_S v_C ai
  (t1 :-> t2).` — lifts plain-`instr_of`-recoverable typing to
  administrative typing.
- `construct_ais_vals'`: **context-irrelevance for value-list typing**
  (value typing doesn't depend on local/label/return components of C,
  only `wf_context` + `v_S`) — crucial for label/frame-boundary-crossing
  lemmas.
- `construct_ais_trap`: `wf_context v_C -> wf_store v_S -> Instrs_ok2 v_S
  v_C [TRAP] v_ft.` — TRAP typechecks at ANY functype (bottom-like); used
  for generic "trapping preserves typing at any type" branches.

## Val_ok/Vals_ok infrastructure (1596-1805)
- `value_extra` (helper Definition, handles `REF_FUNC_ADDR`'s extra
  store-lookup obligation)
- `Vals_ok v_S v_vals v_ts := List.Forall2 (fun t v => Val_ok v_S v t) v_ts
  v_vals.` (NOTE argument order: `Forall2 P v_ts v_vals`, types first)
- `Val_ok_non_bot`: `Val_ok v_S v_val t_lst -> t_lst <> BOT.`
- `ais_vals_typing_inversion`: "list of values on the stack" inversion,
  used pervasively for br/return/label-collapse reasoning.
- `construct_ais_vals`: construction converse; **longest/most intricate
  proof in the file** (~125 lines), `last_ind` (right-to-left induction)
  simultaneously on `v_vals`/`ts`, heavy `rcons`/`cats1`/`take`/`drop`/
  `size` manipulation. High difficulty.

## Subtyping-composition helpers (1807-1831)
- `resulttype_sub_single_inversion`
- `construct_ais_instrtype_sub` — **appears to be a duplicate of
  `construct_ais_subtyping`** (same statement/proof, different name), both
  used interchangeably downstream. Fine to collapse to one Lean lemma with
  two names/aliases, or just one — user's "obvious optimization" allowance.

## `inst_match` — context-component invariance (1833-1922)
`inst_match C C' := TYPES/FUNCS/GLOBALS/TABLES/MEMS/ELEMS/DATAS all equal`
(deliberately excludes LOCALS/LABELS/RETURN — "same module-instance-derived
components, differing local/label/return typing"). NOTE: `wasm2.0.lean`
already has `inst_match`?? — check; the prior Lean session's
`custom_notation.lean`/`typing_lemmas.lean` had its own `inst_match` def,
confirm whether it matches this Rocq shape exactly (7 fields) before reuse.
Helper lemmas: `construct_inst_match_label/return/local/
local_label_return/local_return`, `construct_inst_prepend_label`, plus
`resolve_inst_match` (Ltac).

## Non-bottom propagation to lists (1927-1959)
`Vals_ok_non_bot`, `Ref_ok_non_bot`.

## Final Ltac automation library (1964-2222, end of file, no more Lemmas)
`construct_ais_typing`, `extract_premise`, `destruct_all`,
`invert_ais_single_val_typing`/`invert_ais_vals_typing`/
`invert_ais_single_ref_typing`, `invert_ais_typing`, `invert_instrtype_sub`,
`resolve_pt`/`resolve_all_pt`, hint db for take/drop/size rewriting,
`simplify_take_drop_size`, `simplify_resulttype_sub`,
`join_subtyping_trans`, `list_to_seq`, `construct_size_le`,
`join_subtyping_eq`/`_ge`/`_le` (compose two `<ti:` facts depending on
known size relationship — **central to almost every proof in
type_preservation_pure.v**), `resolve_subtyping` (final lines, 2214-2222).
File ends here, no further declarations.

---

# FILE 2: `test-rocq/theories/type_preservation_pure.v` (947 lines)

## Scope
Proves type preservation ONLY for `Step_pure` — WASM's deterministic,
store-independent "pure"/structural reduction rules: constant folding
(unop/binop/testop/relop/cvtop), control-flow bookkeeping (nop, drop,
select, if/then-else→block desugaring, label-value collapse, all br/br_if/
br_table forms, return crossing label/frame boundaries), local.tee
desugaring, ref.is_null. Explicitly EXCLUDES: store-mutating instructions
(loads/stores, table/memory/global mutation, call-dispatch — those are
`Step_read`/full reduction, in `type_preservation.v`), and SIMD (flagged
unhandled at file end, consistent with `ai_principal_typing`'s SIMD
catchall). **Two proof obligations are `Admitted`, not `Qed`** — see below.

## Header (1-14)
Imports `wasm helper_lemmas helper_tactics typing_lemmas subtyping`;
mathcomp ssreflect; Lia. `Opaque instrtype_sub.`

## `resolve_wfness` Ltac (23-38)
First automation step of nearly every lemma below — extracts
`wf_context`/`wf_store`/`wf_admininstr` from an `Instrs_ok2`/`Instr_ok2`
hypothesis via `ainstrs_ok_context_store_wf`/`ainstr_ok_context_store_wf`.

## `Step_pure__*_preserves` lemmas — ONE PER Step_pure CONSTRUCTOR (41-909)

Each has shape: `Instrs_ok2 v_S v_C <lhs> v_ft -> Step_pure <lhs> <rhs> ->
[extra side conditions] -> Instrs_ok2 v_S v_C <rhs> v_ft`. This IS a
one-lemma-per-reduction-rule file (unlike `typing_lemmas.v`'s
`ai_principal_typing` approach) — **28 named lemmas + 1 master theorem**,
in file order:

1. `Step_pure__nop_preserves` (41-53) — trivial.
2. `Step_pure__drop_preserves` (55-70) — easy.
3. `Step_pure__select_preserves_helper` (72-128, helper not itself a
   Step_pure case) — case-split on SELECT's type annotation
   (Some[]/Some[e]/Some multi-contra/None); uses `Val_ok_non_bot` +
   `valtype_sub_non_bot`. Medium-high (~55 lines).
4. `Step_pure__select_true_preserves` (130-138) — trivial from #3.
5. `Step_pure__select_false_preserves` (140-148) — trivial from #3.
6. `Step_pure__if_preserves_helper` (150-168) — medium.
7. `Step_pure__if_true_preserves` (170-178) — trivial from #6.
8. `Step_pure__if_false_preserves` (180-188) — trivial from #6.
9. `Step_pure__label_vals_preserves` (190-208) — medium, double
   `invert_ais_typing` + `join_subtyping_trans`.
10. `Step_pure__br_zero_preserves` (210-239) — medium-high (~30 lines).
    NOTE: statement takes only the typing hyp + length side-condition, NOT
    an explicit `Step_pure` premise (reduction fact not needed for proof).
11. `Step_pure__br_succ_preserves` (241-320) — **longest/most involved
    lemma in the file** (~80 lines): `lookup_label_1`,
    `Nat.succ_lt_mono`, manual index-decrement reconstruction via 2
    explicit `inv_Forall`/`inversion` blocks. High difficulty.
12. `Step_pure__br_if_true_preserves` (322-353) — medium.
13. `Step_pure__br_if_false_preserves` (355-381) — similar, ends via
    `ais_empty_typing`.
14. `proj_identity` (383-387) — small helper: `mk_list A (proj_list_0 A a)
    = a.`
15. `Step_pure__br_table_lt_preserves` (389-456) — one of the longest
    (~70 lines): `Forall_nth`, `nth_is_same_as_seq_nth`, manual
    `instrtype_sub_trans` chaining. High difficulty.
16. `Step_pure__br_table_ge_preserves` (458-499) — dual/default-target
    case, similar technique, ~40 lines.
17. `Step_pure__frame_vals_preserves` (501-515) — easy-medium, uses
    `construct_ais_vals'` (context-irrelevance) to cross frame boundary.
18. `Step_pure__return_frame_preserves` (517-575) — **`Admitted` — NOT
    proved.** Tactic script entirely commented out (~542-574). **Genuine
    gap in the Rocq source.** Port as `sorry` in Lean, don't silently
    invent a proof.
19. `Step_pure__return_label_preserves` (577-617) — fully proved, medium
    (~40 lines). RETURN propagates outward through enclosing label
    unchanged.
20. `Step_pure__unop_val_preserves` (619-644) — medium. NOTE: takes
    `wf_admininstr` of the *result* constant as an extra hypothesis (not
    derived — presumably from a companion "reduction preserves
    wellformedness" lemma elsewhere, i.e. a `Step_pure_is_wf`-style fact;
    check `wasm2.0.lean` for a `Step_pure_is_wf`-equivalent theorem).
21. `Step_pure__binop_val_preserves` (646-678) — medium, same pattern.
22. `Step_pure__testop_preserves` (680-706) — medium.
23. `Step_pure__relop_preserves` (708-740) — medium.
24. `Step_pure__cvtop_val_preserves` (742-768) — medium.
25. `Step_pure__local_tee_preserves` (770-814) — medium-high:
    `Val_ok_non_bot`+`valtype_sub_non_bot` forces LOCAL_TEE's annotated
    type to equal the value's type.
26. `Step_pure__ref_is_null_helper` (816-846, helper) — generic over
    boolean result (works for 0 or 1). Medium.
27. `Step_pure__ref_is_null_true_preserves` (848-855) — specializes #26
    with `v_n := 1`, trivial.
28. `Step_pure__ref_is_null_false_preserves` (857-909) — medium-high
    (~50 lines): case-splits on 3 `wasm.ref` constructors (REF_NULL
    delegates to #26; REF_FUNC_ADDR/REF_HOST_ADDR each get own ~15-line
    hand proof).

## Master theorem (911-948, end of file)
```coq
Theorem t_pure_preservation: forall v_s v_ais v_ais' v_C tf,
  Instrs_ok2 v_s v_C v_ais tf -> Step_pure v_ais v_ais' ->
  Instrs_ok2 v_s v_C v_ais' tf.
```
Proof: `resolve_wfness`; obtains wellformedness of the reduct via an
external `Step_pure_is_wf` lemma (imported, presumably from
`helper_lemmas.v` or similar — **check for a `Step_pure_is_wf`-equivalent
`*_is_wf` theorem in `wasm2.0.lean`**); `inversion HReduce` case-splits on
all `Step_pure` constructors; each branch either auto-discharged via `try
by eapply construct_ais_trap` (reduction rules whose target is TRAP under
some side condition) or dispatched to the matching named lemma above (in
file order, all 26 non-Admitted lemmas from the list, e.g. `nop`, `drop`,
`select_true/false`, `if_true/false`, `label_vals`, `br_zero`, `br_succ`,
`br_if_true/false`, `br_table_lt/ge`, `frame_vals`, `return_frame`
(admitted — inherits gap), `return_label`, `unop/binop/testop/relop/
cvtop_val`, `ref_is_null_true/false`, `local_tee` (explicitly numbered
"24:" due to Coq's automatic goal reordering from `inversion`)), followed
by:
```coq
(* The rest are all simd instructions *)
Admitted.
```
**So `t_pure_preservation` itself is `Admitted`, not `Qed`** — ALL SIMD
`Step_pure` cases unproved (consistent with zero SIMD coverage in
`ai_principal_typing`). **Exactly two open proof obligations in this
file**: (a) SIMD cases of the master theorem, (b)
`Step_pure__return_frame_preserves`. Both should become Lean `sorry`,
mirroring the Rocq gaps — consistent with the user's stated policy and
with `type_preservation.v`'s own SIMD-only gap pattern (see
`digest_type_preservation.md`).

---

## Summary / key points for the translation effort

1. **`typing_lemmas.v`'s central artifact is the single big
   `ai_principal_typing` Definition (427-673) plus its two soundness
   theorems** — NOT decomposed into per-constructor Lemmas in the source.
   Port as one large match/Prop plus two theorems (`instr_typing_inversion`,
   `ai_typing_inversion`), not 50 separate lemmas, to stay faithful.
2. **`type_preservation_pure.v` has 28 named `Step_pure__*` lemmas + 1
   master theorem**, covering exactly the store-independent/pure reduction
   rules; excludes memory/table/global/call-dispatch (→ `type_preservation.v`)
   and SIMD.
3. **Two genuine gaps to mirror as `sorry`**:
   `Step_pure__return_frame_preserves` (proof body entirely
   commented-out/never attempted) and `t_pure_preservation`'s SIMD cases.
4. **Heavy shared Ltac automation** (`construct_ais_typing`,
   `invert_ais_typing`, `typing_inversion`, `join_subtyping_*`,
   `resolve_subtyping`, `resolve_wfness`, `extract_premise`, ...) — in
   Lean this needs either tactic-macro equivalents or manual expansion per
   lemma; a large fraction of "proof work" here is case-shape-dependent
   dispatch, not bespoke reasoning per lemma, so Lean's `simp`/`omega`/
   custom `simp` sets may cover a lot of this ground more directly.
5. **Cross-reference**: `digest_prior_lean_attempts.md` §3 documents that
   the OLD `typing_lemmas.lean`'s `instrs_seq_typing_inversion` was
   mis-stated with singular `Instr_ok` on the head (proven FALSE) —
   **this digest confirms the correct Rocq-faithful statement** uses
   sequence-level `Instrs_ok`/`Instrs_ok2` on both sides (see
   `instrs_seq_typing_inversion` line 1056 and `ais_seq_typing_inversion`
   line 1121 above) — this matches `SeqTypingInversion.lean`'s already-
   proved `instrs_seq_typing_inversion_fixed`. Use these exact Rocq
   statements when porting.
6. There's a file `spectec/test-rocq/upd_label_unchanged_typing_verified_walkthrough.md`
   (outside `theories/`, at the `test-rocq/` root) that appears to be a
   detailed walkthrough specifically of `upd_label_unchanged_typing`
   (line 158-172 above) — worth reading directly when porting that lemma.
7. All lemma names/statements/line numbers above are copied verbatim from
   source for direct 1:1 mapping.
