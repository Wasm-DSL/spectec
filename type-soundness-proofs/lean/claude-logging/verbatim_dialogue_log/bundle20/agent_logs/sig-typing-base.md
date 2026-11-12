# sig-typing-base — signature audit (v2 relaunch): TypingLemmas.lean, Subtyping.lean, HelperLemmas.lean vs typing_lemmas.v, subtyping.v, helper_lemmas.v, axioms.v

(bundle20 preservation audit, subagent label `sig-typing-base`; written incrementally)

## Task

Subagent "sig-typing-base" (v2 relaunch, merging first-wave tasks `sig-typing` and `sig-base`).
Using the pre-extracted side-by-side files `scratchpad/sigs/sbs_typing.md` and
`scratchpad/sigs/sbs_base.md` as primary input, judge for every Rocq/Lean declaration pair
whether the statements are equivalent and documented; for Rocq declarations with no Lean
counterpart (NONE/NOTPORTED), decide whether the absence is justified and documented
(gap_analysis_v1.md §3c/§3e/§3f/§3g); check that Lean-only helpers are labelled and
plausible; compare each of the 11 Lean `axiom`s in HelperLemmas.lean with its Rocq `Axiom`
in axioms.v (remembering Rocq's `|x| = q`, `q : Q`, means a FLOOR). Read-only; Lean not run.
Only this log file is written inside the repo; scratch goes to
`scratchpad/agents/sig-typing-base/`.

## First-wave partial logs

`agent_logs/sig-typing.md` and `agent_logs/sig-base.md` were read first: both contain only the
task paragraph and the START safety check (no findings), so this run starts from scratch.

## Safety check — START (verbatim)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" sig-typing-base
safety check [sig-typing-base] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T110438.150722636Z-sig-typing-base-1409669.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress notes (incremental)

- Read brief v2 and task file.
- Read first-wave partial logs (empty of findings).
- Read `scratchpad/sigs/sbs_typing.md` (1818 lines, all) and `scratchpad/sigs/sbs_base.md` (2329 lines, all).
- Read gap_analysis_v1.md §3 intro, §3c, §3e-§3g, §4 (lines 72-77, 124-136, 154-203).
- Targeted source reads (line ranges):
  - `wasm2.0.lean`: 1-30 (`Forall₂` zip def, `splice`, `rat_to_nat`), 798-812 (`size`, concrete def),
    1839-1855 (`loadop_`, `loadop_Inn` single constructors), 992-995 (`sz`), 47 (`abbrev M := Nat`),
    2652/2861/4175/4203/4217/4260/4288/4302/4644 (`truncz`, `wrap__`, `ibytes_`, `nbytes_`, `vbytes_`,
    `inv_*bytes_`, `lanes_` are all `opaque`), 12636-12653 (`append_context`, `Append context`),
    12729-12739 (`Valtype_sub`, `Resulttype_sub` with explicit length premise).
  - `TypingLemmas.lean`: 24-37 (header), 53-58, 311-466 (`ai_principal_typing`, `instr_principal_typing`),
    110-192 (`instr_of`, counted), 207-222, 1753-1778 (`value_extra`, `Vals_ok`), 1886-1892 (`inst_match`).
  - `Subtyping.lean`: 18-23 (header), 44-55 (`instrtype_sub`).
  - `HelperLemmas.lean`: 20-25 (header), 60-76 (Template B header), 159-200 (`list_slice_update`, `In2`,
    deletion markers), 569-600 (`prepend_*`, `append_*`), 668-760 (axiom block).
  - Rocq `axioms.v` 1-100 (whole file); `wasm.v` 13 (`the`), 31-74 (`list_update`, `list_update_func`,
    `list_slice_update`), 185-200 (coercions `Z.to_N`, `Z.of_N`, `inject_Z`, `Qfloor`), 300-310
    (`Notation "| x |" := (N.of_nat (seq.size x))`, `!( x )` = `the x`), 342/345 (`res_N`, `M` = N),
    866-872 (`numtype` constructors I32..F64), 1391-1399 (`res_size : option N`);
    `typing_lemmas.v` 20-25, 124-196 (`instr_of`), 226-233, 377-627 (`ai_principal_typing`, comments
    stripped, plus the commented-out vector/STORE arms 454-472, 562-572); `subtyping.v` 8-13.

## Method

1. Every pair in the two side-by-side files was compared for binders, premises and conclusion,
   translating Rocq notation (`:->` = `mkFunctype`, `<ts:` = `ResulttypeSub`, `<ti:` =
   `instrtype_sub`, `<tv:` = `Valtype_sub`, `l [|i|]` = `lookup_total`, `|x|` = `N.of_nat (size x)`,
   `(... < ...)%BN` = Nat `<`).
2. For definitions, the bodies (which the extractor truncates at `:=`) were compared directly in the
   sources: `ai_principal_typing` case by case (all ~60 arms), `instr_of` (constructor count + round-trip
   theorem), `instrtype_sub`, `Vals_ok`, `value_extra`, `inst_match`, `upd_*`, `prepend_*`/`append_*`,
   `In2`, `list_slice_update` (clause by clause vs `wasm.v:66-74`), `list_update(_func)`.
3. Absences (NONE/NOTPORTED) were checked against gap_analysis_v1 §3c/§3e/§3f/§3g and against in-file
   "NOT PORTED" notes (grep).
4. Every Lean axiom was compared with the Rocq `Axiom`, taking Rocq's `|x| = q` (`q : Q`) as
   `N.of_nat (size x) = Z.to_N (Qfloor q)` (coercions at wasm.v:194-200, notation at wasm.v:309), and
   checking that each function the axiom constrains is `opaque` in `wasm2.0.lean` and that `size` is
   concrete (multiples of 8 for numtypes/V128). Uses of every axiom were grepped (all hits are doc text).
5. Trust constructs: `grep sorry|native_decide|implemented_by|unsafe|admit|axiom` over the three files.
6. Citations: a script extracted the first `` `file.v:N` `name` `` citation of every documented decl in the
   three files (176 decls) and checked the name against the Lean decl name and against live Rocq
   declarations (comments stripped). Lean-only helpers' labels were checked.

## Findings

### F1 (minor, new) — `ibytes_inv` axiom is not equivalent to Rocq (Lean strictly weaker)
- Rocq `axioms.v:53-55`: `(|bs|) = (((v_N : Q) / (8%num : Q))%Q : N) -> ibytes_ v_N (inv_ibytes_ v_N bs) = bs`,
  i.e. premise `|bs| = Z.to_N (Qfloor (v_N/8))` = floor(v_N/8).
- Lean `HelperLemmas.lean:753`: `axiom ibytes_inv (v_N : N) (bs : List byte) (hlen : (bs.length : Rat) = (v_N : Rat) / 8)`.
- Exact-Rat premise is unsatisfiable unless 8 | v_N, so Lean's axiom is vacuous for other widths and
  implied by Rocq's (safe direction, no consistency risk). Undocumented. Unused (only doc mentions).
- The other 8 axioms checked are equivalent: `nbytes_len`, `ibytes_len` (both Nat floor `/ 8`, same as
  `(Nat.divmod n 7 0 7).1`), `nbytes_len'`, `vbytes_len'`, `nbytes_inv`, `vbytes_inv` (exact vs floor
  coincide because `size` is concrete: 32/64/128, wasm2.0.lean:798-805), `truncz_quot` (`Z.quot` =
  `Int.tdiv`; `truncz` opaque), `lanes_len`. (`ibytes_len'`/`ibytes_len''` = known inconsistency.)
- Recommendation: state the premise as Rocq does, `bs.length = v_N / 8` (Nat floor), together with the
  planned floor fix of `ibytes_len'`/`ibytes_len''`; optionally restate the primed `nbytes`/`vbytes`
  axioms with Nat floor too for literal correspondence.

### F2 (minor, new) — axiom-block doc comments misdescribe Rocq and the generated file
- `HelperLemmas.lean:674-681` header: "brought `axioms.v` up from 2 to 9 axioms … the 7 new ones" — Lean
  has 11 axioms; Rocq `axioms.v` now has 23 (the 12 Progress-only ones are not mentioned anywhere in the file).
- `HelperLemmas.lean:683-684` (`nbytes_len`): "`nbytes_` and `size` (Rocq: `res_size`) already exist as
  backend `opaque`s in `wasm2.0.lean` (lines ~705, ~3967)" — `size` is a concrete `def` (wasm2.0.lean:798).
- `HelperLemmas.lean:701-704` (`nbytes_len'`): "A `Rat`-valued restatement of `nbytes_len` without the
  Nat-division floor"; `:709-710` (`ibytes_len'`): "`Rat`-valued restatement of `ibytes_len`". Rocq's
  primed axioms are NOT floor-free: `|x| = q` coerces `q` through `Qfloor`/`Z.to_N`. This misreading is
  the common root cause of the known `ibytes_len'`/`ibytes_len''` inconsistency and of F1.
- Recommendation: correct the three doc comments when the axioms are fixed.

### F3 (minor, new) — `ai_principal_typing` LOAD/STORE packed arms differ from Rocq (Lean strictly stronger)
- All ~60 arms were compared; all are equivalent except the packed memory arms:
  - LOAD: Rocq has arms only for `LOAD I32 (Some (mk_loadop__0 Inn_I32 …))`, `LOAD I64 (Some (mk_loadop__0 Inn_I64 …))`
    and `LOAD F32/F64 (Some _) _ => False` (`typing_lemmas.v:544-555`); a mismatched
    `LOAD I32 (Some (mk_loadop__0 Inn_I64 …))` falls through to `| _ => True` (`:622`). Lean
    (`TypingLemmas.lean:412-416`) has one arm `nt = numtype_Inn inntype ∧ …` (and `loadop_`/`loadop_Inn`/`sz`
    are single-constructor, wasm2.0.lean:1839-1855, 992), so the mismatched case is `False`.
  - STORE: Rocq `| (admininstr_STORE v_Inn (Some (mk_sz v_M)) v_memarg) => exists v_mt, …` (`:564-568`;
    F32/F64 exclusion arms commented out at `:562-563`) gives F32/F64 packed stores a real principal type;
    Lean (`TypingLemmas.lean:421-424`) requires `nt = numtype_Inn inntype`, i.e. `False` for F32/F64.
- Both differences only strengthen Lean's definition in cases where `Instr_ok2` is uninhabited (Lean's
  `ai_typing_inversion` is proved sorry-free), so there is no effect on preservation. The STORE difference
  is documented in the doc comment (`TypingLemmas.lean:300-310`); the LOAD one is not, and the doc says the LOAD arms are
  "semantically equivalent to the live Rocq version", which is not exact.
- Recommendation: either mirror Rocq's arms literally, or amend the doc to say Lean is stronger in these
  uninhabited corners.

### F4 (minor, new) — `upd_*_is_same_as_append` (4 lemmas) do not state Rocq's content
- Rocq `typing_lemmas.v:61-96`: e.g. `upd_label v_C (lab @@ (LABELS v_C)) = {| …[]…; LABELS := lab; context_RETURN := None |} @@ v_C`
  (relates `upd_*` to the generic context append).
- Lean `TypingLemmas.lean:69-84`: e.g. `upd_label C (lab ++ C.LABELS) = { C with LABELS := lab ++ C.LABELS } := rfl` —
  the RHS is a record update, so the statement is a trivial restatement of `upd_label`'s definition and
  says nothing about `++` on contexts.
- Lean has `Append context` (wasm2.0.lean:12637-12651, fieldwise `++`, RETURN by left-biased `orElse`), and
  `HelperLemmas.lean` already writes `prepend_local`/`prepend_return`/`append_*` literally with
  `{…} ++ C`, so a faithful statement is expressible (it should also be closable by `rfl`/`simp`, given
  `[] ++ l ≡ l` and `none.orElse f ≡ f ()`). All 4 are unused in Lean. The doc (`TypingLemmas.lean:65-68`) also
  misdescribes Rocq's near-empty context as having `LABELS := lab ++ LABELS C` (Rocq has `LABELS := lab`).
- Related (no meaning change): `prepend_local`/`prepend_return`/`append_*` are ported but unused, and
  `ai_principal_typing`'s FRAME_ arm inlines `{ c' with RETURN := some … }` where Rocq writes
  `prepend_return v_C' t` (equal, because `orElse` is left-biased).
- Recommendation: restate the 4 lemmas with `({ … } : context) ++ C` on the RHS as Rocq does (or label
  them as Lean-only simplifications).

### F5 (minor, new) — most not-ported Rocq declarations are undocumented in the Lean files
- Justified by gap_analysis_v1, but with no in-file note:
  - subtyping.v: `cvt_N_to_ssrnat`, `cvt_ssrnat_to_N_le`, `size_length`, `all2_cat'`, `all2_cat`, `size0nil'`,
    `valuetype_sub_preorder`, `resulttype_sub_preorder`, `instrtype_sub_preorder` (§3f).
  - typing_lemmas.v: `fun_res_list__list`, `fun_list__res_list`, `functype_from_lists` (§3c).
  - helper_lemmas.v: `id_succ_N`, `cvt_succ`, `cvt_succ'`, `Forall2_seq_size`, `Forall2_size`, `Forall2_size2`,
    `split_cons`, `app_cat`, `add_subBN`, `add_subBN'`, `sizecat'`, `sizeN_inj` (§3e).
  - axioms.v: the 12 Progress-only axioms `ibits_inv`, `feq_bit`…`fge_bit`, `ishl_wf`, `ishr_wf`,
    `trunc_sat_total`, `demote_nonempty`, `promote_nonempty` (§3g).
- Only 6 helper_lemmas.v absences have in-file "NOT PORTED" notes: `nth_is_same_as_seq_nth`,
  `in_same_as_In`, `app_left_single_nil`, `app_right_nil`, `app_left_nil`, `size_cons` (plus `repeat_size`,
  which no longer exists in Rocq).
- `Forall2_seq_size`/`Forall2_size`/`Forall2_size2` are FALSE for the zip-based `Forall₂`. gap §3e proposed
  porting them with a length premise; instead the Lean-only `Forall2_nth_of_length` (`HelperLemmas.lean:271`,
  = `Forall2_size` + `hlen`) is used, and its doc points to the removed Rocq `Forall2_nth` rather than the
  current `Forall2_size`.
- Recommendation: add one-line NOT PORTED notes (copying gap §3c/§3e/§3f/§3g), and cite `Forall2_size`
  in `Forall2_nth_of_length`'s doc.

### F6 (minor, new) — stale file headers claim `sorry` stubs
- `TypingLemmas.lean:26-36`: "**MAJOR TODO** … `instr_of` and `ai_principal_typing` … bodies are `sorry` stubs" and
  "Phase 1 (this file, first pass): every signature stated, proofs/bodies `sorry`".
- `Subtyping.lean:22` and `HelperLemmas.lean:24`: "Phase 1 (this file, first pass): every signature stated, proofs `sorry`".
- All false: TypingLemmas/Subtyping contain no `sorry`; HelperLemmas has only the 15 marked-for-deletion ones.
  (The `ai_principal_typing` header comment also says "~57 cases"; the actual definition has ~60 arms and is complete.)
- Recommendation: delete or update these paragraphs.

### F7 (info, known-documented) — zip-based `Forall₂` deviations in these files are the documented ones
- `Vals_ok` (`TypingLemmas.lean:1775`, length baked in), and through it `Vals_ok_non_bot`,
  `ais_vals_typing_inversion`, `construct_ais_vals`: documented, equivalent in meaning to Rocq's inductive `Forall2`.
- `Forall2_app'`, `Forall2_take`, `Forall2_drop` (Subtyping.lean:196/222/231): Forall₂-level conclusions
  lack Rocq's implicit length equality, but are true and only used via `ResulttypeSub`.
- `ResulttypeSub` is faithful: generated `Resulttype_sub` carries `(List.length t_1_lst) = (List.length t_2_lst)`
  explicitly (wasm2.0.lean:12735-12739), so `resulttype_sub_size_eq` etc. match Rocq exactly.

### F8 (info, known-documented) — the 20 citations of lemmas no longer in Rocq are all in HelperLemmas.lean
- None of the 176 documented decls in the three files cites a different (wrong) Rocq declaration. The only
  name differences are the documented renames `_append_option_none`/`_append_option_none_left`/
  `_append_some_left` → `option_orElse_none`/`option_none_orElse`/`option_some_orElse` (semantics checked).
- 20 cite helper_lemmas.v names that no longer exist in Rocq, live or commented (verified by script): 14 are
  the marked-for-deletion `sorry` lemmas; 6 are live, proved Lean lemmas: `leadd` (:182), `length_app_lt`
  (:195), `Forall_nth'` (:235), `add_false` (:546), `concat_cancel_last_n` (:659), `ltsize` (:666).
- Recommendation: relabel those 6 as "Lean-only (Rocq lemma removed upstream)".

### Observation (not a finding, per brief §4.6)
Several of the 15 marked-for-deletion `sorry` lemmas in HelperLemmas.lean are FALSE for the zip-based
`Forall₂`: e.g. `Forall2_nth`/`Forall2_lookup` (:307/:315) conclude `l.length = l'.length` from `Forall₂`
alone (counterexample `l = [x]`, `l' = []`), and `Forall2_forall2weak` (:349) fails for the same lists with an
empty `R`. They are unused and not on the preservation path, so deleting them is correct; they must not be revived as stated.

### Trust constructs in the three files
- `TypingLemmas.lean`, `Subtyping.lean`: no `sorry`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `admit`
  (the hits for "sorry" are only in stale header/doc text, see F6).
- `HelperLemmas.lean`: 15 `sorry`, all preceded by `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED`
  (verified, 15/15); 11 `axiom`s (lines 691-757), none used by any proof (all hits are doc text);
  no `native_decide`/`implemented_by`/`unsafe`/`admit`.

### Lean-only helpers (labels checked, all plausible)
TypingLemmas: `instr_of_admininstr_instr` ("not in Rocq"), `wf_admininstr_ref`/`wf_instr_admininstr` ("Helper"),
`principal_typing_conversion` ("not independently named in the Rocq source"), the `_gen`/`_nil_*`/`_widen_*`
scaffolding (section doc "no direct named Rocq counterpart"), `construct_instrs_subtyping` ("Lean-only helper").
Subtyping: `mkFunctype`, `ValtypeSub`, `ResulttypeSub` (Rocq notations/defs), `forall2_valtype_sub_refl/trans`
("New plumbing (no direct Rocq counterpart)"). HelperLemmas: `lookup_total`, `list_update` (= `List.set`, matches
wasm.v:31-36), `list_update_func` (= `List.modify`, matches wasm.v:50-55), `list_slice_update` (matches wasm.v:66-74
clause by clause), Template A/B helpers (`getElem!_modify_eq_or_ne`, `mem_modify`, `mem_zip_modify(₂/_right)`,
`mem_zip_getElem!`), `Forall2_nth_of_length`, `list_slice_update_forall`, `splice_eq_list_slice_update`,
`splice_length`, `to/from_mathlib_forall₂`: all labelled "Not a Rocq port"/"Lean-only"/"New project-local".
Exception: the 6 live lemmas in F8 still claim a Rocq provenance that no longer exists.

## Coverage (one line per Rocq declaration; `=` equivalent, `=d` equivalent modulo documented deviation, NP = not ported)

```
typing_lemmas.v:12 fun_res_list__list: NP (coercion plumbing; =proj_list_0) gap§3c only, no in-file note [F5]
typing_lemmas.v:16 fun_list__res_list: NP (=list.mk_list) gap§3c only, no in-file note [F5]
typing_lemmas.v:20 functype_from_lists: NP (=mkFunctype) gap§3c only, no in-file note [F5]
typing_lemmas.v:26 upd_label: =
typing_lemmas.v:29 upd_local: =
typing_lemmas.v:32 upd_return: =
typing_lemmas.v:35 upd_local_return: =
typing_lemmas.v:38 upd_local_label_return: =
typing_lemmas.v:55 upd_label_overwrite: =
typing_lemmas.v:61 upd_label_is_same_as_append: DIFFERS: Lean RHS `{C with ..}` not context `++`; unused [F4]
typing_lemmas.v:68 upd_local_is_same_as_append: DIFFERS: as above [F4]
typing_lemmas.v:75 upd_local_return_is_same_as_append: DIFFERS: as above (@@ on option = orElse ok) [F4]
typing_lemmas.v:92 upd_return_is_same_as_append: DIFFERS: as above [F4]
typing_lemmas.v:100 upd_label_unchanged: =
typing_lemmas.v:108 upd_label_unchanged_typing: =
typing_lemmas.v:124 instr_of: = (68 Some cases each; 6 admin-only -> none = Rocq `_ => None`; round-trip thm proved)
typing_lemmas.v:197 instr_ok_context_wf: =
typing_lemmas.v:205 ainstr_ok_context_store_wf: =
typing_lemmas.v:213 instrs_ok_context_wf: =
typing_lemmas.v:221 ainstrs_ok_context_store_wf: =
typing_lemmas.v:299 instrs_empty_typing: =
typing_lemmas.v:333 ais_empty_typing: =
typing_lemmas.v:377 ai_principal_typing: body = case-by-case EXCEPT LOAD packed nt/Inn mismatch (Rocq True, Lean False) and STORE packed F32/F64 (doc'd); Lean stronger [F3]
typing_lemmas.v:626 instr_principal_typing: = (default_val ~ default)
typing_lemmas.v:629 instr_typing_inversion: =
typing_lemmas.v:672 ai_typing_inversion: = (stmt), inherits ai_principal_typing diffs [F3]
typing_lemmas.v:790 ai_typing_inversion': =
typing_lemmas.v:811 split_single_append: =
typing_lemmas.v:822 instrs_single_typing_inversion: =
typing_lemmas.v:884 ais_single_typing_inversion': =
typing_lemmas.v:946 ais_single_typing_inversion: = (stmt), inherits [F3]
typing_lemmas.v:961 ais_single_ref_typing_inversion: =
typing_lemmas.v:978 val_ref_null_is_ref: =
typing_lemmas.v:982 ais_single_val_typing_inversion: =
typing_lemmas.v:1015 instrs_seq_typing_inversion: =
typing_lemmas.v:1080 ais_seq_typing_inversion: =
typing_lemmas.v:1143 ais_composition_typing: =
typing_lemmas.v:1294 ai_val_principal_typing_inversion: =
typing_lemmas.v:1334 injective_admininstr_instr: =
typing_lemmas.v:1341 construct_instrs_typing_single: =
typing_lemmas.v:1350 construct_ais_typing_single: =
typing_lemmas.v:1359 construct_ais_subtyping: =
typing_lemmas.v:1382 injective_valtype_numtype: =
typing_lemmas.v:1401 construct_ais_compose: =
typing_lemmas.v:1412 wf_admininstr_instr: =
typing_lemmas.v:1428 seq_mid_not_null: =
typing_lemmas.v:1436 construct_instr_from_ai: =
typing_lemmas.v:1483 construct_instr_from_ai_single: =
typing_lemmas.v:1493 construct_instrs_from_ais: =
typing_lemmas.v:1513 revert_to_instr_from_ai: =
typing_lemmas.v:1559 revert_to_instrs_from_ais: =
typing_lemmas.v:1587 construct_ai_const_I32: =
typing_lemmas.v:1600 construct_ai_ref: =
typing_lemmas.v:1624 adminval_val_ref: =
typing_lemmas.v:1631 construct_ai_val: =
typing_lemmas.v:1657 construct_ai_maybe: = (the ~ Option.get!)
typing_lemmas.v:1674 construct_ais_vals': =
typing_lemmas.v:1712 construct_ais_trap: =
typing_lemmas.v:1731 value_extra: =
typing_lemmas.v:1738 Vals_ok: =d (length baked in; documented) [F7]
typing_lemmas.v:1741 Val_ok_non_bot: =
typing_lemmas.v:1753 ais_vals_typing_inversion: =d (Vals_ok) [F7]
typing_lemmas.v:1813 construct_ais_vals: =d (Vals_ok) [F7]
typing_lemmas.v:1949 resulttype_sub_single_inversion: =
typing_lemmas.v:1959 construct_ais_instrtype_sub: =
typing_lemmas.v:1975 inst_match: =
typing_lemmas.v:1984 construct_inst_match_label: =
typing_lemmas.v:1994 construct_inst_match_return: =
typing_lemmas.v:2004 construct_inst_match_local: =
typing_lemmas.v:2014 construct_inst_match_local_label_return: =
typing_lemmas.v:2024 construct_inst_match_local_return: =
typing_lemmas.v:2034 construct_inst_prepend_label: =
typing_lemmas.v:2069 Vals_ok_non_bot: =d (premise via Vals_ok; documented) [F7]
typing_lemmas.v:2094 Ref_ok_non_bot: =
subtyping.v:12 Resulttype_subtype: ported as ResulttypeSub (renamed, documented); faithful since generated Resulttype_sub has length premise
subtyping.v:15 cvt_N_to_ssrnat: NP N/ssrnat bridge; gap§3f only [F5]
subtyping.v:32 cvt_ssrnat_to_N_le: NP N/ssrnat bridge; gap§3f only [F5]
subtyping.v:47 instrtype_sub: = (body checked)
subtyping.v:61 size_length: NP bridge; gap§3f only [F5]
subtyping.v:65 valtype_sub_refl: =
subtyping.v:71 valtype_sub_trans: =
subtyping.v:81 valtype_sub_non_bot: =
subtyping.v:92 resulttype_sub_non_bot: =
subtyping.v:114 resulttype_sub_refl: =
subtyping.v:123 resulttype_sub_size_eq: =
subtyping.v:132 resulttype_sub_trans: =
subtyping.v:159 resulttype_sub_app_trans: =
subtyping.v:197 all2_cat': NP mathcomp all2; gap§3f only [F5]
subtyping.v:212 all2_cat: NP mathcomp all2; gap§3f only [F5]
subtyping.v:233 size0nil': NP N bridge; gap§3f only [F5]
subtyping.v:242 resulttype_sub_app: =
subtyping.v:285 Forall2_app': =d (zip Forall₂ conclusion, no length) [F7]
subtyping.v:306 resulttype_sub_app': =
subtyping.v:326 Forall2_take: =d (zip Forall₂) [F7]
subtyping.v:335 Forall2_drop: =d (zip Forall₂) [F7]
subtyping.v:344 resulttype_sub_split: =
subtyping.v:368 drop_size_cat: = (one Lean copy for subtyping.v+helper_lemmas.v duplicates)
subtyping.v:378 take_size_cat: = (one Lean copy for both Rocq duplicates)
subtyping.v:389 resulttype_sub_split_sup: =
subtyping.v:405 resulttype_sub_split_sup': =
subtyping.v:420 instrtype_sub_refl: =
subtyping.v:434 instrtype_sub_trans: =
subtyping.v:512 valuetype_sub_preorder: NP Instance; gap§3f only [F5]
subtyping.v:520 resulttype_sub_preorder: NP Instance; gap§3f only [F5]
subtyping.v:528 instrtype_sub_preorder: NP Instance; gap§3f only [F5]
subtyping.v:535 resulttype_sub_empty: =
subtyping.v:546 resulttype_empty_sub: =
subtyping.v:558 instrtype_sub_compose: =
subtyping.v:583 instrtype_sub_compose_le: =
subtyping.v:658 instrtype_sub_compose_ge: =
subtyping.v:721 instrtype_sub_compose_eq: =
subtyping.v:731 instrtype_sub_compose_le': =
subtyping.v:749 instrtype_sub_compose_ge': =
subtyping.v:768 instrtype_sub_compose1: =
subtyping.v:777 instrtype_sub_compose0: =
subtyping.v:786 instrtype_sub_compose2: =
subtyping.v:795 instrtype_sub_cancel_left: =
subtyping.v:809 instrtype_sub_empty: =
subtyping.v:821 instrtype_sub_sub_empty: =
subtyping.v:836 instrtype_sub_sub_empty1: =
subtyping.v:850 instrtype_sub_sub_empty2: =
subtyping.v:864 instrtype_sub_iff_resulttype_sub: =
subtyping.v:896 instrtype_sub_iff_resulttype_sub': =
subtyping.v:926 instrtype_sub_extend: =
subtyping.v:945 instrtype_sub_add_same: =
subtyping.v:956 resulttype_sub_cons: =
subtyping.v:970 instr_subtyping_strengthen2: =
subtyping.v:990 instr_subtyping_weaken2: =
helper_lemmas.v:17 id_succ_N: NP nat/N; gap§3e only [F5]
helper_lemmas.v:20 nth_is_same_as_seq_nth: NP, in-file note
helper_lemmas.v:40 length_same_split_zero: =
helper_lemmas.v:52 length_app_both_nil: =
helper_lemmas.v:68 length_app_nil: =
helper_lemmas.v:89 cvt_succ: NP nat/N; gap§3e only [F5]
helper_lemmas.v:93 cvt_succ': NP nat/N; gap§3e only [F5]
helper_lemmas.v:141 Forall_size: =
helper_lemmas.v:159 Forall2_seq_size: NP (false for zip Forall₂); replaced by Lean-only Forall2_nth_of_length(+hlen); gap§3e only [F5]
helper_lemmas.v:170 Forall2_size: NP as above; cited only by ExtensionLemmas.Store_ok_globalinst doc [F5]
helper_lemmas.v:186 Forall2_size2: NP as above [F5]
helper_lemmas.v:202 Forall2_list_update_func2: = (sorry; TODO-USER marked for deletion; statement true under zip)
helper_lemmas.v:229 in_same_as_In: NP, in-file note
helper_lemmas.v:270 In2: = (body checked)
helper_lemmas.v:278 In2_split: =
helper_lemmas.v:294 list_update_length: =
helper_lemmas.v:310 list_update_length_func: =
helper_lemmas.v:325 list_slice_update_length: =
helper_lemmas.v:335 split_append_last: =
helper_lemmas.v:344 split_cons: NP list-shape rewrite; gap§3e only [F5]
helper_lemmas.v:351 split_append_1: =
helper_lemmas.v:362 split_append_2: =
helper_lemmas.v:371 split_append_left_1: =
helper_lemmas.v:383 empty_append: =
helper_lemmas.v:394 lookup_app: =
helper_lemmas.v:413 app_left_single_nil: NP, in-file note
helper_lemmas.v:416 app_right_nil: NP, in-file note
helper_lemmas.v:419 app_left_nil: NP, in-file note
helper_lemmas.v:422 _append_option_none: = as option_orElse_none (renamed, cited)
helper_lemmas.v:430 _append_option_none_left: = as option_none_orElse (renamed, cited)
helper_lemmas.v:438 _append_some_left: = as option_some_orElse (renamed, cited)
helper_lemmas.v:471 app_cat: NP stdlib/mathcomp ++; gap§3e only [F5]
helper_lemmas.v:475 prepend_local: = (literal ++; unused)
helper_lemmas.v:482 prepend_label: = (direct cons; defeq to `{..LABELS:=[t]..} ++ C`; documented)
helper_lemmas.v:485 prepend_return: = (literal ++; unused)
helper_lemmas.v:488 append_local: = (literal ++; unused)
helper_lemmas.v:495 append_label: = (literal ++; unused)
helper_lemmas.v:502 append_return: = (literal ++; unused)
helper_lemmas.v:509 lookup_label_0: =
helper_lemmas.v:515 lookup_label_1: =
helper_lemmas.v:531 add_sub: =
helper_lemmas.v:539 add_sub': =
helper_lemmas.v:547 add_subBN: NP N dup of add_sub; gap§3e only [F5]
helper_lemmas.v:554 add_subBN': NP N dup; gap§3e only [F5]
helper_lemmas.v:562 sizecat': NP N size; gap§3e only [F5]
helper_lemmas.v:574 sizecat_le1: =
helper_lemmas.v:582 sizecat_le2: =
helper_lemmas.v:590 drop_size_cat: = (one Lean copy for subtyping.v+helper_lemmas.v duplicates)
helper_lemmas.v:600 take_size_cat: = (one Lean copy for both Rocq duplicates)
helper_lemmas.v:611 sizeN_inj: NP N size; gap§3e only [F5]
helper_lemmas.v:623 size_eq_cat: =
helper_lemmas.v:655 size_cons: NP, in-file note
axioms.v:13 nbytes_len: = (floor /8)
axioms.v:17 ibytes_len: = (floor /8)
axioms.v:21 nbytes_len': = (Lean exact Rat, Rocq floor; coincide: size∈{32,64}) [F2 doc]
axioms.v:24 ibytes_len': KNOWN inconsistent (exact vs floor) - already established
axioms.v:29 vbytes_len': = (Lean exact, Rocq floor; size V128=128)
axioms.v:32 ibytes_len'': KNOWN inconsistent - already established
axioms.v:38 truncz_quot: = (Z.quot ~ Int.tdiv; truncz opaque)
axioms.v:43 lanes_len: =
axioms.v:49 nbytes_inv: = (premise exact vs floor coincide for numtypes)
axioms.v:53 ibytes_inv: NOT EQUIVALENT: premise exact Rat vs Rocq floor -> Lean strictly weaker (vacuous unless 8|v_N); unused [F1]
axioms.v:57 vbytes_inv: = (coincide, 128)
axioms.v:64 ibits_inv: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:72 feq_bit: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:73 fne_bit: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:74 flt_bit: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:75 fgt_bit: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:76 fle_bit: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:77 fge_bit: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:83 ishl_wf: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:85 ishr_wf: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:95 trunc_sat_total: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:97 demote_nonempty: NP Progress-only axiom; gap§3g only, no in-file note [F5]
axioms.v:99 promote_nonempty: NP Progress-only axiom; gap§3g only, no in-file note [F5]
typing_lemmas.v Ltacs (30): do_instr_typing_inversion, do_instrs_typing_inversion, do_ai_typing_inversion, do_ais_typing_inversion, typing_inversion, unfold_instrtype_sub, unfold_principal_typing, valtype_discriminate_helper, vals_typing_inversion, resolve_inst_match, construct_ais_typing, extract_premise, destruct_all, invert_ais_single_val_typing, invert_ais_vals_typing, invert_ais_single_ref_typing, invert_ais_typing, invert_instrtype_sub, resolve_pt, resolve_all_pt, simplify_take_drop_size, simplify_resulttype_sub, join_subtyping_trans, list_to_seq, cvt_le, construct_size_le, join_subtyping_eq, join_subtyping_ge, join_subtyping_le, resolve_subtyping: not ported (Lean tactics instead; documented in TypingLemmas header for typing_lemmas.v)
helper_lemmas.v Ltacs (5): resolve_Nsucc, simplNsucc, simplNsuccH, simplNsizecons, simplNsizeconsgoal: not ported (Lean tactics instead; documented in TypingLemmas header for typing_lemmas.v)
```

## Safety check — END (verbatim)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" sig-typing-base
safety check [sig-typing-base] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T111723.831417771Z-sig-typing-base-1415848.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Uncertainties

- F4's claim that a literal `{…} ++ C` restatement would still close by `rfl` is reasoned (from `List.append`
  reducing on `[]`, `Option.orElse none f ≡ f ()`, and structure eta), not machine-checked (Lean not run, per brief).
- The equivalences for `nbytes_len'`/`vbytes_len'`/`nbytes_inv`/`vbytes_inv` rely on `size` being the concrete
  def at wasm2.0.lean:798 (32/64/128); if that def ever became `opaque`, these would become extra constraints
  (still consistent) rather than equivalences.
- Files written: only this log (inside the target dir) and scratch files under
  `scratchpad/agents/sig-typing-base/` (`rocq_apt.txt`, `cov.py`, `coverage.txt`, `coverage2.txt`).
