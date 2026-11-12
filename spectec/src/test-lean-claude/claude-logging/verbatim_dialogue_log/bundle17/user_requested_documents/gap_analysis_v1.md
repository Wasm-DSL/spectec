# Lean ↔ Rocq gap analysis v1 (bundle17)

Written for: the user and the next session that resumes porting. Compares every
declaration in the 6 Lean files against upstream `rocq-backend-proof-final`.

## 0. Upstream status

- GitHub was reachable this turn (`curl api.github.com/.../branches/rocq-backend-proof-final`
  returned 200). Tip is **`95c256c2c`** (2026-09-29, "Updated rocq output and proofs. No
  more admits on preservation!").
- That is exactly the commit merged locally at `8ac6699ac`. `git diff 95c256c2c HEAD --
  spectec/test-rocq/theories` and the working-tree diff are both empty, so the local
  `spectec/test-rocq/theories/` is byte-identical to upstream. Nothing upstream has moved
  since bundle13.

## 1. The user's correction is right

`Admitted` counts per commit (`git show <c>:<file> | grep -c Admitted`):

| commit | date | `type_preservation.v` | `type_preservation_pure.v` | `extension_lemmas.v` |
|---|---|---:|---:|---:|
| `5b03ae067` (session-1 checkout) | 07-01 | 3 | 2 | 0 |
| `a8b585cdb` | 09-22 | **0** | **0** | 1 |
| `58af2e2f9` … `ee6365844` | 09-24 … 09-29 | 0 | 0 | 1 |
| `95c256c2c` (current) | 09-29 | **0** | **0** | **0** |

There is no `admit` anywhere in either preservation file either. `t_pure_preservation`,
`store_extension_reduce`, `t_read_preservation`, `t_preservation_type` and
`Step_pure__return_frame_preserves` are all `Qed` upstream, and have been since
`a8b585cdb` (2026-09-22). `Step_pure__return_frame_preserves`'s proof body is no longer
commented out (`type_preservation_pure.v:490-547`), and the SIMD cases are all handled
(`t_pure_preservation` dispatches to 21 `Step_pure__v*_preserves` lemmas;
`store_extension_reduce`/`t_preservation_type` dispatch to `mem_store_extension`/
`Step__vstore_preserves`/`Step__vstore_lane_preserves`; `t_read_preservation` to
`Step_read__vload_preserves`/`_vload_lane_preserves`).

How the wrong claim survived: session 1 digested the old `5b03ae067` checkout, where all
five really were `Admitted`, and wrote "mirror the Rocq gap" into the Lean file headers
and doc comments. bundle3 correctly reported that both preservation files had gone to
zero `Admitted` ("SIMD Preservation is real, portable work", proposing a "Tier E2"), but
the Lean headers were never updated. bundle13's resync summary then asserted, without
re-checking, that "`store_extension_reduce` **remains `Admitted` overall**", and bundles
15-16 inherited that through the headers and the prioritization docs (v5, v6).

**Consequence**: the "5 deliberate gaps" and the project-wide decision to exclude SIMD
from scope are both void. Preservation in the current Rocq covers SIMD; the Lean port
must too.

## 2. `funcinst_same` (user's change): sound

```lean
theorem funcinst_same (f1 f2 : List funcinst) (hlen : f1.length = f2.length) :
    Forall₂ Extend_funcinst f1 f2 → f1 = f2
```

- **True**: `Extend_funcinst` has one constructor, `Extend_funcinst x x`, so it is
  pointwise equality; with equal lengths the zip covers every position.
- **Proof is complete and axiom-clean**: `#print axioms TLC.funcinst_same` →
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Checked via a scratch file
  outside the project; `lake build` clean.
- **Faithful**: the original Rocq lemma (`extension_lemmas.v:787` at `5b03ae067`) is
  `Forall2 Func_extension f1 f2 -> f1 = f2` with Rocq's *inductive* `Forall2`, which
  forces equal length. `hlen` restores exactly that, the same move as `Vals_ok`'s baked-in
  length.
- Moving it below `extend_funcinst_eq` was necessary (it uses that lemma).
- Two small notes, no action needed unless you want it: (a) the lemma no longer exists
  upstream (removed at `a8b585cdb`) and nothing in the Lean project uses it, so under your
  rule 1 it is a "mark for deletion" candidate, though you clearly chose to keep it;
  (b) its doc comment says the length is "trivial or already available at every use
  site", but there are no use sites.

## 3. Missing declarations: Rocq names with no Lean counterpart

Method: extract every `Lemma/Theorem/Definition/Fixpoint/Axiom/Instance` from the current
`.v` files with comments stripped, and look each name up in all 6 Lean files.
(`ais_composition_typing_single` is correctly absent: it is commented out upstream.)

### 3a. `type_preservation_pure.v` → `TypePreservationPure.lean`: 47 missing, **all to port**

The whole SIMD section (`type_preservation_pure.v:883-1524`):
`ais_single_plain_typing_inversion`, `vconst_result_typing`, `const_result_typing`,
`ais_vconst_typing_inversion`, `ais_const_typing_inversion`; 19 per-instruction
inversions `ais_{vvunop,vvbinop,vvternop,vvtestop,vunop,vbinop,vtestop,vrelop,vshiftop,
vbitmask,vswizzle,vshuffle,vsplat,vextract_lane,vreplace_lane,vextunop,vextbinop,vnarrow,
vcvtop}_typing_inversion`; `vec_preserves_1/2/3`; 21 `Step_pure__{vvunop,vvbinop,vvternop,
vvtestop,vunop,vbinop_val,vtestop,vrelop,vshiftop,vbitmask,vswizzle,vshuffle,vsplat,
vreplace_lane,vextunop,vextbinop,vnarrow,vcvtop,vextract_lane_num,vextract_lane_pack}
_preserves`.

These are mechanical: each inversion is "`ais_single_plain_typing_inversion` then invert
`Instr_ok`", each `Step_pure__v*` is one `vec_preserves_k` application. The Lean
`Instr_ok`/`Step_pure` vector constructors line up with Rocq's statements (checked
`wasm2.0.lean` `Instr_ok.vconst … vcvtop`, `Step_pure.vvunop … vcvtop`). Rocq's
`ai_principal_typing` still sends all vector instructions to `_ => True`, which is why
these go through `Instr_ok` directly; **`TypingLemmas.ai_principal_typing` needs no
change**.

### 3b. `type_preservation.v` → `TypePreservation.lean`: 24 missing, 23 to port

To port: `wf_context_app`, `wf_context_tab`, `wf_context_mem`, `wf_tableinsts_preserves`,
`wf_memoryinsts_preserves`, `list_update_func_preserves_prop`,
`list_update_func_forall_inv`, `Forall_list_update_func`, `wf_store_mem_update`,
`wf_store_mem_update'`, `mem_store_extension`, `ais_seq3_last_typing`,
`ais_vstore_mems_inversion`, `ais_vstore_lane_mems_inversion`,
`ais_vload_typing_inversion`, `ais_vload_lane_typing_inversion`,
`ais_vstore_typing_inversion`, `ais_vstore_lane_typing_inversion`,
`Step_read__vload_preserves`, `Step_read__vload_lane_preserves`,
`vec_store_preserves_2`, `Step__vstore_preserves`, `Step__vstore_lane_preserves`.

Not ported: `Qfloor_add_Z` (Rocq `Q`/`Z` arithmetic; the Lean model is `Nat`).

Two of these need the same treatment you gave `funcinst_same`, because they derive facts
from a `Forall2` premise: `wf_tableinsts_preserves`/`wf_memoryinsts_preserves`
(`Forall2 Tableinst_ok tbinsts tbts → Forall wf_tableinst tbinsts → Forall wf_tabletype
tbts`) are **false** for the zip-based `Forall₂` when `tbts` is longer. Plan: add
`(hlen : tbinsts.length = tbts.length)`. I will mark these as intended deviations
unless you object.

`mem_store_extension`/`wf_store_mem_update` are stated with Rocq's `list_slice_update`;
the Lean `with_mem` is not `list_slice_update` (see
`with_mem_slice_update_issue.md`). Their Lean signatures should be stated against
whatever `with_mem` becomes.

### 3c. `typing_lemmas.v` → `TypingLemmas.lean`: 11 missing, 8 to port

To port: `ai_typing_inversion'` (needed by `ais_single_plain_typing_inversion`),
`wf_admininstr_instr` (the `↔` version; Lean has only the `→` direction as
`wf_instr_admininstr`), `seq_mid_not_null`, `construct_instr_from_ai`,
`construct_instr_from_ai_single`, `construct_instrs_from_ais` (used by
`t_read_preservation`'s Block/Loop/Call_addr and `t_preservation_type`'s Context Label),
`revert_to_instr_from_ai`, `revert_to_instrs_from_ais`.

Intended deviation (Rocq coercion/notation plumbing, Lean has direct equivalents):
`fun_res_list__list` (= `proj_list_0`), `fun_list__res_list` (= `list.mk_list`),
`functype_from_lists` (= `mkFunctype`).

### 3d. `extension_lemmas.v` → `ExtensionLemmas.lean`: 28 missing, mostly superseded

All are proof plumbing for Rocq's own proofs; the Lean proofs of the lemmas that use them
already went another way (Templates A/B/C in bundles 15-16).

| Rocq | Lean status / proposal |
|---|---|
| `holds_upto_lookup`, `holds_upto_S`, `holds_upto_all`, `holds_upto_all_strong`, `holds_upto_all_strong'`, `holds_upto_lt`, `holds_upto_lt_refl`, `update_holds_upto_lt`, `update_holds_upto_le` | `holds_upto` exists in Lean (`List.range`-based); these are portable one-liners. `holds_upto_lt_refl`/`update_holds_upto_lt` are used by Rocq's `store_extension_reduce`/`mem_store_extension`, so **port** them (cheap). |
| `update_forall_lt`, `update_forall_le`, `update_forall_le_u32` | bool-vs-Prop `<?`/`<` bridges (ssreflect). Lean has only Prop. **No counterpart needed.** |
| `nth_iotaN`, `size_iotaN`, `iota_snocN` | mathcomp `iotaN`; Lean uses `List.range` (`List.getElem_range`, `List.length_range`). **No counterpart needed.** |
| `list_update_func_subst`, `list_update_func_unchanged` | superseded by `HelperLemmas.getElem!_modify_eq_or_ne` (Template A). Port as thin wrappers or skip. |
| `forall_preserved_bytes` | same content as `HelperLemmas.list_slice_update_forall` (bundle15). Duplicate under another name. |
| `invert_meminst` | superseded by `ExtensionLemmas.wf_meminst_parts`. |
| `repeat_forall`, `size_repeat` | `List.replicate` facts in Lean core. Port or skip. |
| `invert_opt_map_some`, `invert_opt_map_none` | `Option.map_some'`/`Option.map_none'`. Port or skip. |
| `pagediv`, `pagediv_ge_0`, `pagediv_ge_0_Z`, `Qfloor_add_Z`, `Zle_Nle` | Rocq `Q`/`Z` page arithmetic for `memory.grow`; the Lean model is `Nat` (`rat_to_nat`) and `construct_meminsts_grow` is already proved without them. **No counterpart needed.** |

### 3e. `helper_lemmas.v` → `HelperLemmas.lean`: 27 missing

| Rocq | Lean status / proposal |
|---|---|
| `prepend_local`, `prepend_return`, `append_local`, `append_label`, `append_return` | context-update `Definition`s. Rocq's `ai_principal_typing` FRAME_ case and `t_read_preservation`/`t_preservation_type` use `prepend_return`/`prepend_local`; Lean inlines `{c with …}`. **Port** (cheap, makes later ports read like Rocq). |
| `Forall_size` | `Forall R l → ∀ i < |l|, R l[i]`. True in Lean. **Port.** |
| `Forall2_seq_size`, `Forall2_size`, `Forall2_size2` | derive length/indexed facts from `Forall2`. **False as stated** for the zip-based `Forall₂` (same class as `Forall2_nth`, `funcinst_same`). Usable replacements already exist (`Forall2_nth_of_length`, `mem_zip_getElem!`). Proposal: port with an explicit length premise, `funcinst_same`-style, since `t_read_preservation`/`store_extension_reduce` use them ~20 times. |
| `_append_option_none`, `_append_option_none_left`, `_append_some_left` | **already ported** as `option_orElse_none`/`option_none_orElse`/`option_some_orElse` (renamed). |
| `add_subBN`, `add_subBN'` | `N` versions of `add_sub`/`add_sub'`, which Lean already has over `Nat`. Duplicate. |
| `split_cons`, `app_left_single_nil`, `app_right_nil`, `app_left_nil`, `app_cat` | list-shape rewrites for Rocq's `rewrite`-driven proofs (`app_cat`: stdlib vs mathcomp `++`). Trivial; port or skip. |
| `id_succ_N`, `cvt_succ`, `cvt_succ'`, `sizecat'`, `sizeN_inj`, `size_cons`, `nth_is_same_as_seq_nth`, `in_same_as_In` | `nat`↔`N` conversions and stdlib↔mathcomp bridging. **No counterpart needed** (one list library, one `Nat`). |

### 3f. `subtyping.v` → `Subtyping.lean`: 10 missing, none needed

`Resulttype_subtype` is ported as `ResulttypeSub` (renamed, documented in-file).
`cvt_N_to_ssrnat`, `cvt_ssrnat_to_N_le`, `size_length`, `all2_cat'`, `all2_cat`,
`size0nil'`: mathcomp/`N` bridging. `valuetype_sub_preorder`,
`resulttype_sub_preorder`, `instrtype_sub_preorder`: Rocq `Instance` registrations for
setoid rewriting; Lean does not use them. (They could be added as Lean `IsPreorder`
instances for completeness; nothing needs them.)

### 3g. `axioms.v` → `HelperLemmas.lean`: 12 missing, Progress-only

`ibits_inv`, `feq_bit`, `fne_bit`, `flt_bit`, `fgt_bit`, `fle_bit`, `fge_bit`, `ishl_wf`,
`ishr_wf`, `trunc_sat_total`, `demote_nonempty`, `promote_nonempty`: every use site is in
`type_progress.v` (bundle13 confirmed). Port with the Progress work, and carefully: a
mis-transcribed axiom is an inconsistency, not just a gap.

### 3h. Not ported at all: `type_progress.v` (6159 lines, Progress), `helper_tactics.v` (Ltac), `wasm1.v` (Wasm 1.0)

As before. Progress is the next project after preservation.

## 4. Signature problems in declarations that *do* exist

1. **`Step_pure__br_table_ge_preserves` has an extra premise.** Lean takes
   `v_l.length ≤ proj_uN_0 (Option.get! (proj_num__0 v_i)) →`; Rocq
   (`type_preservation_pure.v:432`) has no such premise. The bundle13 audit reported this
   file clean, so it missed this. Fix: drop the premise (it is unused by the proof, and
   `t_pure_preservation`'s dispatch would supply it anyway).
2. **Stale "`Admitted` in Rocq" doc comments** on `t_pure_preservation`,
   `Step_pure__return_frame_preserves` and the headers of `TypePreservationPure.lean` and
   `TypePreservation.lean` (plus `store_extension_reduce`, `t_read_preservation`,
   `t_preservation_type`, `step_moduleinst`). All false since `a8b585cdb`. Not edited this
   turn (stopped before any Lean edits).
3. Earlier findings still open (from bundle16's notes): `Extend_store_datainsts'` hard-codes
   `datatype.OK` where Rocq has `Forall2 … aa ts`; `construct_meminsts_grow` hard-codes the
   memory max as present; `table_grow_table_extension` takes `Option uN` where its memory
   sibling takes `Option Nat`.

## 5. Current `sorry`s, classified by your three rules

26 project-wide (was 27; `funcinst_same` is now proved).

- **Rule 1, mark for deletion** (unused, superseded, not upstream): the 15
  `HelperLemmas` declarations `list_update_func_split`, `list_update_func_split_strong`,
  `Forall2_nth`, `Forall2_lookup`, `lookup_list_update_func`, `Forall2_forall2`,
  `Forall2_forall2weak`…`weak4`, `Forall2_list_update_func`,
  `Forall2_list_update_func2`, `Forall2_list_update`, `Forall2_list_update2`,
  `Forall2_list_update_both` (several are false for the zip-based `Forall₂`; replaced by
  `Forall2_nth_of_length`, `mem_zip_modify*`, `getElem!_modify_eq_or_ne`), and
  `ExtensionLemmas.Val_ok_store` (unprovable as stated, removed upstream at
  `a8b585cdb`).
- **Rule 2, Rocq-`Admitted`, mark for later**: **none**. The 5 previously labelled so are
  `Qed` upstream.
- **Rule 3, attempt**: `Step_pure__br_zero_preserves`, `_br_succ_`, `_br_table_lt_`,
  `_br_table_ge_`, `_return_frame_`, `_return_label_`, `t_pure_preservation`,
  `t_read_preservation`, `t_preservation_type`, and `store_extension_reduce` **except its
  four store-val cases, which are false in the Lean model** (see
  `with_mem_slice_update_issue.md`).

## 6. Plan when resumed (signatures first)

1. `TypingLemmas.lean`: add the 8 lemmas of §3c (`sorry`), build.
2. `TypePreservationPure.lean`: fix `br_table_ge`'s signature; add the 47 of §3a
   (`sorry`), build.
3. `TypePreservation.lean`: add the 23 of §3b (`sorry`), the two `Forall₂` ones with
   `hlen`; build.
4. `HelperLemmas`/`ExtensionLemmas`: add `prepend_local`/`prepend_return`/`append_*`,
   `Forall_size`, the `Forall2_size*` family with length premises, and the
   `holds_upto_*` lemmas `store_extension_reduce` needs; build.
5. Fix the stale doc comments; mark the rule-1 `sorry`s for deletion.
6. Proofs, cheapest and most-depended-on first: §3c, the vector inversions and
   `vec_preserves_*`, the 21 `Step_pure__v*`, the 6 control-flow `Step_pure__*`,
   `t_pure_preservation` (uses the generated `Step_pure_is_wf`, `sorry` in
   `wasm2.0.lean`), then `t_read_preservation` (~1460 Rocq lines, ~30 cases),
   `t_preservation_type`, `store_extension_reduce` (pending your decision on §with_mem).
