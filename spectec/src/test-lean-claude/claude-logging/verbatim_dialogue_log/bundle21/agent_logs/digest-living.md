# digest-living

Digest of: the bundle19 `wasm2.0_hand_edits.patch` (+ its README), the claude-logging "living" docs
(`README.md`, `for-claude/NOTES.md`, `for-claude/is_wf_theorems.md`, `for-humans/SUMMARY.md`) and the six static
`for-claude/digest_*.md` Rocq-file digests.

Sub-agent label: `digest-living`. Read-only with respect to the repository. My only writes: this log and scratch
files under `/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/work/digest-living/`.
No agents spawned. No lake/lean/build. Repository access was limited to `cat`/`sed`/`grep`/`wc`/`python3 -I` reads,
read-only `git show`/`git log`, and `patch -o <scratch file>` / `cp` on scratch copies.

Statements are marked: **[file:line]** = taken from the assigned file at that line; **[my check]** = something I
verified myself in scratch (not stated in the assigned files).

## Safety check at start (verbatim output of `verify.sh digest-living-start`)

```
safety check [digest-living-start] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T053102.433028388Z-digest-living-start-464036.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
2a4
> ?? spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/
```

## A. Coverage

Every assigned file was read completely (every line); nothing skimmed:

- `.../verbatim_dialogue_log/bundle19/user_requested_documents/README_wasm2.0_hand_edits.md` (58 lines)
- `.../verbatim_dialogue_log/bundle19/user_requested_documents/wasm2.0_hand_edits.patch` (2612 lines, 92 hunks; all lines read, plus parsed with `python3 -I`)
- `.../claude-logging/README.md` (17), `for-claude/NOTES.md` (1483), `for-claude/is_wf_theorems.md` (121),
  `for-claude/digest_prior_lean_attempts.md` (497), `digest_subtyping_and_extension_lemmas.md` (499),
  `digest_type_preservation.md` (279), `digest_type_progress.md` (160),
  `digest_typing_lemmas_and_type_preservation_pure.md` (391), `digest_wasm_v.md` (562), `for-humans/SUMMARY.md` (167)

## B. `wasm2.0_hand_edits.patch` (bundle19)

### B1. What it is

- Unified diff of ONE file, `a/spectec/src/test-lean-claude/wasm2.0.lean` -> `b/...` (patch L1-2), 92 hunks, no blob
  hashes (so `git apply --3way` cannot fall back to a 3-way merge) [README L37-38]. Apply from repo root with
  `patch -p1 < P` (dry-run first with `--dry-run`) or `git apply P`; `patch -p1 --merge` leaves conflict markers
  [README L31-43]. Net +1570 lines.
- Base = the user's generated file used in bundle19 (the one with the non-opaque `rat_to_nat`), md5
  `7d2167da7174a58377a7c6c43bd8cfc1` [README L9-11]. The only copy was in a session scratchpad
  (`scratchpad/wasm2.0.generated.lean`) [NOTES L94-95] -> not in the repo.
- Contents [README L13-25, NOTES L79-95]: (1) 89 proofs (each a `sorry` replaced, one per `*_is_wf` whose Rocq
  counterpart is `Qed`; the other 63 stay `sorry` = Rocq `Admitted`), (2) FIVE helper-lemma blocks (54 lemmas) each
  headed `/-! Hand-written helper lemmas for the *_is_wf proofs below (bundle19; not generated). -/`, (3)
  `Step_read_is_wf` and `Step_is_wf` moved to just after `inductive Store_ok` and re-signed with an extra
  `Store_ok (fun_store z)` premise (copying the hand edit in Rocq `wasm.v`), each with a `Hand-edited (bundle19)`
  comment; `Step_is_wf` proved, `Step_read_is_wf` left `sorry` ("blocking issue 2": false in the memory.fill/copy/init
  2^32 corner case).
- **[my check] The patch is an exact inverse of HEAD's hand edits.** `git show HEAD:.../wasm2.0.lean` (md5
  `cd0e676e2744e189bbd6f8beb7f0ad76`, 16351 lines, byte-identical to the untracked `OLD_wasm2.0.lean`) with the patch
  reverse-applied and then the user's commit `f07b4e1a8` ("readability scrap": +19 lines of `example`s after `fun_idiv_`
  at ~L3114) reverse-applied reproduces md5 `7d2167da7174a58377a7c6c43bd8cfc1` exactly. So HEAD `wasm2.0.lean` = bundle19
  base + this patch + the 19 scrap lines; bundle20 made no other edit to `wasm2.0.lean`.
- 89 = 88 in-place proofs (hunks with exactly one `-  sorry`) + `Step_is_wf` (removed in hunk 76, re-added proved in
  hunk 92). `Step_read_is_wf` is removed in hunk 75 and re-added (still `sorry`) in hunk 92.

### B2. The five helper blocks (+ the moved block)

1. Before `fzero_is_wf` (patch L7-96, 15 lemmas): `iswf_Forall_nil`, `iswf_Forall_cons`, `iswf_Forall_append`,
   `iswf_Forall_mono`, `iswf_Forall_getElem!` (needs `P default`), `iswf_Forall_modify` (List.modify),
   `iswf_Forall_splice`, `iswf_uN_zero`, `iswf_two_pow_cast`, `iswf_uN_of_lt`, `iswf_uN_lt`, `iswf_uN_proj_lt`,
   `iswf_toNat_sub_le`, `iswf_uN_toNat_emod`, `iswf_Forall_map`.
2. Before `iadd__is_wf` (L315-346, 4): `iswf_uN_bool`, `iswf_inv_signed`, `iswf_sat_u`, `iswf_list_OMap_num0`.
3. Before `vunop__is_wf` (L721-903, 16): `iswf_Forall_Map₂`, `iswf_setproduct2`, `iswf_setproduct1`, `iswf_setproduct`,
   `iswf_inv_lanes_Map`, `iswf_signed_func`, `iswf_inv_signed_func`, `iswf_iabs_func`, `iswf_imin_func`,
   `iswf_imax_func`, `iswf_iadd_sat_func`, `iswf_isub_sat_func`, `iswf_Forall₂_eq_of_func`, `iswf_Forall₃_eq_of_func`,
   `iswf_list_OMap_lane0`, `iswf_Forall₂_left_mem`.
4. Before `store_is_wf` (L1489-1513, 7): `iswf_val_default`, `iswf_funcinst_default`, `iswf_globalinst_default`,
   `iswf_tableinst_default`, `iswf_meminst_default`, `iswf_datainst_default`, `iswf_admininstr_val`.
5. Before `Step_pure_is_wf` (L1874-1949, 12): `iswf_admininstr_instr`, `iswf_admininstr_ref`, `iswf_mem_of_contains`,
   `iswf_Forall_list_OMap`, `iswf_binop`, `iswf_uN_of_succ`, `iswf_I32_const`, `iswf_val_of_admininstr`,
   `iswf_num_Inn_proj`, `iswf_rat_to_nat_floor`, `iswf_rat_to_nat_le`, `iswf_grow_pages`.
6. Moved block (patch L2464-2609): new `Step_read_is_wf` (L2464-2475, `sorry`) and `Step_is_wf` (L2477-2608, proved),
   inserted just before `/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:250.1-250.54 -/ inductive Extend_globalinst`.

### B3. Hunk table (all 92 hunks; theorem names resolved against the reconstructed base)

| hunk | patch line | theorem | +lines | notes / flags |
|---|---|---|---|---|
| 1 | L3 | fzero_is_wf | +93 | HELPER BLOCK (15 lemmas): iswf_Forall_nil, iswf_Forall_cons, iswf_Forall_append, iswf_Forall_mono, iswf_Forall_getElem!, iswf_Forall_modify, iswf_Forall_splice, iswf_uN_zero, iswf_two_pow_cast, iswf_uN_of_lt, iswf_uN_lt, iswf_uN_proj_lt, iswf_toNat_sub_le, iswf_uN_toNat_emod, iswf_Forall_map |
| 2 | L108 | zero_is_wf | +7 |  |
| 3 | L124 | dim_is_wf | +6 |  |
| 4 | L139 | concat_bytes_is_wf | +6 |  |
| 5 | L154 | tablesxt_is_wf | +10 |  |
| 6 | L173 | memsxt_is_wf | +10 |  |
| 7 | L192 | dataidx_instr_is_wf | +5 |  |
| 8 | L206 | dataidx_instrs_is_wf | +7 |  |
| 9 | L222 | dataidx_expr_is_wf | +4 |  |
| 10 | L235 | dataidx_func_is_wf | +5 |  |
| 11 | L249 | dataidx_funcs_is_wf | +7 |  |
| 12 | L265 | memarg0_is_wf | +3 |  |
| 13 | L277 | unop__is_wf | +25 |  |
| 14 | L311 | iadd__is_wf | +35 | HELPER BLOCK (4 lemmas): iswf_uN_bool, iswf_inv_signed, iswf_sat_u, iswf_list_OMap_num0 ; FLAG iadd_: iadd__is_wf proof = iswf_uN_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), relies on transparent def iadd_ = mk_uN ((a+b) % 2^N) |
| 15 | L360 | imul__is_wf | +3 |  |
| 16 | L372 | irem__is_wf | +8 |  |
| 17 | L389 | isub__is_wf | +3 |  |
| 18 | L401 | ieqz__is_wf | +3 |  |
| 19 | L413 | testop__is_wf | +6 |  |
| 20 | L428 | ieq__is_wf | +3 |  |
| 21 | L440 | ige__is_wf | +3 |  |
| 22 | L452 | igt__is_wf | +3 |  |
| 23 | L464 | ile__is_wf | +3 |  |
| 24 | L476 | ilt__is_wf | +3 |  |
| 25 | L488 | ine__is_wf | +3 |  |
| 26 | L500 | relop__is_wf | +12 |  |
| 27 | L521 | cvtop___is_wf | +12 | FLAG trunc_sat___is_wf (numeric TRUNC_SAT via iswf_list_OMap_num0; NOT vcvtop__) |
| 28 | L542 | inez__is_wf | +3 |  |
| 29 | L554 | ineg__is_wf | +3 |  |
| 30 | L566 | iabs__is_wf | +6 |  |
| 31 | L581 | imin__is_wf | +8 |  |
| 32 | L598 | imax__is_wf | +8 |  |
| 33 | L615 | iadd_sat__is_wf | +5 |  |
| 34 | L629 | isub_sat__is_wf | +5 |  |
| 35 | L643 | packnum__is_wf | +7 |  |
| 36 | L659 | unpacknum__is_wf | +7 |  |
| 37 | L675 | vvunop__is_wf | +4 |  |
| 38 | L688 | vvbinop__is_wf | +7 |  |
| 39 | L704 | vvternop__is_wf | +4 |  |
| 40 | L717 | (helper block 3, before vunop__is_wf) | +183 | HELPER BLOCK (16 lemmas): iswf_Forall_Map₂, iswf_setproduct2, iswf_setproduct1, iswf_setproduct, iswf_inv_lanes_Map, iswf_signed_func, iswf_inv_signed_func, iswf_iabs_func, iswf_imin_func, iswf_imax_func, iswf_iadd_sat_func, iswf_isub_sat_func, iswf_Forall₂_eq_of_func, iswf_Forall₃_eq_of_func, iswf_list_OMap_lane0, iswf_Forall₂_left_mem ; helper block 3 (16 lemmas); iswf_list_OMap_lane0 uses lane_.mk_lane__0 J and lsize (lanetype_Jnn J) |
| 41 | L907 | vunop__is_wf | +79 |  |
| 42 | L995 | vbinop__is_wf | +157 |  |
| 43 | L1161 | vrelop__is_wf | +77 |  |
| 44 | L1247 | lcvtop___is_wf | +10 | FLAG lcvtop/trunc_sat: cases h <;> ... subst_vars <;> cases hl <;> first | ... iswf_list_OMap_lane0 ... (trunc_sat___is_wf ..) |
| 45 | L1266 | vcvtop___is_wf | +55 | FLAG vcvtop: explicit fun_vcvtop___case_0..3 patterns; hcands over wf_vcvtop__ / fun_lcvtop__ |
| 46 | L1330 | vextunop___is_wf | +37 |  |
| 47 | L1376 | vextbinop___is_wf | +69 |  |
| 48 | L1454 | vshiftop__is_wf | +5 | FLAG ishl_/ishr_/vshiftop: ishl__is_wf _ _ _ _ (by assumption) hu rfl with hu : wf_uN 32 v_u32  (MUST CHANGE) |
| 49 | L1468 | default__is_wf | +8 |  |
| 50 | L1485 | store_is_wf | +29 | HELPER BLOCK (7 lemmas): iswf_val_default, iswf_funcinst_default, iswf_globalinst_default, iswf_tableinst_default, iswf_meminst_default, iswf_datainst_default, iswf_admininstr_val |
| 51 | L1527 | frame_is_wf | +3 |  |
| 52 | L1539 | funcinst_is_wf | +3 |  |
| 53 | L1551 | globalinst_is_wf | +3 |  |
| 54 | L1563 | tableinst_is_wf | +3 |  |
| 55 | L1575 | meminst_is_wf | +3 |  |
| 56 | L1587 | datainst_is_wf | +3 |  |
| 57 | L1599 | moduleinst_is_wf | +3 |  |
| 58 | L1611 | func_is_wf | +6 |  |
| 59 | L1626 | global_is_wf | +6 |  |
| 60 | L1641 | table_is_wf | +6 |  |
| 61 | L1656 | mem_is_wf | +6 |  |
| 62 | L1671 | data_is_wf | +6 |  |
| 63 | L1686 | local_is_wf | +6 |  |
| 64 | L1701 | with_local_is_wf | +8 |  |
| 65 | L1718 | with_global_is_wf | +9 |  |
| 66 | L1736 | with_table_is_wf | +9 |  |
| 67 | L1754 | with_tableinst_is_wf | +8 |  |
| 68 | L1771 | with_mem_is_wf | +10 |  |
| 69 | L1790 | with_meminst_is_wf | +8 |  |
| 70 | L1807 | with_elem_is_wf | +7 |  |
| 71 | L1823 | with_data_is_wf | +8 |  |
| 72 | L1840 | growtable_is_wf | +6 |  |
| 73 | L1855 | growmemory_is_wf | +6 |  |
| 74 | L1870 | Step_pure_is_wf | +307 | HELPER BLOCK (12 lemmas): iswf_admininstr_instr, iswf_admininstr_ref, iswf_mem_of_contains, iswf_Forall_list_OMap, iswf_binop, iswf_uN_of_succ, iswf_I32_const, iswf_val_of_admininstr, iswf_num_Inn_proj, iswf_rat_to_nat_floor, iswf_rat_to_nat_le, iswf_grow_pages ; FLAG: vshiftop case L2112-2122, vcvtop case L2175-2180, vnarrow binder Jnn_2 L2171 (unrelated to vcvtop__) |
| 75 | L2190 | Step_read_is_wf (OLD, removed) | +0 | FLAG Step_read: removes old Step_read_is_wf; patch fuzz 1 vs regenerated file (context line = old memory.init rule) |
| 76 | L2204 | Step_is_wf (OLD, removed) | +0 | removes old Step_is_wf (re-added in hunk 92) |
| 77 | L2218 | allocfunc_is_wf | +8 |  |
| 78 | L2235 | allocfuncs_is_wf | +7 |  |
| 79 | L2251 | allocglobal_is_wf | +8 |  |
| 80 | L2268 | allocglobals_is_wf | +7 |  |
| 81 | L2284 | alloctable_is_wf | +8 |  |
| 82 | L2301 | alloctables_is_wf | +7 |  |
| 83 | L2317 | allocmem_is_wf | +8 |  |
| 84 | L2334 | allocmems_is_wf | +7 |  |
| 85 | L2350 | allocelem_is_wf | +8 |  |
| 86 | L2367 | allocelems_is_wf | +7 |  |
| 87 | L2383 | allocdata_is_wf | +8 |  |
| 88 | L2400 | allocdatas_is_wf | +7 |  |
| 89 | L2416 | instexport_is_wf | +5 |  |
| 90 | L2430 | allocmodule_is_wf | +5 |  |
| 91 | L2444 | invoke_is_wf | +7 |  |
| 92 | L2460 | Step_read_is_wf (NEW) + Step_is_wf (NEW) | +146 | FLAG Step_read/MEMORY_*: NEW Step_read_is_wf (sorry) + Step_is_wf (proved) after Store_ok; comment L2468 names memory.fill/copy/init |

### B4. Proofs that mention the upstream-sensitive names (exact patch lines)

- `ishl_` / `ishr_`: only via `ishl__is_wf` / `ishr__is_wf` inside `vshiftop__is_wf` (hunk 48, patch L1454-1465):
  `exact wf_lane_.lane__case_0 _ _ _ (ishl__is_wf _ _ _ _ (by assumption) hu rfl) rfl` (L1463) and
  `... (ishr__is_wf _ _ _ _ _ (by assumption) hu rfl) rfl` (L1464), with `hu : wf_uN 32 v_u32` (hypothesis L1455).
  The whole proof is `intro h _ _ hl hu hne heq; subst heq; cases h <;> (try exact absurd rfl hne) <;> subst_vars <;> cases hl <;> first | ... | ...`.
- `vshiftop`: that proof, plus `Step_pure_is_wf`'s `vshiftop` case (L2112-2122): ctor pattern
  `vshiftop c_1 v_n v_Jnn v_N vshiftop c c'_lst var_0_lst h0 h1 h2 h3 h4 h5 h6 h7 h8` (9 hyps), then
  `iswf_Forall₂_left_mem _ _ h1 h0 e he` and `vshiftop__is_wf _ _ _ _ _ _ hr hish hvop (h5 c' hc') h8 (h3 e he) rfl`
  (`h8` = the `wf_uN 32` fact for `v_n`), finally `inv_lanes__is_wf _ _ _ h6 hl h4`.
- `vcvtop` / `lcvtop`: `lcvtop___is_wf` (hunk 44, L1247-1263: `cases h <;> ... <;> subst_vars <;> cases hl <;> first | extend___is_wf | convert___is_wf |
  iswf_list_OMap_lane0 _ _ _ rfl (trunc_sat___is_wf ...) | demote___is_wf | promote___is_wf`); `vcvtop___is_wf` (hunk 45, L1266-1327: `hcands` over `wf_vcvtop__`/`fun_lcvtop__`, then
  `cases h with | fun_vcvtop___case_0 Lnn_1 v_M Lnn_2 vcvtop ... h14 | fun_vcvtop___case_1 ... h11 | fun_vcvtop___case_2 ... h12 | fun_vcvtop___case_3 _ _ _ _ _ => exact absurd rfl hne`);
  helper `iswf_list_OMap_lane0 (J : Jnn) (lt : lanetype) (o : Option iN) (hlt : lt = lanetype_Jnn J)` (L882-887); `Step_pure_is_wf` `vcvtop` case (L2175-2180:
  `vcvtop___is_wf _ _ _ _ _ _ h0 hs1 hs2 hvop hw1 h1 h2`). The numeric `cvtop___is_wf` (hunk 27, L521-539) uses numeric `trunc_sat___is_wf` via `iswf_list_OMap_num0` (L338-345) - NOT the vcvtop__ type.
- `Jnn_2`: only L2171 (`Step_pure.vnarrow` binder names `Jnn_2 N_2 Jnn_1 N_1`), unrelated to the TRUNC_SAT rename.
- `vloadop`, `SHAPEX_`, `VLOAD`/`vload`: NO occurrence anywhere in the patch.
- `iadd_` (the function, not `iadd_sat_`): hunk 14 `iadd__is_wf` (L347-356). Context L312-313 shows
  `def iadd_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := uN.mk_uN (((proj_uN_0 v_iN) + (proj_uN_0 iN_0)) % (2 ^ v_N))`;
  proof `intro _ _ h; subst h; exact iswf_uN_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))` (needs `iadd_` to remain a transparent `def` with `% 2^N`).
  `imul__is_wf` (L360-368) is the same one-liner. `iswf_iadd_sat_func` / `iadd_sat__is_wf` are a different function.
- `Step_read`: hunk 75 (L2190-2200) deletes the old premise-less `Step_read_is_wf` (its context L2191 is the OLD `memory_init_succ` rule with
  `uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)` etc.); hunk 76 (L2204-2214) deletes old `Step_is_wf`; hunk 92 (L2464-2475) re-adds
  `theorem Step_read_is_wf (z : state) (admininstr_lst : List admininstr) (var_1 : List admininstr) : wf_config (config.mk_config z admininstr_lst) → Store_ok (fun_store z) → Step_read (config.mk_config z admininstr_lst) var_1 → Forall (fun (var_1_elem : admininstr) => wf_admininstr var_1_elem) var_1 := sorry`
  and `Step_is_wf` (L2477-2608) whose `read` case is `exact wf_config.config_case_0 _ _ hst (Step_read_is_wf _ _ _ hcfg hsok h0)` (L2493). The hand-edit comment (L2464-2469) says it is false in "memory.fill/copy/init push `CONST I32 (i+1)` with `i = 2^32 - 1` on a 2^16-page memory" (L2468) - to be deleted once proved.
- `MEMORY_FILL`/`MEMORY_COPY`: no occurrence; `MEMORY_INIT`: only the context line L2191.
- `trunc_sat`: L538 (numeric `cvtop___is_wf`), L1260 (`lcvtop___is_wf`).

### B5. [my check] Dry run of the patch on the user's regenerated `wasm2.0.lean` (scratch only)

- When I copied it (about 13:35 +0800), the working-tree `spectec/src/test-lean-claude/wasm2.0.lean` (git ` M`) was the user's regenerated file: md5
  `37bc09d8914f52e3c296df5a1435b1ff`, 14698 lines (byte-identical to the modified `spectec/test-lean/todaywasm2.0.lean`); my scratch copy `regen_wasm2.0.lean` preserves it.
  HEAD's hand-edited version = untracked `spectec/src/test-lean-claude/OLD_wasm2.0.lean` (md5 `cd0e676e2744e189bbd6f8beb7f0ad76`) - a ready source of every proof text.
  NOTE (checked again at 16:07 +0800): the working tree has CHANGED since - `HelperLemmas.lean`, `TypePreservation.lean`, `TypeProgress.lean`, `wasm2.0.lean` all have mtime 16:05:35,
  `git diff --stat` shows these 4 files modified (855+/691-), and `wasm2.0.lean` is now md5 `1d76569c7e0b0afb871af5003d6c8e0e`, 16612 lines, 62 `sorry` theorems (all numeric `*_is_wf`), `Step_read_is_wf` proved at L16101,
  `Step_is_wf` at L16325 (my scratch snapshot: `now_wasm2.0.lean`). I.e. the main session / user has applied the bundle21 changes after my dry-run; the dry-run below concerns the REGENERATED file.
- `patch -o regen_patched.lean -r regen.rej regen_wasm2.0.lean < PATCH` on a scratch copy: exit 0, ALL 92 hunks applied, no `.rej`.
  Fuzz 2 on hunk #2 (`zero_is_wf`) and #3 (`dim_is_wf`) (their context lines are `/- ... at: ../specification/wasm-2.0/1-syntax.spectec:L.C-L.C -/`
  comments whose spec line numbers changed); fuzz 1 on hunk #75 (old `Step_read_is_wf` removal: its context line is the old memory.init rule text, which
  the regeneration changed); offset -64 lines for hunks #37-#92 (the regenerated file is 64 lines shorter before `vvunop_`).
- Output: `/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/work/digest-living/regen_patched.lean`
  (md5 `5db3d39c3fe76686f5d20497073424b9`, 16268 lines; = 14698 + 1570). It has 152 `*_is_wf` theorems: 89 proved, 63 `sorry` = 62 opaque numeric ones
  + `Step_read_is_wf`. The 62: s33_to_u32, extend__, fabs_, fceil_, ffloor_, fnearest_, fneg_, fsqrt_, ftrunc_, iclz_, ictz_, ipopcnt_, wrap__, fadd_, fcopysign_,
  fdiv_, fmax_, fmin_, fmul_, fsub_, iand_, ior_, irotl_, irotr_, ishl_, ishr_, ixor_, feq_, fge_, fgt_, fle_, flt_, fne_, convert__, demote__, promote__,
  reinterpret__, trunc__, trunc_sat__, narrow__, ibits_, fbits_, ibytes_, fbytes_, nbytes_, vbytes_, inv_ibits_, inv_fbits_, inv_ibytes_, inv_fbytes_,
  inv_nbytes_, inv_vbytes_, inot_, irev_, iandnot_, ibitselect_, iavgr_, iq15mulr_sat_, fpmin_, fpmax_, lanes_, inv_lanes_ (each `<name>_is_wf`).
  NOT compiled (no lake allowed) - compile status unknown; the only proof I can see must change is `vshiftop__is_wf` (below).
- Generated-Lean differences vs the bundle19 base (content diff after dropping spec-location comments), relevant to the hand proofs:
  a. TRUNC_SAT: `vcvtop__Fnn_1_M_1_Jnn_2_M_2` -> `vcvtop__Fnn_1_M_1_Inn_2_M_2` (the inductive, `wf_vcvtop__Fnn_1_M_1_Inn_2_M_2` + its ctor
     `vcvtop__Fnn_1_M_1_Inn_2_M_2_case_0 (Fnn_1) (M_1) (Inn_2 : Inn) (M_2) (v_sx) (zero_opt)`, `vcvtop__.mk_vcvtop___2 Fnn_1 M_1 (Inn_2 : Inn) M_2 var_x`,
     `wf_vcvtop__.vcvtop___case_2` with `shape_2 = shape.X (lanetype_Inn Inn_2) (dim.mk_dim M_2)`, `proj_vcvtop___2`). `fun_zeroop` and `fun_halfop` each lose their
     4 TRUNC_SAT cases with I8/I16 destinations (their `..._before_..._case_40` -> `..._case_36`, last ctor `fun_zeroop_case_40` -> `_36`, ctor numbers shift).
     `fun_lcvtop__` TRUNC_SAT ctors only change `Jnn_2` -> `Inn_2` in the vcvtop__ argument (lane results stay `lane_.mk_lane__0 (Jnn_Inn Inn.I32/I64) _`).
     `Jnn_2` survives in EXTEND/EXTADD_PAIRWISE/EXTMUL/vnarrow.
  b. `wf_vloadop_.vloadop__case_0` now ends `... = (vsize v_vectype)/2 ∧ (v_M > 1)` (regen L1780).
  c. `opaque ishl_ (v_N : N) (v_iN : iN) (iN_0 : iN)` and `ishr_ (v_N) (v_sx) (v_iN) (iN_0 : iN)` (was `v_u32 : u32`); `ishl__is_wf`/`ishr__is_wf` now take
     `wf_uN v_N iN_0` (was `wf_uN 32 v_u32`), still `sorry`. `fun_binop_` SHL/SHR rules pass `iN_2` (was `uN.mk_uN (proj_uN_0 iN_2)`).
     `fun_vshiftop_` rules now yield `ishl_ (lsizenn (lanetype_Jnn J)) lane (uN.mk_uN (v_n % (lsizenn (lanetype_Jnn J))))` (same for `ishr_ ... v_sx lane ...`).
     `vshiftop__is_wf`'s own header is unchanged (`wf_uN 32 v_u32`). => the hand proof at patch L1461-1464 passes `hu : wf_uN 32 v_u32` where
     `ishl__is_wf` now wants `wf_uN (lsizenn ..) (uN.mk_uN (v_n % lsizenn ..))`: needs e.g. `iswf_uN_of_lt (Nat.mod_lt _ (by decide))` (helper `iswf_uN_of_lt` exists, patch L64-67).
  d. `Step_read.memory_fill_succ`, `memory_copy_le`, `memory_init_succ` push `admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (iadd_ 32 (Option.get! (proj_num__0 i)) (uN.mk_uN 1)))`
     (copy_le and init_succ do this for both `j` and `i`). The TABLE rules (`table_fill_succ`, `table_copy_le`, `table_init_succ`) still push the unbounded
     `(proj_uN_0 (Option.get! (proj_num__0 i))) + 1` (they need `|REFS| < 2^32`, i.e. `Store_ok`). `table_size` pushes `uN.mk_uN v_n` with `|REFS| = v_n`;
     `memory_size` pushes `v_n` with `v_n*64*Ki = |BYTES|`.
  e. `Moduleinst_ok` and `Globaltype_ok` are IDENTICAL to the base: bundle20's upstream artifacts (B) (hoisted `|addrs| > 0`) and (C) (`Globaltype_ok` = MUT only) are NOT fixed.
  f. `Step_pure` unchanged (54 ctors, same names); `Step_read` has 47 ctors (block, loop, call, call_indirect_call/trap, call_addr, ref_func, local_get, global_get,
     table_get_trap/val, table_size, table_fill_trap/zero/succ, table_copy_trap/zero/le/gt, table_init_trap/zero/succ, load_num_trap/val, load_pack_trap/val,
     vload_oob/val, vload_shape_oob/val, vload_splat_oob/val, vload_zero_oob/val, vload_lane_oob/val, memory_size, memory_fill_trap/zero/succ,
     memory_copy_trap/zero/le/gt, memory_init_trap/zero/succ). `fun_instantiate` gensym numerals renumbered (`i_90093` -> `i_82780`, harmless).
- Lean callers of the hand-edited signatures (grep, all use the 3-underscore + `wf_config` + `Store_ok` + step shape, so the signature must be kept):
  `Step_read_is_wf`: `TypePreservation.lean:2039`; `Step_is_wf`: `TypePreservation.lean:2693, 2747`, `TypeProgress.lean:3855, 4083, 4093, 4262, 4312, 7133, 7195, 7422, 7516, 7720, 7785`.
  Stale prose to update when `Step_read_is_wf` is proved: `TypePreservation.lean:18, 913-915, 2019`; `TypeProgress.lean:46`.


## C. The living docs: current state, numbers, stale statements

### C1. `for-claude/NOTES.md` (1483 lines; "Last updated 2026-10-05 (end of bundle20)" L3)

Read-first list [L6-15]: (1) the bundle20 section, (2) `bundle20/user_requested_documents/insights_for_next_turn.md` (recursor-generated case lemmas, the
`type_of%` guard for agent proofs, `omega` ignores the `N`/`M`/`n` abbrevs), (3) bundle19 `README_wasm2.0_hand_edits.md`, (4) bundle18 `insights_for_next_turn.md` section 4 and bundle16 `insights_for_next_turn.md`.

State at the END OF BUNDLE20 [L17-64, L110-124]:
- Task 1 done: the 16 unused `sorry`s carry `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED` (15 dead `HelperLemmas` + `ExtensionLemmas.Val_ok_store`) [L29]. "Still unanswered from bundle18: may the 16 dead sorries be deleted?" [L148].
- Preservation: audited, statement equal to Rocq and Isabelle, 0 signature mismatches on the chain; trust boundary = 33 generated `sorry`s (`Step_read_is_wf` + 32 numeric), no project axiom;
  non-vacuity machine-checked (`preservation_nonvacuity_witness.lean`); 346 inductives fingerprint-matched 1:1 with Rocq [L30-35]. Findings: (A) FIXED `ibytes_len'`/`ibytes_len''` derived `False`
  (restated with Rocq's floor semantics via `rat_to_nat`; `ibytes_inv` premise fixed likewise); (B) UPSTREAM `Moduleinst_ok` hoisted `|addrs| > 0` (SpecTec `middlend/sideconditions.ml`) so no `$invoke` config is `Config_ok`;
  (C) UPSTREAM `Globaltype_ok` admits only MUT globals; (D) FIXED `s_invert_*` were vacuous with the zip-`Forall₂` (length conjunct added) [L36-42].
- Progress: `TypeProgress.lean` (new, in lakefile, imports `TypePreservation`): all 223 Rocq declarations covered, 280/280 proof targets proved, ONLY sorries = the two known-false subcases
  `t_progress_be_vload_pack` (SHAPE 64x1) and `t_progress_be_vcvtop` (F32->I16 TRUNC_SAT), both proved *stuck* in Lean; `#sorry_deps TLC.t_progress` = those 2 + `Step_read_is_wf` + 56 generated numeric `*_is_wf`;
  `#print axioms` adds 17 project axioms mirroring `axioms.v` [L43-50]. `HelperLemmas.lean`: +12 progress-only axioms of `axioms.v`, `Forall2_size`/`Forall2_size2` with `hlen`, a NOT-PORTED note for `Forall2_seq_size`;
  `TypePreservation.wf_config_frame` renamed `wf_config_wf_frame` [L51-55]. Tooling: `safety-checks/verify_against_baseline.sh` (race-free), recovery checkpoints + merge scripts in `bundle20/checkpoints/` [L56-58].
- Sorry inventory: `HelperLemmas` 15 (dead), `ExtensionLemmas` 1 (dead), `TypeProgress` 2, every other hand-written file 0, `wasm2.0.lean` 63 (= Rocq `Admitted`); `lake build` clean, 3006 jobs [L60-64].
- bundle19 section [L66-146]: user's answers to the bundle18 blockers: (1) `rat_to_nat` no longer opaque (`(r.num.tdiv (Int.ofNat r.den)).toNat`), (2) the memory.fill/copy/init 2^32 corner case awaits a spec fix - "leave the unprovable cases as `sorry`",
  (3) use `Vals_ok` for the locals length (deviation: `t_read_preservation` takes `Vals_ok v_s v_f.LOCALS v_C'.LOCALS`, Rocq takes a bare inductive `Forall2`) [L68-73, L104-106]. New explicit permission: prove inside `wasm2.0.lean` every `sorry`
  theorem whose `wasm.v` counterpart is filled in [L75-77]. `wasm2.0.lean` had 152 `*_is_wf`: 89 proved (all that are `Qed` in Rocq), 63 `sorry` (= the 63 `Admitted` in `wasm.v`; Rocq's 64th `Admitted`, `res_list_eq_dec`, is a derived instance in Lean) [L80-86].
  `#sorry_deps TLC.t_preservation` = 33 [L110-124]: `Step_read_is_wf` + convert__, demote__, extend__, fabs_, fceil_, ffloor_, fnearest_, fneg_, fsqrt_, ftrunc_, iand_, iandnot_, ibitselect_, ibytes_, iclz_, ictz_, inot_, inv_lanes_, ior_, ipopcnt_, irev_, ishl_, ishr_, ixor_, lanes_,
  nbytes_, promote__, reinterpret__, trunc__, trunc_sat__, vbytes_, wrap__ (all `opaque` => unprovable, but satisfiable (return 0/[]/none/`fN.POS fNmag.INF`) so not false) [L113-118]. `t_pure_preservation` reaches 29 of them through `Step_pure_is_wf`; `store_extension_reduce` the 4 byte ones;
  `t_read_preservation` depends only on `Step_read_is_wf` [L121-124].
- `t_read_preservation` helper list (just before `t_preservation_type_aux`): `ais_cons_pre`/`ais_*1` chains, `pt_*` principal-type readers, `ais_seq4_last`, `ais_fill_inv`, `table_refs_ok`, `elem_refs_ok`, `minst_func_externaddr`, `memarg0_align8`, `map_local_inj`,
  `funcinst_ok_parts`, `func_ok_body`, `default_val_ok`, `default_vals_ok`, `Forall2_app_intro` [L98-103]. Scratch dirs named: `tr/`, `w19/`, `deps/Deps.lean` (`#sorry_deps`) - session scratchpad, not the repo [L144-146].
- Older sections: bundle18 [L150-169] (26 -> 18 sorries; `store_extension_reduce` proved WITHOUT `Step_is_wf`; user's `br_table_ge` premise removal and `splice` regeneration verified), bundle17 [L171-224] (no Rocq-`Admitted` preservation lemmas; gap analysis `gap_analysis_v1.md`; `with_mem` out-of-bounds blocker; the
  user's three-rule triage: 16 "mark for deletion", 0 "Rocq Admitted", 10 "attempt" [L215-217]), bundle16 [L235-312] (83 -> 27; "Template B/C"; `@Instrs_ok2.rec` direct application), bundle15 [L314-416] (pass A; `cases ... with` over `obtain`), bundle13 [L418-608] (signature audit, 12 findings/11 fixed; resync), bundle12 [L610-668],
  bundle11 [L670-742], bundle10 [L744-819], bundle9 [L821-900], bundle8 [L902-949], bundle4 rename pass [L951-987], 2026-09-23 resync [L989-1067], session-1 recap/setup/TODO [L1069-1483].

STALE / contradicted statements inside NOTES.md that a new section should not propagate:
- L1-16 header and L17-64 bundle20 text describe the 2 sorries in `TypeProgress.lean` and `Step_read_is_wf` as standing blockers (upstream commit 6582b3a39 / spec 4cf9f29c5 removes the causes).
- L89-91 "`Step_read_is_wf` stays `sorry`: ... false in the corner case".
- L1105-1113 "`wasm2.0.lean` (12503 lines as of session 1) ... **Do not hand-edit this file**" - superseded by the bundle19 permission [L75-77]; same for is_wf_theorems.md L43 and L108-114. The file is now 14698 lines (regenerated) / 16351 (HEAD).
- L1087-1089 name only `safety-checks/check.sh`; bundle20 added `verify_against_baseline.sh` [L56].
- L989 and L991 are the same heading twice (typo). L1176-1199 wasm2.0.lean line numbers are session-1 numbers.
- L1395-1400 "Deliberately-kept gaps (mirror Rocq, do not fix)" is FALSE since bundle17 [L173-186]; the whole "TODO for next session" block L1360-1471 is historical.
- L296-303 ("5 deliberate gaps" etc.) and L522-526 ("this project deliberately excludes SIMD") are historical and wrong now.

### C2. `for-claude/is_wf_theorems.md` (121 lines)

- Purpose: log every `*_is_wf` theorem the project relies on, with true/false/unknown (default: treat `sorry`'d ones as true unless trivial to prove) [L3-8, L99-121].
- Table L29-33 has only 3 rows (all bundle17-era): `Step_is_wf` ("likely FALSE as stated", `sorry`; Rocq `wasm.v:17702` hand-edited with extra `Store_ok (fun_store z)` premise), `Step_pure_is_wf` (believed TRUE, `Qed` upstream `wasm.v:15794-15987`),
  `Step_read_is_wf` (FALSE in 3 corner cases per upstream author; `Admitted` upstream `wasm.v:17354-17698`, hand-edited with `Store_ok`; memory.fill-succ, memory.copy-le, memory.init-succ push `CONST I32 (i + 1)` with `i = 2^32 - 1`, allowed by `Memtype_ok` (2^16 pages = 2^32 bytes); `2^32` not a u32; "a spec-level issue, independent of the backend").
  The prose notes supersede the table: bundle18 [L45-56], bundle19 [L58-87] (89 of 152 proved; 63 sorry = Rocq `Admitted`; `Step_is_wf` proved with the `Store_ok` premise; `Step_pure_is_wf` proved/TRUE; `Step_read_is_wf` `sorry` with premise; the 32 numeric theorems), bundle20 [L89-97] (set equality of the 63 re-verified by script;
  `TypeProgress.lean` uses `Step_is_wf` and through it `Step_read_is_wf`; "Lean's `Step.ctxt_*` congruence rules require `wf_config` of the inner configurations, as Rocq's do"; "Isabelle's `step_wf`/`Step_read_is_wf` lack the `Store_ok` premise and are false as stated (table.size pushes an unbounded `|REFS|`) - independently confirms the hand-added premise").
- To update after the upstream change: `Step_read_is_wf` row/verdict (now provable), re-run the "63 sorry == Rocq Admitted" set comparison (expected Lean: 62 numeric `sorry`s; and recheck what Rocq now `Admitted`s after deleting `ishl_wf`/`ishr_wf`), new bundle21 note.

### C3. `for-humans/SUMMARY.md` (167 lines; "Last updated 2026-10-05 (bundle20)" L3)

Sections: Latest bundle20 [L7-29], Previous bundle19 [L31-48], bundle18 [L50-62], bundle17 [L64-85], then the original session-1 summary [L88-167] "kept for history". Plain-English style (short, intuitive). Contains: "Progress: ported and proved ... exceptions are the two instruction cases that are provably stuck under the current spec" [L15-19];
two upstream (SpecTec) translation artifacts: starting configuration of a function invocation never well-typed; stores containing immutable globals never valid ("shrink what both theorems talk about but don't make them false ... reported for an upstream fix") [L23-28]; bundle19: "`Step_read_is_wf`: false in the known 4 GiB-memory corner case (spec fix pending)" [L40]; patch location + "tested" [L46-48]; bundle17: "Work stopped at that point to report, per the standing instructions. No Lean files were changed this turn" [L84-85].

### C4. `claude-logging/README.md` (17 lines)

Index only: `for-humans/` (short summaries), `for-claude/` (verbose notes for a cold start; start with `for-claude/NOTES.md`), `safety-checks/` (timestamped output of the periodic nothing-outside-`spectec/src/test-lean-claude/` check), `is_wf_theorems.md` (in `for-claude/`).

## D. Standing instructions / refinements that must still be followed (from these files)

1. HARD SAFETY RULE [NOTES L1085-1094]: never modify anything outside `spectec/src/test-lean-claude/`; run `bash spectec/src/test-lean-claude/claude-logging/safety-checks/check.sh` from the repo root periodically and after every batch of edits (writes a timestamped report into `claude-logging/safety-checks/`; bundle20 added the race-free `verify_against_baseline.sh`);
   any agent/subagent MUST be told the rule explicitly and either not write files (pure research agents report in their final answer) or write only under `claude-logging/` and run the same check.
2. Signatures must match the Rocq statements (up to forced backend renaming); proof method may differ [NOTES L1069-1078]; verify Rocq/Lean shapes by `grep` of the real files, never from memory; record provenance (source file:line) in each ported theorem's doc comment [digest_prior_lean_attempts L423-426].
3. "Replicate Rocq's tactics closely, diverge only when needed; if that fails, understand the Rocq proof as a whole first" (user's explicit instruction) [NOTES L745-747, L681-682]; document divergences in the lemma's doc comment (e.g. `construct_ais_vals` left-induction) [L785-788].
4. "If you're experiencing issues with a particular proof, skip it and flag it" - standing guidance since bundle15 [NOTES L357-360]; alternate "pass A" (trivial-first sweep, stop at first genuinely complex item) and "pass B" (attack complex proofs) [L316-325].
5. Ask the user before an interpretive change to a lemma's shape; generalizing a monomorphic lemma ("obvious optimizations") is allowed [NOTES L1467-1471]. Do not add `axiom`s beyond Rocq's trusted base (`axioms.v`) without flagging it as a decision [digest_prior_lean_attempts L456-459; bundle20 added 17 axioms mirroring `axioms.v`].
6. Stop and report on a blocker/needed decision rather than proceeding ("per the standing instructions") [SUMMARY L84-85; NOTES L194-205 "do not attempt those 4 cases until the user decides"].
7. bundle19 permission: `wasm2.0.lean` MAY be edited to prove `sorry` theorems whose `wasm.v` counterpart is filled in; unprovable ones stay `sorry`; the hand edits live inside the generated file and are wiped by regeneration -> re-apply with the patch [NOTES L75-77, L92-95; README_wasm2.0_hand_edits L27-47]. Optional "design choice for later" (separate proof file or backend-emitted proofs): "Neither is needed now" [README L49-57].
8. Track every `*_is_wf` the project relies on in `is_wf_theorems.md` with true/false/unknown (default: treat `sorry`'d as true unless trivial; flag a suspected FALSE prominently as a serious finding) [NOTES L1096-1103; is_wf_theorems L99-121]. `wasm2.0.lean` may change under you: re-check line numbers.
9. New `.lean` files must be added to `lakefile.lean`'s `globs` of `lean_lib TestLeanClaude` [NOTES L1135-1139]; everything lives in `namespace TLC`; use `«mut»` for the Rocq `mut` type [L1316-1322, L1344-1348]; use the project's `Forall`/`Forall₂`/`Forall₃`/`Map`/`Map₂`/`Map₃`/`OMap` (from `ExtendedDeriveDecEq.lean`), do not redefine or redirect codegen to Mathlib's [L1114-1128; digest_prior_lean_attempts L298-330].
10. Dead-sorry convention: mark with `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED`; deletion not yet authorized [NOTES L29, L148]. Three-rule triage of sorries (bundle17 `gap_analysis_v1.md` section 5): mark-for-deletion / Rocq-`Admitted` (leave) / attempt [L215-217].
11. Logging: each turn is a `verbatim_dialogue_log/bundleN/` (prompt/response/modelinfo), user-requested documents in `bundleN/user_requested_documents/`; `for-claude/NOTES.md`, `for-humans/SUMMARY.md`, `for-claude/is_wf_theorems.md` are the living docs to refresh each turn ("Last updated" lines NOTES L3, SUMMARY L3); safety-check outputs accumulate in `claude-logging/safety-checks/` (229 entries incl. `check.sh` and `verify_against_baseline.sh`). [README L1-17; NOTES L1-4; SUMMARY L3-5]


## E. Open issues recorded in these files (with where)

1. 16 dead sorries (15 `HelperLemmas` + `ExtensionLemmas.Val_ok_store`), marked `TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED` [NOTES L29]; "may they be deleted?" never answered [NOTES L148]; several are unprovable as stated under the zip-based `Forall₂` [NOTES L302-303].
2. Upstream SpecTec artifacts (B) `Moduleinst_ok` hoisted `|addrs| > 0` (no `$invoke` config is `Config_ok`; SpecTec `middlend/sideconditions.ml`) and (C) `Globaltype_ok` = single `some MUT` ctor [NOTES L39-41; SUMMARY L23-28; digest_wasm_v L261-270 had already flagged (C)]. [my check] both definitions are byte-identical in the regenerated file (still open after `6582b3a`).
3. 62 opaque-builtin `*_is_wf` `sorry`s in `wasm2.0.lean` cannot be proved (functions are `opaque`; Rocq `Axiom`s with `Admitted` wf lemmas); fix = generator emits real definitions (as for `rat_to_nat`) [is_wf_theorems L81-85; NOTES L116-118].
4. Rocq `Instr_ok` vs `ai_principal_typing` inconsistent for the STORE-packed-float case (a live Rocq WIP leftover; Lean's stricter reading is the correct one) - "worth reporting upstream", no Lean change [NOTES L487-491].
5. bundle9 note: a not-yet-pushed `wf_counterexamples.v` claimed 6 `*_is_wf` provably FALSE (`fone_is_wf`, `utf8_is_wf`, `Step_pure_is_wf`, `Step_read_is_wf`, `runelem_is_wf`, `rundata_is_wf`) [NOTES L824-833]; `Step_pure_is_wf` verdict is superseded (proved, TRUE) [is_wf_theorems L32]; [my check] the Lean file has no theorem named `fone_is_wf`/`utf8_is_wf`/`runelem_is_wf`/`rundata_is_wf` (152 `*_is_wf` total).
6. `eleminst` has no `wf_eleminst` and `wf_store` does not constrain ELEMS: possible generator omission "worth a sanity check, not just silently replicating" [digest_wasm_v L511-517]; consistent with the patch (`wf_store.store_case_` has 6 explicit lists but only 5 hypotheses: funcs, globals, tables, mems, datas - e.g. patch L1547-1595, L1730).
7. digest_type_progress L125-133 (2026-09-23): VLOAD with a SPLAT memarg "reads like a possible spec gap" (typing rule does not bound lane width like VLOAD_LANE/VSTORE_LANE's `wf_sz`); status never followed up in these files (bundle20's progress port proved `t_progress_be` except 2 cases).
8. Maintenance cost: hand proofs live inside a generated file and are wiped by regeneration; two durable alternatives (backend leaves out / marks hand-proved theorems and proofs go in a separate file; or backend emits the proofs) are noted but "Neither is needed now" [README_wasm2.0_hand_edits L49-57].
9. The earlier Lean-only `with_mem` out-of-bounds slice-update length issue (fixed in bundle18 by the clamped, length-preserving `splice`) is recorded in NOTES L194-205, L152-153, L161-163. (The `vstore_lane-oob` N-bits-vs-N/8-bytes typo that the bundle21 report lists as still open upstream is NOT mentioned in any of my assigned files.)

## F. Techniques and pitfalls (with the lemma they came from)

### F-patch: how the 89 hand proofs are built (bundle19 patch)

1. Option-valued generated functions are inductive relations `fun_X ... (var_0 : Option T)` with a final "otherwise" ctor `fun_X_case_N x0 .. (h : ¬ fun_X_before_.. ) : fun_X .. none`.
   Proof shape: `intro h <hyps> hne heq; subst heq; cases h <;> (try exact absurd rfl hne) <;> ...` or explicit ctor patterns ending `| fun_X_case_N x0 x1 .. h0 => exact absurd rfl hne`
   (`vshiftop__is_wf`, `lcvtop___is_wf`, `relop__is_wf`, `vcvtop___is_wf`, `vunop__is_wf` last case, `vbinop__is_wf`, `vextunop___is_wf`).
2. Sum-type enumeration: `rcases v with ⟨inn, op⟩ | ⟨fnn, op⟩ <;> (try cases inn) <;> (try cases fnn) <;> (try cases op) <;> first | exact absurd rfl hne | exact ...` (`unop__is_wf`, `testop__is_wf`, `packnum__is_wf`, `unpacknum__is_wf`).
3. When a rule uses the same partial function twice (witness lists `var_0_lst`, `var_1_lst`), prove functionality and `subst`: `iswf_iabs_func`/`iswf_imin_func`/`iswf_imax_func`/`iswf_iadd_sat_func`/`iswf_isub_sat_func` (via `iswf_signed_func`, `iswf_inv_signed_func`; `cases ha ... cases hb ... omega`) lifted by `iswf_Forall₂_eq_of_func`/`iswf_Forall₃_eq_of_func` (induction on the list the other lists are zipped against; needs both length facts). See `vunop__is_wf` ctors 0-3 and `vbinop__is_wf` ctors 8-23 (`have heqv : var_0_lst = var_1_lst := ...; subst heqv`).
4. SIMD results: `iswf_setproduct` (cartesian product `setproduct_`, via `iswf_setproduct1/2`) + `iswf_Forall_map`/`iswf_Forall_Map₂` (`Map₂` is `List.ap`/`zipWith`) + `iswf_inv_lanes_Map` + opaque `inv_lanes__is_wf` (and `lanes__is_wf`); ctors are grouped by identical bodies (vunop 4-11, 12-25; vbinop 0-7/24-35, 8-23, 36-51; vrelop 0-7, 8-23, 24-35).
5. `List.modify`/`splice`/`getElem!` wf transport: `iswf_Forall_modify` (uses `List.modify_nil`, `List.modify_zero_cons`, `List.modify_succ_cons`), `iswf_Forall_splice` (`List.mem_of_mem_take/drop`), `iswf_Forall_getElem!` (`getElem!_pos`/`getElem!_neg`; needs `P default`, hence the `iswf_*_default` lemmas; `wf_funcinst default` etc. are built with `wf_moduleinst.moduleinst_case_ _ _ _ _ _ _ _ _ (iswf_Forall_nil _)`).
6. State/store projections: `cases hs with | state_case_0 s f hst hf`, `cases hst with | store_case_ fs gs ts ms es ds hfs hgs hts hms hds`; with all-underscore patterns the wanted hypothesis is the 7th/8th/9th/10th/11th slot for funcs/globals/tables/mems/datas (patch L1547-1595); frame: `cases hf with | frame_case_ ls m hls hm`.
7. Allocation lemmas: `cases H; subst_vars; cases hs; refine wf_store.store_case_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ <;> first | assumption | exact iswf_Forall_append ‹_› (iswf_Forall_cons ‹_› (iswf_Forall_nil _))`; plural versions: `induction H with | fun_allocX_case_0 .. => exact hs | fun_allocX_case_1 .. p1 p2 p3 p4 ih => subst p3 p4; exact ih (allocX_is_wf .. p2 hs .. rfl) ..` (patch L2218-2413).
8. `Step_is_wf` needs no induction: Lean's `Step.ctxt_label/ctxt_frame/ctxt_instrs` carry the inner `wf_config`; `table.grow`/`memory.grow` bounds: `cases h0 with | fun_growtable_case_1 _ => exact absurd rfl h1 | fun_growtable_case_0 ti' i j_opt rt r'_lst i' hold hi' _ _ _ hwfnew => rw [← hold]; cases hwfnew with | tableinst_case_ _ _ htt => cases htt with | tabletype_case_0 _ _ hlim => cases hlim with | limits_case_0 _ _ hu _ => have := iswf_uN_lt hu; simp only; omega`;
   memory: `iswf_grow_pages` via `iswf_rat_to_nat_floor` (`rat_to_nat r = r.floor.toNat` using `Rat.floor_def`, `Int.tdiv_eq_ediv`, `Int.ediv_neg_of_neg_of_pos`, `Int.sign_eq_one_of_pos`) and `iswf_rat_to_nat_le` (`Rat.floor_monotone`, `Rat.floor_intCast`, `Rat.intCast_natCast`, `Rat.add_le_add_left`, `Rat.natCast_nonneg`, `Rat.add_zero`, `Rat.natCast_pow`) - possible only because `rat_to_nat` now has a real definition.
9. Numeric: `iswf_two_pow_cast : ((2:Int)^n) = ((2^n : Nat) : Int)` (`Int.natCast_pow`) to turn `wf_uN` bounds into `omega`-friendly Nat facts (`iswf_uN_of_lt`, `iswf_uN_lt`, `iswf_uN_proj_lt`); `Nat.two_pow_pos` hint must be supplied to `omega`; `Int.emod_nonneg`/`Int.emod_lt_of_pos` for `x % 2^N` (`iswf_uN_toNat_emod`, used by `isub_`/`ineg_`); `Nat.mod_lt` for `iadd_`/`imul_`; `Nat.pow_le_pow_right` for `iswf_inv_signed`.
10. Constructor application: pass the explicit-arg underscores exactly, e.g. `wf_num_.num__case_0 _ _ _ (by decide) h rfl` (3 explicit args; `(by decide)` closes the `Inn` side goal), `wf_lane_.lane__case_0 _ _ _ h hlt`, `wf_admininstr.admininstr_case_13 _ _ hnum` (CONST), `admininstr_case_20 _ _ (by decide) hvec` (VCONST), `admininstr_case_7 _ hl` (BR), `_case_44 _ hx` (LOCAL_TEE), `_case_71 _ _ _ hi hais'` (LABEL_), `_case_72 _ _ _ hf'' hais'` (FRAME_), `_case_4 _ _ hb h2` (IFELSE). These indices are positional and shift if the generator adds a ctor. Use `‹_›` (assumption by type) for anonymous hyps.
11. `Step_pure_is_wf` is one `cases h with` listing all 54 ctors in order with exact binder arity (e.g. `| unreachable  =>`, `| vshiftop c_1 v_n v_Jnn v_N vshiftop c c'_lst var_0_lst h0 .. h8 =>`); each non-trivial case first re-derives the `wf_admininstr` of the consumed operands with `hall _ (by simp)` or `hall _ (List.mem_singleton_self _)` (`by simp` can fail on metavariable elements - NOTES L133-134), then `cases` them with `rename_i` for the anonymous hypotheses.
12. `iswf_admininstr_instr`/`iswf_admininstr_val`: `cases h <;> constructor <;> assumption` converts `wf_instr`/`wf_val` to `wf_admininstr` for any ctor.

### F-notes: project-wide Lean/Rocq lessons recorded in NOTES.md and the digests

1. Dependent elimination fails when the inductive INDEX is an opaque term (`l[i]!`, `p.1`, `x.TYPE`, `OMap`/`Option.map` over a variable): do the inversion once in a separate lemma whose arguments are bare variables, then apply it at the opaque site ("Template C" = `Externaddr_invert_funcs/_tables/_mems/_globals` as `_aux` lemmas; fixed `minst_invert_elems`, `store_none_mem_extension`, `table_grow_table_extension`) [NOTES L257-270].
2. A constructor argument that unification assigns to an existing variable keeps its slot but loses your name -> `Unknown identifier` at the USE site, not at `cases` [NOTES L262-264]. Prefer `cases h with | Ctor names => ..` to `obtain ⟨..⟩ := h` for indexed `Prop` inductives (`table_set_table_extension`) [L367-383]; positional names need N leading `_` for N explicit args (`Moduleinst_ok` 14, `Store_ok` 12) [L385-394]; `cases hexpr with | mk_Expr_ok2` takes 7 names, not 8 (explicit arg unified away) [L578-592]; leading params auto-promoted: `Funcinst_ok` (s), `Func_ok` (C), `Expr_ok2` (s), `Expr_ok` (C) [L126-129]; hyps whose types mention bound data may be reordered ahead of earlier ones (`Instr_ok.br_table`, `Instr_ok2.plain`, `Ref_ok.func`): read the real order with `trace_state; sorry` or `cases h` + `rename_i` [L939-949]. Fastest way to learn a position: a deliberate application type mismatch read from `lake build` output [L391-394].
3. `subst h` with two local variables may eliminate the one you wanted: use `rw [h]` on the goal / `rw [e1, e2] at ..` [NOTES L709-720, L141-142; digest_prior L175-178].
4. `.induct` principles (e.g. `list_slice_update.induct`): do not guess auto-generated case names; use `all_goals (first | rfl | simp_all [...])` [NOTES L477-486].
5. Prefer ordinary left induction + `resulttype_sub_split_sup'` over Rocq's `last_ind` (`construct_ais_vals`) [NOTES L775-788]; `instrtype_sub_compose*` bookkeeping is `omega` + `List.length_append` in Lean [L761-773].
6. Mathlib bridge for the project's zip-based `Forall₂` (needs a length equality): `to_mathlib_forall₂`/`from_mathlib_forall₂` (`List.forall₂_iff_zip`); `Vals_ok` bakes in `v_ts.length = v_vals.length`; `Forall P xs` needs `simp [Forall]`; never redirect codegen to Mathlib's `Forall₂` (kernel nested-inductive restriction, `wf_instr`/`wf_admininstr`/`fun_utf8` break) [digest_prior L137-142, L155-156, L298-336; NOTES L838-841].
7. `induction ... using Foo.rec` over a mutual block crashes with `introN` if two types in the block share a constructor short name (`Instr_ok2.frame` 14 fields vs `Instrs_ok2.frame` 10); rename case IDs uniquely (the real backend is believed to do so; verify with `grep -n "| frame"`) [digest_prior L259-296]. `@Instrs_ok2.rec` takes the store as a parameter plus 3 motives and 12 minor premises; `Extend_store_ais` is a direct term-mode application [NOTES L276-279].
8. `omega` ignores backend `abbrev`s (`n`, `m`, `N`, ..): `subst`/`rw` to bare `Nat` or annotate `: Nat`; do not shadow `n`/`m`/`N` as local names [digest_prior L157-163, L441-442; NOTES L9-11 bundle20 insights]. `conv` is unavailable (use `calc`) [digest_prior L179-181]. `aesop` cannot invent the outer `induction .. using ..rec`, fails on non-linear goals `X subs< X`; `grind` loses chained transitivity [L182-194].
9. `generalize h : tables[a] = ti at hwf_old ⊢` before `obtain`/`cases` on a raw indexing expression; never leave a constructor argument `_` if a later `by` block uses its value [digest_prior L168-174].
10. Definitional equalities usable with plain `exact`: `{C with LABELS := t :: C.LABELS}` = `{LABELS := [t], ..} ++ C`; frame/label nest `{LABELS} ++ ({RETURN} ++ ({LOCALS} ++ C0))` = `Func_ok` body context `{LOCALS, LABELS, RETURN} ++ C0` [NOTES L137-140]. Multi-line structure instances: `{` at end of line and each field on its own line at one indentation [L130-132]. Mixed typed/untyped binders `∃ (a) (b : Option T) (c), ..` do not parse: type every binder [L465-468]. `Forall2_nth_of_length .. _ (by omega)`: give the index explicitly [L135-136].
11. `list_slice_update`: Lean's `take/append/drop` version is only length-preserving when `n = update_l.length`; Rocq's recursive Fixpoint (`wasm.v:66-74`) is unconditionally length-preserving - redefined to Rocq's; generated `with_mem` now uses clamped `splice`, with `HelperLemmas.splice_eq_list_slice_update` [NOTES L469-486, L152-153, L161-163, L194-205].
12. Statement-level traps found by audits: `ai_principal_typing` missing `REF_HOST_ADDR` case (vacuous `_ => True`), GLOBAL_SET mutability pin, RETURN/FRAME_ missing conjuncts, BR_TABLE unparenthesized `∀ l ∈ ls, .. ∃ r', ..` swallowing the default-label clause; singular-`Instr_ok` `instrs_seq_typing_inversion` is FALSE (use the sequence-level `Instrs_ok [i]` form) [NOTES L433-454, L864-880, L911-916; digest_prior L205-253; digest_typing_lemmas L131-145].
13. Rocq notation decoder (when reading Rocq statements): `x :> nat` user typeclass coercion, `|x|` = `seq.size` (and `|x| = q` is a FLOORED equation: `N.of_nat (size x)` vs `q` through `Qfloor`/`Z.to_N`), `!(x)` = `the x`, `x[|i|]` = `lookup_total`, `@@` = `Append` class; Lean fields drop the Rocq `funcinst_`/`store_`/`context_` prefixes (`C.TYPES`) [digest_wasm_v L86-107, L222-230; NOTES L36-38, bundle20 `rat_to_nat` note].
14. Lean naming differences: `val`/`ref`/`admininstr` ctors have no type prefix (`val.REF_NULL`); `mut` is `«mut»`; `Datainst_ok` takes 3 args (pass `datatype.OK`); Rocq `Module_instance_ok` = Lean `Moduleinst_ok`; Rocq `Store_extension` etc. = Lean `Extend_store` etc. [NOTES L1324-1358].

## G. The six static `digest_*.md` files: what they hold and how stale they are

- `digest_prior_lean_attempts.md` (497 L): prior art in `spectec/test-lean/` (typing_lemmas.lean 2071 L; `test-lean-claude/` subfolder with Extension/Subtyping/InstrtypeSub/CounterexampleCheck/SeqTypingInversion/MemoryWriteAxioms/StoreExtension); idioms (section 2), the false singular `instrs_seq_typing_inversion` (section 3), Bug 1 (same-named ctors in a mutual block) and Bug 2 (custom `Forall₂` is load-bearing) (section 4), prior-session status quotes (section 5), consolidated "don't" list (section 6). Still valid; historical for the file-level status (all those sorries were closed in later bundles). Not read by that agent: old `wasm2.0*.lean` copies, `sandbox_11.lean`.
- `digest_subtyping_and_extension_lemmas.md` (499 L): `subtyping.v` (914) + `extension_lemmas.v` (2045) lemma map with line numbers. STALE names: `Store_extension`/`Func_extension`/... are now `Extend_store`/`Extend_funcinst`/..; the file was renamed wholesale (NOTES L989-1043); `Val_ok_store`/`funcinst_same` have no upstream counterpart. The `instrtype_sub` definition/algebra (5-conjunct split with `ts_sub`, `ts`, `ts11_sub`, `ts12_sup`) and the compose family remain the authoritative description.
- `digest_type_preservation.md` (279 L): Rocq `type_preservation.v` at the OLD checkout (13 declarations; 3 `Admitted` for SIMD cases; capstone `t_preservation`). STALE: upstream has proved all of them since 2026-09-22 (NOTES L173-186); its closing claim "WASM 2.0 has no SIMD" (L272-279) is wrong (this spec has V128).
- `digest_type_progress.md` (160 L): Rocq `type_progress.v` (4260 L at `a8b585cdb`; 108 Lemma/Theorem, 1 Fixpoint `split_vals`, 10 Definitions; 5 layers; `t_progress_be` L1888 ~1793 lines; `t_progress_e` L3702; `t_progress` L4230). STALE: says `t_progress_be` is fully `Admitted` with 5 `admit.` sites (lane_-union encoding bug) and proposes a porting order; superseded by `TypeProgress.lean` (~8000 lines, bundle20) and by upstream (`Qed` after `6582b3a39`). Imports: does not import the preservation files.
- `digest_typing_lemmas_and_type_preservation_pure.md` (391 L): `typing_lemmas.v` (2222) + `type_preservation_pure.v` (947): `ai_principal_typing` + `instr_typing_inversion`/`ai_typing_inversion`, composition/inversion lemmas, `Vals_ok`, `inst_match`, the Ltac library (not ported 1:1), 28 `Step_pure__*_preserves` lemmas + `t_pure_preservation`. STALE: says `Step_pure__return_frame_preserves` and `t_pure_preservation` (SIMD) are `Admitted` (now `Qed`).
- `digest_wasm_v.md` (562 L): chapter map of the generated `wasm.v` (11133 L at the old checkout), universal boilerplate, 61 numeric axioms, runtime/typing/reduction/module/soundness sections. STALE: "every `_is_wf` ends Admitted" (89 are now proved in Lean, Rocq has its own hand proofs), "no separate progress file", the `Store_extension` vs `Extend_store` open question (resolved: use `Extend_*`), `Step_read_is_wf` at wasm.v:10153 / `Step_is_wf` at 10261 (is_wf_theorems cites wasm.v:17354-17698 and :17702 for the hand-edited ones). Still useful: `ishl_`/`ishr_` listed as Rocq `Axiom`s (L180), `iadd_`/`imul_`/`isub_` NOT axiomatized (direct arithmetic, L195), `vcvtop__`/`fun_vshiftop_` as dispatch functions (L200-201), Rocq `Step_pure` ctor list incl. `vshiftop` and `vcvtop_full/half/zero` (L340-342; Lean has a single `vcvtop` ctor), memory_fill/copy/init `Step_read` rules (L353-358).


## H. Everything in these files that touches the upstream change set (6582b3a39 / 4cf9f29c5), and what must change

Independent confirmation: my scratch dry-run of the bundle19 patch on the regenerated file agrees with the bundle21 README/report (all hunks apply; 3 fuzz hunks;
only `vshiftop__is_wf` must change; 62 numeric `*_is_wf` `sorry`s remain; `Moduleinst_ok`/`Globaltype_ok` artifacts (B)/(C) still open).

1. vcvtop / TRUNC_SAT -> Inn destination
   - Docs: NOTES L47-50 and SUMMARY L15-19 (two stuck cases proved stuck, `t_progress_be_vcvtop` F32->I16 TRUNC_SAT `sorry`); digest_type_progress L113-142 (stale 5-`admit.` story).
   - Patch: `lcvtop___is_wf` L1247-1263, `vcvtop___is_wf` L1266-1327, `iswf_list_OMap_lane0` L882-887, `Step_pure_is_wf` vcvtop case L2175-2180 (no textual use of the renamed type; names `Lnn_2`/`Jnn_2` there are local binders).
2. vloadop SHAPE needs M > 1: Docs: NOTES L47 (`t_progress_be_vload_pack` SHAPE 64x1). Patch: no occurrence of `vloadop`/`SHAPEX_`/`VLOAD`. Regenerated `wf_vloadop_.vloadop__case_0` gains `∧ (v_M > 1)`.
3. ishl_/ishr_ iN shift, vshiftop mod lane size, Rocq `ishl_wf`/`ishr_wf` axioms deleted: Docs: is_wf_theorems L77-80 and NOTES L113-115 list `ishl_`/`ishr_` among the opaque numeric `*_is_wf` (still `sorry`; keep). Patch: `vshiftop__is_wf` L1454-1465 (uses `hu : wf_uN 32 v_u32`; MUST CHANGE - bundle21 did it via `k % L < L < 2^L`) and `Step_pure_is_wf` vshiftop case L2112-2122 (calls `vshiftop__is_wf`; statement unchanged so it survives).
4. memory.fill/copy/init now push `iadd_ 32 i 1`: Docs: NOTES L87-91, L167-168, L110-124; is_wf_theorems L31-33, L35-43, L54-56, L70-72; SUMMARY L38-41, L60-62, L64-85 describe the 2^32 corner case as open. Patch: `iadd__is_wf` L347-356 gives wf of `iadd_ 32 i (uN.mk_uN 1)` (needs `wf_uN 32 (uN.mk_uN 1)` = `iswf_uN_of_lt` + `by decide`); `iswf_I32_const` L1907-1909; `iswf_num_Inn_proj` L1914-1924 (wf of `Option.get! (proj_num__0 i)` from `wf_num_ (numtype_Inn I) i` and `proj_num__0 i ≠ none`); `Step_is_wf` templates for `Store_ok`-style bounds L2533-2553 (table.grow), L2590-2601 (memory.grow); old stale rule text L2191 (hunk 75, fuzz 1).
5. Rocq `Step_read_is_wf` is now `Qed` and `t_progress_be` `Qed`: the hand-edit comment block at patch L2464-2469 ("false in one corner case ... pending a spec-side fix") and the README sentence "stays `sorry`, as in Rocq" are now wrong. The Lean signature with the extra `Store_ok (fun_store z)` premise must be kept (callers listed in B5). Table `+1` rules still need `|REFS| < 2^32` from `Store_ok`; mem bulk rules now wrap via `iadd_`.

### H-docs: concrete update checklist for the three held-back living docs (line numbers refer to the files as they are now, still bundle20 state)

- `NOTES.md`: L3 date/bundle; L6-15 read-first list (point item 1 at the bundle21 report, item 3 at the bundle21 `README_wasm2.0_hand_edits.md` - bundle19's is superseded but kept unchanged); insert a "bundle21 UPDATE" section before L17;
  fix L43-50 (TypeProgress sorries 2 -> 0; `#sorry_deps TLC.t_progress` 59 -> 56; project axioms 17 -> 15 since `ishl_wf`/`ishr_wf` deleted); L60-64 inventory (TypeProgress 0, `wasm2.0.lean` 62, 16 dead sorries unchanged, lake jobs); L89-91 and L110-124 (`#sorry_deps TLC.t_preservation` 33 -> 32; `Step_read_is_wf` no longer a dependency; `t_read_preservation` now has no `sorry` dependency of its own);
  L1087-1089 (mention `verify_against_baseline.sh`); L1105-1113 ("Do not hand-edit" superseded); L148 (dead-sorry deletion question still open).
- `SUMMARY.md`: L3 date; add "Latest (2026-10-15, bundle21)" above L7 and turn L7 into "Previous (2026-10-05, bundle20)" (this file's convention: the prior "Latest" becomes "Previous (date, bundleN)", cf. L31, L50, L64); L15-19 and L40 become stale.
- `is_wf_theorems.md`: add a "bundle21 note" after L97; table L31-33 (`Step_read_is_wf` now proved with the `Store_ok` premise; `Step_is_wf` proved; `Step_pure_is_wf` proved); record the new reliances (`TypeProgress` `binop_total`/`binop_before` now use the generated `ishl__is_wf`/`ishr__is_wf` instead of the deleted axioms; both stay `sorry`, opaque, believed true); re-run the "Lean `sorry` set == Rocq `Admitted` set" comparison (bundle20 note L91-92) - expected: 62 in Lean = Rocq's set minus `res_list_eq_dec`; fix L108-114 ("`wasm2.0.lean` is not ours to edit") and L43.
- `claude-logging/README.md`: no change needed (index only).

## I. Other notable facts

- The patch is self-consistent with the repo history: HEAD `wasm2.0.lean` (16351 L, md5 `cd0e676e..`) = bundle19 base (md5 `7d2167da..`) + this patch + 19 user "readability scrap" lines (commit `f07b4e1a8`, `example`s after `fun_idiv_`); verified by reverse-applying both.
- At session start the working tree had `wasm2.0.lean` regenerated and uncommitted; by 16:05:35 +0800 the main session/user applied the bundle21 changes (4 `.lean` files modified; `wasm2.0.lean` md5 `1d76569c7e0b0afb871af5003d6c8e0e`, 16612 lines, 62 `sorry` theorems, `Step_read_is_wf` at L16101, `Step_is_wf` at L16325).
  The three living docs and `README.md` still carried their 2026-10-06 mtimes (bundle20 state) when I last looked.
- Rocq-side line numbers in these docs (`wasm.v:17702`, `:17354-17698`, `:15794-15987`) and the ones in the digests are for older checkouts.
- Scratch artifacts (all under `/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/work/digest-living/`): `base_noscrap.lean` (exact bundle19 base, md5 `7d2167da..`), `regen_wasm2.0.lean` (user's regenerated file, md5 `37bc09d8..`), `regen_patched.lean` (regenerated + bundle19 patch, md5 `5db3d39c..`), `now_wasm2.0.lean` (working tree at 16:05, md5 `1d76569c..`), `hunks.json`, `hunk_table.md`, `gen_diff_nc.txt` (content diff base vs regenerated, spec-location comments dropped), `parse_patch.py`, `count_sorry.py`.


## Safety check at end (verbatim output of `verify.sh digest-living-end`)

```
safety check [digest-living-end] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T081105.770872766Z-digest-living-end-497171.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
0a1,40
>  M spectec/src/test-lean-claude/.lake/build/ir/TypeProgress.c
>  M spectec/src/test-lean-claude/.lake/build/ir/TypeProgress.c.hash
>  M spectec/src/test-lean-claude/.lake/build/ir/wasm2.0.c
>  M spectec/src/test-lean-claude/.lake/build/ir/wasm2.0.c.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/ExtensionLemmas.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/ExtensionLemmas.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/ExtensionLemmas.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/Subtyping.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservationPure.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservationPure.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservationPure.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.trace
>  D spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.trace.nobuild
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace
>  M spectec/src/test-lean-claude/HelperLemmas.lean
>  M spectec/src/test-lean-claude/TypePreservation.lean
>  M spectec/src/test-lean-claude/TypeProgress.lean
2a43
> ?? spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/
```
