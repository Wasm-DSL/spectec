# Old vs new: the `EXTEND` removal across the model and the proof

Bundle 33, 2026-11-11. This report compares two complete states of `spectec/src/test-lean-claude/`.

- **OLD:** the old proof together with `OLD_wasm2.0.lean`, the model that still has `EXTEND`. This is HEAD `afb06bf8d`, whose `wasm2.0.lean` is byte-identical to `OLD_wasm2.0.lean`.
- **NEW:** the new proof together with `wasm2.0.lean`, i.e. the files now in the working tree. The model is the bundle32 port, and the proof modules are as repaired this turn.

| module | OLD md5 | NEW md5 | lines OLD → NEW | top-level constructs |
|---|---|---|---|---|
| `ExtendedDeriveDecEq.lean` | `e9b33702…` | `e9b33702…` (same) | 738 → 738 | 24 |
| `wasm2.0.lean` | `4207ecaa…` | `fdfafb39…` | 17,527 → 17,522 | 897 |
| `HelperLemmas.lean` | `7b0db228…` | `7b0db228…` (same) | 1,041 → 1,041 | 118 |
| `Subtyping.lean` | `4f5c6ca9…` | `4f5c6ca9…` (same) | 680 → 680 | 52 |
| `TypingLemmas.lean` | `6284f02c…` | `21429230…` | 1,956 → 1,954 | 97 |
| `TypePreservationPure.lean` | `13c13840…` | `ff4fd477…` | 1,974 → 1,974 | 85 |
| `ExtensionLemmas.lean` | `1e2a23a5…` | `1e2a23a5…` (same) | 2,172 → 2,172 | 135 |
| `TypePreservation.lean` | `5241649e…` | `4c4bb6a6…` | 2,912 → 2,912 | 143 |
| `TypeProgress.lean` | `8087d55b…` | `5e00f3b5…` | 8,248 → 8,248 | 318 |

These nine files are the modules that `lakefile.lean` builds. In OLD the model file is `OLD_wasm2.0.lean`; in NEW it is `wasm2.0.lean`.
- **What is computed.** Every table, and every count and list derived from the data, is computed by `report33.py` (§9) from the files, the build logs and the Lean outputs. The explanations are mine, as are a few fixed references inside them: spec positions, tool versions, and line numbers quoted in an explanation. Two rounds of independent readers checked them against the files (§9, Appendix E).
- **The whole directory.** `git status` for the directory, not counting `claude-logging/`, lists: `OLD_wasm2.0.lean` (modified), `TypePreservation.lean` (modified), `TypePreservationPure.lean` (modified), `TypeProgress.lean` (modified), `TypingLemmas.lean` (modified), `wasm2.0.lean` (modified), `wasm2.0_prevattempt.lean` (deleted).
  - `wasm2.0.lean` and the four repaired modules are the subject of this report.
  - The other two are outside both builds, since the lakefile does not build them. You changed both before bundle32:
    - At HEAD, `OLD_wasm2.0.lean` held an older model (16,508 lines, md5 `059c0051…`). It now holds HEAD's `wasm2.0.lean` (17,527 lines, md5 `4207ecaa…`).
    - `wasm2.0_prevattempt.lean` (15,537 lines, md5 `72748a07…` at HEAD) was deleted.
  - `lakefile.lean`, `lake-manifest.json` and `lean-toolchain` are unchanged.

## 0. Bottom line

- **One cause.** The mech-backend merge deleted one line of the Wasm 2.0 spec: the dead instruction `EXTEND numtype n`. Every difference below follows from that. (The merge also removed a `$fzero` hint, but OLD's model had already been generated without it; see §2.)
- **Text.** 211 lines of OLD differ from NEW: 194 in the model and 17 in the proof modules. Each falls into one of three kinds, and none is unexplained:
  - **7 lines deleted**, because they mention the removed constructor: 5 in the model and 2 match arms in `TypingLemmas`.
  - **173 lines renumber a well-formedness constructor name**, `instr_case_K`/`admininstr_case_K` → K−1 for K ≥ 20:
    - 102 in the generated model;
    - 56 in the model's proofs (the bundle32 port);
    - 15 in the proof modules.
  - **31 generated comments** cite a spec position that moved up one line.
- **Structure.** No top-level construct was added, removed, renamed or reordered in any of the nine files.
  - All 1,869 constructs match OLD one for one.
  - 53 have changed text: 24 in code, and 29 only in their source-position comment.
- **Statements.** No user-level theorem, definition, inductive type or constructor changed its statement. This is checked in Lean, over the 12,775 declarations common to both builds, with constructor numbers mapped (§5).
  - The constructor `EXTEND` itself is gone, from `instr` and `admininstr`, together with its two well-formedness cases.
  - **Unchanged statements, smaller types.** The check compares statements by name. Statements that mention `instr` or `admininstr` keep their text, but now range over types with one constructor fewer. That is the intended effect, and it changes nothing of substance: no typing rule ever mentioned `EXTEND` (§2), so no configuration satisfying the main theorems' typing hypotheses could contain it, even in OLD.
  - Every other declaration whose type changed is one Lean generates automatically.
  - **Changed terms.** Terms changed in 5 user-level definitions and 115 user-level theorems. For user-level declarations, these are exactly the ones whose terms refer to an eliminator or equation lemma that changed (§5).
- **Soundness.** Both states compile with 0 errors and 0 `sorry`, and no theorem depends on `sorryAx`.
  - Every user-level theorem present in both has the same axioms. The only 4 differences are numbered auxiliary sub-proofs whose numbers shifted.
  - `t_preservation` has 35 axioms and `t_progress` 74, the same lists as in OLD.
  - The `Inhabited`-default audit finds no theorem needing a default: 0 of 5,517 in OLD and 0 of 5,496 in NEW.
  - The build logs are identical once line numbers and timings are stripped: the same 171 warnings and the same info output.

## 1. Line-level summary

| file | lines OLD → NEW | deleted (`EXTEND`) | constructor renumbered | spec position comment | total OLD lines differing |
|---|---|---|---|---|---|
| `ExtendedDeriveDecEq.lean` | 738 → 738 | 0 | 0 | 0 | 0 |
| `wasm2.0.lean` | 17,527 → 17,522 | 5 | 158 (102 generated + 56 in proofs) | 31 | 194 |
| `HelperLemmas.lean` | 1,041 → 1,041 | 0 | 0 | 0 | 0 |
| `Subtyping.lean` | 680 → 680 | 0 | 0 | 0 | 0 |
| `TypingLemmas.lean` | 1,956 → 1,954 | 2 | 3 | 0 | 5 |
| `TypePreservationPure.lean` | 1,974 → 1,974 | 0 | 2 | 0 | 2 |
| `ExtensionLemmas.lean` | 2,172 → 2,172 | 0 | 0 | 0 | 0 |
| `TypePreservation.lean` | 2,912 → 2,912 | 0 | 2 | 0 | 2 |
| `TypeProgress.lean` | 8,248 → 8,248 | 0 | 8 | 0 | 8 |
| **total** | | 7 | 173 | 31 | **211** |

**How the lines were matched:**
- From each OLD file, delete the lines that mention the removed constructor (§3.1, §4.1).
- The remaining lines align one for one with the NEW file, which has exactly the same length.
- Each differing pair is classified by the rule that maps it, so no line-matching heuristic is involved.
- 0 pairs are left unexplained.
- Four modules are byte-identical: `ExtendedDeriveDecEq`, `HelperLemmas`, `Subtyping`, `ExtensionLemmas`.
- **Bytes.** All 18 files (9 OLD, 9 NEW) are valid UTF-8 with LF line endings, no byte-order mark and exactly one final newline. Their trailing whitespace and tabs are the same in OLD and NEW. Sizes and full md5 sums are in Appendix D.

## 2. The cause

**The spec line.** mech-backend commit `28073cddd` ("Remove extend instruction") deleted line 474 of `specification/wasm-2.0/1-syntax.spectec`, in the numeric-instruction fragment (`syntax instr/num hint(desc "numeric instruction")`):
```
  | EXTEND numtype n                 hint(show %.EXTEND#%#_#S)
```
**No other change matters.** The merge also brought in mech-backend's removal of `def $fzero hint(wfopt)` from `C-hints.spectec` (commit `5d6980fef`). OLD's generated base had already been produced without that hint (bundle29).
- In bundle32 the HEAD generator was run on the HEAD spec with only the `EXTEND` line restored, and it reproduced OLD's generated base byte for byte (`bundle32/evidence/outputs/generator_check.txt`).
- So neither that hint nor the merge's generator changes affect the Wasm 2.0 Lean output. Those changes are:
  - the ImproveIds name-clash fix;
  - the Sideconditions let-reordering;
  - DefToRel's `hint(axiom)`.

**What the instruction was.** In Wasm 2.0 terms, `instr.EXTEND numtype n` was a dead production. In OLD:
- it is mentioned only on the 5 generated lines of §3.1 and in two match arms in `TypingLemmas`;
- no validation rule mentions it, and `Instr_ok` has 73 rules in both versions;
- no reduction rule mentions it, and `Step_pure`, `Step_read` and `Step` have 54, 47 and 23 rules in both versions.

**The real extension instructions are unchanged.** They live under other constructors:
- `i32.extend8_s` and its siblings are `UNOP` with `unop_Inn.EXTEND n`;
- `i64.extend_i32_s/u` is `CVTOP` with `cvtop__Inn_1_Inn_2.EXTEND sx`;
- the SIMD extensions are `VCVTOP` with `vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND half sx`.

**Why so many names moved.** The backend names the constructors of the well-formedness predicates by position: constructor K (from 0) of `wf_instr` is `instr_case_K`, and likewise `admininstr_case_K` for `wf_admininstr`.
- `EXTEND` was constructor 19 of both `instr` and `admininstr` (68 → 67 and 74 → 73 constructors).
- So every later case moved down by one: `wf_instr` goes from 68 to 67 cases, and `wf_admininstr` from 74 to 73.
- The two predicates number their cases alike for K ≤ 67. In OLD, cases 68–73 of `wf_admininstr` are the six administrative-only instructions.

The renaming was done by meaning, not by arithmetic. Every OLD case except the removed case 19 matched exactly one NEW case with identical text: arguments, premises and conclusion. That gives 67 matches in `wf_instr` and 73 in `wf_admininstr`. Case 19 has no counterpart, no NEW case is left over, and no match is ambiguous.

## 3. The model: `OLD_wasm2.0.lean` → `wasm2.0.lean` (194 lines)

### 3.1 Deleted: the five lines that mention `EXTEND`

| OLD line | construct | deleted line |
|---|---|---|
| 1953 | `inductive instr` | `\| EXTEND (v_numtype : numtype) (v_n : n) : instr` |
| 2062 | `inductive wf_instr` | `\| instr_case_19 (v_numtype : numtype) (v_n : n) : wf_instr (instr.EXTEND v_numtype v_n)` |
| 12206 | `inductive admininstr` | `\| EXTEND (v_numtype : numtype) (v_n : n) : admininstr` |
| 12287 | `def admininstr_instr` | `\| instr.EXTEND x0 x1 => admininstr.EXTEND x0 x1` |
| 12409 | `inductive wf_admininstr` | `\| admininstr_case_19 (v_numtype : numtype) (v_n : n) : wf_admininstr (admininstr.EXTEND v_numtype v_n)` |

### 3.2 Renumbered constructor declarations in the generated model (102 lines)

Each of these lines declares one case of `wf_instr` or `wf_admininstr`. Only the name changed; the rest of the declaration is identical. The full map, with the instruction each case is about:

| OLD → NEW | instruction | `wf_instr` line OLD → NEW | `wf_admininstr` line OLD → NEW |
|---|---|---|---|
| `*_case_0` … `*_case_18` | (unchanged) | 19 cases, same names | 19 cases, same names |
| `*_case_19` | **`EXTEND`, deleted** (§3.1) | 2062 → — | 12409 → — |
| `_case_20` → `_case_19` | `VCONST` | 2063 → 2061 | 12410 → 12405 |
| `_case_21` → `_case_20` | `VVUNOP` | 2067 → 2065 | 12414 → 12409 |
| `_case_22` → `_case_21` | `VVBINOP` | 2068 → 2066 | 12415 → 12410 |
| `_case_23` → `_case_22` | `VVTERNOP` | 2069 → 2067 | 12416 → 12411 |
| `_case_24` → `_case_23` | `VVTESTOP` | 2070 → 2068 | 12417 → 12412 |
| `_case_25` → `_case_24` | `VUNOP` | 2071 → 2069 | 12418 → 12413 |
| `_case_26` → `_case_25` | `VBINOP` | 2075 → 2073 | 12422 → 12417 |
| `_case_27` → `_case_26` | `VTESTOP` | 2079 → 2077 | 12426 → 12421 |
| `_case_28` → `_case_27` | `VRELOP` | 2083 → 2081 | 12430 → 12425 |
| `_case_29` → `_case_28` | `VSHIFTOP` | 2087 → 2085 | 12434 → 12429 |
| `_case_30` → `_case_29` | `VBITMASK` | 2091 → 2089 | 12438 → 12433 |
| `_case_31` → `_case_30` | `VSWIZZLE` | 2094 → 2092 | 12441 → 12436 |
| `_case_32` → `_case_31` | `VSHUFFLE` | 2098 → 2096 | 12445 → 12440 |
| `_case_33` → `_case_32` | `VSPLAT` | 2103 → 2101 | 12450 → 12445 |
| `_case_34` → `_case_33` | `VEXTRACT_LANE` | 2106 → 2104 | 12453 → 12448 |
| `_case_35` → `_case_34` | `VREPLACE_LANE` | 2112 → 2110 | 12459 → 12454 |
| `_case_36` → `_case_35` | `VEXTUNOP` | 2116 → 2114 | 12463 → 12458 |
| `_case_37` → `_case_36` | `VEXTBINOP` | 2121 → 2119 | 12468 → 12463 |
| `_case_38` → `_case_37` | `VNARROW` | 2126 → 2124 | 12473 → 12468 |
| `_case_39` → `_case_38` | `VCVTOP` | 2133 → 2131 | 12480 → 12475 |
| `_case_40` → `_case_39` | `REF_NULL` | 2138 → 2136 | 12485 → 12480 |
| `_case_41` → `_case_40` | `REF_FUNC` | 2139 → 2137 | 12486 → 12481 |
| `_case_42` → `_case_41` | `REF_IS_NULL` | 2142 → 2140 | 12489 → 12484 |
| `_case_43` → `_case_42` | `LOCAL_GET` | 2143 → 2141 | 12490 → 12485 |
| `_case_44` → `_case_43` | `LOCAL_SET` | 2146 → 2144 | 12493 → 12488 |
| `_case_45` → `_case_44` | `LOCAL_TEE` | 2149 → 2147 | 12496 → 12491 |
| `_case_46` → `_case_45` | `GLOBAL_GET` | 2152 → 2150 | 12499 → 12494 |
| `_case_47` → `_case_46` | `GLOBAL_SET` | 2155 → 2153 | 12502 → 12497 |
| `_case_48` → `_case_47` | `TABLE_GET` | 2158 → 2156 | 12505 → 12500 |
| `_case_49` → `_case_48` | `TABLE_SET` | 2161 → 2159 | 12508 → 12503 |
| `_case_50` → `_case_49` | `TABLE_SIZE` | 2164 → 2162 | 12511 → 12506 |
| `_case_51` → `_case_50` | `TABLE_GROW` | 2167 → 2165 | 12514 → 12509 |
| `_case_52` → `_case_51` | `TABLE_FILL` | 2170 → 2168 | 12517 → 12512 |
| `_case_53` → `_case_52` | `TABLE_COPY` | 2173 → 2171 | 12520 → 12515 |
| `_case_54` → `_case_53` | `TABLE_INIT` | 2177 → 2175 | 12524 → 12519 |
| `_case_55` → `_case_54` | `ELEM_DROP` | 2181 → 2179 | 12528 → 12523 |
| `_case_56` → `_case_55` | `LOAD` | 2184 → 2182 | 12531 → 12526 |
| `_case_57` → `_case_56` | `STORE` | 2188 → 2186 | 12535 → 12530 |
| `_case_58` → `_case_57` | `VLOAD` | 2197 → 2195 | 12544 → 12539 |
| `_case_59` → `_case_58` | `VLOAD_LANE` | 2201 → 2199 | 12548 → 12543 |
| `_case_60` → `_case_59` | `VSTORE` | 2206 → 2204 | 12553 → 12548 |
| `_case_61` → `_case_60` | `VSTORE_LANE` | 2209 → 2207 | 12556 → 12551 |
| `_case_62` → `_case_61` | `MEMORY_SIZE` | 2214 → 2212 | 12561 → 12556 |
| `_case_63` → `_case_62` | `MEMORY_GROW` | 2215 → 2213 | 12562 → 12557 |
| `_case_64` → `_case_63` | `MEMORY_FILL` | 2216 → 2214 | 12563 → 12558 |
| `_case_65` → `_case_64` | `MEMORY_COPY` | 2217 → 2215 | 12564 → 12559 |
| `_case_66` → `_case_65` | `MEMORY_INIT` | 2218 → 2216 | 12565 → 12560 |
| `_case_67` → `_case_66` | `DATA_DROP` | 2221 → 2219 | 12568 → 12563 |
| `_case_68` → `_case_67` | `REF_FUNC_ADDR` | — | 12571 → 12566 |
| `_case_69` → `_case_68` | `REF_HOST_ADDR` | — | 12572 → 12567 |
| `_case_70` → `_case_69` | `CALL_ADDR` | — | 12573 → 12568 |
| `_case_71` → `_case_70` | `LABEL_` | — | 12574 → 12569 |
| `_case_72` → `_case_71` | `FRAME_` | — | 12578 → 12573 |
| `_case_73` → `_case_72` | `TRAP` | — | 12582 → 12577 |

That is 48 `wf_instr` lines and 54 `wf_admininstr` lines, 102 in all. No other generated line refers to these cases.

### 3.3 Source-position comments (31 lines)

The generator heads some constructs with a comment giving the spec position they come from. Every `1-syntax.spectec:L.c` with L > 474 now reads L−1, because the line above it was deleted. The 31 affected comments head these constructs (OLD → NEW line):

`instr` (1932→1932), `wf_instr` (2006→2005), `expr` (2226→2224), `elemmode` (2229→2227), `wf_elemmode` (2238→2236), `datamode` (2248→2246), `wf_datamode` (2256→2254), `type` (2265→2263), `«local»` (2270→2268), `func` (2275→2273), `wf_func` (2282→2280), `global` (2290→2288), `wf_global` (2297→2295), `table` (2304→2302), `wf_table` (2309→2307), `mem` (2316→2314), `wf_mem` (2321→2319), `elem` (2328→2326), `wf_elem` (2335→2333), `data` (2343→2341), `wf_data` (2350→2348), `start` (2358→2356), `wf_start` (2363→2361), `externidx` (2370→2368), `wf_externidx` (2378→2376), `«export»` (2394→2392), `wf_export` (2399→2397), `«import»` (2407→2405), `wf_import` (2412→2410), `module` (2421→2419), `wf_module` (2428→2426).

Example, `instr`: `/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:552.1-553.22 -/` → `/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.1-552.22 -/`.

### 3.4 The model's proofs: renumbered references (56 lines)

These are the deviations of the bundle32 port. Every one renames a `wf_admininstr` case inside a proof body; no statement changed. They are logged line by line in `bundle32/user_requested_documents/deviations_in_copying.md`, and listed again in Appendix A.

| construct | lines | renamings (OLD → NEW, instruction × lines) |
|---|---|---|
| `iswf_admininstr_VCONST` | 1 | 20→19 `VCONST` ×1 |
| `iswf_admininstr_VCONST_inv` | 1 | 20→19 `VCONST` ×1 |
| `Step_pure_is_wf` | 14 | 44→43 `LOCAL_SET` ×1, 71→70 `LABEL_` ×3, 72→71 `FRAME_` ×1, 73→72 `TRAP` ×9 |
| `iswf_store_I32_8` | 1 | 57→56 `STORE` ×1 |
| `iswf_load_I32_8_U` | 1 | 56→55 `LOAD` ×1 |
| `Step_read_is_wf` | 28 | 20→19 `VCONST` ×6, 43→42 `LOCAL_GET` ×1, 46→45 `GLOBAL_GET` ×1, 48→47 `TABLE_GET` ×2, 49→48 `TABLE_SET` ×4, 52→51 `TABLE_FILL` ×2, 53→52 `TABLE_COPY` ×4, 54→53 `TABLE_INIT` ×2, 66→65 `MEMORY_INIT` ×2, 71→70 `LABEL_` ×3, 72→71 `FRAME_` ×1 |
| `Step_is_wf` | 10 | 20→19 `VCONST` ×1, 44→43 `LOCAL_SET` ×1, 47→46 `GLOBAL_SET` ×1, 49→48 `TABLE_SET` ×1, 51→50 `TABLE_GROW` ×1, 55→54 `ELEM_DROP` ×1, 67→66 `DATA_DROP` ×1, 71→70 `LABEL_` ×2, 72→71 `FRAME_` ×1 |

## 4. The proof modules (17 lines)

**What the error column shows.** It is what Lean reports for the OLD line when compiled against the NEW model. Each module was compiled with the earlier modules already repaired.

### 4.1 Deleted: two match arms on the removed constructor

| module | OLD line | construct | deleted line | why |
|---|---|---|---|---|
| `TypingLemmas` | 131 | `def instr_of` | `\| admininstr.EXTEND x0 x1 => some (instr.EXTEND x0 x1)` | `instr_of : admininstr → Option instr` is the partial inverse of `admininstr_instr` (Rocq `typing_lemmas.v:124`). It has one arm per `admininstr` constructor (74 in OLD, 73 in NEW), and the `EXTEND` arm no longer type-checks. Lean: "Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`" |
| `TypingLemmas` | 454 | `def ai_principal_typing` | `\| admininstr.EXTEND _ _ => False` | `ai_principal_typing` gives the principal type of an administrative instruction. Its `EXTEND` arm said `False`, and with the constructor gone the arm is an invalid pattern. Deleting a `False` arm in front of the final `| _ => True` would normally make that case `True`, but here the case no longer exists, so no other arm changes meaning. Lean: "Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`" |

### 4.2 Renumbered constructor references (15 lines)

The full OLD and NEW text of all 17 changed lines is in Appendix C.

| module | line OLD → NEW | construct | change | instruction | role of the line | error without the change |
|---|---|---|---|---|---|---|
| `TypePreservation` | 1347 → 1347 | `wf_vconst_parts` | `admininstr_case_20` → `admininstr_case_19` | `VCONST` | Destructs `wf_admininstr (VCONST vt c)` into its two premises. | Too many variable names provided at alternative `admininstr_case_20`: 4 provided, but 2 expected / Alternative `admininstr_case_20` is not needed / Alternative `admininstr_case_19` has not been provided |
| `TypePreservation` | 2164 → 2164 | `t_read_preservation` | `admininstr_case_72` → `admininstr_case_71` | `FRAME_` | Preservation of `Step_read`, `call_addr` case: a function call becomes `FRAME_ n f [LABEL_ n [] body]`. It destructs the well-formedness of that `FRAME_` to reach the `LABEL_` inside. | Too many variable names provided at alternative `admininstr_case_72`: 5 provided, but 0 expected / Alternative `admininstr_case_72` is not needed / Alternative `admininstr_case_71` has not been provided |
| `TypePreservationPure` | 1072 → 1072 | `Step_pure__local_tee_preserves` | `admininstr_case_45` → `admininstr_case_44` | `LOCAL_TEE` | Preservation for `local.tee x` ↪ `val val local.set x`. It destructs `wf_admininstr (LOCAL_TEE x)` and builds `wf_instr (LOCAL_SET x)`. | Alternative `admininstr_case_45` is not needed / Alternative `admininstr_case_44` has not been provided |
| `TypePreservationPure` | 1085 → 1085 | `Step_pure__local_tee_preserves` | `instr_case_44` → `instr_case_43` | `LOCAL_SET` | Preservation for `local.tee x` ↪ `val val local.set x`. It destructs `wf_admininstr (LOCAL_TEE x)` and builds `wf_instr (LOCAL_SET x)`. | Type mismatch wf_instr.instr_case_44 v_x hwfl has type wf_instr (instr.LOCAL_TEE v_x) but is expected to have type wf_instr (instr.LOCAL_SET v_x) |
| `TypeProgress` | 800 → 800 | `wf_forall_admin_val` | `admininstr_case_20` → `admininstr_case_19` | `VCONST` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Application type mismatch: The argument c has type vec_ but is expected to have type vvunop in the application wf_admininstr.admininstr_case_20 vt c |
| `TypeProgress` | 801 → 801 | `wf_forall_admin_val` | `admininstr_case_40` → `admininstr_case_39` | `REF_NULL` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Application type mismatch: The argument rt has type reftype but is expected to have type funcidx in the application wf_admininstr.admininstr_case_40 rt |
| `TypeProgress` | 802 → 802 | `wf_forall_admin_val` | `admininstr_case_68` → `admininstr_case_67` | `REF_FUNC_ADDR` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Type mismatch wf_admininstr.admininstr_case_68 a has type wf_admininstr (admininstr.REF_HOST_ADDR a) but is expected to have type wf_admininstr (admininstr_val (val.REF_FUNC_ADDR a)) |
| `TypeProgress` | 803 → 803 | `wf_forall_admin_val` | `admininstr_case_69` → `admininstr_case_68` | `REF_HOST_ADDR` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Type mismatch wf_admininstr.admininstr_case_69 a has type wf_admininstr (admininstr.CALL_ADDR a) but is expected to have type wf_admininstr (admininstr_val (val.REF_HOST_ADDR a)) |
| `TypeProgress` | 814 → 814 | `wf_forall_admin_val` | `admininstr_case_20` → `admininstr_case_19` | `VCONST` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Too many variable names provided at alternative `admininstr_case_20`: 4 provided, but 2 expected / Alternative `admininstr_case_20` is not needed / Alternative `admininstr_case_19` has not been provided |
| `TypeProgress` | 839 → 839 | `wf_config_label` | `admininstr_case_71` → `admininstr_case_70` | `LABEL_` | Rocq `type_progress.v:857`. It destructs `wf_admininstr (LABEL_ n bes es)`. | Alternative `admininstr_case_71` is not needed / Alternative `admininstr_case_70` has not been provided |
| `TypeProgress` | 856 → 856 | `wf_config_frame` | `admininstr_case_72` → `admininstr_case_71` | `FRAME_` | Rocq `type_progress.v:870`. It destructs `wf_admininstr (FRAME_ n f es)`. | Too many variable names provided at alternative `admininstr_case_72`: 5 provided, but 0 expected / Alternative `admininstr_case_72` is not needed / Alternative `admininstr_case_71` has not been provided |
| `TypeProgress` | 7784 → 7784 | `t_progress_e_Instr_ok2_frame` | `admininstr_case_72` → `admininstr_case_71` | `FRAME_` | Progress, frame case. The body is well formed under the inner frame, by destructing `wf_admininstr (FRAME_ …)`. | Too many variable names provided at alternative `admininstr_case_72`: 5 provided, but 0 expected / Alternative `admininstr_case_72` is not needed / Alternative `admininstr_case_71` has not been provided |
| `TypingLemmas` | 570 → 568 | `instr_typing_inversion` | `instr_case_20` → `instr_case_19` | `VCONST` | Inverts `Instr_ok` into the principal type. Its `vconst` case destructs `wf_instr (VCONST …)`. | Too many variable names provided at alternative `instr_case_20`: 4 provided, but 2 expected / Alternative `instr_case_20` is not needed / Alternative `instr_case_19` has not been provided |
| `TypingLemmas` | 1681 → 1679 | `construct_ai_val` | `instr_case_20` → `instr_case_19` | `VCONST` | Types a value as an administrative instruction. The vector case builds `wf_instr (VCONST V128 c)`. | Application type mismatch: The argument c_t has type vec_ but is expected to have type vvunop in the application wf_instr.instr_case_20 vectype.V128 c_t |
| `TypingLemmas` | 1747 → 1745 | `construct_ais_trap` | `admininstr_case_73` → `admininstr_case_72` | `TRAP` | `TRAP` has every type. The proof needs `wf_admininstr TRAP`. | Unknown constant `wf_admininstr.admininstr_case_73` |

**How to read the error column.**
- "Alternative … has not been provided" is reported at the `cases … with` line, which for some rows is the line above the edit. It is listed in the row of the edit it belongs to.
- The error for `TypePreservationPure` line 1085 appears only once line 1072 is fixed, because it sits inside that alternative.

**The first compile hid line 570.** In that compile of the unrepaired `TypingLemmas`, the two invalid patterns of §4.1 made `instr_of` and `ai_principal_typing` fail.
- That cascaded into 80 errors, including 67 `rfl` failures at line 192 (`instr_of_admininstr_instr`).
- It also turned `ai_typing_inversion'`, `ai_val_principal_typing_inversion`, `ais_single_ref_typing_inversion`, `ais_single_val_typing_inversion`, `construct_ai_maybe`, `instr_typing_inversion` into `sorry` declarations, which hid the error at line 570.
- So the table's three `TypingLemmas` rows come from a second compile of that module, with only the two arms of §4.1 deleted. Their line numbers are the NEW ones.
- The other twelve rows come from compiling each unrepaired module against the repaired earlier ones.

**Nothing else needs changing.** No other code line in the four modules mentions a renumbered or removed constructor. The other two `EXTEND` tokens in `TypeProgress`, at lines 3496 and 3705, are the SIMD conversion `vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND`, which still exists.

## 5. Lean-level comparison (elaborated declarations)

**Method.** Both builds were loaded in Lean, and every declaration of the nine modules was dumped with:
- a 32-bit structural hash of its type: Lean's `Expr.hash`, which ignores binder names, binder annotations and metadata;
- the same hash of its value;
- for theorems, its axioms.

Equal hashes are strong evidence that two terms are equal, not proof: a change would be missed only through a 32-bit hash collision.
- **Inductive metadata** is not covered by the hashes, so it was compared separately (below).
- **Environment extensions** were not compared at this level: attributes, simp sets, instances, reducibility and docstrings. All of them are written in the source, and the line accounting (§1) shows that no such line changed.

In the OLD dump, the cases `wf_instr.instr_case_K` and `wf_admininstr.admininstr_case_K` with K ≥ 20 were first renamed to K−1. So were the same cases of their auxiliary `.below` inductives, and the removed case was marked. The comparison is therefore by meaning.

**Totals.** OLD has 12,818 declarations (5,526 theorems), and NEW has 12,787 (5,505 theorems). 12,775 are common to both; 43 are only in OLD and 12 only in NEW.

| module | declarations OLD → NEW | removed | added | type or value changed |
|---|---|---|---|---|
| `ExtendedDeriveDecEq` | 100 → 100 | 0 | 0 | 0 |
| `«wasm2.0»` | 10,630 → 10,608 | 30 | 8 | 438 |
| `HelperLemmas` | 179 → 179 | 0 | 0 | 0 |
| `Subtyping` | 65 → 65 | 0 | 0 | 0 |
| `TypingLemmas` | 415 → 411 | 6 | 2 | 263 |
| `TypePreservationPure` | 206 → 204 | 4 | 2 | 82 |
| `ExtensionLemmas` | 132 → 132 | 0 | 0 | 0 |
| `TypePreservation` | 166 → 166 | 0 | 0 | 38 |
| `TypeProgress` | 925 → 922 | 3 | 0 | 203 |

By kind (OLD → NEW): thm 5,526 → 5,505, def 3,925 → 3,921, ctor 2,336 → 2,330, induct 440 → 440, rec 442 → 442, axiom 83 → 83, opaque 66 → 66.
- Types or values changed only for kinds `def`, `rec`, `thm`. No axiom, opaque or inductive type changed its type or value.
- The four byte-identical modules have no changed declaration at this level either.

### Removed (43)

- **The removed instruction (16):**
  - `instr.EXTEND` and `admininstr.EXTEND`;
  - the `EXTEND` cases of `wf_instr` and `wf_admininstr`, and of their `.below`;
  - the lemmas Lean generates for each removed constructor: `elim`, `inj`, `injEq`, `noConfusion` and `sizeOf_spec`.
- **Ends of numbered families that shrank (15).** Lean numbers many auxiliary declarations by position: equation lemmas `eq_N` (one per match arm), `_proof_N`, and `DecidableEq` sub-proofs. When such a family loses a member, its highest numbers disappear and the members after the removed one are renumbered.
  - The families, with their size OLD → NEW: `TLC.ai_principal_typing.eq_N` 56→55; `TLC.br_reduce_decidable._proof_N` 141→139; `TLC.instr_of.eq_N` 74→73; `TLC.return_reduce_decidable._proof_N` 75→74; `_private.TypePreservationPure.0.TLC.ai_principal_typing.match_1.eq_N` 56→55; `_private.TypingLemmas.0.TLC.instr_of.match_1.eq_N` 74→73; `_private.TypingLemmas.0.admininstr_instr.match_1.eq_N` 68→67; `admininstr.decEq._proof_N` 184→181; `admininstr_instr.eq_N` 68→67; `instr.decEq._proof_N` 170→167.
  - For example, the deleted arms of `admininstr_instr`, `instr_of` and `ai_principal_typing` take away their last equation lemmas, `admininstr_instr.eq_68`, `ai_principal_typing.eq_56`, `instr_of.eq_74`.
  - The lemmas from each deleted arm onward now state the next arm's equation, so their types changed: `admininstr_instr` (48), `ai_principal_typing` (1), `instr_of` (54).
- **Renumbered without shrinking (12).** These belong to families that kept their size but were renumbered, or are hygienic names whose counter moved. Each has a counterpart among the 12 added names.
- **By category:** 10 auto-generated lemmas/eliminators of the removed constructor; 8 derived-instance helpers with hygienic names (counter shifted); 6 derived DecidableEq auxiliary proofs (numbered per constructor); 5 auxiliary proof terms (numbered per declaration); 4 pattern-matching auxiliaries (matchers, splitters, their equations); 4 the removed EXTEND case of wf_instr / wf_admininstr (or of its .below); 3 equation lemmas of definitions by pattern matching (one per arm, numbered); 2 the removed constructor itself; 1 auxiliary simp lemmas (numbered). The full list is in Appendix B.

### Added (12)

All are the renumbered counterparts just described: 8 derived-instance helpers with hygienic names (counter shifted); 2 auxiliary proof terms (numbered per declaration); 1 auxiliary simp lemmas (numbered); 1 pattern-matching auxiliaries (matchers, splitters, their equations). There is no new user-level declaration and no new axiom.

### Statements

No user-level theorem, definition, inductive type or constructor has a different type. The 724 theorems, 124 definitions and 8 recursors whose type differs are all generated by Lean:
- theorems: 262 derived DecidableEq auxiliary proofs (numbered per constructor); 197 pattern-matching auxiliaries (matchers, splitters, their equations); 161 auxiliary proof terms (numbered per declaration); 103 equation lemmas of definitions by pattern matching (one per arm, numbered); 1 auxiliary simp lemmas (numbered).
- definitions: 102 per-constructor eliminators X.CTOR.elim of the changed inductives; 10 recursors / case eliminators / structural-recursion helpers / no-confusion of the changed inductives; 8 pattern-matching auxiliaries (matchers, splitters, their equations); 4 derived DecidableEq helpers (match_on_same_ctor) of the changed inductives, same name in both builds.
- recursors: 8 recursors / case eliminators / structural-recursion helpers / no-confusion of the changed inductives.

**Inductive metadata.** A separate dump recorded every inductive, constructor and recursor: parameters, indices, constructor lists, constructor indices and field counts, and recursor motives, minor premises and rules. OLD was mapped by meaning. Of 3,218 OLD and 3,212 NEW entries, the only differences are:
- the 6 removed constructors: `EXTEND` of `instr` and `admininstr`, and case 19 of `wf_instr`, `wf_admininstr` and their `.below`;
- 6 inductive types with one constructor fewer: `admininstr`, `instr`, `wf_admininstr`, `wf_admininstr.below`, `wf_instr`, `wf_instr.below`;
- 306 constructors whose index went down by exactly 1, with everything else equal. These are the constructors after `EXTEND`: 48 of `instr`, 54 of `admininstr`, and the same numbers for `wf_instr`, `wf_admininstr` and their `.below`;
- 8 recursors with one minor premise fewer: `admininstr.rec`, `instr.rec`, `wf_admininstr.below.rec`, `wf_admininstr.rec`, `wf_instr.below.rec`, `wf_instr.rec` also have one rule fewer, while `admininstr.rec_1`, `instr.rec_1` (the auxiliary recursors of the nested types) keep their 2 rules.

This index shift explains the remaining generated changes: the types of the per-constructor `X.CTOR.elim`, the values of `ctorIdx`/`noConfusionType`, and the `DecidableEq` sub-proofs.

### Definitions whose elaborated value changed (168, of which 5 user-level)

- `admininstr_instr`, `instr_of` and `ai_principal_typing` each lost their `EXTEND` arm.
- `br_reduce_decidable` and `return_reduce_decidable` (`TypeProgress`) have unchanged source. They case-split on an `admininstr` with a `| _ =>` wildcard, so their terms now have one case fewer.
- The rest are derived or auxiliary: 102 per-constructor eliminators X.CTOR.elim of the changed inductives; 28 recursors / case eliminators / structural-recursion helpers / no-confusion of the changed inductives; 14 derived DecidableEq / BEq; 11 pattern-matching auxiliaries (matchers, splitters, their equations); 4 derived SizeOf; 4 derived DecidableEq helpers (match_on_same_ctor) of the changed inductives, same name in both builds.

### Proof terms that changed (115 user-level theorems)

Most of these theorems have unchanged source; Appendix B lists them. A probe on NEW listed, for every theorem and definition, the declarations its term refers to directly, and marked those whose type changed or that are new:
- **All 120 changed user-level declarations refer to such a declaration** (115 theorems and 5 definitions; 120 of 120).
  - Classified by the first such reference: 68 equation lemmas / matchers of the changed definitions; 52 eliminators of the changed inductives.
  - In Wasm terms: their proofs destruct an instruction or its well-formedness, or rewrite with an equation of `ai_principal_typing`, `instr_of` or `admininstr_instr`, whose case analyses now have one case fewer.
- **None of the 2,527 unchanged user-level declarations refers to one.**
- So, for user-level declarations, a changed term coincides exactly with a direct use of something the removal changed.

All 17 theorems edited in §3.4 and §4.2 were pure renamings.
- These 5 have the same proof term as before, once constructor numbers are mapped: `construct_ai_val`, `construct_ais_trap`, `iswf_admininstr_VCONST`, `iswf_load_I32_8_U`, `iswf_store_I32_8`. They only apply a constructor.
- The other 12 each do a `cases` on `wf_instr`/`wf_admininstr`, whose eliminator lost a case.

Among generated theorems, 7 changed value but not type. Each refers directly to a changed declaration:
- `TLC.ai_principal_typing.eq_6` → `TLC.ai_principal_typing.match_1`
- `_private.TypeProgress.0.TLC.is_const.match_1.eq_6` → `TLC.is_const._sparseCasesOn_1`
- `_private.TypeProgress.0.TLC.split_vals.match_1.eq_6` → `TLC.is_const._sparseCasesOn_1`
- `admininstr.brecOn.eq` → `admininstr.casesOn`
- `instr.brecOn.eq` → `instr.casesOn`
- `wf_admininstr.brecOn` → `wf_admininstr.rec`
- `wf_instr.brecOn` → `wf_instr.rec`

### Axioms

- **Unchanged for user-level theorems.** Every user-level theorem present in both builds has the same set of axioms.
  - The only 4 theorems whose axioms differ are numbered auxiliaries: `TLC.br_reduce_decidable._proof_120` {}→{propext}, `TLC.br_reduce_decidable._proof_124` {propext}→{}, `TLC.br_reduce_decidable._proof_81` {}→{propext}, `TLC.br_reduce_decidable._proof_82` {propext}→{}.
  - Their numbers now point at other sub-proofs.
- **`TLC.t_preservation`** uses 35 axioms: the 3 standard ones (`propext`, `Classical.choice`, `Quot.sound`) and 32 of the model's `*_is_wf` axioms.
- **`TLC.t_progress`** uses 74: the 3 standard ones, 56 `*_is_wf` axioms and 15 project axioms from Rocq's `axioms.v`.
- Both lists are identical in OLD and NEW, and no theorem depends on `sorryAx` in either.

### `Inhabited` defaults

This is a kernel replay of the eight project modules other than `ExtendedDeriveDecEq`, with the 121 `Inhabited` instances defined in the modules, and the 7 external ones they use, made opaque:
- OLD: 0 of 5,517 theorems need a default value.
- NEW: 0 of 5,496.
- The difference of 21 is the 24 removed theorems minus the 3 added.
- **Positive control.** The audit was run again on NEW together with a scratch module of three control theorems, two of which read a default value. It checked 5,499 theorems and reported exactly those two (`audit_ctl_model`, `audit_ctl_nat`). So the harness does detect default-dependent proofs with this toolchain and build. The control module was never among the project's modules; a copy is kept as evidence (`evidence/tools/AuditCtl33.lean`).

## 6. Every top-level construct whose text changed

All nine files have the same top-level constructs, in the same order, in OLD and NEW: `ExtendedDeriveDecEq` 24, `wasm2.0` 897, `HelperLemmas` 118, `Subtyping` 52, `TypingLemmas` 97, `TypePreservationPure` 85, `ExtensionLemmas` 135, `TypePreservation` 143, `TypeProgress` 318, 1,869 in all.
- **What counts as a construct.** Entries are as counted by `toplevel32.py`: every command that starts at column 0 outside comments, except `deriving` clauses.
- Attribute lines, `initialize` and `set_option … in` prefixes count as separate entries. Counting declarations only gives 1,866 (`ExtendedDeriveDecEq` 22, `TypingLemmas` 96; the rest unchanged).
- The one-for-one match holds either way.

These 53 have changed text:

| file | construct | change |
|---|---|---|
| `wasm2.0` | `inductive instr` | line mentioning `EXTEND` deleted (1); spec position in the header comment (1) |
| `wasm2.0` | `inductive wf_instr` | line mentioning `EXTEND` deleted (1); spec position in the header comment (1); case declarations renumbered (48) |
| `wasm2.0` | `inductive admininstr` | line mentioning `EXTEND` deleted (1) |
| `wasm2.0` | `def admininstr_instr` | line mentioning `EXTEND` deleted (1) |
| `wasm2.0` | `inductive wf_admininstr` | line mentioning `EXTEND` deleted (1); case declarations renumbered (54) |
| `wasm2.0` | `theorem iswf_admininstr_VCONST` | case references renumbered in the proof (1) |
| `wasm2.0` | `theorem iswf_admininstr_VCONST_inv` | case references renumbered in the proof (1) |
| `wasm2.0` | `theorem Step_pure_is_wf` | case references renumbered in the proof (14) |
| `wasm2.0` | `theorem iswf_store_I32_8` | case references renumbered in the proof (1) |
| `wasm2.0` | `theorem iswf_load_I32_8_U` | case references renumbered in the proof (1) |
| `wasm2.0` | `theorem Step_read_is_wf` | case references renumbered in the proof (28) |
| `wasm2.0` | `theorem Step_is_wf` | case references renumbered in the proof (10) |
| `TypingLemmas` | `def instr_of` | line mentioning `EXTEND` deleted (1) |
| `TypingLemmas` | `def ai_principal_typing` | line mentioning `EXTEND` deleted (1) |
| `TypingLemmas` | `theorem instr_typing_inversion` | case references renumbered in the proof (1) |
| `TypingLemmas` | `theorem construct_ai_val` | case references renumbered in the proof (1) |
| `TypingLemmas` | `theorem construct_ais_trap` | case references renumbered in the proof (1) |
| `TypePreservationPure` | `theorem Step_pure__local_tee_preserves` | case references renumbered in the proof (2) |
| `TypePreservation` | `theorem wf_vconst_parts` | case references renumbered in the proof (1) |
| `TypePreservation` | `theorem t_read_preservation` | case references renumbered in the proof (1) |
| `TypeProgress` | `theorem wf_forall_admin_val` | case references renumbered in the proof (5) |
| `TypeProgress` | `theorem wf_config_label` | case references renumbered in the proof (1) |
| `TypeProgress` | `theorem wf_config_frame` | case references renumbered in the proof (1) |
| `TypeProgress` | `theorem t_progress_e_Instr_ok2_frame` | case references renumbered in the proof (1) |
| `wasm2.0` | 29 more constructs: `expr`, `elemmode`, `wf_elemmode`, `datamode`, `wf_datamode`, `type`, `«local»`, `func`, `wf_func`, `global`, `wf_global`, `table`, `wf_table`, `mem`, `wf_mem`, `elem`, `wf_elem`, `data`, `wf_data`, `start`, `wf_start`, `externidx`, `wf_externidx`, `«export»`, `wf_export`, `«import»`, `wf_import`, `module`, `wf_module` | spec position in the header comment (1 line each) |

## 7. Builds

**How the builds were run.**
- Both states were compiled from scratch in the scratchpad, one Lean process at a time, under a 12 GB memory cap.
- The toolchain's `lean` v4.32.0 was called directly; the repo's `.lake/build` was not used.
- The NEW error, `sorry` and warning counts are from the fresh build of the installed repo files.

| module | errors OLD / NEW | `sorry` warnings OLD / NEW | warnings OLD / NEW | time (s): OLD / NEW scratch / NEW repo |
|---|---|---|---|---|
| `ExtendedDeriveDecEq` | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 2 / 5 |
| `wasm2.0` | 0 / 0 | 0 / 0 | 89 / 89 | 27 / 28 / 55 |
| `HelperLemmas` | 0 / 0 | 0 / 0 | 4 / 4 | 4 / 4 / 7 |
| `Subtyping` | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 2 / 4 |
| `TypingLemmas` | 0 / 0 | 0 / 0 | 9 / 9 | 22 / 36 / 39 |
| `TypePreservationPure` | 0 / 0 | 0 / 0 | 47 / 47 | 5 / 9 / 9 |
| `ExtensionLemmas` | 0 / 0 | 0 / 0 | 14 / 14 | 3 / 5 / 5 |
| `TypePreservation` | 0 / 0 | 0 / 0 | 7 / 7 | 6 / 11 / 11 |
| `TypeProgress` | 0 / 0 | 0 / 0 | 1 / 1 | 15 / 21 / 22 |

**Logs.** The OLD and NEW build logs are identical once line numbers and timings are stripped. Only line numbers move, where lines were deleted above them. The logs contain:
- the same 171 warnings: 94 unused variable; 51 Mathlib naming-convention lint; 7 "tactic does nothing"; 7 "Try this" suggestion; 6 "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"; 3 "This simp argument is unused"; 2 "try 'simp' instead of 'simpa'"; 1 "this tactic is never executed";
- the same info output: 118 lines printed by the `#check Instrs_ok2.rec` left inside a proof at `TypeProgress` line 8151.

**Times.** "NEW scratch" is the build in which the repair was made, and "NEW repo" the fresh build of the installed files, which are byte-identical to it. Times vary with machine load, since the editor's Lean servers were running throughout; they are not a property of the change.

**Memory.** The compiles peaked at 4.54 GiB (4,760,044 KiB), in OLD's `TypeProgress`; NEW's `TypeProgress` peaked at 4,746,004 KiB. The Lean probes of §5 peaked higher, at 5.51 GiB (5,776,760 KiB), in the `Inhabited` audit runs.

**No Lake build of either state.** The repo's `.lake/build` matches neither state.
- Its traces record warning counts that differ even from OLD's: 93 for `wasm2.0`, against 89.
- It holds oleans for modules the lakefile no longer builds (`custom_notation`, `sandbox_5`, `sandbox_10`).
- Both states were therefore checked only by these scratch builds with the bare `lean` binary. The lakefile sets no Lean options, and Lake's recorded setup for `wasm2.0` has empty options, so a Lake build should behave the same. That was not run.

## 8. Left unchanged, and other notes

**Comments that count instructions.** 5 comments in `TypingLemmas` still say 68, though `instr` now has 67 constructors.
- Where (NEW lines): line 187, "the 68-case transcription"; line 1477, "each of `instr`'s 68 constructors"; line 1480, "68×68 cases, mechanical"; line 1482, "the 68×68 case bash"; line 1690, "in the other 68".
- I left them as they were: they are comments, and line 1482 records a past measurement.
- Line 1688, "~74 cases uniformly", describes Rocq's tactic script, so I didn't count it as stale. Read as a statement about Lean, it would now be 73.
- Line 772, "Rocq destructs both instructions (68×68)", also describes Rocq.
- Line 196, "all 73 cases", counts `Instr_ok` rules, which are still 73.

**Comments that cite model line numbers.** 5 comments in the proof modules cite `wasm2.0.lean` by 6 line numbers beyond the first deleted line. All 6 citations were already wrong in OLD, and the declarations they name moved again, by 2 or 5 lines:

| comment (NEW file:line) | cites line | names | actually at OLD → NEW |
|---|---|---|---|
| `HelperLemmas:678` | 4203 | `nbytes_` | 4555 → 4553 |
| `HelperLemmas:726` | 2652 | `truncz` | 2701 → 2699 |
| `HelperLemmas:734` | 4644 | `lanes_` | 5003 → 5001 |
| `TypingLemmas:838` | 11261 | `val_ref` | 11945 → 11943 |
| `Subtyping:15` | 12669 | `Valtype_sub` | 13401 → 13396 |
| `Subtyping:15` | 12675 | `Resulttype_sub` | 13407 → 13402 |

The comments that cite lines 9, 12 and 20 are right in both versions. The one citing line 798 for `size` was already wrong in OLD: it is at line 718 in both.
I left all of them as they are.

**The word `sorry`.** No code contains `sorry`, but the word appears on 7 comment lines of the nine NEW modules:
- `wasm2.0` line 15430: commented-out generated original;
- `wasm2.0` line 15563: commented-out generated original;
- `TypePreservationPure` line 18: status note saying there is no `sorry`;
- `TypePreservation` line 19: status note saying there is no `sorry`;
- `TypePreservation` line 2024: docstring: `Step_read_is_wf` used to be `sorry`;
- `TypeProgress` line 47: status note saying there is no `sorry`;
- `TypeProgress` line 51: status note saying there is no `sorry`;
- so a plain `grep sorry` finds these 7 lines, and none is a proof hole. `OLD_wasm2.0.lean` has the same two commented-out lines, at 15435 and 15568.

**Files not touched this turn:** `wasm2.0.lean`, `OLD_wasm2.0.lean`, `ExtendedDeriveDecEq`, `HelperLemmas`, `Subtyping`, `ExtensionLemmas`.

**Pre-existing, and the same in OLD and NEW: two re-stated theorems.** The fresh generator output, `spectec/test-lean/todaywasm2.0.lean` (md5 `d480dbf1…`), has 89 `sorry`s.
- **Proved as generated:** 87 of those theorems, in both OLD and NEW.
- **Commented out:** the generated `Step_read_is_wf` and `Step_is_wf`, with their `--   sorry` at lines 15430 and 15563. The commented-out text is identical in OLD and NEW.
- **Re-stated:** each is re-stated below `inductive Store_ok` with three changes, as in bundle29:
  - it moves below `Store_ok`;
  - it takes the configuration as `(z : state) (admininstr_lst : List admininstr)`, with `config.mk_config z admininstr_lst` in the hypotheses;
  - it gets the premise `Store_ok (fun_store z)`.
- **The generated forms are false.** Bundles 23 and 29 showed this with a Lean witness, using axioms `propext`, `Classical.choice` and `Quot.sound` only (`bundle29/evidence/unedited_Step_read_is_wf_false.log`).
  - The counterexample is a well-formed configuration whose store holds a table of 2^32 references. It steps by `table.size` to `CONST I32 2^32`, which is not a well-formed `u32`.
  - The witness source was not kept, so it was not re-run on NEW. The counterexample does not involve `EXTEND`.
- **What "zero `sorry`" covers:** all generated statements except these two, which hold only in the weaker re-stated form. This port changed them only by the renamings in their proofs (§3.4).

**Documentation.**
- **Living docs** (`claude-logging/README.md`, `for-claude/*.md`, `for-humans/*.md`): they mention `EXTEND` or numbered `*_case_` names only in `for-claude/digest_wasm_v.md` (lines 153, 156).
  - Those lines describe Rocq's `wasm.v`, which still has `instr_EXTEND` (`spectec/test-rocq/theories/wasm.v:3282`), so they are accurate.
- **Historical logs:** 41 files mention old case numbers, all under `verbatim_dialogue_log/` (bundle12 1, bundle19 1, bundle20 6, bundle21 7, bundle22 1, bundle23 2, bundle29 2, bundle31 1, bundle32 20); 0 are in `safety-checks/`. They are records of past turns, so I left them as they are.

**Cross-check with the trial port** (`spectec/src/temp_port_reference/`). That port was made outside this log, by a patch-based procedure. I compared against it only after my own result compiled, and its records agree with mine everywhere (`evidence/outputs/trial_port_crosscheck.txt`):
- **Files:** all nine NEW files are byte-identical to its `trial_port/`.
- **Edits:** its `patches/edits_73.log` lists the same 73 edits: 56 + 15 renamings and 2 deleted arms. They match one for one by file, kind and text. That log truncates long lines, so the texts were matched as prefixes.
- **Declarations:** its declaration diff `logs/constants_diff_v0_vs_v2.tsv` has the same 43 removed and 12 added declarations as §5. It compares by name, so it names the removed cases by their last numbers (`_case_67`, `_case_73`) rather than by meaning.
- **Warnings, axioms and the audit:** it finds the same warnings, the same axiom counts for `t_preservation` (35), `t_progress` (74), `Step_is_wf` (35) and `Step_read_is_wf` (6), and the same audit result. My dumps give the same four sets in OLD and NEW.
- **Comments:** it flags the same five stale "68" comments.
- **One point where it is out of date.** Its caveat that the falsity of the generated `Step_*` forms "has not been confirmed with a Lean witness" overlooks the bundle 23/29 witness above.

**`lake build`.** I didn't run it, because it writes `.lake/build`.
- That directory predates these changes, so the next `lake build` or editor session rebuilds at least `wasm2.0` and the seven modules that import it, which takes a few minutes.
- `ExtendedDeriveDecEq` is unchanged.
- Until the rebuild, the editor may show errors.

## 9. Method and evidence

Everything is in `claude-logging/verbatim_dialogue_log/bundle33/evidence/`.

**`tools/`:**
- `scan33.py`: finds every affected code reference, by constructor meaning;
- `apply33.py`: applies the 17 edits, asserting each expected line;
- `diff33.py`: the line accounting;
- `EnvDump33.lean`, `envdiff33.py` and `envcat33.py`: the Lean-level comparison;
- `RunAudit33.lean`: the `Inhabited` audit;
- `chain33.sh`, `lrun33.sh` and `check33.sh`: the serial build and the safety checks;
- `IndMeta33.lean` and `Cause33.lean`, analysed by `meta_cause33.py`: the inductive-metadata comparison and the probe of why each proof term changed;
- `AuditCtl33.lean` and `RunAuditCtl33.lean`: the audit's positive control;
- `report33.py`: generates this report. `report33_v1.py` and `report33_v2.py` generated the earlier versions, and `patch_v3*.py` turned v2 into v3;
- `toplevel32.py` and `ctor_map32.py` come from bundle32.

**`outputs/`:**
- the build logs;
- the error logs of the unrepaired modules;
- `diff33_all_changed_lines.tsv`, with all 211 lines;
- the unified diffs `*.diff`;
- the constructor map;
- the declaration dumps `dump_old.tsv.gz` and `dump_new.tsv.gz`, and their comparison `envdiff33.json`/`envcat33.json`;
- the audit outputs, including the positive control (`audit_ctl.txt`);
- the inductive-metadata dumps and their comparison (`indmeta_*.tsv`, `indmeta_diff33.json`), and the cause probe (`cause_new.tsv`, `cause_set.txt`, `cause33.json`);
- `trial_port_crosscheck.txt`.

**`verification/`:** the reports of the independent, read-only verifiers.
- `V-REPORT-1` checked version 1 of this report and raised 17 points.
- Three more checked version 2 (`workflow_reverify_result.json`): `V2-FIX` checked whether those points were resolved, `V2-FRESH` did a fresh refutation, and `V2-CRITIC` looked for completeness. They raised 32 findings.
- None of the 49 points found an error in the repair or in the line accounting. Appendix E says how each was addressed in this version 3.
- Versions 1 and 2 of the report are kept next to the verifier reports.

**A known defect in the build summaries.** The `sorry-warnings=` field of the `chain_*.txt` summaries was counted with the wrong quote character, so it always reads 0. The tool is fixed in `evidence/tools/chain33.sh`, and the counts in §7 are recounted from the logs.
- The only log with such warnings is the first, unrepaired `TypingLemmas` compile: 7 warnings, all from error recovery.
- No final log contains the word `sorry`.

## Appendix A. All 56 changed lines of the model's proofs (§3.4)

The last column is from bundle32's compile of the unrenamed copy (`bundle32/evidence/outputs/compile_verbatim_copy_72_errors.log`, 72 errors on 65 lines; line numbers are NEW's). 40 of the 56 lines failed on the line itself. The other 16 failed on an adjacent line of the same term or `cases`, given as "near L".

| OLD → NEW line | construct | instruction | OLD text → NEW text | error in the unrenamed compile |
|---|---|---|---|---|
| 14712 → 14707 | `iswf_admininstr_VCONST` | `VCONST` | `wf_admininstr.admininstr_case_20 _ _ (by decide) h` → `wf_admininstr.admininstr_case_19 _ _ (by decide) h` | this line |
| 14716 → 14711 | `iswf_admininstr_VCONST_inv` | `VCONST` | `cases h with \| admininstr_case_20 _ _ _ hw => exact hw` → `cases h with \| admininstr_case_19 _ _ _ hw => exact hw` | this line |
| 14727 → 14722 | `Step_pure_is_wf` | `TRAP` | `\| unreachable => exact iswf_Forall_singleton .admininstr_case_73` → `\| unreachable => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14753 → 14748 | `Step_pure_is_wf` | `LABEL_` | `\| admininstr_case_71 _ _ _ hinstrs hbody =>` → `\| admininstr_case_70 _ _ _ hinstrs hbody =>` | this line |
| 14760 → 14755 | `Step_pure_is_wf` | `LABEL_` | `\| admininstr_case_71 _ _ _ _ hbody =>` → `\| admininstr_case_70 _ _ _ _ hbody =>` | this line |
| 14788 → 14783 | `Step_pure_is_wf` | `FRAME_` | `\| admininstr_case_72 _ _ _ _ hbody =>` → `\| admininstr_case_71 _ _ _ _ hbody =>` | this line |
| 14793 → 14788 | `Step_pure_is_wf` | `LABEL_` | `\| admininstr_case_71 _ _ _ _ hbody => exact fun x hx => hbody x (List.mem_append_left _ hx)` → `\| admininstr_case_70 _ _ _ _ hbody => exact fun x hx => hbody x (List.mem_append_left _ hx)` | this line |
| 14794 → 14789 | `Step_pure_is_wf` | `TRAP` | `\| trap_vals => exact iswf_Forall_singleton .admininstr_case_73` → `\| trap_vals => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14795 → 14790 | `Step_pure_is_wf` | `TRAP` | `\| trap_label => exact iswf_Forall_singleton .admininstr_case_73` → `\| trap_label => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14796 → 14791 | `Step_pure_is_wf` | `TRAP` | `\| trap_frame => exact iswf_Forall_singleton .admininstr_case_73` → `\| trap_frame => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14803 → 14798 | `Step_pure_is_wf` | `TRAP` | `\| unop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| unop_trap => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14809 → 14804 | `Step_pure_is_wf` | `TRAP` | `\| binop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| binop_trap => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14820 → 14815 | `Step_pure_is_wf` | `TRAP` | `\| cvtop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| cvtop_trap => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14853 → 14848 | `Step_pure_is_wf` | `TRAP` | `\| vunop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| vunop_trap => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14861 → 14856 | `Step_pure_is_wf` | `TRAP` | `\| vbinop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| vbinop_trap => exact iswf_Forall_singleton .admininstr_case_72` | this line |
| 14963 → 14958 | `Step_pure_is_wf` | `LOCAL_SET` | `exact iswf_Forall_cons hv (iswf_Forall_cons hv (iswf_Forall_singleton (.admininstr_case_44 _ ‹wf_uN 32 x›)))` → `exact iswf_Forall_cons hv (iswf_Forall_cons hv (iswf_Forall_singleton (.admininstr_case_43 _ ‹wf_uN 32 x›)))` | this line |
| 16926 → 16921 | `iswf_store_I32_8` | `STORE` | `wf_admininstr.admininstr_case_57 (some Inn.I32) _ _ _ (some 32)` → `wf_admininstr.admininstr_case_56 (some Inn.I32) _ _ _ (some 32)` | this line |
| 16938 → 16933 | `iswf_load_I32_8_U` | `LOAD` | `wf_admininstr.admininstr_case_56 _ _ _` → `wf_admininstr.admininstr_case_55 _ _ _` | near 16934 |
| 16983 → 16978 | `Step_read_is_wf` | `LABEL_` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ (iswf_Forall_nil _)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ (iswf_Forall_nil _)` | this line |
| 16990 → 16985 | `Step_read_is_wf` | `LABEL_` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _` | near 16986 |
| 17001 → 16996 | `Step_read_is_wf` | `FRAME_` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_72 _ _ _ ‹wf_frame _›` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ ‹wf_frame _›` | this line |
| 17002 → 16997 | `Step_read_is_wf` | `LABEL_` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ (iswf_Forall_nil _)` → `(iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ (iswf_Forall_nil _)` | near 16996 |
| 17009 → 17004 | `Step_read_is_wf` | `LOCAL_GET` | `\| admininstr_case_43 _ hx =>` → `\| admininstr_case_42 _ hx =>` | this line |
| 17015 → 17010 | `Step_read_is_wf` | `GLOBAL_GET` | `\| admininstr_case_46 _ hx =>` → `\| admininstr_case_45 _ hx =>` | this line |
| 17034 → 17029 | `Step_read_is_wf` | `TABLE_FILL` | `\| admininstr_case_52 _ hx =>` → `\| admininstr_case_51 _ hx =>` | this line |
| 17038 → 17033 | `Step_read_is_wf` | `TABLE_SET` | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` | near 17029 |
| 17041 → 17036 | `Step_read_is_wf` | `TABLE_FILL` | `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ hx) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_51 _ hx) (iswf_Forall_nil _)` | near 17029 |
| 17051 → 17046 | `Step_read_is_wf` | `TABLE_COPY` | `\| admininstr_case_53 _ _ hx hy =>` → `\| admininstr_case_52 _ _ hx hy =>` | this line |
| 17056 → 17051 | `Step_read_is_wf` | `TABLE_GET` | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hy) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_47 _ hy) <\|` | near 17046 |
| 17057 → 17052 | `Step_read_is_wf` | `TABLE_SET` | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` | near 17046 |
| 17060 → 17055 | `Step_read_is_wf` | `TABLE_COPY` | `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ _ hx hy) (iswf_Forall_nil _)` | near 17062 |
| 17068 → 17063 | `Step_read_is_wf` | `TABLE_COPY` | `\| admininstr_case_53 _ _ hx hy =>` → `\| admininstr_case_52 _ _ hx hy =>` | this line |
| 17072 → 17067 | `Step_read_is_wf` | `TABLE_GET` | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hy) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_47 _ hy) <\|` | near 17063 |
| 17073 → 17068 | `Step_read_is_wf` | `TABLE_SET` | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\| iswf_Forall_cons hj <\| iswf_Forall_cons hi <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\| iswf_Forall_cons hj <\| iswf_Forall_cons hi <\|` | near 17063 |
| 17075 → 17070 | `Step_read_is_wf` | `TABLE_COPY` | `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ _ hx hy) (iswf_Forall_nil _)` | near 17063 |
| 17084 → 17079 | `Step_read_is_wf` | `TABLE_INIT` | `\| admininstr_case_54 _ _ hx hy =>` → `\| admininstr_case_53 _ _ hx hy =>` | this line |
| 17089 → 17084 | `Step_read_is_wf` | `TABLE_SET` | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` | near 17079 |
| 17092 → 17087 | `Step_read_is_wf` | `TABLE_INIT` | `iswf_Forall_cons (wf_admininstr.admininstr_case_54 _ _ hx hy) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` | near 17079 |
| 17103 → 17098 | `Step_read_is_wf` | `VCONST` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide) ‹wf_uN 128 c›) (iswf_Forall_nil _)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide) ‹wf_uN 128 c›) (iswf_Forall_nil _)` | this line |
| 17107 → 17102 | `Step_read_is_wf` | `VCONST` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` | this line |
| 17114 → 17109 | `Step_read_is_wf` | `VCONST` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` | this line |
| 17121 → 17116 | `Step_read_is_wf` | `VCONST` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` | this line |
| 17127 → 17122 | `Step_read_is_wf` | `VCONST` | `\| admininstr_case_20 _ _ _ hw1 =>` → `\| admininstr_case_19 _ _ _ hw1 =>` | this line |
| 17132 → 17127 | `Step_read_is_wf` | `VCONST` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` | near 17122 |
| 17179 → 17174 | `Step_read_is_wf` | `MEMORY_INIT` | `\| admininstr_case_66 _ hx =>` → `\| admininstr_case_65 _ hx =>` | this line |
| 17185 → 17180 | `Step_read_is_wf` | `MEMORY_INIT` | `iswf_Forall_cons (wf_admininstr.admininstr_case_66 _ hx) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_65 _ hx) (iswf_Forall_nil _)` | near 17174 |
| 17244 → 17239 | `Step_is_wf` | `LABEL_` | `\| admininstr_case_71 _ _ _ hi _ =>` → `\| admininstr_case_70 _ _ _ hi _ =>` | this line |
| 17248 → 17243 | `Step_is_wf` | `LABEL_` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ hi hais') (iswf_Forall_nil _))` → `(iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ hi hais') (iswf_Forall_nil _))` | near 17239 |
| 17257 → 17252 | `Step_is_wf` | `FRAME_` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_72 _ _ _ hf'' hais') (iswf_Forall_nil _))` → `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ hf'' hais') (iswf_Forall_nil _))` | this line |
| 17267 → 17262 | `Step_is_wf` | `LOCAL_SET` | `\| admininstr_case_44 _ hx =>` → `\| admininstr_case_43 _ hx =>` | this line |
| 17274 → 17269 | `Step_is_wf` | `GLOBAL_SET` | `\| admininstr_case_47 _ hx =>` → `\| admininstr_case_46 _ hx =>` | this line |
| 17283 → 17278 | `Step_is_wf` | `TABLE_SET` | `\| admininstr_case_49 _ hx =>` → `\| admininstr_case_48 _ hx =>` | this line |
| 17289 → 17284 | `Step_is_wf` | `TABLE_GROW` | `\| admininstr_case_51 _ hx =>` → `\| admininstr_case_50 _ hx =>` | this line |
| 17303 → 17298 | `Step_is_wf` | `ELEM_DROP` | `\| admininstr_case_55 _ hx =>` → `\| admininstr_case_54 _ hx =>` | this line |
| 17334 → 17329 | `Step_is_wf` | `VCONST` | `\| admininstr_case_20 _ _ hsz hwfc =>` → `\| admininstr_case_19 _ _ hsz hwfc =>` | this line |
| 17364 → 17359 | `Step_is_wf` | `DATA_DROP` | `\| admininstr_case_67 _ hx =>` → `\| admininstr_case_66 _ hx =>` | this line |

## Appendix B. Lean-level lists (§5)

**Only in OLD (43):** `List.match_on_same_ctor._@.wasm2.0.2749490885._hygCtx._hyg.163`, `List.match_on_same_ctor._@.wasm2.0.3401859148._hygCtx._hyg.150`, `List.match_on_same_ctor.het._@.wasm2.0.2749490885._hygCtx._hyg.163`, `List.match_on_same_ctor.het._@.wasm2.0.3401859148._hygCtx._hyg.150`, `TLC.Step_pure__select_preserves_helper._simp_1_59`, `TLC.ai_principal_typing.eq_56`, `TLC.br_reduce_decidable._proof_140`, `TLC.br_reduce_decidable._proof_141`, `TLC.instr_of.eq_74`, `TLC.instr_typing_inversion._proof_1_72`, `TLC.instr_typing_inversion._proof_1_77`, `TLC.return_reduce_decidable._proof_75`, `_private.TypePreservationPure.0.TLC.ai_principal_typing.match_1.eq_56`, `_private.TypePreservationPure.0.TLC.ai_principal_typing.match_1.splitter._sparseCasesOn_60`, `_private.TypingLemmas.0.TLC.instr_of.match_1.eq_74`, `_private.TypingLemmas.0.admininstr_instr.match_1.eq_68`, `admininstr.EXTEND`, `admininstr.EXTEND.elim`, `admininstr.EXTEND.inj`, `admininstr.EXTEND.injEq`, `admininstr.EXTEND.noConfusion`, `admininstr.EXTEND.sizeOf_spec`, `admininstr.decEq._proof_182`, `admininstr.decEq._proof_183`, `admininstr.decEq._proof_184`, `admininstr.match_on_same_ctor._@.wasm2.0.1837273375._hygCtx._hyg.618`, `admininstr.match_on_same_ctor.het._@.wasm2.0.1837273375._hygCtx._hyg.618`, `admininstr_instr.eq_68`, `instr.EXTEND`, `instr.EXTEND.elim`, `instr.EXTEND.inj`, `instr.EXTEND.injEq`, `instr.EXTEND.noConfusion`, `instr.EXTEND.sizeOf_spec`, `instr.decEq._proof_168`, `instr.decEq._proof_169`, `instr.decEq._proof_170`, `instr.match_on_same_ctor._@.wasm2.0.1320104542._hygCtx._hyg.571`, `instr.match_on_same_ctor.het._@.wasm2.0.1320104542._hygCtx._hyg.571`, `wf_admininstr.admininstr_case_19_EXTEND_removed`, `wf_admininstr.below.admininstr_case_19_EXTEND_removed`, `wf_instr.below.instr_case_19_EXTEND_removed`, `wf_instr.instr_case_19_EXTEND_removed`.

**Only in NEW (12):** `List.match_on_same_ctor._@.wasm2.0.2749490885._hygCtx._hyg.161`, `List.match_on_same_ctor._@.wasm2.0.3401859148._hygCtx._hyg.148`, `List.match_on_same_ctor.het._@.wasm2.0.2749490885._hygCtx._hyg.161`, `List.match_on_same_ctor.het._@.wasm2.0.3401859148._hygCtx._hyg.148`, `TLC.Step_pure__select_preserves_helper._simp_1_57`, `TLC.instr_typing_inversion._proof_1_69`, `TLC.instr_typing_inversion._proof_1_75`, `_private.TypePreservationPure.0.TLC.ai_principal_typing.match_1.splitter._sparseCasesOn_59`, `admininstr.match_on_same_ctor._@.wasm2.0.1837273375._hygCtx._hyg.609`, `admininstr.match_on_same_ctor.het._@.wasm2.0.1837273375._hygCtx._hyg.609`, `instr.match_on_same_ctor._@.wasm2.0.1320104542._hygCtx._hyg.562`, `instr.match_on_same_ctor.het._@.wasm2.0.1320104542._hygCtx._hyg.562`.

**User-level theorems whose elaborated proof term changed (115), by module** (a leading `TLC.` is omitted):

- `«wasm2.0»` (9): `Step_is_wf`, `Step_pure_is_wf`, `Step_read_is_wf`, `dataidx_instr_is_wf`, `iswf_I32_const_lt`, `iswf_I32_iadd1`, `iswf_admininstr_VCONST_inv`, `iswf_admininstr_instr`, `iswf_val_of_admininstr`
- `TypingLemmas` (11): `ai_typing_inversion`, `ai_val_principal_typing_inversion`, `ais_single_ref_typing_inversion`, `ais_single_val_typing_inversion`, `construct_ai_maybe`, `injective_admininstr_instr`, `instr_of_admininstr_instr`, `instr_typing_inversion`, `principal_typing_conversion`, `wf_admininstr_instr`, `wf_instr_admininstr`
- `TypePreservationPure` (22): `Step_pure__binop_val_preserves`, `Step_pure__br_if_false_preserves`, `Step_pure__br_if_true_preserves`, `Step_pure__br_succ_preserves`, `Step_pure__br_table_ge_preserves`, `Step_pure__br_table_lt_preserves`, `Step_pure__br_zero_preserves`, `Step_pure__cvtop_val_preserves`, `Step_pure__drop_preserves`, `Step_pure__frame_vals_preserves`, `Step_pure__if_preserves_helper`, `Step_pure__label_vals_preserves`, `Step_pure__local_tee_preserves`, `Step_pure__nop_preserves`, `Step_pure__ref_is_null_false_preserves`, `Step_pure__ref_is_null_helper`, `Step_pure__relop_preserves`, `Step_pure__return_frame_preserves`, `Step_pure__return_label_preserves`, `Step_pure__select_preserves_helper`, `Step_pure__testop_preserves`, `Step_pure__unop_val_preserves`
- `TypePreservation` (38): `ais_elem_drop_inv`, `ais_global_set_inv`, `ais_memory_grow_inv`, `ais_store_mems_inv`, `ais_table_grow_inv`, `ais_table_set_inv`, `inv_data_drop`, `inv_elem_drop`, `inv_global_set`, `inv_local_set`, `inv_memory_grow`, `inv_store_none`, `inv_store_pack`, `inv_table_grow`, `inv_table_set`, `pt_call`, `pt_call_addr`, `pt_call_indirect`, `pt_global_get`, `pt_load_none`, `pt_load_pack`, `pt_local_get`, `pt_memory_copy`, `pt_memory_fill`, `pt_memory_init`, `pt_memory_size`, `pt_ref_func`, `pt_table_copy`, `pt_table_fill`, `pt_table_get`, `pt_table_init`, `pt_table_size`, `t_read_preservation`, `wf_const_num`, `wf_vconst_parts`, `_private.TypePreservation.0.TLC.store_extension_reduce_aux`, `_private.TypePreservation.0.TLC.t_preservation_type_aux`, `_private.TypePreservation.0.TLC.t_preservation_vs_type'_aux`
- `TypeProgress` (35): `br_reduce_extract_vs`, `const_es_exists`, `return_reduce_extract_vs`, `split_vals_inverse`, `split_vals_prefix`, `t_progress_be_binop`, `t_progress_be_br_if`, `t_progress_be_br_table`, `t_progress_be_cvtop`, `t_progress_be_relop`, `t_progress_be_testop`, `t_progress_be_unop`, `t_progress_be_vbinop`, `t_progress_be_vbitmask`, `t_progress_be_vcvtop`, `t_progress_be_vextbinop`, `t_progress_be_vextract_lane`, `t_progress_be_vextunop`, `t_progress_be_vload_lane`, `t_progress_be_vload_pack`, `t_progress_be_vload_splat`, `t_progress_be_vnarrow`, `t_progress_be_vrelop`, `t_progress_be_vreplace_lane`, `t_progress_be_vshiftop`, `t_progress_be_vshuffle`, `t_progress_be_vsplat`, `t_progress_be_vstore_lane`, `t_progress_be_vswizzle`, `t_progress_be_vtestop`, `t_progress_be_vunop`, `t_progress_e_Instr_ok2_frame`, `wf_config_frame`, `wf_config_label`, `wf_forall_admin_val`

**User-level definitions whose elaborated value changed (5):** `TLC.br_reduce_decidable`, `TLC.return_reduce_decidable`, `TLC.ai_principal_typing`, `TLC.instr_of`, `admininstr_instr`.

## Appendix C. All 17 changed lines of the proof modules (§4)

| module | line OLD → NEW | construct | OLD text | NEW text |
|---|---|---|---|---|
| `TypingLemmas` | 131 → — | `instr_of` | `\| admininstr.EXTEND x0 x1 => some (instr.EXTEND x0 x1)` | (deleted) |
| `TypingLemmas` | 454 → — | `ai_principal_typing` | `\| admininstr.EXTEND _ _ => False` | (deleted) |
| `TypingLemmas` | 570 → 568 | `instr_typing_inversion` | `\| instr_case_20 vt v not_none_size wf_vec =>` | `\| instr_case_19 vt v not_none_size wf_vec =>` |
| `TypingLemmas` | 1681 → 1679 | `construct_ai_val` | `have hwfinstr : wf_instr (instr.VCONST vectype.V128 c_t) := wf_instr.instr_case_20 vectype.V128 c_t hsize hwfuN` | `have hwfinstr : wf_instr (instr.VCONST vectype.V128 c_t) := wf_instr.instr_case_19 vectype.V128 c_t hsize hwfuN` |
| `TypingLemmas` | 1747 → 1745 | `construct_ais_trap` | `(Instr_ok2.trap v_S v_C t1s t2s hwfS hwfC wf_admininstr.admininstr_case_73)` | `(Instr_ok2.trap v_S v_C t1s t2s hwfS hwfC wf_admininstr.admininstr_case_72)` |
| `TypePreservationPure` | 1072 → 1072 | `Step_pure__local_tee_preserves` | `\| admininstr_case_45 _ hwfl =>` | `\| admininstr_case_44 _ hwfl =>` |
| `TypePreservationPure` | 1085 → 1085 | `Step_pure__local_tee_preserves` | `have hwfinstr_set : wf_instr (instr.LOCAL_SET v_x) := wf_instr.instr_case_44 v_x hwfl` | `have hwfinstr_set : wf_instr (instr.LOCAL_SET v_x) := wf_instr.instr_case_43 v_x hwfl` |
| `TypePreservation` | 1347 → 1347 | `wf_vconst_parts` | `cases h with \| admininstr_case_20 _ _ h1 h2 => exact ⟨h1, h2⟩` | `cases h with \| admininstr_case_19 _ _ h1 h2 => exact ⟨h1, h2⟩` |
| `TypePreservation` | 2164 → 2164 | `t_read_preservation` | `cases hwfF with \| admininstr_case_72 _ _ _ _ hl => exact hl _ (List.mem_singleton_self _)` | `cases hwfF with \| admininstr_case_71 _ _ _ _ hl => exact hl _ (List.mem_singleton_self _)` |
| `TypeProgress` | 800 → 800 | `wf_forall_admin_val` | `\| val_case_1 vt c hsz hwfc => exact wf_admininstr.admininstr_case_20 vt c hsz hwfc` | `\| val_case_1 vt c hsz hwfc => exact wf_admininstr.admininstr_case_19 vt c hsz hwfc` |
| `TypeProgress` | 801 → 801 | `wf_forall_admin_val` | `\| val_case_2 rt => exact wf_admininstr.admininstr_case_40 rt` | `\| val_case_2 rt => exact wf_admininstr.admininstr_case_39 rt` |
| `TypeProgress` | 802 → 802 | `wf_forall_admin_val` | `\| val_case_3 a => exact wf_admininstr.admininstr_case_68 a` | `\| val_case_3 a => exact wf_admininstr.admininstr_case_67 a` |
| `TypeProgress` | 803 → 803 | `wf_forall_admin_val` | `\| val_case_4 a => exact wf_admininstr.admininstr_case_69 a` | `\| val_case_4 a => exact wf_admininstr.admininstr_case_68 a` |
| `TypeProgress` | 814 → 814 | `wf_forall_admin_val` | `\| admininstr_case_20 _ _ hsz hwfc => exact wf_val.val_case_1 vt c hsz hwfc` | `\| admininstr_case_19 _ _ hsz hwfc => exact wf_val.val_case_1 vt c hsz hwfc` |
| `TypeProgress` | 839 → 839 | `wf_config_label` | `\| admininstr_case_71 _ _ _ hbes hes =>` | `\| admininstr_case_70 _ _ _ hbes hes =>` |
| `TypeProgress` | 856 → 856 | `wf_config_frame` | `\| admininstr_case_72 _ _ _ hwff hes =>` | `\| admininstr_case_71 _ _ _ hwff hes =>` |
| `TypeProgress` | 7784 → 7784 | `t_progress_e_Instr_ok2_frame` | `\| admininstr_case_72 _ _ _ hf hes =>` | `\| admininstr_case_71 _ _ _ hf hes =>` |

## Appendix D. Byte-level facts (§1)

| module | OLD bytes | OLD md5 | NEW bytes | NEW md5 |
|---|---|---|---|---|
| `ExtendedDeriveDecEq.lean` | 36,262 | `e9b33702e9601223b5a4e1dbb8e6f2ad` | 36,262 | `e9b33702e9601223b5a4e1dbb8e6f2ad` |
| `wasm2.0.lean` | 1,332,852 | `4207ecaaae9d5e501ff51ef2fa6b41d5` | 1,332,500 | `fdfafb393a693292cadf089484fcfa86` |
| `HelperLemmas.lean` | 50,710 | `7b0db22807f0243c214a80c92271a3b3` | 50,710 | `7b0db22807f0243c214a80c92271a3b3` |
| `Subtyping.lean` | 35,350 | `4f5c6ca97f91976d2d46e8bf321cbeab` | 35,350 | `4f5c6ca97f91976d2d46e8bf321cbeab` |
| `TypingLemmas.lean` | 105,699 | `6284f02c24b04ab15c9efa95364ef7e2` | 105,607 | `21429230103ffba0fb19da7d0ddcc7f2` |
| `TypePreservationPure.lean` | 119,802 | `13c138409551acf96f0f848923e5a11f` | 119,802 | `ff4fd4773a8e6267f298291c5f07669e` |
| `ExtensionLemmas.lean` | 116,405 | `1e2a23a52276c039a8e8f0b527ecfc0f` | 116,405 | `1e2a23a52276c039a8e8f0b527ecfc0f` |
| `TypePreservation.lean` | 173,658 | `5241649ee2e5699b8096809b4cc03c60` | 173,658 | `4c4bb6a62a90f03f890f3e48c8b03e2d` |
| `TypeProgress.lean` | 449,683 | `8087d55bef5ecafc45080cb3645207d9` | 449,683 | `5e00f3b5530be76c318e126b37cc69c3` |

## Appendix E. Verifier findings and how each was addressed

Each verifier finding (V1 = `V-REPORT-1` on version 1; FIX, FRESH and CRITIC = the three verifiers on version 2) is in `verification/`. None found an error in the repair or in the line accounting. Several found the same point independently; such points are listed once.

| finding | point | how it is addressed in version 3 |
|---|---|---|
| V1-1 | The equation lemmas named as removed were misidentified | §5 Removed now separates the last lemmas of shrinking families (`eq_68`, `eq_74`, `eq_56`) from the renumbered lemmas from each deleted arm onward, whose types changed. |
| V1-2 | §0 axiom claim unqualified | §0 and §5 say "every user-level theorem", and §5 names the 4 numbered auxiliaries that differ. |
| V1-3 | §0 statement claim unqualified | §0 says "user-level" and reports changed terms separately. |
| V1-4, FIX-2 | Category list of the type changes incomplete, then 4 helpers mislabelled | The lists are generated from all categories. The 4 `match_on_same_ctor` helpers present in both builds have their own label. |
| V1-5, FIX-3, CRITIC-11 | "Families shrink by one" imprecise | §5 Removed splits the 43 into 16 for the removed instruction, 15 ends of shrinking families (each with its size OLD → NEW) and 12 renumbered names. |
| V1-6, FIX-1, FRESH-6, CRITIC-11 | "Every number is computed" overstated | The header now says which parts are computed and which are hand-written. §2's match counts are read from the constructor map. |
| V1-7 | `chain33.sh` counted `sorry` warnings with the wrong quotes | The tool is fixed. §7 recounts from the logs, and §9 documents the defect. |
| V1-8, FRESH-8 | Construct counts unlabelled, and their definition | §6 labels each file's count, defines what is counted, and gives the declaration-only count. |
| V1-9 | Line 197 should be 196 | The line numbers in §8 are computed from the NEW files. |
| V1-10 | "~74 cases" comment | Listed in §8 as describing Rocq. |
| V1-11 | "four kinds" for three | Now "three kinds". |
| V1-12 | Shell output inside an error cell | The `/usr/bin/time` lines are stripped. |
| V1-13 | Wrong footnote on the error column | Rewritten as "How to read the error column". |
| V1-14 | `TypePreservation:2024` is not a status note | It is now described as a docstring about `Step_read_is_wf`'s history. |
| V1-15 | `TLC.` dropped from private names | Only a leading `TLC.` is omitted. |
| V1-16, CRITIC-10 | Lake rebuild scope; no Lake build of either state | §8 says "at least `wasm2.0` and the seven modules that import it". §7 says neither state has a Lake build, and why the bare-`lean` builds should match. |
| V1-17 | Audit module set unnamed | §5 names the excluded module and the instances made opaque. |
| FIX-4 | "its 17 points are fixed" overstated | §9 rewritten, and this appendix added. |
| FIX-5 | Only the TypingLemmas rows come from the second compile | Corrected in §4.2. |
| FIX-6, FRESH-1, FRESH-3, CRITIC-7 | Documentation claim false; historical logs not in `safety-checks/` | §8 lists the `digest_wasm_v.md` lines, which describe Rocq's `wasm.v`, and counts the historical files per bundle (0 in `safety-checks/`). |
| FIX-7, FRESH-5 | Control module "never in the repo"; files in the wrong list | Reworded, and §9 lists `AuditCtl33.lean` and `RunAuditCtl33.lean` under `tools/`. |
| FIX-8, FRESH-10 | "67 of 67" counts NEW cases | Reworded: every OLD case except case 19 matched. |
| FRESH-2 | The merge's `$fzero` hint removal is not mentioned | §0 and §2 name commit `5d6980fef` and say why it does not contribute. |
| FRESH-4, CRITIC-6 | Re-stated theorems: three changes, witness not cited, file not named | §8 lists the three changes, names the generator output and its md5, cites the bundle 23/29 witness, says it was not re-run on NEW, and notes the trial port's outdated caveat. |
| FRESH-7, CRITIC-14 | Memory peak; warning kinds; info output; audit wording | §7 gives compile and probe peaks, every warning kind and the info output, and states that the logs are identical. §5 states exactly which instances the audit makes opaque. |
| FRESH-9 | Cross-check matched by prefix | §8 says so. |
| CRITIC-1 | The 15 proof-module lines not shown as text | Appendix C gives all 17 lines in full. |
| CRITIC-2 | Statement check is name-level; inductive contents not compared | §0 explains why name-level equality is enough here, and §5 adds the inductive-metadata comparison. |
| CRITIC-3 | No per-module or per-kind totals | Tables added in §5, and the 3 generated theorems that changed value but not type are listed. |
| CRITIC-4 | Hash method under-described; constructor-index shift not stated | §5 Method gives the hash width and what it ignores. The metadata comparison shows the index shift and what it explains. |
| CRITIC-5 | Cause of the changed terms asserted, not checked | The cause probe in §5: 120 of 120 changed user-level declarations refer to a changed declaration, and none of the unchanged ones do. §5 also explains which edited theorems keep their terms. |
| CRITIC-8 | No byte-level facts | §1 "Bytes" and Appendix D. |
| CRITIC-9 | Comments citing model line numbers | Table in §8. |
| CRITIC-12 | HEAD contents of the two non-module files | The header gives their lines and md5. |
| CRITIC-13 | Appendix A lacks instructions and evidence of necessity | Instruction column, plus the bundle32 compile column. |
