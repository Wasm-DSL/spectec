# Old vs new: the `EXTEND` removal across the model and the proof

Bundle 33, 2026-11-11. Compares two complete states of `spectec/src/test-lean-claude/`:

- **OLD**: the old proof together with `OLD_wasm2.0.lean`, the model that still has `EXTEND`. This is HEAD `afb06bf8d`: its `wasm2.0.lean` is byte-identical to `OLD_wasm2.0.lean`.
- **NEW**: the new proof together with `wasm2.0.lean`, i.e. the files now in the working tree. The model is the bundle32 port; the proof modules are as repaired this turn.

| module | OLD md5 | NEW md5 | lines OLD → NEW |
|---|---|---|---|
| `ExtendedDeriveDecEq.lean` | `e9b33702…` | `e9b33702…` (same) | 738 → 738 |
| `wasm2.0.lean` | `4207ecaa…` | `fdfafb39…` | 17,527 → 17,522 |
| `HelperLemmas.lean` | `7b0db228…` | `7b0db228…` (same) | 1,041 → 1,041 |
| `Subtyping.lean` | `4f5c6ca9…` | `4f5c6ca9…` (same) | 680 → 680 |
| `TypingLemmas.lean` | `6284f02c…` | `21429230…` | 1,956 → 1,954 |
| `TypePreservationPure.lean` | `13c13840…` | `ff4fd477…` | 1,974 → 1,974 |
| `ExtensionLemmas.lean` | `1e2a23a5…` | `1e2a23a5…` (same) | 2,172 → 2,172 |
| `TypePreservation.lean` | `5241649e…` | `4c4bb6a6…` | 2,912 → 2,912 |
| `TypeProgress.lean` | `8087d55b…` | `5e00f3b5…` | 8,248 → 8,248 |

OLD's `wasm2.0.lean` is `OLD_wasm2.0.lean`; NEW's is `wasm2.0.lean`. All counts and tables below are generated from the files and from Lean, by the scripts listed in §9.

## 0. Bottom line

- **One cause.** The mech-backend merge deleted one line of the Wasm 2.0 spec: the dead instruction `EXTEND numtype n`. Every difference below follows from that.
- **Text.** 211 lines of OLD differ from NEW: 194 in the model and 17 in the proof modules. Every one falls into four kinds, and none is unexplained:
  - 7 lines deleted, because they mention the removed constructor: 5 in the model and 2 match arms in `TypingLemmas`.
  - 173 lines renumber a well-formedness constructor name, `instr_case_K`/`admininstr_case_K` → K−1 for K ≥ 20:
    - 102 in the generated model;
    - 56 in the model's proofs (the bundle32 port);
    - 15 in the proof modules.
  - 31 generated comments cite a spec position, and that position moves up one line.
- **Structure.** No top-level construct was added, removed, renamed or reordered in any of the nine files. The 1,869 constructs match OLD one for one. 53 of them have changed text: 24 in code and 29 only in their source-position comment.
- **Statements.** No theorem, definition or inductive type changed its statement. This is checked in Lean, by comparing all 12,775 declarations common to both builds, with the constructor numbers mapped (§5).
  - The constructor `EXTEND` itself is gone, from `instr` and `admininstr`, together with its two well-formedness cases.
  - The only other declarations that changed are ones Lean generates automatically.
- **Soundness.** Both states compile with 0 errors and 0 `sorry`, and no theorem depends on `sorryAx`.
  - Every theorem present in both has the same axioms. `t_preservation` has 35 and `t_progress` 74, the same lists as before.
  - The `Inhabited`-default audit finds no theorem needing a default: 0 of 5,517 (OLD) and 0 of 5,496 (NEW).
  - The warnings are the same 171 messages in both.

## 1. Line-level summary

| file | lines OLD → NEW | deleted (`EXTEND`) | constructor renumbered | spec position comment | total OLD lines differing |
|---|---|---|---|---|---|
| `ExtendedDeriveDecEq.lean` | 738 → 738 | 0 | 0 | 0 | 0 |
| `wasm2.0.lean` | 17,527 → 17,522 | 5 | 158 (102 generated + 56 hand layer) | 31 | 194 |
| `HelperLemmas.lean` | 1,041 → 1,041 | 0 | 0 | 0 | 0 |
| `Subtyping.lean` | 680 → 680 | 0 | 0 | 0 | 0 |
| `TypingLemmas.lean` | 1,956 → 1,954 | 2 | 3 | 0 | 5 |
| `TypePreservationPure.lean` | 1,974 → 1,974 | 0 | 2 | 0 | 2 |
| `ExtensionLemmas.lean` | 2,172 → 2,172 | 0 | 0 | 0 | 0 |
| `TypePreservation.lean` | 2,912 → 2,912 | 0 | 2 | 0 | 2 |
| `TypeProgress.lean` | 8,248 → 8,248 | 0 | 8 | 0 | 8 |
| **total** | | 7 | 173 | 31 | **211** |

How the lines were matched:
- From each OLD file, delete the lines that mention the removed constructor (§3.1, §4.1).
- The remaining lines then align one for one with the NEW file, which has exactly the same length.
- Each differing pair is classified by the rule that maps it, so no line-matching heuristic is involved. 0 pairs are left unexplained.
- Four modules are byte-identical in OLD and NEW: `ExtendedDeriveDecEq`, `HelperLemmas`, `Subtyping` and `ExtensionLemmas`.

## 2. The cause

**The spec change.** mech-backend commit `28073cddd` ("Remove extend instruction") deleted line 474 of `specification/wasm-2.0/1-syntax.spectec`:
```
  | EXTEND numtype n                 hint(show %.EXTEND#%#_#S)
```
**No other generator change matters.** In bundle32 the HEAD generator was run on the spec with only that line restored. It reproduced the old generated base byte for byte. So the merge's other generator changes have no effect on the Wasm 2.0 Lean output: the ImproveIds name-clash fix, the Sideconditions let-reordering and DefToRel's `hint(axiom)`. (Evidence: `bundle32/evidence/outputs/generator_check.txt`.)

**What the instruction was.** In Wasm 2.0 terms, `instr.EXTEND numtype n` was a dead production. In OLD:
- it is mentioned only by the five generated lines of §3.1 and by two match arms in `TypingLemmas`;
- no validation rule mentions it. `Instr_ok` has 73 rules in both versions;
- no reduction rule mentions it. `Step_pure`, `Step_read` and `Step` have 54, 47 and 23 rules in both versions.

**The real extension instructions are unaffected.** They live under other constructors, all unchanged:
- `i32.extend8_s` and the like are `UNOP` with `unop_Inn.EXTEND n`;
- `i64.extend_i32_s/u` is `CVTOP` with `cvtop__Inn_1_Inn_2.EXTEND sx`;
- the SIMD extensions are `VCVTOP` with `vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND half sx`.

**Why so many names moved.** The backend names the constructors of the generated well-formedness predicates by position. The K-th constructor (from 0) of `wf_instr` is `instr_case_K`, and likewise `admininstr_case_K` for `wf_admininstr`. `EXTEND` was constructor 19 of both `instr` and `admininstr`, so every later case moved down by one:
- `wf_instr`: 68 → 67 cases;
- `wf_admininstr`: 74 → 73 cases.

The two predicates share numbering for K ≤ 67. The six administrative-only instructions are `admininstr_case_68`–`73` in OLD.
The renaming was done by meaning, not by arithmetic. Each OLD constructor was matched to the NEW constructor with an identical text: arguments, premises and conclusion. Every case was matched uniquely (67 of 67 and 73 of 73), with nothing ambiguous and nothing unmatched.

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

Each line declares one constructor of `wf_instr` or `wf_admininstr`. Only the name changed; the rest of each declaration is identical. The full map, with the instruction each case is about:

| OLD → NEW | instruction | in `wf_instr` | in `wf_admininstr` |
|---|---|---|---|
| `*_case_0` … `*_case_18` | (unchanged) | 19 cases, same names | 19 cases, same names |
| `*_case_19` | **`EXTEND`, deleted** (§3.1) | OLD line 2062 | OLD line 12409 |
| `_case_20` → `_case_19` | `VCONST` | line 2063 → 2061 | line 12410 → 12405 |
| `_case_21` → `_case_20` | `VVUNOP` | line 2067 → 2065 | line 12414 → 12409 |
| `_case_22` → `_case_21` | `VVBINOP` | line 2068 → 2066 | line 12415 → 12410 |
| `_case_23` → `_case_22` | `VVTERNOP` | line 2069 → 2067 | line 12416 → 12411 |
| `_case_24` → `_case_23` | `VVTESTOP` | line 2070 → 2068 | line 12417 → 12412 |
| `_case_25` → `_case_24` | `VUNOP` | line 2071 → 2069 | line 12418 → 12413 |
| `_case_26` → `_case_25` | `VBINOP` | line 2075 → 2073 | line 12422 → 12417 |
| `_case_27` → `_case_26` | `VTESTOP` | line 2079 → 2077 | line 12426 → 12421 |
| `_case_28` → `_case_27` | `VRELOP` | line 2083 → 2081 | line 12430 → 12425 |
| `_case_29` → `_case_28` | `VSHIFTOP` | line 2087 → 2085 | line 12434 → 12429 |
| `_case_30` → `_case_29` | `VBITMASK` | line 2091 → 2089 | line 12438 → 12433 |
| `_case_31` → `_case_30` | `VSWIZZLE` | line 2094 → 2092 | line 12441 → 12436 |
| `_case_32` → `_case_31` | `VSHUFFLE` | line 2098 → 2096 | line 12445 → 12440 |
| `_case_33` → `_case_32` | `VSPLAT` | line 2103 → 2101 | line 12450 → 12445 |
| `_case_34` → `_case_33` | `VEXTRACT_LANE` | line 2106 → 2104 | line 12453 → 12448 |
| `_case_35` → `_case_34` | `VREPLACE_LANE` | line 2112 → 2110 | line 12459 → 12454 |
| `_case_36` → `_case_35` | `VEXTUNOP` | line 2116 → 2114 | line 12463 → 12458 |
| `_case_37` → `_case_36` | `VEXTBINOP` | line 2121 → 2119 | line 12468 → 12463 |
| `_case_38` → `_case_37` | `VNARROW` | line 2126 → 2124 | line 12473 → 12468 |
| `_case_39` → `_case_38` | `VCVTOP` | line 2133 → 2131 | line 12480 → 12475 |
| `_case_40` → `_case_39` | `REF_NULL` | line 2138 → 2136 | line 12485 → 12480 |
| `_case_41` → `_case_40` | `REF_FUNC` | line 2139 → 2137 | line 12486 → 12481 |
| `_case_42` → `_case_41` | `REF_IS_NULL` | line 2142 → 2140 | line 12489 → 12484 |
| `_case_43` → `_case_42` | `LOCAL_GET` | line 2143 → 2141 | line 12490 → 12485 |
| `_case_44` → `_case_43` | `LOCAL_SET` | line 2146 → 2144 | line 12493 → 12488 |
| `_case_45` → `_case_44` | `LOCAL_TEE` | line 2149 → 2147 | line 12496 → 12491 |
| `_case_46` → `_case_45` | `GLOBAL_GET` | line 2152 → 2150 | line 12499 → 12494 |
| `_case_47` → `_case_46` | `GLOBAL_SET` | line 2155 → 2153 | line 12502 → 12497 |
| `_case_48` → `_case_47` | `TABLE_GET` | line 2158 → 2156 | line 12505 → 12500 |
| `_case_49` → `_case_48` | `TABLE_SET` | line 2161 → 2159 | line 12508 → 12503 |
| `_case_50` → `_case_49` | `TABLE_SIZE` | line 2164 → 2162 | line 12511 → 12506 |
| `_case_51` → `_case_50` | `TABLE_GROW` | line 2167 → 2165 | line 12514 → 12509 |
| `_case_52` → `_case_51` | `TABLE_FILL` | line 2170 → 2168 | line 12517 → 12512 |
| `_case_53` → `_case_52` | `TABLE_COPY` | line 2173 → 2171 | line 12520 → 12515 |
| `_case_54` → `_case_53` | `TABLE_INIT` | line 2177 → 2175 | line 12524 → 12519 |
| `_case_55` → `_case_54` | `ELEM_DROP` | line 2181 → 2179 | line 12528 → 12523 |
| `_case_56` → `_case_55` | `LOAD` | line 2184 → 2182 | line 12531 → 12526 |
| `_case_57` → `_case_56` | `STORE` | line 2188 → 2186 | line 12535 → 12530 |
| `_case_58` → `_case_57` | `VLOAD` | line 2197 → 2195 | line 12544 → 12539 |
| `_case_59` → `_case_58` | `VLOAD_LANE` | line 2201 → 2199 | line 12548 → 12543 |
| `_case_60` → `_case_59` | `VSTORE` | line 2206 → 2204 | line 12553 → 12548 |
| `_case_61` → `_case_60` | `VSTORE_LANE` | line 2209 → 2207 | line 12556 → 12551 |
| `_case_62` → `_case_61` | `MEMORY_SIZE` | line 2214 → 2212 | line 12561 → 12556 |
| `_case_63` → `_case_62` | `MEMORY_GROW` | line 2215 → 2213 | line 12562 → 12557 |
| `_case_64` → `_case_63` | `MEMORY_FILL` | line 2216 → 2214 | line 12563 → 12558 |
| `_case_65` → `_case_64` | `MEMORY_COPY` | line 2217 → 2215 | line 12564 → 12559 |
| `_case_66` → `_case_65` | `MEMORY_INIT` | line 2218 → 2216 | line 12565 → 12560 |
| `_case_67` → `_case_66` | `DATA_DROP` | line 2221 → 2219 | line 12568 → 12563 |
| `_case_68` → `_case_67` | `REF_FUNC_ADDR` | — | line 12571 → 12566 |
| `_case_69` → `_case_68` | `REF_HOST_ADDR` | — | line 12572 → 12567 |
| `_case_70` → `_case_69` | `CALL_ADDR` | — | line 12573 → 12568 |
| `_case_71` → `_case_70` | `LABEL_` | — | line 12574 → 12569 |
| `_case_72` → `_case_71` | `FRAME_` | — | line 12578 → 12573 |
| `_case_73` → `_case_72` | `TRAP` | — | line 12582 → 12577 |

48 `wf_instr` lines + 54 `wf_admininstr` lines = 102. No other generated line refers to these constructors.

### 3.3 Source-position comments (31 lines)

The generator heads some constructs with a comment that gives the spec position they come from. Every `1-syntax.spectec:L.c` with L ≥ 475 now reads L−1, because one spec line above it was deleted. The 31 affected comments head these constructs, listed with OLD → NEW line:

`instr` (1932→1932), `wf_instr` (2006→2005), `expr` (2226→2224), `elemmode` (2229→2227), `wf_elemmode` (2238→2236), `datamode` (2248→2246), `wf_datamode` (2256→2254), `type` (2265→2263), `«local»` (2270→2268), `func` (2275→2273), `wf_func` (2282→2280), `global` (2290→2288), `wf_global` (2297→2295), `table` (2304→2302), `wf_table` (2309→2307), `mem` (2316→2314), `wf_mem` (2321→2319), `elem` (2328→2326), `wf_elem` (2335→2333), `data` (2343→2341), `wf_data` (2350→2348), `start` (2358→2356), `wf_start` (2363→2361), `externidx` (2370→2368), `wf_externidx` (2378→2376), `«export»` (2394→2392), `wf_export` (2399→2397), `«import»` (2407→2405), `wf_import` (2412→2410), `module` (2421→2419), `wf_module` (2428→2426).

Example (`instr`): `/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:552.1-553.22 -/` → `/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.1-552.22 -/`.

### 3.4 The model's proofs: renumbered references (56 lines)

These are the deviations of the bundle32 port. Every one renames a `wf_admininstr` constructor inside a proof body; no statement changed. They are logged line by line in `bundle32/user_requested_documents/deviations_in_copying.md` and listed again in Appendix A.

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

Line numbers are OLD → NEW. The error column shows what Lean reports for the OLD line against the NEW model. Each module was compiled with the earlier modules already repaired.

### 4.1 Deleted: two match arms on the removed constructor

| module | OLD line | construct | deleted line | why |
|---|---|---|---|---|
| `TypingLemmas` | 131 | `def instr_of` | `\| admininstr.EXTEND x0 x1 => some (instr.EXTEND x0 x1)` | `instr_of : admininstr → Option instr` is the partial inverse of `admininstr_instr`, from Rocq `typing_lemmas.v:124`. It has one arm per `admininstr` constructor (74 in OLD, 73 in NEW); the `EXTEND` arm no longer type-checks. Lean: "Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`" |
| `TypingLemmas` | 454 | `def ai_principal_typing` | `\| admininstr.EXTEND _ _ => False` | `ai_principal_typing` gives the principal type of an administrative instruction. Its `EXTEND` arm said `False`. With the constructor gone, the arm is an invalid pattern. Lean: "Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`" |

### 4.2 Renumbered constructor references (15 lines)

| module | line OLD → NEW | construct | change | instruction | role of the line | error without the change |
|---|---|---|---|---|---|---|
| `TypePreservation` | 1347 → 1347 | `wf_vconst_parts` | `admininstr_case_20` → `admininstr_case_19` | `VCONST` | Destructs `wf_admininstr (VCONST vt c)` into its two premises. | Too many variable names provided at alternative `admininstr_case_20`: 4 provided, but 2 expected / Alternative `admininstr_case_20` is not needed / Alternative `admininstr_case_19` has not been provided |
| `TypePreservation` | 2164 → 2164 | `t_read_preservation` | `admininstr_case_72` → `admininstr_case_71` | `FRAME_` | Preservation of `Step_read`, `call_addr` case (a function call becomes `FRAME_ n f [LABEL_ n [] body]`). It destructs the well-formedness of that `FRAME_` to reach the `LABEL_` inside. | Too many variable names provided at alternative `admininstr_case_72`: 5 provided, but 0 expected / Alternative `admininstr_case_72` is not needed / Alternative `admininstr_case_71` has not been provided Command exited with non-zero status 1 |
| `TypePreservationPure` | 1072 → 1072 | `Step_pure__local_tee_preserves` | `admininstr_case_45` → `admininstr_case_44` | `LOCAL_TEE` | Preservation for `local.tee x` ↪ `val val local.set x`. It destructs `wf_admininstr (LOCAL_TEE x)` and builds `wf_instr (LOCAL_SET x)`. | Alternative `admininstr_case_45` is not needed |
| `TypePreservationPure` | 1085 → 1085 | `Step_pure__local_tee_preserves` | `instr_case_44` → `instr_case_43` | `LOCAL_SET` | Preservation for `local.tee x` ↪ `val val local.set x`. It destructs `wf_admininstr (LOCAL_TEE x)` and builds `wf_instr (LOCAL_SET x)`. | Type mismatch wf_instr.instr_case_44 v_x hwfl has type wf_instr (instr.LOCAL_TEE v_x) but is expected to have type wf_instr (instr.LOCAL_SET v_x) |
| `TypeProgress` | 800 → 800 | `wf_forall_admin_val` | `admininstr_case_20` → `admininstr_case_19` | `VCONST` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Application type mismatch: The argument c has type vec_ but is expected to have type vvunop in the application wf_admininstr.admininstr_case_20 vt c |
| `TypeProgress` | 801 → 801 | `wf_forall_admin_val` | `admininstr_case_40` → `admininstr_case_39` | `REF_NULL` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Application type mismatch: The argument rt has type reftype but is expected to have type funcidx in the application wf_admininstr.admininstr_case_40 rt |
| `TypeProgress` | 802 → 802 | `wf_forall_admin_val` | `admininstr_case_68` → `admininstr_case_67` | `REF_FUNC_ADDR` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Type mismatch wf_admininstr.admininstr_case_68 a has type wf_admininstr (admininstr.REF_HOST_ADDR a) but is expected to have type wf_admininstr (admininstr_val (val.REF_FUNC_ADDR a)) |
| `TypeProgress` | 803 → 803 | `wf_forall_admin_val` | `admininstr_case_69` → `admininstr_case_68` | `REF_HOST_ADDR` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Type mismatch wf_admininstr.admininstr_case_69 a has type wf_admininstr (admininstr.CALL_ADDR a) but is expected to have type wf_admininstr (admininstr_val (val.REF_HOST_ADDR a)) |
| `TypeProgress` | 814 → 814 | `wf_forall_admin_val` | `admininstr_case_20` → `admininstr_case_19` | `VCONST` | Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`. | Too many variable names provided at alternative `admininstr_case_20`: 4 provided, but 2 expected / Alternative `admininstr_case_20` is not needed |
| `TypeProgress` | 839 → 839 | `wf_config_label` | `admininstr_case_71` → `admininstr_case_70` | `LABEL_` | Rocq `type_progress.v:857`. It destructs `wf_admininstr (LABEL_ n bes es)`. | Alternative `admininstr_case_71` is not needed |
| `TypeProgress` | 856 → 856 | `wf_config_frame` | `admininstr_case_72` → `admininstr_case_71` | `FRAME_` | Rocq `type_progress.v:870`. It destructs `wf_admininstr (FRAME_ n f es)`. | Too many variable names provided at alternative `admininstr_case_72`: 5 provided, but 0 expected / Alternative `admininstr_case_72` is not needed |
| `TypeProgress` | 7784 → 7784 | `t_progress_e_Instr_ok2_frame` | `admininstr_case_72` → `admininstr_case_71` | `FRAME_` | Progress, frame case. The body is well formed under the inner frame, by destructing `wf_admininstr (FRAME_ …)`. | Too many variable names provided at alternative `admininstr_case_72`: 5 provided, but 0 expected / Alternative `admininstr_case_72` is not needed |
| `TypingLemmas` | 570 → 568 | `instr_typing_inversion` | `instr_case_20` → `instr_case_19` | `VCONST` | Inverts `Instr_ok` into the principal type. The `vconst` case destructs `wf_instr (VCONST …)`. | Too many variable names provided at alternative `instr_case_20`: 4 provided, but 2 expected / Alternative `instr_case_20` is not needed |
| `TypingLemmas` | 1681 → 1679 | `construct_ai_val` | `instr_case_20` → `instr_case_19` | `VCONST` | Types a value as an administrative instruction. The vector case builds `wf_instr (VCONST V128 c)`. | Application type mismatch: The argument c_t has type vec_ but is expected to have type vvunop in the application wf_instr.instr_case_20 vectype.V128 c_t |
| `TypingLemmas` | 1747 → 1745 | `construct_ais_trap` | `admininstr_case_73` → `admininstr_case_72` | `TRAP` | `TRAP` has every type. It needs `wf_admininstr TRAP`. | Unknown constant `wf_admininstr.admininstr_case_73` |

Where two OLD lines are listed, Lean also reports the neighbouring missing alternative: "Alternative `…_{K−1}` has not been provided". The error for `TypePreservationPure` line 1085 only shows once line 1072 is fixed, because it sits inside that alternative: "Type mismatch: `wf_instr.instr_case_44 v_x hwfl` has type `wf_instr (instr.LOCAL_TEE v_x)` but is expected to have type `wf_instr (instr.LOCAL_SET v_x)`".

In the `TypingLemmas` run behind this table, only the two arms of §4.1 had been deleted, so its line numbers are already the NEW ones. In the first compile of the unrepaired module, the two invalid patterns made `instr_of` and `ai_principal_typing` fail. That cascaded into 80 errors, including the `rfl` failures in `instr_of_admininstr_instr`, and hid line 570 (`instr_typing_inversion` became a `sorry` declaration).

Nothing else in the four modules mentions a renumbered constructor or the removed one. The other two `EXTEND` tokens in `TypeProgress` (lines 3496 and 3705) are the SIMD conversion `vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND`, which still exists.

## 5. Lean-level comparison (elaborated declarations)

**How.** Both builds were loaded in Lean, and every declaration of the nine modules was dumped with three things: a hash of its type, a hash of its value (both ignore binder names) and, for theorems, its axioms. In the OLD dump the constructors `wf_instr.instr_case_K` and `wf_admininstr.admininstr_case_K` with K ≥ 20 were first renamed to K−1, together with the same constructors of their `.below`, and the removed case was marked. The comparison is therefore by meaning.

**Totals.**
- OLD has 12,818 declarations (5,526 theorems); NEW has 12,787 (5,505 theorems).
- 12,775 are common to both.
- 43 are only in OLD and 12 only in NEW.

- **Removed (43).**
  - User-visible (4): `instr.EXTEND`, `admininstr.EXTEND`, and the `EXTEND` cases of `wf_instr` and `wf_admininstr`.
  - The rest are generated by Lean: the removed constructors' `elim`/`inj`/`injEq`/`noConfusion`/`sizeOf_spec`, their `.below` cases, the `DecidableEq` sub-proofs, and the equation lemma for the deleted arm of `admininstr_instr`, `instr_of` and `ai_principal_typing` (`eq_68`, `eq_74`, `eq_56`).
  - Also removed are trailing members of numbered auxiliary families (`_proof_N`, `_simp_N`, `match_N.eq_N`) and of hygienic helper names, which shrink by one. By category: 10 auto-generated lemmas/eliminators of the removed constructor; 8 derived-instance helpers with hygienic names (counter shifted); 6 derived DecidableEq auxiliary proofs (numbered per constructor); 5 auxiliary proof terms (numbered per declaration); 4 pattern-matching auxiliaries (matchers, splitters, their equations); 4 the removed EXTEND case of wf_instr / wf_admininstr (or of its .below); 3 equation lemmas of definitions by pattern matching (one per arm, numbered); 2 the removed constructor itself; 1 auxiliary simp lemmas (numbered). Full list in Appendix B.
- **Added (12).** All are renumbered auxiliaries: hygienic name counters, and auxiliary proof and simp lemma numbering. No new user-level declaration and no new axiom. 8 derived-instance helpers with hygienic names (counter shifted); 2 auxiliary proof terms (numbered per declaration); 1 auxiliary simp lemmas (numbered); 1 pattern-matching auxiliaries (matchers, splitters, their equations).
- **Statements: none changed.** No user-level theorem, definition, inductive type or constructor has a different type. The 724 theorems, 124 definitions and 8 recursors with a different type are all generated by Lean:
  - recursors and case eliminators of the four changed inductives, which have one minor premise fewer;
  - per-constructor `X.CTOR.elim` of the constructors after `EXTEND`;
  - positionally numbered equation lemmas, matcher and splitter auxiliaries;
  - `DecidableEq` sub-proofs.
- **Definitions whose elaborated value changed (168; 5 user-level).**
  - `admininstr_instr`, `instr_of` and `ai_principal_typing` each lost their `EXTEND` arm.
  - `br_reduce_decidable` and `return_reduce_decidable` (`TypeProgress`) have unchanged source, but they case-split on an `admininstr` with a `| _ =>` wildcard, so their terms now have one case fewer.
  - The rest are derived or auxiliary: 102 per-constructor eliminators X.CTOR.elim of the changed inductives; 28 recursors / case eliminators / structural-recursion helpers / no-confusion of the changed inductives; 14 derived DecidableEq / BEq; 11 pattern-matching auxiliaries (matchers, splitters, their equations); 4 derived SizeOf; 4 derived-instance helpers with hygienic names (counter shifted).
- **Proof terms that changed: 115 user-level theorems** (list in Appendix B). Most have unchanged source. Their proofs destruct an `instr`/`admininstr` or its well-formedness, or run a tactic over every case, and that now produces one case fewer.
  - Of the 17 theorems edited in §3.4 and §4.2, these 5 have the same proof term as before once constructor numbers are mapped: `construct_ai_val`, `construct_ais_trap`, `iswf_admininstr_VCONST`, `iswf_load_I32_8_U`, `iswf_store_I32_8`.
  - The edits in these theorems were pure renamings.
- **Axioms: unchanged.**
  - Every theorem present in both builds has the same set of axioms.
  - The only 4 differences are numbered auxiliaries, `br_reduce_decidable._proof_81/82/120/124`, whose numbers now point at other sub-proofs.
  - `TLC.t_preservation` uses 35 axioms: `propext`, `Classical.choice`, `Quot.sound` and 32 of the model's `*_is_wf` axioms.
  - `TLC.t_progress` uses 74: the same three, 56 `*_is_wf` axioms and 15 project axioms from Rocq's `axioms.v`.
  - Both lists are identical in OLD and NEW, and no theorem depends on `sorryAx` in either.
- **`Inhabited` defaults.** This is the kernel replay of all eight project modules with every `Inhabited` instance opaque.
  - OLD: 0 of 5,517 theorems need a default value.
  - NEW: 0 of 5,496 theorems need one.
  - The difference of 21 theorems is exactly the removed minus the added theorems above.

## 6. Every top-level construct whose text changed

All nine files have the same top-level constructs in the same order in OLD and NEW: 897, 24, 118, 52, 97, 85, 135, 143 and 318. The 53 constructs with changed text:

| file | construct | change |
|---|---|---|
| `wasm2.0` | `inductive instr` | line(s) mentioning `EXTEND` deleted (1); spec position in the header comment (1) |
| `wasm2.0` | `inductive wf_instr` | line(s) mentioning `EXTEND` deleted (1); spec position in the header comment (1); constructor declarations renumbered (48) |
| `wasm2.0` | `inductive admininstr` | line(s) mentioning `EXTEND` deleted (1) |
| `wasm2.0` | `def admininstr_instr` | line(s) mentioning `EXTEND` deleted (1) |
| `wasm2.0` | `inductive wf_admininstr` | line(s) mentioning `EXTEND` deleted (1); constructor declarations renumbered (54) |
| `wasm2.0` | `theorem iswf_admininstr_VCONST` | constructor references renumbered in the proof (1) |
| `wasm2.0` | `theorem iswf_admininstr_VCONST_inv` | constructor references renumbered in the proof (1) |
| `wasm2.0` | `theorem Step_pure_is_wf` | constructor references renumbered in the proof (14) |
| `wasm2.0` | `theorem iswf_store_I32_8` | constructor references renumbered in the proof (1) |
| `wasm2.0` | `theorem iswf_load_I32_8_U` | constructor references renumbered in the proof (1) |
| `wasm2.0` | `theorem Step_read_is_wf` | constructor references renumbered in the proof (28) |
| `wasm2.0` | `theorem Step_is_wf` | constructor references renumbered in the proof (10) |
| `TypingLemmas` | `def instr_of` | line(s) mentioning `EXTEND` deleted (1) |
| `TypingLemmas` | `def ai_principal_typing` | line(s) mentioning `EXTEND` deleted (1) |
| `TypingLemmas` | `theorem instr_typing_inversion` | constructor references renumbered in the proof (1) |
| `TypingLemmas` | `theorem construct_ai_val` | constructor references renumbered in the proof (1) |
| `TypingLemmas` | `theorem construct_ais_trap` | constructor references renumbered in the proof (1) |
| `TypePreservationPure` | `theorem Step_pure__local_tee_preserves` | constructor references renumbered in the proof (2) |
| `TypePreservation` | `theorem wf_vconst_parts` | constructor references renumbered in the proof (1) |
| `TypePreservation` | `theorem t_read_preservation` | constructor references renumbered in the proof (1) |
| `TypeProgress` | `theorem wf_forall_admin_val` | constructor references renumbered in the proof (5) |
| `TypeProgress` | `theorem wf_config_label` | constructor references renumbered in the proof (1) |
| `TypeProgress` | `theorem wf_config_frame` | constructor references renumbered in the proof (1) |
| `TypeProgress` | `theorem t_progress_e_Instr_ok2_frame` | constructor references renumbered in the proof (1) |
| `wasm2.0` | 29 more constructs: `expr`, `elemmode`, `wf_elemmode`, `datamode`, `wf_datamode`, `type`, `«local»`, `func`, `wf_func`, `global`, `wf_global`, `table`, `wf_table`, `mem`, `wf_mem`, `elem`, `wf_elem`, `data`, `wf_data`, `start`, `wf_start`, `externidx`, `wf_externidx`, `«export»`, `wf_export`, `«import»`, `wf_import`, `module`, `wf_module` | spec position in the header comment (1 line each) |

## 7. Builds

Both states were compiled from scratch in the scratchpad, one Lean process at a time (12 GB cap), with the toolchain's `lean` v4.32.0 called directly. The repo's `.lake/build` was not used. The NEW error and warning counts are from the fresh build of the installed repo files.

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

The warnings are the same 171 messages in OLD and NEW; only their line numbers move, where lines were deleted above them. They are 94 unused variables, 51 Mathlib naming-convention lints and 26 other linter suggestions (tactics that do nothing, unused `simp` arguments, `Try this` hints).
"NEW scratch" is the build in which the repair was made; "NEW repo" is the fresh build of the installed files, which are byte-identical to it. Times vary with machine load (the editor's Lean servers were running throughout) and are not a property of the change. Peak memory was about 4.8 GB, in `TypeProgress`.

## 8. Left unchanged, and other notes

- **Comments that count instructions.** Five comments in `TypingLemmas` still say 68 where `instr` now has 67 constructors. They are at NEW lines 187 ("68-case transcription"), 1477, 1480 and 1482 ("each of `instr`'s 68 constructors", "68×68 cases", "the 68×68 case bash") and 1690 ("the other 68").
  - I left them as they were: they are comments, and line 1482 records a past measurement.
  - Line 772 ("Rocq destructs both instructions (68×68)") describes Rocq and is still accurate.
  - Line 197 ("all 73 cases") counts `Instr_ok` rules, which are still 73.
- **The word `sorry` in comments.** No code contains `sorry`, but the word appears in comments:
  - in `wasm2.0.lean`, the commented-out generated originals `--   sorry` at lines 15430 and 15563, as in bundle32;
  - in status notes saying a module has no `sorry`: `TypePreservationPure` line 18, `TypePreservation` lines 19 and 2024, `TypeProgress` lines 47 and 51.
  - So a plain `grep sorry` over the nine modules finds 7 lines, and none is a proof hole. (`OLD_wasm2.0.lean` has the same two commented-out lines.)
- **Untouched files.** `wasm2.0.lean` and `OLD_wasm2.0.lean` were not modified this turn. Neither were `ExtendedDeriveDecEq`, `HelperLemmas`, `Subtyping` or `ExtensionLemmas`.
- **Cross-check with the trial port.** All nine NEW files are byte-identical to `spectec/src/temp_port_reference/trial_port/`. That port was made outside this log by a patch-based procedure; I compared only after my own result compiled.
- **`lake build`.** I didn't run it, because it writes `.lake/build`. That directory is stale, so the next `lake build` or editor session rebuilds all nine modules, which takes about 2–3 minutes. Until then, the editor may show errors in modules that import the new `wasm2.0`.

## 9. Method and evidence

Everything is in `claude-logging/verbatim_dialogue_log/bundle33/evidence/`:
- `tools/`:
  - `scan33.py`: finds every affected code reference, by constructor meaning;
  - `apply33.py`: applies the 17 edits, checking each expected line;
  - `diff33.py`: does the line accounting of §1, §3, §4 and §6;
  - `EnvDump33.lean`, `envdiff33.py` and `envcat33.py`: the Lean-level comparison of §5;
  - `RunAudit33.lean`: the `Inhabited` audit;
  - `chain33.sh`, `lrun33.sh` and `check33.sh`: the serial build and the safety checks;
  - `report33.py`: generates this report.
- `outputs/`:
  - build logs of OLD, of NEW before repair, of NEW after repair and of the fresh repo build;
  - the error logs of the unrepaired modules;
  - `diff33_all_changed_lines.tsv`, with all 211 lines;
  - unified diffs `*.diff`;
  - the constructor map;
  - the declaration dumps (`dump_old.tsv.gz`, `dump_new.tsv.gz`) and their comparison (`envdiff33.json`, `envcat33.json`);
  - the audit outputs.

## Appendix A. All 56 changed lines of the model's proofs (§3.4)

| OLD → NEW line | construct | OLD text → NEW text |
|---|---|---|
| 14712 → 14707 | `iswf_admininstr_VCONST` | `wf_admininstr.admininstr_case_20 _ _ (by decide) h` → `wf_admininstr.admininstr_case_19 _ _ (by decide) h` |
| 14716 → 14711 | `iswf_admininstr_VCONST_inv` | `cases h with \| admininstr_case_20 _ _ _ hw => exact hw` → `cases h with \| admininstr_case_19 _ _ _ hw => exact hw` |
| 14727 → 14722 | `Step_pure_is_wf` | `\| unreachable => exact iswf_Forall_singleton .admininstr_case_73` → `\| unreachable => exact iswf_Forall_singleton .admininstr_case_72` |
| 14753 → 14748 | `Step_pure_is_wf` | `\| admininstr_case_71 _ _ _ hinstrs hbody =>` → `\| admininstr_case_70 _ _ _ hinstrs hbody =>` |
| 14760 → 14755 | `Step_pure_is_wf` | `\| admininstr_case_71 _ _ _ _ hbody =>` → `\| admininstr_case_70 _ _ _ _ hbody =>` |
| 14788 → 14783 | `Step_pure_is_wf` | `\| admininstr_case_72 _ _ _ _ hbody =>` → `\| admininstr_case_71 _ _ _ _ hbody =>` |
| 14793 → 14788 | `Step_pure_is_wf` | `\| admininstr_case_71 _ _ _ _ hbody => exact fun x hx => hbody x (List.mem_append_left _ hx)` → `\| admininstr_case_70 _ _ _ _ hbody => exact fun x hx => hbody x (List.mem_append_left _ hx)` |
| 14794 → 14789 | `Step_pure_is_wf` | `\| trap_vals => exact iswf_Forall_singleton .admininstr_case_73` → `\| trap_vals => exact iswf_Forall_singleton .admininstr_case_72` |
| 14795 → 14790 | `Step_pure_is_wf` | `\| trap_label => exact iswf_Forall_singleton .admininstr_case_73` → `\| trap_label => exact iswf_Forall_singleton .admininstr_case_72` |
| 14796 → 14791 | `Step_pure_is_wf` | `\| trap_frame => exact iswf_Forall_singleton .admininstr_case_73` → `\| trap_frame => exact iswf_Forall_singleton .admininstr_case_72` |
| 14803 → 14798 | `Step_pure_is_wf` | `\| unop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| unop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 14809 → 14804 | `Step_pure_is_wf` | `\| binop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| binop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 14820 → 14815 | `Step_pure_is_wf` | `\| cvtop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| cvtop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 14853 → 14848 | `Step_pure_is_wf` | `\| vunop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| vunop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 14861 → 14856 | `Step_pure_is_wf` | `\| vbinop_trap => exact iswf_Forall_singleton .admininstr_case_73` → `\| vbinop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 14963 → 14958 | `Step_pure_is_wf` | `exact iswf_Forall_cons hv (iswf_Forall_cons hv (iswf_Forall_singleton (.admininstr_case_44 _ ‹wf_uN 32 x›)))` → `exact iswf_Forall_cons hv (iswf_Forall_cons hv (iswf_Forall_singleton (.admininstr_case_43 _ ‹wf_uN 32 x›)))` |
| 16926 → 16921 | `iswf_store_I32_8` | `wf_admininstr.admininstr_case_57 (some Inn.I32) _ _ _ (some 32)` → `wf_admininstr.admininstr_case_56 (some Inn.I32) _ _ _ (some 32)` |
| 16938 → 16933 | `iswf_load_I32_8_U` | `wf_admininstr.admininstr_case_56 _ _ _` → `wf_admininstr.admininstr_case_55 _ _ _` |
| 16983 → 16978 | `Step_read_is_wf` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ (iswf_Forall_nil _)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ (iswf_Forall_nil _)` |
| 16990 → 16985 | `Step_read_is_wf` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _` |
| 17001 → 16996 | `Step_read_is_wf` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_72 _ _ _ ‹wf_frame _›` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ ‹wf_frame _›` |
| 17002 → 16997 | `Step_read_is_wf` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ (iswf_Forall_nil _)` → `(iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ (iswf_Forall_nil _)` |
| 17009 → 17004 | `Step_read_is_wf` | `\| admininstr_case_43 _ hx =>` → `\| admininstr_case_42 _ hx =>` |
| 17015 → 17010 | `Step_read_is_wf` | `\| admininstr_case_46 _ hx =>` → `\| admininstr_case_45 _ hx =>` |
| 17034 → 17029 | `Step_read_is_wf` | `\| admininstr_case_52 _ hx =>` → `\| admininstr_case_51 _ hx =>` |
| 17038 → 17033 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` |
| 17041 → 17036 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ hx) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_51 _ hx) (iswf_Forall_nil _)` |
| 17051 → 17046 | `Step_read_is_wf` | `\| admininstr_case_53 _ _ hx hy =>` → `\| admininstr_case_52 _ _ hx hy =>` |
| 17056 → 17051 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hy) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_47 _ hy) <\|` |
| 17057 → 17052 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` |
| 17060 → 17055 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ _ hx hy) (iswf_Forall_nil _)` |
| 17068 → 17063 | `Step_read_is_wf` | `\| admininstr_case_53 _ _ hx hy =>` → `\| admininstr_case_52 _ _ hx hy =>` |
| 17072 → 17067 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hy) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_47 _ hy) <\|` |
| 17073 → 17068 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\| iswf_Forall_cons hj <\| iswf_Forall_cons hi <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\| iswf_Forall_cons hj <\| iswf_Forall_cons hi <\|` |
| 17075 → 17070 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ _ hx hy) (iswf_Forall_nil _)` |
| 17084 → 17079 | `Step_read_is_wf` | `\| admininstr_case_54 _ _ hx hy =>` → `\| admininstr_case_53 _ _ hx hy =>` |
| 17089 → 17084 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` → `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` |
| 17092 → 17087 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_54 _ _ hx hy) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` |
| 17103 → 17098 | `Step_read_is_wf` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide) ‹wf_uN 128 c›) (iswf_Forall_nil _)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide) ‹wf_uN 128 c›) (iswf_Forall_nil _)` |
| 17107 → 17102 | `Step_read_is_wf` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` |
| 17114 → 17109 | `Step_read_is_wf` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` |
| 17121 → 17116 | `Step_read_is_wf` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` |
| 17127 → 17122 | `Step_read_is_wf` | `\| admininstr_case_20 _ _ _ hw1 =>` → `\| admininstr_case_19 _ _ _ hw1 =>` |
| 17132 → 17127 | `Step_read_is_wf` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` → `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` |
| 17179 → 17174 | `Step_read_is_wf` | `\| admininstr_case_66 _ hx =>` → `\| admininstr_case_65 _ hx =>` |
| 17185 → 17180 | `Step_read_is_wf` | `iswf_Forall_cons (wf_admininstr.admininstr_case_66 _ hx) (iswf_Forall_nil _)` → `iswf_Forall_cons (wf_admininstr.admininstr_case_65 _ hx) (iswf_Forall_nil _)` |
| 17244 → 17239 | `Step_is_wf` | `\| admininstr_case_71 _ _ _ hi _ =>` → `\| admininstr_case_70 _ _ _ hi _ =>` |
| 17248 → 17243 | `Step_is_wf` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ hi hais') (iswf_Forall_nil _))` → `(iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ hi hais') (iswf_Forall_nil _))` |
| 17257 → 17252 | `Step_is_wf` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_72 _ _ _ hf'' hais') (iswf_Forall_nil _))` → `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ hf'' hais') (iswf_Forall_nil _))` |
| 17267 → 17262 | `Step_is_wf` | `\| admininstr_case_44 _ hx =>` → `\| admininstr_case_43 _ hx =>` |
| 17274 → 17269 | `Step_is_wf` | `\| admininstr_case_47 _ hx =>` → `\| admininstr_case_46 _ hx =>` |
| 17283 → 17278 | `Step_is_wf` | `\| admininstr_case_49 _ hx =>` → `\| admininstr_case_48 _ hx =>` |
| 17289 → 17284 | `Step_is_wf` | `\| admininstr_case_51 _ hx =>` → `\| admininstr_case_50 _ hx =>` |
| 17303 → 17298 | `Step_is_wf` | `\| admininstr_case_55 _ hx =>` → `\| admininstr_case_54 _ hx =>` |
| 17334 → 17329 | `Step_is_wf` | `\| admininstr_case_20 _ _ hsz hwfc =>` → `\| admininstr_case_19 _ _ hsz hwfc =>` |
| 17364 → 17359 | `Step_is_wf` | `\| admininstr_case_67 _ hx =>` → `\| admininstr_case_66 _ hx =>` |

## Appendix B. Lean-level lists (§5)

**Only in OLD (43):** `List.match_on_same_ctor._@.wasm2.0.2749490885._hygCtx._hyg.163`, `List.match_on_same_ctor._@.wasm2.0.3401859148._hygCtx._hyg.150`, `List.match_on_same_ctor.het._@.wasm2.0.2749490885._hygCtx._hyg.163`, `List.match_on_same_ctor.het._@.wasm2.0.3401859148._hygCtx._hyg.150`, `TLC.Step_pure__select_preserves_helper._simp_1_59`, `TLC.ai_principal_typing.eq_56`, `TLC.br_reduce_decidable._proof_140`, `TLC.br_reduce_decidable._proof_141`, `TLC.instr_of.eq_74`, `TLC.instr_typing_inversion._proof_1_72`, `TLC.instr_typing_inversion._proof_1_77`, `TLC.return_reduce_decidable._proof_75`, `_private.TypePreservationPure.0.TLC.ai_principal_typing.match_1.eq_56`, `_private.TypePreservationPure.0.TLC.ai_principal_typing.match_1.splitter._sparseCasesOn_60`, `_private.TypingLemmas.0.TLC.instr_of.match_1.eq_74`, `_private.TypingLemmas.0.admininstr_instr.match_1.eq_68`, `admininstr.EXTEND`, `admininstr.EXTEND.elim`, `admininstr.EXTEND.inj`, `admininstr.EXTEND.injEq`, `admininstr.EXTEND.noConfusion`, `admininstr.EXTEND.sizeOf_spec`, `admininstr.decEq._proof_182`, `admininstr.decEq._proof_183`, `admininstr.decEq._proof_184`, `admininstr.match_on_same_ctor._@.wasm2.0.1837273375._hygCtx._hyg.618`, `admininstr.match_on_same_ctor.het._@.wasm2.0.1837273375._hygCtx._hyg.618`, `admininstr_instr.eq_68`, `instr.EXTEND`, `instr.EXTEND.elim`, `instr.EXTEND.inj`, `instr.EXTEND.injEq`, `instr.EXTEND.noConfusion`, `instr.EXTEND.sizeOf_spec`, `instr.decEq._proof_168`, `instr.decEq._proof_169`, `instr.decEq._proof_170`, `instr.match_on_same_ctor._@.wasm2.0.1320104542._hygCtx._hyg.571`, `instr.match_on_same_ctor.het._@.wasm2.0.1320104542._hygCtx._hyg.571`, `wf_admininstr.admininstr_case_19_EXTEND_removed`, `wf_admininstr.below.admininstr_case_19_EXTEND_removed`, `wf_instr.below.instr_case_19_EXTEND_removed`, `wf_instr.instr_case_19_EXTEND_removed`.

**Only in NEW (12):** `List.match_on_same_ctor._@.wasm2.0.2749490885._hygCtx._hyg.161`, `List.match_on_same_ctor._@.wasm2.0.3401859148._hygCtx._hyg.148`, `List.match_on_same_ctor.het._@.wasm2.0.2749490885._hygCtx._hyg.161`, `List.match_on_same_ctor.het._@.wasm2.0.3401859148._hygCtx._hyg.148`, `TLC.Step_pure__select_preserves_helper._simp_1_57`, `TLC.instr_typing_inversion._proof_1_69`, `TLC.instr_typing_inversion._proof_1_75`, `_private.TypePreservationPure.0.TLC.ai_principal_typing.match_1.splitter._sparseCasesOn_59`, `admininstr.match_on_same_ctor._@.wasm2.0.1837273375._hygCtx._hyg.609`, `admininstr.match_on_same_ctor.het._@.wasm2.0.1837273375._hygCtx._hyg.609`, `instr.match_on_same_ctor._@.wasm2.0.1320104542._hygCtx._hyg.562`, `instr.match_on_same_ctor.het._@.wasm2.0.1320104542._hygCtx._hyg.562`.

**User-level theorems whose elaborated proof term changed (115), by module:**

- `«wasm2.0»` (9): `Step_is_wf`, `Step_pure_is_wf`, `Step_read_is_wf`, `dataidx_instr_is_wf`, `iswf_I32_const_lt`, `iswf_I32_iadd1`, `iswf_admininstr_VCONST_inv`, `iswf_admininstr_instr`, `iswf_val_of_admininstr`
- `TypingLemmas` (11): `ai_typing_inversion`, `ai_val_principal_typing_inversion`, `ais_single_ref_typing_inversion`, `ais_single_val_typing_inversion`, `construct_ai_maybe`, `injective_admininstr_instr`, `instr_of_admininstr_instr`, `instr_typing_inversion`, `principal_typing_conversion`, `wf_admininstr_instr`, `wf_instr_admininstr`
- `TypePreservationPure` (22): `Step_pure__binop_val_preserves`, `Step_pure__br_if_false_preserves`, `Step_pure__br_if_true_preserves`, `Step_pure__br_succ_preserves`, `Step_pure__br_table_ge_preserves`, `Step_pure__br_table_lt_preserves`, `Step_pure__br_zero_preserves`, `Step_pure__cvtop_val_preserves`, `Step_pure__drop_preserves`, `Step_pure__frame_vals_preserves`, `Step_pure__if_preserves_helper`, `Step_pure__label_vals_preserves`, `Step_pure__local_tee_preserves`, `Step_pure__nop_preserves`, `Step_pure__ref_is_null_false_preserves`, `Step_pure__ref_is_null_helper`, `Step_pure__relop_preserves`, `Step_pure__return_frame_preserves`, `Step_pure__return_label_preserves`, `Step_pure__select_preserves_helper`, `Step_pure__testop_preserves`, `Step_pure__unop_val_preserves`
- `TypePreservation` (38): `ais_elem_drop_inv`, `ais_global_set_inv`, `ais_memory_grow_inv`, `ais_store_mems_inv`, `ais_table_grow_inv`, `ais_table_set_inv`, `inv_data_drop`, `inv_elem_drop`, `inv_global_set`, `inv_local_set`, `inv_memory_grow`, `inv_store_none`, `inv_store_pack`, `inv_table_grow`, `inv_table_set`, `pt_call`, `pt_call_addr`, `pt_call_indirect`, `pt_global_get`, `pt_load_none`, `pt_load_pack`, `pt_local_get`, `pt_memory_copy`, `pt_memory_fill`, `pt_memory_init`, `pt_memory_size`, `pt_ref_func`, `pt_table_copy`, `pt_table_fill`, `pt_table_get`, `pt_table_init`, `pt_table_size`, `t_read_preservation`, `wf_const_num`, `wf_vconst_parts`, `_private.TypePreservation.0.store_extension_reduce_aux`, `_private.TypePreservation.0.t_preservation_type_aux`, `_private.TypePreservation.0.t_preservation_vs_type'_aux`
- `TypeProgress` (35): `br_reduce_extract_vs`, `const_es_exists`, `return_reduce_extract_vs`, `split_vals_inverse`, `split_vals_prefix`, `t_progress_be_binop`, `t_progress_be_br_if`, `t_progress_be_br_table`, `t_progress_be_cvtop`, `t_progress_be_relop`, `t_progress_be_testop`, `t_progress_be_unop`, `t_progress_be_vbinop`, `t_progress_be_vbitmask`, `t_progress_be_vcvtop`, `t_progress_be_vextbinop`, `t_progress_be_vextract_lane`, `t_progress_be_vextunop`, `t_progress_be_vload_lane`, `t_progress_be_vload_pack`, `t_progress_be_vload_splat`, `t_progress_be_vnarrow`, `t_progress_be_vrelop`, `t_progress_be_vreplace_lane`, `t_progress_be_vshiftop`, `t_progress_be_vshuffle`, `t_progress_be_vsplat`, `t_progress_be_vstore_lane`, `t_progress_be_vswizzle`, `t_progress_be_vtestop`, `t_progress_be_vunop`, `t_progress_e_Instr_ok2_frame`, `wf_config_frame`, `wf_config_label`, `wf_forall_admin_val`

(`TLC.` prefix omitted.)
