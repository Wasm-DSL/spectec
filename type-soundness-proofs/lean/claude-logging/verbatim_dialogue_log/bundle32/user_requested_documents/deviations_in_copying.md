# Deviations when copying into the regenerated `wasm2.0.lean` (bundle32)

Written for: the user, and later sessions. Date: 2026-11-11.

This is the exhaustive list of every place where text copied from `OLD_wasm2.0.lean` (the theorems' proofs, the two hand-edited theorems, and the 92 helper lemmas marked `/- HELPER LEMMA CREATED BY CLAUDE -/`) differs from the copy in the new `spectec/src/test-lean-claude/wasm2.0.lean`.

## 1. Summary

- **One kind of deviation, 56 lines, in 7 top-level constructs.** Every deviation renames a `wf_admininstr` constructor reference, `admininstr_case_K` to `admininstr_case_{K-1}` (K ≥ 20).
  - **Why:** the regenerated model no longer has the `EXTEND numtype n` instruction. So the generated `wf_admininstr` lost its constructor `admininstr_case_19` (`admininstr.EXTEND`), and every later constructor moved down by one. In the same way, `wf_instr` lost `instr_case_19` and renumbered `instr_case_20..67` to `19..66`, but the copied text never refers to a renumbered `instr_case_K`.
  - **Each rename is by meaning, not by arithmetic.** The new name is the unique new constructor whose full text (argument telescope, premises and conclusion) is identical to the old constructor's. `admininstr_case_19` (EXTEND), the only constructor without a counterpart, is never referenced.
  - **All 56 lines are inside proof bodies.** No theorem or helper statement changed, and no line was added, removed or moved.
- **Everything else was copied verbatim.** The hand-written text is 1,865 lines in both files: 1,809 copied verbatim plus the 56 renamed lines. It consists of:
  - the proofs of all 89 generated theorems;
  - the two hand edits, as in OLD. `Step_read_is_wf` and `Step_is_wf` are re-stated below `inductive Store_ok`, with three changes: the configuration argument `(var_0 : config)` becomes `(z : state) (admininstr_lst : List admininstr)`, written `config.mk_config z admininstr_lst`; there is an extra premise `Store_ok (fun_store z)`; and there is a `/- Hand-edited, as in …` comment above each. At their generated places, the generated originals are commented out with `-- `, and there are two notes.
  - all 92 helper lemmas, each marked and at the same position among the other top-level constructs. They sit in 23 contiguous hand-written regions, which make 24 runs of consecutive helpers: the last region below `Store_ok` also holds the re-stated `Step_read_is_wf` (between its 19th and 20th helper) and `Step_is_wf` (after the 24th).
- **The deviations are necessary.**
  - Left unrenamed, each old name would denote a different constructor of the new model. For example, old `admininstr_case_20` (VCONST) would become the VVUNOP case, old `admininstr_case_57` (STORE) the VLOAD case, and old `admininstr_case_72` (FRAME_) the TRAP case. Old `admininstr_case_73` (TRAP) would denote nothing at all.
  - Compiling the verbatim copy gives 72 errors, every one within 2 lines of one of the 56 lines. 43 of the 56 lines have an error next to them. The other 13 sit inside `cases … with` alternatives (12 directly, 1 nested) whose pattern line is itself one of the renamed lines and failed first, so Lean never elaborated their bodies.
  - With the renames, the file compiles with 0 errors and no `sorry`.

## 2. Deviations per construct

| construct | kind | lines renamed | renames |
|---|---|---|---|
| `iswf_admininstr_VCONST` | helper lemma | 1 | `admininstr_case_20`→`admininstr_case_19` (×1) |
| `iswf_admininstr_VCONST_inv` | helper lemma | 1 | `admininstr_case_20`→`admininstr_case_19` (×1) |
| `Step_pure_is_wf` | generated theorem | 14 | `admininstr_case_44`→`admininstr_case_43` (×1), `admininstr_case_71`→`admininstr_case_70` (×3), `admininstr_case_72`→`admininstr_case_71` (×1), `admininstr_case_73`→`admininstr_case_72` (×9) |
| `iswf_store_I32_8` | helper lemma | 1 | `admininstr_case_57`→`admininstr_case_56` (×1) |
| `iswf_load_I32_8_U` | helper lemma | 1 | `admininstr_case_56`→`admininstr_case_55` (×1) |
| `Step_read_is_wf` | hand-edited generated theorem | 28 | `admininstr_case_20`→`admininstr_case_19` (×6), `admininstr_case_43`→`admininstr_case_42` (×1), `admininstr_case_46`→`admininstr_case_45` (×1), `admininstr_case_48`→`admininstr_case_47` (×2), `admininstr_case_49`→`admininstr_case_48` (×4), `admininstr_case_52`→`admininstr_case_51` (×2), `admininstr_case_53`→`admininstr_case_52` (×4), `admininstr_case_54`→`admininstr_case_53` (×2), `admininstr_case_66`→`admininstr_case_65` (×2), `admininstr_case_71`→`admininstr_case_70` (×3), `admininstr_case_72`→`admininstr_case_71` (×1) |
| `Step_is_wf` | hand-edited generated theorem | 10 | `admininstr_case_20`→`admininstr_case_19` (×1), `admininstr_case_44`→`admininstr_case_43` (×1), `admininstr_case_47`→`admininstr_case_46` (×1), `admininstr_case_49`→`admininstr_case_48` (×1), `admininstr_case_51`→`admininstr_case_50` (×1), `admininstr_case_55`→`admininstr_case_54` (×1), `admininstr_case_67`→`admininstr_case_66` (×1), `admininstr_case_71`→`admininstr_case_70` (×2), `admininstr_case_72`→`admininstr_case_71` (×1) |

## 3. Constructor renames used

Old name (in `OLD_wasm2.0.lean`), new name (in `wasm2.0.lean`), and the instruction the constructor is about. Each pair is the unique match by the constructor's full text.

| old | new | constructor for | lines |
|---|---|---|---|
| `admininstr_case_20` | `admininstr_case_19` | `admininstr.VCONST` | 9 |
| `admininstr_case_43` | `admininstr_case_42` | `admininstr.LOCAL_GET` | 1 |
| `admininstr_case_44` | `admininstr_case_43` | `admininstr.LOCAL_SET` | 2 |
| `admininstr_case_46` | `admininstr_case_45` | `admininstr.GLOBAL_GET` | 1 |
| `admininstr_case_47` | `admininstr_case_46` | `admininstr.GLOBAL_SET` | 1 |
| `admininstr_case_48` | `admininstr_case_47` | `admininstr.TABLE_GET` | 2 |
| `admininstr_case_49` | `admininstr_case_48` | `admininstr.TABLE_SET` | 5 |
| `admininstr_case_51` | `admininstr_case_50` | `admininstr.TABLE_GROW` | 1 |
| `admininstr_case_52` | `admininstr_case_51` | `admininstr.TABLE_FILL` | 2 |
| `admininstr_case_53` | `admininstr_case_52` | `admininstr.TABLE_COPY` | 4 |
| `admininstr_case_54` | `admininstr_case_53` | `admininstr.TABLE_INIT` | 2 |
| `admininstr_case_55` | `admininstr_case_54` | `admininstr.ELEM_DROP` | 1 |
| `admininstr_case_56` | `admininstr_case_55` | `admininstr.LOAD` | 1 |
| `admininstr_case_57` | `admininstr_case_56` | `admininstr.STORE` | 1 |
| `admininstr_case_66` | `admininstr_case_65` | `admininstr.MEMORY_INIT` | 2 |
| `admininstr_case_67` | `admininstr_case_66` | `admininstr.DATA_DROP` | 1 |
| `admininstr_case_71` | `admininstr_case_70` | `admininstr.LABEL_` | 8 |
| `admininstr_case_72` | `admininstr_case_71` | `admininstr.FRAME_` | 3 |
| `admininstr_case_73` | `admininstr_case_72` | `admininstr.TRAP` | 9 |

## 4. Every deviation, line by line

Line numbers: `OLD` = `OLD_wasm2.0.lean`, `new` = the installed `wasm2.0.lean`. The text is the full line with leading spaces trimmed; only the constructor name differs between "before" and "after".

| # | construct | OLD line | new line | before | after |
|---|---|---|---|---|---|
| 1 | `iswf_admininstr_VCONST` | 14712 | 14707 | `wf_admininstr.admininstr_case_20 _ _ (by decide) h` | `wf_admininstr.admininstr_case_19 _ _ (by decide) h` |
| 2 | `iswf_admininstr_VCONST_inv` | 14716 | 14711 | `cases h with \| admininstr_case_20 _ _ _ hw => exact hw` | `cases h with \| admininstr_case_19 _ _ _ hw => exact hw` |
| 3 | `Step_pure_is_wf` | 14727 | 14722 | `\| unreachable => exact iswf_Forall_singleton .admininstr_case_73` | `\| unreachable => exact iswf_Forall_singleton .admininstr_case_72` |
| 4 | `Step_pure_is_wf` | 14753 | 14748 | `\| admininstr_case_71 _ _ _ hinstrs hbody =>` | `\| admininstr_case_70 _ _ _ hinstrs hbody =>` |
| 5 | `Step_pure_is_wf` | 14760 | 14755 | `\| admininstr_case_71 _ _ _ _ hbody =>` | `\| admininstr_case_70 _ _ _ _ hbody =>` |
| 6 | `Step_pure_is_wf` | 14788 | 14783 | `\| admininstr_case_72 _ _ _ _ hbody =>` | `\| admininstr_case_71 _ _ _ _ hbody =>` |
| 7 | `Step_pure_is_wf` | 14793 | 14788 | `\| admininstr_case_71 _ _ _ _ hbody => exact fun x hx => hbody x (List.mem_append_left _ hx)` | `\| admininstr_case_70 _ _ _ _ hbody => exact fun x hx => hbody x (List.mem_append_left _ hx)` |
| 8 | `Step_pure_is_wf` | 14794 | 14789 | `\| trap_vals => exact iswf_Forall_singleton .admininstr_case_73` | `\| trap_vals => exact iswf_Forall_singleton .admininstr_case_72` |
| 9 | `Step_pure_is_wf` | 14795 | 14790 | `\| trap_label => exact iswf_Forall_singleton .admininstr_case_73` | `\| trap_label => exact iswf_Forall_singleton .admininstr_case_72` |
| 10 | `Step_pure_is_wf` | 14796 | 14791 | `\| trap_frame => exact iswf_Forall_singleton .admininstr_case_73` | `\| trap_frame => exact iswf_Forall_singleton .admininstr_case_72` |
| 11 | `Step_pure_is_wf` | 14803 | 14798 | `\| unop_trap => exact iswf_Forall_singleton .admininstr_case_73` | `\| unop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 12 | `Step_pure_is_wf` | 14809 | 14804 | `\| binop_trap => exact iswf_Forall_singleton .admininstr_case_73` | `\| binop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 13 | `Step_pure_is_wf` | 14820 | 14815 | `\| cvtop_trap => exact iswf_Forall_singleton .admininstr_case_73` | `\| cvtop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 14 | `Step_pure_is_wf` | 14853 | 14848 | `\| vunop_trap => exact iswf_Forall_singleton .admininstr_case_73` | `\| vunop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 15 | `Step_pure_is_wf` | 14861 | 14856 | `\| vbinop_trap => exact iswf_Forall_singleton .admininstr_case_73` | `\| vbinop_trap => exact iswf_Forall_singleton .admininstr_case_72` |
| 16 | `Step_pure_is_wf` | 14963 | 14958 | `exact iswf_Forall_cons hv (iswf_Forall_cons hv (iswf_Forall_singleton (.admininstr_case_44 _ ‹wf_uN 32 x›)))` | `exact iswf_Forall_cons hv (iswf_Forall_cons hv (iswf_Forall_singleton (.admininstr_case_43 _ ‹wf_uN 32 x›)))` |
| 17 | `iswf_store_I32_8` | 16926 | 16921 | `wf_admininstr.admininstr_case_57 (some Inn.I32) _ _ _ (some 32)` | `wf_admininstr.admininstr_case_56 (some Inn.I32) _ _ _ (some 32)` |
| 18 | `iswf_load_I32_8_U` | 16938 | 16933 | `wf_admininstr.admininstr_case_56 _ _ _` | `wf_admininstr.admininstr_case_55 _ _ _` |
| 19 | `Step_read_is_wf` | 16983 | 16978 | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ (iswf_Forall_nil _)` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ (iswf_Forall_nil _)` |
| 20 | `Step_read_is_wf` | 16990 | 16985 | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _` |
| 21 | `Step_read_is_wf` | 17001 | 16996 | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_72 _ _ _ ‹wf_frame _›` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ ‹wf_frame _›` |
| 22 | `Step_read_is_wf` | 17002 | 16997 | `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ (iswf_Forall_nil _)` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ (iswf_Forall_nil _)` |
| 23 | `Step_read_is_wf` | 17009 | 17004 | `\| admininstr_case_43 _ hx =>` | `\| admininstr_case_42 _ hx =>` |
| 24 | `Step_read_is_wf` | 17015 | 17010 | `\| admininstr_case_46 _ hx =>` | `\| admininstr_case_45 _ hx =>` |
| 25 | `Step_read_is_wf` | 17034 | 17029 | `\| admininstr_case_52 _ hx =>` | `\| admininstr_case_51 _ hx =>` |
| 26 | `Step_read_is_wf` | 17038 | 17033 | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` |
| 27 | `Step_read_is_wf` | 17041 | 17036 | `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ hx) (iswf_Forall_nil _)` | `iswf_Forall_cons (wf_admininstr.admininstr_case_51 _ hx) (iswf_Forall_nil _)` |
| 28 | `Step_read_is_wf` | 17051 | 17046 | `\| admininstr_case_53 _ _ hx hy =>` | `\| admininstr_case_52 _ _ hx hy =>` |
| 29 | `Step_read_is_wf` | 17056 | 17051 | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hy) <\|` | `iswf_Forall_cons (wf_admininstr.admininstr_case_47 _ hy) <\|` |
| 30 | `Step_read_is_wf` | 17057 | 17052 | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` |
| 31 | `Step_read_is_wf` | 17060 | 17055 | `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` | `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ _ hx hy) (iswf_Forall_nil _)` |
| 32 | `Step_read_is_wf` | 17068 | 17063 | `\| admininstr_case_53 _ _ hx hy =>` | `\| admininstr_case_52 _ _ hx hy =>` |
| 33 | `Step_read_is_wf` | 17072 | 17067 | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hy) <\|` | `iswf_Forall_cons (wf_admininstr.admininstr_case_47 _ hy) <\|` |
| 34 | `Step_read_is_wf` | 17073 | 17068 | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\| iswf_Forall_cons hj <\| iswf_Forall_cons hi <\|` | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\| iswf_Forall_cons hj <\| iswf_Forall_cons hi <\|` |
| 35 | `Step_read_is_wf` | 17075 | 17070 | `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` | `iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ _ hx hy) (iswf_Forall_nil _)` |
| 36 | `Step_read_is_wf` | 17084 | 17079 | `\| admininstr_case_54 _ _ hx hy =>` | `\| admininstr_case_53 _ _ hx hy =>` |
| 37 | `Step_read_is_wf` | 17089 | 17084 | `iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <\|` | `iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hx) <\|` |
| 38 | `Step_read_is_wf` | 17092 | 17087 | `iswf_Forall_cons (wf_admininstr.admininstr_case_54 _ _ hx hy) (iswf_Forall_nil _)` | `iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)` |
| 39 | `Step_read_is_wf` | 17103 | 17098 | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide) ‹wf_uN 128 c›) (iswf_Forall_nil _)` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide) ‹wf_uN 128 c›) (iswf_Forall_nil _)` |
| 40 | `Step_read_is_wf` | 17107 | 17102 | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` |
| 41 | `Step_read_is_wf` | 17114 | 17109 | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` |
| 42 | `Step_read_is_wf` | 17121 | 17116 | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` |
| 43 | `Step_read_is_wf` | 17127 | 17122 | `\| admininstr_case_20 _ _ _ hw1 =>` | `\| admininstr_case_19 _ _ _ hw1 =>` |
| 44 | `Step_read_is_wf` | 17132 | 17127 | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)` | `exact iswf_Forall_cons (wf_admininstr.admininstr_case_19 _ _ (by decide)` |
| 45 | `Step_read_is_wf` | 17179 | 17174 | `\| admininstr_case_66 _ hx =>` | `\| admininstr_case_65 _ hx =>` |
| 46 | `Step_read_is_wf` | 17185 | 17180 | `iswf_Forall_cons (wf_admininstr.admininstr_case_66 _ hx) (iswf_Forall_nil _)` | `iswf_Forall_cons (wf_admininstr.admininstr_case_65 _ hx) (iswf_Forall_nil _)` |
| 47 | `Step_is_wf` | 17244 | 17239 | `\| admininstr_case_71 _ _ _ hi _ =>` | `\| admininstr_case_70 _ _ _ hi _ =>` |
| 48 | `Step_is_wf` | 17248 | 17243 | `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ hi hais') (iswf_Forall_nil _))` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_70 _ _ _ hi hais') (iswf_Forall_nil _))` |
| 49 | `Step_is_wf` | 17257 | 17252 | `(iswf_Forall_cons (wf_admininstr.admininstr_case_72 _ _ _ hf'' hais') (iswf_Forall_nil _))` | `(iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ hf'' hais') (iswf_Forall_nil _))` |
| 50 | `Step_is_wf` | 17267 | 17262 | `\| admininstr_case_44 _ hx =>` | `\| admininstr_case_43 _ hx =>` |
| 51 | `Step_is_wf` | 17274 | 17269 | `\| admininstr_case_47 _ hx =>` | `\| admininstr_case_46 _ hx =>` |
| 52 | `Step_is_wf` | 17283 | 17278 | `\| admininstr_case_49 _ hx =>` | `\| admininstr_case_48 _ hx =>` |
| 53 | `Step_is_wf` | 17289 | 17284 | `\| admininstr_case_51 _ hx =>` | `\| admininstr_case_50 _ hx =>` |
| 54 | `Step_is_wf` | 17303 | 17298 | `\| admininstr_case_55 _ hx =>` | `\| admininstr_case_54 _ hx =>` |
| 55 | `Step_is_wf` | 17334 | 17329 | `\| admininstr_case_20 _ _ hsz hwfc =>` | `\| admininstr_case_19 _ _ hsz hwfc =>` |
| 56 | `Step_is_wf` | 17364 | 17359 | `\| admininstr_case_67 _ hx =>` | `\| admininstr_case_66 _ hx =>` |

## 5. Copied verbatim, although it might look stale (not deviations)

- **References to constructors whose numbers did not change.** The copied text refers 31 times to `wf_admininstr`/`wf_instr` constructors numbered below 19: `admininstr_case_4` (×3), `_5` (×1), `_7` (×5), `_13` (×21) and `instr_case_5` (×1). Constructors 0–18 kept their numbers and their text, so these were copied unchanged.
- **Comments that cite case numbers of `fun_vunop_` and `fun_vbinop_`.** These are at new lines 6332–6339 and 7975–7981, for example "the `none` fallback (case_26)". The regeneration did not touch those relations, so the comments are still accurate.
- **The two notes and the comments above the re-stated hand-edited theorems.** These are `/- AUTOGENERATED Step_read_is_wf MOVED BELOW BECAUSE IT NEEDS Store_ok, WHICH IS BELOW -/`, `/- Step_read_is_wf SHIFTED HERE BY HAND TO USE Store_ok -/`, and the plain comments "Hand-edited, as in `OLD_wasm2.0.lean`: …". They were copied unchanged. "`OLD_wasm2.0.lean`" now names the file they were copied from, which has the same hand edits.
- **The commented-out generated originals of `Step_read_is_wf` and `Step_is_wf`.** The new generator emits these two statements exactly as before, character for character, so the commented-out text still matches the generated text. These two commented-out lines (`--   sorry`) are the only places where the word `sorry` occurs in the file, exactly as in `OLD_wasm2.0.lean`.
- **Line numbers.** The new file has 17,522 lines; `OLD_wasm2.0.lean` has 17,527. The 5 missing lines are generated `EXTEND` lines: the `instr` and `admininstr` constructors, their `wf_instr`/`wf_admininstr` cases, and the `instr` → `admininstr` coercion arm. They are lines 1953, 2062, 12206, 12287 and 12409 of `OLD_wasm2.0.lean`. Everything after line 1953 of OLD therefore sits 1 to 5 lines higher in the new file. This is not a change to any copied text.

## 6. How the copy was made, and how it was checked

**Method.** The copy was made by a deterministic 3-way line merge, with no hand editing:
- base: the old generated model, `spectec/test-lean/todaywasm2.0_shouldwork`, md5 `83ce8797…`;
- ours: `OLD_wasm2.0.lean`;
- theirs: the new generated model.

Every generated line comes from the new model. Every hand-written line comes from `OLD_wasm2.0.lean`. The merge had no conflicts: no part of the hand layer replaces a generated line that the EXTEND removal changed. The hand layer consists of:
- 87 `sorry` → proof replacements;
- 2 commented-out originals;
- 23 inserted blocks, holding the 92 helpers and the two moved theorems.

The 56 renames were then applied to hand-written lines only, using the constructor map built by matching each constructor's full text.

**Checks on the result.** The result is the `wasm2.0.lean` installed in this bundle, md5 `fdfafb39…`.
- **Compilation.** It compiles with the toolchain's `lean` (v4.32.0) in a scratch directory, with 0 errors and no `declaration uses 'sorry'`. The 89 warnings are the same messages as `OLD_wasm2.0.lean`'s 89 (unused variables in generated definitions).
- **Top-level constructs.**
  - The (kind, name) sequence of all 897 top-level constructs is identical to `OLD_wasm2.0.lean`'s, as a set and in order.
  - Without the 92 helpers and the 2 moved theorems, it is identical to the new generated model's.
  - Each helper has the same neighbouring constructs as in OLD, and still sits directly above the first construct that uses it.
- **Theorem statements.**
  - The 87 generated theorems that were not hand-edited have their statements byte-identical to the new generated ones.
  - The 2 hand-edited theorems have statements identical to OLD's.
- **Axioms.** The axiom sets of all 181 theorems (89 generated + 92 helpers) are identical to those in `OLD_wasm2.0.lean`.
  - None of the 3,613 theorems in the module depends on `sorryAx`.
  - The 12 module theorems that exist only in OLD are the auto-generated `instr.EXTEND`/`admininstr.EXTEND` lemmas (`inj`, `injEq`, `sizeOf_spec`) and 6 `decEq` internals.
- **Default values.** The kernel replay with every `Inhabited` instance made opaque finds that 0 of 3,613 theorems need a default value. OLD gives 0 of 3,625.
- **Independent agreement.** The result is byte-identical to `spectec/src/temp_port_reference/trial_port/wasm2.0.lean`. That file was produced earlier by a different session (not in this log) with a different method (patch plus renamer). This session built its own copy first and then compared.

Evidence: `../evidence/` (tools, logs and outputs).

## 7. Independent verification (workflow `wf_3fce5d51-ce6`)

Three read-only agents each tried to refute one claim, using their own scripts. They ran no Lean and wrote only to their scratch directories. Each ran the bundle32 safety check at its start and end, and all six checks are OK. All three returned `claim_holds`.
- **V-EXH: is the copy exhaustive?**
  - It derived OLD's hand layer three ways (GNU `diff --minimal`, Python `difflib`, line multisets) and compared it with the new file's. The 1,865 hand lines on each side are identical except the 56 logged ones.
  - It enumerated the helpers twice, by marker and without the marker (every declaration not in the generated model). Both give the same 92 names in the same order, 627 lines in total, with 4 lines deviating as logged.
  - All 89 theorem blocks match (1,614 lines), and the commented-out originals and the notes are present.
  - It rebuilt the file as the new generated model plus OLD's hunks plus the 56 logged "after" lines, and the result is byte-identical.
- **V-ORD: same top-level names, same order?**
  - It wrote its own comment-aware lexer and unit-tested it on nested `/- /- -/ -/`, `/--`, `/-!` and comment markers inside the other comment kind.
  - It finds 897 constructs in both files, with exactly the same (kind, name) sequence and set, and per-kind counts identical to OLD's.
  - The generated models (old base and new) have the same 805-construct list. Without helpers and the two moved theorems, the new file equals the new generated model (803 = 803).
  - Every helper has the same neighbours and run position as in OLD, and there are no stray column-0 lines.
  - The raw diff from OLD to the new file is exactly the raw diff between the two generated models plus the 56 logged lines.
- **V-DEV: is the deviation log complete and correct?**
  - Applying the model-only transformation (delete the 5 EXTEND lines, rename `*_case_K` to `K-1` for K ≥ 20, shift the locations) to the whole of `OLD_wasm2.0.lean` gives the new file byte for byte. So OLD and the new file differ in exactly 194 lines: 5 deleted EXTEND lines, 133 generated lines and the 56 logged lines.
  - Every rename maps to the unique constructor with identical text, and every logged line is inside a proof body.
  - There is no hand-written use of `EXTEND`, of `*_case_19`, or of a renumbered `instr_case_K`. Nothing depends on constructor position: there is no `.rec`, `.casesOn` or `match`, and no positional `rcases`, on `wf_instr`/`wf_admininstr`.
  - Sections 1–3 of this document match its own counts.

The agents also raised four wording points about the draft of this document. All are fixed above:
- the block versus run count of helpers;
- that 1,865 is the total of the hand-written text, of which 1,809 lines are verbatim;
- the full description of the hand edits;
- why 13 of the 56 renamed lines produced no compile error of their own.

Their results are in `../evidence/verification/`.
