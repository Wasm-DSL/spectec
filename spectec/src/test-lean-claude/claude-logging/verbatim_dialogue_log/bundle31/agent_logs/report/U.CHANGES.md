# Changes made by report updater U

Input: `b31/report/agents/V-<label>/section.verified.md`, which was checked against the scratch
build `b31/final3`. Output: `b31/report/agents/U/<label>.md`, which is true of the installed files.
The installed files are byte-identical to `b31/final4/src/*.lean` (checked by md5 for all nine
modules, `wasm2.0.lean` included). The installed `wasm2.0.lean` and `OLD_wasm2.0.lean` are also
byte-identical to `b31/model/wasm2.0.lean` and `b31/model/OLD_wasm2.0.lean`.

Line references: none of the eleven sections cites a line number in a final3 module. The only
mention of final3 is the line-number note in INFRA, which was rewritten (INFRA item 4), so the line
maps `f3f4/*.linemap.tsv` were not needed. Spec, model, Rocq and orig references keep their
numbers. In INFRA the bare spec references ("line 264", "lines 59-62", …) now name their file.

## P1

1. `t_read_preservation`, last paragraph: "The final build's audits (… across all 5525 theorems)"
   now reads "The audits of the final build b31/final4, whose sources are byte-identical to the
   installed files (… across all 5517 theorems)". Source: `b31/final4/audit/report.txt` ("theorems
   checked: 5517", "theorems needing a default value: 0") and `b31/final4.out` ("theorems
   depending on sorryAx: 0"). Final3 had 5525 theorems. The 8 deleted lemmas account for the
   difference.

No other change. `default_val_ok` mentions only lemmas that still exist. The section does not
quote the revised `t_read_preservation` doc comment, and the new doc agrees with the sketch.

## P23

1. `store_extension_reduce_aux`: "The doc comment was updated." now gives the installed doc's
   content: "the store-writing rules invert their `fun_with_*` premise, and the four memory stores
   hand `fun_with_mem` to `with_mem_store_ok`, which inverts it". The cleanup added the second
   half of that sentence.
2. `reduce_inst_unchanged_aux`: the description of the doc comment gains one sentence, matching
   the cleanup's correction: "It also says that `ctxt_frame` needs no induction hypothesis
   either, since it changes only the store and the inner frame." The old doc had said that
   `ctxt_frame` "is in the first group".

No other change. The proof sketches are untouched. P23 mentions `splice_eq_list_slice_update`
only as a lemma used by `with_mem_store_ok` and does not quote its revised doc comment.
(`wf_store_mem_update`, whose doc was also revised, is not covered by any section.)

## Q1

1. `t_progress_be_testop`, Current proof sketch: the hypothesis `ENone` is renamed `Etestop`
   (three occurrences: the `testop_not_none` result and its two uses in `Step_pure.testop …` and
   `testop__is_wf …`), as at installed `TypeProgress.lean:4640`, `:4644` and `:4645`. The "What
   broke and why" paragraph keeps `cases ENone : fun_testop_ …`, because it quotes the original
   proof (`orig/TypeProgress.lean:4451`).

No other change. Q1 does not quote the revised `testop_not_none` doc comment, and its statement
paraphrase agrees with the new doc.

## Q2, Q3, Q4, Q5, Q6b

No change. These sections cite no final3 line numbers and do not mention the deleted lemmas,
`ENone` or `Moduleinst_ok_data_addr`. They do not quote or describe the doc or inline comments
that the cleanup changed in their constructs:
- Q2: the inline comments in `vunop_real` and `vrelop_some`;
- Q4: the doc of `zero_lane_wf`;
- Q5: the inline comments in `t_progress_be_elem_drop` and `t_progress_be_table_init`;
- Q6b: the `-- memory 0 exists` comment added to the four vload/vstore cases.

Q3's constructs were not touched by the cleanup. In the constructs above, the cleanup changed only
comments, so the fact-checked sketches still hold for the installed files.

## Q6a

1. `t_progress_be_memory_init`, Current proof sketch: "That lemma combines `|F.module.dataaddrs| =
   |C'.datas|` with the `Moduleinst_ok` premise that every data address is `< |S.datas|`" now
   reads "… `|C'.datas|` (`Moduleinst_ok_lengths`) with `minst_invert_datas`, which reads off the
   `Moduleinst_ok` premise that every data address is `< |S.datas|`". This matches the new proof
   of `Moduleinst_ok_data_addr`.

No other change. Q6a does not quote the revised inline comments in `t_progress_be_data_drop`,
`t_progress_be_load_val` and `t_progress_be_load_pack`, and those comments agree with its
sketches.

## MAIN

1. `num_default`, Current proof sketch: "The text is unchanged." now reads "The text of the
   definition is unchanged (the final cleanup rewrote only its doc comment)."

No other change. MAIN's claim that nothing in Rocq uses `num_default` is kept: it is correct, and
the installed doc comment now contradicts it (see Problems). MAIN does not quote the revised doc
comments of `bt_inversion`, `wf_config_mem_bytes` or `mem_bytes_wf`, and those docs agree with its
text.

## INFRA

1. Title: 55 declarations becomes 47.
2. Intro: "These 55" becomes "These 47". HelperLemmas has 36 of them (was 42) and TypeProgress
   has 11 (was 13).
3. Audit paragraph: the final build is now named (b31/final4, whose sources are byte-identical to
   the installed files). "45 theorems among these 55 declarations" becomes "37 theorems among
   these 47 declarations"; the other 10 are still definitions. Reflowed.
4. Line-number note: the old note said "Line numbers refer to the scratch copies
   `b31/final3/src/*.lean`, …". It now says:
   - module names refer to the installed files, and the section cites no line numbers in them;
   - model line numbers refer to `b31/model/wasm2.0.lean` and `b31/model/OLD_wasm2.0.lean`,
     each byte-identical to its installed counterpart.
5. Family table:
   - A: 8 defs + 16 lemmas becomes 8 defs + 13 lemmas.
   - B: 2 defs + 8 lemmas becomes 2 defs + 7 lemmas.
   - C: 8 lemmas becomes 6, and the "Replaces" column drops `fun_func` and `fun_data`.
   - D: 6 + 7 lemmas becomes 5 + 6.

   The "Used by" columns are unchanged, because the deleted lemmas had no users.
6. A heading: 24 declarations becomes 21.
7. A, Wasm 2.0: "(line 264)", "(line 334)", "(line 359)" and "(line 386)" become
   `1-syntax.spectec:264`, `:334`, `:359` and `:386`. The numbers are unchanged; only the file is
   now named.
8. A, Current construct:
   - "Each of the eight functions has three declarations" becomes "a definition and one or two
     bridging lemmas".
   - "Together they give `fun_X a n ↔ n = X a`" is replaced by which views have which lemmas.
     `lsize`, `sizenn`, `lsizenn`, `lsizenn1` and `lsizenn2` have both. `isize` and `jsize` have
     only `fun_X_X`, and `sizenn1` has only `fun_X_eq`, "because the proofs use no more". Where
     both lemmas exist, they give the iff.
9. A, Proofs:
   - `fun_sizenn1_sizenn1` is removed from the `fun_X_X` bullet.
   - In the `fun_X_eq` bullet, "For the derived relations" becomes "For the derived relations
     (`lsizenn*`)", since `fun_jsize_eq` is gone.
10. A, end: the sentences "Three of the lemmas are unused: `fun_isize_eq`, `fun_jsize_eq` and
    `fun_sizenn1_sizenn1`. They were kept so that each view has both bridging lemmas." are deleted.
11. B heading: 10 declarations becomes 9.
12. B, Wasm 2.0: "(lines 59-62)" and "(lines 40-52)" become `1-syntax.spectec:59-62` and
    `1-syntax.spectec:40-52`.
13. B, What broke downstream: "keep their text unchanged" gains "(the final cleanup rewrote only
    `num_default`'s doc comment)".
14. B, Current constructs: the `fun_fzero_wf` sub-bullet is removed.
15. C heading: 8 declarations becomes 6.
16. C, Current constructs: "For X ∈ {func, global, table, mem, elem, data}" becomes "For X ∈
    {global, table, mem, elem}".
17. C: "Two lemmas are unused: `fun_func_inv` … `fun_data_inv` …" becomes "`fun_func` and
    `fun_data` have no inversion lemma, because no proof inverts them". The two reasons are kept
    word for word, now labelled `fun_func` and `fun_data`. Checked: no installed downstream module
    mentions `fun_func`, and `fun_data` occurs only in the TypeProgress section doc and in
    `fun_data_typed`, which builds a witness.
18. D heading: 13 declarations becomes 11.
19. D, Why they are needed: "lines 427-429" becomes `6-typing.spectec:427-429`, "lines 207-209"
    becomes `6-typing.spectec:207-209`, and "line 131" becomes `B-soundness.spectec:131`.
20. D, Current constructs: the X sets of `Moduleinst_ok_X_addr` and `fun_X_typed` no longer
    contain `func`. They are now {global, mem, table, data, elem}.
21. D, Proof, data bullet: the old text said the bound "is read directly from `Moduleinst_ok`'s
    premise … at element i", which described the removed positional `cases` on
    `mk_Moduleinst_ok`. It now describes the new proof:
    - `minst_invert_datas s minst C C h ⟨rfl, …⟩` gives the store bound per address, not per
      pair: every a in `minst.DATAS` has a < |s.DATAS| and a data instance at a, read off
      `Moduleinst_ok`'s premise.
    - Its second component is applied to `minst.DATAS[i]!`, which lies in `minst.DATAS` by
      `getElem!_pos` and `List.getElem_mem`, so no zip pair is needed.

    Installed `TypeProgress.lean:2974-2981`.
22. D, Not needed: "So `fun_func_typed` is unused, and so is `Moduleinst_ok_func_addr`, whose
    only user is `fun_func_typed`." becomes "So no progress case builds a `fun_func` witness, and
    the family has no lemma for function addresses."
23. Per-construct table:
    - The rows of the 8 deleted lemmas are removed. The table now has 47 rows (36 HelperLemmas,
      11 TypeProgress), which match the installed declarations one to one (checked by script).
    - The `fun_global_inv` row now states both bounds itself. Its old text, "The same for
      `$global`: both bounds", referred to the deleted `fun_func_inv` row, and the row above it
      is now `fun_type_inv`, which has a single bound.
    - The proof idea of the `Moduleinst_ok_data_addr` row now names `minst_invert_datas`,
      applied at element i (`getElem!_pos`, `List.getElem_mem`).
24. Observations:
    - The "Unused." bullet is replaced by one short paragraph, "Deleted as unused". It says that
      eight more lemmas were written and then deleted in the final cleanup because no other proof
      used them, names them with their modules, and notes that `Moduleinst_ok_func_addr` was used
      only by `fun_func_typed`.
    - The "Comment precision" bullet and its five remarks are dropped. The cleanup resolved all
      five, as checked against the installed text:
      1. The HelperLemmas header now says the axioms come "(after Section 9)" and mentions the
         Lean-only infrastructure "at the end of the file".
      2. The Function-views header now names `$fzero`'s trigger ("for `$fzero`, the
         well-formedness of its result") and the `fzero` exception (`fun_fzero_32`,
         `fun_fzero_64`).
      3. The TypeProgress header now says "(except for `fun_type`) the address into the store".
      4. The Function-views header now restores views only of "the size functions, `fzero` and
         `default_`". It says that the other relations (`fun_zero`, `fun_unop_`, …) are used
         through their constructors.
      5. The Inversion subsection now says that the lemmas are needed when the output is a term
         (`bt_inversion`) "and are convenient elsewhere".
25. Lines touched by the edits were rewrapped to the section's width. Nothing else changed: the
    proof sketches keep their wording.

## Problems found (not fixed; repository files are out of scope)

- The installed doc comment of `num_default` (`TypePreservation.lean:41-44`) says: "Rocq uses it
  for the default locals of `t_read_preservation`'s Call_addr case". The Rocq sources do not
  support this.
  - In `spectec/test-rocq/theories`, `num_default` occurs only at its definition
    (`type_preservation.v:19`) and in the commented-out `num_default_is_well_formed`
    (`type_preservation.v:75-76`).
  - The Rocq Call_addr case (`type_preservation.v:1838` ff.) types the default locals inline,
    with `destruct a`.

  MAIN states, correctly, that nothing in Rocq uses `num_default`. The rest of that doc comment is
  accurate.
- Minor: the Function-views header says that the section restores "a function view of the size
  functions". `$fsize`, `$sizenn2` and `$shsize` have no view, as INFRA A says. The header is
  accurate if read as "the size functions the proofs use".
