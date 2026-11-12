# 4. `Extend_store_moduleinst`

*(Previous: [03-reduce-inst-unchanged.md](03-reduce-inst-unchanged.md). Next: [05-t-preservation-vs-type.md](05-t-preservation-vs-type.md).)*

**Plain-English summary.** If the store only grew, every fact "address `a` in module instance `i` has type `t`" that held in the old store still holds in the new one — growing the store can't invalidate an existing module's view of it, because every component only ever grows or (for globals/data/elem) changes in a way that's compatible with its old type.

**Code** — [ExtensionLemmas.lean:1754-1781](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1754-L1781):
```lean
/-- Rocq `Extend_store_moduleinst` (was `store_extension_moduleinst`). **The
    key assembly lemma**, reused by `type_preservation.v`'s
    `step_moduleinst`. -/
theorem Extend_store_moduleinst (v_S v_S' : store) (v_i : moduleinst) (v_C : context) :
    Extend_store v_S v_S' → Moduleinst_ok v_S v_i v_C → Moduleinst_ok v_S' v_i v_C := by
  intro hext h
  have hwfS' : wf_store v_S' := Extend_store_wf_store' v_S v_S' hext
  obtain ⟨_, hgb', hge, _, hmb', hme, _, htb', hte, _, hfb', hfe,
          _, hdb', hde, _, heb', hee, _, _⟩ := id hext
  cases h with
  | mk_Moduleinst_ok ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 _
      h21 h22 h23 h24 h25 h26 =>
    exact Moduleinst_ok.mk_Moduleinst_ok v_S' ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl
      h1 h2 (addrss_store_globals_extension v_S v_S' gal gtl hwfS' h3 hgb' hge)
      h4 (addrss_store_funcs_extension v_S v_S' fal ffl hwfS' h5 hfb' hfe)
      h6 (addrss_mems_extension v_S v_S' mal mtl hwfS' h7 hmb' hme)
      h8 (addrss_tables_extension v_S v_S' tal ttl hwfS' h9 htb' hte)
      (Extend_store_exts v_S v_S' eil hext h10)
      h11
      (fun a ha => hdb' a (List.mem_range.mpr (h12 a ha)))
      (fun p hp => Extend_store_datainst_ext v_S v_S' _ _ p.2 hext
        (hde p.1 (List.mem_range.mpr (h12 p.1 (List.of_mem_zip hp).1))) (h13 p hp))
      h14
      (fun a ha => heb' a (List.mem_range.mpr (h15 a ha)))
      (fun p hp => Extend_store_eleminst_ext v_S v_S' _ _ p.2 hext
        (hee p.1 (List.mem_range.mpr (h15 p.1 (List.of_mem_zip hp).1))) (h16 p hp))
      h17 h18 h19 hwfS' h21 h22 h23 h24 h25 h26
```

**Signature.** `Extend_store v_S v_S'` (the growth fact) plus `Moduleinst_ok v_S v_i v_C` (the old typing) implies `Moduleinst_ok v_S' v_i v_C` — *same* `v_i`, *same* `v_C`; only the store argument changes. This is the lemma `type_preservation.v`'s own doc comment calls "the key assembly lemma, reused by `step_moduleinst`" (confirmed in the Lean port's own comment too).

**Proof sketch.** Destructure `Extend_store` once to get its twenty component facts (one in-bounds-forward, one in-bounds-backward, one per-address `Extend_*inst` fact, times six store sorts). Destructure `Moduleinst_ok`'s one constructor to get the module instance's own fourteen component facts. Rebuild the *same* constructor for `v_S'`, replacing each "address `a` resolves to something of type `t`" fact with a version re-derived through the matching `Extend_*`: `addrss_store_globals_extension`/`_funcs_extension`/`_mems_extension`/`_tables_extension` each do "old resolves at type `t`, and the store only extended at that sort, so new resolves at the *same* `t`" for globals/funcs/mems/tables (where the type absolutely cannot change); elements and data get the slightly different `Extend_store_exts`/`Extend_store_datainst_ext`/`Extend_store_eleminst_ext` treatment (since those two sorts can also "change" by being dropped to `[]`, which `Eleminst_ok`/`Datainst_ok` happen to tolerate because the all-`[]`/all-dropped instance is still well-typed at its original declared type — an empty list of refs still has every ref at the claimed reftype, vacuously).

---
*Next: [05-t-preservation-vs-type.md](05-t-preservation-vs-type.md).*
