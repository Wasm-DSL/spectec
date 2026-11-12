# 1. `t_preservation` — the top-level theorem

*(Previous: [00-primer.md](00-primer.md). Next: [02-store-extension-reduce.md](02-store-extension-reduce.md).)*

**Plain-English summary.** This is it — WASM 2.0's type soundness statement, preservation half. *If* a machine configuration is well-typed at some result type `ts`, *and* it takes one step, *then* the new configuration is still well-typed at that same `ts`. Nothing about execution ever invalidates the type system's guarantees. The Rocq source literally comments this lemma `(* Ultimate goal of project *)`.

**Code** — [TypePreservation.lean:2695-2752](../../../../../src/test-lean-claude/TypePreservation.lean#L2695-L2752):
```lean
/-- Rocq `type_preservation.v:2668` `t_preservation`. **THE top-level theorem** — Rocq
    source comment: `(* Ultimate goal of project *)`. Whole-program preservation: reduction
    (`Step`) on a full `config` preserves well-typedness at the same fixed result type.
    `Qed` in Rocq; proved here by the same composition (`store_extension_reduce`,
    `t_preservation_vs_type`, `t_preservation_type`, `reduce_inst_unchanged`,
    `Extend_store_moduleinst`). Its remaining `sorry` dependencies are listed in
    `claude-logging/for-claude/is_wf_theorems.md` (generated `*_is_wf` theorems). -/
theorem t_preservation (c1 : config) (ts : resulttype) (c2 : config) :
    Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts := by
  intro hstep hcfg
  obtain ⟨⟨s1, f1⟩, ais1⟩ := c1
  obtain ⟨⟨s2, f2⟩, ais2⟩ := c2
  cases hcfg with
  | mk_Config_ok _ _ _ t_lst C hstate hexpr hwfC hwfcfg _ =>
    cases hstate with
    | mk_State_ok _ _ _ hsok hframe _ _ =>
      cases hframe with
      | mk_Frame_ok val_lst v_minst t_lst0 C0 hminst hlen hvals _ hwfC0 _ hwflocC =>
        cases hexpr with
        | mk_Expr_ok2 _ _ _ hinstrs _ _ _ =>
          -- well-formedness of the post-state, from the generated `Step_is_wf`
          have hwfcfg2 : wf_config (config.mk_config (state.mk_state s2 f2) ais2) :=
            Step_is_wf _ _ _ hwfcfg hsok hstep
          have hwfais2 : Forall wf_admininstr ais2 := by
            cases hwfcfg2 with | config_case_0 _ _ _ h => exact h
          have hwfst2 : wf_state (state.mk_state s2 f2) := by
            cases hwfcfg2 with | config_case_0 _ _ h _ => exact h
          have hwfs2 : wf_store s2 := by
            cases hwfst2 with | state_case_0 _ _ h _ => exact h
          have hwff2 : wf_frame f2 := by
            cases hwfst2 with | state_case_0 _ _ _ h => exact h
          -- the module context's own LOCALS are empty, so the appended context's
          -- LOCALS are exactly the frame's local types
          have hloc : C0.LOCALS = [] := inst_t_context_local_empty s1 v_minst C0 hminst
          have him := inst_match_locals_append t_lst0 C0
          -- store extension + store typedness across the step
          obtain ⟨hext, hsok2⟩ := store_extension_reduce s1 _ ais1 s2 f2 ais2 C0 _ _
            hwfcfg hstep hminst hinstrs him hsok
          have hmod := reduce_inst_unchanged s1 _ ais1 s2 f2 ais2 hstep
          have hminst2 : Moduleinst_ok s2 v_minst C0 :=
            Extend_store_moduleinst s1 s2 v_minst C0 hext hminst
          -- locals stay well-typed
          have hvals2 := t_preservation_vs_type s1 _ ais1 s2 f2 ais2 C0 _ [] t_lst hstep hsok
            hext hminst (by rw [locals_append_eq t_lst0 C0 hloc]; exact ⟨hlen, hvals⟩) him hinstrs
          rw [locals_append_eq t_lst0 C0 hloc] at hvals2
          obtain ⟨hlen2, hvals2'⟩ := hvals2
          -- and so does the instruction sequence
          have hinstrs2 := t_preservation_type s1 _ ais1 s2 f2 ais2 C0 _ [] t_lst hwfcfg hstep
            hsok hsok2 hext hminst hminst2
            (by rw [locals_append_eq t_lst0 C0 hloc]; exact ⟨hlen, hvals⟩) him hinstrs
          -- reassemble
          exact Config_ok.mk_Config_ok s2 f2 ais2 t_lst _
            (State_ok.mk_State_ok s2 f2 _ hsok2
              (Frame_ok.mk_Frame_ok s2 f2.LOCALS f2.MODULE t_lst0 C0
                (by rw [← hmod]; exact hminst2) hlen2 hvals2' hwfs2 hwfC0 hwff2 hwflocC)
              hwfC hwfst2)
            (Expr_ok2.mk_Expr_ok2 s2 _ ais2 t_lst hinstrs2 hwfs2 hwfC hwfais2)
            hwfC hwfcfg2 hwfst2
```

**Signature.** `c1 c2 : config` are the full before/after machine states; `ts : resulttype` is the fixed type the whole configuration is checked at (think: "the overall program's declared result type"). `Step c1 c2` is one execution step; `Config_ok c1 ts` is the hypothesis; `Config_ok c2 ts` — *same* `ts` — is the conclusion. Note what's *not* parametrized: there's no weakening of `ts` between the two sides. One step can't change what type the whole computation is ultimately aiming for.

**Proof sketch.** Destructure `c1`/`c2` into `(store, frame, instrs)` triples, then peel `Config_ok` → `State_ok` → `Frame_ok` (which itself contains `Moduleinst_ok` and the locals' typing) and `Expr_ok2` via three nested `cases`. That hands you five separate facts about the *pre*-state. Get well-formedness of the *post*-state from the generated `Step_is_wf` (whose own proof is complete, though it rests on `Step_read_is_wf` — primer §0.4). Then compute five facts about the transition, each delegated to one child lemma: the store extends and stays `Store_ok` (`store_extension_reduce`), the frame's module instance is literally unchanged (`reduce_inst_unchanged`), that unchanged module instance is still `Moduleinst_ok` in the bigger store (`Extend_store_moduleinst`), the locals are still well-typed (`t_preservation_vs_type`), and the instruction sequence is still well-typed (`t_preservation_type`). Finally, `exact Config_ok.mk_Config_ok ...` re-assembles exactly the same nested structure for `c2` out of those five facts — the "re-packs the same structure for `c2`" the diagram promised.

**Proof status.** The proof term above is complete, but through its children it rests on 33 `sorry`'d declarations: `Step_read_is_wf`, which is false in one corner case of the bulk memory operations (file `08` §8.11), and 32 generated lemmas asserting that WASM's numeric primitives — left `opaque` in this backend — return well-formed results (primer §0.4).

---
*Next: [02-store-extension-reduce.md](02-store-extension-reduce.md).*
