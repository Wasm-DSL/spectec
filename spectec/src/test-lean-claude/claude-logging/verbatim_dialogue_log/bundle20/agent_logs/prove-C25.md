# prove-C25 log (bundle20 progress port, proof batch C25)

Agent: subagent `prove-C25`. Brief: `scratchpad/briefs/progress_prove_brief.md`; task: `scratchpad/briefs/task_prove-C25.md`.
Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C25/`
(final checked file: `Final.lean`; Lean output: `final_check.txt`).
No repo file was edited (TypeProgress.lean untouched); the only write inside the repo is this log.

## Safety check at START

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C25`

```
safety check [prove-C25] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T140803.792904869Z-prove-C25-1522363.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Results summary

| target | status | still-`sorry` earlier lemmas used | extra axioms |
|---|---|---|---|
| `t_progress_e_call_addr` (TypeProgress.lean:2525) | proved | `default_not_none` (TypeProgress.lean:59) | none |
| `t_progress_e_ref` (TypeProgress.lean:2538) | proved | none (sorry-free) | none |
| `t_progress_e_trap` (TypeProgress.lean:2547) | proved | none (sorry-free) | none |
| `t_progress_e_empty` (TypeProgress.lean:2556) | proved | `v_to_e_const` (TypeProgress.lean:84) | none |

None uses `sorry`/`admit`/`native_decide` or any new or HelperLemmas axiom. `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` for the two targets that use the still-`sorry`
earlier lemmas. Ordering rule: every TypeProgress lemma used (`default_not_none`:59, `v_to_e_const`:84,
`t_progress_e_P`:2407, `t_progress_e_P0`:2426) comes before its target. Other dependencies come from
imported files: `Externaddr_invert_funcs` and `externtype_func_eq` (ExtensionLemmas), `Forall2_nth_of_length`
(HelperLemmas), `Store_ok_parts`, `wf_store_parts` and `funcinst_ok_parts` (TypePreservation, which
TypeProgress.lean:7 imports for Lean-only helpers as its header note says), `mkFunctype` (Subtyping), and
`default__is_wf`, `Step.read`/`Step.pure`, `Step_read.call_addr` and `Step_pure.trap_vals` (wasm2.0). All of these
non-TypeProgress helpers are sorry-free (checked with `#print axioms`).

## t_progress_e_call_addr — proved

Rocq `type_progress.v:5761-5841`. The port follows the Rocq bullet closely: `right`; inject `Htf` and rewrite
`Hts`; `Externaddr_invert_funcs` then `externtype_func_eq`; destructure the funcinst/func; invert `Store_ok`
to get `Funcinst_ok` at the address, and from it `Func_ok`, which gives `Forall (· ≠ BOT) t_lst`;
`default_not_none` gives `HNotNone`; `wf_funcinst`/`wf_func`/`wf_moduleinst` come from `wf_store`;
`wf_frame` comes from `HWfVals` plus `default__is_wf`; finally `Step.read` (`Step_read.call_addr`).
Lean difference: `cases` on `Func_ok` unifies the bare variable `ls` with `Map LOCAL t_lst` directly, so Rocq's
`ts := map (fun '(LOCAL t) => t) ls` / `inj_map` / `LOCAL_injective` detour is not needed.

```lean
  intro C addr ts1 ts2 Hext HWfS HWfC HWfAIs HWfExtType
  unfold t_progress_e_P
  intro f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  obtain ⟨xt, funcinst, HBound, HLookup, HEq, HWf, HSub⟩ := Externaddr_invert_funcs _ _ _ Hext
  subst HEq
  have HSub' := externtype_func_eq _ _ HSub
  obtain ⟨ft, minst, func⟩ := funcinst
  obtain ⟨x, ls, es⟩ := func
  simp only at HSub'
  subst HSub'
  simp only [lookup_total] at HLookup
  obtain ⟨_, _, _, ftl, _, _, _, _, _, _, _, _, hflen, hfok, _⟩ := Store_ok_parts _ Hstore
  have hfiok : Funcinst_ok s (s.FUNCS[addr]!) (ftl[addr]!) :=
    Forall2_nth_of_length _ _ hfok hflen addr HBound
  rw [HLookup] at hfiok
  have hwffi := (wf_store_parts s HWfS).1 (s.FUNCS[addr]!)
    (by rw [getElem!_pos s.FUNCS addr HBound]; exact List.getElem_mem HBound)
  rw [HLookup] at hwffi
  obtain ⟨C0, hmi0, hfo, hwfC0⟩ := funcinst_ok_parts _ _ _ _ _ hfiok
  cases hfo with
  | mk_Func_ok _ t_lst _ _ _ _ _ hbot _ _ hwffunc _ =>
    have HNotNone : Forall (fun t => default_ t ≠ none) t_lst := default_not_none t_lst hbot
    have hwfmi : wf_moduleinst minst := by
      cases hwffi with
      | funcinst_case_ _ _ _ h1 _ => exact h1
    have hwfvals : Forall (fun v => wf_val v) (vcs ++ Map (fun t => Option.get! (default_ t)) t_lst) := by
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact HWfVals v hv
      · simp only [Map, List.mem_map] at hv
        obtain ⟨t, ht, rfl⟩ := hv
        exact default__is_wf t _ (HNotNone t ht) rfl
    have hlen : vcs.length = ts1.length := by rw [← Hts, List.length_map]
    refine ⟨s, f, [admininstr.FRAME_ ts2.length
      ({ LOCALS := vcs ++ Map (fun t => Option.get! (default_ t)) t_lst, MODULE := minst } : frame)
      [admininstr.LABEL_ ts2.length [] (Map (fun i => admininstr_instr i) es)]], ?_⟩
    apply Step.read
    exact Step_read.call_addr (state.mk_state s f) vcs.length vcs addr ts2.length _ es ts1 ts2 minst _ x t_lst
      HBound HLookup rfl HNotNone rfl hwffi hwffunc (wf_frame.frame_case_ _ _ hwfvals hwfmi) rfl hlen rfl
```

## t_progress_e_ref — proved (sorry-free)

Rocq `type_progress.v:5841-5849`: `left`; from `Htf` get `ts1' = []`, so `map typeof vcs = []` and `vcs = []`
(Rocq's `invert_typeof_vcs`); then `destruct ref; by left`.

```lean
  intro C v_ref rt HRefOk HWfS HWfC
  unfold t_progress_e_P
  intro f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  left
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1, List.map_eq_nil_iff] at Hts
  subst Hts
  left
  cases v_ref <;> rfl
```

## t_progress_e_trap — proved (sorry-free)

Rocq `type_progress.v:5849-5868`: case on `vcs`. Empty: `left; right` (`[TRAP]`). Non-empty:
`right`, step `pure` by `trap_vals` with `val_lst := vc :: vcs`, `admininstr_lst := []`.

```lean
  intro C ts1 ts2 HWfS HWfC HWfinstr
  unfold t_progress_e_P
  intro f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  cases vcs with
  | nil =>
    left
    right
    rfl
  | cons vc vcs =>
    right
    refine ⟨s, f, [admininstr.TRAP], ?_⟩
    apply Step.pure
    have H := Step_pure.trap_vals (vc :: vcs) [] (Or.inl (List.cons_ne_nil vc vcs))
    simpa [Map] using H
```

## t_progress_e_empty — proved

Rocq bullet `Admin_instrs_ok__empty` (`type_progress.v:5869-5874`, right after the trap bullet; the task
file said there was no separate Rocq bullet, but there is one):
`left. rewrite cats0 /terminal_form. left. by apply: v_to_e_const.`, ported one-to-one.

```lean
  intro C HWfS HWfC
  unfold t_progress_e_P0
  intro f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  left
  rw [List.append_nil]
  left
  exact v_to_e_const vcs
```

## Final Lean check

Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/prove-C25/Final.lean`
(the file contains all four `*_proof` theorems with verbatim-copied headers, each followed by the guard
`example : type_of% @<name>_proof = type_of% @<name> := rfl`, plus `#print axioms`). Exit code 0; full output:

```
'TLC.t_progress_e_call_addr_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_e_ref_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_e_trap_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_e_empty_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

(`sorryAx` comes only from the earlier still-`sorry` lemmas `default_not_none` (call_addr) and `v_to_e_const`
(empty). Checked with `#print axioms`: `default_not_none` and `v_to_e_const` both depend on `sorryAx`; every
other helper used is sorry-free.)

## Note for the main thread

The brief (section 4) says TypePreservation is "NOT imported here", but TypeProgress.lean:7 does
`import TypePreservation`, and the file header (lines 36-39) says this is deliberate, so its Lean-only
helpers can be reused. The `call_addr` proof uses three such inversion helpers (`Store_ok_parts`,
`wf_store_parts`, `funcinst_ok_parts`). If that import is ever dropped, these would have to be restated locally.

## Safety check at END

Command (from `/home/zhengyew/spectec`): `bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C25`

```
safety check [prove-C25] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T141417.683934957Z-prove-C25-1526621.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```
