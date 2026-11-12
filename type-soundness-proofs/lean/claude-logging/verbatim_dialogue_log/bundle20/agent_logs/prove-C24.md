# prove-C24 — bundle20 progress port, proof batch C24

Agent label: `prove-C24`. Brief: `scratchpad/briefs/progress_prove_brief.md`; task: `scratchpad/briefs/task_prove-C24.md`.
Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C24/`
(`Work.lean` = header copied verbatim by script from TypeProgress.lean:2501-2520, renamed `_proof`, + rfl guard).
No repo file other than this log was written. No agents spawned. No state-changing git. One Lean process at a time.

## Safety check — START (run from /home/zhengyew/spectec)

```
$ bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C24
safety check [prove-C24] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T140623.034932324Z-prove-C24-1521217.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Target 1/1: `t_progress_e_Instr_ok2_frame` (TypeProgress.lean:2501) — PROVED

Rocq source: `type_progress.v:5689-5760` (bullet `Instr_ok2__frame` of `t_progress_e`).

Port notes (follows the Rocq bullet step by step):
- `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs ...` -> injection of `Htf` gives `ts1 = []`, then
  `List.map_eq_nil_iff` gives `vcs = []`; `simp only [List.map_nil, List.nil_append]` normalises config/goal.
- `inversion HExprOk` -> `cases HExprOk with | mk_Expr_ok2 _ _ _ h _ _ _ => exact h` (typing of the frame body,
  `Hadmin : Instrs_ok2 s ({..RETURN := some t..} ++ C') es (mkFunctype [] t)`).
- `return_reduce` case: `return_reduce_extract_vs` + `Step.pure` + `Step_pure.return_frame` (append reassociated
  with `List.append_assoc`, `Map` unfolded). Rocq's `Hlookup` (via `frame_t_context_return_empty`) is `rfl` in Lean,
  since the appended context's `RETURN` is `Option.orElse (some _) _`.
- not-`return_reduce` case: `not_return_reduce_not_lf_return`, `s_typing_not_lf_br` (its `prepend_return C' t` is
  definitionally the appended context), Rocq's `prepend_return C' t = upd_return C' (Some t)` assertion is `rfl`;
  then the IH (`t_progress_e_P1`) splits into `frame_vals` (via `const_es_exists`) / `trap_frame` / `ctxt_frame`
  (+ `Step_is_wf` for the reduct's well-formedness, as in Rocq).
- Deviation (Lean way, fewer sorry deps): the inner-frame configuration well-formedness is built from the
  `admininstr_case_72` inversion of `wf_admininstr (FRAME_ ..)` + `wf_store s` (exactly Rocq's case-(c)
  `inversion HWfinstr; state_case_0; config_case_0`), instead of the still-`sorry` `wf_config_frame`.
- Pitfall hit: `omega` cannot close `v_n = vcs2.length` with `v_n : n` (`abbrev n := Nat`); replaced by
  `Hsize.trans Hsize'.symm`.

Still-`sorry` earlier lemmas used (all before line 2501 of TypeProgress.lean):
`const_es_exists` (110), `not_return_reduce_not_lf_return` (339), `s_typing_not_lf_br` (498),
`return_reduce_extract_vs` (540). Also uses generated `Step_is_wf` (wasm2.0.lean:16045), whose
`#print axioms` already includes `sorryAx` (pre-existing project fact). No new axioms; `by_cases` is classical.

`#print axioms t_progress_e_Instr_ok2_frame_proof`:
```
'TLC.t_progress_e_Instr_ok2_frame_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Proof body (tactic block after `:= by`, exactly as compiled):

```lean
  intro C v_n f es t C' HFrameOk HExprOk HWfS HWfC HWfC' HWfinstr HWfC'' Hsize IH
  unfold t_progress_e_P
  intro f' C'' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts ...` (vcs = [])
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  subst Htf1
  have Hvcs : vcs = [] := List.map_eq_nil_iff.mp Hts
  subst Hvcs
  simp only [List.map_nil, List.nil_append] at HWfConfig ⊢
  -- the typing of the frame body, from `Expr_ok2` (Rocq: `inversion HExprOk`)
  have Hadmin : Instrs_ok2 s
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [], RETURN := some (list.mk_list t) } : context) ++ C')
      es (mkFunctype [] t) := by
    cases HExprOk with
    | mk_Expr_ok2 _ _ _ h _ _ _ => exact h
  by_cases Hretred : return_reduce es
  · -- `return_reduce es`: the frame reduces by `return_frame`
    obtain ⟨vcs', es', Hes⟩ := Hretred
    right
    have Hexists : ∃ (vcs : List val) (es' : List admininstr),
        es = List.map admininstr_val vcs ++ ([admininstr.RETURN] ++ es') := ⟨vcs', es', Hes⟩
    -- Rocq derives this from `frame_t_context_return_empty`; in Lean the `RETURN` field of the
    -- appended context is `Option.orElse (some _) _`, which reduces to `some _`.
    have Hlookup : ((({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [], RETURN := some (list.mk_list t) } : context) ++ C').RETURN = some (list.mk_list t)) := rfl
    obtain ⟨vcs1, vcs2, es'', Hes', Hsize'⟩ :=
      return_reduce_extract_vs s _ t (list.mk_list t) es Hexists Hadmin Hlookup
    refine ⟨s, f', List.map admininstr_val vcs2, ?_⟩
    rw [Hes']
    apply Step.pure
    have Hn : v_n = vcs2.length := by
      simp only [proj_list_0] at Hsize'
      exact Hsize.trans Hsize'.symm
    have Hred := Step_pure.return_frame v_n f vcs1 vcs2 es'' Hn
    simp only [Map, List.append_assoc] at Hred
    exact Hred
  · -- not `return_reduce es`: use the induction hypothesis on the frame body
    have Hnotret' : not_lf_return es := not_return_reduce_not_lf_return es Hretred
    have Hnotbr'' : not_lf_br es :=
      s_typing_not_lf_br s f C' (list.mk_list t) es [] t HFrameOk Hadmin
    -- well-formedness of the body under the inner frame `f` (Rocq: `wf_config_frame` /
    -- inversion of `HWfinstr`)
    have HWfFrame2 : wf_config (config.mk_config (state.mk_state s f) es) := by
      cases HWfinstr with
      | admininstr_case_72 _ _ _ hf hes =>
        exact wf_config.config_case_0 _ _ (wf_state.state_case_0 s f HWfS hf) hes
    have H : (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [], RETURN := some (list.mk_list t) } : context) ++ C') =
        upd_return C' (some (list.mk_list t)) := rfl
    unfold t_progress_e_P1 at IH
    rcases IH f C' (some (list.mk_list t)) HWfFrame2 H HFrameOk Hstore Hnotbr'' Hnotret' with
      ⟨Hconst, Hlen⟩ | Htrap | ⟨s', f'', es', Hprog⟩
    · -- body is all values: `frame_vals`
      right
      obtain ⟨vs, Hvs⟩ := const_es_exists es Hconst
      subst Hvs
      refine ⟨s, f', List.map admininstr_val vs, ?_⟩
      apply Step.pure
      have Hn : v_n = vs.length := by
        simp only [List.length_map, proj_list_0] at Hlen
        exact Hsize.trans Hlen.symm
      exact Step_pure.frame_vals v_n f vs Hn
    · -- body is `[TRAP]`: `trap_frame`
      right
      subst Htrap
      exact ⟨s, f', [admininstr.TRAP], Step.pure _ _ _ (Step_pure.trap_frame v_n f)⟩
    · -- body steps: `ctxt_frame`
      right
      exact ⟨s', f', [admininstr.FRAME_ v_n f'' es'],
        Step.ctxt_frame s f' v_n f es s' f'' es' Hprog HWfFrame2
          (Step_is_wf _ _ _ HWfFrame2 Hstore Hprog)⟩
```

## Final Lean check

```
$ cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/prove-C24/Work.lean
(no output)  exit=0   -- includes the guard `example : type_of% @t_progress_e_Instr_ok2_frame_proof = type_of% @t_progress_e_Instr_ok2_frame := rfl`
```

## Safety check — END (run from /home/zhengyew/spectec)

```
$ bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C24
safety check [prove-C24] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T141038.863034365Z-prove-C24-1524568.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```
