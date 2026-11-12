# prove-C04 — bundle20 progress port, proof batch C04

Subagent `prove-C04`. Task: fill the `sorry` bodies of five `TypeProgress.lean` case lemmas by
porting the matching bullets of Rocq `t_progress_be` (`spectec/test-rocq/theories/type_progress.v`).
No repo file was edited. The only files written were this log and the scratch files
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C04/Work.lean`
and `Work2.lean` (`Work.lean` plus `#print axioms`). Exactly one Lean process ran at a time, using
`lake env lean` (no `lake build`).

## Safety check: START

Run from `/home/zhengyew/spectec`:
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C04`

```
safety check [prove-C04] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T131525.170205236Z-prove-C04-1491681.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method

Each target's header was copied verbatim into `Work.lean`, with only the theorem renamed to
`<name>_proof`. A guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` follows each
one. All five guards pass, so each tactic block below fits the real file unchanged.
`TypeProgress.lean` has no file-level `open`, `set_option` or `variable`, so the scratch context
matches the real one.

Each proof starts by introducing the minor-premise binders, then runs `unfold t_progress_be_P`, then
introduces the Rocq names `s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret`.
From there it follows the Rocq bullet.

Ordering: every `TypeProgress` lemma used comes before line 1674, where `t_progress_be_call`
starts: `wf_config_app` :65, `typeof_append` :188, `invert_typeof_I32` :209,
`invert_typeof_numtype` :225, `not_lf_return_singleton` :349, `funcs_size` :563,
`unop_not_none` :586, `call_indirect_progress` :1312. All eight are still `sorry`. Their statements
are fixed, so the brief allows using them. `Step_is_wf` (wasm2.0.lean, proved in bundle19) and the
`Step`/`Step_read`/`Step_pure` constructors come from imports. No `sorry`, `admit`,
`native_decide` or new axiom was used. No project axiom was used either.

## Results

### 1. `t_progress_be_call` — PROVED
Rocq `type_progress.v:3449-3477`. Uses still-`sorry` lemmas `funcs_size` and `wf_config_app`.
```lean
  intro C x ts1 ts2 Haddr Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `rewrite Hcontext in Haddr; erewrite <- funcs_size; eauto`
  have Hlen : proj_uN_0 x < (fun_funcaddr (state.mk_state s f)).length := by
    subst Hcontext
    rw [funcs_size s f C' _ lab ret Hmod] at Haddr
    exact Haddr
  have HRead : Step (config.mk_config (state.mk_state s f) [admininstr.CALL x])
      (config.mk_config (state.mk_state s f)
        [admininstr.CALL_ADDR ((fun_funcaddr (state.mk_state s f))[proj_uN_0 x]!)]) :=
    Step.read _ _ _ (Step_read.call _ x Hlen)
  cases vcs with
  | nil =>
    exact ⟨s, f, _, HRead⟩
  | cons v vcs =>
    have HWfConfig2 := ((wf_config_app _ _ _).1 HWfConfig).2
    have HWfConfig' := Step_is_wf _ _ _ HWfConfig2 Hstore HRead
    have HStep := Step.ctxt_instrs (state.mk_state s f) (v :: vcs) [admininstr.CALL x] []
      (state.mk_state s f) _ HRead (Or.inl (List.cons_ne_nil _ _)) HWfConfig2 HWfConfig'
    rw [List.append_nil, List.append_nil] at HStep
    exact ⟨s, f, _, HStep⟩
```
Notes: same structure as Rocq. The `CALL` step (`Step.read` + `Step_read.call`) needs `funcs_size`
for its bound. The proof then splits on `vcs`. If `vcs = []`, the step is used directly. Otherwise
`Step.ctxt_instrs` applies, with `wf_config_app` and `Step_is_wf` supplying the two `wf_config`
premises.

### 2. `t_progress_be_call_indirect` — PROVED
Rocq `type_progress.v:3477-3516`. Uses still-`sorry` lemmas `typeof_append`, `invert_typeof_I32`,
`call_indirect_progress` and `wf_config_app`.
```lean
  intro C x y ts1 ts2 lim HSizex HLookupx HSizey HLookupy HWfC HWfinstr HWfTabType
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.`
  unfold mkFunctype at Htf
  injection Htf with Htf1 _
  injection Htf1 with Htf1
  rw [← Htf1] at Hts
  -- Rocq: `move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]].`
  obtain ⟨v1, Hvcs, Hts, Ht1⟩ := typeof_append _ _ _ Hts
  have Hwfv1 : wf_val v1 := HWfVals v1 (by rw [Hvcs]; simp)
  -- Rocq: `eapply invert_typeof_I32 in Ht1 as [n Heqv]; eauto.`
  obtain ⟨n, Heqv⟩ := invert_typeof_I32 v1 Ht1 Hwfv1
  -- Rocq: `pose proof (call_indirect_progress s f v_i x y HNone) as [es HStep].`
  obtain ⟨es, HStep⟩ := call_indirect_progress s f (num_.mk_num__0 Inn.I32 (uN.mk_uN n)) x y
    (by simp [proj_num__0])
  generalize List.take ts1.length vcs = vcs0 at Hvcs
  subst Hvcs
  -- Rocq: `rewrite Hvcs map_cat /= Heqv -catA` (in goal and in HWfConfig)
  have Hlist : List.map admininstr_val (vcs0 ++ [v1]) ++ List.map admininstr_instr [instr.CALL_INDIRECT x y]
      = List.map admininstr_val vcs0 ++
        ([admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n))] ++ [admininstr.CALL_INDIRECT x y]) := by
    simp [Heqv, admininstr_instr]
  rw [Hlist] at HWfConfig ⊢
  -- Rocq: `destruct ts1` (here: on the value prefix)
  cases vcs0 with
  | nil =>
    exact ⟨s, f, es, HStep⟩
  | cons w ws =>
    have HWfCf2 := ((wf_config_app _ _ _).1 HWfConfig).2
    have HWfConfig' := Step_is_wf _ _ _ HWfCf2 Hstore HStep
    have HStep' := Step.ctxt_instrs (state.mk_state s f) (w :: ws) _ [] (state.mk_state s f) es HStep
      (Or.inl (List.cons_ne_nil _ _)) HWfCf2 HWfConfig'
    rw [List.append_nil, List.append_nil] at HStep'
    exact ⟨s, f, _, HStep'⟩
```
Notes: this follows Rocq, with two changes.
1. Rocq's `minst_invert_tables` / `Forall2_size2` steps derive a `Hmod` fact that is never used
   afterwards, since the step comes from `call_indirect_progress`. They are omitted here.
2. Rocq runs `destruct ts1` on the type prefix. Lean splits on the value prefix `take |ts1| vcs`
   instead, which is the same split (`|take|ts1| vcs| = |ts1|`).

### 3. `t_progress_be_return` — PROVED
Rocq `type_progress.v:3516-3521`. Uses the still-`sorry` lemma `not_lf_return_singleton`.
```lean
  intro C ts1 ts ts2 Hretts HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  -- Rocq: `by move/not_lf_return_singleton: Hnotret.`
  exact absurd rfl (not_lf_return_singleton _ Hnotret)
```
Notes: a direct port. `List.map admininstr_instr [instr.RETURN]` unifies with `[admininstr.RETURN]`
by definitional unfolding.

### 4. `t_progress_be_const` — PROVED
Rocq `type_progress.v:3521-3526`. Uses no `sorry` lemma: `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`.
```lean
  intro C t vc HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  -- Rocq: `by left.`
  left
  rfl
```
Notes: `const_list [admininstr.CONST t vc] = true` holds by `rfl`.

### 5. `t_progress_be_unop` — PROVED
Rocq `type_progress.v:3526-3551`. Uses still-`sorry` lemmas `invert_typeof_numtype` and
`unop_not_none`.
```lean
  intro C t unop HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts.`
  unfold mkFunctype at Htf
  injection Htf with Htf1 _
  injection Htf1 with Htf1
  rw [← Htf1] at Hts
  -- Rocq: `invert_typeof_vcs Hts HWfVals HWfConfig.` (vcs = [v1])
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at Hts
    -- Rocq: `eapply invert_typeof_numtype in Ht1 as [n Heqv1]. rewrite Heqv1.`
    obtain ⟨n, Heqv1⟩ := invert_typeof_numtype v1 t Hts
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, admininstr_instr]
    -- Rocq: `case Eunop: (fun_unop_ t unop n) => [ c | ].`
    cases Eunop : fun_unop_ t unop n with
    | some c =>
      cases c with
      | nil =>
        exact ⟨s, f, [admininstr.TRAP], Step.pure _ _ _
          (Step_pure.unop_trap t n unop (by rw [Eunop]; simp) (by rw [Eunop]; rfl))⟩
      | cons c' l =>
        exact ⟨s, f, [admininstr.CONST t c'], Step.pure _ _ _
          (Step_pure.unop_val t n unop c' (by rw [Eunop]; simp) (by rw [Eunop]; simp) (by rw [Eunop]; simp))⟩
    | none =>
      exfalso
      have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
      cases v1 <;> simp only [admininstr_val, admininstr.CONST.injEq, reduceCtorEq] at Heqv1
      obtain ⟨rfl, rfl⟩ := Heqv1
      cases Hwf1 with
      | val_case_0 _ _ Hn =>
        cases HWfinstr with
        | instr_case_14 _ _ Hu =>
          exact unop_not_none _ _ _ Hn Hu Eunop
  · simp at Hts
```
Notes: same case structure as Rocq.
- `invert_typeof_vcs` becomes a `rcases` that keeps only `vcs = [v1]`.
- `fun_unop_ = some []` steps by `Step_pure.unop_trap`.
- `fun_unop_ = some (c' :: _)` steps by `Step_pure.unop_val`; its `List.contains` premise is closed
  by `simp`, using the derived `LawfulBEq num_`.
- `fun_unop_ = none` is impossible. Inverting `admininstr_val v1 = CONST t n` gives `v1 = val.CONST t n`.
  Then `wf_val` and `wf_instr` are inverted (`val_case_0` and `instr_case_14`), and `unop_not_none`
  gives the contradiction.

## Final Lean check output

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/Work.lean`
printed nothing (exit 0), so there were no errors or warnings, and all five `type_of%` `rfl` guards
passed.

`Work2.lean` is `Work.lean` plus `#print axioms` for each proof. Its output:
```
'TLC.t_progress_be_call_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_call_indirect_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_return_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_const_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_be_unop_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
In every case the `sorryAx` comes only from the still-`sorry` earlier lemmas listed above. None of
the proof bodies contains `sorry`, and Lean reported no "declaration uses 'sorry'" warning.

## Safety check: END

Run from `/home/zhengyew/spectec`:
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C04`

```
safety check [prove-C04] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T132056.222426417Z-prove-C04-1495195.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Summary: 5 of 5 proved (`t_progress_be_call`, `t_progress_be_call_indirect`,
`t_progress_be_return`, `t_progress_be_const`, `t_progress_be_unop`). None blocked, none skipped.
