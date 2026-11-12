# prove-C23 (bundle20 progress port, proof batch C23)

Targets (in order): `t_progress_e_plain` (TypeProgress.lean:2462), `t_progress_e_label` (TypeProgress.lean:2472).
Rocq source: `spectec/test-rocq/theories/type_progress.v:5591-5689` (bullets `Instr_ok2__instr` and
`Instr_ok2__label` of `t_progress_e`).

## Safety check at START

Run from `/home/zhengyew/spectec`:
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C23`

```
safety check [prove-C23] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T140304.507283740Z-prove-C23-1519175.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Files written

- This log (the only file written inside the repo).
- Scratch only: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C23/`
  `Work.lean` (both proofs + `rfl` guards), `WorkAx.lean` (same + `#print axioms`), `Ax.lean` (axioms of the lemmas used).
- No repo file edited. `TypeProgress.lean` untouched. No state-changing git, no agents spawned, no `lake build`.

## Method

Scratch file `Work.lean` = `import TypeProgress` / `namespace TLC` / each target's header copied verbatim (renamed
`<name>_proof`) / `example : type_of% @<name>_proof = type_of% @<name> := rfl` / `end TLC`. Both guards compile, so the
statements are identical and the tactic blocks drop into TypeProgress.lean unchanged. TypeProgress.lean has no
`open`/`set_option`/`variable` (only `namespace TLC` ... `end TLC`), so elaboration context is the same.

Ordering rule: every TypeProgress declaration used is before line 2462: `v_to_e_const` (84), `terminal_form` (89),
`const_list_concat` (97), `const_es_exists` (110), `br_reduce` (279), `return_reduce` (284), `br_reduce_decidable` (325),
`return_reduce_decidable` (330), `not_br_reduce_not_lf_br` (334), `not_return_reduce_not_lf_return` (339),
`wf_config_label` (417), `br_reduce_extract_vs` (525), `t_progress_be` (2375), `Instr_ok_Instrs_ok` (2398),
`t_progress_e_P`/`t_progress_e_P0` (defs just before the targets). Everything else comes from imported files
(`Step_is_wf`, `Step.*`/`Step_pure.*` constructors in wasm2.0; `upd_local_label_return` in TypingLemmas; `mkFunctype` in Subtyping).

## Result 1: `t_progress_e_plain` — PROVED

Close port of the Rocq bullet: `Instr_ok_Instrs_ok` gives `Instrs_ok C [be] (ts1 :-> ts2)`, then `t_progress_be` with
`bes := [be]` (its `List.map admininstr_instr [be]` is definitionally `[admininstr_instr be]`), then case split:
const ⇒ `terminal_form` via `const_list_concat` + `v_to_e_const`; step ⇒ `right`.

Proof body (after `:= by`):

```lean
  intro C be ts1 ts2 Hinstr HWfS HWfC HWfinstr
  unfold t_progress_e_P
  intro f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  have Hinstrs : Instrs_ok C [be] (mkFunctype ts1 ts2) := Instr_ok_Instrs_ok C be ts1 ts2 Hinstr
  have Hprog := t_progress_be s C C' f vcs [be] (mkFunctype ts1 ts2) ts1' ts2' lab ret HWfConfig Hinstrs
    HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  rcases Hprog with Hconst | Hprog
  · left
    unfold terminal_form
    left
    exact const_list_concat _ _ (v_to_e_const vcs) Hconst
  · right
    exact Hprog
```

Still-`sorry` earlier lemmas relied on: `Instr_ok_Instrs_ok`, `t_progress_be` (assembled from the `sorry` case lemmas
`t_progress_be_*`), `const_list_concat`, `v_to_e_const`.

## Result 2: `t_progress_e_label` — PROVED

Close port of the Rocq bullet, same case splits in the same order:
1. `Htf` injected ⇒ `ts1 = []`; `Hts : map typeof vcs = []` ⇒ `vcs = []` (Rocq's `invert_typeof_vcs`, empty case).
2. `br_reduce_decidable es`:
   - `isTrue`: destruct `l = mk_uN i`, case on `i` (Rocq `N.peano_ind`):
     - `i = 0`: `br_reduce_extract_vs` (label lookup `(... ++ C).LABELS[0]! = mk_list t2` by `rfl`), reassociate
       with `← List.append_assoc`, `Step.pure` + `Step_pure.br_zero` (length premise from `Hsize'`, `Hsize`).
     - `i = k+1`: `Step.pure` + `Step_pure.br_succ` with `l := mk_uN k`.
   - `isFalse`: `return_reduce_decidable es`:
     - `isTrue`: `Step.pure` + `Step_pure.return_label`.
     - `isFalse`: build `Heqc` (`{LABELS := [mk_list t2]} ++ C = upd_local_label_return C' .. (mk_list t2 :: lab) ret`,
       by `rw [Hcontext]; rfl`), `Heqtf`, `Heqts`, `not_br_reduce_not_lf_br`, `not_return_reduce_not_lf_return`,
       `wf_config_label`; apply IH' with `vcs := []`; terminal ⇒ `label_vals` (via `const_es_exists`) or `trap_label`;
       step ⇒ `Step.ctxt_label` with the wf premises `HWfCL1` and `Step_is_wf` (as in Rocq).

Proof body (after `:= by`):

```lean
  intro C n bes es t1 t2 Hinstrs Hadmin HWfS HWfC HWfinstr HWfC' Hsize IH IH'
  unfold t_progress_e_P
  intro f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  unfold mkFunctype at Htf
  injection Htf with Htf1 _
  injection Htf1 with Htf1
  subst Htf1
  have Hvcs : vcs = [] := List.map_eq_nil_iff.mp Hts
  subst Hvcs
  simp only [List.map_nil, List.nil_append] at HWfConfig ⊢
  cases br_reduce_decidable es with
  | isTrue Hbrred =>
    unfold br_reduce at Hbrred
    obtain ⟨vcs', l, es', Hes⟩ := Hbrred
    obtain ⟨i⟩ := l
    cases i with
    | zero =>
      right
      have Hexists : ∃ (vcs : List val) (es' : List admininstr),
          es = List.map admininstr_val vcs ++ ([admininstr.BR (uN.mk_uN 0)] ++ es') := ⟨vcs', es', Hes⟩
      have Hlookup : (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t2], RETURN := none } : context) ++ C).LABELS[0]! = list.mk_list t2 := by
        rfl
      obtain ⟨vcs1, vcs2, es'', Hes', Hsize'⟩ := br_reduce_extract_vs s _ t1 (list.mk_list t2) es Hexists Hadmin Hlookup
      subst Hes'
      refine ⟨s, f, List.map admininstr_val vcs2 ++ List.map admininstr_instr bes, ?_⟩
      apply Step.pure
      simp only [← List.append_assoc]
      exact Step_pure.br_zero n bes vcs1 vcs2 es'' (by rw [Hsize', Hsize]; rfl)
    | succ i =>
      right
      refine ⟨s, f, List.map admininstr_val vcs' ++ [admininstr.BR (uN.mk_uN i)], ?_⟩
      subst Hes
      apply Step.pure
      simp only [← List.append_assoc]
      exact Step_pure.br_succ n bes vcs' (uN.mk_uN i) es'
  | isFalse Hnotbrred =>
    cases return_reduce_decidable es with
    | isTrue Hretred =>
      unfold return_reduce at Hretred
      obtain ⟨vcs', es', Hes⟩ := Hretred
      right
      refine ⟨s, f, List.map admininstr_val vcs' ++ [admininstr.RETURN], ?_⟩
      subst Hes
      apply Step.pure
      simp only [← List.append_assoc]
      exact Step_pure.return_label n bes vcs' es'
    | isFalse Hnotretred =>
      have Heqc : (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t2], RETURN := none } : context) ++ C) =
          upd_local_label_return C' (List.map typeof f.LOCALS) (list.mk_list t2 :: lab) ret := by
        rw [Hcontext]; rfl
      have Heqtf : functype.mk_functype (list.mk_list []) (list.mk_list t1) = mkFunctype [] t1 := rfl
      have Heqts : List.map typeof ([] : List val) = [] := rfl
      have Hnotbr' := not_br_reduce_not_lf_br es Hnotbrred
      have Hnotret' := not_return_reduce_not_lf_return es Hnotretred
      obtain ⟨HWfCL1, HWfCL2⟩ := wf_config_label _ n bes es HWfConfig
      unfold t_progress_e_P0 at IH'
      have IH'' := IH' f C' [] [] t1 (list.mk_list t2 :: lab) ret HWfCL1 HWfVals Heqtf Heqc Hmod Heqts Hstore
        Hnotbr' Hnotret'
      simp only [List.map_nil, List.nil_append] at IH''
      rcases IH'' with Hterm | Hprog
      · right
        refine ⟨s, f, es, ?_⟩
        rcases Hterm with Hconst | Htrap
        · obtain ⟨vs, Hvs⟩ := const_es_exists _ Hconst
          subst Hvs
          apply Step.pure
          exact Step_pure.label_vals n bes vs
        · subst Htrap
          apply Step.pure
          exact Step_pure.trap_label n bes
      · right
        obtain ⟨s', f', es', Hstep⟩ := Hprog
        refine ⟨s', f', [admininstr.LABEL_ n bes es'], ?_⟩
        exact Step.ctxt_label _ n bes es _ es' Hstep HWfCL1 (Step_is_wf _ _ _ HWfCL1 Hstore Hstep)
```

Still-`sorry` earlier lemmas relied on: `br_reduce_decidable`, `return_reduce_decidable`, `br_reduce_extract_vs`,
`not_br_reduce_not_lf_br`, `not_return_reduce_not_lf_return`, `wf_config_label`, `const_es_exists`.
(Also `Step_is_wf` from wasm2.0.lean, whose `#print axioms` currently includes `sorryAx` through its own dependencies.)

Notes:
- The intro name `n` (Rocq's name) shadows the type `n` inside the proof; harmless, as the type is never mentioned
  after the intro.
- `br_reduce_decidable`/`return_reduce_decidable` are used as Rocq does (`cases` on the `Decidable` value). If the
  main thread prefers no dependency on these `sorry` defs, `by_cases Hbrred : br_reduce es` (classical) is a drop-in
  replacement for the split (swap the branch order).
- Axioms: none beyond Lean core (`propext`, `Classical.choice`, `Quot.sound`) plus `sorryAx` inherited from the
  still-`sorry` earlier lemmas listed above. No project axiom, no `sorry`/`admit`/`native_decide` in the proof text.

## Lean check output (final)

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/Work.lean`
produced NO output (no errors, no warnings; both `rfl` guards pass), real 0m2.189s.

`WorkAx.lean` (= Work.lean + `#print axioms`):

```
'TLC.t_progress_e_plain_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_e_label_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`Ax.lean` (axioms of each lemma used; all still contain `sorryAx`, confirming where the `sorryAx` comes from):

```
'TLC.Instr_ok_Instrs_ok' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.const_list_concat' depends on axioms: [propext, sorryAx]
'TLC.v_to_e_const' depends on axioms: [propext, sorryAx]
'TLC.br_reduce_decidable' depends on axioms: [sorryAx]
'TLC.return_reduce_decidable' depends on axioms: [sorryAx]
'TLC.not_br_reduce_not_lf_br' depends on axioms: [sorryAx]
'TLC.not_return_reduce_not_lf_return' depends on axioms: [sorryAx]
'TLC.wf_config_label' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.br_reduce_extract_vs' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.const_es_exists' depends on axioms: [propext, sorryAx]
'Step_is_wf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Safety check at END

Final Lean re-run of `Work.lean` just before this check: no output, `exit=0`; `grep -c "sorry|admit|native_decide"`
on Work.lean = 0.

Run from `/home/zhengyew/spectec`:
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C23`

```
safety check [prove-C23] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T140810.734015513Z-prove-C23-1522568.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

(The only write after this check is this append to my own log file, which is inside `spectec/src/test-lean-claude`.)
