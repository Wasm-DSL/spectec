# prove-stepread: proving `Step_read_is_wf` in the Lean port (bundle21 sub-task)

Agent: subagent spawned by the bundle21 workflow (brief: `SCR/briefs/stepread.md`).
`SCR` = `/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad`.

Safety order (user, verbatim): "You should NEVER modify anything outside of `spectec/src/test-lean-claude`. In fact, you should run a periodic programmatic check to verify that you have not done so, and log the check output in the claude-logging directory. If you create any agents or otherwise call a different LLM / Claude session, you MUST make it keenly aware of this safety limitation, and it must do the same checks and log it neatly in the claude-logging folder."
Stricter rule for this turn (brief): write nothing anywhere inside `/home/zhengyew/spectec`; work only in `SCR/proj_sr` (read-only, frozen copy), `SCR/work/stepread/` and this log. No agents spawned.

## Safety check: start

```
$ bash SCR/safety/verify.sh prove-stepread-start
safety check [prove-stepread-start] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T050236.233858457Z-prove-stepread-start-453682.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
```
Note on the NOTE: `stat` shows `.lake/build/lib/lean/wasm2.0.trace.nobuild` was created 2026-10-15 12:52:21 +0800 (04:52 UTC), i.e. before this agent started (05:02 UTC); it is not this agent's doing (presumably a lake invocation from an earlier step of the main thread). This agent never runs lake in the repo.

## Work log

### 1. Reading (05:03-05:10 UTC)
- Read the brief in full; read the Rocq proof `spectec/test-rocq/theories/wasm.v` 17275-17624 (read-only) in full: generic helpers (Hmono, Hav, Hai, Hfmap, Hnth, Har, Hrep, Hmkseq, Hupd, Hfin, Hcomb, Hbr, Hgv, Hl2), store bounds (Hsnth, Hlim, Htlen, Hmlen, Helen, Hdlen, Hdbyte), arithmetic (Hc32, Hwn, Hp1, Hm1, Hmsz), then `case: H` and automation; the last block handles the `iadd_ 32 i 1` pushes via `iadd__is_wf`.
- Read in `SCR/proj_sr/wasm2.0.lean`: the 47-constructor `Step_read`, `Store_ok` and the `*_ok` relations it uses (`Tableinst_ok`, `Tabletype_ok`, `Limits_ok`, `Meminst_ok`, `Memtype_ok`, `Eleminst_ok`, `Datainst_ok`), the `wf_*` relations, `fun_table`/`fun_mem`/`fun_elem`/`fun_data`/`fun_store`, the five bundle19 `iswf_*` blocks, `Step_pure_is_wf` and `Step_is_wf` (style).
- Confirmed the regenerated `memory_fill_succ` / `memory_copy_le` / `memory_init_succ` now push `CONST I32 (num_.mk_num__0 Inn.I32 (iadd_ 32 (Option.get! (proj_num__0 i)) (uN.mk_uN 1)))` (wrapping). The table rules still push `i+1` (non-wrapping); those are bounded via `Store_ok` (`Tabletype_ok` limits `< 2^32`, `Eleminst_ok` length `< 2^32`), as in Rocq.
- `wasm2.0.lean` imports only `ExtendedDeriveDecEq` (core Lean, no Mathlib), so only core tactics are used.

### 2. Probes (`SCR/work/stepread/Probe1.lean`, `Probe2.lean`)
- `Store_ok`'s store argument is auto-promoted to a parameter: `cases hs with | mk_Store_ok` takes 12 list names + 17 hypothesis names.
- `Limits_ok`'s `k` is NOT promoted (pattern `mk_Limits_ok _ _ _ hle _ _`); `Tableinst_ok`/`Meminst_ok`/`Eleminst_ok` have the store promoted.
- `omega` ignores `h : v_n ≠ 0` with `v_n : n`; `have h' : 0 < v_n := ...` is still at type `n` and still ignored. Restating as `@Ne Nat v_n 0` / `@Eq Nat ...` / `@LE.le Nat _ ...` works. `omega` does evaluate literal `2 ^ 32`.
- `decide` evaluates `Int.toNat ((2:Int)^32 - 1) = 4294967295`.
- `nomatch h, ...` inside `⟨_, _⟩` parses the comma as a second discriminant; parenthesize.

### 3. Helper lemmas (`SCR/work/stepread/Helpers.lean`) compile in isolation, no warnings.

### 4. Main proof (`SCR/work/stepread/Work.lean`)
- Structure: `intro`, destructure `wf_config`, then `cases h with` over all 47 `Step_read` constructors, one short explicit proof per case (style of `Step_pure_is_wf` / `Step_is_wf`).
- First full compile: no errors, no warnings (05:16 UTC). Cosmetic re-layout only afterwards (one blank line after the import).

### 5. Verification
1. Final compile of Work.lean (template from the brief, guard line included), the last `lake env lean` run on Work.lean:
```
$ cd SCR/proj_sr && timeout 1800 lake env lean SCR/work/stepread/Work.lean
[exit status: 0]
```
   (No output at all: no errors, no warnings, no `declaration uses sorry`. The guard `example : type_of% @Step_read_is_wf_proof = type_of% @Step_read_is_wf := rfl` compiles.)
2. Dependency audit (`SCR/work/stepread/AuditWork.lean`, a copy of Work.lean plus a meta command that walks the closure of `Step_read_is_wf_proof` and lists every constant whose own type/value mentions `sorryAx`):
```
visited 2875 constants; direct sorry users: [extend___is_wf, inv_lanes__is_wf, lanes__is_wf]
'Step_read_is_wf_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
   All three are on the brief's list of 62 allowed opaque-function theorems (Rocq's proof uses the same ones; `Admitted` there). No new axiom, no `native_decide`, no `implemented_by` (grep of Work.lean for `sorry|axiom|native_decide|implemented_by|admit`: none).
3. Rule 2 audit (`SCR/work/stepread/PosWork.lean`): every `wasm2.0` constant referenced by the helpers and the proof (and by the auxiliary constants Lean generated for them), mapped to the source line of its enclosing declaration:
   `519 wasm2.0 constants referenced; max source line 15933 (Store_ok.mk_Store_ok)`, no unresolved ones. `theorem Step_read_is_wf` is at line 15974, so only earlier declarations are used (no `Step_is_wf`, nothing from HelperLemmas/TypePreservation/...).
4. Splice test (`SCR/work/stepread/splice/`): `make_splice.py` copies `SCR/proj_sr/wasm2.0.lean` to `splice/wasm2.0_spliced.lean`, inserts the helper block immediately before `theorem Step_read_is_wf` and replaces `:=\n  sorry` with `:= by\n<proof block>`; compiled standalone with `lake env lean` (no `-o`, nothing written into proj_sr):
   exit 0, 0 errors, 56 s wall, 2.6 GB max RSS; exactly 62 `declaration uses sorry` warnings, which are exactly the brief's 62 opaque-function theorems; no messages at all in the inserted region (lines 15974-16320); everything downstream (`Step_is_wf`, ...) still compiles. The helper/proof text returned is byte-identical to the splice-tested text (checked with `cmp`).
5. `SCR/proj_sr` untouched: nothing in it is newer than this agent's start (its `.lake` dirs are 05:02:02 UTC, the main thread's setup; olean 05:01:40 UTC). `SCR/work/stepread/Smoke.lean` (05:02:02 UTC) was created by the main thread, not by this agent.

### 6. Notes
- Rocq to Lean mapping: Htlen -> `iswf_table_len_lt`; Hmlen -> `iswf_mem_len_le` (only `|BYTES| <= 2^32`; memory.size's page count follows from `v_n*64*1024 = |BYTES|` by omega, so Rocq's existential is not needed); Helen -> `iswf_elem_len_lt`; Hdbyte -> `iswf_data_byte_lt`; Hdlen is not needed any more (memory.init-succ now pushes `iadd_`); Hlim -> `iswf_Limits_ok_le`; Hsnth -> `iswf_Forall_of_Forall₂` + existing `iswf_Forall_getElem!`; Hwn -> `iswf_I32_const_lt`; Hc32 -> existing `iswf_I32_const`; Hp1/Hm1/Hmsz -> `omega` on restated hypotheses; Hgv -> `iswf_globalinst_value` + `global_is_wf`; Rocq's final `iadd__is_wf` block -> `iswf_I32_iadd1`; STORE/LOAD with `memarg0` -> `iswf_store_I32_8`, `iswf_load_I32_8_U`. Rocq's generic list helpers (Hmono, Hfmap, Hnth, Hrep, Hupd, ...) are covered by the bundle19 `iswf_Forall_*` lemmas.
- Lean's `Forall₂` is zip-based, so getting `Forall` on the left list needs the length equation; `Store_ok` provides it for every component.
- The table rules (`table.fill-succ`, `table.copy-le/gt`, `table.init-succ`) still push non-wrapping `i+1` / `i+n-1`; those are bounded with `Store_ok` exactly as in Rocq (`Tabletype_ok` limit `<= 2^32-1`, `Eleminst_ok` length `< 2^32`). The memory rules push `iadd_ 32 _ 1`, which is well formed by `iadd__is_wf`; only memory.size and memory.copy-gt (`j+n-1`) need the memory bound.
- Pitfalls hit: `omega` ignores hypotheses typed at the `n`/`N`/`M` abbreviations (even `have h : 0 < v_n` stays at type `n`); restated with `@Ne Nat`/`@Eq Nat`/`@LE.le Nat _`. `Store_ok`'s store is auto-promoted (12 list + 17 hypothesis binder slots), `Limits_ok`'s `k` is not. `⟨fun h => nomatch h, ...⟩` parses the comma as a second `nomatch` discriminant.
- Stale comment: the bundle19 comment above `theorem Step_read_is_wf` (wasm2.0.lean lines 15966-15972: "`Admitted` in Rocq; left `sorry`. Even with the premise it is false in one corner case (...), pending a spec-side fix.") is now outdated. Suggested replacement for its last sentence: "`Qed` in Rocq since 6582b3a39 (spec commit 4cf9f29c5 made memory.fill/copy/init push `$iadd_(32, i, 1)`); proved here (bundle21)." Suggest inserting the helper block before the `/- Well-Formedness Theorem at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 -/` line so both comments stay attached to the theorem (Lean does not care; the splice test used the position immediately before `theorem`).

### 7. Final `Work.lean` (full content)
```lean
import «wasm2.0»

/-! Hand-written helper lemmas for `Step_read_is_wf` below (bundle21; not generated). -/

theorem iswf_Forall_of_Forall₂ {α β : Type} {R : α → β → Prop} {Q : α → Prop} (l1 : List α) (l2 : List β) :
    Forall₂ R l1 l2 → l1.length = l2.length → (∀ a b, R a b → Q a) → Forall Q l1 := by
  intro h hlen hq x hx
  obtain ⟨y, _, hr⟩ := iswf_Forall₂_left_mem l1 l2 h hlen x hx
  exact hq x y hr

theorem iswf_Limits_ok_le {v : uN} {o : Option uN} {k : Nat} (h : Limits_ok (limits.mk_limits v o) k) :
    proj_uN_0 v ≤ k := by
  cases h with
  | mk_Limits_ok _ _ _ hle _ _ => exact hle

/- Store bounds from `Store_ok` (Rocq's `Htlen`, `Hmlen`, `Helen`). An out-of-range lookup returns the
   default instance, whose lists are empty, so the bounds hold for every index. -/
theorem iswf_table_len_lt (z : state) (x : tableidx) :
    Store_ok (fun_store z) → ((fun_table z x).REFS).length < 2 ^ 32 := by
  intro hs
  cases z with
  | mk_state s f =>
    change Store_ok s at hs
    cases hs with
    | mk_Store_ok _ _ _ _ tis tts _ _ _ _ _ _ _ _ _ _ hlen htab _ _ _ _ _ _ hseq _ _ _ _ =>
      subst hseq
      show (tis[(f.MODULE.TABLES)[proj_uN_0 x]!]!).REFS.length < 2 ^ 32
      apply iswf_Forall_getElem! (P := fun ti : tableinst => ti.REFS.length < 2 ^ 32)
      · refine iswf_Forall_of_Forall₂ tis tts htab hlen (fun a b hab => ?_)
        cases hab with
        | mk_Tableinst_ok v_n m_opt rt ref_lst htt _ hl _ _ _ =>
          cases htt with
          | mk_Tabletype_ok _ _ hlim _ =>
            have h1 : @LE.le Nat _ v_n (Int.toNat (((2 ^ 32) : Int) - (1 : Int))) := iswf_Limits_ok_le hlim
            have h2 : Int.toNat (((2 ^ 32) : Int) - (1 : Int)) = 4294967295 := by decide
            have hl' : @Eq Nat ref_lst.length v_n := hl
            show ref_lst.length < 2 ^ 32
            omega
      · decide

theorem iswf_mem_len_le (z : state) (x : memidx) :
    Store_ok (fun_store z) → ((fun_mem z x).BYTES).length ≤ 2 ^ 32 := by
  intro hs
  cases z with
  | mk_state s f =>
    change Store_ok s at hs
    cases hs with
    | mk_Store_ok _ _ mis mts _ _ _ _ _ _ _ _ _ _ hlen hmem _ _ _ _ _ _ _ _ hseq _ _ _ _ =>
      subst hseq
      show (mis[(f.MODULE.MEMS)[proj_uN_0 x]!]!).BYTES.length ≤ 2 ^ 32
      apply iswf_Forall_getElem! (P := fun mi : meminst => mi.BYTES.length ≤ 2 ^ 32)
      · refine iswf_Forall_of_Forall₂ mis mts hmem hlen (fun a b hab => ?_)
        cases hab with
        | mk_Meminst_ok v_n m_opt b_lst hmt hl _ _ _ =>
          cases hmt with
          | mk_Memtype_ok _ hlim _ =>
            have h1 : @LE.le Nat _ v_n (2 ^ 16) := iswf_Limits_ok_le hlim
            have hl' : @Eq Nat b_lst.length (v_n * (64 * 1024)) := hl
            show b_lst.length ≤ 2 ^ 32
            omega
      · decide

theorem iswf_elem_len_lt (z : state) (y : tableidx) :
    Store_ok (fun_store z) → ((fun_elem z y).REFS).length < 2 ^ 32 := by
  intro hs
  cases z with
  | mk_state s f =>
    change Store_ok s at hs
    cases hs with
    | mk_Store_ok _ _ _ _ _ _ _ _ _ _ eis ets _ _ _ _ _ _ _ _ _ _ hlen hel hseq _ _ _ _ =>
      subst hseq
      show (eis[(f.MODULE.ELEMS)[proj_uN_0 y]!]!).REFS.length < 2 ^ 32
      apply iswf_Forall_getElem! (P := fun ei : eleminst => ei.REFS.length < 2 ^ 32)
      · refine iswf_Forall_of_Forall₂ eis ets hel hlen (fun a b hab => ?_)
        cases hab with
        | mk_Eleminst_ok rt ref_lst _ hl _ => exact hl
      · decide

/- Data bytes are `< 256` (Rocq's `Hdbyte`); this needs only `wf_state`. -/
theorem iswf_data_byte_lt (z : state) (x : dataidx) (k : Nat) :
    wf_state z → wf_uN 32 x → proj_byte_0 (((fun_data z x).BYTES)[k]!) < 2 ^ 32 := by
  intro hz hx
  have hd := data_is_wf z x _ hz hx rfl
  generalize fun_data z x = d at hd ⊢
  cases hd with
  | datainst_case_ l hl =>
    have hb := iswf_Forall_getElem! k hl (wf_byte.byte_case_0 0 ⟨Nat.le_refl 0, by decide⟩)
    generalize l[k]! = b at hb ⊢
    cases hb with
    | byte_case_0 i hi =>
      show i < 2 ^ 32
      omega

theorem iswf_globalinst_value {g : globalinst} (h : wf_globalinst g) : wf_val g.VALUE := by
  cases h with
  | globalinst_case_ _ _ hv => exact hv

theorem iswf_I32_const_lt {k : Nat}
    (h : wf_admininstr (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN k)))) : k < 2 ^ 32 := by
  cases h with
  | admininstr_case_13 _ _ h =>
    cases h with
    | num__case_0 _ _ _ hw _ => exact iswf_uN_lt hw

/- memory.fill-succ, memory.copy-le and memory.init-succ push `$iadd_(32, i, 1)` (spec commit 4cf9f29c5). -/
theorem iswf_I32_iadd1 {i : num_} (h : wf_admininstr (admininstr.CONST numtype.I32 i)) (hne : proj_num__0 i ≠ none) :
    wf_admininstr (admininstr.CONST numtype.I32
      (num_.mk_num__0 Inn.I32 (iadd_ 32 (Option.get! (proj_num__0 i)) (uN.mk_uN 1)))) := by
  cases h with
  | admininstr_case_13 _ _ hw =>
    exact wf_admininstr.admininstr_case_13 _ _ (wf_num_.num__case_0 _ _ _ (by decide)
      (iadd__is_wf 32 _ _ _ (iswf_num_Inn_proj Inn.I32 i hw hne) (iswf_uN_of_lt (by decide)) rfl) rfl)

theorem iswf_store_I32_8 : wf_admininstr (admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) :=
  wf_admininstr.admininstr_case_57 (some Inn.I32) _ _ _
    (iswf_Forall_cons (wf_sz.sz_case_0 8 (by decide)) (iswf_Forall_nil _))
    (memarg0_is_wf _ rfl)
    ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    (by intro t ht; simp at ht; subst ht; exact ⟨rfl, by decide⟩)

theorem iswf_load_I32_8_U :
    wf_admininstr (admininstr.LOAD numtype.I32
      (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0) :=
  wf_admininstr.admininstr_case_56 _ _ _
    (iswf_Forall_cons (wf_loadop_.loadop__case_0 _ _ _
      (wf_loadop_Inn.loadop_Inn_case_0 _ _ _ (wf_sz.sz_case_0 8 (by decide)) (by decide)) rfl)
      (iswf_Forall_nil _))
    (memarg0_is_wf _ rfl)

theorem Step_read_is_wf_proof (z : state) (admininstr_lst : List admininstr) (var_1 : List admininstr) :
  wf_config (config.mk_config z admininstr_lst) →
  Store_ok (fun_store z) →
  Step_read (config.mk_config z admininstr_lst) var_1 →
  Forall (fun (var_1_elem : admininstr) => wf_admininstr var_1_elem) var_1 := by
  intro hcfg hsok h
  obtain ⟨hst, hais⟩ : wf_state z ∧ Forall (fun e => wf_admininstr e) admininstr_lst := by
    cases hcfg with | config_case_0 _ _ h1 h2 => exact ⟨h1, h2⟩
  cases h with
  | block z k val_lst bt instr_lst v_n t_1_lst t_2_lst h0 h1 h2 h3 =>
    have hb := hais (admininstr.BLOCK bt instr_lst) (by simp)
    cases hb; rename_i hinstrs
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ (iswf_Forall_nil _)
      (iswf_Forall_append (fun x hx => hais x (by simp [hx]))
        (iswf_Forall_map _ _ hinstrs (fun _ h => iswf_admininstr_instr h)))) (iswf_Forall_nil _)
  | loop z k val_lst bt instr_lst t_1_lst v_n t_2_lst h0 h1 h2 h3 =>
    have hb := hais (admininstr.LOOP bt instr_lst) (by simp)
    cases hb; rename_i hbt hinstrs
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _
      (iswf_Forall_cons (wf_instr.instr_case_5 _ _ hbt hinstrs) (iswf_Forall_nil _))
      (iswf_Forall_append (fun x hx => hais x (by simp [hx]))
        (iswf_Forall_map _ _ hinstrs (fun _ h => iswf_admininstr_instr h)))) (iswf_Forall_nil _)
  | call z x h0 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | call_indirect_call z i x y a h0 h1 h2 h3 h4 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | call_indirect_trap z i x y h0 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | call_addr z k val_lst a v_n f instr_lst t_1_lst t_2_lst mm v_func x t_lst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    subst h4
    cases h6 with
    | func_case_0 _ _ _ _ hinstrs =>
      exact iswf_Forall_cons (wf_admininstr.admininstr_case_72 _ _ _ h7
        (iswf_Forall_cons (wf_admininstr.admininstr_case_71 _ _ _ (iswf_Forall_nil _)
          (iswf_Forall_map _ _ hinstrs (fun _ h => iswf_admininstr_instr h))) (iswf_Forall_nil _)))
        (iswf_Forall_nil _)
  | ref_func z x h0 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | local_get z x =>
    have hx := hais (admininstr.LOCAL_GET x) (by simp)
    cases hx; rename_i hx
    exact iswf_Forall_cons (iswf_admininstr_val (local_is_wf z x _ hst hx rfl)) (iswf_Forall_nil _)
  | global_get z x =>
    have hx := hais (admininstr.GLOBAL_GET x) (by simp)
    cases hx; rename_i hx
    exact iswf_Forall_cons (iswf_admininstr_val (iswf_globalinst_value (global_is_wf z x _ hst hx rfl)))
      (iswf_Forall_nil _)
  | table_get_trap z i x h0 h1 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | table_get_val z i x h0 h1 =>
    exact iswf_Forall_cons (iswf_admininstr_ref _) (iswf_Forall_nil _)
  | table_size z x v_n h0 =>
    have hL := iswf_table_len_lt z x hsok
    exact iswf_Forall_cons (iswf_I32_const _ (by omega)) (iswf_Forall_nil _)
  | table_fill_trap z i v_val v_n x h0 h1 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | table_fill_zero z i v_val v_n x h0 h1 h2 =>
    exact iswf_Forall_nil _
  | table_fill_succ z i v_val v_n x h0 h1 h2 =>
    have hi := hais (admininstr.CONST numtype.I32 i) (by simp)
    have hv := hais (admininstr_val v_val) (by simp)
    have hn := iswf_I32_const_lt
      (hais (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (by simp))
    have hx := hais (admininstr.TABLE_FILL x) (by simp)
    cases hx; rename_i hx
    have hL := iswf_table_len_lt z x hsok
    have h1' : @Ne Nat v_n 0 := h1
    exact iswf_Forall_cons hi <| iswf_Forall_cons hv <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <|
      iswf_Forall_cons (iswf_I32_const _ (by omega)) <| iswf_Forall_cons hv <|
      iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_52 _ hx) (iswf_Forall_nil _)
  | table_copy_trap z j i v_n x y h0 h1 h2 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | table_copy_zero z j i v_n x y h0 h1 h2 h3 =>
    exact iswf_Forall_nil _
  | table_copy_le z j i v_n x y h0 h1 h2 h3 h4 =>
    have hj := hais (admininstr.CONST numtype.I32 j) (by simp)
    have hi := hais (admininstr.CONST numtype.I32 i) (by simp)
    have hn := iswf_I32_const_lt
      (hais (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (by simp))
    have hxy := hais (admininstr.TABLE_COPY x y) (by simp)
    cases hxy; rename_i hx hy
    have hLx := iswf_table_len_lt z x hsok
    have hLy := iswf_table_len_lt z y hsok
    have h2' : @Ne Nat v_n 0 := h2
    obtain ⟨h3i, h3j⟩ := h3
    exact iswf_Forall_cons hj <| iswf_Forall_cons hi <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hy) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <|
      iswf_Forall_cons (iswf_I32_const _ (by omega)) <| iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)
  | table_copy_gt z j i v_n x y h0 h1 h2 h3 h4 =>
    have hj := hais (admininstr.CONST numtype.I32 j) (by simp)
    have hi := hais (admininstr.CONST numtype.I32 i) (by simp)
    have hn := iswf_I32_const_lt
      (hais (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (by simp))
    have hxy := hais (admininstr.TABLE_COPY x y) (by simp)
    cases hxy; rename_i hx hy
    have hLx := iswf_table_len_lt z x hsok
    have hLy := iswf_table_len_lt z y hsok
    obtain ⟨h4i, h4j⟩ := h4
    exact iswf_Forall_cons (iswf_I32_const _ (by omega)) <| iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_48 _ hy) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <| iswf_Forall_cons hj <| iswf_Forall_cons hi <|
      iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_53 _ _ hx hy) (iswf_Forall_nil _)
  | table_init_trap z j i v_n x y h0 h1 h2 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | table_init_zero z j i v_n x y h0 h1 h2 h3 =>
    exact iswf_Forall_nil _
  | table_init_succ z j i v_n x y h0 h1 h2 h3 h4 =>
    have hj := hais (admininstr.CONST numtype.I32 j) (by simp)
    have hn := iswf_I32_const_lt
      (hais (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (by simp))
    have hxy := hais (admininstr.TABLE_INIT x y) (by simp)
    cases hxy; rename_i hx hy
    have hLx := iswf_table_len_lt z x hsok
    have hLy := iswf_elem_len_lt z y hsok
    have h3' : @Ne Nat v_n 0 := h3
    obtain ⟨h4i, h4j⟩ := h4
    exact iswf_Forall_cons hj <| iswf_Forall_cons (iswf_admininstr_ref _) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_49 _ hx) <|
      iswf_Forall_cons (iswf_I32_const _ (by omega)) <| iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_54 _ _ hx hy) (iswf_Forall_nil _)
  | load_num_trap z i nt ao h0 h1 h2 h3 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | load_num_val z i nt ao c h0 h1 h2 h3 h4 =>
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_13 _ _ h3) (iswf_Forall_nil _)
  | load_pack_trap z i v_Inn v_n v_sx ao h0 h1 h2 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | load_pack_val z i v_Inn v_n v_sx ao c h0 h1 h2 h3 h4 =>
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_13 _ _
      (wf_num_.num__case_0 _ _ _ h0 (extend___is_wf _ _ _ _ _ h3 rfl) rfl)) (iswf_Forall_nil _)
  | vload_oob z i ao h0 h1 h2 h3 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | vload_val z i ao c h0 h1 h2 h3 h4 =>
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide) h3) (iswf_Forall_nil _)
  | vload_shape_oob z i v_M v_N v_sx ao h0 h1 h2 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | vload_shape_val z i v_M v_N v_sx ao c j_lst v_Jnn h0 h1 h2 h3 h4 h5 h6 h7 =>
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)
      (inv_lanes__is_wf _ _ _ h5 (iswf_Forall_map _ _ h6 (fun _ h => h)) h3)) (iswf_Forall_nil _)
  | vload_splat_oob z i v_N ao h0 h1 h2 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | vload_splat_val z i v_N ao c j v_Jnn v_M h0 h1 h2 h3 h4 h5 h6 h7 =>
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)
      (inv_lanes__is_wf _ _ _ h6 (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact h7) h4))
      (iswf_Forall_nil _)
  | vload_zero_oob z i v_N ao h0 h1 h2 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | vload_zero_val z i v_N ao c j h0 h1 h2 h3 h4 =>
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide) (extend___is_wf _ _ _ _ _ h3 h2))
      (iswf_Forall_nil _)
  | vload_lane_oob z i c_1 v_N ao j h0 h1 h2 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | vload_lane_val z i c_1 v_N ao j c k v_Jnn v_M h0 h1 h2 h3 h4 h5 h6 h7 =>
    have hc := hais (admininstr.VCONST vectype.V128 c_1) (by simp)
    cases hc; rename_i _ hw1
    have hls := lanes__is_wf _ _ _ h6 hw1 rfl
    exact iswf_Forall_cons (wf_admininstr.admininstr_case_20 _ _ (by decide)
      (inv_lanes__is_wf _ _ _ h6 (iswf_Forall_modify _ (fun _ _ => h7) _ _ hls) h4)) (iswf_Forall_nil _)
  | memory_size z v_n h0 h1 =>
    have hL := iswf_mem_len_le z (uN.mk_uN 0) hsok
    have h0' : @Eq Nat (v_n * 64 * 1024) ((fun_mem z (uN.mk_uN 0)).BYTES.length) := h0
    exact iswf_Forall_cons (iswf_I32_const _ (by omega)) (iswf_Forall_nil _)
  | memory_fill_trap z i v_val v_n h0 h1 h2 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | memory_fill_zero z i v_val v_n h0 h1 h2 =>
    exact iswf_Forall_nil _
  | memory_fill_succ z i v_val v_n h0 h1 h2 =>
    have hi := hais (admininstr.CONST numtype.I32 i) (by simp)
    have hv := hais (admininstr_val v_val) (by simp)
    have hn := iswf_I32_const_lt
      (hais (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (by simp))
    exact iswf_Forall_cons hi <| iswf_Forall_cons hv <| iswf_Forall_cons iswf_store_I32_8 <|
      iswf_Forall_cons (iswf_I32_iadd1 hi h0) <| iswf_Forall_cons hv <|
      iswf_Forall_cons (iswf_I32_const _ (by omega)) <| iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | memory_copy_trap z j i v_n h0 h1 h2 h3 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | memory_copy_zero z j i v_n h0 h1 h2 h3 =>
    exact iswf_Forall_nil _
  | memory_copy_le z j i v_n h0 h1 h2 h3 h4 =>
    have hj := hais (admininstr.CONST numtype.I32 j) (by simp)
    have hi := hais (admininstr.CONST numtype.I32 i) (by simp)
    have hn := iswf_I32_const_lt
      (hais (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (by simp))
    exact iswf_Forall_cons hj <| iswf_Forall_cons hi <| iswf_Forall_cons iswf_load_I32_8_U <|
      iswf_Forall_cons iswf_store_I32_8 <| iswf_Forall_cons (iswf_I32_iadd1 hj h0) <|
      iswf_Forall_cons (iswf_I32_iadd1 hi h1) <| iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | memory_copy_gt z j i v_n h0 h1 h2 h3 h4 =>
    have hj := hais (admininstr.CONST numtype.I32 j) (by simp)
    have hi := hais (admininstr.CONST numtype.I32 i) (by simp)
    have hn := iswf_I32_const_lt
      (hais (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (by simp))
    have hL := iswf_mem_len_le z (uN.mk_uN 0) hsok
    obtain ⟨h4i, h4j⟩ := h4
    exact iswf_Forall_cons (iswf_I32_const _ (by omega)) <| iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons iswf_load_I32_8_U <| iswf_Forall_cons iswf_store_I32_8 <| iswf_Forall_cons hj <|
      iswf_Forall_cons hi <| iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | memory_init_trap z j i v_n x h0 h1 h2 h3 =>
    exact iswf_Forall_cons (by constructor) (iswf_Forall_nil _)
  | memory_init_zero z j i v_n x h0 h1 h2 h3 =>
    exact iswf_Forall_nil _
  | memory_init_succ z j i v_n x h0 h1 h2 h3 h4 =>
    have hj := hais (admininstr.CONST numtype.I32 j) (by simp)
    have hi := hais (admininstr.CONST numtype.I32 i) (by simp)
    have hn := iswf_I32_const_lt
      (hais (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (by simp))
    have hx := hais (admininstr.MEMORY_INIT x) (by simp)
    cases hx; rename_i hx
    exact iswf_Forall_cons hj <| iswf_Forall_cons (iswf_I32_const _ (iswf_data_byte_lt z x _ hst hx)) <|
      iswf_Forall_cons iswf_store_I32_8 <| iswf_Forall_cons (iswf_I32_iadd1 hj h2) <|
      iswf_Forall_cons (iswf_I32_iadd1 hi h1) <| iswf_Forall_cons (iswf_I32_const _ (by omega)) <|
      iswf_Forall_cons (wf_admininstr.admininstr_case_66 _ hx) (iswf_Forall_nil _)

example : type_of% @Step_read_is_wf_proof = type_of% @Step_read_is_wf := rfl
```

## Safety check: end

```
$ bash SCR/safety/verify.sh prove-stepread-end
safety check [prove-stepread-end] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T052211.521900840Z-prove-stepread-end-461946.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
2a4
> ?? spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/
[verify.sh exit status: 0]
```
Outside `spectec/src/test-lean-claude`: VERIFIED, zero new changes. Inside it, two entries differ from the baseline, neither written by this agent:
- `.lake/build/lib/lean/wasm2.0.trace.nobuild`: the same entry as at the start check (created 04:52 UTC, before this agent started).
- `claude-logging/verbatim_dialogue_log/bundle21/` (new since the start check): `stat` (read-only) shows the directory and its contents (`prompt_21.md`, `agent_logs/`, `user_requested_documents/`) were created 2026-10-15 13:17:11 +0800 (05:17:11 UTC). That is the user's dialogue-log layout, presumably created by the user or the main thread. Every write by this agent went to `SCR/work/stepread/`, `SCR/logs/prove-stepread.md` or (via verify.sh) `SCR/safety/`. This agent never wrote inside /home/zhengyew/spectec and never ran lake there.
