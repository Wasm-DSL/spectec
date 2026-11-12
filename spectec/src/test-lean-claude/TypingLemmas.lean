import Mathlib.Tactic
import «wasm2.0»
import HelperLemmas
import Subtyping

/-!
# TypingLemmas

Lean port of `spectec/test-rocq/theories/typing_lemmas.v`. Full digest:
`claude-logging/for-claude/digest_typing_lemmas_and_type_preservation_pure.md`.

Architecture (mirrors Rocq exactly, do not decompose differently): ONE
big case-exhaustive `ai_principal_typing` Prop gives, for every
`admininstr` constructor, its principal (most specific) type; two
"soundness" theorems (`instr_typing_inversion`, `ai_typing_inversion`)
connect it to the real typing judgments `Instr_ok`/`Instr_ok2`. All later
per-instruction facts go through `ai_principal_typing`, not separate named
lemmas per instruction (unlike `type_preservation_pure.v`, which IS one
lemma per reduction rule).

Rocq's Ltac automation layer (chiefly `typing_lemmas.v:2106-2382`: `construct_ais_typing`,
`invert_ais_typing`, `join_subtyping_*`, `resolve_subtyping`, etc., plus a few tactics
interleaved earlier, e.g. `typing_inversion` at `typing_lemmas.v:1279`) is
NOT ported 1:1 — Lean's `simp`/tactics cover the same dispatch differently;
only the *lemma* declarations that layer sits on top of are ported.

The two large per-constructor case definitions, `instr_of` and `ai_principal_typing`,
are transcribed in full; see their doc comments for where they come from and how they were
checked against Rocq.

Line numbers refer to `spectec/test-rocq/theories` at upstream `rocq-backend-proof`
`6582b3a39`.
-/

namespace TLC

/-! ## Context update helpers (typing_lemmas.v:26-123) -/

/-
TODO FROM USER: Probably don't need many of these; the built-in syntax should do fine, tidy later
-/

/-- Rocq `typing_lemmas.v:26` `upd_label`. -/
def upd_label (C : context) (labs : List resulttype) : context := { C with LABELS := labs }

/-- Rocq `typing_lemmas.v:29` `upd_local`. -/
def upd_local (C : context) (locs : List valtype) : context := { C with LOCALS := locs }

/-- Rocq `typing_lemmas.v:32` `upd_return`. -/
def upd_return (C : context) (ret : Option resulttype) : context := { C with RETURN := ret }

/-- Rocq `typing_lemmas.v:35` `upd_local_return`. -/
def upd_local_return (C : context) (loc : List valtype) (ret : Option resulttype) : context :=
  upd_return (upd_local C loc) ret

/-- Rocq `typing_lemmas.v:38` `upd_local_label_return`. -/
def upd_local_label_return (C : context) (loc : List valtype) (lab : List resulttype) (ret : Option resulttype) : context :=
  upd_return (upd_label (upd_local C loc) lab) ret

/-- Rocq `typing_lemmas.v:55` `upd_label_overwrite`. `upd_label` is a plain record update on
    `LABELS`, so overwriting it twice collapses definitionally. -/
theorem upd_label_overwrite (C : context) (l1 l2 : List resulttype) :
    upd_label (upd_label C l1) l2 = upd_label C l2 := rfl

/-- Rocq `typing_lemmas.v:61` `upd_label_is_same_as_append`. Rocq builds a near-empty
    context with `LABELS := lab ++ LABELS C` and generic-appends onto `v_C`; since Lean's
    `context.LABELS` is a plain list field, `upd_label` already IS that append directly, so
    this collapses to `rfl` and is stated only for provenance. -/
theorem upd_label_is_same_as_append (C : context) (lab : List resulttype) :
    upd_label C (lab ++ C.LABELS) = { C with LABELS := lab ++ C.LABELS } := rfl

/-- Rocq `typing_lemmas.v:68` `upd_local_is_same_as_append`. -/
theorem upd_local_is_same_as_append (C : context) (loc : List valtype) :
    upd_local C (loc ++ C.LOCALS) = { C with LOCALS := loc ++ C.LOCALS } := rfl

/-- Rocq `typing_lemmas.v:75` `upd_local_return_is_same_as_append`. -/
theorem upd_local_return_is_same_as_append (C : context) (loc : List valtype) (ret : Option resulttype) :
    upd_local_return C (loc ++ C.LOCALS) (ret.orElse (fun _ => C.RETURN)) =
      { C with LOCALS := loc ++ C.LOCALS, RETURN := ret.orElse (fun _ => C.RETURN) } := rfl

/-- Rocq `typing_lemmas.v:92` `upd_return_is_same_as_append`. -/
theorem upd_return_is_same_as_append (C : context) (ret : Option resulttype) :
    upd_return C (ret.orElse (fun _ => C.RETURN)) = { C with RETURN := ret.orElse (fun _ => C.RETURN) } := rfl

/-- Rocq `typing_lemmas.v:100` `upd_label_unchanged`. -/
theorem upd_label_unchanged (C : context) (lab : List resulttype) :
    C.LABELS = lab → upd_label C lab = C := by
  intro h; subst h; rfl

/-- Rocq `typing_lemmas.v:108` `upd_label_unchanged_typing`. See also
    `spectec/test-rocq/upd_label_unchanged_typing_verified_walkthrough.md` for a detailed
    Rocq-side walkthrough of this specific lemma. Direct corollary of `upd_label_unchanged`
    (`upd_label v_C v_C.LABELS = v_C` trivially, so both sides of the `↔` are the same
    proposition). -/
theorem upd_label_unchanged_typing (v_S : store) (v_C : context) (v_admininstrs : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C v_admininstrs v_ft ↔ Instrs_ok2 v_S (upd_label v_C v_C.LABELS) v_admininstrs v_ft := by
  rw [upd_label_unchanged v_C v_C.LABELS rfl]

/-! ## `instr_of : admininstr → Option instr` (typing_lemmas.v:124-196) -/

/-- Rocq `typing_lemmas.v:124` `instr_of`. Every "plain" `admininstr` constructor ↦
    `some` of the corresponding `instr` constructor; the 6 purely-administrative forms
    (`REF_FUNC_ADDR`, `REF_HOST_ADDR`, `CALL_ADDR`, `LABEL_`, `FRAME_`, `TRAP`, which have
    no static-instruction counterpart) ↦ `none`, matching Rocq's trailing `| _ => None`.
    This is exactly the case-for-case mirror image of `wasm2.0.lean`'s own
    `admininstr_instr : instr → admininstr` (the *total* embedding in the other direction,
    already generated by the backend) — every constructor pairing below was read directly
    off that definition rather than re-derived, so the two are guaranteed to agree
    constructor-for-constructor. -/
def instr_of (ai : admininstr) : Option instr :=
  match ai with
  | admininstr.NOP => some instr.NOP
  | admininstr.UNREACHABLE => some instr.UNREACHABLE
  | admininstr.DROP => some instr.DROP
  | admininstr.SELECT x0 => some (instr.SELECT x0)
  | admininstr.BLOCK x0 x1 => some (instr.BLOCK x0 x1)
  | admininstr.LOOP x0 x1 => some (instr.LOOP x0 x1)
  | admininstr.IFELSE x0 x1 x2 => some (instr.IFELSE x0 x1 x2)
  | admininstr.BR x0 => some (instr.BR x0)
  | admininstr.BR_IF x0 => some (instr.BR_IF x0)
  | admininstr.BR_TABLE x0 x1 => some (instr.BR_TABLE x0 x1)
  | admininstr.CALL x0 => some (instr.CALL x0)
  | admininstr.CALL_INDIRECT x0 x1 => some (instr.CALL_INDIRECT x0 x1)
  | admininstr.RETURN => some instr.RETURN
  | admininstr.CONST x0 x1 => some (instr.CONST x0 x1)
  | admininstr.UNOP x0 x1 => some (instr.UNOP x0 x1)
  | admininstr.BINOP x0 x1 => some (instr.BINOP x0 x1)
  | admininstr.TESTOP x0 x1 => some (instr.TESTOP x0 x1)
  | admininstr.RELOP x0 x1 => some (instr.RELOP x0 x1)
  | admininstr.CVTOP x0 x1 x2 => some (instr.CVTOP x0 x1 x2)
  | admininstr.VCONST x0 x1 => some (instr.VCONST x0 x1)
  | admininstr.VVUNOP x0 x1 => some (instr.VVUNOP x0 x1)
  | admininstr.VVBINOP x0 x1 => some (instr.VVBINOP x0 x1)
  | admininstr.VVTERNOP x0 x1 => some (instr.VVTERNOP x0 x1)
  | admininstr.VVTESTOP x0 x1 => some (instr.VVTESTOP x0 x1)
  | admininstr.VUNOP x0 x1 => some (instr.VUNOP x0 x1)
  | admininstr.VBINOP x0 x1 => some (instr.VBINOP x0 x1)
  | admininstr.VTESTOP x0 x1 => some (instr.VTESTOP x0 x1)
  | admininstr.VRELOP x0 x1 => some (instr.VRELOP x0 x1)
  | admininstr.VSHIFTOP x0 x1 => some (instr.VSHIFTOP x0 x1)
  | admininstr.VBITMASK x0 => some (instr.VBITMASK x0)
  | admininstr.VSWIZZLE x0 => some (instr.VSWIZZLE x0)
  | admininstr.VSHUFFLE x0 x1 => some (instr.VSHUFFLE x0 x1)
  | admininstr.VSPLAT x0 => some (instr.VSPLAT x0)
  | admininstr.VEXTRACT_LANE x0 x1 x2 => some (instr.VEXTRACT_LANE x0 x1 x2)
  | admininstr.VREPLACE_LANE x0 x1 => some (instr.VREPLACE_LANE x0 x1)
  | admininstr.VEXTUNOP x0 x1 x2 => some (instr.VEXTUNOP x0 x1 x2)
  | admininstr.VEXTBINOP x0 x1 x2 => some (instr.VEXTBINOP x0 x1 x2)
  | admininstr.VNARROW x0 x1 x2 => some (instr.VNARROW x0 x1 x2)
  | admininstr.VCVTOP x0 x1 x2 => some (instr.VCVTOP x0 x1 x2)
  | admininstr.REF_NULL x0 => some (instr.REF_NULL x0)
  | admininstr.REF_FUNC x0 => some (instr.REF_FUNC x0)
  | admininstr.REF_IS_NULL => some instr.REF_IS_NULL
  | admininstr.LOCAL_GET x0 => some (instr.LOCAL_GET x0)
  | admininstr.LOCAL_SET x0 => some (instr.LOCAL_SET x0)
  | admininstr.LOCAL_TEE x0 => some (instr.LOCAL_TEE x0)
  | admininstr.GLOBAL_GET x0 => some (instr.GLOBAL_GET x0)
  | admininstr.GLOBAL_SET x0 => some (instr.GLOBAL_SET x0)
  | admininstr.TABLE_GET x0 => some (instr.TABLE_GET x0)
  | admininstr.TABLE_SET x0 => some (instr.TABLE_SET x0)
  | admininstr.TABLE_SIZE x0 => some (instr.TABLE_SIZE x0)
  | admininstr.TABLE_GROW x0 => some (instr.TABLE_GROW x0)
  | admininstr.TABLE_FILL x0 => some (instr.TABLE_FILL x0)
  | admininstr.TABLE_COPY x0 x1 => some (instr.TABLE_COPY x0 x1)
  | admininstr.TABLE_INIT x0 x1 => some (instr.TABLE_INIT x0 x1)
  | admininstr.ELEM_DROP x0 => some (instr.ELEM_DROP x0)
  | admininstr.LOAD x0 x1 x2 => some (instr.LOAD x0 x1 x2)
  | admininstr.STORE x0 x1 x2 => some (instr.STORE x0 x1 x2)
  | admininstr.VLOAD x0 x1 x2 => some (instr.VLOAD x0 x1 x2)
  | admininstr.VLOAD_LANE x0 x1 x2 x3 => some (instr.VLOAD_LANE x0 x1 x2 x3)
  | admininstr.VSTORE x0 x1 => some (instr.VSTORE x0 x1)
  | admininstr.VSTORE_LANE x0 x1 x2 x3 => some (instr.VSTORE_LANE x0 x1 x2 x3)
  | admininstr.MEMORY_SIZE => some instr.MEMORY_SIZE
  | admininstr.MEMORY_GROW => some instr.MEMORY_GROW
  | admininstr.MEMORY_FILL => some instr.MEMORY_FILL
  | admininstr.MEMORY_COPY => some instr.MEMORY_COPY
  | admininstr.MEMORY_INIT x0 => some (instr.MEMORY_INIT x0)
  | admininstr.DATA_DROP x0 => some (instr.DATA_DROP x0)
  | admininstr.REF_FUNC_ADDR _ => none
  | admininstr.REF_HOST_ADDR _ => none
  | admininstr.CALL_ADDR _ => none
  | admininstr.LABEL_ _ _ _ => none
  | admininstr.FRAME_ _ _ _ => none
  | admininstr.TRAP => none

/-- Round-trip fact, not in Rocq: `instr_of` really is `admininstr_instr`'s left inverse.
    Used by `ai_typing_inversion'`, and a cheap correctness check on the 68-case
    transcription above (`decide`/`rfl`-style case bash would time out at this size, so
    proved by structural case split instead). -/
theorem instr_of_admininstr_instr (i : instr) : instr_of (admininstr_instr i) = some i := by
  cases i <;> rfl

/-! ## Context/store well-formedness projections (typing_lemmas.v:197-229) -/

/-- Rocq `typing_lemmas.v:197` `instr_ok_context_wf`. Every `Instr_ok` constructor bakes in
    `wf_context`/`wf_instr` directly (confirmed by reading all 73 cases in `wasm2.0.lean`), so
    this is a case split closed uniformly by `assumption` (which searches by type, not name,
    so it's robust to not knowing every constructor's exact argument list). -/
theorem instr_ok_context_wf (v_C : context) (v_instr : instr) (v_ft : functype) :
    Instr_ok v_C v_instr v_ft → wf_context v_C ∧ wf_instr v_instr := by
  intro h
  cases h <;> exact ⟨by assumption, by assumption⟩

/-- Helper: `wf_admininstr` unconditionally holds for `admininstr_ref v_ref`, for any `v_ref`
    (all three `wf_admininstr` cases for `REF_NULL`/`REF_FUNC_ADDR`/`REF_HOST_ADDR` have no
    premises in `wasm2.0.lean`). Needed because `Instr_ok2`'s `ref` constructor, unlike its
    other 5 constructors, does NOT bake in a `wf_admininstr` premise directly. -/
theorem wf_admininstr_ref (v_ref : ref) : wf_admininstr (admininstr_ref v_ref) := by
  cases v_ref <;> constructor

/-- Helper: `wf_instr v_instr → wf_admininstr (admininstr_instr v_instr)`. Needed because
    `Instr_ok2`'s `plain` constructor gives `wf_instr v_instr` (the *static* instruction's
    wellformedness), not `wf_admininstr (admininstr_instr v_instr)` directly. `admininstr_instr`
    maps every `instr` constructor to the identically-shaped `admininstr` constructor of the
    same name, and (confirmed by spot-checking several cases in `wasm2.0.lean`) `wf_instr`'s
    and `wf_admininstr`'s cases for corresponding constructors carry identical premises (both
    generated from the same EL-spec wellformedness rule) — so this case-splits both sides in
    lockstep and closes every resulting premise-subgoal by `assumption`. -/
theorem wf_instr_admininstr (v_instr : instr) (h : wf_instr v_instr) :
    wf_admininstr (admininstr_instr v_instr) := by
  cases v_instr <;> cases h <;> constructor <;> assumption

/-- Rocq `typing_lemmas.v:205` `ainstr_ok_context_store_wf`. 4 of `Instr_ok2`'s 6
    constructors bake in `wf_admininstr` directly (closed by `assumption`); `plain` needs
    `wf_instr_admininstr` and `ref` needs `wf_admininstr_ref` instead (see their doc
    comments). -/
theorem ainstr_ok_context_store_wf (v_S : store) (v_C : context) (v_ainstr : admininstr) (v_ft : functype) :
    Instr_ok2 v_S v_C v_ainstr v_ft → wf_context v_C ∧ wf_store v_S ∧ wf_admininstr v_ainstr := by
  intro h
  cases h <;> exact ⟨by assumption, by assumption,
    by first | assumption | exact wf_admininstr_ref _ | exact wf_instr_admininstr _ (by assumption)⟩

/-- Rocq `typing_lemmas.v:213` `instrs_ok_context_wf`. Unlike `instr_ok_context_wf`, the
    `Forall wf_instr v_instrs` component isn't a single hypothesis in every `Instrs_ok`
    constructor: `empty` needs it derived (vacuously, for `[]`), `instr` needs it derived from
    a singular `wf_instr` fact, and `seq` needs two `Forall`s combined across `++`. `sub`/
    `frame` do carry it directly. Every constructor argument (data and hypothesis alike) is
    named explicitly below, matching `wasm2.0.lean`'s `Instrs_ok` telescope exactly, to avoid
    relying on `rename_i`'s exact ordering. -/
theorem instrs_ok_context_wf (v_C : context) (v_instrs : List instr) (v_ft : functype) :
    Instrs_ok v_C v_instrs v_ft → wf_context v_C ∧ Forall wf_instr v_instrs := by
  intro h
  refine ⟨by cases h <;> assumption, ?_⟩
  cases h with
  | empty C hwf => intro p hp; simp at hp
  | instr C v_instr t_1_lst t_2_lst hty hwf hinstr =>
      intro p hp; simp at hp; subst hp; exact hinstr
  | seq C instr_1_lst instr_2_lst t_1_lst t_3_lst t_2_lst h1 h2 hwf hf1 hf2 =>
      intro p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact hf1 p hp'
      · exact hf2 p hp'
  | sub C instr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst h1 hs1 hs2 hwf hf => exact hf
  | frame C instr_lst t_lst t_1_lst t_2_lst h1 hwf hf => exact hf

/-- Rocq `typing_lemmas.v:221` `ainstrs_ok_context_store_wf`. `Instrs_ok2` mirrors `Instrs_ok`
    field-for-field (with `Instr_ok2`/`wf_admininstr`/`wf_store` in place of `Instr_ok`/
    `wf_instr`); same proof shape as `instrs_ok_context_wf`, with the last constructor named
    `Instrs_ok2_frame` rather than `frame`. -/
theorem ainstrs_ok_context_store_wf (v_S : store) (v_C : context) (v_ainstrs : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C v_ainstrs v_ft → wf_context v_C ∧ wf_store v_S ∧ Forall wf_admininstr v_ainstrs := by
  intro h
  refine ⟨by cases h <;> assumption, by cases h <;> assumption, ?_⟩
  cases h with
  | empty C hs hwf => intro p hp; simp at hp
  | instr C v_admininstr t_1_lst t_2_lst hty hs hwf hinstr =>
      intro p hp; simp at hp; subst hp; exact hinstr
  | seq C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst h1 h2 hs hwf hf1 hf2 =>
      intro p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact hf1 p hp'
      · exact hf2 p hp'
  | sub C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst h1 hs1 hs2 hs hwf hf => exact hf
  | Instrs_ok2_frame C admininstr_lst t_lst t_1_lst t_2_lst h1 hs hwf hf => exact hf

/-! ## Composition/empty-typing lemmas, `ai_principal_typing` (typing_lemmas.v:269-628) -/

-- `instrs_empty_typing`/`ais_empty_typing` (Rocq `typing_lemmas.v:299`/`333`) are stated and
-- proved further below, right after `ais_ok_widen_out`, since their proofs need
-- `instrs_ok_nil_sub`/`instrs_ok_widen_in`/`ais_ok_nil_sub`/`ais_ok_widen_in` (part of the
-- seq-typing-inversion scaffolding), which are declared later in this file.

/-- Rocq `typing_lemmas.v:377` `ai_principal_typing` — **THE central definition of the
    file**. Ported from the user's own hand-written `spectec/test-lean/typing_lemmas.lean`
    (built against the `wasm2.0.lean` of that time, byte-for-byte identical to this
    project's then — confirmed via `diff` before porting), per the user's explicit go-ahead to
    reuse it after checking correctness. Later corrections against Rocq: a `REF_HOST_ADDR`
    case (it had fallen through to the `| _ => True` catch-all), `GLOBAL_SET` pinned to a
    mutable global, the `Instr_ok … RETURN …` conjunct of `RETURN`, and the
    `ts.length = v_n` conjunct of `FRAME_`.

    **One real bug found and fixed while checking**: the source file's `BR_TABLE` case wrote
    `∀ l ∈ ls, ∃ r, ... ∧ ... ∧ ∃ r', ...` with no parens around the `∀`'s body, so Lean's
    greedy parsing put the trailing `∃ r', LABELS[l']? = r' ∧ ts subs< r'` clause *inside* the
    `∀ l ∈ ls` binder. That's vacuously true whenever `ls = []` (a valid `BR_TABLE` with only
    a default target), silently dropping the requirement that the *default* label `l'` itself
    be valid and subtype-compatible — checked against the live Rocq `ai_principal_typing`
    (`typing_lemmas.v:414`), which states the two `Forall`s over `ls` and the two conditions
    on `l'` as five independent top-level conjuncts, confirming the default-label conditions
    must NOT be gated by `ls`. Fixed here by parenthesizing the `∀` explicitly.

    **One deliberate difference from Rocq**: the `LOAD`/`STORE` packed-access cases here
    require an `Inn` (`I32`/`I64`) numtype (`nt = numtype_Inn inntype`), so they are
    unsatisfiable for `F32`/`F64` — for `LOAD` this is equivalent to Rocq's explicit
    `admininstr_LOAD F32/F64 (Some _) _ => False` cases. Rocq's `STORE`-packed case does not
    exclude `F32`/`F64` (its exclusion arms are commented out, `typing_lemmas.v:562-563`), which
    is laxer than its own `Instr_ok` rule `store_pack` (`Inn`-only). The Lean version agrees with
    `Instr_ok`, and no proof needs the laxer reading. -/
def ai_principal_typing (v_S : store) (v_C : context) (v_ai : admininstr) (v_ft : functype) : Prop :=
  match v_ai with
  | admininstr.NOP => v_ft = mkFunctype [] []
  | admininstr.UNREACHABLE => True
  | admininstr.DROP => ∃ t : valtype, v_ft = mkFunctype [t] []
  | admininstr.SELECT (some [t]) => v_ft = mkFunctype [t, t, valtype.I32] [t]
  | admininstr.SELECT none =>
    ∃ t t' : valtype,
      v_ft = mkFunctype [t, t, valtype.I32] [t] ∧ Valtype_sub t t' ∧
      ((∃ nt : numtype, t' = valtype_numtype nt) ∨ (∃ vt : vectype, t' = valtype_vectype vt))
  | admininstr.SELECT _ => False
  | admininstr.BLOCK bt instrs =>
    ∃ t1s t2s : List valtype,
      v_ft = mkFunctype t1s t2s ∧ Blocktype_ok v_C bt (mkFunctype t1s t2s) ∧
      Instrs_ok { v_C with LABELS := (list.mk_list t2s) :: v_C.LABELS } instrs (mkFunctype t1s t2s)
  | admininstr.LOOP bt instrs =>
    ∃ t1s t2s : List valtype,
      v_ft = mkFunctype t1s t2s ∧ Blocktype_ok v_C bt (mkFunctype t1s t2s) ∧
      Instrs_ok { v_C with LABELS := (list.mk_list t1s) :: v_C.LABELS } instrs (mkFunctype t1s t2s)
  | admininstr.IFELSE bt instrs1 instrs2 =>
    ∃ t1s t2s : List valtype,
      v_ft = mkFunctype (t1s ++ [valtype.I32]) t2s ∧ Blocktype_ok v_C bt (mkFunctype t1s t2s) ∧
      Instrs_ok { v_C with LABELS := (list.mk_list t2s) :: v_C.LABELS } instrs1 (mkFunctype t1s t2s) ∧
      Instrs_ok { v_C with LABELS := (list.mk_list t2s) :: v_C.LABELS } instrs2 (mkFunctype t1s t2s)
  | admininstr.BR l =>
    ∃ t1s ts t2s : List valtype,
      v_ft = mkFunctype (t1s ++ ts) t2s ∧ v_C.LABELS[proj_uN_0 l]? = some (list.mk_list ts)
  | admininstr.BR_IF l =>
    ∃ ts : List valtype,
      v_ft = mkFunctype (ts ++ [valtype.I32]) ts ∧ v_C.LABELS[proj_uN_0 l]? = some (list.mk_list ts)
  | admininstr.BR_TABLE ls l' =>
    ∃ t1s ts t2s : List valtype,
      v_ft = mkFunctype (t1s ++ ts ++ [valtype.I32]) t2s ∧
      (∀ l ∈ ls, ∃ r : resulttype, v_C.LABELS[proj_uN_0 l]? = some r ∧ Resulttype_sub (list.mk_list ts) r) ∧
      (∃ r' : resulttype, v_C.LABELS[proj_uN_0 l']? = some r' ∧ Resulttype_sub (list.mk_list ts) r')
  | admininstr.CALL x =>
    ∃ t1s t2s : List valtype, v_ft = mkFunctype t1s t2s ∧ v_C.FUNCS[proj_uN_0 x]? = some (mkFunctype t1s t2s)
  | admininstr.CALL_INDIRECT x y =>
    ∃ t1s t2s : List valtype, ∃ lim : limits,
      v_ft = mkFunctype (t1s ++ [valtype.I32]) t2s ∧
      v_C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim reftype.FUNCREF) ∧
      v_C.TYPES[proj_uN_0 y]? = some (mkFunctype t1s t2s)
  | admininstr.RETURN =>
    ∃ t1s ts t2s : List valtype, v_ft = mkFunctype (t1s ++ ts) t2s ∧ v_C.RETURN = some (list.mk_list ts) ∧
      -- TODO FROM USER: Investigate to what extent we can just use Instr_ok for these, e.g. CONST
      Instr_ok v_C instr.RETURN (mkFunctype (t1s ++ ts) t2s)
  | admininstr.CONST nt c => v_ft = mkFunctype [] [valtype_numtype nt] ∧ wf_num_ nt c
  | admininstr.UNOP nt _ => v_ft = mkFunctype [valtype_numtype nt] [valtype_numtype nt]
  | admininstr.BINOP nt _ => v_ft = mkFunctype [valtype_numtype nt, valtype_numtype nt] [valtype_numtype nt]
  | admininstr.TESTOP nt _ => v_ft = mkFunctype [valtype_numtype nt] [valtype.I32]
  | admininstr.RELOP nt _ => v_ft = mkFunctype [valtype_numtype nt, valtype_numtype nt] [valtype.I32]
  | admininstr.CVTOP nt1 nt2 _ => v_ft = mkFunctype [valtype_numtype nt2] [valtype_numtype nt1]
  | admininstr.VCONST vt c =>
    ∃ uN_size : Nat, size (valtype_vectype vt) = some uN_size ∧ wf_uN uN_size c ∧
      v_ft = mkFunctype [] [valtype_vectype vt]
  | admininstr.REF_NULL rt => v_ft = mkFunctype [] [valtype_reftype rt]
  | admininstr.REF_FUNC x =>
    ∃ ft : functype, v_ft = mkFunctype [] [valtype_reftype reftype.FUNCREF] ∧ v_C.FUNCS[proj_uN_0 x]? = some ft
  | admininstr.REF_IS_NULL => ∃ rt : reftype, v_ft = mkFunctype [valtype_reftype rt] [valtype.I32]
  | admininstr.LOCAL_GET x =>
    ∃ t : valtype, v_ft = mkFunctype [] [t] ∧ v_C.LOCALS[proj_uN_0 x]? = some t
  | admininstr.LOCAL_SET x =>
    ∃ t : valtype, v_ft = mkFunctype [t] [] ∧ v_C.LOCALS[proj_uN_0 x]? = some t
  | admininstr.LOCAL_TEE x =>
    ∃ t : valtype, v_ft = mkFunctype [t] [t] ∧ v_C.LOCALS[proj_uN_0 x]? = some t
  | admininstr.GLOBAL_GET x =>
    ∃ (t : valtype) (m : «mut»), v_ft = mkFunctype [] [t] ∧ v_C.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype m t)
  | admininstr.GLOBAL_SET x =>
    ∃ (t : valtype), v_ft = mkFunctype [t] [] ∧
      v_C.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype (some r_MUT.MUT) t)
  | admininstr.TABLE_GET x =>
    ∃ (rt : reftype) (lim : limits),
      v_ft = mkFunctype [valtype.I32] [valtype_reftype rt] ∧ v_C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)
  | admininstr.TABLE_SET x =>
    ∃ (rt : reftype) (lim : limits),
      v_ft = mkFunctype [valtype.I32, valtype_reftype rt] [] ∧ v_C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)
  | admininstr.TABLE_SIZE x =>
    ∃ (rt : reftype) (lim : limits),
      v_ft = mkFunctype [] [valtype.I32] ∧ v_C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)
  | admininstr.TABLE_GROW x =>
    ∃ (rt : reftype) (lim : limits),
      v_ft = mkFunctype [valtype_reftype rt, valtype.I32] [valtype.I32] ∧ v_C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)
  | admininstr.TABLE_FILL x =>
    ∃ (rt : reftype) (lim : limits),
      v_ft = mkFunctype [valtype.I32, valtype_reftype rt, valtype.I32] [] ∧ v_C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)
  | admininstr.TABLE_COPY x1 x2 =>
    ∃ (rt : reftype) (lim1 lim2 : limits),
      v_ft = mkFunctype [valtype.I32, valtype.I32, valtype.I32] [] ∧
      v_C.TABLES[proj_uN_0 x1]? = some (tabletype.mk_tabletype lim1 rt) ∧
      v_C.TABLES[proj_uN_0 x2]? = some (tabletype.mk_tabletype lim2 rt)
  | admininstr.TABLE_INIT x1 x2 =>
    ∃ (rt : reftype) (lim : limits),
      v_ft = mkFunctype [valtype.I32, valtype.I32, valtype.I32] [] ∧
      v_C.TABLES[proj_uN_0 x1]? = some (tabletype.mk_tabletype lim rt) ∧
      v_C.ELEMS[proj_uN_0 x2]? = some rt
  | admininstr.ELEM_DROP x =>
    ∃ rt : reftype, v_ft = mkFunctype [] [] ∧ v_C.ELEMS[proj_uN_0 x]? = some rt
  | admininstr.LOAD nt none marg =>
    ∃ (mt : memtype) (sz : Nat),
      v_ft = mkFunctype [valtype.I32] [valtype_numtype nt] ∧ v_C.MEMS[0]? = some mt ∧
      size (valtype_numtype nt) = some sz ∧ 2 ^ (proj_uN_0 marg.ALIGN) ≤ (sz / 8)
  | admininstr.LOAD nt (some (loadop_.mk_loadop__0 inntype (loadop_Inn.mk_loadop_Inn (sz.mk_sz num_bits_to_read) _))) marg =>
    nt = numtype_Inn inntype ∧
    ∃ mt : memtype,
      v_ft = mkFunctype [valtype.I32] [valtype_Inn inntype] ∧ v_C.MEMS[0]? = some mt ∧
      2 ^ (proj_uN_0 marg.ALIGN) ≤ (num_bits_to_read / 8)
  | admininstr.STORE nt none marg =>
    ∃ (mt : memtype) (sz : Nat),
      v_ft = mkFunctype [valtype.I32, valtype_numtype nt] [] ∧ v_C.MEMS[0]? = some mt ∧
      size (valtype_numtype nt) = some sz ∧ 2 ^ (proj_uN_0 marg.ALIGN) ≤ (sz / 8)
  | admininstr.STORE nt (some (sz.mk_sz num_bits_to_read)) marg =>
    ∃ (mt : memtype) (inntype : Inn),
      nt = numtype_Inn inntype ∧ v_ft = mkFunctype [valtype.I32, valtype_numtype nt] [] ∧
      v_C.MEMS[0]? = some mt ∧ 2 ^ (proj_uN_0 marg.ALIGN) ≤ (num_bits_to_read / 8)
  | admininstr.MEMORY_SIZE => ∃ mt : memtype, v_ft = mkFunctype [] [valtype.I32] ∧ v_C.MEMS[0]? = some mt
  | admininstr.MEMORY_GROW => ∃ mt : memtype, v_ft = mkFunctype [valtype.I32] [valtype.I32] ∧ v_C.MEMS[0]? = some mt
  | admininstr.MEMORY_FILL =>
    ∃ mt : memtype, v_ft = mkFunctype [valtype.I32, valtype.I32, valtype.I32] [] ∧ v_C.MEMS[0]? = some mt
  | admininstr.MEMORY_COPY =>
    ∃ mt : memtype, v_ft = mkFunctype [valtype.I32, valtype.I32, valtype.I32] [] ∧ v_C.MEMS[0]? = some mt
  | admininstr.MEMORY_INIT x =>
    ∃ mt : memtype,
      v_ft = mkFunctype [valtype.I32, valtype.I32, valtype.I32] [] ∧ v_C.MEMS[0]? = some mt ∧
      v_C.DATAS[proj_uN_0 x]? = some datatype.OK
  | admininstr.DATA_DROP x => v_ft = mkFunctype [] [] ∧ v_C.DATAS[proj_uN_0 x]? = some datatype.OK
  | admininstr.REF_FUNC_ADDR a =>
    ∃ ft : functype,
      v_ft = mkFunctype [] [valtype_reftype reftype.FUNCREF] ∧
      Externaddr_ok v_S (externaddr.FUNC a) (externtype.FUNC ft)
  | admininstr.REF_HOST_ADDR _ => v_ft = mkFunctype [] [valtype_reftype reftype.EXTERNREF]
  | admininstr.CALL_ADDR a =>
    ∃ ts1 ts2 : List valtype,
      v_ft = mkFunctype ts1 ts2 ∧ Externaddr_ok v_S (externaddr.FUNC a) (externtype.FUNC (mkFunctype ts1 ts2))
  | admininstr.LABEL_ n_ instrs admininstrs =>
    ∃ ts t's : List valtype,
      v_ft = mkFunctype [] ts ∧ t's.length = n_ ∧
      Instrs_ok2 v_S v_C (instrs.map admininstr_instr) (mkFunctype t's ts) ∧
      Instrs_ok2 v_S { v_C with LABELS := (list.mk_list t's) :: v_C.LABELS } admininstrs (mkFunctype [] ts)
  | admininstr.FRAME_ v_n f admininstrs =>
    ∃ (ts : List valtype) (c' : context),
      v_ft = mkFunctype [] ts ∧ Frame_ok v_S f c' ∧
      Expr_ok2 v_S { c' with RETURN := some (list.mk_list ts) } admininstrs (list.mk_list ts) ∧
      ts.length = v_n
  | admininstr.TRAP => True
  | _ => True

/-- Rocq `typing_lemmas.v:626` `instr_principal_typing`. Store is irrelevant for the
    surface (non-administrative) judgment; Rocq plugs in `default_val : store`, matching
    Lean's `default : store` (both types already `deriving Inhabited`). -/
def instr_principal_typing (v_C : context) (v_instr : instr) (v_ft : functype) : Prop :=
  ai_principal_typing default v_C (admininstr_instr v_instr) v_ft

/-! ## Master inversion theorems (typing_lemmas.v:629-810) -/

/-- Rocq `typing_lemmas.v:629` `instr_typing_inversion`. -/
theorem instr_typing_inversion (v_C : context) (v_instr : instr) (t1s t2s : List valtype) :
    Instr_ok v_C v_instr (mkFunctype t1s t2s) → instr_principal_typing v_C v_instr (mkFunctype t1s t2s) := by
  intro h
  cases h
  case br_table l_lst l' t1_lst t_lst wf_instr_bt h_ls_bound h_ls_sub h_l'_bound h_l'_sub wf_c =>
    -- Handled *before* the shared `simp_all` pipeline below: empirically, `simp_all`
    -- mangles this specific case's hypothesis names/shapes (its two `Forall`s over the
    -- same `l_lst`, plus a `∀ l ∈ ls` in the goal, confuse it), unlike every other case,
    -- which `simp_all` handles fine. Confirmed via `trace_state` during porting. Also
    -- note: `cases`'s actual binder order here is NOT the source declaration order —
    -- `wf_instr` (declared last, but mentions the same `l_lst`/`l'` as the conclusion
    -- index) is bound *first* among the hypotheses, confirmed empirically the same way.
    unfold instr_principal_typing
    unfold ai_principal_typing
    simp only [admininstr_instr]
    refine ⟨t1_lst, t_lst, t2s, by simp [List.append_assoc], ?_, ?_⟩
    · intro l hl
      exact ⟨v_C.LABELS[proj_uN_0 l]!, by simp [h_ls_bound l hl], h_ls_sub l hl⟩
    · exact ⟨v_C.LABELS[proj_uN_0 l']!, by simp [h_l'_bound], h_l'_sub⟩
  all_goals (
    unfold instr_principal_typing
    <;> unfold ai_principal_typing
    <;> simp only [admininstr_instr]
    <;> try simp_all)

  case drop t wf_drop wf_c =>
    exists t

  case select_impl
      t t' nt vt subt
      t'_constraints wf_select wf_c =>
    refine ⟨t, rfl, t', subt, ?_⟩
    rcases t'_constraints with t'_constraint | t'_constraint
    · exact Or.inl ⟨nt, t'_constraint⟩
    · exact Or.inr ⟨vt, t'_constraint⟩

  case block
      bt instrs wf_block wf_c wf_c' bt_ok instrs_ok =>
    exists t1s
    exists t2s

  case loop
      bt instrs wf_loop wf_c wf_c' bt_ok instrs_ok =>
    exists t1s
    exists t2s

  case «if»
      bt instrs1 instrs2 t wf_if wf_c wf_c' bt_ok instrs1_ok instrs2_ok =>
    exists t
    exists t2s

  case br
      lidx t1s' ts wf_br lidx_within_LABELS LABELS_gives_ts wf_c =>
    exists t1s'
    exists ts
    apply And.intro
    · exists t2s
    · unfold proj_list_0 at LABELS_gives_ts
      have hlab : v_C.LABELS[proj_uN_0 lidx] = list.mk_list ts :=
        Eq.subst (motive := fun z => v_C.LABELS[proj_uN_0 lidx] = list.mk_list z) LABELS_gives_ts rfl
      simp only [hlab]

  case br_if
      lidx wf_br_if lidx_within_LABELS wf_c LABELS_gives_t2s =>
    exists t2s
    apply And.intro
    · rfl
    · unfold proj_list_0 at LABELS_gives_t2s
      have h : v_C.LABELS[(proj_uN_0 lidx)] = (list.mk_list t2s) :=
        Eq.subst (motive := fun x => v_C.LABELS[(proj_uN_0 lidx)] = list.mk_list x) LABELS_gives_t2s rfl
      simp only [h]

  case call
      idx wf_call idx_within_FUNCS wf_c FUNCS_gives_ft =>
    exists t1s
    exists t2s

  case call_indirect
      idx1 idx2 t1s' lim wf_call_indirect wf_tt idx1_within_TABLES idx2_within_TYPES
      TABLES_gives_tt idx2_within_TYPES2 wf_c TYPES_gives_ft =>
    exists t1s', t2s

  case «return»
      t1s' ts wf_return RETURN_gives_ts wf_c =>
    exists t1s', t2s
    exact ⟨rfl, Instr_ok.return v_C t1s' ts t2s RETURN_gives_ts wf_c wf_return⟩

  case const
      nt n wf_const wf_c =>
    cases wf_const with
    | instr_case_13 nt n h =>
        exact h

  case ref_func
      idx ft wf_ref_func idx_in_FUNCS FUNCS_gives_ft wf_c =>
    rfl

  case ref_is_null
      rt wr_ref_is_null wf_c =>
    exists rt

  case vconst
      vec wf_vconst wf_c =>
    cases wf_vconst with
    | instr_case_19 vt v not_none_size wf_vec =>
        refine ⟨(size (valtype_vectype vectype.V128)).get!, ?_, ?_, ?_⟩
        · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp not_none_size
          rfl
        · exact wf_vec
        · rfl

  case load_val
      nt marg mt MEMS_length_nonzero nt_size_not_none
      size_constraint wf_mt wf_load MEMS_length_nonzero2
      mt_at_MEMS_0_idx wf_c =>
    refine ⟨(size (valtype_numtype nt)).get!, ?_, ?_⟩
    · cases nt <;>
      simp [size, valtype_numtype]
    · cases nt <;>
      simp [size, valtype_numtype] at size_constraint ⊢ <;>
      norm_num at size_constraint <;>
      exact_mod_cast size_constraint

  case load_pack
      inn m is_signed marg mt size_constraint wf_inn
      wf_load MEMS_not_empty MEMS_0_is_marg wf_c =>
    cases m
    · norm_num at size_constraint ⊢
      have h_false : False := by
        have h_pos : (2 ^ (proj_uN_0 marg.ALIGN)) > (0 : Rat) := by positivity
        linarith only [size_constraint, h_pos]
      exact h_false
    · rename_i n
      have bridge :
        ∀ (n0 n1 n2 : Nat), n0 ≤ ((n1 : Rat) / n2) → n0 ≤ (n1 / n2) := by
            intros n0 n1 n2 h
            rcases Nat.eq_zero_or_pos n2 with hz | hpos
            · subst hz
              simp at h ⊢
              exact_mod_cast h
            · rcases lt_or_ge ((n1:Rat) / n2) (n0 + 1 : Rat) with hlt | hge
              · have heq : n1 / n2 = n0 := by
                  have hmul_le : n0 * n2 ≤ n1 := by
                    rw [le_div_iff₀ (by exact_mod_cast hpos : (0:Rat) < n2)] at h
                    exact_mod_cast h
                  have hmul_lt : n1 < (n0 + 1) * n2 := by
                    rw [div_lt_iff₀ (by exact_mod_cast hpos : (0:Rat) < n2)] at hlt
                    exact_mod_cast hlt
                  have h1 : n0 ≤ (n1 / n2) := (Nat.le_div_iff_mul_le hpos).mpr hmul_le
                  have h2 : (n1 / n2) < (n0 + 1) := (Nat.div_lt_iff_lt_mul hpos).mpr hmul_lt
                  omega
                omega
              · have : n0 + 1 ≤ n1 / n2 := by
                  rw [Nat.le_div_iff_mul_le hpos]
                  rw [le_div_iff₀ (by exact_mod_cast hpos)] at hge
                  exact_mod_cast hge
                omega
      exact_mod_cast
        bridge (2 ^ (proj_uN_0 marg.ALIGN)) n.succ 8
          (by exact_mod_cast size_constraint)

  case store_val
      nt marg mt MEMS_length_nonzero nt_size_not_none size_constraint
      wf_mt wf_store MEMS_length_nonzero2 mt_at_MEMS_0_idx wf_c =>
    refine ⟨(size (valtype_numtype nt)).get!, ?_, ?_⟩
    · cases nt <;>
      simp [size, valtype_numtype]
    · cases nt <;>
      simp [size, valtype_numtype, Option.bind, Option.get] at size_constraint ⊢ <;>
      norm_num at size_constraint <;>
        exact_mod_cast size_constraint

  case store_pack
      inn m marg mt size_constraint wf_mt wf_store
      MEMS_not_empty MEMS_0_is_mt wf_c =>
    apply And.intro
    · cases inn <;>
      simp [valtype_Inn, valtype_numtype] <;>
      rfl
    · have bridge :
        ∀ (n0 n1 n2 : Nat), n0 ≤ ((n1 : Rat) / n2) → n0 ≤ (n1 / n2) := by
            intros n0 n1 n2 h
            rcases Nat.eq_zero_or_pos n2 with h_zero | h_pos
            · subst h_zero
              simp [*] at h ⊢
              exact h
            · rcases lt_or_ge (n1 / n2) (n0 + 1) with h2_near | h_far
              · have lower_limit : n1/n2 = n0 := by
                    let upper := h2_near
                    have lower : n0 ≤ n1/n2 := by
                        have h_throwaway : n0 * n2 ≤ n1 := by
                            rw [le_div_iff₀ (by exact_mod_cast h_pos)] at h
                            exact_mod_cast h
                        exact (Nat.le_div_iff_mul_le h_pos).mpr h_throwaway
                    omega
                omega
              · omega
      have applied_bridge := bridge ((2 : ℕ) ^ (proj_uN_0 marg.ALIGN)) m 8 (
        by
        exact_mod_cast size_constraint
      )
      exact applied_bridge

/-- Lean-only helper (not independently named in the Rocq source, near
    `instr_principal_typing`, `typing_lemmas.v:626`; needed by `ai_typing_inversion`'s `plain`
    case below): bridges
    `instr_principal_typing` (surface, `Instr_ok`-facing) and `ai_principal_typing`
    (administrative, `Instr_ok2`-facing) for the "plain" (non-purely-administrative)
    instructions, since `Instr_ok2.plain` produces its conclusion via `admininstr_instr`.
    Ported from a prior Lean session's `spectec/test-lean/typing_lemmas.lean`
    `principal_typing_conversion`. -/
theorem principal_typing_conversion (i : instr) :
    ∀ (s : store) (c : context) (t1s t2s : List valtype),
      instr_principal_typing c i (mkFunctype t1s t2s)
      ↔ ai_principal_typing s c (admininstr_instr i) (mkFunctype t1s t2s) := by
  intro s c t1s t2s
  unfold instr_principal_typing
  cases i <;> try rfl
  case SELECT op_ts =>
    cases op_ts
    case none => rfl
    case some t =>
      cases t
      case nil => rfl
      case cons head tail =>
        cases tail
        case nil => rfl
        case cons head' tail' => rfl
  case LOAD nt o_loadop marg =>
    cases o_loadop
    case none => rfl
    case some loadop =>
      cases loadop
      case mk_loadop__0 inn l_inn => rfl
  case STORE nt o_sz marg =>
    cases o_sz
    case none => rfl
    case some sz => rfl

/-- Rocq `typing_lemmas.v:672` `ai_typing_inversion` — **the master per-instruction
    inversion lemma**, administrative level, up to `<ti:` subtyping. Highest
    difficulty/longest proof in the "inversion" family (57-way case split in Rocq). Ported
    from the user's `spectec/test-lean/typing_lemmas.lean` (built against the then-identical
    `wasm2.0.lean`), using this project's own already-proved `instrtype_sub_refl`
    (`Subtyping.lean`) in place of that file's own un-proved copy of the same lemma. -/
theorem ai_typing_inversion (v_S : store) (v_C : context) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instr_ok2 v_S v_C v_ai (mkFunctype t1s t2s) →
    ∃ t1s' t2s', ai_principal_typing v_S v_C v_ai (mkFunctype t1s' t2s') ∧
      instrtype_sub (mkFunctype t1s' t2s') (mkFunctype t1s t2s) := by
  intro instr_ok2
  generalize gen_ft : mkFunctype t1s t2s = ft at instr_ok2
  cases instr_ok2 using Instr_ok2.casesOn
  case plain i t1s' t2s' hwfS hwfI hinstr_ok hwfC =>
    refine ⟨t1s', t2s', ?_, ?_⟩
    case refine_1 =>
      apply (principal_typing_conversion i v_S v_C t1s' t2s').mp
      exact instr_typing_inversion v_C i t1s' t2s' hinstr_ok
    case refine_2 =>
      exact instrtype_sub_refl _
  case Instr_ok2_frame v_n f ais t_lst c' hframe hexpr hwfS hwfC' hwfai hwfCtx hlen hwfC =>
    refine ⟨[], t_lst, ?_, ?_⟩
    case refine_1 =>
      exact ⟨t_lst, c', rfl, hframe, hexpr, hlen.symm⟩
    case refine_2 =>
      exact instrtype_sub_refl _
  case label v_n instrs ais out_ts lab_ts hwfS hwfai hwfCtx hlen instrs_ok ais_ok hwfC =>
    refine ⟨[], out_ts, ?_, ?_⟩
    case refine_1 =>
      exact ⟨out_ts, lab_ts, rfl, hlen.symm, instrs_ok, ais_ok⟩
    case refine_2 =>
      exact instrtype_sub_refl _
  case call_addr faddr t1s' t2s' hext hwfS hwfai hwfext hwfC =>
    refine ⟨t1s', t2s', ?_, ?_⟩
    case refine_1 =>
      exact ⟨t1s', t2s', rfl, hext⟩
    case refine_2 =>
      exact instrtype_sub_refl _
  case ref r rt href hwfS hwfC =>
    refine ⟨[], [valtype_reftype rt], ?_, ?_⟩
    case refine_1 =>
      unfold ai_principal_typing
      cases r with
      | REF_NULL rt' =>
        unfold admininstr_ref
        cases href with
        | null hs => rfl
      | REF_FUNC_ADDR faddr =>
        cases href
        rename_i extft hwf_store hwf_externtype hexternaddr
        exact ⟨extft, rfl, hexternaddr⟩
      | REF_HOST_ADDR haddr =>
        unfold admininstr_ref
        cases href with
        | extern hs => rfl
    case refine_2 =>
      exact instrtype_sub_refl _
  case trap ta tb hwfS hwfai hwfC =>
    refine ⟨ta, tb, ?_, ?_⟩
    case refine_1 => trivial
    case refine_2 => exact instrtype_sub_refl _

/-- Rocq `typing_lemmas.v:790` `ai_typing_inversion'`. The no-slack
    special case of `ai_typing_inversion` for an embedded plain instruction: an `Instr_ok2`
    derivation for `admininstr_instr v_instr` can only come from `Instr_ok2.plain` (or, for
    `REF_NULL`, from `Instr_ok2.ref`), so it hands back `Instr_ok` at the *same* type. -/
theorem ai_typing_inversion' (v_S : store) (v_C : context) (v_instr : instr) (t1s t2s : List valtype) :
    Instr_ok2 v_S v_C (admininstr_instr v_instr) (mkFunctype t1s t2s) →
    Instr_ok v_C v_instr (mkFunctype t1s t2s) := by
  -- Rocq destructs both instructions (68×68); here the generalized index equation is pushed
  -- through `instr_of`, which inverts `admininstr_instr` and is `none` on the
  -- administrative-only constructors.
  intro h
  generalize hai : admininstr_instr v_instr = ai at h
  generalize hft : mkFunctype t1s t2s = ft at h
  have hof : instr_of ai = some v_instr := by rw [← hai]; exact instr_of_admininstr_instr v_instr
  cases h with
  | plain C i t1 t2 hok _ _ _ =>
    rw [instr_of_admininstr_instr] at hof
    injection hof with hi
    subst hi
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    exact hok
  | ref C r rt href _ hwfC =>
    cases r with
    | REF_NULL rt' =>
      simp only [admininstr_ref, instr_of] at hof
      injection hof with hi
      subst hi
      cases href
      simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at hft
      obtain ⟨e1, e2⟩ := hft
      subst e1; subst e2
      exact Instr_ok.ref_null v_C _ hwfC (by constructor)
    | REF_FUNC_ADDR a => simp [admininstr_ref, instr_of] at hof
    | REF_HOST_ADDR a => simp [admininstr_ref, instr_of] at hof
  | label => simp [instr_of] at hof
  | Instr_ok2_frame => simp [instr_of] at hof
  | call_addr => simp [instr_of] at hof
  | trap => simp [instr_of] at hof

/-! ## Single/seq/append composition — surface and administrative, both directions
    (typing_lemmas.v:811-1178) -/

/-- Rocq `typing_lemmas.v:811` `split_single_append`. Generic list helper. -/
theorem split_single_append {α : Type} (l l' : List α) (x : α) :
    [x] = l ++ l' → (l = [x] ∧ l' = []) ∨ (l = [] ∧ l' = [x]) := by
  intro h
  cases l with
  | nil => right; simpa using h.symm
  | cons y ys =>
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hxy, hnil⟩ := h
    obtain ⟨hys, hl'⟩ := List.append_eq_nil_iff.mp hnil.symm
    left
    exact ⟨by rw [hys, ← hxy], hl'⟩

-- `instrs_single_typing_inversion` (Rocq `typing_lemmas.v:822`) is defined further below,
-- right after `instrs_seq_typing_inversion`, since its proof needs `instrs_ok_nil_sub`/
-- `instr_subtyping_weaken2`/`_strengthen2`, all defined later in this file (see
-- `instrs_single_typing_inversion_gen`).

-- `ais_single_typing_inversion'` (Rocq `typing_lemmas.v:884`) and
-- `ais_single_typing_inversion` (`typing_lemmas.v:946`) are defined further below, right
-- after `ais_composition_typing`, since their proofs need `ais_ok_nil_sub`/
-- `instr_subtyping_weaken2`/`_strengthen2`/`ai_typing_inversion` in scope — same reordering
-- reason as `instrs_single_typing_inversion` above.

-- `ais_single_ref_typing_inversion` (Rocq `typing_lemmas.v:961`) and
-- `ais_single_val_typing_inversion` (`typing_lemmas.v:982`) are defined further below,
-- right after `ais_single_typing_inversion`, which their proofs need in scope.

/-- Rocq `typing_lemmas.v:978` `val_ref_null_is_ref`. Definitional: `val_ref`
    (`wasm2.0.lean:11261`) maps `ref.REF_NULL x0 ↦ val.REF_NULL x0` directly. -/
theorem val_ref_null_is_ref (rt : reftype) : val.REF_NULL rt = val_ref (ref.REF_NULL rt) := rfl

/-! ### Sequence-typing inversion machinery (ported from a prior Lean session's
    `spectec/test-lean/test-lean-claude/SeqTypingInversion.lean`, which independently
    discovered — and fixed — a false-lemma bug: an earlier attempt stated the analogous fact
    with singular `Instr_ok` on the head, which is FALSE (see
    `claude-logging/for-claude/digest_prior_lean_attempts.md` §3). The sequence-level
    conclusion below (`Instrs_ok`/`Instrs_ok2` on both pieces, not singular `Instr_ok`/
    `Instr_ok2` on the head) is the Rocq-faithful, actually-true shape. The `_gen`/`_nil_*`/
    `_widen_*` lemmas here have no direct named Rocq counterpart (they're this proof's own
    induction scaffolding — Rocq's tactic proof of the same fact doesn't need named
    sub-lemmas), kept `private`-in-spirit (not exported as project API) but not marked
    `private`; no other file uses them. -/

theorem instrs_ok_nil_sub_gen {C : context} {instr_lst : List instr} {ft : functype}
    (h : Instrs_ok C instr_lst ft) :
    instr_lst = [] → ∀ t1 t2, ft = mkFunctype t1 t2 → ResulttypeSub t1 t2 := by
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True) with
  | empty C' _ =>
    intro _ t1 t2 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    rw [← e1, ← e2]
    exact resulttype_sub_refl []
  | instr C' v_instr t1' t2' _ _ _ => intro heq _ _ _; cases heq
  | seq C' i1 i2 s1 s3 s2 h1 h2 _ _ _ ih1 ih2 =>
    intro heq t1 t2 hft
    have h12 : i1 = [] ∧ i2 = [] := List.append_eq_nil_iff.mp heq
    obtain ⟨e1, e2⟩ := h12
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e3, e4⟩ := hft
    have hs12 : ResulttypeSub s1 s2 := ih1 e1 s1 s2 rfl
    have hs23 : ResulttypeSub s2 s3 := ih2 e2 s2 s3 rfl
    rw [← e3, ← e4]
    exact resulttype_sub_trans s1 s2 s3 hs12 hs23
  | sub C' i t1'' t2'' t1''' t2''' hok hsub1 hsub2 _ _ ih =>
    intro heq t1 t2 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    have hmid := ih heq t1''' t2''' rfl
    rw [← e1, ← e2]
    exact resulttype_sub_trans t1'' t2''' t2'' (resulttype_sub_trans t1'' t1''' t2''' hsub1 hmid) hsub2
  | frame C' i tpre t1'''' t2'''' hok _ _ ih =>
    intro heq t1 t2 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    have hmid := ih heq t1'''' t2'''' rfl
    rw [← e1, ← e2]
    exact resulttype_sub_app tpre t1'''' tpre t2'''' (resulttype_sub_refl tpre) hmid
  | _ => intros; trivial

theorem instrs_ok_nil_sub {C : context} {t1 t2 : List valtype}
    (h : Instrs_ok C [] (mkFunctype t1 t2)) : ResulttypeSub t1 t2 :=
  instrs_ok_nil_sub_gen h rfl t1 t2 rfl

/-- `Instrs_ok C [] (t f-> t)` for any `t`: the empty sequence trivially "does nothing", via
    `frame` prepending `t` to `Instrs_ok.empty`'s `[] f-> []`. -/
theorem instrs_ok_nil_refl {C : context} (hC : wf_context C) (t : List valtype) :
    Instrs_ok C [] (mkFunctype t t) := by
  have h := Instrs_ok.frame C [] t [] [] (Instrs_ok.empty C hC) hC (by intro x hx; simp at hx)
  simpa [mkFunctype] using h

/-- Contravariant input-widening for a fixed `Instrs_ok` derivation: if `Instrs_ok C is (t
    f-> t2)` and `t1 subs< t`, then also `Instrs_ok C is (t1 f-> t2)`. Direct application of
    `Instrs_ok.sub` with a reflexive output-side witness. -/
theorem instrs_ok_widen_in {C : context} {is : List instr} {t t1 t2 : List valtype}
    (h : Instrs_ok C is (mkFunctype t t2)) (hsub : ResulttypeSub t1 t)
    (hC : wf_context C) (hwf : Forall (fun i => wf_instr i) is) :
    Instrs_ok C is (mkFunctype t1 t2) :=
  Instrs_ok.sub C is t1 t2 t t2 h hsub (resulttype_sub_refl t2) hC hwf

/-- Covariant output-widening: dual of `instrs_ok_widen_in`. -/
theorem instrs_ok_widen_out {C : context} {is : List instr} {t t1 t2 : List valtype}
    (h : Instrs_ok C is (mkFunctype t1 t)) (hsub : ResulttypeSub t t2)
    (hC : wf_context C) (hwf : Forall (fun i => wf_instr i) is) :
    Instrs_ok C is (mkFunctype t1 t2) :=
  Instrs_ok.sub C is t1 t2 t1 t h (resulttype_sub_refl t1) hsub hC hwf

theorem instrs_ok_cons_gen {C : context} {instr_lst : List instr} {ft : functype}
    (h : Instrs_ok C instr_lst ft) :
    ∀ (i : instr) (is : List instr), instr_lst = i :: is →
    ∀ (ts1 ts3 : List valtype), ft = mkFunctype ts1 ts3 →
    ∃ ts2, Instrs_ok C [i] (mkFunctype ts1 ts2) ∧ Instrs_ok C is (mkFunctype ts2 ts3) := by
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True) with
  | empty C' _ => intro i is heq; simp at heq
  | instr C' v_instr t1' t2' hok hwf_c hwf_i =>
    intro i is heq ts1 ts3 hft
    simp only [List.cons.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e3, e4⟩ := hft
    subst e1; subst e2; subst e3; subst e4
    refine ⟨t2', ?_, ?_⟩
    · exact Instrs_ok.instr C' v_instr t1' t2' hok hwf_c hwf_i
    · exact instrs_ok_nil_refl hwf_c t2'
  | seq C' i1 i2 s1 s3 s2 h1 h2 hwf_c hwf_i1 hwf_i2 ih1 ih2 =>
    intro i is heq ts1 ts3 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e3, e4⟩ := hft
    subst e3; subst e4
    cases i1 with
    | nil =>
      simp only [List.nil_append] at heq
      subst heq
      have hsub1 : ResulttypeSub s1 s2 := instrs_ok_nil_sub h1
      obtain ⟨ts2', hpart1, hpart2⟩ := ih2 i is rfl s2 s3 rfl
      have hwf_i' : Forall (fun j => wf_instr j) [i] := by
        intro x hx; simp at hx; rw [hx]; exact hwf_i2 i (by simp)
      refine ⟨ts2', instrs_ok_widen_in hpart1 hsub1 hwf_c hwf_i', hpart2⟩
    | cons hd tl =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨e1, e2⟩ := heq
      subst e1
      obtain ⟨ts2', hpart1, hpart2⟩ := ih1 hd tl rfl s1 s2 rfl
      refine ⟨ts2', hpart1, ?_⟩
      have hwf_tl : Forall (fun i => wf_instr i) tl := by
        intro x hx; exact hwf_i1 x (by simp [hx])
      rw [← e2]
      exact Instrs_ok.seq C' tl i2 ts2' s3 s2 hpart2 h2 hwf_c hwf_tl hwf_i2
  | sub C' i' t1'' t2'' t1''' t2''' hok hsub1 hsub2 hwf_c hwf_i ih =>
    intro i is heq ts1 ts3 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    obtain ⟨ts2', hpart1, hpart2⟩ := ih i is heq t1''' t2''' rfl
    have hwf_i' : Forall (fun j => wf_instr j) [i] := by
      intro x hx; simp at hx; rw [hx]
      exact hwf_i i (by rw [heq]; simp)
    have hwf_is : Forall (fun j => wf_instr j) is := by
      intro x hx; exact hwf_i x (by rw [heq]; simp [hx])
    refine ⟨ts2', ?_, ?_⟩
    · exact instrs_ok_widen_in hpart1 hsub1 hwf_c hwf_i'
    · exact instrs_ok_widen_out hpart2 hsub2 hwf_c hwf_is
  | frame C' i' tpre t1'''' t2'''' hok hwf_c hwf_i ih =>
    intro i is heq ts1 ts3 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    obtain ⟨ts2', hpart1, hpart2⟩ := ih i is heq t1'''' t2'''' rfl
    have hwf_i' : Forall (fun j => wf_instr j) [i] := by
      intro x hx; simp at hx; rw [hx]
      exact hwf_i i (by rw [heq]; simp)
    have hwf_is : Forall (fun j => wf_instr j) is := by
      intro x hx; exact hwf_i x (by rw [heq]; simp [hx])
    refine ⟨tpre ++ ts2', ?_, ?_⟩
    · rw [← e1]; exact Instrs_ok.frame C' [i] tpre t1'''' ts2' hpart1 hwf_c hwf_i'
    · rw [← e2]; exact Instrs_ok.frame C' is tpre ts2' t2'''' hpart2 hwf_c hwf_is
  | _ => intros; trivial

/-- Rocq `typing_lemmas.v:1015` `instrs_seq_typing_inversion`. **IMPORTANT**: this is the
    Rocq-faithful sequence-level statement (`Instrs_ok`, not singular `Instr_ok`, on the
    head) — a previous session's `typing_lemmas.lean` mis-stated the analogous lemma with
    singular `Instr_ok` on the head and it was proved FALSE (see
    `claude-logging/for-claude/digest_prior_lean_attempts.md` §3). Use exactly this shape.
    Proof ported from a prior Lean session's `SeqTypingInversion.lean`
    (`instrs_seq_typing_inversion_fixed`), adapted to this file's `[v_instr] ++ v_instrs`
    phrasing (defeq to `v_instr :: v_instrs`) and this file's conjunct order. -/
theorem instrs_seq_typing_inversion (v_C : context) (v_instrs : List instr) (v_instr : instr) (t1s t2s : List valtype) :
    Instrs_ok v_C ([v_instr] ++ v_instrs) (mkFunctype t1s t2s) →
    ∃ t3s, Instrs_ok v_C v_instrs (mkFunctype t3s t2s) ∧ Instrs_ok v_C [v_instr] (mkFunctype t1s t3s) := by
  intro h
  obtain ⟨t3s, hpart1, hpart2⟩ := instrs_ok_cons_gen h v_instr v_instrs rfl t1s t2s rfl
  exact ⟨t3s, hpart2, hpart1⟩

/-- Generalized induction scaffold for `instrs_single_typing_inversion` (no direct Rocq
    counterpart — Rocq's `dependent induction` doesn't need a named `_gen` helper; this
    project's `Instrs_ok.rec` needs the singleton-list equation and the functype equation
    both generalized before induction, same pattern as `instrs_ok_nil_sub_gen`/
    `instrs_ok_cons_gen` above). -/
theorem instrs_single_typing_inversion_gen {C : context} {instr_lst : List instr} {ft : functype}
    (h : Instrs_ok C instr_lst ft) :
    ∀ v_instr, instr_lst = [v_instr] → ∀ t1s t2s, ft = mkFunctype t1s t2s →
      ∃ t1s_sup t2s_sub, Instr_ok C v_instr (mkFunctype t1s_sup t2s_sub) ∧
        instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) := by
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True) with
  | empty C' _ => intro v_instr heq; simp at heq
  | instr C' vi t1' t2' hok hwf_c hwf_i =>
    intro v_instr heq t1s t2s hft
    simp only [List.cons.injEq, and_true] at heq
    subst heq
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    exact ⟨t1', t2', hok, instrtype_sub_refl _⟩
  | seq C' i1 i2 s1 s3 s2 h1 h2 hwf_c hwf_i1 hwf_i2 ih1 ih2 =>
    intro v_instr heq t1s t2s hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    rcases split_single_append i1 i2 v_instr heq.symm with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · subst he1; subst he2
      have hsub : ResulttypeSub s2 s3 := instrs_ok_nil_sub h2
      obtain ⟨t1s_sup, t2s_sub, hok, hisub⟩ := ih1 v_instr rfl s1 s2 rfl
      exact ⟨t1s_sup, t2s_sub, hok, instr_subtyping_weaken2 t1s_sup t2s_sub s1 s2 s3 hisub hsub⟩
    · subst he1; subst he2
      have hsub : ResulttypeSub s1 s2 := instrs_ok_nil_sub h1
      obtain ⟨t1s_sup, t2s_sub, hok, hisub⟩ := ih2 v_instr rfl s2 s3 rfl
      exact ⟨t1s_sup, t2s_sub, hok, instr_subtyping_strengthen2 t1s_sup t2s_sub s2 s3 s1 hisub hsub⟩
  | sub C' i t1'' t2'' t1''' t2''' hok hsub1 hsub2 hwf_c hwf_i ih =>
    intro v_instr heq t1s t2s hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    obtain ⟨t1s_sup, t2s_sub, hok', hisub⟩ := ih v_instr heq t1''' t2''' rfl
    refine ⟨t1s_sup, t2s_sub, hok', instrtype_sub_trans _ _ _ hisub ?_⟩
    exact ⟨[], [], t1'', t2'', rfl, rfl, resulttype_sub_refl [], hsub1, hsub2⟩
  | frame C' i tpre t1'''' t2'''' hok hwf_c hwf_i ih =>
    intro v_instr heq t1s t2s hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    obtain ⟨t1s_sup, t2s_sub, hok', hisub⟩ := ih v_instr heq t1'''' t2'''' rfl
    refine ⟨t1s_sup, t2s_sub, hok', instrtype_sub_trans _ _ _ hisub ?_⟩
    rw [← e1, ← e2]
    exact ⟨tpre, tpre, t1'''', t2'''', rfl, rfl, resulttype_sub_refl tpre,
      resulttype_sub_refl t1'''', resulttype_sub_refl t2''''⟩
  | _ => intros; trivial

/-- Rocq `typing_lemmas.v:822` `instrs_single_typing_inversion`. -/
theorem instrs_single_typing_inversion (v_C : context) (v_instr : instr) (t1s t2s : List valtype) :
    Instrs_ok v_C [v_instr] (mkFunctype t1s t2s) →
    ∃ t1s_sup t2s_sub, Instr_ok v_C v_instr (mkFunctype t1s_sup t2s_sub) ∧
      instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) :=
  fun h => instrs_single_typing_inversion_gen h v_instr rfl t1s t2s rfl

/-! ### Administrative analogue: same proof shape, `Instrs_ok2`/`Instr_ok2`/`wf_admininstr`/
    `wf_store` throughout in place of `Instrs_ok`/`Instr_ok`/`wf_instr`. -/

theorem ais_ok_nil_sub_gen {v_S : store} {C : context} {ai_lst : List admininstr} {ft : functype}
    (h : Instrs_ok2 v_S C ai_lst ft) :
    ai_lst = [] → ∀ t1 t2, ft = mkFunctype t1 t2 → ResulttypeSub t1 t2 := by
  induction h using Instrs_ok2.rec
    (motive_1 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True) with
  | empty C' _ _ =>
    intro _ t1 t2 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    rw [← e1, ← e2]
    exact resulttype_sub_refl []
  | instr C' v_ai t1' t2' _ _ _ _ => intro heq _ _ _; cases heq
  | seq C' i1 i2 s1 s3 s2 h1 h2 _ _ _ _ ih1 ih2 =>
    intro heq t1 t2 hft
    have h12 : i1 = [] ∧ i2 = [] := List.append_eq_nil_iff.mp heq
    obtain ⟨e1, e2⟩ := h12
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e3, e4⟩ := hft
    have hs12 : ResulttypeSub s1 s2 := ih1 e1 s1 s2 rfl
    have hs23 : ResulttypeSub s2 s3 := ih2 e2 s2 s3 rfl
    rw [← e3, ← e4]
    exact resulttype_sub_trans s1 s2 s3 hs12 hs23
  | sub C' i t1'' t2'' t1''' t2''' hok hsub1 hsub2 _ _ _ ih =>
    intro heq t1 t2 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    have hmid := ih heq t1''' t2''' rfl
    rw [← e1, ← e2]
    exact resulttype_sub_trans t1'' t2''' t2'' (resulttype_sub_trans t1'' t1''' t2''' hsub1 hmid) hsub2
  | Instrs_ok2_frame C' i tpre t1'''' t2'''' hok _ _ _ ih =>
    intro heq t1 t2 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    have hmid := ih heq t1'''' t2'''' rfl
    rw [← e1, ← e2]
    exact resulttype_sub_app tpre t1'''' tpre t2'''' (resulttype_sub_refl tpre) hmid
  | _ => intros; trivial

theorem ais_ok_nil_sub {v_S : store} {C : context} {t1 t2 : List valtype}
    (h : Instrs_ok2 v_S C [] (mkFunctype t1 t2)) : ResulttypeSub t1 t2 :=
  ais_ok_nil_sub_gen h rfl t1 t2 rfl

theorem ais_ok_nil_refl {v_S : store} {C : context} (hS : wf_store v_S) (hC : wf_context C) (t : List valtype) :
    Instrs_ok2 v_S C [] (mkFunctype t t) := by
  have h := Instrs_ok2.Instrs_ok2_frame v_S C [] t [] [] (Instrs_ok2.empty v_S C hS hC) hS hC
    (by intro x hx; simp at hx)
  simpa [mkFunctype] using h

theorem ais_ok_widen_in {v_S : store} {C : context} {ais : List admininstr} {t t1 t2 : List valtype}
    (h : Instrs_ok2 v_S C ais (mkFunctype t t2)) (hsub : ResulttypeSub t1 t)
    (hS : wf_store v_S) (hC : wf_context C) (hwf : Forall (fun a => wf_admininstr a) ais) :
    Instrs_ok2 v_S C ais (mkFunctype t1 t2) :=
  Instrs_ok2.sub v_S C ais t1 t2 t t2 h hsub (resulttype_sub_refl t2) hS hC hwf

theorem ais_ok_widen_out {v_S : store} {C : context} {ais : List admininstr} {t t1 t2 : List valtype}
    (h : Instrs_ok2 v_S C ais (mkFunctype t1 t)) (hsub : ResulttypeSub t t2)
    (hS : wf_store v_S) (hC : wf_context C) (hwf : Forall (fun a => wf_admininstr a) ais) :
    Instrs_ok2 v_S C ais (mkFunctype t1 t2) :=
  Instrs_ok2.sub v_S C ais t1 t2 t1 t h (resulttype_sub_refl t1) hsub hS hC hwf

/-- Rocq `typing_lemmas.v:299` `instrs_empty_typing`. ⇒: `instrs_ok_context_wf` +
    `instrs_ok_nil_sub`. ⇐: `instrs_ok_nil_refl` (reflexive `t2s f-> t2s`) widened on the
    input side via `instrs_ok_widen_in` — mirrors Rocq's own `frame`-then-`sub` proof. -/
theorem instrs_empty_typing (v_C : context) (t1s t2s : List valtype) :
    Instrs_ok v_C [] (mkFunctype t1s t2s) ↔ (wf_context v_C ∧ ResulttypeSub t1s t2s) := by
  constructor
  · intro h
    exact ⟨(instrs_ok_context_wf v_C [] (mkFunctype t1s t2s) h).1, instrs_ok_nil_sub h⟩
  · rintro ⟨hwf, hsub⟩
    exact instrs_ok_widen_in (instrs_ok_nil_refl hwf t2s) hsub hwf (by intro x hx; simp at hx)

/-- Rocq `typing_lemmas.v:333` `ais_empty_typing`. Administrative counterpart of
    `instrs_empty_typing` above, same proof shape via the `Instrs_ok2` nil/widen lemmas. -/
theorem ais_empty_typing (v_S : store) (v_C : context) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [] (mkFunctype t1s t2s) ↔ (wf_context v_C ∧ wf_store v_S ∧ ResulttypeSub t1s t2s) := by
  constructor
  · intro h
    obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C [] (mkFunctype t1s t2s) h
    exact ⟨hwfC, hwfS, ais_ok_nil_sub h⟩
  · rintro ⟨hwfC, hwfS, hsub⟩
    exact ais_ok_widen_in (ais_ok_nil_refl hwfS hwfC t2s) hsub hwfS hwfC (by intro x hx; simp at hx)

theorem ais_ok_cons_gen {v_S : store} {C : context} {ai_lst : List admininstr} {ft : functype}
    (h : Instrs_ok2 v_S C ai_lst ft) :
    ∀ (a : admininstr) (ais : List admininstr), ai_lst = a :: ais →
    ∀ (ts1 ts3 : List valtype), ft = mkFunctype ts1 ts3 →
    ∃ ts2, Instrs_ok2 v_S C [a] (mkFunctype ts1 ts2) ∧ Instrs_ok2 v_S C ais (mkFunctype ts2 ts3) := by
  induction h using Instrs_ok2.rec
    (motive_1 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True) with
  | empty C' _ _ => intro a ais heq; simp at heq
  | instr C' v_ai t1' t2' hok hs hwf_c hwf_i =>
    intro a ais heq ts1 ts3 hft
    simp only [List.cons.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e3, e4⟩ := hft
    subst e1; subst e2; subst e3; subst e4
    refine ⟨t2', ?_, ?_⟩
    · exact Instrs_ok2.instr v_S C' v_ai t1' t2' hok hs hwf_c hwf_i
    · exact ais_ok_nil_refl hs hwf_c t2'
  | seq C' i1 i2 s1 s3 s2 h1 h2 hs hwf_c hwf_i1 hwf_i2 ih1 ih2 =>
    intro a ais heq ts1 ts3 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e3, e4⟩ := hft
    subst e3; subst e4
    cases i1 with
    | nil =>
      simp only [List.nil_append] at heq
      subst heq
      have hsub1 : ResulttypeSub s1 s2 := ais_ok_nil_sub h1
      obtain ⟨ts2', hpart1, hpart2⟩ := ih2 a ais rfl s2 s3 rfl
      have hwf_a' : Forall (fun j => wf_admininstr j) [a] := by
        intro x hx; simp at hx; rw [hx]; exact hwf_i2 a (by simp)
      refine ⟨ts2', ais_ok_widen_in hpart1 hsub1 hs hwf_c hwf_a', hpart2⟩
    | cons hd tl =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨e1, e2⟩ := heq
      subst e1
      obtain ⟨ts2', hpart1, hpart2⟩ := ih1 hd tl rfl s1 s2 rfl
      refine ⟨ts2', hpart1, ?_⟩
      have hwf_tl : Forall (fun a => wf_admininstr a) tl := by
        intro x hx; exact hwf_i1 x (by simp [hx])
      rw [← e2]
      exact Instrs_ok2.seq v_S C' tl i2 ts2' s3 s2 hpart2 h2 hs hwf_c hwf_tl hwf_i2
  | sub C' i' t1'' t2'' t1''' t2''' hok hsub1 hsub2 hs hwf_c hwf_i ih =>
    intro a ais heq ts1 ts3 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    obtain ⟨ts2', hpart1, hpart2⟩ := ih a ais heq t1''' t2''' rfl
    have hwf_a' : Forall (fun j => wf_admininstr j) [a] := by
      intro x hx; simp at hx; rw [hx]
      exact hwf_i a (by rw [heq]; simp)
    have hwf_ais : Forall (fun j => wf_admininstr j) ais := by
      intro x hx; exact hwf_i x (by rw [heq]; simp [hx])
    refine ⟨ts2', ?_, ?_⟩
    · exact ais_ok_widen_in hpart1 hsub1 hs hwf_c hwf_a'
    · exact ais_ok_widen_out hpart2 hsub2 hs hwf_c hwf_ais
  | Instrs_ok2_frame C' i' tpre t1'''' t2'''' hok hs hwf_c hwf_i ih =>
    intro a ais heq ts1 ts3 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    obtain ⟨ts2', hpart1, hpart2⟩ := ih a ais heq t1'''' t2'''' rfl
    have hwf_a' : Forall (fun j => wf_admininstr j) [a] := by
      intro x hx; simp at hx; rw [hx]
      exact hwf_i a (by rw [heq]; simp)
    have hwf_ais : Forall (fun j => wf_admininstr j) ais := by
      intro x hx; exact hwf_i x (by rw [heq]; simp [hx])
    refine ⟨tpre ++ ts2', ?_, ?_⟩
    · rw [← e1]; exact Instrs_ok2.Instrs_ok2_frame v_S C' [a] tpre t1'''' ts2' hpart1 hs hwf_c hwf_a'
    · rw [← e2]; exact Instrs_ok2.Instrs_ok2_frame v_S C' ais tpre ts2' t2'''' hpart2 hs hwf_c hwf_ais
  | _ => intros; trivial

/-- Rocq `typing_lemmas.v:1080` `ais_seq_typing_inversion`. Administrative analog of
    `instrs_seq_typing_inversion`; proof ported the same way from a prior Lean session's
    `SeqTypingInversion.lean` (`instrs_seq_typing_inversion_fixed`), re-derived here for the
    `Instrs_ok2`/store-threaded setting (see `ais_ok_cons_gen` above). -/
theorem ais_seq_typing_inversion (v_S : store) (v_C : context) (v_ais : List admininstr) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C ([v_ai] ++ v_ais) (mkFunctype t1s t2s) →
    ∃ t3s, Instrs_ok2 v_S v_C v_ais (mkFunctype t3s t2s) ∧ Instrs_ok2 v_S v_C [v_ai] (mkFunctype t1s t3s) := by
  intro h
  obtain ⟨t3s, hpart1, hpart2⟩ := ais_ok_cons_gen h v_ai v_ais rfl t1s t2s rfl
  exact ⟨t3s, hpart2, hpart1⟩

/-- Rocq `typing_lemmas.v:1143` `ais_composition_typing`. Generalizes `ais_seq_typing_inversion`
    from a single head admininstr to an arbitrary prefix `v_ais1`, by induction on `v_ais1`
    reusing `ais_seq_typing_inversion` at each step. -/
theorem ais_composition_typing (v_S : store) (v_C : context) (v_ais1 v_ais2 : List admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C (v_ais1 ++ v_ais2) (mkFunctype t1s t2s) →
    ∃ t3s, Instrs_ok2 v_S v_C v_ais1 (mkFunctype t1s t3s) ∧ Instrs_ok2 v_S v_C v_ais2 (mkFunctype t3s t2s) := by
  induction v_ais1 generalizing t1s with
  | nil =>
    intro h
    simp only [List.nil_append] at h
    exact ⟨t1s, ais_ok_nil_refl (ainstrs_ok_context_store_wf v_S v_C v_ais2 (mkFunctype t1s t2s) h).2.1
      (ainstrs_ok_context_store_wf v_S v_C v_ais2 (mkFunctype t1s t2s) h).1 t1s, h⟩
  | cons a as ih =>
    intro h
    simp only [List.cons_append] at h
    obtain ⟨tmid, hrest_typing, ha_typing⟩ := ais_seq_typing_inversion v_S v_C (as ++ v_ais2) a t1s t2s h
    obtain ⟨t3s, has_typing, hv_ais2_typing⟩ := ih tmid hrest_typing
    have hwf_a_all := ainstrs_ok_context_store_wf v_S v_C [a] (mkFunctype t1s tmid) ha_typing
    have hwf_as_all := ainstrs_ok_context_store_wf v_S v_C as (mkFunctype tmid t3s) has_typing
    refine ⟨t3s, ?_, hv_ais2_typing⟩
    have heq2 : [a] ++ as = a :: as := rfl
    rw [← heq2]
    exact Instrs_ok2.seq v_S v_C [a] as t1s t3s tmid ha_typing has_typing
      hwf_as_all.2.1 hwf_as_all.1 hwf_a_all.2.2 hwf_as_all.2.2

/-- Administrative analogue of `instrs_single_typing_inversion_gen` — same proof shape,
    `Instrs_ok2`/`Instr_ok2`/`wf_store` throughout, and the `Instr_ok2`/`Expr_ok2` motives
    trivialized (same 3-way-mutual-inductive pattern as `ais_ok_cons_gen` above). -/
theorem ais_single_typing_inversion'_gen {v_S : store} {C : context} {ai_lst : List admininstr} {ft : functype}
    (h : Instrs_ok2 v_S C ai_lst ft) :
    ∀ v_ai, ai_lst = [v_ai] → ∀ t1s t2s, ft = mkFunctype t1s t2s →
      ∃ t1s_sup t2s_sub, Instr_ok2 v_S C v_ai (mkFunctype t1s_sup t2s_sub) ∧
        instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) := by
  induction h using Instrs_ok2.rec
    (motive_1 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True) with
  | empty C' _ _ => intro v_ai heq; simp at heq
  | instr C' vai t1' t2' hok hs hwf_c hwf_i =>
    intro v_ai heq t1s t2s hft
    simp only [List.cons.injEq, and_true] at heq
    subst heq
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    exact ⟨t1', t2', hok, instrtype_sub_refl _⟩
  | seq C' i1 i2 s1 s3 s2 h1 h2 hs hwf_c hwf_i1 hwf_i2 ih1 ih2 =>
    intro v_ai heq t1s t2s hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    rcases split_single_append i1 i2 v_ai heq.symm with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · subst he1; subst he2
      have hsub : ResulttypeSub s2 s3 := ais_ok_nil_sub h2
      obtain ⟨t1s_sup, t2s_sub, hok, hisub⟩ := ih1 v_ai rfl s1 s2 rfl
      exact ⟨t1s_sup, t2s_sub, hok, instr_subtyping_weaken2 t1s_sup t2s_sub s1 s2 s3 hisub hsub⟩
    · subst he1; subst he2
      have hsub : ResulttypeSub s1 s2 := ais_ok_nil_sub h1
      obtain ⟨t1s_sup, t2s_sub, hok, hisub⟩ := ih2 v_ai rfl s2 s3 rfl
      exact ⟨t1s_sup, t2s_sub, hok, instr_subtyping_strengthen2 t1s_sup t2s_sub s2 s3 s1 hisub hsub⟩
  | sub C' i t1'' t2'' t1''' t2''' hok hsub1 hsub2 hs hwf_c hwf_i ih =>
    intro v_ai heq t1s t2s hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    subst e1; subst e2
    obtain ⟨t1s_sup, t2s_sub, hok', hisub⟩ := ih v_ai heq t1''' t2''' rfl
    refine ⟨t1s_sup, t2s_sub, hok', instrtype_sub_trans _ _ _ hisub ?_⟩
    exact ⟨[], [], t1'', t2'', rfl, rfl, resulttype_sub_refl [], hsub1, hsub2⟩
  | Instrs_ok2_frame C' i tpre t1'''' t2'''' hok hs hwf_c hwf_i ih =>
    intro v_ai heq t1s t2s hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    obtain ⟨t1s_sup, t2s_sub, hok', hisub⟩ := ih v_ai heq t1'''' t2'''' rfl
    refine ⟨t1s_sup, t2s_sub, hok', instrtype_sub_trans _ _ _ hisub ?_⟩
    rw [← e1, ← e2]
    exact ⟨tpre, tpre, t1'''', t2'''', rfl, rfl, resulttype_sub_refl tpre,
      resulttype_sub_refl t1'''', resulttype_sub_refl t2''''⟩
  | _ => trivial

/-- Rocq `typing_lemmas.v:884` `ais_single_typing_inversion'`. -/
theorem ais_single_typing_inversion' (v_S : store) (v_C : context) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [v_ai] (mkFunctype t1s t2s) →
    ∃ t1s_sup t2s_sub, Instr_ok2 v_S v_C v_ai (mkFunctype t1s_sup t2s_sub) ∧
      instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) :=
  fun h => ais_single_typing_inversion'_gen h v_ai rfl t1s t2s rfl

/-- Rocq `typing_lemmas.v:946` `ais_single_typing_inversion`. **The single most-used lemma
    downstream** in `type_preservation_pure.v` — turns "list-of-one administrative
    instruction is typed" directly into "its principal typing, up to subtyping". Chains
    `ais_single_typing_inversion'` with `ai_typing_inversion`, composing the two
    `instrtype_sub` facts via `instrtype_sub_trans` — mirrors Rocq exactly. -/
theorem ais_single_typing_inversion (v_S : store) (v_C : context) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [v_ai] (mkFunctype t1s t2s) →
    ∃ t1s_sup t2s_sub, ai_principal_typing v_S v_C v_ai (mkFunctype t1s_sup t2s_sub) ∧
      instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t1s_sup, t2s_sub, hok, hsub⟩ := ais_single_typing_inversion' v_S v_C v_ai t1s t2s h
  obtain ⟨t1s', t2s', hprincipal, hsub'⟩ := ai_typing_inversion v_S v_C v_ai t1s_sup t2s_sub hok
  exact ⟨t1s', t2s', hprincipal, instrtype_sub_trans _ _ _ hsub' hsub⟩

/-- Rocq `typing_lemmas.v:961` `ais_single_ref_typing_inversion`. -/
theorem ais_single_ref_typing_inversion (v_S : store) (v_C : context) (v_ref : ref) (ts1 ts2 : List valtype) :
    Instrs_ok2 v_S v_C [admininstr_ref v_ref] (mkFunctype ts1 ts2) →
    ∃ t : reftype, instrtype_sub (mkFunctype [] [valtype_reftype t]) (mkFunctype ts1 ts2) ∧ Ref_ok v_S v_ref t := by
  intro h
  obtain ⟨t1s_sup, t2s_sub, hai, hsub⟩ := ais_single_typing_inversion v_S v_C (admininstr_ref v_ref) ts1 ts2 h
  obtain ⟨_, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C [admininstr_ref v_ref] (mkFunctype ts1 ts2) h
  cases v_ref with
  | REF_NULL rt =>
    unfold admininstr_ref ai_principal_typing at hai
    unfold mkFunctype at hai
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hai
    obtain ⟨e1, e2⟩ := hai
    subst e1; subst e2
    exact ⟨rt, hsub, Ref_ok.null v_S rt hwfS⟩
  | REF_FUNC_ADDR faddr =>
    unfold admininstr_ref ai_principal_typing at hai
    obtain ⟨ft, heq, hext⟩ := hai
    unfold mkFunctype at heq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    subst e1; subst e2
    have hwf_externtype : wf_externtype (externtype.FUNC ft) := by cases hext <;> assumption
    exact ⟨reftype.FUNCREF, hsub, Ref_ok.func v_S faddr ft hext hwfS hwf_externtype⟩
  | REF_HOST_ADDR haddr =>
    unfold admininstr_ref ai_principal_typing at hai
    unfold mkFunctype at hai
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hai
    obtain ⟨e1, e2⟩ := hai
    subst e1; subst e2
    exact ⟨reftype.EXTERNREF, hsub, Ref_ok.extern v_S haddr hwfS⟩

/-- Rocq `typing_lemmas.v:982` `ais_single_val_typing_inversion`. -/
theorem ais_single_val_typing_inversion (v_S : store) (v_C : context) (v_val : val) (ts1 ts2 : List valtype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val] (mkFunctype ts1 ts2) →
    ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype ts1 ts2) ∧ Val_ok v_S v_val t := by
  intro h
  obtain ⟨t1s_sup, t2s_sub, hai, hsub⟩ := ais_single_typing_inversion v_S v_C (admininstr_val v_val) ts1 ts2 h
  obtain ⟨_, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C [admininstr_val v_val] (mkFunctype ts1 ts2) h
  cases v_val with
  | CONST nt c =>
    unfold admininstr_val ai_principal_typing at hai
    obtain ⟨heq, hwn⟩ := hai
    unfold mkFunctype at heq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    subst e1; subst e2
    exact ⟨valtype_numtype nt, hsub, Val_ok.numtype v_S nt c hwfS (wf_val.val_case_0 nt c hwn)⟩
  | VCONST vt c =>
    unfold admininstr_val ai_principal_typing at hai
    obtain ⟨uN_size, hsize, hwu, heq⟩ := hai
    unfold mkFunctype at heq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    subst e1; subst e2
    have hne : size (valtype_vectype vt) ≠ none := by rw [hsize]; simp
    have hwu' : wf_uN (Option.get! (size (valtype_vectype vt))) c := by rw [hsize]; exact hwu
    exact ⟨valtype_vectype vt, hsub, Val_ok.vectype v_S vt c hwfS (wf_val.val_case_1 vt c hne hwu')⟩
  | REF_NULL rt =>
    unfold admininstr_val ai_principal_typing at hai
    unfold mkFunctype at hai
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hai
    obtain ⟨e1, e2⟩ := hai
    subst e1; subst e2
    refine ⟨valtype_reftype rt, hsub, ?_⟩
    rw [val_ref_null_is_ref]
    exact Val_ok.reftype v_S (ref.REF_NULL rt) rt (Ref_ok.null v_S rt hwfS) hwfS
  | REF_FUNC_ADDR faddr =>
    unfold admininstr_val ai_principal_typing at hai
    obtain ⟨ft, heq, hext⟩ := hai
    unfold mkFunctype at heq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    subst e1; subst e2
    have hwf_externtype : wf_externtype (externtype.FUNC ft) := by cases hext <;> assumption
    exact ⟨valtype_reftype reftype.FUNCREF, hsub,
      Val_ok.reftype v_S (ref.REF_FUNC_ADDR faddr) reftype.FUNCREF
        (Ref_ok.func v_S faddr ft hext hwfS hwf_externtype) hwfS⟩
  | REF_HOST_ADDR haddr =>
    unfold admininstr_val ai_principal_typing at hai
    unfold mkFunctype at hai
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hai
    obtain ⟨e1, e2⟩ := hai
    subst e1; subst e2
    exact ⟨valtype_reftype reftype.EXTERNREF, hsub,
      Val_ok.reftype v_S (ref.REF_HOST_ADDR haddr) reftype.EXTERNREF
        (Ref_ok.extern v_S haddr hwfS) hwfS⟩

/-! ## More inversion/construction lemmas (typing_lemmas.v:1294-1730) -/

/-- Rocq `typing_lemmas.v:1294` `ai_val_principal_typing_inversion`. Relies on
    `ai_principal_typing`'s own `REF_HOST_ADDR` case: the `spectec/test-lean/typing_lemmas.lean`
    version it was ported from lacked that case, so it fell through to the generic
    `| _ => True` catch-all (`ai_typing_inversion`'s `ref`/`REF_HOST_ADDR` case had relied on
    the same gap; both are fixed). -/
theorem ai_val_principal_typing_inversion (v_S : store) (v_C : context) (v_val : val) (t1s t2s : List valtype) :
    ai_principal_typing v_S v_C (admininstr_val v_val) (mkFunctype t1s t2s) →
    ∃ t_lst, [] = t1s ∧ [t_lst] = t2s := by
  intro h
  unfold ai_principal_typing at h
  cases v_val with
  | CONST nt c =>
    unfold admininstr_val at h
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at h
    exact ⟨valtype_numtype nt, h.1.1.symm, h.1.2.symm⟩
  | VCONST vt c =>
    unfold admininstr_val at h
    obtain ⟨_, _, _, heq⟩ := h
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at heq
    exact ⟨valtype_vectype vt, heq.1.symm, heq.2.symm⟩
  | REF_NULL rt =>
    unfold admininstr_val at h
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at h
    exact ⟨valtype_reftype rt, h.1.symm, h.2.symm⟩
  | REF_FUNC_ADDR a =>
    unfold admininstr_val at h
    obtain ⟨_, heq, _⟩ := h
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at heq
    exact ⟨valtype_reftype reftype.FUNCREF, heq.1.symm, heq.2.symm⟩
  | REF_HOST_ADDR a =>
    unfold admininstr_val at h
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at h
    exact ⟨valtype_reftype reftype.EXTERNREF, h.1.symm, h.2.symm⟩

set_option maxHeartbeats 1000000 in
/-- Rocq `typing_lemmas.v:1334` `injective_admininstr_instr`. Rocq: `destruct x1; destruct x2;
    try discriminate; auto` — same shape here (`admininstr_instr` maps each of `instr`'s 68
    constructors to the identically-shaped `admininstr` constructor of the same name; a
    same-constructor case reduces the goal to reflexivity, a mismatched pair is closed by
    `simp`'s built-in constructor-injectivity/no-confusion). 68×68 cases, mechanical.
    `maxHeartbeats` raised: importing `Mathlib.Tactic` (for `ai_principal_typing`'s port,
    see above) enlarges `simp_all`'s default simp-set enough that the 68×68 case bash no
    longer finishes in the default budget (it did, in ~26s, before Mathlib was imported). -/
theorem injective_admininstr_instr : Function.Injective admininstr_instr := by
  intro a b h
  cases a <;> cases b <;> simp_all [admininstr_instr]

/-- Rocq `typing_lemmas.v:1341` `construct_instrs_typing_single`. -/
theorem construct_instrs_typing_single (v_C : context) (v_ai : instr) (ts1 ts2 : List valtype) :
    Instr_ok v_C v_ai (mkFunctype ts1 ts2) → Instrs_ok v_C [v_ai] (mkFunctype ts1 ts2) := by
  intro h
  obtain ⟨hwf, hwfi⟩ := instr_ok_context_wf v_C v_ai (mkFunctype ts1 ts2) h
  exact Instrs_ok.instr v_C v_ai ts1 ts2 h hwf hwfi

/-- Rocq `typing_lemmas.v:1350` `construct_ais_typing_single`. -/
theorem construct_ais_typing_single (v_S : store) (v_C : context) (v_ai : admininstr) (ts1 ts2 : List valtype) :
    Instr_ok2 v_S v_C v_ai (mkFunctype ts1 ts2) → Instrs_ok2 v_S v_C [v_ai] (mkFunctype ts1 ts2) := by
  intro h
  obtain ⟨hwfC, hwfS, hwfa⟩ := ainstr_ok_context_store_wf v_S v_C v_ai (mkFunctype ts1 ts2) h
  exact Instrs_ok2.instr v_S v_C v_ai ts1 ts2 h hwfS hwfC hwfa

/-- Rocq `typing_lemmas.v:1359` `construct_ais_subtyping`. Rocq's proof: `frame`-extend the
    original derivation by the `instrtype_sub` witness's shared/subsumed prefix (`ts_sub`),
    then `sub` the two remaining pieces via `resulttype_sub_app` (one side reflexive on
    `ts_sub`, the other using the existential's own two `ResulttypeSub` facts directly). -/
theorem construct_ais_subtyping (v_S : store) (v_C : context) (v_ais : List admininstr) (ts1 ts2 ts1' ts2' : List valtype) :
    Instrs_ok2 v_S v_C v_ais (mkFunctype ts1 ts2) →
    instrtype_sub (mkFunctype ts1 ts2) (mkFunctype ts1' ts2') →
    Instrs_ok2 v_S v_C v_ais (mkFunctype ts1' ts2') := by
  intro hai hsub
  obtain ⟨ts_sub, ts, ts1_sub, ts2_sup, heq1, heq2, hsub_ts, hsub1, hsub2⟩ := hsub
  subst heq1
  subst heq2
  obtain ⟨hwfC, hwfS, hwfF⟩ := ainstrs_ok_context_store_wf v_S v_C v_ais (mkFunctype ts1 ts2) hai
  have hframe := Instrs_ok2.Instrs_ok2_frame v_S v_C v_ais ts_sub ts1 ts2 hai hwfS hwfC hwfF
  exact Instrs_ok2.sub v_S v_C v_ais (ts_sub ++ ts1_sub) (ts ++ ts2_sup) (ts_sub ++ ts1) (ts_sub ++ ts2)
    hframe
    (resulttype_sub_app ts_sub ts1_sub ts_sub ts1 (resulttype_sub_refl ts_sub) hsub1)
    (resulttype_sub_app ts_sub ts2 ts ts2_sup hsub_ts hsub2)
    hwfS hwfC hwfF

/-- Rocq `typing_lemmas.v:1382` `injective_valtype_numtype`. -/
theorem injective_valtype_numtype : Function.Injective valtype_numtype := by
  intro a b h
  cases a <;> cases b <;> simp_all [valtype_numtype]

/-- Rocq `typing_lemmas.v:1401` `construct_ais_compose`. Heavily reused in
    `type_preservation_pure.v` to glue partial typing derivations back together. -/
theorem construct_ais_compose (v_S : store) (v_C : context) (v_ais1 v_ais2 : List admininstr) (t1s t2s t3s : List valtype) :
    Instrs_ok2 v_S v_C v_ais1 (mkFunctype t1s t2s) → Instrs_ok2 v_S v_C v_ais2 (mkFunctype t2s t3s) →
    Instrs_ok2 v_S v_C (v_ais1 ++ v_ais2) (mkFunctype t1s t3s) := by
  intro h1 h2
  obtain ⟨hwfC1, hwfS1, hwfF1⟩ := ainstrs_ok_context_store_wf v_S v_C v_ais1 (mkFunctype t1s t2s) h1
  obtain ⟨hwfC2, hwfS2, hwfF2⟩ := ainstrs_ok_context_store_wf v_S v_C v_ais2 (mkFunctype t2s t3s) h2
  exact Instrs_ok2.seq v_S v_C v_ais1 v_ais2 t1s t3s t2s h1 h2 hwfS1 hwfC1 hwfF1 hwfF2

/-! ### Moving typing derivations between `instr` and `admininstr_instr`
    (typing_lemmas.v:1412-1586) -/

/-- Rocq `typing_lemmas.v:1412` `wf_admininstr_instr`. The `→` direction already exists
    here as `wf_instr_admininstr`; this is Rocq's `↔`. -/
theorem wf_admininstr_instr (i : instr) : wf_instr i ↔ wf_admininstr (admininstr_instr i) := by
  refine ⟨wf_instr_admininstr i, fun h => ?_⟩
  cases i <;> cases h <;> constructor <;> assumption

/-- Rocq `typing_lemmas.v:1428` `seq_mid_not_null`. -/
theorem seq_mid_not_null {A : Type} (a : A) (l l' : List A) : l ++ [a] ++ l' ≠ [] := by
  intro h
  simp at h

/-- Rocq `typing_lemmas.v:1436` `construct_instr_from_ai`. -/
theorem construct_instr_from_ai (v_S : store) (v_C : context) (v_instr : instr) (ts1 ts2 : List valtype) :
    wf_store v_S → Instrs_ok v_C [v_instr] (mkFunctype ts1 ts2) →
    Instrs_ok2 v_S v_C [admininstr_instr v_instr] (mkFunctype ts1 ts2) := by
  -- Rocq inducts on the `Instrs_ok` derivation; going through the principal (sub)typing of
  -- the single instruction instead avoids re-doing the seq/sub/frame bookkeeping.
  intro hS h
  obtain ⟨t1, t2, hok, hsub⟩ := instrs_single_typing_inversion v_C v_instr ts1 ts2 h
  obtain ⟨hC, hi⟩ := instr_ok_context_wf v_C v_instr _ hok
  exact construct_ais_subtyping v_S v_C [admininstr_instr v_instr] t1 t2 ts1 ts2
    (construct_ais_typing_single v_S v_C _ t1 t2 (Instr_ok2.plain v_S v_C v_instr t1 t2 hok hS hC hi)) hsub

/-- Rocq `typing_lemmas.v:1483` `construct_instr_from_ai_single`. -/
theorem construct_instr_from_ai_single (v_S : store) (v_C : context) (v_instr : instr) (ts1 ts2 : List valtype) :
    wf_store v_S → Instr_ok v_C v_instr (mkFunctype ts1 ts2) →
    Instr_ok2 v_S v_C (admininstr_instr v_instr) (mkFunctype ts1 ts2) := by
  intro hS h
  obtain ⟨hC, hi⟩ := instr_ok_context_wf v_C v_instr _ h
  exact Instr_ok2.plain v_S v_C v_instr ts1 ts2 h hS hC hi

/-- Rocq `typing_lemmas.v:1493` `construct_instrs_from_ais`. -/
theorem construct_instrs_from_ais (v_S : store) (v_C : context) (v_instrs : List instr) (ts1 ts2 : List valtype) :
    wf_store v_S → Instrs_ok v_C v_instrs (mkFunctype ts1 ts2) →
    Instrs_ok2 v_S v_C (v_instrs.map admininstr_instr) (mkFunctype ts1 ts2) := by
  intro hS
  induction v_instrs generalizing ts1 ts2 with
  | nil =>
    intro h
    obtain ⟨hC, hsub⟩ := (instrs_empty_typing v_C ts1 ts2).mp h
    exact (ais_empty_typing v_S v_C ts1 ts2).mpr ⟨hC, hS, hsub⟩
  | cons i is ih =>
    intro h
    obtain ⟨t3s, htail, hhead⟩ := instrs_seq_typing_inversion v_C is i ts1 ts2 (by simpa using h)
    have := construct_ais_compose v_S v_C [admininstr_instr i] (is.map admininstr_instr) ts1 t3s ts2
      (construct_instr_from_ai v_S v_C i ts1 t3s hS hhead) (ih t3s ts2 htail)
    simpa using this

/-- `Instrs_ok` counterpart of `construct_ais_subtyping` (Lean-only helper): frame
    by the shared prefix, then `sub` both sides. Rocq gets the same effect inside its
    `dependent induction` proofs of `revert_to_*`. -/
theorem construct_instrs_subtyping (v_C : context) (v_instrs : List instr) (ts1 ts2 ts1' ts2' : List valtype) :
    Instrs_ok v_C v_instrs (mkFunctype ts1 ts2) →
    instrtype_sub (mkFunctype ts1 ts2) (mkFunctype ts1' ts2') →
    Instrs_ok v_C v_instrs (mkFunctype ts1' ts2') := by
  intro hi hsub
  obtain ⟨ts_sub, ts, ts1_sub, ts2_sup, heq1, heq2, hsub_ts, hsub1, hsub2⟩ := hsub
  subst heq1
  subst heq2
  obtain ⟨hwfC, hwfF⟩ := instrs_ok_context_wf v_C v_instrs (mkFunctype ts1 ts2) hi
  have hframe := Instrs_ok.frame v_C v_instrs ts_sub ts1 ts2 hi hwfC hwfF
  exact Instrs_ok.sub v_C v_instrs (ts_sub ++ ts1_sub) (ts ++ ts2_sup) (ts_sub ++ ts1) (ts_sub ++ ts2)
    hframe
    (resulttype_sub_app ts_sub ts1_sub ts_sub ts1 (resulttype_sub_refl ts_sub) hsub1)
    (resulttype_sub_app ts_sub ts2 ts ts2_sup hsub_ts hsub2)
    hwfC hwfF

/-- Rocq `typing_lemmas.v:1513` `revert_to_instr_from_ai`. -/
theorem revert_to_instr_from_ai (v_S : store) (v_C : context) (v_instr : instr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [admininstr_instr v_instr] (mkFunctype t1s t2s) →
    Instrs_ok v_C [v_instr] (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t1, t2, hok2, hsub⟩ := ais_single_typing_inversion' v_S v_C (admininstr_instr v_instr) t1s t2s h
  exact construct_instrs_subtyping v_C [v_instr] t1 t2 t1s t2s
    (construct_instrs_typing_single v_C v_instr t1 t2 (ai_typing_inversion' v_S v_C v_instr t1 t2 hok2)) hsub

/-- Rocq `typing_lemmas.v:1559` `revert_to_instrs_from_ais`. -/
theorem revert_to_instrs_from_ais (v_S : store) (v_C : context) (v_instrs : List instr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C (v_instrs.map admininstr_instr) (mkFunctype t1s t2s) →
    Instrs_ok v_C v_instrs (mkFunctype t1s t2s) := by
  induction v_instrs generalizing t1s t2s with
  | nil =>
    intro h
    obtain ⟨hC, _, hsub⟩ := (ais_empty_typing v_S v_C t1s t2s).mp h
    exact (instrs_empty_typing v_C t1s t2s).mpr ⟨hC, hsub⟩
  | cons i is ih =>
    intro h
    obtain ⟨t3s, htail, hhead⟩ :=
      ais_seq_typing_inversion v_S v_C (is.map admininstr_instr) (admininstr_instr i) t1s t2s (by simpa using h)
    have h1 := revert_to_instr_from_ai v_S v_C i t1s t3s hhead
    have h2 := ih t3s t2s htail
    obtain ⟨hC, hf1⟩ := instrs_ok_context_wf v_C [i] _ h1
    obtain ⟨_, hf2⟩ := instrs_ok_context_wf v_C is _ h2
    exact Instrs_ok.seq v_C [i] is t1s t2s t3s h1 h2 hC hf1 hf2

/-- Rocq `typing_lemmas.v:1587` `construct_ai_const_I32`. -/
theorem construct_ai_const_I32 (v_S : store) (v_C : context) (v_num : num_) :
    wf_num_ numtype.I32 v_num → wf_context v_C → wf_store v_S →
    Instr_ok2 v_S v_C (admininstr.CONST numtype.I32 v_num) (mkFunctype [] [valtype.I32]) := by
  intro hwfnum hwfC hwfS
  have hwfinstr : wf_instr (instr.CONST numtype.I32 v_num) := wf_instr.instr_case_13 numtype.I32 v_num hwfnum
  exact Instr_ok2.plain v_S v_C (instr.CONST numtype.I32 v_num) [] [valtype.I32]
    (Instr_ok.const v_C numtype.I32 v_num hwfC hwfinstr) hwfS hwfC hwfinstr

/-- Rocq `typing_lemmas.v:1600` `construct_ai_ref`. Simpler than Rocq's own proof: unlike
    Rocq's mirrored `Instr_ok2__ref` constructor (which Rocq only invokes for the
    `FUNC_ADDR`/`HOST_ADDR` cases, routing `REF_NULL` through the "plain" `instr` path
    instead), this backend's `Instr_ok2.ref` constructor is generic over every `ref`
    constructor including `REF_NULL` (confirmed in `wasm2.0.lean`), so no case split on
    `Ref_ok` is needed at all. -/
theorem construct_ai_ref (v_S : store) (v_C : context) (v_ref : ref) (t : reftype) :
    Ref_ok v_S v_ref t → wf_context v_C → wf_store v_S →
    Instr_ok2 v_S v_C (admininstr_ref v_ref) (mkFunctype [] [valtype_reftype t]) := by
  intro href hwfC hwfS
  exact Instr_ok2.ref v_S v_C v_ref t href hwfS hwfC

/-- Rocq `typing_lemmas.v:1624` `adminval_val_ref`. -/
theorem adminval_val_ref (r : ref) : admininstr_val (val_ref r) = admininstr_ref r := by
  cases r <;> rfl

/-- Rocq `typing_lemmas.v:1631` `construct_ai_val`. `vectype`/`reftype` sub-cases use
    `cases vt`/`adminval_val_ref` respectively since `vectype` has a single constructor
    (`V128`) and the `reftype` case reduces to `construct_ai_ref` via the equation just
    proved above. -/
theorem construct_ai_val (v_S : store) (v_C : context) (v_val : val) (t : valtype) :
    Val_ok v_S v_val t → wf_context v_C → wf_store v_S →
    Instr_ok2 v_S v_C (admininstr_val v_val) (mkFunctype [] [t]) := by
  intro hval hwfC hwfS
  cases hval with
  | numtype nt c_t hs hwfval =>
    cases hwfval with
    | val_case_0 _ _ hwfnum =>
      have hwfinstr : wf_instr (instr.CONST nt c_t) := wf_instr.instr_case_13 nt c_t hwfnum
      exact Instr_ok2.plain v_S v_C (instr.CONST nt c_t) [] [valtype_numtype nt]
        (Instr_ok.const v_C nt c_t hwfC hwfinstr) hs hwfC hwfinstr
  | vectype vt c_t hs hwfval =>
    cases vt
    cases hwfval with
    | val_case_1 _ _ hsize hwfuN =>
      have hwfinstr : wf_instr (instr.VCONST vectype.V128 c_t) := wf_instr.instr_case_19 vectype.V128 c_t hsize hwfuN
      exact Instr_ok2.plain v_S v_C (instr.VCONST vectype.V128 c_t) [] [valtype.V128]
        (Instr_ok.vconst v_C c_t hwfC hwfinstr) hs hwfC hwfinstr
  | reftype r rt href hs =>
    rw [adminval_val_ref]
    exact construct_ai_ref v_S v_C r rt href hwfC hs

/-- Rocq `typing_lemmas.v:1657` `construct_ai_maybe`. Rocq closes this with one generic
    `destruct ai; ...; try contradiction; eapply plain; eauto` tactic script covering all
    ~74 cases uniformly; mirrored here the same way via `cases ai <;> simp_all [instr_of]`
    (closing the 6 admin-only cases by contradiction against `hsome`, reducing
    `Option.get! (instr_of ai)` to the corresponding `instr` literal in the other 68) then a
    single trailing `Instr_ok2.plain` application, relying on `admininstr_instr (instr.CTOR
    args) = admininstr.CTOR args` being definitional. -/
theorem construct_ai_maybe (v_S : store) (v_C : context) (ai : admininstr) (t1 t2 : List valtype) :
    instr_of ai ≠ none → wf_store v_S → Instr_ok v_C (Option.get! (instr_of ai)) (mkFunctype t1 t2) →
    Instr_ok2 v_S v_C ai (mkFunctype t1 t2) := by
  intro hsome hwfS hinstr
  obtain ⟨hwfC, hwfi⟩ := instr_ok_context_wf v_C (Option.get! (instr_of ai)) (mkFunctype t1 t2) hinstr
  cases ai <;> simp_all [instr_of] <;>
    exact Instr_ok2.plain v_S v_C _ _ _ hinstr hwfS hwfC hwfi

/-- Rocq `typing_lemmas.v:1674` `construct_ais_vals'`. **Context-irrelevance for
    value-list typing** (value typing doesn't depend on local/label/return components of
    `C`) — crucial for label/frame-boundary-crossing lemmas in `type_preservation_pure.v`. -/
theorem construct_ais_vals' (v_S : store) (v_C v_C' : context) (v_vals : List val) (v_ft : functype) :
    Instrs_ok2 v_S v_C (v_vals.map admininstr_val) v_ft → wf_context v_C' →
    Instrs_ok2 v_S v_C' (v_vals.map admininstr_val) v_ft := by
  induction v_vals generalizing v_ft with
  | nil =>
    intro h hC'
    obtain ⟨t1, t2⟩ := v_ft
    obtain ⟨t1s⟩ := t1
    obtain ⟨t2s⟩ := t2
    obtain ⟨_, hwfS, hsub⟩ := (ais_empty_typing v_S v_C t1s t2s).mp (by simpa [mkFunctype] using h)
    simpa [mkFunctype] using (ais_empty_typing v_S v_C' t1s t2s).mpr ⟨hC', hwfS, hsub⟩
  | cons x xs ih =>
    intro h hC'
    obtain ⟨t1, t2⟩ := v_ft
    obtain ⟨t1s⟩ := t1
    obtain ⟨t2s⟩ := t2
    have heq : (x :: xs).map admininstr_val = [admininstr_val x] ++ xs.map admininstr_val := by simp
    rw [heq] at h
    obtain ⟨t3s, htail, hhead⟩ :=
      ais_seq_typing_inversion v_S v_C (xs.map admininstr_val) (admininstr_val x) t1s t2s h
    obtain ⟨t, hsub, hval⟩ := ais_single_val_typing_inversion v_S v_C x t1s t3s hhead
    have hwfS := (ainstrs_ok_context_store_wf v_S v_C (xs.map admininstr_val) (mkFunctype t3s t2s) htail).2.1
    have hhead' : Instrs_ok2 v_S v_C' [admininstr_val x] (mkFunctype t1s t3s) :=
      construct_ais_subtyping v_S v_C' [admininstr_val x] [] [t] t1s t3s
        (construct_ais_typing_single v_S v_C' (admininstr_val x) [] [t]
          (construct_ai_val v_S v_C' x t hval hC' hwfS)) hsub
    have htail' : Instrs_ok2 v_S v_C' (xs.map admininstr_val) (mkFunctype t3s t2s) :=
      ih (mkFunctype t3s t2s) htail hC'
    have := construct_ais_compose v_S v_C' [admininstr_val x] (xs.map admininstr_val) t1s t3s t2s hhead' htail'
    simpa [heq, mkFunctype] using this

/-- Rocq `typing_lemmas.v:1712` `construct_ais_trap`. TRAP typechecks at ANY functype: unlike
    Rocq's `Instrs_ok2__seq`-based decomposition, `Instr_ok2.trap` here is already generic
    over the target functype, so `construct_ais_typing_single` closes it directly. -/
theorem construct_ais_trap (v_S : store) (v_C : context) (v_ft : functype) :
    wf_context v_C → wf_store v_S → Instrs_ok2 v_S v_C [admininstr.TRAP] v_ft := by
  intro hwfC hwfS
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  exact construct_ais_typing_single v_S v_C admininstr.TRAP t1s t2s
    (Instr_ok2.trap v_S v_C t1s t2s hwfS hwfC wf_admininstr.admininstr_case_72)

/-! ## Val_ok / Vals_ok infrastructure (typing_lemmas.v:1731-1948) -/

/-- Rocq `typing_lemmas.v:1731` `value_extra`. -/
def value_extra (v_S : store) (v_val : val) : Prop :=
  match v_val with
  | .REF_FUNC_ADDR v_funcaddr => ∃ v_ft, Externaddr_ok v_S (.FUNC v_funcaddr) (.FUNC v_ft)
  | _ => True

/-- Rocq `typing_lemmas.v:1738` `Vals_ok`. NOTE argument order matches Rocq exactly:
    `Forall2 P v_ts v_vals` (types first, values second).

    **Definition deliberately strengthened over a literal transcription**
    (per explicit user decision — see `claude-logging/verbatim_dialogue_log/`
    `bundle8/vals_ok_non_bot_analysis.md` and
    `bundle9/user_requested_documents/vals_ok_non_bot_resolution.md`): Rocq's
    `Forall2` is an *inductive* relation that forces `v_ts.length =
    v_vals.length` as part of its own shape; this codebase's generated
    `Forall₂` is a zip-based `def` that does not. Baking the length fact in
    here (Option 2 of the analysis doc) keeps every *use site* of `Vals_ok`
    exactly as ergonomic as a literal transcription would have been (nothing
    downstream has to separately plumb a length hypothesis through), at the
    cost of *construction* sites needing to supply the length fact too —
    which is either trivial or already available at every construction site
    identified so far (see the resolution doc). This is the closest Lean
    analogue of what Rocq's own `Forall2` gives for free. -/
def Vals_ok (v_S : store) (v_vals : List val) (v_ts : List valtype) : Prop :=
  v_ts.length = v_vals.length ∧ Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals

/-- Rocq `typing_lemmas.v:1741` `Val_ok_non_bot`. -/
theorem Val_ok_non_bot (v_S : store) (v_val : val) (t : valtype) :
    Val_ok v_S v_val t → t ≠ valtype.BOT := by
  intro h
  cases h with
  | numtype nt _ _ _ => cases nt <;> simp [valtype_numtype]
  | vectype vt _ _ _ => cases vt <;> simp [valtype_vectype]
  | reftype _ rt _ _ => cases rt <;> simp [valtype_reftype]

/-- Rocq `typing_lemmas.v:1753` `ais_vals_typing_inversion`. -/
theorem ais_vals_typing_inversion (v_S : store) (v_C : context) (v_vals : List val) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C (v_vals.map admininstr_val) (mkFunctype t1s t2s) →
    ∃ v_ts : List valtype, instrtype_sub (mkFunctype [] v_ts) (mkFunctype t1s t2s) ∧ Vals_ok v_S v_vals v_ts := by
  induction v_vals generalizing t1s t2s with
  | nil =>
    intro h
    refine ⟨[], ?_, by simp [Vals_ok, Forall₂]⟩
    obtain ⟨_, hwfS, hsub⟩ := (ais_empty_typing v_S v_C t1s t2s).mp (by simpa using h)
    exact ⟨t1s, t2s, [], [], by simp, by simp, hsub, resulttype_sub_refl [], resulttype_sub_refl []⟩
  | cons a xs ih =>
    intro h
    have heq : (a :: xs).map admininstr_val = [admininstr_val a] ++ xs.map admininstr_val := by simp
    rw [heq] at h
    obtain ⟨t3s, htail, hhead⟩ :=
      ais_seq_typing_inversion v_S v_C (xs.map admininstr_val) (admininstr_val a) t1s t2s h
    obtain ⟨v_ts, hsub_tail, hvals_tail⟩ := ih t3s t2s htail
    obtain ⟨t, hsub_head, hval_head⟩ := ais_single_val_typing_inversion v_S v_C a t1s t3s hhead
    obtain ⟨hlen_tail, hforall_tail⟩ := hvals_tail
    refine ⟨t :: v_ts, ?_, ⟨by simp [hlen_tail], ?_⟩⟩
    · have hsub_head' : instrtype_sub (mkFunctype [] ([t] ++ [])) (mkFunctype t1s t3s) := by simpa using hsub_head
      exact instrtype_sub_compose2 [] [t] [] v_ts t1s t3s t2s hsub_head' hsub_tail
    · intro p hp
      rcases List.mem_cons.mp (by simpa using hp) with rfl | hp
      · exact hval_head
      · exact hforall_tail p hp

/-- Rocq `typing_lemmas.v:1813` `construct_ais_vals`. Longest/most intricate proof in the
    Rocq file (~130 lines, `last_ind` on `v_vals`/`ts` simultaneously). This proof diverges:
    it is an ordinary left induction on `v_vals`, splitting the codomain with
    `resulttype_sub_split_sup'` on the `t :: ts'` shape, which avoids Rocq's `take`/`drop`
    size arithmetic. -/
theorem construct_ais_vals (v_S : store) (v_C : context) (v_vals : List val) (t1s t2s ts : List valtype) :
    wf_context v_C → wf_store v_S → instrtype_sub (mkFunctype [] ts) (mkFunctype t1s t2s) →
    Vals_ok v_S v_vals ts → Instrs_ok2 v_S v_C (v_vals.map admininstr_val) (mkFunctype t1s t2s) := by
  intro hwfC hwfS
  induction v_vals generalizing t1s t2s ts with
  | nil =>
    intro hsub hvals
    obtain ⟨hlen, _⟩ := hvals
    have hts : ts = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst hts
    have hrsub : ResulttypeSub t1s t2s := instrtype_sub_empty t1s t2s hsub
    exact (ais_empty_typing v_S v_C t1s t2s).mpr ⟨hwfC, hwfS, hrsub⟩
  | cons a xs ih =>
    intro hsub hvals
    rcases ts with _ | ⟨t, ts'⟩
    · obtain ⟨hlen, _⟩ := hvals
      simp only [List.length_nil, List.length_cons] at hlen
      omega
    · obtain ⟨hlen, hforall⟩ := hvals
      obtain ⟨ts_sub, ts_w, ts11_sub, ts12_sup, he1, he2, hsw, hs11, hs12⟩ := hsub
      have hts11 : ts11_sub = [] := resulttype_sub_empty ts11_sub hs11
      rw [hts11, List.append_nil] at he1
      rw [← he1] at hsw
      obtain ⟨hsplit1, hsplit2⟩ := resulttype_sub_split_sup' ts12_sup [t] ts' hs12
      have hval_head : Val_ok v_S a t := hforall (t, a) (by simp)
      have hvals_tail : Vals_ok v_S xs ts' := by
        refine ⟨by simpa using hlen, ?_⟩
        intro p hp
        exact hforall p (List.mem_cons_of_mem _ hp)
      have head_sub : instrtype_sub (mkFunctype [] [t]) (mkFunctype t1s (ts_w ++ ts12_sup.take 1)) :=
        ⟨t1s, ts_w, [], ts12_sup.take 1, (List.append_nil t1s).symm, rfl, hsw,
          resulttype_sub_refl [], hsplit1⟩
      have tail_sub : instrtype_sub (mkFunctype [] ts') (mkFunctype (ts_w ++ ts12_sup.take 1) t2s) := by
        refine ⟨ts_w ++ ts12_sup.take 1, ts_w ++ ts12_sup.take 1, [], ts12_sup.drop 1,
          (List.append_nil _).symm, ?_, resulttype_sub_refl _, resulttype_sub_refl [], hsplit2⟩
        rw [he2, List.append_assoc, List.take_append_drop]
      have head_typing : Instrs_ok2 v_S v_C [admininstr_val a] (mkFunctype t1s (ts_w ++ ts12_sup.take 1)) :=
        construct_ais_subtyping v_S v_C [admininstr_val a] [] [t] t1s (ts_w ++ ts12_sup.take 1)
          (construct_ais_typing_single v_S v_C (admininstr_val a) [] [t]
            (construct_ai_val v_S v_C a t hval_head hwfC hwfS)) head_sub
      have tail_typing : Instrs_ok2 v_S v_C (xs.map admininstr_val) (mkFunctype (ts_w ++ ts12_sup.take 1) t2s) :=
        ih (ts_w ++ ts12_sup.take 1) t2s ts' tail_sub hvals_tail
      have hcombined := construct_ais_compose v_S v_C [admininstr_val a] (xs.map admininstr_val)
        t1s (ts_w ++ ts12_sup.take 1) t2s head_typing tail_typing
      simpa using hcombined

/-! ## Subtyping-composition helpers (typing_lemmas.v:1949-1974) -/

/-- Rocq `typing_lemmas.v:1949` `resulttype_sub_single_inversion`. `Forall₂` here is the
    zip-based `def` (not an inductive), so `[t1].zip [t2] = [(t1,t2)]` and membership is
    closed by `simp`. -/
theorem resulttype_sub_single_inversion (t1 t2 : valtype) :
    ResulttypeSub [t1] [t2] → Valtype_sub t1 t2 := by
  intro h
  cases h with
  | mk_Resulttype_sub _ _ _ hf => exact hf (t1, t2) (by simp)

/-- Rocq `typing_lemmas.v:1959` `construct_ais_instrtype_sub`. Same statement/proof as
    `construct_ais_subtyping` above (Rocq keeps both names, used interchangeably
    downstream) — kept as a separate lemma for provenance fidelity. -/
theorem construct_ais_instrtype_sub (v_S : store) (v_C : context) (v_ais : List admininstr) (t1s t2s t1s' t2s' : List valtype) :
    Instrs_ok2 v_S v_C v_ais (mkFunctype t1s t2s) →
    instrtype_sub (mkFunctype t1s t2s) (mkFunctype t1s' t2s') →
    Instrs_ok2 v_S v_C v_ais (mkFunctype t1s' t2s') :=
  construct_ais_subtyping v_S v_C v_ais t1s t2s t1s' t2s'

/-! ## `inst_match` — context-component invariance (typing_lemmas.v:1975-2043) -/

/-- Rocq `typing_lemmas.v:1975` `inst_match`. Deliberately excludes LOCALS/LABELS/RETURN:
    "same module-instance-derived components, differing local/label/return typing". -/
def inst_match (C C' : context) : Prop :=
  C.TYPES = C'.TYPES ∧ C.FUNCS = C'.FUNCS ∧ C.GLOBALS = C'.GLOBALS ∧ C.TABLES = C'.TABLES ∧
  C.MEMS = C'.MEMS ∧ C.ELEMS = C'.ELEMS ∧ C.DATAS = C'.DATAS

/-- Rocq `typing_lemmas.v:1984` `construct_inst_match_label`. `inst_match`
    deliberately excludes LABELS (see its own doc comment above), and
    `upd_label` only touches LABELS, so this is definitional. -/
theorem construct_inst_match_label (C C' : context) (lab : List resulttype) :
    inst_match C C' → inst_match C (upd_label C' lab) := fun h => h

/-- Rocq `typing_lemmas.v:1994` `construct_inst_match_return`. Definitional,
    as `construct_inst_match_label` (RETURN is excluded from `inst_match`). -/
theorem construct_inst_match_return (C C' : context) (ret : Option resulttype) :
    inst_match C C' → inst_match C (upd_return C' ret) := fun h => h

/-- Rocq `typing_lemmas.v:2004` `construct_inst_match_local`. Definitional,
    as `construct_inst_match_label` (LOCALS is excluded from `inst_match`). -/
theorem construct_inst_match_local (C C' : context) (loc : List valtype) :
    inst_match C C' → inst_match C (upd_local C' loc) := fun h => h

/-- Rocq `typing_lemmas.v:2014` `construct_inst_match_local_label_return`.
    Definitional, as `construct_inst_match_label` (all three touched fields
    are excluded from `inst_match`). -/
theorem construct_inst_match_local_label_return (C C' : context) (loc : List valtype) (lab : List resulttype) (ret : Option resulttype) :
    inst_match C C' → inst_match C (upd_local_label_return C' loc lab ret) := fun h => h

/-- Rocq `typing_lemmas.v:2024` `construct_inst_match_local_return`.
    Definitional, as `construct_inst_match_label`. -/
theorem construct_inst_match_local_return (C C' : context) (loc : List valtype) (ret : Option resulttype) :
    inst_match C C' → inst_match C (upd_local_return C' loc ret) := fun h => h

/-- Rocq `typing_lemmas.v:2034` `construct_inst_prepend_label`. Definitional,
    as `construct_inst_match_label` (`prepend_label` only touches LABELS). -/
theorem construct_inst_prepend_label (C C' : context) (lab : resulttype) :
    inst_match C C' → inst_match C (prepend_label C' lab) := fun h => h

/-! ## Non-bottom propagation to lists (typing_lemmas.v:2069-2105) -/

/-- Rocq `typing_lemmas.v:2069` `Vals_ok_non_bot`. **Deviation**: the hypothesis is the
    length-carrying `Vals_ok` instead of the bare `Forall₂` Rocq states. Rocq's `Forall2` is
    inductive and forces `v_ts.length = v_val.length`; this project's `Forall₂` is a zip-based
    `def` that does not, so with a bare `Forall₂` the lemma would be false (see `Vals_ok` and
    `claude-logging/verbatim_dialogue_log/bundle8/vals_ok_non_bot_analysis.md`). `Vals_ok` is
    exactly the Lean-side stand-in for what Rocq's own `Forall2` carries for free. Proved by
    converting to Mathlib's `List.Forall₂` via `to_mathlib_forall₂`, then structural induction
    (mirroring Rocq's own proof, which inducts on `v_val` and case-splits `v_ts`). -/
theorem Vals_ok_non_bot (v_S : store) (v_val : List val) (v_ts : List valtype) :
    Vals_ok v_S v_val v_ts → Forall (fun t => t ≠ valtype.BOT) v_ts := by
  rintro ⟨hlen, hforall⟩
  have h2 : List.Forall₂ (fun t v => Val_ok v_S v t) v_ts v_val := to_mathlib_forall₂ hlen hforall
  clear hforall hlen
  induction h2 with
  | nil => intro t ht; simp at ht
  | cons hval _ ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Val_ok_non_bot v_S _ t hval
      · exact ih t ht

/-- Rocq `typing_lemmas.v:2094` `Ref_ok_non_bot`. -/
theorem Ref_ok_non_bot (v_S : store) (v_val : ref) (t : reftype) :
    Ref_ok v_S v_val t → valtype_reftype t ≠ valtype.BOT := by
  intro h
  cases h with
  | null _ => cases t <;> simp [valtype_reftype]
  | func _ _ _ _ _ => simp [valtype_reftype]
  | extern _ _ => simp [valtype_reftype]

end TLC
