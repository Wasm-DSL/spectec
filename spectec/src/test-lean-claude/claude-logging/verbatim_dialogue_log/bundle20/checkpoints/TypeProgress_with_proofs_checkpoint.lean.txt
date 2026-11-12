import «wasm2.0»
import HelperLemmas
import Subtyping
import TypingLemmas
import TypePreservationPure
import ExtensionLemmas
import TypePreservation

/-!
# TypeProgress

Lean port of `spectec/test-rocq/theories/type_progress.v` (upstream `rocq-backend-proof-final`
`95c256c2c`): the **progress** half of type safety. The main theorem is `t_progress`: a
configuration that is `Config_ok` at some result type is either terminal (only values, or a single
`TRAP`) or can take a `Step`.

Structure (it follows the Rocq file):
1. list / administrative-instruction plumbing (`is_const`, `const_list`, `terminal_form`,
   `split_vals`, ...);
2. canonical forms (`typeof`, `invert_typeof_*`);
3. `br`/`return` shape predicates (`br_reduce`, `not_lf_br`, ...) and their typing lemmas;
4. numeric and lane/vector totality lemmas;
5. `t_progress_be` (basic instructions), `t_progress_e` (administrative instructions), `t_progress`;
6. the two counterexample families (`vload_shape64_*`, `vcvtop_trunc_sat_i16_*`) showing where
   progress is FALSE as the spec stands, which is why Rocq's `t_progress_be` is `Admitted`.

**Lean-only structure (bundle20).** Rocq proves `t_progress_be` / `t_progress_e` with one
`Instrs_ok_ind'` / `Admin_instrs_ok_ind'` application whose bullets handle each typing rule. Here
each bullet is a standalone lemma `t_progress_be_<rule>` / `t_progress_e_<rule>` whose statement is,
verbatim, the corresponding minor premise of Lean's auto-generated mutual recursor `Instrs_ok.rec`
/ `Instrs_ok2.rec` for the motives `t_progress_be_P`/`_P0` and `t_progress_e_P`/`_P0`/`_P1` (Rocq's
`P`/`P0`/`P1`). The statements were generated mechanically from the recursors' types, so they fit
by construction, and `t_progress_be`/`t_progress_e` are proved by a single application of the
recursor. The cases can therefore be proved and checked independently.

**Imports.** Rocq's `type_progress.v` does not import the preservation files; this file imports
`TypePreservation` anyway, only to reuse Lean-only helpers (`Moduleinst_ok_lengths`,
`getElem?_eq_some_bang`, typing builders). No logical dependency on preservation results is
intended.

Status (end of bundle20): **everything is proved** except two subcases that are FALSE as the spec
stands, exactly where Rocq has its two `admit`s: the in-bounds `VLOAD V128 (SHAPE 64 X 1)` subcase of
`t_progress_be_vload_pack` (Rocq `admit` at v:5208) and the `F32 X 4 → I16 X 8 TRUNC_SAT … ZERO`
subcase of `t_progress_be_vcvtop` (v:4319). Each is one commented `sorry`. Both are machine-checked
to be stuck (`vload_shape64_stuck`, `vcvtop_trunc_sat_i16_stuck`). `#sorry_deps TLC.t_progress`
lists those two, `Step_read_is_wf` and 56 generated numeric `*_is_wf` theorems (all `Admitted` in
Rocq). `#print axioms` adds 17 project axioms, each mirroring Rocq's `axioms.v`.
-/

namespace TLC


/-- Rocq `type_progress.v:25` `cat_nil`. An append is empty iff both parts are empty. -/
theorem cat_nil (T : Type) (s1 s2 : List T) :
    s1 ++ s2 = [] ↔ s1 = [] ∧ s2 = [] := by
  constructor
  · intro h
    cases s1 with
    | nil => exact ⟨rfl, h⟩
    | cons a l => cases h
  · rintro ⟨rfl, rfl⟩
    rfl

-- `length_size` (type_progress.v:33) NOT PORTED: a Rocq-only bridge between stdlib `length` and mathcomp `size`. Both are `List.length` in Lean, so the statement would collapse to `Iff.rfl`.

/-- Rocq `type_progress.v:37` `LOCAL_injective`. The `local` constructor `LOCAL` is injective. -/
theorem LOCAL_injective : Function.Injective «local».LOCAL := by
  intro x y H
  injection H

/-- Rocq `type_progress.v:43` `default_not_none`. Every non-`BOT` value type has a default value.
    Rocq's boolean `t != BOT` and `default_ t != None` (coerced by `is_true`) are stated with `≠`. -/
theorem default_not_none (ts : List valtype) :
    Forall (fun t => t ≠ valtype.BOT) ts →
    Forall (fun t => default_ t ≠ none) ts := by
  intro HForall t ht
  have h := HForall t ht
  cases t with
  | BOT => exact absurd rfl h
  | _ => simp [default_]

/-- Rocq `type_progress.v:53` `wf_config_app`. A configuration over `ais ++ ais'` is well-formed iff
    the configurations over `ais` and over `ais'` (same state) both are. -/
theorem wf_config_app (s : state) (ais ais' : List admininstr) :
    wf_config (config.mk_config s (ais ++ ais')) ↔
    (wf_config (config.mk_config s ais) ∧ wf_config (config.mk_config s ais')) := by
  constructor
  · intro H
    cases H with
    | config_case_0 _ _ hs hf =>
      refine ⟨wf_config.config_case_0 _ _ hs ?_, wf_config.config_case_0 _ _ hs ?_⟩
      · intro x hx; exact hf x (List.mem_append_left _ hx)
      · intro x hx; exact hf x (List.mem_append_right _ hx)
  · rintro ⟨H1, H2⟩
    cases H1 with
    | config_case_0 _ _ hs hf1 =>
      cases H2 with
      | config_case_0 _ _ _ hf2 =>
        refine wf_config.config_case_0 _ _ hs ?_
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hf1 x h
        · exact hf2 x h

/-- Rocq `type_progress.v:70` `is_const`: is this administrative instruction a value? -/
def is_const (e : admininstr) : Bool :=
  match e with
  | .CONST _ _ => true
  | .VCONST _ _ => true
  | .REF_NULL _ => true
  | .REF_FUNC_ADDR _ => true
  | .REF_HOST_ADDR _ => true
  | _ => false

/-- Rocq `type_progress.v:80` `const_list` (`List.forallb is_const`). -/
def const_list (es : List admininstr) : Bool := es.all is_const

/-- Rocq `type_progress.v:83` `v_to_e_const`. Values injected into `admininstr` form a `const_list`
    (Rocq's `is_true` coercion becomes `= true`). -/
theorem v_to_e_const (vs : List val) :
    const_list (List.map admininstr_val vs) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, const_list, List.all_cons, Bool.and_eq_true] at ih ⊢
    refine ⟨?_, ih⟩
    cases v <;> rfl

/-- Rocq `type_progress.v:92` `terminal_form`. Rocq coerces the boolean `const_list es` to `Prop`
    via `is_true`; here that is `const_list es = true`. -/
def terminal_form (es : List admininstr) : Prop :=
  const_list es = true ∨ es = [admininstr.TRAP]

/-- Rocq `type_progress.v:95` `const_list_cat`. `const_list` of an append is the boolean conjunction. -/
theorem const_list_cat (vs1 vs2 : List admininstr) :
    const_list (vs1 ++ vs2) = (const_list vs1 && const_list vs2) := by
  unfold const_list
  exact List.all_append

/-- Rocq `type_progress.v:104` `const_list_concat`. The append of two `const_list`s is a `const_list`. -/
theorem const_list_concat (vs1 vs2 : List admininstr) :
    const_list vs1 = true →
    const_list vs2 = true →
    const_list (vs1 ++ vs2) = true := by
  intro Hconst1 Hconst2
  rw [const_list_cat, Hconst1, Hconst2]
  rfl

/-- Rocq `type_progress.v:114` `const_list_split`. If an append is a `const_list`, so are both parts. -/
theorem const_list_split (vs1 vs2 : List admininstr) :
    const_list (vs1 ++ vs2) = true →
    const_list vs1 = true ∧
    const_list vs2 = true := by
  intro Hconst
  rw [const_list_cat] at Hconst
  exact Bool.and_eq_true_iff.mp Hconst

/-- Rocq `type_progress.v:124` `const_es_exists`. A `const_list` is the image of some list of values.
    **Deviation:** Rocq returns a `sig` (`{vs | es = map admininstr_val vs}`); Lean states `∃` (Prop). -/
theorem const_es_exists (es : List admininstr) :
    const_list es = true →
    ∃ vs, es = List.map admininstr_val vs := by
  induction es with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a es ih =>
    intro HConst
    obtain ⟨ha, hes⟩ := const_list_split [a] es HConst
    obtain ⟨vs, rfl⟩ := ih hes
    have ha' : is_const a = true := by simpa [const_list] using ha
    cases a with
    | CONST t n => exact ⟨val.CONST t n :: vs, rfl⟩
    | VCONST t v => exact ⟨val.VCONST t v :: vs, rfl⟩
    | REF_NULL t => exact ⟨val.REF_NULL t :: vs, rfl⟩
    | REF_FUNC_ADDR a => exact ⟨val.REF_FUNC_ADDR a :: vs, rfl⟩
    | REF_HOST_ADDR a => exact ⟨val.REF_HOST_ADDR a :: vs, rfl⟩
    | _ => simp [is_const] at ha'

/-- Rocq `type_progress.v:143` `map_eq_nil`. If `map f l` is empty, then `l` is empty. -/
theorem map_eq_nil {A B : Type} (f : A → B) (l : List A) :
    List.map f l = [] → l = [] := by
  intro h
  cases l with
  | nil => rfl
  | cons a l => cases h

/-- Rocq `type_progress.v:151` `map_neq_nil`. If `map f l` is non-empty, then `l` is non-empty. -/
theorem map_neq_nil {A B : Type} (f : A → B) (l : List A) :
    List.map f l ≠ [] → l ≠ [] := by
  intro h hl
  subst hl
  exact h rfl

/-- Rocq `type_progress.v:159` `reduce_trap_left`. A non-empty `const_list` followed by `TRAP` steps
    (`Step_pure`) to `[TRAP]`. -/
theorem reduce_trap_left (vs : List admininstr) :
    const_list vs = true →
    vs ≠ [] →
    Step_pure (vs ++ [admininstr.TRAP]) [admininstr.TRAP] := by
  intro HConst H
  obtain ⟨vcs, rfl⟩ := const_es_exists vs HConst
  exact Step_pure.trap_vals vcs [] (Or.inl (map_neq_nil admininstr_val vcs H))

/-- Rocq `type_progress.v:174` `v_e_trap`. If `vs ++ es = [TRAP]` with `vs` a `const_list`, then
    `vs = []` and `es = [TRAP]`. -/
theorem v_e_trap (vs es : List admininstr) :
    const_list vs = true →
    vs ++ es = [admininstr.TRAP] →
    vs = [] ∧ es = [admininstr.TRAP] := by
  intro HConst H
  cases vs with
  | nil => exact ⟨rfl, H⟩
  | cons v vs =>
    cases vs with
    | nil =>
      have hv : is_const v = true := by simpa [const_list] using HConst
      have hv' : v = admininstr.TRAP := (List.cons.inj H).1
      subst hv'
      simp [is_const] at hv
    | cons v' vs' => simp at H

/-- Rocq `type_progress.v:186` `concat_cancel_last`. Cancel a final singleton on both sides of an
    append equation. -/
theorem concat_cancel_last {X : Type} (l1 l2 : List X) (e1 e2 : X) :
    l1 ++ [e1] = l2 ++ [e2] →
    l1 = l2 ∧ e1 = e2 := by
  intro H
  have H0 : (l1 ++ [e1]).reverse = (l2 ++ [e2]).reverse := by rw [H]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.cons.injEq] at H0
  obtain ⟨h1, h2⟩ := H0
  exact ⟨List.reverse_inj.mp h2, h1⟩

/-- Rocq `type_progress.v:197` `extract_list1`. If `es ++ [e1] = [e2]`, then `es = []` and `e1 = e2`. -/
theorem extract_list1 {X : Type} (es : List X) (e1 e2 : X) :
    es ++ [e1] = [e2] →
    es = [] ∧ e1 = e2 := by
  intro H
  exact concat_cancel_last es [] e1 e2 H

/-- Rocq `type_progress.v:206` `v_to_e_cat`. `map admininstr_val` distributes over append (folded form). -/
theorem v_to_e_cat (vs1 vs2 : List val) :
    List.map admininstr_val vs1 ++ List.map admininstr_val vs2 =
    List.map admininstr_val (vs1 ++ vs2) := by
  induction vs1 with
  | nil => rfl
  | cons a l IH => simp only [List.map_cons, List.cons_append, IH]

/-- Rocq `type_progress.v:214` `be_to_e_cat`. `map admininstr_instr` distributes over append (folded form). -/
theorem be_to_e_cat (bes1 bes2 : List instr) :
    List.map admininstr_instr bes1 ++ List.map admininstr_instr bes2 =
    List.map admininstr_instr (bes1 ++ bes2) := by
  induction bes1 with
  | nil => rfl
  | cons a l IH => simp only [List.map_cons, List.cons_append, IH]

/-- Rocq `type_progress.v:222` `to_e_list_cat`. `map admininstr_instr` distributes over append
    (unfolded form; the converse orientation of `be_to_e_cat`). -/
theorem to_e_list_cat (bes1 bes2 : List instr) :
    List.map admininstr_instr (bes1 ++ bes2) =
    List.map admininstr_instr bes1 ++ List.map admininstr_instr bes2 := by
  induction bes1 with
  | nil => rfl
  | cons a l IH => simp only [List.map_cons, List.cons_append, IH]

/-- Rocq `type_progress.v:231` `cat_split`. If `l = l1 ++ l2`, then `l1` and `l2` are the `take`/`drop`
    of `l` at `size l1` (Rocq `size` is `List.length`). -/
theorem cat_split {X : Type} (l l1 l2 : List X) :
    l = l1 ++ l2 →
    l1 = List.take l1.length l ∧
    l2 = List.drop l1.length l := by
  intro HCat
  subst HCat
  exact ⟨(List.take_left).symm, (List.drop_left).symm⟩

/-- Rocq `type_progress.v:246` `terminal_form_v_e`. If `vs ++ es` is terminal and `vs` is a
    `const_list`, then `es` is terminal. -/
theorem terminal_form_v_e (vs es : List admininstr) :
    const_list vs = true →
    terminal_form (vs ++ es) →
    terminal_form es := by
  intro HConst HTerm
  unfold terminal_form at HTerm ⊢
  rcases HTerm with H | H
  · left
    exact (const_list_split vs es H).2
  · cases vs with
    | nil =>
      right
      simpa using H
    | cons a vs' =>
      exfalso
      simp only [List.cons_append, List.cons.injEq] at H
      obtain ⟨rfl, _⟩ := H
      simp [const_list, is_const] at HConst

/-- Rocq `type_progress.v:262` `typeof`: the value type of a value. -/
def typeof (v : val) : valtype :=
  match v with
  | .CONST t _ => valtype_numtype t
  | .VCONST t _ => valtype_vectype t
  | .REF_NULL t => valtype_reftype t
  | .REF_FUNC_ADDR _ => valtype.FUNCREF
  | .REF_HOST_ADDR _ => valtype.EXTERNREF

/-- Rocq `type_progress.v:271` `typeof_append`. If the types of `vs` are `ts ++ [t]`, then `vs` is its
    first `size ts` elements (typed `ts`) followed by one value `v` of type `t`. -/
theorem typeof_append (ts : List valtype) (t : valtype) (vs : List val) :
    List.map typeof vs = ts ++ [t] →
    ∃ v,
      vs = List.take ts.length vs ++ [v] ∧
      List.map typeof (List.take ts.length vs) = ts ∧
      typeof v = t := by
  intro HMapType
  obtain ⟨H, H0⟩ := cat_split _ _ _ HMapType
  rw [← List.map_take] at H
  rw [← List.map_drop] at H0
  generalize hD : List.drop ts.length vs = D at H0
  cases D with
  | nil => simp at H0
  | cons v l =>
    cases l with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at H0
      refine ⟨v, ?_, H.symm, H0.symm⟩
      rw [← hD]
      exact (List.take_append_drop _ _).symm
    | cons v' l' => simp at H0

/-- Rocq `type_progress.v:295` `typeof_cat`. If the types of `vs` are `ts1 ++ ts2`, then `vs` splits as
    `vs1 ++ vs2` with types `ts1` and `ts2`. -/
theorem typeof_cat (ts1 ts2 : List valtype) (vs : List val) :
    List.map typeof vs = ts1 ++ ts2 →
    ∃ vs1 vs2,
      vs = vs1 ++ vs2 ∧
      List.map typeof vs1 = ts1 ∧
      List.map typeof vs2 = ts2 := by
  induction ts2 using List.reverseRecOn generalizing ts1 vs with
  | nil =>
    intro H
    refine ⟨vs, [], by simp, ?_, rfl⟩
    simpa using H
  | append_singleton ts2' t IH =>
    intro H
    rw [← List.append_assoc] at H
    obtain ⟨v, Hvs, H1, H2⟩ := typeof_append (ts1 ++ ts2') t vs H
    obtain ⟨vs1, vs2, Hvs', IH1, IH2⟩ := IH ts1 (List.take (ts1 ++ ts2').length vs) H1
    refine ⟨vs1, vs2 ++ [v], ?_, IH1, ?_⟩
    · rw [← List.append_assoc, ← Hvs']
      exact Hvs
    · rw [List.map_append, IH2]
      show ts2' ++ [typeof v] = ts2' ++ [t]
      rw [H2]

-- Ltac `invert_typeof_vcs` (type_progress.v:365) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

/-- Rocq `type_progress.v:416` `invert_typeof_I32`. Canonical form: a well-formed value of type `I32` is
    an `i32.const` (Rocq's `v' : N` is `Nat` here). -/
theorem invert_typeof_I32 (v : val) :
    typeof v = valtype.I32 →
    wf_val v →
    ∃ v',
      admininstr_val v = admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v')) := by
  intro Ht Hwf
  cases v with
  | CONST nt n =>
    cases nt with
    | I32 =>
      cases Hwf with
      | val_case_0 _ _ Hn =>
        cases Hn with
        | num__case_0 vInn x _ _ hnt =>
          cases vInn with
          | I32 =>
            cases x with
            | mk_uN i => exact ⟨i, rfl⟩
          | I64 => cases hnt
        | num__case_1 vFnn x _ hnt =>
          cases vFnn <;> cases hnt
    | I64 => cases Ht
    | F32 => cases Ht
    | F64 => cases Ht
  | VCONST vt c => cases vt; cases Ht
  | REF_NULL rt => cases rt <;> cases Ht
  | REF_FUNC_ADDR _ => cases Ht
  | REF_HOST_ADDR _ => cases Ht

/-- Rocq `type_progress.v:434` `invert_typeof_I64`. Canonical form: a well-formed value of type `I64` is
    an `i64.const` (Rocq's `v' : N` is `Nat` here). -/
theorem invert_typeof_I64 (v : val) :
    typeof v = valtype.I64 →
    wf_val v →
    ∃ v',
      admininstr_val v = admininstr.CONST numtype.I64 (num_.mk_num__0 Inn.I64 (uN.mk_uN v')) := by
  intro Ht Hwf
  cases v with
  | CONST nt n =>
    cases nt with
    | I64 =>
      cases Hwf with
      | val_case_0 _ _ Hn =>
        cases Hn with
        | num__case_0 vInn x _ _ hnt =>
          cases vInn with
          | I32 => cases hnt
          | I64 =>
            cases x with
            | mk_uN i => exact ⟨i, rfl⟩
        | num__case_1 vFnn x _ hnt =>
          cases vFnn <;> cases hnt
    | I32 => cases Ht
    | F32 => cases Ht
    | F64 => cases Ht
  | VCONST vt c => cases vt; cases Ht
  | REF_NULL rt => cases rt <;> cases Ht
  | REF_FUNC_ADDR _ => cases Ht
  | REF_HOST_ADDR _ => cases Ht

/-- Rocq `type_progress.v:452` `invert_typeof_numtype`. Canonical form: a value of numeric type `t` is
    a `CONST t n`. -/
theorem invert_typeof_numtype (v : val) (t : numtype) :
    typeof v = valtype_numtype t →
    ∃ (n : num_),
      admininstr_val v = admininstr.CONST t n := by
  intro Ht
  cases v with
  | CONST nt n =>
    cases nt <;> cases t <;> first | exact ⟨n, rfl⟩ | cases Ht
  | VCONST vt c => cases vt; cases t <;> cases Ht
  | REF_NULL rt => cases rt <;> cases t <;> cases Ht
  | REF_FUNC_ADDR _ => cases t <;> cases Ht
  | REF_HOST_ADDR _ => cases t <;> cases Ht

/-- Rocq `type_progress.v:467` `invert_typeof_numtype_wf`. As `invert_typeof_numtype`, and the payload is
    well-formed (`wf_num_ t n`) when the value is. -/
theorem invert_typeof_numtype_wf (v : val) (t : numtype) :
    typeof v = valtype_numtype t →
    wf_val v →
    ∃ (n : num_),
      admininstr_val v = admininstr.CONST t n ∧ wf_num_ t n := by
  intro Ht Hwf
  cases v with
  | CONST nt n =>
    cases nt <;> cases t <;>
      first
      | (cases Hwf with
         | val_case_0 _ _ Hn => exact ⟨n, rfl, Hn⟩)
      | cases Ht
  | VCONST vt c => cases vt; cases t <;> cases Ht
  | REF_NULL rt => cases rt <;> cases t <;> cases Ht
  | REF_FUNC_ADDR _ => cases t <;> cases Ht
  | REF_HOST_ADDR _ => cases t <;> cases Ht

/-- Rocq `type_progress.v:482` `invert_typeof_V128`. Canonical form: a well-formed value of type `V128`
    is a `VCONST V128 c` with `c` a well-formed 128-bit number (Rocq `!(res_size ...)` is
    `Option.get! (size ...)`). -/
theorem invert_typeof_V128 (v : val) :
    typeof v = valtype.V128 →
    wf_val v →
    ∃ (c : vec_),
      admininstr_val v = admininstr.VCONST vectype.V128 c ∧
      wf_uN (Option.get! (size (valtype_vectype vectype.V128))) c := by
  intro Ht Hwf
  cases v with
  | CONST nt n => cases nt <;> cases Ht
  | VCONST vt c =>
    cases vt
    cases Hwf with
    | val_case_1 _ _ _ h2 => exact ⟨c, rfl, h2⟩
  | REF_NULL rt => cases rt <;> cases Ht
  | REF_FUNC_ADDR _ => cases Ht
  | REF_HOST_ADDR _ => cases Ht

/-- Rocq `type_progress.v:498` `invert_typeof_reftype`. Canonical form: a value of reference type `t` is
    `REF_NULL t`, or a `REF_FUNC_ADDR x` or `REF_HOST_ADDR x`. -/
theorem invert_typeof_reftype (v : val) (t : reftype) :
    typeof v = valtype_reftype t →
    (admininstr_val v = admininstr.REF_NULL t) ∨
    (∃ x,
      admininstr_val v = admininstr.REF_FUNC_ADDR x ∨
      admininstr_val v = admininstr.REF_HOST_ADDR x) := by
  intro Ht
  cases v with
  | CONST nt n =>
    cases nt <;> cases t <;> simp [typeof, valtype_numtype, valtype_reftype] at Ht
  | VCONST vt c =>
    cases vt; cases t <;> simp [typeof, valtype_vectype, valtype_reftype] at Ht
  | REF_NULL rt =>
    left
    cases rt <;> cases t <;> simp [typeof, valtype_reftype, admininstr_val] at Ht ⊢
  | REF_FUNC_ADDR x => exact Or.inr ⟨x, Or.inl rfl⟩
  | REF_HOST_ADDR x => exact Or.inr ⟨x, Or.inr rfl⟩

/-- Rocq `type_progress.v:530` `invert_typeof_reftype'`. A value of reference type is
    `admininstr_ref r` for some `ref` `r`. -/
theorem invert_typeof_reftype' (v : val) (t : reftype) :
    typeof v = valtype_reftype t →
    (∃ r, admininstr_val v = admininstr_ref r) := by
  intro Ht
  cases v with
  | CONST nt n =>
    cases nt <;> cases t <;> simp [typeof, valtype_numtype, valtype_reftype] at Ht
  | VCONST vt c =>
    cases vt; cases t <;> simp [typeof, valtype_vectype, valtype_reftype] at Ht
  | REF_NULL rt => exact ⟨ref.REF_NULL rt, rfl⟩
  | REF_FUNC_ADDR x => exact ⟨ref.REF_FUNC_ADDR x, rfl⟩
  | REF_HOST_ADDR x => exact ⟨ref.REF_HOST_ADDR x, rfl⟩

-- `instr_eqb` and `eqinstrP` (type_progress.v:556-558) NOT PORTED: a boolean equality on `instr`
-- and its ssreflect `Equality.axiom` reflection lemma. Lean derives `DecidableEq instr` in the
-- generated file, which is used directly.

/-- Rocq `type_progress.v:560` `list_slice_size`. An in-bounds slice of length `j` has length `j`. Rocq
    `list_slice bs i j` (wasm.v:57) is `List.take j (List.drop i bs)`, and `|bs|` is `bs.length`. The
    premise is Rocq's Prop `N.le` (`binN_scope`), `i j : N` → `Nat`. -/
theorem list_slice_size {T : Type} (bs : List T) (i j : Nat) :
    i + j ≤ bs.length →
    (List.take j (List.drop i bs)).length = j := by
  intro H
  rw [List.length_take, List.length_drop]
  omega

-- `Scheme Instr_ok_ind'` (type_progress.v:587) NOT PORTED: Lean auto-generates the mutual recursor
-- `Instrs_ok.rec` (motives for `Instr_ok` and `Instrs_ok`), used by `t_progress_be` below.

/-- Rocq `type_progress.v:590` `br_reduce`. Rocq's `++` is right-associative; the grouping is kept
    explicitly (Lean's `++` is left-associative). -/
def br_reduce (es : List admininstr) : Prop :=
  ∃ (vcs : List val) (l : labelidx) (es' : List admininstr),
    es = List.map admininstr_val vcs ++ ([admininstr.BR l] ++ es')

/-- Rocq `type_progress.v:594` `return_reduce`. -/
def return_reduce (es : List admininstr) : Prop :=
  ∃ (vcs : List val) (es' : List admininstr),
    es = List.map admininstr_val vcs ++ ([admininstr.RETURN] ++ es')

/-- Rocq `type_progress.v:599` `not_lf_br`. -/
def not_lf_br (es : List admininstr) : Prop :=
  ∀ (vcs : List val) (l : labelidx) (es' : List admininstr),
    es ≠ List.map admininstr_val vcs ++ ([admininstr.BR l] ++ es')

/-- Rocq `type_progress.v:604` `not_lf_return`. -/
def not_lf_return (es : List admininstr) : Prop :=
  ∀ (vcs : List val) (es' : List admininstr),
    es ≠ List.map admininstr_val vcs ++ ([admininstr.RETURN] ++ es')

/-- Rocq `type_progress.v:609` `split_vals`: split off the leading run of values. -/
def split_vals : List admininstr → List val × List admininstr
  | .CONST t v :: es' => let p := split_vals es'; (val.CONST t v :: p.1, p.2)
  | .VCONST t v :: es' => let p := split_vals es'; (val.VCONST t v :: p.1, p.2)
  | .REF_NULL t :: es' => let p := split_vals es'; (val.REF_NULL t :: p.1, p.2)
  | .REF_FUNC_ADDR t :: es' => let p := split_vals es'; (val.REF_FUNC_ADDR t :: p.1, p.2)
  | .REF_HOST_ADDR t :: es' => let p := split_vals es'; (val.REF_HOST_ADDR t :: p.1, p.2)
  | es => ([], es)

/-- Rocq `type_progress.v:629` `split_vals_inverse`. `split_vals` splits `es` into its leading values
    `vs` and the rest `es'`, with `es = map admininstr_val vs ++ es'`. -/
theorem split_vals_inverse (vs : List val) (es es' : List admininstr) :
    split_vals es = (vs, es') →
    es = List.map admininstr_val vs ++ es' := by
  induction es generalizing vs es' with
  | nil =>
    intro H
    simp only [split_vals, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    rfl
  | cons e es ih =>
    intro H
    cases e <;> simp only [split_vals, Prod.mk.injEq] at H <;>
      (try (obtain ⟨rfl, rfl⟩ := H; rfl)) <;>
      (obtain ⟨rfl, rfl⟩ := H
       simp only [List.map_cons, admininstr_val, List.cons_append, List.cons.injEq, true_and]
       exact ih _ _ rfl)

/-- Rocq `type_progress.v:652` `split_vals_prefix`. `split_vals` stops at the first non-value: on
    `vs ++ [e] ++ es` with `e` not a value it returns `(vs, [e] ++ es)`. Rocq's `~is_const e`
    (`is_true` coercion) is `¬ (is_const e = true)`; Rocq's right-associated `++` is kept. -/
theorem split_vals_prefix (vs : List val) (e : admininstr) (es : List admininstr) :
    ¬ (is_const e = true) →
    split_vals (List.map admininstr_val vs ++ ([e] ++ es)) = (vs, [e] ++ es) := by
  intro H
  induction vs with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    cases e <;> simp_all [is_const, split_vals]
  | cons v vs ih =>
    show split_vals (admininstr_val v :: (List.map admininstr_val vs ++ ([e] ++ es))) = (v :: vs, [e] ++ es)
    cases v <;> simp only [admininstr_val, split_vals, ih]

/-- Rocq `type_progress.v:666` `br_reduce_decidable`. `br_reduce es` is decidable.
    **Deviation:** Rocq's `decidable` is ssrbool's sumbool `{P} + {~ P}` (computational, not a
    `Prop`); its exact Lean counterpart is `Decidable P` (in `Type`), so this is a `def`, not a
    `theorem` (a Lean `theorem` must state a `Prop`). Lean's constructors are `isFalse`/`isTrue`
    (Rocq: `left : P` / `right : ~ P`). Not an `instance` (Rocq's is a plain `Lemma`). -/
def br_reduce_decidable (es : List admininstr) : Decidable (br_reduce es) := by
  unfold br_reduce
  rcases Ees : split_vals es with ⟨vs, es'⟩
  rcases Ees' : es' with _ | ⟨e, es''⟩
  · refine isFalse ?_
    rintro ⟨vcs, l, es''', Hcontra⟩
    rw [Hcontra, split_vals_prefix vcs (admininstr.BR l) es''' (by simp [is_const])] at Ees
    have h2 := (Prod.mk.inj Ees).2
    rw [Ees'] at h2
    simp at h2
  · cases e with
    | BR l =>
      refine isTrue ⟨vs, l, es'', ?_⟩
      have h := split_vals_inverse vs es es' Ees
      rw [h, Ees']
      rfl
    | _ =>
      refine isFalse ?_
      rintro ⟨vcs, li, es''', Hcontra⟩
      rw [Hcontra, split_vals_prefix vcs (admininstr.BR li) es''' (by simp [is_const])] at Ees
      have h2 := (Prod.mk.inj Ees).2
      rw [Ees'] at h2
      simp at h2

/-- Rocq `type_progress.v:692` `return_reduce_decidable`. `return_reduce es` is decidable.
    **Deviation:** as for `br_reduce_decidable`: Rocq's sumbool `decidable` is Lean's `Decidable`,
    so this is a `def`, not a `theorem`. -/
def return_reduce_decidable (es : List admininstr) : Decidable (return_reduce es) := by
  unfold return_reduce
  rcases Ees : split_vals es with ⟨vs, es'⟩
  rcases Ees' : es' with _ | ⟨e, es''⟩
  · refine isFalse ?_
    rintro ⟨vcs, es''', Hcontra⟩
    rw [Hcontra, split_vals_prefix vcs admininstr.RETURN es''' (by simp [is_const])] at Ees
    have h2 := (Prod.mk.inj Ees).2
    rw [Ees'] at h2
    simp at h2
  · cases e with
    | RETURN =>
      refine isTrue ⟨vs, es'', ?_⟩
      have h := split_vals_inverse vs es es' Ees
      rw [h, Ees']
      rfl
    | _ =>
      refine isFalse ?_
      rintro ⟨vcs, es''', Hcontra⟩
      rw [Hcontra, split_vals_prefix vcs admininstr.RETURN es''' (by simp [is_const])] at Ees
      have h2 := (Prod.mk.inj Ees).2
      rw [Ees'] at h2
      simp at h2

/-- Rocq `type_progress.v:717` `not_br_reduce_not_lf_br`. If `es` is not a `br_reduce` shape, it
    satisfies `not_lf_br`. -/
theorem not_br_reduce_not_lf_br (es : List admininstr) :
    ¬ br_reduce es → not_lf_br es := by
  unfold br_reduce not_lf_br
  intro H1 vcs l es' H2
  exact H1 ⟨vcs, l, es', H2⟩

/-- Rocq `type_progress.v:725` `not_return_reduce_not_lf_return`. If `es` is not a
    `return_reduce` shape, it satisfies `not_lf_return`. -/
theorem not_return_reduce_not_lf_return (es : List admininstr) :
    ¬ return_reduce es → not_lf_return es := by
  unfold return_reduce not_lf_return
  intro H1 vcs es' H2
  exact H1 ⟨vcs, es', H2⟩

/-- Rocq `type_progress.v:733` `not_lf_br_singleton`. A singleton satisfying `not_lf_br` is not a
    `BR l`. -/
theorem not_lf_br_singleton (e : admininstr) (l : labelidx) :
    not_lf_br [e] → e ≠ admininstr.BR l := by
  intro H Hcontra
  subst Hcontra
  exact H [] l [] (by simp)

/-- Rocq `type_progress.v:741` `not_lf_return_singleton`. A singleton satisfying `not_lf_return`
    is not `RETURN`. -/
theorem not_lf_return_singleton (e : admininstr) :
    not_lf_return [e] → e ≠ admininstr.RETURN := by
  intro H Hcontra
  subst Hcontra
  exact H [] [] (by simp)

/-- Rocq `type_progress.v:749` `not_lf_br_right`. `not_lf_br` of an append passes to its prefix. -/
theorem not_lf_br_right (es1 es2 : List admininstr) :
    not_lf_br (es1 ++ es2) →
    not_lf_br es1 := by
  unfold not_lf_br
  intro Hnotbr vcs l es' Hcontra
  apply Hnotbr vcs l (es' ++ es2)
  rw [Hcontra]
  simp only [List.append_assoc]

/-- Rocq `type_progress.v:760` `not_lf_br_left`. `not_lf_br` of an append with a value prefix
    passes to the suffix. Rocq's `is_true (const_list es1)` is `const_list es1 = true`. -/
theorem not_lf_br_left (es1 es2 : List admininstr) :
    const_list es1 = true →
    not_lf_br (es1 ++ es2) →
    not_lf_br es2 := by
  unfold not_lf_br
  intro Hconst Hnotbr vcs l es' Hcontra
  obtain ⟨vs1, Hvs1⟩ := const_es_exists es1 Hconst
  apply Hnotbr (vs1 ++ vcs) l es'
  rw [Hvs1, Hcontra]
  simp only [List.map_append, List.append_assoc]

/-- Rocq `type_progress.v:772` `not_lf_return_right`. `not_lf_return` of an append passes to its
    prefix. -/
theorem not_lf_return_right (es1 es2 : List admininstr) :
    not_lf_return (es1 ++ es2) →
    not_lf_return es1 := by
  unfold not_lf_return
  intro hnotret vcs es' hcontra
  apply hnotret vcs (es' ++ es2)
  rw [hcontra]
  simp

/-- Rocq `type_progress.v:783` `not_lf_return_left`. `not_lf_return` of an append with a value
    prefix passes to the suffix. Rocq's `is_true (const_list es1)` is `const_list es1 = true`. -/
theorem not_lf_return_left (es1 es2 : List admininstr) :
    const_list es1 = true →
    not_lf_return (es1 ++ es2) →
    not_lf_return es2 := by
  unfold not_lf_return
  intro hconst hnotret vcs es' hcontra
  obtain ⟨vs1, hvs1⟩ := const_es_exists es1 hconst
  apply hnotret (vs1 ++ vcs) es'
  rw [hvs1, hcontra]
  simp

/-- Rocq `type_progress.v:795` `Forall2_Val_ok_is_same_as_map`. If the values are pointwise
    `Val_ok` at the types `v_t1`, then `v_t1` is the list of their `typeof`s.
    **Deviation:** extra premise `v_t1.length = v_local_vals.length` right after the `Forall₂`
    premise. Lean's generated `Forall₂` is zip-based and does not imply equal lengths (Rocq's
    inductive `Forall2` does), and the conclusion (a list equality) is false without it, e.g. for
    `v_t1 = [t, t']`, `v_local_vals = [v]` with `Val_ok v_S v t`. Project precedent:
    `funcinst_same`, `Vals_ok`. -/
theorem Forall2_Val_ok_is_same_as_map (v_S : store) (v_t1 : List valtype) (v_local_vals : List val) :
    Forall₂ (fun v s => Val_ok v_S s v) v_t1 v_local_vals →
    v_t1.length = v_local_vals.length →
    List.map typeof v_local_vals = v_t1 := by
  intro hforall hlen
  have h := to_mathlib_forall₂ hlen hforall
  clear hforall hlen
  induction h with
  | nil => rfl
  | @cons a b l1 l2 hab _ ih =>
    have hab' : Val_ok v_S b a := hab
    have hty : typeof b = a := by
      cases hab' with
      | numtype _ _ _ _ => rfl
      | vectype _ _ _ _ => rfl
      | reftype _ _ href _ => cases href <;> rfl
    rw [List.map_cons, hty, ih]

/-- Rocq `type_progress.v:808` `frame_t_context_local_types`. A frame's typing context has the
    `typeof`s of the frame's locals as `LOCALS`. (Lean's `Frame_ok` carries the locals' length
    equality as an explicit premise, so no extra length premise is needed here.) -/
theorem frame_t_context_local_types (s : store) (f : frame) (C : context) :
    Frame_ok s f C →
    C.LOCALS = List.map typeof f.LOCALS := by
  intro hframe
  cases hframe with
  | mk_Frame_ok val_lst v_minst t_lst0 C0 hminst hlen hvals _ _ _ _ =>
    have hloc := inst_t_context_local_empty s v_minst C0 hminst
    show t_lst0 ++ C0.LOCALS = List.map typeof val_lst
    rw [hloc, List.append_nil]
    exact (Forall2_Val_ok_is_same_as_map s t_lst0 val_lst hvals hlen).symm

/-- Rocq `type_progress.v:819` `frame_t_context_label_empty`. A frame's typing context has no
    labels. -/
theorem frame_t_context_label_empty (s : store) (f : frame) (C : context) :
    Frame_ok s f C →
    C.LABELS = [] := by
  intro hframe
  cases hframe with
  | mk_Frame_ok _ v_minst _ C0 hminst _ _ _ _ _ _ =>
    have hlab := inst_t_context_labels_empty s v_minst C0 hminst
    show [] ++ C0.LABELS = []
    simp [hlab]

/-- Rocq `type_progress.v:829` `wf_forall_admin_val`. A list of values is well-formed iff its image
    under `admininstr_val` is. -/
theorem wf_forall_admin_val (v_lst : List val) :
    Forall (fun v => wf_val v) v_lst ↔
    Forall (fun a => wf_admininstr a) (List.map (fun v => admininstr_val v) v_lst) := by
  constructor
  · intro h a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    have hwf := h v hv
    cases hwf with
    | val_case_0 nt c hn => exact wf_admininstr.admininstr_case_13 nt c hn
    | val_case_1 vt c hsz hwfc => exact wf_admininstr.admininstr_case_20 vt c hsz hwfc
    | val_case_2 rt => exact wf_admininstr.admininstr_case_40 rt
    | val_case_3 a => exact wf_admininstr.admininstr_case_68 a
    | val_case_4 a => exact wf_admininstr.admininstr_case_69 a
  · intro h v hv
    have hwf := h (admininstr_val v) (List.mem_map.mpr ⟨v, hv, rfl⟩)
    cases v with
    | CONST nt c =>
      have hwf' : wf_admininstr (admininstr.CONST nt c) := hwf
      cases hwf' with
      | admininstr_case_13 _ _ hn => exact wf_val.val_case_0 nt c hn
    | VCONST vt c =>
      have hwf' : wf_admininstr (admininstr.VCONST vt c) := hwf
      cases hwf' with
      | admininstr_case_20 _ _ hsz hwfc => exact wf_val.val_case_1 vt c hsz hwfc
    | REF_NULL rt => exact wf_val.val_case_2 rt
    | REF_FUNC_ADDR a => exact wf_val.val_case_3 a
    | REF_HOST_ADDR a => exact wf_val.val_case_4 a

/-- Rocq `type_progress.v:846` `wf_forall_admin`. Well-formed instructions have a well-formed image
    under `admininstr_instr`. -/
theorem wf_forall_admin (i_lst : List instr) :
    Forall (fun i => wf_instr i) i_lst →
    Forall (fun a => wf_admininstr a) (List.map (fun i => admininstr_instr i) i_lst) := by
  intro h a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  exact (wf_admininstr_instr i).mp (h i hi)

/-- Rocq `type_progress.v:857` `wf_config_label`. A well-formed configuration whose instructions are
    one `LABEL_ n bes es` gives well-formed configurations (same state) for the body `es` and for
    the continuation `bes`. -/
theorem wf_config_label (s : state) (n : n) (bes : List instr) (es : List admininstr) :
    wf_config (config.mk_config s [admininstr.LABEL_ n bes es]) →
    wf_config (config.mk_config s es) ∧ wf_config (config.mk_config s (List.map admininstr_instr bes)) := by
  intro h
  cases h with
  | config_case_0 _ _ hst hall =>
    have hlab : wf_admininstr (admininstr.LABEL_ n bes es) := hall _ (List.mem_singleton_self _)
    cases hlab with
    | admininstr_case_71 _ _ _ hbes hes =>
      exact ⟨wf_config.config_case_0 s es hst hes,
             wf_config.config_case_0 s _ hst (wf_forall_admin bes hbes)⟩

/-- Rocq `type_progress.v:870` `wf_config_frame`. A well-formed configuration whose instructions are
    one `FRAME_ n f es` gives well-formed configurations for the body `es`, both under the outer
    frame `f'` and under the inner frame `f`. (Distinct from the Lean-only
    `wf_config_wf_frame` of TypePreservation.lean, which was renamed in bundle20 to free this name.) -/
theorem wf_config_frame (s : store) (f' : frame) (n : n) (f : frame) (es : List admininstr) :
    wf_config (config.mk_config (state.mk_state s f') [admininstr.FRAME_ n f es]) →
    wf_config (config.mk_config (state.mk_state s f') es) ∧
      wf_config (config.mk_config (state.mk_state s f) es) := by
  intro h
  cases h with
  | config_case_0 _ _ hst hall =>
    have hfr : wf_admininstr (admininstr.FRAME_ n f es) := hall _ (List.mem_singleton_self _)
    cases hfr with
    | admininstr_case_72 _ _ _ hwff hes =>
      cases hst with
      | state_case_0 _ _ hwfs hwff' =>
        exact ⟨wf_config.config_case_0 _ es (wf_state.state_case_0 s f' hwfs hwff') hes,
               wf_config.config_case_0 _ es (wf_state.state_case_0 s f hwfs hwff) hes⟩

/-- Rocq `type_progress.v:885` `frame_t_context_return_empty`. A frame's typing context has no
    return type. -/
theorem frame_t_context_return_empty (s : store) (f : frame) (C : context) :
    Frame_ok s f C →
    C.RETURN = none := by
  intro hframe
  cases hframe with
  | mk_Frame_ok _ _ _ C0 hminst _ _ _ _ _ _ =>
    cases hminst
    rfl

/-- Rocq `type_progress.v:895` `Admin_instrs_ok_cons`. A typing of `[e] ++ es` splits, up to a
    common stack prefix `ts`, into typings of `[e]` and of `es` that compose. -/
theorem Admin_instrs_ok_cons (s : store) (C : context) (es : List admininstr) (e : admininstr)
    (ts1 ts2 : List valtype) :
    Instrs_ok2 s C ([e] ++ es) (mkFunctype ts1 ts2) →
    ∃ (ts ts1' ts2' ts3 : List valtype),
      ts1 = ts ++ ts1' ∧
      ts2 = ts ++ ts2' ∧
      Instrs_ok2 s C [e] (mkFunctype ts1' ts3) ∧
      Instrs_ok2 s C es (mkFunctype ts3 ts2') := by
  intro hadmin
  obtain ⟨t3s, h1, h2⟩ := ais_seq_typing_inversion s C es e ts1 ts2 hadmin
  exact ⟨[], ts1, ts2, t3s, rfl, rfl, h2, h1⟩

/-- Rocq `type_progress.v:912` `Admin_instrs_ok_cat`. A typing of `es1 ++ es2` splits, up to a
    common stack prefix `ts`, into typings of `es1` and of `es2` that compose. -/
theorem Admin_instrs_ok_cat (s : store) (C : context) (es1 es2 : List admininstr)
    (ts1 ts2 : List valtype) :
    Instrs_ok2 s C (es1 ++ es2) (mkFunctype ts1 ts2) →
    ∃ (ts ts1' ts2' ts3 : List valtype),
      ts1 = ts ++ ts1' ∧
      ts2 = ts ++ ts2' ∧
      Instrs_ok2 s C es1 (mkFunctype ts1' ts3) ∧
      Instrs_ok2 s C es2 (mkFunctype ts3 ts2') := by
  induction es1 generalizing ts1 ts2 with
  | nil =>
    intro hadmin
    obtain ⟨hWfC, hWfS, _⟩ := ainstrs_ok_context_store_wf s C _ _ hadmin
    refine ⟨[], ts1, ts2, ts1, rfl, rfl, ?_, by simpa using hadmin⟩
    have hf := Instrs_ok2.Instrs_ok2_frame s C [] ts1 [] [] (Instrs_ok2.empty s C hWfS hWfC) hWfS hWfC
      (by intro x hx; simp at hx)
    simpa [mkFunctype] using hf
  | cons e1 es1' ih =>
    intro hadmin
    obtain ⟨hWfC, hWfS, _⟩ := ainstrs_ok_context_store_wf s C _ _ hadmin
    have hadmin' : Instrs_ok2 s C ([e1] ++ (es1' ++ es2)) (mkFunctype ts1 ts2) := hadmin
    obtain ⟨ts, ts1', ts2', ts3, Ets1, Ets2, Hadmin1, Hadmin2⟩ :=
      Admin_instrs_ok_cons s C (es1' ++ es2) e1 ts1 ts2 hadmin'
    obtain ⟨ts', ts1'', ts2'', ts3', Ets1', Ets2', Hadmin1', Hadmin2'⟩ := ih ts3 ts2' Hadmin2
    have hwf1 := (ainstrs_ok_context_store_wf s C [e1] _ Hadmin1).2.2
    have hwf_es1' := (ainstrs_ok_context_store_wf s C es1' _ Hadmin1').2.2
    have hwf_es2 := (ainstrs_ok_context_store_wf s C es2 _ Hadmin2').2.2
    have hf1 : Instrs_ok2 s C es1' (mkFunctype (ts' ++ ts1'') (ts' ++ ts3')) :=
      Instrs_ok2.Instrs_ok2_frame s C es1' ts' ts1'' ts3' Hadmin1' hWfS hWfC hwf_es1'
    have hf2 : Instrs_ok2 s C es2 (mkFunctype (ts' ++ ts3') (ts' ++ ts2'')) :=
      Instrs_ok2.Instrs_ok2_frame s C es2 ts' ts3' ts2'' Hadmin2' hWfS hWfC hwf_es2
    rw [← Ets1'] at hf1
    rw [← Ets2'] at hf2
    exact ⟨ts, ts1', ts2', ts' ++ ts3', Ets1, Ets2,
      Instrs_ok2.seq s C [e1] es1' ts1' (ts' ++ ts3') ts3 Hadmin1 hf1 hWfS hWfC hwf1 hwf_es1', hf2⟩

/-- Rocq `type_progress.v:949` `Admin_instrs_ok_all`. Every member of a typed sequence is typed at
    some function type. Rocq's boolean membership `e \in es` is Lean's `e ∈ es`. -/
theorem Admin_instrs_ok_all (s : store) (C : context) (es : List admininstr) (ts1 ts2 : List valtype) :
    Instrs_ok2 s C es (mkFunctype ts1 ts2) →
    ∀ (e : admininstr), e ∈ es → ∃ (ts1' ts2' : List valtype), Instr_ok2 s C e (mkFunctype ts1' ts2') := by
  induction es generalizing ts1 ts2 with
  | nil =>
    intro _ e he
    simp at he
  | cons e' es' ih =>
    intro hadmin e he
    have hadmin' : Instrs_ok2 s C ([e'] ++ es') (mkFunctype ts1 ts2) := hadmin
    obtain ⟨ts, ts1', ts2', ts3, Ets1, Ets2, Hadmin1, Hadmin2⟩ :=
      Admin_instrs_ok_cons s C es' e' ts1 ts2 hadmin'
    rcases List.mem_cons.mp he with rfl | hin
    · obtain ⟨t1s_sup, t2s_sub, hty, _⟩ := ais_single_typing_inversion' s C e ts1' ts3 Hadmin1
      exact ⟨t1s_sup, t2s_sub, hty⟩
    · exact ih ts3 ts2' Hadmin2 e hin

/-- Rocq `type_progress.v:972` `s_typing_lf_br'`. A sequence typed in a frame's context (no labels)
    contains no top-level `BR l`. -/
theorem s_typing_lf_br' (s : store) (f : frame) (C : context) (es : List admininstr)
    (t1s t2s : List valtype) (l : labelidx) :
    Frame_ok s f C →
    Instrs_ok2 s C es (mkFunctype t1s t2s) →
    Forall (fun e => e ≠ admininstr.BR l) es := by
  intro hframe
  induction es generalizing t1s t2s with
  | nil =>
    intro _ e he
    simp at he
  | cons a es ih =>
    intro hadmin e he
    have hadmin' : Instrs_ok2 s C ([a] ++ es) (mkFunctype t1s t2s) := hadmin
    obtain ⟨t3s, HType2, HType1⟩ := ais_seq_typing_inversion s C es a t1s t2s hadmin'
    rcases List.mem_cons.mp he with rfl | hin
    · intro H
      subst H
      have hbr : Instrs_ok2 s C [admininstr_instr (instr.BR l)] (mkFunctype t1s t3s) := HType1
      have hbr' := revert_to_instr_from_ai s C (instr.BR l) t1s t3s hbr
      obtain ⟨t1s_sup, t2s_sub, hty, _⟩ := instrs_single_typing_inversion C (instr.BR l) t1s t3s hbr'
      cases hty
      have hlt : proj_uN_0 l < C.LABELS.length := by assumption
      rw [frame_t_context_label_empty s f C hframe] at hlt
      simp at hlt
    · exact ih t3s t2s HType2 e hin

/-- Rocq `type_progress.v:1009` `s_typing_lf_br`. As `s_typing_lf_br'`, for a sequence typed in the
    frame's context with a return type prepended (`prepend_return C rt`, HelperLemmas.lean). -/
theorem s_typing_lf_br (s : store) (f : frame) (C : context) (rt : resulttype) (es : List admininstr)
    (t1s t2s : List valtype) (l : labelidx) :
    Frame_ok s f C →
    Instrs_ok2 s (prepend_return C rt) es (mkFunctype t1s t2s) →
    Forall (fun e => e ≠ admininstr.BR l) es := by
  intro Hframe
  induction es generalizing t1s t2s with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons a es ih =>
    intro Hadmin e he
    obtain ⟨t3s, HType1, HType2⟩ := ais_seq_typing_inversion s _ es a t1s t2s Hadmin
    rcases List.mem_cons.mp he with rfl | he'
    · intro Hbr
      subst Hbr
      have h1 := revert_to_instr_from_ai s _ (instr.BR l) t1s t3s HType2
      obtain ⟨t1s_sup, t2s_sub, HType2', HSub⟩ := instrs_single_typing_inversion _ (instr.BR l) t1s t3s h1
      have Hlab := frame_t_context_label_empty s f C Hframe
      cases HType2'
      rename_i _ _ _ _ hlt _
      have : (prepend_return C rt).LABELS = [] := by
        show ([] : List resulttype) ++ C.LABELS = []
        rw [Hlab]; rfl
      rw [this] at hlt
      simp at hlt
    · exact ih t3s t2s HType1 e he'

/-- Rocq `type_progress.v:1045` `s_typing_lf_return`. A sequence typed in a frame's context (no
    return type) contains no top-level `RETURN`. -/
theorem s_typing_lf_return (s : store) (f : frame) (C : context) (es : List admininstr)
    (t1s t2s : List valtype) :
    Frame_ok s f C →
    Instrs_ok2 s C es (mkFunctype t1s t2s) →
    Forall (fun e => e ≠ admininstr.RETURN) es := by
  intro Hframe
  induction es generalizing t1s t2s with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons a es ih =>
    intro Hadmin e he
    obtain ⟨t3s, HType1, HType2⟩ := ais_seq_typing_inversion s _ es a t1s t2s Hadmin
    rcases List.mem_cons.mp he with rfl | he'
    · intro Hret
      subst Hret
      have h1 := revert_to_instr_from_ai s _ instr.RETURN t1s t3s HType2
      obtain ⟨t1s_sup, t2s_sub, HType2', HSub⟩ := instrs_single_typing_inversion _ instr.RETURN t1s t3s h1
      have Hr := frame_t_context_return_empty s f C Hframe
      cases HType2'
      rename_i _ _ _ hret _
      rw [Hr] at hret
      cases hret
    · exact ih t3s t2s HType1 e he'

/-- Rocq `type_progress.v:1072` `s_typing_not_lf_br'`. A sequence typed in a frame's context
    satisfies `not_lf_br`. -/
theorem s_typing_not_lf_br' (s : store) (f : frame) (C : context) (es : List admininstr)
    (t1s t2s : List valtype) :
    Frame_ok s f C →
    Instrs_ok2 s C es (mkFunctype t1s t2s) →
    not_lf_br es := by
  intro Hframe Hadmin vcs l es' Hcontra
  have Hes := s_typing_lf_br' s f C es t1s t2s l Hframe Hadmin
  clear Hframe Hadmin
  induction vcs generalizing es with
  | nil =>
    simp only [List.map_nil, List.nil_append] at Hcontra
    subst Hcontra
    exact Hes (admininstr.BR l) (List.mem_cons_self) rfl
  | cons v vcs ih =>
    cases es with
    | nil => simp at Hcontra
    | cons e es0 =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at Hcontra
      exact ih es0 Hcontra.2 (fun x hx => Hes x (List.mem_cons_of_mem _ hx))

/-- Rocq `type_progress.v:1094` `s_typing_not_lf_br`. A sequence typed in the frame's context with
    a return type prepended (`prepend_return C rt`) satisfies `not_lf_br`. -/
theorem s_typing_not_lf_br (s : store) (f : frame) (C : context) (rt : resulttype) (es : List admininstr)
    (t1s t2s : List valtype) :
    Frame_ok s f C →
    Instrs_ok2 s (prepend_return C rt) es (mkFunctype t1s t2s) →
    not_lf_br es := by
  intro Hframe Hadmin vcs l es' Hcontra
  have Hes := s_typing_lf_br s f C rt es t1s t2s l Hframe Hadmin
  clear Hframe Hadmin
  induction vcs generalizing es with
  | nil =>
    simp only [List.map_nil, List.nil_append] at Hcontra
    subst Hcontra
    exact Hes (admininstr.BR l) (List.mem_cons_self) rfl
  | cons v vcs ih =>
    cases es with
    | nil => simp at Hcontra
    | cons e es0 =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at Hcontra
      exact ih es0 Hcontra.2 (fun x hx => Hes x (List.mem_cons_of_mem _ hx))

/-- Rocq `type_progress.v:1116` `s_typing_not_lf_return`. A sequence typed in a frame's context
    satisfies `not_lf_return`. -/
theorem s_typing_not_lf_return (s : store) (f : frame) (C : context) (es : List admininstr)
    (t1s t2s : List valtype) :
    Frame_ok s f C →
    Instrs_ok2 s C es (mkFunctype t1s t2s) →
    not_lf_return es := by
  intro Hframe Hadmin vcs es' Hcontra
  have Hes := s_typing_lf_return s f C es t1s t2s Hframe Hadmin
  clear Hframe Hadmin
  induction vcs generalizing es with
  | nil =>
    simp only [List.map_nil, List.nil_append] at Hcontra
    subst Hcontra
    exact Hes admininstr.RETURN (List.mem_cons_self) rfl
  | cons v vcs ih =>
    cases es with
    | nil => simp at Hcontra
    | cons e es0 =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at Hcontra
      exact ih es0 Hcontra.2 (fun x hx => Hes x (List.mem_cons_of_mem _ hx))

/-- Rocq `type_progress.v:1137` `size_eq1_cat`. Two appends with equal-length prefixes are equal
    iff prefixes and suffixes are. Rocq's `|l1'| = |l2'|` (`N.of_nat (size _)`) is
    `l1'.length = l2'.length`; `A` is explicit, as in Rocq. -/
theorem size_eq1_cat (A : Type) (l1 l2 l1' l2' : List A) :
    l1'.length = l2'.length →
    l1' ++ l1 = l2' ++ l2 →
    l1' = l2' ∧ l1 = l2 := by
  intro Hsize Hcat
  exact List.append_inj Hcat Hsize

/-- Rocq `type_progress.v:1159` `br_reduce_extract_vs`. In a sequence typed from the empty stack
    of the shape `vcs ++ [BR 0] ++ es'`, the values before the `BR 0` split as `vcs1 ++ vcs2`
    with `vcs2` as long as the label type `ts = C.LABELS[0]!`. Rocq's `lookup_total (LABELS C) 0`
    is `C.LABELS[0]!`, and `|ts|` (`ts : resulttype` coerced to a list) is
    `(proj_list_0 valtype ts).length` (as in `t_progress_e_P1`). -/
theorem br_reduce_extract_vs (s : store) (C : context) (ts2 : List valtype) (ts : resulttype)
    (es : List admininstr) :
    (∃ (vcs : List val) (es' : List admininstr),
      es = List.map admininstr_val vcs ++ ([admininstr.BR (uN.mk_uN 0)] ++ es')) →
    Instrs_ok2 s C es (mkFunctype [] ts2) →
    C.LABELS[0]! = ts →
    (∃ (vcs1 vcs2 : List val) (es' : List admininstr),
      es = List.map admininstr_val vcs1 ++
        (List.map admininstr_val vcs2 ++ ([admininstr.BR (uN.mk_uN 0)] ++ es')) ∧
      vcs2.length = (proj_list_0 valtype ts).length) := by
  intro Hbr Hadmin Hlookup
  obtain ⟨vcs, es', Hbr⟩ := Hbr
  have Hadmin' := Hadmin
  rw [Hbr, ← List.append_assoc] at Hadmin'
  obtain ⟨ta, tb, tc, ts3, Ets1, Ets2, Hadmin1, Hadmin2⟩ :=
    Admin_instrs_ok_cat s C _ es' [] ts2 Hadmin'
  obtain ⟨Ets', Ets1'⟩ := List.append_eq_nil_iff.mp Ets1.symm
  subst Ets' Ets1'
  obtain ⟨td, te, tf, ts3', Ets1, Ets2', Hadmin1, Hadmin1'⟩ :=
    Admin_instrs_ok_cat s C _ [admininstr.BR (uN.mk_uN 0)] [] ts3 Hadmin1
  obtain ⟨Ets'', Ets1''⟩ := List.append_eq_nil_iff.mp Ets1.symm
  subst Ets'' Ets1''
  obtain ⟨t, Hsub, HValsok⟩ := ais_vals_typing_inversion s C vcs [] ts3' Hadmin1
  obtain ⟨t1', t2', Hai, Hsub0⟩ :=
    ais_single_typing_inversion s C (admininstr.BR (uN.mk_uN 0)) ts3' tf Hadmin1'
  unfold ai_principal_typing at Hai
  obtain ⟨t1s_, lab, t2s_, Hft, Hlab⟩ := Hai
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Hft
  obtain ⟨rfl, rfl⟩ := Hft
  have Hlab' : C.LABELS[0]? = some (list.mk_list lab) := Hlab
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp Hlab'
  have Hlab'' : C.LABELS[0]! = list.mk_list lab := by rw [getElem!_pos C.LABELS 0 hk]; exact he
  rw [Hlab''] at Hlookup
  subst Hlookup
  have Hsubr : ResulttypeSub t ts3' := (instrtype_sub_iff_resulttype_sub t ts3' []).mpr Hsub
  have Hnonbot := Vals_ok_non_bot s vcs t HValsok
  have Ht : t = ts3' := resulttype_sub_non_bot t ts3' Hnonbot Hsubr
  subst Ht
  obtain ⟨tsa, tsb, ts11_sub, ts12_sup, E1, E2, Hs1, Hs2, Hs3⟩ := Hsub0
  subst E1
  have Hs12 := resulttype_sub_app tsa ts11_sub tsb (t1s_ ++ lab) Hs1 Hs2
  have Heq := resulttype_sub_non_bot _ _ Hnonbot Hs12
  have Hlen : tsa.length = tsb.length := by
    cases Hs1 with
    | mk_Resulttype_sub _ _ hlen _ => exact hlen
  obtain ⟨Hts, H2⟩ := size_eq1_cat valtype ts11_sub (t1s_ ++ lab) tsa tsb Hlen Heq
  subst Hts H2
  have Hlenv := HValsok.1
  refine ⟨vcs.take (tsa ++ t1s_).length, vcs.drop (tsa ++ t1s_).length, es', ?_, ?_⟩
  · rw [Hbr]
    simp only [← List.append_assoc, ← List.map_append, List.take_append_drop]
  · show (vcs.drop (tsa ++ t1s_).length).length = lab.length
    simp only [List.length_drop, List.length_append] at Hlenv ⊢
    omega

/-- Rocq `type_progress.v:1221` `return_reduce_extract_vs`. In a sequence typed from the empty stack
    of the shape `vcs ++ [RETURN] ++ es'`, the values before the `RETURN` split as `vcs1 ++ vcs2`
    with `vcs2` as long as the return type `t` (`C.RETURN = some t`). Rocq's `size t`
    (`t : resulttype` coerced to a list) is `(proj_list_0 valtype t).length`. -/
theorem return_reduce_extract_vs (s : store) (C : context) (ts2 : List valtype) (t : resulttype)
    (es : List admininstr) :
    (∃ (vcs : List val) (es' : List admininstr),
      es = List.map admininstr_val vcs ++ ([admininstr.RETURN] ++ es')) →
    Instrs_ok2 s C es (mkFunctype [] ts2) →
    C.RETURN = some t →
    (∃ (vcs1 vcs2 : List val) (es' : List admininstr),
      es = List.map admininstr_val vcs1 ++
        (List.map admininstr_val vcs2 ++ ([admininstr.RETURN] ++ es')) ∧
      vcs2.length = (proj_list_0 valtype t).length) := by
  intro hret hadmin hlookup
  obtain ⟨vcs, es', hes⟩ := hret
  subst hes
  obtain ⟨x3, hV, hrest⟩ := ais_composition_typing s C (List.map admininstr_val vcs)
    ([admininstr.RETURN] ++ es') [] ts2 hadmin
  obtain ⟨x4, _, hRET⟩ := ais_seq_typing_inversion s C es' admininstr.RETURN x3 ts2 hrest
  obtain ⟨vts, hsubV, hvok⟩ := ais_vals_typing_inversion s C vcs [] x3 hV
  obtain ⟨u1, u2, hpt, hsubR⟩ := ais_single_typing_inversion s C admininstr.RETURN x3 x4 hRET
  unfold ai_principal_typing at hpt
  obtain ⟨t1s, tsr, t2s, heq, hr, _⟩ := hpt
  unfold mkFunctype at heq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at heq
  obtain ⟨e1, e2⟩ := heq
  rw [e1, e2] at hsubR
  rw [hlookup] at hr
  have ht : t = list.mk_list tsr := Option.some.inj hr
  subst ht
  simp only [proj_list_0]
  obtain ⟨hl1, _⟩ := hvok
  have hl2 := resulttype_sub_size_eq _ _ ((instrtype_sub_iff_resulttype_sub vts x3 []).mpr hsubV)
  obtain ⟨tp1', tp1, ts1', ts2'', h1e1, h1e2, h1s1, h1s2, h1s3⟩ := hsubR
  have hl3 := resulttype_sub_size_eq _ _ h1s2
  have hx3 : x3.length = tp1'.length + ts1'.length := by rw [h1e1]; simp
  simp only [List.length_append] at hl3
  have hlen : tsr.length ≤ vcs.length := by omega
  refine ⟨vcs.take (vcs.length - tsr.length), vcs.drop (vcs.length - tsr.length), es', ?_, ?_⟩
  · rw [← List.append_assoc (List.map admininstr_val (List.take _ vcs)), ← List.map_append,
      List.take_append_drop]
  · simp only [List.length_drop]
    omega

/-- Rocq `type_progress.v:1280` `lookup_types`. Under `Moduleinst_ok s f.MODULE C`, a type lookup
    in the updated context `upd_local_label_return C loc lab ret` agrees with the lookup in the
    frame's module instance (`lookup_total l idx` written `l[idx]!`). -/
theorem lookup_types (s : store) (f : frame) (C : context) (loc : List valtype)
    (lab : List resulttype) (ret : Option resulttype) (idx : Nat) :
    Moduleinst_ok s f.MODULE C →
    (upd_local_label_return C loc lab ret).TYPES[idx]! = f.MODULE.TYPES[idx]! := by
  intro h
  have hT : C.TYPES = f.MODULE.TYPES := by
    generalize f.MODULE = m at h ⊢
    cases h
    rfl
  show C.TYPES[idx]! = f.MODULE.TYPES[idx]!
  rw [hT]

/-- Rocq `type_progress.v:1290` `funcs_size`. Under `Moduleinst_ok s f.MODULE C`, the updated
    context has as many functions as the frame's module instance (Rocq `|l|` is `l.length`). No
    length premise is needed: Lean's generated `Moduleinst_ok` states
    `funcaddr_lst.length = functype_F_lst.length` explicitly. -/
theorem funcs_size (s : store) (f : frame) (C : context) (loc : List valtype)
    (lab : List resulttype) (ret : Option resulttype) :
    Moduleinst_ok s f.MODULE C →
    (upd_local_label_return C loc lab ret).FUNCS.length = f.MODULE.FUNCS.length := by
  intro h
  show C.FUNCS.length = f.MODULE.FUNCS.length
  exact ((Moduleinst_ok_lengths s f.MODULE C h).2.1).symm

/-- Rocq `type_progress.v:1300` `admininstr_CONST_eq_arg`. `admininstr.CONST` is injective in its
    numeric argument. -/
theorem admininstr_CONST_eq_arg (t : numtype) (i1 i2 : num_) :
    admininstr.CONST t i1 = admininstr.CONST t i2 →
    i1 = i2 := by
  intro h
  injection h

/-- Rocq `type_progress.v:1308` `typeof_non_bot`. The type of a value is never `BOT`. -/
theorem typeof_non_bot (v : val) :
    typeof v ≠ valtype.BOT := by
  cases v with
  | CONST t _ => cases t <;> simp [typeof, valtype_numtype]
  | VCONST t _ => cases t; simp [typeof, valtype_vectype]
  | REF_NULL t => cases t <;> simp [typeof, valtype_reftype]
  | REF_FUNC_ADDR _ => simp [typeof]
  | REF_HOST_ADDR _ => simp [typeof]

/-- Rocq `type_progress.v:1317` `typeof_vals_non_bot`. The types of a list of values contain no
    `BOT`. -/
theorem typeof_vals_non_bot (vs : List val) (ts : List valtype) :
    List.map typeof vs = ts →
    Forall (fun t => t ≠ valtype.BOT) ts := by
  intro h
  subst h
  intro t ht
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
  exact typeof_non_bot v

/-- Rocq `type_progress.v:1333` `unop_not_none`. A well-formed unary operator applied to a
    well-formed number of the same type is defined (`fun_unop_` does not return `none`). -/
theorem unop_not_none (nt : numtype) (u : unop_) (n1 : num_) :
    wf_num_ nt n1 →
    wf_unop_ nt u →
    fun_unop_ nt u n1 ≠ none := by
  intro hn hu hneq
  cases hn with
  | num__case_0 vI vx h1 h2 h3 =>
    cases hu with
    | unop__case_0 vI0 vx0 h4 =>
      subst h3
      cases vI <;> cases vI0 <;> cases vx0 <;> simp [numtype_Inn, fun_unop_] at h4 hneq
    | unop__case_1 vF vx0 h4 =>
      subst h3
      cases vI <;> cases vF <;> simp [numtype_Inn, numtype_Fnn] at h4
  | num__case_1 vF vx h1 h3 =>
    cases hu with
    | unop__case_0 vI0 vx0 h4 =>
      subst h3
      cases vF <;> cases vI0 <;> simp [numtype_Inn, numtype_Fnn] at h4
    | unop__case_1 vF0 vx0 h4 =>
      subst h3
      cases vF <;> cases vF0 <;> cases vx0 <;> simp [numtype_Fnn, fun_unop_] at h4 hneq

/-- Rocq `type_progress.v:1348` `two_pow_pos`. `2 ^ v_N` is positive (Rocq: in binary `N`). -/
theorem two_pow_pos (v_N : Nat) : 0 < 2 ^ v_N := by
  exact Nat.two_pow_pos v_N

/-- Rocq `type_progress.v:1351` `Zsub1_toN`. Truncated subtraction of one through `Int`:
    `Z.to_N (Z.of_N m - 1) = m - 1` (Rocq's `Z.to_N` coercion is `Int.toNat`; Rocq's
    `(1%num : Z)`, the `N` literal cast to `Z`, is convertible to `1%Z` and is written `(1 : Int)`,
    the form the generated Lean code uses, e.g. `Int.toNat ((v_N : Int) - (1 : Int))`). -/
theorem Zsub1_toN (m : Nat) : Int.toNat ((m : Int) - (1 : Int)) = m - 1 := by
  omega

/-- Rocq `type_progress.v:1357` `wf_uN_lt`. A well-formed `uN(N)` value is below `2 ^ N`. -/
theorem wf_uN_lt (v_N : N) (i : Nat) : wf_uN v_N (uN.mk_uN i) → i < 2 ^ v_N := by
  intro h
  cases h with
  | uN_case_0 _ hb =>
    obtain ⟨_, hle⟩ := hb
    have hp : 0 < 2 ^ v_N := Nat.two_pow_pos v_N
    have hc : ((2 ^ v_N : Nat) : Int) = (2 : Int) ^ v_N := by push_cast; rfl
    omega

/-- Rocq `type_progress.v:1368` `two_pow_succ`. For `m ≠ 0`, `2 ^ m = 2 * 2 ^ (m - 1)` (truncated
    subtraction, as Rocq's `N.sub`). -/
theorem two_pow_succ (m : Nat) : m ≠ 0 →
    2 ^ m = 2 * 2 ^ (m - 1) := by
  intro hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.pow_succ, Nat.add_sub_cancel]
  omega

/-- Rocq `type_progress.v:1376` `signed_total`. `signed_` is total on `[0, 2 ^ N)`, and its result
    lies in `[0 - 2 ^ (N - 1), 2 ^ (N - 1))` (Rocq's `N → Z` coercion is the `Nat → Int` cast). -/
theorem signed_total (v_N : N) (i : Nat) :
    i < 2 ^ v_N →
    ∃ z, fun_signed_ v_N i z ∧
      0 - ((2 ^ (v_N - 1) : Nat) : Int) ≤ z ∧
      z < ((2 ^ (v_N - 1) : Nat) : Int) := by
  intro hlt
  have hp : 0 < 2 ^ v_N := Nat.two_pow_pos v_N
  have hp1 : 0 < 2 ^ (v_N - 1) := Nat.two_pow_pos (v_N - 1)
  have e1 : Int.toNat ((v_N : Int) - (1 : Int)) = v_N - 1 := by omega
  have hc1 : ((2 ^ v_N : Nat) : Int) = (2 : Int) ^ v_N := by push_cast; rfl
  have hc2 : ((2 ^ (v_N - 1) : Nat) : Int) = (2 : Int) ^ (v_N - 1) := by push_cast; rfl
  by_cases E : i < 2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))
  · refine ⟨(i : Int), fun_signed_.fun_signed__case_0 v_N i E, ?_, ?_⟩
    · rw [e1] at E; omega
    · rw [e1] at E; omega
  · rw [e1] at E
    have hge : 2 ^ (v_N - 1) ≤ i := by omega
    have hN0 : v_N ≠ 0 := by
      intro h0; subst h0; simp at hlt hge; omega
    have hd := two_pow_succ v_N hN0
    refine ⟨(i : Int) - (2 : Int) ^ v_N, fun_signed_.fun_signed__case_1 v_N i ⟨by rw [e1]; exact hge, hlt⟩, ?_, ?_⟩
    · omega
    · omega

/-- Rocq `type_progress.v:1405` `invsigned_total`. `inv_signed_` is total on
    `[0 - 2 ^ (N - 1), 2 ^ (N - 1))`. -/
theorem invsigned_total (v_N : N) (z : Int) :
    0 - ((2 ^ (v_N - 1) : Nat) : Int) ≤ z →
    z < ((2 ^ (v_N - 1) : Nat) : Int) →
    ∃ ret, fun_inv_signed_ v_N z ret := by
  intro hlo hhi
  have e1 : Int.toNat ((v_N : Int) - (1 : Int)) = v_N - 1 := by omega
  have hc1 : ((2 ^ v_N : Nat) : Int) = (2 : Int) ^ v_N := by push_cast; rfl
  have hc2 : ((2 ^ (v_N - 1) : Nat) : Int) = (2 : Int) ^ (v_N - 1) := by push_cast; rfl
  by_cases Ez : 0 ≤ z
  · refine ⟨Int.toNat z, fun_inv_signed_.fun_inv_signed__case_0 v_N z ⟨Ez, ?_⟩⟩
    rw [e1]; omega
  · refine ⟨Int.toNat (z + (2 : Int) ^ v_N), fun_inv_signed_.fun_inv_signed__case_1 v_N z ⟨?_, ?_⟩⟩
    · rw [e1]; omega
    · omega

/-- Rocq `type_progress.v:1425` `Zquot_abs_le`. Truncating division does not increase an absolute
    bound (Rocq `Z.abs` is Mathlib's `|·|`; Rocq `Z.quot` is `Int.tdiv`, as in `truncz_quot`,
    HelperLemmas.lean). -/
theorem Zquot_abs_le (a b p : Int) : b ≠ 0 → 0 ≤ p →
    |a| ≤ p → |Int.tdiv a b| ≤ p := by
  intro hb hp ha
  have h1 := Int.natAbs_tdiv_le_natAbs a b
  rw [Int.abs_eq_natAbs] at ha ⊢
  omega

/-- Rocq `type_progress.v:1435` `Zquot_ge_inv`. If `|a| ≤ p`, `1 ≤ p` and the truncated quotient
    `a / b` reaches `p`, then `b = 1 ∧ a = p` or `b = -1 ∧ a = -p` (`Z.quot` is `Int.tdiv`). -/
theorem Zquot_ge_inv (a b p : Int) : b ≠ 0 → 1 ≤ p →
    |a| ≤ p → p ≤ Int.tdiv a b →
    (b = 1 ∧ a = p) ∨ (b = -1 ∧ a = -p) := by
  intro Hb Hp Ha Hge
  have Ha' := abs_le.mp Ha
  have Hcase : b = 1 ∨ b = -1 ∨ 2 ≤ |b| := by
    rcases lt_trichotomy b 0 with h | h | h
    · rw [abs_of_neg h]; omega
    · exact absurd h Hb
    · rw [abs_of_pos h]; omega
  rcases Hcase with Hb1 | Hbm1 | Hb2
  · subst Hb1
    rw [Int.tdiv_one] at Hge
    left
    exact ⟨rfl, by omega⟩
  · subst Hbm1
    right
    refine ⟨rfl, ?_⟩
    have Hop : Int.tdiv a (-1) = - Int.tdiv a 1 := Int.tdiv_neg a 1
    rw [Hop, Int.tdiv_one] at Hge
    omega
  · exfalso
    have H1 : (Int.tdiv a b).natAbs = Int.natAbs a / Int.natAbs b := Int.natAbs_tdiv a b
    rw [Int.abs_eq_natAbs] at Ha Hb2
    have H2 : Int.natAbs a / Int.natAbs b ≤ Int.natAbs a / 2 :=
      Nat.div_le_div_left (by omega) (by omega)
    omega

/-- Rocq `type_progress.v:1456` `wf_uN_lt'`. `wf_uN_lt` for an arbitrary `u : uN`; Rocq's
    coercion `(u :> N)` (instance `proj_uN_0_coercion`) is `proj_uN_0 u`. -/
theorem wf_uN_lt' (v_N : N) (u : uN) : wf_uN v_N u → proj_uN_0 u < 2 ^ v_N := by
  intro H
  exact iswf_uN_proj_lt H

/-- Rocq `type_progress.v:1459` `signed_nonzero`. `signed_` maps a nonzero input to a nonzero
    integer. -/
theorem signed_nonzero (v_N : N) (i : Nat) (z : Int) :
    fun_signed_ v_N i z → i ≠ 0 → z ≠ 0 := by
  intro H Hi
  cases H with
  | fun_signed__case_0 h => omega
  | fun_signed__case_1 h =>
    have h2 := h.2
    simp only [iswf_two_pow_cast] at *
    omega

/-- Rocq `type_progress.v:1467` `lt_wf_uN`. Converse of `wf_uN_lt`: `i < 2 ^ N` makes `mk_uN i`
    a well-formed `uN(N)`. -/
theorem lt_wf_uN (v_N : Nat) (i : Nat) : i < 2 ^ v_N → wf_uN v_N (uN.mk_uN i) := by
  intro H
  exact iswf_uN_of_lt H

/-- Rocq `type_progress.v:1475` `inv_signed_wf`. The result of `inv_signed_` is a well-formed
    `uN(N)`. -/
theorem inv_signed_wf (v_N : N) (z : Int) (m : Nat) :
    fun_inv_signed_ v_N z m → wf_uN v_N (uN.mk_uN m) := by
  intro H
  exact iswf_inv_signed H

/-- Rocq `type_progress.v:1485` `idiv_total`. `idiv_` is total on well-formed `iN(N)` operands
    (the result is an `Option iN`; `none` for division by zero / signed overflow). -/
theorem idiv_total (v_N : N) (v_sx : sx) (i1 i2 : uN) :
    wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_idiv_ v_N v_sx i1 i2 r := by
  intro Hw1 Hw2
  have Hl1 := wf_uN_lt' _ _ Hw1
  have Hl2 := wf_uN_lt' _ _ Hw2
  obtain ⟨n1⟩ := i1
  obtain ⟨n2⟩ := i2
  simp only [proj_uN_0] at Hl1 Hl2
  cases v_sx with
  | U =>
    cases n2 with
    | zero => exact ⟨_, fun_idiv_.fun_idiv__case_0 _ _⟩
    | succ p2 =>
      refine ⟨_, fun_idiv_.fun_idiv__case_1 _ _ _ ?_⟩
      apply lt_wf_uN
      have Hq := truncz_quot (n1 : Int) ((p2 + 1 : Nat) : Int) (by omega)
      simp only [Int.cast_natCast] at Hq
      simp only [proj_uN_0]
      rw [Hq]
      have Hq0 : 0 ≤ Int.tdiv (n1 : Int) ((p2 + 1 : Nat) : Int) :=
        Int.tdiv_nonneg (by omega) (by omega)
      have Hq1 : Int.tdiv (n1 : Int) ((p2 + 1 : Nat) : Int) ≤ (n1 : Int) :=
        Int.tdiv_le_self _ (by omega)
      omega
  | S =>
    cases n2 with
    | zero => exact ⟨_, fun_idiv_.fun_idiv__case_2 _ _⟩
    | succ p2 =>
      obtain ⟨z1, Hs1, Hlo1, Hhi1⟩ := signed_total v_N n1 Hl1
      obtain ⟨z2, Hs2, Hlo2, Hhi2⟩ := signed_total v_N (p2 + 1) Hl2
      have Hz2 : z2 ≠ 0 := signed_nonzero _ _ _ Hs2 (by omega)
      have HPp : 0 < 2 ^ (v_N - 1) := Nat.two_pow_pos _
      have HP1 : (1 : Int) ≤ ((2 ^ (v_N - 1) : Nat) : Int) := by omega
      have Ha1 : |z1| ≤ ((2 ^ (v_N - 1) : Nat) : Int) := by
        rw [abs_le]; omega
      by_cases Hq : Int.tdiv z1 z2 < ((2 ^ (v_N - 1) : Nat) : Int)
      · have Hab := Zquot_abs_le z1 z2 ((2 ^ (v_N - 1) : Nat) : Int) Hz2 (by omega) Ha1
        have Hab' := abs_le.mp Hab
        obtain ⟨r, Hr⟩ := invsigned_total v_N (Int.tdiv z1 z2) (by omega) Hq
        refine ⟨some (uN.mk_uN r), fun_idiv_.fun_idiv__case_4 _ _ _ z2 z1 r Hs2 Hs1 ?_
          (inv_signed_wf _ _ _ Hr)⟩
        rw [truncz_quot z1 z2 Hz2]
        exact Hr
      · have Hge : ((2 ^ (v_N - 1) : Nat) : Int) ≤ Int.tdiv z1 z2 := by omega
        have Hinv := Zquot_ge_inv z1 z2 _ Hz2 HP1 Ha1 Hge
        refine ⟨none, fun_idiv_.fun_idiv__case_3 _ _ _ z2 z1 Hs2 Hs1 ?_⟩
        have Hn : Int.toNat ((v_N : Int) - 1) = v_N - 1 := by omega
        rw [Hn]
        rcases Hinv with ⟨Hb, Ha⟩ | ⟨Hb, Ha⟩
        · rw [Hb, Ha]
          push_cast
          simp
        · rw [Hb, Ha]
          push_cast
          simp

/-- Rocq `type_progress.v:1535` `irem_total`. `irem_` is total on well-formed `iN(N)` operands. -/
theorem irem_total (v_N : N) (v_sx : sx) (i1 i2 : uN) :
    wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_irem_ v_N v_sx i1 i2 r := by
  intro Hw1 Hw2
  have Hl1 := wf_uN_lt' _ _ Hw1
  have Hl2 := wf_uN_lt' _ _ Hw2
  cases v_sx with
  | U => exact ⟨_, fun_irem_.fun_irem__case_1 _ _ _⟩
  | S =>
    cases i2 with
    | mk_uN n2 =>
      cases n2 with
      | zero => exact ⟨_, fun_irem_.fun_irem__case_2 _ _⟩
      | succ p2 =>
        obtain ⟨z1, Hs1, Hlo1, Hhi1⟩ := signed_total v_N (proj_uN_0 i1) Hl1
        obtain ⟨z2, Hs2, Hlo2, Hhi2⟩ := signed_total v_N (proj_uN_0 (uN.mk_uN (p2 + 1))) Hl2
        have Hz2 : z2 ≠ 0 := signed_nonzero _ _ _ Hs2 (by simp [proj_uN_0])
        have HPp : 0 < 2 ^ (v_N - 1) := Nat.two_pow_pos _
        have Hrem : z1 - z2 * Int.tdiv z1 z2 = Int.tmod z1 z2 := (Int.tmod_def z1 z2).symm
        have Hbnd : (Int.tmod z1 z2).natAbs < z2.natAbs := by
          rw [Int.natAbs_tmod]
          exact Nat.mod_lt _ (Int.natAbs_pos.mpr Hz2)
        obtain ⟨r, Hr⟩ : ∃ ret, fun_inv_signed_ v_N
            (z1 - z2 * truncz ((z1 : Rat) / (z2 : Rat))) ret := by
          rw [truncz_quot _ _ Hz2, Hrem]
          apply invsigned_total
          · omega
          · omega
        exact ⟨some (uN.mk_uN r), fun_irem_.fun_irem__case_3 _ _ _ z1 z2 z2 z1 r Hs2 Hs1 Hr
          ⟨rfl, rfl⟩⟩

/-- Rocq `type_progress.v:1562` `ilt_total`. `ilt_` is total on well-formed `iN(N)` operands. -/
theorem ilt_total (v_N : N) (v_sx : sx) (i1 i2 : uN) : wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_ilt_ v_N v_sx i1 i2 r := by
  intro Hw1 Hw2
  cases v_sx with
  | U => exact ⟨_, fun_ilt_.fun_ilt__case_0 _ _ _⟩
  | S =>
    obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ Hw1)
    obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ Hw2)
    exact ⟨_, fun_ilt_.fun_ilt__case_1 _ _ _ _ _ Hs2 Hs1⟩

/-- Rocq `type_progress.v:1572` `igt_total`. `igt_` is total on well-formed `iN(N)` operands. -/
theorem igt_total (v_N : N) (v_sx : sx) (i1 i2 : uN) : wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_igt_ v_N v_sx i1 i2 r := by
  intro Hw1 Hw2
  cases v_sx with
  | U => exact ⟨_, fun_igt_.fun_igt__case_0 _ _ _⟩
  | S =>
    obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ Hw1)
    obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ Hw2)
    exact ⟨_, fun_igt_.fun_igt__case_1 _ _ _ _ _ Hs2 Hs1⟩

/-- Rocq `type_progress.v:1582` `ile_total`. `ile_` is total on well-formed `iN(N)` operands. -/
theorem ile_total (v_N : N) (v_sx : sx) (i1 i2 : uN) : wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_ile_ v_N v_sx i1 i2 r := by
  intro Hw1 Hw2
  cases v_sx with
  | U => exact ⟨_, fun_ile_.fun_ile__case_0 _ _ _⟩
  | S =>
    obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ Hw1)
    obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ Hw2)
    exact ⟨_, fun_ile_.fun_ile__case_1 _ _ _ _ _ Hs2 Hs1⟩

/-- Rocq `type_progress.v:1592` `ige_total`. `ige_` is total on well-formed `iN(N)` operands. -/
theorem ige_total (v_N : N) (v_sx : sx) (i1 i2 : uN) : wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_ige_ v_N v_sx i1 i2 r := by
  intro Hw1 Hw2
  cases v_sx with
  | U => exact ⟨_, fun_ige_.fun_ige__case_0 _ _ _⟩
  | S =>
    obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ Hw1)
    obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ Hw2)
    exact ⟨_, fun_ige_.fun_ige__case_1 _ _ _ _ _ Hs2 Hs1⟩

-- Ltac `num_shapes` (type_progress.v:1602) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

/-- Rocq `type_progress.v:1612` `idiv_wf`. Any result of `idiv_` is a well-formed `uN(N)` (`idiv_`
    has no generated `_is_wf` lemma; its clauses carry the result's wf premise). Rocq's
    `option_to_list r` is `Option.toList r`. -/
theorem idiv_wf (v_N : N) (v_sx : sx) (a b : iN) (r : Option iN) :
    fun_idiv_ v_N v_sx a b r → Forall (fun x => wf_uN v_N x) (Option.toList r) := by
  intro H
  cases H with
  | fun_idiv__case_0 => exact iswf_Forall_nil _
  | fun_idiv__case_1 _ _ h => exact iswf_Forall_cons h (iswf_Forall_nil _)
  | fun_idiv__case_2 => exact iswf_Forall_nil _
  | fun_idiv__case_3 => exact iswf_Forall_nil _
  | fun_idiv__case_4 _ _ _ _ _ _ _ _ h => exact iswf_Forall_cons h (iswf_Forall_nil _)

/-- Rocq `type_progress.v:1621` `wf_uN_mk_proj`. Re-wrapping the projection of a well-formed `uN`
    keeps it well-formed; Rocq's coercion `(x :> N)` is `proj_uN_0 x`. -/
theorem wf_uN_mk_proj (v_N : N) (x : uN) : wf_uN v_N x → wf_uN v_N (uN.mk_uN (proj_uN_0 x)) := by
  intro H
  cases x with
  | mk_uN i => exact H

/-- Rocq `type_progress.v:1624` `wf_fN_num_`. Well-formed `fN` values wrap to well-formed
    `num_.mk_num__1 F x` numbers. -/
theorem wf_fN_num_ (F : Fnn) (l : List fN) :
    Forall (fun x => wf_fN (sizenn (numtype_Fnn F)) x) l →
    Forall (fun x => wf_num_ (numtype_Fnn F) (num_.mk_num__1 F x)) l := by
  intro Hl x hx
  exact wf_num_.num__case_1 _ _ _ (Hl x hx) rfl

/-- Rocq `type_progress.v:1629` `wf_opt_num_`. A well-formed optional `iN` result wraps to
    well-formed `num_.mk_num__0 I x` numbers, both pointwise and through
    `list_ num_ (Option.map ..)` (Rocq `option_to_list`/`option_map` are `Option.toList`/`Option.map`). -/
theorem wf_opt_num_ (I : Inn) (o : Option iN) :
    Forall (fun x => wf_uN (sizenn (numtype_Inn I)) x) (Option.toList o) →
    Forall (fun x => wf_num_ (numtype_Inn I) (num_.mk_num__0 I x)) (Option.toList o) ∧
    Forall (fun x => wf_num_ (numtype_Inn I) x) (list_ num_ (Option.map (fun y => num_.mk_num__0 I y) o)) := by
  intro Ho
  cases o with
  | none => exact ⟨fun x hx => by simp at hx, fun x hx => by simp [list_] at hx⟩
  | some x =>
    have Hx : wf_num_ (numtype_Inn I) (num_.mk_num__0 I x) := by
      cases I <;> exact wf_num_.num__case_0 _ _ _ (by decide) (Ho x (by simp)) rfl
    constructor
    · intro y hy
      simp at hy
      subst hy
      exact Hx
    · intro y hy
      simp [list_] at hy
      subst hy
      exact Hx

-- Ltac `binop_wf` (type_progress.v:1641) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

/-- Rocq `type_progress.v:1663` `binop_total`. `binop_` is total on well-formed operands and a
    well-formed operator. -/
theorem binop_total (nt : numtype) (b : binop_) (n1 n2 : num_) :
    wf_num_ nt n1 → wf_num_ nt n2 → wf_binop_ nt b →
    ∃ lst, fun_binop_ nt b n1 n2 lst := by
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 hn2 hb
  rcases hb with ⟨I, bI, hI⟩ | ⟨F, bF, hF⟩
  · subst hI
    rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    rcases hn2 with ⟨I2, x2, _, hw2, h2⟩ | ⟨F2, x2, _, h2⟩
    swap
    · exact (numIF _ _ h2).elim
    obtain rfl := numI _ _ h2
    cases bI with
    | DIV sx =>
      cases I
      · obtain ⟨r, Hr⟩ := idiv_total _ sx x1 x2 hw1 hw2
        have Hw := idiv_wf _ _ _ _ _ Hr
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I32 r Hw
        exact ⟨_, fun_binop_.fun_binop__case_6 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1⟩
      · obtain ⟨r, Hr⟩ := idiv_total _ sx x1 x2 hw1 hw2
        have Hw := idiv_wf _ _ _ _ _ Hr
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I64 r Hw
        exact ⟨_, fun_binop_.fun_binop__case_7 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1⟩
    | REM sx =>
      cases I
      · obtain ⟨r, Hr⟩ := irem_total _ sx x1 x2 hw1 hw2
        have Hw := irem__is_wf _ _ _ _ _ _ Hr hw1 hw2 rfl
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I32 r Hw
        exact ⟨_, fun_binop_.fun_binop__case_8 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1⟩
      · obtain ⟨r, Hr⟩ := irem_total _ sx x1 x2 hw1 hw2
        have Hw := irem__is_wf _ _ _ _ _ _ Hr hw1 hw2 rfl
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I64 r Hw
        exact ⟨_, fun_binop_.fun_binop__case_9 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1⟩
    | _ =>
      cases I <;> apply Exists.intro <;> constructor <;>
        refine wf_num_.num__case_0 _ _ _ (by decide) ?_ rfl <;>
        first
          | exact iadd__is_wf _ _ _ _ hw1 hw2 rfl
          | exact isub__is_wf _ _ _ _ hw1 hw2 rfl
          | exact imul__is_wf _ _ _ _ hw1 hw2 rfl
          | exact iand__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ior__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ixor__is_wf _ _ _ _ hw1 hw2 rfl
          | exact irotl__is_wf _ _ _ _ hw1 hw2 rfl
          | exact irotr__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ishl_wf _ _ _ hw1
          | exact ishr_wf _ _ _ _ hw1
  · subst hF
    rcases hn1 with ⟨I1, x1, _, _, h1⟩ | ⟨F1, x1, hw1, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    rcases hn2 with ⟨I2, x2, _, _, h2⟩ | ⟨F2, x2, hw2, h2⟩
    · exact (numIF _ _ h2.symm).elim
    obtain rfl := numF _ _ h2
    cases F <;> cases bF <;> apply Exists.intro <;> constructor <;> (try apply wf_fN_num_) <;>
      first
        | exact fadd__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fsub__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmul__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fdiv__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmin__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmax__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fcopysign__is_wf _ _ _ _ hw1 hw2 rfl

/-- Rocq `type_progress.v:1691` `relop_total`. `relop_` is total on well-formed operands and a
    well-formed operator. -/
theorem relop_total (nt : numtype) (r : relop_) (n1 n2 : num_) :
    wf_num_ nt n1 → wf_num_ nt n2 → wf_relop_ nt r →
    ∃ c, fun_relop_ nt r n1 n2 c := by
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 hn2 hr
  rcases hr with ⟨I, rI, hI⟩ | ⟨F, rF, hF⟩
  · subst hI
    rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    rcases hn2 with ⟨I2, x2, _, hw2, h2⟩ | ⟨F2, x2, _, h2⟩
    swap
    · exact (numIF _ _ h2).elim
    obtain rfl := numI _ _ h2
    cases rI with
    | LT sx =>
      cases I
      · obtain ⟨c, Hc⟩ := ilt_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_4 sx x1 x2 c Hc⟩
      · obtain ⟨c, Hc⟩ := ilt_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_5 sx x1 x2 c Hc⟩
    | GT sx =>
      cases I
      · obtain ⟨c, Hc⟩ := igt_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_6 sx x1 x2 c Hc⟩
      · obtain ⟨c, Hc⟩ := igt_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_7 sx x1 x2 c Hc⟩
    | LE sx =>
      cases I
      · obtain ⟨c, Hc⟩ := ile_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_8 sx x1 x2 c Hc⟩
      · obtain ⟨c, Hc⟩ := ile_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_9 sx x1 x2 c Hc⟩
    | GE sx =>
      cases I
      · obtain ⟨c, Hc⟩ := ige_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_10 sx x1 x2 c Hc⟩
      · obtain ⟨c, Hc⟩ := ige_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_11 sx x1 x2 c Hc⟩
    | _ => cases I <;> apply Exists.intro <;> constructor
  · subst hF
    rcases hn1 with ⟨I1, x1, _, _, h1⟩ | ⟨F1, x1, hw1, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    rcases hn2 with ⟨I2, x2, _, _, h2⟩ | ⟨F2, x2, hw2, h2⟩
    · exact (numIF _ _ h2.symm).elim
    obtain rfl := numF _ _ h2
    cases F <;> cases rF <;> apply Exists.intro <;> constructor

/-- Rocq `type_progress.v:1715` `cvtop_total`. `cvtop__` is total on a well-formed operand and a
    well-formed conversion operator. -/
theorem cvtop_total (nt1 nt2 : numtype) (cvt : cvtop__) (c1 : num_) :
    wf_num_ nt1 c1 → wf_cvtop__ nt1 nt2 cvt →
    ∃ c2, fun_cvtop__ nt1 nt2 cvt c1 c2 := by
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hc1 hcvt
  rcases hcvt with ⟨I1, I2, x, hx, e1, e2⟩ | ⟨I1, F2, x, hx, e1, e2⟩ |
      ⟨F1, I2, x, hx, e1, e2⟩ | ⟨F1, F2, x, hx, e1, e2⟩
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, hw, h1⟩ | ⟨F1', y, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    cases x <;> cases I1 <;> cases I2 <;> apply Exists.intro <;> constructor
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, hw, h1⟩ | ⟨F1', y, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    cases x with
    | CONVERT sx => cases I1 <;> cases F2 <;> apply Exists.intro <;> constructor
    | REINTERPRET =>
      cases hx with
      | cvtop__Inn_1_Fnn_2_case_1 hsz =>
        cases I1 <;> cases F2 <;>
          first
            | (exfalso; revert hsz; decide)
            | (apply Exists.intro; constructor <;> decide)
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, _, h1⟩ | ⟨F1', y, hw, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    cases x with
    | TRUNC sx => cases F1 <;> cases I2 <;> apply Exists.intro <;> constructor
    | TRUNC_SAT sx => cases F1 <;> cases I2 <;> apply Exists.intro <;> constructor
    | REINTERPRET =>
      cases hx with
      | cvtop__Fnn_1_Inn_2_case_2 hsz =>
        cases F1 <;> cases I2 <;>
          first
            | (exfalso; revert hsz; decide)
            | (apply Exists.intro; constructor <;> decide)
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, _, h1⟩ | ⟨F1', y, hw, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    cases x <;> cases F1 <;> cases F2 <;> apply Exists.intro <;> constructor

/-- Rocq `type_progress.v:1735` `binop_before`. On well-formed operands and operator, the
    generated "earlier clauses apply" predicate `fun_binop__before_fun_binop__case_38` holds (it
    lists every `binop_` clause before the catch-all case 38). -/
theorem binop_before (nt : numtype) (b : binop_) (n1 n2 : num_) :
    wf_num_ nt n1 → wf_num_ nt n2 → wf_binop_ nt b →
    fun_binop__before_fun_binop__case_38 nt b n1 n2 := by
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 hn2 hb
  rcases hb with ⟨I, bI, hI⟩ | ⟨F, bF, hF⟩
  · subst hI
    rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    rcases hn2 with ⟨I2, x2, _, hw2, h2⟩ | ⟨F2, x2, _, h2⟩
    swap
    · exact (numIF _ _ h2).elim
    obtain rfl := numI _ _ h2
    cases bI with
    | DIV sx =>
      cases I
      · obtain ⟨r, Hr⟩ := idiv_total _ sx x1 x2 hw1 hw2
        have Hw := idiv_wf _ _ _ _ _ Hr
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I32 r Hw
        exact fun_binop__before_fun_binop__case_38.fun_binop__case_6 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1
      · obtain ⟨r, Hr⟩ := idiv_total _ sx x1 x2 hw1 hw2
        have Hw := idiv_wf _ _ _ _ _ Hr
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I64 r Hw
        exact fun_binop__before_fun_binop__case_38.fun_binop__case_7 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1
    | REM sx =>
      cases I
      · obtain ⟨r, Hr⟩ := irem_total _ sx x1 x2 hw1 hw2
        have Hw := irem__is_wf _ _ _ _ _ _ Hr hw1 hw2 rfl
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I32 r Hw
        exact fun_binop__before_fun_binop__case_38.fun_binop__case_8 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1
      · obtain ⟨r, Hr⟩ := irem_total _ sx x1 x2 hw1 hw2
        have Hw := irem__is_wf _ _ _ _ _ _ Hr hw1 hw2 rfl
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I64 r Hw
        exact fun_binop__before_fun_binop__case_38.fun_binop__case_9 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1
    | _ =>
      cases I <;> constructor <;>
        refine wf_num_.num__case_0 _ _ _ (by decide) ?_ rfl <;>
        first
          | exact iadd__is_wf _ _ _ _ hw1 hw2 rfl
          | exact isub__is_wf _ _ _ _ hw1 hw2 rfl
          | exact imul__is_wf _ _ _ _ hw1 hw2 rfl
          | exact iand__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ior__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ixor__is_wf _ _ _ _ hw1 hw2 rfl
          | exact irotl__is_wf _ _ _ _ hw1 hw2 rfl
          | exact irotr__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ishl_wf _ _ _ hw1
          | exact ishr_wf _ _ _ _ hw1
  · subst hF
    rcases hn1 with ⟨I1, x1, _, _, h1⟩ | ⟨F1, x1, hw1, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    rcases hn2 with ⟨I2, x2, _, _, h2⟩ | ⟨F2, x2, hw2, h2⟩
    · exact (numIF _ _ h2.symm).elim
    obtain rfl := numF _ _ h2
    cases F <;> cases bF <;> constructor <;> (try apply wf_fN_num_) <;>
      first
        | exact fadd__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fsub__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmul__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fdiv__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmin__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmax__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fcopysign__is_wf _ _ _ _ hw1 hw2 rfl

/-- Rocq `type_progress.v:1761` `binop_not_none`. On well-formed operands and operator, any result
    `lst` that `fun_binop_` relates them to is not `none` (the catch-all case 38 cannot fire). -/
theorem binop_not_none (nt : numtype) (b : binop_) (n1 n2 : num_) (lst : Option (List num_)) :
    wf_num_ nt n1 →
    wf_num_ nt n2 →
    wf_binop_ nt b →
    fun_binop_ nt b n1 n2 lst →
    lst ≠ none := by
  intro hn1 hn2 hb hf hnone
  subst hnone
  cases hf with
  | fun_binop__case_38 _ _ _ _ hnb => exact hnb (binop_before _ _ _ _ hn1 hn2 hb)

/-- Rocq `type_progress.v:1774` `relop_before`. On well-formed operands and operator, the
    generated "an earlier clause applies" predicate `fun_relop__before_fun_relop__case_24` holds. -/
theorem relop_before (nt : numtype) (r : relop_) (n1 n2 : num_) :
    wf_num_ nt n1 → wf_num_ nt n2 → wf_relop_ nt r →
    fun_relop__before_fun_relop__case_24 nt r n1 n2 := by
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 hn2 hr
  rcases hr with ⟨I, rI, hI⟩ | ⟨F, rF, hF⟩
  · subst hI
    rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    rcases hn2 with ⟨I2, x2, _, hw2, h2⟩ | ⟨F2, x2, _, h2⟩
    swap
    · exact (numIF _ _ h2).elim
    obtain rfl := numI _ _ h2
    cases rI <;> cases I <;> constructor <;> exact uN.mk_uN 0
  · subst hF
    rcases hn1 with ⟨I1, x1, _, _, h1⟩ | ⟨F1, x1, hw1, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    rcases hn2 with ⟨I2, x2, _, _, h2⟩ | ⟨F2, x2, hw2, h2⟩
    · exact (numIF _ _ h2.symm).elim
    obtain rfl := numF _ _ h2
    cases F <;> cases rF <;> constructor

/-- Rocq `type_progress.v:1787` `relop_not_none`. On well-formed operands and operator, any result
    `c` that `fun_relop_` relates them to is not `none`. -/
theorem relop_not_none (nt : numtype) (r : relop_) (n1 n2 : num_) (c : Option num_) :
    wf_num_ nt n1 →
    wf_num_ nt n2 →
    wf_relop_ nt r →
    fun_relop_ nt r n1 n2 c →
    c ≠ none := by
  intro hn1 hn2 hr hf hnone
  subst hnone
  cases hf with
  | fun_relop__case_24 _ _ _ _ hnb => exact hnb (relop_before _ _ _ _ hn1 hn2 hr)

/-- Rocq `type_progress.v:1800` `cvtop_before`. On a well-formed operand and conversion operator,
    the generated predicate `fun_cvtop___before_fun_cvtop___case_36` (an earlier clause of
    `fun_cvtop__` applies) holds. -/
theorem cvtop_before (nt1 nt2 : numtype) (cvt : cvtop__) (c1 : num_) :
    wf_num_ nt1 c1 → wf_cvtop__ nt1 nt2 cvt →
    fun_cvtop___before_fun_cvtop___case_36 nt1 nt2 cvt c1 := by
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hc1 hcvt
  rcases hcvt with ⟨I1, I2, x, hx, e1, e2⟩ | ⟨I1, F2, x, hx, e1, e2⟩ |
      ⟨F1, I2, x, hx, e1, e2⟩ | ⟨F1, F2, x, hx, e1, e2⟩
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, hw, h1⟩ | ⟨F1', y, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    cases x <;> cases I1 <;> cases I2 <;> constructor
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, hw, h1⟩ | ⟨F1', y, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    cases x with
    | CONVERT sx => cases I1 <;> cases F2 <;> constructor
    | REINTERPRET =>
      cases hx with
      | cvtop__Inn_1_Fnn_2_case_1 hsz =>
        cases I1 <;> cases F2 <;>
          first
            | (exfalso; revert hsz; decide)
            | (constructor <;> decide)
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, _, h1⟩ | ⟨F1', y, hw, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    cases x with
    | TRUNC sx => cases F1 <;> cases I2 <;> constructor
    | TRUNC_SAT sx => cases F1 <;> cases I2 <;> constructor
    | REINTERPRET =>
      cases hx with
      | cvtop__Fnn_1_Inn_2_case_2 hsz =>
        cases F1 <;> cases I2 <;>
          first
            | (exfalso; revert hsz; decide)
            | (constructor <;> decide)
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, _, h1⟩ | ⟨F1', y, hw, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    cases x <;> cases F1 <;> cases F2 <;> constructor

/-- Rocq `type_progress.v:1824` `cvtop_not_none`. On a well-formed operand and conversion
    operator, any result `c2` that `fun_cvtop__` relates them to is not `none`. -/
theorem cvtop_not_none (nt1 nt2 : numtype) (cvt : cvtop__) (c1 : num_) (c2 : Option (List num_)) :
    wf_num_ nt1 c1 →
    wf_cvtop__ nt1 nt2 cvt →
    fun_cvtop__ nt1 nt2 cvt c1 c2 →
    c2 ≠ none := by
  intro hc1 hcvt hf hnone
  subst hnone
  cases hf with
  | fun_cvtop___case_36 _ _ _ _ hnb => exact hnb (cvtop_before _ _ _ _ hc1 hcvt)

/-- Rocq `type_progress.v:1836` `testop_not_none`. The function `fun_testop_` is defined
    (`≠ none`) on a well-formed operand and test operator. -/
theorem testop_not_none (nt : numtype) (t : testop_) (n1 : num_) :
    wf_num_ nt n1 →
    wf_testop_ nt t →
    fun_testop_ nt t n1 ≠ none := by
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 ht
  rcases ht with ⟨I, tI, hI⟩
  subst hI
  rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
  swap
  · exact (numIF _ _ h1).elim
  obtain rfl := numI _ _ h1
  cases tI
  cases I <;> simp [fun_testop_, numtype_Inn]

/-- Rocq `type_progress.v:1854` `Forall_all`. If every element satisfies the boolean predicate `P`
    (as a `Forall`), the list passes the boolean `all P`. mathcomp `all P l` ↦ `l.all P`; Rocq's
    `is_true` coercions ↦ `= true`. -/
theorem Forall_all (T : Type) (P : T → Bool) (l : List T) :
    Forall (fun x => P x = true) l → l.all P = true := by
  intro h
  exact List.all_eq_true.mpr h

/-- Rocq `type_progress.v:1858` `all_Forall`. Converse of `Forall_all`: a list passing the boolean
    `all P` satisfies `P` element-wise. -/
theorem all_Forall (T : Type) (P : T → Bool) (l : List T) :
    l.all P = true → Forall (fun x => P x = true) l := by
  intro h
  exact List.all_eq_true.mp h

/-- Rocq `type_progress.v:1865` `Forall_exists_Forall2`. If every `b ∈ l` has an `R`-related
    witness `a` satisfying `P`, the witnesses form a list `la` with `Forall2 R la l` and
    `Forall P la`. **Deviation:** Lean's generated `Forall₂` is zip-based and does not imply equal
    lengths (with it alone the conclusion would hold trivially with `la = []`), while Rocq's
    inductive `Forall2` does; so Rocq's conjunct `Forall2 R la l` is rendered as
    `(Forall₂ R la l ∧ la.length = l.length)` (length right after the `Forall₂`, grouped so the
    outer `_ ∧ Forall P la` shape is Rocq's). Downstream Rocq uses of `Forall2_size_eq` (1982/3941;
    NOT PORTED in Lean) need exactly this length fact, which Lean callers take from this conjunct. -/
theorem Forall_exists_Forall2 (A B : Type) (R : A → B → Prop) (P : A → Prop) (l : List B) :
    Forall (fun b => ∃ a, R a b ∧ P a) l →
    ∃ la, (Forall₂ R la l ∧ la.length = l.length) ∧ Forall P la := by
  induction l with
  | nil =>
    intro _
    exact ⟨[], ⟨fun t ht => by simp at ht, rfl⟩, fun x hx => by simp at hx⟩
  | cons b l ih =>
    intro h
    obtain ⟨a, hr, hp⟩ := h b (by simp)
    obtain ⟨la, ⟨h2, hlen⟩, hp'⟩ := ih (fun x hx => h x (by simp [hx]))
    refine ⟨a :: la, ⟨?_, by simp [hlen]⟩, ?_⟩
    · intro t ht
      rw [List.zip_cons_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hr
      · exact h2 t ht
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp
      · exact hp' x hx

-- `Forall2_size_eq` (type_progress.v:1874, `Forall2 R la lb -> (|la|) = (|lb|)`) NOT PORTED: Rocq's
-- inductive `Forall2` carries the length but Lean's zip-based `Forall₂` does not (the literal
-- statement is false in Lean, e.g. `la = []`, `lb = [b]`), so adding `hlen` would make the lemma
-- return its own premise (same as `Forall2_seq_size`, HelperLemmas.lean:293). Its Rocq uses (Ltac
-- `vunop_case` at 1982 and 3941) only extract the length; Lean callers take it from the length
-- conjunct of `Forall_iabs_total` / `Forall_exists_Forall2`.

/-- Rocq `type_progress.v:1884` `wf_lane_Jnn_inv`. A well-formed lane of lane type
    `lanetype_Jnn J` that projects as an integer lane is `mk_lane__0 J x` with `x` in range.
    Rocq's boolean `proj_lane__0 l != None` ↦ `proj_lane__0 l ≠ none`. -/
theorem wf_lane_Jnn_inv (J : Jnn) (l : lane_) :
    wf_lane_ (lanetype_Jnn J) l → proj_lane__0 l ≠ none →
    ∃ x, l = lane_.mk_lane__0 J x ∧ wf_uN (lsize (lanetype_Jnn J)) x := by
  intro Hw _
  cases Hw with
  | lane__case_0 J' c Hc Heq =>
    have HJ : J' = J := by
      cases J <;> cases J' <;> first | rfl | (exfalso; simp [lanetype_Jnn] at Heq)
    subst HJ
    exact ⟨c, rfl, Hc⟩
  | lane__case_1 F c Hc Heq =>
    exfalso
    cases F <;> cases J <;> simp [lanetype_Jnn, lanetype_Fnn] at Heq

/-- Rocq `type_progress.v:1897` `wf_lane_Jnn_some`. `lane_` has disjoint integer / float cases, so
    every well-formed lane of lane type `lanetype_Jnn J` projects as an integer lane. -/
theorem wf_lane_Jnn_some (J : Jnn) (l : lane_) :
    wf_lane_ (lanetype_Jnn J) l → proj_lane__0 l ≠ none := by
  intro Hw
  cases Hw with
  | lane__case_0 J' c Hc Heq => simp [proj_lane__0]
  | lane__case_1 F c Hc Heq =>
    exfalso
    cases F <;> cases J <;> simp [lanetype_Jnn, lanetype_Fnn] at Heq

/-- Rocq `type_progress.v:1905` `wf_lane_Fnn_inv`. A well-formed lane of lane type
    `lanetype_Fnn F` is `mk_lane__1 F x` with `x` well-formed. -/
theorem wf_lane_Fnn_inv (F : Fnn) (l : lane_) :
    wf_lane_ (lanetype_Fnn F) l →
    ∃ x, l = lane_.mk_lane__1 F x ∧ wf_fN (sizenn (numtype_Fnn F)) x := by
  intro Hw
  cases Hw with
  | lane__case_0 J c Hc Heq =>
    exfalso
    cases F <;> cases J <;> simp [lanetype_Jnn, lanetype_Fnn] at Heq
  | lane__case_1 F' c Hc Heq =>
    have HF : F' = F := by
      cases F <;> cases F' <;> first | rfl | (exfalso; simp [lanetype_Fnn] at Heq)
    subst HF
    exact ⟨c, rfl, Hc⟩

/-- Rocq `type_progress.v:1916` `Forall_lane_Jnn`. List version of `wf_lane_Jnn_inv`. -/
theorem Forall_lane_Jnn (J : Jnn) (ls : List lane_) :
    Forall (fun l => wf_lane_ (lanetype_Jnn J) l) ls →
    Forall (fun l => proj_lane__0 l ≠ none) ls →
    Forall (fun l => ∃ x, l = lane_.mk_lane__0 J x ∧ wf_uN (lsize (lanetype_Jnn J)) x) ls := by
  intro Hw Hs l hl
  exact wf_lane_Jnn_inv J l (Hw l hl) (Hs l hl)

/-- Rocq `type_progress.v:1927` `Forall_lane_map_wf`. Mapping a range-preserving operation `f`
    over in-range `Jnn` lanes gives well-formed lanes. Rocq `!(x)` ↦ `Option.get! x`. -/
theorem Forall_lane_map_wf (J : Jnn) (f : iN → iN) (ls : List lane_) :
    (∀ x, wf_uN (lsize (lanetype_Jnn J)) x → wf_uN (lsize (lanetype_Jnn J)) (f x)) →
    Forall (fun l => ∃ x, l = lane_.mk_lane__0 J x ∧ wf_uN (lsize (lanetype_Jnn J)) x) ls →
    Forall (fun l => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J (f (Option.get! (proj_lane__0 l))))) ls := by
  intro Hf H l hl
  obtain ⟨x, hx, hwx⟩ := H l hl
  subst hx
  exact wf_lane_.lane__case_0 _ _ _ (Hf x hwx) rfl

/-- Rocq `type_progress.v:1938` `Forall_lane_fop_wf`. Likewise for a (set-valued) float operation
    `fop` over well-formed `Fnn` lanes: every result lane is well-formed. Rocq's `res_N`
    (`Definition res_N := N`, wasm.v:342) ↦ `N`, as in Lean's generated float operations. -/
theorem Forall_lane_fop_wf (F : Fnn) (fop : N → fN → List fN) (ls : List lane_) :
    (∀ x, wf_fN (sizenn (numtype_Fnn F)) x →
      Forall (fun r => wf_fN (sizenn (numtype_Fnn F)) r) (fop (sizenn (numtype_Fnn F)) x)) →
    Forall (fun l => wf_lane_ (lanetype_Fnn F) l) ls →
    Forall (fun l => Forall (fun it =>
        wf_lane_ (lanetype_Fnn F) (lane_.mk_lane__1 F it))
      (fop (sizenn (numtype_Fnn F)) (Option.get! (proj_lane__1 l)))) ls := by
  intro Hf H l hl
  obtain ⟨x, hx, hwx⟩ := wf_lane_Fnn_inv F l (H l hl)
  subst hx
  intro r hr
  exact wf_lane_.lane__case_1 _ _ _ (Hf x hwx r hr) rfl

/-- Rocq `type_progress.v:1953` `iabs_lane_total`. `fun_iabs_` is total on an in-range `Jnn` lane
    value, and its result makes a well-formed lane. -/
theorem iabs_lane_total (J : Jnn) (x : iN) :
    wf_uN (lsize (lanetype_Jnn J)) x →
    ∃ v, fun_iabs_ (lsizenn (lanetype_Jnn J)) x v ∧
      wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v) := by
  intro Hx
  obtain ⟨z, Hz, _⟩ := signed_total (lsize (lanetype_Jnn J)) (proj_uN_0 x) (iswf_uN_proj_lt Hx)
  have Ha : fun_iabs_ (lsizenn (lanetype_Jnn J)) x
      (if z ≥ (0 : Int) then x else ineg_ (lsizenn (lanetype_Jnn J)) x) :=
    fun_iabs_.fun_iabs__case_0 _ _ _ Hz
  exact ⟨_, Ha, wf_lane_.lane__case_0 _ _ _ (iabs__is_wf _ _ _ _ Ha Hx rfl) rfl⟩

/-- Rocq `type_progress.v:1968` `Forall_iabs_total`. Lane-wise `fun_iabs_` over in-range `Jnn` lanes
    has results `vs` (`Forall2`-related to the lanes), all making well-formed lanes.
    **Deviation:** as in `Forall_exists_Forall2`, Rocq's conjunct `Forall2 R vs ls` is rendered as
    `(Forall₂ R vs ls ∧ vs.length = ls.length)` (zip-based `Forall₂` would be satisfied trivially
    by `vs = []`); the generated `fun_vunop_` iabs cases need this length premise. -/
theorem Forall_iabs_total (J : Jnn) (ls : List lane_) :
    Forall (fun l => ∃ x, l = lane_.mk_lane__0 J x ∧ wf_uN (lsize (lanetype_Jnn J)) x) ls →
    ∃ vs, (Forall₂ (fun v l => fun_iabs_ (lsizenn (lanetype_Jnn J)) (Option.get! (proj_lane__0 l)) v)
          vs ls ∧ vs.length = ls.length) ∧
      Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs := by
  intro H
  apply Forall_exists_Forall2
  intro l hl
  obtain ⟨x, hx, Hx⟩ := H l hl
  subst hx
  exact iabs_lane_total J x Hx

-- Ltac `vunop_case` (type_progress.v:1980) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

/-- Rocq `type_progress.v:2004` `vunop_real`. On well-formed arguments (and, for an integer shape,
    lanes that project as integer lanes) a real case of `fun_vunop_` applies, and hence its
    `before` predicate `fun_vunop__before_fun_vunop__case_26` holds. Rocq's boolean
    `all (fun l => proj_lane__0 l != None) L` ↦ `L.all (fun l => proj_lane__0 l != none) = true`. -/
theorem vunop_real (sh : shape) (vunop : vunop_) (val : vec_) :
    wf_vunop_ sh vunop →
    wf_uN 128 val →
    wf_shape sh →
    (∀ (J : Jnn) (M : N), sh = shape.X (lanetype_Jnn J) (dim.mk_dim M) →
      (lanes_ sh val).all (fun l : lane_ => proj_lane__0 l != none) = true) →
    (∃ vs, fun_vunop_ sh vunop val (some vs)) ∧
      fun_vunop__before_fun_vunop__case_26 sh vunop val := by
  intro Hop Hv Hsh Hall
  have Hl := lanes__is_wf _ _ _ Hsh Hv rfl
  cases Hop with
  | vunop__case_0 J M o Ho Hs =>
    -- integer shape: lane facts (Rocq `Hsome`, `Hlx`, `Forall_iabs_total`) feed every real case
    subst Hs
    have Hl' : Forall (fun l => wf_lane_ (lanetype_Jnn J) l)
        (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) val) := Hl
    have Hsome : Forall (fun l => proj_lane__0 l ≠ none)
        (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) val) := by
      intro l hl
      have h := all_Forall _ _ _ (Hall J M rfl) l hl
      simpa using h
    have Hlx := Forall_lane_Jnn J _ Hl' Hsome
    obtain ⟨vs, ⟨H2a, H2b⟩, Hvw⟩ := Forall_iabs_total J _ Hlx
    have Hneg := Forall_lane_map_wf J (fun x => ineg_ (lsizenn (lanetype_Jnn J)) x) _
      (fun x hx => ineg__is_wf _ x _ hx rfl) Hlx
    have Hpop := Forall_lane_map_wf J (fun x => ipopcnt_ (lsizenn (lanetype_Jnn J)) x) _
      (fun x hx => ipopcnt__is_wf _ x _ hx rfl) Hlx
    -- Rocq `destruct J, o; inversion Ho`: only `POPCNT` at `J = I8` is well formed
    cases J <;> cases o <;> (try (cases Ho; contradiction))
    -- Rocq `split; [eexists | ]; econstructor; vunop_case ...`: `constructor` picks the matching
    -- case of `fun_vunop_` (resp. its `before` predicate); each premise is then closed from the
    -- lane facts, with `rfl` last so that it only fills the remaining metavariables.
    all_goals
      refine ⟨?_, ?_⟩
      · apply Exists.intro
        constructor
        all_goals first | exact H2b | exact H2a | exact Hsome | exact Hsh | exact Hvw | exact Hneg | exact Hpop | rfl
      · constructor
        all_goals first | exact H2b | exact H2a | exact Hsome | exact Hsh | exact Hvw | exact Hneg | exact Hpop | rfl
  | vunop__case_1 F M o Hs =>
    -- float shape: one `Forall_lane_fop_wf` fact per operation (Rocq `vunop_case`, float branch)
    subst Hs
    have Hl' : Forall (fun l => wf_lane_ (lanetype_Fnn F) l)
        (lanes_ (shape.X (lanetype_Fnn F) (dim.mk_dim M)) val) := Hl
    have Habs := Forall_lane_fop_wf F fabs_ _ (fun x hx => fabs__is_wf _ x _ hx rfl) Hl'
    have Hneg := Forall_lane_fop_wf F fneg_ _ (fun x hx => fneg__is_wf _ x _ hx rfl) Hl'
    have Hsqrt := Forall_lane_fop_wf F fsqrt_ _ (fun x hx => fsqrt__is_wf _ x _ hx rfl) Hl'
    have Hceil := Forall_lane_fop_wf F fceil_ _ (fun x hx => fceil__is_wf _ x _ hx rfl) Hl'
    have Hfloor := Forall_lane_fop_wf F ffloor_ _ (fun x hx => ffloor__is_wf _ x _ hx rfl) Hl'
    have Htrunc := Forall_lane_fop_wf F ftrunc_ _ (fun x hx => ftrunc__is_wf _ x _ hx rfl) Hl'
    have Hnearest := Forall_lane_fop_wf F fnearest_ _ (fun x hx => fnearest__is_wf _ x _ hx rfl) Hl'
    cases F <;> cases o
    all_goals
      refine ⟨?_, ?_⟩
      · apply Exists.intro
        constructor
        all_goals first | exact Hsh | exact Habs | exact Hneg | exact Hsqrt | exact Hceil | exact Hfloor | exact Htrunc | exact Hnearest | rfl
      · constructor
        all_goals first | exact Hsh | exact Habs | exact Hneg | exact Hsqrt | exact Hceil | exact Hfloor | exact Htrunc | exact Hnearest | rfl

/-- Rocq `type_progress.v:2032` `vunop_total`. `fun_vunop_` relates well-formed arguments to some
    result (a real case or the catch-all). -/
theorem vunop_total (sh : shape) (vunop : vunop_) (val : vec_) :
    wf_vunop_ sh vunop →
    wf_uN 128 val →
    wf_shape sh →
    (∃ ret, fun_vunop_ sh vunop val ret) := by
  intro Hop Hv Hsh
  -- By `wf_lane_Jnn_some` every lane projects as an integer lane, so `vunop_real`'s side premise
  -- always holds (Rocq splits on it, and refutes the negative branch by 27-way inversion of the
  -- `before` predicate; that branch is impossible, so here it is never needed).
  have Hall : ∀ (J : Jnn) (M : N), sh = shape.X (lanetype_Jnn J) (dim.mk_dim M) →
      (lanes_ sh val).all (fun l : lane_ => proj_lane__0 l != none) = true := by
    intro J M hsh
    have Hl := lanes__is_wf _ _ _ Hsh Hv rfl
    subst hsh
    apply Forall_all
    intro l hl
    have h := wf_lane_Jnn_some J l (Hl l hl)
    simpa using h
  obtain ⟨⟨vs, Hvs⟩, _⟩ := vunop_real sh vunop val Hop Hv Hsh Hall
  exact ⟨some vs, Hvs⟩

/-- Rocq `type_progress.v:2059` `vunop_not_none`. On well-formed arguments, any result `ret` of
    `fun_vunop_` is not `none` (the catch-all case 26 cannot fire). -/
theorem vunop_not_none (sh : shape) (vunop : vunop_) (val : vec_) (ret : Option (List vec_)) :
    wf_vunop_ sh vunop →
    wf_uN 128 val →
    wf_shape sh →
    fun_vunop_ sh vunop val ret →
    ret ≠ none := by
  intro Hop Hv Hsh Hf Hn
  subst Hn
  -- Rocq's 27-way `inversion Hf`, done once over bare variables (only the catch-all case 26
  -- can return `none`).
  have inv : ∀ (s : shape) (op : vunop_) (v : vec_), fun_vunop_ s op v none →
      ¬ fun_vunop__before_fun_vunop__case_26 s op v := by
    intro s op v H
    cases H with
    | fun_vunop__case_26 _ _ _ Hnb => exact Hnb
  have Hall : ∀ (J : Jnn) (M : N), sh = shape.X (lanetype_Jnn J) (dim.mk_dim M) →
      (lanes_ sh val).all (fun l : lane_ => proj_lane__0 l != none) = true := by
    intro J M hsh
    have Hl := lanes__is_wf _ _ _ Hsh Hv rfl
    subst hsh
    apply Forall_all
    intro l hl
    have h := wf_lane_Jnn_some J l (Hl l hl)
    simpa using h
  -- the real case supplied by `vunop_real` contradicts the catch-all
  exact inv _ _ _ Hf (vunop_real sh vunop val Hop Hv Hsh Hall).2

/-- Rocq `type_progress.v:2092` `sat_s_range`. `sat_s_ v_N z` lies in `[0 - 2^(v_N-1), 2^(v_N-1))`.
    Rocq's `(2 ^ (v_N - 1))%BN` is `N` arithmetic (truncated subtraction) cast to `Z`; here the
    power is computed in `Nat` and cast to `Int`. -/
theorem sat_s_range (v_N : N) (z : Int) :
    (0 : Int) - ((2 ^ (v_N - 1) : Nat) : Int) ≤ sat_s_ v_N z ∧
      sat_s_ v_N z < ((2 ^ (v_N - 1) : Nat) : Int) := by
  unfold sat_s_
  -- Rocq `Zsub1_toN` / `two_pow_pos`, done inline (`omega` / `Nat.two_pow_pos`)
  rw [show Int.toNat ((v_N : Int) - (1 : Int)) = v_N - 1 by omega, iswf_two_pow_cast]
  have Hp : 0 < 2 ^ (v_N - 1) := Nat.two_pow_pos _
  split_ifs <;> omega

/-- Rocq `type_progress.v:2103` `imin_total_wf`. `fun_imin_` is total on in-range operands and its
    result is in range. -/
theorem imin_total_wf (v_N : N) (v_sx : sx) (i1 i2 : iN) : wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_imin_ v_N v_sx i1 i2 r ∧ wf_uN v_N r := by
  intro H1 H2
  have hr : ∃ r, fun_imin_ v_N v_sx i1 i2 r := by
    cases v_sx with
    | U =>
      by_cases E : proj_uN_0 i1 ≤ proj_uN_0 i2
      · exact ⟨i1, fun_imin_.fun_imin__case_0 _ _ _ E⟩
      · exact ⟨i2, fun_imin_.fun_imin__case_1 _ _ _ (by omega)⟩
    | S =>
      obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (iswf_uN_proj_lt H1)
      obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (iswf_uN_proj_lt H2)
      exact ⟨_, fun_imin_.fun_imin__case_2 v_N i1 i2 z2 z1 Hs2 Hs1⟩
  obtain ⟨r, Hr⟩ := hr
  exact ⟨r, Hr, imin__is_wf _ _ _ _ _ _ Hr H1 H2 rfl⟩

/-- Rocq `type_progress.v:2119` `imax_total_wf`. `fun_imax_` is total on in-range operands and its
    result is in range. -/
theorem imax_total_wf (v_N : N) (v_sx : sx) (i1 i2 : iN) : wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_imax_ v_N v_sx i1 i2 r ∧ wf_uN v_N r := by
  intro H1 H2
  have hex : ∃ r, fun_imax_ v_N v_sx i1 i2 r := by
    cases v_sx with
    | U =>
      by_cases E : proj_uN_0 i1 < proj_uN_0 i2
      · exact ⟨i2, fun_imax_.fun_imax__case_1 v_N i1 i2 E⟩
      · exact ⟨i1, fun_imax_.fun_imax__case_0 v_N i1 i2 (by omega)⟩
    | S =>
      obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ H1)
      obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ H2)
      exact ⟨_, fun_imax_.fun_imax__case_2 v_N i1 i2 z2 z1 Hs2 Hs1⟩
  obtain ⟨r, Hr⟩ := hex
  exact ⟨r, Hr, imax__is_wf _ _ _ _ _ _ Hr H1 H2 rfl⟩

/-- Rocq `type_progress.v:2135` `iadd_sat_total_wf`. `fun_iadd_sat_` is total on in-range operands
    and its result is in range. -/
theorem iadd_sat_total_wf (v_N : N) (v_sx : sx) (i1 i2 : iN) : wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_iadd_sat_ v_N v_sx i1 i2 r ∧ wf_uN v_N r := by
  intro H1 H2
  have hex : ∃ r, fun_iadd_sat_ v_N v_sx i1 i2 r := by
    cases v_sx with
    | U => exact ⟨_, fun_iadd_sat_.fun_iadd_sat__case_0 v_N i1 i2⟩
    | S =>
      obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ H1)
      obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ H2)
      obtain ⟨Hlo, Hhi⟩ := sat_s_range v_N (z1 + z2)
      obtain ⟨m, Hm⟩ := invsigned_total v_N (sat_s_ v_N (z1 + z2)) Hlo Hhi
      exact ⟨_, fun_iadd_sat_.fun_iadd_sat__case_1 v_N i1 i2 z2 z1 m Hs2 Hs1 Hm⟩
  obtain ⟨r, Hr⟩ := hex
  exact ⟨r, Hr, iadd_sat__is_wf _ _ _ _ _ _ Hr H1 H2 rfl⟩

/-- Rocq `type_progress.v:2149` `isub_sat_total_wf`. `fun_isub_sat_` is total on in-range operands
    and its result is in range. -/
theorem isub_sat_total_wf (v_N : N) (v_sx : sx) (i1 i2 : iN) : wf_uN v_N i1 → wf_uN v_N i2 →
    ∃ r, fun_isub_sat_ v_N v_sx i1 i2 r ∧ wf_uN v_N r := by
  intro H1 H2
  have hex : ∃ r, fun_isub_sat_ v_N v_sx i1 i2 r := by
    cases v_sx with
    | U => exact ⟨_, fun_isub_sat_.fun_isub_sat__case_0 v_N i1 i2⟩
    | S =>
      obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ H1)
      obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ H2)
      obtain ⟨Hlo, Hhi⟩ := sat_s_range v_N (z1 - z2)
      obtain ⟨m, Hm⟩ := invsigned_total v_N (sat_s_ v_N (z1 - z2)) Hlo Hhi
      exact ⟨_, fun_isub_sat_.fun_isub_sat__case_1 v_N i1 i2 z2 z1 m Hs2 Hs1 Hm⟩
  obtain ⟨r, Hr⟩ := hex
  exact ⟨r, Hr, isub_sat__is_wf _ _ _ _ _ _ Hr H1 H2 rfl⟩

/-- Rocq `type_progress.v:2165` `jlane`: `l` is a well-formed integer lane of shape `J`. -/
def jlane (J : Jnn) (l : lane_) : Prop :=
  ∃ x, l = lane_.mk_lane__0 J x ∧ wf_uN (lsize (lanetype_Jnn J)) x

/-- Rocq `type_progress.v:2167` `flane`: `l` is a well-formed float lane of shape `F`. -/
def flane (F : Fnn) (l : lane_) : Prop :=
  ∃ x, l = lane_.mk_lane__1 F x ∧ wf_fN (sizenn (numtype_Fnn F)) x

/-- Rocq `type_progress.v:2170` `lanes_Jnn_form`. The lanes of a well-formed vector at an integer
    shape are all `jlane J` (in the `Jnn` injection and in range). -/
theorem lanes_Jnn_form (J : Jnn) (M : N) (c : vec_) :
    wf_shape (shape.X (lanetype_Jnn J) (dim.mk_dim M)) → wf_uN 128 c →
    Forall (jlane J) (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c) := by
  intro Hsh Hc
  have Hl := lanes__is_wf _ _ _ Hsh Hc rfl
  intro l hl
  have Hw := Hl l hl
  exact wf_lane_Jnn_inv J l Hw (wf_lane_Jnn_some J l Hw)

/-- Rocq `type_progress.v:2179` `lanes_Fnn_form`. The lanes of a well-formed vector at a float
    shape are all `flane F`. -/
theorem lanes_Fnn_form (F : Fnn) (M : N) (c : vec_) :
    wf_shape (shape.X (lanetype_Fnn F) (dim.mk_dim M)) → wf_uN 128 c →
    Forall (flane F) (lanes_ (shape.X (lanetype_Fnn F) (dim.mk_dim M)) c) := by
  intro Hsh Hc
  have Hl := lanes__is_wf _ _ _ Hsh Hc rfl
  intro l hl
  exact wf_lane_Fnn_inv F l (Hl l hl)

/-- Rocq `type_progress.v:2187` `jlane_some`. `jlane` lanes project as integer lanes. -/
theorem jlane_some (J : Jnn) (L : List lane_) :
    Forall (jlane J) L → Forall (fun l => proj_lane__0 l ≠ none) L := by
  intro H l hl
  obtain ⟨x, rfl, _⟩ := H l hl
  simp [proj_lane__0]

/-- Rocq `type_progress.v:2190` `flane_some`. `flane` lanes project as float lanes. -/
theorem flane_some (F : Fnn) (L : List lane_) :
    Forall (flane F) L → Forall (fun l => proj_lane__1 l ≠ none) L := by
  intro H l hl
  obtain ⟨x, rfl, _⟩ := H l hl
  simp [proj_lane__1]

/-- Rocq `type_progress.v:2193` `lanes_size_eq`. Two vectors have the same number of lanes at a
    given shape (mathcomp `size` ↦ `List.length`; Lean proof can use `lanes_len`,
    HelperLemmas.lean:785). -/
theorem lanes_size_eq (lt : lanetype) (M : N) (c1 c2 : vec_) :
    (lanes_ (shape.X lt (dim.mk_dim M)) c1).length = (lanes_ (shape.X lt (dim.mk_dim M)) c2).length := by
  rw [lanes_len, lanes_len]

/-- Rocq `type_progress.v:2200` `zip_lane_wf`. Lane-wise application of a range-preserving binary
    operation `f` to two equally long lists of `jlane J` lanes gives well-formed lanes. No `hlen`
    deviation: Rocq's `Forall2` conclusion additionally carries `size L1 = size L2`, which is
    already the premise `L1.length = L2.length`, so the zip-based `Forall₂` conclusion is
    equivalent here. -/
theorem zip_lane_wf (J : Jnn) (lt : lanetype) (f : iN → iN → iN) (L1 L2 : List lane_) :
    lt = lanetype_Jnn J →
    (∀ a b, wf_uN (lsize (lanetype_Jnn J)) a → wf_uN (lsize (lanetype_Jnn J)) b →
      wf_uN (lsize (lanetype_Jnn J)) (f a b)) →
    Forall (jlane J) L1 → Forall (jlane J) L2 → L1.length = L2.length →
    Forall₂ (fun l1 l2 =>
        wf_lane_ lt (lane_.mk_lane__0 J (f (Option.get! (proj_lane__0 l1)) (Option.get! (proj_lane__0 l2)))))
      L1 L2 := by
  intro hlt Hf H1 H2 _
  subst hlt
  rintro ⟨l1, l2⟩ ht
  obtain ⟨h1, h2⟩ := List.of_mem_zip ht
  obtain ⟨x1, rfl, Hx1⟩ := H1 _ h1
  obtain ⟨x2, rfl, Hx2⟩ := H2 _ h2
  exact wf_lane_.lane__case_0 _ _ _ (Hf _ _ Hx1 Hx2) rfl

/-- Rocq `type_progress.v:2214` `zip_flane_wf`. A float-lane operation `fop` that preserves
    `wf_fN` maps two equal-length lists of well-formed `F`-lanes, lane-wise, to well-formed
    `F`-lanes. Rocq's `res_N` is `N` (`Nat`); `!(·)` is `Option.get!`. The `Forall₂` conclusion is
    zip-based (no length fact), but the length equality is already the premise
    `L1.length = L2.length`, so the statement is equivalent to Rocq's. -/
theorem zip_flane_wf (F : Fnn) (fop : N → fN → fN → List fN) (L1 L2 : List lane_) :
    (∀ a b, wf_fN (sizenn (numtype_Fnn F)) a → wf_fN (sizenn (numtype_Fnn F)) b →
      Forall (fun r => wf_fN (sizenn (numtype_Fnn F)) r) (fop (sizenn (numtype_Fnn F)) a b)) →
    Forall (flane F) L1 → Forall (flane F) L2 → L1.length = L2.length →
    Forall₂ (fun l1 l2 => Forall (fun it => wf_lane_ (lanetype_Fnn F) (lane_.mk_lane__1 F it))
      (fop (sizenn (numtype_Fnn F)) (Option.get! (proj_lane__1 l1)) (Option.get! (proj_lane__1 l2)))) L1 L2 := by
  intro Hf H1 H2 _
  rintro ⟨l1, l2⟩ ht
  obtain ⟨h1, h2⟩ := List.of_mem_zip ht
  obtain ⟨x1, rfl, Hx1⟩ := H1 _ h1
  obtain ⟨x2, rfl, Hx2⟩ := H2 _ h2
  intro r hr
  exact wf_lane_.lane__case_1 _ _ _ (Hf _ _ Hx1 Hx2 r hr) rfl

/-- Rocq `type_progress.v:2230` `zip_lane_rel`. Lane-wise application of a total relation `R`
    whose results satisfy `W`: on equal-length lists of well-formed `J`-lanes there are results
    `vs` related lane-wise, all satisfying `W`, with `vs.length = L1.length`. Rocq's inductive
    `List_Forall3` is Lean's zip-based `Forall₃` (same argument order); the lengths it would carry
    are already given (`vs.length = L1.length` in the conclusion, `L1.length = L2.length` premise). -/
theorem zip_lane_rel (J : Jnn) (R : iN → iN → iN → Prop) (W : iN → Prop) (L1 L2 : List lane_) :
    (∀ a b, wf_uN (lsize (lanetype_Jnn J)) a → wf_uN (lsize (lanetype_Jnn J)) b →
      ∃ r, R a b r ∧ W r) →
    Forall (jlane J) L1 → Forall (jlane J) L2 → L1.length = L2.length →
    ∃ vs, Forall₃ (fun v l1 l2 => R (Option.get! (proj_lane__0 l1)) (Option.get! (proj_lane__0 l2)) v) vs L1 L2 ∧
      Forall W vs ∧ vs.length = L1.length := by
  intro HR H1 H2 Hlen
  induction L1 generalizing L2 with
  | nil =>
    refine ⟨[], ?_, ?_, rfl⟩
    · rintro ⟨⟨v, l1⟩, l2⟩ ht
      simp at ht
    · intro v hv
      simp at hv
  | cons l1 L1' IH =>
    cases L2 with
    | nil => simp at Hlen
    | cons l2 L2' =>
      obtain ⟨x1, rfl, Hx1⟩ := H1 _ (List.mem_cons_self ..)
      obtain ⟨x2, rfl, Hx2⟩ := H2 _ (List.mem_cons_self ..)
      obtain ⟨vs, H3, Hw, Hs⟩ := IH L2' (fun l hl => H1 l (List.mem_cons_of_mem _ hl))
        (fun l hl => H2 l (List.mem_cons_of_mem _ hl)) (by simpa using Hlen)
      obtain ⟨r, Hr, Hwr⟩ := HR x1 x2 Hx1 Hx2
      refine ⟨r :: vs, ?_, ?_, ?_⟩
      · rintro ⟨⟨v, l1'⟩, l2'⟩ ht
        simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at ht
        rcases ht with ⟨⟨rfl, rfl⟩, rfl⟩ | ht
        · simpa [proj_lane__0] using Hr
        · exact H3 _ (by simpa using ht)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Hwr
        · exact Hw v hv
      · simp [Hs]

-- Ltac `vlane_close` (type_progress.v:2252) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

/-- Rocq `type_progress.v:2282` `vbinop_some`. On a well-formed shape and operator and two
    well-formed 128-bit vectors, `fun_vbinop_` has some (non-`none`) result. -/
theorem vbinop_some (sh : shape) (op : vbinop_) (c1 c2 : vec_) :
    wf_shape sh → wf_vbinop_ sh op → wf_uN 128 c1 → wf_uN 128 c2 →
    ∃ r, fun_vbinop_ sh op c1 c2 (some r) := by
  intro Hsh Hop H1 H2
  -- Rocq `inversion Hop`: integer shapes first, then float shapes.
  cases Hop
  · rename_i J M o Ho Hs
    subst Hs
    have HL1 := lanes_Jnn_form J M c1 Hsh H1
    have HL2 := lanes_Jnn_form J M c2 Hsh H2
    have HS1 := jlane_some _ _ HL1
    have HS2 := jlane_some _ _ HL2
    have Hsz := lanes_size_eq (lanetype_Jnn J) M c1 c2
    -- Rocq `destruct o`. After `cases J` the goals are I32, I64, I8, I16, which is the order of
    -- the generated `fun_vbinop__case_*` constructors; the (J, op) pairs excluded by the lane-size
    -- side condition of `wf_vbinop_Jnn_N` (`Hle`/`Hge`/`Heq`) are closed by `absurd`.
    cases o with
    | ADD =>
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => iadd_ (lsizenn (lanetype_Jnn J)) a b) _ _ rfl
        (fun a b Ha Hb => iadd__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_0 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_1 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_2 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_3 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | SUB =>
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => isub_ (lsizenn (lanetype_Jnn J)) a b) _ _ rfl
        (fun a b Ha Hb => isub__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_4 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_5 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_6 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_7 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | ADD_SAT sx =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 16 := by cases Ho; assumption
      -- `zip_lane_rel` gives the lane results `vs` (used for both `var_1_lst` and `var_0_lst`)
      obtain ⟨vs, H3, Hw, Hsv⟩ := zip_lane_rel J
        (fun a b r => fun_iadd_sat_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN (lsize (lanetype_Jnn J)) r) _ _
        (fun a b Ha Hb => iadd_sat_total_wf _ sx a b Ha Hb) HL1 HL2 Hsz
      have Hw' : Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs :=
        fun v hv => wf_lane_.lane__case_0 _ _ _ (Hw v hv) rfl
      cases J
      · exact absurd Hle (by decide)
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_18 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_19 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
    | SUB_SAT sx =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 16 := by cases Ho; assumption
      obtain ⟨vs, H3, Hw, Hsv⟩ := zip_lane_rel J
        (fun a b r => fun_isub_sat_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN (lsize (lanetype_Jnn J)) r) _ _
        (fun a b Ha Hb => isub_sat_total_wf _ sx a b Ha Hb) HL1 HL2 Hsz
      have Hw' : Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs :=
        fun v hv => wf_lane_.lane__case_0 _ _ _ (Hw v hv) rfl
      cases J
      · exact absurd Hle (by decide)
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_22 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_23 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
    | MUL =>
      have Hge : lsizenn (lanetype_Jnn J) ≥ 16 := by cases Ho; assumption
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => imul_ (lsizenn (lanetype_Jnn J)) a b) _ _ rfl
        (fun a b Ha Hb => imul__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_24 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_25 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact absurd Hge (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_27 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | AVGRU =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 16 := by cases Ho; assumption
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => iavgr_ (lsizenn (lanetype_Jnn J)) sx.U a b) _ _ rfl
        (fun a b Ha Hb => iavgr__is_wf _ _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact absurd Hle (by decide)
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_30 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_31 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | Q15MULR_SATS =>
      have Heq : lsizenn (lanetype_Jnn J) = 16 := by cases Ho; assumption
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => iq15mulr_sat_ (lsizenn (lanetype_Jnn J)) sx.S a b) _ _ rfl
        (fun a b Ha Hb => iq15mulr_sat__is_wf _ _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact absurd Heq (by decide)
      · exact absurd Heq (by decide)
      · exact absurd Heq (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_35 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | MIN sx =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 32 := by cases Ho; assumption
      obtain ⟨vs, H3, Hw, Hsv⟩ := zip_lane_rel J
        (fun a b r => fun_imin_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN (lsize (lanetype_Jnn J)) r) _ _
        (fun a b Ha Hb => imin_total_wf _ sx a b Ha Hb) HL1 HL2 Hsz
      have Hw' : Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs :=
        fun v hv => wf_lane_.lane__case_0 _ _ _ (Hw v hv) rfl
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_8 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_10 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_11 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
    | MAX sx =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 32 := by cases Ho; assumption
      obtain ⟨vs, H3, Hw, Hsv⟩ := zip_lane_rel J
        (fun a b r => fun_imax_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN (lsize (lanetype_Jnn J)) r) _ _
        (fun a b Ha Hb => imax_total_wf _ sx a b Ha Hb) HL1 HL2 Hsz
      have Hw' : Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs :=
        fun v hv => wf_lane_.lane__case_0 _ _ _ (Hw v hv) rfl
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_12 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_14 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_15 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
  · -- float shapes: the result list is `v128_lst`, built from `setproduct_` of the lane results
    rename_i F M o Hs
    subst Hs
    have HL1 := lanes_Fnn_form F M c1 Hsh H1
    have HL2 := lanes_Fnn_form F M c2 Hsh H2
    have Hsz := lanes_size_eq (lanetype_Fnn F) M c1 c2
    cases o with
    | ADD =>
      have hz := zip_flane_wf F fadd_ _ _ (fun a b Ha Hb => fadd__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_36 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_37 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | SUB =>
      have hz := zip_flane_wf F fsub_ _ _ (fun a b Ha Hb => fsub__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_38 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_39 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | MUL =>
      have hz := zip_flane_wf F fmul_ _ _ (fun a b Ha Hb => fmul__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_40 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_41 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | DIV =>
      have hz := zip_flane_wf F fdiv_ _ _ (fun a b Ha Hb => fdiv__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_42 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_43 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | MIN =>
      have hz := zip_flane_wf F fmin_ _ _ (fun a b Ha Hb => fmin__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_44 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_45 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | MAX =>
      have hz := zip_flane_wf F fmax_ _ _ (fun a b Ha Hb => fmax__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_46 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_47 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | PMIN =>
      have hz := zip_flane_wf F fpmin_ _ _ (fun a b Ha Hb => fpmin__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_48 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_49 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | PMAX =>
      have hz := zip_flane_wf F fpmax_ _ _ (fun a b Ha Hb => fpmax__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_50 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_51 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩

/-- Rocq `type_progress.v:2327` `mk_uN_eta`. Eta law for `uN`; Rocq's coercion `(u :> N)` is
    `proj_uN_0 u`. -/
theorem mk_uN_eta (u : uN) : uN.mk_uN (proj_uN_0 u) = u := by
  cases u
  rfl

/-- Rocq `type_progress.v:2332` `res_bool_bit`. A boolean result is a 1-bit integer. Rocq's
    `res_bool` is Lean's generated `nat_of_bool` (same spectec definition,
    3-numerics.spectec:9.1-9.22). -/
theorem res_bool_bit (b : Bool) : wf_uN 1 (uN.mk_uN (nat_of_bool b)) := by
  apply iswf_uN_of_lt
  cases b <;> simp [nat_of_bool]

/-- Rocq `type_progress.v:2335` `ieq_bit`. The result of `ieq_` is a 1-bit integer
    (`(· :> N)` is `proj_uN_0`). -/
theorem ieq_bit (v_N : N) (a b : iN) : wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ v_N a b))) := by
  exact res_bool_bit _

/-- Rocq `type_progress.v:2338` `ine_bit`. The result of `ine_` is a 1-bit integer. -/
theorem ine_bit (v_N : N) (a b : iN) : wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ v_N a b))) := by
  exact res_bool_bit _

/-- Rocq `type_progress.v:2341` `icmp_total_bit`. On well-formed operands, each of
    `fun_ilt_`/`fun_igt_`/`fun_ile_`/`fun_ige_` has a result, and that result is a 1-bit integer. -/
theorem icmp_total_bit (v_N : N) (v_sx : sx) (i1 i2 : iN) :
    wf_uN v_N i1 → wf_uN v_N i2 →
    (∃ r, fun_ilt_ v_N v_sx i1 i2 r ∧ wf_uN 1 (uN.mk_uN (proj_uN_0 r))) ∧
    (∃ r, fun_igt_ v_N v_sx i1 i2 r ∧ wf_uN 1 (uN.mk_uN (proj_uN_0 r))) ∧
    (∃ r, fun_ile_ v_N v_sx i1 i2 r ∧ wf_uN 1 (uN.mk_uN (proj_uN_0 r))) ∧
    (∃ r, fun_ige_ v_N v_sx i1 i2 r ∧ wf_uN 1 (uN.mk_uN (proj_uN_0 r))) := by
  intro H1 H2
  obtain ⟨r1, Hr1⟩ := ilt_total v_N v_sx i1 i2 H1 H2
  obtain ⟨r2, Hr2⟩ := igt_total v_N v_sx i1 i2 H1 H2
  obtain ⟨r3, Hr3⟩ := ile_total v_N v_sx i1 i2 H1 H2
  obtain ⟨r4, Hr4⟩ := ige_total v_N v_sx i1 i2 H1 H2
  refine ⟨⟨r1, Hr1, ?_⟩, ⟨r2, Hr2, ?_⟩, ⟨r3, Hr3, ?_⟩, ⟨r4, Hr4, ?_⟩⟩
  · cases Hr1 <;> exact res_bool_bit _
  · cases Hr2 <;> exact res_bool_bit _
  · cases Hr3 <;> exact res_bool_bit _
  · cases Hr4 <;> exact res_bool_bit _

/-- Rocq `type_progress.v:2360` `Forall_zipWith`. If `f` always lands in `P`, every element of
    `zipWith f l1 l2` satisfies `P`. Rocq's `list_zipWith` (map over the truncating `zip`) is
    `List.zipWith`. -/
theorem Forall_zipWith (A B C : Type) (P : C → Prop) (f : A → B → C) (l1 : List A) (l2 : List B) :
    (∀ a b, P (f a b)) → Forall P (List.zipWith f l1 l2) := by
  intro H
  induction l1 generalizing l2 with
  | nil => intro x hx; simp [List.zipWith] at hx
  | cons a l1 IH =>
    cases l2 with
    | nil => intro x hx; simp [List.zipWith] at hx
    | cons b l2 =>
      intro x hx
      simp only [List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact H a b
      · exact IH l2 x hx

/-- Rocq `type_progress.v:2367` `Forall2_all`. A total relation holds pairwise on equal-length
    lists. The zip-based `Forall₂` conclusion lacks the length fact, which is the premise here, so
    the statement is equivalent to Rocq's. -/
theorem Forall2_all (A B : Type) (P : A → B → Prop) (l1 : List A) (l2 : List B) :
    (∀ a b, P a b) → l1.length = l2.length → Forall₂ P l1 l2 := by
  intro H _ t _
  exact H t.1 t.2

/-- Rocq `type_progress.v:2375` `Forall_map_P`. `Forall` transported along `map f` when `f`
    sends `Q`-elements to `P`-elements. -/
theorem Forall_map_P (A B : Type) (P : B → Prop) (Q : A → Prop) (f : A → B) (l : List A) :
    (∀ a, Q a → P (f a)) → Forall Q l → Forall P (List.map f l) := by
  intro H Hl x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact H a (Hl a ha)

-- Ltac `bit_close` (type_progress.v:2380) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

-- Ltac `vrelop_close` (type_progress.v:2386) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

/-- Rocq `type_progress.v:2400` `vrelop_some`. On a well-formed shape and operator and two
    well-formed 128-bit vectors, `fun_vrelop_` has some (non-`none`) result. -/
theorem vrelop_some (sh : shape) (op : vrelop_) (c1 c2 : vec_) :
    wf_shape sh → wf_vrelop_ sh op → wf_uN 128 c1 → wf_uN 128 c2 →
    ∃ r, fun_vrelop_ sh op c1 c2 (some r) := by
  intro Hsh Hop H1 H2
  -- Lean's `Map₂` is `zipWith` (Rocq's `list_zipWith`)
  have hMap2 : ∀ (α β γ : Type) (f : α → β → γ) (l1 : List α) (l2 : List β),
      Map₂ f l1 l2 = List.zipWith f l1 l2 := by
    intro α β γ f l1 l2
    simp [Map₂, List.ap, List.zipWith_map_left]
  cases Hop with
  | vrelop__case_0 J M o Ho Hs =>
    -- integer lane shapes
    subst Hs
    have HL1 := lanes_Jnn_form J M c1 Hsh H1
    have HL2 := lanes_Jnn_form J M c2 Hsh H2
    have HS1 := jlane_some _ _ HL1
    have HS2 := jlane_some _ _ HL2
    have Hsz := lanes_size_eq (lanetype_Jnn J) M c1 c2
    rcases o with _ | _ | sx | sx | sx | sx
    case' LT =>
      obtain ⟨vs, H3, Hw, Hvs⟩ := zip_lane_rel J (fun a b r => fun_ilt_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN 1 (uN.mk_uN (proj_uN_0 r))) _ _
        (fun a b Ha Hb => (icmp_total_bit _ sx a b Ha Hb).1) HL1 HL2 Hsz
    case' GT =>
      obtain ⟨vs, H3, Hw, Hvs⟩ := zip_lane_rel J (fun a b r => fun_igt_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN 1 (uN.mk_uN (proj_uN_0 r))) _ _
        (fun a b Ha Hb => (icmp_total_bit _ sx a b Ha Hb).2.1) HL1 HL2 Hsz
    case' LE =>
      obtain ⟨vs, H3, Hw, Hvs⟩ := zip_lane_rel J (fun a b r => fun_ile_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN 1 (uN.mk_uN (proj_uN_0 r))) _ _
        (fun a b Ha Hb => (icmp_total_bit _ sx a b Ha Hb).2.2.1) HL1 HL2 Hsz
    case' GE =>
      obtain ⟨vs, H3, Hw, Hvs⟩ := zip_lane_rel J (fun a b r => fun_ige_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN 1 (uN.mk_uN (proj_uN_0 r))) _ _
        (fun a b Ha Hb => (icmp_total_bit _ sx a b Ha Hb).2.2.2) HL1 HL2 Hsz
    all_goals cases J
    -- Rocq: `eexists; econstructor`
    all_goals (apply Exists.intro; constructor)
    -- the equations defining the lane lists / result (Rocq: `apply: eqxx`)
    all_goals try (first
      | exact (rfl : (_ : List lane_) = _)
      | exact (rfl : (_ : List iN) = _)
      | exact (rfl : (_ : vec_) = _))
    all_goals try exact H3
    -- Rocq's `vrelop_close`
    all_goals try (first
      | exact HS1 | exact HS2 | exact Hsz | exact Hsh | exact Hvs | exact Hvs.trans Hsz | exact Hw
      | exact rfl
      | exact Forall2_all _ _ _ _ _ (fun _ _ => ieq_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => ine_bit _ _ _) Hsz
      | (rw [hMap2]; apply Forall_zipWith; intro a b
         exact wf_lane_.lane__case_0 _ _ _ (extend___is_wf _ _ _ _ _ (by first | exact ieq_bit _ _ _ | exact ine_bit _ _ _) rfl) rfl)
      | (refine Forall_map_P _ _ _ _ _ _ ?_ Hw
         intro a ha
         exact wf_lane_.lane__case_0 _ _ _ (extend___is_wf _ _ _ _ _ ha rfl) rfl))
  | vrelop__case_1 F M o Hs =>
    -- float lane shapes
    subst Hs
    have HL1 := lanes_Fnn_form F M c1 Hsh H1
    have HL2 := lanes_Fnn_form F M c2 Hsh H2
    have HS1 := flane_some _ _ HL1
    have HS2 := flane_some _ _ HL2
    have Hsz := lanes_size_eq (lanetype_Fnn F) M c1 c2
    cases F
    all_goals cases o
    all_goals (apply Exists.intro; constructor)
    -- choose `v_Inn` with `isize v_Inn = size F` (Rocq: `exact: (eqxx (isize Inn_I32))`)
    all_goals try (first | exact (rfl : isize Inn.I32 = _) | exact (rfl : isize Inn.I64 = _))
    all_goals try (first
      | exact (rfl : (_ : List lane_) = _)
      | exact (rfl : (_ : List iN) = _)
      | exact (rfl : (_ : vec_) = _))
    all_goals try (first
      | exact HS1 | exact HS2 | exact Hsz | exact Hsh
      | (cases Hsh with | shape_case_0 _ _ hd hm => exact wf_shape.shape_case_0 _ _ hd hm)
      | exact rfl | decide
      | exact Forall2_all _ _ _ _ _ (fun _ _ => feq_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => fne_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => flt_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => fgt_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => fle_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => fge_bit _ _ _) Hsz
      | (rw [hMap2]; apply Forall_zipWith; intro a b
         exact wf_lane_.lane__case_0 _ _ _ (extend___is_wf _ _ _ _ _ (by first | exact feq_bit _ _ _ | exact fne_bit _ _ _ | exact flt_bit _ _ _ | exact fgt_bit _ _ _ | exact fle_bit _ _ _ | exact fge_bit _ _ _) rfl) rfl))

/-- Rocq `type_progress.v:2442` `invsigned_total_32m1`. `fun_inv_signed_ 32` is defined at
    `-1` (Rocq's `(0 - 1)%Z`, kept literally as `(0 : Int) - 1`). -/
theorem invsigned_total_32m1 : ∃ ret, fun_inv_signed_ 32 ((0 : Int) - 1) ret := by
  exact invsigned_total 32 _ (by decide) (by decide)

/-- Rocq `type_progress.v:2447` `Forall_list_slice`. `Forall` is preserved by slicing; Rocq's
    `list_slice l i j` (drop `i`, then take `j`) is `List.take j (List.drop i l)`, as in the
    generated code. `T` is implicit, as in Rocq. -/
theorem Forall_list_slice {T : Type} (P : T → Prop) (l : List T) (i j : N) :
    Forall P l → Forall P (List.take j (List.drop i l)) := by
  intro H x hx
  exact H x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-- Rocq `type_progress.v:2458` `mem_bytes_wf`. The bytes of any entry `ms[k]!` (Rocq
    `ms [| k |]`, default-valued out of range) of a list of well-formed memory instances are
    well-formed bytes. -/
theorem mem_bytes_wf (ms : List meminst) (k : N) :
    Forall wf_meminst ms → Forall wf_byte ((ms[k]!).BYTES) := by
  intro Hall
  by_cases E : k < ms.length
  · have H : wf_meminst (ms[k]!) := by
      rw [getElem!_pos ms k E]
      exact Hall _ (List.getElem_mem E)
    generalize ms[k]! = m at H ⊢
    cases H with
    | meminst_case_ _ _ _ h => exact h
  · rw [getElem!_neg ms k E]
    have hd : (default : meminst).BYTES = [] := rfl
    rw [hd]
    intro b hb
    simp at hb

/-- Rocq `type_progress.v:2471` `wf_config_mem_bytes`. In a well-formed configuration, the bytes
    of the memory `fun_mem (state.mk_state s f) x` are well-formed. -/
theorem wf_config_mem_bytes (s : store) (f : frame) (ais : List admininstr) (x : memidx) :
    wf_config (config.mk_config (state.mk_state s f) ais) →
    Forall wf_byte ((fun_mem (state.mk_state s f) x).BYTES) := by
  intro H
  cases H with
  | config_case_0 _ _ hs _ =>
    cases hs with
    | state_case_0 _ _ hst _ =>
      cases hst with
      | store_case_ _ _ _ _ _ _ _ _ _ h _ =>
        exact mem_bytes_wf _ _ h

/-- Rocq `type_progress.v:2486` `all_and_Forall`. A boolean `all` over a conjunction splits into
    two `Forall`s. Rocq's mathcomp `all` is `List.all`; bool-to-Prop coercions (`is_true`) are
    `· = true`. -/
theorem all_and_Forall (T : Type) (P Q : T → Bool) (l : List T) :
    List.all l (fun x => P x && Q x) = true →
    Forall (fun x => P x = true) l ∧ Forall (fun x => Q x = true) l := by
  intro h
  rw [List.all_eq_true] at h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have := h x hx
    rw [Bool.and_eq_true] at this
    exact this.1
  · have := h x hx
    rw [Bool.and_eq_true] at this
    exact this.2

/-- Rocq `type_progress.v:2494` `Forall_and_all`. Converse of `all_and_Forall`. -/
theorem Forall_and_all (T : Type) (P Q : T → Bool) (l : List T) :
    Forall (fun x => P x = true) l → Forall (fun x => Q x = true) l →
    List.all l (fun x => P x && Q x) = true := by
  intro HP HQ
  rw [List.all_eq_true]
  intro x hx
  rw [Bool.and_eq_true]
  exact ⟨HP x hx, HQ x hx⟩

/-- Rocq `type_progress.v:2503` `packnum_not_none`. Packing a well-formed number of the
    unpacked type of `lt` never fails (Rocq's boolean `!= None` is `≠ none`). -/
theorem packnum_not_none (lt : lanetype) (c : num_) :
    wf_num_ (unpack lt) c → packnum_ lt c ≠ none := by
  intro Hwf
  rcases c with ⟨I, x⟩ | ⟨F, x⟩ <;> cases lt <;> (try cases I) <;> (try cases F)
  all_goals first
    | (simp [packnum_]; done)
    | (simp [packnum_, OMap, size, valtype_numtype, unpack, lanetype_packtype]; done)
    | (exfalso; cases Hwf; simp_all [unpack, numtype_Inn, numtype_Fnn])

/-- Rocq `type_progress.v:2513` `lanes_nth_wf`. Every in-range lane (`k < v_N`, Rocq `%BN`) of a
    well-formed 128-bit vector at a well-formed shape is a well-formed lane. -/
theorem lanes_nth_wf (lt : lanetype) (v_N : N) (c : vec_) (k : N) :
    wf_shape (shape.X lt (dim.mk_dim v_N)) →
    wf_uN 128 c →
    k < v_N →
    wf_lane_ lt ((lanes_ (shape.X lt (dim.mk_dim v_N)) c)[k]!) := by
  intro Hsh Hc Hk
  have Hall := lanes__is_wf (shape.X lt (dim.mk_dim v_N)) c _ Hsh Hc rfl
  have H := Forall_size _ _ Hall k
  rw [lanes_len] at H
  exact H Hk

/-- Rocq `type_progress.v:2527` `vstore_lane_progress`. `VSTORE_LANE` on lane type `J` with `M`
    lanes, an in-range lane index and an `I32` address always steps. Rocq's premise
    `Qeq_bool (M : Q) ((128%num : Q) / ((jsize J) : Q))%Q = true` (decidable `Qeq`) is stated as
    `=` on Lean's normalized `Rat`, exactly as the generated `Step.vstore_lane_val` renders the same
    spectec premise; `(laneidx :> N)` is `proj_uN_0 laneidx`. -/
theorem vstore_lane_progress (s : store) (f : frame) (n1 : N) (memarg : memarg) (laneidx : laneidx)
    (c1 : vec_) (J : Jnn) (M : N) :
    wf_uN 128 c1 →
    wf_shape (shape.X (lanetype_Jnn J) (dim.mk_dim M)) →
    proj_uN_0 laneidx < M →
    (M : Rat) = ((128 : Rat) / (jsize J : Rat)) →
    ∃ (s' : store) (f' : frame) (es' : List admininstr), Step
      (config.mk_config (state.mk_state s f)
        [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)),
         admininstr.VCONST vectype.V128 c1,
         admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz (jsize J)) memarg laneidx])
      (config.mk_config (state.mk_state s' f') es') := by
  intro Hc Hsh Hk HM
  have Hl := lanes_nth_wf _ _ _ _ Hsh Hc Hk
  obtain ⟨x, Hx, Hwx⟩ := wf_lane_Jnn_inv J _ Hl (wf_lane_Jnn_some J _ Hl)
  refine ⟨_, _, _, Step.vstore_lane_val (state.mk_state s f) _ c1 (jsize J) memarg laneidx _ J M ?_ rfl HM ?_ ?_ rfl ?_⟩
  · simp [proj_num__0]
  · rw [Hx]; simp [proj_lane__0]
  · rw [lanes_len]; exact Hk
  · rw [Hx]; exact Hwx

/-- Rocq `type_progress.v:2551` `Forall2_map_l`. `Forall₂ R (map f l) l` from a pointwise fact.
    The zip-based `Forall₂` conclusion lacks the length fact, which holds trivially here
    (`map` preserves length), so the statement is equivalent to Rocq's. -/
theorem Forall2_map_l (A B : Type) (R : B → A → Prop) (f : A → B) (l : List A) :
    Forall (fun a => R (f a) a) l → Forall₂ R (List.map f l) l := by
  intro H
  induction l with
  | nil => intro t ht; simp at ht
  | cons a l ih =>
    intro t ht
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact H a (List.mem_cons_self ..)
    · exact ih (fun x hx => H x (List.mem_cons_of_mem _ hx)) t ht

/-- Rocq `type_progress.v:2556` `invert_typeof_I32_wf`. A well-formed value of type `I32` is a
    `CONST I32` of an in-range (32-bit) integer. -/
theorem invert_typeof_I32_wf (v : val) :
    typeof v = valtype.I32 → wf_val v →
    ∃ k, admininstr_val v = admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN k)) ∧
      wf_uN 32 (uN.mk_uN k) := by
  intro Ht Hwf
  obtain ⟨n, Heqv, Hwfn⟩ := invert_typeof_numtype_wf v numtype.I32 Ht Hwf
  cases Hwfn with
  | num__case_0 I x Hr Hx Hnt =>
    cases I with
    | I32 =>
      cases x with
      | mk_uN k => exact ⟨k, Heqv, Hx⟩
    | I64 => cases Hnt
  | num__case_1 F x Hx Hnt => cases F <;> cases Hnt

/-- Rocq `type_progress.v:2568` `size_list_repeat`. `list_repeat x n` (Lean `List.replicate n x`)
    has length `n`. In Lean this is core `List.length_replicate`; kept by name for the 1-1 port. -/
theorem size_list_repeat (X : Type) (x : X) (n : N) : (List.replicate n x).length = n := by
  simp

/-- Rocq `type_progress.v:2575` `Forall_list_repeat`. Every element of `List.replicate n x`
    (Rocq `list_repeat x n`) satisfies `P` when `x` does. -/
theorem Forall_list_repeat (X : Type) (P : X → Prop) (x : X) (n : N) :
    P x → Forall P (List.replicate n x) := by
  intro hx t ht
  rw [List.eq_of_mem_replicate ht]
  exact hx

/-- Rocq `type_progress.v:2579` `bit_of_wf1`. A 1-bit integer is a well-formed `bit`. -/
theorem bit_of_wf1 (i : N) : wf_uN 1 (uN.mk_uN i) → wf_bit (bit.mk_bit i) := by
  intro H
  cases H with
  | uN_case_0 _ Hb =>
    have Hle : i ≤ 1 := by simpa using Hb.2
    exact wf_bit.bit_case_0 i (Nat.le_one_iff_eq_zero_or_eq_one.mp Hle)

/-- Rocq `type_progress.v:2587` `wf_dim_le16`. A well-formed dimension is at most 16. -/
theorem wf_dim_le16 (M : N) : wf_dim (dim.mk_dim M) → M ≤ 16 := by
  intro H
  cases H with
  | dim_case_0 i Hi => rcases Hi with (((h | h) | h) | h) | h <;> simp [h]

/-- Rocq `type_progress.v:2594` `wf_ishape_inv`. An integer shape is a well-formed shape with a
    `Jnn` lane type and at most 16 lanes. -/
theorem wf_ishape_inv (sh : ishape) :
    wf_ishape sh →
    ∃ (J : Jnn) (M : N), sh = ishape.mk_ishape (shape.X (lanetype_Jnn J) (dim.mk_dim M)) ∧
      wf_shape (shape.X (lanetype_Jnn J) (dim.mk_dim M)) ∧ M ≤ 16 := by
  intro H
  cases H with
  | ishape_case_0 J sh' Hs Hlt =>
    cases sh' with
    | X lt d =>
      cases d with
      | mk_dim M =>
        simp only [fun_lanetype] at Hlt
        subst Hlt
        refine ⟨J, M, rfl, Hs, ?_⟩
        cases Hs with
        | shape_case_0 _ _ Hd _ => exact wf_dim_le16 M Hd

/-- Rocq `type_progress.v:2604` `holds_upto_intro`. Introduction rule for `holds_upto`
    (`TLC.holds_upto`, ExtensionLemmas.lean:89, = `Forall P (List.range n)`, Rocq
    `Forall P (iotaN 0 n)`). -/
theorem holds_upto_intro (P : N → Prop) (n : N) :
    (∀ (k : N), k < n → P k) → holds_upto P n := by
  intro H k hk
  exact H k (List.mem_range.mp hk)

/-- Rocq `type_progress.v:2614` `jlane_proj_wf`. Projecting a list of well-formed `J`-lanes to
    their integers gives well-formed integers. -/
theorem jlane_proj_wf (J : Jnn) (L : List lane_) :
    Forall (jlane J) L →
    Forall (fun x => wf_uN (lsize (lanetype_Jnn J)) x) (List.map (fun l => Option.get! (proj_lane__0 l)) L) := by
  intro H x hx
  simp only [List.mem_map] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  obtain ⟨y, rfl, hy⟩ := H l hl
  exact hy

/-- Rocq `type_progress.v:2619` `jlane_map_proj`. Re-injecting the projected integers of a list
    of `J`-lanes gives back the list. -/
theorem jlane_map_proj (J : Jnn) (L : List lane_) :
    Forall (jlane J) L →
    List.map (fun c => lane_.mk_lane__0 J c) (List.map (fun l => Option.get! (proj_lane__0 l)) L) = L := by
  intro H
  induction L with
  | nil => rfl
  | cons l L ih =>
    obtain ⟨x, rfl, _⟩ := H l (List.mem_cons_self ..)
    have := ih (fun t ht => H t (List.mem_cons_of_mem _ ht))
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨rfl, this⟩

/-- Rocq `type_progress.v:2625` `evens`: the elements at even positions (of an even-length list). -/
def evens {T : Type} : List T → List T
  | a :: _ :: l' => a :: evens l'
  | _ => []

/-- Rocq `type_progress.v:2630` `odds`: the elements at odd positions. -/
def odds {T : Type} : List T → List T
  | _ :: b :: l' => b :: odds l'
  | _ => []

/-- Rocq `type_progress.v:2636` `evens_odds_ind`. Two-step list induction: a property of `[]`, of
    every singleton, and preserved by consing two elements, holds of every list. -/
theorem evens_odds_ind (T : Type) (P : List T → Prop) :
    P [] → (∀ a, P [a]) → (∀ a b l, P l → P (a :: b :: l)) → ∀ l, P l := by
  intro H0 H1 H2
  have H : ∀ (n : Nat) (l : List T), l.length ≤ n → P l := by
    intro n
    induction n with
    | zero =>
      intro l hl
      cases l with
      | nil => exact H0
      | cons a l => simp at hl
    | succ n ih =>
      intro l hl
      match l with
      | [] => exact H0
      | [a] => exact H1 a
      | a :: b :: l =>
        apply H2
        apply ih
        simp at hl
        omega
  intro l
  exact H l.length l (Nat.le_refl _)

/-- Rocq `type_progress.v:2645` `evens_odds_concat`. For an even-length list, interleaving
    `evens l` and `odds l` again gives back `l`. Rocq's mathcomp `~~ odd (size l)` is stated as
    `¬ Odd l.length` (Mathlib `Odd`). Rocq's `T : eqType` is only forced by Rocq's `concat_`
    (`X : eqType`); Lean's generated `concat_` takes a plain `Type`, so `T : Type` here. -/
theorem evens_odds_concat (T : Type) (l : List T) :
    ¬ Odd l.length →
    concat_ T (List.zipWith (fun a b => [a, b]) (evens l) (odds l)) = l := by
  revert l
  apply evens_odds_ind T (fun l => ¬ Odd l.length → concat_ T (List.zipWith (fun a b => [a, b]) (evens l) (odds l)) = l)
  · intro _
    simp [evens, odds, concat_]
  · intro a h
    exfalso
    exact h (by simp)
  · intro a b l IH Hl
    have hl' : ¬ Odd l.length := by
      intro hodd
      apply Hl
      simp only [List.length_cons]
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m + 1, by omega⟩
    have IH' := IH hl'
    simp [evens, odds, concat_, IH']

/-- Rocq `type_progress.v:2652` `evens_odds_size`. For an even-length list, `evens l` and
    `odds l` have the same length (`~~ odd (size l)` stated as `¬ Odd l.length`). -/
theorem evens_odds_size (T : Type) (l : List T) :
    ¬ Odd l.length → (evens l).length = (odds l).length := by
  refine evens_odds_ind T (fun l => ¬ Odd l.length → (evens l).length = (odds l).length) ?_ ?_ ?_ l
  · intro _
    simp [evens, odds]
  · intro a h
    exact absurd ⟨0, by simp⟩ h
  · intro a b l IH Hl
    have Hl' : ¬ Odd l.length := by
      intro ho
      apply Hl
      rw [Nat.odd_iff] at ho ⊢
      simp only [List.length_cons]
      omega
    simp only [evens, odds, List.length_cons]
    rw [IH Hl']

/-- Rocq `type_progress.v:2658` `Forall_evens`. `Forall P` passes from a list to its
    even-position elements. -/
theorem Forall_evens (T : Type) (P : T → Prop) (l : List T) :
    Forall P l → Forall P (evens l) := by
  refine evens_odds_ind T (fun l => Forall P l → Forall P (evens l)) ?_ ?_ ?_ l
  · intro _ x hx
    simp [evens] at hx
  · intro a _ x hx
    simp [evens] at hx
  · intro a b l IH H x hx
    simp only [evens, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact H _ (by simp)
    · exact IH (fun y hy => H y (by simp [hy])) x hx

/-- Rocq `type_progress.v:2664` `Forall_odds`. `Forall P` passes from a list to its
    odd-position elements. -/
theorem Forall_odds (T : Type) (P : T → Prop) (l : List T) :
    Forall P l → Forall P (odds l) := by
  refine evens_odds_ind T (fun l => Forall P l → Forall P (odds l)) ?_ ?_ ?_ l
  · intro _ x hx
    simp [odds] at hx
  · intro a _ x hx
    simp [odds] at hx
  · intro a b l IH H x hx
    simp only [odds, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact H _ (by simp)
    · exact IH (fun y hy => H y (by simp [hy])) x hx

/-- Rocq `type_progress.v:2670` `Forall2_of_Forall`. If `Q` relates any two `W`-elements, then two
    equal-length lists of `W`-elements are `Forall₂ Q`-related. (Rocq's inductive `Forall2` also
    carries the length equation, which here is already the premise `l1.length = l2.length`, so the
    zip-based `Forall₂` conclusion loses nothing.) -/
theorem Forall2_of_Forall (A : Type) (W : A → Prop) (Q : A → A → Prop) (l1 l2 : List A) :
    (∀ a b, W a → W b → Q a b) → Forall W l1 → Forall W l2 → l1.length = l2.length →
    Forall₂ Q l1 l2 := by
  intro HQ H1 H2 _ t ht
  obtain ⟨a, b⟩ := t
  have h := List.of_mem_zip ht
  exact HQ a b (H1 a h.1) (H2 b h.2)

/-- Rocq `type_progress.v:2679` `list_slice_size_eq`. Slicing two equal-length lists at the same
    `i`, `j` gives equal-length results. Rocq's `list_slice l i j` (drop `i`, then take `j`) is
    written `List.take j (List.drop i l)`. -/
theorem list_slice_size_eq (A B : Type) (l1 : List A) (l2 : List B) (i j : Nat) :
    l1.length = l2.length →
    (List.take j (List.drop i l1)).length = (List.take j (List.drop i l2)).length := by
  intro h
  simp [List.length_take, List.length_drop, h]

/-- Rocq `type_progress.v:2687` `zip_lane_wf2`. Applying an `iN` function that maps well-formed
    `Ji`-width arguments to a well-formed `Jo`-width result, lane-wise to two equal-length lists of
    well-formed `Ji` lanes, gives well-formed `Jo` lanes. (The length equation of Rocq's `Forall2`
    conclusion is the premise `L1.length = L2.length`.) -/
theorem zip_lane_wf2 (Ji Jo : Jnn) (lt : lanetype) (f : iN → iN → iN) (L1 L2 : List lane_) :
    lt = lanetype_Jnn Jo →
    (∀ a b, wf_uN (lsize (lanetype_Jnn Ji)) a → wf_uN (lsize (lanetype_Jnn Ji)) b →
      wf_uN (lsize (lanetype_Jnn Jo)) (f a b)) →
    Forall (jlane Ji) L1 → Forall (jlane Ji) L2 → L1.length = L2.length →
    Forall₂ (fun l1 l2 => wf_lane_ lt
      (lane_.mk_lane__0 Jo (f (Option.get! (proj_lane__0 l1)) (Option.get! (proj_lane__0 l2))))) L1 L2 := by
  intro hlt Hf H1 H2 _ t ht
  obtain ⟨a, b⟩ := t
  have h := List.of_mem_zip ht
  obtain ⟨x1, rfl, Hx1⟩ := H1 a h.1
  obtain ⟨x2, rfl, Hx2⟩ := H2 b h.2
  exact wf_lane_.lane__case_0 lt Jo _ (Hf x1 x2 Hx1 Hx2) hlt

/-- Rocq `type_progress.v:2701` `zip_wf`. If `P (f a b)` holds for all well-formed `J` lanes `a`,
    `b`, then `P` holds of every element of `List.zipWith f L1 L2` (Rocq `list_zipWith`, which
    also truncates to the shorter list). -/
theorem zip_wf (J : Jnn) (P : iN → Prop) (f : lane_ → lane_ → iN) (L1 L2 : List lane_) :
    (∀ a b, jlane J a → jlane J b → P (f a b)) →
    Forall (jlane J) L1 → Forall (jlane J) L2 → Forall P (List.zipWith f L1 L2) := by
  intro Hf H1 H2 x hx
  rw [← List.map_uncurry_zip_eq_zipWith] at hx
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hx
  have h := List.of_mem_zip hab
  exact Hf a b (H1 a h.1) (H2 b h.2)

/-- Rocq `type_progress.v:2710` `size_zipWith_eq`. Zipping two equal-length lists keeps the
    length. -/
theorem size_zipWith_eq (A B C : Type) (f : A → B → C) (l1 : List A) (l2 : List B) :
    l1.length = l2.length → (List.zipWith f l1 l2).length = l1.length := by
  intro h
  simp [List.length_zipWith, h]

/-- Rocq `type_progress.v:2715` `shape_lanes_even`. A full-width integer shape `J X M`
    (`lsize J * M = 128`) has an even number of lanes (`~~ odd (size _)` stated as
    `¬ Odd _.length`). -/
theorem shape_lanes_even (J : Jnn) (M : Nat) (c : vec_) :
    lsize (lanetype_Jnn J) * M = 128 →
    ¬ Odd (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c).length := by
  intro H
  rw [lanes_len]
  cases J <;> simp only [lsize, lanetype_Jnn, psize, size, valtype_numtype, Option.get!] at H <;>
    (have : M = 16 ∨ M = 8 ∨ M = 4 ∨ M = 2 := by omega
     rcases this with rfl | rfl | rfl | rfl <;> decide)

/-- Rocq `type_progress.v:2727` `add_sub_parens`. `n1 + (n2 - n3) = (n1 + n2) - n3` across Rocq's
    `N`/`Z` coercions, given `n3 ≤ n2` in `Z`. Rocq elaborates the statement (checked with `coqc`)
    to `n1 + Z.to_N (Z.of_N n2 - n3) = Z.to_N (Z.of_N (n1 + n2) - n3)` with `n1 n2 : N` and
    `n3 : Z`; here `Z.of_N` is the `Nat → Int` cast and `Z.to_N` is `Int.toNat`. -/
theorem add_sub_parens (n1 : Nat) (n2 : Nat) (n3 : Int) :
    n3 ≤ (n2 : Int) →
    n1 + ((n2 : Int) - n3).toNat = (((n1 + n2 : Nat) : Int) - n3).toNat := by
  intro h
  omega

/-- Rocq `type_progress.v:2734` `call_indirect_progress`. `CONST I32 v_i; CALL_INDIRECT x y`
    always steps (to a call, or a trap) once `v_i` is an integer number. -/
theorem call_indirect_progress (s : store) (f : frame) (v_i : num_) (x : tableidx) (y : typeidx) :
    proj_num__0 v_i ≠ none →
    ∃ es, Step (config.mk_config (state.mk_state s f)
        ([admininstr.CONST numtype.I32 v_i] ++ [admininstr.CALL_INDIRECT x y]))
      (config.mk_config (state.mk_state s f) es) := by
  intro HNone
  by_cases h : Step_read_before_call_indirect_trap (config.mk_config (state.mk_state s f) [admininstr.CONST numtype.I32 v_i, admininstr.CALL_INDIRECT x y])
  · cases h with
    | call_indirect_call_0 _ _ _ _ a h1 h2 h3 h4 h5 =>
      exact ⟨[admininstr.CALL_ADDR a], Step.read _ _ _ (Step_read.call_indirect_call _ _ _ _ _ h1 h2 h3 h4 h5)⟩
  · exact ⟨[admininstr.TRAP], Step.read _ _ _ (Step_read.call_indirect_trap _ _ _ _ h)⟩

/-- Rocq `type_progress.v:2811` `vcvtop_trunc_sat_i16`: recognises `F32 → I16 TRUNC_SAT`, the
    `vcvtop` variant that the spec allows but cannot reduce (see `vcvtop_trunc_sat_i16_stuck`). -/
def vcvtop_trunc_sat_i16 (op : vcvtop__) : Bool :=
  match op with
  | .mk_vcvtop___2 Fnn.F32 _ Jnn.I16 _ (.TRUNC_SAT _ _) => true
  | _ => false

/-- Rocq `type_progress.v:2817` `vcvtop_lane_total`. Every well-formed `vcvtop` other than
    `F32 → I16 TRUNC_SAT` has a non-empty lane-wise result `$lcvtop__` on every well-formed lane.
    Rocq's `~~ vcvtop_trunc_sat_i16 op` is stated as `vcvtop_trunc_sat_i16 op = false`. -/
theorem vcvtop_lane_total (sh_1 sh_2 : shape) (op : vcvtop__) (ci : lane_) :
    wf_vcvtop__ sh_1 sh_2 op → vcvtop_trunc_sat_i16 op = false →
    wf_lane_ (fun_lanetype sh_1) ci →
    ∃ r, fun_lcvtop__ sh_1 sh_2 op ci (some r) ∧ r ≠ [] := by
  intro Hop Hts Hl
  have inj : ∀ a b : Jnn, lanetype_Jnn a = lanetype_Jnn b → a = b := by
    intro a b h
    cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)
  have injF : ∀ a b : Fnn, lanetype_Fnn a = lanetype_Fnn b → a = b := by
    intro a b h
    cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)
  have hJF : ∀ (a : Jnn) (b : Fnn), lanetype_Jnn a ≠ lanetype_Fnn b := by
    intro a b h
    cases a <;> cases b <;> (revert h; decide)
  have lJ : ∀ (J1 : Jnn) (c0 : lane_), wf_lane_ (lanetype_Jnn J1) c0 →
      ∃ c, c0 = lane_.mk_lane__0 J1 c := by
    intro J1 c0 h
    cases h with
    | lane__case_0 J c _ Heq => exact ⟨c, by rw [inj _ _ Heq]⟩
    | lane__case_1 F c _ Heq => exact absurd Heq (hJF _ _)
  have lF : ∀ (F1 : Fnn) (c0 : lane_), wf_lane_ (lanetype_Fnn F1) c0 →
      ∃ c, c0 = lane_.mk_lane__1 F1 c := by
    intro F1 c0 h
    cases h with
    | lane__case_0 J c _ Heq => exact absurd Heq.symm (hJF _ _)
    | lane__case_1 F c _ Heq => exact ⟨c, by rw [injF _ _ Heq]⟩
  have key : ∀ (f : iN → lane_) (o : Option iN), o ≠ none → list_ lane_ (OMap f o) ≠ [] := by
    intro f o ho
    cases o with
    | none => exact absurd rfl ho
    | some y => simp [list_, OMap]
  have keyL : ∀ (f : fN → lane_) (l : List fN), l ≠ [] → Map f l ≠ [] := by
    intro f l hl h
    exact hl (List.map_eq_nil_iff.mp h)
  cases Hop with
  | vcvtop___case_0 J1 M1 J2 M2 o Ho E1 E2 =>
    subst E1 E2
    obtain ⟨c, rfl⟩ := lJ J1 ci Hl
    cases o with
    | EXTEND h sx =>
      cases Ho with
      | vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 _ _ hs =>
        cases J1 <;> cases J2 <;>
        first
        | exact absurd hs (by decide)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_14 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_3 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_4 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
  | vcvtop___case_1 J1 M1 F2 M2 o Ho E1 E2 =>
    subst E1 E2
    obtain ⟨c, rfl⟩ := lJ J1 ci Hl
    cases o with
    | CONVERT ho sx =>
      cases Ho with
      | vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 _ _ hs =>
        rcases hs with ⟨⟨h1, h2⟩, _⟩ | ⟨h1, _⟩ <;> cases J1 <;> cases F2 <;>
        first
        | exact absurd h1 (by decide)
        | exact absurd h2 (by decide)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_16 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_19 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_20 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
  | vcvtop___case_2 F1 M1 J2 M2 o Ho E1 E2 =>
    subst E1 E2
    obtain ⟨c, rfl⟩ := lF F1 ci Hl
    cases o with
    | TRUNC_SAT sx zo =>
      cases Ho with
      | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 _ _ hs =>
        rcases hs with ⟨⟨h1, h2⟩, _⟩ | ⟨h1, _⟩ <;> cases F1 <;> cases J2 <;>
        first
        | exact absurd h1 (by decide)
        | exact absurd h2 (by decide)
        | (simp [vcvtop_trunc_sat_i16] at Hts; done)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_24 _ _ _ _ _ _ _ _ rfl rfl rfl, key _ _ (trunc_sat_total _ _ _ _)⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_25 _ _ _ _ _ _ _ _ rfl rfl rfl, key _ _ (trunc_sat_total _ _ _ _)⟩
  | vcvtop___case_3 F1 M1 F2 M2 o Ho E1 E2 =>
    subst E1 E2
    obtain ⟨c, rfl⟩ := lF F1 ci Hl
    cases o with
    | DEMOTE z =>
      cases Ho with
      | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 _ hs =>
        cases F1 <;> cases F2 <;>
        first
        | exact absurd hs (by decide)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_29 _ _ _ _ _ _ rfl rfl rfl, keyL _ _ (demote_nonempty _ _ _)⟩
    | PROMOTELOW =>
      cases Ho with
      | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 hs =>
        cases F1 <;> cases F2 <;>
        first
        | exact absurd hs (by decide)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_34 _ _ _ _ _ _ rfl rfl rfl, keyL _ _ (promote_nonempty _ _ _)⟩

/-- Rocq `type_progress.v:2849` `vcvtop_lanes_total`. The lane-wise results of a (non
    `F32 → I16 TRUNC_SAT`) conversion over a list of well-formed lanes: all defined, non-empty, and
    made of well-formed destination lanes. **Deviation:** the conjunct `vs.length = L.length` is
    added right after the `Forall₂` conjunct. Rocq's inductive `Forall2 _ vs L` implies
    `size vs = size L`, but Lean's zip-based `Forall₂` does not, and without the conjunct the
    statement would hold trivially with `vs = []`. -/
theorem vcvtop_lanes_total (sh_1 sh_2 : shape) (op : vcvtop__) (L : List lane_) :
    wf_shape sh_1 → wf_shape sh_2 →
    wf_vcvtop__ sh_1 sh_2 op → vcvtop_trunc_sat_i16 op = false →
    Forall (wf_lane_ (fun_lanetype sh_1)) L →
    ∃ vs : List (Option (List lane_)),
      Forall₂ (fun v ci => fun_lcvtop__ sh_1 sh_2 op ci v) vs L ∧
      vs.length = L.length ∧
      Forall (fun v => v ≠ none) vs ∧
      Forall (fun r => r ≠ []) (List.map (fun v => Option.get! v) vs) ∧
      Forall (Forall (wf_lane_ (fun_lanetype sh_2))) (List.map (fun v => Option.get! v) vs) := by
  intro Hs1 Hs2 Hop Hts HL
  have H : ∃ vs : List (Option (List lane_)),
      (Forall₂ (fun v ci => fun_lcvtop__ sh_1 sh_2 op ci v) vs L ∧ vs.length = L.length) ∧
      Forall (fun v => v ≠ none ∧ Option.get! v ≠ [] ∧
        Forall (wf_lane_ (fun_lanetype sh_2)) (Option.get! v)) vs := by
    apply Forall_exists_Forall2 (Option (List lane_)) lane_ (fun v ci => fun_lcvtop__ sh_1 sh_2 op ci v)
    intro ci Hci
    obtain ⟨r, Hr, Hne⟩ := vcvtop_lane_total _ _ _ _ Hop Hts (HL ci Hci)
    refine ⟨some r, Hr, by simp, by simpa using Hne, ?_⟩
    exact lcvtop___is_wf _ _ _ _ _ _ Hr Hs1 Hs2 Hop (HL ci Hci) (by simp) rfl
  obtain ⟨vs, ⟨H2, Hlen⟩, HP⟩ := H
  refine ⟨vs, H2, Hlen, ?_, ?_, ?_⟩
  · intro v hv
    exact (HP v hv).1
  · exact Forall_map_P _ _ _ _ _ _ (fun v hv => hv.2.1) HP
  · exact Forall_map_P _ _ _ _ _ _ (fun v hv => hv.2.2) HP

/-- Rocq `type_progress.v:2871` `setproduct2_Forall`. `setproduct2_` (prefix `w` to every list)
    preserves `Forall (Forall P)` when `P w`. Rocq's `X : eqType` (forced by Rocq's
    `setproduct2_`) is a plain `Type`, as Lean's generated `setproduct2_` takes. -/
theorem setproduct2_Forall (X : Type) (P : X → Prop) (w : X) (S : List (List X)) :
    P w → Forall (Forall P) S → Forall (Forall P) (setproduct2_ X w S) := by
  intro Hw HS
  induction S with
  | nil =>
    intro l hl
    simp [setproduct2_] at hl
  | cons s S' IH =>
    intro l hl
    simp only [setproduct2_, List.mem_append, List.mem_singleton] at hl
    rcases hl with rfl | hl
    · intro x hx
      simp only [List.singleton_append, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Hw
      · exact HS s (by simp) x hx
    · exact IH (fun t ht => HS t (List.mem_cons_of_mem _ ht)) l hl

/-- Rocq `type_progress.v:2875` `setproduct1_Forall`. `setproduct1_` preserves
    `Forall (Forall P)` when `Forall P l` (Rocq `X : eqType` → `Type`, as for
    `setproduct2_Forall`). -/
theorem setproduct1_Forall (X : Type) (P : X → Prop) (l : List X) (S : List (List X)) :
    Forall P l → Forall (Forall P) S → Forall (Forall P) (setproduct1_ X l S) := by
  intro Hl HS
  induction l with
  | nil => intro x hx; simp [setproduct1_] at hx
  | cons w l' ih =>
    have Hw : P w := Hl w (List.mem_cons_self ..)
    have Hl' : Forall P l' := fun x hx => Hl x (List.mem_cons_of_mem _ hx)
    have h2 := setproduct2_Forall X P w S Hw HS
    have h1 := ih Hl'
    intro x hx
    simp only [setproduct1_, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h2 x hx
    · exact h1 x hx

/-- Rocq `type_progress.v:2882` `setproduct_Forall`. Every list in the cartesian product
    `setproduct_ X ls` satisfies `Forall P` if every list of `ls` does (Rocq `X : eqType` →
    `Type`). -/
theorem setproduct_Forall (X : Type) (P : X → Prop) (ls : List (List X)) :
    Forall (Forall P) ls → Forall (Forall P) (setproduct_ X ls) := by
  intro H
  induction ls with
  | nil =>
    intro x hx
    simp only [setproduct_, List.mem_singleton] at hx
    subst hx
    intro y hy
    simp at hy
  | cons l ls' ih =>
    have Hl : Forall P l := H l (List.mem_cons_self ..)
    have Hls' : Forall (Forall P) ls' := fun x hx => H x (List.mem_cons_of_mem _ hx)
    exact setproduct1_Forall X P l (setproduct_ X ls') Hl (ih Hls')

/-- Rocq `type_progress.v:2889` `setproduct_nonempty`. The cartesian product of non-empty lists is
    non-empty (Rocq `X : eqType` → `Type`). -/
theorem setproduct_nonempty (X : Type) (ls : List (List X)) :
    Forall (fun l => l ≠ []) ls → setproduct_ X ls ≠ [] := by
  intro H
  induction ls with
  | nil => simp [setproduct_]
  | cons l ls' ih =>
    have Hl : l ≠ [] := H l (List.mem_cons_self ..)
    have Hls' : Forall (fun l => l ≠ []) ls' := fun x hx => H x (List.mem_cons_of_mem _ hx)
    have IH := ih Hls'
    simp only [setproduct_]
    cases l with
    | nil => exact absurd rfl Hl
    | cons w l' =>
      cases hS : setproduct_ X ls' with
      | nil => exact absurd hS IH
      | cons s S => simp [setproduct1_, setproduct2_]

/-- Rocq `type_progress.v:2897` `setproduct_pick`. Choosing a result vector from a non-empty,
    well-formed `setproduct_`. Rocq's boolean `(|l| >? 0)%BN` is stated as the Prop
    `l.length > 0`, and `c \in l` as `c ∈ l`. -/
theorem setproduct_pick (lt : lanetype) (M : Nat) (lss : List (List lane_)) :
    Forall (fun l => l ≠ []) lss → Forall (Forall (wf_lane_ lt)) lss →
    ∃ c : vec_,
      (List.map (fun cj => inv_lanes_ (shape.X lt (dim.mk_dim M)) cj) (setproduct_ lane_ lss)).length > 0 ∧
      c ∈ List.map (fun cj => inv_lanes_ (shape.X lt (dim.mk_dim M)) cj) (setproduct_ lane_ lss) ∧
      Forall (Forall (wf_lane_ lt)) (setproduct_ lane_ lss) := by
  intro Hne Hw
  have Hsp := setproduct_nonempty lane_ lss Hne
  have Hsw := setproduct_Forall lane_ (wf_lane_ lt) lss Hw
  revert Hsp Hsw
  cases hS : setproduct_ lane_ lss with
  | nil => intro Hsp; exact absurd rfl Hsp
  | cons cj S =>
    intro _ Hsw
    refine ⟨inv_lanes_ (shape.X lt (dim.mk_dim M)) cj, ?_, ?_, Hsw⟩
    · simp
    · simp

/-- Rocq `type_progress.v:2912` `halfop_of`. -/
def halfop_of (op : vcvtop__) : Option half :=
  match op with
  | .mk_vcvtop___0 _ _ _ _ (.EXTEND hf _) => some hf
  | .mk_vcvtop___1 _ _ _ _ (.CONVERT ho _) => ho
  | .mk_vcvtop___2 _ _ _ _ _ => none
  | .mk_vcvtop___3 _ _ _ _ (.DEMOTE _) => none
  | .mk_vcvtop___3 _ _ _ _ .PROMOTELOW => some half.LOW

/-- Rocq `type_progress.v:2921` `zeroop_of`. -/
def zeroop_of (op : vcvtop__) : Option zero :=
  match op with
  | .mk_vcvtop___0 _ _ _ _ _ => none
  | .mk_vcvtop___1 _ _ _ _ _ => none
  | .mk_vcvtop___2 _ _ _ _ (.TRUNC_SAT _ z) => z
  | .mk_vcvtop___3 _ _ _ _ (.DEMOTE z) => some z
  | .mk_vcvtop___3 _ _ _ _ .PROMOTELOW => none

-- Ltac `vcvtop_cases` (type_progress.v:2930) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

/-- Rocq `type_progress.v:2943` `halfop_total`. For a well-formed (non `F32 → I16 TRUNC_SAT`)
    `vcvtop`, `$halfop` is defined and equals `halfop_of op`. -/
theorem halfop_total (sh_1 sh_2 : shape) (op : vcvtop__) :
    wf_vcvtop__ sh_1 sh_2 op → vcvtop_trunc_sat_i16 op = false →
    fun_halfop sh_1 sh_2 op (some (halfop_of op)) := by
  intro Hop Hts
  cases Hop with
  | vcvtop___case_0 J1 M1 J2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases J1 <;> cases J2 <;> constructor <;> rfl
  | vcvtop___case_1 J1 M1 F2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases J1 <;> cases F2 <;> constructor <;> rfl
  | vcvtop___case_2 F1 M1 J2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases F1 <;> cases J2 <;> constructor <;> rfl
  | vcvtop___case_3 F1 M1 F2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx <;> (cases F1 <;> cases F2 <;> constructor <;> rfl)

/-- Rocq `type_progress.v:2951` `zeroop_total`. For a well-formed (non `F32 → I16 TRUNC_SAT`)
    `vcvtop`, `$zeroop` is defined and equals `zeroop_of op`. -/
theorem zeroop_total (sh_1 sh_2 : shape) (op : vcvtop__) :
    wf_vcvtop__ sh_1 sh_2 op → vcvtop_trunc_sat_i16 op = false →
    fun_zeroop sh_1 sh_2 op (some (zeroop_of op)) := by
  intro Hop Hts
  cases Hop with
  | vcvtop___case_0 J1 M1 J2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases J1 <;> cases J2 <;> constructor <;> rfl
  | vcvtop___case_1 J1 M1 F2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases J1 <;> cases F2 <;> constructor <;> rfl
  | vcvtop___case_2 F1 M1 J2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases F1 <;> cases J2 <;> constructor <;> rfl
  | vcvtop___case_3 F1 M1 F2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx <;> (cases F1 <;> cases F2 <;> constructor <;> rfl)

/-- Rocq `type_progress.v:2959` `zero_lane_wf`. Packing the zero of a number type into a lane
    succeeds and gives a well-formed lane. Rocq's `!(x)` (`the x`) is `Option.get! x`. -/
theorem zero_lane_wf (nt : numtype) :
    packnum_ (lanetype_numtype nt) (fun_zero nt) ≠ none ∧
    wf_lane_ (lanetype_numtype nt) (Option.get! (packnum_ (lanetype_numtype nt) (fun_zero nt))) := by
  have Hz : wf_num_ (unpack (lanetype_numtype nt)) (fun_zero nt) := by
    cases nt <;> exact zero_is_wf _ _ rfl
  have Hp := packnum_not_none _ _ Hz
  exact ⟨Hp, packnum__is_wf _ _ _ Hz Hp rfl⟩

/-- Rocq `type_progress.v:2969` `vcvtop_step_full`. A well-formed `VCVTOP` with neither half nor
    zero (and not `F32 → I16 TRUNC_SAT`) on a `V128` constant steps to a `V128` constant. -/
theorem vcvtop_step_full (L1 L2 : lanetype) (M : Nat) (op : vcvtop__) (c1 : uN) :
    wf_uN 128 c1 → wf_shape (shape.X L1 (dim.mk_dim M)) → wf_shape (shape.X L2 (dim.mk_dim M)) →
    wf_vcvtop__ (shape.X L1 (dim.mk_dim M)) (shape.X L2 (dim.mk_dim M)) op →
    vcvtop_trunc_sat_i16 op = false →
    halfop_of op = none → zeroop_of op = none →
    ∃ c, Step_pure [admininstr.VCONST vectype.V128 c1,
                    admininstr.VCVTOP (shape.X L2 (dim.mk_dim M)) (shape.X L1 (dim.mk_dim M)) op]
                   [admininstr.VCONST vectype.V128 c] := by
  intro Hc Hs1 Hs2 Hop Hts Hh Hz
  have Hl := lanes__is_wf _ _ _ Hs1 Hc rfl
  obtain ⟨vs, H2, Hn, Hne0, Hne, Hw⟩ := vcvtop_lanes_total _ _ _ _ Hs1 Hs2 Hop Hts Hl
  obtain ⟨c, Hgt, Hin, Hsw⟩ := setproduct_pick L2 M _ Hne Hw
  have Hhalf := halfop_total _ _ _ Hop Hts
  have Hzero := zeroop_total _ _ _ Hop Hts
  rw [Hh] at Hhalf
  rw [Hz] at Hzero
  refine ⟨c, Step_pure.vcvtop c1 _ _ op c (some c) ?_ (by simp) rfl⟩
  exact fun_vcvtop__.fun_vcvtop___case_0 L1 M L2 op c1 c M _ _ vs (some none) (some none)
    Hn H2 Hzero Hhalf (by simp) (by simp) ⟨rfl, rfl⟩ rfl Hne0 rfl Hgt (List.elem_eq_true_of_mem Hin) Hs1 Hs2 rfl

/-- Rocq `type_progress.v:2991` `vcvtop_step_half`. A well-formed `VCVTOP` with a half (and not
    `F32 → I16 TRUNC_SAT`) on a `V128` constant steps to a `V128` constant. -/
theorem vcvtop_step_half (L1 : lanetype) (M1 : Nat) (L2 : lanetype) (M2 : Nat) (op : vcvtop__)
    (c1 : uN) (h : half) :
    wf_uN 128 c1 → wf_shape (shape.X L1 (dim.mk_dim M1)) → wf_shape (shape.X L2 (dim.mk_dim M2)) →
    wf_vcvtop__ (shape.X L1 (dim.mk_dim M1)) (shape.X L2 (dim.mk_dim M2)) op →
    vcvtop_trunc_sat_i16 op = false →
    halfop_of op = some h →
    ∃ c, Step_pure [admininstr.VCONST vectype.V128 c1,
                    admininstr.VCVTOP (shape.X L2 (dim.mk_dim M2)) (shape.X L1 (dim.mk_dim M1)) op]
                   [admininstr.VCONST vectype.V128 c] := by
  intro Hc Hs1 Hs2 Hop Hts Hh
  have Hl := Forall_list_slice _ _ (fun_half h 0 M2) M2 (lanes__is_wf _ _ _ Hs1 Hc rfl)
  obtain ⟨vs, H2, Hn, Hne0, Hne, Hw⟩ := vcvtop_lanes_total _ _ _ _ Hs1 Hs2 Hop Hts Hl
  obtain ⟨c, Hgt, Hin, Hsw⟩ := setproduct_pick L2 M2 _ Hne Hw
  have Hhalf := halfop_total _ _ _ Hop Hts
  rw [Hh] at Hhalf
  refine ⟨c, Step_pure.vcvtop c1 _ _ op c (some c) ?_ (by simp) rfl⟩
  exact fun_vcvtop__.fun_vcvtop___case_1 L1 M1 L2 M2 op c1 c h _ _ vs (some (some h))
    Hn H2 Hhalf (by simp) rfl rfl Hne0 rfl Hgt (List.elem_eq_true_of_mem Hin) Hs1 Hs2

/-- Rocq `type_progress.v:3012` `vcvtop_step_zero`. A well-formed `VCVTOP` with `ZERO` (and not
    `F32 → I16 TRUNC_SAT`) between number-type lanes, on a `V128` constant, steps to a `V128`
    constant. -/
theorem vcvtop_step_zero (nt1 : numtype) (M1 : Nat) (nt2 : numtype) (M2 : Nat) (op : vcvtop__)
    (c1 : uN) :
    wf_uN 128 c1 → wf_shape (shape.X (lanetype_numtype nt1) (dim.mk_dim M1)) →
    wf_shape (shape.X (lanetype_numtype nt2) (dim.mk_dim M2)) →
    wf_vcvtop__ (shape.X (lanetype_numtype nt1) (dim.mk_dim M1))
      (shape.X (lanetype_numtype nt2) (dim.mk_dim M2)) op →
    vcvtop_trunc_sat_i16 op = false →
    zeroop_of op = some zero.ZERO →
    ∃ c, Step_pure [admininstr.VCONST vectype.V128 c1,
                    admininstr.VCVTOP (shape.X (lanetype_numtype nt2) (dim.mk_dim M2))
                      (shape.X (lanetype_numtype nt1) (dim.mk_dim M1)) op]
                   [admininstr.VCONST vectype.V128 c] := by
  intro Hc Hs1 Hs2 Hop Hts Hz
  have Hl := lanes__is_wf _ _ _ Hs1 Hc rfl
  obtain ⟨vs, H2, Hn, Hne0, Hne, Hw⟩ := vcvtop_lanes_total _ _ _ _ Hs1 Hs2 Hop Hts Hl
  obtain ⟨Hpz, Hwz⟩ := zero_lane_wf nt2
  have Hu : ∀ nt : numtype, unpack (lanetype_numtype nt) = nt := by
    intro nt; cases nt <;> rfl
  have Hpz' : packnum_ (lanetype_numtype nt2) (fun_zero (unpack (lanetype_numtype nt2))) ≠ none := by
    rw [Hu nt2]; exact Hpz
  have Hwz' : wf_lane_ (lanetype_numtype nt2)
      (Option.get! (packnum_ (lanetype_numtype nt2) (fun_zero (unpack (lanetype_numtype nt2))))) := by
    rw [Hu nt2]; exact Hwz
  have Hne' : Forall (fun l => l ≠ [])
      (List.map (fun v => Option.get! v) vs ++
        List.replicate M1 [Option.get! (packnum_ (lanetype_numtype nt2) (fun_zero (unpack (lanetype_numtype nt2))))]) := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact Hne l hl
    · rw [List.eq_of_mem_replicate hl]
      exact List.cons_ne_nil _ _
  have Hw' : Forall (Forall (wf_lane_ (lanetype_numtype nt2)))
      (List.map (fun v => Option.get! v) vs ++
        List.replicate M1 [Option.get! (packnum_ (lanetype_numtype nt2) (fun_zero (unpack (lanetype_numtype nt2))))]) := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact Hw l hl
    · rw [List.eq_of_mem_replicate hl]
      intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact Hwz'
  obtain ⟨c, Hgt, Hin, Hsw⟩ := setproduct_pick (lanetype_numtype nt2) M2 _ Hne' Hw'
  have Hzero := zeroop_total _ _ _ Hop Hts
  rw [Hz] at Hzero
  refine ⟨c, Step_pure.vcvtop c1 _ _ op c (some c) ?_ (by simp) rfl⟩
  exact fun_vcvtop__.fun_vcvtop___case_2 (lanetype_numtype nt1) M1 (lanetype_numtype nt2) M2 op c1 c _ _ vs
    (some (some zero.ZERO)) Hn H2 Hzero (by simp) rfl rfl Hne0 Hpz' rfl Hgt (List.elem_eq_true_of_mem Hin) Hs1 Hs2

-- Ltac `vcvtop_cases_full` (type_progress.v:3046) NOT PORTED: proof automation; the Lean proofs do
-- this inline.

/-- Rocq `type_progress.v:3064` `vcvtop_zero_numtype`. `vcvtop`-zero applies to number-type lanes
    only: the operators with a `ZERO` (`TRUNC_SAT` to `I32`, `DEMOTE`) have number-type lanes on
    both sides. -/
theorem vcvtop_zero_numtype (L1 : lanetype) (M1 : Nat) (L2 : lanetype) (M2 : Nat) (op : vcvtop__)
    (z : zero) :
    wf_vcvtop__ (shape.X L1 (dim.mk_dim M1)) (shape.X L2 (dim.mk_dim M2)) op →
    vcvtop_trunc_sat_i16 op = false →
    zeroop_of op = some z →
    ∃ nt1 nt2, L1 = lanetype_numtype nt1 ∧ L2 = lanetype_numtype nt2 := by
  intro Hop Hts Hz
  cases Hop with
  | vcvtop___case_0 J1 M1' J2 M2' x Hx E1 E2 =>
    exact absurd Hz (by simp [zeroop_of])
  | vcvtop___case_1 J1 M1' F2 M2' x Hx E1 E2 =>
    exact absurd Hz (by simp [zeroop_of])
  | vcvtop___case_2 F1 M1' J2 M2' x Hx E1 E2 =>
    simp only [shape.X.injEq, dim.mk_dim.injEq] at E1 E2
    obtain ⟨rfl, rfl⟩ := E1
    obtain ⟨rfl, rfl⟩ := E2
    cases Hx with
    | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 sx zo hcond =>
      simp only [zeroop_of] at Hz
      subst Hz
      cases z
      cases F1 <;> cases J2 <;> first
        | (simp [vcvtop_trunc_sat_i16] at Hts; done)
        | (exfalso; revert hcond; decide)
        | exact ⟨numtype.F64, numtype.I32, rfl, rfl⟩
  | vcvtop___case_3 F1 M1' F2 M2' x Hx E1 E2 =>
    simp only [shape.X.injEq, dim.mk_dim.injEq] at E1 E2
    obtain ⟨rfl, rfl⟩ := E1
    obtain ⟨rfl, rfl⟩ := E2
    cases Hx with
    | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 z' hcond =>
      cases F1 <;> cases F2 <;> first
        | (exfalso; revert hcond; decide)
        | exact ⟨numtype.F64, numtype.F32, rfl, rfl⟩
    | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 hcond =>
      exact absurd Hz (by simp [zeroop_of])

/-- Rocq `type_progress.v:3076` `vcvtop_full_lsize`. Without half / zero, source and destination
    lanes have the same size. -/
theorem vcvtop_full_lsize (L1 : lanetype) (M1 : Nat) (L2 : lanetype) (M2 : Nat) (op : vcvtop__) :
    wf_vcvtop__ (shape.X L1 (dim.mk_dim M1)) (shape.X L2 (dim.mk_dim M2)) op →
    vcvtop_trunc_sat_i16 op = false →
    halfop_of op = none → zeroop_of op = none → lsize L1 = lsize L2 := by
  intro Hop Hts Hh Hz
  cases Hop with
  | vcvtop___case_0 J1 M1' J2 M2' x Hx E1 E2 =>
    exact absurd Hh (by simp [halfop_of])
  | vcvtop___case_1 J1 M1' F2 M2' x Hx E1 E2 =>
    simp only [shape.X.injEq, dim.mk_dim.injEq] at E1 E2
    obtain ⟨rfl, rfl⟩ := E1
    obtain ⟨rfl, rfl⟩ := E2
    cases Hx with
    | vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 ho sx hcond =>
      simp only [halfop_of] at Hh
      subst Hh
      cases J1 <;> cases F2 <;> first
        | rfl
        | exact absurd hcond (by decide)
  | vcvtop___case_2 F1 M1' J2 M2' x Hx E1 E2 =>
    simp only [shape.X.injEq, dim.mk_dim.injEq] at E1 E2
    obtain ⟨rfl, rfl⟩ := E1
    obtain ⟨rfl, rfl⟩ := E2
    cases Hx with
    | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 sx zo hcond =>
      simp only [zeroop_of] at Hz
      subst Hz
      cases F1 <;> cases J2 <;> first
        | rfl
        | exact absurd hcond (by decide)
  | vcvtop___case_3 F1 M1' F2 M2' x Hx E1 E2 =>
    cases Hx with
    | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 z' hcond =>
      exact absurd Hz (by simp [zeroop_of])
    | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 hcond =>
      exact absurd Hh (by simp [halfop_of])

/-- Lean-only (bundle20): Rocq's motive `P` (for `Instr_ok`) in the `Instrs_ok_ind'` application
    that proves `t_progress_be` (`type_progress.v:3102-3115`), verbatim; like Rocq's it takes the
    (unused) typing derivation as its last argument. -/
def t_progress_be_P (C : context) (be : instr) (tf : functype) (_ : Instr_ok C be tf) : Prop :=
  ∀ (s : store) (f : frame) (C' : context) (vcs : List val) (ts1 ts2 : List valtype)
    (lab : List resulttype) (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ List.map admininstr_instr [be])) →
    Forall (fun e => wf_val e) vcs →
    tf = mkFunctype ts1 ts2 →
    C = upd_local_label_return C' (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE C' →
    List.map typeof vcs = ts1 →
    Store_ok s →
    not_lf_br (List.map admininstr_instr [be]) →
    not_lf_return (List.map admininstr_instr [be]) →
    const_list (List.map admininstr_instr [be]) = true ∨
      ∃ (s' : store) (f' : frame) (es' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ List.map admininstr_instr [be]))
          (config.mk_config (state.mk_state s' f') es')

/-- Lean-only (bundle20): Rocq's motive `P0` (for `Instrs_ok`) of `t_progress_be`
    (`type_progress.v:3116-3128`). -/
def t_progress_be_P0 (C : context) (bes : List instr) (tf : functype) (_ : Instrs_ok C bes tf) : Prop :=
  ∀ (s : store) (f : frame) (C' : context) (vcs : List val) (ts1 ts2 : List valtype)
    (lab : List resulttype) (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ List.map admininstr_instr bes)) →
    Forall (fun e => wf_val e) vcs →
    tf = mkFunctype ts1 ts2 →
    C = upd_local_label_return C' (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE C' →
    List.map typeof vcs = ts1 →
    Store_ok s →
    not_lf_br (List.map admininstr_instr bes) →
    not_lf_return (List.map admininstr_instr bes) →
    const_list (List.map admininstr_instr bes) = true ∨
      ∃ (s' : store) (f' : frame) (es' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ List.map admininstr_instr bes))
          (config.mk_config (state.mk_state s' f') es')

/-- Lean-only (bundle20): the `Instr_ok.nop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3130`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_nop :
    ∀ (C : context) (a : wf_context C) (a_1 : wf_instr _root_.instr.NOP),
  t_progress_be_P C _root_.instr.NOP (functype.mk_functype (list.mk_list []) (list.mk_list [])) (Instr_ok.nop C a a_1) := by
  intro C HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  refine ⟨s, f, [], ?_⟩
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  subst Htf1
  have Hvcs : vcs = [] := map_eq_nil typeof vcs Hts
  subst Hvcs
  exact Step.pure _ _ _ Step_pure.nop

/-- Lean-only (bundle20): the `Instr_ok.unreachable` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3140`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_unreachable :
    ∀ (C : context) (t_1_lst t_2_lst : List valtype) (a : wf_context C)
  (a_1 : wf_instr _root_.instr.UNREACHABLE),
  t_progress_be_P C _root_.instr.UNREACHABLE (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok.unreachable C t_1_lst t_2_lst a a_1) := by
  intro C ts1 ts2 HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  cases vcs with
  | nil =>
    exact ⟨s, f, [admininstr.TRAP], Step.pure _ _ _ Step_pure.unreachable⟩
  | cons vc' vcs' =>
    refine ⟨s, f, List.map admininstr_val (vc' :: vcs') ++ ([admininstr.TRAP] ++ []), ?_⟩
    have H : Step (config.mk_config (state.mk_state s f) [admininstr.UNREACHABLE])
        (config.mk_config (state.mk_state s f) [admininstr.TRAP]) :=
      Step.pure _ _ _ Step_pure.unreachable
    obtain ⟨_, HWf1⟩ := (wf_config_app _ _ _).mp HWfConfig
    have HWf2 := Step_is_wf _ _ _ HWf1 Hstore H
    exact Step.ctxt_instrs _ (vc' :: vcs') [admininstr.UNREACHABLE] [] _ [admininstr.TRAP] H
      (Or.inl (List.cons_ne_nil _ _)) HWf1 HWf2

/-- Lean-only (bundle20): the `Instr_ok.drop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3160`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_drop :
    ∀ (C : context) (t : valtype) (a : wf_context C) (a_1 : wf_instr _root_.instr.DROP),
  t_progress_be_P C _root_.instr.DROP (functype.mk_functype (list.mk_list [t]) (list.mk_list [])) (Instr_ok.drop C t a a_1) := by
  intro C t HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  subst Htf1
  match vcs, Hts with
  | [v], _ =>
    exact ⟨s, f, [], Step.pure _ _ _ (Step_pure.drop v)⟩

/-- Lean-only (bundle20): the `Instr_ok.select_expl` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3173`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_select_expl :
    ∀ (C : context) (t : valtype) (a : wf_context C) (a_1 : wf_instr (_root_.instr.SELECT (some [t]))),
  t_progress_be_P C (_root_.instr.SELECT (some [t]))
    (functype.mk_functype (list.mk_list [t, t, valtype.I32]) (list.mk_list [t])) (Instr_ok.select_expl C t a a_1) := by
  intro C t HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨_, _, Ht3, _⟩ := Hts
    have HP3 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨n3, Hn3⟩ := invert_typeof_I32 v3 Ht3 HP3
    cases v3 with
    | CONST nt c =>
      simp only [admininstr_val, admininstr.CONST.injEq] at Hn3
      obtain ⟨rfl, rfl⟩ := Hn3
      cases n3 with
      | zero =>
        exact ⟨s, f, [admininstr_val v2], Step.pure _ _ _
          (Step_pure.select_false v1 v2 _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]))⟩
      | succ n3' =>
        exact ⟨s, f, [admininstr_val v1], Step.pure _ _ _
          (Step_pure.select_true v1 v2 _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]))⟩
    | _ => simp [admininstr_val] at Hn3
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.select_impl` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3190`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_select_impl :
    ∀ (C : context) (t t' : valtype) (v_numtype : numtype) (v_vectype : vectype) (a : Valtype_sub t t')
  (a_1 : t' = valtype_numtype v_numtype ∨ t' = valtype_vectype v_vectype) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.SELECT none)),
  t_progress_be_P C (_root_.instr.SELECT none) (functype.mk_functype (list.mk_list [t, t, valtype.I32]) (list.mk_list [t]))
    (Instr_ok.select_impl C t t' v_numtype v_vectype a a_1 a_2 a_3) := by
  intro C t t' nt vt HVsub Hteq HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨_, _, Ht3, _⟩ := Hts
    have HP3 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨n3, Hn3⟩ := invert_typeof_I32 v3 Ht3 HP3
    cases v3 with
    | CONST nt c =>
      simp only [admininstr_val, admininstr.CONST.injEq] at Hn3
      obtain ⟨rfl, rfl⟩ := Hn3
      cases n3 with
      | zero =>
        exact ⟨s, f, [admininstr_val v2], Step.pure _ _ _
          (Step_pure.select_false v1 v2 _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]))⟩
      | succ n3' =>
        exact ⟨s, f, [admininstr_val v1], Step.pure _ _ _
          (Step_pure.select_true v1 v2 _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]))⟩
    | _ => simp [admininstr_val] at Hn3
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.block` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3207`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_block :
    ∀ (C : context) (bt : blocktype) (instr_lst : List _root_.instr) (t_1_lst t_2_lst : List valtype)
  (a : Blocktype_ok C bt (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 :
    Instrs_ok
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_2_lst], RETURN := none } : context) ++
        C)
      instr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.BLOCK bt instr_lst))
  (a_4 :
    wf_context
      ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_2_lst], RETURN := none } : context)),
  t_progress_be_P0
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_2_lst], RETURN := none } : context) ++
        C)
      instr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a_1 →
    t_progress_be_P C (_root_.instr.BLOCK bt instr_lst) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
      (Instr_ok.block C bt instr_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4) := by
  intro C bt bes vt1 vt2 HBok HType HWfC HWfinstr HWfC' IHH
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  refine ⟨s, f, [admininstr.LABEL_ vt2.length [] (List.map admininstr_val vcs ++ List.map admininstr_instr bes)], ?_⟩
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  have Hfun : fun_blocktype (state.mk_state s f) bt = functype.mk_functype (list.mk_list vt1) (list.mk_list vt2) := by
    cases HBok with
    | valtype valtype_opt _ _ => cases valtype_opt <;> rfl
    | typeidx x _ _ _ Hty _ _ =>
      show f.MODULE.TYPES[proj_uN_0 x]! = _
      rw [← lookup_types s f C' (List.map typeof f.LOCALS) lab ret _ Hmod, ← Hcontext]
      exact Hty
  have Hlen : vcs.length = vt1.length := by rw [← Hts, List.length_map]
  exact Step.read _ _ _ (Step_read.block (state.mk_state s f) vcs.length vcs bt bes vt2.length
    vt1 vt2 Hfun rfl Hlen rfl)

/-- Lean-only (bundle20): the `Instr_ok.loop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3229`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_loop :
    ∀ (C : context) (bt : blocktype) (instr_lst : List _root_.instr) (t_1_lst t_2_lst : List valtype)
  (a : Blocktype_ok C bt (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 :
    Instrs_ok
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_1_lst], RETURN := none } : context) ++
        C)
      instr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.LOOP bt instr_lst))
  (a_4 :
    wf_context
      ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_1_lst], RETURN := none } : context)),
  t_progress_be_P0
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_1_lst], RETURN := none } : context) ++
        C)
      instr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a_1 →
    t_progress_be_P C (_root_.instr.LOOP bt instr_lst) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
      (Instr_ok.loop C bt instr_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4) := by
  intro C bt bes vt1 vt2 HBok HType HWfC HWfinstr HWfC' IHH
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  refine ⟨s, f, [admininstr.LABEL_ vt1.length [instr.LOOP bt bes] (List.map admininstr_val vcs ++ List.map admininstr_instr bes)], ?_⟩
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  have Hfun : fun_blocktype (state.mk_state s f) bt = functype.mk_functype (list.mk_list vt1) (list.mk_list vt2) := by
    cases HBok with
    | valtype valtype_opt _ _ => cases valtype_opt <;> rfl
    | typeidx x _ _ _ Hty _ _ =>
      show f.MODULE.TYPES[proj_uN_0 x]! = _
      rw [← lookup_types s f C' (List.map typeof f.LOCALS) lab ret _ Hmod, ← Hcontext]
      exact Hty
  have Hlen : vcs.length = vt1.length := by rw [← Hts, List.length_map]
  exact Step.read _ _ _ (Step_read.loop (state.mk_state s f) vt1.length vcs bt bes vt1 vt2.length
    vt2 Hfun Hlen.symm rfl rfl)

/-- Lean-only (bundle20): the `Instr_ok.if` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3251`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_if :
    ∀ (C : context) (bt : blocktype) (instr_1_lst instr_2_lst : List _root_.instr) (t_1_lst t_2_lst : List valtype)
  (a : Blocktype_ok C bt (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 :
    Instrs_ok
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_2_lst], RETURN := none } : context) ++
        C)
      instr_1_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_2 :
    Instrs_ok
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_2_lst], RETURN := none } : context) ++
        C)
      instr_2_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_3 : wf_context C) (a_4 : wf_instr (_root_.instr.IFELSE bt instr_1_lst instr_2_lst))
  (a_5 :
    wf_context
      ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_2_lst], RETURN := none } : context)),
  t_progress_be_P0
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_2_lst], RETURN := none } : context) ++
        C)
      instr_1_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a_1 →
    t_progress_be_P0
        (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t_2_lst], RETURN := none } : context) ++
          C)
        instr_2_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a_2 →
      t_progress_be_P C (_root_.instr.IFELSE bt instr_1_lst instr_2_lst)
        (functype.mk_functype (list.mk_list (t_1_lst ++ [valtype.I32])) (list.mk_list t_2_lst))
        (Instr_ok.if C bt instr_1_lst instr_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5) := by
  intro C bt bes1 bes2 vt1 vt2 HBok HType HType2 HWfC HWfinstr HWfC' IHH IHH2
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  obtain ⟨v, Hvcs, Hvs1, Hvs2⟩ := typeof_append vt1 valtype.I32 vcs Hts
  generalize List.take vt1.length vcs = vs1 at Hvcs Hvs1
  subst Hvcs
  have HWfv : wf_val v := HWfVals v (by simp)
  obtain ⟨n, Heqv⟩ := invert_typeof_I32 v Hvs2 HWfv
  simp only [List.map_append, List.append_assoc, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, admininstr_instr] at HWfConfig ⊢
  rw [Heqv] at HWfConfig ⊢
  have Hwf1 := ((wf_config_app _ _ _).mp HWfConfig).2
  cases n with
  | zero =>
    have HStep : Step (config.mk_config (state.mk_state s f)
        [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)), admininstr.IFELSE bt bes1 bes2])
        (config.mk_config (state.mk_state s f) [admininstr.BLOCK bt bes2]) :=
      Step.pure _ _ _ (Step_pure.if_false _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]))
    have Hwf2 := Step_is_wf _ _ _ Hwf1 Hstore HStep
    cases vs1 with
    | nil => exact ⟨s, f, _, HStep⟩
    | cons x xs =>
      exact ⟨s, f, _, Step.ctxt_instrs _ (x :: xs) _ [] _ _ HStep (Or.inl (List.cons_ne_nil _ _)) Hwf1 Hwf2⟩
  | succ n' =>
    have HStep : Step (config.mk_config (state.mk_state s f)
        [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (n' + 1))), admininstr.IFELSE bt bes1 bes2])
        (config.mk_config (state.mk_state s f) [admininstr.BLOCK bt bes1]) :=
      Step.pure _ _ _ (Step_pure.if_true _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]))
    have Hwf2 := Step_is_wf _ _ _ Hwf1 Hstore HStep
    cases vs1 with
    | nil => exact ⟨s, f, _, HStep⟩
    | cons x xs =>
      exact ⟨s, f, _, Step.ctxt_instrs _ (x :: xs) _ [] _ _ HStep (Or.inl (List.cons_ne_nil _ _)) Hwf1 Hwf2⟩

/-- Lean-only (bundle20): the `Instr_ok.br` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3338`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_br :
    ∀ (C : context) (l : labelidx) (t_1_lst t_lst t_2_lst : List valtype) (a : proj_uN_0 l < C.LABELS.length)
  (a_1 : proj_list_0 valtype C.LABELS[proj_uN_0 l]! = t_lst) (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.BR l)),
  t_progress_be_P C (_root_.instr.BR l) (functype.mk_functype (list.mk_list (t_1_lst ++ t_lst)) (list.mk_list t_2_lst))
    (Instr_ok.br C l t_1_lst t_lst t_2_lst a a_1 a_2 a_3) := by
  intro C l ts1 ts ts2 Hlablen Hlablookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  exact (not_lf_br_singleton _ l Hnotbr rfl).elim

/-- Lean-only (bundle20): the `Instr_ok.br_if` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3344`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_br_if :
    ∀ (C : context) (l : labelidx) (t_lst : List valtype) (a : proj_uN_0 l < C.LABELS.length)
  (a_1 : proj_list_0 valtype C.LABELS[proj_uN_0 l]! = t_lst) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.BR_IF l)),
  t_progress_be_P C (_root_.instr.BR_IF l) (functype.mk_functype (list.mk_list (t_lst ++ [valtype.I32])) (list.mk_list t_lst))
    (Instr_ok.br_if C l t_lst a a_1 a_2 a_3) := by
  intro C l t_lst a a_1 a_2 a_3
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, -⟩ := Htf
  rw [← Htf1] at Hts
  obtain ⟨v1, Hvcs, Hts', Ht1⟩ := typeof_append _ _ _ Hts
  have Hwfv1 : wf_val v1 :=
    HWfVals v1 (by rw [Hvcs]; exact List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨n, Heqv⟩ := invert_typeof_I32 v1 Ht1 Hwfv1
  generalize List.take t_lst.length vcs = vs at Hvcs Hts'
  subst Hvcs
  have Hcfg : List.map admininstr_val (vs ++ [v1]) ++ List.map admininstr_instr [_root_.instr.BR_IF l]
      = List.map admininstr_val vs ++
          ([admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n)), admininstr.BR_IF l] ++ []) := by
    simp [Heqv, admininstr_instr]
  rw [Hcfg] at HWfConfig ⊢
  -- Rocq's `ctxt_instrs` step under the value prefix `vs` (plain `pure` when `vs = []`, Rocq's `destruct ts`)
  have Hctxt : ∀ (es es' : List admininstr), Step_pure es es' →
      Forall (fun e => wf_admininstr e) es' →
      wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vs ++ (es ++ []))) →
      ∃ (s' : store) (f' : frame) (es'' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vs ++ (es ++ [])))
          (config.mk_config (state.mk_state s' f') es'') := by
    intro es es' Hpure Hes' Hwf
    obtain ⟨Hst, Hais⟩ : wf_state (state.mk_state s f) ∧
        Forall (fun e => wf_admininstr e) (List.map admininstr_val vs ++ (es ++ [])) := by
      cases Hwf with | config_case_0 _ _ h1 h2 => exact ⟨h1, h2⟩
    have Hes : Forall (fun e => wf_admininstr e) es :=
      fun e he => Hais e (List.mem_append_right _ (List.mem_append_left _ he))
    cases vs with
    | nil =>
      refine ⟨s, f, es', ?_⟩
      simp only [List.map_nil, List.nil_append, List.append_nil]
      exact Step.pure _ _ _ Hpure
    | cons v vs' =>
      exact ⟨s, f, List.map admininstr_val (v :: vs') ++ (es' ++ []),
        Step.ctxt_instrs _ (v :: vs') es [] _ es' (Step.pure _ _ _ Hpure) (Or.inl (List.cons_ne_nil _ _))
          (wf_config.config_case_0 _ _ Hst Hes) (wf_config.config_case_0 _ _ Hst Hes')⟩
  have Hl : wf_uN 32 l := by
    cases a_3 with | instr_case_8 _ h => exact h
  cases n with
  | zero =>
    exact Hctxt _ [] (Step_pure.br_if_false _ _ (by simp [proj_num__0])
      (by simp [proj_num__0, proj_uN_0])) (iswf_Forall_nil _) HWfConfig
  | succ n' =>
    exact Hctxt _ [admininstr.BR l] (Step_pure.br_if_true _ _ (by simp [proj_num__0])
      (by simp [proj_num__0, proj_uN_0]))
      (iswf_Forall_cons (wf_admininstr.admininstr_case_7 _ Hl) (iswf_Forall_nil _)) HWfConfig

/-- Lean-only (bundle20): the `Instr_ok.br_table` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3393`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_br_table :
    ∀ (C : context) (l_lst : List labelidx) (l' : labelidx) (t_1_lst t_lst t_2_lst : List valtype)
  (a : Forall (fun (l_elem : labelidx) => proj_uN_0 l_elem < C.LABELS.length) l_lst)
  (a_1 : Forall (fun (l_elem : labelidx) => Resulttype_sub (list.mk_list t_lst) C.LABELS[proj_uN_0 l_elem]!) l_lst)
  (a_2 : proj_uN_0 l' < C.LABELS.length) (a_3 : Resulttype_sub (list.mk_list t_lst) C.LABELS[proj_uN_0 l']!)
  (a_4 : wf_context C) (a_5 : wf_instr (_root_.instr.BR_TABLE l_lst l')),
  t_progress_be_P C (_root_.instr.BR_TABLE l_lst l')
    (functype.mk_functype (list.mk_list (t_1_lst ++ (t_lst ++ [valtype.I32]))) (list.mk_list t_2_lst))
    (Instr_ok.br_table C l_lst l' t_1_lst t_lst t_2_lst a a_1 a_2 a_3 a_4 a_5) := by
  intro C l_lst l' t_1_lst t_lst t_2_lst a a_1 a_2 a_3 a_4 a_5
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, -⟩ := Htf
  rw [← Htf1, ← List.append_assoc] at Hts
  obtain ⟨v1, Hvcs, Hts', Ht1⟩ := typeof_append _ _ _ Hts
  have Hwfv1 : wf_val v1 :=
    HWfVals v1 (by rw [Hvcs]; exact List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨n, Heqv⟩ := invert_typeof_I32 v1 Ht1 Hwfv1
  generalize List.take (t_1_lst ++ t_lst).length vcs = vs at Hvcs Hts'
  subst Hvcs
  have Hcfg : List.map admininstr_val (vs ++ [v1]) ++ List.map admininstr_instr [_root_.instr.BR_TABLE l_lst l']
      = List.map admininstr_val vs ++
          ([admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n)), admininstr.BR_TABLE l_lst l'] ++ []) := by
    simp [Heqv, admininstr_instr]
  rw [Hcfg] at HWfConfig ⊢
  -- Rocq's `ctxt_instrs` step under the value prefix `vs` (plain `pure` when `vs = []`, Rocq's `destruct (ts1 ++ ts)`)
  have Hctxt : ∀ (es es' : List admininstr), Step_pure es es' →
      Forall (fun e => wf_admininstr e) es' →
      wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vs ++ (es ++ []))) →
      ∃ (s' : store) (f' : frame) (es'' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vs ++ (es ++ [])))
          (config.mk_config (state.mk_state s' f') es'') := by
    intro es es' Hpure Hes' Hwf
    obtain ⟨Hst, Hais⟩ : wf_state (state.mk_state s f) ∧
        Forall (fun e => wf_admininstr e) (List.map admininstr_val vs ++ (es ++ [])) := by
      cases Hwf with | config_case_0 _ _ h1 h2 => exact ⟨h1, h2⟩
    have Hes : Forall (fun e => wf_admininstr e) es :=
      fun e he => Hais e (List.mem_append_right _ (List.mem_append_left _ he))
    cases vs with
    | nil =>
      refine ⟨s, f, es', ?_⟩
      simp only [List.map_nil, List.nil_append, List.append_nil]
      exact Step.pure _ _ _ Hpure
    | cons v vs' =>
      exact ⟨s, f, List.map admininstr_val (v :: vs') ++ (es' ++ []),
        Step.ctxt_instrs _ (v :: vs') es [] _ es' (Step.pure _ _ _ Hpure) (Or.inl (List.cons_ne_nil _ _))
          (wf_config.config_case_0 _ _ Hst Hes) (wf_config.config_case_0 _ _ Hst Hes')⟩
  obtain ⟨Hls, Hl'⟩ : Forall (fun l => wf_uN 32 l) l_lst ∧ wf_uN 32 l' := by
    cases a_5 with | instr_case_9 _ _ h1 h2 => exact ⟨h1, h2⟩
  by_cases Hv1 : n < l_lst.length
  · exact Hctxt _ _ (Step_pure.br_table_lt _ _ _ (by simpa [proj_num__0, proj_uN_0] using Hv1)
      (by simp [proj_num__0]))
      (iswf_Forall_cons (wf_admininstr.admininstr_case_7 _ (iswf_Forall_getElem! _ Hls (iswf_uN_zero _)))
        (iswf_Forall_nil _)) HWfConfig
  · exact Hctxt _ [admininstr.BR l'] (Step_pure.br_table_ge _ _ _ (by simp [proj_num__0])
      (by simp [proj_num__0, proj_uN_0]; omega))
      (iswf_Forall_cons (wf_admininstr.admininstr_case_7 _ Hl') (iswf_Forall_nil _)) HWfConfig

/-- Lean-only (bundle20): the `Instr_ok.call` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3449`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_call :
    ∀ (C : context) (x : idx) (t_1_lst t_2_lst : List valtype) (a : proj_uN_0 x < C.FUNCS.length)
  (a_1 : C.FUNCS[proj_uN_0 x]! = functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
  (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.CALL x)),
  t_progress_be_P C (_root_.instr.CALL x) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok.call C x t_1_lst t_2_lst a a_1 a_2 a_3) := by
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

/-- Lean-only (bundle20): the `Instr_ok.call_indirect` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3477`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_call_indirect :
    ∀ (C : context) (x y : idx) (t_1_lst t_2_lst : List valtype) (lim : limits)
  (a : proj_uN_0 x < C.TABLES.length) (a_1 : C.TABLES[proj_uN_0 x]! = tabletype.mk_tabletype lim reftype.FUNCREF)
  (a_2 : proj_uN_0 y < C.TYPES.length)
  (a_3 : C.TYPES[proj_uN_0 y]! = functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
  (a_4 : wf_context C) (a_5 : wf_instr (_root_.instr.CALL_INDIRECT x y))
  (a_6 : wf_tabletype (tabletype.mk_tabletype lim reftype.FUNCREF)),
  t_progress_be_P C (_root_.instr.CALL_INDIRECT x y)
    (functype.mk_functype (list.mk_list (t_1_lst ++ [valtype.I32])) (list.mk_list t_2_lst))
    (Instr_ok.call_indirect C x y t_1_lst t_2_lst lim a a_1 a_2 a_3 a_4 a_5 a_6) := by
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

/-- Lean-only (bundle20): the `Instr_ok.return` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3516`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_return :
    ∀ (C : context) (t_1_lst t_lst t_2_lst : List valtype) (a : C.RETURN = some (list.mk_list t_lst))
  (a_1 : wf_context C) (a_2 : wf_instr _root_.instr.RETURN),
  t_progress_be_P C _root_.instr.RETURN (functype.mk_functype (list.mk_list (t_1_lst ++ t_lst)) (list.mk_list t_2_lst))
    (Instr_ok.return C t_1_lst t_lst t_2_lst a a_1 a_2) := by
  intro C ts1 ts ts2 Hretts HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  -- Rocq: `by move/not_lf_return_singleton: Hnotret.`
  exact absurd rfl (not_lf_return_singleton _ Hnotret)

/-- Lean-only (bundle20): the `Instr_ok.const` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3521`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_const :
    ∀ (C : context) (nt : numtype) (c_nt : num_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.CONST nt c_nt)),
  t_progress_be_P C (_root_.instr.CONST nt c_nt) (functype.mk_functype (list.mk_list []) (list.mk_list [valtype_numtype nt]))
    (Instr_ok.const C nt c_nt a a_1) := by
  intro C t vc HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  -- Rocq: `by left.`
  left
  rfl

/-- Lean-only (bundle20): the `Instr_ok.unop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3526`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_unop :
    ∀ (C : context) (nt : numtype) (unop_nt : unop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.UNOP nt unop_nt)),
  t_progress_be_P C (_root_.instr.UNOP nt unop_nt)
    (functype.mk_functype (list.mk_list [valtype_numtype nt]) (list.mk_list [valtype_numtype nt]))
    (Instr_ok.unop C nt unop_nt a a_1) := by
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

/-- Lean-only (bundle20): the `Instr_ok.binop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3551`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_binop :
    ∀ (C : context) (nt : numtype) (binop_nt : binop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.BINOP nt binop_nt)),
  t_progress_be_P C (_root_.instr.BINOP nt binop_nt)
    (functype.mk_functype (list.mk_list [valtype_numtype nt, valtype_numtype nt]) (list.mk_list [valtype_numtype nt]))
    (Instr_ok.binop C nt binop_nt a a_1) := by
  intro C nt binop_nt HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨n1, Heqv1, Hwf1⟩ := invert_typeof_numtype_wf v1 nt Ht1 HP1
    obtain ⟨n2, Heqv2, Hwf2⟩ := invert_typeof_numtype_wf v2 nt Ht2 HP2
    have Hwfb : wf_binop_ nt binop_nt := by cases Hwfinstr; assumption
    obtain ⟨lst_opt, HBinop⟩ := binop_total nt binop_nt n1 n2 Hwf1 Hwf2 Hwfb
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
    rcases lst_opt with _ | ⟨_ | ⟨a', as'⟩⟩
    · exact absurd rfl (binop_not_none nt binop_nt n1 n2 none Hwf1 Hwf2 Hwfb HBinop)
    · exact ⟨s, f, [admininstr.TRAP], Step.pure _ _ _
        (Step_pure.binop_trap nt n1 n2 binop_nt _ HBinop (by simp) (by simp))⟩
    · exact ⟨s, f, [admininstr.CONST nt a'], Step.pure _ _ _
        (Step_pure.binop_val nt n1 n2 binop_nt a' _ HBinop (by simp) (by simp) (by simp))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.testop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3582`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_testop :
    ∀ (C : context) (nt : numtype) (testop_nt : testop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.TESTOP nt testop_nt)),
  t_progress_be_P C (_root_.instr.TESTOP nt testop_nt)
    (functype.mk_functype (list.mk_list [valtype_numtype nt]) (list.mk_list [valtype.I32]))
    (Instr_ok.testop C nt testop_nt a a_1) := by
  intro C nt testop_nt HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1, Hwf1⟩ := invert_typeof_numtype_wf v1 nt Ht1 HP1
    have Hwft : wf_testop_ nt testop_nt := by cases Hwfinstr; assumption
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    cases ENone : fun_testop_ nt testop_nt n1 with
    | some c' =>
      have Hne : fun_testop_ nt testop_nt n1 ≠ none := by rw [ENone]; simp
      have Hc : c' = Option.get! (fun_testop_ nt testop_nt n1) := by rw [ENone]; simp
      exact ⟨s, f, [admininstr.CONST numtype.I32 c'], Step.pure _ _ _
        (Step_pure.testop nt n1 testop_nt c' Hne Hc
          (testop__is_wf nt testop_nt n1 c' Hwft Hwf1 Hne Hc))⟩
    | none => exact absurd ENone (testop_not_none nt testop_nt n1 Hwf1 Hwft)
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.relop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3600`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_relop :
    ∀ (C : context) (nt : numtype) (relop_nt : relop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.RELOP nt relop_nt)),
  t_progress_be_P C (_root_.instr.RELOP nt relop_nt)
    (functype.mk_functype (list.mk_list [valtype_numtype nt, valtype_numtype nt]) (list.mk_list [valtype.I32]))
    (Instr_ok.relop C nt relop_nt a a_1) := by
  intro C nt relop_nt HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨n1, Heqv1, Hwf1⟩ := invert_typeof_numtype_wf v1 nt Ht1 HP1
    obtain ⟨n2, Heqv2, Hwf2⟩ := invert_typeof_numtype_wf v2 nt Ht2 HP2
    have Hwfr : wf_relop_ nt relop_nt := by cases Hwfinstr; assumption
    obtain ⟨c, Hrelop⟩ := relop_total nt relop_nt n1 n2 Hwf1 Hwf2 Hwfr
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
    rcases c with _ | c'
    · exact absurd rfl (relop_not_none nt relop_nt n1 n2 none Hwf1 Hwf2 Hwfr Hrelop)
    · have Hne : (some c' : Option num_) ≠ none := by simp
      have Hc : c' = Option.get! (some c') := by simp
      exact ⟨s, f, [admininstr.CONST numtype.I32 c'], Step.pure _ _ _
        (Step_pure.relop nt n1 n2 relop_nt c' (some c') Hrelop Hne Hc
          (relop__is_wf nt relop_nt n1 n2 c' (some c') Hrelop Hwfr Hwf1 Hwf2 Hne Hc))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.cvtop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3625`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_cvtop :
    ∀ (C : context) (nt_1 nt_2 : numtype) (cvtop : cvtop__) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.CVTOP nt_1 nt_2 cvtop)),
  t_progress_be_P C (_root_.instr.CVTOP nt_1 nt_2 cvtop)
    (functype.mk_functype (list.mk_list [valtype_numtype nt_2]) (list.mk_list [valtype_numtype nt_1]))
    (Instr_ok.cvtop C nt_1 nt_2 cvtop a a_1) := by
  intro C nt_1 nt_2 cvtop HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1, Hwf1⟩ := invert_typeof_numtype_wf v1 nt_2 Ht1 HP1
    have Hwfc : wf_cvtop__ nt_2 nt_1 cvtop := by cases Hwfinstr; assumption
    obtain ⟨n2, Hcvtop⟩ := cvtop_total nt_2 nt_1 cvtop n1 Hwf1 Hwfc
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    rcases n2 with _ | ⟨_ | ⟨c, cs⟩⟩
    · exact absurd rfl (cvtop_not_none nt_2 nt_1 cvtop n1 none Hwf1 Hwfc Hcvtop)
    · exact ⟨s, f, [admininstr.TRAP], Step.pure _ _ _
        (Step_pure.cvtop_trap nt_2 n1 nt_1 cvtop _ Hcvtop (by simp) (by simp))⟩
    · exact ⟨s, f, [admininstr.CONST nt_1 c], Step.pure _ _ _
        (Step_pure.cvtop_val nt_2 n1 nt_1 cvtop c _ Hcvtop (by simp) (by simp) (by simp))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.ref_null` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3653`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_ref_null :
    ∀ (C : context) (rt : reftype) (a : wf_context C) (a_1 : wf_instr (_root_.instr.REF_NULL rt)),
  t_progress_be_P C (_root_.instr.REF_NULL rt) (functype.mk_functype (list.mk_list []) (list.mk_list [valtype_reftype rt]))
    (Instr_ok.ref_null C rt a a_1) := by
  intro C rt HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  left
  rfl

/-- Lean-only (bundle20): the `Instr_ok.ref_func` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3658`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_ref_func :
    ∀ (C : context) (x : idx) (ft : functype) (a : proj_uN_0 x < C.FUNCS.length)
  (a_1 : C.FUNCS[proj_uN_0 x]! = ft) (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.REF_FUNC x)),
  t_progress_be_P C (_root_.instr.REF_FUNC x) (functype.mk_functype (list.mk_list []) (list.mk_list [valtype.FUNCREF]))
    (Instr_ok.ref_func C x ft a a_1 a_2 a_3) := by
  intro C x ft Hxrange Heft HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs⟩
  · rw [Hcontext] at Hxrange
    rw [funcs_size s f C' (List.map typeof f.LOCALS) lab ret Hmod] at Hxrange
    exact ⟨s, f, [admininstr.REF_FUNC_ADDR ((fun_funcaddr (state.mk_state s f))[proj_uN_0 x]!)],
      Step.read _ _ _ (Step_read.ref_func (state.mk_state s f) x (by simpa [fun_funcaddr] using Hxrange))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.ref_is_null` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3672`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_ref_is_null :
    ∀ (C : context) (rt : reftype) (a : wf_context C) (a_1 : wf_instr _root_.instr.REF_IS_NULL),
  t_progress_be_P C _root_.instr.REF_IS_NULL
    (functype.mk_functype (list.mk_list [valtype_reftype rt]) (list.mk_list [valtype.I32]))
    (Instr_ok.ref_is_null C rt a a_1) := by
  intro C rt HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    rcases invert_typeof_reftype v1 rt Ht1 with Hnull | ⟨x, Hf | Hh⟩
    · refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Hnull]
      exact Step.pure _ _ _ (Step_pure.ref_is_null_true (ref.REF_NULL rt) rt rfl)
    · refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Hf]
      refine Step.pure _ _ _ (Step_pure.ref_is_null_false (ref.REF_FUNC_ADDR x) ?_)
      intro HContra
      generalize hl : [admininstr_ref (ref.REF_FUNC_ADDR x), admininstr.REF_IS_NULL] = l at HContra
      cases HContra with
      | ref_is_null_true_0 v_ref rt' h =>
        subst h
        simp [admininstr_ref] at hl
    · refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Hh]
      refine Step.pure _ _ _ (Step_pure.ref_is_null_false (ref.REF_HOST_ADDR x) ?_)
      intro HContra
      generalize hl : [admininstr_ref (ref.REF_HOST_ADDR x), admininstr.REF_IS_NULL] = l at HContra
      cases HContra with
      | ref_is_null_true_0 v_ref rt' h =>
        subst h
        simp [admininstr_ref] at hl
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vconst` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3716`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vconst :
    ∀ (C : context) (c : vec_) (a : wf_context C) (a_1 : wf_instr (_root_.instr.VCONST vectype.V128 c)),
  t_progress_be_P C (_root_.instr.VCONST vectype.V128 c) (functype.mk_functype (list.mk_list []) (list.mk_list [valtype.V128]))
    (Instr_ok.vconst C c a a_1) := by
  intro C c HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  left
  rfl

/-- Lean-only (bundle20): the `Instr_ok.vvunop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3721`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vvunop :
    ∀ (C : context) (v_vvunop : _root_.vvunop) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VVUNOP vectype.V128 v_vvunop)),
  t_progress_be_P C (_root_.instr.VVUNOP vectype.V128 v_vvunop)
    (functype.mk_functype (list.mk_list [valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vvunop C v_vvunop a a_1) := by
  intro C v_vvunop HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, _⟩ := invert_typeof_V128 v1 Ht1 HP
    refine ⟨s, f, [admininstr.VCONST vectype.V128 (vvunop_ vectype.V128 v_vvunop c1)], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1]
    exact Step.pure _ _ _ (Step_pure.vvunop c1 v_vvunop _ rfl)
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vvbinop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3733`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vvbinop :
    ∀ (C : context) (v_vvbinop : _root_.vvbinop) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VVBINOP vectype.V128 v_vvbinop)),
  t_progress_be_P C (_root_.instr.VVBINOP vectype.V128 v_vvbinop)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vvbinop C v_vvbinop a a_1) := by
  intro C v_vvbinop HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    have HP0 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, _⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, _⟩ := invert_typeof_V128 v2 Ht2 HP0
    refine ⟨s, f, [admininstr.VCONST vectype.V128 (vvbinop_ vectype.V128 v_vvbinop c1 c2)], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    exact Step.pure _ _ _ (Step_pure.vvbinop c1 c2 v_vvbinop _ rfl)
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vvternop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3746`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vvternop :
    ∀ (C : context) (v_vvternop : _root_.vvternop) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VVTERNOP vectype.V128 v_vvternop)),
  t_progress_be_P C (_root_.instr.VVTERNOP vectype.V128 v_vvternop)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.V128, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vvternop C v_vvternop a a_1) := by
  intro C v_vvternop HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, Ht3, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    have HP0 : wf_val v2 := HWfVals v2 (by simp)
    have HP1 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨c1, Heqv1, _⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, _⟩ := invert_typeof_V128 v2 Ht2 HP0
    obtain ⟨c3, Heqv3, _⟩ := invert_typeof_V128 v3 Ht3 HP1
    refine ⟨s, f, [admininstr.VCONST vectype.V128 (vvternop_ vectype.V128 v_vvternop c1 c2 c3)], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2, Heqv3]
    exact Step.pure _ _ _ (Step_pure.vvternop c1 c2 c3 v_vvternop _ rfl)
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vvtestop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3760`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vvtestop :
    ∀ (C : context) (v_vvtestop : _root_.vvtestop) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VVTESTOP vectype.V128 v_vvtestop)),
  t_progress_be_P C (_root_.instr.VVTESTOP vectype.V128 v_vvtestop)
    (functype.mk_functype (list.mk_list [valtype.V128]) (list.mk_list [valtype.I32]))
    (Instr_ok.vvtestop C v_vvtestop a a_1) := by
  intro C v_vvtestop HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    cases v_vvtestop
    exact ⟨s, f, [admininstr.CONST numtype.I32
        (num_.mk_num__0 Inn.I32 (ine_ (Option.get! (size valtype.V128)) c1 (uN.mk_uN 0)))],
      Step.pure _ _ _ (Step_pure.vvtestop c1 _ (by simp [proj_num__0]) (by simp [size]) rfl
        (wf_num_.num__case_0 _ _ _ (by simp [size, valtype_Inn])
          (ine__is_wf _ c1 (uN.mk_uN 0) _ Hwf1 (wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩) rfl) rfl)
        (wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vunop` case of Rocq's `t_progress_be` proof (no separate Rocq bullet (handled by the surrounding `Instrs_ok_ind'` automation / a shared bullet)),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vunop :
    ∀ (C : context) (sh : shape) (vunop_sh : vunop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VUNOP sh vunop_sh)),
  t_progress_be_P C (_root_.instr.VUNOP sh vunop_sh)
    (functype.mk_functype (list.mk_list [valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vunop C sh vunop_sh a a_1) := by
  intro C sh vunop_sh HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    have Hwfsh : wf_shape sh := by cases Hwfinstr; assumption
    have Hwfop : wf_vunop_ sh vunop_sh := by cases Hwfinstr; assumption
    obtain ⟨lst_opt, Hvunop⟩ := vunop_total sh vunop_sh c1 Hwfop Hwf1 Hwfsh
    rcases lst_opt with _ | ⟨_ | ⟨v', vs⟩⟩
    · exact absurd rfl (vunop_not_none sh vunop_sh c1 none Hwfop Hwf1 Hwfsh Hvunop)
    · exact ⟨s, f, [admininstr.TRAP], Step.pure _ _ _
        (Step_pure.vunop_trap c1 sh vunop_sh _ Hvunop (by simp) (by simp))⟩
    · exact ⟨s, f, [admininstr.VCONST vectype.V128 v'], Step.pure _ _ _
        (Step_pure.vunop c1 sh vunop_sh v' _ Hvunop (by simp) (by simp) (by simp))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vbinop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3803`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vbinop :
    ∀ (C : context) (sh : shape) (vbinop_sh : vbinop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VBINOP sh vbinop_sh)),
  t_progress_be_P C (_root_.instr.VBINOP sh vbinop_sh)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vbinop C sh vbinop_sh a a_1) := by
  intro C sh vbinop_sh HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP2
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
    have Hwfsh : wf_shape sh := by cases Hwfinstr; assumption
    have Hwfop : wf_vbinop_ sh vbinop_sh := by cases Hwfinstr; assumption
    obtain ⟨r, Hr⟩ := vbinop_some sh vbinop_sh c1 c2 Hwfsh Hwfop Hwf1 Hwf2
    rcases r with _ | ⟨v, vs⟩
    · exact ⟨s, f, [admininstr.TRAP], Step.pure _ _ _
        (Step_pure.vbinop_trap c1 c2 sh vbinop_sh _ Hr (by simp) (by simp))⟩
    · exact ⟨s, f, [admininstr.VCONST vectype.V128 v], Step.pure _ _ _
        (Step_pure.vbinop_val c1 c2 sh vbinop_sh v _ Hr (by simp) (by simp) (by simp))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vtestop` case of Rocq's `t_progress_be` proof (no separate Rocq bullet (handled by the surrounding `Instrs_ok_ind'` automation / a shared bullet)),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vtestop :
    ∀ (C : context) (sh : shape) (vtestop_sh : vtestop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VTESTOP sh vtestop_sh)),
  t_progress_be_P C (_root_.instr.VTESTOP sh vtestop_sh)
    (functype.mk_functype (list.mk_list [valtype.V128]) (list.mk_list [valtype.I32]))
    (Instr_ok.vtestop C sh vtestop_sh a a_1) := by
  intro C sh vtestop_sh HwfC Hwfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    have Hwfsh : wf_shape sh := by cases Hwfinstr; assumption
    have Hwfop : wf_vtestop_ sh vtestop_sh := by cases Hwfinstr; assumption
    obtain ⟨v_Jnn, v_N, var_x, Hsh⟩ := Hwfop
    subst Hsh
    cases var_x
    have Hlall := lanes__is_wf _ _ _ Hwfsh Hwf1 rfl
    cases E : List.all (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) c1)
        (fun ci => (proj_lane__0 ci != none) && (proj_uN_0 (Option.get! (proj_lane__0 ci)) != 0)) with
    | true =>
      obtain ⟨Hsome, Hnz⟩ := all_and_Forall _ _ _ _ E
      exact ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))], Step.pure _ _ _
        (Step_pure.vtestop_true c1 v_Jnn v_N _ rfl
          (fun ci hci => by simpa using Hsome ci hci)
          (fun ci hci => by simpa using Hnz ci hci) Hlall Hwfsh)⟩
    | false =>
      refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))], Step.pure _ _ _
        (Step_pure.vtestop_false c1 v_Jnn v_N ?_)⟩
      intro Hb
      generalize hl : [admininstr.VCONST vectype.V128 c1, admininstr.VTESTOP (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) (vtestop_.mk_vtestop__0 v_Jnn v_N vtestop_Jnn_N.ALL_TRUE)] = l at Hb
      cases Hb with
      | vtestop_true_0 c' J' N' ls Hls Hsome Hnz Hwl Hsh' =>
        obtain ⟨h1, h2⟩ := List.cons.inj hl
        obtain ⟨-, hc⟩ := admininstr.VCONST.inj h1
        obtain ⟨h3, -⟩ := List.cons.inj h2
        obtain ⟨hsh, -⟩ := admininstr.VTESTOP.inj h3
        subst hc
        subst Hls
        rw [hsh] at E
        have Hall := Forall_and_all _ (fun ci => proj_lane__0 ci != none)
          (fun ci => proj_uN_0 (Option.get! (proj_lane__0 ci)) != 0) _
          (fun ci hci => by simpa using Hsome ci hci) (fun ci hci => by simpa using Hnz ci hci)
        exact Bool.noConfusion (Hall.symm.trans E)
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vrelop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3852`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vrelop :
    ∀ (C : context) (sh : shape) (vrelop_sh : vrelop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VRELOP sh vrelop_sh)),
  t_progress_be_P C (_root_.instr.VRELOP sh vrelop_sh)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vrelop C sh vrelop_sh a a_1) := by
  intro C sh vrelop HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    have HP0 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP0
    have Hwfsh : wf_shape sh := by cases HWfinstr; assumption
    have Hwfop : wf_vrelop_ sh vrelop := by cases HWfinstr; assumption
    obtain ⟨r, Hr⟩ := vrelop_some sh vrelop c1 c2 Hwfsh Hwfop Hwf1 Hwf2
    refine ⟨s, f, [admininstr.VCONST vectype.V128 r], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    exact Step.pure _ _ _ (Step_pure.vrelop c1 c2 sh vrelop r (some r) Hr (Option.some_ne_none r) rfl)
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vshiftop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3867`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vshiftop :
    ∀ (C : context) (sh : ishape) (vshiftop_sh : vshiftop_) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VSHIFTOP sh vshiftop_sh)),
  t_progress_be_P C (_root_.instr.VSHIFTOP sh vshiftop_sh)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.I32]) (list.mk_list [valtype.V128]))
    (Instr_ok.vshiftop C sh vshiftop_sh a a_1) := by
  intro C sh op HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    have HP0 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨k, Heqv2, Hwfk⟩ := invert_typeof_I32_wf v2 Ht2 HP0
    have Hwish : wf_ishape sh := by cases HWfinstr; assumption
    have Hwop : wf_vshiftop_ sh op := by cases HWfinstr; assumption
    obtain ⟨J, M, o, Hsh⟩ := Hwop
    subst Hsh
    have Hwsh : wf_shape (shape.X (lanetype_Jnn J) (dim.mk_dim M)) := by cases Hwish; assumption
    have Hl := lanes__is_wf _ _ _ Hwsh Hwf1 rfl
    have Hlx : Forall (fun l => ∃ x, l = lane_.mk_lane__0 J x ∧ wf_uN (lsize (lanetype_Jnn J)) x)
        (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1) := by
      intro l hl
      exact wf_lane_Jnn_inv J l (Hl l hl) (wf_lane_Jnn_some J l (Hl l hl))
    cases o with
    | SHL =>
      refine ⟨s, f, [admininstr.VCONST vectype.V128 (inv_lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M))
        (List.map (fun l => lane_.mk_lane__0 J (ishl_ (lsizenn (lanetype_Jnn J)) (Option.get! (proj_lane__0 l)) (uN.mk_uN k)))
          (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Heqv1, Heqv2]
      refine Step.pure _ _ _ (Step_pure.vshiftop c1 k J M _ _ (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)
        (List.map (fun l => some (lane_.mk_lane__0 J (ishl_ (lsizenn (lanetype_Jnn J)) (Option.get! (proj_lane__0 l)) (uN.mk_uN k))))
          (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)) ?_ ?_ rfl ?_ ?_ Hl Hwsh Hwish Hwfk)
      · simp
      · apply Forall2_map_l
        intro l hl
        obtain ⟨x, rfl, _⟩ := Hlx l hl
        cases J
        · exact fun_vshiftop_.fun_vshiftop__case_0 M x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_1 M x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_2 M x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_3 M x k M rfl
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨l, _, rfl⟩ := ho
        exact Option.some_ne_none _
      · simp only [Map, List.map_map]
        rfl
    | SHR v_sx =>
      refine ⟨s, f, [admininstr.VCONST vectype.V128 (inv_lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M))
        (List.map (fun l => lane_.mk_lane__0 J (ishr_ (lsizenn (lanetype_Jnn J)) v_sx (Option.get! (proj_lane__0 l)) (uN.mk_uN k)))
          (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Heqv1, Heqv2]
      refine Step.pure _ _ _ (Step_pure.vshiftop c1 k J M _ _ (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)
        (List.map (fun l => some (lane_.mk_lane__0 J (ishr_ (lsizenn (lanetype_Jnn J)) v_sx (Option.get! (proj_lane__0 l)) (uN.mk_uN k))))
          (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)) ?_ ?_ rfl ?_ ?_ Hl Hwsh Hwish Hwfk)
      · simp
      · apply Forall2_map_l
        intro l hl
        obtain ⟨x, rfl, _⟩ := Hlx l hl
        cases J
        · exact fun_vshiftop_.fun_vshiftop__case_4 M v_sx x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_5 M v_sx x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_6 M v_sx x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_7 M v_sx x k M rfl
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨l, _, rfl⟩ := ho
        exact Option.some_ne_none _
      · simp only [Map, List.map_map]
        rfl
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vbitmask` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3917`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vbitmask :
    ∀ (C : context) (sh : ishape) (a : wf_context C) (a_1 : wf_instr (_root_.instr.VBITMASK sh)),
  t_progress_be_P C (_root_.instr.VBITMASK sh)
    (functype.mk_functype (list.mk_list [valtype.V128]) (list.mk_list [valtype.I32])) (Instr_ok.vbitmask C sh a a_1) := by
  intro C sh HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP
    have Hwish : wf_ishape sh := by cases HWfinstr; assumption
    obtain ⟨J, M, Hsh, Hwsh, HM⟩ := wf_ishape_inv _ Hwish
    subst Hsh
    have HL := lanes_Jnn_form J M c1 Hwsh Hwf1
    have Hz0 : wf_uN (lsize (lanetype_Jnn J)) (uN.mk_uN 0) :=
      wf_uN.uN_case_0 _ 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
    obtain ⟨vs, ⟨H2, Hsvs⟩, Hb⟩ := Forall_exists_Forall2 uN lane_
      (fun v l => fun_ilt_ (lsize (lanetype_Jnn J)) sx.S (Option.get! (proj_lane__0 l)) (uN.mk_uN 0) v)
      (fun v => wf_bit (bit.mk_bit (proj_uN_0 v)))
      (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)
      (by
        intro l hl
        obtain ⟨x, rfl, Hx⟩ := HL l hl
        obtain ⟨r, Hr, Hrb⟩ := (icmp_total_bit _ sx.S x (uN.mk_uN 0) Hx Hz0).1
        exact ⟨r, Hr, bit_of_wf1 _ Hrb⟩)
    have HlenM : (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1).length = M := lanes_len _ _ _
    obtain ⟨bits, Hbits⟩ : ∃ bits : List bit, bits =
        Map (fun (v : uN) => bit.mk_bit (proj_uN_0 v)) vs ++
          List.replicate (Int.toNat ((32 : Int) - (M : Int))) (bit.mk_bit 0) := ⟨_, rfl⟩
    have Hbw : Forall (fun b => wf_bit b) bits := by
      intro b hb
      rw [Hbits] at hb
      rcases List.mem_append.1 hb with hb | hb
      · simp only [Map, List.mem_map] at hb
        obtain ⟨v, hv, rfl⟩ := hb
        exact Hb v hv
      · rw [List.eq_of_mem_replicate hb]
        exact wf_bit.bit_case_0 0 (Or.inl rfl)
    have Hbl : bits.length = 32 := by
      rw [Hbits]
      simp only [Map, List.length_append, List.length_map, List.length_replicate]
      have HM' : @LE.le Nat instLENat M 16 := HM
      have Hsvs' : vs.length = (M : Nat) := Hsvs.trans HlenM
      rw [Hsvs']
      omega
    refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (irev_ 32 (inv_ibits_ 32 bits)))], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1]
    exact Step.pure _ _ _ (Step_pure.vbitmask c1 J M (inv_ibits_ 32 bits)
      (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1) vs
      Hsvs (jlane_some J _ HL) H2 rfl ((ibits_inv 32 bits Hbl Hbw).trans Hbits)
      (inv_ibits__is_wf 32 bits _ Hbw rfl) Hwsh Hb (wf_bit.bit_case_0 0 (Or.inl rfl)))
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vswizzle` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:3963`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vswizzle :
    ∀ (C : context) (sh : ishape) (a : wf_context C) (a_1 : wf_instr (_root_.instr.VSWIZZLE sh)),
  t_progress_be_P C (_root_.instr.VSWIZZLE sh)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vswizzle C sh a a_1) := by
  intro C sh HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP2
    have Hsh : sh = ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim 16)) := by
      cases HWfinstr; assumption
    subst Hsh
    have Hwsh : wf_shape (shape.X lanetype.I8 (dim.mk_dim 16)) :=
      wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (Or.inr rfl)) rfl
    have HL1 : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1) :=
      lanes_Jnn_form Jnn.I8 16 c1 Hwsh Hwf1
    have HL2 : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) :=
      lanes_Jnn_form Jnn.I8 16 c2 Hwsh Hwf2
    obtain ⟨cs, Hcs⟩ : ∃ cs : List iN, cs = List.map (fun l => Option.get! (proj_lane__0 l))
        (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1) ++
        List.replicate (Int.toNat ((256 : Int) - ((16 : Nat) : Int))) (uN.mk_uN 0) := ⟨_, rfl⟩
    have Hcsw : Forall (fun x => wf_uN 8 x) cs := by
      intro x hx
      rw [Hcs, List.mem_append] at hx
      rcases hx with hx | hx
      · exact jlane_proj_wf Jnn.I8 _ HL1 x hx
      · rw [List.eq_of_mem_replicate hx]
        exact wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩
    have Hcsl : cs.length = 256 := by
      rw [Hcs, List.length_append, List.length_map, lanes_len, List.length_replicate]
      all_goals decide
    have Hidx : ∀ k, k < 16 → ∃ x, (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2)[k]! =
        lane_.mk_lane__0 Jnn.I8 x ∧ wf_uN 8 x := by
      intro k hk
      have hk' : k < (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2).length := by
        rw [lanes_len]; exact hk
      rw [getElem!_pos _ k hk']
      exact HL2 _ (List.getElem_mem hk')
    have Hx256 : ∀ x : uN, wf_uN 8 x → proj_uN_0 x < 256 := by
      intro x hx
      cases hx with
      | uN_case_0 i h =>
        have h2 : i ≤ 255 := h.2
        simp only [proj_uN_0]; omega
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
    refine ⟨s, f, _, Step.pure _ _ _ (Step_pure.vswizzle c1 c2 packtype.I8 16 _
      (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) cs 0 rfl ?_ ?_ ?_ ?_ ?_ rfl Hwsh ?_ ?_)⟩
    · exact jlane_some Jnn.I8 _ HL1
    · exact Hcs
    · intro k hk
      rw [List.mem_range] at hk
      obtain ⟨x, Hx, Hwx⟩ := Hidx k hk
      rw [Hx, Hcsl]
      exact Hx256 x Hwx
    · intro k hk
      rw [List.mem_range] at hk
      obtain ⟨x, Hx, _⟩ := Hidx k hk
      rw [Hx]; simp [proj_lane__0]
    · intro k hk
      rw [List.mem_range] at hk
      rw [lanes_len]; exact hk
    · exact wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩
    · intro k hk
      rw [List.mem_range] at hk
      obtain ⟨x, Hx, Hwx⟩ := Hidx k hk
      rw [Hx]
      have hj : proj_uN_0 x < cs.length := by rw [Hcsl]; exact Hx256 x Hwx
      refine wf_lane_.lane__case_0 _ _ _ ?_ ?_
      · show wf_uN 8 (cs[proj_uN_0 x]!)
        rw [getElem!_pos cs _ hj]
        exact Hcsw _ (List.getElem_mem hj)
      · rfl
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vshuffle` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4009`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vshuffle :
    ∀ (C : context) (sh : ishape) (i_lst : List laneidx)
  (a : Forall (fun (i_elem : laneidx) => proj_uN_0 i_elem < 2 * proj_dim_0 (fun_dim (proj_ishape_0 sh))) i_lst)
  (a_1 : wf_context C) (a_2 : wf_dim (fun_dim (proj_ishape_0 sh))) (a_3 : wf_instr (_root_.instr.VSHUFFLE sh i_lst)),
  t_progress_be_P C (_root_.instr.VSHUFFLE sh i_lst)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vshuffle C sh i_lst a a_1 a_2 a_3) := by
  intro C sh i_lst Hilt HWfC HWfdim HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP2
    have Hshlen : sh = ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim 16)) ∧ i_lst.length = 16 := by
      cases HWfinstr; assumption
    obtain ⟨Hsh, Hlen⟩ := Hshlen
    subst Hsh
    have Hwsh : wf_shape (shape.X lanetype.I8 (dim.mk_dim 16)) :=
      wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (Or.inr rfl)) rfl
    have HL1 : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1) :=
      lanes_Jnn_form Jnn.I8 16 c1 Hwsh Hwf1
    have HL2 : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) :=
      lanes_Jnn_form Jnn.I8 16 c2 Hwsh Hwf2
    have HL : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1 ++
        lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact HL1 l hl
      · exact HL2 l hl
    obtain ⟨cs, Hcs⟩ : ∃ cs : List iN, cs = List.map (fun l => Option.get! (proj_lane__0 l))
        (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1 ++
         lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) := ⟨_, rfl⟩
    have Hcsw : Forall (fun x => wf_uN 8 x) cs := by
      rw [Hcs]; exact jlane_proj_wf Jnn.I8 _ HL
    have Hcsl : cs.length = 32 := by
      rw [Hcs, List.length_map, List.length_append, lanes_len, lanes_len]
    have Hi32 : ∀ k, k < 16 → proj_uN_0 (i_lst[k]!) < 32 := by
      intro k hk
      have hk' : k < i_lst.length := by rw [Hlen]; exact hk
      rw [getElem!_pos i_lst k hk']
      exact Hilt _ (List.getElem_mem hk')
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
    refine ⟨s, f, _, Step.pure _ _ _ (Step_pure.vshuffle c1 c2 packtype.I8 16 i_lst _ cs 0
      ?_ ?_ ?_ rfl ?_ Hwsh ?_)⟩
    · rw [Hcs]; exact jlane_map_proj Jnn.I8 _ HL
    · intro k hk
      rw [List.mem_range] at hk
      rw [Hcsl]; exact Hi32 k hk
    · intro k hk
      rw [List.mem_range] at hk
      rw [Hlen]; exact hk
    · intro x hx
      refine wf_lane_.lane__case_0 _ _ _ ?_ ?_
      · exact Hcsw x hx
      · rfl
    · intro k hk
      rw [List.mem_range] at hk
      have hj : proj_uN_0 (i_lst[k]!) < cs.length := by rw [Hcsl]; exact Hi32 k hk
      refine wf_lane_.lane__case_0 _ _ _ ?_ ?_
      · show wf_uN 8 (cs[proj_uN_0 (i_lst[k]!)]!)
        rw [getElem!_pos cs _ hj]
        exact Hcsw _ (List.getElem_mem hj)
      · rfl
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vsplat` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4051`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vsplat :
    ∀ (C : context) (sh : shape) (a : wf_context C) (a_1 : wf_instr (_root_.instr.VSPLAT sh)),
  t_progress_be_P C (_root_.instr.VSPLAT sh)
    (functype.mk_functype (list.mk_list [valtype_numtype (shunpack sh)]) (list.mk_list [valtype.V128]))
    (Instr_ok.vsplat C sh a a_1) := by
  intro C sh HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨Lnn, ⟨Ndim⟩⟩ := sh
    have Hwfsh : wf_shape (shape.X Lnn (dim.mk_dim Ndim)) := by cases HWfinstr; assumption
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_numtype_wf v1 (unpack Lnn) Ht1 HP1
    have Hpk := packnum_not_none Lnn c1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    exact ⟨s, f, [admininstr.VCONST vectype.V128
      (inv_lanes_ (shape.X Lnn (dim.mk_dim Ndim)) (List.replicate Ndim (Option.get! (packnum_ Lnn c1))))],
      Step.pure _ _ _ (Step_pure.vsplat Lnn c1 Ndim _ Hpk rfl Hwfsh)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vextract_lane` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4068`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vextract_lane :
    ∀ (C : context) (sh : shape) (sx_opt : Option sx) (i : laneidx)
  (a : proj_uN_0 i < proj_dim_0 (fun_dim sh)) (a_1 : wf_context C) (a_2 : wf_dim (fun_dim sh))
  (a_3 : wf_instr (_root_.instr.VEXTRACT_LANE sh sx_opt i)),
  t_progress_be_P C (_root_.instr.VEXTRACT_LANE sh sx_opt i)
    (functype.mk_functype (list.mk_list [valtype.V128]) (list.mk_list [valtype_numtype (shunpack sh)]))
    (Instr_ok.vextract_lane C sh sx_opt i a a_1 a_2 a_3) := by
  intro C sh sx_opt i Hi HWfC HWfdim HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    obtain ⟨lt, ⟨M⟩⟩ := sh
    have Hwsh : wf_shape (shape.X lt (dim.mk_dim M)) := by cases HWfinstr; assumption
    have Hiff : (List.contains [lanetype.I32, lanetype.I64, lanetype.F32, lanetype.F64] lt = true) ↔
        (sx_opt = none) := by
      cases HWfinstr; assumption
    have Hi' : proj_uN_0 i < M := Hi
    have Hwf1' : wf_uN 128 c1 := Hwf1
    have Hl := lanes_nth_wf lt M c1 (proj_uN_0 i) Hwsh Hwf1' Hi'
    have Hlen : proj_uN_0 i < (lanes_ (shape.X lt (dim.mk_dim M)) c1).length := by
      rw [lanes_len]; exact Hi'
    rcases sx_opt with _ | sx <;> cases lt
    -- numtype lanes, no sign extension
    · obtain ⟨x, Hx, -⟩ := wf_lane_Jnn_inv Jnn.I32 _ Hl (wf_lane_Jnn_some Jnn.I32 _ Hl)
      exact ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 x)], Step.pure _ _ _
        (Step_pure.vextract_lane_num c1 numtype.I32 M i _
          (show unpacknum_ lanetype.I32 ((lanes_ (shape.X lanetype.I32 (dim.mk_dim M)) c1)[proj_uN_0 i]!) ≠ none by
            rw [Hx]; simp [unpacknum_])
          Hlen
          (show num_.mk_num__0 Inn.I32 x = Option.get! (unpacknum_ lanetype.I32 ((lanes_ (shape.X lanetype.I32 (dim.mk_dim M)) c1)[proj_uN_0 i]!)) by
            rw [Hx]; simp [unpacknum_])
          Hwsh)⟩
    · obtain ⟨x, Hx, -⟩ := wf_lane_Jnn_inv Jnn.I64 _ Hl (wf_lane_Jnn_some Jnn.I64 _ Hl)
      exact ⟨s, f, [admininstr.CONST numtype.I64 (num_.mk_num__0 Inn.I64 x)], Step.pure _ _ _
        (Step_pure.vextract_lane_num c1 numtype.I64 M i _
          (show unpacknum_ lanetype.I64 ((lanes_ (shape.X lanetype.I64 (dim.mk_dim M)) c1)[proj_uN_0 i]!) ≠ none by
            rw [Hx]; simp [unpacknum_])
          Hlen
          (show num_.mk_num__0 Inn.I64 x = Option.get! (unpacknum_ lanetype.I64 ((lanes_ (shape.X lanetype.I64 (dim.mk_dim M)) c1)[proj_uN_0 i]!)) by
            rw [Hx]; simp [unpacknum_])
          Hwsh)⟩
    · obtain ⟨x, Hx, -⟩ := wf_lane_Fnn_inv Fnn.F32 _ Hl
      exact ⟨s, f, [admininstr.CONST numtype.F32 (num_.mk_num__1 Fnn.F32 x)], Step.pure _ _ _
        (Step_pure.vextract_lane_num c1 numtype.F32 M i _
          (show unpacknum_ lanetype.F32 ((lanes_ (shape.X lanetype.F32 (dim.mk_dim M)) c1)[proj_uN_0 i]!) ≠ none by
            rw [Hx]; simp [unpacknum_])
          Hlen
          (show num_.mk_num__1 Fnn.F32 x = Option.get! (unpacknum_ lanetype.F32 ((lanes_ (shape.X lanetype.F32 (dim.mk_dim M)) c1)[proj_uN_0 i]!)) by
            rw [Hx]; simp [unpacknum_])
          Hwsh)⟩
    · obtain ⟨x, Hx, -⟩ := wf_lane_Fnn_inv Fnn.F64 _ Hl
      exact ⟨s, f, [admininstr.CONST numtype.F64 (num_.mk_num__1 Fnn.F64 x)], Step.pure _ _ _
        (Step_pure.vextract_lane_num c1 numtype.F64 M i _
          (show unpacknum_ lanetype.F64 ((lanes_ (shape.X lanetype.F64 (dim.mk_dim M)) c1)[proj_uN_0 i]!) ≠ none by
            rw [Hx]; simp [unpacknum_])
          Hlen
          (show num_.mk_num__1 Fnn.F64 x = Option.get! (unpacknum_ lanetype.F64 ((lanes_ (shape.X lanetype.F64 (dim.mk_dim M)) c1)[proj_uN_0 i]!)) by
            rw [Hx]; simp [unpacknum_])
          Hwsh)⟩
    -- sx = none with a packed lane, or sx = some with a numtype lane, contradicts the side condition
    · exact absurd (Hiff.mpr rfl) (by decide)
    · exact absurd (Hiff.mpr rfl) (by decide)
    · exact absurd (Hiff.mp (by decide)) (by simp)
    · exact absurd (Hiff.mp (by decide)) (by simp)
    · exact absurd (Hiff.mp (by decide)) (by simp)
    · exact absurd (Hiff.mp (by decide)) (by simp)
    -- packed lanes, sign extension
    · obtain ⟨x, Hx, Hwx⟩ := wf_lane_Jnn_inv Jnn.I8 _ Hl (wf_lane_Jnn_some Jnn.I8 _ Hl)
      exact ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (extend__ 8 32 sx x))], Step.pure _ _ _
        (Step_pure.vextract_lane_pack c1 packtype.I8 M sx i (num_.mk_num__0 Inn.I32 (extend__ 8 32 sx x))
          (by simp [proj_num__0])
          (wf_lane_Jnn_some Jnn.I8 _ Hl)
          Hlen
          (show extend__ 8 32 sx x = extend__ 8 32 sx (Option.get! (proj_lane__0 ((lanes_ (shape.X lanetype.I8 (dim.mk_dim M)) c1)[proj_uN_0 i]!))) by
            rw [Hx]; simp [proj_lane__0])
          (wf_num_.num__case_0 _ _ _ (by simp [size, valtype_Inn]) (extend___is_wf 8 32 sx x _ Hwx rfl) rfl)
          Hwsh)⟩
    · obtain ⟨x, Hx, Hwx⟩ := wf_lane_Jnn_inv Jnn.I16 _ Hl (wf_lane_Jnn_some Jnn.I16 _ Hl)
      exact ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (extend__ 16 32 sx x))], Step.pure _ _ _
        (Step_pure.vextract_lane_pack c1 packtype.I16 M sx i (num_.mk_num__0 Inn.I32 (extend__ 16 32 sx x))
          (by simp [proj_num__0])
          (wf_lane_Jnn_some Jnn.I16 _ Hl)
          Hlen
          (show extend__ 16 32 sx x = extend__ 16 32 sx (Option.get! (proj_lane__0 ((lanes_ (shape.X lanetype.I16 (dim.mk_dim M)) c1)[proj_uN_0 i]!))) by
            rw [Hx]; simp [proj_lane__0])
          (wf_num_.num__case_0 _ _ _ (by simp [size, valtype_Inn]) (extend___is_wf 16 32 sx x _ Hwx rfl) rfl)
          Hwsh)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vreplace_lane` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4112`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vreplace_lane :
    ∀ (C : context) (sh : shape) (i : laneidx) (a : proj_uN_0 i < proj_dim_0 (fun_dim sh))
  (a_1 : wf_context C) (a_2 : wf_dim (fun_dim sh)) (a_3 : wf_instr (_root_.instr.VREPLACE_LANE sh i)),
  t_progress_be_P C (_root_.instr.VREPLACE_LANE sh i)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype_numtype (shunpack sh)]) (list.mk_list [valtype.V128]))
    (Instr_ok.vreplace_lane C sh i a a_1 a_2 a_3) := by
  intro C sh i Hrange HWfC HWfdim HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨Lnn, ⟨Ndim⟩⟩ := sh
    have Hwfsh : wf_shape (shape.X Lnn (dim.mk_dim Ndim)) := by cases HWfinstr; assumption
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_numtype_wf v2 _ Ht2 HP2
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
    have Hpk := packnum_not_none Lnn c2 Hwf2
    exact ⟨s, f, _, Step.pure _ _ _ (Step_pure.vreplace_lane c1 Lnn c2 Ndim i _ Hpk rfl Hwfsh)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vextunop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4132`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vextunop :
    ∀ (C : context) (sh_1 sh_2 : ishape) (vextunop : vextunop__) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VEXTUNOP sh_1 sh_2 vextunop)),
  t_progress_be_P C (_root_.instr.VEXTUNOP sh_1 sh_2 vextunop)
    (functype.mk_functype (list.mk_list [valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vextunop C sh_1 sh_2 vextunop a a_1) := by
  intro C sh_1 sh_2 op HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    have Hw1 : wf_ishape sh_1 := by cases HWfinstr; assumption
    have Hw2 : wf_ishape sh_2 := by cases HWfinstr; assumption
    have Hop : wf_vextunop__ sh_2 sh_1 op := by cases HWfinstr; assumption
    obtain ⟨J1, M1, J2, M2, o, Ho, E1, E2⟩ := Hop
    subst E1 E2
    have Hs1 : wf_shape (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) := by cases Hw2; assumption
    have Hs2 : wf_shape (shape.X (lanetype_Jnn J2) (dim.mk_dim M2)) := by cases Hw1; assumption
    have H128 : lsize (lanetype_Jnn J1) * M1 = 128 := by cases Hs1; assumption
    obtain ⟨sx, Hsz⟩ := Ho
    have Hwf1' : wf_uN 128 c1 := Hwf1
    have HL := lanes_Jnn_form J1 M1 c1 Hs1 Hwf1'
    obtain ⟨E, hE⟩ : ∃ E : List iN, E = List.map (fun l => extend__ (lsizenn1 (lanetype_Jnn J1))
        (lsizenn2 (lanetype_Jnn J2)) sx (Option.get! (proj_lane__0 l)))
        (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) c1) := ⟨_, rfl⟩
    have HEw : Forall (fun x => wf_uN (lsize (lanetype_Jnn J2)) x) E := by
      rw [hE]
      refine Forall_map_P _ _ _ (jlane J1) _ _ ?_ HL
      rintro l ⟨x, rfl, Hx⟩
      exact extend___is_wf (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx x _ Hx rfl
    have HEe : ¬ Odd E.length := by
      rw [hE, List.length_map]; exact shape_lanes_even J1 M1 c1 H128
    have HEs := evens_odds_size _ _ HEe
    have HW2 : Forall₂ (fun a b => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn J2) (dim.mk_dim M2)))
        (lane_.mk_lane__0 J2 (iadd_ (lsizenn2 (lanetype_Jnn J2)) a b))) (evens E) (odds E) :=
      Forall2_of_Forall iN (fun x => wf_uN (lsize (lanetype_Jnn J2)) x) _ (evens E) (odds E)
        (fun a b Ha Hb => wf_lane_.lane__case_0 _ _ _
          (iadd__is_wf (lsizenn2 (lanetype_Jnn J2)) a b _ Ha Hb rfl) rfl)
        (Forall_evens _ _ _ HEw) (Forall_odds _ _ _ HEw) HEs
    have HS := jlane_some _ _ HL
    have HEc : concat_ iN (Map₂ (fun a b => [a, b]) (evens E) (odds E)) =
        Map (fun l => extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx
          (Option.get! (proj_lane__0 l))) (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) c1) := by
      have hM : Map₂ (fun a b : iN => [a, b]) (evens E) (odds E) =
          List.zipWith (fun a b => [a, b]) (evens E) (odds E) := by
        simp [Map₂, List.ap, List.zipWith_map_left]
      rw [hM, evens_odds_concat _ _ HEe]
      exact hE
    have Hfun : fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)))
        (ishape.mk_ishape (shape.X (lanetype_Jnn J2) (dim.mk_dim M2)))
        (vextunop__.mk_vextunop___0 J1 M1 J2 M2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx)) c1
        (some (inv_lanes_ (shape.X (lanetype_Jnn J2) (dim.mk_dim M2))
          (Map₂ (fun a b => lane_.mk_lane__0 J2 (iadd_ (lsizenn2 (lanetype_Jnn J2)) a b)) (evens E) (odds E)))) := by
      cases J1 <;> cases J2 <;> first
        | exact absurd Hsz (by decide)
        | exact fun_vextunop__.fun_vextunop___case_14 M1 M2 sx c1 (evens E) (odds E) M1 M2 _ _
            rfl HS HEc rfl Hs1 Hs2 HEs HW2 rfl rfl
        | exact fun_vextunop__.fun_vextunop___case_3 M1 M2 sx c1 (evens E) (odds E) M1 M2 _ _
            rfl HS HEc rfl Hs1 Hs2 HEs HW2 rfl rfl
    exact ⟨s, f, _, Step.pure _ _ _ (Step_pure.vextunop c1 _ _ _ _ _ Hfun (by simp) rfl)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vextbinop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4180`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vextbinop :
    ∀ (C : context) (sh_1 sh_2 : ishape) (vextbinop : vextbinop__) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VEXTBINOP sh_1 sh_2 vextbinop)),
  t_progress_be_P C (_root_.instr.VEXTBINOP sh_1 sh_2 vextbinop)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vextbinop C sh_1 sh_2 vextbinop a a_1) := by
  intro C sh_1 sh_2 op HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    have HP0 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP0
    have Hw1 : wf_ishape sh_1 := by cases HWfinstr; assumption
    have Hw2 : wf_ishape sh_2 := by cases HWfinstr; assumption
    have Hop : wf_vextbinop__ sh_2 sh_1 op := by cases HWfinstr; assumption
    obtain ⟨J1, M1, J2, M2, o, Ho, E1, E2⟩ := Hop
    subst E1 E2
    have Hs1 : wf_shape (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) := by cases Hw2; assumption
    have Hs2 : wf_shape (shape.X (lanetype_Jnn J2) (dim.mk_dim M2)) := by cases Hw1; assumption
    have H128 : lsize (lanetype_Jnn J1) * M1 = 128 := by
      cases Hs1 with
      | shape_case_0 _ _ _ h => exact h
    have HL1 := lanes_Jnn_form J1 M1 c1 Hs1 Hwf1
    have HL2 := lanes_Jnn_form J1 M1 c2 Hs1 Hwf2
    have HLs := lanes_size_eq (lanetype_Jnn J1) M1 c1 c2
    -- Lean's `Map₂` is `zipWith` (Rocq's `list_zipWith`)
    have hMap2 : ∀ {A B D : Type} (g : A → B → D) (l1 : List A) (l2 : List B),
        Map₂ g l1 l2 = List.zipWith g l1 l2 := by
      intro A B D g l1 l2
      simp [Map₂, List.ap, List.zipWith_map_left]
    have Hext : ∀ (v_sx : sx) (l : lane_), jlane J1 l →
        wf_uN (lsize (lanetype_Jnn J2)) (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) v_sx
          (Option.get! (proj_lane__0 l))) := by
      intro v_sx l ⟨x, hx, Hx⟩
      subst hx
      exact extend___is_wf _ _ v_sx x _ Hx rfl
    have Hfun : ∃ c, fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)))
        (ishape.mk_ishape (shape.X (lanetype_Jnn J2) (dim.mk_dim M2)))
        (vextbinop__.mk_vextbinop___0 J1 M1 J2 M2 o) c1 c2 (some c) := by
      rcases Ho with ⟨hf, v_sx, Hsz⟩ | ⟨Hsz⟩
      · -- EXTMUL: the extended lanes of one half of each operand are multiplied.
        have HS1 := Forall_list_slice _ _ (fun_half hf 0 M2) M2 HL1
        have HS2 := Forall_list_slice _ _ (fun_half hf 0 M2) M2 HL2
        have HSs := list_slice_size_eq _ _ _ _ (fun_half hf 0 M2) M2 HLs
        have HW := zip_lane_wf2 J1 J2 (lanetype_Jnn J2)
          (fun a b => imul_ (lsizenn2 (lanetype_Jnn J2))
            (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) v_sx a)
            (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) v_sx b)) _ _ rfl
          (fun a b Ha Hb => imul__is_wf _ _ _ _ (extend___is_wf _ _ _ _ _ Ha rfl)
            (extend___is_wf _ _ _ _ _ Hb rfl) rfl) HS1 HS2 HSs
        have HSo1 := jlane_some _ _ HS1
        have HSo2 := jlane_some _ _ HS2
        cases J1 <;> cases J2 <;> (try exact absurd Hsz (by decide)) <;>
        first
          | exact ⟨_, fun_vextbinop__.fun_vextbinop___case_3 M1 M2 hf v_sx c1 c2 M1 M2 _ _ _ rfl rfl
              HSo1 HSo2 rfl Hs1 Hs2 HSs HSo1 HSo2 HW rfl rfl⟩
          | exact ⟨_, fun_vextbinop__.fun_vextbinop___case_4 M1 M2 hf v_sx c1 c2 M1 M2 _ _ _ rfl rfl
              HSo1 HSo2 rfl Hs1 Hs2 HSs HSo1 HSo2 HW rfl rfl⟩
          | exact ⟨_, fun_vextbinop__.fun_vextbinop___case_14 M1 M2 hf v_sx c1 c2 M1 M2 _ _ _ rfl rfl
              HSo1 HSo2 rfl Hs1 Hs2 HSs HSo1 HSo2 HW rfl rfl⟩
      · -- DOT: the products of the extended lanes are added pairwise.
        obtain ⟨P, HPdef⟩ : ∃ P : List iN, P = List.zipWith (fun a b => imul_ (lsizenn2 (lanetype_Jnn J2))
            (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx.S (Option.get! (proj_lane__0 a)))
            (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx.S (Option.get! (proj_lane__0 b))))
            (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) c1)
            (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) c2) := ⟨_, rfl⟩
        have HPw : Forall (fun x => wf_uN (lsize (lanetype_Jnn J2)) x) P := by
          rw [HPdef]
          exact zip_wf J1 _ _ _ _ (fun a b Ha Hb => imul__is_wf _ _ _ _ (Hext _ _ Ha) (Hext _ _ Hb) rfl) HL1 HL2
        have HPe : ¬ Odd P.length := by
          rw [HPdef, size_zipWith_eq _ _ _ _ _ _ HLs]
          exact shape_lanes_even J1 M1 c1 H128
        have HPs := evens_odds_size _ _ HPe
        have HPc := evens_odds_concat _ _ HPe
        have HW2 : Forall₂ (fun a b => wf_lane_ (lanetype_Jnn J2)
            (lane_.mk_lane__0 J2 (iadd_ (lsizenn2 (lanetype_Jnn J2)) a b))) (evens P) (odds P) :=
          Forall2_of_Forall _ _ _ _ _
            (fun a b Ha Hb => wf_lane_.lane__case_0 _ J2 _ (iadd__is_wf _ _ _ _ Ha Hb rfl) rfl)
            (Forall_evens _ _ _ HPw) (Forall_odds _ _ _ HPw) HPs
        have HSo1 := jlane_some _ _ HL1
        have HSo2 := jlane_some _ _ HL2
        cases J1 <;> cases J2 <;> (try exact absurd Hsz (by decide))
        exact ⟨_, fun_vextbinop__.fun_vextbinop___case_19 M1 M2 c1 c2 (evens P) (odds P) M1 M2 _ _ _ rfl rfl
          HSo1 HSo2 (by simp only [hMap2]; exact HPc.trans HPdef) rfl Hs1 Hs2 HPs HW2 rfl rfl⟩
    obtain ⟨c, Hc⟩ := Hfun
    refine ⟨s, f, [admininstr.VCONST vectype.V128 c], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    exact Step.pure _ _ _ (Step_pure.vextbinop c1 c2 _ _ _ c (some c) Hc (Option.some_ne_none c) rfl)
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vnarrow` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4264`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vnarrow :
    ∀ (C : context) (sh_1 sh_2 : ishape) (v_sx : sx) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VNARROW sh_1 sh_2 v_sx)),
  t_progress_be_P C (_root_.instr.VNARROW sh_1 sh_2 v_sx)
    (functype.mk_functype (list.mk_list [valtype.V128, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vnarrow C sh_1 sh_2 v_sx a a_1) := by
  intro C sh_1 sh_2 v_sx HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    have HP0 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP0
    have Hw1 : wf_ishape sh_1 := by cases HWfinstr; assumption
    have Hw2 : wf_ishape sh_2 := by cases HWfinstr; assumption
    obtain ⟨J2, N2, rfl, Hs2, _⟩ := wf_ishape_inv _ Hw1
    obtain ⟨J1, N1, rfl, Hs1, _⟩ := wf_ishape_inv _ Hw2
    have HL1 := lanes_Jnn_form J1 N1 c1 Hs1 Hwf1
    have HL2 := lanes_Jnn_form J1 N1 c2 Hs1 Hwf2
    have Hnar : ∀ L, Forall (jlane J1) L →
        Forall (fun cj => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn J2) (dim.mk_dim N2))) (lane_.mk_lane__0 J2 cj))
          (List.map (fun l => narrow__ (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2)) v_sx
            (Option.get! (proj_lane__0 l))) L) := by
      intro L HL
      refine Forall_map_P _ _ _ _ _ _ ?_ HL
      intro l ⟨x, hx, Hx⟩
      subst hx
      exact wf_lane_.lane__case_0 _ J2 _ (narrow___is_wf _ _ v_sx x _ Hx rfl) rfl
    refine ⟨s, f, [admininstr.VCONST vectype.V128 (inv_lanes_ (shape.X (lanetype_Jnn J2) (dim.mk_dim N2))
      (Map (fun cj => lane_.mk_lane__0 J2 cj) (Map (fun l => narrow__ (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2)) v_sx
          (Option.get! (proj_lane__0 l))) (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim N1)) c1)) ++
       Map (fun cj => lane_.mk_lane__0 J2 cj) (Map (fun l => narrow__ (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2)) v_sx
          (Option.get! (proj_lane__0 l))) (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim N1)) c2))))], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    exact Step.pure _ _ _ (Step_pure.vnarrow c1 c2 J2 N2 J1 N1 v_sx _
      (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim N1)) c1) (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim N1)) c2)
      _ _ rfl rfl (jlane_some _ _ HL1) rfl (jlane_some _ _ HL2) rfl rfl
      (lanes__is_wf _ _ _ Hs1 Hwf1 rfl) (lanes__is_wf _ _ _ Hs1 Hwf2 rfl) Hs1 Hs2 (Hnar _ HL1) (Hnar _ HL2))
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vcvtop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4301`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vcvtop :
    ∀ (C : context) (sh_1 sh_2 : shape) (vcvtop : vcvtop__) (a : wf_context C)
  (a_1 : wf_instr (_root_.instr.VCVTOP sh_1 sh_2 vcvtop)),
  t_progress_be_P C (_root_.instr.VCVTOP sh_1 sh_2 vcvtop)
    (functype.mk_functype (list.mk_list [valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vcvtop C sh_1 sh_2 vcvtop a a_1) := by
  intro C sh_1 sh_2 op HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Hts HP
    have Hwf1' : wf_uN 128 c1 := Hwf1
    rw [show List.map admininstr_val [v1] = [admininstr.VCONST vectype.V128 c1] by
      simp [Heqv1]]
    have Hs1 : wf_shape sh_1 := by cases HWfinstr; assumption
    have Hs2 : wf_shape sh_2 := by cases HWfinstr; assumption
    have Hop : wf_vcvtop__ sh_2 sh_1 op := by cases HWfinstr; assumption
    cases Hti : vcvtop_trunc_sat_i16 op with
    | true =>
      -- FALSE subcase as the spec stands (Rocq: admit at type_progress.v:4319); see vcvtop_trunc_sat_i16_stuck.
      sorry
    | false =>
      obtain ⟨L2, ⟨M2⟩⟩ := sh_1
      obtain ⟨L1, ⟨M1⟩⟩ := sh_2
      cases Hh : halfop_of op with
      | some h =>
        obtain ⟨c, Hc⟩ := vcvtop_step_half L1 M1 L2 M2 op c1 h Hwf1' Hs2 Hs1 Hop Hti Hh
        exact ⟨s, f, [admininstr.VCONST vectype.V128 c], Step.pure _ _ _ Hc⟩
      | none =>
        cases Hz : zeroop_of op with
        | some z =>
          obtain ⟨nt1, nt2, E1, E2⟩ := vcvtop_zero_numtype L1 M1 L2 M2 op z Hop Hti Hz
          subst E1 E2
          cases z
          obtain ⟨c, Hc⟩ := vcvtop_step_zero nt1 M1 nt2 M2 op c1 Hwf1' Hs2 Hs1 Hop Hti Hz
          exact ⟨s, f, [admininstr.VCONST vectype.V128 c], Step.pure _ _ _ Hc⟩
        | none =>
          have HL := vcvtop_full_lsize L1 M1 L2 M2 op Hop Hti Hh Hz
          have HM : M1 = M2 := by
            have Hm1 : lsize L1 * M1 = 128 := by cases Hs2; assumption
            have Hm2 : lsize L2 * M2 = 128 := by cases Hs1; assumption
            have Hp : 0 < lsize L2 := by cases L2 <;> decide
            rw [HL] at Hm1
            exact Nat.eq_of_mul_eq_mul_left Hp (Hm1.trans Hm2.symm)
          subst HM
          obtain ⟨c, Hc⟩ := vcvtop_step_full L1 L2 _ op c1 Hwf1' Hs2 Hs1 Hop Hti Hh Hz
          exact ⟨s, f, [admininstr.VCONST vectype.V128 c], Step.pure _ _ _ Hc⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.local_get` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4340`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_local_get :
    ∀ (C : context) (x : idx) (t : valtype) (a : proj_uN_0 x < C.LOCALS.length)
  (a_1 : C.LOCALS[proj_uN_0 x]! = t) (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.LOCAL_GET x)),
  t_progress_be_P C (_root_.instr.LOCAL_GET x) (functype.mk_functype (list.mk_list []) (list.mk_list [t]))
    (Instr_ok.local_get C x t a a_1 a_2 a_3) := by
  intro C x t Hlen Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs1⟩
  · exact ⟨s, f, List.map admininstr_val [fun_local (state.mk_state s f) x],
      Step.read _ _ _ (Step_read.local_get _ x)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.local_set` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4349`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_local_set :
    ∀ (C : context) (x : idx) (t : valtype) (a : proj_uN_0 x < C.LOCALS.length)
  (a_1 : C.LOCALS[proj_uN_0 x]! = t) (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.LOCAL_SET x)),
  t_progress_be_P C (_root_.instr.LOCAL_SET x) (functype.mk_functype (list.mk_list [t]) (list.mk_list []))
    (Instr_ok.local_set C x t a a_1 a_2 a_3) := by
  intro C x t Hlen Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · cases Estate : with_local (state.mk_state s f) x v1 with
    | mk_state s' f' =>
      refine ⟨s', f', [], ?_⟩
      rw [← Estate]
      exact Step.local_set _ v1 x
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.local_tee` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4359`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_local_tee :
    ∀ (C : context) (x : idx) (t : valtype) (a : proj_uN_0 x < C.LOCALS.length)
  (a_1 : C.LOCALS[proj_uN_0 x]! = t) (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.LOCAL_TEE x)),
  t_progress_be_P C (_root_.instr.LOCAL_TEE x) (functype.mk_functype (list.mk_list [t]) (list.mk_list [t]))
    (Instr_ok.local_tee C x t a a_1 a_2 a_3) := by
  intro C x t Hlen Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · exact ⟨s, f, [admininstr_val v1, admininstr_val v1, admininstr.LOCAL_SET x],
      Step.pure _ _ _ (Step_pure.local_tee v1 x)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.global_get` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4368`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_global_get :
    ∀ (C : context) (x : idx) (t : valtype) (v_mut : «mut») (a : proj_uN_0 x < C.GLOBALS.length)
  (a_1 : C.GLOBALS[proj_uN_0 x]! = globaltype.mk_globaltype v_mut t) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.GLOBAL_GET x)),
  t_progress_be_P C (_root_.instr.GLOBAL_GET x) (functype.mk_functype (list.mk_list []) (list.mk_list [t]))
    (Instr_ok.global_get C x t v_mut a a_1 a_2 a_3) := by
  intro C x t v_mut Hlen Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs1⟩
  · exact ⟨s, f, List.map admininstr_val [(fun_global (state.mk_state s f) x).VALUE],
      Step.read _ _ _ (Step_read.global_get _ x)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.global_set` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4377`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_global_set :
    ∀ (C : context) (x : idx) (t : valtype) (a : proj_uN_0 x < C.GLOBALS.length)
  (a_1 : C.GLOBALS[proj_uN_0 x]! = globaltype.mk_globaltype (some r_MUT.MUT) t) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.GLOBAL_SET x)),
  t_progress_be_P C (_root_.instr.GLOBAL_SET x) (functype.mk_functype (list.mk_list [t]) (list.mk_list []))
    (Instr_ok.global_set C x t a a_1 a_2 a_3) := by
  intro C x t Hlen Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · cases Estate : with_global (state.mk_state s f) x v1 with
    | mk_state s' f' =>
      refine ⟨s', f', [], ?_⟩
      rw [← Estate]
      exact Step.global_set _ v1 x
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.table_get` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4388`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_table_get :
    ∀ (C : context) (x : idx) (rt : reftype) (lim : limits) (a : proj_uN_0 x < C.TABLES.length)
  (a_1 : C.TABLES[proj_uN_0 x]! = tabletype.mk_tabletype lim rt) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.TABLE_GET x)) (a_4 : wf_tabletype (tabletype.mk_tabletype lim rt)),
  t_progress_be_P C (_root_.instr.TABLE_GET x)
    (functype.mk_functype (list.mk_list [valtype.I32]) (list.mk_list [valtype_reftype rt]))
    (Instr_ok.table_get C x rt lim a a_1 a_2 a_3 a_4) := by
  intro C x rt lim Hlen Hlookup HWfC HWfinstr HWfTabType
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n, Heqv⟩ := invert_typeof_I32 v1 Ht1 HP1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv]
    by_cases Es : n < (fun_table (state.mk_state s f) x).REFS.length
    · exact ⟨s, f, [admininstr_ref ((fun_table (state.mk_state s f) x).REFS[n]!)],
        Step.read _ _ _ (Step_read.table_get_val _ _ x
          (by simpa [proj_num__0, proj_uN_0] using Es) (by simp [proj_num__0]))⟩
    · exact ⟨s, f, [admininstr.TRAP],
        Step.read _ _ _ (Step_read.table_get_trap _ _ x (by simp [proj_num__0])
          (by simp [proj_num__0, proj_uN_0]; omega))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.table_set` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4408`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_table_set :
    ∀ (C : context) (x : idx) (rt : reftype) (lim : limits) (a : proj_uN_0 x < C.TABLES.length)
  (a_1 : C.TABLES[proj_uN_0 x]! = tabletype.mk_tabletype lim rt) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.TABLE_SET x)) (a_4 : wf_tabletype (tabletype.mk_tabletype lim rt)),
  t_progress_be_P C (_root_.instr.TABLE_SET x)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype_reftype rt]) (list.mk_list []))
    (Instr_ok.table_set C x rt lim a a_1 a_2 a_3 a_4) := by
  intro C x rt lim Hlen Hlookup HWfC HWfinstr HWfTabType
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs3⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 HP1
    obtain ⟨r2, Heqv2⟩ := invert_typeof_reftype' v2 rt Ht2
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    by_cases Es : n1 < (fun_table (state.mk_state s f) x).REFS.length
    · cases Estate : with_table (state.mk_state s f) x n1 r2 with
      | mk_state s' f' =>
        refine ⟨s', f', [], ?_⟩
        rw [← Estate]
        exact Step.table_set_val _ _ r2 x (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Es)
    · exact ⟨s, f, [admininstr.TRAP],
        Step.table_set_trap _ _ r2 x (by simp [proj_num__0])
          (by simp [proj_num__0, proj_uN_0]; omega)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.table_size` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4429`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_table_size :
    ∀ (C : context) (x : idx) (lim : limits) (rt : reftype) (a : proj_uN_0 x < C.TABLES.length)
  (a_1 : C.TABLES[proj_uN_0 x]! = tabletype.mk_tabletype lim rt) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.TABLE_SIZE x)) (a_4 : wf_tabletype (tabletype.mk_tabletype lim rt)),
  t_progress_be_P C (_root_.instr.TABLE_SIZE x) (functype.mk_functype (list.mk_list []) (list.mk_list [valtype.I32]))
    (Instr_ok.table_size C x lim rt a a_1 a_2 a_3 a_4) := by
  intro C x lim rt Hlen Hlookup HWfC HWfinstr HWfTabType
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs1⟩
  · exact ⟨s, f, [admininstr.CONST numtype.I32
        (num_.mk_num__0 Inn.I32 (uN.mk_uN (fun_table (state.mk_state s f) x).REFS.length))],
      Step.read _ _ _ (Step_read.table_size _ x _ rfl)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.table_grow` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4448`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_table_grow :
    ∀ (C : context) (x : idx) (rt : reftype) (lim : limits) (a : proj_uN_0 x < C.TABLES.length)
  (a_1 : C.TABLES[proj_uN_0 x]! = tabletype.mk_tabletype lim rt) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.TABLE_GROW x)) (a_4 : wf_tabletype (tabletype.mk_tabletype lim rt)),
  t_progress_be_P C (_root_.instr.TABLE_GROW x)
    (functype.mk_functype (list.mk_list [valtype_reftype rt, valtype.I32]) (list.mk_list [valtype.I32]))
    (Instr_ok.table_grow C x rt lim a a_1 a_2 a_3 a_4) := by
  intro C x rt lim Hlen Hlookup HWfC HWfinstr HWfTabType
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs3⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    obtain ⟨r1, Heqv1⟩ := invert_typeof_reftype' v1 rt Ht1
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 HP2
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    obtain ⟨r, Hunsigned⟩ := invsigned_total_32m1
    exact ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN r))],
      Step.table_grow_fail _ r1 n2 x r (by simpa using Hunsigned)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.table_fill` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4464`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_table_fill :
    ∀ (C : context) (x : idx) (rt : reftype) (lim : limits) (a : proj_uN_0 x < C.TABLES.length)
  (a_1 : C.TABLES[proj_uN_0 x]! = tabletype.mk_tabletype lim rt) (a_2 : wf_context C)
  (a_3 : wf_instr (_root_.instr.TABLE_FILL x)) (a_4 : wf_tabletype (tabletype.mk_tabletype lim rt)),
  t_progress_be_P C (_root_.instr.TABLE_FILL x)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype_reftype rt, valtype.I32]) (list.mk_list []))
    (Instr_ok.table_fill C x rt lim a a_1 a_2 a_3 a_4) := by
  intro C x rt lim Hlen Hlookup HWfC HWfinstr HWfTabType
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs4⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _, Ht3, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 HP1
    have HP3 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 HP3
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv3]
    by_cases Hs : n1 + n3 > (fun_table (state.mk_state s f) x).REFS.length
    · exact ⟨s, f, [admininstr.TRAP],
        Step.read _ _ _ (Step_read.table_fill_trap _ _ v2 n3 x (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs))⟩
    · cases n3 with
      | zero =>
        exact ⟨s, f, [], Step.read _ _ _ (Step_read.table_fill_zero _ _ v2 0 x (by simp [proj_num__0])
          (by simp [proj_num__0, proj_uN_0]; omega) rfl)⟩
      | succ n3 =>
        have H : Int.toNat (((n3 + 1 : Nat) : Int) - 1) = n3 := by omega
        refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)), admininstr_val v2,
          admininstr.TABLE_SET x, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (n1 + 1))),
          admininstr_val v2, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n3)),
          admininstr.TABLE_FILL x], ?_⟩
        have Hstep := Step_read.table_fill_succ (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
          v2 (n3 + 1) x (by simp [proj_num__0]) (by simp) (by simp [proj_num__0, proj_uN_0]; omega)
        rw [H] at Hstep
        exact Step.read _ _ _ Hstep
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.table_copy` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4511`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_table_copy :
    ∀ (C : context) (x_1 x_2 : idx) (lim_1 : limits) (rt : reftype) (lim_2 : limits)
  (a : proj_uN_0 x_1 < C.TABLES.length) (a_1 : C.TABLES[proj_uN_0 x_1]! = tabletype.mk_tabletype lim_1 rt)
  (a_2 : proj_uN_0 x_2 < C.TABLES.length) (a_3 : C.TABLES[proj_uN_0 x_2]! = tabletype.mk_tabletype lim_2 rt)
  (a_4 : wf_context C) (a_5 : wf_instr (_root_.instr.TABLE_COPY x_1 x_2))
  (a_6 : wf_tabletype (tabletype.mk_tabletype lim_1 rt)) (a_7 : wf_tabletype (tabletype.mk_tabletype lim_2 rt)),
  t_progress_be_P C (_root_.instr.TABLE_COPY x_1 x_2)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype.I32, valtype.I32]) (list.mk_list []))
    (Instr_ok.table_copy C x_1 x_2 lim_1 rt lim_2 a a_1 a_2 a_3 a_4 a_5 a_6 a_7) := by
  intro C x1 x2 lim1 rt lim2 Hlenx1 Hlookupx1 Hlenx2 Hlookupx2 HWfC HWfinstr HWfTabType1 HWfTabType2
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, Ht3, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    have HP3 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 HP1
    obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 HP2
    obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 HP3
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2, Heqv3]
    by_cases Hs : n2 + n3 > (fun_table (state.mk_state s f) x2).REFS.length ∨
        n1 + n3 > (fun_table (state.mk_state s f) x1).REFS.length
    · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.table_copy_trap (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
          (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)) n3 x1 x2 (by simp [proj_num__0]) (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs))⟩
    · have Hb : n2 + n3 ≤ (fun_table (state.mk_state s f) x2).REFS.length ∧
          n1 + n3 ≤ (fun_table (state.mk_state s f) x1).REFS.length := by omega
      by_cases Hz : n3 = 0
      · subst Hz
        exact ⟨s, f, [], Step.read _ _ _
          (Step_read.table_copy_zero (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
            (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)) 0 x1 x2 (by simp [proj_num__0]) (by simp [proj_num__0])
            (by simpa [proj_num__0, proj_uN_0] using Hb) rfl)⟩
      · by_cases Hle : n1 ≤ n2
        · exact ⟨s, f, _, Step.read _ _ _
            (Step_read.table_copy_le (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
              (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)) n3 x1 x2 (by simp [proj_num__0]) (by simp [proj_num__0])
              Hz (by simpa [proj_num__0, proj_uN_0] using Hb) (by simpa [proj_num__0, proj_uN_0] using Hle))⟩
        · exact ⟨s, f, _, Step.read _ _ _
            (Step_read.table_copy_gt (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
              (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)) n3 x1 x2 (by simp [proj_num__0]) (by simp [proj_num__0])
              (by simp only [proj_num__0, proj_uN_0, Option.get!_some]; omega) Hz
              (by simpa [proj_num__0, proj_uN_0] using Hb))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.table_init` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4605`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_table_init :
    ∀ (C : context) (x_1 x_2 : idx) (lim : limits) (rt : reftype) (a : proj_uN_0 x_1 < C.TABLES.length)
  (a_1 : C.TABLES[proj_uN_0 x_1]! = tabletype.mk_tabletype lim rt) (a_2 : proj_uN_0 x_2 < C.ELEMS.length)
  (a_3 : C.ELEMS[proj_uN_0 x_2]! = rt) (a_4 : wf_context C) (a_5 : wf_instr (_root_.instr.TABLE_INIT x_1 x_2))
  (a_6 : wf_tabletype (tabletype.mk_tabletype lim rt)),
  t_progress_be_P C (_root_.instr.TABLE_INIT x_1 x_2)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype.I32, valtype.I32]) (list.mk_list []))
    (Instr_ok.table_init C x_1 x_2 lim rt a a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro C x1 x2 lim1 rt Hlenx1 Hlookupx1 Hlenx2 Hlookupx2 HWfC HWfinstr HWfTabType
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  -- Rocq: `invert_typeof_vcs Hts HWfConfig HWfVals.` (vcs = [v1; v2; v3])
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs4⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, Ht3, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    have Hwf2 : wf_val v2 := HWfVals v2 (by simp)
    have Hwf3 : wf_val v3 := HWfVals v3 (by simp)
    -- Rocq: `eapply invert_typeof_I32 in Ht1/Ht2/Ht3 as [n_i Heqv_i]; eauto. rewrite Heqv_i.`
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 Hwf2
    obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 Hwf3
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2, Heqv3,
      admininstr_instr]
    -- Rocq: `case Hs: ((n2 + n3 >? |elem.REFS|) || (n1 + n3 >? |table.REFS|)).`
    by_cases Hs : (n2 + n3 > (fun_elem (state.mk_state s f) x2).REFS.length) ∨
        (n1 + n3 > (fun_table (state.mk_state s f) x1).REFS.length)
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply table_init_trap; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.table_init_trap _ _ _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs))⟩
    · -- Rocq: `destruct n3 using N.peano_ind.`
      rcases n3 with _ | n3
      · -- Rocq: `exists s, f, []. eapply read. eapply table_init_zero; eauto. ...`
        exact ⟨s, f, [], Step.read _ _ _
          (Step_read.table_init_zero _ _ _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega) rfl)⟩
      · -- Rocq: `exists s, f, [...]. eapply read. eapply table_init_succ; eauto. ...`
        exact ⟨s, f, _, Step.read _ _ _
          (Step_read.table_init_succ _ _ _ _ _ _
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega)
            (by simp [proj_num__0]) (by simp [proj_num__0]) (Nat.succ_ne_zero _)
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.elem_drop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4683`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_elem_drop :
    ∀ (C : context) (x : idx) (rt : reftype) (a : proj_uN_0 x < C.ELEMS.length)
  (a_1 : C.ELEMS[proj_uN_0 x]! = rt) (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.ELEM_DROP x)),
  t_progress_be_P C (_root_.instr.ELEM_DROP x) (functype.mk_functype (list.mk_list []) (list.mk_list []))
    (Instr_ok.elem_drop C x rt a a_1 a_2 a_3) := by
  intro C x rt Hlen Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs1⟩
  · -- Rocq: `case Estate: (with_elem (mk_state s f) x []) => [s' f']. exists s', f', [].
    --        rewrite -Estate. by apply: Step__elem_drop.`
    cases Estate : with_elem (state.mk_state s f) x [] with
    | mk_state s' f' =>
      refine ⟨s', f', [], ?_⟩
      rw [← Estate]
      exact Step.elem_drop _ x
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.memory_size` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4693`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_memory_size :
    ∀ (C : context) (mt : memtype) (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt) (a_2 : wf_context C)
  (a_3 : wf_memtype mt) (a_4 : wf_instr _root_.instr.MEMORY_SIZE),
  t_progress_be_P C _root_.instr.MEMORY_SIZE (functype.mk_functype (list.mk_list []) (list.mk_list [valtype.I32]))
    (Instr_ok.memory_size C mt a a_1 a_2 a_3 a_4) := by
  intro C mt Hlen Hlookup HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs⟩
  · -- Rocq: `addr := lookup_total (MEMS (frame_MODULE f)) 0` and `Haddr : addr < |meminst_lst|`
    have HeqC : C.MEMS = C'.MEMS := by subst Hcontext; rfl
    obtain ⟨_, _, Hmlen, _, _, _⟩ := Moduleinst_ok_lengths s f.MODULE C' Hmod
    have Hlen' : 0 < f.MODULE.MEMS.length := by rw [Hmlen, ← HeqC]; exact Hlen
    have Hinv := minst_invert_mems s f.MODULE C' C' Hmod ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨_, _, Haddr, _, _⟩ :=
      Hinv _ (mem_zip_getElem! f.MODULE.MEMS C'.MEMS 0 Hlen' (by rw [← Hmlen]; exact Hlen'))
    have Haddr' : f.MODULE.MEMS[0]! < s.MEMS.length := Haddr
    -- Rocq: `invert_storeok Hstore` and `Hmem : Meminst_ok s (lookup_total meminst_lst addr) ...`
    obtain ⟨_, mtl, _, _, _, _, _, _, Hml, HMem, _⟩ := Store_ok_parts s Hstore
    have Hmem : Meminst_ok s s.MEMS[f.MODULE.MEMS[0]!]! mtl[f.MODULE.MEMS[0]!]! :=
      HMem _ (mem_zip_getElem! s.MEMS mtl _ Haddr' (by rw [← Hml]; exact Haddr'))
    -- Rocq: `inversion Hmem`
    obtain ⟨v_n, _, bs, Hmi, _, Hbs, _, _⟩ := meminst_ok_raw s _ _ Hmem
    refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))],
      Step.read _ _ _ (Step_read.memory_size (state.mk_state s f) v_n ?_ ?_)⟩
    · simp only [fun_mem, proj_uN_0]
      rw [Hmi, Hbs, Nat.mul_assoc]
    · exact wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.memory_grow` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4745`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_memory_grow :
    ∀ (C : context) (mt : memtype) (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt) (a_2 : wf_context C)
  (a_3 : wf_memtype mt) (a_4 : wf_instr _root_.instr.MEMORY_GROW),
  t_progress_be_P C _root_.instr.MEMORY_GROW (functype.mk_functype (list.mk_list [valtype.I32]) (list.mk_list [valtype.I32]))
    (Instr_ok.memory_grow C mt a a_1 a_2 a_3 a_4) := by
  intro C mt Hlen Hlookup HWfC HWMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 HP1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    -- Rocq: `pose proof invsigned_total_32m1 as [r Hunsigned]` then `memory_grow_fail`
    obtain ⟨r, Hunsigned⟩ := invsigned_total_32m1
    exact ⟨s, f, _, Step.memory_grow_fail (state.mk_state s f) n1 r (by simpa using Hunsigned)⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.memory_fill` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4769`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_memory_fill :
    ∀ (C : context) (mt : memtype) (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt) (a_2 : wf_context C)
  (a_3 : wf_memtype mt) (a_4 : wf_instr _root_.instr.MEMORY_FILL),
  t_progress_be_P C _root_.instr.MEMORY_FILL
    (functype.mk_functype (list.mk_list [valtype.I32, valtype.I32, valtype.I32]) (list.mk_list []))
    (Instr_ok.memory_fill C mt a a_1 a_2 a_3 a_4) := by
  intro C mt Hlen Hlookup HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, Ht3, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP3 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 HP1
    obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 HP3
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv3]
    by_cases Hs : n1 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.memory_fill_trap (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)) v2 n3
          (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · by_cases Hz : n3 = 0
      · subst Hz
        exact ⟨s, f, [], Step.read _ _ _
          (Step_read.memory_fill_zero (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)) v2 0
            (by simp [proj_num__0]) (by simp only [proj_num__0, proj_uN_0, Option.get!_some]; omega) rfl)⟩
      · exact ⟨s, f, _, Step.read _ _ _
          (Step_read.memory_fill_succ (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)) v2 n3
            (by simp [proj_num__0]) Hz (by simp only [proj_num__0, proj_uN_0, Option.get!_some]; omega))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.memory_copy` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4820`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_memory_copy :
    ∀ (C : context) (mt : memtype) (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt) (a_2 : wf_context C)
  (a_3 : wf_memtype mt) (a_4 : wf_instr _root_.instr.MEMORY_COPY),
  t_progress_be_P C _root_.instr.MEMORY_COPY
    (functype.mk_functype (list.mk_list [valtype.I32, valtype.I32, valtype.I32]) (list.mk_list []))
    (Instr_ok.memory_copy C mt a a_1 a_2 a_3 a_4) := by
  intro C mt Hlen Hlookup HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  subst Htf1
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vs⟩⟩⟩⟩ <;>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
      List.nil_eq, and_true] at Hts
  obtain ⟨Ht1, Ht2, Ht3⟩ := Hts
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 (HWfVals v2 (by simp))
  obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 (HWfVals v3 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [Heqv1, Heqv2, Heqv3]
  show ∃ s' f' es', Step (config.mk_config (state.mk_state s f)
    [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)),
     admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)),
     admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n3)),
     admininstr.MEMORY_COPY]) (config.mk_config (state.mk_state s' f') es')
  by_cases Hs : n2 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length ∨
      n1 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
  · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
      (Step_read.memory_copy_trap _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
        (by simpa [proj_num__0, proj_uN_0] using Hs)
        (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
  · have HB : n2 + n3 ≤ (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length ∧
        n1 + n3 ≤ (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length := by
      omega
    by_cases H0 : n3 = 0
    · exact ⟨s, f, [], Step.read _ _ _
        (Step_read.memory_copy_zero _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using HB) H0)⟩
    · by_cases Hle : n1 ≤ n2
      · exact ⟨s, f, _, Step.read _ _ _
          (Step_read.memory_copy_le _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0]) H0
            (by simpa [proj_num__0, proj_uN_0] using HB)
            (by simpa [proj_num__0, proj_uN_0] using Hle))⟩
      · exact ⟨s, f, _, Step.read _ _ _
          (Step_read.memory_copy_gt _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
            (by simp only [proj_num__0, proj_uN_0, Option.get!_some]; omega) H0
            (by simpa [proj_num__0, proj_uN_0] using HB))⟩

/-- Lean-only (bundle20): the `Instr_ok.memory_init` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4917`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_memory_init :
    ∀ (C : context) (x : idx) (mt : memtype) (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt)
  (a_2 : proj_uN_0 x < C.DATAS.length) (a_3 : C.DATAS[proj_uN_0 x]! = datatype.OK) (a_4 : wf_context C)
  (a_5 : wf_memtype mt) (a_6 : wf_instr (_root_.instr.MEMORY_INIT x)),
  t_progress_be_P C (_root_.instr.MEMORY_INIT x)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype.I32, valtype.I32]) (list.mk_list []))
    (Instr_ok.memory_init C x mt a a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro C x mt Hlen Hlookup HRange HData HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  -- Rocq: `invert_typeof_vcs Hts HWfConfig HWfVals.` (vcs = [v1; v2; v3])
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs4⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, Ht3, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    have Hwf2 : wf_val v2 := HWfVals v2 (by simp)
    have Hwf3 : wf_val v3 := HWfVals v3 (by simp)
    -- Rocq: `eapply invert_typeof_I32 in Ht1/Ht2/Ht3 as [n_i Heqv_i]; eauto. rewrite Heqv_i.`
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 Hwf2
    obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 Hwf3
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2, Heqv3,
      admininstr_instr]
    -- Rocq: `case Hs: ((n2 + n3 >? |data.BYTES|) || (n1 + n3 >? |mem.BYTES|)).`
    by_cases Hs : (n2 + n3 > (fun_data (state.mk_state s f) x).BYTES.length) ∨
        (n1 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length)
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply memory_init_trap; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.memory_init_trap _ _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: `destruct n3 using N.peano_ind.`
      rcases n3 with _ | n3
      · -- Rocq: `exists s, f, []. eapply read. eapply memory_init_zero; eauto. ...`
        exact ⟨s, f, [], Step.read _ _ _
          (Step_read.memory_init_zero _ _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega) rfl)⟩
      · -- Rocq: `exists s, f, [...]. eapply read. eapply memory_init_succ; eauto. ...`
        exact ⟨s, f, _, Step.read _ _ _
          (Step_read.memory_init_succ _ _ _ _ _
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega)
            (by simp [proj_num__0]) (by simp [proj_num__0]) (Nat.succ_ne_zero _)
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega))⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.data_drop` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:4995`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_data_drop :
    ∀ (C : context) (x : idx) (a : proj_uN_0 x < C.DATAS.length)
  (a_1 : C.DATAS[proj_uN_0 x]! = datatype.OK) (a_2 : wf_context C) (a_3 : wf_instr (_root_.instr.DATA_DROP x)),
  t_progress_be_P C (_root_.instr.DATA_DROP x) (functype.mk_functype (list.mk_list []) (list.mk_list []))
    (Instr_ok.data_drop C x a a_1 a_2 a_3) := by
  intro C x HRange Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs1⟩
  · -- Rocq: `case Estate: (with_data (mk_state s f) x []) => [s' f']. exists s', f', [].
    --        rewrite -Estate. by eapply Step__data_drop.`
    cases Estate : with_data (state.mk_state s f) x [] with
    | mk_state s' f' =>
      refine ⟨s', f', [], ?_⟩
      rw [← Estate]
      exact Step.data_drop _ x
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.load_val` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5005`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_load_val :
    ∀ (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype) (a : 0 < C.MEMS.length)
  (a_1 : C.MEMS[0]! = mt) (a_2 : size (valtype_numtype nt) ≠ none)
  (a_3 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))
  (a_4 : wf_context C) (a_5 : wf_memtype mt) (a_6 : wf_instr (_root_.instr.LOAD nt none v_memarg)),
  t_progress_be_P C (_root_.instr.LOAD nt none v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32]) (list.mk_list [valtype_numtype nt]))
    (Instr_ok.load_val C nt v_memarg mt a a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro C nt memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + size/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET
        + rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply load_num_trap; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.load_num_trap _ _ _ _ (by simp [proj_num__0]) Hfunsize
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: in bounds, read the value back out of the byte slice (`load_num_val` with
      -- `c := inv_nbytes_ nt bs`; `nbytes_inv` + `list_slice_size`; `inv_nbytes__is_wf` +
      -- `Forall_list_slice` + `wf_config_mem_bytes`).
      have Hsz : ((rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)) : Nat) : Rat)
          = ((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat) := by
        cases nt <;> decide +kernel
      refine ⟨s, f, [admininstr.CONST nt (inv_nbytes_ nt
          (List.take (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))
            (List.drop (n1 + proj_uN_0 memarg.OFFSET)
              ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))))],
        Step.read _ _ _ (Step_read.load_num_val _ _ _ _ _ (by simp [proj_num__0]) Hfunsize ?_ ?_
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
      · -- Rocq: `apply/eqP; apply: nbytes_inv. apply: list_slice_size. ... by apply: Hs.`
        simp only [proj_num__0, Option.get!_some, proj_uN_0]
        apply nbytes_inv
        rw [list_slice_size _ _ _ (by simp only [proj_uN_0] at Hs ⊢; omega)]
        exact Hsz
      · -- Rocq: `eapply inv_nbytes__is_wf; last by apply: eqxx. apply: Forall_list_slice.
        --        by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).`
        exact inv_nbytes__is_wf nt _ _
          (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.load_pack` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5034`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_load_pack :
    ∀ (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (v_memarg : memarg) (mt : memtype)
  (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt) (a_2 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_M : Rat) / (8 : Rat))) (a_3 : wf_context C)
  (a_4 : wf_memtype mt)
  (a_5 :
    wf_instr
      (_root_.instr.LOAD (numtype_Inn v_Inn)
        (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_M) v_sx))) v_memarg)),
  t_progress_be_P C
    (_root_.instr.LOAD (numtype_Inn v_Inn)
      (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_M) v_sx))) v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32]) (list.mk_list [valtype_Inn v_Inn]))
    (Instr_ok.load_pack C v_Inn v_M v_sx v_memarg mt a a_1 a_2 a_3 a_4 a_5) := by
  intro C v_Inn v_M v_sx memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + M/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat ((v_M : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply load_pack_trap; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.load_pack_trap _ _ _ _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: in bounds, read the value back out of the byte slice (`load_pack_val` with
      -- `c := inv_ibytes_ M bs`; `ibytes_inv` + `list_slice_size`; `inv_ibytes__is_wf` +
      -- `Forall_list_slice` + `wf_config_mem_bytes`).
      refine ⟨s, f, [admininstr.CONST (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn
          (extend__ v_M (Option.get! (size (valtype_Inn v_Inn))) v_sx
            (inv_ibytes_ v_M (List.take (rat_to_nat ((v_M : Rat) / (8 : Rat)))
              (List.drop (n1 + proj_uN_0 memarg.OFFSET)
                ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))))))],
        Step.read _ _ _ (Step_read.load_pack_val _ _ _ _ _ _ _ ?_ (by simp [proj_num__0]) ?_ ?_
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
      · -- Rocq: `1: by destruct v_Inn.`
        cases v_Inn <;> simp [valtype_Inn, size]
      · -- Rocq: `apply/eqP; apply: ibytes_inv. apply: list_slice_size. ... by apply: Hs.`
        simp only [proj_num__0, Option.get!_some, proj_uN_0]
        apply ibytes_inv
        exact list_slice_size _ _ _ (by simp only [proj_uN_0] at Hs ⊢; omega)
      · -- Rocq: `eapply inv_ibytes__is_wf; last by apply: eqxx. apply: Forall_list_slice.
        --        by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).`
        exact inv_ibytes__is_wf _ _ _
          (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.store_val` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5061`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_store_val :
    ∀ (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype) (a : 0 < C.MEMS.length)
  (a_1 : C.MEMS[0]! = mt) (a_2 : size (valtype_numtype nt) ≠ none)
  (a_3 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))
  (a_4 : wf_context C) (a_5 : wf_memtype mt) (a_6 : wf_instr (_root_.instr.STORE nt none v_memarg)),
  t_progress_be_P C (_root_.instr.STORE nt none v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype_numtype nt]) (list.mk_list []))
    (Instr_ok.store_val C nt v_memarg mt a a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro C nt memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs3⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    --        rewrite Heqv1. eapply invert_typeof_numtype in Ht2 as [n2 Heqv2]; eauto. rewrite Heqv2.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    obtain ⟨n2, Heqv2⟩ := invert_typeof_numtype v2 nt Ht2
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + size/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET
        + rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. by eapply store_num_trap; eauto.`
      exact ⟨s, f, [admininstr.TRAP],
        Step.store_num_trap _ _ _ _ _ (by simp [proj_num__0]) Hfunsize
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩)⟩
    · -- Rocq: `do 3 eexists. eapply (store_num_val (mk_state s f)); eauto.`
      exact ⟨_, _, _, Step.store_num_val (state.mk_state s f) _ _ _ _ _
        (by simp [proj_num__0]) Hfunsize rfl⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.store_pack` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5081`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_store_pack :
    ∀ (C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (mt : memtype) (a : 0 < C.MEMS.length)
  (a_1 : C.MEMS[0]! = mt) (a_2 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_M : Rat) / (8 : Rat))) (a_3 : wf_context C) (a_4 : wf_memtype mt)
  (a_5 : wf_instr (_root_.instr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_M)) v_memarg)),
  t_progress_be_P C (_root_.instr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_M)) v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype_Inn v_Inn]) (list.mk_list []))
    (Instr_ok.store_pack C v_Inn v_M v_memarg mt a a_1 a_2 a_3 a_4 a_5) := by
  intro C v_Inn v_M memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs3⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    have Hwf2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + M/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat ((v_M : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. destruct Inn.` then per `Inn`:
      -- `eapply invert_typeof_I32/I64 in Ht2 as [n2 Heqv2]; eauto. rewrite H in Heqv2.
      --  rewrite Heqv2. eapply store_pack_trap; eauto. econstructor; eauto.`
      refine ⟨s, f, [admininstr.TRAP], ?_⟩
      cases v_Inn
      · obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 Hwf2
        rw [Heqv2]
        exact Step.store_pack_trap _ _ Inn.I32 _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩)
      · obtain ⟨n2, Heqv2⟩ := invert_typeof_I64 v2 Ht2 Hwf2
        rw [Heqv2]
        exact Step.store_pack_trap _ _ Inn.I64 _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩)
    -- Rocq: `destruct Inn.` then per `Inn`: invert `Ht2`, `do 3 eexists.
    -- eapply (store_pack_val (mk_state s f)); eauto.`
    cases v_Inn
    · obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 Hwf2
      rw [Heqv2]
      exact ⟨_, _, _, Step.store_pack_val (state.mk_state s f) _ Inn.I32 _ _ _ _
        (by simp [proj_num__0]) (by simp [valtype_Inn, size]) (by simp [proj_num__0]) rfl⟩
    · obtain ⟨n2, Heqv2⟩ := invert_typeof_I64 v2 Ht2 Hwf2
      rw [Heqv2]
      exact ⟨_, _, _, Step.store_pack_val (state.mk_state s f) _ Inn.I64 _ _ _ _
        (by simp [proj_num__0]) (by simp [valtype_Inn, size]) (by simp [proj_num__0]) rfl⟩
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vload_val` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5132`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vload_val :
    ∀ (C : context) (v_memarg : memarg) (mt : memtype) (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt)
  (a_2 : size valtype.V128 ≠ none)
  (a_3 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))
  (a_4 : wf_context C) (a_5 : wf_memtype mt) (a_6 : wf_instr (_root_.instr.VLOAD vectype.V128 none v_memarg)),
  t_progress_be_P C (_root_.instr.VLOAD vectype.V128 none v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32]) (list.mk_list [valtype.V128]))
    (Instr_ok.vload_val C v_memarg mt a a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro C memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + size V128/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET
        + rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply vload_oob; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.vload_oob _ _ _ (by simp [proj_num__0]) Hfunsize
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: in bounds, read the value back out of the byte slice (`Step_read__vload_val` with
      -- `c := inv_vbytes_ V128 bs`; `vbytes_inv` + `list_slice_size`; `inv_vbytes__is_wf` +
      -- `Forall_list_slice` + `wf_config_mem_bytes`).
      refine ⟨s, f, [admininstr.VCONST vectype.V128 (inv_vbytes_ vectype.V128
          (List.take (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))
            (List.drop (n1 + proj_uN_0 memarg.OFFSET)
              ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))))],
        Step.read _ _ _ (Step_read.vload_val _ _ _ _ (by simp [proj_num__0]) Hfunsize ?_ ?_
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
      · -- Rocq: `apply/eqP; apply: vbytes_inv. apply: list_slice_size. ... by apply: Hs.`
        simp only [proj_num__0, Option.get!_some, proj_uN_0]
        apply vbytes_inv
        rw [list_slice_size _ _ _ (by simp only [proj_uN_0] at Hs ⊢; omega)]
        decide +kernel
      · -- Rocq: `eapply (inv_vbytes__is_wf V128); [ | by apply: eqxx | by [] ].
        --        apply: Forall_list_slice. by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).`
        exact inv_vbytes__is_wf vectype.V128 _ _
          (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl Hfunsize
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vload_pack` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5161`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vload_pack :
    ∀ (C : context) (v_M : M) (v_N : N) (v_sx : sx) (v_memarg : memarg) (mt : memtype)
  (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt) (a_2 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((v_M : Rat) / (8 : Rat)) * (v_N : Rat)))
  (a_3 : wf_context C) (a_4 : wf_memtype mt)
  (a_5 : wf_instr (_root_.instr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx)) v_memarg)),
  t_progress_be_P C (_root_.instr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx)) v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32]) (list.mk_list [valtype.V128]))
    (Instr_ok.vload_pack C v_M v_N v_sx v_memarg mt a a_1 a_2 a_3 a_4 a_5) := by
  intro C v_M v_N v_sx memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + (v_M * v_N) / 8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (((v_M * v_N) : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply vload_shape_oob; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.vload_shape_oob _ _ _ _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: `have Hbnd : n1 + OFFSET + (v_M * v_N) / 8 <= |mem.BYTES|`.
      have Hbnd : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (((v_M * v_N) : Rat) / (8 : Rat))
          ≤ (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length := Nat.le_of_not_gt Hs
      -- Rocq: `have Hwv : wf_vloadop_ V128 (SHAPEX_ (mk_sz v_M) v_N v_sx)` (inversion HWfinstr).
      have Hwv : wf_vloadop_ vectype.V128 (vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx) := by
        cases HWfinstr
        rename_i Hv _
        exact Hv _ (by simp)
      -- Rocq: `inversion Hwv as [? ? ? ? Hsz HMN | | ]; subst.` and `HMN' : v_M * v_N = 64`.
      cases Hwv
      rename_i Hsz HMN
      have HMN' : @Eq Nat (v_M * v_N) 64 := by
        simp only [proj_sz_0, vsize] at HMN
        have h : (v_M : Rat) * (v_N : Rat) = ((64 : Nat) : Rat) := by rw [HMN]; norm_num
        exact_mod_cast h
      -- Rocq: `have Hcases : v_M = 8 \/ v_M = 16 \/ v_M = 32 \/ v_M = 64` (inversion Hsz).
      have Hcases : v_M = 8 ∨ v_M = 16 ∨ v_M = 32 ∨ v_M = 64 := by
        cases Hsz
        rename_i H
        simpa [or_assoc] using H
      -- Rocq: `pose J := fun k => inv_ibytes_ v_M (list_slice BYTES (n1 + OFFSET + k * v_M / 8)
      -- (v_M / 8))` and `HJ : forall k, wf_uN v_M (J k)`.
      have HJ : ∀ k : Nat, wf_uN v_M (inv_ibytes_ v_M (List.take (rat_to_nat ((v_M : Rat) / (8 : Rat)))
          (List.drop (n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (((k * v_M) : Rat) / (8 : Rat)))
            (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))) := fun k =>
        inv_ibytes__is_wf _ _ _ (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl
      -- Rocq: `case: Hcases => [E | [E | [E | E]]]; subst v_M. 4: { admit }.` In the three good
      -- cases (`v_M` = 8/16/32, so `v_N` = 8/4/2) the lanes widen to `Jnn` = I16/I32/I64; they
      -- share the `vload_shape_val` step below, parametrised by `q = v_M / 8` and that `Jnn`.
      obtain E | ⟨q, Jn, Hq, HJn, Hshape⟩ : v_M = 64 ∨ ∃ (q : Nat) (Jn : Jnn), v_M = 8 * q ∧
          jsize Jn = v_M * 2 ∧ wf_shape (shape.X (lanetype_Jnn Jn) (dim.mk_dim v_N)) := by
        rcases Hcases with E | E | E | E
        · subst E
          obtain rfl : @Eq Nat v_N 8 := by omega
          exact Or.inr ⟨1, Jnn.I16, rfl, rfl,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · subst E
          obtain rfl : @Eq Nat v_N 4 := by omega
          exact Or.inr ⟨2, Jnn.I32, rfl, rfl,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · subst E
          obtain rfl : @Eq Nat v_N 2 := by omega
          exact Or.inr ⟨4, Jnn.I64, rfl, rfl,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · exact Or.inl E
      · -- FALSE subcase as the spec stands (Rocq: admit at type_progress.v:5208); see vload_shape64_stuck.
        sorry
      · -- Rocq: `eapply (vload_shape_val (mk_state s f) _ _ _ _ _ _ (mkseqN J N) Jnn)`.
        -- the byte offsets/sizes are whole numbers, since `v_M = 8 * q`
        have HkM : ∀ k : Nat, rat_to_nat (((k * v_M) : Rat) / (8 : Rat)) = k * q := by
          intro k
          rw [show ((k : Rat) * (v_M : Rat)) / (8 : Rat) = ((k * q : Nat) : Rat) by
            rw [Hq]; push_cast; ring]
          exact rat_to_nat_natCast _
        have HM : rat_to_nat ((v_M : Rat) / (8 : Rat)) = q := by
          rw [show (v_M : Rat) / (8 : Rat) = ((q : Nat) : Rat) by rw [Hq]; push_cast; ring]
          exact rat_to_nat_natCast _
        have HMN8 : rat_to_nat (((v_M * v_N) : Rat) / (8 : Rat)) = v_N * q := by
          rw [show ((v_M : Rat) * (v_N : Rat)) / (8 : Rat) = ((v_N * q : Nat) : Rat) by
            rw [Hq]; push_cast; ring]
          exact rat_to_nat_natCast _
        have zip_map_self : ∀ {β : Type} (g : Nat → β) (l : List Nat),
            List.zip l (List.map g l) = List.map (fun k => (k, g k)) l := by
          intro β g l
          induction l with
          | nil => rfl
          | cons a l ih => simp [ih]
        refine ⟨s, f, _, Step.read _ _ _ (Step_read.vload_shape_val _ _ _ _ _ _ _
          ((List.range v_N).map (fun (k : Nat) => inv_ibytes_ v_M (List.take (rat_to_nat ((v_M : Rat) / (8 : Rat)))
            (List.drop (n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (((k * v_M) : Rat) / (8 : Rat)))
              (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))))
          Jn ?_ ?_ HJn rfl (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩) Hshape ?_ (by simp))⟩
        · -- the address is an `i32` (one premise per lane)
          intro k _
          simp [proj_num__0]
        · -- Rocq: `apply/eqP; apply: ibytes_inv; apply: list_slice_size; apply: (Hsl ... Hbnd)`.
          intro p hp
          rw [zip_map_self] at hp
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
          rw [List.mem_range] at hk
          simp only [proj_num__0, Option.get!_some]
          rw [show proj_uN_0 (uN.mk_uN n1) = n1 from rfl]
          apply ibytes_inv
          apply list_slice_size
          rw [HkM, HM]
          rw [HMN8] at Hbnd
          have h1 : (k + 1) * q ≤ v_N * q := Nat.mul_le_mul_right q hk
          rw [Nat.add_mul, Nat.one_mul] at h1
          omega
        · -- Rocq: `eapply lane__case_0; [ (eapply extend___is_wf; last by apply: eqxx); apply: HJ | by [] ]`.
          intro x hx
          obtain ⟨k, _, rfl⟩ := List.mem_map.1 hx
          exact wf_lane_.lane__case_0 _ _ _ (extend___is_wf _ _ _ _ _ (HJ k) rfl) rfl
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vload_splat` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5228`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vload_splat :
    ∀ (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype) (a : 0 < C.MEMS.length)
  (a_1 : C.MEMS[0]! = mt) (a_2 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_n : Rat) / (8 : Rat))) (a_3 : wf_context C) (a_4 : wf_memtype mt)
  (a_5 : wf_instr (_root_.instr.VLOAD vectype.V128 (some (vloadop_.SPLAT (sz.mk_sz v_n))) v_memarg)),
  t_progress_be_P C (_root_.instr.VLOAD vectype.V128 (some (vloadop_.SPLAT (sz.mk_sz v_n))) v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32]) (list.mk_list [valtype.V128]))
    (Instr_ok.vload_splat C v_n v_memarg mt a a_1 a_2 a_3 a_4 a_5) := by
  intro C v_n memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + v_n / 8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat ((v_n : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply vload_splat_oob; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.vload_splat_oob _ _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: `have Hbnd : n1 + OFFSET + v_n / 8 <= |mem.BYTES|`.
      have Hbnd : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat ((v_n : Rat) / (8 : Rat))
          ≤ (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length := Nat.le_of_not_gt Hs
      -- Rocq: `have Hwfk : wf_uN v_n (inv_ibytes_ v_n (list_slice BYTES (n1 + OFFSET) (v_n / 8)))`.
      have Hwfk : wf_uN v_n (inv_ibytes_ v_n (List.take (rat_to_nat ((v_n : Rat) / (8 : Rat)))
          (List.drop (n1 + proj_uN_0 memarg.OFFSET) (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))) :=
        inv_ibytes__is_wf _ _ _ (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl
      -- Rocq: `have Hsz : wf_sz (mk_sz v_n)` (inversion HWfinstr, then of `wf_vloadop_`).
      have Hsz : wf_sz (sz.mk_sz v_n) := by
        cases HWfinstr
        rename_i Hv _
        have Hv' : wf_vloadop_ vectype.V128 (vloadop_.SPLAT (sz.mk_sz v_n)) := Hv _ (by simp)
        cases Hv'
        assumption
      -- Rocq: `have Hcases : v_n = 8 \/ v_n = 16 \/ v_n = 32 \/ v_n = 64` (inversion Hsz).
      have Hcases : v_n = 8 ∨ v_n = 16 ∨ v_n = 32 ∨ v_n = 64 := by
        cases Hsz
        rename_i H
        simpa [or_assoc] using H
      -- Rocq: `case: Hcases => [E | [E | [E | E]]]; subst v_n; ... eapply (vload_splat_val ... Jnn M)`
      -- with (`Jnn`, `M`) = (I8, 16) / (I16, 8) / (I32, 4) / (I64, 2); the four cases share the step.
      obtain ⟨Jn, vM, HJn, HvM, Hshape⟩ : ∃ (Jn : Jnn) (vM : Nat), v_n = jsize Jn ∧
          (vM : Rat) = (128 : Rat) / (v_n : Rat) ∧ wf_shape (shape.X (lanetype_Jnn Jn) (dim.mk_dim vM)) := by
        rcases Hcases with E | E | E | E <;> subst E
        · exact ⟨Jnn.I8, 16, rfl, by norm_num,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · exact ⟨Jnn.I16, 8, rfl, by norm_num,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · exact ⟨Jnn.I32, 4, rfl, by norm_num,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · exact ⟨Jnn.I64, 2, rfl, by norm_num,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
      subst HJn
      refine ⟨s, f, _, Step.read _ _ _ (Step_read.vload_splat_val _ _ _ _ _
        (inv_ibytes_ (jsize Jn) (List.take (rat_to_nat (((jsize Jn) : Rat) / (8 : Rat)))
          (List.drop (n1 + proj_uN_0 memarg.OFFSET) (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES)))
        Jn vM (by simp [proj_num__0]) ?_ rfl HvM rfl (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩)
        Hshape ?_)⟩
      · -- Rocq: `apply/eqP; apply: ibytes_inv; apply: list_slice_size; by apply: Hbnd`.
        simp only [proj_num__0, Option.get!_some]
        rw [show proj_uN_0 (uN.mk_uN n1) = n1 from rfl]
        apply ibytes_inv
        exact list_slice_size _ _ _ Hbnd
      · -- Rocq: `eapply lane__case_0; [ by rewrite mk_uN_eta; apply: Hwfk | by [] ]`.
        have mk_uN_eta : ∀ u : uN, uN.mk_uN (proj_uN_0 u) = u := fun u => by cases u; rfl
        rw [mk_uN_eta]
        exact wf_lane_.lane__case_0 _ _ _ Hwfk rfl
  · simp at Hts

/-- Lean-only (bundle20): the `Instr_ok.vload_zero` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5277`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vload_zero :
    ∀ (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype) (a : 0 < C.MEMS.length)
  (a_1 : C.MEMS[0]! = mt) (a_2 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_n : Rat) / (8 : Rat))) (a_3 : wf_context C) (a_4 : wf_memtype mt)
  (a_5 : wf_instr (_root_.instr.VLOAD vectype.V128 (some (vloadop_.ZERO (sz.mk_sz v_n))) v_memarg)),
  t_progress_be_P C (_root_.instr.VLOAD vectype.V128 (some (vloadop_.ZERO (sz.mk_sz v_n))) v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32]) (list.mk_list [valtype.V128]))
    (Instr_ok.vload_zero C v_n v_memarg mt a a_1 a_2 a_3 a_4 a_5) := by
  intro C v_n v_memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨rfl, rfl⟩ := Htf
  obtain ⟨v1, rfl, Ht1⟩ := List.map_eq_singleton_iff.mp Hts
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
  have Hwf0 : wf_uN 32 (uN.mk_uN 0) := wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
  by_cases Hs : n1 + proj_uN_0 v_memarg.OFFSET + rat_to_nat ((v_n : Rat) / 8)
      > ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length
  · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
      (Step_read.vload_zero_oob _ _ _ _ (by simp [proj_num__0]) Hs Hwf0)⟩
  · have Hbnd : n1 + proj_uN_0 v_memarg.OFFSET + rat_to_nat ((v_n : Rat) / 8)
        ≤ ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length := Nat.le_of_not_lt Hs
    exact ⟨s, f, _, Step.read _ _ _
      (Step_read.vload_zero_val _ _ _ _ _ _ (by simp [proj_num__0])
        (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl
        (inv_ibytes__is_wf _ _ _
          (Forall_list_slice _ _ _ _ (wf_config_mem_bytes s f _ (uN.mk_uN 0) HWfConfig)) rfl)
        Hwf0)⟩

/-- Lean-only (bundle20): the `Instr_ok.vload_lane` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5304`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vload_lane :
    ∀ (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype)
  (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt) (a_2 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_n : Rat) / (8 : Rat)))
  (a_3 : ((proj_uN_0 v_laneidx) : Rat) < ((128 : Rat) / (v_n : Rat))) (a_4 : wf_context C) (a_5 : wf_memtype mt)
  (a_6 : wf_instr (_root_.instr.VLOAD_LANE vectype.V128 (sz.mk_sz v_n) v_memarg v_laneidx)),
  t_progress_be_P C (_root_.instr.VLOAD_LANE vectype.V128 (sz.mk_sz v_n) v_memarg v_laneidx)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype.V128]) (list.mk_list [valtype.V128]))
    (Instr_ok.vload_lane C v_n v_memarg v_laneidx mt a a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro C v_n v_memarg v_laneidx mt Hlen Hlookup HLim Hidx HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨rfl, rfl⟩ := Htf
  obtain ⟨v1, l1, rfl, Ht1, Hts'⟩ := List.map_eq_cons_iff.mp Hts
  obtain ⟨v2, rfl, Ht2⟩ := List.map_eq_singleton_iff.mp Hts'
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  obtain ⟨c1, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 (HWfVals v2 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
  have Hwf0 : wf_uN 32 (uN.mk_uN 0) := wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
  by_cases Hs : n1 + proj_uN_0 v_memarg.OFFSET + rat_to_nat ((v_n : Rat) / 8)
      > ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length
  · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
      (Step_read.vload_lane_oob _ _ _ _ _ _ (by simp [proj_num__0]) Hs Hwf0)⟩
  · have Hbnd : n1 + proj_uN_0 v_memarg.OFFSET + rat_to_nat ((v_n : Rat) / 8)
        ≤ ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length := Nat.le_of_not_lt Hs
    have Hwfk : wf_uN v_n (inv_ibytes_ v_n (List.take (rat_to_nat ((v_n : Rat) / 8))
        (List.drop (n1 + proj_uN_0 v_memarg.OFFSET)
          ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES)))) :=
      inv_ibytes__is_wf _ _ _
        (Forall_list_slice _ _ _ _ (wf_config_mem_bytes s f _ (uN.mk_uN 0) HWfConfig)) rfl
    have Heta : ∀ x : uN, uN.mk_uN (proj_uN_0 x) = x := fun x => by cases x; rfl
    have Hsz : wf_sz (sz.mk_sz v_n) := by cases HWfinstr; assumption
    have Hcases : v_n = 8 ∨ v_n = 16 ∨ v_n = 32 ∨ v_n = 64 := by
      cases Hsz with
      | sz_case_0 _ h =>
        rcases h with ((h | h) | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    rcases Hcases with E | E | E | E <;> subst E
    · exact ⟨s, f, _, Step.read _ _ _
        (Step_read.vload_lane_val _ _ _ _ _ _ _ _ Jnn.I8 16 (by simp [proj_num__0])
          (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl (by norm_num) rfl Hwf0
          (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
          (wf_lane_.lane__case_0 _ _ _ (by rw [Heta]; exact Hwfk) rfl))⟩
    · exact ⟨s, f, _, Step.read _ _ _
        (Step_read.vload_lane_val _ _ _ _ _ _ _ _ Jnn.I16 8 (by simp [proj_num__0])
          (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl (by norm_num) rfl Hwf0
          (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
          (wf_lane_.lane__case_0 _ _ _ (by rw [Heta]; exact Hwfk) rfl))⟩
    · exact ⟨s, f, _, Step.read _ _ _
        (Step_read.vload_lane_val _ _ _ _ _ _ _ _ Jnn.I32 4 (by simp [proj_num__0])
          (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl (by norm_num) rfl Hwf0
          (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
          (wf_lane_.lane__case_0 _ _ _ (by rw [Heta]; exact Hwfk) rfl))⟩
    · exact ⟨s, f, _, Step.read _ _ _
        (Step_read.vload_lane_val _ _ _ _ _ _ _ _ Jnn.I64 2 (by simp [proj_num__0])
          (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl (by norm_num) rfl Hwf0
          (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
          (wf_lane_.lane__case_0 _ _ _ (by rw [Heta]; exact Hwfk) rfl))⟩

/-- Lean-only (bundle20): the `Instr_ok.vstore` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5348`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vstore :
    ∀ (C : context) (v_memarg : memarg) (mt : memtype) (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt)
  (a_2 : size valtype.V128 ≠ none)
  (a_3 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))
  (a_4 : wf_context C) (a_5 : wf_memtype mt) (a_6 : wf_instr (_root_.instr.VSTORE vectype.V128 v_memarg)),
  t_progress_be_P C (_root_.instr.VSTORE vectype.V128 v_memarg)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype.V128]) (list.mk_list []))
    (Instr_ok.vstore C v_memarg mt a a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro C v_memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨rfl, rfl⟩ := Htf
  obtain ⟨v1, l1, rfl, Ht1, Hts'⟩ := List.map_eq_cons_iff.mp Hts
  obtain ⟨v2, rfl, Ht2⟩ := List.map_eq_singleton_iff.mp Hts'
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 (HWfVals v2 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
  exact ⟨_, _, _, Step.vstore_val _ _ _ _ _ (by simp [proj_num__0]) Hfunsize rfl⟩

/-- Lean-only (bundle20): the `Instr_ok.vstore_lane` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5363`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_vstore_lane :
    ∀ (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype)
  (a : 0 < C.MEMS.length) (a_1 : C.MEMS[0]! = mt) (a_2 : ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_n : Rat) / (8 : Rat)))
  (a_3 : ((proj_uN_0 v_laneidx) : Rat) < ((128 : Rat) / (v_n : Rat))) (a_4 : wf_context C) (a_5 : wf_memtype mt)
  (a_6 : wf_instr (_root_.instr.VSTORE_LANE vectype.V128 (sz.mk_sz v_n) v_memarg v_laneidx)),
  t_progress_be_P C (_root_.instr.VSTORE_LANE vectype.V128 (sz.mk_sz v_n) v_memarg v_laneidx)
    (functype.mk_functype (list.mk_list [valtype.I32, valtype.V128]) (list.mk_list []))
    (Instr_ok.vstore_lane C v_n v_memarg v_laneidx mt a a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro C v_n v_memarg v_laneidx mt Hlen Hlookup HLim Hidx HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨rfl, rfl⟩ := Htf
  obtain ⟨v1, l1, rfl, Ht1, Hts'⟩ := List.map_eq_cons_iff.mp Hts
  obtain ⟨v2, rfl, Ht2⟩ := List.map_eq_singleton_iff.mp Hts'
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  obtain ⟨c1, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 (HWfVals v2 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
  have Hwf0 : wf_uN 32 (uN.mk_uN 0) := wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
  by_cases Hs : n1 + proj_uN_0 v_memarg.OFFSET + v_n
      > ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length
  · exact ⟨s, f, [admininstr.TRAP],
      Step.vstore_lane_oob _ _ _ _ _ _ (by simp [proj_num__0]) Hs Hwf0⟩
  · have Hsz : wf_sz (sz.mk_sz v_n) := by cases HWfinstr; assumption
    have Hcases : v_n = 8 ∨ v_n = 16 ∨ v_n = 32 ∨ v_n = 64 := by
      cases Hsz with
      | sz_case_0 _ h =>
        rcases h with ((h | h) | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    have Hwf128 : wf_uN 128 c1 := Hwf2
    rcases Hcases with E | E | E | E <;> subst E
    · exact vstore_lane_progress s f n1 v_memarg v_laneidx c1 Jnn.I8 16 Hwf128
        (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
        (by have h := Hidx; norm_num at h; exact_mod_cast h) (show ((16 : ℕ) : Rat) = 128 / ((8 : ℕ) : Rat) by norm_num)
    · exact vstore_lane_progress s f n1 v_memarg v_laneidx c1 Jnn.I16 8 Hwf128
        (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
        (by have h := Hidx; norm_num at h; exact_mod_cast h) (show ((8 : ℕ) : Rat) = 128 / ((16 : ℕ) : Rat) by norm_num)
    · exact vstore_lane_progress s f n1 v_memarg v_laneidx c1 Jnn.I32 4 Hwf128
        (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
        (by have h := Hidx; norm_num at h; exact_mod_cast h) (show ((4 : ℕ) : Rat) = 128 / ((32 : ℕ) : Rat) by norm_num)
    · exact vstore_lane_progress s f n1 v_memarg v_laneidx c1 Jnn.I64 2 Hwf128
        (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
        (by have h := Hidx; norm_num at h; omega) (show ((2 : ℕ) : Rat) = 128 / ((64 : ℕ) : Rat) by norm_num)

/-- Lean-only (bundle20): the `Instrs_ok.empty` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5394`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_empty :
    ∀ (C : context) (a : wf_context C),
  t_progress_be_P0 C [] (functype.mk_functype (list.mk_list []) (list.mk_list [])) (Instrs_ok.empty C a) := by
  intro C a
  unfold t_progress_be_P0
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  left
  rfl

/-- Lean-only (bundle20): the `Instrs_ok.instr` case of Rocq's `t_progress_be` proof (no separate Rocq bullet (handled by the surrounding `Instrs_ok_ind'` automation / a shared bullet)),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_instr :
    ∀ (C : context) (v_instr : _root_.instr) (t_1_lst t_2_lst : List valtype)
  (a : Instr_ok C v_instr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))) (a_1 : wf_context C)
  (a_2 : wf_instr v_instr),
  t_progress_be_P C v_instr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_be_P0 C [v_instr] (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
      (Instrs_ok.instr C v_instr t_1_lst t_2_lst a a_1 a_2) := by
  intro C v_instr t_1_lst t_2_lst a a_1 a_2 ih
  exact ih

/-- Lean-only (bundle20): the `Instrs_ok.seq` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5399`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_seq :
    ∀ (C : context) (instr_1_lst instr_2_lst : List _root_.instr) (t_1_lst t_3_lst t_2_lst : List valtype)
  (a : Instrs_ok C instr_1_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : Instrs_ok C instr_2_lst (functype.mk_functype (list.mk_list t_2_lst) (list.mk_list t_3_lst)))
  (a_2 : wf_context C) (a_3 : Forall (fun (instr_1_elem : _root_.instr) => wf_instr instr_1_elem) instr_1_lst)
  (a_4 : Forall (fun (instr_2_elem : _root_.instr) => wf_instr instr_2_elem) instr_2_lst),
  t_progress_be_P0 C instr_1_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_be_P0 C instr_2_lst (functype.mk_functype (list.mk_list t_2_lst) (list.mk_list t_3_lst)) a_1 →
      t_progress_be_P0 C (instr_1_lst ++ instr_2_lst) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_3_lst))
        (Instrs_ok.seq C instr_1_lst instr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4) := by
  intro C instr_1_lst instr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 ih1 ih2
  unfold t_progress_be_P0 at ih1 ih2 ⊢
  intro s f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  rw [← e1] at hts
  rw [List.map_append] at hnotbr hnotret hwf ⊢
  by_cases hconst : const_list (List.map admininstr_instr instr_1_lst) = true
  · -- Rocq: the first sequence is all values; continue with the second one
    obtain ⟨vs1, hvs1⟩ := const_es_exists _ hconst
    have hadmin1 : Instrs_ok2 s C (List.map admininstr_instr instr_1_lst) (mkFunctype t_1_lst t_2_lst) :=
      construct_instrs_from_ais s C instr_1_lst t_1_lst t_2_lst (by cases hstore; assumption) a
    rw [hvs1] at hadmin1
    obtain ⟨vts, hsub, hvok⟩ := ais_vals_typing_inversion s C vs1 t_1_lst t_2_lst hadmin1
    obtain ⟨ts_sub, ts0, ts11_sub, ts12_sup, h1, h2, hs0, hs1, hs2⟩ := hsub
    have e11 : ts11_sub = [] := resulttype_sub_empty _ hs1
    rw [e11, List.append_nil] at h1
    have hnb0 : Forall (fun t => t ≠ valtype.BOT) ts_sub := by
      rw [← h1]; exact typeof_vals_non_bot vcs t_1_lst hts
    have e0 : ts_sub = ts0 := resulttype_sub_non_bot _ _ hnb0 hs0
    have e2 : vts = ts12_sup := resulttype_sub_non_bot _ _ (Vals_ok_non_bot _ _ _ hvok) hs2
    obtain ⟨hvlen, hvf⟩ := hvok
    have hmapvs1 : List.map typeof vs1 = vts := Forall2_Val_ok_is_same_as_map s vts vs1 hvf hvlen
    have heqts2 : List.map typeof (vcs ++ vs1) = t_2_lst := by
      rw [List.map_append, hmapvs1, hts, h2, ← e0, ← h1, e2]
    have hnotbr2 := not_lf_br_left _ _ hconst hnotbr
    have hnotret2 := not_lf_return_left _ _ hconst hnotret
    rw [hvs1, ← List.append_assoc, ← List.map_append] at hwf
    have hwfvs1 : Forall (fun v => wf_val v) vs1 := by
      have h := wf_forall_admin _ a_3
      rw [hvs1] at h
      exact (wf_forall_admin_val vs1).mpr h
    have hwfv' : Forall (fun e => wf_val e) (vcs ++ vs1) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hwfv x hx
      · exact hwfvs1 x hx
    rcases ih2 s f C' (vcs ++ vs1) t_2_lst t_3_lst lab ret hwf hwfv' rfl hctx hmod heqts2 hstore hnotbr2
        hnotret2 with hconst2 | ⟨s', f', es', hstep⟩
    · left
      exact const_list_concat _ _ hconst hconst2
    · right
      refine ⟨s', f', es', ?_⟩
      rw [hvs1, ← List.append_assoc, ← List.map_append]
      exact hstep
  · -- Rocq: the first sequence is not all values; it steps, in the context of the second one
    have hnotbr1 := not_lf_br_right _ _ hnotbr
    have hnotret1 := not_lf_return_right _ _ hnotret
    rw [← List.append_assoc] at hwf
    obtain ⟨hwf1, hwf2⟩ := (wf_config_app _ _ _).mp hwf
    rcases ih1 s f C' vcs t_1_lst t_2_lst lab ret hwf1 hwfv rfl hctx hmod hts hstore hnotbr1 hnotret1 with
      hc | ⟨s', f', es1', hstep⟩
    · exact absurd hc hconst
    · right
      refine ⟨s', f', es1' ++ List.map admininstr_instr instr_2_lst, ?_⟩
      rw [← List.append_assoc]
      rcases instr_2_lst with _ | ⟨i2, instr_2_lst⟩
      · simp only [List.map_nil, List.append_nil]
        exact hstep
      · have hwf' := Step_is_wf (state.mk_state s f) _ _ hwf1 hstore hstep
        have h := Step.ctxt_instrs (state.mk_state s f) []
          (List.map admininstr_val vcs ++ List.map admininstr_instr instr_1_lst)
          (List.map admininstr_instr (i2 :: instr_2_lst)) (state.mk_state s' f') es1' hstep
          (Or.inr (by simp)) hwf1 hwf'
        exact h

/-- Lean-only (bundle20): the `Instrs_ok.sub` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5466`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_sub :
    ∀ (C : context) (instr_lst : List _root_.instr) (t'_1_lst t'_2_lst t_1_lst t_2_lst : List valtype)
  (a : Instrs_ok C instr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : Resulttype_sub (list.mk_list t'_1_lst) (list.mk_list t_1_lst))
  (a_2 : Resulttype_sub (list.mk_list t_2_lst) (list.mk_list t'_2_lst)) (a_3 : wf_context C)
  (a_4 : Forall (fun (v_instr_elem : _root_.instr) => wf_instr v_instr_elem) instr_lst),
  t_progress_be_P0 C instr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_be_P0 C instr_lst (functype.mk_functype (list.mk_list t'_1_lst) (list.mk_list t'_2_lst))
      (Instrs_ok.sub C instr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4) := by
  intro C instr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 ih
  unfold t_progress_be_P0 at ih ⊢
  intro s f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t'_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  have hnb : Forall (fun t => t ≠ valtype.BOT) t'_1_lst := by
    rw [e1]; exact typeof_vals_non_bot vcs ts1 hts
  have e2 : t'_1_lst = t_1_lst := resulttype_sub_non_bot _ _ hnb a_1
  exact ih s f C' vcs t_1_lst t_2_lst lab ret hwf hwfv rfl hctx hmod (by rw [hts, ← e1, e2]) hstore hnotbr
    hnotret

/-- Lean-only (bundle20): the `Instrs_ok.frame` case of Rocq's `t_progress_be` proof (bullet at `type_progress.v:5475`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok.rec` for motives
    `t_progress_be_P`/`t_progress_be_P0`, so the 78 cases can be proved and checked one by one. -/
theorem t_progress_be_frame :
    ∀ (C : context) (instr_lst : List _root_.instr) (t_lst t_1_lst t_2_lst : List valtype)
  (a : Instrs_ok C instr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))) (a_1 : wf_context C)
  (a_2 : Forall (fun (v_instr_elem : _root_.instr) => wf_instr v_instr_elem) instr_lst),
  t_progress_be_P0 C instr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_be_P0 C instr_lst (functype.mk_functype (list.mk_list (t_lst ++ t_1_lst)) (list.mk_list (t_lst ++ t_2_lst)))
      (Instrs_ok.frame C instr_lst t_lst t_1_lst t_2_lst a a_1 a_2) := by
  intro C instr_lst t_lst t_1_lst t_2_lst a a_1 a_2 ih
  unfold t_progress_be_P0 at ih ⊢
  intro s f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t_lst ++ t_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  rw [← e1] at hts
  -- Rocq splits `vcs` at `size ts` (take/drop); here split it along the type list directly
  obtain ⟨vcs1, vcs2, rfl, _hts1, hts2⟩ := List.map_eq_append_iff.mp hts
  rw [List.map_append, List.append_assoc] at hwf
  obtain ⟨_hwf1, hwf2⟩ := (wf_config_app _ _ _).mp hwf
  have hwfv2 : Forall (fun e => wf_val e) vcs2 := fun x hx => hwfv x (List.mem_append_right _ hx)
  rcases ih s f C' vcs2 t_1_lst t_2_lst lab ret hwf2 hwfv2 rfl hctx hmod hts2 hstore hnotbr hnotret with
    hconst | ⟨s', f', es', hstep⟩
  · exact Or.inl hconst
  · right
    refine ⟨s', f', List.map admininstr_val vcs1 ++ es', ?_⟩
    rw [List.map_append, List.append_assoc]
    rcases vcs1 with _ | ⟨v, vcs1⟩
    · simp only [List.map_nil, List.nil_append]
      exact hstep
    · have hwf' := Step_is_wf (state.mk_state s f) _ _ hwf2 hstore hstep
      have h := Step.ctxt_instrs (state.mk_state s f) (v :: vcs1)
        (List.map admininstr_val vcs2 ++ List.map admininstr_instr instr_lst) [] (state.mk_state s' f') es' hstep
        (Or.inl (List.cons_ne_nil _ _)) hwf2 hwf'
      simp only [List.append_nil] at h
      exact h

/-- Rocq `type_progress.v:3086` `t_progress_be`: progress for basic-instruction sequences, under a
    prefix of values `vcs` whose types are the sequence's input types. **`Admitted` in Rocq**: two of
    its cases are false as the spec stands (see `vload_shape64_stuck` and
    `vcvtop_trunc_sat_i16_stuck` at the end of this file), and Rocq also leaves an `admit` in the
    `vcvtop` case. Here the theorem is assembled from the 78 case lemmas `t_progress_be_*` by one
    application of the mutual recursor `Instrs_ok.rec` (Rocq: `Instrs_ok_ind'`). All 78 cases are
    proved apart from the two known-false subcases (in `t_progress_be_vload_pack` and
    `t_progress_be_vcvtop`), which keep one commented `sorry` each, as Rocq keeps its `admit`s. -/
theorem t_progress_be (s : store) (C C' : context) (f : frame) (vcs : List val) (bes : List instr)
    (tf : functype) (ts1 ts2 : List valtype) (lab : List resulttype) (ret : Option resulttype) :
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ List.map admininstr_instr bes)) →
    Instrs_ok C bes tf →
    Forall (fun e => wf_val e) vcs →
    tf = mkFunctype ts1 ts2 →
    C = upd_local_label_return C' (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE C' →
    List.map typeof vcs = ts1 →
    Store_ok s →
    not_lf_br (List.map admininstr_instr bes) →
    not_lf_return (List.map admininstr_instr bes) →
    const_list (List.map admininstr_instr bes) = true ∨
      ∃ (s' : store) (f' : frame) (es' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ List.map admininstr_instr bes))
          (config.mk_config (state.mk_state s' f') es') := by
  intro hwf hinstrs
  exact (Instrs_ok.rec (motive_1 := t_progress_be_P) (motive_2 := t_progress_be_P0)
    t_progress_be_nop t_progress_be_unreachable t_progress_be_drop t_progress_be_select_expl t_progress_be_select_impl t_progress_be_block t_progress_be_loop t_progress_be_if t_progress_be_br t_progress_be_br_if t_progress_be_br_table t_progress_be_call t_progress_be_call_indirect t_progress_be_return t_progress_be_const t_progress_be_unop t_progress_be_binop t_progress_be_testop t_progress_be_relop t_progress_be_cvtop t_progress_be_ref_null t_progress_be_ref_func t_progress_be_ref_is_null t_progress_be_vconst t_progress_be_vvunop t_progress_be_vvbinop t_progress_be_vvternop t_progress_be_vvtestop t_progress_be_vunop t_progress_be_vbinop t_progress_be_vtestop t_progress_be_vrelop t_progress_be_vshiftop t_progress_be_vbitmask t_progress_be_vswizzle t_progress_be_vshuffle t_progress_be_vsplat t_progress_be_vextract_lane t_progress_be_vreplace_lane t_progress_be_vextunop t_progress_be_vextbinop t_progress_be_vnarrow t_progress_be_vcvtop t_progress_be_local_get t_progress_be_local_set t_progress_be_local_tee t_progress_be_global_get t_progress_be_global_set t_progress_be_table_get t_progress_be_table_set t_progress_be_table_size t_progress_be_table_grow t_progress_be_table_fill t_progress_be_table_copy t_progress_be_table_init t_progress_be_elem_drop t_progress_be_memory_size t_progress_be_memory_grow t_progress_be_memory_fill t_progress_be_memory_copy t_progress_be_memory_init t_progress_be_data_drop t_progress_be_load_val t_progress_be_load_pack t_progress_be_store_val t_progress_be_store_pack t_progress_be_vload_val t_progress_be_vload_pack t_progress_be_vload_splat t_progress_be_vload_zero t_progress_be_vload_lane t_progress_be_vstore t_progress_be_vstore_lane t_progress_be_empty t_progress_be_instr t_progress_be_seq t_progress_be_sub t_progress_be_frame
    hinstrs) s f C' vcs ts1 ts2 lab ret hwf

/-- Rocq `type_progress.v:5515` `Instr_ok_Instrs_ok`: a single instruction typing gives the
    sequence typing. -/
theorem Instr_ok_Instrs_ok (C : context) (be : instr) (ts1 ts2 : List valtype) :
    Instr_ok C be (mkFunctype ts1 ts2) → Instrs_ok C [be] (mkFunctype ts1 ts2) := by
  intro hinstr
  obtain ⟨hwfC, hwfi⟩ := instr_ok_context_wf C be _ hinstr
  exact Instrs_ok.instr C be ts1 ts2 hinstr hwfC hwfi

-- `Scheme Instr_ok2_ind'`/`Admin_instrs_ok_ind'`/`Expr_ok2_ind'` (type_progress.v:5524) NOT PORTED:
-- Lean auto-generates the mutual recursor `Instrs_ok2.rec`, used by `t_progress_e` below.

/-- Lean-only (bundle20): Rocq's motive `P` (for `Instr_ok2`) in the `Admin_instrs_ok_ind'`
    application that proves `t_progress_e` (`type_progress.v:5553-5565`). The store `s` is a
    parameter of Lean's mutual inductive, so the recursor is used with motive `t_progress_e_P s`. -/
def t_progress_e_P (s : store) (C : context) (e : admininstr) (tf : functype) (_ : Instr_ok2 s C e tf) : Prop :=
  ∀ (f : frame) (C' : context) (vcs : List val) (ts1 ts2 : List valtype)
    (lab : List resulttype) (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ [e])) →
    Forall (fun e => wf_val e) vcs →
    tf = mkFunctype ts1 ts2 →
    C = upd_local_label_return C' (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE C' →
    List.map typeof vcs = ts1 →
    Store_ok s →
    not_lf_br [e] →
    not_lf_return [e] →
    terminal_form (List.map admininstr_val vcs ++ [e]) ∨
      ∃ (s' : store) (f' : frame) (es' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ [e]))
          (config.mk_config (state.mk_state s' f') es')

/-- Lean-only (bundle20): Rocq's motive `P0` (for `Instrs_ok2`) of `t_progress_e`
    (`type_progress.v:5566-5578`). -/
def t_progress_e_P0 (s : store) (C : context) (es : List admininstr) (tf : functype) (_ : Instrs_ok2 s C es tf) : Prop :=
  ∀ (f : frame) (C' : context) (vcs : List val) (ts1 ts2 : List valtype)
    (lab : List resulttype) (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ es)) →
    Forall (fun e => wf_val e) vcs →
    tf = mkFunctype ts1 ts2 →
    C = upd_local_label_return C' (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE C' →
    List.map typeof vcs = ts1 →
    Store_ok s →
    not_lf_br es →
    not_lf_return es →
    terminal_form (List.map admininstr_val vcs ++ es) ∨
      ∃ (s' : store) (f' : frame) (es' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ es))
          (config.mk_config (state.mk_state s' f') es')

/-- Lean-only (bundle20): Rocq's motive `P1` (for `Expr_ok2`) of `t_progress_e`
    (`type_progress.v:5579-5589`). Rocq's `|es| = |ts|` (`ts : resulttype` coerced to a list) is
    `es.length = (proj_list_0 valtype ts).length`. -/
def t_progress_e_P1 (s : store) (C : context) (es : List admininstr) (ts : resulttype) (_ : Expr_ok2 s C es ts) : Prop :=
  ∀ (f : frame) (C' : context) (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) es) →
    C = upd_return C' ret →
    Frame_ok s f C' →
    Store_ok s →
    not_lf_br es →
    not_lf_return es →
    (const_list es = true ∧ es.length = (proj_list_0 valtype ts).length) ∨
    es = [admininstr.TRAP] ∨
    ∃ (s' : store) (f' : frame) (es' : List admininstr),
      Step (config.mk_config (state.mk_state s f) es) (config.mk_config (state.mk_state s' f') es')

/-- Lean-only (bundle20): the `plain` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5591`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_plain (s : store) :
    ∀ (C : context) (v_instr : _root_.instr) (t_1_lst t_2_lst : List valtype)
  (a : Instr_ok C v_instr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))) (a_1 : wf_store s)
  (a_2 : wf_context C) (a_3 : wf_instr v_instr),
  t_progress_e_P s C (admininstr_instr v_instr) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.plain s C v_instr t_1_lst t_2_lst a a_1 a_2 a_3) := by
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

/-- Lean-only (bundle20): the `label` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5603`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_label (s : store) :
    ∀ (C : context) (v_n : n) (instr'_lst : List _root_.instr) (admininstr_lst : List admininstr)
  (t_lst t'_lst : List valtype)
  (a :
    Instrs_ok2 s C (Map (fun (instr'_elem : _root_.instr) => admininstr_instr instr'_elem) instr'_lst)
      (functype.mk_functype (list.mk_list t'_lst) (list.mk_list t_lst)))
  (a_1 :
    Instrs_ok2 s
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t'_lst], RETURN := none } : context) ++
        C)
      admininstr_lst (functype.mk_functype (list.mk_list []) (list.mk_list t_lst)))
  (a_2 : wf_store s) (a_3 : wf_context C) (a_4 : wf_admininstr (admininstr.LABEL_ v_n instr'_lst admininstr_lst))
  (a_5 :
    wf_context
      ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t'_lst], RETURN := none } : context))
  (a_6 : v_n = t'_lst.length),
  t_progress_e_P0 s C (Map (fun (instr'_elem : _root_.instr) => admininstr_instr instr'_elem) instr'_lst)
      (functype.mk_functype (list.mk_list t'_lst) (list.mk_list t_lst)) a →
    t_progress_e_P0 s
        (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [list.mk_list t'_lst], RETURN := none } : context) ++
          C)
        admininstr_lst (functype.mk_functype (list.mk_list []) (list.mk_list t_lst)) a_1 →
      t_progress_e_P s C (admininstr.LABEL_ v_n instr'_lst admininstr_lst)
        (functype.mk_functype (list.mk_list []) (list.mk_list t_lst))
        (Instr_ok2.label s C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6) := by
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

/-- Lean-only (bundle20): the `Instr_ok2_frame` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5689`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_Instr_ok2_frame (s : store) :
    ∀ (C : context) (v_n : n) (f : frame) (admininstr_lst : List admininstr) (t_lst : List valtype)
  (C' : context) (a : Frame_ok s f C')
  (a_1 :
    Expr_ok2 s
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [], RETURN := some (list.mk_list t_lst) } : context) ++
        C')
      admininstr_lst (list.mk_list t_lst))
  (a_2 : wf_store s) (a_3 : wf_context C) (a_4 : wf_context C')
  (a_5 : wf_admininstr (admininstr.FRAME_ v_n f admininstr_lst))
  (a_6 :
    wf_context
      ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [], RETURN := some (list.mk_list t_lst) } : context))
  (a_7 : v_n = t_lst.length),
  t_progress_e_P1 s
      (({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [], RETURN := some (list.mk_list t_lst) } : context) ++
        C')
      admininstr_lst (list.mk_list t_lst) a_1 →
    t_progress_e_P s C (admininstr.FRAME_ v_n f admininstr_lst) (functype.mk_functype (list.mk_list []) (list.mk_list t_lst))
      (Instr_ok2.Instr_ok2_frame s C v_n f admininstr_lst t_lst C' a a_1 a_2 a_3 a_4 a_5 a_6 a_7) := by
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

/-- Lean-only (bundle20): the `call_addr` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5761`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_call_addr (s : store) :
    ∀ (C : context) (v_funcaddr : funcaddr) (t_1_lst t_2_lst : List valtype)
  (a :
    Externaddr_ok s (externaddr.FUNC v_funcaddr)
      (externtype.FUNC (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))))
  (a_1 : wf_store s) (a_2 : wf_context C) (a_3 : wf_admininstr (admininstr.CALL_ADDR v_funcaddr))
  (a_4 : wf_externtype (externtype.FUNC (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))),
  t_progress_e_P s C (admininstr.CALL_ADDR v_funcaddr) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.call_addr s C v_funcaddr t_1_lst t_2_lst a a_1 a_2 a_3 a_4) := by
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

/-- Lean-only (bundle20): the `ref` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5841`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_ref (s : store) :
    ∀ (C : context) (v_ref : _root_.ref) (rt : reftype) (a : Ref_ok s v_ref rt) (a_1 : wf_store s)
  (a_2 : wf_context C),
  t_progress_e_P s C (admininstr_ref v_ref) (functype.mk_functype (list.mk_list []) (list.mk_list [valtype_reftype rt]))
    (Instr_ok2.ref s C v_ref rt a a_1 a_2) := by
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

/-- Lean-only (bundle20): the `trap` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5849`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_trap (s : store) :
    ∀ (C : context) (t_1_lst t_2_lst : List valtype) (a : wf_store s) (a_1 : wf_context C)
  (a_2 : wf_admininstr admininstr.TRAP),
  t_progress_e_P s C admininstr.TRAP (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.trap s C t_1_lst t_2_lst a a_1 a_2) := by
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

/-- Lean-only (bundle20): the `empty` case of Rocq's `t_progress_e` proof (no separate Rocq bullet (closed by the `=> //` of the `Admin_instrs_ok_ind'` application)),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_empty (s : store) :
    ∀ (C : context) (a : wf_store s) (a_1 : wf_context C),
  t_progress_e_P0 s C [] (functype.mk_functype (list.mk_list []) (list.mk_list [])) (Instrs_ok2.empty s C a a_1) := by
  intro C HWfS HWfC
  unfold t_progress_e_P0
  intro f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  left
  rw [List.append_nil]
  left
  exact v_to_e_const vcs

/-- Lean-only (bundle20): the `instr` case of Rocq's `t_progress_e` proof (no separate Rocq bullet (closed by the `=> //` of the `Admin_instrs_ok_ind'` application)),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_instr (s : store) :
    ∀ (C : context) (v_admininstr : admininstr) (t_1_lst t_2_lst : List valtype)
  (a : Instr_ok2 s C v_admininstr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : wf_store s) (a_2 : wf_context C) (a_3 : wf_admininstr v_admininstr),
  t_progress_e_P s C v_admininstr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_e_P0 s C [v_admininstr] (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
      (Instrs_ok2.instr s C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3) := by
  intro C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3 ih
  exact ih

/-- Lean-only (bundle20): the `seq` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5875`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_seq (s : store) :
    ∀ (C : context) (admininstr_1_lst admininstr_2_lst : List admininstr)
  (t_1_lst t_3_lst t_2_lst : List valtype)
  (a : Instrs_ok2 s C admininstr_1_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : Instrs_ok2 s C admininstr_2_lst (functype.mk_functype (list.mk_list t_2_lst) (list.mk_list t_3_lst)))
  (a_2 : wf_store s) (a_3 : wf_context C)
  (a_4 : Forall (fun (admininstr_1_elem : admininstr) => wf_admininstr admininstr_1_elem) admininstr_1_lst)
  (a_5 : Forall (fun (admininstr_2_elem : admininstr) => wf_admininstr admininstr_2_elem) admininstr_2_lst),
  t_progress_e_P0 s C admininstr_1_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_e_P0 s C admininstr_2_lst (functype.mk_functype (list.mk_list t_2_lst) (list.mk_list t_3_lst)) a_1 →
      t_progress_e_P0 s C (admininstr_1_lst ++ admininstr_2_lst)
        (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_3_lst))
        (Instrs_ok2.seq s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5) := by
  intro C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih1 ih2
  unfold t_progress_e_P0 at ih1 ih2 ⊢
  intro f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  rw [← e1] at hts
  by_cases hconst : const_list admininstr_1_lst = true
  · -- Rocq: the first sequence is all values; continue with the second one under `vcs ++ vs1`
    obtain ⟨vs1, hvs1⟩ := const_es_exists _ hconst
    have hadmin1 : Instrs_ok2 s C admininstr_1_lst (mkFunctype t_1_lst t_2_lst) := a
    rw [hvs1] at hadmin1
    obtain ⟨vts, hsub, hvok⟩ := ais_vals_typing_inversion s C vs1 t_1_lst t_2_lst hadmin1
    obtain ⟨ts_sub, ts0, ts11_sub, ts12_sup, h1, h2, hs0, hs1, hs2⟩ := hsub
    have e11 : ts11_sub = [] := resulttype_sub_empty _ hs1
    rw [e11, List.append_nil] at h1
    have hnb0 : Forall (fun t => t ≠ valtype.BOT) ts_sub := by
      rw [← h1]; exact typeof_vals_non_bot vcs t_1_lst hts
    have e0 : ts_sub = ts0 := resulttype_sub_non_bot _ _ hnb0 hs0
    have e2 : vts = ts12_sup := resulttype_sub_non_bot _ _ (Vals_ok_non_bot _ _ _ hvok) hs2
    obtain ⟨hvlen, hvf⟩ := hvok
    have hmapvs1 : List.map typeof vs1 = vts := Forall2_Val_ok_is_same_as_map s vts vs1 hvf hvlen
    have heqts2 : List.map typeof (vcs ++ vs1) = t_2_lst := by
      rw [List.map_append, hmapvs1, hts, h2, ← e0, ← h1, e2]
    have hnotbr2 := not_lf_br_left _ _ hconst hnotbr
    have hnotret2 := not_lf_return_left _ _ hconst hnotret
    rw [hvs1, ← List.append_assoc, ← List.map_append] at hwf
    have hwfvs1 : Forall (fun v => wf_val v) vs1 := by
      have h := a_4
      rw [hvs1] at h
      exact (wf_forall_admin_val vs1).mpr h
    have hwfv' : Forall (fun e => wf_val e) (vcs ++ vs1) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hwfv x hx
      · exact hwfvs1 x hx
    rw [hvs1, ← List.append_assoc, ← List.map_append]
    exact ih2 f C' (vcs ++ vs1) t_2_lst t_3_lst lab ret hwf hwfv' rfl hctx hmod heqts2 hstore hnotbr2 hnotret2
  · -- Rocq: the first sequence is not all values; it reduces (or is a trap), in the context of the second
    have hnotbr1 := not_lf_br_right _ _ hnotbr
    have hnotret1 := not_lf_return_right _ _ hnotret
    rw [← List.append_assoc] at hwf
    obtain ⟨hwf1, _hwf2⟩ := (wf_config_app _ _ _).mp hwf
    have ih1r :=
      ih1 f C' vcs t_1_lst t_2_lst lab ret hwf1 hwfv rfl hctx hmod hts hstore hnotbr1 hnotret1
    rw [← List.append_assoc]
    rcases admininstr_2_lst with _ | ⟨a2, es2⟩
    · rw [List.append_nil]
      exact ih1r
    · rcases ih1r with hterm | ⟨s', f', es1', hstep⟩
      · rcases hterm with hc | htrap
        · exfalso
          rw [const_list_cat, Bool.and_eq_true] at hc
          exact hconst hc.2
        · -- Rocq: `v_e_trap` gives `vcs = []`, `es1 = [TRAP]`; then `trap_vals` with `val_lst := []`
          right
          refine ⟨s, f, [admininstr.TRAP], ?_⟩
          rw [htrap]
          exact Step.pure _ _ _ (Step_pure.trap_vals [] (a2 :: es2) (Or.inr (List.cons_ne_nil _ _)))
      · right
        refine ⟨s', f', es1' ++ (a2 :: es2), ?_⟩
        have hwf' := Step_is_wf (state.mk_state s f) _ _ hwf1 hstore hstep
        exact Step.ctxt_instrs (state.mk_state s f) [] (List.map admininstr_val vcs ++ admininstr_1_lst)
          (a2 :: es2) (state.mk_state s' f') es1' hstep (Or.inr (List.cons_ne_nil _ _)) hwf1 hwf'

/-- Lean-only (bundle20): the `sub` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5949`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_sub (s : store) :
    ∀ (C : context) (admininstr_lst : List admininstr) (t'_1_lst t'_2_lst t_1_lst t_2_lst : List valtype)
  (a : Instrs_ok2 s C admininstr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : Resulttype_sub (list.mk_list t'_1_lst) (list.mk_list t_1_lst))
  (a_2 : Resulttype_sub (list.mk_list t_2_lst) (list.mk_list t'_2_lst)) (a_3 : wf_store s) (a_4 : wf_context C)
  (a_5 : Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst),
  t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list t'_1_lst) (list.mk_list t'_2_lst))
      (Instrs_ok2.sub s C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5) := by
  intro C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih
  unfold t_progress_e_P0 at ih ⊢
  intro f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t'_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  have hnb : Forall (fun t => t ≠ valtype.BOT) t'_1_lst := by
    rw [e1]; exact typeof_vals_non_bot vcs ts1 hts
  have e2 : t'_1_lst = t_1_lst := resulttype_sub_non_bot _ _ hnb a_1
  exact ih f C' vcs t_1_lst t_2_lst lab ret hwf hwfv rfl hctx hmod (by rw [hts, ← e1, e2]) hstore hnotbr
    hnotret

/-- Lean-only (bundle20): the `Instrs_ok2_frame` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:5958`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_Instrs_ok2_frame (s : store) :
    ∀ (C : context) (admininstr_lst : List admininstr) (t_lst t_1_lst t_2_lst : List valtype)
  (a : Instrs_ok2 s C admininstr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : wf_store s) (a_2 : wf_context C)
  (a_3 : Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst),
  t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list (t_lst ++ t_1_lst)) (list.mk_list (t_lst ++ t_2_lst)))
      (Instrs_ok2.Instrs_ok2_frame s C admininstr_lst t_lst t_1_lst t_2_lst a a_1 a_2 a_3) := by
  intro C es ts ts1 ts2 Hadmin HWfS HWfC HWfAIs IH
  unfold t_progress_e_P0 at IH ⊢
  intro f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  -- Rocq: `Heqts` / `cat_take_drop`: split `vcs` at `size ts`
  have Htf1 : ts ++ ts1 = ts1' := by
    unfold mkFunctype at Htf
    injection Htf with h1 h2
    injection h1
  obtain ⟨vcs1, vcs2, rfl, Hts1, Heqts⟩ := List.map_eq_append_iff.mp (Hts.trans Htf1.symm)
  rw [List.map_append, List.append_assoc] at HWfConfig
  obtain ⟨_HWfC1, HWfC2⟩ := (wf_config_app _ _ _).mp HWfConfig
  have HWfV2 : Forall (fun e => wf_val e) vcs2 := fun x hx => HWfVals x (List.mem_append_right _ hx)
  have IH' := IH f C' vcs2 ts1 ts2 lab ret HWfC2 HWfV2 rfl Hcontext Hmod Heqts Hstore Hnotbr Hnotret
  rw [List.map_append, List.append_assoc]
  rcases IH' with (Hconst | Htrap) | ⟨s', f', es', IH'⟩
  · left; left
    exact const_list_concat _ _ (v_to_e_const vcs1) Hconst
  · rw [Htrap]
    cases vcs1 with
    | nil => left; right; rfl
    | cons vc1 vcs1 =>
      right
      exact ⟨s, f, [admininstr.TRAP],
        Step.pure _ _ _ (Step_pure.trap_vals (vc1 :: vcs1) [] (Or.inl (List.cons_ne_nil _ _)))⟩
  · right
    refine ⟨s', f', List.map admininstr_val vcs1 ++ es', ?_⟩
    have HWfStep := Step_is_wf _ _ _ HWfC2 Hstore IH'
    cases vcs1 with
    | nil => simpa using IH'
    | cons vc1 vcs1 =>
      have H := Step.ctxt_instrs _ (vc1 :: vcs1) (List.map admininstr_val vcs2 ++ es) [] _ es' IH'
        (Or.inl (List.cons_ne_nil _ _)) HWfC2 HWfStep
      simp only [List.append_nil] at H
      exact H

/-- Lean-only (bundle20): the `mk_Expr_ok2` case of Rocq's `t_progress_e` proof (bullet at `type_progress.v:6006`),
    stated as exactly the minor premise of the mutual recursor `Instrs_ok2.rec` (store `s` is a
    parameter) for motives `t_progress_e_P s`/`t_progress_e_P0 s`/`t_progress_e_P1 s`. -/
theorem t_progress_e_mk_Expr_ok2 (s : store) :
    ∀ (C : context) (admininstr_lst : List admininstr) (t_lst : List valtype)
  (a : Instrs_ok2 s C admininstr_lst (functype.mk_functype (list.mk_list []) (list.mk_list t_lst)))
  (a_1 : wf_store s) (a_2 : wf_context C)
  (a_3 : Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst),
  t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list []) (list.mk_list t_lst)) a →
    t_progress_e_P1 s C admininstr_lst (list.mk_list t_lst) (Expr_ok2.mk_Expr_ok2 s C admininstr_lst t_lst a a_1 a_2 a_3) := by
  intro C es ts Hadmin HWfS HWfC HWfAIs IH
  unfold t_progress_e_P0 at IH
  unfold t_progress_e_P1
  intro f C' ret HWfConfig HEq HFrameOk Hstore Hnotbr Hnotret
  have Hloc := frame_t_context_local_types _ _ _ HFrameOk
  have Hlab := frame_t_context_label_empty _ _ _ HFrameOk
  cases HFrameOk
  rename_i val_lst v_moduleinst t_lst C0 Hmod _ _ _ _ _ _
  have HEq' : C = upd_local_label_return C0 (List.map typeof val_lst) [] ret := by
    rw [HEq]
    unfold upd_return upd_local_label_return upd_label upd_local
    congr 1
  have IH' := IH { LOCALS := val_lst, MODULE := v_moduleinst } C0 [] [] ts [] ret HWfConfig
    (iswf_Forall_nil _) rfl HEq' Hmod rfl Hstore Hnotbr Hnotret
  rcases IH' with (Hconst | Htrap) | Hprog
  · left
    refine ⟨Hconst, ?_⟩
    obtain ⟨vs, rfl⟩ := const_es_exists _ Hconst
    obtain ⟨v_ts, HSub, HVals⟩ := ais_vals_typing_inversion _ _ _ [] ts Hadmin
    have HSub' := (instrtype_sub_iff_resulttype_sub v_ts ts []).mpr HSub
    cases HSub' with
    | mk_Resulttype_sub _ _ HSizets _ =>
      simp only [proj_list_0, List.length_map]
      rw [← HVals.1, HSizets]
  · right; left; exact Htrap
  · right; right; exact Hprog

/-- Rocq `type_progress.v:5536` `t_progress_e`: progress for administrative-instruction sequences
    (labels, frames, calls, traps), by mutual induction on `Instr_ok2`/`Instrs_ok2`/`Expr_ok2`.
    `Qed` in Rocq (relying on the `Admitted` `t_progress_be`). Here it is assembled from the 12 case
    lemmas `t_progress_e_*` by one application of the mutual recursor `Instrs_ok2.rec` (Rocq:
    `Admin_instrs_ok_ind'`). -/
theorem t_progress_e (s : store) (C C' : context) (f : frame) (vcs : List val) (es : List admininstr)
    (tf : functype) (ts1 ts2 : List valtype) (lab : List resulttype) (ret : Option resulttype) :
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ es)) →
    Instrs_ok2 s C es tf →
    Forall (fun e => wf_val e) vcs →
    tf = mkFunctype ts1 ts2 →
    C = upd_local_label_return C' (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE C' →
    List.map typeof vcs = ts1 →
    Store_ok s →
    not_lf_br es →
    not_lf_return es →
    terminal_form (List.map admininstr_val vcs ++ es) ∨
      ∃ (s' : store) (f' : frame) (es' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vcs ++ es))
          (config.mk_config (state.mk_state s' f') es') := by
  intro hwf hadmin
  exact (Instrs_ok2.rec (motive_1 := t_progress_e_P s) (motive_2 := t_progress_e_P0 s) (motive_3 := t_progress_e_P1 s)
    (t_progress_e_plain s) (t_progress_e_label s) (t_progress_e_Instr_ok2_frame s) (t_progress_e_call_addr s) (t_progress_e_ref s) (t_progress_e_trap s) (t_progress_e_empty s) (t_progress_e_instr s) (t_progress_e_seq s) (t_progress_e_sub s) (t_progress_e_Instrs_ok2_frame s) (t_progress_e_mk_Expr_ok2 s)
    hadmin) f C' vcs ts1 ts2 lab ret hwf

/-- Rocq `type_progress.v:6064` `t_progress`: **progress**. A configuration that is `Config_ok` at
    some result type is either terminal (only values, or a single `TRAP`) or can take a step. `Qed`
    in Rocq, from `t_progress_e`. -/
theorem t_progress (s : store) (f : frame) (es : List admininstr) (ts : resulttype) :
    Config_ok (config.mk_config (state.mk_state s f) es) ts →
    terminal_form es ∨
      ∃ (s' : store) (f' : frame) (es' : List admininstr),
        Step (config.mk_config (state.mk_state s f) es) (config.mk_config (state.mk_state s' f') es') := by
  intro hconfig
  cases hconfig with
  | mk_Config_ok _ _ _ t_lst C hstate hexpr _ hwfconfig _ =>
  cases hstate with
  | mk_State_ok _ _ _ hstore hframe _ _ =>
  cases hexpr with
  | mk_Expr_ok2 _ _ _ hadmin _ _ _ =>
  have hloc := frame_t_context_local_types s f C hframe
  have hlab := frame_t_context_label_empty s f C hframe
  have hret := frame_t_context_return_empty s f C hframe
  have hC : C = upd_local_label_return (upd_local_label_return C [] [] none)
      (List.map typeof f.LOCALS) [] none := by
    rcases C with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    simp only at hloc hlab hret
    subst hloc hlab hret
    rfl
  have hmod : Moduleinst_ok s f.MODULE (upd_local_label_return C [] [] none) := by
    cases hframe with
    | mk_Frame_ok val_lst v_minst t_lst0 C0 hminst _ _ _ _ _ _ =>
      have hl : C0.LOCALS = [] := by cases hminst; rfl
      have hb : C0.LABELS = [] := by cases hminst; rfl
      have hr : C0.RETURN = none := by cases hminst; rfl
      rcases C0 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
      simp only at hl hb hr
      subst hl hb hr
      exact hminst
  exact t_progress_e s C (upd_local_label_return C [] [] none) f [] es (mkFunctype [] t_lst) [] t_lst [] none
    hwfconfig hadmin (fun x hx => by cases hx) rfl hC hmod rfl hstore
    (s_typing_not_lf_br' s f C es [] t_lst hframe hadmin)
    (s_typing_not_lf_return s f C es [] t_lst hframe hadmin)

/-- Rocq `type_progress.v:6103` `vload_shape64_wf`. `VLOAD (SHAPE 64 X 1)` is well formed
    (`64 * 1 = 128 / 2`), although `vload-shape-val` needs a `Jnn` of size 128 (counterexample
    family to `t_progress_be`, with `vload_shape64_stuck`). -/
theorem vload_shape64_wf (sx : sx) :
    wf_vloadop_ vectype.V128 (vloadop_.SHAPEX_ (sz.mk_sz 64) 1 sx) := by
  refine wf_vloadop_.vloadop__case_0 _ _ _ _ (wf_sz.sz_case_0 64 (by decide)) ?_
  norm_num [proj_sz_0, vsize]

/-- Rocq `type_progress.v:6107` `vload_shape64_stuck`. An in-bounds `VLOAD (SHAPE 64 X 1)` does not
    reduce (`vload-shape-oob` needs it out of bounds). Rocq's coercion `(i :> N)` is `proj_uN_0 i`
    and `|l|` is `l.length`. -/
theorem vload_shape64_stuck (z : state) (i : iN) (sx : sx) (ao : memarg) (es : List admininstr) :
    proj_uN_0 i + proj_uN_0 ao.OFFSET + 8 ≤ (fun_mem z (uN.mk_uN 0)).BYTES.length →
    ¬ Step_read (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 i),
        admininstr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz 64) 1 sx)) ao]) es := by
  intro Hb H
  have key : ∀ (vs : List val) (a b x : admininstr), [a, b] = Map admininstr_val vs ++ [x] → b = x := by
    intro vs a b x h
    rcases vs with _ | ⟨v, _ | ⟨v', vs'⟩⟩
    · simp [Map] at h
    · simp [Map] at h
      exact h.2
    · simp [Map] at h
  generalize hc : config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 i),
        admininstr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz 64) 1 sx)) ao] = c at H
  cases H
  all_goals try (simp at hc; done)
  all_goals try (injection hc with h1 h2; exact absurd (key _ _ _ _ h2) (by simp))
  case vload_shape_oob =>
    simp only [config.mk_config.injEq, List.cons.injEq, admininstr.CONST.injEq, admininstr.VLOAD.injEq,
      Option.some.injEq, vloadop_.SHAPEX_.injEq, sz.mk_sz.injEq, true_and, and_true] at hc
    obtain ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    rename_i _ _ Hgt
    have h8 : rat_to_nat (((64 : Nat) : Rat) * ((1 : Nat) : Rat) / (8 : Rat)) = 8 := by
      have : (((64 : Nat) : Rat) * ((1 : Nat) : Rat) / (8 : Rat)) = ((8 : Nat) : Rat) := by norm_num
      rw [this, rat_to_nat_natCast]
    rw [h8] at Hgt
    simp only [proj_num__0, Option.get!_some] at Hgt
    omega
  case vload_shape_val =>
    simp only [config.mk_config.injEq, List.cons.injEq, admininstr.CONST.injEq, admininstr.VLOAD.injEq,
      Option.some.injEq, vloadop_.SHAPEX_.injEq, sz.mk_sz.injEq, true_and, and_true] at hc
    obtain ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    rename_i _ _ J _ h1 _ _ _ _ _ _
    cases J <;> exact absurd h1 (by decide)

/-- Rocq `type_progress.v:6124` `vcvtop_trunc_sat_i16_wf_instr`. `VCVTOP (I16 X 8) (F32 X 4)
    (TRUNC_SAT sx ZERO)` is well formed: the side condition of `vcvtop__` allows it
    (`$sizenn1(F32) = 2 * $lsizenn2(I16)`). -/
theorem vcvtop_trunc_sat_i16_wf_instr (sx : sx) :
    wf_instr (instr.VCVTOP (shape.X lanetype.I16 (dim.mk_dim 8)) (shape.X lanetype.F32 (dim.mk_dim 4))
      (vcvtop__.mk_vcvtop___2 Fnn.F32 4 Jnn.I16 8
        (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT sx (some zero.ZERO)))) := by
  refine wf_instr.instr_case_39 _ _ _ ?_ ?_ ?_
  · exact wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)
  · exact wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)
  · exact wf_vcvtop__.vcvtop___case_2 _ _ _ _ _ _ _
      (wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2.vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 _ _ _ _ _ _
        (Or.inr ⟨by decide, rfl⟩)) rfl rfl

/-- Rocq `type_progress.v:6132` `vcvtop_trunc_sat_i16_stuck`. That well-formed `VCVTOP` on a `V128`
    constant does not reduce: `$lcvtop__` only defines `TRUNC_SAT` for `Inn` destinations, so
    `$vcvtop__` has no result (counterexample family to `t_progress_be`). -/
theorem vcvtop_trunc_sat_i16_stuck (sx : sx) (c : vec_) (es : List admininstr) :
    ¬ Step_pure [admininstr.VCONST vectype.V128 c,
        admininstr.VCVTOP (shape.X lanetype.I16 (dim.mk_dim 8)) (shape.X lanetype.F32 (dim.mk_dim 4))
          (vcvtop__.mk_vcvtop___2 Fnn.F32 4 Jnn.I16 8
            (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT sx (some zero.ZERO)))] es := by
  intro H
  -- generalize the left side so that `cases` can handle the rule `trap_vals` (a non-constructor lhs)
  generalize hl : [admininstr.VCONST vectype.V128 c,
        admininstr.VCVTOP (shape.X lanetype.I16 (dim.mk_dim 8)) (shape.X lanetype.F32 (dim.mk_dim 4))
          (vcvtop__.mk_vcvtop___2 Fnn.F32 4 Jnn.I16 8
            (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT sx (some zero.ZERO)))] = l at H
  cases H
  all_goals (try (simp at hl; done))
  · -- `trap_vals`: the left side `[VCONST, VCVTOP]` has no `TRAP`
    rename_i vl al _
    rcases vl with _ | ⟨v, _ | ⟨v', vl⟩⟩ <;> simp [Map] at hl
  · -- `vcvtop`
    cases hl
    rename_i hne _ hf
    cases hf with
    | fun_vcvtop___case_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hMM _ =>
      -- full: the lane counts differ (`4 = 8`)
      omega
    | fun_vcvtop___case_1 _ _ _ _ _ _ _ v_half c_1_lst c_lst_lst var_1_lst var_0 hlen hF2 hh hvne hvget hc hF1 _ _ _ _ _ =>
      -- half: `TRUNC_SAT` has no `half`
      cases hh <;> first | exact absurd rfl hvne | (simp at hvget)
    | fun_vcvtop___case_2 _ _ _ _ _ _ v128 c_1_lst c_lst_lst var_1_lst var_0 hlen hF2 hz hvne hvget hc hF1 _ _ _ _ _ _ =>
      -- zero: no lane-wise `TRUNC_SAT` to `I16`
      have hlcvtop : ∀ (ci : lane_) (v : Option (List lane_)),
          fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim 4)) (shape.X lanetype.I16 (dim.mk_dim 8))
            (vcvtop__.mk_vcvtop___2 Fnn.F32 4 Jnn.I16 8
              (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT sx (some zero.ZERO))) ci v → v = none := by
        intro ci v hv
        cases hv
        rfl
      have h4 : c_1_lst.length = 4 := by rw [hc]; exact lanes_len lanetype.F32 4 c
      rcases var_1_lst with _ | ⟨v, vl⟩
      · have h0 : c_1_lst.length = 0 := hlen.symm
        omega
      · rcases c_1_lst with _ | ⟨ci, cl⟩
        · simp at hlen
        · exact hF1 v (List.mem_cons_self ..) (hlcvtop ci v (hF2 (v, ci) (List.mem_cons_self ..)))
    | fun_vcvtop___case_3 _ _ _ _ hnb =>
      -- fallthrough: the result is `none`
      exact hne rfl

end TLC
