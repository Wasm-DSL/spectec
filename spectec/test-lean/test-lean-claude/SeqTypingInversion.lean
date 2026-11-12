import «wasm2.0»
import custom_notation

/-!
# Corrected `instrs_seq_typing_inversion`

Attempts the *corrected* restatement of `typing_lemmas.lean`'s
`instrs_seq_typing_inversion` identified in `logs/DECISIONS.md`
(`2026-09-23 ~00:05`/`~00:15` entries): the original states its conclusion
using singular `Instr_ok` for the head instruction, which is false (see
`CounterexampleCheck.lean`); Rocq's analogous `ais_seq_typing_inversion`
(`typing_lemmas.v:1080`) instead uses the *sequence*-level judgment applied
to a singleton, which is the shape used here.

Building block first: a local re-derivation of `instrs_empty_typing`'s "→"
direction (that file already has this exact fact, proved, but it isn't in an
importable module — see `logs/DECISIONS.md`'s cross-file-import entry for
why everything here is self-contained rather than importing it).
-/

namespace TestLeanClaude

theorem valtype_sub_refl (t : valtype) : Valtype_sub t t := Valtype_sub.refl t

theorem valtype_sub_trans {a b c : valtype} (h1 : Valtype_sub a b) (h2 : Valtype_sub b c) :
    Valtype_sub a c := by
  cases h1 with
  | refl _ => exact h2
  | bot _ => exact Valtype_sub.bot c

theorem forall2_valtype_sub_refl (ts : List valtype) :
    Forall₂ (fun a b => Valtype_sub a b) ts ts := by
  induction ts with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with hp | hp
    · rw [hp]; exact valtype_sub_refl x
    · exact ih p hp

theorem forall2_valtype_sub_trans {t1s t2s t3s : List valtype}
    (hlen12 : t1s.length = t2s.length) (hlen23 : t2s.length = t3s.length)
    (h1 : Forall₂ (fun a b => Valtype_sub a b) t1s t2s)
    (h2 : Forall₂ (fun a b => Valtype_sub a b) t2s t3s) :
    Forall₂ (fun a b => Valtype_sub a b) t1s t3s := by
  induction t1s generalizing t2s t3s with
  | nil =>
    match t2s, t3s, hlen12, hlen23 with
    | [], [], _, _ => intro p hp; simp at hp
  | cons x xs ih =>
    match t2s, hlen12 with
    | y :: ys, hlen12 =>
      match t3s, hlen23 with
      | z :: zs, hlen23 =>
        have hxy : Valtype_sub x y := h1 (x, y) (by simp)
        have hyz : Valtype_sub y z := h2 (y, z) (by simp)
        have hxz : Valtype_sub x z := valtype_sub_trans hxy hyz
        have htail : Forall₂ (fun a b => Valtype_sub a b) xs zs := by
          apply ih (Nat.succ.inj hlen12) (Nat.succ.inj hlen23)
          · intro p hp; exact h1 p (by simp; right; exact hp)
          · intro p hp; exact h2 p (by simp; right; exact hp)
        intro p hp
        simp only [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with hp | hp
        · rw [hp]; exact hxz
        · exact htail p hp

theorem resulttype_sub_refl (ts : List valtype) : Resulttype_sub (.mk_list ts) (.mk_list ts) :=
  Resulttype_sub.mk_Resulttype_sub ts ts rfl (forall2_valtype_sub_refl ts)

theorem resulttype_sub_trans {t1s t2s t3s : List valtype}
    (h1 : Resulttype_sub (.mk_list t1s) (.mk_list t2s))
    (h2 : Resulttype_sub (.mk_list t2s) (.mk_list t3s)) :
    Resulttype_sub (.mk_list t1s) (.mk_list t3s) := by
  cases h1 with
  | mk_Resulttype_sub _ _ hlen1 hf1 =>
    cases h2 with
    | mk_Resulttype_sub _ _ hlen2 hf2 =>
      exact Resulttype_sub.mk_Resulttype_sub t1s t3s (hlen1.trans hlen2)
        (forall2_valtype_sub_trans hlen1 hlen2 hf1 hf2)

theorem resulttype_sub_app {t1s_sub t2s_sub t1s t2s : List valtype}
    (h1 : Resulttype_sub (.mk_list t1s_sub) (.mk_list t1s))
    (h2 : Resulttype_sub (.mk_list t2s_sub) (.mk_list t2s)) :
    Resulttype_sub (.mk_list (t1s_sub ++ t2s_sub)) (.mk_list (t1s ++ t2s)) := by
  cases h1 with
  | mk_Resulttype_sub _ _ hlen1 hf1 =>
    cases h2 with
    | mk_Resulttype_sub _ _ hlen2 hf2 =>
      refine Resulttype_sub.mk_Resulttype_sub (t1s_sub ++ t2s_sub) (t1s ++ t2s) (by simp [hlen1, hlen2]) ?_
      have hzip := List.zip_append (l₁ := t1s_sub) (r₁ := t2s_sub) (l₂ := t1s) (r₂ := t2s) hlen1
      intro p hp
      rw [hzip] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hf1 p hp
      · exact hf2 p hp

/-- Rocq: the "→" direction of `instrs_empty_typing`'s characterization
    (already established, proved, in `typing_lemmas.lean` — re-derived here
    since that file isn't importable, see file header). By induction on
    `Instrs_ok`, generalizing the instruction-list index to the concrete `[]`. -/
theorem instrs_ok_nil_sub_gen {C : context} {instr_lst : List instr} {ft : functype}
    (h : Instrs_ok C instr_lst ft) :
    instr_lst = [] → ∀ t1 t2, ft = mkFunctype t1 t2 → Resulttype_sub (.mk_list t1) (.mk_list t2) := by
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
    have hs12 : Resulttype_sub (.mk_list s1) (.mk_list s2) := ih1 e1 s1 s2 rfl
    have hs23 : Resulttype_sub (.mk_list s2) (.mk_list s3) := ih2 e2 s2 s3 rfl
    rw [← e3, ← e4]
    exact resulttype_sub_trans hs12 hs23
  | sub C' i t1'' t2'' t1''' t2''' hok hsub1 hsub2 _ _ ih =>
    intro heq t1 t2 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    have hmid := ih heq t1''' t2''' rfl
    rw [← e1, ← e2]
    exact resulttype_sub_trans (resulttype_sub_trans hsub1 hmid) hsub2
  | frame C' i tpre t1'''' t2'''' hok _ _ ih =>
    intro heq t1 t2 hft
    unfold mkFunctype at hft
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    have hmid := ih heq t1'''' t2'''' rfl
    rw [← e1, ← e2]
    exact resulttype_sub_app (resulttype_sub_refl tpre) hmid
  | _ => intros; trivial

theorem instrs_ok_nil_sub {C : context} {t1 t2 : List valtype}
    (h : Instrs_ok C [] (mkFunctype t1 t2)) :
    Resulttype_sub (.mk_list t1) (.mk_list t2) :=
  instrs_ok_nil_sub_gen h rfl t1 t2 rfl

/-- `Instrs_ok C [] (t f-> t)` for any `t`: the empty sequence trivially
    "does nothing", via `frame` prepending `t` to `Instrs_ok.empty`'s
    `[] f-> []`. -/
theorem instrs_ok_nil_refl {C : context} (hC : wf_context C) (t : List valtype) :
    Instrs_ok C [] (mkFunctype t t) := by
  have h := Instrs_ok.frame C [] t [] [] (Instrs_ok.empty C hC) hC (by intro x hx; simp at hx)
  simpa [mkFunctype] using h

/-- Contravariant input-widening for a fixed `Instrs_ok` derivation: if
    `Instrs_ok C is (t f-> t2)` and `t1 subs< t`, then also
    `Instrs_ok C is (t1 f-> t2)`. Direct application of `Instrs_ok.sub` with
    a reflexive output-side witness. -/
theorem instrs_ok_widen_in {C : context} {is : List instr} {t t1 t2 : List valtype}
    (h : Instrs_ok C is (mkFunctype t t2)) (hsub : Resulttype_sub (.mk_list t1) (.mk_list t))
    (hC : wf_context C) (hwf : Forall (fun i => wf_instr i) is) :
    Instrs_ok C is (mkFunctype t1 t2) :=
  Instrs_ok.sub C is t1 t2 t t2 h hsub (resulttype_sub_refl t2) hC hwf

/-- Covariant output-widening: dual of `instrs_ok_widen_in`. -/
theorem instrs_ok_widen_out {C : context} {is : List instr} {t t1 t2 : List valtype}
    (h : Instrs_ok C is (mkFunctype t1 t)) (hsub : Resulttype_sub (.mk_list t) (.mk_list t2))
    (hC : wf_context C) (hwf : Forall (fun i => wf_instr i) is) :
    Instrs_ok C is (mkFunctype t1 t2) :=
  Instrs_ok.sub C is t1 t2 t1 t h (resulttype_sub_refl t1) hsub hC hwf

/-- The corrected `instrs_seq_typing_inversion`: see the file header and
    `logs/DECISIONS.md` (`2026-09-23 ~00:05`/`~00:15`) for why the original
    `typing_lemmas.lean` statement (using singular `Instr_ok` for the head)
    is false, and why this sequence-level-conclusion restatement (matching
    Rocq's `ais_seq_typing_inversion`, `typing_lemmas.v:1080`) is the fix.
    Generic/quantified-inside form first (needed for the induction, same
    reason as `instrs_ok_nil_sub_gen` above), specialized wrapper below. -/
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
      have hsub1 : Resulttype_sub (.mk_list s1) (.mk_list s2) := instrs_ok_nil_sub h1
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

theorem instrs_seq_typing_inversion_fixed {C : context} {i : instr} {is : List instr}
    {ts1 ts3 : List valtype} (h : Instrs_ok C (i :: is) (mkFunctype ts1 ts3)) :
    ∃ ts2, Instrs_ok C [i] (mkFunctype ts1 ts2) ∧ Instrs_ok C is (mkFunctype ts2 ts3) :=
  instrs_ok_cons_gen h i is rfl ts1 ts3 rfl

end TestLeanClaude
