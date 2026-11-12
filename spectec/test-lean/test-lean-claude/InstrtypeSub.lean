import «wasm2.0»
import custom_notation

/-!
# `instrtype_sub` reflexivity and transitivity

This targets two live `sorry`s in the pre-existing, human-written
`test-lean/typing_lemmas.lean` (not part of this folder, not edited here —
see `logs/DECISIONS.md` for why): `instrtype_sub_refl` (line 1112-1117) and
`instrtype_sub_trans` (line 1545-1556). Both are stated there against a
hand-defined `instrtype_sub` (typing_lemmas.lean:1042-1053, copied verbatim
below since it isn't exported from a buildable module) modelling
Wasm's "instruction-sequence subtyping via frame extension": an actual
instruction type `original_ft` is usable where `contextualized_ft` is
expected iff `contextualized_ft` = `original_ft` sandwiched between a shared
resulttype-subtyping "frame" on both sides.

Rocq counterpart: `subtyping.v:420` (`instrtype_sub_refl`) and `:434`
(`instrtype_sub_trans`), both fully proved there (`<ti:` notation). Isabelle
doesn't have a direct counterpart under this name.

Both compile cleanly with 0 `sorry` (verified: `lake env lean
test-lean-claude/InstrtypeSub.lean` from `test-lean/` produces no output).
The proof bodies below should paste in directly to replace the two `sorry`s
in `typing_lemmas.lean` (only the statement's surrounding context differs:
that file has these as free-standing theorems already using its own
`instrtype_sub`/`subs<`). Also proves, as reusable supporting lemmas along
the way, `resulttype_sub_refl`/`_trans`/`_app`/`_split`/`_split_sup` (Rocq:
`subtyping.v:114,132,242,344,389` respectively) — none of which existed yet
in this folder, and `_split`/`_split_sup` in particular are genuinely new
relative to `typing_lemmas.lean`'s own content (that file has
`resulttype_sub_refl`/`_trans`/`_app` already but not the split family).
Not copied into that file automatically since editing it is outside this
folder's scope unless asked.
-/

namespace TestLeanClaude

/-- Copied verbatim from `typing_lemmas.lean:1042-1053` (that file's own
    definition, not part of any buildable module, hence copied rather than
    imported — see file header). -/
def instrtype_sub (original_ft contextualized_ft : functype) : Prop :=
  match original_ft, contextualized_ft with
  | .mk_functype (.mk_list original_input_type) (.mk_list original_output_type),
    .mk_functype (.mk_list actual_supplied_input_type) (.mk_list actual_needed_output_type) =>
    ∃ (rest_in rest_out supplied_in needed_out : List valtype),
      actual_supplied_input_type = rest_in ++ supplied_in
      ∧ actual_needed_output_type = rest_out ++ needed_out
      ∧ (rest_in subs< rest_out)
      ∧ (supplied_in subs< original_input_type)
      ∧ (original_output_type subs< needed_out)

infix:20 "instrsub<" => instrtype_sub

/-- `Valtype_sub` (`wasm2.0.lean:9418-9420`) is reflexive by its own `refl`
    constructor; spelled out for use inside `Forall₂`. -/
theorem valtype_sub_refl (t : valtype) : Valtype_sub t t := Valtype_sub.refl t

/-- `Valtype_sub` is transitive: the only non-`refl` case is `bot`, which
    concludes `Sub BOT c` unconditionally regardless of the middle term. -/
theorem valtype_sub_trans {a b c : valtype} (h1 : Valtype_sub a b) (h2 : Valtype_sub b c) :
    Valtype_sub a c := by
  cases h1 with
  | refl _ => exact h2
  | bot _ => exact Valtype_sub.bot c

/-- Pointwise-`Forall₂` reflexivity, specialized to `Valtype_sub`. -/
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

/-- Pointwise-`Forall₂` transitivity, specialized to `Valtype_sub`, proved by
    plain list induction (avoids relying on any Mathlib `Forall₂` bridging
    machinery, since `Forall₂` here is the SpecTec-Lean-backend's own `def`
    via `List.zip`, not `List.Forall₂`). -/
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

/-- Rocq: `subtyping.v` uses this as `<ts:`'s definitional reflexivity; here
    re-derived directly from `Resulttype_sub`'s single constructor
    (`wasm2.0.lean:9424-9428`). -/
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

/-- Rocq: `subtyping.v:242`, `resulttype_sub_app`. Concatenation of two
    `Resulttype_sub` facts is a `Resulttype_sub` of the concatenations —
    the "easy direction" companion to `resulttype_sub_split`
    (`subtyping.v:344-420`, the harder decomposition direction that
    `instrtype_sub_trans` above actually needs and that isn't ported here). -/
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

/-- Rocq: `subtyping.v:344`, `resulttype_sub_split` — the harder decomposition
    direction `instrtype_sub_trans` needs. Splits a `Resulttype_sub` of a
    concatenation `ts1 ++ ts2` against the count-matching prefix/suffix of the
    target list, at the length of `ts1`. -/
theorem resulttype_sub_split {ts1 ts2 ts : List valtype}
    (h : Resulttype_sub (.mk_list (ts1 ++ ts2)) (.mk_list ts)) :
    ∃ ts_1 ts_2, ts = ts_1 ++ ts_2 ∧ ts1.length = ts_1.length ∧
      Resulttype_sub (.mk_list ts1) (.mk_list ts_1) ∧
      Resulttype_sub (.mk_list ts2) (.mk_list ts_2) := by
  cases h with
  | mk_Resulttype_sub _ _ hlen hf =>
    have hle : ts1.length ≤ ts.length := by
      simp only [List.length_append] at hlen; omega
    have hlent : ts1.length = (ts.take ts1.length).length := by simp [List.length_take, hle]
    have hzip : (ts1 ++ ts2).zip ts
        = ts1.zip (ts.take ts1.length) ++ ts2.zip (ts.drop ts1.length) := by
      calc (ts1 ++ ts2).zip ts
          = (ts1 ++ ts2).zip (ts.take ts1.length ++ ts.drop ts1.length) := by
            rw [List.take_append_drop]
        _ = ts1.zip (ts.take ts1.length) ++ ts2.zip (ts.drop ts1.length) := List.zip_append hlent
    refine ⟨ts.take ts1.length, ts.drop ts1.length, (List.take_append_drop _ _).symm, hlent, ?_, ?_⟩
    · refine Resulttype_sub.mk_Resulttype_sub ts1 (ts.take ts1.length) hlent ?_
      intro p hp
      exact hf p (hzip ▸ List.mem_append.mpr (Or.inl hp))
    · refine Resulttype_sub.mk_Resulttype_sub ts2 (ts.drop ts1.length) ?_ ?_
      · simp only [List.length_append] at hlen
        simp [List.length_drop]; omega
      · intro p hp
        exact hf p (hzip ▸ List.mem_append.mpr (Or.inr hp))

/-- Rocq: `subtyping.v:389`, `resulttype_sub_split_sup` — the mirror-image of
    `resulttype_sub_split` above: here the *target* (RHS) is the
    concatenation, and the source (LHS) gets split to match. -/
theorem resulttype_sub_split_sup {ts ts1 ts2 : List valtype}
    (h : Resulttype_sub (.mk_list ts) (.mk_list (ts1 ++ ts2))) :
    ∃ ts_1 ts_2, ts = ts_1 ++ ts_2 ∧ ts1.length = ts_1.length ∧
      Resulttype_sub (.mk_list ts_1) (.mk_list ts1) ∧
      Resulttype_sub (.mk_list ts_2) (.mk_list ts2) := by
  cases h with
  | mk_Resulttype_sub _ _ hlen hf =>
    have hle : ts1.length ≤ ts.length := by
      simp only [List.length_append] at hlen; omega
    have hlent : ts1.length = (ts.take ts1.length).length := by simp [List.length_take, hle]
    have hzip : ts.zip (ts1 ++ ts2)
        = (ts.take ts1.length).zip ts1 ++ (ts.drop ts1.length).zip ts2 := by
      calc ts.zip (ts1 ++ ts2)
          = (ts.take ts1.length ++ ts.drop ts1.length).zip (ts1 ++ ts2) := by
            rw [List.take_append_drop]
        _ = (ts.take ts1.length).zip ts1 ++ (ts.drop ts1.length).zip ts2 := List.zip_append hlent.symm
    refine ⟨ts.take ts1.length, ts.drop ts1.length, (List.take_append_drop _ _).symm, hlent, ?_, ?_⟩
    · refine Resulttype_sub.mk_Resulttype_sub (ts.take ts1.length) ts1 hlent.symm ?_
      intro p hp
      exact hf p (hzip ▸ List.mem_append.mpr (Or.inl hp))
    · refine Resulttype_sub.mk_Resulttype_sub (ts.drop ts1.length) ts2 ?_ ?_
      · simp only [List.length_append] at hlen
        simp [List.length_drop]; omega
      · intro p hp
        exact hf p (hzip ▸ List.mem_append.mpr (Or.inr hp))

/-- Rocq: `subtyping.v:420`, `instrtype_sub_refl`.
    Targets `typing_lemmas.lean:1112-1117`'s `sorry`. -/
theorem instrtype_sub_refl (ft : functype) : ft instrsub< ft := by
  obtain ⟨t1, t2⟩ := ft
  obtain ⟨t1'⟩ := t1
  obtain ⟨t2'⟩ := t2
  refine ⟨[], [], t1', t2', rfl, rfl, ?_, ?_, ?_⟩
  · exact resulttype_sub_refl []
  · exact resulttype_sub_refl t1'
  · exact resulttype_sub_refl t2'

/-- Rocq: `subtyping.v:434`, `instrtype_sub_trans`.
    Targets `typing_lemmas.lean:1545-1556`'s `sorry`.

    Follows Rocq's construction exactly (their proof has an ASCII diagram
    explaining the witness choice): writing `k := len(rest_in₁₂) =
    len(rest_out₁₂)` (equal since `Resulttype_sub` bakes in length equality),
    split `h23`'s two `Resulttype_sub` facts at `k` — once on the "sup"
    (RHS-is-concat) side via `resulttype_sub_split_sup`, once on the plain
    (LHS-is-concat) side via `resulttype_sub_split` — to get four fresh
    pieces, then reassemble the final witness as
    `rest_in := rest_in₂₃ ++ a`, `rest_out := rest_out₂₃ ++ c`,
    `supplied_in := b`, `needed_out := d`, chaining `resulttype_sub_trans`
    twice for the `rest_in subs< rest_out` obligation and once each for the
    other two. -/
theorem instrtype_sub_trans {ft1 ft2 ft3 : functype}
    (h12 : ft1 instrsub< ft2) (h23 : ft2 instrsub< ft3) :
    ft1 instrsub< ft3 := by
  obtain ⟨oi1', oo1'⟩ := ft1
  obtain ⟨oi1⟩ := oi1'
  obtain ⟨oo1⟩ := oo1'
  obtain ⟨si2', no2'⟩ := ft2
  obtain ⟨si2⟩ := si2'
  obtain ⟨no2⟩ := no2'
  obtain ⟨si3', no3'⟩ := ft3
  obtain ⟨si3⟩ := si3'
  obtain ⟨no3⟩ := no3'
  obtain ⟨rin12, rout12, sup12, nout12, hsi2, hno2, hrsub12, hsup12, hnout12⟩ := h12
  obtain ⟨rin23, rout23, sup23, nout23, hsi3, hno3, hrsub23, hsup23, hnout23⟩ := h23
  subst hsi2
  subst hno2
  obtain ⟨a, b, hab, _hlenab, ha, hb⟩ := resulttype_sub_split_sup hsup23
  obtain ⟨c, d, hcd, _hlencd, hc, hd⟩ := resulttype_sub_split hnout23
  refine ⟨rin23 ++ a, rout23 ++ c, b, d, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsi3, hab, List.append_assoc]
  · rw [hno3, hcd, List.append_assoc]
  · exact resulttype_sub_app hrsub23 (resulttype_sub_trans (resulttype_sub_trans ha hrsub12) hc)
  · exact resulttype_sub_trans hb hsup12
  · exact resulttype_sub_trans hnout12 hd

/-- Targets `typing_lemmas.lean:1536-1543`'s `sorry`, `instr_subtyping_weaken2`:
    weakening an `instrtype_sub` fact's contextualized output along a further
    `Resulttype_sub` step. Rocq doesn't have this exact lemma under this name
    (its `subtyping.v` composes `instrtype_sub_compose_*` families instead),
    but the proof is a direct one-shot application of `resulttype_sub_split`
    + `resulttype_sub_trans` on the "needed_out"/"rest_out" pieces, reusing
    the same witnesses from `h` for everything else. -/
theorem instr_subtyping_weaken2 {tx1 tx2 ty1 ty2 ty2_sup : List valtype}
    (h : (mkFunctype tx1 ty1) instrsub< (mkFunctype tx2 ty2))
    (hy : ty2 subs< ty2_sup) :
    (mkFunctype tx1 ty1) instrsub< (mkFunctype tx2 ty2_sup) := by
  obtain ⟨rin, rout, sup, nout, htx2, hty2, hrsub, hsup, hnout⟩ := h
  subst hty2
  obtain ⟨rout', nout', hty2sup, _hlen, hrout, hnout'⟩ := resulttype_sub_split hy
  refine ⟨rin, rout', sup, nout', htx2, hty2sup, resulttype_sub_trans hrsub hrout, hsup,
    resulttype_sub_trans hnout hnout'⟩

end TestLeanClaude
