import «wasm2.0»

/-!
# Limits / externtype subtyping: reflexivity, transitivity, injectivity

Source material for this file:
* Rocq (branch `rocq-backend-proof`, `spectec/test-rocq/theories/extension_lemmas.v`,
  lines 285-412): `limits_sub_refl`, `limits_sub_trans`, `externtype_sub_refl`,
  `externtype_sub_trans`, `externtype_global_eq`, `externtype_func_eq`.
* These lemmas are not covered by Isabelle's `Properties.thy`; the closest
  Isabelle analogue is scattered through `Subtyping_Properties.thy` /
  `Subtyping_Theorem.thy` (branch `isabelle-mech-backend`), which were not
  separately ported here.

This complements `test-lean/typing_lemmas.lean`, which already covers
`Valtype_sub`/`Resulttype_sub` reflexivity and transitivity but not the
module/extern-type subtyping relations (`Limits_sub`, `Externtype_sub`, etc.)
defined at `wasm2.0.lean:9432-9496`.
-/

namespace TestLeanClaude

/-- Rocq: `limits_sub_refl` (extension_lemmas.v:285). -/
theorem limits_sub_refl {lim : limits} (h : wf_limits lim) : Limits_sub lim lim := by
  obtain ⟨v_u32, u32_opt⟩ := lim
  obtain ⟨nb⟩ := v_u32
  rcases u32_opt with _ | u
  · exact Limits_sub.eps nb nb (Nat.le_refl nb) h h
  · obtain ⟨mb⟩ := u
    refine Limits_sub.max nb mb nb (some mb) (Nat.le_refl nb) ?_ h h
    intro x hx
    have hxeq : x = mb := by simpa using hx
    subst hxeq
    exact Nat.le_refl x

/-- Rocq: `limits_sub_trans` (extension_lemmas.v:306). -/
theorem limits_sub_trans {lim lim' lim'' : limits}
    (h1 : Limits_sub lim lim') (h2 : Limits_sub lim' lim'') :
    Limits_sub lim lim'' := by
  cases h1 with
  | max n1 m1 n2 m2_opt hn hm hwf1 hwf2 =>
    rcases m2_opt with _ | m2
    · cases h2 with
      | eps n2' n3 hn' hwf2' hwf3 =>
        exact Limits_sub.max n1 m1 n3 none (Nat.le_trans hn' hn) (by simp [Forall]) hwf1 hwf3
    · cases h2 with
      | max n2' m2' n3 m3_opt hn' hm' hwf2' hwf3 =>
        refine Limits_sub.max n1 m1 n3 m3_opt (Nat.le_trans hn' hn) ?_ hwf1 hwf3
        rcases m3_opt with _ | m3
        · simp [Forall]
        · intro x hx
          have hxeq : x = m3 := by simpa using hx
          have hm2 : m1 ≤ m2 := by simpa [Forall] using hm
          have hm3 : m2 ≤ m3 := by simpa [Forall] using hm'
          rw [hxeq]
          exact Nat.le_trans hm2 hm3
  | eps n1 n2 hn hwf1 hwf2 =>
    cases h2 with
    | eps n2' n3 hn' hwf2' hwf3 =>
      exact Limits_sub.eps n1 n3 (Nat.le_trans hn' hn) hwf1 hwf3

/-- `Functype_sub` is definitionally reflexivity-only, so it forces equality. -/
theorem functype_sub_eq {a b : functype} (h : Functype_sub a b) : a = b := by
  cases h; rfl

/-- `Globaltype_sub` is definitionally reflexivity-only, so it forces equality. -/
theorem globaltype_sub_eq {a b : globaltype} (h : Globaltype_sub a b) : a = b := by
  cases h; rfl

/-- Rocq: `externtype_sub_refl` (extension_lemmas.v:343). -/
theorem externtype_sub_refl {xt : externtype} (h : wf_externtype xt) :
    Externtype_sub xt xt := by
  cases xt with
  | FUNC ft => exact Externtype_sub.func ft ft (Functype_sub.mk_Functype_sub ft) h h
  | GLOBAL gt => exact Externtype_sub.global gt gt (Globaltype_sub.mk_Globaltype_sub gt) h h
  | TABLE tt =>
    obtain ⟨lim, rt⟩ := tt
    have hwft : wf_tabletype (tabletype.mk_tabletype lim rt) := by
      cases h with
      | externtype_case_2 _ hw => exact hw
    have hlim : wf_limits lim := by
      cases hwft with
      | tabletype_case_0 _ _ hl => exact hl
    exact Externtype_sub.table (tabletype.mk_tabletype lim rt) (tabletype.mk_tabletype lim rt)
      (Tabletype_sub.mk_Tabletype_sub lim rt lim (limits_sub_refl hlim) hwft hwft)
      h h
  | MEM mt =>
    obtain ⟨lim⟩ := mt
    have hwfm : wf_memtype (memtype.PAGE lim) := by
      cases h with
      | externtype_case_3 _ hw => exact hw
    have hlim : wf_limits lim := by
      cases hwfm with
      | memtype_case_0 _ hl => exact hl
    exact Externtype_sub.mem (memtype.PAGE lim) (memtype.PAGE lim)
      (Memtype_sub.mk_Memtype_sub lim lim (limits_sub_refl hlim) hwfm hwfm)
      h h

/-- Rocq: `externtype_sub_trans` (extension_lemmas.v:363). -/
theorem externtype_sub_trans {xt xt' xt'' : externtype}
    (h1 : Externtype_sub xt xt') (h2 : Externtype_sub xt' xt'') :
    Externtype_sub xt xt'' := by
  cases h1 with
  | func ft1 ft2 hf hwf1 hwf2 =>
    cases h2 with
    | func _ ft3 hf' hwf2' hwf3 =>
      have e : ft1 = ft3 := (functype_sub_eq hf).trans (functype_sub_eq hf')
      exact Externtype_sub.func ft1 ft3 (e ▸ Functype_sub.mk_Functype_sub ft1) hwf1 hwf3
  | global gt1 gt2 hg hwf1 hwf2 =>
    cases h2 with
    | global _ gt3 hg' hwf2' hwf3 =>
      have e : gt1 = gt3 := (globaltype_sub_eq hg).trans (globaltype_sub_eq hg')
      exact Externtype_sub.global gt1 gt3 (e ▸ Globaltype_sub.mk_Globaltype_sub gt1) hwf1 hwf3
  | table tt1 tt2 ht hwf1 hwf2 =>
    cases h2 with
    | table _ tt3 ht' hwf2' hwf3 =>
      cases ht with
      | mk_Tabletype_sub lim1 rt lim2 hlim hwft1 hwft2 =>
        cases ht' with
        | mk_Tabletype_sub _ _ lim3 hlim' hwft2' hwft3 =>
          exact Externtype_sub.table (tabletype.mk_tabletype lim1 rt) (tabletype.mk_tabletype lim3 rt)
            (Tabletype_sub.mk_Tabletype_sub lim1 rt lim3 (limits_sub_trans hlim hlim') hwft1 hwft3)
            hwf1 hwf3
  | mem mt1 mt2 hm hwf1 hwf2 =>
    cases h2 with
    | mem _ mt3 hm' hwf2' hwf3 =>
      cases hm with
      | mk_Memtype_sub lim1 lim2 hlim hwfm1 hwfm2 =>
        cases hm' with
        | mk_Memtype_sub _ lim3 hlim' hwfm2' hwfm3 =>
          exact Externtype_sub.mem (memtype.PAGE lim1) (memtype.PAGE lim3)
            (Memtype_sub.mk_Memtype_sub lim1 lim3 (limits_sub_trans hlim hlim') hwfm1 hwfm3)
            hwf1 hwf3

/-- Rocq: `externtype_global_eq` (extension_lemmas.v:394). -/
theorem externtype_global_eq {gt gt' : globaltype}
    (h : Externtype_sub (externtype.GLOBAL gt) (externtype.GLOBAL gt')) : gt = gt' := by
  cases h with
  | global _ _ hg _ _ => exact globaltype_sub_eq hg

/-- Rocq: `externtype_func_eq` (extension_lemmas.v:403). -/
theorem externtype_func_eq {ft ft' : functype}
    (h : Externtype_sub (externtype.FUNC ft) (externtype.FUNC ft')) : ft = ft' := by
  cases h with
  | func _ _ hf _ _ => exact functype_sub_eq hf

end TestLeanClaude
