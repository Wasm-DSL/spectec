import «wasm2.0»
import HelperLemmas
import Subtyping
import TypingLemmas
import TypePreservationPure

/-!
# ExtensionLemmas

Lean port of `spectec/test-rocq/theories/extension_lemmas.v`. Full
digest: `claude-logging/for-claude/digest_subtyping_and_extension_lemmas.md`.

Names and statement shapes follow the current Rocq source (upstream `rocq-backend-proof`
`6582b3a39`; the line numbers below refer to it): the `Extend_store_*`/`extend_*_refl*`
names, the index-based `holds_upto P n` ("P holds at every index below n") conclusions
(Rocq `wasm.v:107`, `holds_upto P n := Forall P (iotaN 0 n)`, i.e. exactly
`Forall P (List.range n)` here — see the `holds_upto` definition below), the `wf_*`
premises, and the unified `Externtype_sub` premises of `minst_invert_funcs`/`_globals`/
`_tables`/`_mems`. These replaced the `store_extension_*` names, `Forall₂`/existential-split
conclusions and per-kind premises of the older Rocq revision (`5b03ae067`) this file was first
ported from; see
`claude-logging/verbatim_dialogue_log/bundle3/updated_documents/resync_impact_report.md`.

**Naming note**: the store-extension relations are
`Extend_store`/`Extend_funcinst`/`Extend_tableinst`/`Extend_meminst`/
`Extend_globalinst`/`Extend_eleminst`/`Extend_datainst`, generated from the same EL spec
both in Rocq's `wasm.v` and in `wasm2.0.lean`. (The `Store_extension`/`Func_extension`/…
names in the early digests were never declared in any Rocq revision.)
**Consequence for lemma signatures**:
the `Extend_*` relations' constructors (confirmed by reading `wasm2.0.lean`
directly) bake in `wf_*` well-formedness premises for `Extend_funcinst`/
`Extend_globalinst`/`Extend_tableinst`/`Extend_meminst`/`Extend_datainst`
(but NOT `Extend_eleminst`, which has none), and Rocq's
`extend_funcinst_refl_0`/etc. carry exactly these `wf_*`
premises, as the lemmas below do. A prior Lean session's `Extension.lean` (see
`digest_prior_lean_attempts.md`) independently arrived at the same
signatures early on; its proofs are reused below.

Similarly, `Admin_instrs_ok`/`Thread_ok`/`Admin_instr_ok` (named by the
digest for the custom `Scheme`-based mutual induction backing
`Extend_store_ais`) do not exist — the matching judgments are
`Instrs_ok2`/`Instr_ok2`/`Expr_ok2`, used below.

`Val_ok_store`, which current Rocq no
longer has and which nothing used, has been deleted.
-/

namespace TLC

/-- Rocq `wasm.v:107` `holds_upto`. `holds_upto P n := Forall P (iotaN 0 n)`
    in Rocq — i.e. "P holds at every index strictly below `n`" — which is
    exactly `Forall P (List.range n)` here (`iotaN 0 n` ≈ `List.range n`).
    An `abbrev` (not `def`) so it unfolds transparently wherever a bare
    `Forall _ (List.range _)` fact (e.g. from `forall_range_lt`/
    `forall_range_refl` below) is needed in its place. -/
abbrev holds_upto (P : Nat → Prop) (n : Nat) : Prop := Forall P (List.range n)

/-- Bounds side-condition needed by `Extend_store`'s constructor: every index
    into `List.range l.length` is `< l.length`. No direct Rocq counterpart
    by name, but is exactly what Rocq's `holds_upto_lt_refl` (`extension_lemmas.v:1530`)
    states (not
    ported by name — pure proof-engineering plumbing, skipped per the same
    rationale as `helper_tactics.v`; the *fact* is used here via this
    equivalent). Reused from a prior Lean session's `Extension.lean`
    (`forall_range_lt`). -/
theorem forall_range_lt {α : Type} (l : List α) :
    Forall (fun a => a < l.length) (List.range l.length) := by
  intro a ha
  exact List.mem_range.mp ha

/-- Lifts a single-instance reflexivity fact, plus a well-formedness `Forall`
    over a list, to the `holds_upto` shape the `extend_*_refl` lemmas below
    (and `Extend_store`'s constructor) need. New plumbing, no Rocq
    counterpart by name. Reused from `Extension.lean` (`forall_range_refl`). -/
theorem forall_range_refl {α : Type} [Inhabited α] (l : List α) (P : α → Prop)
    (R : α → α → Prop) (hP : Forall P l) (hR : ∀ x, P x → R x x) :
    Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a ha
  have ha' : a < l.length := List.mem_range.mp ha
  have hmem : l[a]! ∈ l := by
    rw [getElem!_pos l a ha']
    exact List.getElem_mem ha'
  exact hR _ (hP _ hmem)

/-- As `forall_range_refl`, but for `Extend_eleminst`, which has no
    well-formedness side condition. Reused from `Extension.lean`
    (`forall_range_refl_noWf`). -/
theorem forall_range_refl_noWf {α : Type} [Inhabited α] (l : List α) (R : α → α → Prop)
    (hR : ∀ x, R x x) : Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a _
  exact hR _

/-! ## `Store_ok` inversion (extension_lemmas.v:42-218) -/

-- DELETED BECAUSE NOT USED
-- Rocq `extension_lemmas.v:20` `Val_ok_store` (`5b03ae067`; since removed upstream):
-- swap-invariance of `Val_ok` across the non-`FUNCS` store fields.

/-! ### Single-instance `*_ok` inversion helpers

    No Rocq counterparts: Rocq's `inversion`/`dependent induction` can invert
    a `*_ok` hypothesis in place even when its subject is a compound term
    such as `l[i]!` or `p.1`. Lean's `cases` cannot — dependent elimination
    needs the inductive's indices to be solvable, and an opaque `getElem!`
    application or a `Prod` projection is not. Stating each inversion as its
    own lemma over *bare variables* sidesteps that completely, and makes the
    `s_invert_*` / `minst_invert_elems` proofs below one-liners. This is the
    general fix for `obtain`/`cases`-on-opaque-index friction. -/

theorem funcinst_ok_invert (s : store) (f : funcinst) (t : functype) :
    Funcinst_ok s f t → ∃ minst v_func, f = funcinst.MKfuncinst t minst v_func := by
  intro h
  cases h with
  | mk_Funcinst_ok _ vmi vf _ _ _ _ _ _ _ => exact ⟨vmi, vf, rfl⟩

theorem globalinst_ok_invert (s : store) (g : globalinst) (t : globaltype) :
    Globalinst_ok s g t → ∃ v_mut v_vt v_v, g = globalinst.MKglobalinst t v_v ∧
      t = globaltype.mk_globaltype v_mut v_vt ∧ Val_ok s v_v v_vt := by
  intro h
  cases h with
  | mk_Globalinst_ok v_mut vt v_val _ hvok _ _ => exact ⟨v_mut, vt, v_val, rfl, rfl, hvok⟩

/-- `Limits_ok`'s own index embeds `OMap` (an `Option.map`), so `cases` on a
    `Limits_ok` hypothesis whose limits argument is already a *compound* term
    fails dependent elimination — it would have to invert a `match` on a
    variable. Stated here over a bare `lim` plus an equational premise (the
    standard Lean encoding of Rocq's `dependent induction`), which makes the
    elimination trivial and pushes the `Option` reasoning into an explicit
    injectivity step. No Rocq counterpart: Rocq's `inversion` handles this
    directly. -/
theorem limits_ok_invert (lim : limits) (k : Nat) (h : Limits_ok lim k) :
    ∀ (v_n : Nat) (m_opt : Option Nat),
      lim = limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN) →
      v_n ≤ k ∧ Forall (fun m' => v_n ≤ m' ∧ m' ≤ k) (Option.toList m_opt) := by
  cases h with
  | mk_Limits_ok n1 mo1 _ hle hforall _ =>
    intro v_n m_opt heq
    injection heq with h1 h2
    injection h1 with h1'
    subst h1'
    have hmo : mo1 = m_opt := by
      rcases mo1 with _ | a <;> rcases m_opt with _ | b <;> simp_all [OMap]
    subst hmo
    exact ⟨hle, hforall⟩

theorem meminst_ok_invert (s : store) (mi : meminst) (t : memtype) :
    Meminst_ok s mi t → ∃ (b_lst : List byte) (v_n : Nat) (v_m : Option Nat),
      mi = meminst.MKmeminst t b_lst ∧
      t = memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (v_m.map uN.mk_uN)) ∧
      v_n = b_lst.length / (64 * Ki) ∧
      Forall (fun m' => v_n ≤ m' ∧ m' ≤ 2 ^ 16) v_m.toList := by
  intro h
  cases h with
  | mk_Meminst_ok v_n m_opt b_lst hmtok hlen _ _ _ =>
    refine ⟨b_lst, v_n, m_opt, rfl, rfl, ?_, ?_⟩
    · rw [hlen]
      exact (Nat.mul_div_cancel v_n (by simp [Ki])).symm
    · cases hmtok with
      | mk_Memtype_ok _ hlimok _ => exact (limits_ok_invert _ _ hlimok v_n m_opt rfl).2

theorem tableinst_ok_invert (s : store) (tb : tableinst) (tbt : tabletype) :
    Tableinst_ok s tb tbt → ∃ (ref_lst : List ref) (v_m : Option Nat) (rt : reftype),
      tb = tableinst.MKtableinst tbt ref_lst ∧
      tbt = tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN ref_lst.length) (v_m.map uN.mk_uN)) rt ∧
      Tabletype_ok tbt ∧ Forall (fun r => Ref_ok s r rt) ref_lst := by
  intro h
  cases h with
  | mk_Tableinst_ok v_n m_opt rt ref_lst httok hrefs hlen _ _ _ =>
    subst hlen
    exact ⟨ref_lst, m_opt, rt, rfl, rfl, httok, hrefs⟩

theorem eleminst_ok_invert (s : store) (e : eleminst) (t : elemtype) :
    Eleminst_ok s e t →
    ∃ ref_lst, Forall (fun r => Ref_ok s r t) ref_lst ∧ e = eleminst.MKeleminst t ref_lst := by
  intro h
  cases h with
  | mk_Eleminst_ok _ ref_lst hrefs _ _ => exact ⟨ref_lst, hrefs, rfl⟩

/-- Rocq `extension_lemmas.v:42` `s_invert_funcs`.
    **Deviation (restores Rocq's meaning):** the conclusion carries the length equation
    explicitly. Rocq's inductive `Forall2` implies it; with Lean's zip-based `Forall₂`, the
    conclusion `∃ xs, Forall₂ P s.X xs` alone would be vacuous (`xs := []` satisfies it for every
    store). The generated `Store_ok` supplies the length. -/
theorem s_invert_funcs (s : store) : Store_ok s →
    ∃ fts, s.FUNCS.length = fts.length ∧
      Forall₂ (fun f t => ∃ minst v_func, f = funcinst.MKfuncinst t minst v_func) s.FUNCS fts := by
  intro h
  cases h with
  | mk_Store_ok gil gtl mil mtl til ttl fil ftl dil dtl eil etl _ _ _ _ _ _ hlf hf _ _ _ _ heq =>
    subst heq
    exact ⟨ftl, hlf, fun p hp => funcinst_ok_invert _ _ _ (hf p hp)⟩

/-- Rocq `extension_lemmas.v:74` `s_invert_globals`.
    **Deviation (restores Rocq's meaning):** the conclusion carries the length equation
    explicitly, as in `s_invert_funcs`. -/
theorem s_invert_globals (s : store) : Store_ok s →
    ∃ gts, s.GLOBALS.length = gts.length ∧
      Forall₂ (fun g t => ∃ v_mut v_vt v_v, g = globalinst.MKglobalinst t v_v ∧
      t = globaltype.mk_globaltype v_mut v_vt ∧ Val_ok s v_v v_vt) s.GLOBALS gts := by
  intro h
  cases h with
  | mk_Store_ok gil gtl mil mtl til ttl fil ftl dil dtl eil etl hlg hg _ _ _ _ _ _ _ _ _ _ heq =>
    subst heq
    exact ⟨gtl, hlg, fun p hp => globalinst_ok_invert _ _ _ (hg p hp)⟩

/-- Rocq `extension_lemmas.v:106` `s_invert_mems`. Encodes the memory page-count invariant
    and the hard cap `v_m ≤ 2^16` pages when a max is declared. Rocq's `v_m : option N` is a
    genuine option (no declared max is a valid memtype), threaded via
    `option_map`/`option_to_list`; here it is an `Option Nat`, with the cap conjunct scoped to
    `v_m.toList` (vacuous when `none`). Rocq writes the page count as `pagediv`
    (`extension_lemmas.v:21`, a `Q` division coerced to `N`), which has no Lean counterpart:
    the same `b_lst.length / (64 * Ki)` computation is inlined here.
    **Deviation (restores Rocq's meaning):** the conclusion carries the length equation
    explicitly, as in `s_invert_funcs`. -/
theorem s_invert_mems (s : store) : Store_ok s →
    ∃ mts, s.MEMS.length = mts.length ∧ Forall₂ (fun m t => ∃ (b_lst : List byte) (v_n : Nat) (v_m : Option Nat),
      m = meminst.MKmeminst t b_lst ∧
      t = memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (v_m.map uN.mk_uN)) ∧
      v_n = b_lst.length / (64 * Ki) ∧ Forall (fun m' => v_n ≤ m' ∧ m' ≤ 2 ^ 16) v_m.toList) s.MEMS mts := by
  intro h
  cases h with
  | mk_Store_ok gil gtl mil mtl til ttl fil ftl dil dtl eil etl _ _ hlm hm _ _ _ _ _ _ _ _ heq =>
    subst heq
    exact ⟨mtl, hlm, fun p hp => meminst_ok_invert _ _ _ (hm p hp)⟩

/-- Rocq `extension_lemmas.v:175` `s_invert_tables`. As in `s_invert_mems`, the declared
    table-size max is a genuine `Option` (here `Option Nat`), as in Rocq.
    **Deviation (restores Rocq's meaning):** the conclusion carries the length equation
    explicitly, as in `s_invert_funcs`. -/
theorem s_invert_tables (s : store) : Store_ok s →
    ∃ tbts, s.TABLES.length = tbts.length ∧ Forall₂ (fun tb tbt => ∃ (ref_lst : List ref) (v_m : Option Nat) (rt : reftype),
      tb = tableinst.MKtableinst tbt ref_lst ∧
      tbt = tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN ref_lst.length) (v_m.map uN.mk_uN)) rt ∧
      Tabletype_ok tbt ∧ Forall (fun r => Ref_ok s r rt) ref_lst) s.TABLES tbts := by
  intro h
  cases h with
  | mk_Store_ok gil gtl mil mtl til ttl fil ftl dil dtl eil etl _ _ _ _ hlt ht _ _ _ _ _ _ heq =>
    subst heq
    exact ⟨ttl, hlt, fun p hp => tableinst_ok_invert _ _ _ (ht p hp)⟩

/-! ## `Extend_store` component-wise inversion (extension_lemmas.v:219-284) -/

/-- Rocq `extension_lemmas.v:219` `se_invert_funcs`. Takes two `holds_upto`
    bound-hypotheses directly and concludes with a `holds_upto`-indexed pointwise fact. -/
theorem se_invert_funcs (s s' : store) : Extend_store s s' →
    -- TODO FROM USER: I think the point of this relatively strange premise
    -- format was to follow the format of `Extend_store` plus all its generator
    -- artifacts; we might want to make it follow even closer.
    holds_upto (fun a => a < s.FUNCS.length) s.FUNCS.length →
    holds_upto (fun a => a < s'.FUNCS.length) s.FUNCS.length →
    holds_upto (fun a => Extend_funcinst (s.FUNCS[a]!) (s'.FUNCS[a]!)) s.FUNCS.length := by
  intro h _ _
  cases h with
  | mk_Extend_store _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ => exact h

/-- Rocq `extension_lemmas.v:230` `se_invert_tables`, shaped as `se_invert_funcs`. -/
theorem se_invert_tables (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.TABLES.length) s.TABLES.length →
    holds_upto (fun a => a < s'.TABLES.length) s.TABLES.length →
    holds_upto (fun a => Extend_tableinst (s.TABLES[a]!) (s'.TABLES[a]!)) s.TABLES.length := by
  intro h _ _
  cases h with
  | mk_Extend_store _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ _ => exact h

/-- Rocq `extension_lemmas.v:241` `se_invert_mems`, shaped as `se_invert_funcs`. -/
theorem se_invert_mems (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.MEMS.length) s.MEMS.length →
    holds_upto (fun a => a < s'.MEMS.length) s.MEMS.length →
    holds_upto (fun a => Extend_meminst (s.MEMS[a]!) (s'.MEMS[a]!)) s.MEMS.length := by
  intro h _ _
  cases h with
  | mk_Extend_store _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact h

/-- Rocq `extension_lemmas.v:252` `se_invert_store_globals`, shaped as `se_invert_funcs`. -/
theorem se_invert_store_globals (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.GLOBALS.length) s.GLOBALS.length →
    holds_upto (fun a => a < s'.GLOBALS.length) s.GLOBALS.length →
    holds_upto (fun a => Extend_globalinst (s.GLOBALS[a]!) (s'.GLOBALS[a]!)) s.GLOBALS.length := by
  intro h _ _
  cases h with
  | mk_Extend_store _ _ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact h

/-- Rocq `extension_lemmas.v:263` `se_invert_elems`, shaped as `se_invert_funcs`. -/
theorem se_invert_elems (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.ELEMS.length) s.ELEMS.length →
    holds_upto (fun a => a < s'.ELEMS.length) s.ELEMS.length →
    holds_upto (fun a => Extend_eleminst (s.ELEMS[a]!) (s'.ELEMS[a]!)) s.ELEMS.length := by
  intro h _ _
  cases h with
  | mk_Extend_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => exact h

/-- Rocq `extension_lemmas.v:274` `se_invert_datas`, shaped as `se_invert_funcs`. -/
theorem se_invert_datas (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.DATAS.length) s.DATAS.length →
    holds_upto (fun a => a < s'.DATAS.length) s.DATAS.length →
    holds_upto (fun a => Extend_datainst (s.DATAS[a]!) (s'.DATAS[a]!)) s.DATAS.length := by
  intro h _ _
  cases h with
  | mk_Extend_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ => exact h

/-! ## Subtyping-of-externtypes cluster (extension_lemmas.v:285-411). `Limits_sub`/
    `Externtype_sub` etc. are generated inductives in `wasm2.0.lean`, confirmed
    field-for-field against Rocq. -/

/-- Rocq `extension_lemmas.v:285` `limits_sub_refl`. -/
theorem limits_sub_refl (lim : limits) : wf_limits lim → Limits_sub lim lim := by
  intro h
  obtain ⟨v_u32, u32_opt⟩ := lim
  obtain ⟨v_n⟩ := v_u32
  rcases u32_opt with _ | m
  · exact Limits_sub.eps v_n v_n (Nat.le_refl v_n) h h
  · obtain ⟨m'⟩ := m
    refine Limits_sub.max v_n m' v_n (some m') (Nat.le_refl v_n) ?_ h h
    intro x hx
    simp only [Option.toList, List.mem_singleton] at hx
    rw [hx]

/-- Rocq `extension_lemmas.v:306` `limits_sub_trans`. -/
theorem limits_sub_trans (lim lim' lim'' : limits) :
    Limits_sub lim lim' → Limits_sub lim' lim'' → Limits_sub lim lim'' := by
  intro h1 h2
  cases h1 with
  | eps n_1 n_2 hge1 hwf1 _ =>
    cases h2 with
    | eps _ n_3 hge2 _ hwf2' =>
      exact Limits_sub.eps n_1 n_3 (Nat.le_trans hge2 hge1) hwf1 hwf2'
  | max n_1 m_1 n_2 m_2_opt hge1 hforall1 hwf1 _ =>
    rcases m_2_opt with _ | m_2
    · cases h2 with
      | eps _ n_3 hge2 _ hwf2' =>
        exact Limits_sub.max n_1 m_1 n_3 none (Nat.le_trans hge2 hge1)
          (fun x hx => absurd hx (by simp [Option.toList])) hwf1 hwf2'
    · cases h2 with
      | max _ _ n_3 m_3_opt hge2 hforall2 _ hwf2' =>
        refine Limits_sub.max n_1 m_1 n_3 m_3_opt (Nat.le_trans hge2 hge1) ?_ hwf1 hwf2'
        intro x hx
        have hm2x := hforall2 x hx
        have hm1m2 := hforall1 m_2 (by simp [Option.toList])
        exact Nat.le_trans hm1m2 hm2x

/-- Rocq `extension_lemmas.v:343` `externtype_sub_refl`. -/
theorem externtype_sub_refl (xt : externtype) : wf_externtype xt → Externtype_sub xt xt := by
  intro h
  cases xt with
  | FUNC ft => exact Externtype_sub.func ft ft (Functype_sub.mk_Functype_sub ft) h h
  | GLOBAL gt => exact Externtype_sub.global gt gt (Globaltype_sub.mk_Globaltype_sub gt) h h
  | TABLE tt =>
    cases h with
    | externtype_case_2 _ hwftt =>
      obtain ⟨lim, rt⟩ := tt
      cases hwftt with
      | tabletype_case_0 _ _ hwflim =>
        exact Externtype_sub.table (tabletype.mk_tabletype lim rt) (tabletype.mk_tabletype lim rt)
          (Tabletype_sub.mk_Tabletype_sub lim rt lim (limits_sub_refl lim hwflim)
            (wf_tabletype.tabletype_case_0 lim rt hwflim) (wf_tabletype.tabletype_case_0 lim rt hwflim))
          (wf_externtype.externtype_case_2 (tabletype.mk_tabletype lim rt) (wf_tabletype.tabletype_case_0 lim rt hwflim))
          (wf_externtype.externtype_case_2 (tabletype.mk_tabletype lim rt) (wf_tabletype.tabletype_case_0 lim rt hwflim))
  | MEM mt =>
    cases h with
    | externtype_case_3 _ hwfmt =>
      obtain ⟨lim⟩ := mt
      cases hwfmt with
      | memtype_case_0 _ hwflim =>
        exact Externtype_sub.mem (memtype.PAGE lim) (memtype.PAGE lim)
          (Memtype_sub.mk_Memtype_sub lim lim (limits_sub_refl lim hwflim)
            (wf_memtype.memtype_case_0 lim hwflim) (wf_memtype.memtype_case_0 lim hwflim))
          (wf_externtype.externtype_case_3 (memtype.PAGE lim) (wf_memtype.memtype_case_0 lim hwflim))
          (wf_externtype.externtype_case_3 (memtype.PAGE lim) (wf_memtype.memtype_case_0 lim hwflim))

/-- Rocq `extension_lemmas.v:363` `externtype_sub_trans`. -/
theorem externtype_sub_trans (xt xt' xt'' : externtype) :
    Externtype_sub xt xt' → Externtype_sub xt' xt'' → Externtype_sub xt xt'' := by
  intro h1 h2
  cases xt' with
  | FUNC ft' =>
    cases h1 with
    | func ft _ hsub1 hwf1 _ =>
      cases h2 with
      | func _ ft'' hsub2 _ hwf2' =>
        have e1 : ft = ft' := by cases hsub1; rfl
        have e2 : ft' = ft'' := by cases hsub2; rfl
        have e3 : ft = ft'' := e1.trans e2
        rw [e3] at hwf1 ⊢
        exact Externtype_sub.func ft'' ft'' (Functype_sub.mk_Functype_sub ft'') hwf1 hwf1
  | GLOBAL gt' =>
    cases h1 with
    | global gt _ hsub1 hwf1 _ =>
      cases h2 with
      | global _ gt'' hsub2 _ hwf2' =>
        have e1 : gt = gt' := by cases hsub1; rfl
        have e2 : gt' = gt'' := by cases hsub2; rfl
        have e3 : gt = gt'' := e1.trans e2
        rw [e3] at hwf1 ⊢
        exact Externtype_sub.global gt'' gt'' (Globaltype_sub.mk_Globaltype_sub gt'') hwf1 hwf1
  | TABLE tt' =>
    cases h1 with
    | table tt _ hsub1 hwf1 _ =>
      cases h2 with
      | table _ tt'' hsub2 _ hwf2' =>
        cases hsub1 with
        | mk_Tabletype_sub lim1 rt lim2 hlimsub1 hwftt1 _ =>
          cases hsub2 with
          | mk_Tabletype_sub _ _ lim3 hlimsub2 _ hwftt2' =>
            exact Externtype_sub.table (tabletype.mk_tabletype lim1 rt) (tabletype.mk_tabletype lim3 rt)
              (Tabletype_sub.mk_Tabletype_sub lim1 rt lim3 (limits_sub_trans lim1 lim2 lim3 hlimsub1 hlimsub2) hwftt1 hwftt2')
              hwf1 (wf_externtype.externtype_case_2 (tabletype.mk_tabletype lim3 rt) hwftt2')
  | MEM mt' =>
    cases h1 with
    | mem mt _ hsub1 hwf1 _ =>
      cases h2 with
      | mem _ mt'' hsub2 _ hwf2' =>
        cases hsub1 with
        | mk_Memtype_sub lim1 lim2 hlimsub1 hwfmt1 _ =>
          cases hsub2 with
          | mk_Memtype_sub _ lim3 hlimsub2 _ hwfmt2' =>
            exact Externtype_sub.mem (memtype.PAGE lim1) (memtype.PAGE lim3)
              (Memtype_sub.mk_Memtype_sub lim1 lim3 (limits_sub_trans lim1 lim2 lim3 hlimsub1 hlimsub2) hwfmt1 hwfmt2')
              hwf1 (wf_externtype.externtype_case_3 (memtype.PAGE lim3) hwfmt2')

/-- Rocq `extension_lemmas.v:394` `externtype_global_eq`. `Globaltype_sub` in
    `wasm2.0.lean` is trivial (`Globaltype_sub gt gt` only), so
    `Externtype_sub (GLOBAL gt) (GLOBAL gt')` collapses to `gt = gt'`. -/
theorem externtype_global_eq (gt gt' : globaltype) :
    Externtype_sub (externtype.GLOBAL gt) (externtype.GLOBAL gt') → gt = gt' := by
  intro h
  cases h with
  | global _ _ hsub _ _ => cases hsub; rfl

/-- Rocq `extension_lemmas.v:403` `externtype_func_eq`. `Functype_sub` in
    `wasm2.0.lean` is likewise trivial, so this collapses to `ft = ft'`. -/
theorem externtype_func_eq (ft ft' : functype) :
    Externtype_sub (externtype.FUNC ft) (externtype.FUNC ft') → ft = ft' := by
  intro h
  cases h with
  | func _ _ hsub _ _ => cases hsub; rfl

/-! ## `Externaddr_ok` chain-peeling inversion ("Template C")

    Rocq `extension_lemmas.v:1065-1160`: `Externaddr_invert_funcs`/`_tables`/
    `_mems`/`_globals`. `Extend_store_ref`,
    `minst_invert_funcs`/`_tables`/`_globals`/`_mems` and the whole
    `addrs_*_extension` family build on these four.

    Each one peels an arbitrarily-deep stack of `Externaddr_ok.sub`
    applications off a kind-specific `Externaddr_ok` derivation, bottoming
    out at the single kind-specific base constructor, and composes the
    accumulated subtyping steps with `externtype_sub_trans`. Rocq does this
    with `dependent induction HExt`; Lean's `induction` tactic refuses
    non-variable indices, so each is split into a `_aux` lemma stated over
    fully general indices plus equational premises (the standard Lean 4
    encoding of Rocq's `dependent induction`), with the public lemma
    instantiating it at `rfl`/`rfl`. That is a proof-method divergence only:
    the public signatures match Rocq's statements field for field. -/

private theorem Externaddr_invert_funcs_aux (s : store) (ea : externaddr) (xt0 : externtype)
    (h : Externaddr_ok s ea xt0) :
    ∀ (exta : addr) (ext : functype), ea = externaddr.FUNC exta → xt0 = externtype.FUNC ext →
    ∃ (xt : externtype) (v_funcinst : funcinst),
      exta < s.FUNCS.length ∧ lookup_total s.FUNCS exta = v_funcinst ∧
      xt = externtype.FUNC v_funcinst.TYPE ∧
      wf_externtype (externtype.FUNC v_funcinst.TYPE) ∧
      Externtype_sub xt (externtype.FUNC ext) := by
  induction h with
  | global _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | mem _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | table _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | func a fi hb hl _ hwfx =>
    intro exta ext hea hxt
    injection hea with ha
    injection hxt with ht
    subst ha
    subst ht
    exact ⟨externtype.FUNC fi.TYPE, fi, hb, hl, rfl, hwfx, externtype_sub_refl _ hwfx⟩
  | sub ea xt xt' _ hsub _ _ _ ih =>
    intro exta ext hea hxt
    cases hsub with
    | func ft1 ft2 hfsub hwf1 hwf2 =>
      injection hxt with ht
      subst ht
      obtain ⟨xt0, fi, hb, hl, hxteq, hwf, hsub0⟩ := ih exta ft1 hea rfl
      exact ⟨xt0, fi, hb, hl, hxteq, hwf,
        externtype_sub_trans _ _ _ hsub0 (Externtype_sub.func ft1 ft2 hfsub hwf1 hwf2)⟩
    | global _ _ _ _ _ => simp at hxt
    | table _ _ _ _ _ => simp at hxt
    | mem _ _ _ _ _ => simp at hxt

/-- Rocq `Externaddr_invert_funcs` (`extension_lemmas.v:1065`). -/
theorem Externaddr_invert_funcs (s : store) (exta : addr) (ext : functype) :
    Externaddr_ok s (externaddr.FUNC exta) (externtype.FUNC ext) →
    ∃ (xt : externtype) (v_funcinst : funcinst),
      exta < s.FUNCS.length ∧ lookup_total s.FUNCS exta = v_funcinst ∧
      xt = externtype.FUNC v_funcinst.TYPE ∧
      wf_externtype (externtype.FUNC v_funcinst.TYPE) ∧
      Externtype_sub xt (externtype.FUNC ext) :=
  fun h => Externaddr_invert_funcs_aux s _ _ h exta ext rfl rfl

private theorem Externaddr_invert_tables_aux (s : store) (ea : externaddr) (xt0 : externtype)
    (h : Externaddr_ok s ea xt0) :
    ∀ (exta : addr) (ext : tabletype), ea = externaddr.TABLE exta → xt0 = externtype.TABLE ext →
    ∃ (xt : externtype) (v_tableinst : tableinst),
      exta < s.TABLES.length ∧ lookup_total s.TABLES exta = v_tableinst ∧
      xt = externtype.TABLE v_tableinst.TYPE ∧
      wf_externtype (externtype.TABLE v_tableinst.TYPE) ∧
      Externtype_sub xt (externtype.TABLE ext) := by
  induction h with
  | global _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | mem _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | func _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | table a ti hb hl _ hwfx =>
    intro exta ext hea hxt
    injection hea with ha
    injection hxt with ht
    subst ha
    subst ht
    exact ⟨externtype.TABLE ti.TYPE, ti, hb, hl, rfl, hwfx, externtype_sub_refl _ hwfx⟩
  | sub ea xt xt' _ hsub _ _ _ ih =>
    intro exta ext hea hxt
    cases hsub with
    | table tt1 tt2 hfsub hwf1 hwf2 =>
      injection hxt with ht
      subst ht
      obtain ⟨xt0, ti, hb, hl, hxteq, hwf, hsub0⟩ := ih exta tt1 hea rfl
      exact ⟨xt0, ti, hb, hl, hxteq, hwf,
        externtype_sub_trans _ _ _ hsub0 (Externtype_sub.table tt1 tt2 hfsub hwf1 hwf2)⟩
    | global _ _ _ _ _ => simp at hxt
    | func _ _ _ _ _ => simp at hxt
    | mem _ _ _ _ _ => simp at hxt

/-- Rocq `Externaddr_invert_tables` (`extension_lemmas.v:1089`). -/
theorem Externaddr_invert_tables (s : store) (exta : addr) (ext : tabletype) :
    Externaddr_ok s (externaddr.TABLE exta) (externtype.TABLE ext) →
    ∃ (xt : externtype) (v_tableinst : tableinst),
      exta < s.TABLES.length ∧ lookup_total s.TABLES exta = v_tableinst ∧
      xt = externtype.TABLE v_tableinst.TYPE ∧
      wf_externtype (externtype.TABLE v_tableinst.TYPE) ∧
      Externtype_sub xt (externtype.TABLE ext) :=
  fun h => Externaddr_invert_tables_aux s _ _ h exta ext rfl rfl

private theorem Externaddr_invert_mems_aux (s : store) (ea : externaddr) (xt0 : externtype)
    (h : Externaddr_ok s ea xt0) :
    ∀ (exta : addr) (ext : memtype), ea = externaddr.MEM exta → xt0 = externtype.MEM ext →
    ∃ (xt : externtype) (v_meminst : meminst),
      exta < s.MEMS.length ∧ lookup_total s.MEMS exta = v_meminst ∧
      xt = externtype.MEM v_meminst.TYPE ∧
      wf_externtype (externtype.MEM v_meminst.TYPE) ∧
      Externtype_sub xt (externtype.MEM ext) := by
  induction h with
  | global _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | table _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | func _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | mem a mi hb hl _ hwfx =>
    intro exta ext hea hxt
    injection hea with ha
    injection hxt with ht
    subst ha
    subst ht
    exact ⟨externtype.MEM mi.TYPE, mi, hb, hl, rfl, hwfx, externtype_sub_refl _ hwfx⟩
  | sub ea xt xt' _ hsub _ _ _ ih =>
    intro exta ext hea hxt
    cases hsub with
    | mem mt1 mt2 hfsub hwf1 hwf2 =>
      injection hxt with ht
      subst ht
      obtain ⟨xt0, mi, hb, hl, hxteq, hwf, hsub0⟩ := ih exta mt1 hea rfl
      exact ⟨xt0, mi, hb, hl, hxteq, hwf,
        externtype_sub_trans _ _ _ hsub0 (Externtype_sub.mem mt1 mt2 hfsub hwf1 hwf2)⟩
    | global _ _ _ _ _ => simp at hxt
    | func _ _ _ _ _ => simp at hxt
    | table _ _ _ _ _ => simp at hxt

/-- Rocq `Externaddr_invert_mems` (`extension_lemmas.v:1113`). -/
theorem Externaddr_invert_mems (s : store) (exta : addr) (ext : memtype) :
    Externaddr_ok s (externaddr.MEM exta) (externtype.MEM ext) →
    ∃ (xt : externtype) (v_meminst : meminst),
      exta < s.MEMS.length ∧ lookup_total s.MEMS exta = v_meminst ∧
      xt = externtype.MEM v_meminst.TYPE ∧
      wf_externtype (externtype.MEM v_meminst.TYPE) ∧
      Externtype_sub xt (externtype.MEM ext) :=
  fun h => Externaddr_invert_mems_aux s _ _ h exta ext rfl rfl

private theorem Externaddr_invert_globals_aux (s : store) (ea : externaddr) (xt0 : externtype)
    (h : Externaddr_ok s ea xt0) :
    ∀ (exta : addr) (ext : globaltype), ea = externaddr.GLOBAL exta → xt0 = externtype.GLOBAL ext →
    ∃ (xt : externtype) (v_globalinst : globalinst),
      exta < s.GLOBALS.length ∧ lookup_total s.GLOBALS exta = v_globalinst ∧
      xt = externtype.GLOBAL v_globalinst.TYPE ∧
      wf_externtype (externtype.GLOBAL v_globalinst.TYPE) ∧
      Externtype_sub xt (externtype.GLOBAL ext) := by
  induction h with
  | mem _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | table _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | func _ _ _ _ _ _ => intro _ _ hea _; simp at hea
  | global a gi hb hl _ hwfx =>
    intro exta ext hea hxt
    injection hea with ha
    injection hxt with ht
    subst ha
    subst ht
    exact ⟨externtype.GLOBAL gi.TYPE, gi, hb, hl, rfl, hwfx, externtype_sub_refl _ hwfx⟩
  | sub ea xt xt' _ hsub _ _ _ ih =>
    intro exta ext hea hxt
    cases hsub with
    | global gt1 gt2 hfsub hwf1 hwf2 =>
      injection hxt with ht
      subst ht
      obtain ⟨xt0, gi, hb, hl, hxteq, hwf, hsub0⟩ := ih exta gt1 hea rfl
      exact ⟨xt0, gi, hb, hl, hxteq, hwf,
        externtype_sub_trans _ _ _ hsub0 (Externtype_sub.global gt1 gt2 hfsub hwf1 hwf2)⟩
    | mem _ _ _ _ _ => simp at hxt
    | func _ _ _ _ _ => simp at hxt
    | table _ _ _ _ _ => simp at hxt

/-- Rocq `Externaddr_invert_globals` (`extension_lemmas.v:1137`). -/
theorem Externaddr_invert_globals (s : store) (exta : addr) (ext : globaltype) :
    Externaddr_ok s (externaddr.GLOBAL exta) (externtype.GLOBAL ext) →
    ∃ (xt : externtype) (v_globalinst : globalinst),
      exta < s.GLOBALS.length ∧ lookup_total s.GLOBALS exta = v_globalinst ∧
      xt = externtype.GLOBAL v_globalinst.TYPE ∧
      wf_externtype (externtype.GLOBAL v_globalinst.TYPE) ∧
      Externtype_sub xt (externtype.GLOBAL ext) :=
  fun h => Externaddr_invert_globals_aux s _ _ h exta ext rfl rfl

/-! ## `Moduleinst_ok`/`inst_match` interaction with store contents
    (extension_lemmas.v:412-627). `minst_invert_funcs`/`_tables`/`_globals`/`_mems` relate the
    store's types to the context's by the unified `Externtype_sub` relation, as in Rocq. -/

/-- Rocq `extension_lemmas.v:412` `minst_invert_functypes`. -/
theorem minst_invert_functypes (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' → C'.TYPES = minst.TYPES := by
  intro h hmatch
  cases h
  exact hmatch.1.symm

/-- Rocq `extension_lemmas.v:421` `minst_invert_funcs`. Uses
    `Externtype_sub (FUNC ft') (FUNC ft)`.
    **Note:** Rocq's conclusion is an inductive `Forall2`, which also gives
    `|minst.X| = |C'.X|`; the zip-based `Forall₂` here does not. Callers obtain the length from
    `Moduleinst_ok_lengths` (TypePreservation.lean) together with `inst_match`. -/
theorem minst_invert_funcs (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun fa ft => ∃ minst1 v_func ft', fa < v_S.FUNCS.length ∧
      lookup_total v_S.FUNCS fa = funcinst.MKfuncinst ft' minst1 v_func ∧
      Externtype_sub (externtype.FUNC ft') (externtype.FUNC ft)) minst.FUNCS C'.FUNCS := by
  intro hok hmatch
  cases hok with
  | mk_Moduleinst_ok ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl _ _ _ _ h5 =>
    rw [← hmatch.2.1]
    intro p hp
    obtain ⟨_, fi, hab, hlk, hxt, _, hsub⟩ := Externaddr_invert_funcs v_S p.1 p.2 (h5 p hp)
    subst hxt
    obtain ⟨ft', minst1, vfunc⟩ := fi
    exact ⟨minst1, vfunc, ft', hab, hlk, hsub⟩

/-- Rocq `extension_lemmas.v:456` `minst_invert_tables`. Uses
    `Externtype_sub (TABLE tbt') (TABLE tbt)` (which itself
    unfolds to a `Limits_sub` premise plus matching `wf_tabletype` facts,
    per `wasm2.0.lean`'s `Tabletype_sub`/`Externtype_sub` definitions).
    **Note:** Rocq's conclusion is an inductive `Forall2`, which also gives
    `|minst.X| = |C'.X|`; the zip-based `Forall₂` here does not. Callers obtain the length from
    `Moduleinst_ok_lengths` (TypePreservation.lean) together with `inst_match`. -/
theorem minst_invert_tables (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun tba tbt => ∃ tbr tbt', tba < v_S.TABLES.length ∧
      lookup_total v_S.TABLES tba = tableinst.MKtableinst tbt' tbr ∧
      Externtype_sub (externtype.TABLE tbt') (externtype.TABLE tbt)) minst.TABLES C'.TABLES := by
  intro hok hmatch
  cases hok with
  | mk_Moduleinst_ok ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl _ _ _ _ _ _ _ _ h9 =>
    rw [← hmatch.2.2.2.1]
    intro p hp
    obtain ⟨_, ti, hab, hlk, hxt, _, hsub⟩ := Externaddr_invert_tables v_S p.1 p.2 (h9 p hp)
    subst hxt
    obtain ⟨tbt', tbr⟩ := ti
    exact ⟨tbr, tbt', hab, hlk, hsub⟩

/-- Rocq `extension_lemmas.v:493` `minst_invert_globals`. Uses
    `Externtype_sub (GLOBAL gt') (GLOBAL gt)`.
    **Note:** Rocq's conclusion is an inductive `Forall2`, which also gives
    `|minst.X| = |C'.X|`; the zip-based `Forall₂` here does not. Callers obtain the length from
    `Moduleinst_ok_lengths` (TypePreservation.lean) together with `inst_match`. -/
theorem minst_invert_globals (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ga gt => ∃ gt' v_val, ga < v_S.GLOBALS.length ∧
      lookup_total v_S.GLOBALS ga = globalinst.MKglobalinst gt' v_val ∧
      Externtype_sub (externtype.GLOBAL gt') (externtype.GLOBAL gt)) minst.GLOBALS C'.GLOBALS := by
  intro hok hmatch
  cases hok with
  | mk_Moduleinst_ok ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl _ _ h3 =>
    rw [← hmatch.2.2.1]
    intro p hp
    obtain ⟨_, gi, hab, hlk, hxt, _, hsub⟩ := Externaddr_invert_globals v_S p.1 p.2 (h3 p hp)
    subst hxt
    obtain ⟨gt', v_val⟩ := gi
    exact ⟨gt', v_val, hab, hlk, hsub⟩

/-- Rocq `extension_lemmas.v:529` `minst_invert_mems`. Uses
    `Externtype_sub (MEM v_mt) (MEM mt)`.
    **Note:** Rocq's conclusion is an inductive `Forall2`, which also gives
    `|minst.X| = |C'.X|`; the zip-based `Forall₂` here does not. Callers obtain the length from
    `Moduleinst_ok_lengths` (TypePreservation.lean) together with `inst_match`. -/
theorem minst_invert_mems (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ma mt => ∃ v_mt b_lst, ma < v_S.MEMS.length ∧
      lookup_total v_S.MEMS ma = meminst.MKmeminst v_mt b_lst ∧
      Externtype_sub (externtype.MEM v_mt) (externtype.MEM mt)) minst.MEMS C'.MEMS := by
  intro hok hmatch
  cases hok with
  | mk_Moduleinst_ok ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl _ _ _ _ _ _ h7 =>
    rw [← hmatch.2.2.2.2.1]
    intro p hp
    obtain ⟨_, mi, hab, hlk, hxt, _, hsub⟩ := Externaddr_invert_mems v_S p.1 p.2 (h7 p hp)
    subst hxt
    obtain ⟨v_mt, b_lst⟩ := mi
    exact ⟨v_mt, b_lst, hab, hlk, hsub⟩

/-- Rocq `extension_lemmas.v:564` `minst_invert_elems`.
    `Eleminst_ok v_S (v_S.ELEMS[p.1]!) p.2` cannot be
    inverted in place — both its subject and its type index are opaque terms
    (`getElem!` / `Prod` projections), which defeats dependent elimination
    under `cases`, `obtain` and `set`+`clear_value` alike — so the proof uses
    `eleminst_ok_invert` above, which does the inversion once, in a lemma whose
    arguments are bare variables.
    **Note:** Rocq's conclusion is an inductive `Forall2`, which also gives
    `|minst.X| = |C'.X|`; the zip-based `Forall₂` here does not. Callers obtain the length from
    `Moduleinst_ok_lengths` (TypePreservation.lean) together with `inst_match`. -/
theorem minst_invert_elems (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ea et => ∃ ref_lst, ea < v_S.ELEMS.length ∧ Forall (fun r => Ref_ok v_S r et) ref_lst ∧
      lookup_total v_S.ELEMS ea = eleminst.MKeleminst et ref_lst) minst.ELEMS C'.ELEMS := by
  intro hok hmatch
  cases hok with
  | mk_Moduleinst_ok ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ h15 h16 =>
    rw [← hmatch.2.2.2.2.2.1]
    intro p hp
    obtain ⟨ref_lst, hrefs, heq⟩ := eleminst_ok_invert v_S _ p.2 (h16 p hp)
    exact ⟨ref_lst, h15 p.1 (List.of_mem_zip hp).1, hrefs, heq⟩

/-- Rocq `extension_lemmas.v:596` `minst_invert_datas`. -/
theorem minst_invert_datas (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    minst.DATAS.length = C'.DATAS.length ∧
      Forall (fun da => ∃ b_lst, da < v_S.DATAS.length ∧ lookup_total v_S.DATAS da = datainst.MKdatainst b_lst)
        minst.DATAS := by
  intro hok hmatch
  cases hok with
  | mk_Moduleinst_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlen hbound _ _ _ _ _ _ _ _ _ _ =>
    refine ⟨?_, ?_⟩
    · rw [hlen]; exact congrArg List.length hmatch.2.2.2.2.2.2
    · intro da hda
      rcases hdv : v_S.DATAS[da]! with ⟨b_lst⟩
      exact ⟨b_lst, hbound da hda, hdv⟩

/-! ## Misc lookup/inversion lemmas (extension_lemmas.v:837-925) -/

/-- Every in-range store global has a `Globalinst_ok` derivation. Rocq reads
    this off `invert_storeok` plus `Forall2_size`; here it needs
    `HelperLemmas.Forall2_nth_of_length` because `Forall₂` is zip-based. -/
theorem Store_ok_globalinst (s : store) (i : Nat) (hi : i < s.GLOBALS.length) :
    Store_ok s → ∃ gt, Globalinst_ok s (s.GLOBALS[i]!) gt := by
  intro h
  cases h with
  | mk_Store_ok gil gtl _ _ _ _ _ _ _ _ _ _ hlen hg _ _ _ _ _ _ _ _ _ _ heq =>
    subst heq
    exact ⟨gtl[i]!, Forall2_nth_of_length gil gtl hg hlen i hi⟩

/-- Rocq `extension_lemmas.v:837` `lookup_global`. -/
theorem lookup_global (v_a : Nat) (v_C v_C' : context) (v_mut : «mut») (v_vt : valtype) (v_S : store) (minst : moduleinst) :
    v_a < v_C'.GLOBALS.length → lookup_total v_C'.GLOBALS v_a = globaltype.mk_globaltype v_mut v_vt →
    Moduleinst_ok v_S minst v_C → inst_match v_C v_C' → Store_ok v_S →
    Val_ok v_S (lookup_total v_S.GLOBALS (lookup_total minst.GLOBALS v_a)).VALUE v_vt := by
  intro hlt hlk hmi him hsok
  -- the module instance's globals list and the context's globaltype list agree in length
  have hlen : minst.GLOBALS.length = v_C'.GLOBALS.length := by
    rw [← him.2.2.1]
    cases hmi with
    | mk_Moduleinst_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2 => exact h2
  -- so the global address at index `v_a` points at a store global of the declared type
  obtain ⟨gt', v_val, hb, hlk2, hsub⟩ :=
    Forall2_nth_of_length minst.GLOBALS v_C'.GLOBALS (minst_invert_globals v_S minst v_C v_C' hmi him)
      hlen v_a (by rw [hlen]; exact hlt)
  simp only [lookup_total] at hlk hlk2 ⊢
  have hgt' : gt' = globaltype.mk_globaltype v_mut v_vt := by
    rw [externtype_global_eq gt' _ hsub]; exact hlk
  -- and `Store_ok` says that store global is well-typed, hence so is its value
  obtain ⟨gt, hgok⟩ := Store_ok_globalinst v_S _ hb hsok
  obtain ⟨_, vt', v_v, he1, he2, hvok⟩ := globalinst_ok_invert v_S _ gt hgok
  rw [hlk2] at he1
  injection he1 with hA hB
  rw [hlk2]
  show Val_ok v_S v_val v_vt
  rw [hB]
  have hgteq : gt = globaltype.mk_globaltype v_mut v_vt := by rw [← hA]; exact hgt'
  rw [hgteq] at he2
  injection he2 with _ hvt
  rw [hvt]
  exact hvok

/-- Rocq `extension_lemmas.v:870` `bt_inversion`. The block type elaboration `fun_blocktype`
    agrees with the declarative `Blocktype_ok` relation's chosen functype.
    **Note:** Rocq's premise is the equation `fun_blocktype (mk_state v_S r_v_f) b_lstt =
    (bt1 :-> bt2)`; `fun_blocktype` is a relation here (`sideconditions_on_defs`), so the premise
    is its witness `fun_blocktype (state.mk_state v_S r_v_f) b_lstt (mkFunctype bt1 bt2)`. -/
theorem bt_inversion (v_S : store) (v_C v_C' : context) (r_v_f : frame) (b_lstt : blocktype)
    (ts1 ts2 bt1 bt2 : List valtype) :
    Moduleinst_ok v_S r_v_f.MODULE v_C → Blocktype_ok v_C' b_lstt (mkFunctype ts1 ts2) →
    fun_blocktype (state.mk_state v_S r_v_f) b_lstt (mkFunctype bt1 bt2) → inst_match v_C v_C' →
    ts1 = bt1 ∧ ts2 = bt2 := by
  intro hmi hb hf him
  cases hb with
  | valtype vopt _ _ =>
    rcases vopt with _ | t <;> cases hf <;> simp_all
  | typeidx x _ _ _ hlk _ _ =>
    have hty : v_C'.TYPES = r_v_f.MODULE.TYPES :=
      minst_invert_functypes v_S r_v_f.MODULE v_C v_C' hmi him
    cases hf with
    | fun_blocktype_case_2 _ _ ht =>
      have hf := (fun_type_inv ht).2
      simp only [mkFunctype] at hf
      rw [hty] at hlk
      have heq := hlk.symm.trans hf.symm
      injection heq with h1 h2
      injection h1 with h1'
      injection h2 with h2'
      exact ⟨h1', h2'⟩

/-- Rocq `extension_lemmas.v:897` `tc_func_reference2`. -/
theorem tc_func_reference2 (v_S : store) (v_C : context) (minst : moduleinst) (idx : Nat) (tf : functype) (v_type : funcinst) :
    lookup_total minst.TYPES idx = v_type.TYPE → Moduleinst_ok v_S minst v_C →
    lookup_total v_C.TYPES idx = tf → tf = v_type.TYPE := by
  intro heq hok htf
  cases hok
  rw [← heq, ← htf]

/-- Rocq `extension_lemmas.v:908` `store_typed_exterval_types`. -/
theorem store_typed_exterval_types (v_S : store) (v_f : funcinst) (v_a : Nat) :
    v_a < v_S.FUNCS.length → lookup_total v_S.FUNCS v_a = v_f → Store_ok v_S →
    Externaddr_ok v_S (externaddr.FUNC v_a) (externtype.FUNC v_f.TYPE) := by
  intro ha heq hstore
  cases hstore with
  | mk_Store_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwfS _ _ _ =>
    exact Externaddr_ok.func v_S v_a v_f ha heq hwfS (wf_externtype.externtype_case_0 v_f.TYPE)

/-! ## Extension relations are reflexive per store-component kind
    (extension_lemmas.v:926-1005 for the single-instance `extend_*_refl_0` lemmas,
    1538-1626 for the list-lifted `extend_*_refl` lemmas, which are stated
    store-specifically with a `holds_upto` conclusion.) -/

/-- Rocq `extension_lemmas.v:997` `extend_funcinst_refl_0`. Takes `wf_funcinst`, which
    `Extend_funcinst`'s constructor requires (see the naming note above). Proof
    reused from a prior Lean session's `Extension.lean` (`extend_funcinst_refl`). -/
theorem extend_funcinst_refl_0 {f : funcinst} (h : wf_funcinst f) : Extend_funcinst f f := by
  obtain ⟨ft, mm, fc⟩ := f
  exact Extend_funcinst.mk_Extend_funcinst ft mm fc h

/-- Rocq `extension_lemmas.v:1592` `extend_func_refl`: store-specific, with a `holds_upto`
    conclusion. Proved directly from
    `forall_range_refl` above, which already produces exactly this
    `holds_upto`-shaped fact (`holds_upto` unfolds to `Forall _ (List.range _)`). -/
theorem extend_func_refl (s : store) (h : Forall wf_funcinst s.FUNCS) :
    holds_upto (fun n => Extend_funcinst (s.FUNCS[n]!) (s.FUNCS[n]!)) s.FUNCS.length :=
  forall_range_refl s.FUNCS wf_funcinst Extend_funcinst h (fun x hx => extend_funcinst_refl_0 hx)

/-- Rocq `extension_lemmas.v:957` `extend_tableinst_refl_0`. Proof reused from `Extension.lean`
    (`extend_tableinst_refl`). -/
theorem extend_tableinst_refl_0 {t : tableinst} (h : wf_tableinst t) : Extend_tableinst t t := by
  obtain ⟨ty, refs⟩ := t
  obtain ⟨lim, rt⟩ := ty
  obtain ⟨v_u32, u32_opt⟩ := lim
  obtain ⟨v_n⟩ := v_u32
  rcases u32_opt with _ | u32opt
  · exact Extend_tableinst.mk_Extend_tableinst v_n none rt refs v_n refs
      (Nat.le_refl v_n) (Nat.le_refl refs.length) h h
  · obtain ⟨n'⟩ := u32opt
    exact Extend_tableinst.mk_Extend_tableinst v_n (some n') rt refs v_n refs
      (Nat.le_refl v_n) (Nat.le_refl refs.length) h h

/-- Rocq `extension_lemmas.v:1550` `extend_table_refl`, shaped as `extend_func_refl`. -/
theorem extend_table_refl (s : store) (h : Forall wf_tableinst s.TABLES) :
    holds_upto (fun n => Extend_tableinst (s.TABLES[n]!) (s.TABLES[n]!)) s.TABLES.length :=
  forall_range_refl s.TABLES wf_tableinst Extend_tableinst h (fun x hx => extend_tableinst_refl_0 hx)

/-- Rocq `extension_lemmas.v:938` `extend_meminst_refl_0`. Proof reused from `Extension.lean`
    (`extend_meminst_refl`). -/
theorem extend_meminst_refl_0 {m : meminst} (h : wf_meminst m) : Extend_meminst m m := by
  obtain ⟨ty, bs⟩ := m
  obtain ⟨lim⟩ := ty
  obtain ⟨v_u32, u32_opt⟩ := lim
  obtain ⟨v_n⟩ := v_u32
  rcases u32_opt with _ | u32opt
  · exact Extend_meminst.mk_Extend_meminst v_n none bs v_n bs
      (Nat.le_refl v_n) (Nat.le_refl bs.length) h h
  · obtain ⟨n'⟩ := u32opt
    exact Extend_meminst.mk_Extend_meminst v_n (some n') bs v_n bs
      (Nat.le_refl v_n) (Nat.le_refl bs.length) h h

/-- A `meminst` whose `BYTES` are replaced by an at-least-as-long,
    well-formed buffer extends the original. Lean-only helper: no Rocq
    counterpart by name — Rocq rebuilds `Extend_meminst` inline at each use
    site, which its `inversion`/`econstructor` machinery makes cheap. Here the
    `Option`-shaped limits max has to be split explicitly to put the type into
    `Extend_meminst`'s expected `OMap`-applied form, so it is worth doing once.
    Used by `store_none_mem_extension`. -/
theorem extend_meminst_bytes (mi : meminst) (bs' : List byte)
    (hwf : wf_meminst mi) (hwfbs : Forall wf_byte bs')
    (hle : mi.BYTES.length ≤ bs'.length) : Extend_meminst mi { mi with BYTES := bs' } := by
  have hwfmt : wf_memtype mi.TYPE := by
    cases hwf with | meminst_case_ _ _ h _ => exact h
  have hwfnew : wf_meminst { mi with BYTES := bs' } := by
    cases hwf with | meminst_case_ _ _ h _ => exact wf_meminst.meminst_case_ _ bs' h hwfbs
  obtain ⟨mt, bs⟩ := mi
  cases hwfmt with
  | memtype_case_0 lim hwflim =>
    cases hwflim with
    | limits_case_0 u uo _ _ =>
      obtain ⟨nn⟩ := u
      rcases uo with _ | uu
      · exact Extend_meminst.mk_Extend_meminst nn none bs nn bs' (Nat.le_refl nn) hle hwf hwfnew
      · obtain ⟨mm⟩ := uu
        exact Extend_meminst.mk_Extend_meminst nn (some mm) bs nn bs' (Nat.le_refl nn) hle hwf hwfnew

/-- Rocq `extension_lemmas.v:1561` `extend_mem_refl`, shaped as `extend_func_refl`. -/
theorem extend_mem_refl (s : store) (h : Forall wf_meminst s.MEMS) :
    holds_upto (fun n => Extend_meminst (s.MEMS[n]!) (s.MEMS[n]!)) s.MEMS.length :=
  forall_range_refl s.MEMS wf_meminst Extend_meminst h (fun x hx => extend_meminst_refl_0 hx)

/-- Rocq `extension_lemmas.v:926` `extend_globalinst_refl_0`. Proof reused from `Extension.lean`
    (`extend_globalinst_refl`). -/
theorem extend_globalinst_refl_0 {g : globalinst} (h : wf_globalinst g) : Extend_globalinst g g := by
  obtain ⟨ty, v⟩ := g
  obtain ⟨v_mut, t⟩ := ty
  exact Extend_globalinst.mk_Extend_globalinst v_mut t v v (Or.inr rfl) h h

/-- Rocq `extension_lemmas.v:1538` `extend_global_refl`, shaped as `extend_func_refl`. -/
theorem extend_global_refl (s : store) (h : Forall wf_globalinst s.GLOBALS) :
    holds_upto (fun n => Extend_globalinst (s.GLOBALS[n]!) (s.GLOBALS[n]!)) s.GLOBALS.length :=
  forall_range_refl s.GLOBALS wf_globalinst Extend_globalinst h (fun x hx => extend_globalinst_refl_0 hx)

/-- Rocq `extension_lemmas.v:976` `extend_eleminst_refl_0` (`Extend_eleminst` has no `wf_*`
    premise, as in Rocq).
    Proof reused from `Extension.lean` (`extend_eleminst_refl`). -/
theorem extend_eleminst_refl_0 (e : eleminst) : Extend_eleminst e e := by
  obtain ⟨rt, refs⟩ := e
  exact Extend_eleminst.mk_Extend_eleminst rt refs refs (Or.inl rfl)

/-- Rocq `extension_lemmas.v:1572` `extend_elem_refl`, shaped as `extend_func_refl`; no `wf_*`
    premise, as in Rocq. -/
theorem extend_elem_refl (s : store) :
    holds_upto (fun n => Extend_eleminst (s.ELEMS[n]!) (s.ELEMS[n]!)) s.ELEMS.length :=
  forall_range_refl_noWf s.ELEMS Extend_eleminst extend_eleminst_refl_0

/-- Rocq `extension_lemmas.v:986` `extend_datainst_refl_0`. Proof reused from `Extension.lean`
    (`extend_datainst_refl`). -/
theorem extend_datainst_refl_0 {d : datainst} (h : wf_datainst d) : Extend_datainst d d := by
  obtain ⟨bs⟩ := d
  exact Extend_datainst.mk_Extend_datainst bs bs (Or.inl rfl) h h

/-- Rocq `extension_lemmas.v:1581` `extend_data_refl`, shaped as `extend_func_refl`. -/
theorem extend_data_refl (s : store) (h : Forall wf_datainst s.DATAS) :
    holds_upto (fun n => Extend_datainst (s.DATAS[n]!) (s.DATAS[n]!)) s.DATAS.length :=
  forall_range_refl s.DATAS wf_datainst Extend_datainst h (fun x hx => extend_datainst_refl_0 hx)

/-- Rocq `extension_lemmas.v:1603` `Extend_store_refl`.
    **No `Extend_store_trans` (transitivity) lemma exists in the Rocq file** —
    downstream preservation proofs
    re-derive extension facts per reduction step rather than composing two
    `Extend_store` proofs — so none is ported here either.
    Proof reused from a prior Lean session's `Extension.lean`
    (`extend_store_refl`); note it calls the single-instance `_refl_0` lemmas
    and `forall_range_refl` directly rather than routing through the
    store-specific `extend_func_refl`-family lemmas above — a legitimate
    proof-method divergence (Lean has proof irrelevance), not a
    signature divergence. -/
theorem Extend_store_refl {s : store} (h : wf_store s) : Extend_store s s := by
  cases h with
  | store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas =>
    have hwf : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas
    exact Extend_store.mk_Extend_store _ _
      (forall_range_lt globals) (forall_range_lt globals)
      (forall_range_refl globals wf_globalinst Extend_globalinst hglobals
        (fun x hx => extend_globalinst_refl_0 hx))
      (forall_range_lt mems) (forall_range_lt mems)
      (forall_range_refl mems wf_meminst Extend_meminst hmems
        (fun x hx => extend_meminst_refl_0 hx))
      (forall_range_lt tables) (forall_range_lt tables)
      (forall_range_refl tables wf_tableinst Extend_tableinst htables
        (fun x hx => extend_tableinst_refl_0 hx))
      (forall_range_lt funcs) (forall_range_lt funcs)
      (forall_range_refl funcs wf_funcinst Extend_funcinst hfuncs
        (fun x hx => extend_funcinst_refl_0 hx))
      (forall_range_lt datas) (forall_range_lt datas)
      (forall_range_refl datas wf_datainst Extend_datainst hdatas
        (fun x hx => extend_datainst_refl_0 hx))
      (forall_range_lt elems) (forall_range_lt elems)
      (forall_range_refl_noWf elems Extend_eleminst extend_eleminst_refl_0)
      hwf hwf

/-! ## `Extend_store` preserves `Ref_ok`/`Val_ok` (extension_lemmas.v:1161-1258) -/

/-- `Extend_funcinst` is a reflexivity-only relation in `wasm2.0.lean` (its
    single constructor forces both sides to be the *same* record), so it
    collapses to plain equality. No Rocq counterpart by name — Rocq's
    `Extend_store_ref` gets the same fact inline via `inversion
    HFuncsExtend`. Lean-only helper; needed because the `getElem!`
    applications that appear as `Extend_funcinst`'s indices at use sites are
    opaque terms that defeat `cases` there, whereas here both sides are bare
    variables. -/
theorem extend_funcinst_eq (f1 f2 : funcinst) : Extend_funcinst f1 f2 → f1 = f2 := by
  intro h
  cases h
  rfl

/-- Rocq `extension_lemmas.v:787` `funcinst_same` (`5b03ae067`; since removed upstream).
    Nothing in this project uses it.

    **Strengthened over a literal transcription**, same move as `Vals_ok`
    (`TypingLemmas.lean`) and for the same reason: `wasm2.0.lean`'s
    `Forall₂` is a zip-based `def` (`∀ t ∈ xs.zip ys, P t.1 t.2`), which does
    NOT force `f1.length = f2.length` the way Rocq's inductive `Forall2`
    does — so `Forall₂ Extend_funcinst f1 f2` alone is satisfiable even when
    `f1`/`f2` have different lengths, and the lemma is unprovable as
    literally stated without an extra length hypothesis. Takes `hlen`
    explicitly instead. Proved via the `Forall₂`/Mathlib
    `List.Forall₂` bridge (`HelperLemmas.to_mathlib_forall₂`): once lengths
    are known equal, Mathlib's inductive `List.Forall₂` is available, and
    `Extend_funcinst`-pointwise-implies-`Eq` (`extend_funcinst_eq`) plus
    `List.forall₂_eq_eq_eq` collapses it to `f1 = f2` directly. -/
theorem funcinst_same (f1 f2 : List funcinst) (hlen : f1.length = f2.length) :
    Forall₂ Extend_funcinst f1 f2 → f1 = f2 := by
  intro h
  have h' : List.Forall₂ Extend_funcinst f1 f2 := to_mathlib_forall₂ hlen h
  have h'' : List.Forall₂ (· = ·) f1 f2 := h'.imp (fun a b hab => extend_funcinst_eq a b hab)
  rwa [List.forall₂_eq_eq_eq] at h''

/-- The last two hypotheses of `Extend_store`'s constructor are `wf_store s`
    and `wf_store s'`; Rocq's `invert_extend_store` tactic (`extension_lemmas.v:774`)
    surfaces them as `HWfStore`/`HWfStore'`. These two named projections stand in for that
    tactic (which, per the project's standing decision, is not ported —
    Rocq's Ltac tactics are proof plumbing, not content). -/
theorem Extend_store_wf_store (s s' : store) : Extend_store s s' → wf_store s := by
  intro h
  cases h with
  | mk_Extend_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwf _ => exact hwf

theorem Extend_store_wf_store' (s s' : store) : Extend_store s s' → wf_store s' := by
  intro h
  cases h with
  | mk_Extend_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwf' => exact hwf'

theorem Extend_store_ref (v_S v_S' : store) (v_t : reftype) (v_val : ref) :
    Extend_store v_S v_S' → Ref_ok v_S v_val v_t → Ref_ok v_S' v_val v_t := by
  intro hs hv
  cases hs with
  | mk_Extend_store _ _ _ _ _ _ _ _ _ _ hfb' hfe _ _ _ _ _ _ _ hwfS' =>
    cases hv with
    | null _ => exact Ref_ok.null _ _ hwfS'
    | extern a _ => exact Ref_ok.extern v_S' a hwfS'
    | func a ext hext _ _ =>
      obtain ⟨_, fi, hab, hlk, _, hwffi, _⟩ := Externaddr_invert_funcs v_S a ext hext
      simp only [lookup_total] at hlk
      have hmem : a ∈ List.range v_S.FUNCS.length := List.mem_range.mpr hab
      have heq : v_S.FUNCS[a]! = v_S'.FUNCS[a]! := extend_funcinst_eq _ _ (hfe a hmem)
      exact Ref_ok.func v_S' a fi.TYPE
        (Externaddr_ok.func v_S' a fi (hfb' a hmem) (heq.symm.trans hlk) hwfS' hwffi) hwfS' hwffi

theorem Extend_store_refs (v_S v_S' : store) (v_ts : List reftype) (v_vals : List ref) :
    Extend_store v_S v_S' → Forall₂ (fun t v => Ref_ok v_S v t) v_ts v_vals →
    Forall₂ (fun t v => Ref_ok v_S' v t) v_ts v_vals :=
  fun hs h p hp => Extend_store_ref v_S v_S' p.1 p.2 hs (h p hp)

/-- Rocq `extension_lemmas.v:1201` `Extend_store_refs'`. Single-type version of
    `Extend_store_refs` (a `Forall` over one `reftype`, not a `Forall₂`
    across two parallel lists). -/
theorem Extend_store_refs' (v_S v_S' : store) (v_t : reftype) (v_refs : List ref) :
    Extend_store v_S v_S' → Forall (fun v_ref => Ref_ok v_S v_ref v_t) v_refs →
    Forall (fun v_ref => Ref_ok v_S' v_ref v_t) v_refs :=
  fun hs h r hr => Extend_store_ref v_S v_S' v_t r hs (h r hr)

theorem Extend_store_val (v_S v_S' : store) (v_t : valtype) (v_val : val) :
    Extend_store v_S v_S' → Val_ok v_S v_val v_t → Val_ok v_S' v_val v_t := by
  intro hs hv
  have hwfS' : wf_store v_S' := Extend_store_wf_store' v_S v_S' hs
  cases hv with
  | numtype nt c_t _ hwfv => exact Val_ok.numtype v_S' nt c_t hwfS' hwfv
  | vectype vt c_t _ hwfv => exact Val_ok.vectype v_S' vt c_t hwfS' hwfv
  | reftype r rt hrok _ =>
    exact Val_ok.reftype v_S' r rt (Extend_store_ref v_S v_S' rt r hs hrok) hwfS'

theorem Extend_store_vals (v_S v_S' : store) (v_t : List valtype) (v_val : List val) :
    Extend_store v_S v_S' → Vals_ok v_S v_val v_t → Vals_ok v_S' v_val v_t := by
  intro hs h
  simp only [Vals_ok] at h ⊢
  exact ⟨h.1, fun p hp => Extend_store_val v_S v_S' p.1 p.2 hs (h.2 p hp)⟩

theorem config_same (s s' : store) (f f' : frame) (ais ais' : List admininstr) :
    config.mk_config (state.mk_state s f) ais = config.mk_config (state.mk_state s' f') ais' →
    s = s' ∧ f = f' ∧ ais = ais' := by
  intro h
  injection h with h1 h2
  injection h1 with h3 h4
  exact ⟨h3, h4, h2⟩

theorem config_same2 (s s' : store) (f f' : frame) (ais ais' : List admininstr) :
    s = s' ∧ f = f' ∧ ais = ais' →
    config.mk_config (state.mk_state s f) ais = config.mk_config (state.mk_state s' f') ais' := by
  rintro ⟨rfl, rfl, rfl⟩
  rfl

/-! ## Extension facts produced by specific store-mutating operations
    (extension_lemmas.v:1627-2041): each takes `wf_*` premises and concludes with a
    `holds_upto` fact, as in Rocq -/

/-- Rocq `extension_lemmas.v:1627` `global_set_global_extension`. Takes `Forall
    wf_globalinst v_g` and `wf_val v_val_1` premises; the conclusion is
    `holds_upto`-shaped and the post-update list `v_g'` is an explicit
    hypothesis-bound parameter rather than `list_update_func` written inline
    in the conclusion. -/
theorem global_set_global_extension (v_g v_g' : List globalinst) (v_idx : Nat) (v_valtype : valtype)
    (v_val_0 v_val_1 : val) :
    Forall wf_globalinst v_g → wf_val v_val_1 →
    v_idx < v_g.length → lookup_total v_g v_idx = globalinst.MKglobalinst (globaltype.mk_globaltype (some r_MUT.MUT) v_valtype) v_val_0 →
    v_g' = list_update_func v_g v_idx (fun g => { g with VALUE := v_val_1 }) →
    holds_upto (fun a => Extend_globalinst (v_g[a]!) (v_g'[a]!)) v_g.length := by
  intro hwf hwfval hidx hlookup heq
  intro a ha
  have ha' : a < v_g.length := List.mem_range.mp ha
  subst heq
  rw [getElem!_modify_eq_or_ne v_g v_idx a _ ha']
  by_cases h : a = v_idx
  · subst h
    rw [if_pos rfl, ← lookup_total, hlookup]
    exact Extend_globalinst.mk_Extend_globalinst (some r_MUT.MUT) v_valtype v_val_0 v_val_1
      (Or.inl rfl) (hlookup ▸ hwf (v_g[a]!) (getElem!_pos v_g a ha' ▸ List.getElem_mem ha'))
      (wf_globalinst.globalinst_case_ _ _ hwfval)
  · rw [if_neg h]
    exact extend_globalinst_refl_0 (hwf (v_g[a]!) (getElem!_pos v_g a ha' ▸ List.getElem_mem ha'))

/-- Rocq `extension_lemmas.v:1679` `store_none_mem_extension`. Takes `Forall wf_byte
    v_nb`/`Forall wf_meminst v_ms` premises; the conclusion is `holds_upto`-shaped
    with `v_ms'` explicit.
    Unlike its sibling
    `memory_grow_mem_extension`, this lemma does *not* get `Forall wf_meminst
    v_ms'` handed to it, so the post-update element's well-formedness has to be
    rebuilt. That is done in `extend_meminst_bytes` above (bare variables, so
    the inversions are unproblematic), fed with
    `HelperLemmas.list_slice_update_forall`/`_length`.
-/
theorem store_none_mem_extension (v_ms v_ms' : List meminst) (v_idx : Nat) (v_mt : memtype) (b_lst : List byte)
    (v_l v_n_len : Nat) (v_nb : List byte) :
    Forall wf_byte v_nb → Forall wf_meminst v_ms →
    v_idx < v_ms.length → lookup_total v_ms v_idx = meminst.MKmeminst v_mt b_lst →
    v_ms' = list_update_func v_ms v_idx (fun m => { m with BYTES := list_slice_update m.BYTES v_l v_n_len v_nb }) →
    holds_upto (fun a => Extend_meminst (v_ms[a]!) (v_ms'[a]!)) v_ms.length := by
  intro hwfnb hwf hidx hlookup heq
  intro a ha
  have ha' : a < v_ms.length := List.mem_range.mp ha
  rw [heq, getElem!_modify_eq_or_ne v_ms v_idx a _ ha']
  by_cases h : a = v_idx
  · subst h
    rw [if_pos rfl]
    have hwfold := hwf (v_ms[a]!) (getElem!_pos v_ms a ha' ▸ List.getElem_mem ha')
    rw [show v_ms[a]! = lookup_total v_ms a from rfl, hlookup] at hwfold
    rw [show v_ms[a]! = lookup_total v_ms a from rfl, hlookup]
    have hwfbs : Forall wf_byte b_lst := by
      cases hwfold with | meminst_case_ _ _ _ hb => exact hb
    exact extend_meminst_bytes (meminst.MKmeminst v_mt b_lst) _ hwfold
      (list_slice_update_forall b_lst v_nb v_l v_n_len hwfbs hwfnb)
      (by simp [list_slice_update_length])
  · rw [if_neg h]
    exact extend_meminst_refl_0 (hwf (v_ms[a]!) (getElem!_pos v_ms a ha' ▸ List.getElem_mem ha'))

/-- Rocq `extension_lemmas.v:1753` `memory_grow_mem_extension`. Takes `Forall
    wf_meminst v_ms`/`Forall wf_meminst v_ms'` premises; the conclusion is
    `holds_upto`-shaped with `v_ms'` explicit. The declared max `v_j` is a genuine
    `Option` (Rocq's `v_j_opt : option N`), carried through unchanged by `memory.grow`,
    on both the pre- and post-grow memtype. Note this lemma — unlike
    `construct_meminsts_grow` — needs no `≤ 2^16` bound at all: it's pure
    `Extend_meminst` monotonicity, not full `Meminst_ok` reconstruction. -/
theorem memory_grow_mem_extension (v_ms v_ms' : List meminst) (v_idx : Nat) (b_lst : List byte)
    (v_i v_n : Nat) (v_j : Option Nat) :
    Forall wf_meminst v_ms → Forall wf_meminst v_ms' →
    v_idx < v_ms.length →
    lookup_total v_ms v_idx = meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN v_i) (v_j.map uN.mk_uN))) b_lst →
    Forall (fun j => v_i + v_n ≤ j) v_j.toList →
    v_ms' = list_update_func v_ms v_idx (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (v_i + v_n)) (v_j.map uN.mk_uN)))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))) →
    holds_upto (fun a => Extend_meminst (v_ms[a]!) (v_ms'[a]!)) v_ms.length := by
  intro hwf hwf' hidx hlookup _ heq
  intro a ha
  have ha' : a < v_ms.length := List.mem_range.mp ha
  rw [heq, getElem!_modify_eq_or_ne v_ms v_idx a _ ha']
  by_cases h : a = v_idx
  · subst h
    rw [if_pos rfl]
    have hwfold := hwf (v_ms[a]!) (getElem!_pos v_ms a ha' ▸ List.getElem_mem ha')
    rw [show v_ms[a]! = lookup_total v_ms a from rfl, hlookup] at hwfold
    have ha2 : a < v_ms'.length := by rw [heq]; simpa [list_update_func] using ha'
    have hwfnew := hwf' (v_ms'[a]!) (getElem!_pos v_ms' a ha2 ▸ List.getElem_mem ha2)
    rw [heq, getElem!_modify_eq_or_ne v_ms a a _ ha', if_pos rfl] at hwfnew
    rw [show v_ms[a]! = lookup_total v_ms a from rfl, hlookup]
    exact Extend_meminst.mk_Extend_meminst v_i v_j b_lst (v_i + v_n)
      (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))
      (Nat.le_add_right v_i v_n) (by simp) hwfold hwfnew
  · rw [if_neg h]
    exact extend_meminst_refl_0 (hwf (v_ms[a]!) (getElem!_pos v_ms a ha' ▸ List.getElem_mem ha'))

/-- Rocq `extension_lemmas.v:1841` `table_set_table_extension`. Takes a `Forall
    wf_tableinst v_tbs` premise; the conclusion is `holds_upto`-shaped with
    `v_tbs'` explicit. -/
theorem table_set_table_extension (v_tbs v_tbs' : List tableinst) (v_idx : Nat) (tbt : tabletype) (tbr : List ref)
    (v_i : Nat) (v_tbr : ref) :
    Forall wf_tableinst v_tbs →
    v_idx < v_tbs.length → lookup_total v_tbs v_idx = tableinst.MKtableinst tbt tbr →
    v_tbs' = list_update_func v_tbs v_idx (fun tb => { tb with REFS := list_update_func tb.REFS v_i (fun _ => v_tbr) }) →
    holds_upto (fun a => Extend_tableinst (v_tbs[a]!) (v_tbs'[a]!)) v_tbs.length := by
  intro hwf hidx hlookup heq
  intro a ha
  have ha' : a < v_tbs.length := List.mem_range.mp ha
  subst heq
  rw [getElem!_modify_eq_or_ne v_tbs v_idx a _ ha']
  by_cases h : a = v_idx
  · subst h
    have hwft := hwf (v_tbs[a]!) (getElem!_pos v_tbs a ha' ▸ List.getElem_mem ha')
    rw [show v_tbs[a]! = lookup_total v_tbs a from rfl, hlookup] at hwft ⊢
    rw [if_pos rfl]
    obtain ⟨lim, rt⟩ := tbt
    obtain ⟨vn32, mopt32⟩ := lim
    obtain ⟨v_n⟩ := vn32
    rcases mopt32 with _ | m32
    · cases hwft with
      | tableinst_case_ _ _ hwftt =>
        exact Extend_tableinst.mk_Extend_tableinst v_n none rt tbr v_n (list_update_func tbr v_i (fun _ => v_tbr))
          (Nat.le_refl v_n) (by simp [list_update_func]) (wf_tableinst.tableinst_case_ _ _ hwftt)
          (wf_tableinst.tableinst_case_ _ _ hwftt)
    · obtain ⟨m'⟩ := m32
      cases hwft with
      | tableinst_case_ _ _ hwftt =>
        exact Extend_tableinst.mk_Extend_tableinst v_n (some m') rt tbr v_n (list_update_func tbr v_i (fun _ => v_tbr))
          (Nat.le_refl v_n) (by simp [list_update_func]) (wf_tableinst.tableinst_case_ _ _ hwftt)
          (wf_tableinst.tableinst_case_ _ _ hwftt)
  · rw [if_neg h]
    exact extend_tableinst_refl_0 (hwf (v_tbs[a]!) (getElem!_pos v_tbs a ha' ▸ List.getElem_mem ha'))

/-- Rocq `extension_lemmas.v:1894` `table_grow_table_extension`. Takes `Forall
    wf_tableinst v_tbs`/`Forall wf_tableinst v_tbs'` premises; the conclusion is
    `holds_upto`-shaped with `v_tbs'` explicit.
    Proof: "Template A" index split, with the post-update `wf_tableinst` handed
    over directly by `hwf'`, following
    `memory_grow_mem_extension`'s term order exactly; `j : Option uN` is
    split *after* the rewrites (splitting it before leaves an
    `omega` goal about `(list_update_func v_tbs a f).length` — a
    metavariable from an out-of-order `rw` leaking into a later goal, not a
    real arithmetic obligation). Note `j : Option uN` here (not `Option Nat`):
    that matches Rocq, whose `j` is used directly as the limits max.
-/
theorem table_grow_table_extension (v_tbs v_tbs' : List tableinst) (v_idx : Nat) (j : Option uN) (r : ref)
    (rt : reftype) (nn : Nat) (tbr : List ref) :
    Forall wf_tableinst v_tbs → Forall wf_tableinst v_tbs' →
    v_idx < v_tbs.length →
    lookup_total v_tbs v_idx = tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN tbr.length) j) rt) tbr →
    v_tbs' = list_update_func v_tbs v_idx (fun _ =>
      tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (tbr.length + nn)) j) rt)
        (tbr ++ List.replicate nn r)) →
    holds_upto (fun a => Extend_tableinst (v_tbs[a]!) (v_tbs'[a]!)) v_tbs.length := by
  intro hwf hwf' hidx hlookup heq
  intro a ha
  have ha' : a < v_tbs.length := List.mem_range.mp ha
  rw [heq, getElem!_modify_eq_or_ne v_tbs v_idx a _ ha']
  by_cases h : a = v_idx
  · subst h
    rw [if_pos rfl]
    have hwfold := hwf (v_tbs[a]!) (getElem!_pos v_tbs a ha' ▸ List.getElem_mem ha')
    rw [show v_tbs[a]! = lookup_total v_tbs a from rfl, hlookup] at hwfold
    have ha2 : a < v_tbs'.length := by rw [heq]; simpa [list_update_func] using ha'
    have hwfnew := hwf' (v_tbs'[a]!) (getElem!_pos v_tbs' a ha2 ▸ List.getElem_mem ha2)
    rw [heq, getElem!_modify_eq_or_ne v_tbs a a _ ha', if_pos rfl] at hwfnew
    rw [show v_tbs[a]! = lookup_total v_tbs a from rfl, hlookup]
    rcases j with _ | ju
    · exact Extend_tableinst.mk_Extend_tableinst tbr.length none rt tbr (tbr.length + nn)
        (tbr ++ List.replicate nn r) (Nat.le_add_right _ _) (by simp) hwfold hwfnew
    · obtain ⟨jn⟩ := ju
      exact Extend_tableinst.mk_Extend_tableinst tbr.length (some jn) rt tbr (tbr.length + nn)
        (tbr ++ List.replicate nn r) (Nat.le_add_right _ _) (by simp) hwfold hwfnew
  · rw [if_neg h]
    exact extend_tableinst_refl_0 (hwf (v_tbs[a]!) (getElem!_pos v_tbs a ha' ▸ List.getElem_mem ha'))

/-- Rocq `extension_lemmas.v:1956` `elem_drop_elem_extension`. The conclusion is
    `holds_upto`-shaped with `es'` explicit (no `wf_*` premise —
    `Extend_eleminst` has none). -/
theorem elem_drop_elem_extension (es es' : List eleminst) (idx : Nat) :
    idx < es.length → es' = list_update_func es idx (fun e => { e with REFS := [] }) →
    holds_upto (fun a => Extend_eleminst (es[a]!) (es'[a]!)) es.length := by
  intro hidx heq
  intro a ha
  have ha' : a < es.length := List.mem_range.mp ha
  subst heq
  rw [getElem!_modify_eq_or_ne es idx a _ ha']
  by_cases h : a = idx
  · subst h
    rw [if_pos rfl]
    obtain ⟨rt, refs⟩ := es[a]!
    exact Extend_eleminst.mk_Extend_eleminst rt refs [] (Or.inr rfl)
  · rw [if_neg h]
    exact extend_eleminst_refl_0 _

/-- Rocq `extension_lemmas.v:1989` `data_drop_data_extension`. Takes a `Forall
    wf_datainst ds` premise; the conclusion is `holds_upto`-shaped with `ds'`
    explicit. -/
theorem data_drop_data_extension (ds ds' : List datainst) (idx : Nat) :
    Forall wf_datainst ds → idx < ds.length → ds' = list_update_func ds idx (fun _ => datainst.MKdatainst []) →
    holds_upto (fun a => Extend_datainst (ds[a]!) (ds'[a]!)) ds.length := by
  intro hwf hidx heq
  intro a ha
  have ha' : a < ds.length := List.mem_range.mp ha
  subst heq
  rw [getElem!_modify_eq_or_ne ds idx a _ ha']
  by_cases h : a = idx
  · subst h
    rw [if_pos rfl]
    have hwfd := hwf (ds[a]!) (getElem!_pos ds a ha' ▸ List.getElem_mem ha')
    rcases hdv : ds[a]! with ⟨bs⟩
    rw [hdv] at hwfd
    exact Extend_datainst.mk_Extend_datainst bs [] (Or.inr rfl) hwfd (wf_datainst.datainst_case_ [] (by simp [Forall]))
  · rw [if_neg h]
    exact extend_datainst_refl_0 (hwf (ds[a]!) (getElem!_pos ds a ha' ▸ List.getElem_mem ha'))

/-- Rocq `extension_lemmas.v:2026` `update_global_unchanged`. Frame lemma:
    updating only `store.GLOBALS` leaves every other component (and
    globals-length) unchanged. -/
theorem update_global_unchanged (v_S v_S' : store) (func : globalinst → globalinst) (v_idx : Nat) :
    v_S' = { v_S with GLOBALS := list_update_func v_S.GLOBALS v_idx func } →
    v_S.FUNCS = v_S'.FUNCS ∧ v_S.TABLES = v_S'.TABLES ∧ v_S.GLOBALS.length = v_S'.GLOBALS.length ∧
      v_S.MEMS = v_S'.MEMS ∧ v_S.ELEMS = v_S'.ELEMS ∧ v_S.DATAS = v_S'.DATAS := by
  intro h
  subst h
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
  simp [list_update_func, List.length_modify]

/-! ## `Externaddr_ok` preserved by store extension (extension_lemmas.v:2042-2265): the
    `addrs_*_extension` lemmas take a `wf_store v_S'` premise and two `holds_upto`
    premises, as in Rocq -/

/-! ### Per-instance consequences of the `Extend_*inst` relations

    `Extend_funcinst` collapses to equality (`extend_funcinst_eq`, above).
    The other three carry strictly less: `Extend_globalinst` preserves the
    `TYPE` field exactly, while `Extend_tableinst`/`Extend_meminst` only
    bound the old limits-minimum by the new one, which is exactly a
    `Tabletype_sub`/`Memtype_sub` step in the *new → old* direction. Rocq
    extracts these inline (`inversion HHolds; inversion H4; ...` inside
    `addrs_tables_extension`, which its own source comments mark "TODO
    improve this lemma proof later"); factoring them out as named lemmas
    here is a proof-method divergence only. -/

theorem extend_globalinst_type_eq (g g' : globalinst) :
    Extend_globalinst g g' → g.TYPE = g'.TYPE := by
  intro h
  cases h
  rfl

/-- Returns the `wf_tabletype` facts alongside the subtyping step, because
    both use sites need them and re-inverting `Tabletype_sub` at the use site
    is impossible there: its first index is an opaque `getElem!` projection,
    which defeats dependent elimination. -/
theorem extend_tableinst_sub (ti ti' : tableinst) :
    Extend_tableinst ti ti' →
    Tabletype_sub ti'.TYPE ti.TYPE ∧ wf_tabletype ti'.TYPE ∧ wf_tabletype ti.TYPE := by
  intro h
  cases h with
  | mk_Extend_tableinst v_n m_opt rt refs n' refs' hle _ hwf1 hwf2 =>
    cases hwf1 with
    | tableinst_case_ _ _ hwftt1 =>
      cases hwf2 with
      | tableinst_case_ _ _ hwftt2 =>
        have hlim1 : wf_limits (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v : m) => uN.mk_uN v) m_opt)) := by
          cases hwftt1 with | tabletype_case_0 _ _ hl => exact hl
        have hlim2 : wf_limits (limits.mk_limits (uN.mk_uN n') (OMap (fun (v : m) => uN.mk_uN v) m_opt)) := by
          cases hwftt2 with | tabletype_case_0 _ _ hl => exact hl
        refine ⟨Tabletype_sub.mk_Tabletype_sub _ rt _ ?_ hwftt2 hwftt1, hwftt2, hwftt1⟩
        rcases m_opt with _ | mm
        · exact Limits_sub.eps n' v_n hle (by simpa [OMap] using hlim2) (by simpa [OMap] using hlim1)
        · refine Limits_sub.max n' mm v_n (some mm) hle ?_ (by simpa [OMap] using hlim2)
            (by simpa [OMap] using hlim1)
          intro x hx
          have hxe : x = mm := by simpa using hx
          subst hxe
          exact Nat.le_refl _

theorem extend_meminst_sub (mi mi' : meminst) :
    Extend_meminst mi mi' →
    Memtype_sub mi'.TYPE mi.TYPE ∧ wf_memtype mi'.TYPE ∧ wf_memtype mi.TYPE := by
  intro h
  cases h with
  | mk_Extend_meminst v_n m_opt bs n' bs' hle _ hwf1 hwf2 =>
    cases hwf1 with
    | meminst_case_ _ _ hwfmt1 _ =>
      cases hwf2 with
      | meminst_case_ _ _ hwfmt2 _ =>
        have hlim1 : wf_limits (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v : m) => uN.mk_uN v) m_opt)) := by
          cases hwfmt1 with | memtype_case_0 _ hl => exact hl
        have hlim2 : wf_limits (limits.mk_limits (uN.mk_uN n') (OMap (fun (v : m) => uN.mk_uN v) m_opt)) := by
          cases hwfmt2 with | memtype_case_0 _ hl => exact hl
        refine ⟨Memtype_sub.mk_Memtype_sub _ _ ?_ hwfmt2 hwfmt1, hwfmt2, hwfmt1⟩
        rcases m_opt with _ | mm
        · exact Limits_sub.eps n' v_n hle (by simpa [OMap] using hlim2) (by simpa [OMap] using hlim1)
        · refine Limits_sub.max n' mm v_n (some mm) hle ?_ (by simpa [OMap] using hlim2)
            (by simpa [OMap] using hlim1)
          intro x hx
          have hxe : x = mm := by simpa using hx
          subst hxe
          exact Nat.le_refl _

theorem addrs_store_funcs_extension (v_S v_S' : store) (v_funcaddr : Nat) (v_ft : functype) :
    wf_store v_S' → Externaddr_ok v_S (externaddr.FUNC v_funcaddr) (externtype.FUNC v_ft) →
    holds_upto (fun a => a < v_S'.FUNCS.length) v_S.FUNCS.length →
    holds_upto (fun a => Extend_funcinst (v_S.FUNCS[a]!) (v_S'.FUNCS[a]!)) v_S.FUNCS.length →
    Externaddr_ok v_S' (externaddr.FUNC v_funcaddr) (externtype.FUNC v_ft) := by
  intro hwfS' hok hbound hext
  obtain ⟨xt, fi, hab, hlk, hxt, hwffi, hsub⟩ := Externaddr_invert_funcs v_S v_funcaddr v_ft hok
  subst hxt
  have hfteq : fi.TYPE = v_ft := externtype_func_eq _ _ hsub
  simp only [lookup_total] at hlk
  have hmem : v_funcaddr ∈ List.range v_S.FUNCS.length := List.mem_range.mpr hab
  have heq : v_S.FUNCS[v_funcaddr]! = v_S'.FUNCS[v_funcaddr]! :=
    extend_funcinst_eq _ _ (hext v_funcaddr hmem)
  have hres := Externaddr_ok.func v_S' v_funcaddr fi (hbound v_funcaddr hmem)
    (heq.symm.trans hlk) hwfS' hwffi
  rw [hfteq] at hres
  exact hres

theorem addrs_tables_extension (v_S v_S' : store) (v_tableaddr : Nat) (tt : tabletype) :
    wf_store v_S' → Externaddr_ok v_S (externaddr.TABLE v_tableaddr) (externtype.TABLE tt) →
    holds_upto (fun a => a < v_S'.TABLES.length) v_S.TABLES.length →
    holds_upto (fun a => Extend_tableinst (v_S.TABLES[a]!) (v_S'.TABLES[a]!)) v_S.TABLES.length →
    Externaddr_ok v_S' (externaddr.TABLE v_tableaddr) (externtype.TABLE tt) := by
  intro hwfS' hok hbound hext
  obtain ⟨xt, ti, hab, hlk, hxt, hwfti, hsub⟩ := Externaddr_invert_tables v_S v_tableaddr tt hok
  subst hxt
  simp only [lookup_total] at hlk
  have hmem : v_tableaddr ∈ List.range v_S.TABLES.length := List.mem_range.mpr hab
  -- `Tabletype_sub (new).TYPE (old).TYPE`, with `(old) = ti` by `hlk`.
  have htrip : Tabletype_sub (v_S'.TABLES[v_tableaddr]!).TYPE ti.TYPE ∧
      wf_tabletype (v_S'.TABLES[v_tableaddr]!).TYPE ∧ wf_tabletype ti.TYPE := by
    have h := extend_tableinst_sub _ _ (hext v_tableaddr hmem)
    rwa [hlk] at h
  have hsub' := htrip.1
  have hwfti' : wf_externtype (externtype.TABLE (v_S'.TABLES[v_tableaddr]!).TYPE) :=
    wf_externtype.externtype_case_2 _ htrip.2.1
  have hbase := Externaddr_ok.table v_S' v_tableaddr (v_S'.TABLES[v_tableaddr]!)
    (hbound v_tableaddr hmem) rfl hwfS' hwfti'
  refine Externaddr_ok.sub v_S' (externaddr.TABLE v_tableaddr) (externtype.TABLE tt) _ hbase ?_
    hwfS' ?_ hwfti'
  · exact externtype_sub_trans _ (externtype.TABLE ti.TYPE) _
      (Externtype_sub.table _ _ hsub' hwfti' hwfti) hsub
  · cases hsub with
    | table _ _ _ _ hwf2 => exact hwf2

theorem addrs_store_globals_extension (v_S v_S' : store) (v_globaladdr : Nat) (gt : globaltype) :
    wf_store v_S' → Externaddr_ok v_S (externaddr.GLOBAL v_globaladdr) (externtype.GLOBAL gt) →
    holds_upto (fun a => a < v_S'.GLOBALS.length) v_S.GLOBALS.length →
    holds_upto (fun a => Extend_globalinst (v_S.GLOBALS[a]!) (v_S'.GLOBALS[a]!)) v_S.GLOBALS.length →
    Externaddr_ok v_S' (externaddr.GLOBAL v_globaladdr) (externtype.GLOBAL gt) := by
  intro hwfS' hok hbound hext
  obtain ⟨xt, gi, hab, hlk, hxt, hwfgi, hsub⟩ := Externaddr_invert_globals v_S v_globaladdr gt hok
  subst hxt
  have hgteq : gi.TYPE = gt := externtype_global_eq _ _ hsub
  simp only [lookup_total] at hlk
  have hmem : v_globaladdr ∈ List.range v_S.GLOBALS.length := List.mem_range.mpr hab
  have hty : (v_S'.GLOBALS[v_globaladdr]!).TYPE = gt := by
    rw [← extend_globalinst_type_eq _ _ (hext v_globaladdr hmem), hlk, hgteq]
  have hwf' : wf_externtype (externtype.GLOBAL (v_S'.GLOBALS[v_globaladdr]!).TYPE) := by
    rw [hty, ← hgteq]; exact hwfgi
  have hres := Externaddr_ok.global v_S' v_globaladdr (v_S'.GLOBALS[v_globaladdr]!)
    (hbound v_globaladdr hmem) rfl hwfS' hwf'
  rw [hty] at hres
  exact hres

theorem addrs_mems_extension (v_S v_S' : store) (v_memaddr : Nat) (mt : memtype) :
    wf_store v_S' → Externaddr_ok v_S (externaddr.MEM v_memaddr) (externtype.MEM mt) →
    holds_upto (fun a => a < v_S'.MEMS.length) v_S.MEMS.length →
    holds_upto (fun a => Extend_meminst (v_S.MEMS[a]!) (v_S'.MEMS[a]!)) v_S.MEMS.length →
    Externaddr_ok v_S' (externaddr.MEM v_memaddr) (externtype.MEM mt) := by
  intro hwfS' hok hbound hext
  obtain ⟨xt, mi, hab, hlk, hxt, hwfmi, hsub⟩ := Externaddr_invert_mems v_S v_memaddr mt hok
  subst hxt
  simp only [lookup_total] at hlk
  have hmem : v_memaddr ∈ List.range v_S.MEMS.length := List.mem_range.mpr hab
  have htrip : Memtype_sub (v_S'.MEMS[v_memaddr]!).TYPE mi.TYPE ∧
      wf_memtype (v_S'.MEMS[v_memaddr]!).TYPE ∧ wf_memtype mi.TYPE := by
    have h := extend_meminst_sub _ _ (hext v_memaddr hmem)
    rwa [hlk] at h
  have hsub' := htrip.1
  have hwfmi' : wf_externtype (externtype.MEM (v_S'.MEMS[v_memaddr]!).TYPE) :=
    wf_externtype.externtype_case_3 _ htrip.2.1
  have hbase := Externaddr_ok.mem v_S' v_memaddr (v_S'.MEMS[v_memaddr]!)
    (hbound v_memaddr hmem) rfl hwfS' hwfmi'
  refine Externaddr_ok.sub v_S' (externaddr.MEM v_memaddr) (externtype.MEM mt) _ hbase ?_
    hwfS' ?_ hwfmi'
  · exact externtype_sub_trans _ (externtype.MEM mi.TYPE) _
      (Externtype_sub.mem _ _ hsub' hwfmi' hwfmi) hsub
  · cases hsub with
    | mem _ _ _ _ hwf2 => exact hwf2

theorem addrss_store_funcs_extension (v_S v_S' : store) (v_funcaddrs : List Nat) (tcf : List functype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.FUNC a) (externtype.FUNC t)) v_funcaddrs tcf →
    holds_upto (fun a => a < v_S'.FUNCS.length) v_S.FUNCS.length →
    holds_upto (fun a => Extend_funcinst (v_S.FUNCS[a]!) (v_S'.FUNCS[a]!)) v_S.FUNCS.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.FUNC a) (externtype.FUNC t)) v_funcaddrs tcf :=
  fun hwfS' h hbound hext p hp =>
    addrs_store_funcs_extension v_S v_S' p.1 p.2 hwfS' (h p hp) hbound hext

theorem addrss_tables_extension (v_S v_S' : store) (v_addrs : List Nat) (tcs : List tabletype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.TABLE a) (externtype.TABLE t)) v_addrs tcs →
    holds_upto (fun a => a < v_S'.TABLES.length) v_S.TABLES.length →
    holds_upto (fun a => Extend_tableinst (v_S.TABLES[a]!) (v_S'.TABLES[a]!)) v_S.TABLES.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.TABLE a) (externtype.TABLE t)) v_addrs tcs :=
  fun hwfS' h hbound hext p hp =>
    addrs_tables_extension v_S v_S' p.1 p.2 hwfS' (h p hp) hbound hext

theorem addrss_store_globals_extension (v_S v_S' : store) (v_addrs : List Nat) (tcs : List globaltype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.GLOBAL a) (externtype.GLOBAL t)) v_addrs tcs →
    holds_upto (fun a => a < v_S'.GLOBALS.length) v_S.GLOBALS.length →
    holds_upto (fun a => Extend_globalinst (v_S.GLOBALS[a]!) (v_S'.GLOBALS[a]!)) v_S.GLOBALS.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.GLOBAL a) (externtype.GLOBAL t)) v_addrs tcs :=
  fun hwfS' h hbound hext p hp =>
    addrs_store_globals_extension v_S v_S' p.1 p.2 hwfS' (h p hp) hbound hext

theorem addrss_mems_extension (v_S v_S' : store) (v_addrs : List Nat) (tcs : List memtype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.MEM a) (externtype.MEM t)) v_addrs tcs →
    holds_upto (fun a => a < v_S'.MEMS.length) v_S.MEMS.length →
    holds_upto (fun a => Extend_meminst (v_S.MEMS[a]!) (v_S'.MEMS[a]!)) v_S.MEMS.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.MEM a) (externtype.MEM t)) v_addrs tcs :=
  fun hwfS' h hbound hext p hp =>
    addrs_mems_extension v_S v_S' p.1 p.2 hwfS' (h p hp) hbound hext

/-- `Externaddr_ok` is preserved by `Extend_store`, for any externaddr kind.
    No Rocq counterpart as a standalone lemma — Rocq inlines this
    `dependent induction` inside `Extend_store_exts` (`extension_lemmas.v`
    :2283-2288), dispatching to the four `addrs_*_extension` lemmas and
    re-applying `Externaddr_ok__sub` in the `sub` case. Factored out here
    because `Extend_store_moduleinst` needs the same case analysis. -/
theorem Extend_store_externaddr (v_S v_S' : store) (xa : externaddr) (xt : externtype) :
    Extend_store v_S v_S' → Externaddr_ok v_S xa xt → Externaddr_ok v_S' xa xt := by
  intro hs h
  have hwfS' : wf_store v_S' := Extend_store_wf_store' v_S v_S' hs
  obtain ⟨_, hgb', hge, _, hmb', hme, _, htb', hte, _, hfb', hfe,
          _, _, _, _, _, _, _, _⟩ := id hs
  induction h with
  | global a gi hb hl hwfs hwfx =>
    exact addrs_store_globals_extension v_S v_S' a gi.TYPE hwfS'
      (Externaddr_ok.global v_S a gi hb hl hwfs hwfx) hgb' hge
  | mem a mi hb hl hwfs hwfx =>
    exact addrs_mems_extension v_S v_S' a mi.TYPE hwfS'
      (Externaddr_ok.mem v_S a mi hb hl hwfs hwfx) hmb' hme
  | table a ti hb hl hwfs hwfx =>
    exact addrs_tables_extension v_S v_S' a ti.TYPE hwfS'
      (Externaddr_ok.table v_S a ti hb hl hwfs hwfx) htb' hte
  | func a fi hb hl hwfs hwfx =>
    exact addrs_store_funcs_extension v_S v_S' a fi.TYPE hwfS'
      (Externaddr_ok.func v_S a fi hb hl hwfs hwfx) hfb' hfe
  | sub ea xt1 xt' _ hsub _ hwfxt hwfxt' ih =>
    exact Externaddr_ok.sub v_S' ea xt1 xt' ih hsub hwfS' hwfxt hwfxt'

/-! ## `Extend_store` preserves `Exportinst_ok`/`Eleminst_ok`(store-addressed)/
    `Datainst_ok`(store-addressed)/`Moduleinst_ok` (extension_lemmas.v:2266-2454) -/

theorem Extend_store_exts (v_S v_S' : store) (v_exportinst : List exportinst) :
    Extend_store v_S v_S' → Forall (Exportinst_ok v_S) v_exportinst → Forall (Exportinst_ok v_S') v_exportinst := by
  intro hext h e he
  have hwfS' : wf_store v_S' := Extend_store_wf_store' v_S v_S' hext
  cases h e he with
  | mk_Exportinst_ok nm xa xt hxaok _ hwfxt hwfe =>
    exact Exportinst_ok.mk_Exportinst_ok v_S' nm xa xt
      (Extend_store_externaddr v_S v_S' xa xt hext hxaok) hwfS' hwfxt hwfe

theorem Extend_store_eleminst (v_S v_S' : store) (a : eleminst) (t : elemtype) :
    Extend_store v_S v_S' → Eleminst_ok v_S a t → Eleminst_ok v_S' a t := by
  intro hext h
  have hwfS' : wf_store v_S' := Extend_store_wf_store' v_S v_S' hext
  cases h with
  | mk_Eleminst_ok _ ref_lst hrefs hlen _ =>
    exact Eleminst_ok.mk_Eleminst_ok v_S' t ref_lst
      (fun r hr => Extend_store_ref v_S v_S' t r hext (hrefs r hr)) hlen hwfS'

/-- Combined step used by `Extend_store_eleminsts'`: the *same-index* element
    of the extended store is `Eleminst_ok` too. Stated over bare variables
    `e`/`e'` precisely so that both inversions are available — at the call
    site both are opaque `getElem!` applications, where `cases` cannot
    reach them. No Rocq counterpart (Rocq inverts in place, which its
    `Forall2`/`eq_to_prop` machinery permits). -/
theorem Extend_store_eleminst_ext (v_S v_S' : store) (e e' : eleminst) (t : elemtype) :
    Extend_store v_S v_S' → Extend_eleminst e e' → Eleminst_ok v_S e t → Eleminst_ok v_S' e' t := by
  intro hs he hok
  have hwfS' : wf_store v_S' := Extend_store_wf_store' v_S v_S' hs
  cases hok with
  | mk_Eleminst_ok _ ref_lst hrefs hlen _ =>
    cases he with
    | mk_Extend_eleminst _ _ refs' hor =>
      rcases hor with rfl | rfl
      · exact Eleminst_ok.mk_Eleminst_ok v_S' t ref_lst
          (fun r hr => Extend_store_ref v_S v_S' t r hs (hrefs r hr)) hlen hwfS'
      · exact Eleminst_ok.mk_Eleminst_ok v_S' t [] (by intro r hr; simp [Forall] at hr)
          (by simp) hwfS'

/-- As `Extend_store_eleminst_ext`, for `Datainst_ok`. -/
theorem Extend_store_datainst_ext (v_S v_S' : store) (d d' : datainst) (t : datatype) :
    Extend_store v_S v_S' → Extend_datainst d d' → Datainst_ok v_S d t →
    Datainst_ok v_S' d' t := by
  intro hs hd hok
  have hwfS' : wf_store v_S' := Extend_store_wf_store' v_S v_S' hs
  cases hok with
  | mk_Datainst_ok b_lst hlen _ _ =>
    cases hd with
    | mk_Extend_datainst _ b'_lst hor _ hwfd' =>
      refine Datainst_ok.mk_Datainst_ok v_S' b'_lst ?_ hwfS' hwfd'
      rcases hor with rfl | rfl
      · exact hlen
      · simp

/-- Rocq `extension_lemmas.v:2304` `Extend_store_eleminsts'`.
    Address-based version, for module-instance `ELEMS` fields addressed by
    index. -/
theorem Extend_store_eleminsts' (v_S v_S' : store) (aa : List Nat) (ts : List elemtype) :
    Extend_store v_S v_S' → Forall (fun a => a < v_S.ELEMS.length) aa →
    Forall₂ (fun a t => Eleminst_ok v_S (lookup_total v_S.ELEMS a) t) aa ts →
    Forall (fun a => a < v_S'.ELEMS.length) aa ∧
      Forall₂ (fun a t => Eleminst_ok v_S' (lookup_total v_S'.ELEMS a) t) aa ts := by
  intro hext hlen h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heb', hee, _, _⟩ := id hext
  refine ⟨fun a ha => heb' a (List.mem_range.mpr (hlen a ha)), ?_⟩
  intro p hp
  have hpa : p.1 ∈ aa := (List.of_mem_zip hp).1
  exact Extend_store_eleminst_ext v_S v_S' _ _ p.2 hext
    (hee p.1 (List.mem_range.mpr (hlen p.1 hpa))) (h p hp)

theorem Extend_store_eleminsts (v_S v_S' : store) (aa : List eleminst) (ts : List elemtype) :
    Extend_store v_S v_S' → Forall₂ (fun a t => Eleminst_ok v_S a t) aa ts →
    Forall₂ (fun a t => Eleminst_ok v_S' a t) aa ts :=
  fun hext h p hp => Extend_store_eleminst v_S v_S' p.1 p.2 hext (h p hp)

/-- Rocq `extension_lemmas.v:2360` `Extend_store_datainsts'`. **Deviation**: Rocq relates
    `aa` to a list `ts` of datatypes by `Forall2`; since `datatype` has the single value `OK`,
    this states premise and conclusion as a `Forall` over `aa` with `datatype.OK` (dropping
    the `|aa| = |ts|` that Rocq's `Forall2` implies). -/
theorem Extend_store_datainsts' (v_S v_S' : store) (aa : List Nat) :
    Extend_store v_S v_S' → Forall (fun a => a < v_S.DATAS.length) aa →
    Forall (fun a => Datainst_ok v_S (lookup_total v_S.DATAS a) datatype.OK) aa →
    Forall (fun a => a < v_S'.DATAS.length) aa ∧ Forall (fun a => Datainst_ok v_S' (lookup_total v_S'.DATAS a) datatype.OK) aa := by
  intro hext hlen h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdb', hde, _, _, _, _, _⟩ := id hext
  refine ⟨fun a ha => hdb' a (List.mem_range.mpr (hlen a ha)), ?_⟩
  intro a ha
  exact Extend_store_datainst_ext v_S v_S' _ _ datatype.OK hext
    (hde a (List.mem_range.mpr (hlen a ha))) (h a ha)

theorem Extend_store_datainsts (v_S v_S' : store) (aa : List datainst) :
    Extend_store v_S v_S' → Forall (fun a => Datainst_ok v_S a datatype.OK) aa →
    Forall (fun a => Datainst_ok v_S' a datatype.OK) aa := by
  intro hext h a ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwfS'⟩ := hext
  cases h a ha with
  | mk_Datainst_ok b_lst hlen _ hwf => exact Datainst_ok.mk_Datainst_ok v_S' b_lst hlen hwfS' hwf

/-- Rocq `extension_lemmas.v:2422` `Extend_store_moduleinst`. **The
    key assembly lemma**, reused by `type_preservation.v`'s
    `step_moduleinst` and `t_preservation`. -/
theorem Extend_store_moduleinst (v_S v_S' : store) (v_i : moduleinst) (v_C : context) :
    Extend_store v_S v_S' → Moduleinst_ok v_S v_i v_C → Moduleinst_ok v_S' v_i v_C := by
  intro hext h
  have hwfS' : wf_store v_S' := Extend_store_wf_store' v_S v_S' hext
  obtain ⟨_, hgb', hge, _, hmb', hme, _, htb', hte, _, hfb', hfe,
          _, hdb', hde, _, heb', hee, _, _⟩ := id hext
  cases h with
  | mk_Moduleinst_ok ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 _
      h21 h22 h23 h24 h25 h26 =>
    exact Moduleinst_ok.mk_Moduleinst_ok v_S' ftl fal gal tal mal eal dal eil ffl gtl ttl mtl etl dtl
      h1 h2 (addrss_store_globals_extension v_S v_S' gal gtl hwfS' h3 hgb' hge)
      h4 (addrss_store_funcs_extension v_S v_S' fal ffl hwfS' h5 hfb' hfe)
      h6 (addrss_mems_extension v_S v_S' mal mtl hwfS' h7 hmb' hme)
      h8 (addrss_tables_extension v_S v_S' tal ttl hwfS' h9 htb' hte)
      (Extend_store_exts v_S v_S' eil hext h10)
      h11
      (fun a ha => hdb' a (List.mem_range.mpr (h12 a ha)))
      (fun p hp => Extend_store_datainst_ext v_S v_S' _ _ p.2 hext
        (hde p.1 (List.mem_range.mpr (h12 p.1 (List.of_mem_zip hp).1))) (h13 p hp))
      h14
      (fun a ha => heb' a (List.mem_range.mpr (h15 a ha)))
      (fun p hp => Extend_store_eleminst_ext v_S v_S' _ _ p.2 hext
        (hee p.1 (List.mem_range.mpr (h15 p.1 (List.of_mem_zip hp).1))) (h16 p hp))
      h17 h18 h19 hwfS' h21 h22 h23 h24 h25 h26

/-! ## `Extend_store` preserves `*_instance_ok` (extension_lemmas.v:2455-2573) -/

theorem Extend_store_funcinst (s s' : store) (v : funcinst) (t : functype) :
    Extend_store s s' → Funcinst_ok s v t → Funcinst_ok s' v t := by
  intro hext h
  have hwfS' : wf_store s' := Extend_store_wf_store' s s' hext
  cases h with
  | mk_Funcinst_ok _ vmi vf C hftok hmiok hfok _ hwfC hwff =>
    exact Funcinst_ok.mk_Funcinst_ok s' t vmi vf C hftok
      (Extend_store_moduleinst s s' vmi C hext hmiok) hfok hwfS' hwfC hwff

theorem Extend_store_funcinsts (s s' : store) (vs : List funcinst) (ts : List functype) :
    Extend_store s s' → Forall₂ (fun v t => Funcinst_ok s v t) vs ts →
    Forall₂ (fun v t => Funcinst_ok s' v t) vs ts :=
  fun hext h p hp => Extend_store_funcinst s s' p.1 p.2 hext (h p hp)

theorem Extend_store_globalinst (s s' : store) (v : globalinst) (t : globaltype) :
    Extend_store s s' → Globalinst_ok s v t → Globalinst_ok s' v t := by
  intro hext h
  have hwfS' : wf_store s' := Extend_store_wf_store' s s' hext
  cases h with
  | mk_Globalinst_ok v_mut vt v_val hgtok hvok _ hwfg =>
    exact Globalinst_ok.mk_Globalinst_ok s' v_mut vt v_val hgtok
      (Extend_store_val s s' vt v_val hext hvok) hwfS' hwfg

theorem Extend_store_globalinsts (s s' : store) (vs : List globalinst) (ts : List globaltype) :
    Extend_store s s' → Forall₂ (fun v t => Globalinst_ok s v t) vs ts →
    Forall₂ (fun v t => Globalinst_ok s' v t) vs ts :=
  fun hext h p hp => Extend_store_globalinst s s' p.1 p.2 hext (h p hp)

theorem Extend_store_tableinst (s s' : store) (v : tableinst) (t : tabletype) :
    Extend_store s s' → Tableinst_ok s v t → Tableinst_ok s' v t := by
  intro hext h
  have hwfS' : wf_store s' := Extend_store_wf_store' s s' hext
  cases h with
  | mk_Tableinst_ok v_n m_opt rt ref_lst httok hrefs hlen _ hwfti hwftt =>
    exact Tableinst_ok.mk_Tableinst_ok s' v_n m_opt rt ref_lst httok
      (fun r hr => Extend_store_ref s s' rt r hext (hrefs r hr)) hlen hwfS' hwfti hwftt

theorem Extend_store_tableinsts (s s' : store) (vs : List tableinst) (ts : List tabletype) :
    Extend_store s s' → Forall₂ (fun v t => Tableinst_ok s v t) vs ts →
    Forall₂ (fun v t => Tableinst_ok s' v t) vs ts :=
  fun hext h p hp => Extend_store_tableinst s s' p.1 p.2 hext (h p hp)

theorem Extend_store_meminst (s s' : store) (v : meminst) (t : memtype) :
    Extend_store s s' → Meminst_ok s v t → Meminst_ok s' v t := by
  intro hext h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwfS'⟩ := hext
  cases h with
  | mk_Meminst_ok v_n m_opt b_lst hmty hlen _ hwfm hwft =>
    exact Meminst_ok.mk_Meminst_ok s' v_n m_opt b_lst hmty hlen hwfS' hwfm hwft

theorem Extend_store_meminsts (s s' : store) (vs : List meminst) (ts : List memtype) :
    Extend_store s s' → Forall₂ (fun v t => Meminst_ok s v t) vs ts →
    Forall₂ (fun v t => Meminst_ok s' v t) vs ts :=
  fun hext h p hp => Extend_store_meminst s s' p.1 p.2 hext (h p hp)

/-- Rocq `extension_lemmas.v:2563` `Extend_store_externaddrs_func`.
    A second, ergonomically-restated proof of essentially
    `addrs_store_funcs_extension`'s func case (no explicit `holds_upto`
    bound-witness needed); the preferred form downstream. -/
theorem Extend_store_externaddrs_func (s s' : store) (fa : Nat) (ft : functype) :
    Extend_store s s' → Externaddr_ok s (externaddr.FUNC fa) (externtype.FUNC ft) →
    Externaddr_ok s' (externaddr.FUNC fa) (externtype.FUNC ft) :=
  fun hext h => Extend_store_externaddr s s' _ _ hext h

/-! ## The big `Instrs_ok2`/`Instr_ok2` monotonicity theorem (extension_lemmas.v:2574-2678) -/

/-- `Frame_ok` transports along store extension. Rocq does this inline inside
    `Extend_store_ais`'s `Frame` case (`inversion f0; econstructor; eauto`
    with `Extend_store_moduleinst`/`Extend_store_vals`). -/
theorem Extend_store_frame (s s' : store) (f : frame) (C : context) :
    Extend_store s s' → Frame_ok s f C → Frame_ok s' f C := by
  intro hext h
  cases h with
  | mk_Frame_ok val_lst v_minst t_lst0 C0 hminst hlen hvals _ hwfC0 hwff hwflocC =>
    exact Frame_ok.mk_Frame_ok s' val_lst v_minst t_lst0 C0
      (Extend_store_moduleinst s s' v_minst C0 hext hminst) hlen
      (fun p hp => Extend_store_val s s' p.1 p.2 hext (hvals p hp))
      (Extend_store_wf_store' s s' hext) hwfC0 hwff hwflocC

/-- Rocq `extension_lemmas.v:2580` `Extend_store_ais`. **THE big
    monotonicity theorem**: admin-instruction-sequence typing is preserved
    under store extension (given both stores well-formed). Rocq proves this
    via a custom mutual induction principle (`Scheme ais_ok_ind'`,
    `extension_lemmas.v:2574`, over `Instrs_ok2`/`Expr_ok2`/`Instr_ok2`); here the
    generated recursor `Instrs_ok2.rec` already has that shape. Directly reused by
    `type_preservation.v`'s `t_preservation_type` ("Context Instrs"
    congruence case) and `step_moduleinst`. -/
theorem Extend_store_ais (s s' : store) (c : context) (ais : List admininstr) (ft : functype) :
    Extend_store s s' → Store_ok s → Store_ok s' → Instrs_ok2 s c ais ft → Instrs_ok2 s' c ais ft := by
  intro hext _ _ h
  have hwfS' : wf_store s' := Extend_store_wf_store' s s' hext
  -- `Instr_ok2`/`Instrs_ok2`/`Expr_ok2` are one `mutual` block whose store is a
  -- *parameter*, so the generated three-motive recursor already keeps `s` fixed:
  -- no `Scheme`-style custom induction principle is needed (Rocq's `ais_ok_ind'`).
  exact Instrs_ok2.rec
    (motive_1 := fun C ai ft' _ => Instr_ok2 s' C ai ft')
    (motive_2 := fun C ais' ft' _ => Instrs_ok2 s' C ais' ft')
    (motive_3 := fun C ae ts _ => Expr_ok2 s' C ae ts)
    -- Instr_ok2.plain
    (fun C vi t1 t2 hok _ hwfC hwfi => Instr_ok2.plain s' C vi t1 t2 hok hwfS' hwfC hwfi)
    -- Instr_ok2.label
    (fun C vn il al tl tl' _ _ _ hwfC hwfai hwfC2 hvn ih1 ih2 =>
      Instr_ok2.label s' C vn il al tl tl' ih1 ih2 hwfS' hwfC hwfai hwfC2 hvn)
    -- Instr_ok2.Instr_ok2_frame
    (fun C vn fr al tl C' hfr _ _ hwfC hwfC' hwfai hwfC2 hvn ih =>
      Instr_ok2.Instr_ok2_frame s' C vn fr al tl C'
        (Extend_store_frame s s' fr C' hext hfr) ih hwfS' hwfC hwfC' hwfai hwfC2 hvn)
    -- Instr_ok2.call_addr
    (fun C fa t1 t2 hea _ hwfC hwfai hwfxt =>
      Instr_ok2.call_addr s' C fa t1 t2
        (Extend_store_externaddrs_func s s' fa _ hext hea) hwfS' hwfC hwfai hwfxt)
    -- Instr_ok2.ref
    (fun C r rt hr _ hwfC =>
      Instr_ok2.ref s' C r rt (Extend_store_ref s s' rt r hext hr) hwfS' hwfC)
    -- Instr_ok2.trap
    (fun C t1 t2 _ hwfC hwfai => Instr_ok2.trap s' C t1 t2 hwfS' hwfC hwfai)
    -- Instrs_ok2.empty
    (fun C _ hwfC => Instrs_ok2.empty s' C hwfS' hwfC)
    -- Instrs_ok2.instr
    (fun C ai t1 t2 _ _ hwfC hwfai ih => Instrs_ok2.instr s' C ai t1 t2 ih hwfS' hwfC hwfai)
    -- Instrs_ok2.seq
    (fun C a1l a2l t1 t3 t2 _ _ _ hwfC hf1 hf2 ih1 ih2 =>
      Instrs_ok2.seq s' C a1l a2l t1 t3 t2 ih1 ih2 hwfS' hwfC hf1 hf2)
    -- Instrs_ok2.sub
    (fun C al t1' t2' t1 t2 _ hs1 hs2 _ hwfC hf ih =>
      Instrs_ok2.sub s' C al t1' t2' t1 t2 ih hs1 hs2 hwfS' hwfC hf)
    -- Instrs_ok2.Instrs_ok2_frame
    (fun C al tl t1 t2 _ _ hwfC hf ih =>
      Instrs_ok2.Instrs_ok2_frame s' C al tl t1 t2 ih hwfS' hwfC hf)
    -- Expr_ok2.mk_Expr_ok2
    (fun C al tl _ _ hwfC hf ih => Expr_ok2.mk_Expr_ok2 s' C al tl ih hwfS' hwfC hf)
    h

/-! ### Single-instance rebuild helpers for the `construct_*` family

    Each `construct_*` lemma below says "the store component list stays
    well-typed after one in-place update". With "Template B"
    (`HelperLemmas.mem_zip_modify` etc.) handling the zip/index bookkeeping,
    all that is left per lemma is the *single-instance* step: given the old
    element's `*_ok` derivation, rebuild it for the updated element. Those
    steps are collected here, each stated over bare variables so the
    inversions are unproblematic (see the note on the `*_ok_invert` helpers
    near the top of this file). Rocq does these inline inside each
    `construct_*` proof. -/

/-- Every well-typed value is well-formed. Needed to rebuild `wf_globalinst`
    after a `global.set`. The three `ref` cases are the interesting ones:
    `Val_ok.reftype` carries no `wf_val`, but `wf_val`'s `ref` constructors
    have no premises either, so they are discharged directly. -/
theorem Val_ok_wf_val (s : store) (v : val) (t : valtype) : Val_ok s v t → wf_val v := by
  intro h
  cases h with
  | numtype _ _ _ hwfv => exact hwfv
  | vectype _ _ _ hwfv => exact hwfv
  | reftype r _ _ _ =>
    cases r with
    | REF_NULL rt => exact wf_val.val_case_2 rt
    | REF_FUNC_ADDR a => exact wf_val.val_case_3 a
    | REF_HOST_ADDR a => exact wf_val.val_case_4 a

/-- `elem.drop`: emptying an eleminst's `REFS` preserves `Eleminst_ok`. -/
theorem eleminst_ok_drop (s : store) (e : eleminst) (t : elemtype) :
    Eleminst_ok s e t → Eleminst_ok s { e with REFS := [] } t := by
  intro h
  cases h with
  | mk_Eleminst_ok _ _ _ _ hwfS =>
    exact Eleminst_ok.mk_Eleminst_ok s t [] (by intro r hr; simp [Forall] at hr) (by simp) hwfS

/-- `data.drop`: emptying a datainst's `BYTES` preserves `Datainst_ok`. -/
theorem datainst_ok_drop (s : store) (d : datainst) :
    Datainst_ok s d datatype.OK → Datainst_ok s (datainst.MKdatainst []) datatype.OK := by
  intro h
  cases h with
  | mk_Datainst_ok _ _ hwfS _ =>
    exact Datainst_ok.mk_Datainst_ok s [] (by simp) hwfS
      (wf_datainst.datainst_case_ [] (by simp [Forall]))

/-- `global.set`: overwriting a globalinst's `VALUE` with a value of the
    declared valtype preserves `Globalinst_ok` (the globaltype is unchanged,
    so mutability plays no role in the *typing* obligation). -/
theorem globalinst_ok_set (s : store) (g : globalinst) (t : globaltype) (v_mut : «mut»)
    (vt : valtype) (v : val) :
    Globalinst_ok s g t → t = globaltype.mk_globaltype v_mut vt → Val_ok s v vt →
    Globalinst_ok s { g with VALUE := v } t := by
  intro h ht hvok
  cases h with
  | mk_Globalinst_ok v_mut' vt' _ hgtok _ hwfS _ =>
    injection ht with _ hvt
    subst hvt
    exact Globalinst_ok.mk_Globalinst_ok s v_mut' vt' v hgtok hvok hwfS
      (wf_globalinst.globalinst_case_ _ v (Val_ok_wf_val s v vt' hvok))

/-- `table.set`: overwriting one slot of a tableinst's `REFS` with a
    correctly-typed `ref` preserves `Tableinst_ok`. -/
theorem tableinst_ok_set (s : store) (tb : tableinst) (ty : tabletype) (lim : limits)
    (t : reftype) (i : Nat) (r : ref) :
    Tableinst_ok s tb ty → ty = tabletype.mk_tabletype lim t → Ref_ok s r t →
    Tableinst_ok s { tb with REFS := list_update_func tb.REFS i (fun _ => r) } ty := by
  intro h ht hr
  cases h with
  | mk_Tableinst_ok v_n m_opt rt ref_lst httok hrefs hlen hwfS _ hwftt =>
    injection ht with _ hrt
    subst hrt
    refine Tableinst_ok.mk_Tableinst_ok s v_n m_opt rt
      (list_update_func ref_lst i (fun _ => r)) httok ?_ ?_ hwfS
      (wf_tableinst.tableinst_case_ _ _ hwftt) hwftt
    · intro x hx
      rcases mem_modify (fun _ => r) ref_lst i x hx with hx' | ⟨rfl, _⟩
      · exact hrefs x hx'
      · exact hr
    · rw [list_update_length_func]; exact hlen

/-- `memory.store`/`memory.init`: splicing well-formed bytes into a meminst's
    `BYTES` preserves `Meminst_ok` (`list_slice_update` is length-preserving,
    so the page-count invariant survives untouched). -/
theorem meminst_ok_store (s : store) (mi : meminst) (ty : memtype) (v_i : Nat) (v_nb : List byte) :
    Meminst_ok s mi ty → Forall wf_byte v_nb →
    Meminst_ok s { mi with BYTES := list_slice_update mi.BYTES v_i v_nb.length v_nb } ty := by
  intro h hwfnb
  cases h with
  | mk_Meminst_ok v_n m_opt b_lst hmtok hlen hwfS hwfmi hwfmt =>
    have hwfbs : Forall wf_byte b_lst := by
      cases hwfmi with | meminst_case_ _ _ _ hb => exact hb
    refine Meminst_ok.mk_Meminst_ok s v_n m_opt
      (list_slice_update b_lst v_i v_nb.length v_nb) hmtok ?_ hwfS ?_ hwfmt
    · rw [list_slice_update_length]; exact hlen
    · exact wf_meminst.meminst_case_ _ _ (by cases hwfmi with | meminst_case_ _ _ hm _ => exact hm)
        (list_slice_update_forall b_lst v_nb v_i v_nb.length hwfbs hwfnb)

/-! ## "construct_*" lemmas — complementary direction: pre-mutation typing
    witness + fresh `Ref_ok`/`Val_ok` for new payload → post-mutation typing
    witness (extension_lemmas.v:2679-3088). These are
    exactly the ingredients `type_preservation.v`'s `store_extension_reduce`
    needs per store-mutating reduction rule. -/

/-- Every `Ref_ok` derivation carries `wf_store`. -/
theorem Ref_ok_wf_store (s : store) (r : ref) (t : reftype) : Ref_ok s r t → wf_store s := by
  intro h
  cases h <;> assumption

/-- The three facts about a *post-grow* tableinst that `Tableinst_ok`'s
    reconstruction needs, all read off the `Forall wf_tableinst` premise that
    `construct_tableinsts_grow` is handed. The `≤ 2^32-1` bound in particular
    comes from nowhere else: `wf_uN 32` on the new limits minimum is exactly
    `Limits_ok`'s bound, which is why Rocq's proof also reaches for
    `HWftbinsts` at that point. -/
theorem wf_tableinst_parts (nn : Nat) (jo : Option uN) (rt : reftype) (refs : List ref)
    (h : wf_tableinst (tableinst.MKtableinst
      (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN nn) jo) rt) refs)) :
    wf_limits (limits.mk_limits (uN.mk_uN nn) jo) ∧ nn ≤ Int.toNat ((2 ^ 32 : Int) - 1) ∧
      wf_tabletype (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN nn) jo) rt) := by
  cases h with
  | tableinst_case_ _ _ hwftt =>
    have hlim : wf_limits (limits.mk_limits (uN.mk_uN nn) jo) := by
      cases hwftt with | tabletype_case_0 _ _ hl => exact hl
    refine ⟨hlim, ?_, hwftt⟩
    cases hlim with
    | limits_case_0 _ _ hwfu _ => cases hwfu with | uN_case_0 _ hb => exact hb.2

/-- As `wf_tableinst_parts`, for a post-grow meminst. -/
theorem wf_meminst_parts (nn : Nat) (jo : Option uN) (bs : List byte)
    (h : wf_meminst (meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN nn) jo)) bs)) :
    wf_limits (limits.mk_limits (uN.mk_uN nn) jo) ∧ nn ≤ Int.toNat ((2 ^ 32 : Int) - 1) ∧
      wf_memtype (memtype.PAGE (limits.mk_limits (uN.mk_uN nn) jo)) ∧ Forall wf_byte bs := by
  cases h with
  | meminst_case_ _ _ hwfmt hwfbs =>
    have hlim : wf_limits (limits.mk_limits (uN.mk_uN nn) jo) := by
      cases hwfmt with | memtype_case_0 _ hl => exact hl
    refine ⟨hlim, ?_, hwfmt, hwfbs⟩
    cases hlim with
    | limits_case_0 _ _ hwfu _ => cases hwfu with | uN_case_0 _ hb => exact hb.2

/-- Rocq `extension_lemmas.v:2691` `construct_tableinsts`. `table.set`
    preserves table typedness at unchanged type list `ts`. -/
theorem construct_tableinsts (s : store) (ts : List tabletype) (t : reftype) (tba : Nat) (lim : limits)
    (tbr : List ref) (i : Nat) (ref_lst : ref) :
    Forall₂ (fun v ty => Tableinst_ok s v ty) s.TABLES ts → Ref_ok s ref_lst t →
    lookup_total s.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype lim t) tbr →
    Forall₂ (fun v ty => Tableinst_ok s v ty)
      (list_update_func s.TABLES tba (fun v1 => { v1 with REFS := list_update_func v1.REFS i (fun _ => ref_lst) })) ts := by
  intro h hr hlk p hp
  rcases mem_zip_modify _ s.TABLES ts tba p hp with hp' | ⟨h1, h2⟩
  · exact h p hp'
  · have hok := h _ h2
    rw [show (s.TABLES[tba]! : tableinst) = lookup_total s.TABLES tba from rfl, hlk] at hok h1
    obtain ⟨_, _, _, he1, _, _, _⟩ := tableinst_ok_invert s _ p.2 hok
    injection he1 with hA _
    rw [h1]
    exact tableinst_ok_set s _ p.2 lim t i ref_lst hok hA.symm hr

/-- Rocq `extension_lemmas.v:2740` `construct_tableinsts_grow`. Takes a `Forall
    wf_tableinst tbinsts` premise; the post-`table.grow` table list is
    bound via an explicit `tbinsts = ...` hypothesis rather than written
    inline in the conclusion. -/
theorem construct_tableinsts_grow (s : store) (ts : List tabletype) (ref_lst : ref) (t : reftype)
    (tba : Nat) (v_r : List ref) (j_opt : Option uN) (v_n : Nat) (tbinsts : List tableinst) :
    Forall wf_tableinst tbinsts →
    Forall₂ (fun v ty => Tableinst_ok s v ty) s.TABLES ts → Ref_ok s ref_lst t →
    Forall (fun v_j => v_r.length + v_n ≤ (proj_uN_0 v_j)) (Option.toList j_opt) →
    lookup_total s.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_r.length) j_opt) t) v_r →
    tbinsts = list_update_func s.TABLES tba (fun _ => tableinst.MKtableinst
        (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (v_r.length + v_n)) j_opt) t) (v_r ++ List.replicate v_n ref_lst)) →
    Forall₂ (fun v ty => Tableinst_ok s v ty) tbinsts
      (list_update_func ts tba (fun _ => tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (v_r.length + v_n)) j_opt) t)) := by
  intro hwftb h hr hrange hlk heq p hp
  subst heq
  rcases mem_zip_modify₂ _ _ s.TABLES ts tba p hp with hp' | ⟨h1, h2, h3⟩
  · exact h p hp'
  · have hwfp1 : wf_tableinst p.1 := hwftb p.1 (List.of_mem_zip hp).1
    rw [h1] at hwfp1
    have hok := h _ h3
    rw [show (s.TABLES[tba]! : tableinst) = lookup_total s.TABLES tba from rfl, hlk] at hok
    obtain ⟨rl0, v_m, rt, he1, he2, httok, hrefs⟩ := tableinst_ok_invert s _ (ts[tba]!) hok
    injection he1 with hA hB
    rw [← hA] at he2 httok
    injection he2 with hC hrt
    injection hC with hD hjo
    subst hjo
    subst hrt
    rw [← hB] at hrefs
    -- old limits bound: the declared max (if any) is still ≤ 2^32-1
    have holdlim : Limits_ok (limits.mk_limits (uN.mk_uN v_r.length) (v_m.map uN.mk_uN))
        (Int.toNat ((2 ^ 32 : Int) - 1)) := by
      cases httok with | mk_Tabletype_ok _ _ hl _ => exact hl
    have hmbound := (limits_ok_invert _ _ holdlim v_r.length v_m rfl).2
    -- new well-formedness, from the `Forall wf_tableinst` premise
    obtain ⟨hwflim2, hbound2, hwftt2⟩ :=
      wf_tableinst_parts (v_r.length + v_n) (v_m.map uN.mk_uN) t (v_r ++ List.replicate v_n ref_lst) hwfp1
    rw [h1, h2]
    refine Tableinst_ok.mk_Tableinst_ok s (v_r.length + v_n) v_m t
      (v_r ++ List.replicate v_n ref_lst) ?_ ?_ (by simp)
      (Ref_ok_wf_store s ref_lst t hr) hwfp1 hwftt2
    · refine Tabletype_ok.mk_Tabletype_ok _ t
        (Limits_ok.mk_Limits_ok (v_r.length + v_n) v_m _ hbound2 ?_ hwflim2) hwftt2
      intro mm hmm
      refine ⟨?_, (hmbound mm hmm).2⟩
      have hmem : uN.mk_uN mm ∈ Option.toList (v_m.map uN.mk_uN) := by
        rcases v_m with _ | mm0 <;> simp_all
      exact hrange _ hmem
    · intro x hx
      rcases List.mem_append.mp hx with hx1 | hx2
      · exact hrefs x hx1
      · rw [List.eq_of_mem_replicate hx2]; exact hr

/-- Rocq `extension_lemmas.v:2830` `construct_globalinsts`. `global.set`
    preserves global typedness (type list unchanged, mutable globals don't
    change globaltype). -/
theorem construct_globalinsts (s : store) (ts : List globaltype) (ga : Nat) (v : val) (t : valtype) (v_old : val) :
    Forall₂ (fun v0 ty => Globalinst_ok s v0 ty) s.GLOBALS ts →
    lookup_total s.GLOBALS ga = globalinst.MKglobalinst (globaltype.mk_globaltype (some r_MUT.MUT) t) v_old →
    Val_ok s v t →
    Forall₂ (fun v0 ty => Globalinst_ok s v0 ty) (list_update_func s.GLOBALS ga (fun g => { g with VALUE := v })) ts := by
  intro h hlk hvok p hp
  rcases mem_zip_modify _ s.GLOBALS ts ga p hp with hp' | ⟨h1, h2⟩
  · exact h p hp'
  · have hok := h _ h2
    rw [show (s.GLOBALS[ga]! : globalinst) = lookup_total s.GLOBALS ga from rfl, hlk] at hok h1
    obtain ⟨_, _, _, he1, _, _⟩ := globalinst_ok_invert s _ p.2 hok
    injection he1 with hA _
    rw [h1]
    exact globalinst_ok_set s _ p.2 (some r_MUT.MUT) t v hok hA.symm hvok

/-- Raw inversion of `Meminst_ok` over bare variables, keeping the
    *multiplicative* byte-length equation `|bs| = n * 64Ki` that
    `meminst_ok_invert` above converts to the division form `s_invert_mems`
    wants. `construct_meminsts_grow` needs the multiplicative one. -/
theorem meminst_ok_raw (s : store) (mi : meminst) (ty : memtype) :
    Meminst_ok s mi ty → ∃ (v_n : Nat) (m_opt : Option Nat) (bs : List byte),
      mi = meminst.MKmeminst
        (memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN))) bs ∧
      ty = memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN)) ∧
      bs.length = v_n * (64 * Ki) ∧
      Memtype_ok (memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN))) ∧
      wf_store s := by
  intro h
  cases h with
  | mk_Meminst_ok v_n m_opt bs hmtok hlen hwfS _ _ =>
    exact ⟨v_n, m_opt, bs, rfl, rfl, hlen, hmtok, hwfS⟩

/-- Rocq `extension_lemmas.v:2859` `construct_meminsts`. Takes a `Forall wf_byte
    v_nb` premise; the slice length is `v_nb.length` directly, as Rocq writes `(|v_nb|)`
    inline rather than a separate length parameter. -/
theorem construct_meminsts (s : store) (ts : List memtype) (ma : Nat) (v_mt : memtype) (b_lst : List byte)
    (v_i : Nat) (v_nb : List byte) :
    Forall wf_byte v_nb →
    Forall₂ (fun v ty => Meminst_ok s v ty) s.MEMS ts →
    lookup_total s.MEMS ma = meminst.MKmeminst v_mt b_lst →
    Forall₂ (fun v ty => Meminst_ok s v ty)
      (list_update_func s.MEMS ma (fun m => { m with BYTES := list_slice_update m.BYTES v_i v_nb.length v_nb })) ts := by
  intro hwfnb h hlk p hp
  rcases mem_zip_modify _ s.MEMS ts ma p hp with hp' | ⟨h1, h2⟩
  · exact h p hp'
  · rw [h1]
    exact meminst_ok_store s _ p.2 v_i v_nb (h _ h2) hwfnb

/-- Rocq `extension_lemmas.v:2918` `construct_meminsts_grow`.
    The `lim_old + v_n ≤ 2 ^ 16` premise mirrors `$growmemory`'s `-- if i' <= $(2^16)` side
    condition. `Nat`-based rather than Rocq's `Q` (byte counts and page counts are naturals
    in this model). The declared max is a genuine `Option` (`v_j_opt`), as in
    Rocq. The proof follows `construct_tableinsts_grow`. -/
theorem construct_meminsts_grow (s : store) (ts : List memtype) (ma : Nat) (b_lst : List byte)
    (lim_old v_n : Nat) (v_j_opt : Option uN) (minsts : List meminst) :
    Forall wf_meminst minsts →
    Forall₂ (fun v ty => Meminst_ok s v ty) s.MEMS ts →
    lookup_total s.MEMS ma = meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN lim_old) v_j_opt)) b_lst →
    lim_old = b_lst.length / (64 * Ki) →
    Forall (fun v_j => lim_old + v_n ≤ (proj_uN_0 v_j)) (Option.toList v_j_opt) → lim_old + v_n ≤ 2 ^ 16 →
    minsts = list_update_func s.MEMS ma (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (lim_old + v_n)) v_j_opt))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))) →
    Forall₂ (fun v ty => Meminst_ok s v ty) minsts
      (list_update_func ts ma (fun _ => memtype.PAGE (limits.mk_limits (uN.mk_uN (lim_old + v_n)) v_j_opt))) := by
  intro hwfm h hlk _ hrange hle2 heq p hp
  subst heq
  rcases mem_zip_modify₂ _ _ s.MEMS ts ma p hp with hp' | ⟨h1, h2, h3⟩
  · exact h p hp'
  · have hwfp1 : wf_meminst p.1 := hwfm p.1 (List.of_mem_zip hp).1
    rw [h1] at hwfp1
    have hok := h _ h3
    rw [show (s.MEMS[ma]! : meminst) = lookup_total s.MEMS ma from rfl, hlk] at hok
    obtain ⟨vn0, m_opt, bs0, he1, _, hblen, hmtok, hwfS⟩ := meminst_ok_raw s _ (ts[ma]!) hok
    injection he1 with hA hB
    injection hA with hA'
    injection hA' with hA1 hA2
    injection hA1 with hn
    subst hn
    subst hB
    subst hA2
    -- old `Memtype_ok` bounds the declared max (if any) by 2^16
    have holdlim : Limits_ok (limits.mk_limits (uN.mk_uN lim_old) (m_opt.map uN.mk_uN)) (2 ^ 16) := by
      cases hmtok with | mk_Memtype_ok _ hl _ => exact hl
    have hjbound := (limits_ok_invert _ _ holdlim lim_old m_opt rfl).2
    obtain ⟨hwflim2, _, hwfmt2, _⟩ :=
      wf_meminst_parts (lim_old + v_n) (m_opt.map uN.mk_uN)
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) hwfp1
    rw [h1, h2]
    refine Meminst_ok.mk_Meminst_ok s (lim_old + v_n) m_opt
      (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) ?_ ?_ hwfS hwfp1 hwfmt2
    · refine Memtype_ok.mk_Memtype_ok _
        (Limits_ok.mk_Limits_ok (lim_old + v_n) m_opt (2 ^ 16) hle2 ?_ hwflim2) hwfmt2
      intro mm hmm
      refine ⟨?_, (hjbound mm hmm).2⟩
      have hmem : uN.mk_uN mm ∈ Option.toList (m_opt.map uN.mk_uN) := by
        rcases m_opt with _ | mm0
        · simp at hmm
        · simp only [Option.toList_some, List.mem_singleton] at hmm
          subst hmm
          simp
      exact hrange _ hmem
    · simp only [List.length_append, List.length_replicate, hblen]
      exact (Nat.add_mul lim_old v_n (64 * Ki)).symm

/-- Rocq `extension_lemmas.v:3041` `construct_datainsts`. `data.drop`
    preserves data typedness trivially. -/
theorem construct_datainsts (s : store) (da : Nat) (b_lst : List byte) :
    Forall (fun a => Datainst_ok s a datatype.OK) s.DATAS → lookup_total s.DATAS da = datainst.MKdatainst b_lst →
    Forall (fun a => Datainst_ok s a datatype.OK) (list_update_func s.DATAS da (fun _ => datainst.MKdatainst [])) := by
  intro h hlk x hx
  rcases mem_modify _ s.DATAS da x hx with hx' | ⟨h1, h2⟩
  · exact h x hx'
  · rw [h1]
    exact datainst_ok_drop s _ (h _ h2)

/-- Rocq `extension_lemmas.v:3066` (last declaration in file) `construct_eleminsts`.
    `elem.drop` preserves element typedness trivially. -/
theorem construct_eleminsts (s : store) (ts : List elemtype) (ea : Nat) (t : elemtype) (ref_lst : List ref) :
    Forall₂ (fun v ty => Eleminst_ok s v ty) s.ELEMS ts →
    lookup_total s.ELEMS ea = eleminst.MKeleminst t ref_lst →
    Forall₂ (fun v ty => Eleminst_ok s v ty) (list_update_func s.ELEMS ea (fun e => { e with REFS := [] })) ts := by
  intro h hlk p hp
  rcases mem_zip_modify _ s.ELEMS ts ea p hp with hp' | ⟨h1, h2⟩
  · exact h p hp'
  · rw [h1]
    exact eleminst_ok_drop s _ p.2 (h _ h2)

end TLC
