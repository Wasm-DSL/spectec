import Mathlib.Tactic
import «wasm2.0»

/-!
# HelperLemmas

Lean port of `spectec/test-rocq/theories/helper_lemmas.v` (general
list/predicate/arithmetic helper lemmas used throughout the Rocq WASM 2.0
type safety proof), plus all 21 axioms of `axioms.v` (after Section 9) and, at the end of the
file, Lean-only infrastructure for the model regenerated with `sideconditions_on_defs`: function
views of the size relations the proofs use, of `fzero` and of `default_`, and inversion lemmas for
the state lookups.

Provenance: every ported declaration cites its Rocq source line number in
`spectec/test-rocq/theories` at upstream `rocq-backend-proof` `6582b3a39`; a lemma that
upstream has since removed is cited at revision `5b03ae067`, the one this file was first
ported from, and says so. Lean-only helpers say that they are. Full
structural digest this was ported from:
`claude-logging/for-claude/NOTES.md` (inline digest section) and
`claude-logging/for-claude/digest_wasm_v.md`.

Per project policy: proof *method* is free to differ from Rocq's
ssreflect/mathcomp tactics (Lean has proof irrelevance), but *signatures*
mirror the Rocq statements. A handful of Rocq lemmas exist purely to
bridge Coq's two parallel list libraries (mathcomp `seq` vs stdlib
`List`) or to work around ssreflect rewriting quirks (the Rocq author's
own comment flags some of these as removable); those are noted inline but
not ported, since Lean has exactly one list type and no such need.

The unused lemmas the user marked for
deletion have been deleted; their Rocq citations remain below as `DELETED BECAUSE NOT USED`
notes.
-/

namespace TLC

/-! ## Prelude helpers (from wasm.v's hand-written prelude, not backend-generated) -/

/-- Rocq `wasm.v:10`: `lookup_total {T} {Inhabited T} (l : seq T) (n : N) : T :=
    seq.nth default_val l (N.to_nat n)`. Lean indexes by `Nat`. -/
-- TODO FROM USER: This looks like a Rocq-specific design choice that I overturned in my handwritten test-lean. Investigate further to see if this is necessary.
def lookup_total {α : Type} [Inhabited α] (l : List α) (n : Nat) : α := l[n]!

/-- Rocq `wasm.v:31`: `Fixpoint list_update {A} (l : seq A) (n : N) (y : A) : seq A`. Matches
    `List.set` (with a `Nat` index). -/
abbrev list_update {α : Type} (l : List α) (n : Nat) (y : α) : List α := l.set n y

/-- Rocq `wasm.v:51`: `Fixpoint list_update_func {A} (l : seq A) (n : N) (y : A -> A) : seq A`.
    Matches `List.modify` (with a `Nat` index). -/
abbrev list_update_func {α : Type} (l : List α) (n : Nat) (f : α → α) : List α := l.modify n f

/-- Lean-only helper (no Rocq counterpart; "Template A"). The `[a]!`-indexed
    characterization of `List.modify` used for the `*_extension`
    lemmas' `holds_upto`-monotonicity goals: at the modified index, the
    updated value is `f` applied to the old one; elsewhere, unchanged. Built
    from Lean core's `getElem_modify_eq`/`getElem_modify_ne`
    (`Init/Data/List/Nat/Modify.lean`) via the standard `[a]!`-to-`[a]'h`
    bridge (`getElem!_pos`). -/
theorem getElem!_modify_eq_or_ne {α : Type} [Inhabited α] (l : List α) (idx a : Nat) (f : α → α)
    (ha : a < l.length) :
    (l.modify idx f)[a]! = if a = idx then f (l[a]!) else l[a]! := by
  have hmod : a < (l.modify idx f).length := by simp [ha]
  rw [getElem!_pos (l.modify idx f) a hmod]
  by_cases h : a = idx
  · subst h
    rw [List.getElem_modify_eq f a l (by simpa using hmod), getElem!_pos l a ha]
    simp
  · rw [List.getElem_modify_ne f l (Ne.symm h) hmod, getElem!_pos l a ha, if_neg h]

/-! ### "Template B": membership in a `zip` after a `List.modify`

    Lean-only helpers (no Rocq counterpart). Rocq's
    `Forall2` is an *inductive* relation, so its `construct_*` proofs in
    `extension_lemmas.v` can induct on it directly and peel off the updated
    position. This codebase's generated `Forall₂` is the zip-based `def`
    `∀ p ∈ xs.zip ys, P p.1 p.2`, so the corresponding step is: "every pair in
    the zip of a modified list is either an original pair, or the image of the
    pair at the modified index". That is exactly what these three lemmas say,
    and they are what the `ExtensionLemmas.lean` `construct_*` family
    uses for the position correlation. Each also hands back membership of the
    *original* element, so the caller can feed it the `Forall`/`Forall₂`
    hypothesis it already has. -/

theorem mem_modify {α : Type} [Inhabited α] (f : α → α) (l : List α) :
    ∀ (idx : Nat) (x : α), x ∈ l.modify idx f → x ∈ l ∨ (x = f (l[idx]!) ∧ l[idx]! ∈ l) := by
  induction l with
  | nil => intro idx x hx; simp at hx
  | cons a l ih =>
    intro idx x hx
    cases idx with
    | zero =>
      simp only [List.modify_zero_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr ⟨by simp, by simp⟩
      · exact Or.inl (by simp [hx])
    | succ i =>
      simp only [List.modify_succ_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl (by simp)
      · rcases ih i x hx with h | ⟨h1, h2⟩
        · exact Or.inl (by simp [h])
        · exact Or.inr ⟨by simpa using h1, by simpa using List.mem_cons_of_mem a h2⟩

theorem mem_zip_modify {α β : Type} [Inhabited α] (f : α → α) (l : List α) :
    ∀ (ts : List β) (idx : Nat) (p : α × β), p ∈ (l.modify idx f).zip ts →
      p ∈ l.zip ts ∨ (p.1 = f (l[idx]!) ∧ (l[idx]!, p.2) ∈ l.zip ts) := by
  induction l with
  | nil => intro ts idx p hp; simp at hp
  | cons a l ih =>
    intro ts idx p hp
    cases ts with
    | nil => simp at hp
    | cons b ts =>
      cases idx with
      | zero =>
        simp only [List.modify_zero_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inr ⟨by simp, by simp⟩
        · exact Or.inl (by simp [hp])
      | succ i =>
        simp only [List.modify_succ_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inl (by simp)
        · rcases ih ts i p hp with h | ⟨h1, h2⟩
          · exact Or.inl (by simp [h])
          · exact Or.inr ⟨by simpa using h1, by simpa using List.mem_cons_of_mem (a, b) h2⟩

theorem mem_zip_modify₂ {α β : Type} [Inhabited α] [Inhabited β] (f : α → α) (g : β → β)
    (l : List α) :
    ∀ (ts : List β) (idx : Nat) (p : α × β), p ∈ (l.modify idx f).zip (ts.modify idx g) →
      p ∈ l.zip ts ∨
        (p.1 = f (l[idx]!) ∧ p.2 = g (ts[idx]!) ∧ (l[idx]!, ts[idx]!) ∈ l.zip ts) := by
  induction l with
  | nil => intro ts idx p hp; simp at hp
  | cons a l ih =>
    intro ts idx p hp
    cases ts with
    | nil => simp at hp
    | cons b ts =>
      cases idx with
      | zero =>
        simp only [List.modify_zero_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inr ⟨by simp, by simp, by simp⟩
        · exact Or.inl (by simp [hp])
      | succ i =>
        simp only [List.modify_succ_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inl (by simp)
        · rcases ih ts i p hp with h | ⟨h1, h2, h3⟩
          · exact Or.inl (by simp [h])
          · exact Or.inr ⟨by simpa using h1, by simpa using h2,
              by simpa using List.mem_cons_of_mem (a, b) h3⟩

/-- Rocq `wasm.v:66-74`: `Fixpoint list_slice_update {A} (l : seq A) (i j : N) (update_l : seq A) :
    seq A`, replacing (up to) the `n`-element slice `[i, i+n)` of `l` with `update_l` (where
    `n = |update_l|` at every call site). Mirrors Rocq's structural recursion exactly: it
    recurses element-by-element down `l`, stops early and returns the untouched remainder as
    soon as either the index countdown or `update_l` itself runs out, and is therefore
    *unconditionally* length-preserving (`list_slice_update_length` below needs no side
    hypothesis, matching Rocq). A `take`/`append`/`drop` formulation would be length-preserving
    only when `n = update_l.length`. -/
def list_slice_update {α : Type} (l : List α) (i n : Nat) (update_l : List α) : List α :=
  match l, update_l with
  | [], _ => []
  | l, [] => l
  | x :: l', y :: u_l' =>
    match i, n with
    | 0, 0 => x :: l'
    | _ + 1, 0 => x :: l'
    | 0, n + 1 => y :: list_slice_update l' 0 n u_l'
    | i + 1, n => x :: list_slice_update l' i n (y :: u_l')

/-- Rocq `helper_lemmas.v:270`: `Fixpoint In2 {A B} (x : A) (y : B) (l : list A) (l' : list B) :
    Prop`, "the pair (x,y) occurs at the same position in l and l'". -/
def In2 {α β : Type} (x : α) (y : β) (l : List α) (l' : List β) : Prop :=
  match l, l' with
  | [], [] => False
  | [], _ :: _ => False
  | _ :: _, [] => False
  | a :: as', b :: bs' => (a = x ∧ b = y) ∨ In2 x y as' bs'

/-! ## Section 1 : general list/predicate helper lemmas (helper_lemmas.v:17-293) -/

/-- Rocq `helper_lemmas.v:16` `leadd` (`5b03ae067`; since removed upstream). -/
theorem leadd (i n : Nat) : i ≤ i + n := by omega

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:25` `list_update_func_split` (`5b03ae067`; since removed upstream).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:44` `list_update_func_split_strong` (`5b03ae067`; since removed upstream).

/-- Rocq `helper_lemmas.v:64` `length_app_lt` (`5b03ae067`; since removed upstream). -/
theorem length_app_lt {α : Type} (l l' l1' l2' : List α) :
    l.length = l1'.length → l' = l1' ++ l2' → l.length ≤ l'.length := by
  intro hlen heq
  subst heq
  rw [List.length_append]
  omega

-- `nth_is_same_as_seq_nth` (helper_lemmas.v:20) NOT PORTED: pure bridge between Coq's
-- stdlib `List.nth` and mathcomp's `seq.nth`; Lean has one list library, no counterpart needed.

/-- Rocq `helper_lemmas.v:40` `length_same_split_zero`. -/
theorem length_same_split_zero {α : Type} (l l2' : List α) :
    l.length = l.length + l2'.length → l2'.length = 0 := by
  intro h; omega

/-- Rocq `helper_lemmas.v:52` `length_app_both_nil`. -/
theorem length_app_both_nil {α : Type} (l l' l1' l2' : List α) :
    l.length = l'.length → l.length = l1'.length → l' = l1' ++ l2' → l2' = [] := by
  intro h1 h2 h3
  have hlen : l2'.length = 0 := by
    rw [h3, List.length_append] at h1
    omega
  cases l2' with
  | nil => rfl
  | cons a as => simp at hlen

/-- Rocq `helper_lemmas.v:68` `length_app_nil`. -/
theorem length_app_nil {α : Type} (l' l1' l2' : List α) :
    l'.length = l1'.length → l' = l1' ++ l2' → l2' = [] := by
  intro h1 h2
  have hlen : l2'.length = 0 := by
    rw [h2, List.length_append] at h1
    omega
  cases l2' with
  | nil => rfl
  | cons a as => simp at hlen

/-- Rocq `helper_lemmas.v:135` `Forall_nth'` (`5b03ae067`; since removed upstream). That
    revision also had the near-duplicate `Forall_size`, which differed only by a
    stdlib/mathcomp `List.nth`↔`nth` bridge not needed here; current Rocq keeps only
    `Forall_size` (below, same statement). -/
theorem Forall_nth' {α : Type} [Inhabited α] (l : List α) (R : α → Prop) :
    Forall R l → ∀ i, i < l.length → R (lookup_total l i) := by
  intro h i hi
  simp only [lookup_total, getElem!_pos l i hi]
  exact h (l[i]'hi) (List.getElem_mem hi)

/-- Rocq `helper_lemmas.v:141` `Forall_size`. Same statement as `Forall_nth'` above, its
    near-duplicate before the upstream `nat`→`N` rework. -/
theorem Forall_size {α : Type} [Inhabited α] (l : List α) (R : α → Prop) :
    Forall R l → ∀ i, i < l.length → R (lookup_total l i) :=
  Forall_nth' l R

/-- Membership of the same-index pair in a `zip`, given both bounds. The
    missing half of "Template B": `Forall₂`'s zip representation makes
    *pointwise* facts free but says nothing index-correlated until you can
    exhibit the pair. Lean-only helper. -/
theorem mem_zip_getElem! {α β : Type} [Inhabited α] [Inhabited β] (l : List α) :
    ∀ (l' : List β) (i : Nat), i < l.length → i < l'.length → (l[i]!, l'[i]!) ∈ l.zip l' := by
  induction l with
  | nil => intro l' i hi _; simp at hi
  | cons a l ih =>
    intro l' i hi hi'
    cases l' with
    | nil => simp at hi'
    | cons b l' =>
      cases i with
      | zero => simp
      | succ j =>
        simp only [List.zip_cons_cons, List.mem_cons]
        exact Or.inr (by simpa using ih l' j (by simpa using hi) (by simpa using hi'))

/-- Index-wise consequence of `Forall₂`, *with* the length hypothesis supplied
    explicitly (Lean-only; `Forall2_size` below is this fact in Rocq's argument order). Rocq's
    `Forall2_nth`/`Forall2_size` *derive* `l.length = l'.length` from the inductive
    `Forall2`, which this codebase's zip-based `Forall₂` cannot do (see the bridge
    section at the end of this file), so callers pass the length in instead — every
    call site has it. -/
theorem Forall2_nth_of_length {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    (l : List α) (l' : List β) (h : Forall₂ R l l') (hlen : l.length = l'.length)
    (i : Nat) (hi : i < l.length) : R (l[i]!) (l'[i]!) :=
  h _ (mem_zip_getElem! l l' i hi (hlen ▸ hi))

/-- Rocq `helper_lemmas.v:170` `Forall2_size`.
    **Deviation (zip-based `Forall₂`):** Rocq's inductive `Forall2` forces equal lengths, from
    which Rocq derives the pointwise fact; Lean's generated `Forall₂` is zip-based, so the length
    equation is an explicit premise `hlen` (project precedent: `funcinst_same`, `Vals_ok`). Rocq's
    `l [|i|]` (`lookup_total`) is Lean's `l[i]!`. -/
theorem Forall2_size {α β : Type} [Inhabited α] [Inhabited β] (l : List α) (l' : List β)
    (R : α → β → Prop) (hlen : l.length = l'.length) :
    Forall₂ R l l' → ∀ (i : Nat), i < l.length → R (l[i]!) (l'[i]!) :=
  fun h i hi => Forall2_nth_of_length l l' h hlen i hi

/-- Rocq `helper_lemmas.v:186` `Forall2_size2`: `Forall2_size` with the index
    bounded by the second list. Same **deviation** (`hlen`) as `Forall2_size`. -/
theorem Forall2_size2 {α β : Type} [Inhabited α] [Inhabited β] (l : List α) (l' : List β)
    (R : α → β → Prop) (hlen : l.length = l'.length) :
    Forall₂ R l l' → ∀ (i : Nat), i < l'.length → R (l[i]!) (l'[i]!) :=
  fun h i hi => Forall2_nth_of_length l l' h hlen i (hlen ▸ hi)

-- `Forall2_seq_size` (helper_lemmas.v:159, `Forall2 R l l' -> |l| = |l'|`) NOT PORTED: with the
-- zip-based `Forall₂` the conclusion is not derivable, and adding `hlen` would make the lemma
-- return its own premise; Lean callers use the length fact they already have (`Vals_ok`,
-- `Moduleinst_ok_lengths`, `hlen` premises).

theorem mem_zip_modify_right {α β : Type} [Inhabited α] [Inhabited β] (g : β → β)
    (l : List α) :
    ∀ (ts : List β) (idx : Nat) (p : α × β), p ∈ l.zip (ts.modify idx g) →
      p ∈ l.zip ts ∨
        (p.1 = l[idx]! ∧ p.2 = g (ts[idx]!) ∧ (l[idx]!, ts[idx]!) ∈ l.zip ts) := by
  induction l with
  | nil => intro ts idx p hp; simp at hp
  | cons a l ih =>
    intro ts idx p hp
    cases ts with
    | nil => simp at hp
    | cons b ts =>
      cases idx with
      | zero =>
        simp only [List.modify_zero_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inr ⟨by simp, by simp, by simp⟩
        · exact Or.inl (by simp [hp])
      | succ i =>
        simp only [List.modify_succ_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inl (by simp)
        · rcases ih ts i p hp with h | ⟨h1, h2, h3⟩
          · exact Or.inl (by simp [h])
          · exact Or.inr ⟨by simpa using h1, by simpa using h2,
              by simpa using List.mem_cons_of_mem (a, b) h3⟩

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:153` `Forall2_nth`, merged with `Forall2_nth2` (helper_lemmas.v:167)
--    (`5b03ae067`; since removed upstream; see `Forall2_size`/`Forall2_nth_of_length`).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:181` `Forall2_lookup`, merged with `Forall2_lookup2`
--     (helper_lemmas.v:194) (`5b03ae067`; since removed upstream; same content as `Forall2_nth`
--     phrased via `lookup_total`).

-- `in_same_as_In` (helper_lemmas.v:229) NOT PORTED: bridges mathcomp's boolean `\in` with
-- stdlib's `List.In`; Lean has one membership notion (`∈`), no counterpart needed.

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:256` `lookup_list_update_func` (`5b03ae067`; since removed upstream).


/-- Rocq `helper_lemmas.v:278` `In2_split`. -/
theorem In2_split {α β : Type} (x : α) (y : β) (l : List α) (l' : List β) :
    In2 x y l l' → x ∈ l ∧ y ∈ l' := by
  induction l generalizing l' with
  | nil => cases l' <;> (intro h; simp only [In2] at h)
  | cons a as ih =>
    cases l' with
    | nil => intro h; simp only [In2] at h
    | cons b bs =>
      intro h
      simp only [In2] at h
      rcases h with ⟨ha, hb⟩ | h
      · subst ha; subst hb; exact ⟨List.mem_cons_self, List.mem_cons_self⟩
      · obtain ⟨hx, hy⟩ := ih bs h
        exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:286` `Forall2_forall2` (`5b03ae067`; since removed upstream).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:313` `Forall2_forall2weak` (`5b03ae067`; since removed upstream).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:325` `Forall2_forall2weak2` (`5b03ae067`; since removed upstream).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:336` `Forall2_forall2weak3` (`5b03ae067`; since removed upstream).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:351` `Forall2_forall2weak4` (`5b03ae067`; since removed upstream).

/-! ## Section 2 : Forall2 interaction with list_update / list_update_func / lookup_total
    (helper_lemmas.v:294-334; the deleted `Forall2_list_update*` lemmas are from revision
    `5b03ae067`, except `Forall2_list_update_func2`, still at helper_lemmas.v:202) -/

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:366` `Forall2_list_update_func` (`5b03ae067`; since removed upstream).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:202` `Forall2_list_update_func2`.

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:414` `Forall2_list_update` (`5b03ae067`; since removed upstream).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:436` `Forall2_list_update2` (`5b03ae067`; since removed upstream).

-- DELETED BECAUSE NOT USED
-- Rocq `helper_lemmas.v:458` `Forall2_list_update_both` (`5b03ae067`; since removed upstream).

/-- Rocq `helper_lemmas.v:294` `list_update_length`. -/
theorem list_update_length {α : Type} (l : List α) (i : Nat) (x : α) :
    (list_update l i x).length = l.length := List.length_set

/-- Rocq `helper_lemmas.v:310` `list_update_length_func`. -/
theorem list_update_length_func {α : Type} (l : List α) (f : α → α) (i : Nat) :
    (list_update_func l i f).length = l.length := List.length_modify f l i

/-- Rocq `helper_lemmas.v:325` `list_slice_update_length`. Unconditional, as in Rocq, because
    `list_slice_update` follows Rocq's structural recursion (see its comment); a
    `take`/`append`/`drop`-based definition would need `n = l'.length` as a side hypothesis. -/
theorem list_slice_update_length {α : Type} (l l' : List α) (i n : Nat) :
    (list_slice_update l i n l').length = l.length := by
  induction l, i, n, l' using list_slice_update.induct
  all_goals (first | rfl | simp_all [list_slice_update])

/-- Lean-only helper (Rocq proves the same fact inline, as `Hslice` inside a `wasm.v` proof;
    needed by `ExtensionLemmas.lean`'s `store_none_mem_extension`/`construct_meminsts`:
    a `memory.store`/`memory.init` writes a slice of fresh, already-known-
    well-formed bytes into an existing, already-well-formed byte buffer; the
    result is well-formed pointwise). Same proof technique as
    `list_slice_update_length` above (`induction ... using
    list_slice_update.induct`), since `Forall P` pointwise-respects the same
    "copy old / splice in new / stop early" recursion that length does. -/
theorem list_slice_update_forall {α : Type} {P : α → Prop} (l l' : List α) (i n : Nat)
    (hl : Forall P l) (hl' : Forall P l') : Forall P (list_slice_update l i n l') := by
  induction l, i, n, l' using list_slice_update.induct with
  | _ => first
    | (simp_all [list_slice_update, Forall])
    | (intro z hz
       simp only [list_slice_update, List.mem_cons] at hz
       rcases hz with rfl | hz'
       · simp_all [Forall, List.mem_cons]
       · simp_all [Forall, List.mem_cons])


/-- `splice` (the generated prelude helper behind `$with_mem`, `wasm2.0.lean:12`) agrees
    with Rocq's `list_slice_update` once the declared
    slice length is the payload's own length. Not a Rocq lemma: it bridges the Lean
    backend's rendering of `BYTES[i : j] = b*` to the Rocq backend's, so the Rocq-shaped
    statements (`store_none_mem_extension`, `construct_meminsts`, `mem_store_extension`, …)
    apply to the model's `$with_mem` (the relation `fun_with_mem`). -/
theorem splice_eq_list_slice_update {α : Type} (l b : List α) (i : Nat) :
    splice l b i = list_slice_update l i b.length b := by
  induction l generalizing b i with
  | nil => simp [splice, list_slice_update]
  | cons x l' ih =>
    cases b with
    | nil => simp [splice, list_slice_update]
    | cons y u =>
      cases i with
      | zero =>
        have h := ih u 0
        simp only [splice] at h ⊢
        simp only [list_slice_update, List.length_cons]
        rw [← h]
        simp [Nat.succ_min_succ]
      | succ i0 =>
        have h := ih (y :: u) i0
        simp only [splice, List.length_cons] at h ⊢
        simp only [list_slice_update]
        rw [← h]
        simp [Nat.succ_min_succ]
        rw [Nat.add_right_comm]
        simp

/-- `splice` never changes the length of the list it writes into (Lean-only). -/
theorem splice_length {α : Type} (l b : List α) (i : Nat) : (splice l b i).length = l.length := by
  rw [splice_eq_list_slice_update]
  exact list_slice_update_length l b i b.length

/-! ## Section 3 : list append/split lemmas (helper_lemmas.v:335-421) -/

/-- Rocq `helper_lemmas.v:335` `split_append_last`. -/
theorem split_append_last {α : Type} (z y : List α) (i j : α) :
    z ++ [i] = y ++ [j] → z = y ∧ i = j := by
  intro h
  have hrev : i :: z.reverse = j :: y.reverse := by
    simpa using congrArg List.reverse h
  injection hrev with hij hzy
  refine ⟨?_, hij⟩
  simpa using congrArg List.reverse hzy

/-- Rocq `helper_lemmas.v:351` `split_append_1`. -/
theorem split_append_1 {α : Type} (z : List α) (i j : α) :
    z ++ [i] = [j] → z = [] ∧ i = j := by
  intro h
  exact split_append_last z [] i j (by simpa using h)

/-- Rocq `helper_lemmas.v:362` `split_append_2`. -/
theorem split_append_2 {α : Type} (z : List α) (i j k : α) :
    z ++ [i] = [j, k] → z = [j] ∧ i = k := by
  intro h
  exact split_append_last z [j] i k (by simpa using h)

/-- Rocq `helper_lemmas.v:371` `split_append_left_1`. -/
theorem split_append_left_1 {α : Type} (z : List α) (i j : α) :
    [i] ++ z = [j] → z = [] ∧ i = j := by
  intro h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  exact ⟨h.2, h.1⟩

/-- Rocq `helper_lemmas.v:383` `empty_append`. -/
theorem empty_append {α : Type} (i j : List α) :
    [] = i ++ j → i = [] ∧ j = [] := by
  intro h
  cases i with
  | nil => exact ⟨rfl, by simpa using h.symm⟩
  | cons a as => simp at h

/-- Rocq `helper_lemmas.v:394` `lookup_app`. -/
theorem lookup_app {α : Type} [Inhabited α] (l l' : List α) (n : Nat) :
    n < l.length → lookup_total l n = lookup_total (l ++ l') n := by
  intro h
  simp [lookup_total, List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

-- helper_lemmas.v:412-421 (`app_left_single_nil`, `app_right_nil`, `app_left_nil`) NOT PORTED:
-- the Rocq author's own comment flags these as ssreflect-rewriting-recognition workarounds
-- ("I'll probably remove them later") — trivial `List.append_nil`/`List.nil_append` facts,
-- already in Lean core, no counterpart needed.

/-! ## Section 5 : Option-append helper lemmas (helper_lemmas.v:422-440) -/

-- Rocq's `Append_Option` instance is "first-Some-wins": `_append (Some b) c = Some b`,
-- `_append None c = c`. This matches Lean's `Option.orElse` exactly (`a.orElse b` tries `a`
-- first, falls back to `b ()`). The three lemmas below restate the Rocq facts using `orElse`.

/-- Rocq `helper_lemmas.v:422` `_append_option_none`. -/
theorem option_orElse_none {α : Type} (c : Option α) : (c.orElse (fun _ => none)) = c := by
  cases c <;> simp

/-- Rocq `helper_lemmas.v:430` `_append_option_none_left`. -/
theorem option_none_orElse {α : Type} (c : Option α) : ((none : Option α).orElse (fun _ => c)) = c := by
  simp

/-- Rocq `helper_lemmas.v:438` `_append_some_left`. -/
theorem option_some_orElse {α : Type} (b : α) (c : Option α) :
    ((some b).orElse (fun _ => c)) = some b := by
  simp

/-! ## Section 6 : arithmetic helper lemmas (helper_lemmas.v:531-546) -/

/-- Rocq `helper_lemmas.v:626` `add_false` (`5b03ae067`; since removed upstream). -/
theorem add_false (n m : Nat) : n + (m + 1) ≠ n := by omega

/-- Rocq `helper_lemmas.v:531` `add_sub`. -/
theorem add_sub (a b : Nat) : a + b - b = a := by omega

/-- Rocq `helper_lemmas.v:539` `add_sub'`. -/
theorem add_sub' (a b : Nat) : a + b - a = b := by omega

/-! ## Section 7 : list-concatenation cancellation
    (helper_lemmas.v:637-683, `5b03ae067`; since removed upstream) -/

-- `concat_cancel_last_n` (helper_lemmas.v:637, `5b03ae067`; since removed upstream) is stated
-- below `size_eq_cat`, from which it is derived (both need `take_size_cat`/`drop_size_cat`,
-- defined further down).

/-! ## Section 8 : context/prepend_label helpers (helper_lemmas.v:475-530) -/

/-- Rocq `helper_lemmas.v:482` `prepend_label`. Rocq builds a near-empty `context` with only
    `LABELS := [t]` and appends it (fieldwise) onto `v_C`; since Lean's `context.LABELS` is a
    plain `List resulttype` field, this collapses to a direct cons. -/
def prepend_label (C : context) (t : resulttype) : context := { C with LABELS := t :: C.LABELS }

/-- Rocq `helper_lemmas.v:475` `prepend_local`. Defined as Rocq's literal
    `{| …; context_LOCALS := t_lst; … |} @@ v_C`, which is also exactly the context shape
    the generated `Frame_ok` conclusion uses, so the two unfold to the same term. -/
def prepend_local (C : context) (t_lst : List valtype) : context :=
  ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := t_lst, LABELS := [], RETURN := none } : context) ++ C

/-- Rocq `helper_lemmas.v:485` `prepend_return`. Rocq's literal
    `{| …; context_RETURN := Some v_t |} @@ v_C`; the generated `Instr_ok2.Instr_ok2_frame`
    rule uses exactly this shape for the frame body's context. -/
def prepend_return (C : context) (t : resulttype) : context :=
  ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := [], LABELS := [], RETURN := some t } : context) ++ C

/-- Rocq `helper_lemmas.v:488` `append_local`: `v_C @@ {| …; context_LOCALS := t_lst; … |}`. -/
def append_local (C : context) (t_lst : List valtype) : context :=
  C ++ ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := t_lst, LABELS := [], RETURN := none } : context)

/-- Rocq `helper_lemmas.v:495` `append_label`: `v_C @@ {| …; LABELS := [t_lst]; … |}`. -/
def append_label (C : context) (t : resulttype) : context :=
  C ++ ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := [], LABELS := [t], RETURN := none } : context)

/-- Rocq `helper_lemmas.v:502` `append_return`: `v_C @@ {| …; context_RETURN := Some v_t |}`. -/
def append_return (C : context) (t : resulttype) : context :=
  C ++ ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := [], LABELS := [], RETURN := some t } : context)

/-- Rocq `helper_lemmas.v:509` `lookup_label_0`. -/
theorem lookup_label_0 (C : context) (t : resulttype) :
    lookup_total (prepend_label C t).LABELS 0 = t := by
  simp [lookup_total, prepend_label]

/-- Rocq `helper_lemmas.v:515` `lookup_label_1`. -/
theorem lookup_label_1 (C : context) (t : resulttype) (n : Nat) :
    lookup_total (prepend_label C t).LABELS (n + 1) = lookup_total C.LABELS n := by
  simp [lookup_total, prepend_label]

/-! ## Section 9 : more seq/arithmetic lemmas (helper_lemmas.v:562-657) -/

/-- Rocq `helper_lemmas.v:574` `sizecat_le1`. -/
theorem sizecat_le1 {α : Type} (l l' : List α) : l.length ≤ (l ++ l').length := by
  rw [List.length_append]; omega

/-- Rocq `helper_lemmas.v:582` `sizecat_le2`. -/
theorem sizecat_le2 {α : Type} (l l' : List α) : l'.length ≤ (l ++ l').length := by
  rw [List.length_append]; omega

-- `lt_irrefl` (helper_lemmas.v:773, `5b03ae067`; since removed upstream) NOT PORTED: Rocq
-- stated this as a *Boolean* equation (ssrnat idiom, `x < x = false`); Lean's `Nat.lt_irrefl`
-- (already in core) is the direct Prop-valued equivalent, no restatement needed.

/-- Rocq `helper_lemmas.v:590` `drop_size_cat`. -/
theorem drop_size_cat {α : Type} (x y : List α) : (x ++ y).drop x.length = y := by
  induction x with
  | nil => simp
  | cons a as ih => simpa using ih

/-- Rocq `helper_lemmas.v:600` `take_size_cat`. -/
theorem take_size_cat {α : Type} (x y : List α) : (x ++ y).take x.length = x := by
  induction x with
  | nil => simp
  | cons a as ih => simpa using ih

/-- Rocq `helper_lemmas.v:623` `size_eq_cat`. Polymorphic twin of `concat_cancel_last_n`
    below (same conclusion, different Rocq proof technique via `take`/`drop`). -/
theorem size_eq_cat {α : Type} (l1 l2 l1' l2' : List α) :
    l1.length = l2.length → l1' ++ l1 = l2' ++ l2 → l1' = l2' ∧ l1 = l2 := by
  intro hlen heq
  have hlen' : l1'.length = l2'.length := by
    have hl := congrArg List.length heq
    simp only [List.length_append] at hl
    omega
  have h1 : l2' = l1' := by
    have h := take_size_cat l1' l1
    rw [heq, hlen'] at h
    rwa [take_size_cat] at h
  have h2 : l2 = l1 := by
    have h := drop_size_cat l1' l1
    rw [heq, hlen'] at h
    rwa [drop_size_cat] at h
  exact ⟨h1.symm, h2.symm⟩

/-- Rocq `helper_lemmas.v:637` `concat_cancel_last_n` (`5b03ae067`; since removed upstream).
    Rocq stated this monomorphically for
    `list valtype`; generalized to `{α : Type}` here since the proof never uses anything
    `valtype`-specific (an "obvious optimization" per project policy). Semantically the same
    fact as `size_eq_cat` above — derived from it directly. -/
theorem concat_cancel_last_n {α : Type} (l1 l2 l3 l4 : List α) :
    l1 ++ l2 = l3 ++ l4 → l2.length = l4.length → l1 = l3 ∧ l2 = l4 := fun heq hlen =>
  size_eq_cat l2 l4 l1 l3 hlen heq

-- `size_cons` (helper_lemmas.v:655) NOT PORTED: trivial `List.length_cons`, already in Lean core.

/-- Rocq `helper_lemmas.v:837` `ltsize` (`5b03ae067`; since removed upstream). -/
theorem ltsize {α : Type} (x : Nat) (s s2 : List α) : x < s.length → x < (s ++ s2).length := by
  intro h
  have := sizecat_le1 s s2
  omega

-- `repeat_size` (helper_lemmas.v:849, `5b03ae067`; since removed upstream) NOT PORTED: trivial
-- `List.length_replicate`, already in Lean core.

/-! ## Axioms (from `axioms.v`).

    All 21 `Axiom`s of Rocq's `axioms.v` are ported as Lean `axiom`s: the 11 of
    `axioms.v:13-57` first, then the 10 progress-only ones of `axioms.v:64-89`.

    **Reading Rocq's `|x| = q` correctly:** `|x|` is `N.of_nat (size x)` (`wasm.v:290`) and a
    `q : Q` on the right is coerced to `N` through `Qfloor` and `Z.to_N` (`wasm.v:187-193`), so
    the Rocq axioms state FLOORED equations. `rat_to_nat` (`wasm2.0.lean:9`) is exactly that
    composite. (`size` is a concrete definition in `wasm2.0.lean`, not an opaque.) -/

/-- Rocq `axioms.v:13` `nbytes_len`. `nbytes_` (an `opaque` returning `List byte`,
    `wasm2.0.lean:4203`) and `size` (Rocq: `res_size`; a `def` returning `Option Nat`,
    `wasm2.0.lean:798`, hence the `Option.get!`) are generated in `wasm2.0.lean`; this restates
    Rocq's axiom about their relationship. `(Nat.divmod n 7 0 7).1` in Rocq
    is stdlib's internal implementation of `n / 8`; restated directly as `/ 8` here. -/
axiom nbytes_len (v_nt : numtype) (v_c : num_) :
    (nbytes_ v_nt v_c).length = (Option.get! (size (valtype_numtype v_nt))) / 8

/-- Rocq `axioms.v:17` `ibytes_len`. Rocq's bound variable is itself named `size`, shadowing
    the unrelated `size` bit-width function used in `nbytes_len` above (a Rocq/spectec
    naming collision, not our doing) — renamed to `sz` here to avoid shadowing the `size` def
    from `wasm2.0.lean` (`size : valtype → Option Nat`, unrelated to this `sz : N`). -/
axiom ibytes_len (sz v_n : N) (v_c : iN) :
    (ibytes_ v_n (wrap__ sz v_n v_c)).length = v_n / 8

/-- Rocq `axioms.v:21` `nbytes_len'`. A `Rat`-valued
    restatement of `nbytes_len` without the Nat-division floor — the two
    coincide since bit-widths are always multiples of 8, but the
    Rocq source states both. -/
axiom nbytes_len' (v_nt : numtype) (v_c : num_) :
    ((nbytes_ v_nt v_c).length : Rat) = (Option.get! (size (valtype_numtype v_nt)) : Rat) / 8

/-- Rocq `axioms.v:24` `ibytes_len'`. Floored restatement of `ibytes_len`.
    Rocq's `|x| = (v_n / 8)%Q` compares an `N` with a `Q`
    through the coercions `Qfloor : Q → Z` and `Z.to_N : Z → N` (`wasm.v:187-193`), i.e. it states
    `|x| = ⌊v_n / 8⌋`; `rat_to_nat` (`wasm2.0.lean:9`) is exactly `Z.to_N ∘ Qfloor`, so the
    statement below is the faithful translation. Read instead as the exact rational equation
    `((ibytes_ …).length : Rat) = (v_n : Rat) / 8`, the axiom would be INCONSISTENT: at `v_n = 1`
    it says a natural number equals `1/8`, and `False` follows (machine-checked; see the
    preservation audit report, `claude-logging/verbatim_dialogue_log/bundle20/
    user_requested_documents/preservation_audit_report.md`). -/
axiom ibytes_len' (sz v_n : N) (v_c : iN) :
    (ibytes_ v_n (wrap__ sz v_n v_c)).length = rat_to_nat ((v_n : Rat) / 8)

/-- Rocq `axioms.v:32` `ibytes_len''`. Same fact as
    `ibytes_len'` but without the `wrap__` composition — a direct statement
    about `ibytes_` at any bit-width, independent of how the underlying
    integer value was produced. Floored for the same reason as `ibytes_len'` (the exact
    rational reading would be inconsistent). -/
axiom ibytes_len'' (v_n : N) (v_c : iN) :
    (ibytes_ v_n v_c).length = rat_to_nat ((v_n : Rat) / 8)

/-- Rocq `axioms.v:29` `vbytes_len'`. The vector/SIMD
    analogue of `nbytes_len'`/`ibytes_len'`. -/
axiom vbytes_len' (v_vt : vectype) (v_c : vec_) :
    ((vbytes_ v_vt v_c).length : Rat) = (Option.get! (size (valtype_vectype v_vt)) : Rat) / 8

/-- Rocq `axioms.v:38` `truncz_quot`. `truncz`
    (truncation of a rational towards zero) is an uninterpreted `opaque` in
    `wasm2.0.lean` (line 2652, `truncz : Rat → Int`); on a quotient of two
    integers — the only way the spec's integer operators ever use it — it
    coincides with Lean's `Int.tdiv` (truncating division, matching Coq's
    `Z.quot`). -/
axiom truncz_quot (a b : Int) (h : b ≠ 0) :
    truncz ((a : Rat) / (b : Rat)) = Int.tdiv a b

/-- Rocq `axioms.v:43` `lanes_len`. `lanes_` is an
    uninterpreted `opaque` in `wasm2.0.lean` (line 4644). By its definition
    in the specification it splits a 128-bit vector into exactly `dim`
    lanes. -/
axiom lanes_len (lt : lanetype) (v_N : N) (c : vec_) :
    (lanes_ (shape.X lt (dim.mk_dim v_N)) c).length = v_N

/-- Rocq `axioms.v:49` `nbytes_inv`. `nbytes_`/
    `ibytes_` and their inverses `inv_nbytes_`/`inv_ibytes_` are
    uninterpreted `opaque`s in `wasm2.0.lean`. In the specification they are
    mutually inverse bijections between values and byte sequences of the
    right width. -/
axiom nbytes_inv (nt : numtype) (bs : List byte)
    (hlen : (bs.length : Rat) = (Option.get! (size (valtype_numtype nt)) : Rat) / 8) :
    nbytes_ nt (inv_nbytes_ nt bs) = bs

/-- Rocq `axioms.v:53` `ibytes_inv`. Rocq's premise `|bs| = (v_N / 8 : N)` is floored
    (`Z.to_N ∘ Qfloor`, wasm.v:187-193), i.e. `rat_to_nat`. (The exact rational premise
    `(bs.length : Rat) = (v_N : Rat) / 8` would be unsatisfiable unless `8 ∣ v_N`, making the
    axiom strictly weaker than Rocq's.) -/
axiom ibytes_inv (v_N : N) (bs : List byte) (hlen : bs.length = rat_to_nat ((v_N : Rat) / 8)) :
    ibytes_ v_N (inv_ibytes_ v_N bs) = bs

/-- Rocq `axioms.v:57` `vbytes_inv`. -/
axiom vbytes_inv (vt : vectype) (bs : List byte)
    (hlen : (bs.length : Rat) = (Option.get! (size (valtype_vectype vt)) : Rat) / 8) :
    vbytes_ vt (inv_vbytes_ vt bs) = bs

/-! ### Progress-only axioms of `axioms.v` (`axioms.v:64-89`; used by `TypeProgress.lean`)

    Each constrains functions that are `opaque` in `wasm2.0.lean` (no Lean definition), exactly as
    in Rocq, where they are uninterpreted `Axiom`s of `wasm.v`. Consistency: each has an obvious
    model consistent with the others and with every proved theorem (comparisons return 0/1,
    `trunc_sat__` returns `some 0`, `demote__`/`promote__` return `[INF]`,
    `ibits_`/`inv_ibits_` are binary encode/decode). -/

/-- Rocq `axioms.v:64` `ibits_inv`: `ibits_` and `inv_ibits_` are mutually inverse between
    `iN(N)` and well-formed bit sequences of length `N`. -/
axiom ibits_inv (v_N : N) (bs : List bit) :
    bs.length = v_N → Forall (fun b => wf_bit b) bs → ibits_ v_N (inv_ibits_ v_N bs) = bs

/-- Rocq `axioms.v:72` `feq_bit`: the float comparison `feq_` returns a boolean (0 or 1). -/
axiom feq_bit (v_N : N) (a b : fN) : wf_uN 1 (feq_ v_N a b)

/-- Rocq `axioms.v:73` `fne_bit`. -/
axiom fne_bit (v_N : N) (a b : fN) : wf_uN 1 (fne_ v_N a b)

/-- Rocq `axioms.v:74` `flt_bit`. -/
axiom flt_bit (v_N : N) (a b : fN) : wf_uN 1 (flt_ v_N a b)

/-- Rocq `axioms.v:75` `fgt_bit`. -/
axiom fgt_bit (v_N : N) (a b : fN) : wf_uN 1 (fgt_ v_N a b)

/-- Rocq `axioms.v:76` `fle_bit`. -/
axiom fle_bit (v_N : N) (a b : fN) : wf_uN 1 (fle_ v_N a b)

/-- Rocq `axioms.v:77` `fge_bit`. -/
axiom fge_bit (v_N : N) (a b : fN) : wf_uN 1 (fge_ v_N a b)

-- Rocq's former `ishl_wf`/`ishr_wf` (`axioms.v:83-86` at revision `95c256c2c`) were deleted
-- upstream in `6582b3a39`, and are not ported. Spec commit `4cf9f29c5` gives `$ishl_`/`$ishr_`
-- an `iN(N)` shift amount (`$binop_` passes its second operand directly; `$vshiftop_` reduces it
-- modulo the lane size first), so the generated `ishl__is_wf`/`ishr__is_wf` apply wherever these
-- were used.

/-- Rocq `axioms.v:85` `trunc_sat_total`: saturating truncation always produces a result. -/
axiom trunc_sat_total (v_M : M) (v_N : N) (v_sx : sx) (x : fN) : trunc_sat__ v_M v_N v_sx x ≠ none

/-- Rocq `axioms.v:87` `demote_nonempty`. -/
axiom demote_nonempty (v_M : M) (v_N : N) (x : fN) : demote__ v_M v_N x ≠ []

/-- Rocq `axioms.v:89` `promote_nonempty`. -/
axiom promote_nonempty (v_M : M) (v_N : N) (x : fN) : promote__ v_M v_N x ≠ []

/-! ## `Forall₂` bridge to Mathlib's `List.Forall₂`

Not a port of any Rocq lemma — Lean-only infrastructure. This
codebase's generated `Forall₂` (`wasm2.0.lean:20`) is a zip-based `def`
(`∀ t ∈ xs₁.zip xs₂, P t.1 t.2`), unlike Rocq's `Forall2`, which is an
*inductive* relation that forces `xs₁.length = xs₂.length` as part of its
own shape. Concretely: with `xs₁ := [x]`, `xs₂ := []`, our `Forall₂ P xs₁
xs₂` reduces to `∀ p ∈ [], _`, which is vacuously `True` — a fact Rocq's
`Forall2 P [x] []` simply has no proof of at all (`nil`/`cons` mismatch is
uninhabited there). This gap is invisible as long as a Rocq `Forall2` proof
never needs the length fact, but several downstream lemmas do (see
`TypingLemmas.lean`'s `Vals_ok`/`Vals_ok_non_bot`, and the `hlen` premises of
`ExtensionLemmas.lean`'s `funcinst_same` and of `Forall2_size` above). Once an explicit length
hypothesis is supplied, this pair of lemmas converts freely between our
`Forall₂` and Mathlib's `List.Forall₂` (an inductive relation with a real
`nil`/`cons` induction principle), which is more ergonomic to do induction
on directly than the zip-based version. -/

/-- Given an explicit length hypothesis, this codebase's zip-based `Forall₂`
    coincides with Mathlib's inductive `List.Forall₂`. -/
theorem to_mathlib_forall₂ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (hlen : l1.length = l2.length) (h : Forall₂ R l1 l2) : List.Forall₂ R l1 l2 := by
  rw [List.forall₂_iff_zip]
  refine ⟨hlen, ?_⟩
  intro a b hab
  exact h (a, b) hab

/-- The reverse direction needs no extra hypothesis: Mathlib's `List.Forall₂`
    already forces equal length by construction (`List.Forall₂.length_eq`). -/
theorem from_mathlib_forall₂ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) : l1.length = l2.length ∧ Forall₂ R l1 l2 := by
  rw [List.forall₂_iff_zip] at h
  obtain ⟨hlen, hz⟩ := h
  refine ⟨hlen, ?_⟩
  intro p hp
  exact hz hp

/-! ## Function views of total relations (Lean-only)

Since `sideconditions_on_defs` (user commit `12b021fc9`), the backend turns every spec function
that needs a side condition (a `!`, an index, or, for `$fzero`, the well-formedness of its result),
directly or through another such function, into a relation `fun_<name>`, even when the function is
total. The downstream proofs were written against the functions, so this section restores a
function view of the size functions the proofs use (`lsize`, `isize`, `jsize`, `sizenn`, `sizenn1`,
`lsizenn`, `lsizenn1`, `lsizenn2`), of `fzero` and of `default_` (names the model no longer uses),
with the definitions they had in the old model (`OLD_wasm2.0.lean`), and proves, as far as the
proofs need them, that the relation holds of the view (`fun_<name>_<name>`; for `default_`,
`fun_default_default`) and that the view is the relation's only output (`fun_<name>_eq`;
`fun_default_eq`). `fzero` is the exception: `fun_fzero` holds only at the
widths 32 and 64 (`fun_fzero_32`, `fun_fzero_64`). The other relations, total or partial
(`fun_zero`, `fun_unop_`, `$table`, `$with_*`, …), are used through their constructors, whose
premises carry the bounds. Not a port of any Rocq lemma. -/

/-- Function view of `fun_lsize` (old model's `lsize`): the bit width of a lane type. -/
def lsize (v_lanetype : lanetype) : Nat :=
  match v_lanetype with
  | lanetype.I32 => Option.get! (size (valtype_numtype numtype.I32))
  | lanetype.I64 => Option.get! (size (valtype_numtype numtype.I64))
  | lanetype.F32 => Option.get! (size (valtype_numtype numtype.F32))
  | lanetype.F64 => Option.get! (size (valtype_numtype numtype.F64))
  | lanetype.I8 => psize packtype.I8
  | lanetype.I16 => psize packtype.I16

theorem fun_lsize_lsize (lt : lanetype) : fun_lsize lt (lsize lt) := by
  cases lt <;> constructor <;> simp [size, valtype_numtype]

theorem fun_lsize_eq {lt : lanetype} {n : Nat} (h : fun_lsize lt n) : n = lsize lt := by
  cases h <;> rfl

/-- Function view of `fun_isize` (old model's `isize`). -/
def isize (v_Inn : Inn) : Nat :=
  Option.get! (size (valtype_Inn v_Inn))

theorem fun_isize_isize (I : Inn) : fun_isize I (isize I) :=
  fun_isize.fun_isize_case_0 I (by cases I <;> simp [size, valtype_Inn])

/-- Function view of `fun_jsize` (old model's `jsize`). -/
def jsize (v_Jnn : Jnn) : Nat :=
  lsize (lanetype_Jnn v_Jnn)

theorem fun_jsize_jsize (J : Jnn) : fun_jsize J (jsize J) :=
  fun_jsize.fun_jsize_case_0 J _ (fun_lsize_lsize _)

/-- Function view of `fun_sizenn` (old model's `sizenn`). -/
def sizenn (v_numtype : numtype) : Nat :=
  Option.get! (size (valtype_numtype v_numtype))

theorem fun_sizenn_sizenn (nt : numtype) : fun_sizenn nt (sizenn nt) :=
  fun_sizenn.fun_sizenn_case_0 nt (by cases nt <;> simp [size, valtype_numtype])

theorem fun_sizenn_eq {nt : numtype} {n : Nat} (h : fun_sizenn nt n) : n = sizenn nt := by
  cases h; rfl

/-- Function view of `fun_sizenn1` (old model's `sizenn1`). -/
def sizenn1 (v_numtype : numtype) : Nat :=
  Option.get! (size (valtype_numtype v_numtype))

theorem fun_sizenn1_eq {nt : numtype} {n : Nat} (h : fun_sizenn1 nt n) : n = sizenn1 nt := by
  cases h; rfl

/-- Function view of `fun_lsizenn` (old model's `lsizenn`). -/
def lsizenn (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

theorem fun_lsizenn_lsizenn (lt : lanetype) : fun_lsizenn lt (lsizenn lt) :=
  fun_lsizenn.fun_lsizenn_case_0 lt _ (fun_lsize_lsize lt)

theorem fun_lsizenn_eq {lt : lanetype} {n : Nat} (h : fun_lsizenn lt n) : n = lsizenn lt := by
  cases h with
  | fun_lsizenn_case_0 h => exact fun_lsize_eq h

/-- Function view of `fun_lsizenn1` (old model's `lsizenn1`). -/
def lsizenn1 (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

theorem fun_lsizenn1_lsizenn1 (lt : lanetype) : fun_lsizenn1 lt (lsizenn1 lt) :=
  fun_lsizenn1.fun_lsizenn1_case_0 lt _ (fun_lsize_lsize lt)

theorem fun_lsizenn1_eq {lt : lanetype} {n : Nat} (h : fun_lsizenn1 lt n) : n = lsizenn1 lt := by
  cases h with
  | fun_lsizenn1_case_0 h => exact fun_lsize_eq h

/-- Function view of `fun_lsizenn2` (old model's `lsizenn2`). -/
def lsizenn2 (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

theorem fun_lsizenn2_lsizenn2 (lt : lanetype) : fun_lsizenn2 lt (lsizenn2 lt) :=
  fun_lsizenn2.fun_lsizenn2_case_0 lt _ (fun_lsize_lsize lt)

theorem fun_lsizenn2_eq {lt : lanetype} {n : Nat} (h : fun_lsizenn2 lt n) : n = lsizenn2 lt := by
  cases h with
  | fun_lsizenn2_case_0 h => exact fun_lsize_eq h

/-- Function view of `fun_fzero` (old model's `fzero`): positive zero. Unlike the old function,
    the relation also requires `wf_fN N (fzero N)`, which holds for the widths 32 and 64 only
    (`wf_fzero_32`, `wf_fzero_64`). -/
def fzero (_v_N : N) : fN :=
  fN.POS (fNmag.SUBNORM 0)

theorem fun_fzero_eq {v_N : N} {x : fN} (h : fun_fzero v_N x) : x = fzero v_N := by
  cases h; rfl

theorem wf_fzero_32 : wf_fN 32 (fzero 32) :=
  wf_fN.fN_case_0 _ _ (wf_fNmag.fNmag_case_1 32 _ 0 _ _
    (fun_E.fun_E_case_0 32 (by decide)) (fun_M.fun_M_case_0 32 (by decide)) ⟨by decide, rfl⟩)

theorem wf_fzero_64 : wf_fN 64 (fzero 64) :=
  wf_fN.fN_case_0 _ _ (wf_fNmag.fNmag_case_1 64 _ 0 _ _
    (fun_E.fun_E_case_0 64 (by decide)) (fun_M.fun_M_case_0 64 (by decide)) ⟨by decide, rfl⟩)

theorem fun_fzero_32 : fun_fzero 32 (fzero 32) := fun_fzero.fun_fzero_case_0 32 wf_fzero_32

theorem fun_fzero_64 : fun_fzero 64 (fzero 64) := fun_fzero.fun_fzero_case_0 64 wf_fzero_64

/-- Function view of `fun_default_` (old model's `default_`): the default value of a value type,
    `none` only for `BOT`. -/
def default_ (v_valtype : valtype) : Option val :=
  match v_valtype with
  | valtype.I32 => some (val.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)))
  | valtype.I64 => some (val.CONST numtype.I64 (num_.mk_num__0 Inn.I64 (uN.mk_uN 0)))
  | valtype.F32 => some (val.CONST numtype.F32 (num_.mk_num__1 Fnn.F32 (fzero 32)))
  | valtype.F64 => some (val.CONST numtype.F64 (num_.mk_num__1 Fnn.F64 (fzero 64)))
  | valtype.V128 => some (val.VCONST vectype.V128 (uN.mk_uN 0))
  | valtype.FUNCREF => some (val.REF_NULL reftype.FUNCREF)
  | valtype.EXTERNREF => some (val.REF_NULL reftype.EXTERNREF)
  | _ => none

theorem fun_default_default (t : valtype) : fun_default_ t (default_ t) := by
  cases t
  · exact fun_default_.fun_default__case_0
  · exact fun_default_.fun_default__case_1
  · exact fun_default_.fun_default__case_2 _ fun_fzero_32
  · exact fun_default_.fun_default__case_3 _ fun_fzero_64
  · exact fun_default_.fun_default__case_4
  · exact fun_default_.fun_default__case_5
  · exact fun_default_.fun_default__case_6
  · exact fun_default_.fun_default__case_7 _ (fun h => by cases h)

theorem fun_default_eq {t : valtype} {o : Option val} (h : fun_default_ t o) : o = default_ t := by
  cases h with
  | fun_default__case_2 _ hz => rw [fun_fzero_eq hz]; rfl
  | fun_default__case_3 _ hz => rw [fun_fzero_eq hz]; rfl
  | fun_default__case_7 _ hn =>
    revert hn
    cases t <;> intro hn
    case BOT => rfl
    all_goals first
      | exact (hn (.fun_default__case_2 (fzero 32))).elim
      | exact (hn (.fun_default__case_3 (fzero 64))).elim
      | exact (hn (by constructor)).elim
  | _ => rfl

/-! ### Inversion of the state lookups (Lean-only)

The state lookups are relations with one constructor each. For those the proofs invert
(`fun_type`, `fun_global`, `fun_table`, `fun_mem`, `fun_elem`, `fun_local`), these lemmas return
the constructor's premises (the index bounds) and its output as an equation. They are needed when
the output is a term, which `cases` cannot unify with the constructor's indexing expression
(`bt_inversion`), and are convenient elsewhere. -/

theorem fun_type_inv {s : store} {f : frame} {x : uN} {ft : functype} :
    fun_type (state.mk_state s f) x ft →
    proj_uN_0 x < f.MODULE.TYPES.length ∧ ft = f.MODULE.TYPES[proj_uN_0 x]! := by
  rintro ⟨⟩; exact ⟨‹_›, rfl⟩

theorem fun_global_inv {s : store} {f : frame} {x : uN} {gi : globalinst} :
    fun_global (state.mk_state s f) x gi →
    proj_uN_0 x < f.MODULE.GLOBALS.length ∧ f.MODULE.GLOBALS[proj_uN_0 x]! < s.GLOBALS.length ∧
      gi = s.GLOBALS[f.MODULE.GLOBALS[proj_uN_0 x]!]! := by
  rintro ⟨⟩; exact ⟨‹_›, ‹_›, rfl⟩

theorem fun_table_inv {s : store} {f : frame} {x : uN} {ti : tableinst} :
    fun_table (state.mk_state s f) x ti →
    proj_uN_0 x < f.MODULE.TABLES.length ∧ f.MODULE.TABLES[proj_uN_0 x]! < s.TABLES.length ∧
      ti = s.TABLES[f.MODULE.TABLES[proj_uN_0 x]!]! := by
  rintro ⟨⟩; exact ⟨‹_›, ‹_›, rfl⟩

theorem fun_mem_inv {s : store} {f : frame} {x : uN} {mi : meminst} :
    fun_mem (state.mk_state s f) x mi →
    proj_uN_0 x < f.MODULE.MEMS.length ∧ f.MODULE.MEMS[proj_uN_0 x]! < s.MEMS.length ∧
      mi = s.MEMS[f.MODULE.MEMS[proj_uN_0 x]!]! := by
  rintro ⟨⟩; exact ⟨‹_›, ‹_›, rfl⟩

theorem fun_elem_inv {s : store} {f : frame} {x : uN} {ei : eleminst} :
    fun_elem (state.mk_state s f) x ei →
    proj_uN_0 x < f.MODULE.ELEMS.length ∧ f.MODULE.ELEMS[proj_uN_0 x]! < s.ELEMS.length ∧
      ei = s.ELEMS[f.MODULE.ELEMS[proj_uN_0 x]!]! := by
  rintro ⟨⟩; exact ⟨‹_›, ‹_›, rfl⟩

theorem fun_local_inv {s : store} {f : frame} {x : uN} {v : val} :
    fun_local (state.mk_state s f) x v →
    proj_uN_0 x < f.LOCALS.length ∧ v = f.LOCALS[proj_uN_0 x]! := by
  rintro ⟨⟩; exact ⟨‹_›, rfl⟩

end TLC
