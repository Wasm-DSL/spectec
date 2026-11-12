import Mathlib.Tactic
import «wasm2.0»
import «custom_notation»
open functype list

set_option pp.parens true
set_option pp.numericTypes true

-- Cheap bridge from the codegen's custom, zip-based `Forall₂` to Mathlib's
-- real inductive `List.Forall₂`, given the length fact that every
-- `Resulttype_sub`/`Forall₂`-carrying constructor already hands you
-- separately (see `mk_Resulttype_sub`). Once converted, the whole
-- `List.Forall₂` lemma library (`forall₂_take_append`, `forall₂_take`,
-- `Forall₂.length_eq`, ...) is available directly.
theorem to_mathlib_forall₂ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (hlen : l1.length = l2.length) (h : Forall₂ R l1 l2) : List.Forall₂ R l1 l2 :=
  List.forall₂_iff_zip.mpr ⟨hlen, fun hab => h _ hab⟩

theorem from_mathlib_forall₂
  {R : α → β → Prop}
  {l1 : List α}
  {l2 : List β}
  :
  List.Forall₂ R l1 l2
  → Forall₂ R l1 l2
  := fun h t ht => (List.forall₂_iff_zip.mp h).2 ht


  -- sorry

theorem zip_self_both_sides_equal
  {α : Type} (l : List α)
  : ∀ e_e ∈ l.zip l, e_e.1 = e_e.2 := by

  intro e_e h
  simp [List.zip] at *
  obtain ⟨a, a_in_l, h_eq⟩ := h
  subst h_eq
  rfl


theorem valtype_sub_refl (t1 : valtype) : t1 sub< t1 := by
  constructor

theorem resulttype_sub_refl (t1s : List valtype) : t1s subs< t1s := by
  unfold resulttypeSub
  apply Resulttype_sub.mk_Resulttype_sub
  · rfl
  · simp [List.zip, Forall₂] at *
    intro a h
    exact valtype_sub_refl a

  -- · unfold Forall₂
  --   induction t1s with
  --   | nil => simp
  --   | cons head tail ih =>
  --     simp [List.zip] at *
  --     apply And.intro
  --     · exact valtype_sub_refl head
  --     · exact ih

theorem zip_trans (l1 l2 l3 : List α)
  : ∀ r : α → α → Prop,
      (∀ a b, (a, b) ∈ l1.zip l2 → r a b) →
      (∀ b c, (b, c) ∈ l2.zip l3 → r b c) →
      (l1.length = l2.length) →
      (l2.length = l3.length) →
      (∀ a b c, r a b → r b c → r a c)

      → ∀ a c, (a, c) ∈ l1.zip l3 → r a c

  := by

  intro
    r forall_ab_trans forall_bc_trans
    length_same_l1_l2 length_same_l2_l3
    forall_ac_trans a c ac_from_l1_l3

  -- intro r h a c ac_from_l1_l3
  -- obtain ⟨
  --   forall_ab_trans,
  --   forall_bc_trans,
  --   length_same_l1_l2,
  --   length_same_l2_l3,
  --   forall_ac_trans
  -- ⟩ := h
  obtain ⟨i, i_in_bounds_l1_l3, hia_c⟩ := List.mem_iff_getElem.mp ac_from_l1_l3
  rw [List.getElem_zip] at hia_c
  -- set a := l1[i]'(
  --   by
  --     rw [List.length_zip] at i_in_bounds_l1_l3
  --     omega
  -- ) with ha
  obtain ⟨h_a, h_c⟩ := Prod.mk.injEq .. ▸ hia_c
  rw [List.length_zip] at i_in_bounds_l1_l3
  have i_in_bounds_l1 : i < l1.length := by omega
  have i_in_bounds_l2 : i < l2.length := by omega
  have i_in_bounds_l3 : i < l3.length := by omega
  set ab := (l1.zip l2)[i]'(
    by
      rw [List.length_zip]
      omega
  ) with hab
  set a' := ab.1 with ha'
  set b' := ab.2 with hb'
  have ab_of_l1_l2 : ab ∈ l1.zip l2 := by
    apply List.getElem_mem
  set bc := (l2.zip l3)[i]'(
    by
      rw [List.length_zip]
      omega
  ) with hbc
  set b'' := bc.1 with hb''
  set c' := bc.2 with hc'
  have bc_of_l2_l3 : bc ∈ l2.zip l3 := by
    apply List.getElem_mem
  have trans_ab := forall_ab_trans a' b' ab_of_l1_l2
  have trans_bc := forall_bc_trans b'' c' bc_of_l2_l3
  rw [List.getElem_zip] at *

  have a'_is_a : a' = a := by
    rw [ha', h_a.symm, hab]
  have b'_is_b'' : b' = b'' := by
    rw [hb', hb'', hab, hbc]
  have c'_is_c : c' = c := by
    rw [hc', h_c.symm, hbc]

  rw [b'_is_b''] at trans_ab
  have trans_ac := forall_ac_trans a' b'' c' trans_ab trans_bc
  rw [a'_is_a, c'_is_c] at trans_ac
  exact trans_ac


theorem valtype_sub_trans
  (t1 t2 t3 : valtype)
  (h1 : t1 sub< t2)
  (h2 : t2 sub< t3)
  :
  t1 sub< t3 := by
  cases h1
  · cases h2
    · constructor
    · constructor
  · cases h2
    · constructor
    · constructor


theorem resulttype_sub_trans
  (t1s t2s t3s : List valtype)
  (h1 : t1s subs< t2s)
  (h2 : t2s subs< t3s)
  :
  t1s subs< t3s := by
  unfold resulttypeSub at *
  obtain ⟨_, _, h1_eq, h1_forall⟩ := h1
  obtain ⟨_, _, h2_eq, h2_forall⟩ := h2
  apply Resulttype_sub.mk_Resulttype_sub
  · exact Eq.trans h1_eq h2_eq
  · simp [Forall₂] at *
    intro a b h
    have t := zip_trans t1s t2s t3s Valtype_sub

    have t' := t h1_forall h2_forall h1_eq h2_eq valtype_sub_trans a b h

    exact t'


theorem resulttype_sub_app
  (ts1_sub ts2_sub ts1 ts2 : List valtype)
  (h1 : ts1_sub subs< ts1)
  (h2 : ts2_sub subs< ts2)
  :
  (ts1_sub ++ ts2_sub) subs< (ts1 ++ ts2) := by
  unfold resulttypeSub at *
  cases h1
  cases h2
  rename_i
    same_length_ts1_ts1sub
    all_ts1sub_sub_ts1
    same_length_ts2_ts2sub
    all_ts2sub_sub_ts2

  simp [Forall₂] at *

  apply Resulttype_sub.mk_Resulttype_sub

  case mk_Resulttype_sub.mk_Resulttype_sub.a =>
    aesop

  case mk_Resulttype_sub.mk_Resulttype_sub.a =>
    simp [Forall₂] at *
    grind










theorem instrs_empty_typing
    (p_context : context)
    (t1s t2s : List valtype)
    :
    Instrs_ok p_context [] (t1s f-> t2s) ↔
    (wf_context p_context ∧ (t1s subs< t2s))
    := by
    apply Iff.intro
    · intro h
      apply And.intro
      · generalize gen_instrs_ok_list : ([] : List instr) = l at h
        generalize gen_instrs_ok_functype : (t1s f-> t2s) = ft at h
        induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
        all_goals trivial
      · generalize gen_instrs_ok_list : ([] : List instr) = l at h
        generalize gen_instrs_ok_functype : (t1s f-> t2s) = ft at h
        induction h
          using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
          generalizing t1s t2s
        all_goals try trivial
        · have all_empty : (t1s = []) ∧ (t2s = []) := by
            unfold mkFunctype at gen_instrs_ok_functype
            simp at gen_instrs_ok_functype
            exact gen_instrs_ok_functype
          have t1s_empty : t1s = [] := all_empty.left
          have t2s_empty : t2s = [] := all_empty.right
          rw [t1s_empty, t2s_empty]
          exact resulttype_sub_refl []
        case mp.right.seq
          c i1s i2s t3s t5s t4s instrs_ok1 instrs_ok2
          wf_c wf_i1s wf_i2s what1 what2 =>
          have both_empty : i1s = [] ∧ i2s = [] := by
            exact List.append_eq_nil_iff.mp gen_instrs_ok_list.symm
          -- simp [both_empty] at what1 what2 instrs_ok1 instrs_ok2 wf_i1s wf_i2s
          simp [both_empty] at *
          unfold mkFunctype at what1 what2
          simp at *
          have t3s_subs_t5s : t3s subs< t5s := by
            exact resulttype_sub_trans
              t3s t4s t5s
              what1
              what2
          unfold mkFunctype at gen_instrs_ok_functype
          simp at gen_instrs_ok_functype
          obtain ⟨t1s_is_t3s, t2s_is_t5s⟩ := gen_instrs_ok_functype
          rw [t1s_is_t3s, t2s_is_t5s]
          exact t3s_subs_t5s
        case mp.right.sub
          c instrs
          t'1s t'2s t''1s t''2s
          instrs_ok
          res_sub_t'1s_t1s
          res_sub_t2s_t'2s
          wf_c
          wf_all_instr_in_instrs
          ih =>
          unfold mkFunctype at *
          simp at *
          have h := ih t''1s t''2s gen_instrs_ok_list rfl rfl
          unfold resulttypeSub at *
          have t'1s_sub_t''2s: Resulttype_sub (mk_list t'1s) (mk_list t''2s) := by
            exact resulttype_sub_trans t'1s t''1s t''2s res_sub_t'1s_t1s h
          have t'1s_sub_t'2s: Resulttype_sub (mk_list t'1s) (mk_list t'2s) := by
            exact resulttype_sub_trans t'1s t''2s t'2s t'1s_sub_t''2s res_sub_t2s_t'2s
          obtain ⟨t1s_is_t'1s, t2s_is_t'2s⟩ := gen_instrs_ok_functype
          rw [t1s_is_t'1s, t2s_is_t'2s]
          exact t'1s_sub_t'2s

        case mp.right.frame
          c instrs ts t'1s t'2s instrs_ok wf_c wf_all_instr_in_c ih =>
          unfold mkFunctype at *
          simp at *
          have t'1s_sub_t'2s : t'1s subs< t'2s := by
            exact ih t'1s t'2s gen_instrs_ok_list rfl rfl
          have ts_sub_ts : ts subs< ts := by
            exact resulttype_sub_refl ts
          have t'1s_sub_t'2s_app : (ts ++ t'1s) subs< (ts ++ t'2s) := by
            exact resulttype_sub_app ts t'1s ts t'2s ts_sub_ts t'1s_sub_t'2s
          obtain ⟨t1s_is_ts_t'1s, t2s_is_ts_t'2s⟩ := gen_instrs_ok_functype
          rw [t1s_is_ts_t'1s, t2s_is_ts_t'2s]
          exact t'1s_sub_t'2s_app
    · intro h
      obtain ⟨wf_c, t1s_sub_t2s⟩ := h
      apply Instrs_ok.sub (t_1_lst := t2s ++ []) (t_2_lst := t2s ++ [])

      case mpr.a =>
        apply Instrs_ok.frame
        case a =>
          apply Instrs_ok.empty
          exact wf_c
        case a =>
          exact wf_c
        case a =>
          simp [Forall]

      case mpr.a =>
        simp
        unfold resulttypeSub at *
        exact t1s_sub_t2s

      case mpr.a =>
        simp
        exact resulttype_sub_refl t2s

      case mpr.a =>
        exact wf_c

      case mpr.a =>
        simp [Forall]




theorem ais_empty_typing
  (s : store)
  (c : context)
  (t1s t2s : List valtype)
  :
  Instrs_ok2 s c [] (t1s f-> t2s) ↔
  (wf_context c ∧ wf_store s ∧ (t1s subs< t2s)) := by

  apply Iff.intro
  case mp =>
    intro instrs_ok2
    refine ⟨?_, ?_, ?_⟩
    case refine_1 =>
      generalize gen_instrs_ok2_list : ([] : List admininstr) = l at instrs_ok2
      cases instrs_ok2 <;> exact ‹wf_context c›

    case refine_2 =>
      generalize gen_instrs_ok2_list : ([] : List admininstr) = l at instrs_ok2
      cases instrs_ok2 <;> exact ‹wf_store s›

    case refine_3 =>
      generalize gen_instrs_ok2_list : ([] : List admininstr) = l at instrs_ok2
      have main :
        ∀ (l' : List admininstr) (ft : functype),
          Instrs_ok2 s c l' ft →
          ∀ (t1s t2s : List valtype),
            ([] : List admininstr) = l' →
            (t1s f-> t2s) = ft →
            t1s subs< t2s := by
        clear instrs_ok2 gen_instrs_ok2_list t1s t2s l
        intro l' ft h
        induction h
          using Instrs_ok2.rec
            (motive_1 := fun _ _ _ _ => True)
            (motive_3 := fun _ _ _ _ => True)
        all_goals try trivial

        case empty =>
          intro t1s t2s
          unfold resulttypeSub
          unfold mkFunctype
          simp
          intro h1 h2
          have h : t1s = t2s := by
            rw [h1, h2]
          rw [h]
          exact resulttype_sub_refl t2s

        case instr =>
          unfold resulttypeSub mkFunctype
          simp

        case seq
          c' ainstrs1 ainstrs2 t1s t3s t2s
          instrs_ok2_t1s_t2s instrs_ok2_t2s_t3s
          wf_s wf_c' wf_all_ainstrs1 wf_all_ainstrs2
          ih1 ih2
          =>
          unfold resulttypeSub mkFunctype Forall at *
          simp_all
          intro t'1s t'2s ainstrs1_empty ainstrs2_empty t1s_eq t2s_eq
          simp_all
          exact resulttype_sub_trans t1s t2s t3s ih1 ih2

        case sub
          c' ainstrs t'1s t'2s t1s t2s instrs_ok2
          t'1s_subs_t1s t2s_subs_t'2s wf_s wf_c' wf_all_ainstrs ih
          =>
          unfold resulttypeSub mkFunctype Forall at *
          simp_all
          intro t''1s t''2s ainstrs_empty t''1s_is_t'1s t''2s_is_t'2s
          simp_all
          have t'1s_subs_t2s : t'1s subs< t2s := by
            exact resulttype_sub_trans t'1s t1s t2s t'1s_subs_t1s ih
          exact resulttype_sub_trans t'1s t2s t'2s t'1s_subs_t2s t2s_subs_t'2s

        case Instrs_ok2_frame
          c' ainstrs ts t1s t2s
          instrs_ok2 wf_s wf_c'
          wf_all_ainstrs ih
          -- t'1s t'2s
          -- ainstrs_empty breakdown
          =>
          unfold resulttypeSub mkFunctype Forall at *
          simp_all
          intro t1s' t2s' empty_ainstrs t1s'_eq t2s'_eq
          have ih' := ih t1s t2s empty_ainstrs rfl rfl
          apply resulttype_sub_app
          case h1 => exact resulttype_sub_refl ts
          case h2 => exact ih'
          -- obtain ⟨breakdown_t'1s, breakdown_t'2s⟩ := breakdown
          -- exact resulttype_sub_app ts t1s ts t2s (by exact resulttype_sub_refl ts) ih

      exact main l (t1s f-> t2s) instrs_ok2 t1s t2s gen_instrs_ok2_list rfl

  case mpr =>
    intro temp
    obtain ⟨wf_c, wf_s, t1s_sub_t2s⟩ := temp
    have empty_ok : Instrs_ok2 s c [] (([] : List valtype) f-> ([] : List valtype)) :=
      Instrs_ok2.empty s c wf_s wf_c
    have frame_ok :
        Instrs_ok2 s c [] ((t1s ++ ([] : List valtype)) f-> (t1s ++ ([] : List valtype))) :=
      Instrs_ok2.Instrs_ok2_frame s c [] t1s [] [] empty_ok wf_s wf_c (by simp [Forall])
    have base : Instrs_ok2 s c [] (t1s f-> t1s) := by simpa using frame_ok
    exact Instrs_ok2.sub s c [] t1s t2s t1s t1s
      base (resulttype_sub_refl t1s) t1s_sub_t2s wf_s wf_c (by simp [Forall])

















def ai_principal_typing
    -- p_* for params to keep track of which variables come from parameters in
    -- this huge definition
    (p_store      : store)
    (p_context    : context)
    (p_admininstr : admininstr)
    (p_functype   : functype)
    : Prop :=
    match p_admininstr with
        | admininstr.NOP            => p_functype = ([] f-> [])
        | admininstr.UNREACHABLE    => true -- this is equivalent to the spec, which has no effective additonal constraints
        | admininstr.DROP           => ∃ (t : valtype),
                                           p_functype = ([t] f-> [])
        | admininstr.SELECT
            (some [(t : valtype)])  => p_functype = ([t, t, valtype.I32] f-> [t])
        | admininstr.SELECT
            none                    => ∃ (t t' : valtype),
                                           p_functype = ([t, t, valtype.I32] f-> [t])
                                         ∧ t sub< t'
                                         ∧ (
                                              ∃ (nt : numtype), t' = valtype_numtype nt
                                            ∨ ∃ (vt : vectype), t' = valtype_vectype vt
                                           )
        | admininstr.SELECT
            _                       => false
        | admininstr.BLOCK
            (bt : blocktype)
            (instrs : List instr)   => ∃ (t1s t2s : List valtype),
                                           p_functype = (t1s f-> t2s)
                                         ∧ Blocktype_ok p_context bt (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t2s) :: p_context.LABELS}
                                               instrs
                                               (t1s f-> t2s)
        | admininstr.LOOP
            (bt : blocktype)
            (instrs : List instr)   => ∃ (t1s t2s : List valtype),
                                           p_functype = (t1s f-> t2s)
                                         ∧ Blocktype_ok p_context bt (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t1s) :: p_context.LABELS}
                                               instrs
                                               (t1s f-> t2s)
        | admininstr.IFELSE
            (bt : blocktype)
            (instrs1 : List instr)
            (instrs2 : List instr)  => ∃ (t1s t2s : List valtype),
                                           p_functype = ((t1s ++ [valtype.I32]) f-> t2s)
                                         ∧ Blocktype_ok p_context bt (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t2s) :: p_context.LABELS}
                                               instrs1
                                               (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t2s) :: p_context.LABELS}
                                               instrs2
                                               (t1s f-> t2s)
        | admininstr.BR
            (l : labelidx)          => ∃ (t1s ts t2s : List valtype),
                                           p_functype = ((t1s ++ ts) f-> t2s)
                                         ∧ p_context.LABELS[proj_uN_0 l]? = some (list.mk_list ts)

        | admininstr.BR_IF
            (l : labelidx)          => ∃ (ts : List valtype),
                                           p_functype = ((ts ++ [valtype.I32]) f-> ts)
                                         ∧ p_context.LABELS[proj_uN_0 l]? = some (list.mk_list ts)

        | admininstr.BR_TABLE
            (ls : List labelidx)
            (l' : labelidx)         => ∃ (t1s ts t2s : List valtype),
                                           p_functype = ((t1s ++ ts ++ [valtype.I32]) f-> t2s)
                                         ∧ ∀ l ∈ ls,
                                               ∃ (r : resulttype),
                                                   p_context.LABELS[proj_uN_0 l]? = some r
                                                 ∧ Resulttype_sub (list.mk_list ts) r
                                         ∧ ∃ (r' : resulttype),
                                               p_context.LABELS[proj_uN_0 l']? = some r'
                                             ∧ Resulttype_sub (list.mk_list ts) r'

        | admininstr.CALL
            (x : funcidx)           => ∃ (t1s t2s : List valtype),
                                           p_functype = (t1s f-> t2s)
                                         ∧ p_context.FUNCS[proj_uN_0 x]? = some (t1s f-> t2s)

        | admininstr.CALL_INDIRECT
            (x : tableidx)
            (y : typeidx)           => ∃ (t1s t2s : List valtype) (lim : limits),
                                           p_functype = ((t1s ++ [valtype.I32]) f-> t2s)
                                         ∧ p_context.TABLES[proj_uN_0 x]? = (tabletype.mk_tabletype lim reftype.FUNCREF)
                                         ∧ p_context.TYPES[proj_uN_0 y]? = some (t1s f-> t2s)

        | admininstr.RETURN         => ∃ (t1s ts t2s : List valtype),
                                           p_functype = ((t1s ++ ts) f-> t2s)
                                         ∧ p_context.RETURN = some (list.mk_list ts)

        | admininstr.CONST
            (nt : numtype)
            (c : num_)              => p_functype = ([] f-> [valtype_numtype nt])
                                     ∧ wf_num_ nt c

        | admininstr.UNOP
            (nt : numtype)
            (u : unop_)             => p_functype = ([valtype_numtype nt] f-> [valtype_numtype nt])


        | admininstr.BINOP
            (nt : numtype)
            (b : binop_)            => p_functype = ([valtype_numtype nt, valtype_numtype nt] f-> [valtype_numtype nt])

        | admininstr.TESTOP
            (nt : numtype)
            (t : testop_)           => p_functype = ([valtype_numtype nt] f-> [valtype.I32])

        | admininstr.RELOP
            (nt : numtype)
            (r : relop_)            => p_functype = ([valtype_numtype nt, valtype_numtype nt] f-> [valtype.I32])

        -- TODO: I think we don't split into both cvtop-reinterpret and cvtop-convert
        -- because cvtop *includes* REINTERPRET, and that causes the proof to jam.
        -- To solve this, we need to modify the syntax so that they are separate, which
        -- I think is the TODO already in 6-typing.spectec for Wasm 2.0.
        | admininstr.CVTOP
            (nt1 : numtype)
            (nt2 : numtype)
            (c : cvtop__)           => p_functype = ([valtype_numtype nt2] f-> [valtype_numtype nt1])

        | admininstr.VCONST
            (vt : vectype)
            (c : vec_)              => ∃ (uN_size : Nat),
                                           size (valtype_vectype vt) = some uN_size
                                         ∧ wf_uN uN_size c
                                         ∧ p_functype = ([] f-> [valtype_vectype vt])

        | admininstr.REF_NULL
            (rt : reftype)          => p_functype = ([] f-> [valtype_reftype rt])
        | admininstr.REF_FUNC
            (x : funcidx)           => ∃ (ft : functype),
                                           p_functype = ([] f-> [valtype_reftype reftype.FUNCREF])
                                         ∧ p_context.FUNCS[proj_uN_0 x]? = some ft

        | admininstr.REF_IS_NULL    => ∃ (rt : reftype),
                                           p_functype = ([valtype_reftype rt] f-> [valtype.I32])

        | admininstr.LOCAL_GET
            (x : localidx)          => ∃ (t : valtype),
                                           p_functype = ([] f-> [t])
                                         ∧ p_context.LOCALS[proj_uN_0 x]? = some t

        | admininstr.LOCAL_SET
            (x : localidx)          => ∃ (t : valtype),
                                           p_functype = ([t] f-> [])
                                         ∧ p_context.LOCALS[proj_uN_0 x]? = some t

        | admininstr.LOCAL_TEE
            (x : localidx)          => ∃ (t : valtype),
                                           p_functype = ([t] f-> [t])
                                         ∧ p_context.LOCALS[proj_uN_0 x]? = some t

        | admininstr.GLOBAL_GET
            (x : globalidx)         => ∃ (t : valtype) (m : «mut»),
                                           p_functype = ([] f-> [t])
                                         ∧ p_context.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype m t)

        | admininstr.GLOBAL_SET
            (x : globalidx)         => ∃ (t : valtype) (m : «mut»),
                                           p_functype = ([t] f-> [])
                                         ∧ p_context.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype m t)

        | admininstr.TABLE_GET
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype.I32] f-> [valtype_reftype rt])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)

        | admininstr.TABLE_SET
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype.I32, valtype_reftype rt] f-> [])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)


        | admininstr.TABLE_SIZE
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([] f-> [valtype.I32])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)

        | admininstr.TABLE_GROW
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype_reftype rt, valtype.I32] f-> [valtype.I32])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)

        | admininstr.TABLE_FILL
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype.I32, valtype_reftype rt, valtype.I32] f-> [])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)

        | admininstr.TABLE_COPY
            (x1 : tableidx)
            (x2 : tableidx)         => ∃ (rt : reftype) (lim1 lim2 : limits),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.TABLES[proj_uN_0 x1]? = some (tabletype.mk_tabletype lim1 rt)
                                         ∧ p_context.TABLES[proj_uN_0 x2]? = some (tabletype.mk_tabletype lim2 rt)

        | admininstr.TABLE_INIT
            (x1 : tableidx)
            (x2 : elemidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.TABLES[proj_uN_0 x1]? = some (tabletype.mk_tabletype lim rt)
                                         ∧ p_context.ELEMS[proj_uN_0 x2]? = some rt

        | admininstr.ELEM_DROP
            (x : elemidx)           => ∃ (rt : reftype),
                                           p_functype = ([] f-> [])
                                         ∧ p_context.ELEMS[proj_uN_0 x]? = some rt

        | admininstr.LOAD
            (nt : numtype)
            none
            (marg : memarg)         => ∃ (mt : memtype) (s : Nat),
                                           p_functype = ([valtype.I32] f-> [valtype_numtype nt])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ size (valtype_numtype nt) = some s
                                         ∧ 2^(proj_uN_0 marg.ALIGN) ≤ (s / 8)

        -- TODO: probably correct, but check ai-gen
        | admininstr.LOAD
            (nt : numtype)
            (
                some (
                    loadop_.mk_loadop__0
                    (inntype : Inn)
                    (
                        loadop_Inn.mk_loadop_Inn
                        (sz.mk_sz (num_bits_to_read : Nat))
                        _ -- (issigned : sx)
                    )
                )
            )
            (marg : memarg)         => nt = numtype_Inn inntype
                                     ∧ ∃ (mt : memtype),
                                           p_functype = ([valtype.I32] f-> [valtype_Inn inntype])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ 2^(proj_uN_0 marg.ALIGN) ≤ (num_bits_to_read / 8)

        | admininstr.STORE
            (nt : numtype)
            none
            (marg: memarg)          => ∃ (mt : memtype) (s : Nat),
                                           p_functype = ([valtype.I32, valtype_numtype nt] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ size (valtype_numtype nt) = some s
                                         ∧ 2^(proj_uN_0 marg.ALIGN) ≤ (s / 8)

        | admininstr.STORE
            (nt : numtype)
            (some (sz.mk_sz (num_bits_to_read : Nat)))
            (marg : memarg)

                                    -- unlike the LOAD case, we need to
                                    -- existentially quantify inntype here
                                    -- because it is not uniquely determined by
                                    -- num_bits_to_read
                                    => ∃ (mt : memtype) (inntype : Inn),
                                           nt = numtype_Inn inntype
                                         ∧ p_functype = ([valtype.I32, valtype_numtype nt] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ 2^(proj_uN_0 marg.ALIGN) ≤ (num_bits_to_read / 8)

        | admininstr.MEMORY_SIZE    => ∃ (mt : memtype),
                                           p_functype = ([] f-> [valtype.I32])
                                         ∧ p_context.MEMS[0]? = some mt

        | admininstr.MEMORY_GROW    => ∃ (mt : memtype),
                                           p_functype = ([valtype.I32] f-> [valtype.I32])
                                         ∧ p_context.MEMS[0]? = some mt

        | admininstr.MEMORY_FILL    => ∃ (mt : memtype),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt

        | admininstr.MEMORY_COPY    => ∃ (mt : memtype),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt

        | admininstr.MEMORY_INIT
            (x : dataidx)           => ∃ (mt : memtype),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ p_context.DATAS[proj_uN_0 x]? = some datatype.OK

        | admininstr.DATA_DROP
            (x : dataidx)           => p_functype = ([] f-> [])
                                     ∧ p_context.DATAS[proj_uN_0 x]? = some datatype.OK

        | admininstr.REF_FUNC_ADDR
            (a : funcaddr)          => ∃ (ft : functype),
                                           p_functype = ([] f-> [valtype_reftype reftype.FUNCREF])
                                         ∧ Externaddr_ok p_store (externaddr.FUNC a) (externtype.FUNC ft)

        | admininstr.CALL_ADDR
            (a : funcaddr)          => ∃ (ts1 ts2 : List valtype),
                                           p_functype = (ts1 f-> ts2)
                                         ∧ Externaddr_ok p_store (externaddr.FUNC a) (externtype.FUNC (ts1 f-> ts2))

        | admininstr.LABEL_
            (_n : n)
            (instrs : List instr)
            (admininstrs : List admininstr)
                                    => ∃ (ts t's : List valtype),
                                           p_functype = ([] f-> ts)
                                         ∧ t's.length = _n
                                         ∧ Instrs_ok2
                                               p_store
                                               p_context
                                               (instrs.map admininstr_instr)
                                               (t's f-> ts)
                                         ∧ Instrs_ok2
                                               p_store
                                               {p_context with LABELS := (list.mk_list t's) :: p_context.LABELS}
                                               admininstrs
                                               ([] f-> ts)

        | admininstr.FRAME_
            (n_ : n)
            (f : frame)
            (admininstrs : List admininstr)
                                    => ∃ (ts : List valtype) (c' : context),
                                           p_functype = ([] f-> ts)
                                         ∧ Frame_ok p_store f c'
                                         ∧ Expr_ok2 p_store ({ c' with RETURN := some (list.mk_list ts) }) admininstrs (list.mk_list ts)

        | admininstr.TRAP           => true

        -- TODO: I think this hasn't been implemented yet in the spec?
        | admininstr.EXTEND
            (_ : numtype)
            (_ : n)                 => false

        | _                         => true

def instr_principal_typing
    (context : context) (instruction : instr) (functype : functype) : Prop :=
    ai_principal_typing
        -- NOTE!!
        --
        -- We rely on the fact that the store is not used in any instr, so we
        -- pass a dummy store to reduce work.
        (store.MKstore [] [] [] [] [] [])

        context
        (admininstr_instr instruction)
        functype

theorem instr_typing_inversion
    (c : context)
    (instr : instr)
    (t1s t2s : List valtype)
    :
    Instr_ok c instr (t1s f-> t2s) →
    instr_principal_typing c instr (t1s f-> t2s) :=
    by
        intro h
        cases h
        <;> unfold instr_principal_typing
        <;> unfold ai_principal_typing
        <;> simp only [admininstr_instr]
        <;> try simp_all

        case drop t wf_drop wf_c =>
            exists t

        case select_impl
            t t' nt vt subt
            t'_constraints wf_select wf_c =>
            exists t
            apply And.intro
            · rfl
            · exists t'
              apply And.intro
              · exact subt
              · exists nt
                rcases t'_constraints with t'_constraint | t'_constraint
                · left
                  exact t'_constraint
                · right
                  exists vt

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
            lidx t1s ts wf_br lidx_within_LABELS LABELS_gives_ts wf_c =>
            exists t1s
            exists ts
            apply And.intro
            · exists t2s
            · unfold proj_list_0 at LABELS_gives_ts
              have hlab : c.LABELS[proj_uN_0 lidx] = mk_list ts :=
                Eq.subst (motive := fun z => c.LABELS[proj_uN_0 lidx] = mk_list z) LABELS_gives_ts rfl
              exact hlab

        case br_if
            lidx wf_br_if lidx_within_LABELS wf_c LABELS_gives_t2s =>
            exists t2s
            apply And.intro
            · rfl
            · unfold proj_list_0 at LABELS_gives_t2s
              have h : c.LABELS[(proj_uN_0 lidx)] = (mk_list t2s) :=
                Eq.subst (motive := fun x => c.LABELS[(proj_uN_0 lidx)] = mk_list x) LABELS_gives_t2s rfl
              exact h

        case br_table
            ls l' t1s ts wf_br_table ls_within_LABELS l'_within_LABELS ts_sub_ls l'_within_LABELS2 ts_sub_l' wf_c =>
            exists t1s
            exists ts
            apply And.intro
            · exists t2s
            · intro l hl
              have l_within_LABELS : (proj_uN_0 l) < c.LABELS.length :=
                ls_within_LABELS l hl
              refine ⟨c.LABELS[proj_uN_0 l]'l_within_LABELS, by simp, ?_, ts_sub_l'⟩
              have h : Resulttype_sub (mk_list ts) (c.LABELS[(proj_uN_0 l)]?.getD default) :=
                ts_sub_ls l hl
              have hh : c.LABELS[(proj_uN_0 l)]?.getD default = c.LABELS[(proj_uN_0 l)] :=
                by
                  simp [l_within_LABELS]
              rw [hh] at h
              exact h

        · case call
            idx wf_call idx_within_FUNCS wf_c FUNCS_gives_ft =>
            exists t1s
            exists t2s

        · case call_indirect
            idx1 idx2 t1s lim wf_call_indirect wf_tt idx1_within_TABLES idx2_within_TYPES
            TABLES_gives_tt idx2_within_TYPES2 wf_c TYPES_gives_ft =>
            exists t1s, t2s

        · case «return»
            t1s ts wf_return RETURN_gives_ts wf_c =>
            exists t1s, t2s

        · case const
            nt n wf_const wf_c =>
            cases wf_const with
            | instr_case_13 nt n h =>
                exact h

            -- cases wf_const
            -- rename_i blah
            -- exact blah

            -- rcases wf_const with ⟨s⟩
            -- rename_i blah
            -- exact blah

        · case ref_func
            idx ft wf_ref_func idx_in_FUNCS FUNCS_gives_ft wf_c =>
            rfl

        · case ref_is_null
            rt wr_ref_is_null wf_c =>
            exists rt

        · case vconst
            vec wf_vconst wf_c =>
            cases wf_vconst with
            | instr_case_20 vt v not_none_size wf_vec =>
                refine ⟨(size (valtype_vectype vectype.V128)).get!, ?_, ?_, ?_⟩
                -- · have x := Option.ne_none_iff_exists.mp not_none_size
                · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp not_none_size
                  rfl

                · exact wf_vec

                · rfl


                -- refine ⟨?_, ?_, ?_, ?_⟩
                -- · cases wf_vec with
                --   | uN_case_0 n i h =>
                --       exists n


                -- cases wf_vec with
                -- | uN_case_0 n i =>
                --     exists n

        · case load_val
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

        · case load_pack
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

                    -- rcases Nat.eq_zero_or_pos n2 with hz_n2 | hpos_n2
                    -- · subst hz_n2
                    --   simp at h ⊢
                    --   exact h
                    -- · rcases Nat.eq_zero_or_pos n1 with hz_n1 | hpos_n1
                    --   · subst hz_n1
                    --     simp at h ⊢
                    --     exact h
                    --   ·

        · case store_val
            nt marg mt MEMS_length_nonzero nt_size_not_none size_constraint
            wf_mt wf_store MEMS_length_nonzero2 mt_at_MEMS_0_idx wf_c =>
            refine ⟨(size (valtype_numtype nt)).get!, ?_, ?_⟩
            · cases nt <;>
              simp [size, valtype_numtype]
            · cases nt <;>
              simp [size, valtype_numtype, Option.bind, Option.get] at size_constraint ⊢ <;>
              norm_num at size_constraint <;>
                exact_mod_cast size_constraint

        · case store_pack
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


def instrtype_sub (original_ft contextualized_ft : functype) : Prop :=
  match original_ft, contextualized_ft with
  | mk_functype (mk_list original_input_type) (mk_list original_output_type),
    mk_functype (mk_list actual_supplied_input_type) (mk_list actual_needed_output_type) =>
    ∃ (rest_in rest_out supplied_in needed_out : List valtype),
      actual_supplied_input_type = rest_in ++ supplied_in
      ∧ actual_needed_output_type = rest_out ++ needed_out
      ∧ (rest_in subs< rest_out)
      ∧ (supplied_in subs< original_input_type)
      ∧ (original_output_type subs< needed_out)

infix:20 "instrsub<" => instrtype_sub -- TODO: move to notation

theorem principal_typing_conversion (i : instr) :
  ∀ (s : store) (c : context) (t1s t2s : List valtype),
    instr_principal_typing c i (t1s f-> t2s)
    ↔ ai_principal_typing s c (admininstr_instr i) (t1s f-> t2s) := by
  intro s c t1s t2s
  unfold instr_principal_typing
  cases i <;> try rfl
  case SELECT op_ts
    =>
    cases op_ts
    case none =>
      rfl
    case some t =>
      cases t
      case nil => rfl
      case cons head tail =>
        cases tail
        case nil => rfl
        case cons head' tail' =>
          rfl

  case LOAD nt o_loadop marg =>
    cases o_loadop
    case none => rfl
    case some loadop =>
      cases loadop
      case mk_loadop__0 inn l_inn =>
        rfl

  case STORE nt o_sz marg =>
    cases o_sz
    case none => rfl
    case some sz =>
      rfl

  -- TODO: find out why this other approach was so slow

  -- apply Iff.intro
  -- case mp =>
  --   intro i_principal
  --   unfold instr_principal_typing at *
  --   cases i
  --   <;> try rfl

  --   case NOP =>
  --     unfold ai_principal_typing at *
  --     unfold admininstr_instr at *
  --     simp_all
  --   case DROP =>
  --     unfold ai_principal_typing at *
  --     unfold admininstr_instr at *
  --     simp_all



  -- case mpr => sorry

theorem instrtype_sub_refl
  (ft : functype)
  :
  ft instrsub< ft
  := by
  sorry

theorem ai_typing_inversion
  (s          : store)
  (c          : context)
  (ainstr     : admininstr)
  (t1s t2s    : List valtype)
  :
  Instr_ok2 s c ainstr (t1s f-> t2s) →
  ∃ t1s' t2s',
    ai_principal_typing s c ainstr (t1s' f-> t2s')
    ∧ ((t1s' f-> t2s') instrsub< (t1s f-> t2s))
  := by
  intros instr_ok2
  generalize gen_ft : (t1s f-> t2s) = ft at instr_ok2
  cases instr_ok2 using Instr_ok2.casesOn
  case plain
    i t1s' t2s' wf_s wf_i instr_ok wf_c
    =>
    refine ⟨t1s', t2s', ?_, ?_⟩
    case refine_1 =>
      apply (principal_typing_conversion i s c t1s' t2s').mp
      apply instr_typing_inversion
      exact instr_ok

    case refine_2 =>
      exact instrtype_sub_refl _

  case Instr_ok2_frame
    return_length f ais ts c' frame_ok expr_ok2 wf_s wf_c' wf_ai wf_c'' length wf_c
    =>
    refine ⟨t1s, t2s, ?_, ?_⟩
    case refine_1 =>
      unfold mkFunctype at *
      simp_all
      unfold ai_principal_typing
      simp_all
      refine ⟨ts, ?_⟩
      unfold mkFunctype at *
      simp_all
      refine ⟨c', ?_, ?_⟩
      case refine_1 => exact frame_ok
      case refine_2 => exact expr_ok2
    case refine_2 =>
      simp [mkFunctype] at gen_ft
      obtain ⟨t1s_eq, t2s_eq⟩ := gen_ft
      rw [t1s_eq, t2s_eq]
      exact instrtype_sub_refl _

  case label
    arity is ais ts ts' wf_s wf_ai wf_context_with_LABELS length instrs_ok_is instrs_ok_ais wf_c
    =>
    refine ⟨t1s, t2s, ?_, ?_⟩
    case refine_1 =>
      unfold mkFunctype at *
      unfold ai_principal_typing
      simp_all
      refine ⟨ts, ?_, ?_⟩
      case refine_1 => rfl
      case refine_2 =>
        refine ⟨ts', ?_, ?_, ?_⟩
        case refine_1 => rfl
        case refine_2 =>
          unfold mkFunctype at *
          exact instrs_ok_is
        case refine_3 =>
          exact instrs_ok_ais
    case refine_2 =>
      simp [mkFunctype] at gen_ft
      obtain ⟨t1s_eq, t2s_eq⟩ := gen_ft
      rw [t1s_eq, t2s_eq]
      exact instrtype_sub_refl _
  case call_addr
    faddr t1s' t2s' externaddr_ok wf_s wf_ais wf_ext wf_c
    =>
    unfold mkFunctype at *
    simp_all
    refine ⟨t1s, t2s, ?_, ?_⟩
    case refine_1 =>
      unfold ai_principal_typing
      simp_all
      refine ⟨t1s', t2s', ?_, ?_⟩
      case refine_1 => rfl
      case refine_2 => exact externaddr_ok
    case refine_2 =>
      obtain ⟨t1s_eq, t2s_eq⟩ := gen_ft
      rw [t1s_eq, t2s_eq]
      exact instrtype_sub_refl _
  case ref
    r rt ref_ok wf_s wf_c
    =>
    refine ⟨t1s, t2s, ?_, ?_⟩
    case refine_1 =>
      unfold ai_principal_typing admininstr_ref
      simp_all
      unfold mkFunctype at *
      cases r <;> simp_all
      case REF_NULL rt'=>
        unfold valtype_reftype at *
        cases rt <;> cases rt' <;> simp_all
        case FUNCREF.EXTERNREF => cases ref_ok
        case EXTERNREF.FUNCREF => cases ref_ok
      case REF_FUNC_ADDR faddr' =>
        cases ref_ok
        case func ext wf_s' wf_ext externaddr_ok =>
          apply And.intro
          case left => rfl
          case right => exists ext
    case refine_2 =>
      simp [mkFunctype] at gen_ft
      obtain ⟨t1s_eq, t2s_eq⟩ := gen_ft
      rw [t1s_eq, t2s_eq]
      exact instrtype_sub_refl _
  case trap
    t1s' t2s' wf_s wf_ai wf_c
    =>
    obtain ⟨t1s_eq, t2s_eq⟩ := gen_ft
    refine ⟨t1s, t2s, ?_, ?_⟩
    case refine_1 =>
      unfold ai_principal_typing
      simp
    case refine_2 =>
      exact instrtype_sub_refl _
  -- obtain ⟨⟨t1s', t2s'⟩, ai_princ_typing, t1s't2s'_ftsub_t1st2s⟩ := ai_typing_inversion_helper s c ainstr t1s t2s instr_ok2
  -- all_goals unfold ai_principal_typing mkFunctype admininstr_instr
  -- all_goals simp_all
  -- case plain wf_s wf_i wf_c instr_ok =>

  --   sorry
  -- case label => sorry
  -- case frame => sorry
  -- case call_addr => sorry
  -- case ref => sorry
  -- case trap => sorry


-- mutual
-- inductive StepOk : Nat → Prop where
--   | step : ∀ n, n ≠ 0 → StepOk n              -- like Instr_ok2: about one item

-- inductive SeqOk : List Nat → Prop where        -- like Instrs_ok2: a sequence
--   | nil  : SeqOk []
--   | cons : ∀ n ns, StepOk n → SeqOk ns → SeqOk (n :: ns)

-- inductive ProgOk : List Nat → Prop where       -- like Expr_ok2: wraps a sequence
--   | prog : ∀ ns, SeqOk ns → ProgOk ns
-- end
-- set_option pp.proofs true
-- #check StepOk.rec
-- theorem prog_all_nonzero (ns : List Nat) (h : ProgOk ns) : ∀ x ∈ ns, x ≠ 0 := by
--   induction h using ProgOk.rec
--     (motive_1 := fun n _ => n ≠ 0)
--     (motive_2 := fun ns _ => ∀ x ∈ ns, x ≠ 0)

theorem ainstr_ok_context_store_wf
  (s : store)
  (c : context)
  (ai : admininstr)
  (ft : functype)
  :
  Instr_ok2 s c ai ft
  → wf_context c
    ∧ wf_store s
    ∧ wf_admininstr ai

  := by
  intro instr_ok
  refine ⟨?_, ?_, ?_⟩
  case refine_1 =>
    cases instr_ok using Instr_ok2.casesOn
    <;> try aesop
  case refine_2 =>
    cases instr_ok using Instr_ok2.casesOn
    <;> try aesop
  case refine_3 =>
    cases instr_ok using Instr_ok2.casesOn
    <;> try aesop
    case plain i t1s t2s wf_s wf_i instr_ok wf_c =>
      cases wf_i <;> constructor <;> assumption
    case ref r rt ref_ok wf_s wf_c =>
      cases ref_ok <;> constructor

theorem construct_ais_typing_single
  (s : store)
  (c : context)
  (ai : admininstr)
  (t1s t2s : List valtype)
  :
  Instr_ok2 s c ai (t1s f-> t2s) →
  Instrs_ok2 s c [ai] (t1s f-> t2s) := by

  intro instr_ok
  have wf_c_s_a := ainstr_ok_context_store_wf s c ai (t1s f-> t2s) instr_ok
  obtain ⟨wf_c, wf_s, wf_ai⟩ := wf_c_s_a
  constructor
  case a => assumption
  case a => assumption
  case a => assumption
  case a => assumption

theorem construct_ai_const_I32
  (s : store)
  (c : context)
  (n : num_)
  :
  wf_num_ numtype.I32 n
  → wf_context c
  → wf_store s
  → Instr_ok2 s c (admininstr.CONST numtype.I32 n) ([] f-> [valtype.I32])

  := by
  intro wf_n wf_c wf_s

  unfold mkFunctype at *
  apply Instr_ok2.plain s c (instr.CONST numtype.I32 n) [] [valtype.I32]

  case a =>
    constructor
    case a => assumption
    case a =>
      constructor
      assumption
  case a =>
    assumption
  case a => assumption
  case a =>
    constructor
    assumption


theorem construct_ais_subtyping
  (s : store)
  (c : context)
  (ais : List admininstr)
  (t1s t2s t1s' t2s' : List valtype)
  :
  Instrs_ok2 s c ais (t1s f-> t2s)
  → (t1s f-> t2s) ftsub< (t1s' f-> t2s')
  → Instrs_ok2 s c ais (t1s' f-> t2s')

  := by

  intro instrs_ok2 ft_sub_rel
  cases ft_sub_rel
  assumption

def inst_match (c1 c2 : context) : Prop :=
  c1.TYPES = c2.TYPES
  ∧ c1.FUNCS = c2.FUNCS
  ∧ c1.GLOBALS = c2.GLOBALS
  ∧ c1.TABLES = c2.TABLES
  ∧ c1.MEMS = c2.MEMS
  ∧ c1.ELEMS = c2.ELEMS
  ∧ c1.DATAS = c2.DATAS

theorem ainstrs_ok_context_store_wf
  (s : store)
  (c : context)
  (ais : List admininstr)
  (ft : functype)
  :
  Instrs_ok2 s c ais ft
  → wf_context c
    ∧ wf_store s
    ∧ ∀ ai ∈ ais, wf_admininstr ai

  := by
  intro instrs_ok
  refine ⟨?_, ?_, ?_⟩
  case refine_1 =>
    cases instrs_ok using Instrs_ok2.casesOn
    <;> try assumption
  case refine_2 =>
    cases instrs_ok using Instrs_ok2.casesOn
    <;> try assumption
  case refine_3 =>
    cases instrs_ok using Instrs_ok2.casesOn
    <;> try aesop

theorem construct_ais_compose
  (s : store)
  (c : context)
  (ais1 ais2 : List admininstr)
  (t1s t2s t3s : List valtype)
  :
  Instrs_ok2 s c ais1 (t1s f-> t2s)
  → Instrs_ok2 s c ais2 (t2s f-> t3s)
  → Instrs_ok2 s c (ais1 ++ ais2) (t1s f-> t3s)

  := by

  intro seq1 seq2
  apply Instrs_ok2.seq s c ais1 ais2 t1s t3s t2s
  case a => assumption
  case a => assumption
  case a => cases seq1 <;> assumption
  case a => cases seq1 <;> assumption
  case a =>
    have h := ainstrs_ok_context_store_wf s c ais1 (t1s f-> t2s) seq1
    obtain ⟨wf_c, wf_s, wf_ais1⟩ := h
    simp [Forall]
    assumption
    -- This works as well if we want to remove ainstrs_ok_context_store_wf
    -- simp [Forall]
    -- intro ai ai_from_ais1
    -- cases seq1 <;> try aesop
  case a =>
    have h := ainstrs_ok_context_store_wf s c ais2 (t2s f-> t3s) seq2
    obtain ⟨wf_c, wf_s, wf_ais2⟩ := h
    simp [Forall]
    assumption

def Vals_ok (s : store) (vals : List val) (ts : List valtype) : Prop :=
  -- TODO: should we fix the generated Forall₂ to match the mathlib one
  Forall₂ (fun (t : valtype) (v : val) => Val_ok s v t) ts vals

theorem Val_ok_non_bot (s : store) (v : val) (vt : valtype) :
  Val_ok s v vt → vt ≠ valtype.BOT := by
  intro h
  cases h
  case numtype nt n wf_s wf_v =>
    cases nt
    <;> unfold valtype_numtype at *
    <;> simp_all
  case vectype vt v wf_s wf_v  =>
    cases vt
    unfold valtype_vectype at *
    simp_all
  case reftype r rt ref_ok wf_s =>
    cases r
    <;> cases rt
    <;> unfold valtype_reftype at *
    <;> simp_all

theorem construct_ai_val
  (s : store)
  (c : context)
  (v : val)
  (vt : valtype)
  :
  Val_ok s v vt
  → wf_context c
  → wf_store s
  → Instr_ok2 s c (admininstr_val v) ([] f-> [vt])

  := by

  intro val_ok wf_c wf_s
  cases val_ok
  case numtype nt n wf_s' wf_v =>
    unfold mkFunctype at *
    simp_all
    apply Instr_ok2.plain s c (instr.CONST nt n) [] [valtype_numtype nt]
    case a =>
      constructor
      case a => assumption
      case a =>
        constructor
        cases wf_v
        case val_case_0 => assumption
    case a => assumption
    case a => assumption
    case a =>
      cases wf_v
      case val_case_0 wf_n =>
        constructor
        assumption

  case vectype vt v wf_s' wf_v =>
    unfold mkFunctype at *
    simp_all
    apply Instr_ok2.plain s c (instr.VCONST vt v) [] [valtype_vectype vt]
    case a =>
      constructor
      case a => assumption
      case a =>
        constructor
        case a =>
          unfold valtype_vectype at *
          unfold size at *
          simp_all
        case a =>
          cases v
          case mk_uN i =>
            cases wf_v
            case val_case_1 size_vt_not_none wf_un =>
              simp_all
    case a => assumption
    case a => assumption
    case a =>
      constructor
      case a =>
        unfold valtype_vectype at *
        unfold size at *
        simp_all
      case a =>
        cases v
        case mk_uN i =>
          cases wf_v
          case val_case_1 size_vt_not_none wf_un =>
            simp_all

  case reftype r rt ref_ok wf_s' =>
    unfold mkFunctype at *
    simp_all
    cases r
    case REF_NULL rt' =>
      simp [val_ref, admininstr_val]
      apply Instr_ok2.ref s c (ref.REF_NULL rt') rt
      <;> assumption
    case REF_FUNC_ADDR faddr' =>
      simp [val_ref, admininstr_val]
      apply Instr_ok2.ref s c (ref.REF_FUNC_ADDR faddr') rt
      <;> assumption
    case REF_HOST_ADDR haddr' =>
      simp [val_ref, admininstr_val]
      apply Instr_ok2.ref s c (ref.REF_HOST_ADDR haddr') rt
      <;> assumption

theorem instr_subtyping_weaken2
  (tx1 tx2 ty1 ty2 ty2_sup : List valtype)
  :
  ((tx1 f-> ty1) instrsub< (tx2 f-> ty2))
  → (ty2 subs< ty2_sup)
  → ((tx1 f-> ty1) instrsub< (tx2 f-> ty2_sup))
  := by
  sorry

theorem instrtype_sub_trans
  (ft1 ft2 ft3 : functype)
  :
  (ft1 instrsub< ft2)
  → (ft2 instrsub< ft3)
  → (ft1 instrsub< ft3)
  := by
  intros ft1_sub_ft2 ft2_sub_ft3
  unfold instrtype_sub at *
  simp_all

  sorry

theorem instr_subtyping_strengthen2
  (tx1 tx2 ty1 ty2 tx2_sub : List valtype)
  :
  ((tx1 f-> ty1) instrsub< (tx2 f-> ty2))
  → (tx2_sub subs< tx2)
  → ((tx1 f-> ty1) instrsub< (tx2_sub f-> ty2))
  := by
  intros orig_instrsub sub_rel
  unfold instrtype_sub at *
  unfold mkFunctype at *
  simp_all
  obtain ⟨
    rest_in,
    rest_out,
    supplied_in,
    tx2_breakdown,
    needed_out,
    ty2_breakdown,
    rest_in_subs_rest_out,
    supplied_in_subs_tx1,
    ty1_subs_needed_out
  ⟩ := orig_instrsub
  simp_all
  cases sub_rel
  case mk_Resulttype_sub length elemwise_sub =>
    simp_all
    have split_tx2_sub : tx2_sub = tx2_sub.take rest_in.length ++ tx2_sub.drop rest_in.length := by
      rw [List.take_append_drop]
    have length' : tx2_sub.length = (rest_in ++ supplied_in).length := by
      grind
    have elemwise_sub' := to_mathlib_forall₂ length' elemwise_sub
    have rest_in':
      List.Forall₂
        (fun t_1_elem t_2_elem => (t_1_elem sub<t_2_elem))
        (List.take rest_in.length tx2_sub)
        rest_in
        := by
      exact List.forall₂_take_append tx2_sub rest_in supplied_in elemwise_sub'
    have rest_out':
      List.Forall₂
        (fun t_1_elem t_2_elem => (t_1_elem sub<t_2_elem))
        (List.drop rest_in.length tx2_sub)
        supplied_in
        := by
      exact List.forall₂_drop_append tx2_sub rest_in supplied_in elemwise_sub'
    exists (List.take rest_in.length tx2_sub), rest_out, (List.drop rest_in.length tx2_sub)
    refine ⟨?_, ?_⟩
    case refine_1 => grind
    case refine_2 =>
      exists needed_out
      refine ⟨?_, ?_, ?_, ?_⟩
      case refine_1 => rfl
      case refine_2 =>
        apply resulttype_sub_trans
        case t2s => exact rest_in
        case h2 =>
          exact rest_in_subs_rest_out
        case h1 =>
          apply Resulttype_sub.mk_Resulttype_sub
          case a => exact rest_in'.length_eq
          case a =>
            apply from_mathlib_forall₂
            exact rest_in'
      case refine_3 =>
        apply resulttype_sub_trans
        case t2s => exact supplied_in
        case h2 => exact supplied_in_subs_tx1
        case h1 =>
          apply Resulttype_sub.mk_Resulttype_sub
          case a => exact rest_out'.length_eq
          case a => exact from_mathlib_forall₂ rest_out'
      case refine_4 =>
        exact ty1_subs_needed_out

theorem instrs_single_typing_inversion
  (c : context)
  (i : instr)
  (t1s t2s : List valtype)
  :
  Instrs_ok c [i] (t1s f-> t2s)
  → ∃ t1s_sup t2s_sub,
      Instr_ok c i (t1s_sup f-> t2s_sub)
      ∧ ((t1s_sup f-> t2s_sub) instrsub< (t1s f-> t2s))

  := by

  intros instrs_ok
  generalize l : [i] = instrs at instrs_ok
  generalize ft' : (t1s f-> t2s) = ft at instrs_ok
  induction instrs_ok
    using Instrs_ok.rec
    (motive_1 := fun _ _ _ _ => true)
    generalizing t1s t2s i
  <;> try simp_all

  case instr c' i' t1s' t2s' instr_ok wf_c' wf_i' =>

    refine ⟨t1s', t2s', ?_, ?_⟩
    case refine_1 =>
      exact instr_ok
    case refine_2 =>
      apply instrtype_sub_refl





  -- refine ⟨t1s, t2s, ?_, ?_⟩
  -- case refine_1 =>
  --   generalize is : [i] = instrs at instrs_ok
  --   cases instrs_ok
  --   case empty =>
  --     have h: False := by simp at is
  --     contradiction
  --   case instr i' wf_i'  i_is_i' instr_ok =>
  --     simp_all
  --     exact instr_ok
  --   case seq is1 is2 t3s wf_all_is1 wf_all_is2 wf_c instrs_ok_is1 instrs_ok_is2 =>
  --     have h : (is1 = [] ∧ is2 = [i]) ∨ (is1 = [i] ∧ is2 = []) := by
  --       exact (List.append_eq_singleton_iff.mp (id (Eq.symm is)))
  --     cases h
  --     case inl h_is1_is2 =>
  --       obtain ⟨is1_eq, is2_eq⟩ := h_is1_is2

  case seq
    c' is1 is2 t1s' t2s' t3s'
    instrs_ok_1 instrs_ok_2
    wf_c' wf_all_i1s wf_all_i2s
    ih1 ih2
    =>

    -- refine ⟨t1s', t2s', ?_, ?_⟩
    unfold mkFunctype at *
      -- simp_all
    have h : is1 = [] ∧ is2 = [i] ∨ is1 = [i] ∧ is2 = [] := by
      exact (List.append_eq_singleton_iff.mp (id (Eq.symm l)))
    cases h
    case inl h_is1_is2 =>
      obtain ⟨is1_eq, is2_eq⟩ := h_is1_is2
      rw [is1_eq] at instrs_ok_1
      have h := (instrs_empty_typing c' t1s' t3s').mp instrs_ok_1
      obtain ⟨wf_c'_2, t1s'_subs_t3s'⟩ := h
      have hh := ih2 i t3s' t2s' is2_eq.symm rfl
      obtain ⟨t1s_sup, t2s_sub, instr_ok, ft_sub_rel⟩ := hh
      exists t1s_sup, t2s_sub
      refine ⟨?_, ?_⟩
      case refine_1 =>
        exact instr_ok
      case refine_2 =>
        have strengthen := instr_subtyping_strengthen2 t1s_sup t3s' t2s_sub t2s' t1s'
        have strengthen_applied := strengthen ft_sub_rel t1s'_subs_t3s'
        exact strengthen_applied

    case inr h_is1_is2 =>
      obtain ⟨is1_eq, is2_eq⟩ := h_is1_is2
      rw [is2_eq] at instrs_ok_2
      have h := (instrs_empty_typing c' t3s' t2s').mp instrs_ok_2
      obtain ⟨wf_c'_2, t3s'_subs_t2s'⟩ := h
      have hh := ih1 i t1s' t3s' is1_eq.symm rfl
      obtain ⟨t1s_sup, t2s_sub, instr_ok, ft_sub_rel⟩ := hh
      exists t1s_sup, t2s_sub
      refine ⟨?_, ?_⟩
      case refine_1 =>
        exact instr_ok
      case refine_2 =>
        have weaken := instr_subtyping_weaken2 t1s_sup t1s' t2s_sub t3s' t2s'
        have weaken_applied := weaken ft_sub_rel t3s'_subs_t2s'
        exact weaken_applied

  case sub
    c' is t1s' t2s' t1s'' t2s'' instrs_ok
    t1s'_sub_t1s'' t2s''_sub_t2s'
    wf_c' wf_all_is ih
    =>
    unfold mkFunctype at *
    simp_all
    have h := ih i t1s'' t2s'' l rfl rfl
    obtain ⟨t1s_sup, t2s_sub, instr_ok, ft_sub_rel⟩ := h
    exists t1s_sup, t2s_sub
    refine ⟨?_, ?_⟩
    case refine_1 =>
      exact instr_ok
    case refine_2 =>
      apply instrtype_sub_trans
      apply ft_sub_rel
      unfold instrtype_sub
      unfold resulttypeSub at *
      simp_all
      exists [], [], t1s'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      rfl
      exact t2s'
      rfl
      apply resulttype_sub_refl
      exact t1s'_sub_t1s''
      exact t2s''_sub_t2s'

  case frame
    c' is ts t1s' t2s' instrs_ok wf_c' wf_all_is ih
    =>
    unfold mkFunctype at *
    simp_all
    have h := ih i t1s' t2s' l rfl rfl
    obtain ⟨t1s_sup, t2s_sub, instr_ok, ft_sub_rel⟩ := h
    exists t1s_sup, t2s_sub
    refine ⟨?_, ?_⟩
    case refine_1 =>
      exact instr_ok
    case refine_2 =>
      apply instrtype_sub_trans
      refine ft_sub_rel
      unfold instrtype_sub
      simp_all
      exists ts, ts, t1s'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      rfl
      exact t2s'
      rfl
      exact resulttype_sub_refl ts
      exact resulttype_sub_refl t1s'
      exact resulttype_sub_refl t2s'

theorem ais_single_typing_inversion'
  (s : store)
  (c : context)
  (ai : admininstr)
  (ts1 ts2 : List valtype)
  :
  Instrs_ok2 s c [ai] (ts1 f-> ts2)
  → ∃ ts1_sup ts2_sub,
      Instr_ok2 s c ai (ts1_sup f-> ts2_sub)
      ∧ ((ts1_sup f-> ts2_sub) instrsub< (ts1 f-> ts2))
  := by

  intro instrs_ok2
  generalize ais_contents : [ai] = ais at instrs_ok2
  generalize ft_contents : (ts1 f-> ts2) = ft at instrs_ok2
  #check Instrs_ok2.rec
  induction instrs_ok2
    using Instrs_ok2.rec
    (motive_1 := fun _ _ _ _ => true)
    (motive_3 := fun _ _ _ _ => true)
    generalizing ts1 ts2 ai
  <;> try simp_all
  case instr
    c' ai' ts1' ts2' instr_ok2 wf_s wf_c' wf_ai'
    =>
    refine ⟨ts1', ts2', ?_, ?_⟩
    case refine_1 =>
      exact instr_ok2
    case refine_2 =>
      unfold mkFunctype at *
      simp_all
      apply instrtype_sub_refl
  case seq
    c'
    ais1 ais2
    ts1' ts3' ts2'
    instrs_ok2_1 instrs_ok2_2
    wf_s wf_c
    wf_all_ais1 wf_all_ais2
    ih1 ih2

    =>

    have empty_and_filled_ais1_ais2 : ais1 = [] ∧ ais2 = [ai] ∨ ais1 = [ai] ∧ ais2 = [] := by
      exact (List.append_eq_singleton_iff.mp (id (Eq.symm ais_contents)))

    cases empty_and_filled_ais1_ais2
    case inl ais1_ais2 =>
      obtain ⟨ais1_empty, ais2_populated⟩ := ais1_ais2
      have ih2_applied := ih2 ai ts2' ts3' ais2_populated.symm rfl
      obtain ⟨ts1_sup, ts2_sub, instr_ok2, ft_sub_rel⟩ := ih2_applied
      exists ts1_sup, ts2_sub
      refine ⟨?_, ?_⟩
      case refine_1 =>
        exact instr_ok2
      case refine_2 =>
        unfold mkFunctype at *
        apply instrtype_sub_trans
        refine ft_sub_rel
        unfold instrtype_sub
        simp
        exists [], [], ts1'
        refine ⟨?_, ?_⟩
        case refine_1 => rfl
        case refine_2 =>
          exists ts3'
          refine ⟨?_, ?_, ?_, ?_⟩
          case refine_1 => rfl
          case refine_2 => apply resulttype_sub_refl
          case refine_3 =>
            rw [ais1_empty] at instrs_ok2_1
            have ⟨wf_c', wf_s_2, subsrel⟩ := (ais_empty_typing s c' ts1' ts2').mp instrs_ok2_1
            exact subsrel
          case refine_4 => apply resulttype_sub_refl

    case inr ais1_ais2 =>
      obtain ⟨ais1_populated, ais2_empty⟩ := ais1_ais2
      have ih1_applied := ih1 ai ts1' ts2' ais1_populated.symm rfl
      obtain ⟨ts1_sup, ts2_sub, instr_ok2, ft_sub_rel⟩ := ih1_applied
      exists ts1_sup, ts2_sub
      refine ⟨?_, ?_⟩
      case refine_1 =>
        exact instr_ok2
      case refine_2 =>
        unfold mkFunctype at *
        apply instrtype_sub_trans
        refine ft_sub_rel
        unfold instrtype_sub
        simp
        exists [], [], ts1'
        refine ⟨?_, ?_⟩
        case refine_1 => rfl
        case refine_2 =>
          exists ts3'
          refine ⟨?_, ?_, ?_, ?_⟩
          case refine_1 => simp
          case refine_2 => apply resulttype_sub_refl
          case refine_3 => apply resulttype_sub_refl
          case refine_4 =>
            rw [ais2_empty] at instrs_ok2_2
            have ⟨wf_c', wf_s_2, subsrel⟩ := (ais_empty_typing s c' ts2' ts3').mp instrs_ok2_2
            exact subsrel
  case sub
    c' ais' ts1' ts2' ts1'' ts2'' instrs_ok2
    ts1'_subs_ts1'' ts2''_subs_ts2'
    wf_s wf_c wf_all_ais' ih
    =>
    unfold mkFunctype at *
    simp_all
    have ih_applied := ih ai ts1'' ts2'' ais_contents rfl rfl
    obtain ⟨ts1_sup, ts2_sub, instr_ok2, ft_sub_rel⟩ := ih_applied
    exists ts1_sup, ts2_sub
    refine ⟨?_, ?_⟩
    case refine_1 =>
      exact instr_ok2
    case refine_2 =>
      obtain ⟨ts1_eq, ts2_eq⟩ := ft_contents
      rw [ts1_eq, ts2_eq] at *
      simp_all
      apply instrtype_sub_trans
      refine ft_sub_rel
      unfold instrtype_sub
      simp_all
      exists [], [], ts1'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      case a.refine_2 => exact ts2'
      case a.refine_1 => rfl
      case a.refine_3 => rfl
      case a.refine_4 => apply resulttype_sub_refl
      case a.refine_5 => exact ts1'_subs_ts1''
      case a.refine_6 => exact ts2''_subs_ts2'
      -- refine
      --   (instrtype_sub_trans (mk_functype (mk_list ts1'') (mk_list ts2'')) ?_
      --     (mk_functype (mk_list ts1') (mk_list ts2')) ?_ ?_)

  case Instrs_ok2_frame
    c' ais' ts ts1' ts2' instrs_ok2 wf_s wf_c' wf_forall_ais' ih
    =>

    unfold mkFunctype at *
    simp at ft_contents
    have ih_applied := ih ai ts1' ts2' ais_contents rfl
    obtain ⟨ts1_sup, ts2_sub, instr_ok2, ft_sub_rel⟩ := ih_applied
    exists ts1_sup, ts2_sub
    refine ⟨?_, ?_⟩
    case refine_1 =>
      exact instr_ok2
    case refine_2 =>
      apply instrtype_sub_trans
      refine ft_sub_rel
      unfold instrtype_sub
      simp
      refine ⟨
        ts,
        ts,
        ts1',
        rfl,
        ⟨
          ts2',
          ⟨
            rfl,
            by apply resulttype_sub_refl,
            by apply resulttype_sub_refl,
            by apply resulttype_sub_refl
          ⟩
        ⟩
      ⟩

      -- unfold instrtype_sub
      -- simp_all
      -- exists ts, ts, ts1'
      -- refine ⟨?_, ⟨ts2', ?_, ?_, ?_, ?_⟩⟩
      -- case refine_1 => rfl
      -- case refine_2 => rfl
      -- case refine_3 => apply resulttype_sub_refl
      -- case refine_4 =>
      --   unfold instrtype_sub at ft_sub_rel
      --   simp at ft_sub_rel
      --   obtain ⟨rest_in, rest_out, supplied_in, a1,x,a3, a4, a5, a6⟩ := ft_sub_rel


      --   sorry

theorem ais_single_typing_inversion
  (s : store)
  (c : context)
  (ai : admininstr)
  (ts1 ts2 : List valtype)
  :
  Instrs_ok2 s c [ai] (ts1 f-> ts2)
  → ∃ ts1_sup ts2_sub,
      ai_principal_typing s c ai (ts1_sup f-> ts2_sub)
      ∧ ((ts1_sup f-> ts2_sub) instrsub< (ts1 f-> ts2))
  := by
  intros instrs_ok2
  have asti' := ais_single_typing_inversion' s c ai ts1 ts2 instrs_ok2
  obtain ⟨ts1_sup, ts2_sub, instr_ok2, instrsub_rel⟩ := asti'
  have ai_inv := ai_typing_inversion s c ai ts1_sup ts2_sub instr_ok2
  obtain ⟨ts1', ts2', pt, instrsub_rel'⟩ := ai_inv
  exists ts1', ts2'
  refine ⟨?_, ?_⟩
  case refine_1 =>
    exact pt
  case refine_2 =>
    exact instrtype_sub_trans
      (ts1' f-> ts2')
      (ts1_sup f-> ts2_sub)
      (ts1 f-> ts2)
      instrsub_rel'
      instrsub_rel

  -- exists ts1_sup, ts2_sub
  -- refine ⟨?_, ?_⟩
  -- case refine_1 =>
  --   have ai_inv := ai_typing_inversion s c ai ts1_sup ts2_sub instr_ok2
  --   obtain ⟨ts1', ts2', pt, instrsub_rel'⟩ := ai_inv
  --   unfold ai_principal_typing

  --   sorry
  -- case refine_2 =>
  --   exact instrsub_rel

theorem instrs_seq_typing_inversion
  (c : context)
  (i : instr)
  (is : List instr)
  (ts1 ts3 : List valtype)
  :
  Instrs_ok c (i :: is) (ts1 f-> ts3)
  → ∃ ts2,
      Instr_ok c i (ts1 f-> ts2)
      ∧ Instrs_ok c is (ts2 f-> ts3)
  := by
  intros instrs_ok
  generalize instrs_eq : (i :: is) = instrs at instrs_ok
  generalize ft_eq : (ts1 f-> ts3) = ft at instrs_ok
  #check Instrs_ok.rec
  induction instrs_ok
    using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  <;> try simp_all
  case instr
    c' i' ts1_orig ts3_orig instr_ok wf_c' wf_i'
    =>
    obtain ⟨ts1_eq, ts3_eq⟩ := ft_eq
    obtain ⟨i_eq, is_eq⟩ := instrs_eq
    rw [i_eq, is_eq] at *
    simp_all
    exists ts3
    refine ⟨?_, ?_⟩
    case refine_1 =>
      exact instr_ok
    case refine_2 =>
      apply (instrs_empty_typing c' ts3 ts3).mpr
      refine ⟨?_, ?_⟩
      case refine_1 => assumption
      case refine_2 => apply resulttype_sub_refl
  case seq
    c' i_list_1 i_list_2 ts1_orig ts3_orig ts2_orig instrs_ok_ts1_to_ts2 instrs_ok_ts2_to_ts3 wf_c' wf_all_i_list wf_all_is_list ih_i_list ih_is_list
    =>
    unfold mkFunctype at ft_eq
    simp at ft_eq
    sorry
    -- exists ts2_orig
    -- refine ⟨?_, ?_⟩
    -- unfold mkFunctype at *
    -- simp_all
    -- obtain ⟨ts1_eq, ts3_eq⟩ := ft_eq
    -- subst ts1_eq
    -- subst ts3_eq
    -- case refine_1 =>
    --   cases i_list
    --   case nil =>
    --     cases is_list
    --     case nil =>
    --       have f : False := by aesop
    --       contradiction
    --     case cons is_list_hd is_list_tl =>
    --       simp_all
    --       obtain ⟨is_hd_eq, is_tl_eq⟩ := instrs_eq
    --       subst is_hd_eq
    --       subst is_tl_eq

    --       have h := (instrs_empty_typing c' ts1 ts2_orig).mp instrs_ok_ts1_to_ts2

    --       sorry
    --   case cons hd tl =>

    --     sorry
    -- case refine_2 =>
    --   sorry
  case sub => sorry
  case frame => sorry
