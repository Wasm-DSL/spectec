import Mathlib.Tactic
import «typing_lemmas»
open functype list

/- ════════════════════════════════════════════════════════════════════════
   STAGE 0: the raw recursor. Two motives, one per type in the mutual
   group. This is the thing everything else in this file is built from.
   ════════════════════════════════════════════════════════════════════════ -/
#check @Instrs_ok.rec
-- Instrs_ok.rec : ∀ {motive_1 : ... → Instr_ok ... → Prop}
--                   {motive_2 : ... → Instrs_ok ... → Prop},
--   (empty case) → (instr case) → (seq case) → (sub case) → (frame case) →
--   ∀ {C is ft} (t : Instrs_ok C is ft), motive_2 C is ft t


/- ════════════════════════════════════════════════════════════════════════
   STAGE 1: the ORIGINAL approach. Trace THREE moments:
     (a) right before `induction` -- what instrs_eq/ft_eq/goal look like
     (b) immediately inside `case seq`, BEFORE simp_all -- the RAW ih,
         straight out of the recursor + the auto-inferred motive
     (c) immediately AFTER simp_all -- the ih you actually see
   ════════════════════════════════════════════════════════════════════════ -/
theorem stage1_original
  (c : context) (i : instr) (is : List instr) (ts1 ts3 : List valtype)
  :
  Instrs_ok c (i :: is) (ts1 f-> ts3)
  → ∃ ts2, Instr_ok c i (ts1 f-> ts2) ∧ Instrs_ok c is (ts2 f-> ts3)
  := by
  intros instrs_ok
  generalize instrs_eq : (i :: is) = instrs at instrs_ok
  generalize ft_eq : (ts1 f-> ts3) = ft at instrs_ok

  dbg_trace "=== (a) MOMENT BEFORE induction ==="
  trace_state

  induction instrs_ok using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  case seq c' i_list is_list ts1_orig ts3_orig ts2_orig
      instrs_ok_ts1_to_ts2 instrs_ok_ts2_to_ts3 wf_c' wf_all_i_list wf_all_is_list
      ih_i_list ih_is_list =>

    dbg_trace "=== (b) RAW ih, straight from recursor+motive, BEFORE simp_all ==="
    trace_state

    simp_all

    dbg_trace "=== (c) ih AFTER simp_all simplifies it using instrs_eq/ft_eq ==="
    trace_state
    sorry
  all_goals sorry


/- ════════════════════════════════════════════════════════════════════════
   STAGE 2: the FIXED approach. The theorem's OWN statement is already
   quantified over the recursion target's own head/tail (a, b), so the
   auto-inferred motive is properly general FROM THE START -- one trace,
   no "raw vs after-simp" distinction needed, because there's nothing to
   simplify away: the ih is already exactly what you need.
   ════════════════════════════════════════════════════════════════════════ -/
theorem stage2_fixed
  (c : context) :
  ∀ (instrs : List instr) (ft : functype), Instrs_ok c instrs ft →
    ∀ (a : instr) (b : List instr), instrs = a :: b →
      ∀ (t1' t3' : List valtype), ft = (t1' f-> t3') →
        ∃ ts2, Instr_ok c a (t1' f-> ts2) ∧ Instrs_ok c b (ts2 f-> t3')
  := by
  intro instrs ft h
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  <;> try trivial
  case seq C i_list is_list t1_lst t3_lst t2_lst h1 h2 wf_c' wf1 wf2 ih1 ih2 =>

    dbg_trace "=== STAGE 2: ih1/ih2 already general, no simp needed ==="
    trace_state
    sorry
  all_goals sorry
