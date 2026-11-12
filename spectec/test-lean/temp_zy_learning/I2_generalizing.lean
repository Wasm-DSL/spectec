import Mathlib.Tactic
set_option pp.fieldNotation false
/- ═══════════════════════════════════════════════════════════════════════
   LESSON I2: GENERALIZING -- what `induction` does with hypotheses that
   mention the thing you're inducting on, and why it matters so much.

   Real world: same PearStack. -/

inductive PearStack where
  | empty
  | onePear (rest : PearStack)

def pearCount : PearStack → Nat
  | .empty => 0
  | .onePear rest => pearCount rest + 1

/- ─── Problem 1: inducting on something that's not "bare" ───
   Suppose your goal is about `onePear s` for a FIXED, already-specific
   `s` -- not about an arbitrary PearStack. Try to induct directly: -/
theorem stuck_example (s : PearStack) :
    pearCount (.onePear s) = pearCount s + 1 := by
  induction s with
  | empty => rfl
  | onePear rest ih =>
    -- `ih` here is about `pearCount (.onePear rest) = pearCount rest + 1`
    -- -- i.e. it's ALREADY the theorem's own conclusion, recursively, for
    -- `rest`. That's fine for THIS particular goal (which is actually
    -- provable directly by `rfl` in every branch, since `pearCount`'s
    -- own definition IS this equation) -- but notice `s` here doesn't
    -- interact with anything external. The next example is where the
    -- real problem shows up.
    rfl

-- `apply` translations of the induction above -- see I3 for the general
-- recipe. Nothing else in context depends on `s`, so the "args" version
-- needs no `revert` at all, and the "bare" version needs only `revert s`
-- (to turn the goal into the Pi-shape `apply` can unify against).
theorem stuck_example_apply_args (s : PearStack) :
    pearCount (.onePear s) = pearCount s + 1 := by
  apply PearStack.rec
    (motive := fun s => pearCount (.onePear s) = pearCount s + 1)
    (t := s)
  · rfl
  · intro rest ih
    rfl

theorem stuck_example_apply_bare (s : PearStack) :
    pearCount (.onePear s) = pearCount s + 1 := by
  revert s
  apply PearStack.rec
  · rfl
  · intro rest ih
    rfl

/- ─── Problem 2: a hypothesis ELSEWHERE mentions the target ───
   This is the shape of the actual, real difficulty from the
   `instrs_seq_typing_inversion` saga earlier this session. Say you have
   an EXTRA fact tying some outer, fixed value to your induction target,
   and you want to induct on the target while KEEPING that connection
   available, case by case. -/
#check PearStack.rec
theorem with_extra_fact (fixed : PearStack) (n : Nat) (h : pearCount fixed = n) :
    n = 0 ∨ n > 0 := by
  /- If you `induction fixed` directly WITHOUT first dealing with `h`,
     Lean has a problem: `h`'s statement mentions `fixed`, the very thing
     about to be case-split. Lean's `induction` tactic actually handles
     this automatically for you -- it REVERTS any hypothesis depending on
     the target, does the induction, then re-introduces it per branch,
     freshly specialized. Watch: -/
  induction fixed with
  | empty =>
    -- Lean has automatically turned `h : pearCount fixed = n` into
    -- `h : pearCount PearStack.empty = n` for you, right here:
    trace_state
    left; simp [pearCount] at h; omega
  | onePear rest ih =>
    -- and here, `h : pearCount (.onePear rest) = n` -- STILL correctly
    -- connected, per-branch, without you writing a single `generalize`.
    trace_state
    right; simp [pearCount] at h; omega

-- `apply` translations. Since `h` depends on the target `fixed`,
-- `induction fixed`'s auto-revert has to be done by hand one way or
-- another for BOTH versions -- they differ only in whether that reverting
-- happens BEFORE `apply` (bare) or `h`'s statement gets folded into an
-- explicit motive and `h` itself is fed back in as one trailing goal (args).
theorem with_extra_fact_apply_args (fixed : PearStack) (n : Nat) (h : pearCount fixed = n) :
    n = 0 ∨ n > 0 := by
  apply PearStack.rec
    (motive := fun fixed => pearCount fixed = n → (n = 0 ∨ n > 0))
    (t := fixed)
  · intro h; left; simp [pearCount] at h; omega
  · intro rest ih h; right; simp [pearCount] at h; omega
  · exact h -- `h` was never reverted, so `apply` leaves this one extra goal.

theorem with_extra_fact_apply_bare (fixed : PearStack) (n : Nat) (h : pearCount fixed = n) :
    n = 0 ∨ n > 0 := by
  revert h      -- `h` depends on `fixed`, so RULE 2 says it goes first.
  revert fixed  -- NOW `fixed` is the outermost bound variable, matching
                -- `PearStack.rec`'s own trailing `(t : PearStack)`.
  apply PearStack.rec
  · intro h; left; simp [pearCount] at h; omega
  · intro rest ih h; right; simp [pearCount] at h; omega

/- So when DO you need `generalize` yourself? When the CONNECTION you
   care about isn't a plain hypothesis sitting in context already -- it's
   baked into the GOAL's own shape, or you deliberately want to name and
   inspect the equation Lean would otherwise handle silently. -/

theorem manual_generalize_needed (n : Nat) (fixed : PearStack) (hn : pearCount fixed = n) :
    pearCount fixed = n := by
  -- Trivial on its own, but let's do it the SAME way `induction using`
  -- constructs its ih's -- deliberately generalizing `fixed` and its
  -- functional relationship to `n` FIRST, then inducting, so you can see
  -- the mechanism explicitly rather than have `induction` do it for you.
  generalize eq1 : fixed = s at hn
  induction s with
  | empty =>
    trace_state  -- `eq1 : fixed = PearStack.empty` sits right there
    simp_all
  | onePear rest ih =>
    trace_state  -- `eq1 : fixed = PearStack.onePear rest`
    simp_all

-- `apply` translations. `eq1` and `hn` both mention `s`, so both need
-- threading through either way.
theorem manual_generalize_needed_apply_args
    (n : Nat) (fixed : PearStack) (hn : pearCount fixed = n) :
    pearCount fixed = n := by
  generalize eq1 : fixed = s at hn
  apply PearStack.rec
    (motive := fun s => fixed = s → pearCount s = n → pearCount s = n)
    (t := s)
  · intro eq1 hn; exact hn
  · intro rest ih eq1 hn; exact hn
  · exact eq1
  · exact hn

theorem manual_generalize_needed_apply_bare
    (n : Nat) (fixed : PearStack) (hn : pearCount fixed = n) :
    pearCount fixed = n := by
  generalize eq1 : fixed = s at hn
  revert hn
  revert eq1
  revert s
  apply PearStack.rec
  · intro eq1 hn; exact hn
  · intro rest ih eq1 hn; exact hn

/- ─── The REAL danger: generalizing something, then the CONCLUSION not
   depending on the recursion target at all ───
   This is the exact shape of the `instrs_seq_typing_inversion` problem.
   If your GOAL doesn't mention the target's own structure (only some
   OUTER fixed value tied to it via a `generalize`-produced equation),
   the `ih` you get in each branch stays tied to that OUTER value -- not
   genuinely general over the branch's own sub-piece. Watch this fail to
   be useful in the "cons"-like branch, on purpose: -/
theorem narrow_ih_demo (p : PearStack) :
    p = .onePear .empty → pearCount p = 1 := by
  intro hp
  -- generalize BOTH the hypothesis and the goal, so `p` is replaced
  -- everywhere (not just inside `hp`) -- otherwise the goal keeps
  -- talking about the un-generalized `p` and nothing lines up.
  generalize eq1 : p = s at hp ⊢
  induction s with
  | empty =>
    exact absurd hp.symm (by simp)
  | onePear rest ih =>
    -- `ih`'s TYPE mentions the OUTER `p`, not a freshly-quantified
    -- statement about `rest` in general. Print it:
    trace_state
    -- ih : p = PearStack.onePear rest → pearCount (PearStack.onePear rest) = 1
    -- Useful here ONLY because `p` still happens to be around and
    -- connected via `hp`/`eq1` -- but if `rest` were, say, TWO levels
    -- deep inside a bigger structure (as in the real `seq` case), this
    -- ih would be gated on `p` equaling something it almost never does.
    -- This is precisely I2's lesson, and precisely what Lesson I5 fixes
    -- by stating a properly GENERAL auxiliary goal before inducting.
    injection hp with rest_eq
    subst rest_eq
    rfl

-- `apply` translations. Same recipe: `eq1` and `hp` both mention `s`.
theorem narrow_ih_demo_apply_args (p : PearStack) :
    p = .onePear .empty → pearCount p = 1 := by
  intro hp
  generalize eq1 : p = s at hp ⊢
  apply PearStack.rec
    (motive := fun s => p = s → (s = .onePear .empty → pearCount s = 1))
    (t := s)
  · intro eq1 hp
    exact absurd hp.symm (by simp)
  · intro rest ih eq1 hp
    injection hp with rest_eq
    subst rest_eq
    rfl
  · exact eq1
  · exact hp

theorem narrow_ih_demo_apply_bare (p : PearStack) :
    p = .onePear .empty → pearCount p = 1 := by
  intro hp
  generalize eq1 : p = s at hp ⊢
  revert hp
  revert eq1
  revert s
  apply PearStack.rec
  · intro eq1 hp
    exact absurd hp.symm (by simp)
  · intro rest ih eq1 hp
    injection hp with rest_eq
    subst rest_eq
    rfl

/- ─── Making the stuckness genuine ───
   `narrow_ih_demo` above is unsatisfying: `ih` really is narrow (gated on
   `p = rest`), but the goal is small enough that the proof never needs
   `ih` at all -- it closes by `rfl` regardless. To see a case where the
   narrow `ih` actually blocks you, you need a shape where TWO
   independently-recursive sub-derivations get combined, so that neither
   sub-derivation's `ih`-gate lines up with the outer equation. That's
   what happened in the real `instrs_seq_typing_inversion` (see
   `typing_lemmas.lean`): its `Instrs_ok` has a "seq" constructor built
   from `Instrs_ok c i_list ft1` and `Instrs_ok c is_list ft2` joined by
   `i_list ++ is_list`. `PearStack.onePear` alone can't reproduce this --
   it has only ONE recursive argument, so there's only ever one shape to
   check. We add the one missing ingredient: a way to glue two
   `PearStack`s together, and a proof-relevant predicate built the same
   "single / combined" way `Instrs_ok`/`SeqOk` are: -/

def combine : PearStack → PearStack → PearStack
  | .empty, q => q
  | .onePear rest, q => .onePear (combine rest q)

inductive PearOk : PearStack → Prop where
  | empty : PearOk .empty
  | one : PearOk (.onePear .empty)
  | seq (a b : PearStack) : PearOk a → PearOk b → PearOk (combine a b)
#check PearOk.rec
/- GOAL: an inversion lemma -- given a proof that `onePear rest` is
   `PearOk`, recover a proof that `rest` itself is `PearOk`. This is the
   `instrs_seq_typing_inversion`-shaped claim: "peel one layer off a
   PROOF, not just off a plain value." It's true (see `general` below),
   but naive `generalize`-then-`induction`, I2-style, cannot prove it: -/
theorem narrow_ih_demo_stuck (rest : PearStack) :
    PearOk (.onePear rest) → PearOk rest := by
  intro h
  generalize eq1 : (PearStack.onePear rest) = s at h
  induction h with
  | empty => exact absurd eq1 (by simp)
  | one =>
    injection eq1 with rest_eq
    exact rest_eq ▸ .empty
  | seq a b ha hb iha ihb =>
    -- iha : PearStack.onePear rest = a → PearOk rest
    -- ihb : PearStack.onePear rest = b → PearOk rest
    -- eq1 : PearStack.onePear rest = combine a b
    -- Both ih's are gated on the OUTER `onePear rest` equaling one whole
    -- SIDE of the combine -- not on anything about `a`/`b`'s own shape.
    cases a with
    | empty =>
      -- combine .empty b = b, so eq1 : onePear rest = b -- `ihb` fires
      -- directly. Fine so far, same as `narrow_ih_demo`'s lucky case.
      simp only [combine] at eq1
      exact ihb eq1
    | onePear a' =>
      -- combine (.onePear a') b = .onePear (combine a' b), so injecting
      -- eq1 gives `rest = combine a' b` -- but `iha` demands
      -- `onePear rest = onePear a'`, i.e. `rest = a'`. That's a STRICTLY
      -- STRONGER fact than what we have (`rest = combine a' b`), true
      -- only in the special case `b = .empty`. In general (`b` nonempty)
      -- `iha` is simply inapplicable here -- genuinely stuck, not just
      -- unused:
      simp only [combine] at eq1
      sorry

-- `apply` translations -- same stuck point, same reason (see
-- `mechanics_walkthrough` in the APPENDIX below for the fully-worked-out
-- step trace of exactly this `_bare` derivation).
theorem narrow_ih_demo_stuck_apply_args (rest : PearStack) :
    PearOk (.onePear rest) → PearOk rest := by
  intro h
  generalize eq1 : (PearStack.onePear rest) = s at h
  apply PearOk.rec
    (motive := fun s _ => (PearStack.onePear rest) = s → PearOk rest)
    (t := h)
  · intro eq1
    exact absurd eq1 (by simp)
  · intro eq1
    injection eq1 with rest_eq
    exact rest_eq ▸ .empty
  · intro a b ha hb iha ihb eq1
    cases a with
    | empty =>
      simp only [combine] at eq1
      exact ihb eq1
    | onePear a' =>
      simp only [combine] at eq1
      sorry
  · exact eq1 -- `eq1` was never reverted, so this feeds it back in.

theorem narrow_ih_demo_stuck_apply_bare (rest : PearStack) :
    PearOk (.onePear rest) → PearOk rest := by
  intro h
  generalize eq1 : (PearStack.onePear rest) = s at h
  revert eq1
  revert h
  apply PearOk.rec
  · intro eq1
    exact absurd eq1 (by simp)
  · intro eq1
    injection eq1 with rest_eq
    exact rest_eq ▸ .empty
  · intro a b ha hb iha ihb eq1
    cases a with
    | empty =>
      simp only [combine] at eq1
      exact ihb eq1
    | onePear a' =>
      simp only [combine] at eq1
      sorry

/- ─── The actual fix, I5-style: generalize the GOAL, not just the target ───
   State the head/tail split as an explicit, universally-quantified
   conclusion BEFORE inducting, so `induction`'s auto-derived `ih`'s are
   about `a`/`b`'s own structure from the start (no `p`/`rest`-shaped gate
   baked in by a stray `generalize`-equation getting reverted). -/
theorem general (p : PearStack) (h : PearOk p) :
    ∀ rest, p = .onePear rest → PearOk rest := by
  induction h with
  | empty => intro rest hcontra; exact absurd hcontra (by simp)
  | one => intro rest hcontra; injection hcontra with rest_eq; exact rest_eq ▸ .empty
  | seq a b ha hb iha ihb =>
    intro rest heq
    cases a with
    | empty =>
      simp only [combine] at heq
      exact ihb rest heq
    | onePear a' =>
      simp only [combine] at heq
      injection heq with heq'
      -- `iha` is now properly general (`∀ rest, a = onePear rest → PearOk
      -- rest`), so plugging in `a'` and `rfl` genuinely works:
      have hA : PearOk a' := iha a' rfl
      exact heq' ▸ PearOk.seq a' b hA hb

-- `apply` translations. `general`'s own conclusion already IS the
-- properly general motive -- no other hypothesis needs threading, so
-- neither version needs a trailing bullet the way the stuck/narrow proofs
-- above did.
theorem general_apply_args (p : PearStack) (h : PearOk p) :
    ∀ rest, p = .onePear rest → PearOk rest := by
  apply PearOk.rec
    (motive := fun p _ => ∀ rest, p = .onePear rest → PearOk rest)
    (t := h)
  · intro rest hcontra; exact absurd hcontra (by simp)
  · intro rest hcontra; injection hcontra with rest_eq; exact rest_eq ▸ .empty
  · intro a b ha hb iha ihb rest heq
    cases a with
    | empty =>
      simp only [combine] at heq
      exact ihb rest heq
    | onePear a' =>
      simp only [combine] at heq
      injection heq with heq'
      have hA : PearOk a' := iha a' rfl
      exact heq' ▸ PearOk.seq a' b hA hb

theorem general_apply_bare (p : PearStack) (h : PearOk p) :
    ∀ rest, p = .onePear rest → PearOk rest := by
  revert h
  apply PearOk.rec
  · intro rest hcontra; exact absurd hcontra (by simp)
  · intro rest hcontra; injection hcontra with rest_eq; exact rest_eq ▸ .empty
  · intro a b ha hb iha ihb rest heq
    cases a with
    | empty =>
      simp only [combine] at heq
      exact ihb rest heq
    | onePear a' =>
      simp only [combine] at heq
      injection heq with heq'
      have hA : PearOk a' := iha a' rfl
      exact heq' ▸ PearOk.seq a' b hA hb

theorem narrow_ih_demo_fixed (rest : PearStack) :
    PearOk (.onePear rest) → PearOk rest :=
  fun h => general (.onePear rest) h rest rfl

theorem narrow_ih_demo_fixed2 (rest : PearStack) :
    PearOk (.onePear rest) → PearOk rest := by
    intro h
    have g := general
    have g' := g (PearStack.onePear rest) h rest
    simp at g'
    assumption

/- ─── A THIRD fix: the same idea, but as one keyword on the ORIGINAL
   proof instead of a separate lemma ───
   `rest` never depended on `h`/`s` at all, so nothing ever forced it to
   be reverted -- that's exactly why `iha`/`ihb` stayed narrow in
   `narrow_ih_demo_stuck`. `generalizing rest` reverts it anyway, so the
   motive becomes `fun s _ => ∀ rest, rest.onePear = s → PearOk rest`
   instead of the old `fun s _ => rest.onePear = s → PearOk rest` -- the
   exact same fix `general` makes by restating the goal, triggered here by
   one word on `induction` instead of a whole separate lemma. This is
   `narrow_ih_demo_stuck` with its `sorry` filled in, nothing else
   touched, plus `generalizing rest`: -/
theorem narrow_ih_demo_stuck_via_generalizing (rest : PearStack) :
    PearOk (.onePear rest) → PearOk rest := by
  intro h
  generalize eq1 : (PearStack.onePear rest) = s at h
  induction h generalizing rest with
  | empty => exact absurd eq1 (by simp)
  | one =>
    injection eq1 with rest_eq
    exact rest_eq ▸ .empty
  | seq a b ha hb iha ihb =>
    -- `iha`/`ihb` are now `∀ (rest : PearStack), rest.onePear = _ → PearOk
    -- rest` -- properly general, word for word what `general`'s own
    -- `iha`/`ihb` were. The one price: they're no longer bare
    -- implications, so `ihb eq1` (which worked in the stuck version)
    -- doesn't typecheck anymore -- the witness has to be supplied first.
    cases a with
    | empty =>
      simp only [combine] at eq1
      exact ihb rest eq1
    | onePear a' =>
      simp only [combine] at eq1
      injection eq1 with eq1'
      have hA : PearOk a' := iha a' rfl
      exact eq1' ▸ .seq a' b hA hb


/- ═══════════════════════════════════════════════════════════════════════
   APPENDIX: what `induction h` above is actually doing, one mechanical
   step at a time.

   You just watched `induction h` get stuck. Before fixing that (in
   `general`, right after this appendix), it's worth seeing exactly what
   that one tactic call does under the hood -- the fix only makes sense
   once you've seen precisely what a "motive" is and how it gets built.

   Two rules govern every `induction`/`cases` call. Both are illustrated,
   with the real Lean state at every step, below.

   RULE 1 -- the thing you induct on must be a bare local variable, not a
   compound expression. `PearOk (.onePear rest)` is compound (`PearOk`
   applied to `.onePear rest`, not to a plain variable) -- you cannot
   induct on a hypothesis of this type directly. `generalize` manufactures
   a bare variable to induct on instead.

   RULE 2 -- once the target IS a bare variable (say `s`, in `h : PearOk
   s`), every OTHER hypothesis whose type mentions `s` (or mentions `h`
   itself) must be reverted into the goal before the case split happens.
   Since the local context can only ever refer backward to earlier
   entries, when several things need reverting they go in the reverse of
   the order they were introduced -- you can't remove an earlier entry
   while a later one still refers to it, same reason you can only pop a
   stack from the top.

   WHY (the intuition behind both rules): before induction, `s` is one
   single, unspecified `PearStack`. Induction's whole move is to stop
   treating it as one thing and instead handle each of the finitely many
   ways it could have been built -- at which point `s` isn't one thing
   anymore, it's three different concrete things, one per case. Anything
   stated about the OLD, single, unspecified `s` can't just sit there
   unchanged -- there's no single `s` left for it to be about. The only way
   to guarantee it gets correctly re-stated, once per case, with that
   case's own concrete value substituted in, is to fold it into the very
   goal being proved BEFORE the split, so that whatever operation
   specializes the goal per case also specializes it. -/

theorem mechanics_walkthrough (rest : PearStack) :
    PearOk (.onePear rest) → PearOk rest := by
  intro h
  -- STATE 0. `h`'s type is `PearOk rest.onePear` -- compound, not a bare
  -- variable. RULE 1 says we cannot induct on `h` yet.
  trace_state
  /- rest : PearStack
     h : PearOk rest.onePear
     ⊢ PearOk rest -/

  -- Apply RULE 1: manufacture a bare variable `s` standing for the
  -- compound index, recording the fact we'd otherwise lose as `eq1`.
  generalize eq1 : (PearStack.onePear rest) = s at h

  -- STATE 1. `h : PearOk s` now has a bare-variable index -- RULE 1 is
  -- satisfied. Check RULE 2: does anything (other than `h`) mention `s`?
  -- `eq1 : rest.onePear = s` does. The goal `PearOk rest` mentions neither
  -- `s` nor `h` -- leave it alone.
  trace_state
  /- rest s : PearStack
     eq1 : rest.onePear = s
     h : PearOk s
     ⊢ PearOk rest -/

  -- Apply RULE 2 to the one offender:
  revert eq1

  -- STATE 2. Re-check RULE 2 on what's left: does anything besides `h`
  -- mention `s` now? No. The only thing left mentioning `s` is `h` itself
  -- -- the target of the induction.
  trace_state
  /- rest s : PearStack
     h : PearOk s
     ⊢ rest.onePear = s → PearOk rest -/

  -- `h` itself must ALSO leave the context: `PearOk.rec`'s conclusion
  -- proves its motive for *every* possible proof, not one fixed witness,
  -- so `h` has to become a universally-quantified variable in the goal.
  revert h

  -- STATE 3. This exact goal is what `apply PearOk.rec` gets matched
  -- against, a few lines below.
  trace_state
  /- rest s : PearStack
     ⊢ PearOk s → rest.onePear = s → PearOk rest -/

  /- ── The motive, derived, not chosen ──
     A motive is obtained by taking the STATE 3 goal and abstracting it
     over exactly the two things about to vary: `s` (renamed to a fresh
     bound name `a`) and `h` (renamed `t`, even though the body below
     never actually uses it):

       myMotive := fun (a : PearStack) (t : PearOk a) =>
                     rest.onePear = a → PearOk rest

     Two checks (see the two `example`s right after this theorem) confirm
     this is exactly the right function -- both are `rfl`, i.e. true by
     computation alone:
       1. plugging the ORIGINAL `s`, `h` back into `myMotive` reproduces
          STATE 1's un-reverted goal exactly;
       2. STATE 3's goal is exactly "for every proof `h`, `myMotive s h`".

     ── PearOk.rec, desugared, and what `a✝` means ──
     Hovering `PearOk.rec` shows it in "declaration signature" style, with
     named parameters:

       PearOk.rec {motive : (a : PearStack) → PearOk a → Prop}
         (empty : motive PearStack.empty PearOk.empty)
         (one : motive (PearStack.onePear PearStack.empty) PearOk.one)
         (seq : ∀ (a b : PearStack) (a_1 : PearOk a) (a_2 : PearOk b),
                  motive a a_1 → motive b a_2 → motive (combine a b) (PearOk.seq a b a_1 a_2))
         {a✝ : PearStack} (t : PearOk a✝) : motive a✝ t

     `#check PearOk.rec` (no `@`) prints exactly that. `#check @PearOk.rec`
     (with `@`) prints the fully desugared ∀/→ chain instead -- same type,
     just every argument folded into one Pi-chain rather than split into a
     named-parameter list (see the two `#check`s below the examples):

       ∀ {motive : (a : PearStack) → PearOk a → Prop},
         motive PearStack.empty PearOk.empty →
         motive (PearStack.onePear PearStack.empty) PearOk.one →
         (∀ (a b : PearStack) (a_1 : PearOk a) (a_2 : PearOk b),
            motive a a_1 → motive b a_2 → motive (combine a b) (PearOk.seq a b a_1 a_2)) →
         ∀ {a✝ : PearStack} (t : PearOk a✝), motive a✝ t

     `a✝` is Lean's name for "the general `PearStack` index" -- the
     ORIGINAL declaration `inductive PearOk : PearStack → Prop` never gave
     this position a name (you wrote the index's TYPE, not a name for it),
     so the compiler invents one when auto-generating `.rec`, and marks it
     with `✝` to say "compiler-invented, not something you can type
     yourself" -- it's a display-only placeholder, nothing more.

     ── `apply PearOk.rec`, one binder at a time ──
     `apply e` peels binders off the FRONT of `e`'s type, one at a time,
     replacing each with a blank (a metavariable) to be filled in later,
     until what's left over can be lined up against the goal. Whichever
     blanks get pinned down BY that lining-up are done; whichever don't
     become your new goals, in the order they were introduced.

     Applied to `PearOk.rec`'s desugared type against the STATE 3 goal:

     Step 1. Peel `motive`. Introduce blank `?m : (a : PearStack) →
       PearOk a → Prop`. Unknown so far.
     Step 2. Peel `empty`. Introduce blank `?empty : ?m PearStack.empty
       PearOk.empty`. Mentions `?m`, so still unknown.
     Step 3. Peel `one`. Same idea: `?one : ?m (PearStack.onePear
       PearStack.empty) PearOk.one`. Still unknown.
     Step 4. Peel `seq`. `?seq : (the big ∀ a b a_1 a_2 type, with `?m` in
       place of `motive`)`. Still unknown.
     Step 5. Reach the tail, `∀ {a✝} (t : PearOk a✝), ?m a✝ t`, and line it
       up against the goal `∀ (h : PearOk s), rest.onePear = s → PearOk
       rest`:
         • match the bound variable's type on each side: `PearOk a✝`
           (with `a✝` itself a blank `?a`, so `PearOk ?a`) against
           `PearOk s` -- forces `?a := s`. FIRST THING PINNED DOWN.
         • match everything after the arrow, now that `?a := s` is known:
           left side (as a function of `t`) is `?m s t`; right side is
           `rest.onePear = s → PearOk rest`, which doesn't mention `t` at
           all. For `?m` to be a genuine function usable for every proof
           `t` (not secretly tied to this one `s`), it has to be
           `?m := fun a _ => rest.onePear = a → PearOk rest` -- abstracting
           `s` itself into a fresh name `a`. SECOND THING PINNED DOWN.
     Step 6. Go back and finish `?empty`, `?one`, `?seq` now that `?m` is
       known -- plug it in and beta-reduce. Nothing supplied a VALUE for
       these three, only their TYPES got determined -- a blank with a
       known type but no value is exactly what a goal is. These three
       become your leftover goals, empty/one/seq, in that order.

     Watch the predicted types show up exactly, below: -/
  apply PearOk.rec
  case empty =>
    trace_state
    /- rest s : PearStack
       ⊢ rest.onePear = PearStack.empty → PearOk rest -/
    sorry
  case one =>
    trace_state
    /- rest s : PearStack
       ⊢ rest.onePear = PearStack.empty.onePear → PearOk rest -/
    sorry
  case seq =>
    trace_state
    /- rest s : PearStack
       ⊢ ∀ (a b : PearStack), PearOk a → PearOk b →
           (rest.onePear = a → PearOk rest) → (rest.onePear = b → PearOk rest) →
           rest.onePear = combine a b → PearOk rest -/
    sorry

-- Check 1: plugging the ORIGINAL s, h back into the abstracted motive
-- reproduces STATE 1's un-reverted goal exactly.
example (rest s : PearStack) (h : PearOk s) :
    (fun (a : PearStack) (_t : PearOk a) => rest.onePear = a → PearOk rest) s h
      = (rest.onePear = s → PearOk rest) := rfl

-- Check 2: STATE 3's goal is exactly "for every proof h, myMotive s h".
example (rest s : PearStack) :
    (PearOk s → rest.onePear = s → PearOk rest)
      = (∀ h : PearOk s,
           (fun (a : PearStack) (_t : PearOk a) => rest.onePear = a → PearOk rest) s h) := rfl

-- Named-parameter signature style (what hovering `PearOk.rec` shows):
#check PearOk.rec
-- Fully desugared ∀/→ chain (same type, different rendering):
#check @PearOk.rec

/- ─── Under the hood, for every theorem above ───
   Every `induction ... with | ctor args => tac` block in this file
   compiles to a `PearStack.rec` (or the compiler's `brecOn`-based
   cousin) application: one argument per constructor, each built from
   the tactic block for that case, with the `ih` names you wrote slotted
   into exactly the ih POSITIONS R3 identified in the raw recursor type.
   `generalize ... at h ⊢` never changes THAT fact -- it only changes
   WHAT GOAL each of those tactic-block arguments has to prove, by
   altering what `h`/⊢ look like at the moment the recursor gets built.
   Confirm directly: -/
set_option pp.proofs true in
#print with_extra_fact

/- ═══════════════════════════════════════════════════════════════════════
   ONE MORE CASE: `induction ... generalizing`, the flavor this file
   hasn't shown yet.

   Every stuck `ih` above was stuck because some EXISTING hypothesis
   (`hp`, `eq1`, `h`) mentioned the target and got dragged along with a
   too-narrow connection to it. `generalizing` isn't for that -- `induction`
   already reverts anything that mentions the target FOR FREE, with no
   `generalizing` needed (see `with_extra_fact` above). `generalizing` is
   for the opposite situation: a variable that does NOT depend on the
   target at all, so nothing forces it to be reverted, but the RECURSIVE
   CALL needs the `ih` at a DIFFERENT value of it than the one you started
   with. `pearCount` can't show this -- it never threads an extra argument
   through its own recursion. An accumulator-style version does: -/

def pearCountAcc : PearStack → Nat → Nat
  | .empty, acc => acc
  | .onePear rest, acc => pearCountAcc rest (acc + 1)  -- `acc` CHANGES here

-- WITHOUT generalizing: `acc` stays fixed in `ih`, and the `onePear` step
-- needs it at `acc + 1` instead.
theorem acc_stuck (s : PearStack) (acc : Nat) :
    pearCountAcc s acc = pearCount s + acc := by
  induction s with
  | empty => simp [pearCountAcc, pearCount]
  | onePear rest ih =>
    -- ih : pearCountAcc rest acc = pearCount rest + acc -- fixed at THIS acc
    trace_state
    show pearCountAcc rest (acc + 1) = pearCount rest + 1 + acc
    sorry -- `ih` only talks about `acc`; the goal needs it at `acc + 1`.

-- WITH generalizing: `acc` is reverted before the split, so `ih` becomes
-- `∀ acc, ...` -- usable at whatever value each recursive call needs.
theorem acc_fixed (s : PearStack) (acc : Nat) :
    pearCountAcc s acc = pearCount s + acc := by
  induction s generalizing acc with
  | empty => simp [pearCountAcc, pearCount]
  | onePear rest ih =>
    -- ih : ∀ (acc : Nat), pearCountAcc rest acc = pearCount rest + acc
    trace_state
    show pearCountAcc rest (acc + 1) = pearCount rest + 1 + acc
    rw [ih]
    omega

-- Since `induction ... generalizing y` is just sugar for `revert y`
-- before the split (see the `generalizeVars`/`evalInductionCore` trace
-- from earlier this session), this is identical to writing the revert
-- yourself:
theorem acc_fixed_by_hand (s : PearStack) (acc : Nat) :
    pearCountAcc s acc = pearCount s + acc := by
  revert acc
  induction s with
  | empty => intro acc; simp [pearCountAcc, pearCount]
  | onePear rest ih =>
    intro acc
    show pearCountAcc rest (acc + 1) = pearCount rest + 1 + acc
    rw [ih]
    omega
