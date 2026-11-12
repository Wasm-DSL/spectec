import «wasm2.0»

set_option linter.unusedVariables false

/- ═══════════════════════════════════════════════════════════════════════
   PROGRESS EXPLAINER: `t_progress_e` is ONE application of the mutual
   recursor `Instrs_ok2.rec`. What that recursor is, how each argument
   turns its type into the goal, why the motives look the way they do, and
   how the same proof reads with the `induction` tactic.

   Real world: `TLC.t_progress_e` in
   spectec/src/test-lean-claude/TypeProgress.lean:7837 (Rocq: type_progress.v:5512).
   Every toy lesson in this folder shows up here at full size: R4's indices,
   R5's shared mutual recursor, I3's "induction computes the main motive from
   the goal", I4's "you supply the OTHER motives", I5's "make the goal general
   BEFORE inducting".

   HOW TO RUN: just open this file. It belongs to the `test-lean` Lake project
   (the nearest `lean-toolchain` above it is spectec/test-lean/), so
   `import «wasm2.0»` is test-lean's own, already-built spec. That spec is
   older than test-lean-claude's, but its `mutual Instr_ok2 / Instrs_ok2 /
   Expr_ok2` block is byte-for-byte identical (checked with `diff`), and that
   block is all this file is about.

   WHAT IS COPIED VERBATIM from spectec/src/test-lean-claude/:
     * the helpers `mkFunctype` (Subtyping.lean:33), `upd_label` .. `upd_local_label_return`
       (TypingLemmas.lean:44 to :57), and `is_const` .. `not_lf_return`
       (TypeProgress.lean:114 to :551);
     * the three motives `t_progress_e_P` / `_P0` / `_P1`
       (TypeProgress.lean:7246 / :7265 / :7285);
     * the STATEMENTS of the 12 case lemmas `t_progress_e_<case>`
       (TypeProgress.lean, from `t_progress_e_plain` at :7301 to `t_progress_e_mk_Expr_ok2`
       at :7798). Their PROOFS are `sorry` here: this
       project can't import TypeProgress, and only the statements (the
       types) matter for how the pieces fit. All 12 are fully proved in
       TypeProgress.lean.

   HOW CLAIMS ARE CHECKED. Every claim is backed by Lean, not just a comment:
     * `example : <claim> := <proof>`, and `have h : <type> := <proof>`, only
       compile if the claim holds;
     * `#guard_msgs in <command>` runs the command and checks that its
       messages -- an output, a goal printed by `trace_state`, an error --
       are EXACTLY the doc comment written above it. An expected error is
       therefore a PASSING check, and if anything changes, the line turns red;
     * `fail_if_success tac` passes only if `tac` FAILS;
     * `with_reducible exact e` is `exact e` with unfolding of ordinary
       definitions switched off. It only succeeds if the type of `e` already
       IS the goal (up to renaming bound variables), so it separates "fits as
       is" from "fits after unfolding a definition".
   The only warnings should be the 12 `declaration uses 'sorry'` of Part 4.
   The unguarded `#check` / `#print` lines are there for you to hover.

   CONTENTS
     Part 0  copied definitions (+ a few printing helpers)
     Part 1  recursors in one screen (`Nat.rec`)
     Part 2  three things that make `Instrs_ok2.rec` look scary
     Part 3  anatomy of `Instrs_ok2.rec`
     Part 4  the 12 case lemmas ARE the 12 minor premises
     Part 5  `t_progress_e`, one argument at a time
     Part 6  the same proof with tactics: `refine`, then `induction`
     Part 7  why these motives? (the intuition)
     Part 8  cheat sheet: recursor term ↔ `induction`
-/

namespace TLC

/- ═══════════════════════════════════════════════════════════════════════
   Part 0. COPIED DEFINITIONS (verbatim)

   What the helpers mean:
     * `mkFunctype t1 t2` is Rocq's `t1 :-> t2`, the instruction type t1 → t2;
     * `upd_local_label_return C locs labs ret` is `C` with its LOCALS, LABELS
       and RETURN fields overwritten;
     * `terminal_form es`: `es` is all values, or is exactly `[TRAP]`;
     * `not_lf_br es` / `not_lf_return es`: `es` is NOT "some values, then a
       BR / RETURN, then anything", i.e. no jump is about to escape. -/

def mkFunctype (t1 t2 : List valtype) : functype := functype.mk_functype (.mk_list t1) (.mk_list t2)

def upd_label (C : context) (labs : List resulttype) : context := { C with LABELS := labs }

def upd_local (C : context) (locs : List valtype) : context := { C with LOCALS := locs }

def upd_return (C : context) (ret : Option resulttype) : context := { C with RETURN := ret }

def upd_local_label_return (C : context) (loc : List valtype) (lab : List resulttype) (ret : Option resulttype) : context :=
  upd_return (upd_label (upd_local C loc) lab) ret

def is_const (e : admininstr) : Bool :=
  match e with
  | .CONST _ _ => true
  | .VCONST _ _ => true
  | .REF_NULL _ => true
  | .REF_FUNC_ADDR _ => true
  | .REF_HOST_ADDR _ => true
  | _ => false

def const_list (es : List admininstr) : Bool := es.all is_const

def terminal_form (es : List admininstr) : Prop :=
  const_list es = true ∨ es = [admininstr.TRAP]

def typeof (v : val) : valtype :=
  match v with
  | .CONST t _ => valtype_numtype t
  | .VCONST t _ => valtype_vectype t
  | .REF_NULL t => valtype_reftype t
  | .REF_FUNC_ADDR _ => valtype.FUNCREF
  | .REF_HOST_ADDR _ => valtype.EXTERNREF

def not_lf_br (ais : List admininstr) : Prop :=
  ∀ (vals : List val) (l : labelidx) (ais' : List admininstr),
    ais ≠ ((List.map admininstr_val vals) ++ ([admininstr.BR l] ++ ais'))

def not_lf_return (ais : List admininstr) : Prop :=
  ∀ (vals : List val) (ais' : List admininstr),
    ais ≠ ((List.map admininstr_val vals) ++ ([admininstr.RETURN] ++ ais'))

/- The three motives. For now, read them only for their SHAPE (Part 7
   explains every line). Each one
     * takes the store `s` FIRST, so that `t_progress_e_P s` has exactly the
       type the recursor wants for `motive_1` (Part 2.2);
     * then takes the recursor's indices: the context, the instruction(s),
       the type;
     * then takes the typing derivation as `_`, and ignores it (Part 2.1);
     * and says "for all <the things that vary between uses>,
       <hypotheses> → the configuration is terminal or can step".
   `t_progress_e_P0` is for sequences (`Instrs_ok2`), and is the theorem
   itself; `t_progress_e_P` is for one instruction (`Instr_ok2`);
   `t_progress_e_P1` is for a frame body (`Expr_ok2`). -/

def t_progress_e_P (s : store) (C : context) (ai : admininstr) (ft : functype) (_ : Instr_ok2 s C ai ft) : Prop :=
  ∀ (f : frame) (framemoduleC : context) (vals : List val) (vt1 vt2 : List valtype)
    (lab : List resulttype) (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ [ai])) →
    Forall (fun e => wf_val e) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br [ai] →
    not_lf_return [ai] →
    terminal_form (List.map admininstr_val vals ++ [ai]) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ [ai]))
          (config.mk_config (state.mk_state s' f') ais')

def t_progress_e_P0 (s : store) (C : context) (ais : List admininstr) (ft : functype) (_ : Instrs_ok2 s C ais ft) : Prop :=
  ∀ (f : frame) (framemoduleC : context) (vals : List val) (vt1 vt2 : List valtype)
    (lab : List resulttype) (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais)) →
    Forall (fun e => wf_val e) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form (List.map admininstr_val vals ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais))
          (config.mk_config (state.mk_state s' f') ais')

def t_progress_e_P1 (s : store) (C : context) (ais : List admininstr) (rt : resulttype) (_ : Expr_ok2 s C ais rt) : Prop :=
  ∀ (f : frame) (framemoduleC : context) (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) ais) →
    C = upd_return framemoduleC ret →
    Frame_ok s f framemoduleC →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    (const_list ais = true ∧ ais.length = (proj_list_0 valtype rt).length) ∨
    ais = [admininstr.TRAP] ∨
    ∃ (s' : store) (f' : frame) (ais' : List admininstr),
      Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais')

/- ─── Printing helpers (skip on a first read) ───
   Small `MetaM` programs that print pieces of a recursor's type, so the
   `#guard_msgs` checks below can pin them. The recursor names the store
   parameter and the indices with anonymous `a✝`s; `recType` renames them
   for printing (it changes nothing else). -/

open Lean Meta in
/-- Rename the leading `∀` binders of `e` (`none` = keep the name). Only for printing. -/
def renameBinders : Expr → List (Option Name) → Expr
  | .forallE n d b bi, m :: ms => .forallE (m.getD n) d (renameBinders b ms) bi
  | e, _ => e

open Lean Meta in
/-- The type of `rec`, with the store called `s` and the three indices called `idx`. -/
def recType (rec : Name) (idx : List Name) : MetaM Expr := do
  let ty := (← getConstInfo rec).type
  return renameBinders ty (some `s :: List.replicate 15 none ++ idx.map some)

open Lean Meta in
/-- Print the type of the minor premise called `minor` in the recursor `rec`. -/
def showMinor (rec minor : Name) : MetaM Unit := do
  forallTelescope (← recType rec [`C, `ais, `ft]) fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName == minor then
        IO.println s!"({minor} : {← ppExpr d.type})"

open Lean Meta in
/-- Check that the three sibling recursors share their first 16 binders, then print the rest. -/
def siblingRecursors : MetaM Unit := do
  let recs := [(``Instr_ok2.rec, [`C, `ai, `ft]), (``Instrs_ok2.rec, [`C, `ais, `ft]),
    (``Expr_ok2.rec, [`C, `e, `rt])]
  let first16 (e : Expr) : Array Expr := Id.run do
    let mut acc := #[]
    let mut t := e
    for _ in [0:16] do
      if let .forallE _ d b _ := t then
        acc := acc.push d
        t := b
    return acc
  let tys ← recs.mapM fun (r, _) => do return (← getConstInfo r).type
  let shared := tys.all (fun t => first16 t == first16 tys.head!)
  IO.println s!"first 16 binders (store, 3 motives, 12 minors) identical in all three: {shared}"
  for (r, idx) in recs do
    forallTelescope (← recType r idx) fun xs body => do
      let rest ← (xs.extract 16 xs.size).mapM fun x => do
        let d ← x.fvarId!.getDecl
        if d.binderInfo.isImplicit then return s!"\{{d.userName}}"
        else return s!"({d.userName} : {← ppExpr d.type})"
      IO.println s!"{r} : <those 16> → ∀ {" ".intercalate rest.toList}, {← ppExpr body}"

open Lean Meta in
/-- For each of the 12 minor premises: the motive it concludes, and the motives of its IHs. -/
def minorTable (rec : Name) : MetaM Unit := do
  forallTelescope (← getConstInfo rec).type fun xs _ => do
    let motives := xs.extract 1 4
    let motiveOf (e : Expr) : MetaM (Option String) := do
      if motives.contains e.getAppFn then
        return some (toString (← e.getAppFn.fvarId!.getUserName))
      return none
    for x in xs.extract 4 16 do
      let d ← x.fvarId!.getDecl
      forallTelescope d.type fun ys concl => do
        let ihs ← ys.filterMapM fun y => do motiveOf (← inferType y)
        let name := toString d.userName
        let ihStr := if ihs.isEmpty then "none" else ", ".intercalate ihs.toList
        IO.println s!"{name.pushn ' ' (17 - name.length)} concludes {(← motiveOf concl).getD "?"};  IHs: {ihStr}"

open Lean Meta in
/-- `Instrs_ok2.rec s (t_progress_e_P s) (t_progress_e_P0 s) (t_progress_e_P1 s)`, built by hand. -/
def recWithMotives (s : Expr) : Expr :=
  mkAppN (mkConst ``Instrs_ok2.rec) #[s, mkApp (mkConst ``t_progress_e_P) s,
    mkApp (mkConst ``t_progress_e_P0) s, mkApp (mkConst ``t_progress_e_P1) s]

open Lean Meta in
/-- Print the minor premise `minor` of the recursor AFTER the three motives are plugged in. -/
def showMinorAfterMotives (minor : Name) : MetaM Unit := do
  withLocalDeclD `s (mkConst ``store) fun s => do
    forallTelescope (← inferType (recWithMotives s)) fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if d.userName == minor then
          IO.println s!"({minor} : {← ppExpr d.type})"

open Lean Meta in
/-- Plug in the motives, then feed the 12 case lemmas one by one. Before each one, compare the
    type the recursor expects with the lemma's type. `==` on `Expr` is equality up to renaming
    bound variables: no unfolding of anything. -/
def checkMinors : MetaM Unit := do
  let cases : List (Name × Name) :=
    -- single backticks: the lemmas are only declared later, in Part 4
    [(`plain, `TLC.t_progress_e_plain), (`label, `TLC.t_progress_e_label),
     (`Instr_ok2_frame, `TLC.t_progress_e_Instr_ok2_frame), (`call_addr, `TLC.t_progress_e_call_addr),
     (`ref, `TLC.t_progress_e_ref), (`trap, `TLC.t_progress_e_trap), (`empty, `TLC.t_progress_e_empty),
     (`instr, `TLC.t_progress_e_instr), (`seq, `TLC.t_progress_e_seq), (`sub, `TLC.t_progress_e_sub),
     (`Instrs_ok2_frame, `TLC.t_progress_e_Instrs_ok2_frame), (`mk_Expr_ok2, `TLC.t_progress_e_mk_Expr_ok2)]
  withLocalDeclD `s (mkConst ``store) fun s => do
    let mut acc := recWithMotives s
    for (minor, lem) in cases do
      let .forallE n expected _ _ ← inferType acc | throwError "not a ∀"
      let given ← inferType (mkApp (mkConst lem) s)
      let name := toString n
      IO.println s!"{name.pushn ' ' (17 - name.length)} expects exactly the type of `{lem} s`: {expected == given}"
      acc := mkApp acc (mkApp (mkConst lem) s)
    IO.println s!"left after the 12 minors: {← ppExpr (← inferType acc)}"

open Lean Meta in
/-- β-reduce the proof term of `decl` and show the recursor application inside it. -/
def showRecApp (decl : Name) : MetaM Unit := do
  let .thmInfo tv ← getConstInfo decl | throwError "not a theorem"
  lambdaTelescope tv.value fun xs body => do
    IO.println s!"head before β-reduction: {← ppExpr body.getAppFn}"
    let b := body.headBeta
    IO.println s!"head after β-reduction:  {← ppExpr b.getAppFn}, applied to {b.getAppNumArgs} arguments"
    IO.println s!"motive_1 := {← ppExpr b.getAppArgs[1]!}"
    IO.println s!"motive_3 := {← ppExpr b.getAppArgs[3]!}"
    let m2 := b.getAppArgs[2]!
    let p0 := mkApp (mkConst ``t_progress_e_P0) xs[0]!
    let .defnInfo dv ← getConstInfo ``t_progress_e_P0 | throwError "?"
    IO.println s!"motive_2 is literally `t_progress_e_P0 s`: {m2 == p0}"
    IO.println s!"motive_2 is the body of `t_progress_e_P0`, unfolded: {m2 == (mkApp dv.value xs[0]!).headBeta}"
    IO.println s!"motive_2 is definitionally equal to `t_progress_e_P0 s`: {← isDefEq m2 p0}"

open Lean in
/-- Lean's own record of how many parameters and indices an inductive has. -/
def paramsAndIndices (names : List Name) : CoreM Unit := do
  for nm in names do
    let some (.inductInfo i) := (← getEnv).find? nm | throwError "{nm} is not an inductive"
    IO.println s!"{nm}: {i.numParams} parameter(s), {i.numIndices} index(es)"

/- ═══════════════════════════════════════════════════════════════════════
   Part 1. RECURSORS IN ONE SCREEN (recap of R1-R3, I1, I3)

   Every inductive type `T` comes with a recursor `T.rec`. Read its type as:
   "to get `motive t` for EVERY `t : T`, give me one proof per constructor".
     * MOTIVE: what you want for each `t`, as a function of `t`;
     * MINOR PREMISES: one per constructor, i.e. the cases. A minor premise
       also gets an induction hypothesis (IH) -- "the motive holds there" --
       for each argument of the constructor that is itself a `T`;
     * MAJOR PREMISE: the `t : T` you are doing induction on;
     * RESULT: `motive t`. -/

/--
info: @Nat.rec : {motive : Nat → Sort u_1} → motive Nat.zero → ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
-/
#guard_msgs in
#check @Nat.rec

-- The recursor used directly: the motive, one minor premise per constructor, the major premise.
theorem zero_add_rec (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun n => 0 + n = n)
    rfl                                  -- minor premise for `zero`:  motive 0
    (fun n ih => congrArg Nat.succ ih)   -- minor premise for `succ`:  ∀ n, motive n → motive (n + 1)
    n                                    -- major premise

-- The same proof with `induction`: it COMPUTES the motive from the goal (I3), and every minor
-- premise becomes a goal that you fill in with `| constructor args => tactics`.
theorem zero_add_ind (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

/- Intuition: a recursor is a FOLD over the tree of constructors. It computes
   ("ι-reduces", scratch_iota_examples.lean) like this: -/
example (z : Nat) (st : Nat → Nat → Nat) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) z st (n + 1) = st n (Nat.rec (motive := fun _ => Nat) z st n) :=
  rfl
/- So the IH that a minor premise receives is "what the recursion produced for
   that child", and that is why assuming it is legitimate. Everything below is
   this same picture, with a bigger tree. -/

/- ═══════════════════════════════════════════════════════════════════════
   Part 2. THREE THINGS THAT MAKE `Instrs_ok2.rec` LOOK SCARY

   ─── 2.1 It is an inductive PREDICATE (R4) ───
   A "value" of `Instrs_ok2 s C ais ft` is a typing DERIVATION: a tree whose
   nodes are constructors (`empty`, `instr`, `seq`, `sub`, `Instrs_ok2_frame`).
   Induction on `hadmin : Instrs_ok2 s C ais ft` is a fold over that tree.

   Constructors conclude at SPECIFIC indices -- `empty` at `[]`, `seq` at
   `admininstr_1_lst ++ admininstr_2_lst`, `sub` at the type it subsumes to -- so the
   motive must be a FUNCTION of the indices, so that it can be asked about
   each of them:
       motive_2 : (C : context) → (ais : List admininstr) → (ft : functype)
                  → Instrs_ok2 s C ais ft → Prop
   Its last argument is the derivation itself: Lean's `.rec` always passes it
   ("dependent elimination"). We prove a `Prop` and never care WHICH
   derivation we have, so all three motive definitions take it as `_`.

   ─── 2.2 The store `s` is a PARAMETER, not an index ───
   The declaration says
       inductive Instrs_ok2 : store → context → List admininstr → functype → Prop
   with all four after the colon, so syntactically all four are indices. But
   every constructor, and every premise of every constructor, uses the SAME
   `s`, so Lean promotes it to a parameter (option `inductive.autoPromoteIndices`,
   on by default). `C` can't be promoted: `label` types its body under
   `{LABELS := ..} ++ C`, and `Instr_ok2_frame` its body under `{RETURN := ..} ++ C'`.
   Watch the promotion on a toy, then read Lean's own record: -/

inductive Reach : Nat → Nat → Prop where   -- "n is reachable from k in steps of 2"
  | refl (k : Nat) : Reach k k
  | step (k n : Nat) : Reach k n → Reach k (n + 2)

set_option inductive.autoPromoteIndices false in
inductive Reach' : Nat → Nat → Prop where
  | refl (k : Nat) : Reach' k k
  | step (k n : Nat) : Reach' k n → Reach' k (n + 2)

/--
info: TLC.Reach: 1 parameter(s), 1 index(es)
TLC.Reach': 0 parameter(s), 2 index(es)
Instrs_ok2: 1 parameter(s), 3 index(es)
-/
#guard_msgs in
#eval paramsAndIndices [``Reach, ``Reach', ``Instrs_ok2]

/- Consequences, all visible in Part 3:
     * `Instrs_ok2.rec` is an induction principle for ONE fixed store. Its
       first argument is `{s : store}`, and the motives do NOT take a store;
     * so the motive definitions take `s` first and are passed partially
       applied, as `t_progress_e_P s`. (Rocq doesn't promote, so Rocq's
       motive is `P := fun s C e tf H => ...`, with `s` as a motive argument.);
     * the minor premises don't quantify over the store either, which is why
       every case lemma reads `theorem t_progress_e_X (s : store) : ∀ (C : context) ...`
       and is passed as `(t_progress_e_X s)`.

   ─── 2.3 It is MUTUAL (R5) ───
   `Instr_ok2` (one admin instruction), `Instrs_ok2` (a sequence) and
   `Expr_ok2` (a frame body) are defined together and refer to each other:
       Instr_ok2.label            has two `Instrs_ok2` premises (continuation, body)
       Instr_ok2.Instr_ok2_frame  has an  `Expr_ok2` premise    (the frame body)
       Instrs_ok2.instr           has an  `Instr_ok2` premise
       Instrs_ok2.seq/sub/Instrs_ok2_frame have `Instrs_ok2` premises
       Expr_ok2.mk_Expr_ok2       has an  `Instrs_ok2` premise
   So a derivation tree for a SEQUENCE contains nodes of all three kinds, and
   the fold has to say what it produces at each kind of node: one motive per
   type (3), and one minor premise per constructor of the WHOLE group
   (6 + 5 + 1 = 12). Lean generates three sibling recursors that share the
   store, the 3 motives and the 12 minor premises, and differ only in the
   major premise and the result (R5): -/

/--
info: first 16 binders (store, 3 motives, 12 minors) identical in all three: true
Instr_ok2.rec : <those 16> → ∀ {C} {ai} {ft} (t : Instr_ok2 s C ai ft), motive_1 C ai ft t
Instrs_ok2.rec : <those 16> → ∀ {C} {ais} {ft} (t : Instrs_ok2 s C ais ft), motive_2 C ais ft t
Expr_ok2.rec : <those 16> → ∀ {C} {e} {rt} (t : Expr_ok2 s C e rt), motive_3 C e rt t
-/
#guard_msgs in
#eval siblingRecursors

/- ═══════════════════════════════════════════════════════════════════════
   Part 3. ANATOMY OF `Instrs_ok2.rec`

   `#check @Instrs_ok2.rec` (hover it) prints about 140 lines. Its skeleton,
   with Lean's anonymous names `a, a_1, a_2, a_3` renamed, and `FT t1 t2`
   short for `functype.mk_functype (list.mk_list t1) (list.mk_list t2)`:

     @Instrs_ok2.rec :
       ∀ {s : store}                                              ① the parameter
         {motive_1 : (C : context) → (ai : admininstr) → (ft : functype)
                     → Instr_ok2 s C ai ft → Prop}                ② the motives, one
         {motive_2 : (C : context) → (ais : List admininstr) → (ft : functype)
                     → Instrs_ok2 s C ais ft → Prop}                per type, all
         {motive_3 : (C : context) → (e : adminexpr) → (rt : resulttype)
                     → Expr_ok2 s C e rt → Prop},                   IMPLICIT
       (plain : …) → (label : …) → (Instr_ok2_frame : …) →        ③ the 12 minor
       (call_addr : …) → (ref : …) → (trap : …) →                    premises, named
       (empty : …) → (instr : …) → (seq : …) → (sub : …) →           after their
       (Instrs_ok2_frame : …) → (mk_Expr_ok2 : …) →                  constructors
       ∀ {C : context} {ais : List admininstr} {ft : functype}    ④ the indices
         (t : Instrs_ok2 s C ais ft),                             ⑤ the major premise
       motive_2 C ais ft t                                        ⑥ the result

   ①, ② and ④ are implicit (`{}`): Lean is meant to find them by unification.
   You pass ③ and ⑤, and in `t_progress_e` also ② by name (5.1 and 6.5 say why). -/
#check @Instrs_ok2.rec

/- ─── 3.2 How one minor premise is built from its constructor: `label` ───
   The constructor (in wasm2.0.lean), abbreviated:
     | label (s) (C) (v_n) (instr'_lst) (admininstr_lst) (t_lst) (t'_lst) :
         Instrs_ok2 s C (Map admininstr_instr instr'_lst) (FT t'_lst t_lst) →    -- in the group
         Instrs_ok2 s ({LABELS := [t'_lst]} ++ C) admininstr_lst (FT [] t_lst) →  -- in the group
         wf_store s → wf_context C → wf_admininstr (LABEL_ ..) → wf_context {..} →
         v_n = t'_lst.length →                                                  -- not in the group
         Instr_ok2 s C (LABEL_ v_n instr'_lst admininstr_lst) (FT [] t_lst)

   The recipe for its minor premise:
     (a) `∀` over every argument of the constructor EXCEPT the parameter `s`;
     (b) every premise becomes a named hypothesis (`a, a_1, …`);
     (c) every premise whose type is in the mutual group (a sub-derivation)
         ALSO gets an IH: the motive OF THAT PREMISE'S TYPE, at that premise's
         indices, applied to the premise. Both such premises are `Instrs_ok2`
         here, so both IHs use `motive_2`, although `label` itself builds an
         `Instr_ok2` (R5's rule);
     (d) premises outside the group (`wf_*`, `Instr_ok`, `Frame_ok`, …) get NO IH;
     (e) the conclusion is the motive of the constructor's OWN type
         (`motive_1`), at the conclusion's indices, applied to the constructor
         applied to all the bound variables.
   The real thing, read off the recursor's type (with `pp.proofs` on, so the
   constructor application in the conclusion is printed instead of `⋯`): -/

/--
info: (label : ∀ (C : context) (v_n : n) (instr'_lst : List _root_.instr) (admininstr_lst : List admininstr)
  (t_lst t'_lst : List valtype)
  (a :
    Instrs_ok2 s C (Map (fun instr'_elem => admininstr_instr instr'_elem) instr'_lst)
      (functype.mk_functype (list.mk_list t'_lst) (list.mk_list t_lst)))
  (a_1 :
    Instrs_ok2 s
      ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [],
          LABELS := [list.mk_list t'_lst], RETURN := none } ++
        C)
      admininstr_lst (functype.mk_functype (list.mk_list []) (list.mk_list t_lst)))
  (a_2 : wf_store s) (a_3 : wf_context C) (a_4 : wf_admininstr (admininstr.LABEL_ v_n instr'_lst admininstr_lst))
  (a_5 :
    wf_context
      { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [],
        LABELS := [list.mk_list t'_lst], RETURN := none })
  (a_6 : v_n = t'_lst.length),
  motive_2 C (Map (fun instr'_elem => admininstr_instr instr'_elem) instr'_lst)
      (functype.mk_functype (list.mk_list t'_lst) (list.mk_list t_lst)) a →
    motive_2
        ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [],
            LABELS := [list.mk_list t'_lst], RETURN := none } ++
          C)
        admininstr_lst (functype.mk_functype (list.mk_list []) (list.mk_list t_lst)) a_1 →
      motive_1 C (admininstr.LABEL_ v_n instr'_lst admininstr_lst)
        (functype.mk_functype (list.mk_list []) (list.mk_list t_lst))
        (Instr_ok2.label s C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6))
-/
#guard_msgs in
set_option pp.proofs true in
#eval showMinor ``Instrs_ok2.rec `label

/- ─── 3.3 All 12 minor premises at a glance ───
   For each minor premise: which motive it concludes (= the type its
   constructor builds) and which IHs it receives (= the types of its
   sub-derivations), computed from the recursor's type: -/

/--
info: plain             concludes motive_1;  IHs: none
label             concludes motive_1;  IHs: motive_2, motive_2
Instr_ok2_frame   concludes motive_1;  IHs: motive_3
call_addr         concludes motive_1;  IHs: none
ref               concludes motive_1;  IHs: none
trap              concludes motive_1;  IHs: none
empty             concludes motive_2;  IHs: none
instr             concludes motive_2;  IHs: motive_1
seq               concludes motive_2;  IHs: motive_2, motive_2
sub               concludes motive_2;  IHs: motive_2
Instrs_ok2_frame  concludes motive_2;  IHs: motive_2
mk_Expr_ok2       concludes motive_3;  IHs: motive_2
-/
#guard_msgs in
#eval minorTable ``Instrs_ok2.rec

/- Read this with Part 1's fold picture. At a `seq` node the recursion goes
   into both children with `Instrs_ok2.rec`. An `instr` node's child is an
   `Instr_ok2` derivation, so there it switches to the sibling `Instr_ok2.rec`;
   a `label` node switches back; a FRAME_ node uses `Expr_ok2.rec`. That is
   why all three motives must be given even though we only want motive_2's
   answer: the fold passes through nodes of every kind, and at each one it
   must know what it is building. -/

/- ═══════════════════════════════════════════════════════════════════════
   Part 4. THE 12 CASE LEMMAS ARE THE 12 MINOR PREMISES

   Statements copied verbatim from TypeProgress.lean (the proofs are `sorry`
   here and are complete there). Each statement is the minor premise of the
   same name with the motives plugged in, and Part 5.2 checks that
   mechanically. That's also why the hypotheses are called `a, a_1, …`: the
   statements were produced from Lean's printout of the recursor's type.
   `(s : store)` comes BEFORE the colon because a minor premise doesn't
   quantify over the store (Part 2.2). -/

-- minor `plain`: concludes motive_1 (P). No IH: `Instr_ok` is not in the mutual group.
theorem t_progress_e_plain (s : store) :
    ∀ (C : context) (v_instr : _root_.instr) (t_1_lst t_2_lst : List valtype)
  (a : Instr_ok C v_instr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))) (a_1 : wf_store s)
  (a_2 : wf_context C) (a_3 : wf_instr v_instr),
  t_progress_e_P s C (admininstr_instr v_instr) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.plain s C v_instr t_1_lst t_2_lst a a_1 a_2 a_3) := by sorry

-- minor `label`: concludes P. IHs: P0 for the continuation `instr'_lst`, P0 for the body
-- (typed under one more label).
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
        (Instr_ok2.label s C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6) := by sorry

-- minor `Instr_ok2_frame`: concludes P. IH: P1 for the frame body (an `Expr_ok2`).
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
      (Instr_ok2.Instr_ok2_frame s C v_n f admininstr_lst t_lst C' a a_1 a_2 a_3 a_4 a_5 a_6 a_7) := by sorry

-- minor `call_addr`: concludes P. No IH.
theorem t_progress_e_call_addr (s : store) :
    ∀ (C : context) (v_funcaddr : funcaddr) (t_1_lst t_2_lst : List valtype)
  (a :
    Externaddr_ok s (externaddr.FUNC v_funcaddr)
      (externtype.FUNC (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))))
  (a_1 : wf_store s) (a_2 : wf_context C) (a_3 : wf_admininstr (admininstr.CALL_ADDR v_funcaddr))
  (a_4 : wf_externtype (externtype.FUNC (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))),
  t_progress_e_P s C (admininstr.CALL_ADDR v_funcaddr) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.call_addr s C v_funcaddr t_1_lst t_2_lst a a_1 a_2 a_3 a_4) := by sorry

-- minor `ref`: concludes P. No IH.
theorem t_progress_e_ref (s : store) :
    ∀ (C : context) (v_ref : _root_.ref) (rt : reftype) (a : Ref_ok s v_ref rt) (a_1 : wf_store s)
  (a_2 : wf_context C),
  t_progress_e_P s C (admininstr_ref v_ref) (functype.mk_functype (list.mk_list []) (list.mk_list [valtype_reftype rt]))
    (Instr_ok2.ref s C v_ref rt a a_1 a_2) := by sorry

-- minor `trap`: concludes P. No IH.
theorem t_progress_e_trap (s : store) :
    ∀ (C : context) (t_1_lst t_2_lst : List valtype) (a : wf_store s) (a_1 : wf_context C)
  (a_2 : wf_admininstr admininstr.TRAP),
  t_progress_e_P s C admininstr.TRAP (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.trap s C t_1_lst t_2_lst a a_1 a_2) := by sorry

-- minor `empty`: concludes motive_2 (P0). No IH.
theorem t_progress_e_empty (s : store) :
    ∀ (C : context) (a : wf_store s) (a_1 : wf_context C),
  t_progress_e_P0 s C [] (functype.mk_functype (list.mk_list []) (list.mk_list [])) (Instrs_ok2.empty s C a a_1) := by sorry

-- minor `instr`: concludes P0 at `[v_admininstr]`. IH: P at `v_admininstr`.
theorem t_progress_e_instr (s : store) :
    ∀ (C : context) (v_admininstr : admininstr) (t_1_lst t_2_lst : List valtype)
  (a : Instr_ok2 s C v_admininstr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : wf_store s) (a_2 : wf_context C) (a_3 : wf_admininstr v_admininstr),
  t_progress_e_P s C v_admininstr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_e_P0 s C [v_admininstr] (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
      (Instrs_ok2.instr s C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3) := by sorry

-- minor `seq`: concludes P0 at `admininstr_1_lst ++ admininstr_2_lst`. IHs: P0 for each half.
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
        (Instrs_ok2.seq s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5) := by sorry

-- minor `sub`: concludes P0 at the type after subsumption, `t'_1_lst → t'_2_lst`. IH: P0 at the
-- original type `t_1_lst → t_2_lst`.
theorem t_progress_e_sub (s : store) :
    ∀ (C : context) (admininstr_lst : List admininstr) (t'_1_lst t'_2_lst t_1_lst t_2_lst : List valtype)
  (a : Instrs_ok2 s C admininstr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : Resulttype_sub (list.mk_list t'_1_lst) (list.mk_list t_1_lst))
  (a_2 : Resulttype_sub (list.mk_list t_2_lst) (list.mk_list t'_2_lst)) (a_3 : wf_store s) (a_4 : wf_context C)
  (a_5 : Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst),
  t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list t'_1_lst) (list.mk_list t'_2_lst))
      (Instrs_ok2.sub s C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5) := by sorry

-- minor `Instrs_ok2_frame`: concludes P0 at `t_lst ++ t_1_lst → t_lst ++ t_2_lst`. IH: P0 without `t_lst`.
theorem t_progress_e_Instrs_ok2_frame (s : store) :
    ∀ (C : context) (admininstr_lst : List admininstr) (t_lst t_1_lst t_2_lst : List valtype)
  (a : Instrs_ok2 s C admininstr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
  (a_1 : wf_store s) (a_2 : wf_context C)
  (a_3 : Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst),
  t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
    t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list (t_lst ++ t_1_lst)) (list.mk_list (t_lst ++ t_2_lst)))
      (Instrs_ok2.Instrs_ok2_frame s C admininstr_lst t_lst t_1_lst t_2_lst a a_1 a_2 a_3) := by sorry

-- minor `mk_Expr_ok2`: concludes motive_3 (P1). IH: P0 for the same instructions.
theorem t_progress_e_mk_Expr_ok2 (s : store) :
    ∀ (C : context) (admininstr_lst : List admininstr) (t_lst : List valtype)
  (a : Instrs_ok2 s C admininstr_lst (functype.mk_functype (list.mk_list []) (list.mk_list t_lst)))
  (a_1 : wf_store s) (a_2 : wf_context C)
  (a_3 : Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst),
  t_progress_e_P0 s C admininstr_lst (functype.mk_functype (list.mk_list []) (list.mk_list t_lst)) a →
    t_progress_e_P1 s C admininstr_lst (list.mk_list t_lst) (Expr_ok2.mk_Expr_ok2 s C admininstr_lst t_lst a a_1 a_2 a_3) := by sorry

/- ═══════════════════════════════════════════════════════════════════════
   Part 5. `t_progress_e`, ONE ARGUMENT AT A TIME

   The proof in TypeProgress.lean (copied in 5.8) is

       intro hwf hadmin
       exact (Instrs_ok2.rec (motive_1 := t_progress_e_P s) (motive_2 := t_progress_e_P0 s)
                (motive_3 := t_progress_e_P1 s)
                (t_progress_e_plain s) … (t_progress_e_mk_Expr_ok2 s)       -- 12 minors
                hadmin) f framemoduleC vals vt1 vt2 lab ret hwf

   Applying something of type `∀ x : A, B x` to a `v : A` gives type `B v`:
   the leading binder is used up, and `v` is substituted for `x` in the rest.
   That is ALL that happens below, once per argument, plus ONE unfolding of a
   definition in 5.5.

   ─── 5.1 The parameter `{s}` is never written: unification finds it ───
   The first argument written is `(motive_1 := t_progress_e_P s)`. The
   recursor wants `motive_1` to have the type
       (C : context) → (ai : admininstr) → (ft : functype) → Instr_ok2 ?s C ai ft → Prop
   where `?s` is still unknown. The argument has the type below, so matching
   `Instr_ok2 ?s C ai ft` with `Instr_ok2 s C ai ft` sets `?s := s`. -/

section
variable (s : store)
/--
info: t_progress_e_P s : (C : context) → (ai : admininstr) → (ft : functype) → Instr_ok2 s C ai ft → Prop
-/
#guard_msgs in
#check t_progress_e_P s
end

/- Why name the motives at all? They are implicit arguments, and Lean can't
   always guess a motive (that's higher-order unification). Here the recursor
   application sits in FUNCTION position -- `( … hadmin) f framemoduleC …` --
   so it has no expected type to read a motive off. 6.5 shows the error you
   get without them.

   ─── 5.2 Plug in the three motives ───
   Substitution turns every `motive_1 X Y Z W` in the rest of the type into
   `t_progress_e_P s X Y Z W`, and likewise for motives 2 and 3. Here is the
   first minor premise, `plain`, before and after: -/

/--
info: (plain : ∀ (C : context) (v_instr : _root_.instr) (t_1_lst t_2_lst : List valtype)
  (a : Instr_ok C v_instr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))) (a_1 : wf_store s)
  (a_2 : wf_context C) (a_3 : wf_instr v_instr),
  motive_1 C (admininstr_instr v_instr) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.plain s C v_instr t_1_lst t_2_lst a a_1 a_2 a_3))
-/
#guard_msgs in
set_option pp.proofs true in
#eval showMinor ``Instrs_ok2.rec `plain

/--
info: (plain : ∀ (C : context) (v_instr : _root_.instr) (t_1_lst t_2_lst : List valtype)
  (a : Instr_ok C v_instr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))) (a_1 : wf_store s)
  (a_2 : wf_context C) (a_3 : wf_instr v_instr),
  t_progress_e_P s C (admininstr_instr v_instr) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.plain s C v_instr t_1_lst t_2_lst a a_1 a_2 a_3))
-/
#guard_msgs in
set_option pp.proofs true in
#eval showMinorAfterMotives `plain

/- The second printout is, word for word, the statement of
   `t_progress_e_plain s` in Part 4. The same holds for all 12. The check
   below feeds the lemmas in one at a time, and before each one compares the
   type the recursor expects with the lemma's type, up to renaming bound
   variables only. Its last line is what is left once all 12 are in (5.3): -/

/--
info: plain             expects exactly the type of `TLC.t_progress_e_plain s`: true
label             expects exactly the type of `TLC.t_progress_e_label s`: true
Instr_ok2_frame   expects exactly the type of `TLC.t_progress_e_Instr_ok2_frame s`: true
call_addr         expects exactly the type of `TLC.t_progress_e_call_addr s`: true
ref               expects exactly the type of `TLC.t_progress_e_ref s`: true
trap              expects exactly the type of `TLC.t_progress_e_trap s`: true
empty             expects exactly the type of `TLC.t_progress_e_empty s`: true
instr             expects exactly the type of `TLC.t_progress_e_instr s`: true
seq               expects exactly the type of `TLC.t_progress_e_seq s`: true
sub               expects exactly the type of `TLC.t_progress_e_sub s`: true
Instrs_ok2_frame  expects exactly the type of `TLC.t_progress_e_Instrs_ok2_frame s`: true
mk_Expr_ok2       expects exactly the type of `TLC.t_progress_e_mk_Expr_ok2 s`: true
left after the 12 minors: ∀ {a : context} {a_1 : List admininstr} {a_2 : functype} (t : Instrs_ok2 s a a_1 a_2), t_progress_e_P0 s a a_1 a_2 t
-/
#guard_msgs in
#eval checkMinors

/- ─── 5.3 to 5.7, as one tactic proof ───
   Each `have` below states the type at that step, so it only compiles if
   the step really produces that type. Put your cursor on each line to watch
   the goal and hypotheses. -/

theorem t_progress_e_steps (s : store) (C framemoduleC : context) (f : frame) (vals : List val)
    (ais : List admininstr) (ft : functype) (vt1 vt2 : List valtype) (lab : List resulttype)
    (ret : Option resulttype) :
    wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)) →
    Instrs_ok2 s C ais ft →
    Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form ((List.map admininstr_val vals) ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais))
          (config.mk_config (state.mk_state s' f') ais') := by
  intro hwf hadmin
  -- 5.3  After the motives and the 12 minor premises, what is left is "for EVERY derivation,
  --      P0 holds": the induction is done. Only ④ (implicit indices) and ⑤ remain.
  have step3 : ∀ {C : context} {ais : List admininstr} {ft : functype} (t : Instrs_ok2 s C ais ft),
      t_progress_e_P0 s C ais ft t :=
    Instrs_ok2.rec (motive_1 := t_progress_e_P s) (motive_2 := t_progress_e_P0 s)
      (motive_3 := t_progress_e_P1 s)
      (t_progress_e_plain s) (t_progress_e_label s) (t_progress_e_Instr_ok2_frame s)
      (t_progress_e_call_addr s) (t_progress_e_ref s) (t_progress_e_trap s)
      (t_progress_e_empty s) (t_progress_e_instr s) (t_progress_e_seq s) (t_progress_e_sub s)
      (t_progress_e_Instrs_ok2_frame s) (t_progress_e_mk_Expr_ok2 s)
  -- 5.4  The major premise. The indices `{C} {ais} {ft}` are implicit: matching
  --      `Instrs_ok2 s ?C ?ais ?ft` against the type of `hadmin` sets ?C := C, ?ais := ais,
  --      ?ft := ft. Pure substitution, so it fits with unfolding switched off:
  have step4 : t_progress_e_P0 s C ais ft hadmin := by
    with_reducible exact step3 hadmin
  -- 5.5  THE ONE UNFOLDING. The parenthesis closes here, and the result is applied to `f`.
  --      But `t_progress_e_P0 s C ais ft hadmin` is not visibly a `∀`, so Lean computes its
  --      weak head normal form: it unfolds the definition `t_progress_e_P0` (δ-reduction) and
  --      substitutes `s C ais ft hadmin` for its parameters (β-reduction). `hadmin` goes into the
  --      ignored `_`, and P0's body appears. The bound names are primed here to make the
  --      substitution in 5.6 visible; names of bound variables never matter.
  have step5 : ∀ (f' : frame) (fm' : context) (vals' : List val) (vt1' vt2' : List valtype)
      (lab' : List resulttype) (ret' : Option resulttype),
      wf_config (config.mk_config (state.mk_state s f') (List.map admininstr_val vals' ++ ais)) →
      Forall (fun e => wf_val e) vals' →
      ft = mkFunctype vt1' vt2' →
      C = upd_local_label_return fm' (List.map typeof f'.LOCALS) lab' ret' →
      Moduleinst_ok s f'.MODULE fm' →
      List.map typeof vals' = vt1' →
      Store_ok s →
      not_lf_br ais →
      not_lf_return ais →
      terminal_form (List.map admininstr_val vals' ++ ais) ∨
        ∃ (s' : store) (f'' : frame) (ais' : List admininstr),
          Step (config.mk_config (state.mk_state s f') (List.map admininstr_val vals' ++ ais))
            (config.mk_config (state.mk_state s' f'') ais') := by
    fail_if_success with_reducible exact step4   -- does NOT fit without unfolding ...
    exact step4                                  -- ... fits once `t_progress_e_P0` is unfolded
  -- 5.6  `f framemoduleC vals vt1 vt2 lab ret` fill the seven `∀`s. They happen to have the same
  --      names as P0's binders, but it's positional: `f` goes into `f'`, `framemoduleC` into
  --      `fm'`, and so on. Pure substitution again:
  have step6 : wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais)) →
      Forall (fun e => wf_val e) vals →
      ft = mkFunctype vt1 vt2 →
      C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
      Moduleinst_ok s f.MODULE framemoduleC →
      List.map typeof vals = vt1 →
      Store_ok s →
      not_lf_br ais →
      not_lf_return ais →
      terminal_form (List.map admininstr_val vals ++ ais) ∨
        ∃ (s' : store) (f' : frame) (ais' : List admininstr),
          Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais))
            (config.mk_config (state.mk_state s' f') ais') := by
    with_reducible exact step5 f framemoduleC vals vt1 vt2 lab ret
  -- 5.7  `hwf` fills the first premise, which is exactly its type. What is left is the goal you
  --      see after `intro hwf hadmin`, except that the goal says `fun val => wf_val val` where
  --      this says `fun e => wf_val e` (a bound name, which doesn't matter). So it fits with
  --      unfolding switched off:
  have step7 := step6 hwf
  with_reducible exact step7

/- Proof that 5.5 really is an unfolding step: forbid unfolding `t_progress_e_P0`, and applying
   a proof of it to `f` is rejected. -/
section
attribute [local irreducible] t_progress_e_P0
/--
error: Function expected at
  h
but this term has type
  t_progress_e_P0 s C ais ft hadmin

Note: Expected a function because this term is being applied to the argument
  f
-/
#guard_msgs in
example (s : store) (C : context) (ais : List admininstr) (ft : functype)
    (hadmin : Instrs_ok2 s C ais ft) (f : frame) (h : t_progress_e_P0 s C ais ft hadmin) : True :=
  (h f).elim
end

/- ─── 5.8 The original, verbatim (plus a `trace_state`) ───
   The pinned goal is the one at your `exact`: compare it with 5.7. -/

/--
trace: s : store
C framemoduleC : context
f : frame
vals : List val
ais : List admininstr
ft : functype
vt1 vt2 : List valtype
lab : List resulttype
ret : Option resulttype
hwf : wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais))
hadmin : Instrs_ok2 s C ais ft
⊢ Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
      C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
        Moduleinst_ok s f.MODULE framemoduleC →
          List.map typeof vals = vt1 →
            Store_ok s →
              not_lf_br ais →
                not_lf_return ais →
                  terminal_form (List.map admininstr_val vals ++ ais) ∨
                    ∃ s' f' ais',
                      Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais))
                        (config.mk_config (state.mk_state s' f') ais')
-/
#guard_msgs in
theorem t_progress_e (s : store) (C framemoduleC : context) (f : frame) (vals : List val) (ais : List admininstr)
    (ft : functype) (vt1 vt2 : List valtype) (lab : List resulttype) (ret : Option resulttype) :
    wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)) →
    Instrs_ok2 s C ais ft →
    Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form ((List.map admininstr_val vals) ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais))
          (config.mk_config (state.mk_state s' f') ais') := by
  intro hwf hadmin
  trace_state
  exact (
    Instrs_ok2.rec
      (motive_1 := t_progress_e_P s)
      (motive_2 := t_progress_e_P0 s)
      (motive_3 := t_progress_e_P1 s)
      (t_progress_e_plain s)
      (t_progress_e_label s)
      (t_progress_e_Instr_ok2_frame s)
      (t_progress_e_call_addr s)
      (t_progress_e_ref s)
      (t_progress_e_trap s)
      (t_progress_e_empty s)
      (t_progress_e_instr s)
      (t_progress_e_seq s)
      (t_progress_e_sub s)
      (t_progress_e_Instrs_ok2_frame s)
      (t_progress_e_mk_Expr_ok2 s)
      hadmin
    ) f framemoduleC vals vt1 vt2 lab ret hwf

/- ═══════════════════════════════════════════════════════════════════════
   Part 6. THE SAME PROOF WITH TACTICS

   ─── 6.1 `refine` with named holes: the minor premises become goals ───
   Write `?plain`, `?label`, … instead of the 12 lemmas. Each hole becomes a
   goal tagged with that name, and its type is the minor premise (5.2), as
   the pinned `trace_state` shows for `seq`. Every case lemma then closes its
   goal with unfolding switched off, which is 5.2's check done a second way. -/

/--
trace: s : store
C framemoduleC : context
f : frame
vals : List val
ais : List admininstr
ft : functype
vt1 vt2 : List valtype
lab : List resulttype
ret : Option resulttype
hwf : wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais))
hadmin : Instrs_ok2 s C ais ft
⊢ ∀ (C : context) (admininstr_1_lst admininstr_2_lst : List admininstr) (t_1_lst t_3_lst t_2_lst : List valtype)
    (a : Instrs_ok2 s C admininstr_1_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)))
    (a_1 : Instrs_ok2 s C admininstr_2_lst (functype.mk_functype (list.mk_list t_2_lst) (list.mk_list t_3_lst)))
    (a_2 : wf_store s) (a_3 : wf_context C)
    (a_4 : Forall (fun admininstr_1_elem => wf_admininstr admininstr_1_elem) admininstr_1_lst)
    (a_5 : Forall (fun admininstr_2_elem => wf_admininstr admininstr_2_elem) admininstr_2_lst),
    t_progress_e_P0 s C admininstr_1_lst (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst)) a →
      t_progress_e_P0 s C admininstr_2_lst (functype.mk_functype (list.mk_list t_2_lst) (list.mk_list t_3_lst)) a_1 →
        t_progress_e_P0 s C (admininstr_1_lst ++ admininstr_2_lst)
          (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_3_lst))
          (Instrs_ok2.seq s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5)
-/
#guard_msgs in
set_option pp.proofs true in
theorem t_progress_e_refine (s : store) (C framemoduleC : context) (f : frame) (vals : List val)
    (ais : List admininstr) (ft : functype) (vt1 vt2 : List valtype) (lab : List resulttype)
    (ret : Option resulttype) :
    wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)) →
    Instrs_ok2 s C ais ft →
    Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form ((List.map admininstr_val vals) ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais))
          (config.mk_config (state.mk_state s' f') ais') := by
  intro hwf hadmin
  refine (Instrs_ok2.rec (motive_1 := t_progress_e_P s) (motive_2 := t_progress_e_P0 s)
    (motive_3 := t_progress_e_P1 s)
    ?plain ?label ?Instr_ok2_frame ?call_addr ?ref ?trap ?empty ?instr ?seq ?sub ?Instrs_ok2_frame
    ?mk_Expr_ok2 hadmin) f framemoduleC vals vt1 vt2 lab ret hwf
  case seq =>
    trace_state
    with_reducible exact t_progress_e_seq s
  case plain => with_reducible exact t_progress_e_plain s
  case label => with_reducible exact t_progress_e_label s
  case Instr_ok2_frame => with_reducible exact t_progress_e_Instr_ok2_frame s
  case call_addr => with_reducible exact t_progress_e_call_addr s
  case ref => with_reducible exact t_progress_e_ref s
  case trap => with_reducible exact t_progress_e_trap s
  case empty => with_reducible exact t_progress_e_empty s
  case instr => with_reducible exact t_progress_e_instr s
  case sub => with_reducible exact t_progress_e_sub s
  case Instrs_ok2_frame => with_reducible exact t_progress_e_Instrs_ok2_frame s
  case mk_Expr_ok2 => with_reducible exact t_progress_e_mk_Expr_ok2 s

/- ─── 6.2 `induction … using`: the goal has to BECOME P0 first ───
   The key difference from `refine`: you may not write the main motive
   (I3); it is COMPUTED by abstracting the targets
   `C ais ft hadmin` out of the current goal. So first make the goal look like
   P0's body, i.e. `∀ f framemoduleC vals vt1 vt2 lab ret, wf_config … → …`.
   That is `revert`, and it's exactly Rocq's `move: f C' vcs ts1 ts2 lab ret
   HWfConfig.` before its `apply Admin_instrs_ok_ind'` (and I5's "state the
   general goal first").

   One trap: a single `revert f framemoduleC …` reverts in the order of the
   local CONTEXT, and the theorem declares `framemoduleC` before `f`: -/

/--
trace: s : store
C : context
ais : List admininstr
ft : functype
hadmin : Instrs_ok2 s C ais ft
⊢ ∀ (framemoduleC : context) (f : frame) (vals : List val) (vt1 vt2 : List valtype) (lab : List resulttype)
    (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais)) → True
-/
#guard_msgs in
example (s : store) (C framemoduleC : context) (f : frame) (vals : List val) (ais : List admininstr)
    (ft : functype) (vt1 vt2 : List valtype) (lab : List resulttype) (ret : Option resulttype)
    (hwf : wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)))
    (hadmin : Instrs_ok2 s C ais ft) : True := by
  revert f framemoduleC vals vt1 vt2 lab ret hwf
  trace_state
  intros
  trivial

/- `∀ framemoduleC f` is not `∀ f framemoduleC`. The two are logically
   equivalent but they are DIFFERENT types, and the case lemmas are stated
   with P0's order. Reverting one variable at a time (last first) gives
   exactly P0's order. Then `induction` needs only the OTHER two motives (I4),
   and each alternative `| ctor names => …` receives the minor premise's `∀`
   variables, IHs last, under your names. -/

/--
trace: s : store
C : context
ais : List admininstr
ft : functype
hadmin : Instrs_ok2 s C ais ft
⊢ ∀ (f : frame) (framemoduleC : context) (vals : List val) (vt1 vt2 : List valtype) (lab : List resulttype)
    (ret : Option resulttype),
    wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais)) →
      Forall (fun val => wf_val val) vals →
        ft = mkFunctype vt1 vt2 →
          C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
            Moduleinst_ok s f.MODULE framemoduleC →
              List.map typeof vals = vt1 →
                Store_ok s →
                  not_lf_br ais →
                    not_lf_return ais →
                      terminal_form (List.map admininstr_val vals ++ ais) ∨
                        ∃ s' f' ais',
                          Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vals ++ ais))
                            (config.mk_config (state.mk_state s' f') ais')
-/
#guard_msgs in
theorem t_progress_e_induction (s : store) (C framemoduleC : context) (f : frame) (vals : List val)
    (ais : List admininstr) (ft : functype) (vt1 vt2 : List valtype) (lab : List resulttype)
    (ret : Option resulttype) :
    wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)) →
    Instrs_ok2 s C ais ft →
    Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form ((List.map admininstr_val vals) ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais))
          (config.mk_config (state.mk_state s' f') ais') := by
  intro hwf hadmin
  revert hwf; revert ret; revert lab; revert vt2; revert vt1; revert vals; revert framemoduleC; revert f
  trace_state    -- the goal is now P0's body, at the indices `C ais ft`
  induction hadmin using Instrs_ok2.rec (motive_1 := t_progress_e_P s) (motive_3 := t_progress_e_P1 s) with
  | plain C v_instr t_1_lst t_2_lst a a_1 a_2 a_3 =>
    with_reducible exact t_progress_e_plain s C v_instr t_1_lst t_2_lst a a_1 a_2 a_3
  | label C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6 ih ih' =>
    exact t_progress_e_label s C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6 ih ih'
  | Instr_ok2_frame C v_n f admininstr_lst t_lst C' a a_1 a_2 a_3 a_4 a_5 a_6 a_7 ih =>
    exact t_progress_e_Instr_ok2_frame s C v_n f admininstr_lst t_lst C' a a_1 a_2 a_3 a_4 a_5 a_6 a_7 ih
  | call_addr C v_funcaddr t_1_lst t_2_lst a a_1 a_2 a_3 a_4 =>
    exact t_progress_e_call_addr s C v_funcaddr t_1_lst t_2_lst a a_1 a_2 a_3 a_4
  | ref C v_ref rt a a_1 a_2 =>
    exact t_progress_e_ref s C v_ref rt a a_1 a_2
  | trap C t_1_lst t_2_lst a a_1 a_2 =>
    exact t_progress_e_trap s C t_1_lst t_2_lst a a_1 a_2
  | empty C a a_1 =>
    exact t_progress_e_empty s C a a_1
  | instr C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_instr s C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3 ih
  | seq C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih1 ih2 =>
    -- Here motive_2 is the COMPUTED `fun C ais ft hadmin => ∀ f …`, not the name
    -- `t_progress_e_P0 s`, so the goal and the IHs are P0's body, and the lemma's
    -- `t_progress_e_P0 s …` has to be unfolded to match. (`plain` above concludes motive_1,
    -- which we supplied by name, so it fits as is.)
    fail_if_success
      with_reducible
        exact t_progress_e_seq s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst
          a a_1 a_2 a_3 a_4 a_5 ih1 ih2
    exact t_progress_e_seq s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4
      a_5 ih1 ih2
  | sub C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih =>
    exact t_progress_e_sub s C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih
  | Instrs_ok2_frame C admininstr_lst t_lst t_1_lst t_2_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_Instrs_ok2_frame s C admininstr_lst t_lst t_1_lst t_2_lst a a_1 a_2 a_3 ih
  | mk_Expr_ok2 C admininstr_lst t_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_mk_Expr_ok2 s C admininstr_lst t_lst a a_1 a_2 a_3 ih

/- ─── 6.3 Under the hood: it is the same term ───
   `#print t_progress_e_induction` (hover it) starts with
   `(fun x_0 => Instrs_ok2.rec) (fun C ais ft hadmin => ∀ f …) (fun C v_instr … => t_progress_e_plain s C v_instr …) …`:
   `induction` builds the recursor applied to the computed motive as a
   β-redex, and wraps each alternative in a `fun`. β-reduce it, and it is the
   hand-written term of 5.8, with motive_2 spelled out instead of named: -/
#print t_progress_e_induction

/--
info: head before β-reduction: fun x_0 => Instrs_ok2.rec
head after β-reduction:  @Instrs_ok2.rec, applied to 28 arguments
motive_1 := t_progress_e_P s
motive_3 := t_progress_e_P1 s
motive_2 is literally `t_progress_e_P0 s`: false
motive_2 is the body of `t_progress_e_P0`, unfolded: true
motive_2 is definitionally equal to `t_progress_e_P0 s`: true
-/
#guard_msgs in
#eval showRecApp ``t_progress_e_induction

/--
info: head before β-reduction: @Instrs_ok2.rec
head after β-reduction:  @Instrs_ok2.rec, applied to 28 arguments
motive_1 := t_progress_e_P s
motive_3 := t_progress_e_P1 s
motive_2 is literally `t_progress_e_P0 s`: true
motive_2 is the body of `t_progress_e_P0`, unfolded: false
motive_2 is definitionally equal to `t_progress_e_P0 s`: true
-/
#guard_msgs in
#eval showRecApp ``t_progress_e

/- Both are `@Instrs_ok2.rec` applied to 28 arguments: s, 3 motives, 12
   minors, 3 indices, hadmin, then f framemoduleC vals vt1 vt2 lab ret hwf.
   The 8 reverted variables are applied after the recursor in BOTH: `revert`
   turned them into binders of the goal, and closing that goal applies them
   back, just like the direct term's `( … ) f framemoduleC … hwf`.

   ─── 6.4 The idiomatic form: `generalizing` ───
   `induction … generalizing x y` does the `revert` for you, and then re-`intro`s
   the variables at the start of each alternative. Three things to know, all
   verified in the proof below:
     (1) `hwf` mentions the index `ais`, so it is reverted AUTOMATICALLY.
         Listing it is an error (6.5d);
     (2) the variables are reverted in context order, so the IHs come out as
         `∀ framemoduleC f …`, the order 6.2 warned about. A case lemma needs
         `∀ f framemoduleC …`, so each IH passes through a one-line adapter
         `fun f fm => ih fm f` that swaps the first two arguments;
     (3) the variables are re-introduced ONLY in alternatives that conclude
         the computed motive (`empty`, `instr`, `seq`, `sub`,
         `Instrs_ok2_frame`). There the goal is "the 8 premises → conclusion",
         and the lemma is applied to `f framemoduleC vals vt1 vt2 lab ret hwf`
         INSIDE the case. The direct term applies those 8 arguments ONCE, at
         the end. The alternatives for motive_1 and motive_3 (`plain`, …,
         `mk_Expr_ok2`) keep the goal `t_progress_e_P s …` / `t_progress_e_P1 s …`,
         as the pinned trace of `plain` shows. -/

/--
trace: case plain
s : store
C✝ : context
ais : List admininstr
ft : functype
C : context
v_instr : instr
t_1_lst t_2_lst : List valtype
a : Instr_ok C v_instr (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
a_1 : wf_store s
a_2 : wf_context C
a_3 : wf_instr v_instr
⊢ t_progress_e_P s C (admininstr_instr v_instr) (functype.mk_functype (list.mk_list t_1_lst) (list.mk_list t_2_lst))
    (Instr_ok2.plain s C v_instr t_1_lst t_2_lst a a_1 a_2 a_3)
-/
#guard_msgs in
set_option pp.proofs true in
theorem t_progress_e_generalizing (s : store) (C framemoduleC : context) (f : frame) (vals : List val)
    (ais : List admininstr) (ft : functype) (vt1 vt2 : List valtype) (lab : List resulttype)
    (ret : Option resulttype) :
    wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)) →
    Instrs_ok2 s C ais ft →
    Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form ((List.map admininstr_val vals) ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais))
          (config.mk_config (state.mk_state s' f') ais') := by
  intro hwf hadmin
  induction hadmin using Instrs_ok2.rec (motive_1 := t_progress_e_P s) (motive_3 := t_progress_e_P1 s)
    generalizing f framemoduleC vals vt1 vt2 lab ret with
  | plain C v_instr t_1_lst t_2_lst a a_1 a_2 a_3 =>
    trace_state
    exact t_progress_e_plain s C v_instr t_1_lst t_2_lst a a_1 a_2 a_3
  | label C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6 ih ih' =>
    exact t_progress_e_label s C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6
      (fun f fm => ih fm f) (fun f fm => ih' fm f)
  | Instr_ok2_frame C v_n f admininstr_lst t_lst C' a a_1 a_2 a_3 a_4 a_5 a_6 a_7 ih =>
    exact t_progress_e_Instr_ok2_frame s C v_n f admininstr_lst t_lst C' a a_1 a_2 a_3 a_4 a_5 a_6 a_7 ih
  | call_addr C v_funcaddr t_1_lst t_2_lst a a_1 a_2 a_3 a_4 =>
    exact t_progress_e_call_addr s C v_funcaddr t_1_lst t_2_lst a a_1 a_2 a_3 a_4
  | ref C v_ref rt a a_1 a_2 =>
    exact t_progress_e_ref s C v_ref rt a a_1 a_2
  | trap C t_1_lst t_2_lst a a_1 a_2 =>
    exact t_progress_e_trap s C t_1_lst t_2_lst a a_1 a_2
  | empty C a a_1 =>
    exact t_progress_e_empty s C a a_1 f framemoduleC vals vt1 vt2 lab ret hwf
  | instr C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_instr s C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3 ih
      f framemoduleC vals vt1 vt2 lab ret hwf
  | seq C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih1 ih2 =>
    fail_if_success   -- without the adapters, the IHs have the wrong binder order
      exact t_progress_e_seq s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst
        a a_1 a_2 a_3 a_4 a_5 ih1 ih2 f framemoduleC vals vt1 vt2 lab ret hwf
    exact t_progress_e_seq s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5
      (fun f fm => ih1 fm f) (fun f fm => ih2 fm f) f framemoduleC vals vt1 vt2 lab ret hwf
  | sub C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih =>
    exact t_progress_e_sub s C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5
      (fun f fm => ih fm f) f framemoduleC vals vt1 vt2 lab ret hwf
  | Instrs_ok2_frame C admininstr_lst t_lst t_1_lst t_2_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_Instrs_ok2_frame s C admininstr_lst t_lst t_1_lst t_2_lst a a_1 a_2 a_3
      (fun f fm => ih fm f) f framemoduleC vals vt1 vt2 lab ret hwf
  | mk_Expr_ok2 C admininstr_lst t_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_mk_Expr_ok2 s C admininstr_lst t_lst a a_1 a_2 a_3 (fun f fm => ih fm f)

/- If the theorem had declared `f` BEFORE `framemoduleC`, the context order
   would already be P0's order, and no adapters would be needed: -/
theorem t_progress_e_generalizing' (s : store) (C : context) (f : frame) (framemoduleC : context)
    (vals : List val) (ais : List admininstr) (ft : functype) (vt1 vt2 : List valtype)
    (lab : List resulttype) (ret : Option resulttype) :
    wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)) →
    Instrs_ok2 s C ais ft →
    Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form ((List.map admininstr_val vals) ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais))
          (config.mk_config (state.mk_state s' f') ais') := by
  intro hwf hadmin
  induction hadmin using Instrs_ok2.rec (motive_1 := t_progress_e_P s) (motive_3 := t_progress_e_P1 s)
    generalizing f framemoduleC vals vt1 vt2 lab ret with
  | plain C v_instr t_1_lst t_2_lst a a_1 a_2 a_3 =>
    exact t_progress_e_plain s C v_instr t_1_lst t_2_lst a a_1 a_2 a_3
  | label C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6 ih ih' =>
    exact t_progress_e_label s C v_n instr'_lst admininstr_lst t_lst t'_lst a a_1 a_2 a_3 a_4 a_5 a_6 ih ih'
  | Instr_ok2_frame C v_n f admininstr_lst t_lst C' a a_1 a_2 a_3 a_4 a_5 a_6 a_7 ih =>
    exact t_progress_e_Instr_ok2_frame s C v_n f admininstr_lst t_lst C' a a_1 a_2 a_3 a_4 a_5 a_6 a_7 ih
  | call_addr C v_funcaddr t_1_lst t_2_lst a a_1 a_2 a_3 a_4 =>
    exact t_progress_e_call_addr s C v_funcaddr t_1_lst t_2_lst a a_1 a_2 a_3 a_4
  | ref C v_ref rt a a_1 a_2 =>
    exact t_progress_e_ref s C v_ref rt a a_1 a_2
  | trap C t_1_lst t_2_lst a a_1 a_2 =>
    exact t_progress_e_trap s C t_1_lst t_2_lst a a_1 a_2
  | empty C a a_1 =>
    exact t_progress_e_empty s C a a_1 f framemoduleC vals vt1 vt2 lab ret hwf
  | instr C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_instr s C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3 ih
      f framemoduleC vals vt1 vt2 lab ret hwf
  | seq C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih1 ih2 =>
    exact t_progress_e_seq s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5
      ih1 ih2 f framemoduleC vals vt1 vt2 lab ret hwf
  | sub C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih =>
    exact t_progress_e_sub s C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5
      ih f framemoduleC vals vt1 vt2 lab ret hwf
  | Instrs_ok2_frame C admininstr_lst t_lst t_1_lst t_2_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_Instrs_ok2_frame s C admininstr_lst t_lst t_1_lst t_2_lst a a_1 a_2 a_3
      ih f framemoduleC vals vt1 vt2 lab ret hwf
  | mk_Expr_ok2 C admininstr_lst t_lst a a_1 a_2 a_3 ih =>
    exact t_progress_e_mk_Expr_ok2 s C admininstr_lst t_lst a a_1 a_2 a_3 ih

/- ─── 6.5 What goes wrong, verified ───
   (a) Plain `induction` refuses mutual types; you must name the recursor: -/

/--
error: The `induction` tactic does not support the type `Instrs_ok2` because it is mutually inductive

Hint: Consider using the `cases` tactic instead
-/
#guard_msgs in
example (s : store) (C : context) (ais : List admininstr) (ft : functype)
    (hadmin : Instrs_ok2 s C ais ft) : True := by
  induction hadmin

/- (b) Naming the MAIN motive in `using` is the wall from I3 (the motives
   here are trivial `True`s, to keep the message short): -/

/--
error: Expected resulting type of eliminator to be an application of one of its parameters (the motive), but found
  True
-/
#guard_msgs in
example (s : store) (C : context) (ais : List admininstr) (ft : functype)
    (hadmin : Instrs_ok2 s C ais ft) : True := by
  induction hadmin using Instrs_ok2.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)

/- (c) Leaving out the OTHER motives is worse, because `induction` doesn't
   complain at first. The cases that conclude motive_1 or motive_3 get an
   unsolved metavariable `?m…` as their goal (traced below for `plain`), and the
   problem only surfaces when the kernel rejects the finished term. So,
   as in I4, you must name every motive except the main one: -/

/--
trace: s : store
C : context
ais : List admininstr
ft : functype
hadmin : Instrs_ok2 s C ais ft
C✝ : context
v_instr✝ : instr
t_1_lst✝ t_2_lst✝ : List valtype
a✝³ : Instr_ok C✝ v_instr✝ (functype.mk_functype (list.mk_list t_1_lst✝) (list.mk_list t_2_lst✝))
a✝² : wf_store s
a✝¹ : wf_context C✝
a✝ : wf_instr v_instr✝
⊢ ?m.22 C✝ (admininstr_instr v_instr✝) (functype.mk_functype (list.mk_list t_1_lst✝) (list.mk_list t_2_lst✝))
    (Instr_ok2.plain s C✝ v_instr✝ t_1_lst✝ t_2_lst✝ a✝³ a✝² a✝¹ a✝)
---
warning: declaration uses `sorry`
---
error: (kernel) declaration has metavariables 'TLC._example'
-/
#guard_msgs in
set_option pp.proofs true in
example (s : store) (C : context) (ais : List admininstr) (ft : functype)
    (hadmin : Instrs_ok2 s C ais ft) : True := by
  induction hadmin using Instrs_ok2.rec
  case plain => trace_state; sorry
  all_goals sorry

/- (d) `generalizing hwf`: `hwf` mentions the index `ais`, so `induction`
   already generalizes it: -/

/--
error: Unnecessary `generalizing` argument: Variable `hwf` is generalized automatically
-/
#guard_msgs in
example (s : store) (C framemoduleC : context) (f : frame) (vals : List val) (ais : List admininstr)
    (ft : functype) (hwf : wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)))
    (hadmin : Instrs_ok2 s C ais ft) : True := by
  induction hadmin using Instrs_ok2.rec (motive_1 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)
    generalizing hwf
  all_goals trivial

/- (e) Why the direct term names its motives. With an expected type, Lean can
   elaborate `Instrs_ok2.rec` "as an eliminator" (I3's mechanism): it computes
   motive_2 from the expected type, and here it even finds motive_1 and
   motive_3 by unifying with the case lemmas' statements. So this works with
   NO motives named: -/
example (s : store) (C : context) (ais : List admininstr) (ft : functype)
    (hadmin : Instrs_ok2 s C ais ft) : t_progress_e_P0 s C ais ft hadmin :=
  Instrs_ok2.rec
    (t_progress_e_plain s) (t_progress_e_label s) (t_progress_e_Instr_ok2_frame s)
    (t_progress_e_call_addr s) (t_progress_e_ref s) (t_progress_e_trap s)
    (t_progress_e_empty s) (t_progress_e_instr s) (t_progress_e_seq s) (t_progress_e_sub s)
    (t_progress_e_Instrs_ok2_frame s) (t_progress_e_mk_Expr_ok2 s) hadmin

/- But in `t_progress_e` the recursor is in FUNCTION position (applied
   further to `f … hwf`), so there is no expected type to compute motive_2
   from: -/

/--
error: failed to elaborate eliminator, expected type is not available
-/
#guard_msgs in
example (s : store) (C framemoduleC : context) (f : frame) (vals : List val) (ais : List admininstr)
    (ft : functype) (vt1 vt2 : List valtype) (lab : List resulttype) (ret : Option resulttype)
    (hwf : wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)))
    (hadmin : Instrs_ok2 s C ais ft) :
    Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form ((List.map admininstr_val vals) ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais))
          (config.mk_config (state.mk_state s' f') ais') :=
  (Instrs_ok2.rec
    (t_progress_e_plain s) (t_progress_e_label s) (t_progress_e_Instr_ok2_frame s)
    (t_progress_e_call_addr s) (t_progress_e_ref s) (t_progress_e_trap s)
    (t_progress_e_empty s) (t_progress_e_instr s) (t_progress_e_seq s) (t_progress_e_sub s)
    (t_progress_e_Instrs_ok2_frame s) (t_progress_e_mk_Expr_ok2 s) hadmin) f framemoduleC vals vt1 vt2 lab ret hwf

/- Naming motive_2 alone is enough. Lean then elaborates the application
   normally, and solves motive_1 and motive_3 by unification against the case
   lemmas, which literally mention `t_progress_e_P s …` and `t_progress_e_P1 s …`.
   TypeProgress.lean names all three, which is clearer and doesn't depend on
   that unification succeeding: -/
example (s : store) (C framemoduleC : context) (f : frame) (vals : List val) (ais : List admininstr)
    (ft : functype) (vt1 vt2 : List valtype) (lab : List resulttype) (ret : Option resulttype)
    (hwf : wf_config (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais)))
    (hadmin : Instrs_ok2 s C ais ft) :
    Forall (fun val => wf_val val) vals →
    ft = mkFunctype vt1 vt2 →
    C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret →
    Moduleinst_ok s f.MODULE framemoduleC →
    List.map typeof vals = vt1 →
    Store_ok s →
    not_lf_br ais →
    not_lf_return ais →
    terminal_form ((List.map admininstr_val vals) ++ ais) ∨
      ∃ (s' : store) (f' : frame) (ais' : List admininstr),
        Step (config.mk_config (state.mk_state s f) ((List.map admininstr_val vals) ++ ais))
          (config.mk_config (state.mk_state s' f') ais') :=
  (Instrs_ok2.rec (motive_2 := t_progress_e_P0 s)
    (t_progress_e_plain s) (t_progress_e_label s) (t_progress_e_Instr_ok2_frame s)
    (t_progress_e_call_addr s) (t_progress_e_ref s) (t_progress_e_trap s)
    (t_progress_e_empty s) (t_progress_e_instr s) (t_progress_e_seq s) (t_progress_e_sub s)
    (t_progress_e_Instrs_ok2_frame s) (t_progress_e_mk_Expr_ok2 s) hadmin) f framemoduleC vals vt1 vt2 lab ret hwf

/- ═══════════════════════════════════════════════════════════════════════
   Part 7. WHY THESE MOTIVES? (the intuition)

   ─── 7.1 Why `Instrs_ok2.rec`, and why induct on the typing derivation ───
   The hypothesis to induct on is `hadmin : Instrs_ok2 s C ais ft`. Of the
   three sibling recursors, `Instrs_ok2.rec` is the one whose major premise
   has that type and whose result is motive_2, the statement about
   sequences, i.e. the theorem.
   Why the DERIVATION and not the list `ais`? The typing rules carry the
   information the proof needs: `seq` splits the list exactly where the types
   line up, `sub` changes the type without changing the list,
   `Instrs_ok2_frame` threads extra stack values through, and `label` / FRAME_
   bodies are typed in DIFFERENT contexts. Induction on the list would only
   give an IH for its tail, and nothing for a label's or a frame's body.

   ─── 7.2 Three motives: each one is "what the PARENT cases need as an IH" ───
   From 3.3:
     * P0 (motive_2) is the IH in `seq`, `sub`, `Instrs_ok2_frame` (sequences
       inside sequences), in `label` (continuation and body) and in
       `mk_Expr_ok2`. It is the theorem itself, generalized (7.3);
     * P (motive_1) is the IH only in `instr`, so it is chosen to make `instr`
       trivial (7.4);
     * P1 (motive_3) is the IH only in `Instr_ok2_frame`, so it is chosen to be
       exactly what the FRAME_ case needs (7.5).
   A motive that is too WEAK (say `fun _ _ _ _ => True`, as in I4) leaves
   the cases that use it as an IH unprovable; one that is too STRONG leaves
   its OWN cases unprovable. Each of the three is chosen from what its
   consumers need.

   ─── 7.3 P0, line by line ───
   (a) `∀ f framemoduleC vals vt1 vt2 lab ret` -- GENERALIZATION (I2, I5).
       The IHs are used at DIFFERENT values than the outer ones:
         seq              if the first half is already values `vs1`: ih2 at
                          `vals := vcs ++ vs1`; otherwise ih1 at the same `vals`
                                                        (TypeProgress.lean:7697, :7704)
         sub              `vt1 vt2 :=` the types before subsumption       (:7746)
         Instrs_ok2_frame `vals := vcs2`, the stack minus the frame part  (:7772)
         label (body)     `vals := []`, `lab :=` one more label           (:7406)
         Instr_ok2_frame  the INNER frame `f`, its module context, `ret := some _` (:7497)
         mk_Expr_ok2      a frame rebuilt from `Frame_ok`, `vals := []`, `lab := []`
                                                                           (:7817)
       Had any of the seven been fixed outside the motive, the matching IH
       would talk about the wrong values and be useless. `hwf`'s premise
       `wf_config …` mentions `f`, `vals` and `ais`, so it must sit after the
       `∀`s; that's why it is passed right after them.
   (b) `ft = mkFunctype vt1 vt2` and
       `C = upd_local_label_return framemoduleC (List.map typeof f.LOCALS) lab ret`
       -- INDEX EQUATIONS. The motive receives the indices as plain variables:
       it has to accept any derivation node, whose indices are things like
       `FT (t_lst ++ t_1_lst) (t_lst ++ t_2_lst)` or `{LABELS := ..} ++ C`. So
       what we know about their SHAPE is stated as equations, and each case
       re-establishes them for its children. E.g. `label` (whose proof calls
       `t'_lst` `t2`) proves, for its body,
       `{LABELS := [t2]} ++ C = upd_local_label_return C' … (t2 :: lab) ret`
       (:7398).
   (c) `wf_config (… ++ ais)`, `not_lf_br ais`, `not_lf_return ais` mention the
       index `ais`, so they MUST be inside the motive: a child derivation is
       about a different list, and the case has to re-prove these for it (e.g.
       `seq` splits `not_lf_br (es1 ++ es2)` in two). `Store_ok s` mentions
       only the parameter and could have stayed outside as a fixed
       hypothesis. It is inside to mirror Rocq's P0, which costs nothing.
   (d) The conclusion, `terminal_form (vals ++ ais) ∨ ∃ … Step …`: values on top
       of the stack are part of the configuration that is terminal or steps.

   ─── 7.4 P is P0 at `[ai]`, so `instr` is free ───
   `Instrs_ok2.instr` turns `Instr_ok2 … ai ft` into `Instrs_ok2 … [ai] ft`.
   With P chosen as "P0 with `ais := [ai]`", the IH and the goal of the `instr`
   case unfold to the same proposition: -/
example (s : store) (C : context) (v : admininstr) (t1 t2 : List valtype)
    (a : Instr_ok2 s C v (functype.mk_functype (.mk_list t1) (.mk_list t2)))
    (a1 : wf_store s) (a2 : wf_context C) (a3 : wf_admininstr v) :
    t_progress_e_P s C v _ a = t_progress_e_P0 s C [v] _ (Instrs_ok2.instr s C v t1 t2 a a1 a2 a3) :=
  rfl
/- which is why `t_progress_e_instr`'s proof is just `exact ih`
   (TypeProgress.lean:7642). The real work for single instructions
   (`plain`, `label`, FRAME_, `call_addr`, `ref`, `trap`) is then stated in the
   same "values, then the instruction" shape as for sequences.

   ─── 7.5 P1: what the FRAME_ case needs to know about its body ───
   A FRAME_ instruction `FRAME_ n f es` runs its body `es` from an EMPTY stack,
   under its OWN frame `f`, in that frame's context: no labels (the frame's
   module context `C'` has none) and `RETURN` set to the frame's result
   type. So P1 has:
     * no `vals`, and `wf_config` about `es` alone;
     * the context described by `Frame_ok s f framemoduleC` (the frame's
       locals are well-typed for its module) and
       `C = upd_return framemoduleC ret`, instead of P0's moduleinst equation;
     * a conclusion with three outcomes, one per way FRAME_ can step:
         - body is all values, AND exactly `|rt|` of them: `Step_pure.frame_vals`
           needs `n = |vals|` (:7508), and the case knows `n = |t_lst|`, so the
           length conjunct is precisely what lets it fire;
         - body is `[TRAP]`: `Step_pure.trap_frame`;
         - body steps: `Step.ctxt_frame`.
       (A body that is `vals ++ RETURN :: …` is dealt with by
       `Step_pure.return_frame` BEFORE the IH is used.)
   The one place P1 is PROVED is `mk_Expr_ok2`. It turns P0 (its IH) into P1:
   it unpacks `Frame_ok` to rebuild `C = upd_local_label_return C0 (locals) [] ret`,
   then calls the IH with `vals := []`, `lab := []`.

   ─── 7.6 Why 12 separate lemmas? ───
   The cases take from 2 to about 100 lines of proof each. As separate
   lemmas whose statements are copied from the recursor's type, they can be
   proved and checked one at a time, and the final assembly is a single
   application in which nothing but 5.5's unfolding happens. The `induction` versions in Part 6 are the
   other way to organize the same thing: the case proofs would go inside the
   12 alternatives.

   ═══════════════════════════════════════════════════════════════════════
   Part 8. CHEAT SHEET: recursor term ↔ `induction`

     direct term (TypeProgress, 5.8)        `induction` (6.2 / 6.4)
     ─────────────────────────────────────  ─────────────────────────────────────────────
     `Instrs_ok2.rec … hadmin`              `induction hadmin using Instrs_ok2.rec`
     `(motive_1 := t_progress_e_P s)`       the same, inside `using …`  (I4)
     `(motive_3 := t_progress_e_P1 s)`      the same, inside `using …`  (I4)
     `(motive_2 := t_progress_e_P0 s)`      NOT written: computed from the goal (I3), so the
                                            goal must look like P0's body first: revert
                                            `f framemoduleC vals vt1 vt2 lab ret hwf` one by
                                            one, or `generalizing` (which reverts `hwf` itself)
     12 minor arguments `(t_progress_e_X s)` 12 alternatives `| X names => exact t_progress_e_X s names`
     a minor's `∀`-variables, IHs last      the names after `| X`, IHs last
     `( … ) f framemoduleC … hwf`, once     after `revert`: the same, applied once at the end;
                                            with `generalizing`: re-`intro`duced in each
                                            alternative that concludes motive_2
     proof term                             the same `Instrs_ok2.rec` application, motive_2
                                            spelled out as a `fun`, alternatives as `fun`s (6.3)
-/

end TLC
