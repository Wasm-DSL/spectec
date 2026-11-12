# Part 0 — WASM 2.0 primer

> **About the code in this primer.** The primer quotes definitions to explain concepts, so many of its code blocks are *excerpts*: some are trimmed (`…` or a `-- ...` line marks an elision), some are lightly reformatted for readability, and some carry comments of mine (a `--` comment that does not appear in the linked source is an annotation). Blocks introduced with the word *verbatim* are exact. Every block links to its source lines. The theorem files `01`–`08`, by contrast, quote the source verbatim throughout — doc comments included — and are generated mechanically from it.

## 0.1 The execution model: one flat instruction list, rewritten in place

A running WASM program is a **stack machine**, but this formalization (like the official spec) encodes the stack *inside the instruction list itself*, rather than as a separate data structure. A value sitting "on the stack" is literally just a `CONST`/`VCONST`/ref-literal instruction sitting in the list, waiting to be consumed by the instruction to its right.

There are two instruction types: the surface syntax `instr` (what you'd write in a `.wat` file) and `admininstr` ("administrative instruction"), which is `instr` plus a handful of extra runtime-only forms. Execution only ever rewrites `List admininstr`.

**`instr`** — [wasm2.0.lean:1906-1974](../../../../../src/test-lean-claude/wasm2.0.lean#L1906-L1974) (68 constructors; excerpt — the `-- ...` lines mark elided groups):
```lean
inductive instr : Type where
  | NOP : instr
  | UNREACHABLE : instr
  | DROP : instr
  | SELECT (valtype_lst_opt : Option (List valtype)) : instr
  | BLOCK (v_blocktype : blocktype) (instr_lst : List instr) : instr
  | LOOP (v_blocktype : blocktype) (instr_lst : List instr) : instr
  | IFELSE (v_blocktype : blocktype) (instr_lst_0 : List instr) (instr_lst_1 : List instr) : instr
  | BR (v_labelidx : labelidx) : instr
  | BR_IF (v_labelidx : labelidx) : instr
  | BR_TABLE (labelidx_lst : List labelidx) (v_labelidx : labelidx) : instr
  | CALL (v_funcidx : funcidx) : instr
  | CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : instr
  | RETURN : instr
  | CONST (v_numtype : numtype) (_ : num_) : instr
  | UNOP (v_numtype : numtype) (_ : unop_) : instr
  | BINOP (v_numtype : numtype) (_ : binop_) : instr
  | TESTOP (v_numtype : numtype) (_ : testop_) : instr
  | RELOP (v_numtype : numtype) (_ : relop_) : instr
  -- ... (CVTOP/EXTEND and the full SIMD vector-instruction family: VCONST, VVUNOP,
  --      VBINOP, VSHUFFLE, VEXTRACT_LANE, VCVTOP, ... — same shape, numeric payload differs)
  | REF_NULL (v_reftype : reftype) : instr
  | REF_FUNC (v_funcidx : funcidx) : instr
  | REF_IS_NULL : instr
  | LOCAL_GET (v_localidx : localidx) : instr
  | LOCAL_SET (v_localidx : localidx) : instr
  | LOCAL_TEE (v_localidx : localidx) : instr
  | GLOBAL_GET (v_globalidx : globalidx) : instr
  | GLOBAL_SET (v_globalidx : globalidx) : instr
  | TABLE_GET (v_tableidx : tableidx) : instr
  | TABLE_SET (v_tableidx : tableidx) : instr
  | TABLE_SIZE (v_tableidx : tableidx) : instr
  | TABLE_GROW (v_tableidx : tableidx) : instr
  | TABLE_FILL (v_tableidx : tableidx) : instr
  | TABLE_COPY (v_tableidx_0 : tableidx) (v_tableidx_1 : tableidx) : instr
  | TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : instr
  | ELEM_DROP (v_elemidx : elemidx) : instr
  | LOAD (v_numtype : numtype) (_ : Option loadop_) (v_memarg : memarg) : instr
  | STORE (v_numtype : numtype) (sz_opt : Option sz) (v_memarg : memarg) : instr
  -- ... VLOAD/VLOAD_LANE/VSTORE/VSTORE_LANE (SIMD memory ops, same shape)
  | MEMORY_SIZE : instr
  | MEMORY_GROW : instr
  | MEMORY_FILL : instr
  | MEMORY_COPY : instr
  | MEMORY_INIT (v_dataidx : dataidx) : instr
  | DATA_DROP (v_dataidx : dataidx) : instr
deriving Inhabited, BEq
```
This is what you'd expect from a WASM instruction set: numeric ops, control flow (`BLOCK`/`LOOP`/`IFELSE`/`BR`/`BR_IF`/`BR_TABLE`/`CALL`/`RETURN`), locals/globals, tables, linear memory, and the "bulk memory"/SIMD extensions that WASM 2.0 added over 1.0.

**`admininstr`** — [wasm2.0.lean:11562-11636](../../../../../src/test-lean-claude/wasm2.0.lean#L11562-L11636) is *exactly* the same list, plus six extra constructors (74 in all) that only exist at runtime, never in source text:
```lean
inductive admininstr : Type where
  | NOP : admininstr
  -- ... every instr constructor again, verbatim ...
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : admininstr   -- a resolved function reference
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : admininstr   -- a resolved host (external) reference
  | CALL_ADDR (v_funcaddr : funcaddr) : admininstr       -- "call this concrete store address"
  | LABEL_ (v_n : n) (instr_lst : List instr) (admininstr_lst : List admininstr) : admininstr
  | FRAME_ (v_n : n) (v_frame : frame) (admininstr_lst : List admininstr) : admininstr
  | TRAP : admininstr
deriving Inhabited, BEq
```
Two helper coercions wrap plain data into this type so it can sit in the instruction list as a "value in disguise": `admininstr_val : val → admininstr` and `admininstr_ref : ref → admininstr` (and `admininstr_instr` lifts a plain `instr`). So `[CONST I32 5, CONST I32 7, ADD]` really is the list `[admininstr.CONST .I32 5, admininstr.CONST .I32 7, admininstr.BINOP .I32 .ADD]`, and "the stack has 5 and 7 on it" is just: those two constructors are sitting at the front of the list.

**`LABEL_` and `FRAME_` are how structured control flow becomes flat rewriting.** A `block`/`loop` doesn't nest the machine — it wraps its body in `LABEL_ n [continuation] [body]`, where `n` is the block's arity (how many result values it produces). `br k` searches outward through `k` enclosing `LABEL_`/`FRAME_` markers and, on finding its target, keeps only the top `n` values and throws away everything else inside that label — exactly the usual "unwind to a resumption point" operation, done here by literal list surgery. A function call wraps the callee's body in `FRAME_ n f [LABEL_ n [] [...callee instrs...]]`: the new `frame` carries the callee's locals and module instance, and `return`/falling off the end both unwind to the `FRAME_` marker the same way `br` unwinds to a `LABEL_`.

Concretely, from the real `Step_pure` rules (§0.7 below): the sequence
```
[LABEL_ 1 [] [CONST I32 5, CONST I32 7, BR 0]]
```
fires the `br_zero` rule (branching to the label 0 steps out directly) and rewrites in one step to
```
[CONST I32 7]
```
— the `5` (extra stuff below the branch's payload) is discarded, the `7` (the top 1 value, matching the label's arity `n=1`) survives, and the label marker itself vanishes. That's the entire mechanism behind `block`/`br`/`return`/`call` in this semantics: no separate control stack, just markers in the list and rules that know how to splice around them.

## 0.2 Runtime state: `store`, `frame`, `moduleinst`, `state`, `config`

```lean
structure moduleinst where       -- what a module's indices resolve to: store ADDRESSES
  MKmoduleinst ::
  TYPES : List functype
  FUNCS : List funcaddr
  GLOBALS : List globaladdr
  TABLES : List tableaddr
  MEMS : List memaddr
  ELEMS : List elemaddr
  DATAS : List dataaddr
  EXPORTS : List exportinst
```
([wasm2.0.lean:11373-11383](../../../../../src/test-lean-claude/wasm2.0.lean#L11373-L11383))

A `moduleinst` holds no data at all, only *addresses* — see the worked example of the
two-level lookup (`fun_global`) at the end of this section.

```lean
structure store where            -- the global heap: every allocated instance, by address
  MKstore ::
  FUNCS : List funcinst
  GLOBALS : List globalinst
  TABLES : List tableinst
  MEMS : List meminst
  ELEMS : List eleminst
  DATAS : List datainst
```
([wasm2.0.lean:11498-11506](../../../../../src/test-lean-claude/wasm2.0.lean#L11498-L11506)) — an "address" (`funcaddr`, `globaladdr`, ...) is just a `Nat` index into the matching list. `moduleinst` is the indirection layer: a module's local index `x` (e.g. "global #2 of *this* module") maps through `moduleinst.GLOBALS[x]` to a store address, which then indexes `store.GLOBALS` to get the actual `globalinst`. This is why you'll see chains like `s.GLOBALS[f.MODULE.GLOBALS[x]!]!` everywhere in the proofs below.

```lean
structure frame where             -- the currently-executing activation
  MKframe ::
  LOCALS : List val
  MODULE : moduleinst
```
([wasm2.0.lean:11529-11533](../../../../../src/test-lean-claude/wasm2.0.lean#L11529-L11533))

```lean
inductive state : Type where      -- store + frame together
  | mk_state (v_store : store) (v_frame : frame) : state

inductive config : Type where     -- state + the instruction list being executed
  | mk_config (v_state : state) (admininstr_lst : List admininstr) : config
```
([wasm2.0.lean:11547-11548](../../../../../src/test-lean-claude/wasm2.0.lean#L11547-L11548), [wasm2.0.lean:11957-11958](../../../../../src/test-lean-claude/wasm2.0.lean#L11957-L11958))

So a `config` is the entire machine state at one instant: *(store, frame, instruction list)*. `Step : config → config → Prop` is "one small-step rewrite of the whole machine." A `wf_*` sibling exists for each of these (`wf_store`, `wf_frame`, `wf_state`, `wf_config`) — see §0.4.

**The two-level address lookup, concretely.** Reading a global's value is:
```lean
def fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
  match v_state with
  | state.mk_state s f => (s.GLOBALS)[(f.MODULE.GLOBALS)[proj_uN_0 v_globalidx]!]!
```
([wasm2.0.lean:12203-12205](../../../../../src/test-lean-claude/wasm2.0.lean#L12203-L12205)) — read inside-out: `v_globalidx` is a **module-local index** (what `global.get 2` means in the bytecode — meaningless outside this one module); `f.MODULE.GLOBALS[v_globalidx]` translates that into a **store address** (a `globaladdr`, a different, global numbering shared across every module currently loaded); `s.GLOBALS[address]` is the actual memory access, landing on the real `globalinst`. A `moduleinst` is purely this one layer of pointers — it is what makes "global #2" mean something *for one particular module*; the `store` is where the global actually lives. This split is what lets two different modules import the *same* global (different local indices, same store address, same underlying `globalinst`), and it's exactly what `Moduleinst_ok`'s `Externaddr_ok` premises (§0.5) are checking: that every address a module's lookup tables point to really does resolve, in the store, to something of the declared type.

## 0.3 Static types: `valtype`, `resulttype`, `functype`, `context`

```lean
inductive valtype : Type where
  | I32 : valtype | I64 : valtype | F32 : valtype | F64 : valtype
  | V128 : valtype | FUNCREF : valtype | EXTERNREF : valtype
  | BOT : valtype      -- "unknown/unreachable" — the stack-polymorphism marker
```
([wasm2.0.lean:548-557](../../../../../src/test-lean-claude/wasm2.0.lean#L548-L557)) — the four number types, the 128-bit SIMD vector type, two reference types, and `BOT`. `BOT` exists because after `unreachable`/`br`/`return`, the type checker must accept *any* subsequent stack shape (the code is dead), and WASM's typing rules formalize that as a one-sided subtyping judgment against `BOT` rather than a special "stack-polymorphic" case; that's what all the `resulttype_sub`/`Val_ok_non_bot` lemmas you'll see cited are managing.

```lean
inductive list (X : Type) : Type where     -- a generic one-constructor wrapper
  | mk_list (X_lst : List X) : list X
abbrev resulttype : Type := list valtype
inductive functype : Type where
  | mk_functype (v_resulttype_0 : resulttype) (v_resulttype_1 : resulttype) : functype
```
([wasm2.0.lean:127-129](../../../../../src/test-lean-claude/wasm2.0.lean#L127-L129), [wasm2.0.lean:618](../../../../../src/test-lean-claude/wasm2.0.lean#L618), [wasm2.0.lean:718-720](../../../../../src/test-lean-claude/wasm2.0.lean#L718-L720)) — **a code-generation quirk worth knowing up front**: `resulttype` is *not* literally `List valtype`, it's this `list` newtype wrapping one. That's why code below is full of `obtain ⟨t1s⟩ := t1` (unwrapping a `resulttype` down to the bare `List valtype` it carries) and helpers like `mkFunctype t1s t2s := functype.mk_functype (.mk_list t1s) (.mk_list t2s)` ([Subtyping.lean:32](../../../../../src/test-lean-claude/Subtyping.lean#L32)). A `functype` is the usual `t1* → t2*` arrow type for instruction/function signatures.

```lean
structure context where           -- the STATIC twin of (moduleinst, frame) — types, not addresses
  MKcontext ::
  TYPES : List functype
  FUNCS : List functype          -- function TYPES this module's func indices resolve to
  GLOBALS : List globaltype
  TABLES : List tabletype
  MEMS : List memtype
  ELEMS : List elemtype
  DATAS : List datatype
  LOCALS : List valtype          -- types of the CURRENT locals (empty at module level)
  LABELS : List resulttype       -- arities of enclosing LABEL_s, innermost first
  RETURN : Option resulttype     -- arity of the enclosing FRAME_, if any
```
([wasm2.0.lean:12623-12634](../../../../../src/test-lean-claude/wasm2.0.lean#L12623-L12634)) — `context` is what the typing judgments below check instructions *against*, in the same way `moduleinst`/`frame` is what the `Step` relation executes *with*. `LOCALS`/`LABELS`/`RETURN` are exactly the pieces that change as you type-check your way into a block, a loop, or a function body; everything else is fixed by the enclosing module.

One recurring pairing you'll see constantly below: a proof carries **both** a `C` (the context matching the *runtime* `moduleinst`, via `Moduleinst_ok s f.MODULE C`) **and** a `C'` (the context the *typing derivation at hand* is actually stated against, via `Instrs_ok2 s C' ais ...`), connected by:
```lean
def inst_match (C C' : context) : Prop :=
  C.TYPES = C'.TYPES ∧ C.FUNCS = C'.FUNCS ∧ C.GLOBALS = C'.GLOBALS ∧ C.TABLES = C'.TABLES ∧
  C.MEMS = C'.MEMS ∧ C.ELEMS = C'.ELEMS ∧ C.DATAS = C'.DATAS
```
([TypingLemmas.lean:1886-1888](../../../../../src/test-lean-claude/TypingLemmas.lean#L1886-L1888)) — deliberately *excluding* `LOCALS`/`LABELS`/`RETURN`, since those legitimately differ (`C'` may be several blocks/calls deeper than `C`). `inst_match` is the bridge that lets a proof take a fact indexed by the module's own context `C` (e.g. "global 2's type, per the module instance") and use it against whatever deeply-nested `C'` the current instruction sequence is typed in.

## 0.4 Two families of judgment: `wf_*` (syntactic sanity) vs. `*_ok` (well-typed)

The development keeps two separate correctness notions, and it's easy to conflate them:
- **`wf_*`** (`wf_store`, `wf_config`, `wf_frame`, `wf_val`, `wf_admininstr`, ...) is cheap, structural well-formedness — things like "every byte is a valid byte," "a `CONST` instruction's payload actually fits its numtype's bit width." It carries no typing information.
- **`*_ok`** (`Store_ok`, `Config_ok`, `Val_ok`, `Moduleinst_ok`, ...) is the real **typing** judgment — "this store/value/instruction sequence is well-typed at such-and-such type." This is the family type *preservation* is actually about.

There is also a family of generated *well-formedness preservation* theorems — `Step_pure_is_wf`, `Step_read_is_wf`, and `Step_is_wf` ([wasm2.0.lean:16028-16049](../../../../../src/test-lean-claude/wasm2.0.lean#L16028-L16049) for the last two) — stating that the reduct of a step is again syntactically well-formed. The proofs in this walkthrough use them to get `wf` facts about reducts (`hwf'` in files `07` and `08`; `Step_is_wf` in files `01` and `06`). `Step_pure_is_wf` and `Step_is_wf` are proved; `Step_read_is_wf` is `sorry` (and `Admitted` in Rocq), and it is false in one corner case of the bulk memory operations (file `08` §8.11).

**What is and is not proved.** Walking each theorem's transitive dependencies in the compiled Lean environment, and collecting every declaration whose own proof contains `sorry`, gives:

| Theorem | Declarations it rests on that are `sorry` |
|---|---|
| `t_read_preservation` (file `08`) | 1 — `Step_read_is_wf` |
| `store_extension_reduce` (file `02`) | 4 — `nbytes__is_wf`, `ibytes__is_wf`, `vbytes__is_wf`, `wrap___is_wf` |
| `t_pure_preservation` (file `07`) | 29 numeric `*_is_wf` lemmas |
| `t_preservation_type` (file `06`), `t_preservation` (file `01`) | 33 — `Step_read_is_wf` plus 32 numeric/byte-encoding `*_is_wf` lemmas (the union of the rows above) |
| the seven store-writing lemmas and `Extend_store_refl` (file `02`), `reduce_inst_unchanged` (`03`), `Extend_store_moduleinst` (`04`), `t_preservation_vs_type` (`05`) | none — fully proved |

The 32 numeric lemmas each say that one of WASM's numeric primitives returns a well-formed result — for instance `wrap___is_wf`: wrapping an `M`-bit integer to `N` bits yields a valid `N`-bit integer; `nbytes__is_wf`: a number's byte encoding consists of valid bytes. They cannot be proved here because the primitives themselves (`wrap__`, `nbytes_`, `fadd_`, …) are generated as `opaque` — SpecTec's "axiom definitions", left uninterpreted by this backend — so there is no definition to reason from. They are assumptions about the numerics library, not gaps in the type-soundness argument.

<details>
<summary>How the table above was measured (a Lean script you can re-run)</summary>

Save this as a `.lean` file anywhere, then run `lake env lean <file>` from `spectec/src/test-lean-claude` (it loads the compiled modules, so it takes seconds, not a rebuild):

```lean
import TypePreservation
open Lean

/-- All constants reachable from `root` (through types and values) whose own type or value
    mentions `sorryAx` directly. -/
def sorryDeps (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut result : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    let exprs := match ci with
      | .thmInfo v => #[v.type, v.value]
      | .defnInfo v => #[v.type, v.value]
      | .opaqueInfo v => #[v.type, v.value]
      | _ => #[ci.type]
    let mut direct := false
    for e in exprs do
      for c in e.getUsedConstants do
        if c == ``sorryAx then direct := true
        else if !visited.contains c then stack := stack.push c
    if direct then result := result.push n
  return result

#eval show CoreM Unit from do
  let env ← getEnv
  for n in [``TLC.t_preservation, ``TLC.t_read_preservation] do
    IO.println s!"{n}: {sorryDeps env n}"
```

</details>

## 0.5 The typing judgments, concretely

**Values and references:**
```lean
inductive Val_ok : store → val → valtype → Prop where
  | numtype (s : store) (nt : numtype) (c_t : num_) :
    wf_store s → wf_val (val.CONST nt c_t) → Val_ok s (val.CONST nt c_t) (valtype_numtype nt)
  | vectype (s : store) (vt : vectype) (c_t : vec_) :
    wf_store s → wf_val (val.VCONST vt c_t) → Val_ok s (val.VCONST vt c_t) (valtype_vectype vt)
  | reftype (s : store) (r : ref) (rt : reftype) :
    Ref_ok s r rt → wf_store s → Val_ok s (val_ref r) (valtype_reftype rt)

inductive Ref_ok : store → ref → reftype → Prop where
  | null (s : store) (rt : reftype) : wf_store s → Ref_ok s (ref.REF_NULL rt) rt
  | func (s : store) (a : addr) (ext : functype) :
    Externaddr_ok s (externaddr.FUNC a) (externtype.FUNC ext) → wf_store s →
    wf_externtype (externtype.FUNC ext) → Ref_ok s (ref.REF_FUNC_ADDR a) reftype.FUNCREF
  | extern (s : store) (a : addr) : wf_store s → Ref_ok s (ref.REF_HOST_ADDR a) reftype.EXTERNREF
```
([wasm2.0.lean:15597-15609](../../../../../src/test-lean-claude/wasm2.0.lean#L15597-L15609), [wasm2.0.lean:15582-15593](../../../../../src/test-lean-claude/wasm2.0.lean#L15582-L15593)) — unsurprising: a number/vector constant is well-typed at its own type if it's `wf_val`; a reference is well-typed if it's null, or a function reference whose store address actually exists and has the claimed type, or an opaque host reference (always fine, since the host type is abstract).

```lean
def Vals_ok (v_S : store) (v_vals : List val) (v_ts : List valtype) : Prop :=
  v_ts.length = v_vals.length ∧ Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals
```
([TypingLemmas.lean:1775-1776](../../../../../src/test-lean-claude/TypingLemmas.lean#L1775-L1776)) — the lifting of `Val_ok` to lists (used for "the frame's locals are well-typed"). The explicit length conjunct is a Lean-only wrinkle: this file's generated `Forall₂` is zip-based and (unlike Rocq's inductive `Forall2`) doesn't by itself imply equal lengths, so it's threaded through by hand wherever indexing needs it.

**Module instances and activation records:**
```lean
inductive Moduleinst_ok : store → moduleinst → context → Prop where
  | mk_Moduleinst_ok (s) (functype_lst) (funcaddr_lst) (globaladdr_lst) (tableaddr_lst)
      (memaddr_lst) (elemaddr_lst) (dataaddr_lst) (exportinst_lst)
      (functype_F_lst) (globaltype_lst) (tabletype_lst) (memtype_lst) (elemtype_lst) (datatype_lst) :
    Forall (fun ft => Functype_ok ft) functype_lst →
    globaladdr_lst.length = globaltype_lst.length →
    Forall₂ (fun a t => Externaddr_ok s (externaddr.GLOBAL a) (externtype.GLOBAL t)) globaladdr_lst globaltype_lst →
    -- ... the same length+Forall₂ pair, once each, for FUNCS / MEMS / TABLES ...
    Forall (fun e => Exportinst_ok s e) exportinst_lst →
    dataaddr_lst.length = datatype_lst.length →
    Forall (fun a => a < s.DATAS.length) dataaddr_lst →
    Forall₂ (fun a t => Datainst_ok s (s.DATAS[a]!) t) dataaddr_lst datatype_lst →
    -- ... the same pair for ELEMS ...
    disjoint_ name (Map (fun e => e.NAME) exportinst_lst) →                    -- export names are unique
    (List.length (… all the addr lists concatenated as externaddrs …)) > 0 →   -- ("$moduleinst_is_ok", a nonemptiness side-condition)
    Forall (fun e => List.contains (… those externaddrs …) e.ADDR) exportinst_lst →  -- exports point somewhere real
    wf_store s → wf_moduleinst ({ TYPES := functype_lst, FUNCS := funcaddr_lst, … }) →
    wf_context ({ TYPES := functype_lst, FUNCS := functype_F_lst, …, LOCALS := [], LABELS := [], RETURN := none }) →
    Forall (fun t => wf_externtype (externtype.GLOBAL t)) globaltype_lst →
    -- ... same wf_externtype Forall for FUNC/MEM/TABLE ...
    Moduleinst_ok s ({ TYPES := functype_lst, FUNCS := funcaddr_lst, GLOBALS := globaladdr_lst,
                        TABLES := tableaddr_lst, MEMS := memaddr_lst, ELEMS := elemaddr_lst,
                        DATAS := dataaddr_lst, EXPORTS := exportinst_lst })
                      ({ TYPES := functype_lst, FUNCS := functype_F_lst, GLOBALS := globaltype_lst,
                         TABLES := tabletype_lst, MEMS := memtype_lst, ELEMS := elemtype_lst,
                         DATAS := datatype_lst, LOCALS := [], LABELS := [], RETURN := none })
```
(lightly reformatted for space; full text at [wasm2.0.lean:15671-15739](../../../../../src/test-lean-claude/wasm2.0.lean#L15671-L15739)) — in plain terms: *every address this module instance holds actually resolves, in the store, to something of the type the module's static signature promised.* That's it, just repeated once per sort (globals/funcs/mems/tables/elems/datas), plus "export names are unique and point at a real address."

```lean
inductive Frame_ok : store → frame → context → Prop where
  | mk_Frame_ok (s) (val_lst) (v_moduleinst) (t_lst) (C) :
    Moduleinst_ok s v_moduleinst C →
    t_lst.length = val_lst.length →
    Forall₂ (fun t v => Val_ok s v t) t_lst val_lst →
    wf_store s → wf_context C → wf_frame ({ LOCALS := val_lst, MODULE := v_moduleinst }) →
    wf_context ({ …, LOCALS := t_lst, LABELS := [], RETURN := none }) →
    Frame_ok s ({ LOCALS := val_lst, MODULE := v_moduleinst })
               (({ …, LOCALS := t_lst, LABELS := [], RETURN := none } : context) ++ C)
```
([wasm2.0.lean:15743-15780](../../../../../src/test-lean-claude/wasm2.0.lean#L15743-L15780)) — a frame is `Frame_ok` at the context `(locals-only context) ++ C` exactly when its module instance is `Moduleinst_ok` at `C` *and* its locals are well-typed at the claimed local types. This is precisely "`Frame_ok`, locals typed" from the diagram's first line.

**Instructions, instruction sequences, expressions** (mutually recursive — a block's body is `Instrs_ok2`, which needs `Instr_ok2` for a `LABEL_`, which needs `Instrs_ok2` again...):
```lean
mutual
inductive Instr_ok2 : store → context → admininstr → functype → Prop where
  | plain (s C v_instr t_1_lst t_2_lst) :
    Instr_ok C v_instr (mkFunctype t_1_lst t_2_lst) →   -- delegates PLAIN instrs to the (huge, static) `Instr_ok`
    wf_store s → wf_context C → wf_instr v_instr →
    Instr_ok2 s C (admininstr_instr v_instr) (mkFunctype t_1_lst t_2_lst)
  | label (s C v_n instr'_lst admininstr_lst t_lst t'_lst) :
    Instrs_ok2 s C (Map admininstr_instr instr'_lst) (mkFunctype t'_lst t_lst) →
    Instrs_ok2 s ({ …, LABELS := [.mk_list t'_lst] } ++ C) admininstr_lst (mkFunctype [] t_lst) →
    wf_store s → wf_context C → wf_admininstr (admininstr.LABEL_ v_n instr'_lst admininstr_lst) →
    wf_context ({ …, LABELS := [.mk_list t'_lst] }) → v_n = t'_lst.length →
    Instr_ok2 s C (admininstr.LABEL_ v_n instr'_lst admininstr_lst) (mkFunctype [] t_lst)
  | Instr_ok2_frame (s C v_n f admininstr_lst t_lst C') :
    Frame_ok s f C' →
    Expr_ok2 s ({ …, RETURN := some (.mk_list t_lst) } ++ C') admininstr_lst (.mk_list t_lst) →
    wf_store s → wf_context C → wf_context C' → wf_admininstr (admininstr.FRAME_ v_n f admininstr_lst) →
    wf_context ({ …, RETURN := some (.mk_list t_lst) }) → v_n = t_lst.length →
    Instr_ok2 s C (admininstr.FRAME_ v_n f admininstr_lst) (mkFunctype [] t_lst)
  | call_addr (s C v_funcaddr t_1_lst t_2_lst) :
    Externaddr_ok s (externaddr.FUNC v_funcaddr) (externtype.FUNC (mkFunctype t_1_lst t_2_lst)) →
    wf_store s → wf_context C → wf_admininstr (admininstr.CALL_ADDR v_funcaddr) →
    wf_externtype (externtype.FUNC (mkFunctype t_1_lst t_2_lst)) →
    Instr_ok2 s C (admininstr.CALL_ADDR v_funcaddr) (mkFunctype t_1_lst t_2_lst)
  | ref (s C v_ref rt) :
    Ref_ok s v_ref rt → wf_store s → wf_context C →
    Instr_ok2 s C (admininstr_ref v_ref) (mkFunctype [] [valtype_reftype rt])
  | trap (s C t_1_lst t_2_lst) :
    wf_store s → wf_context C → wf_admininstr admininstr.TRAP →
    Instr_ok2 s C admininstr.TRAP (mkFunctype t_1_lst t_2_lst)   -- TRAP types at ANY signature

inductive Instrs_ok2 : store → context → List admininstr → functype → Prop where
  | empty (s C) : wf_store s → wf_context C → Instrs_ok2 s C [] (mkFunctype [] [])
  | instr (s C v_admininstr t_1_lst t_2_lst) :
    Instr_ok2 s C v_admininstr (mkFunctype t_1_lst t_2_lst) → wf_store s → wf_context C →
    wf_admininstr v_admininstr → Instrs_ok2 s C [v_admininstr] (mkFunctype t_1_lst t_2_lst)
  | seq (s C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst) :
    Instrs_ok2 s C admininstr_1_lst (mkFunctype t_1_lst t_2_lst) →
    Instrs_ok2 s C admininstr_2_lst (mkFunctype t_2_lst t_3_lst) →   -- sequencing: types must CHAIN
    wf_store s → wf_context C → Forall wf_admininstr admininstr_1_lst → Forall wf_admininstr admininstr_2_lst →
    Instrs_ok2 s C (admininstr_1_lst ++ admininstr_2_lst) (mkFunctype t_1_lst t_3_lst)
  | sub (s C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst) :
    Instrs_ok2 s C admininstr_lst (mkFunctype t_1_lst t_2_lst) →
    Resulttype_sub (.mk_list t'_1_lst) (.mk_list t_1_lst) → Resulttype_sub (.mk_list t_2_lst) (.mk_list t'_2_lst) →
    wf_store s → wf_context C → Forall wf_admininstr admininstr_lst →
    Instrs_ok2 s C admininstr_lst (mkFunctype t'_1_lst t'_2_lst)        -- ordinary subtyping/weakening
  | Instrs_ok2_frame (s C admininstr_lst t_lst t_1_lst t_2_lst) :
    Instrs_ok2 s C admininstr_lst (mkFunctype t_1_lst t_2_lst) → wf_store s → wf_context C →
    Forall wf_admininstr admininstr_lst →
    Instrs_ok2 s C admininstr_lst (mkFunctype (t_lst ++ t_1_lst) (t_lst ++ t_2_lst))  -- stack-prefix framing

inductive Expr_ok2 : store → context → adminexpr → resulttype → Prop where
  | mk_Expr_ok2 (s C admininstr_lst t_lst) :
    Instrs_ok2 s C admininstr_lst (mkFunctype [] t_lst) → wf_store s → wf_context C →
    Forall wf_admininstr admininstr_lst → Expr_ok2 s C admininstr_lst (.mk_list t_lst)
end
```
(reformatted for space; full text at [wasm2.0.lean:15785-15915](../../../../../src/test-lean-claude/wasm2.0.lean#L15785-L15915)) — this is ordinary sequent-style instruction typing: one instruction has a `functype` (`plain` just defers to the big static `Instr_ok` judgment for everything that isn't administrative); a sequence's type is the composition of its pieces' types (`seq`); you can always weaken via subtyping (`sub`) or add a matching stack prefix to both sides (`Instrs_ok2_frame`); and an `Expr_ok2` is just an `Instrs_ok2` with an empty input type (a *complete* program fragment, consuming nothing). `LABEL_`/`FRAME_`/`CALL_ADDR`/bare values/`TRAP` get their own `Instr_ok2` rules because they're administrative — they don't exist in `Instr_ok`, the plain-syntax judgment.

**The store itself:**
```lean
inductive Store_ok : store → Prop where
  | mk_Store_ok (s) (globalinst_lst globaltype_lst) (meminst_lst memtype_lst)
      (tableinst_lst tabletype_lst) (funcinst_lst functype_lst)
      (datainst_lst datatype_lst) (eleminst_lst elemtype_lst) :
    globalinst_lst.length = globaltype_lst.length →
    Forall₂ (fun v t => Globalinst_ok s v t) globalinst_lst globaltype_lst →
    meminst_lst.length = memtype_lst.length → Forall₂ (fun v t => Meminst_ok s v t) meminst_lst memtype_lst →
    tableinst_lst.length = tabletype_lst.length → Forall₂ (fun v t => Tableinst_ok s v t) tableinst_lst tabletype_lst →
    funcinst_lst.length = functype_lst.length → Forall₂ (fun v t => Funcinst_ok s v t) funcinst_lst functype_lst →
    datainst_lst.length = datatype_lst.length → Forall₂ (fun v t => Datainst_ok s v t) datainst_lst datatype_lst →
    eleminst_lst.length = elemtype_lst.length → Forall₂ (fun v t => Eleminst_ok s v t) eleminst_lst elemtype_lst →
    s = ({ FUNCS := funcinst_lst, GLOBALS := globalinst_lst, TABLES := tableinst_lst,
           MEMS := meminst_lst, ELEMS := eleminst_lst, DATAS := datainst_lst }) →
    wf_store s → Forall wf_memtype memtype_lst → Forall wf_tabletype tabletype_lst →
    wf_store ({ FUNCS := funcinst_lst, GLOBALS := globalinst_lst, TABLES := tableinst_lst,
                MEMS := meminst_lst, ELEMS := eleminst_lst, DATAS := datainst_lst }) →
    Store_ok s
```
([wasm2.0.lean:15992-16025](../../../../../src/test-lean-claude/wasm2.0.lean#L15992-L16025)) — "every instance in every one of the six store components is well-typed at *some* type, and all those per-component types exist." The six component judgments it bottoms out at are all one-liners of the same shape as `Val_ok.numtype`, e.g.:
```lean
inductive Globalinst_ok : store → globalinst → globaltype → Prop where
  | mk_Globalinst_ok (s mut t v_val) :
    Globaltype_ok (globaltype.mk_globaltype mut t) → Val_ok s v_val t → wf_store s →
    wf_globalinst (…) → Globalinst_ok s (…) (globaltype.mk_globaltype mut t)
-- Meminst_ok / Tableinst_ok / Funcinst_ok: same pattern — the *_type_ok check, plus
-- (for tables/mems) `Forall (Ref_ok ...)` or a byte-length match, plus (for funcs)
-- `Moduleinst_ok` on its closed-over module instance and `Func_ok` on its code.
```
([wasm2.0.lean:15921-15988](../../../../../src/test-lean-claude/wasm2.0.lean#L15921-L15988))

**Packaging it all up:**
```lean
inductive State_ok : state → context → Prop where
  | mk_State_ok (s f C) : Store_ok s → Frame_ok s f C → wf_context C → wf_state (state.mk_state s f) →
    State_ok (state.mk_state s f) C

inductive Config_ok : config → resulttype → Prop where
  | mk_Config_ok (s f admininstr_lst t_lst C) :
    State_ok (state.mk_state s f) C → Expr_ok2 s C admininstr_lst (.mk_list t_lst) → wf_context C →
    wf_config (config.mk_config (state.mk_state s f) admininstr_lst) → wf_state (state.mk_state s f) →
    Config_ok (config.mk_config (state.mk_state s f) admininstr_lst) (.mk_list t_lst)
```
([wasm2.0.lean:16315-16331](../../../../../src/test-lean-claude/wasm2.0.lean#L16315-L16331)) — `Config_ok c ts` is literally: the store is `Store_ok`, the frame is `Frame_ok` (which bundles `Moduleinst_ok` + typed locals), and the instruction list is `Expr_ok2`-typed at `ts`, all against one shared context `C`. **This is exactly "Unpacks `Config_ok` → `State_ok` → `Store_ok` + `Frame_ok` (`Moduleinst_ok`, locals typed) + `Expr_ok2` (`Instrs_ok2`)"** from the top of the diagram.

## 0.6 Store growth: `Extend_store`

Executing an instruction can *allocate* (e.g. `memory.grow`) but a closed WASM program never *deletes* anything from the store, and never shrinks it. "Preservation across a step" therefore needs a second invariant beyond "still well-typed": the new store must be a **growth** of the old one. That's `Extend_store`:
```lean
inductive Extend_store : store → store → Prop where
  | mk_Extend_store (s s') :
    Forall (fun a => a < s.GLOBALS.length) (List.range s.GLOBALS.length) →
    Forall (fun a => a < s'.GLOBALS.length) (List.range s.GLOBALS.length) →          -- s' has ≥ as many globals
    Forall (fun a => Extend_globalinst (s.GLOBALS[a]!) (s'.GLOBALS[a]!)) (List.range s.GLOBALS.length) →
    -- ... the identical three-line shape, once each, for MEMS / TABLES / FUNCS / DATAS / ELEMS ...
    wf_store s → wf_store s' → Extend_store s s'
```
([wasm2.0.lean:16289-16311](../../../../../src/test-lean-claude/wasm2.0.lean#L16289-L16311)) — every existing address is still a valid address in the new store, *and* the old and new instance at that address are related by a per-sort "extension" relation:
```lean
inductive Extend_globalinst : globalinst → globalinst → Prop where
  | mk_Extend_globalinst (mut t v_val val') :
    (mut = some r_MUT.MUT) ∨ (v_val = val') →     -- mutable globals may change value; immutable ones CANNOT
    …  → Extend_globalinst (…VALUE:=v_val…) (…VALUE:=val'…)

inductive Extend_meminst : meminst → meminst → Prop where
  | mk_Extend_meminst (n m_opt b_lst n' b'_lst) :
    n ≤ n' → b_lst.length ≤ b'_lst.length →        -- memory only ever GROWS (page count, byte count)
    …  → Extend_meminst (…TYPE:=PAGE n…, BYTES:=b_lst…) (…TYPE:=PAGE n'…, BYTES:=b'_lst…)

inductive Extend_tableinst : tableinst → tableinst → Prop where      -- same shape: tables only grow
  | mk_Extend_tableinst (n m_opt rt ref_lst n' ref'_lst) :
    n ≤ n' → ref_lst.length ≤ ref'_lst.length → … → Extend_tableinst (…) (…)

inductive Extend_funcinst : funcinst → funcinst → Prop where         -- funcs are IMMUTABLE once allocated
  | mk_Extend_funcinst (ft mm fc) : wf_funcinst (…) → Extend_funcinst (…TYPE:=ft,MODULE:=mm,CODE:=fc…) (…same…)

inductive Extend_datainst : datainst → datainst → Prop where         -- a data segment can only be data.drop'd
  | mk_Extend_datainst (b_lst b'_lst) : (b_lst = b'_lst) ∨ (b'_lst = []) → … → Extend_datainst (…) (…)

inductive Extend_eleminst : eleminst → eleminst → Prop where         -- same: only elem.drop, i.e. → []
  | mk_Extend_eleminst (rt ref_lst ref'_lst) : (ref_lst = ref'_lst) ∨ (ref'_lst = []) → Extend_eleminst (…) (…)
```
([wasm2.0.lean:16175-16282](../../../../../src/test-lean-claude/wasm2.0.lean#L16175-L16282)) — this precisely encodes WASM's allocation discipline: tables/memories only grow and keep their old contents as a prefix; mutable globals can change, immutable ones are frozen; functions, once allocated, never change at all; element/data segments are immutable except for the one-way "drop" operation that zeroes them out. Every store-writing `Step` rule has a matching proof that its particular write respects exactly one of these five shapes — that's what the seven "store-writing lemmas" in file `02` are each individually proving.

## 0.7 The reduction relation: `Step`, `Step_pure`, `Step_read`

The dynamics are split into three relations, and the split is exactly why the big proofs below are structured the way they are:

- **`Step_pure : List admininstr → List admininstr → Prop`** — rules that rewrite the instruction list *without consulting the store or frame at all*: arithmetic, `drop`/`select`/`if`, branch/return bookkeeping, trap propagation. Store-independent and frame-independent.
- **`Step_read : config → List admininstr → Prop`** — rules that *read* the store/frame (table/global/local lookups, function calls, SIMD/scalar loads) but never write them.
- **`Step : config → config → Prop`** — the full relation: it *lifts* both smaller relations in (via the `pure`/`read` constructors below), adds the **congruence rules** that let a step happen underneath a `LABEL_`/`FRAME_`/a value-and-tail-instruction prefix, and adds every rule that actually **writes** the store (`global.set`, `table.set`, `table.grow`, `elem.drop`, the memory-store family, `memory.grow`, `data.drop`).

The `Step` definition, all 23 constructors, with long side conditions abbreviated to `…` — [wasm2.0.lean:14699-14797](../../../../../src/test-lean-claude/wasm2.0.lean#L14699-L14797):
```lean
inductive Step : config → config → Prop where
  | pure (z admininstr_lst admininstr'_lst) :
    Step_pure admininstr_lst admininstr'_lst →
    Step (config.mk_config z admininstr_lst) (config.mk_config z admininstr'_lst)
  | read (z admininstr_lst admininstr'_lst) :
    Step_read (config.mk_config z admininstr_lst) admininstr'_lst →
    Step (config.mk_config z admininstr_lst) (config.mk_config z admininstr'_lst)
  | ctxt_label (z v_n instr_0_lst admininstr_lst z' admininstr'_lst) :
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    wf_config (…) → wf_config (…) →
    Step (config.mk_config z [admininstr.LABEL_ v_n instr_0_lst admininstr_lst])
         (config.mk_config z' [admininstr.LABEL_ v_n instr_0_lst admininstr'_lst])
  | ctxt_frame (s f v_n f' admininstr_lst s' f'' admininstr'_lst) :
    Step (config.mk_config (state.mk_state s f') admininstr_lst) (config.mk_config (state.mk_state s' f'') admininstr'_lst) →
    wf_config (…) → wf_config (…) →
    Step (config.mk_config (state.mk_state s f) [admininstr.FRAME_ v_n f' admininstr_lst])
         (config.mk_config (state.mk_state s' f) [admininstr.FRAME_ v_n f'' admininstr'_lst])
  | ctxt_instrs (z val_lst admininstr_lst admininstr_1_lst z' admininstr'_lst) :
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    (val_lst ≠ []) ∨ (admininstr_1_lst ≠ []) → wf_config (…) → wf_config (…) →
    Step (config.mk_config z ((Map admininstr_val val_lst) ++ (admininstr_lst ++ admininstr_1_lst)))
         (config.mk_config z' ((Map admininstr_val val_lst) ++ (admininstr'_lst ++ admininstr_1_lst)))
  -- the store-writing rules (detailed with their preservation proofs in 02-store-extension-reduce.md):
  | local_set (z v_val x) : Step (… [admininstr_val v_val, .LOCAL_SET x]) (config.mk_config (with_local z x v_val) [])
  | global_set (z v_val x) : Step (… [admininstr_val v_val, .GLOBAL_SET x]) (config.mk_config (with_global z x v_val) [])
  | table_set_trap (z i v_ref x) : (proj_num__0 i) ≠ none → (… i's index) ≥ (… table length) →
    Step (… [.CONST .I32 i, admininstr_ref v_ref, .TABLE_SET x]) (config.mk_config z [.TRAP])
  | table_set_val (z i v_ref x) : (proj_num__0 i) ≠ none → (… i's index) < (… table length) →
    Step (… [.CONST .I32 i, admininstr_ref v_ref, .TABLE_SET x]) (config.mk_config (with_table z x _ v_ref) [])
  | table_grow_succeed (z v_ref v_n x ti var_0) : fun_growtable (fun_table z x) v_n v_ref var_0 → var_0 ≠ none →
    Option.get! var_0 = ti → Step (…) (config.mk_config (with_tableinst z x ti) [.CONST .I32 (… new size)])
  | table_grow_fail (z v_ref v_n x var_0) : fun_inv_signed_ 32 (-1) var_0 → Step (…) (config.mk_config z [.CONST .I32 var_0])
  | elem_drop (z x) : Step (… [.ELEM_DROP x]) (config.mk_config (with_elem z x []) [])
  | store_num_trap (z i nt c ao) : … (out of bounds) … → Step (…) (config.mk_config z [.TRAP])
  | store_num_val (z i nt c ao b_lst) : … → b_lst = nbytes_ nt c → Step (…) (config.mk_config (with_mem z 0 _ _ b_lst) [])
  | store_pack_trap (z i v_Inn c v_n ao) : … → Step (…) (config.mk_config z [.TRAP])
  | store_pack_val (z i v_Inn c v_n ao b_lst) : … → Step (…) (config.mk_config (with_mem z 0 _ _ b_lst) [])
  | vstore_oob (z i c ao) : … → Step (…) (config.mk_config z [.TRAP])
  | vstore_val (z i c ao b_lst) : … → Step (…) (config.mk_config (with_mem z 0 _ _ b_lst) [])
  | vstore_lane_oob (z i c v_N ao j) : … → Step (…) (config.mk_config z [.TRAP])
  | vstore_lane_val (z i c v_N ao j b_lst v_Jnn v_M) : … → Step (…) (config.mk_config (with_mem z 0 _ _ b_lst) [])
  | memory_grow_succeed (z v_n mi var_0) : fun_growmemory (fun_mem z 0) v_n var_0 → var_0 ≠ none → Option.get! var_0 = mi →
    Step (…) (config.mk_config (with_meminst z 0 mi) [.CONST .I32 (… new page count)])
  | memory_grow_fail (z v_n var_0) : fun_inv_signed_ 32 (-1) var_0 → Step (…) (config.mk_config z [.CONST .I32 var_0])
  | data_drop (z x) : Step (… [.DATA_DROP x]) (config.mk_config (with_data z x []) [])
```
(abbreviated side-conditions for space; the exact text follows)

<details>
<summary>The <code>Step</code> definition, verbatim (wasm2.0.lean, lines 14698–14797)</summary>

```lean
/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 -/
inductive Step : config → config → Prop where
  | pure (z : state) (admininstr_lst : List admininstr) (admininstr'_lst : List admininstr) :
    Step_pure admininstr_lst admininstr'_lst →
    Step (config.mk_config z admininstr_lst) (config.mk_config z admininstr'_lst)
  | read (z : state) (admininstr_lst : List admininstr) (admininstr'_lst : List admininstr) :
    Step_read (config.mk_config z admininstr_lst) admininstr'_lst →
    Step (config.mk_config z admininstr_lst) (config.mk_config z admininstr'_lst)
  | ctxt_label (z : state) (v_n : n) (instr_0_lst : List instr) (admininstr_lst : List admininstr) (z' : state) (admininstr'_lst : List admininstr) :
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z' admininstr'_lst) →
    Step (config.mk_config z [admininstr.LABEL_ v_n instr_0_lst admininstr_lst]) (config.mk_config z' [admininstr.LABEL_ v_n instr_0_lst admininstr'_lst])
  | ctxt_frame (s : store) (f : frame) (v_n : n) (f' : frame) (admininstr_lst : List admininstr) (s' : store) (f'' : frame) (admininstr'_lst : List admininstr) :
    Step (config.mk_config (state.mk_state s f') admininstr_lst) (config.mk_config (state.mk_state s' f'') admininstr'_lst) →
    wf_config (config.mk_config (state.mk_state s f') admininstr_lst) →
    wf_config (config.mk_config (state.mk_state s' f'') admininstr'_lst) →
    Step (config.mk_config (state.mk_state s f) [admininstr.FRAME_ v_n f' admininstr_lst]) (config.mk_config (state.mk_state s' f) [admininstr.FRAME_ v_n f'' admininstr'_lst])
  | ctxt_instrs (z : state) (val_lst : List val) (admininstr_lst : List admininstr) (admininstr_1_lst : List admininstr) (z' : state) (admininstr'_lst : List admininstr) :
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    (val_lst ≠ []) ∨ (admininstr_1_lst ≠ []) →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z' admininstr'_lst) →
    Step (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (admininstr_lst ++ admininstr_1_lst))) (config.mk_config z' ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (admininstr'_lst ++ admininstr_1_lst)))
  | local_set (z : state) (v_val : val) (x : idx) : Step (config.mk_config z [admininstr_val v_val, admininstr.LOCAL_SET x]) (config.mk_config (with_local z x v_val) [])
  | global_set (z : state) (v_val : val) (x : idx) : Step (config.mk_config z [admininstr_val v_val, admininstr.GLOBAL_SET x]) (config.mk_config (with_global z x v_val) [])
  | table_set_trap (z : state) (i : num_) (v_ref : ref) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) ≥ (List.length ((fun_table z x).REFS)) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_ref v_ref, admininstr.TABLE_SET x]) (config.mk_config z [admininstr.TRAP])
  | table_set_val (z : state) (i : num_) (v_ref : ref) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_ref v_ref, admininstr.TABLE_SET x]) (config.mk_config (with_table z x (proj_uN_0 (Option.get! (proj_num__0 i))) v_ref) [])
  | table_grow_succeed (z : state) (v_ref : ref) (v_n : n) (x : idx) (ti : tableinst) (var_0 : Option tableinst) :
    fun_growtable (fun_table z x) v_n v_ref var_0 →
    var_0 ≠ none →
    (Option.get! var_0) = ti →
    Step (config.mk_config z [admininstr_ref v_ref, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_GROW x]) (config.mk_config (with_tableinst z x ti) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (List.length ((fun_table z x).REFS))))])
  | table_grow_fail (z : state) (v_ref : ref) (v_n : n) (x : idx) (var_0 : Nat) :
    fun_inv_signed_ 32 (- (1 : Int)) var_0 →
    Step (config.mk_config z [admininstr_ref v_ref, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_GROW x]) (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN var_0))])
  | elem_drop (z : state) (x : idx) : Step (config.mk_config z [admininstr.ELEM_DROP x]) (config.mk_config (with_elem z x []) [])
  | store_num_trap (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST nt c, admininstr.STORE nt none ao]) (config.mk_config z [admininstr.TRAP])
  | store_num_val (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) (b_lst : List byte) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    b_lst = (nbytes_ nt c) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST nt c, admininstr.STORE nt none ao]) (config.mk_config (with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))) b_lst) [])
  | store_pack_trap (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_n : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST (numtype_Inn v_Inn) c, admininstr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) (config.mk_config z [admininstr.TRAP])
  | store_pack_val (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) (b_lst : List byte) :
    (proj_num__0 i) ≠ none →
    (size (valtype_Inn v_Inn)) ≠ none →
    (proj_num__0 c) ≠ none →
    b_lst = (ibytes_ v_n (wrap__ (Option.get! (size (valtype_Inn v_Inn))) v_n (Option.get! (proj_num__0 c)))) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST (numtype_Inn v_Inn) c, admininstr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) (config.mk_config (with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat ((v_n : Rat) / (8 : Rat))) b_lst) [])
  | vstore_oob (z : state) (i : num_) (c : vec_) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE vectype.V128 ao]) (config.mk_config z [admininstr.TRAP])
  | vstore_val (z : state) (i : num_) (c : vec_) (ao : memarg) (b_lst : List byte) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    b_lst = (vbytes_ vectype.V128 c) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE vectype.V128 ao]) (config.mk_config (with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat))) b_lst) [])
  | vstore_lane_oob (z : state) (i : num_) (c : vec_) (v_N : N) (ao : memarg) (j : laneidx) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + v_N) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) ao j]) (config.mk_config z [admininstr.TRAP])
  | vstore_lane_val (z : state) (i : num_) (c : vec_) (v_N : N) (ao : memarg) (j : laneidx) (b_lst : List byte) (v_Jnn : Jnn) (v_M : M) :
    (proj_num__0 i) ≠ none →
    v_N = (jsize v_Jnn) →
    (v_M : Rat) = ((128 : Rat) / (v_N : Rat)) →
    (proj_lane__0 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!)) ≠ none →
    (proj_uN_0 j) < (List.length (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)) →
    b_lst = (ibytes_ v_N (uN.mk_uN (proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!)))))) →
    wf_uN v_N (uN.mk_uN (proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!))))) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) ao j]) (config.mk_config (with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat ((v_N : Rat) / (8 : Rat))) b_lst) [])
  | memory_grow_succeed (z : state) (v_n : n) (mi : meminst) (var_0 : Option meminst) :
    fun_growmemory (fun_mem z (uN.mk_uN 0)) v_n var_0 →
    var_0 ≠ none →
    (Option.get! var_0) = mi →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_GROW]) (config.mk_config (with_meminst z (uN.mk_uN 0) mi) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (rat_to_nat (((List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) : Rat) / ((64 * Ki) : Rat)))))])
  | memory_grow_fail (z : state) (v_n : n) (var_0 : Nat) :
    fun_inv_signed_ 32 (- (1 : Int)) var_0 →
    Step (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_GROW]) (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN var_0))])
  | data_drop (z : state) (x : idx) : Step (config.mk_config z [admininstr.DATA_DROP x]) (config.mk_config (with_data z x []) [])
```

</details>

A `Step_pure` excerpt, verbatim — the first 22 of its 54 constructors ([wasm2.0.lean:13743-13805](../../../../../src/test-lean-claude/wasm2.0.lean#L13743-L13805); the whole definition is [wasm2.0.lean:13744-13995](../../../../../src/test-lean-claude/wasm2.0.lean#L13744-L13995)):
```lean
/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.109 -/
inductive Step_pure : List admininstr → List admininstr → Prop where
  | unreachable : Step_pure [admininstr.UNREACHABLE] [admininstr.TRAP]
  | nop : Step_pure [admininstr.NOP] []
  | drop (v_val : val) : Step_pure [admininstr_val v_val, admininstr.DROP] []
  | select_true (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : Option (List valtype)) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0 →
    Step_pure [admininstr_val val_1, admininstr_val val_2, admininstr.CONST numtype.I32 c, admininstr.SELECT t_lst_opt] [admininstr_val val_1]
  | select_false (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : Option (List valtype)) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) = 0 →
    Step_pure [admininstr_val val_1, admininstr_val val_2, admininstr.CONST numtype.I32 c, admininstr.SELECT t_lst_opt] [admininstr_val val_2]
  | if_true (c : num_) (bt : blocktype) (instr_1_lst : List instr) (instr_2_lst : List instr) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0 →
    Step_pure [admininstr.CONST numtype.I32 c, admininstr.IFELSE bt instr_1_lst instr_2_lst] [admininstr.BLOCK bt instr_1_lst]
  | if_false (c : num_) (bt : blocktype) (instr_1_lst : List instr) (instr_2_lst : List instr) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) = 0 →
    Step_pure [admininstr.CONST numtype.I32 c, admininstr.IFELSE bt instr_1_lst instr_2_lst] [admininstr.BLOCK bt instr_2_lst]
  | label_vals (v_n : n) (instr_lst : List instr) (val_lst : List val) : Step_pure [admininstr.LABEL_ v_n instr_lst (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)] (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)
  | br_zero (v_n : n) (instr'_lst : List instr) (val'_lst : List val) (val_lst : List val) (admininstr_lst : List admininstr) :
    v_n = (List.length val_lst) →
    Step_pure [admininstr.LABEL_ v_n instr'_lst ((((Map (fun (val'_elem : val) => admininstr_val val'_elem) val'_lst) ++ (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)) ++ [admininstr.BR (uN.mk_uN 0)]) ++ admininstr_lst)] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (Map (fun (instr'_elem : instr) => admininstr_instr instr'_elem) instr'_lst))
  | br_succ (v_n : n) (instr'_lst : List instr) (val_lst : List val) (l : labelidx) (admininstr_lst : List admininstr) : Step_pure [admininstr.LABEL_ v_n instr'_lst (((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.BR (uN.mk_uN ((proj_uN_0 l) + 1))]) ++ admininstr_lst)] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.BR l])
  | br_if_true (c : num_) (l : labelidx) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0 →
    Step_pure [admininstr.CONST numtype.I32 c, admininstr.BR_IF l] [admininstr.BR l]
  | br_if_false (c : num_) (l : labelidx) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) = 0 →
    Step_pure [admininstr.CONST numtype.I32 c, admininstr.BR_IF l] []
  | br_table_lt (i : num_) (l_lst : List labelidx) (l' : labelidx) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length l_lst) →
    (proj_num__0 i) ≠ none →
    Step_pure [admininstr.CONST numtype.I32 i, admininstr.BR_TABLE l_lst l'] [admininstr.BR ((l_lst)[proj_uN_0 (Option.get! (proj_num__0 i))]!)]
  | br_table_ge (i : num_) (l_lst : List labelidx) (l' : labelidx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) ≥ (List.length l_lst) →
    Step_pure [admininstr.CONST numtype.I32 i, admininstr.BR_TABLE l_lst l'] [admininstr.BR l']
  | frame_vals (v_n : n) (f : frame) (val_lst : List val) :
    v_n = (List.length val_lst) →
    Step_pure [admininstr.FRAME_ v_n f (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)] (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)
  | return_frame (v_n : n) (f : frame) (val'_lst : List val) (val_lst : List val) (admininstr_lst : List admininstr) :
    v_n = (List.length val_lst) →
    Step_pure [admininstr.FRAME_ v_n f ((((Map (fun (val'_elem : val) => admininstr_val val'_elem) val'_lst) ++ (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)) ++ [admininstr.RETURN]) ++ admininstr_lst)] (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)
  | return_label (v_n : n) (instr'_lst : List instr) (val_lst : List val) (admininstr_lst : List admininstr) : Step_pure [admininstr.LABEL_ v_n instr'_lst (((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.RETURN]) ++ admininstr_lst)] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.RETURN])
  | trap_vals (val_lst : List val) (admininstr_lst : List admininstr) :
    (val_lst ≠ []) ∨ (admininstr_lst ≠ []) →
    Step_pure ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ ([admininstr.TRAP] ++ admininstr_lst)) [admininstr.TRAP]
  | trap_label (v_n : n) (instr'_lst : List instr) : Step_pure [admininstr.LABEL_ v_n instr'_lst [admininstr.TRAP]] [admininstr.TRAP]
  | trap_frame (v_n : n) (f : frame) : Step_pure [admininstr.FRAME_ v_n f [admininstr.TRAP]] [admininstr.TRAP]
  | unop_val (nt : numtype) (c_1 : num_) (unop : unop_) (c : num_) :
    (List.length (Option.get! (fun_unop_ nt unop c_1))) > 0 →
    (fun_unop_ nt unop c_1) ≠ none →
    List.contains (Option.get! (fun_unop_ nt unop c_1)) c →
    Step_pure [admininstr.CONST nt c_1, admininstr.UNOP nt unop] [admininstr.CONST nt c]
  | unop_trap (nt : numtype) (c_1 : num_) (unop : unop_) :
    (fun_unop_ nt unop c_1) ≠ none →
    (Option.get! (fun_unop_ nt unop c_1)) = [] →
    Step_pure [admininstr.CONST nt c_1, admininstr.UNOP nt unop] [admininstr.TRAP]
```

A `Step_read` excerpt, verbatim — the head of the definition and its first three constructors ([wasm2.0.lean:14410-14426](../../../../../src/test-lean-claude/wasm2.0.lean#L14410-L14426)), then the three that read a function reference, a local, and a global ([wasm2.0.lean:14464-14468](../../../../../src/test-lean-claude/wasm2.0.lean#L14464-L14468)). All 47 constructors appear verbatim in [08-t-read-preservation.md](08-t-read-preservation.md), grouped by instruction family:
```lean
/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.109 -/
inductive Step_read : config → List admininstr → Prop where
  | block (z : state) (k : Nat) (val_lst : List val) (bt : blocktype) (instr_lst : List instr) (v_n : n) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (fun_blocktype z bt) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    k = (List.length val_lst) →
    k = (List.length t_1_lst) →
    v_n = (List.length t_2_lst) →
    Step_read (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.BLOCK bt instr_lst])) [admininstr.LABEL_ v_n [] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))]
  | loop (z : state) (k : Nat) (val_lst : List val) (bt : blocktype) (instr_lst : List instr) (t_1_lst : List valtype) (v_n : n) (t_2_lst : List valtype) :
    (fun_blocktype z bt) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    k = (List.length val_lst) →
    k = (List.length t_1_lst) →
    v_n = (List.length t_2_lst) →
    Step_read (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.LOOP bt instr_lst])) [admininstr.LABEL_ k [instr.LOOP bt instr_lst] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))]
  | call (z : state) (x : idx) :
    (proj_uN_0 x) < (List.length (fun_funcaddr z)) →
    Step_read (config.mk_config z [admininstr.CALL x]) [admininstr.CALL_ADDR ((fun_funcaddr z)[proj_uN_0 x]!)]
```
```lean
  | ref_func (z : state) (x : idx) :
    (proj_uN_0 x) < (List.length (fun_funcaddr z)) →
    Step_read (config.mk_config z [admininstr.REF_FUNC x]) [admininstr.REF_FUNC_ADDR ((fun_funcaddr z)[proj_uN_0 x]!)]
  | local_get (z : state) (x : idx) : Step_read (config.mk_config z [admininstr.LOCAL_GET x]) [admininstr_val (fun_local z x)]
  | global_get (z : state) (x : idx) : Step_read (config.mk_config z [admininstr.GLOBAL_GET x]) [admininstr_val ((fun_global z x).VALUE)]
```

Why the split exists, mechanically: `t_preservation_type_aux` (file `07`) only has to case-split on `Step`'s 23 constructors; two of those cases (`pure`, `read`) are single-line dispatches to the two *other* theorems that handle `Step_pure`'s 54 cases and `Step_read`'s 47 cases *separately*. Nobody writes one 23+54+47-case monster proof.

## 0.8 The recurring Rocq→Lean porting pattern: `_aux` lemmas

You will see this shape four times in this walkthrough (`t_preservation_vs_type'_aux`, `reduce_inst_unchanged_aux`, `store_extension_reduce_aux`, `t_preservation_type_aux`), so it's worth understanding once. Rocq's tactic language has `dependent induction`/`remember ... ; generalize dependent ...`, which lets you induct on a hypothesis like `Step (config1) (config2)` even though `config1`/`config2` aren't variables (they're already-destructured `(s, f, ais)` triples). Lean's `induction` tactic is stricter — it needs the thing you're inducting on, and *everything that mentions its indices*, fully generalized first. The idiom here is:

1. Write a `private theorem foo_aux (c1 c2 : config) (h : Step c1 c2) : ∀ (s f ais s' f' ais' ...), c1 = mk_config ... → c2 = mk_config ... → <the real statement, phrased with s,f,ais instead of c1,c2> := by induction h; ...`
2. Write the real, usable `theorem foo (s f ais s' f' ais' ...) (h : Step (mk_config ...) (mk_config ...)) : <statement> := foo_aux _ _ h s f ais s' f' ais' rfl rfl`

— i.e. the `_aux` version is the fully-general induction target (equalities instead of fixed indices), and the public wrapper is a one-line application that immediately discharges those equalities with `rfl`. This is pure Lean plumbing, not mathematical content; once you recognize the pattern you can skip straight to reading the wrapper's signature and the `_aux`'s `induction`/`case` structure.

## 0.9 Where this all comes from

Every theorem in this walkthrough carries a doc-comment citing a line number in a file like `type_preservation.v` or `type_preservation_pure.v`, and the file headers say things like *"Lean port of `spectec/test-rocq/theories/type_preservation_pure.v`."* This Lean development is a port of an existing **Rocq (Coq)** mechanization of WASM 2.0 type soundness (in the WasmCert tradition), itself generated in large part from a formal spec written in **SpecTec** (this repo's DSL for the official WASM spec — note the comments like `/- ... at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 -/` tagging almost every definition in `wasm2.0.lean`). The porting work replaces Rocq's `Qed`-closed proofs and heavy Ltac automation (`resolve_wfness`, `invert_ais_typing`, `resolve_all_pt`, ...) with hand-written Lean tactic proofs, one Rocq lemma at a time, flagging any remaining gap explicitly as `sorry` rather than silently admitting it.

---

Next: [`01-t-preservation.md`](01-t-preservation.md) — the top-level theorem.
