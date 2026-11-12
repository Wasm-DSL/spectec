# Digest: `test-rocq/theories/wasm.v` (11133 lines) — the core Rocq file

Produced by a research subagent in session 1 (spanning a crash + resume).
Coverage: verbatim line-by-line for lines 1-3900, 7070-10970 (~9000 of
11133 lines read directly). For the dense repetitive `3-numerics` axiom
block (3900-7069) and part of `8-reduction` (~9970-10260), used a mix of
direct reads + exhaustive grep-extracted signatures. Pure read-only
research, nothing modified.

This is the Rocq analogue of `wasm2.0.lean` (the backend-generated base
file in our target dir) — both come from the same
`specification/wasm-2.0/*.spectec` EL source. **Don't re-port this file's
content as new Lean files — its definitions already exist in
`wasm2.0.lean`.** This digest exists so we can (a) get exact Rocq
identifier names when reading the lemma-file digests, and (b) build the
Rocq↔Lean name-mapping table.

The file is entirely auto-generated; every declaration carries a
`(* ... Definition at: <spectec-file>:<line>.<col>-... *)` comment naming
its EL source. Chapter structure:

| Chapter (spectec file) | wasm.v line range | Content |
|---|---|---|
| *(hand-written prelude)* | 1-213 | generic Rocq/mathcomp utility library |
| `0-aux.spectec` | 232-306 | tiny generic helpers |
| `1-syntax.spectec` | 214-3499 | **core AST**: numeric bit-types, value types, operator enums, `instr`, module syntax |
| `2-syntax-aux.spectec` | 3500-3665 | syntax-level aux functions |
| `3-numerics.spectec` | 3671-7069 | numeric semantics: **mostly `Axiom`s** |
| `4-runtime.spectec` | 7080-8140 | runtime values, instance records, `store`, `frame`, `state`, `admininstr`, `config` |
| `5-runtime-aux.spectec` | 8141-8598 | state/store projection & `with_*` update helpers |
| `6-typing.spectec` | 8599-9506 | `context`, subtyping, **`Instr_ok`/`Instrs_ok`**, `Module_ok` |
| `8-reduction.spectec` | 9507-~10280 | `Step_pure`, `Step_read`, `Step`, `Steps`, `Eval_expr` |
| `9-module.spectec` | 10288-10719 | allocation functions, `fun_instantiate`, `fun_invoke` |
| `A-binary.spectec` | 10721-10728 | only 3 leftover type aliases — binary format not present |
| `B-soundness.spectec` | 10730-11129 | store-aware typing (`Ref_ok`, `Val_ok`, `Instr_ok2`/`Instrs_ok2`/`Expr_ok2`, `Store_ok`, `Extend_*`, `Config_ok`) |

**IMPORTANT: no preservation/progress theorem is stated anywhere in
`wasm.v`.** It ends at `Config_ok` (11129) with only 3 dangling empty
`A-binary.spectec` comments after. `wasm.v` builds every *definition*
needed to state type soundness but has no `Theorem`/`Lemma` named
`preservation`/`progress`/`type_soundness` — those live in
`type_preservation.v` (`t_preservation`, confirmed — see
`digest_type_preservation.md`) and presumably a `type_progress.v`-style
file if one exists (not yet digested/confirmed — check the 9-file list;
per the Bash listing at session start, files are: `helper_tactics.v`,
`wasm.v`, `typing_lemmas.v`, `axioms.v`, `wasm1.v`, `type_preservation.v`,
`helper_lemmas.v`, `subtyping.v`, `extension_lemmas.v`,
`type_preservation_pure.v` — **no separate progress file exists**; if
Progress is proved at all in this development, it must be inside
`type_preservation.v` or one of the other files under a different name —
re-check `digest_type_preservation.md`'s declaration list (13 decls, all
named `*preservation*` or supporting — no `progress` found there either).
**Progress may simply not be part of this Rocq development at all** —
confirm with the user if this matters for scope.

**Every single `*_is_wf` companion lemma (hundreds) ends `Admitted`** — none
are proved. These assert "well-formed inputs + a function/relation
produces an output → output is well-formed," for nearly every
`Definition`/`Inductive`. Pure scaffolding, unproved. **For the Lean port:
state as `sorry` too** (matches how `wasm2.0.lean`'s own `*_is_wf`
theorems are already `sorry` — consistent, no extra work needed here,
just don't feel obligated to prove Rocq-`Admitted` `*_is_wf` facts that
Rocq itself never proved).

---

## 0. Universal boilerplate pattern (~150+ `Inductive Foo : Type := ...` declarations)

Every simple type gets: `Inhabited` instance, `Foo_eq_dec`/`Foo_eqb`/
`eqFooP`/`HB.instance` decidable-equality quintet (already covered by
`ExtendedDeriveDecEq.lean`'s `deriving ... DecidableEq` in the Lean
version — no action needed). Recursive types (`instr`, `admininstr`) use
`Fixpoint Foo_eq_dec`. Record types (memarg, exportinst, moduleinst,
funcinst, globalinst, tableinst, meminst, eleminst, datainst, store,
frame, context) additionally get an `_append_Foo`/`Append Foo` instance
(fieldwise `@@`, with an explicit `(* FIXME - Non-trivial append *)`
comment on non-appendable fields) and RecordSet's `Settable`/`settable!`
(→ Lean's native `{ r with field := v }`, no action needed).

Every syntactic type typically also has a companion
`Inductive wf_Foo : Foo -> Prop` (structural/range well-formedness,
**distinct from** the `_ok`-suffixed typing judgments in `6-typing`/
`B-soundness`) — these are the validity side-conditions threaded through
`Instr_ok` etc.

## 1. Prelude (hand-written, 1-213) — generic library, not spectec-generated
```coq
Class Inhabited (T: Type) := { default_val : T }.
Definition lookup_total {T} {_: Inhabited T} (l: seq T) (n: nat) : T := seq.nth default_val l n.
Definition the {T} {_ : Inhabited T} (arg : option T) : T := match arg with None => default_val | Some v => v end.
Fixpoint list_update / list_update_func / list_slice / list_slice_update ...
Class Append (α: Type) := _append : α -> α -> α.   Infix "@@" := _append.
Inductive List_Forall3 ... / Foralli_help ... / holds_upto (Forall P (iota 0 n)).
Class Coercion (A B : Type) := { coerce : A -> B }.  Notation "x ':>' B" := coerce ... 
Notation "| x |" := (seq.size x).      (* list length, |l| everywhere *)
Notation "!( x )" := (the x).           (* unwrap option via Inhabited default *)
Notation "x '[|' a '|]'" := (lookup_total x a).   (* indexing x[|i|] *)
```
**Translation-critical**: `x :> nat` is a user-defined typeclass coercion
(not Rocq's builtin `Coercion`) resolved through `Coercion`/
`total_coercion`/`transitive_coercion`; each site needs resolving to a
concrete conversion function in Lean — no 1:1 equivalent. `!(x)` is a
TOTAL-but-unsafe option unwrap via a global default; used constantly where
a side-condition elsewhere guarantees `Some`. `@@` is generic append via
the `Append` typeclass (seq/option/nat/per-record fieldwise). **These 4
notations (`:>`, `|x|`, `!()`, `[| |]`, `@@`) are used thousands of times
— when reading Rocq lemma statements, mentally expand them.**

## 2. Numeric bit-representation types (`1-syntax.spectec`, 214-753)
`r_MUT` (singleton), `res_N`/`n`/`m := nat`, `Ki := 1024`, `fun_sum`
(relational list-sum), `opt_`/`list_`/`concat_`/`inv_concat_` (the last is
a genuine `Axiom` — no computable inverse), `setproduct_` family
(cartesian product), `disjoint_`. `res_list X := mk_list (seq X)` (the
`resulttype` wrapper — **matches Lean's `list` wrapper type in
`wasm2.0.lean`, line 520 per session 1's own earlier grep**;
`res_list_eq_dec` is `Admitted` with `(* FIXME - No clear way to do
decidable equality *)` — the ONE type in the whole file where auto-DecEq
synthesis failed). `bit`/`byte`/`uN`/`sN` + `wf_*` range predicates (match
`wasm2.0.lean`'s `bit`/`byte`/`uN`/`sN` exactly per session 1's earlier
read). `signif`/`expon`/`fun_M`/`E`. `fNmag`/`fN` + `wf_*`. `char`+`wf_char`,
`fun_utf8` (UTF-8 encoding relation, 4 cases + concat closure — matches
`wasm2.0.lean`'s `fun_utf8` exactly per session 1's earlier read),
`name`+`wf_name`. Index-type aliases (`idx`, `laneidx`, `typeidx`, etc, all
→ `u32`/`u8`).

## 3. Value types & shapes (749-1063)
`numtype`(I32/I64/F32/F64), `vectype`(V128), `reftype`(FUNCREF/EXTERNREF),
`valtype` (=numtype+vectype+reftype+**BOT**), `Inn`/`Fnn` (I32/I64 vs
F32/F64 tags + projections), `resulttype := res_list valtype`,
`packtype`(I8/I16), `lanetype`, `mut := option r_MUT`. `limits`
`mk_limits(u32)(option u32)` +`wf_limits`. `globaltype`, `functype
mk_functype(resulttype)(resulttype)`, `tabletype`+`wf_tabletype`,
`memtype PAGE(limits)`+`wf_memtype`, `elemtype := reftype`, `datatype OK`,
`externtype` (FUNC/GLOBAL/TABLE/MEM)+`wf_externtype`. `dim`/`shape`+wf,
size helper functions (`res_size`, `psize`, etc — **`res_size` is
confirmed used in `axioms.v`'s `nbytes_len` axiom** per session 1's earlier
find). `num_` (bit-pattern payload, mk_num__0 Inn iN | mk_num__1 Fnn fN) +
`wf_num_`, `lane_`+`wf_lane_`, `vec_ := vN`, `fun_zero`+`zero_is_wf`.

## 4. Operator enums (1520-2680)
Per-numeric-class enum pattern (`unop_Inn`/`unop_Fnn`→`unop_`,
`binop_Inn`/`binop_Fnn`→`binop_`, `testop_Inn`→`testop_`,
`relop_Inn`/`relop_Fnn`→`relop_`, `cvtop` flat), SIMD-lane variants
(`vunop_Jnn_N`/`vunop_Fnn_N`→`vunop_`, similarly `vbinop_`/`vtestop_`/
`vrelop_`/`vcvtop`/`vshiftop_`/`vextunop_`/`vextbinop_`), each with a
`wf_*` encoding lane-width/applicability side conditions. **`memarg`
record** `{ALIGN; OFFSET}` +`wf_memarg`. `loadop_Inn`/`loadop_`,
`vloadop`, `blocktype` (`_RESULT`/`_IDX`)+`wf_blocktype`.

## 5. `instr` — the core AST (2818-3113)
68 constructors (NOP, UNREACHABLE, DROP, SELECT, BLOCK/LOOP/IFELSE,
BR/BR_IF/BR_TABLE, CALL/CALL_INDIRECT/RETURN, CONST/UNOP/BINOP/TESTOP/
RELOP/CVTOP/instr_EXTEND, VCONST+SIMD family, REF_NULL/REF_FUNC/
REF_IS_NULL, LOCAL_*/GLOBAL_*, TABLE_*/ELEM_DROP, LOAD/STORE/VLOAD*/
VSTORE*, MEMORY_*/DATA_DROP). `wf_instr` has one case per constructor
(`instr_case_0`..`_67`), pure syntactic check, **separate from and weaker
than** the real typing judgment `Instr_ok` (6-typing). `expr := seq instr`.

## 6. Module-level syntax (3115-3499)
`elemmode`/`datamode`+wf, `type`/`local`/`func`/`global`/`table`/`mem`/
`elem`/`data`/`start`/`externidx`/`export`/`import`/`module` — each with a
`wf_*`. `module MODULE(types)(imports)(funcs)(globals)(tables)(mems)
(elems)(data)(option start)(exports)`.

## 7. `2-syntax-aux.spectec` (3500-3665)
`fun_concat_bytes`, `unpack`/`shunpack` (packed lanes → I32), `fun_funcsxt`/
`fun_globalsxt`/`fun_tablesxt`/`fun_memsxt` (filter+project externtype
lists), `dataidx_instr`, `fun_dataidx_instrs/expr/func/funcs` (collect
data-segment indices for `Module_ok`'s data count), `memarg0`.

## 8. `3-numerics.spectec` (3671-7069) — MOSTLY AXIOMATIZED
**Nearly all IEEE-754 float and bit-level integer arithmetic is a Rocq
`Axiom`** (opaque, no proof obligation). 61 axioms total:
`s33_to_u32`, `truncz`, `extend__`, `fabs_`/`fceil_`/`ffloor_`/`fnearest_`/
`fneg_`/`fsqrt_`/`ftrunc_` (multi-valued, return `seq fN`!), `iclz_`/
`ictz_`/`ipopcnt_`, `wrap__` (**note: `wasm2.0.lean` already has `wrap__`
as `opaque ... := by ...` with an `_is_wf` theorem, per session 1's
earlier grep — confirms Lean port already mirrors this axiomatization**),
`fadd_`/`fcopysign_`/`fdiv_`/`fmax_`/`fmin_`/`fmul_`/`fsub_` (multi-valued),
`iand_`/`ior_`/`irotl_`/`irotr_`/`ixor_`, `ishl_`/`ishr_`, `feq_`/`fge_`/
`fgt_`/`fle_`/`flt_`/`fne_`, `convert__`, `demote__`/`promote__`
(multi-valued), `reinterpret__`, `trunc__`/`trunc_sat__`, `narrow__`,
`ibits_`/`fbits_`, `ibytes_`/`fbytes_`, `nbytes_`/`vbytes_` (**confirmed —
`wasm2.0.lean` already has `nbytes_`/`ibytes_` as `opaque` with `_is_wf`,
per session 1's find — this is exactly what `axioms.v`'s 2 axioms
`nbytes_len`/`ibytes_len` are about, see NOTES.md**), `inv_ibits_`/
`inv_fbits_`, `inv_ibytes_`/`inv_fbytes_`/`inv_nbytes_`/`inv_vbytes_`,
`inot_`/`irev_`, `iandnot_`/`ibitselect_`, `iavgr_`/`iq15mulr_sat_`,
`fpmin_`/`fpmax_`, `lanes_`/`inv_lanes_`.

On top, constructively-defined dispatch functions/relations select the
right axiom per operator (still using axioms as building blocks):
`res_bool`, `sat_u_`/`sat_s_`, `fun_signed_`/`fun_inv_signed_`,
`fun_unop_`, `iadd_`/`imul_`/`isub_` (NOT axiomatized — direct nat/int
arithmetic), `fun_idiv_`/`fun_irem_` (relational, partial), `fun_binop_`,
`ieqz_`/`fun_testop_`, `ieq_`/`ine_`, `fun_ige_`/`fun_igt_`/`fun_ile_`/
`fun_ilt_`, `fun_relop_`, `fun_cvtop__`, `inez_`/`ineg_`, `fun_iabs_`/
`fun_imin_`/`fun_imax_`/`fun_iadd_sat_`/`fun_isub_sat_`, `packnum_`/
`unpacknum_`, `zeroop`/`halfop`/`fun_half`, `vvunop_`/`vvbinop_`/
`vvternop_`, `fun_vunop_`/`fun_vbinop_`/`fun_vrelop_`, `vcvtop__`,
`fun_vextunop__`/`fun_vextbinop__`, `fun_vshiftop_`. Every one has an
`_is_wf` lemma (`Admitted`).

## 9. `4-runtime.spectec` — runtime values, instances, admin syntax (7080-8140)
Address aliases (`addr := nat`, `funcaddr`, etc.), `externaddr`+wf.
`num`/`vec` (runtime-level, **distinct from `num_`/`vec_` bit-payload
types** — one-letter naming collision to watch), `ref` (REF_NULL/
REF_FUNC_ADDR/REF_HOST_ADDR — **no `wf_ref` emitted, apparent gap**), `val`
(5 ctors)+`wf_val`, `val_ref` (ref→val lift), `result` (_VALS/TRAP)+wf.

Records: `exportinst{NAME;ADDR}`+wf, `moduleinst{TYPES;FUNCS;GLOBALS;
TABLES;MEMS;ELEMS;DATAS;EXPORTS}`+wf (**only constrains EXPORTS**, other
lists unconstrained — matches session 1's earlier read of
`wasm2.0.lean`'s `moduleinst` structure), `funcinst{TYPE;MODULE;CODE}`+wf,
`globalinst{TYPE;VALUE}`+wf, `tableinst{TYPE;REFS}`+wf,
`meminst{TYPE;BYTES}`+wf, `eleminst{TYPE;REFS}` (**NO `wf_eleminst` —
confirmed gap**), `datainst{BYTES}`+wf, `store{FUNCS;GLOBALS;TABLES;MEMS;
ELEMS;DATAS}` (`wf_store` constrains all but **ELEMS** — matches the
eleminst gap), `frame{LOCALS;MODULE}`+wf, `state mk_state(store)(frame)`+wf
(plain `Inductive`, not `Record`).

**Field-naming quirk**: some fields are prefixed by owning type
(`funcinst_TYPE`, `store_FUNCS`, `context_TYPES`, ...) to avoid Rocq's flat
record-projection namespace colliding; others are bare (`NAME`, `TYPES`,
`VALUE`, `LOCALS`, ...). **Lean 4 structures don't need this** (dot-notation
disambiguates per-structure) — `wasm2.0.lean` already drops these prefixes
back to clean names (confirmed: session 1 found `context.TYPES` not
`context.context_TYPES` in the Lean file) — **so when reading Rocq lemma
statements that use `context_TYPES C`, the Lean equivalent is `C.TYPES`,
etc. Build this stripping into the name-mapping table.**

`admininstr` — every `instr` constructor duplicated with `admininstr_`
prefix, PLUS: `admininstr_REF_FUNC_ADDR`, `admininstr_REF_HOST_ADDR`,
`CALL_ADDR`, `LABEL_(n)(seq instr)(seq admininstr)`,
`FRAME_(n)(frame)(seq admininstr)`, `admininstr_TRAP`. `admininstr_instr`/
`admininstr_ref`/`admininstr_val` (structural embeddings). `wf_admininstr`
(73 cases). `config mk_config(state)(seq admininstr)`+wf.

## 10. `5-runtime-aux.spectec` (8141-8598)
`default_` (zero-value per valtype, `None` for BOT), `fun_funcsxa`/
`fun_globalsxa`/`fun_tablesxa`/`fun_memsxa` (runtime analog of the `sxt`
filters), `fun_store`/`fun_frame`/`fun_funcaddr`/`fun_funcinst`/
`fun_globalinst`/`fun_tableinst`/`fun_meminst`/`fun_eleminst`/
`fun_datainst`/`fun_moduleinst`/`fun_type`/`fun_func`/`fun_global`/
`fun_table`/`fun_mem`/`fun_elem`/`fun_data`/`fun_local` (state projections
+ index-chained lookups). `with_local`/`with_global`/`with_table`/
`with_tableinst`/`with_mem`/`with_meminst`/`with_elem`/`with_data`
(RecordSet `<| field := ... |>` functional updates). `fun_growtable`
(success/failure via negated-precondition pattern — append `n` copies of
ref, checked against max), `fun_growmemory` (**uses EXACT RATIONAL
arithmetic**, `mathcomp rat`/`%Q`, to convert byte-length↔page-count —
matches `wasm2.0.lean`'s `rat_to_nat`/`Rat` usage confirmed in session 1's
earlier grep of the load/store typing rules, lines ~10946-11012).

## 11. `6-typing.spectec` — static typing judgments (8599-9506)
`context{TYPES;FUNCS;GLOBALS;TABLES;MEMS;ELEMS;DATAS;LOCALS;LABELS;
RETURN}` — **matches `wasm2.0.lean`'s `context` structure exactly**
(confirmed field-for-field against session 1's earlier read of
`wasm2.0.lean:9312`). `wf_context` only Forall-checks TABLES/MEMS.

`Limits_ok`, `Functype_ok`, `Globaltype_ok` (⚠ **flagged by digesting
agent as possibly unusual**: its sole constructor requires `mut = Some
MUT` literally, i.e. syntactically only "mutable" globaltypes pass
`Globaltype_ok` — worth double-checking against the EL spec / `wasm2.0.lean`'s
own `Globaltype_ok`-equivalent before assuming this is intentional, since
`Global_ok` elsewhere seems to handle both mutability cases via a separate
`gt == mk_globaltype v_mut t` equality check, i.e. `Globaltype_ok` alone
may just be a narrower internal helper, not the general "any valid
globaltype" predicate its name suggests), `Tabletype_ok` (limits ≤
2^32-1), `Memtype_ok` (limits ≤ 2^16), `Externtype_ok`.

`Valtype_sub` (refl:t~t | bot:BOT~t — **BOT is the sole nontrivial
subtype**), `Resulttype_sub` (pointwise `Valtype_sub` via `Forall2` +
equal length), `Limits_sub`/`Functype_sub`(invariant)/`Globaltype_sub`
(invariant)/`Tabletype_sub`/`Memtype_sub`/`Externtype_sub` (4 ctors).
`Blocktype_ok` (2 ctors: `_RESULT` direct, `_IDX` looks up `context_TYPES`).

**THE central mutually-recursive pair** (`with` keyword):
```coq
Inductive Instr_ok : context -> instr -> functype -> Prop :=
  (* ~70 constructors, one per instr case: nop, unreachable, drop,
     select_expl, select_impl, block, loop, res_if, br, br_if, br_table,
     call, call_indirect, res_return, const, unop, binop, testop, relop,
     cvtop_reinterpret, cvtop_convert, ref_null, ref_func, ref_is_null,
     vconst, Instr_ok__vvunop/vvbinop/vvternop/vvtestop, vunop, vbinop,
     vtestop, vrelop, vshiftop, vbitmask, vswizzle, vshuffle, vsplat,
     vextract_lane, vreplace_lane, vextunop, vextbinop, vnarrow,
     Instr_ok__vcvtop, local_get/set/tee, global_get/set,
     table_get/set/size/grow/fill/copy/init, elem_drop,
     memory_size/grow/fill/copy/init, data_drop, load_val, load_pack,
     store_val, store_pack, vload, vload_splat, vload_zero, vload_lane,
     vstore, vstore_lane.
     block/loop/if push a fresh nested context via record-update-and-@@-
     merge of a fresh {LABELS:=[t2]} context onto C, then require
     Instrs_ok of the body. *)
with
Instrs_ok : context -> seq instr -> functype -> Prop :=
  | empty | Instrs_ok__instr
  | res_seq (sequences t1->t2, t2->t3)
  | sub (subsumption via Resulttype_sub both sides)
  | Instrs_ok__frame (extends both sides by common prefix t_lst).
```
**This matches `wasm2.0.lean`'s already-confirmed `Instr_ok`/`Instrs_ok`
(lines 9514, 10020) exactly by name** — good naming correspondence,
confirms session 1's earlier finding. Cross-reference with
`digest_typing_lemmas_and_type_preservation_pure.md`'s coverage of
`ai_principal_typing` which is stated in terms of exactly these
constructors' shapes.

`Expr_ok` (wraps `Instrs_ok` with empty input stack), `Instr_const`/
`Expr_const` (const-expr fragment: CONST/VCONST/REF_NULL/REF_FUNC/
GLOBAL_GET-of-immutable-only), `Expr_ok_const` (Expr_ok + Expr_const).
`Type_ok`, `Func_ok` (checks `context_TYPES[x]`, excludes BOT locals,
`Expr_ok` under context extended with `{LOCALS:=t1++t_lst; LABELS:=[t2];
RETURN:=Some t2}`), `Global_ok` (`Globaltype_ok`+`Expr_ok_const`),
`Table_ok`, `Mem_ok`, `Elemmode_ok`, `Elem_ok`, `Datamode_ok`, `Data_ok`,
`Start_ok` (func type must be `[] -> []`), `Import_ok`, `Externidx_ok`,
`Export_ok`.

`Module_ok` — single huge constructor (~30 quantified vars): wires
`fun_memsxt`/`tablesxt`/`globalsxt`/`funcsxt` on import externtypes,
`Forall2 Type_ok`, `Forall2 Import_ok` against types-only pre-context,
`Forall2 {Global,Table,Mem,Elem}_ok` against `C'`, `Forall Data_ok`
against `C'`, `Forall2 Func_ok` against `C`, `Forall Start_ok/Export_ok`,
"at most one memory" (`|mt_lst|<=1`), builds final `C`/`C'` contexts by
concatenating imported+internal component lists.

## 12. `8-reduction.spectec` — operational semantics (9507-~10280)
Pattern: `Step_*_before_<name>` helper `Inductive`s state a rule's success
precondition; a companion "otherwise" rule's premise is literally
`~(Step_*_before_<name> ...)` (negated Prop, since not Boolean-decidable
in general — e.g. `rat`/`Q` equalities).

`Step_pure : seq admininstr -> seq admininstr -> Prop` — structural/local,
state-independent. Full constructor list (verified verbatim): unreachable/
nop/drop, select_true/false, if_true/false, label_vals, br_zero/br_succ,
br_if_true/false, br_table_lt/ge, frame_vals, return_frame, return_label,
trap_vals/label/frame, unop_val/trap, binop_val/trap, testop, relop,
cvtop_val/trap, ref_is_null_true/false, vvunop/vvbinop/vvternop/vvtestop,
vunop, vunop_trap, vbinop_val/trap, vtestop_true/false, vrelop, vshiftop,
vbitmask, vswizzle, vshuffle, vsplat, vextract_lane_num/pack,
vreplace_lane, vextunop/vextbinop, vnarrow, vcvtop_full/half/zero,
local_tee. Each rule invokes the matching `fun_*_` relation from
3-numerics + threads a "val ∈ result_set" nondeterministic-choice premise
for multi-valued float ops, plus a `_trap` sibling for empty result sets.
**Matches `type_preservation_pure.v`'s 28 `Step_pure__*_preserves` lemma
names one-to-one** (cross-ref `digest_typing_lemmas_and_type_preservation_pure.md`)
— confirms full coverage of non-SIMD `Step_pure` cases there. `+ Lemma
Step_pure_is_wf, Admitted` — **this is the external wellformedness lemma
`t_pure_preservation`'s proof invokes** per that digest.

`fun_blocktype` (resolves blocktype to functype). `Step_read_before_*`
helpers (call_indirect_trap, table_fill/copy/init_zero, table_copy_le,
memory_fill/copy/init_zero, memory_copy_le). `Step_read : config -> seq
admininstr -> Prop` — reads state without writing. Verified through
`table_copy_le`; remaining constructors (table_init_*, memory_fill/copy/
init_*, load/store, vload/vstore family) grep-confirmed present but not
individually re-verified this pass — read directly at wasm.v ~9970-10152
if exact text needed. `Step_read_is_wf` at 10153.

`Step : config -> config -> Prop` (~10160-10260, signature confirmed body
not transcribed) — closes `Step_pure`/`Step_read` plus state-WRITING
instructions (global.set, table.set/grow, memory.grow, elem.drop,
data.drop, LABEL_/FRAME_ congruence). `+ Step_is_wf` at 10261, Admitted.
`Steps` (reflexive-transitive closure), `Eval_expr` (big-step via `Steps`).
**Cross-ref: `digest_type_preservation.md`'s `store_extension_reduce` and
`t_preservation_type` both do `induction`/`dependent induction` directly
on this `Step` relation's full constructor set** — need the complete,
exact constructor list from wasm.v directly when porting those (re-read
lines ~10160-10260 verbatim at that time, this digest doesn't have it
transcribed).

## 13. `9-module.spectec` — allocation & instantiation (10288-10719)
`fun_funcs`/`fun_globals`/`fun_tables`/`fun_mems` (filter-by-tag, second
copy specific to this section). `fun_allocfunc`/`fun_allocfuncs`,
`fun_allocglobal`/`s`, `fun_alloctable`/`s`, `fun_allocmem`/`s`,
`fun_allocelem`/`s`, `fun_allocdata`/`s` — each singular allocator appends
one instance, returns fresh address = old length; plural folds singular
over a list. **Matches `wasm2.0.lean`'s already-confirmed `fun_allocfunc`
...`fun_allocdatas` (lines 11283-11538) exactly.** `instexport` (resolves
export's externidx-relative index to absolute externaddr).
`fun_allocmodule` (master allocator, threads store through alloc*
sequence). `runelem`/`rundata` (lower ELEM/DATA into TABLE_INIT+ELEM_DROP
/MEMORY_INIT+DATA_DROP instr sequences). `fun_instantiate` (full algorithm:
`Eval_expr` for init exprs, `fun_allocmodule`, runs runelem/rundata +
optional start CALL_ADDR). `fun_invoke` (wraps CALL_ADDR into runnable
config). Trailing `A-binary.spectec` aliases: `startopt`, `code`, `nopt`.

## 14. `B-soundness.spectec` — store-aware typing/soundness scaffolding (10730-11129)

`Context_ok` (rebuilds context shape, requires `Functype_ok`/
`Globaltype_ok`/`Memtype_ok`/`Tabletype_ok` pointwise). `Externaddr_ok`
(index-bound+lookup per kind + `__sub` closing under `Externtype_sub`).
`Ref_ok` (null: any rt | `Ref_ok__func` via `Externaddr_ok`...FUNC:
FUNCREF | extern: REF_HOST_ADDR unconditionally EXTERNREF — host addrs
opaque/untyped). `Val_ok` (wraps `Ref_ok` for ref case via `val_ref`
coercion). `Result_ok` (pointwise Val_ok | trap-any-type).
`adminexpr := seq admininstr`.

`Datainst_ok` (trivial, always OK — matches session 1's earlier note re:
content-independence), `Eleminst_ok` (pointwise `Ref_ok` over
`eleminst_REFS`), `Exportinst_ok` (wraps `Externaddr_ok`).
`Moduleinst_ok` — store-relative analogue of `wf_moduleinst`+`wf_context`
combined: every FUNCS/GLOBALS/TABLES/MEMS addr resolves via
`Externaddr_ok` to matching context entry; DATAS/ELEMS addr bounded +
`Datainst_ok`/`Eleminst_ok`; EXPORTS pairwise-disjoint NAMEs + ADDR must
be among module's own addresses. `Frame_ok` (`Moduleinst_ok` on
`frame_MODULE` + pointwise `Val_ok` on LOCALS against context extended
with `LOCALS:=t_lst`; result context is `C @@ {LOCALS:=t_lst}`).

**Second mutually-recursive typing triple** — mirrors `Instr_ok`/
`Instrs_ok`/`Expr_ok` but on `admininstr` (not `instr`) and store-indexed,
typing CALL_ADDR/LABEL_/FRAME_/ref-values/TRAP:
```coq
Instr_ok2 : store -> context -> admininstr -> functype -> Prop :=
  | plain (delegates to Instr_ok for admininstr_instr embedding)
  | label (LABEL_ n instr' admininstr via Instrs_ok2 on continuation+body)
  | Instr_ok2__frame (FRAME_ n f admininstr via Frame_ok + Expr_ok2)
  | Instr_ok2__call_addr (via Externaddr_ok ... FUNC ft)
  | Instr_ok2__ref (via Ref_ok) | Instr_ok2__trap (any type)
with Instrs_ok2 : store -> context -> seq admininstr -> functype -> Prop :=
  empty/instr/seq/sub/frame (exact structural mirror of Instrs_ok's 5)
with Expr_ok2 : store -> context -> adminexpr -> resulttype -> Prop
```
**IMPORTANT for the mutual-induction-scheme correspondence question raised
in `digest_subtyping_and_extension_lemmas.md`**: `extension_lemmas.v`'s
custom `Scheme` is over `Admin_instrs_ok`/`Thread_ok`/`Admin_instr_ok` —
those names do NOT literally appear here (this file has `Instr_ok2`/
`Instrs_ok2`/`Expr_ok2`, not `Admin_instr_ok`/`Admin_instrs_ok`/
`Thread_ok`). **Either `Admin_instr_ok` etc. are aliases/notations defined
elsewhere (not found by this digest — check `typing_lemmas.v`'s digest,
which doesn't mention them either) — OR the extension_lemmas.v digest's
inferred names are approximate/from a different naming convention than
what's literally in this file.** This needs direct resolution: grep
`test-rocq/theories/*.v` for `Admin_instr_ok`/`Thread_ok` before writing
any Lean code depending on this correspondence. **Flagging as an open
question for whoever ports `store_extension_ais`.**

`Globalinst_ok`, `Meminst_ok` (+ exact byte count `|BYTES|==n*64*Ki`),
`Tableinst_ok` (+ `|REFS|==n`), `Funcinst_ok` (`Functype_ok` +
`Moduleinst_ok(funcinst_MODULE)` + `Func_ok` under that context).

`Store_ok` — pointwise `Globalinst_ok`/`Meminst_ok`/`Tableinst_ok`/
`Funcinst_ok`/`Datainst_ok`/`Eleminst_ok` over the six store lists, each
tied to a same-length parallel type-list (the "store signature").

`Extend_globalinst`/`Extend_meminst`/`Extend_tableinst`/`Extend_funcinst`/
`Extend_datainst`/`Extend_eleminst` — per-component monotonicity:
globalinst only changes VALUE if mutable; meminst/tableinst may only grow
(length inequalities, not literal pointwise prefix check here); funcinst
exactly rigid (`Extend_funcinst x x` — functions never change); datainst/
eleminst may only shrink-to-passive (`b==b' \/ b'==[]`, i.e. "dropped" is
the only mutation, matching data.drop/elem.drop). **These are the Rocq
names the `extension_lemmas.v` digest's inferred `Func_extension`/
`Table_extension`/`Mem_extension`/`Global_extension`/`Elem_extension`/
`Data_extension` are presumably aliases/shorthand for — likely just this
digest's fuller names (`Extend_funcinst` vs `Func_extension`) referring to
the SAME relations under informal shorthand in that other digest's prose.
Confirm exact names before porting; the canonical ones are these
`Extend_*inst` names shown here, matching `wasm2.0.lean`'s own
`Extend_globalinst`/`Extend_meminst`/`Extend_tableinst`/`Extend_funcinst`/
`Extend_datainst`/`Extend_eleminst` (confirmed present, session 1's
earlier grep, lines 12346-12459) — exact 1:1 name match, good.**

`Extend_store` — lifts the six per-component `Extend_*` relations
pointwise across the OLD store's index range only (via `holds_upto`), for
GLOBALS/MEMS/TABLES/FUNCS/DATAS/ELEMS. **Matches `wasm2.0.lean`'s
`Extend_store` (12460, confirmed by session 1 earlier) — though note
`extension_lemmas.v`'s inferred "prefix-extended + suffix-appended" shape
for `Store_extension` (a DIFFERENT name — `Store_extension` not
`Extend_store`!) may be describing a DIFFERENT, possibly related-but-not-
identical relation. Need to determine: is `Store_extension` (used in
`extension_lemmas.v`/`type_preservation.v`) the SAME relation as
`Extend_store` (defined here in `wasm.v`/`B-soundness.spectec`), just
under two names, or are they genuinely two different relations (e.g. one
used pre-typing-infra, one post)? Given `extension_lemmas.v` imports
`wasm` and uses `Store_extension` without redefining it, `Store_extension`
must be defined in `wasm.v` too — but this digest, despite covering
`B-soundness.spectec` in full (`Extend_*` family), did NOT find a
`Store_extension`/`Func_extension`/`Table_extension`/etc. declaration
under those exact names anywhere. **This is a real gap — grep wasm.v
directly for `Store_extension` and `Func_extension` before relying on
either digest's naming.** (Best guess: `Store_extension`/`Func_extension`
etc. ARE `Extend_store`/`Extend_funcinst` etc. and the other digest's
author paraphrased/normalized the names rather than copying verbatim —
but confirm, don't assume.)

`State_ok` (Store_ok + Frame_ok). `Config_ok` — `mk_Config_ok`: `State_ok
(mk_state s f) C -> Expr_ok2 s C admininstr_lst t_lst -> ... -> Config_ok
(mk_config (mk_state s f) admininstr_lst) t_lst`. **Matches
`wasm2.0.lean`'s `Config_ok` (12496, confirmed session 1 earlier) and the
Rocq capstone theorem `t_preservation`'s conclusion type exactly** (cross-
ref `digest_type_preservation.md` #13 and NOTES.md's naming-discovery
section).

File ends at line 11129; lines 11131-11133 are three orphaned
`A-binary.spectec` mutual-recursion comments with no bodies.

---

## Cross-checked facts to flag explicitly

1. **No preservation/progress theorem in `wasm.v`** — everything needed to
   *state* soundness is here, the theorem itself is in `type_preservation.v`
   (confirmed: `t_preservation`). No separate Progress theorem/file found
   in the 9-file corpus — may not exist in this development at all; ask
   the user if Progress is in scope.
2. **Every `_is_wf` lemma is `Admitted`** (hundreds) — referenced as
   premises inside real judgments, so needed as Lean declarations, not
   necessarily proved (mirrors `wasm2.0.lean`'s own `sorry`'d `_is_wf`s).
3. **Two disjoint well-formedness gaps**: `eleminst`/`wf_eleminst` never
   emitted, `wf_store` doesn't constrain `store_ELEMS`; `fun_eleminst`/
   `fun_elem` also lack `_is_wf` companions. Possible genuine
   generator/spectec-source omission — worth a sanity check, not just
   silently replicating in Lean (though `wasm2.0.lean` likely already has
   whatever the backend generated, consistent either way — check if
   `wasm2.0.lean` also lacks a `wf_eleminst`).
4. **`res_list_eq_dec` is `Admitted`** — the one type where auto-DecEq
   synthesis failed (`(* FIXME - No clear way to do decidable equality *)`).
   `wasm2.0.lean`'s `list` type (the Lean equivalent) DOES successfully
   `deriving ... DecidableEq` per session 1's earlier read (line ~127 of
   `wasm2.0.lean`) — so this specific Rocq gap does NOT carry over to
   Lean; no action needed.
5. **Numeric arithmetic almost entirely axiomatized** (61 axioms) — if the
   Lean port needs to be executable (not just type-correct), these need
   real implementations; porting as Lean `axiom`/`opaque` (matching
   `wasm2.0.lean`'s existing `opaque ... := by ... sorry` pattern for
   `wrap__`/`nbytes_`/etc, already confirmed present) faithfully preserves
   content but isn't executable. **Not our concern — `wasm2.0.lean`
   already handles this, we just use it.**
6. **Two mutually-recursive judgment triples**: `Instr_ok`/`Instrs_ok`
   (6-typing, 2-way) and `Instr_ok2`/`Instrs_ok2`/`Expr_ok2`
   (B-soundness, 3-way). Both already exist as Lean `mutual`/inductive
   blocks in `wasm2.0.lean` (confirmed).
7. RecordSet's `<| field := v |>` → Lean's native `{ r with field := v }`.
8. The `:>`/`|x|`/`!()`/`[| |]`/`@@` notations are typeclass-dispatched,
   used thousands of times — expand mentally when reading Rocq statements;
   `wasm2.0.lean` will have already resolved these concretely per-site.
9. `mathcomp`'s `seq`/`eqType`/`rat`/`int` vs stdlib `list`/`Z`/`Q` —
   `wasm2.0.lean` uses plain `List`/`Nat`/`Int`/`Rat` already, no action
   needed on our side, just be aware when reading Rocq statements that
   `==`/`!=` there is boolean `eqType` equality, not `=`.
10. **Naming collision to watch**: `num` (runtime value, in `admininstr`
    context) vs `num_` (bit-pattern payload) are distinct types one
    underscore apart; similarly `unop_` (wrapper) vs `unop_Inn` (numtype-
    specific sub-enum). Read carefully.
11. **OPEN QUESTION (flagged above, needs resolution before porting
    extension_lemmas.v's capstone theorems)**: is `Store_extension` (used
    throughout `extension_lemmas.v`/`type_preservation.v`) the same
    relation as `Extend_store` (the only such top-level relation this
    digest found defined in `wasm.v` itself)? And are `Func_extension`/
    `Table_extension`/`Mem_extension`/`Global_extension`/`Elem_extension`/
    `Data_extension` the same as `Extend_funcinst`/`Extend_tableinst`/
    `Extend_meminst`/`Extend_globalinst`/`Extend_eleminst`/
    `Extend_datainst`? Best guess: yes, same relations, just referred to
    by paraphrased/shortened names in the extension_lemmas.v digest
    (written by a different agent than this one). **Verify via direct
    grep of wasm.v for `Store_extension`/`Func_extension` before trusting
    either digest's naming when writing Lean signatures** — if confirmed
    identical, use `Extend_store`/`Extend_funcinst`/etc. (this digest's
    names) since they're confirmed to exist verbatim in both `wasm.v` and
    `wasm2.0.lean`.
