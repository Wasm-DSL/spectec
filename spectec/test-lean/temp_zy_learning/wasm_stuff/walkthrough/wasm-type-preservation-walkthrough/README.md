# WASM 2.0 type-preservation walkthrough

A function-by-function walkthrough of the `t_preservation` theorem tree in this repo's
Lean port of WASM 2.0 type soundness, written up from a chat conversation. For every
theorem in the diagram below it gives a plain-English summary, the code verbatim, a
piece-by-piece reading of the signature, and a proof sketch; a primer (`00`) covers
the WASM 2.0 background, assuming none. The diagram comes from
`spectec/src/test-lean-claude/claude-logging/for-claude/verbatim_dialogue_log/bundle20/user_requested_documents/preservation_audit_report.md`:

```
t_preservation  (TypePreservation.lean:2699)          Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts
│  Unpacks Config_ok → State_ok → Store_ok + Frame_ok (Moduleinst_ok, locals typed) + Expr_ok2 (Instrs_ok2),
│  then re-packs the same structure for c2 from:
├─ store_extension_reduce   (TP:1611)   Step ⇒ Extend_store s s' ∧ Store_ok s'
│   └─ store_extension_reduce_aux (TP:1438): induction on the Step derivation
│        (equational premises c1 = …, c2 = … encode Rocq's `dependent induction`)
│        ├─ congruence rules (label/frame/instrs context): the IH
│        ├─ store-writing rules → one lemma each: global_set_store_ok, table_set_store_ok,
│        │   table_grow_store_ok, elem_drop_store_ok, data_drop_store_ok,
│        │   with_mem_store_ok (TP:1341, the 4 store rules), memory_grow_store_ok (TP:1355)
│        └─ every other rule: store unchanged ⇒ Extend_store_refl
├─ reduce_inst_unchanged    (TP:536)    a step never changes the frame's MODULE
├─ Extend_store_moduleinst  (ExtensionLemmas.lean:1724)  Moduleinst_ok survives store extension
├─ t_preservation_vs_type   (TP:227)    the locals stay well-typed (Vals_ok) across a step
└─ t_preservation_type      (TP:2679)   the instruction sequence keeps its type
    └─ t_preservation_type_aux (TP:2422): induction on Step
         ├─ Step.pure  → t_pure_preservation (TypePreservationPure.lean:1858): case split over the
         │               54 Step_pure rules, one Step_pure__*_preserves lemma per rule
         ├─ Step.read  → t_read_preservation (TP:2028): case split over the 47 Step_read rules
         ├─ congruence rules (ctxt_label / ctxt_frame / ctxt_instrs): IH + typing decomposition
         └─ store-writing rules: the reduct is [] or a constant, typed directly
```

The line numbers in the diagram are from an earlier snapshot. The links in the files use
the current ones, checked against the source as of commit `8aa8000c4` (the theorem files
were last changed in `edc84f7ec`).

## Files

Read in order; each file links to the next.

| File | Covers |
|---|---|
| [`00-primer.md`](00-primer.md) | WASM 2.0 background: the execution model, runtime state, static types, the `wf_*` versus `*_ok` judgment families (with a measured table of what is and is not proved), the typing judgments, store growth (`Extend_store`), the `Step`/`Step_pure`/`Step_read` split, and the Rocq→Lean `_aux` porting pattern. |
| [`01-t-preservation.md`](01-t-preservation.md) | `t_preservation`, the top-level theorem. |
| [`02-store-extension-reduce.md`](02-store-extension-reduce.md) | `store_extension_reduce` and `store_extension_reduce_aux`; the seven store-writing lemmas; `Extend_store_refl`; the bonus `step_moduleinst`. |
| [`03-reduce-inst-unchanged.md`](03-reduce-inst-unchanged.md) | `reduce_inst_unchanged`. |
| [`04-extend-store-moduleinst.md`](04-extend-store-moduleinst.md) | `Extend_store_moduleinst`. |
| [`05-t-preservation-vs-type.md`](05-t-preservation-vs-type.md) | `t_preservation_vs_type`, with its two layers underneath. |
| [`06-t-preservation-type.md`](06-t-preservation-type.md) | `t_preservation_type`. |
| [`07-t-preservation-type-aux.md`](07-t-preservation-type-aux.md) | `t_preservation_type_aux` (all 23 `Step` cases) and `t_pure_preservation` (all 54 `Step_pure` cases, §7a). |
| [`08-t-read-preservation.md`](08-t-read-preservation.md) | `t_read_preservation` (all 47 `Step_read` cases), organised by instruction family, each with its `Step_read` rules verbatim and a WASM explanation; the theorem's one `sorry` dependency and the known corner case. |
| [`09-helper-glossary.md`](09-helper-glossary.md) | The recurring helper lemmas, grouped by purpose, with one-line meanings and exact statements. |

## About the code in these files

- **Files `01`–`09` quote the source verbatim**, doc comments included: every Lean code
  block was extracted mechanically from a stated line range, never retyped. (The only other
  code blocks are two plain-text execution traces in `08`, labelled schematic.) The primer (`00`)
  instead shows *excerpts* — trimmed, sometimes reformatted, sometimes annotated — and says
  so at its top; its blocks marked *verbatim* are exact.
- **Every code block links to its source lines.** The links are relative paths from this
  folder into `spectec/src/test-lean-claude/`, so they work from any Markdown viewer that
  resolves relative links (VS Code's preview, GitHub). If this folder moves, they will need
  re-pointing.

## Changes in this revision

This revision completes the walkthrough and corrects the previous one:

- Added `08-t-read-preservation.md` (the missing `Step.read` leaf) and `09-helper-glossary.md`.
- **Fixed code that was not verbatim** in the earlier files: `store_extension_reduce_aux`
  (file `02`) had lines joined with `;`, a context literal elided with `…`, and one
  transcription error — two calls written `ais_composition_typing s C' _ _ …` where the
  source has `ais_composition_typing _ _ _ _ …`; `table_grow_store_ok` and
  `memory_grow_store_ok` (file `02`) had dropped the source's comments; and
  `t_pure_preservation` (file `07`) had its 54 cases compressed to one line each. All code
  blocks are now generated from the source and include each theorem's doc comment.
- **Corrected the primer's claim about `sorry`s.** It said `Step_read_is_wf` was the only
  unproven dependency of `t_preservation`; measured, `t_preservation` rests on 33 `sorry`'d
  declarations (`Step_read_is_wf` plus 32 lemmas about opaque numeric primitives), while
  `t_read_preservation` rests on exactly one. It also called `Step_is_wf` and
  `Step_pure_is_wf` unproven; both are proved. See primer §0.4.
- Smaller fixes: `admininstr` has six extra constructors beyond `instr` (74 versus 68), not
  five; the primer's `Step_pure`/`Step_read` samples are now verbatim excerpts (they had
  been labelled "full constructors" while being paraphrased); file `02` gives every
  store-writing lemma the full summary/code/signature/proof-sketch treatment; and all source
  links were re-pointed after this folder moved to `spectec/test-lean/temp_zy_learning/`.
