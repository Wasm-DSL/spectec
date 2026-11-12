# WASM 2.0 spectec files: category A vs category B

For every `.spectec` file in `specification/wasm-2.0`, this is the result of
exhaustively going through its top-level constructs (`syntax`, `def`,
`relation`/`rule`, `grammar`, `var`) and sorting them into:

- **A** — constructs with a direct manifestation in WASM: something you can
  write in a `.wat` file, or directly observe about a running module.
- **B** — constructs that exist for the convenience of *defining* the spec
  (semantics, algorithms, encoding, proofs, generic plumbing) but are never
  themselves authored or observed.

Each source file has a same-named `.wat` companion in this directory. Where
category A is non-empty, that file *is* the demonstration (every
construct exercised, verified against `wasm-interp`). Where category A is
empty, the companion is a minimal `(module)` whose header comment explains
the categorization for that file in full, construct by construct — this
document is the index, not a replacement for those.

## The headline result

Only **1-syntax.spectec** has substantial category-A content — and in fact
it is essentially *all* of category A for the entire directory: every value
type, every instruction, every module-level construct (func/table/memory/
global/elem/data/start/import/export) that a `.wat` file can contain is
declared there. Every other file defines something *about* that syntax —
semantics, an algorithm, a proof, an encoding — none of which you write or
observe directly:

| File | Category A? | What it actually defines | Companion |
|---|---|---|---|
| `0-aux` | none | generic list/option/number helpers (the spec's own tiny prelude) | [0-aux.wat](0-aux.wat) |
| `1-syntax` | **substantial — see below** | the entire surface syntax of WASM 2.0 | [1-syntax.wat](1-syntax.wat) |
| `2-syntax-aux` | none | auxiliary accessors/filters over 1-syntax's types | [2-syntax-aux.wat](2-syntax-aux.wat) |
| `3-numerics` | none | what every numeric/vector operator *computes* (semantics, not syntax) | [3-numerics.wat](3-numerics.wat) |
| `4-runtime` | none | the abstract machine's runtime state (addresses, instances, store, admin instructions) | [4-runtime.wat](4-runtime.wat) |
| `5-runtime-aux` | none | accessors/updates/growth over runtime state | [5-runtime-aux.wat](5-runtime-aux.wat) |
| `6-typing` | none | validation judgments (`Instr_ok`, `Module_ok`, subtyping) | [6-typing.wat](6-typing.wat) |
| `8-reduction` | none | small-step execution semantics (what "stepping" means) | [8-reduction.wat](8-reduction.wat) |
| `9-module` | none | allocation / instantiation / invocation algorithms | [9-module.wat](9-module.wat) |
| `A-binary` | none* | the binary (byte-level) encoding grammar | [A-binary.wat](A-binary.wat) |
| `B-soundness` | none | type-soundness proof scaffolding | [B-soundness.wat](B-soundness.wat) |

\* `A-binary.spectec`'s grammar rules produce the actual bytes of a `.wasm`
file — arguably the most literal "manifestation in WASM" of anything here —
but they're applied *by the compiler*, never written in `.wat` text
directly, which is why it's categorized as B for this exercise. Its
companion file explains the nuance and how to see its output directly with
`wasm2wat`/`xxd`.

(There is no `7-*.spectec` in this directory — the source numbering skips
it — so there's no `7-*.wat` either.)

## 1-syntax.spectec's category A, in full

Everything below is exercised in [1-syntax.wat](1-syntax.wat):

- **Value types**: `numtype` (i32/i64/f32/f64), `vectype` (v128), `reftype`
  (funcref/externref), `valtype`, `resulttype`, `packtype` (i8/i16, via SIMD
  shapes), `shape`/`ishape`/`fshape`/`pshape`.
- **Names & indices**: `name` (incl. non-ASCII), every index space
  (type/func/global/table/mem/elem/data/label/local).
- **External types**: `mut`, `limits`, `globaltype`, `functype`,
  `tabletype`, `memtype`, `elemtype`, `externtype`.
- **Operator vocabularies**: every `unop`/`binop`/`testop`/`relop`/`cvtop`
  name for i32/i64/f32/f64 (~131 instructions, all individually verified);
  every vector operator vocabulary (`vvunop`/`vvbinop`/`vvternop`/
  `vvtestop`/`vunop`/`vbinop`/`vtestop`/`vrelop`/`vshiftop`/`vextunop`/
  `vextbinop`/`vcvtop`, ~96 instructions on representative shapes, all 6
  shapes touched); `sx`, `sz`, `memarg`.
- **Instructions**: every alternative of `instr/parametric`, `instr/block`,
  `instr/br`, `instr/call`, `instr/num`, `instr/vec`, `instr/ref`,
  `instr/local`, `instr/global`, `instr/table`, `instr/elem`,
  `instr/memory`, `instr/data`.
- **Module structure**: `type`, `local`, `func`, `global`, `table`, `mem`,
  `elem` (all three `elemmode`s: active/passive/declare), `data` (both
  `datamode`s: active/passive), `start`, `externidx`, `export`, `import`,
  `module`.

Every demo function is zero-argument and self-contained, specifically so
the whole file can be verified in one shot:

```
wat2wasm 1-syntax.wat --debug-names -o 1-syntax.wasm
wasm-interp 1-syntax.wasm --run-all-exports --dummy-import-func
```

(All 278 zero-arg exports were cross-checked this way — the scalar/cvtop
section against independently-computed Python expected values, the SIMD
section by hand-decoding wasm-interp's hex lane output — plus the one
parameterized export (`add_and_log`) checked separately via `-r`/`-a`.
Every value matched. The one export that's *expected* to trap
(`ctrl_unreachable_traps`, demonstrating `UNREACHABLE`) does, and only
that one.)

**A version-compatibility note**, since wasmdebug compiles with
`--enable-all`: that flag enables post-2.0 proposals (e.g. typed function
references), and under it, `ref.func`'s inferred type in *code* becomes
more precise than plain `funcref`, which broke `table.set`/`table.fill`
with a `ref.func` argument until fixed. The fix (used in
[1-syntax.wat](1-syntax.wat)) is to route the reference through a
funcref-typed **global**, not a local — `ref.func` stays plain `funcref`
in constant-expression contexts (global initializers, elem segments) but
not inside regular function-body code. The file compiles and runs
identically under wat2wasm's plain WASM-2.0 defaults and under
`--enable-all`; both were checked.

## Everything else in 1-syntax.spectec (still category B)

For completeness: `syntax list(X)` (generic combinator); `bit`/`byte`/`uN`/
`sN`/`iN`/`fN`/`vN`/`char` as *generic parametrized families* (the
semantic domains, as opposed to one instantiation like `i32` which is
category A); `consttype`/`Inn`/`Fnn`/`Vnn`/`Pnn`/`Jnn`/`Lnn` (internal
grouping shorthands — you write "i32", never "Inn"); every `var`
declaration (pure metavariable naming); `$lanetype`/`$size`/`$psize`/
`$lsize`/`$isize`/`$jsize`/`$fsize` and inverses, `$sizenn*`/`$lsizenn*`,
`num_`/`pack_`/`lane_`/`vec_`/`$zero` (auxiliary size/domain functions);
`$dim`/`$shsize` (shape accessors).
