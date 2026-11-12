# `hint(builtin)` + type-family interaction — minimal repro

Minimal, from-scratch reproduction of why `nbytes_`/`cbytes_`/`zbytes_`/`reinterpret__`
compile to a hard `def ... := none` in `fixedlean3.0.lean` while sibling
`hint(builtin)` functions like `ibits_`, `iclz_`, `vbytes_` stay a genuine
`opaque` axiom. Same compiler, same pipeline flags as `test-lean-backend/diag.sh`,
just an 11-line spec instead of the real wasm-3.0 corpus.

## The spec (`toy.spectec`)

```
syntax numtype = I32 | I64 | F32 | F64
syntax vectype = V128

syntax Inn = I32 | I64
syntax Fnn = F32 | F64
syntax Vnn = V128

syntax num_(numtype)          ;; family header
syntax num_(Inn) = nat        ;; instantiation 1
syntax num_(Fnn) = nat        ;; instantiation 2

syntax vec_(vectype) = nat    ;; single, direct declaration -- no separate header

def $foo(numtype, num_(numtype)) : nat*  hint(builtin)
def $bar(vectype, vec_(vectype)) : nat*  hint(builtin)
```

`foo`/`bar` mirror `nbytes_`/`vbytes_` exactly: same arity, same `hint(builtin)`,
zero defining equations for either. The only structural difference is `num_`
(declared via a bare header line plus *two* separate instantiation bodies --
a genuine spectec "type family") versus `vec_` (one direct declaration, no
header, one instantiation).

## Regenerating

From `spectec/` (one level up):

```sh
./spectec test-lean/family-hint-repro/toy.spectec \
    --print-all-il-to "test-lean/family-hint-repro/il/%s.il" \
    --ite --let-intro-mech --typefamily-removal --remove-indexed-types --totalize \
    --else --else-simplification --uncase-removal --sub-expansion --pattern-simp --sub \
    --definition-to-relation --sideconditions --alias-demut --improve-ids --single-pattern-match \
    --lean -o test-lean/family-hint-repro/toy.lean

# same run again with --print-il-as-ast, into il/ast_*.il, to see the raw hint list
```

These are the exact stage flags `test-lean-backend/diag.sh` uses for the real
wasm-1/2/3.0 specs.

## What to look at

**`il/ast_02-let-intro-mech.il`** (before `typefamily-removal`) -- both defs
carry only the `builtin` hint:
```
(HintD (DecH "foo" (hint "builtin" "{}")))
(HintD (DecH "bar" (hint "builtin" "{}")))
```

**`il/ast_03-typefamily-removal.il`** -- they diverge right here. A synthetic
`partial` hint gets injected for `foo`, not for `bar`:
```
(HintD (DecH "foo" (hint "partial" "{}")))   <- injected
(HintD (DecH "foo" (hint "builtin" "{}")))
(HintD (DecH "bar" (hint "builtin" "{}")))    <- untouched
```

**`il/04-remove-indexed-types.il`** -- still identical in shape, zero clauses
either way:
```
def $foo(numtype : numtype, num_ : num_) : nat*
def $bar(vectype : vectype, vec_ : vec_) : nat*
```

**`il/05-totalize.il`** -- the consequence. `foo` gets Option-wrapped with an
unconditional `none`; `bar` is untouched:
```
def $foo(numtype : numtype, num_ : num_) : nat*?
  def $foo{x0 : numtype, x1 : num_}(x0, x1) = ?()

def $bar(vectype : vectype, vec_ : vec_) : nat*
```

**`toy.lean`** -- final output:
```lean
def foo (v_numtype : numtype) (v_num_ : num_) : Option (List Nat) :=
  none

opaque bar (v_vectype : vectype) (v_vec_ : vec_) : List Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption
```

## The mechanism

`typefamilyremoval.ml:572-574`:

```ocaml
| DecD (id, params, typ, clauses) when List.length params > 1 && List.exists (is_type_family_param env) params -> 
    let totalize_hint = HintD (DecH (id, [totalize_hint]) $ def.at) in
    [DecD (...); totalize_hint]
```

Any multi-parameter `def` with a parameter whose type is a genuine spectec
"type family" (`Env.find_opt_typ` reports more than one instantiation, or one
instantiation whose argument pattern isn't a plain variable/type-param passthrough
-- see `check_type_family` / `check_normal_type_creation`, same file, lines
121-125 and 62-69) gets this synthetic `hint(partial)` unconditionally --
independent of `hint(builtin)`, independent of whether the function has any
actual clauses to totalize. `totalize.ml` then sees that hint and Option-wraps
the def with a `none` catch-all, same as it would for a genuinely
partially-covered function.

`num_(numtype)` has two instantiations (`num_(Inn)`, `num_(Fnn)`), so it trips
the guard. `vec_(vectype)` has exactly one, so it doesn't. This has nothing to
do with `numtype` (4 alternatives) vs. `vectype` (1 alternative) directly --
it's the *second* parameter's type family-ness that decides it, which happens
to correlate with the first parameter's alternative count in the real spec
but isn't the same check.

`hint(builtin)` itself is never read anywhere in this path -- it's only
consumed by the reference interpreter backend
(`backend-interpreter/interpreter.ml:815`), to look up a hand-written
implementation. In the Lean pipeline it's inert; the opaque-vs-`Option`
decision is a side effect of the type-family flattening pass, applied
regardless of what the builtin hint says.

## Why this matters for the real spec

`nbytes_`, `cbytes_`, `zbytes_`, `reinterpret__` all take a `numtype`/
`storagetype`/`Cnn`-typed dependent second parameter with 2+ real
instantiations, so they get auto-tagged partial and totalized to
`:= none` -- making the `load`/`store`/`reinterpret`/GC-array-init reduction
rules that depend on them permanently unsatisfiable in `fixedlean3.0.lean`.
`ibits_`/`iclz_`/`fadd_`/`vbytes_` escape it only because their own dependent
parameter (or lack of one) doesn't happen to resolve to a multi-instantiation
family -- not because of anything about their actual partiality. See
`spectec/BEQ_INHABITED_RELD_FIX_PLAN.md`-adjacent audit notes for the full
write-up on `fixedlean3.0.lean`.

A one-line fix at the same guard -- skip the injection when `clauses = []`,
since there's nothing to totalize when no clause was ever written -- would
let a zero-equation `hint(builtin)` def fall through to the ordinary
`OpaqueConstruct` handling regardless of its parameters' family-ness.
