# Response 26 (verbatim)

Answers both the main message and the mid-turn input.

---

## What `wfopt` does

`wfopt` is a hint read by the `Undep` pass ([undep.ml](spectec/src/middlend/undep.ml)). Undep runs before `Sideconditions` and `DefToRel`, and decides where `wf_*` premises go. The generator runs Undep in its default "minimal" mode, `WfMinimal`, and the hint adds a further optimization on top of that. For a definition `$f` marked `def $f hint(wfopt)`, it changes two things:

1. **The result expression gets no `wf` premise.** Each clause normally gets `wf_*` premises for the terms in its result expression (`get_wf_terms`, [undep.ml:329](spectec/src/middlend/undep.ml#L329)). With the hint, those result terms are skipped and only terms from the clause's premises still get one. The variables that stay unguarded are the ones that appear in the result (`quants_filtered`, [undep.ml:394](spectec/src/middlend/undep.ml#L394)).
2. **A `f_is_wf` theorem is generated instead.** That theorem is only generated for hinted definitions whose return type needs well-formedness ([undep.ml:682](spectec/src/middlend/undep.ml#L682)).

So the well-formedness of the result stops being a check inside the definition and becomes a separate proof obligation, the `_is_wf` theorem.

For relations it works the same way ([undep.ml:503](spectec/src/middlend/undep.ml#L503)). Using the relation's mode hint, it drops `wf` premises for conclusion variables that the inputs or premises already determine, and generates a `_is_wf` lemma about the outputs. That is why `Step` carries `hint(wfopt)`.

## The intent

The commits that introduced it are:
- `e3185b997`: "Implement wfopt hint that enables minimal optimization for relations. (Utilizing mode hint)"
- `853b8863c`: "Made wfopt be an optin hint for functions"

Without the hint, every definition that builds a value of a type with a `wf_` predicate gets a `wf` premise on its own result. A premise turns it into a relation, which bloats the model. `wfopt` is an opt-in way to say "this definition always produces well-formed results; don't check it, generate a lemma and I'll prove it". It keeps simple definitions as plain functions and moves well-formedness into proofs. That only works when the claim is actually true, and for `$fzero` it isn't (it fails at `N = 0`).

## What the diff shows (`todaywasm2.0.lean` → `todaywasm2.0_withoutwfopt.lean`)

The only spec change is removing `def $fzero hint(wfopt)` from `C-hints.spectec`. I checked that `todaywasm2.0.lean` is byte-identical to my run-`Sideconditions`-twice experiment output, so the comparison is against that model.

1. **`fzero` becomes a relation, and `fzero_is_wf` disappears.**
   ```lean
   inductive fun_fzero : N → fN → Prop where
     | fun_fzero_case_0 (v_N : Nat) :
       wf_fN v_N (fN.POS (fNmag.SUBNORM 0)) →
       fun_fzero v_N (fN.POS (fNmag.SUBNORM 0))
   ```
   - The result now gets a `wf_fN` premise. A definition with a premise is turned into a relation by `DefToRel`.
   - The false theorem is gone. Its condition is now a premise, so `fun_fzero 0 _` simply has no derivation.
   - `fun_fzero 32 _` and `fun_fzero 64 _` are derivable.
2. **The change spreads to the callers.**
   - `fun_zero` (cases 2 and 3) now takes `var_0` with `fun_fzero (Option.get! (size …)) var_0`.
   - `default_` also becomes a relation, because it calls a relation now. It is now `fun_default_`, with a `_before_…_case_7` relation for the fallback case. That helper's constructors 2 and 3 have an unused `(var_0 : fN)` binder, which is harmless.
   - `default__is_wf` now takes a premise `fun_default_ v_valtype var_0`.
3. **`Step_read.call_addr`** gets a `var_0_lst` with `Forall₂ … fun_default_ t_elem var_0_elem`, and the locals come from `var_0_lst`. The length premise `|var_0_lst| = |t_lst|` is present, from the second `Sideconditions` run.

That is the whole diff (101 lines).

## What this means for the proofs

- **Fixed:** the false `fzero_is_wf` is gone. You don't need a premise on `N` or a hand edit.
- **Proofs to update** in this file:
  - `zero_is_wf` must now invert `fun_fzero`, using the `iswf_fzero_32`/`iswf_fzero_64` facts I already proved.
  - `default__is_wf` gets an extra relation premise to invert.
  - `Step_read_is_wf`/`Step_is_wf` change in their `call_addr` case.
- **Downstream:** typing and progress proofs that use `default_` (function call, local initialization) must now provide `fun_default_` witnesses instead of computing `default_ t`. I haven't measured how many sites that is.

I only read and compared files; nothing was written.
