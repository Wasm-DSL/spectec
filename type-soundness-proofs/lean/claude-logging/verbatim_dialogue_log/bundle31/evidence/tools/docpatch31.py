"""bundle31 header-doc patch (applied after the merge): the status paragraphs of TypePreservation.lean
and TypeProgress.lean still said that t_preservation / t_progress depend on sorried generated
`*_is_wf` theorems; since commit e6273da37 those are axioms of the model, and after this repair
nothing depends on sorry. Also adds one sentence on the relational model.
Usage: docpatch31.py <dir with TypePreservation.lean and TypeProgress.lean> (edited in place)"""
import sys
d = sys.argv[1]

fn = d + '/TypePreservation.lean'
s = open(fn, encoding='utf-8').read()
old = '''rules push `$iadd_(32, i, 1)`). The only `sorry`s that `t_preservation` still depends on
are generated `*_is_wf` theorems about functions that are `opaque` in `wasm2.0.lean` (`Axiom`s in
Rocq, where the same theorems are `Admitted`); see `claude-logging/for-claude/is_wf_theorems.md`.
`num_default_is_well_formed` is proved (its Rocq statement is commented out upstream).
'''
new = '''rules push `$iadd_(32, i, 1)`). `t_preservation` depends on no `sorry`: besides Lean's standard
axioms, `#print axioms` lists only the model's `*_is_wf` axioms for the functions that are
`opaque` in `wasm2.0.lean` (`Axiom`s in Rocq too, where these theorems are `Admitted`).
`num_default_is_well_formed` is proved (its Rocq statement is commented out upstream).

Since the model was regenerated with `sideconditions_on_defs` (user commit `12b021fc9`), the state
lookups and updates (`fun_table`, `fun_with_mem`, …) are relations whose premises carry the index
bounds. The proofs here invert them, mostly through the inversion lemmas at the end of
`HelperLemmas.lean`.
'''
assert s.count(old) == 1, 'TypePreservation header changed'
s = s.replace(old, new)
open(fn, 'w', encoding='utf-8').write(s)

fn = d + '/TypeProgress.lean'
s = open(fn, encoding='utf-8').read()
old = '''`#sorry_deps TLC.t_progress` lists only generated numeric `*_is_wf` theorems about functions that
are `opaque` in Lean (`Axiom`s in Rocq, whose `*_is_wf` are all `Admitted` there too); see
`claude-logging/for-claude/is_wf_theorems.md`. `#print axioms` adds the project axioms that mirror
Rocq's `axioms.v` (`ishl_wf`/`ishr_wf` were deleted with Rocq's, since `ishl_`/`ishr_` now take an
`iN(N)` shift amount and the generated `ishl__is_wf`/`ishr__is_wf` apply directly).
'''
new = '''`t_progress` depends on no `sorry`. Besides Lean's standard axioms, `#print axioms` lists the model's
`*_is_wf` axioms for the functions that are `opaque` in Lean (`Axiom`s in Rocq too, whose `*_is_wf`
are all `Admitted` there) and the project axioms that mirror Rocq's `axioms.v` (`ishl_wf`/`ishr_wf`
were deleted with Rocq's, since `ishl_`/`ishr_` now take an `iN(N)` shift amount and the generated
`ishl__is_wf`/`ishr__is_wf` apply directly).

Since the model was regenerated with `sideconditions_on_defs` (user commit `12b021fc9`), the state
lookups and updates are relations whose premises carry the index bounds, so progress has to supply
those bounds; the section "Lean-only: index bounds for the state lookups" derives them from
`Moduleinst_ok`.
'''
assert s.count(old) == 1, 'TypeProgress header changed'
s = s.replace(old, new)
open(fn, 'w', encoding='utf-8').write(s)
print('docpatch31: headers of TypePreservation.lean and TypeProgress.lean updated')

old = """With `sideconditions_on_defs`, the state lookups `fun_global`, `fun_table`, `fun_mem`, `fun_elem`,
`fun_data`, `fun_func` and `fun_type` are relations whose premises bound the index into the module
instance and the address into the store. Progress has to supply those premises. `Moduleinst_ok`
provides both: the instance's address lists have the context's lengths (`Moduleinst_ok_lengths`),
and every address in them is in bounds for the store (`minst_invert_*`). The `*_addr` lemmas
combine the two, and the `fun_*_typed` lemmas build the lookup from a typed index. -/"""
new = """With `sideconditions_on_defs`, the state lookups `fun_global`, `fun_table`, `fun_mem`, `fun_elem`,
`fun_data` and `fun_type` are relations whose premises bound the index into the module instance
and (except for `fun_type`) the address into the store; the updates `fun_with_*` need the first
bound too. Progress has to supply those premises. `Moduleinst_ok` provides both: the instance's
address lists have the context's lengths (`Moduleinst_ok_lengths`), and every address in them is
in bounds for the store (`minst_invert_*`). The `*_addr` lemmas combine the two, and the
`fun_*_typed` lemmas build the lookup from a typed index. -/"""
assert s.count(old) == 1, 'infra section doc changed'
s = s.replace(old, new)
open(fn, 'w', encoding='utf-8').write(s)
print('docpatch31: infra section doc reflowed')
