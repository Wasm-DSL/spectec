"""bundle31 cleanup patch, applied to the merged final sources after postpatch31/docpatch31.
Comment/doc fixes flagged by the report writers and verifiers, the rename ENone -> Etestop, a
robust proof of Moduleinst_ok_data_addr, and deletion of the 8 new lemmas that nothing uses.
Every edit is scoped to one top-level unit (declaration + its doc comment) and must match once.
Usage: cleanup31.py <dir with the final .lean sources> (edited in place)"""
import sys
B = '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/b31'
sys.path.insert(0, B + '/tools')
sys.path.insert(0, '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/tools')
from units31 import units
d = sys.argv[1]
log = []

def load(m):
    return units(open(f'{d}/{m}.lean', encoding='utf-8').read())

def save(m, us):
    open(f'{d}/{m}.lean', 'w', encoding='utf-8').write('\n'.join(u['text'] for u in us))

def edit(us, name, old, new, count=1):
    hits = [u for u in us if (u['name'] == name if name else old in u['text'])]
    assert len(hits) == 1, (name, old[:60], len(hits))
    u = hits[0]
    assert u['text'].count(old) == count, (name, old[:60], u['text'].count(old))
    u['text'] = u['text'].replace(old, new)
    log.append(f'edit {name or "(section text)"}: {old.strip()[:50]!r}')

def delete(us, name):
    k = [i for i, u in enumerate(us) if u['name'] == name]
    assert len(k) == 1, name
    del us[k[0]]
    log.append(f'delete {name}')

# ---------------- HelperLemmas
us = load('HelperLemmas')
edit(us, None,
'''type safety proof), plus all 21 axioms of `axioms.v` (at the end of the file).''',
'''type safety proof), plus all 21 axioms of `axioms.v` (after Section 9) and, at the end of the
file, Lean-only infrastructure for the model regenerated with `sideconditions_on_defs`: function
views of the size relations the proofs use, of `fzero` and of `default_`, and inversion lemmas for
the state lookups.''')
edit(us, None,
'''Since `sideconditions_on_defs` (user commit `12b021fc9`), the backend turns every spec function
whose body uses `!` or indexing into a relation `fun_<name>`, even when the function is total. The
downstream proofs were written against the functions, so this section restores a function view of
each total one they use, with the definition it had in the old model (`OLD_wasm2.0.lean`), and
proves that the relation holds of it (`fun_<name>_<name>`) and that it is the relation's only output
(`fun_<name>_eq`). Partial functions (`$table`, `$mem`, `$with_*`, …) get no function view: the
proofs use their relations, whose premises carry the bounds. Not a port of any Rocq lemma. -/''',
'''Since `sideconditions_on_defs` (user commit `12b021fc9`), the backend turns every spec function
that needs a side condition (a `!`, an index, or, for `$fzero`, the well-formedness of its result),
directly or through another such function, into a relation `fun_<name>`, even when the function is
total. The downstream proofs were written against the functions, so this section restores a
function view of the size functions the proofs use (`lsize`, `isize`, `jsize`, `sizenn`, `sizenn1`,
`lsizenn`, `lsizenn1`, `lsizenn2`), of `fzero` and of `default_` (names the model no longer uses),
with the definitions they had in the old model (`OLD_wasm2.0.lean`), and proves, as far as the
proofs need them, that the relation holds of the view (`fun_<name>_<name>`; for `default_`,
`fun_default_default`) and that the view is the relation's only output (`fun_<name>_eq`;
`fun_default_eq`). `fzero` is the exception: `fun_fzero` holds only at the
widths 32 and 64 (`fun_fzero_32`, `fun_fzero_64`). The other relations, total or partial
(`fun_zero`, `fun_unop_`, `$table`, `$with_*`, …), are used through their constructors, whose
premises carry the bounds. Not a port of any Rocq lemma. -/''')
for n in ['fun_isize_eq', 'fun_jsize_eq', 'fun_sizenn1_sizenn1', 'fun_fzero_wf', 'fun_func_inv', 'fun_data_inv']:
    delete(us, n)
edit(us, None,
'''The lookups `fun_type`, `fun_func`, `fun_global`, `fun_table`, `fun_mem`, `fun_elem`, `fun_data`
and `fun_local` are relations with one constructor each. These lemmas read off its premises (the
index bounds) and its output, for a lookup whose output is a term rather than a variable (`cases`
cannot unify such an output with the constructor's indexing expression). -/''',
'''The state lookups are relations with one constructor each. For those the proofs invert
(`fun_type`, `fun_global`, `fun_table`, `fun_mem`, `fun_elem`, `fun_local`), these lemmas return
the constructor's premises (the index bounds) and its output as an equation. They are needed when
the output is a term, which `cases` cannot unify with the constructor's indexing expression
(`bt_inversion`), and are convenient elsewhere. -/''')
edit(us, 'splice_eq_list_slice_update',
'''    apply to the Lean `with_mem`. -/''',
'''    apply to the model's `$with_mem` (the relation `fun_with_mem`). -/''')
save('HelperLemmas', us)

# ---------------- ExtensionLemmas
us = load('ExtensionLemmas')
edit(us, 'bt_inversion',
'''/-- Rocq `extension_lemmas.v:870` `bt_inversion`. The block type elaboration `fun_blocktype`
    (a relation since `sideconditions_on_defs`; it was a function) agrees with the declarative
    `Blocktype_ok` relation's chosen functype. -/''',
'''/-- Rocq `extension_lemmas.v:870` `bt_inversion`. The block type elaboration `fun_blocktype`
    agrees with the declarative `Blocktype_ok` relation's chosen functype.
    **Note:** Rocq's premise is the equation `fun_blocktype (mk_state v_S r_v_f) b_lstt =
    (bt1 :-> bt2)`; `fun_blocktype` is a relation here (`sideconditions_on_defs`), so the premise
    is its witness `fun_blocktype (state.mk_state v_S r_v_f) b_lstt (mkFunctype bt1 bt2)`. -/''')
save('ExtensionLemmas', us)

# ---------------- TypePreservation
us = load('TypePreservation')
edit(us, 'num_default',
'''/-- Rocq `type_preservation.v:19` `num_default`. Default/zero value per numtype; used to
    build default locals in `t_read_preservation`'s Call_addr/frame-invocation case. -/''',
'''/-- Rocq `type_preservation.v:19` `num_default`. Default/zero value per numtype (`fzero` is the
    HelperLemmas function view of `fun_fzero`). Only `num_default_is_well_formed` uses it; the
    default locals of `t_read_preservation`'s `call_addr` case come from `default_`
    (`default_vals_ok`). -/''')
edit(us, 'wf_store_mem_update',
'''    with `list_slice_update`; the Lean `with_mem` (`splice`) is bridged to it by''',
'''    with `list_slice_update`; the model's `$with_mem` (the relation `fun_with_mem`, which writes
    with `splice`) is bridged to it by''')
edit(us, 'reduce_inst_unchanged_aux',
'''    congruence rules that need the induction hypothesis; `ctxt_frame` is in
    the first group, since it changes only the *inner* frame. -/''',
'''    congruence rules that need the induction hypothesis; `ctxt_frame` needs no
    induction hypothesis either, since it changes only the store and the *inner* frame. -/''')
edit(us, 'store_extension_reduce_aux',
'''    carry the inner configuration's `wf_config` as a premise), the store-writing rules invert
    their `fun_with_*` premise and go to the per-rule lemmas above, and every other rule leaves
    the store unchanged. -/''',
'''    carry the inner configuration's `wf_config` as a premise), the store-writing rules invert
    their `fun_with_*` premise (the four memory stores hand `fun_with_mem` to `with_mem_store_ok`,
    which inverts it) and go to the per-rule lemmas above, and every other rule leaves the store
    unchanged. -/''')
edit(us, 't_read_preservation',
'''    `Forall₂` is zip-based and does not, and the `local.get` case needs the length to index the
    locals (the same kind of deviation as `funcinst_same`'s `hlen`). The only caller,''',
'''    `Forall₂` is zip-based and does not, and the `local.get` case uses the length (with
    `Forall2_nth_of_length`) to index the locals (the same kind of deviation as `funcinst_same`'s
    `hlen`; since `sideconditions_on_defs` the rule's `fun_local` premise also bounds the index by
    `F.LOCALS`, so there the length is convenient rather than necessary). The only caller,''')
save('TypePreservation', us)

# ---------------- TypeProgress
us = load('TypeProgress')
delete(us, 'fun_func_typed')
delete(us, 'Moduleinst_ok_func_addr')
edit(us, 'Moduleinst_ok_data_addr',
'''  have hi' : i < minst.DATAS.length := (Moduleinst_ok_lengths s minst C h).2.2.2.2.1 ▸ hi
  refine ⟨hi', ?_⟩
  cases h with
  | mk_Moduleinst_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdb =>
    exact hdb _ (by rw [getElem!_pos _ i hi']; exact List.getElem_mem hi')''',
'''  have hi' : i < minst.DATAS.length := (Moduleinst_ok_lengths s minst C h).2.2.2.2.1 ▸ hi
  obtain ⟨_, hb, _⟩ := (minst_invert_datas s minst C C h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).2
    minst.DATAS[i]! (by rw [getElem!_pos _ i hi']; exact List.getElem_mem hi')
  exact ⟨hi', hb⟩''')
edit(us, 'testop_not_none',
'''/-- Rocq `type_progress.v:1829` `testop_not_none`. The function `fun_testop_` is defined
    (`≠ none`) on a well-formed operand and test operator. Restated: `fun_testop_` is now a''',
'''/-- Rocq `type_progress.v:1829` `testop_not_none`. A well-formed test operator applied to a
    well-formed number of the same type is defined. Restated: `fun_testop_` is now a''')
edit(us, 't_progress_be_testop', 'ENone', 'Etestop', count=3)
edit(us, 'zero_lane_wf',
'''`z` with `fun_zero nt z`; it used to take the function application `fun_zero nt`.) -/''',
'''`z` with `fun_zero nt z`; it used to be stated for the function application `fun_zero nt`.) -/''')
edit(us, 't_progress_be_elem_drop',
'''  rw [Hcontext] at Hlen
  rcases vcs with _ | ⟨v1, vcs1⟩
  · -- Rocq: `exists s', f', []. ... by apply: Step__elem_drop.`
''',
'''  -- Lean-only: the bound `x < |C'.ELEMS|` for the premise of `fun_with_elem`
  rw [Hcontext] at Hlen
  rcases vcs with _ | ⟨v1, vcs1⟩
  · -- Rocq: `case Estate: (with_elem (mk_state s f) x []) => [s' f']. exists s', f', [].
    --        rewrite -Estate. by apply: Step__elem_drop.` (Lean: `fun_with_elem` is a relation;
    --        its constructor gives the new state directly, so there is no case split.)
''')
edit(us, 't_progress_be_table_init',
'''  rw [Hcontext] at Hlenx1 Hlenx2
''',
'''  -- Lean-only: the table and the element segment as witnesses of the relations `fun_table` and
  -- `fun_elem` (`fun_table_typed`/`fun_elem_typed`, from `Moduleinst_ok` and the index bounds)
  rw [Hcontext] at Hlenx1 Hlenx2
''')
edit(us, 't_progress_be_data_drop',
'''    --        rewrite -Estate. by eapply Step__data_drop.`
''',
'''    --        rewrite -Estate. by eapply Step__data_drop.` (Lean: `fun_with_data` is a relation;
    --        its constructor gives the new state directly, so there is no case split.)
''')
for n in ['t_progress_be_load_val', 't_progress_be_load_pack']:
    edit(us, n,
'''        --        by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).`
''',
'''        --        by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).` (the Lean lemma also
        --        takes the memory instance and its `fun_mem` witness `Hm`)
''')
edit(us, 'vrelop_some',
'''    -- choose `v_Inn` with `isize v_Inn = size F` (Rocq: `exact: (eqxx (isize Inn_I32))`)
''',
'''    -- choose the result lane width: `var_1 := isize Inn.I32` (resp. `Inn.I64`) closes
    -- `var_1 = size F`, then `fun_isize_isize` fixes `v_Inn` (Rocq: `exact: (eqxx (isize Inn_I32))`)
''')
edit(us, 'vrelop_some',
'''    all_goals (apply Exists.intro; constructor)
    all_goals try exact fun_lsizenn_lsizenn _
''',
'''    all_goals (apply Exists.intro; constructor)
    -- Lean-only: the new `fun_lsizenn (lanetype_Jnn J) var_0` premise fixes the lane width
    all_goals try exact fun_lsizenn_lsizenn _
''')
edit(us, 'vunop_real',
'''    -- lane facts, with `rfl` last so that it only fills the remaining metavariables.
''',
'''    -- lane facts or the size witness `Hsz` (the new `fun_lsizenn` premise), with `rfl` last so
    -- that it only fills the remaining metavariables.
''')
for n in ['t_progress_be_vload_zero', 't_progress_be_vload_lane', 't_progress_be_vstore', 't_progress_be_vstore_lane']:
    edit(us, n,
'''  right
  subst Hcontext
''',
'''  right
  -- memory `0` exists (`C.MEMS = C'.MEMS`, typed by the frame's module)
  subst Hcontext
''')
edit(us, 'wf_config_mem_bytes',
'''/-- Rocq `type_progress.v:2464` `wf_config_mem_bytes`. In a well-formed configuration, the bytes
    of a memory found by `fun_mem` are well-formed. (`fun_mem` is a relation since
    `sideconditions_on_defs`; this used to take the function application
    `fun_mem (state.mk_state s f) x`.) -/''',
'''/-- Rocq `type_progress.v:2464` `wf_config_mem_bytes`. In a well-formed configuration, the bytes
    of a memory found by `fun_mem` are well-formed. **Deviation:** Rocq concludes about
    `BYTES (fun_mem (mk_state s f) x)`; `fun_mem` is a relation here (`sideconditions_on_defs`),
    so the lemma takes its witness `fun_mem (state.mk_state s f) x mi` and concludes for `mi`. -/''')
save('TypeProgress', us)
print('cleanup31:', len(log), 'edits'); print('\n'.join('  ' + l for l in log))
