import re, sys, json
sys.path.insert(0, '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/tools')
from leanparse import items
B = '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/b31'
CL = {
 'P1': ('TypePreservation', 't_read_preservation default_val_ok'),
 'P23': ('TypePreservation', "t_preservation_type_aux t_preservation_vs_type'_aux store_extension_reduce_aux table_grow_store_ok with_mem_store_ok memory_grow_store_ok reduce_inst_unchanged_aux num_default_is_well_formed"),
 'Q1': ('TypeProgress', 'invert_typeof_I32 invert_typeof_I64 invert_typeof_I32_wf wf_fN_num_ binop_total relop_total cvtop_total binop_before relop_before cvtop_before unop_not_none testop_not_none t_progress_be_unop t_progress_be_testop'),
 'Q2': ('TypeProgress', 'wf_lane_Jnn_inv wf_lane_Jnn_some wf_lane_Fnn_inv Forall_lane_map_wf Forall_lane_fop_wf iabs_lane_total vunop_real zip_lane_wf zip_flane_wf zip_lane_wf2 vbinop_some vrelop_some wf_ishape_inv'),
 'Q3': ('TypeProgress', 't_progress_be_vvunop t_progress_be_vvbinop t_progress_be_vvternop t_progress_be_vshiftop t_progress_be_vbitmask t_progress_be_vswizzle t_progress_be_vshuffle t_progress_be_vextract_lane'),
 'Q4': ('TypeProgress', 't_progress_be_vextunop t_progress_be_vextbinop t_progress_be_vnarrow t_progress_be_vcvtop vcvtop_lane_total zero_lane_wf vcvtop_step_zero vcvtop_zero_numtype vcvtop_full_lsize'),
 'Q5': ('TypeProgress', 't_progress_be_block t_progress_be_loop t_progress_be_br_table t_progress_be_local_get t_progress_be_global_get t_progress_be_global_set call_indirect_progress t_progress_e_call_addr t_progress_be_table_get t_progress_be_table_set t_progress_be_table_size t_progress_be_table_fill t_progress_be_table_copy t_progress_be_table_init t_progress_be_elem_drop'),
 'Q6a': ('TypeProgress', 't_progress_be_memory_size t_progress_be_memory_fill t_progress_be_memory_copy t_progress_be_memory_init t_progress_be_data_drop t_progress_be_load_val t_progress_be_load_pack t_progress_be_store_val t_progress_be_store_pack'),
 'Q6b': ('TypeProgress', 't_progress_be_vload_val t_progress_be_vload_pack t_progress_be_vload_splat t_progress_be_vload_zero t_progress_be_vload_lane t_progress_be_vstore t_progress_be_vstore_lane vstore_lane_progress'),
}
rep = json.load(open(B + '/cascade2/report.json'))
broken = {}
for m in ['TypePreservation', 'TypeProgress']:
    for n in rep[m]['sorried']: broken[n] = (m, 'sorried')
    for n in rep[m]['deleted']: broken[n] = (m, 'deleted')
owner = {}
for lab, (m, names) in CL.items():
    for n in names.split():
        assert n in broken and broken[n][0] == m, (lab, n)
        assert n not in owner, n
        owner[n] = lab
assert set(owner) == set(broken), set(broken) - set(owner)
# users computed on the ORIGINAL sources (src2: original proofs + bundle31 infra)
decls = []
for m in ['HelperLemmas', 'Subtyping', 'TypingLemmas', 'TypePreservationPure', 'ExtensionLemmas', 'TypePreservation', 'TypeProgress']:
    for it in items(open(B + '/src2/' + m + '.lean').read()):
        if it['name']: decls.append((m, it['name'], it['text']))
def refs(text, name):
    return re.search(r'(?<![\w.\'])' + re.escape(name) + r'(?![\w\'])', text) is not None
info = {}
for n in owner:
    users = sorted(u for (m, u, t) in decls if u != n and refs(t, n))
    info[n] = {'owner': owner[n], 'module': broken[n][0], 'kind': broken[n][1],
               'users_same_cluster': [u for u in users if owner.get(u) == owner[n]],
               'users_other_clusters': [f'{u} ({owner[u]})' for u in users if u in owner and owner[u] != owner[n]],
               'users_not_broken': [u for u in users if u not in owner]}
json.dump({'clusters': CL, 'info': info}, open(B + '/clusters.json', 'w'), indent=1)
for lab, (m, names) in CL.items():
    print('=====', lab, m)
    for n in names.split():
        i = info[n]
        shared = i['users_other_clusters'] or i['users_not_broken']
        print(f"  {n:32} {i['kind']:8} {'SHARED' if shared else 'local '} other={i['users_other_clusters']} notbroken={i['users_not_broken'][:6]}{'...' if len(i['users_not_broken'])>6 else ''}")
