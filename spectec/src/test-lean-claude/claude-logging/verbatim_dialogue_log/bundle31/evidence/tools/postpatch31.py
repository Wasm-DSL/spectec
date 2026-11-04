"""bundle31 post-merge patch of TypeProgress.lean (not part of any agent's assignment):
`mem_bytes_wf` gets an index bound (its old out-of-range case read the default `meminst`, the only
default-dependent theorem of the downstream modules), and `wf_config_mem_bytes` passes that bound,
which `fun_mem_inv` provides. Statement of `wf_config_mem_bytes` unchanged.
Usage: postpatch31.py <TypeProgress.lean> (edited in place)"""
import sys, re
B = '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/b31'
fn = sys.argv[1]
s = open(fn, encoding='utf-8').read()
# users of mem_bytes_wf other than wf_config_mem_bytes would break: refuse
uses = [m.start() for m in re.finditer(r'(?<![\w.\'])mem_bytes_wf(?![\w\'])', s)]
a = s.index('/-- Rocq `type_progress.v:2451` `mem_bytes_wf`.')
b = s.index('/-- Rocq `type_progress.v:2464` `wf_config_mem_bytes`.')
c = s.index('/-! ### Lean-only: index bounds for the state lookups')
assert a < c < b, 'unexpected layout'
others = [u for u in uses if not (a <= u < s.index('\n\n', s.index('theorem wf_config_mem_bytes')) )]
# the only allowed occurrences: the definition itself (a..c) and inside wf_config_mem_bytes
wcm_start = s.index('theorem wf_config_mem_bytes')
wcm_end = s.index('/-- Rocq `type_progress.v:2479` `all_and_Forall`.')
bad = [u for u in uses if not (a <= u < c or wcm_start <= u < wcm_end)]
assert not bad, f'mem_bytes_wf used elsewhere at offsets {bad}: adapt those uses first'
new_mb = open(B + '/postpatch/mem_bytes.part', encoding='utf-8').read()
s = s[:a] + new_mb + s[c:]
wcm_start = s.index('theorem wf_config_mem_bytes')
wcm_end = s.index('/-- Rocq `type_progress.v:2479` `all_and_Forall`.')
body = s[wcm_start:wcm_end]
k = body.index(':= by\n') + len(':= by\n')
new_body = body[:k] + open(B + '/postpatch/wf_config_mem_bytes_proof.part', encoding='utf-8').read() + '\n'
s = s[:wcm_start] + new_body + s[wcm_end:]
open(fn, 'w', encoding='utf-8').write(s)
print('postpatch31: mem_bytes_wf bounded; wf_config_mem_bytes proof updated')
