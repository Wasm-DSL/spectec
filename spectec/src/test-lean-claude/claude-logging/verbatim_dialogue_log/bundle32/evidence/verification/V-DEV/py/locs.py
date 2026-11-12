import re, sys
W = sys.argv[1]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
go = rd(W + '/G_old.lean'); gn = rd(W + '/G_new.lean')
pat = re.compile(r'1-syntax\.spectec:(\d+)\.(\d+)-(\d+)\.(\d+)')
# collect all 1-syntax refs in order
ro = [m.groups() for l in go for m in pat.finditer(l)]
rn = [m.groups() for l in gn for m in pat.finditer(l)]
print('refs old', len(ro), 'new', len(rn))
same=[]; shifted=[]; other=[]
for a,b in zip(ro,rn):
    a=tuple(map(int,a)); b=tuple(map(int,b))
    if a==b: same.append(a)
    elif (a[0]-1,a[1],a[2]-1,a[3])==b: shifted.append(a)
    else: other.append((a,b))
print('same', len(same), 'max start line among same', max(x[0] for x in same), 'max end line among same', max(x[2] for x in same))
print('shifted', len(shifted), 'min start line among shifted', min(x[0] for x in shifted))
print('other', other)
# any partially shifted (start unchanged but end shifted)?
