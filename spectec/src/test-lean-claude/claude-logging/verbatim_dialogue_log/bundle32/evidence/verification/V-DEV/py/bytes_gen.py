import re, sys
W = sys.argv[1]
raw_go = open(W + '/G_old.lean', 'rb').read(); raw_gn = open(W + '/G_new.lean', 'rb').read()
go = raw_go.decode('utf-8').split('\n')
locpat = re.compile(r'1-syntax\.spectec:(\d+)\.(\d+)-(\d+)\.(\d+)')
TH = 552
def shiftloc(m):
    a,b,c,d = map(int, m.groups())
    if a >= TH: a -= 1
    if c >= TH: c -= 1
    return '1-syntax.spectec:%d.%d-%d.%d' % (a,b,c,d)
ipat = re.compile(r'(?<![A-Za-z0-9_])(instr_case_|admininstr_case_)(\d+)(?![A-Za-z0-9_])')
def ren(m):
    k = int(m.group(2))
    if k >= 20: k -= 1
    return m.group(1) + str(k)
EXT = {1925, 2034, 11544, 11625, 11747}
out = '\n'.join(locpat.sub(shiftloc, ipat.sub(ren, l)) for i,l in enumerate(go) if (i+1) not in EXT).encode('utf-8')
print('T(G_old) bytes == G_new bytes:', out == raw_gn)
# which spectec files are referenced by location comments, and do any non-1-syntax refs differ?
