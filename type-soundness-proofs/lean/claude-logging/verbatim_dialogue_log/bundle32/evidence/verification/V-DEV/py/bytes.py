import re, sys
W = sys.argv[1]; OUT = sys.argv[2]
raw_old = open(W + '/OLD.lean', 'rb').read(); raw_c = open(W + '/cand1.lean', 'rb').read()
print('CR bytes old/cand:', raw_old.count(b'\r'), raw_c.count(b'\r'), 'BOM:', raw_old[:3] == b'\xef\xbb\xbf', raw_c[:3] == b'\xef\xbb\xbf', 'ends with newline:', raw_old.endswith(b'\n'), raw_c.endswith(b'\n'))
old = raw_old.decode('utf-8').split('\n')
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
EXT = {1953, 2062, 12206, 12287, 12409}
out = [locpat.sub(shiftloc, ipat.sub(ren, l)) for i,l in enumerate(old) if (i+1) not in EXT]
data = '\n'.join(out).encode('utf-8')
open(OUT, 'wb').write(data)
print('T(OLD) bytes == cand1 bytes:', data == raw_c, len(data), len(raw_c))
