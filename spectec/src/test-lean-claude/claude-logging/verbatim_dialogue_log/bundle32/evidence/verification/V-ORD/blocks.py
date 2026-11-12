#!/usr/bin/env python3
"""List helper blocks with line ranges and neighbours. Usage: python3 -I blocks.py DIR"""
import json
import os
import sys

D = sys.argv[1]
for k in ('cand1', 'OLD'):
    cs = json.load(open(os.path.join(D, k + '.json'), encoding='utf-8'))['constructs']
    print('=====', k)
    i = 0
    b = 0
    while i < len(cs):
        if cs[i]['helper']:
            j = i
            while j < len(cs) and cs[j]['helper']:
                j += 1
            b += 1
            p = cs[i - 1]
            n = cs[j] if j < len(cs) else None
            print(f"block {b:2d}: L{cs[i]['line']}-{cs[j-1]['end']} n={j-i} "
                  f"prev=[{p['kind']} {p['name']} L{p['line']}] "
                  f"next=[{n['kind']} {n['name']} L{n['line']}] first={cs[i]['name']} last={cs[j-1]['name']}")
            i = j
        else:
            i += 1
