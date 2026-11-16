#!/usr/bin/env python3
"""compare_ops.py <inputs.txt> <expected.txt> <label>=<actual.txt> ...
Per operation: results equal bit for bit; results that are NaN on both sides with different bits (Lean
shows every NaN as 7ff8000000000000); real mismatches. Also the NaN bit patterns the C produced."""
import sys
from collections import Counter, defaultdict
EXP, MAN = 0x7ff0000000000000, 0x000fffffffffffff
nan = lambda b: (b & EXP) == EXP and (b & MAN) != 0
inp = [l.split() for l in open(sys.argv[1])]
exp = {}
for l in open(sys.argv[2]):
    op, i, h = l.split(); exp[(op, int(i))] = int(h, 16)
ops = list(dict.fromkeys(k[0] for k in exp))
bad = False
for pair in sys.argv[3:]:
    label, path = pair.split('=', 1)
    eq, np_, mm, pats, first = Counter(), Counter(), Counter(), defaultdict(Counter), {}
    seen = 0
    for l in open(path):
        op, i, h = l.split(); k = (op, int(i)); g = int(h, 16); e = exp[k]; seen += 1
        if nan(g): pats[op][f"{g:016x}"] += 1
        if g == e: eq[op] += 1
        elif nan(g) and nan(e): np_[op] += 1
        else:
            mm[op] += 1
            first.setdefault(op, f"x={inp[k[1]][0]} y={inp[k[1]][1]} lean={e:016x} c={g:016x}")
    tot_m = sum(mm.values()) + (len(exp) - seen)
    print(f"{label}: results={seen}/{len(exp)} bit_equal={sum(eq.values())} both_nan_other_bits={sum(np_.values())} MISMATCH={tot_m}")
    for op in ops:
        p = ' '.join(f"{b}x{c}" for b, c in pats[op].most_common(4))
        line = f"    {op:<9} equal={eq[op]:<6} nan_other_bits={np_[op]:<5} mismatch={mm[op]:<4} C NaN patterns: {p or '-'}"
        if op in first: line += f"   FIRST: {first[op]}"
        print(line)
    bad = bad or tot_m != 0
sys.exit(1 if bad else 0)
