#!/usr/bin/env python3
"""Compare the output of a compiled batch with the expected results from evalFn.

usage: compare.py <expected.txt> <label>=<actual.txt> ...

expected.txt lines:  <prog> <case> <fn> some <r> <out>...   |   <prog> <case> <fn> none   |   # comment
actual lines:        <prog> <case> <r> <out>...

<out>... are, in parameter order: the final value of every inout integer or float, the final elements
of every inout array or slice, and the elements of every by-value array or slice as the C caller sees
them after the call (the expected file has the input there: the callee must not have touched it).

Integers are decimal. A double is `f:` followed by the 16 hexadecimal digits of its bit pattern, and is
compared ON THE BIT PATTERN: +0.0 and -0.0 differ, a value and its neighbour differ. One class of
difference is not a mismatch and is counted separately as `nan_payload`: both sides are NaN but the
bits (sign, quiet bit, payload) differ. Reason: Tenon's values are Lean `Float`s and Lean's only window on
the bits, `Float.toBits`, returns 7ff8000000000000 for every NaN, so the reference cannot say which NaN
is expected. (For a by-value slice the expected bits are the input bits, exactly.)

A case is COMPARED only if evalFn returned `some`. A `none` case is outside the guarantee: it is
counted as SKIPPED, never as a pass, and it is an ERROR if the C side produced a line for it (the
driver must not even call the C function on such an input).
Exit status 0 only if there is no mismatch and no error.
"""
import sys

EXP = 0x7ff0000000000000
MAN = 0x000fffffffffffff


def is_nan(b):
    return (b & EXP) == EXP and (b & MAN) != 0


def tok(x):
    """int -> ('i', v); f:hex -> ('f', bits)."""
    if x.startswith('f:'):
        if len(x) != 18:
            raise ValueError
        return ('f', int(x[2:], 16))
    return ('i', int(x))


def kinds(vals, st):
    for k, b in vals:
        if k != 'f':
            continue
        st['floats'] += 1
        if is_nan(b):
            st['nan'] += 1
        elif (b & ~(1 << 63)) == EXP:
            st['inf'] += 1
        elif (b & ~(1 << 63)) == 0:
            st['zero'] += 1
            if b >> 63:
                st['negzero'] += 1
        elif (b & EXP) == 0:
            st['subnormal'] += 1


def main():
    exp_path, pairs = sys.argv[1], sys.argv[2:]
    some, none, emit_err = {}, set(), 0
    st = dict(floats=0, nan=0, inf=0, zero=0, negzero=0, subnormal=0)
    for line in open(exp_path):
        t = line.split()
        if not t:
            continue
        if t[0] == '#':
            emit_err += 1
            continue
        key = (int(t[0]), int(t[1]))
        if t[3] == 'some':
            some[key] = [tok(x) for x in t[4:]]
            kinds(some[key], st)
        else:
            none.add(key)
    progs = {k[0] for k in some} | {k[0] for k in none}
    progs_some = {k[0] for k in some}
    nvals = sum(len(v) for v in some.values())
    print(f"expected: programs={len(progs)} programs_with_comparable_input={len(progs_some)} "
          f"inputs_some={len(some)} inputs_none(skipped)={len(none)} values_compared={nvals} emit_errors={emit_err}")
    print(f"expected floats: float_values={st['floats']} nan={st['nan']} inf={st['inf']} zero={st['zero']} "
          f"(negative_zero={st['negzero']}) subnormal={st['subnormal']}")
    bad = False
    for pair in pairs:
        label, path = pair.split('=', 1)
        seen, mism, errs = {}, [], []
        for line in open(path, errors='replace'):
            t = line.split()
            try:
                key = (int(t[0]), int(t[1]))
                vals = [tok(x) for x in t[2:]]
                if not vals:
                    raise ValueError
            except (ValueError, IndexError):
                errs.append(f"unparsable line: {line.strip()[:80]}")
                continue
            if key in seen:
                errs.append(f"duplicate result for {key}")
            seen[key] = vals
        for key in seen:
            if key in none:
                errs.append(f"C produced a result for {key}, where evalFn is none (must be skipped)")
            elif key not in some:
                errs.append(f"C produced a result for unknown case {key}")
        compared = fcomp = nanpay = fwrong = 0
        for key, r in sorted(some.items()):
            if key not in seen:
                mism.append((key, r, 'missing'))
                continue
            compared += 1
            got = seen[key]
            ok = len(got) == len(r)
            if ok:
                for (ek, ev), (gk, gv) in zip(r, got):
                    if ek != gk:
                        ok = False
                    elif ek == 'i':
                        ok = ok and ev == gv
                    else:
                        fcomp += 1
                        if ev != gv:
                            if is_nan(ev) and is_nan(gv):
                                nanpay += 1          # reported, not a mismatch (see the docstring)
                            else:
                                ok = False
                                fwrong += 1
            if not ok:
                mism.append((key, r, got))
        missing = sum(1 for m in mism if m[2] == 'missing')
        detail = f" (wrong={len(mism) - missing} missing={missing})" if mism else ""
        print(f"  {label:<16} compared={compared} skipped={len(none)} mismatches={len(mism)}{detail} errors={len(errs)}"
              f" | floats_compared_bitwise={fcomp} float_values_wrong={fwrong} nan_payload_differs={nanpay}")
        show = lambda v: ' '.join((f"f:{b:016x}" if k == 'f' else str(b)) for k, b in v)
        for key, r, got in mism[:10]:
            what = 'result' if got == 'missing' or got[:1] != r[:1] else 'final parameter values'
            g = got if got == 'missing' else show(got)[:160]
            print(f"    MISMATCH prog={key[0]} case={key[1]} ({what}) evalFn={show(r)[:160]} C={g}")
        for e in errs[:10]:
            print(f"    ERROR {e}")
        if mism or errs:
            bad = True
    sys.exit(1 if bad else 0)


main()
