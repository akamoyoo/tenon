"""Tests of the binding against NumPy.   cd py && python3 test_tenon_kernels.py   (after ./py/build.sh)

Part 1 compares results with NumPy on random inputs (empty arrays and edge cases included).
Part 2 checks that every entry check refuses what it must refuse, and that nothing is copied.
Part 3 (floats): bitwise comparison with the same order of operations written in Python/NumPy,
"close" comparison with NumPy's own sum, dot and windowed statistics (differences are printed), the
entry checks for float arguments, and the generated requirement checks against Tenon's `evalC`.
"""
import json
import math
import os
import sys
import unittest

import numpy as np

import tenon_kernels as k

RNG = np.random.default_rng(20261116)
LENS = [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129, 1000, 1023, 1024, 1025, 4097]
E9 = 10**9


def np_rolling(x, w):
    """Rolling sum by difference of cumulative sums (exact in int64 for these ranges)."""
    c = np.cumsum(x)
    out = c.copy()
    if w < len(x):
        out[w:] = c[w:] - c[:-w]
    return out


def rand_x(n, kind):
    if kind == "full":
        return RNG.integers(-E9, E9, size=n, endpoint=True, dtype=np.int64)
    if kind == "max":
        return np.full(n, E9, dtype=np.int64)
    if kind == "min":
        return np.full(n, -E9, dtype=np.int64)
    if kind == "alt":
        a = np.full(n, E9, dtype=np.int64); a[1::2] = -E9; return a
    return RNG.integers(-5, 5, size=n, endpoint=True, dtype=np.int64)


class AgainstNumPy(unittest.TestCase):
    def test_prefix_sum(self):
        n_cases = 0
        for n in LENS + [10**6, 10**6 + 1]:
            for kind in ("full", "small", "max", "min", "alt"):
                x = rand_x(n, kind)
                out = k.prefix_sum(x)
                self.assertTrue(np.array_equal(out, np.cumsum(x)), (n, kind))
                self.assertTrue(np.array_equal(k.prefix_sum(x, wide=False), out), (n, kind))
                n_cases += 1
        print(f"prefix_sum: {n_cases} inputs equal to np.cumsum (lengths 0..{10**6 + 1})")

    def test_prefix_sum_ten_million(self):
        for kind in ("full", "max"):
            x = rand_x(10**7, kind)
            self.assertTrue(np.array_equal(k.prefix_sum(x), np.cumsum(x)))
        print("prefix_sum: 2 inputs of 10^7 elements equal to np.cumsum (one of them all 10^9: the largest sums)")

    def test_rolling_sum(self):
        n_cases = 0
        for kern in ("wide", "exact", "loose"):
            for n in LENS:
                ws = sorted({1, 2, 3, max(1, n // 2), max(1, n - 1), max(1, n), n + 1, n + 7, 10**6})
                for w in ws:
                    for kind in ("full", "small", "max", "min", "alt"):
                        x = rand_x(n, kind)
                        out = k.rolling_sum(x, w, kernel=kern)
                        self.assertTrue(np.array_equal(out, np_rolling(x, w)), (n, w, kind, kern))
                        n_cases += 1
        print(f"rolling_sum: {n_cases} inputs equal to the cumsum-difference rolling sum (three kernels: out declared int64, ±10^15, ±2.1·10^16)")

    def test_rolling_sum_convolve(self):
        # a second, independent reference for small cases
        n_cases = 0
        for n in [1, 2, 5, 16, 100]:
            for w in [1, 2, 3, 7, n]:
                x = rand_x(n, "small")
                ref = np.convolve(x, np.ones(w, dtype=np.int64))[:n]
                self.assertTrue(np.array_equal(k.rolling_sum(x, w), ref), (n, w))
                n_cases += 1
        print(f"rolling_sum: {n_cases} inputs equal to np.convolve(x, ones(w))[:n]")

    def test_rolling_sum_large(self):
        x = rand_x(10**7, "max")
        for w in (10**6, 1):
            self.assertTrue(np.array_equal(k.rolling_sum(x, w), np_rolling(x, w)))
        x = rand_x(10**7, "full")
        self.assertTrue(np.array_equal(k.rolling_sum(x, 12345), np_rolling(x, 12345)))
        print("rolling_sum: 3 inputs of 10^7 elements (w = 10^6 with all elements 10^9: window sum 10^15, the declared bound)")

    def test_lower_bound(self):
        n_cases = 0
        for f in (k.lower_bound, k.lower_bound_branchy):
            for n in LENS:
                for span in (3, 50, 10**6, 2**62):
                    a = np.sort(RNG.integers(-span, span, size=n, endpoint=True, dtype=np.int64))
                    keys = list(RNG.integers(-span - 2, span + 2, size=12, endpoint=True)) + [k.I64_MIN, k.I64_MAX, 0]
                    keys += [int(v) for v in a[:3]] + [int(v) for v in a[-3:]]
                    for p in keys:
                        self.assertEqual(f(a, int(p)), int(np.searchsorted(a, p, side="left")), (n, span, p))
                        n_cases += 1
            a = np.array([k.I64_MIN, k.I64_MIN, -1, 0, k.I64_MAX, k.I64_MAX], dtype=np.int64)
            for p in (k.I64_MIN, k.I64_MIN + 1, 0, k.I64_MAX - 1, k.I64_MAX):
                self.assertEqual(f(a, p), int(np.searchsorted(a, p, side="left")))
                n_cases += 1
        print(f"lower_bound, lower_bound_branchy: {n_cases} queries equal to np.searchsorted(side='left')")

    def test_lower_bound_million(self):
        a = np.sort(RNG.integers(-10**12, 10**12, size=10**6, dtype=np.int64))
        keys = RNG.integers(-10**12, 10**12, size=2000, dtype=np.int64)
        ref = np.searchsorted(a, keys, side="left")
        for f in (k.lower_bound, k.lower_bound_branchy):
            got = [f(a, int(p)) for p in keys]
            self.assertEqual(got, [int(r) for r in ref])
        print("lower_bound, lower_bound_branchy: 2000 queries each on 10^6 elements equal to np.searchsorted")

    def test_argmax(self):
        n_cases = 0
        for n in LENS[1:]:
            for span in (0, 1, 3, 10**6, 2**62):
                a = RNG.integers(-span, span, size=n, endpoint=True, dtype=np.int64)
                self.assertEqual(k.argmax(a), int(np.argmax(a)), (n, span))
                n_cases += 1
            for a in (np.full(n, k.I64_MIN, dtype=np.int64), np.full(n, k.I64_MAX, dtype=np.int64),
                      np.arange(n, dtype=np.int64), np.arange(n, dtype=np.int64)[::-1].copy()):
                self.assertEqual(k.argmax(a), int(np.argmax(a)))
                n_cases += 1
        with self.assertRaises(ValueError):
            k.argmax(np.zeros(0, dtype=np.int64))            # as np.argmax
        self.assertEqual(k.call("tn_argmax", np.zeros(0, dtype=np.int64)), 0)   # the kernel itself returns 0
        print(f"argmax: {n_cases} inputs equal to np.argmax (ties: first maximum; all INT64_MIN included); empty array refused")

    def test_empty(self):
        e = np.zeros(0, dtype=np.int64)
        self.assertEqual(len(k.prefix_sum(e)), 0)
        self.assertEqual(len(k.rolling_sum(e, 1)), 0)
        self.assertEqual(len(k.rolling_sum(e, 10**6)), 0)
        self.assertEqual(k.lower_bound(e, 5), 0)
        self.assertEqual(k.lower_bound_branchy(e, 5), 0)
        print("empty arrays: prefix_sum, rolling_sum, lower_bound accept length 0")


class EntryChecks(unittest.TestCase):
    def refuse(self, f, *args, **kw):
        with self.assertRaises(k.EntryCheckError):
            f(*args, **kw)

    def test_zero_copy(self):
        x = np.arange(10, dtype=np.int64)
        out = np.zeros(10, dtype=np.int64)
        addr = out.ctypes.data
        r = k.prefix_sum(x, out)
        self.assertIs(r, out)                                  # the caller's buffer was written in place
        self.assertEqual(out.ctypes.data, addr)
        self.assertTrue(np.array_equal(out, np.cumsum(x)))
        self.assertTrue(np.array_equal(x, np.arange(10)))      # the by-value argument is untouched
        v = np.zeros(30, dtype=np.int64)[10:20]                # a contiguous view into a larger buffer
        k.rolling_sum(x, 3, v)
        self.assertTrue(np.array_equal(v, np_rolling(x, 3)))
        print("zero copy: results are written into the caller's buffer (also through a contiguous view)")

    def test_dtype_and_layout(self):
        x = np.arange(10, dtype=np.int64)
        for bad in (np.arange(10, dtype=np.int32), np.arange(10, dtype=np.uint64), np.arange(10, dtype=np.float64),
                    np.arange(10, dtype=">i8"), [1, 2, 3], x.reshape(2, 5), np.arange(20, dtype=np.int64)[::2],
                    np.int64(3), None):
            self.refuse(k.prefix_sum, bad)
            self.refuse(k.rolling_sum, bad, 2)
            self.refuse(k.lower_bound, bad, 1)
            self.refuse(k.argmax, bad)
        ro = np.zeros(10, dtype=np.int64); ro.flags.writeable = False
        self.refuse(k.prefix_sum, x, ro)                       # inout buffer must be writeable
        self.assertEqual(k.lower_bound(ro, 1), 10)             # a read-only buffer is fine for a by-value slice
        # misaligned int64 data
        raw = np.zeros(8 * 10 + 1, dtype=np.uint8)
        mis = raw[1:].view(np.int64)
        self.assertFalse(mis.flags.aligned)
        self.refuse(k.argmax, mis)
        print("refused: int32, uint64, float64, big-endian int64, list, 2-D, strided view, scalar, None, read-only out, misaligned")

    def test_ranges(self):
        x = np.zeros(10, dtype=np.int64)
        for v in (E9 + 1, -E9 - 1, k.I64_MAX, k.I64_MIN):
            y = x.copy(); y[7] = v
            self.refuse(k.prefix_sum, y)
            self.refuse(k.rolling_sum, y, 3)
        y = x.copy(); y[0] = E9; y[9] = -E9                    # the ends of the range are accepted
        k.prefix_sum(y); k.rolling_sum(y, 3)
        for w in (0, -1, 10**6 + 1, 2**70):
            self.refuse(k.rolling_sum, x, w)
        for w in (2.0, "3", None, True):
            self.refuse(k.rolling_sum, x, w)
        k.rolling_sum(x, np.int64(4)); k.rolling_sum(x, 10**6)
        self.refuse(k.lower_bound, x, 2**63)                   # p outside int64
        self.refuse(k.lower_bound, x, 1.5)
        # kernels whose output is declared ±10^15: the initial contents of a caller-supplied inout
        # buffer must be inside that range too (the parameter type is about the value passed in)
        out = np.zeros(10, dtype=np.int64); out[3] = 10**15 + 1
        self.refuse(k.prefix_sum, x, out, wide=False)
        self.refuse(k.rolling_sum, x, 3, out, kernel="exact")
        out[3] = 10**15
        k.prefix_sum(x, out, wide=False)
        print("refused: elements outside ±10^9, w outside 1..=10^6, non-integer w, p outside int64, out contents outside a declared ±10^15")

    def test_full_range_output_needs_no_scan(self):
        # kernels whose output is declared with the whole int64 range: any garbage in `out` is a legal
        # argument, it is not scanned (E2 is skipped) and it is overwritten
        x = RNG.integers(-E9, E9, size=1000, dtype=np.int64)
        for junk in (k.I64_MAX, k.I64_MIN, 10**15 + 1):
            out = np.full(1000, junk, dtype=np.int64)
            self.assertTrue(np.array_equal(k.prefix_sum(x, out), np.cumsum(x)))
            out = np.full(1000, junk, dtype=np.int64)
            self.assertTrue(np.array_equal(k.rolling_sum(x, 7, out), np_rolling(x, 7)))
        self.assertFalse(k.needs_scan(k.SIGS["tn_prefix_sum_w"]["params"][1]))
        self.assertTrue(k.needs_scan(k.SIGS["tn_prefix_sum_w"]["params"][0]))      # the input still has a range
        self.assertTrue(k.needs_scan(k.SIGS["tn_prefix_sum"]["params"][1]))
        for name in ("tn_ewma", "tn_sum8", "tn_dot", "tn_rolling_mean", "tn_rolling_var", "tn_rolling_std"):
            self.assertFalse(any(k.needs_scan(p) for p in k.SIGS[name]["params"]), name)
        print("no scan: outputs declared with the full int64 range accept and overwrite arbitrary contents; "
              "no float parameter is ever scanned")

    def test_preconditions(self):
        x = np.zeros(10, dtype=np.int64)
        self.refuse(k.prefix_sum, x, np.zeros(9, dtype=np.int64))
        self.refuse(k.prefix_sum, x, np.zeros(11, dtype=np.int64))
        self.refuse(k.rolling_sum, x, 3, np.zeros(9, dtype=np.int64))
        big = np.zeros(10**7 + 1, dtype=np.int64)
        self.refuse(k.prefix_sum, big)
        self.refuse(k.rolling_sum, big, 3)
        self.refuse(k.call, "tn_prefix_sum", big[:10**6 + 1], np.zeros(10**6 + 1, dtype=np.int64))
        k.call("tn_prefix_sum", big[:10**6], np.zeros(10**6, dtype=np.int64))
        print("refused (generated from req): len(out) != len(x), more than 10^7 elements (10^6 for `prefixSum`)")

    def test_aliasing(self):
        x = np.arange(10, dtype=np.int64)
        self.refuse(k.prefix_sum, x, x)                        # out is x
        buf = np.zeros(20, dtype=np.int64)
        self.refuse(k.prefix_sum, buf[:10], buf[5:15])         # overlapping views
        self.refuse(k.rolling_sum, buf[:10], 2, buf[5:15])
        k.prefix_sum(buf[:10], buf[10:])                       # disjoint halves of one buffer are fine
        print("refused: out sharing memory with x (same array, overlapping views)")



# ---------------------------------------------------------------------------------------------
# Part 3: floats

def bits(a):
    return np.ascontiguousarray(a, dtype=np.float64).view(np.uint64)


def same_bits(a, b):
    """Bitwise equal, except that any NaN equals any NaN (Tenon cannot tell NaNs apart; README)."""
    a = np.asarray(a, dtype=np.float64); b = np.asarray(b, dtype=np.float64)
    if a.shape != b.shape:
        return False
    na, nb = np.isnan(a), np.isnan(b)
    return bool(np.array_equal(na, nb) and np.array_equal(bits(a)[~na], bits(b)[~nb]))


SPECIAL = np.array([0.0, -0.0, 1.0, -1.0, np.inf, -np.inf, np.nan, 5e-324, -5e-324, 2.2250738585072014e-308,
                    1.7976931348623157e308, -1.7976931348623157e308, 0.1, 1e16, -1e16, 1.0 + 2**-52, 2.0**53, 1e-300])


def rand_f(n, kind):
    if kind == "normal":
        return RNG.standard_normal(n)
    if kind == "wide":                                   # magnitudes over 600 binary orders
        return RNG.standard_normal(n) * np.exp2(RNG.integers(-300, 300, size=n).astype(np.float64))
    if kind == "offset":                                 # large mean, small spread: hard for sums of squares
        return 1e8 + RNG.standard_normal(n)
    if kind == "special":
        return RNG.choice(SPECIAL, size=n)
    if kind == "mixed":
        a = RNG.standard_normal(n); m = RNG.random(n) < 0.05; a[m] = RNG.choice(SPECIAL, size=int(m.sum())); return a
    return RNG.integers(-5, 5, size=n, endpoint=True).astype(np.float64)


def py_ewma(x, alpha):
    """The kernel's order of operations in plain Python floats (IEEE double, one rounding per operation)."""
    out = np.empty(len(x)); prev = 0.0
    for i, v in enumerate(x.tolist()):
        prev = alpha * v + (1.0 - alpha) * prev
        out[i] = prev
    return out


def lanes(x, y=None):
    """sum8 / dot in the kernel's lane order, with NumPy doing the eight lanes of each step at once."""
    n8 = len(x) // 8
    acc = np.zeros(8)
    xr = x[:8 * n8].reshape(n8, 8)
    yr = None if y is None else y[:8 * n8].reshape(n8, 8)
    for i in range(n8):
        acc = acc + (xr[i] if y is None else xr[i] * yr[i])        # elementwise: one rounding per operation
    a = [float(v) for v in acc]
    for j in range(8 * n8, len(x)):
        a[0] = a[0] + (float(x[j]) if y is None else float(x[j]) * float(y[j]))
    return ((a[0] + a[1]) + (a[2] + a[3])) + ((a[4] + a[5]) + (a[6] + a[7]))


def np_rolling_mean(x, w):
    """Straightforward: the mean of each window, computed from scratch."""
    n = len(x); out = np.empty(n)
    m = min(w, n)
    for i in range(min(m, n)):
        out[i] = x[:i + 1].mean()
    if n > m:
        out[m - 1:] = np.lib.stride_tricks.sliding_window_view(x, m).mean(axis=1)
    return out


def np_rolling_var(x, w):
    n = len(x); out = np.empty(n)
    m = min(w, n)
    for i in range(min(m, n)):
        out[i] = x[:i + 1].var()
    if n > m:
        out[m - 1:] = np.lib.stride_tricks.sliding_window_view(x, m).var(axis=1)
    return out


def relmax(a, b, floor=0.0):
    d = np.abs(a - b) / np.maximum(np.abs(b), floor if floor else np.finfo(float).tiny)
    return float(np.max(d)) if len(d) else 0.0


class FloatKernels(unittest.TestCase):
    def test_ewma_bitwise(self):
        n_cases = n_vals = 0
        for n in LENS[:22] + [5000]:
            for kind in ("normal", "wide", "special", "mixed", "small"):
                for alpha in (0.5, 0.1, 1.0, 0.0, 0.9999999, 1e-300, -0.3, 1.5, float("nan"), float("inf")):
                    x = rand_f(n, kind)
                    with np.errstate(all="ignore"):
                        ref = py_ewma(x, alpha)
                    got = k.ewma(x, alpha)
                    self.assertTrue(same_bits(got, ref), (n, kind, alpha))
                    n_cases += 1; n_vals += n
        x = rand_f(10**6, "normal")
        self.assertTrue(same_bits(k.ewma(x, 0.05), py_ewma(x, 0.05)))
        print(f"ewma: {n_cases + 1} inputs ({n_vals + 10**6} values, NaN, ±inf, ±0, subnormals included) "
              f"bitwise equal to the plain Python loop")

    def test_sum8_bitwise_and_numpy(self):
        n_cases = 0
        for n in LENS + [10**5 + 3]:
            for kind in ("normal", "wide", "special", "mixed", "small", "offset"):
                x = rand_f(n, kind)
                with np.errstate(all="ignore"):
                    ref = lanes(x)
                self.assertTrue(same_bits(k.sum8(x), ref), (n, kind))
                n_cases += 1
        print(f"sum8: {n_cases} inputs bitwise equal to the same lane order written in NumPy")
        # against np.sum (pairwise summation, another order) and against the exactly rounded sum
        for kind in ("normal", "wide", "offset"):
            x = rand_f(10**6, kind)
            exact = math.fsum(x)
            s8, snp, naive = k.sum8(x), float(np.sum(x)), float(np.add.accumulate(x)[-1])
            scale = abs(exact) if exact else 1.0
            self.assertLess(abs(s8 - snp), 1e-9 * max(float(np.sum(np.abs(x))), 1e-300))
            print(f"sum8 vs np.sum, 10^6 {kind:<6}: sum8 == np.sum bitwise: {bits(np.array([s8]))[0] == bits(np.array([snp]))[0]}; "
                  f"relative error against math.fsum: sum8 {abs(s8 - exact) / scale:.2e}, np.sum {abs(snp - exact) / scale:.2e}, "
                  f"left-to-right {abs(naive - exact) / scale:.2e}")

    def test_dot_bitwise_and_numpy(self):
        n_cases = 0
        for n in LENS + [10**5 + 3]:
            for kind in ("normal", "wide", "special", "mixed", "small"):
                x, y = rand_f(n, kind), rand_f(n, "normal" if kind == "wide" else kind)
                with np.errstate(all="ignore"):
                    ref = lanes(x, y)
                self.assertTrue(same_bits(k.dot(x, y), ref), (n, kind))
                n_cases += 1
        print(f"dot: {n_cases} inputs bitwise equal to the same lane order written in NumPy (products rounded, then added)")
        for kind in ("normal", "offset"):
            x, y = rand_f(10**6, kind), rand_f(10**6, kind)
            d8, dnp = k.dot(x, y), float(np.dot(x, y))
            ref = math.fsum(x * y)                      # exact sum of the ROUNDED products
            scale = abs(ref) if ref else 1.0
            self.assertLess(abs(d8 - dnp), 1e-9 * float(np.sum(np.abs(x * y))))
            print(f"dot vs np.dot, 10^6 {kind:<6}: bitwise equal: {bits(np.array([d8]))[0] == bits(np.array([dnp]))[0]}; "
                  f"relative difference dot - np.dot: {abs(d8 - dnp) / scale:.2e}; against fsum of rounded products: "
                  f"dot {abs(d8 - ref) / scale:.2e}, np.dot {abs(dnp - ref) / scale:.2e}")

    def test_rolling_mean(self):
        worst = {}
        n_cases = 0
        for kind in ("normal", "small", "offset", "wide"):
            for n in (1, 2, 7, 64, 1000, 20000):
                for w in sorted({1, 2, 5, 20, max(1, n // 3), n, n + 5}):
                    x = rand_f(n, kind)
                    got = k.rolling_mean(x, w)
                    ref = np_rolling_mean(x, w)
                    if kind == "wide":
                        # the incremental sum loses small windows that follow huge values: compare on the
                        # scale of the largest element seen so far
                        err = float(np.max(np.abs(got - ref) / np.maximum.accumulate(np.abs(x))))
                    else:
                        err = relmax(got, ref, floor=1e-3 if kind != "offset" else 0.0)
                    worst[kind] = max(worst.get(kind, 0.0), err)
                    n_cases += 1
        self.assertLess(worst["normal"], 1e-9); self.assertLess(worst["offset"], 1e-12)
        self.assertEqual(worst["small"], 0.0)            # small integers: every operation is exact
        self.assertLess(worst["wide"], 1e-9)
        x = rand_f(10**6, "normal")
        e6 = relmax(k.rolling_mean(x, 1000), np_rolling_mean(x, 1000), floor=1e-3)
        print(f"rolling_mean: {n_cases} inputs against the mean of each window computed from scratch; max relative "
              f"difference: N(0,1) {worst['normal']:.2e} (|mean| floored at 1e-3), 1e8+N(0,1) {worst['offset']:.2e}, "
              f"small integers {worst['small']:.1e} (exact), 600 binary orders of magnitude {worst['wide']:.2e} "
              f"(relative to the largest |x| so far); 10^6 elements, w=1000: {e6:.2e}")
        # first elements exactly: out[0] = x[0]
        self.assertEqual(float(k.rolling_mean(np.array([3.5, 1.0]), 4)[0]), 3.5)
        # documented poisoning: after an infinity every output is NaN
        y = np.ones(10); y[2] = np.inf
        with np.errstate(all="ignore"):
            r = k.rolling_mean(y, 3)
        self.assertTrue(np.all(np.isnan(r[5:])) and np.isinf(r[2]))
        print("rolling_mean: an infinity in x makes every output after its window NaN (inf - inf), as documented")

    def test_rolling_var(self):
        n_cases = 0
        worst = {}
        clamp = {}
        for kind in ("normal", "small", "offset"):
            for n in (1, 2, 7, 64, 1000, 20000):
                for w in sorted({1, 2, 5, 20, max(1, n // 3), n, n + 5}):
                    x = rand_f(n, kind)
                    got = k.rolling_var(x, w)
                    ref = np_rolling_var(x, w)
                    self.assertTrue(np.all(got >= 0.0))                      # the clamp
                    self.assertTrue(same_bits(k.rolling_std(x, w), np.sqrt(got)), (kind, n, w))
                    # absolute difference relative to the scale of the squares, and relative to the variance
                    scale = max(float(np.max(x * x)), 1.0) if n else 1.0
                    worst[kind] = max(worst.get(kind, 0.0), float(np.max(np.abs(got - ref))) / scale)
                    big = ref > 1e-3
                    if big.any():
                        worst[kind + "_rel"] = max(worst.get(kind + "_rel", 0.0), float(np.max(np.abs(got - ref)[big] / ref[big])))
                    clamp[kind] = clamp.get(kind, 0) + int(np.sum((got == 0.0) & (ref > 0.0)))
                    n_cases += 2
        self.assertLess(worst["normal_rel"], 1e-8)
        self.assertLess(worst["offset"], 1e-11)          # small against x^2 = 1e16, enormous against the variance (about 1)
        print(f"rolling_var / rolling_std: {n_cases} inputs against np.var of each window; rolling_std == sqrt(rolling_var) bitwise. "
              f"Max relative difference where the variance exceeds 1e-3: N(0,1) {worst['normal_rel']:.2e}, small integers "
              f"{worst.get('small_rel', 0.0):.2e}, 1e8+N(0,1) {worst['offset_rel']:.2e} (the naive formula: absolute error "
              f"{worst['offset']:.1e} of x^2); results clamped to 0 where the true variance is positive: "
              f"N(0,1) {clamp['normal']}, small integers {clamp['small']}, 1e8+N(0,1) {clamp['offset']}")
        # a NaN is not hidden by the clamp
        y = np.ones(6); y[1] = np.nan
        self.assertTrue(np.isnan(k.rolling_var(y, 2)[1]) and np.isnan(k.rolling_std(y, 2)[1]))
        # a constant window: the naive formula may give a tiny negative number; it must come out as 0.0, never negative
        c = np.full(1000, 0.1)
        v = k.rolling_var(c, 10)
        self.assertTrue(np.all(v >= 0.0) and float(v.max()) < 1e-15)
        print(f"rolling_var: NaN propagates through the clamp; a constant window of 0.1 gives values in [0, {float(v.max()):.1e}], never negative")

    def test_float_empty_and_one(self):
        e = np.zeros(0)
        self.assertEqual(len(k.ewma(e, 0.5)), 0)
        self.assertEqual(k.sum8(e), 0.0)
        self.assertEqual(k.dot(e, e), 0.0)
        self.assertEqual(len(k.rolling_mean(e, 3)), 0)
        self.assertEqual(len(k.rolling_var(e, 3)), 0)
        self.assertEqual(len(k.rolling_std(e, 3)), 0)
        self.assertEqual(k.sum8(np.array([-0.0])), 0.0)
        print("float kernels accept length 0 (sum8 and dot return 0.0)")


class FloatEntryChecks(unittest.TestCase):
    def refuse(self, f, *args, **kw):
        with self.assertRaises(k.EntryCheckError):
            f(*args, **kw)

    def test_zero_copy_and_no_fill(self):
        x = RNG.standard_normal(100)
        out = np.full(100, np.nan)                       # arbitrary contents are fine for a float output
        addr = out.ctypes.data
        r = k.ewma(x, 0.25, out)
        self.assertIs(r, out); self.assertEqual(out.ctypes.data, addr)
        self.assertTrue(same_bits(out, py_ewma(x, 0.25)))
        xc = x.copy(); k.rolling_mean(x, 5, out); k.rolling_var(x, 5, out); k.rolling_std(x, 5, out)
        self.assertTrue(np.array_equal(bits(x), bits(xc)))            # by-value input untouched
        v = np.zeros(300)[100:200]
        k.ewma(x, 0.25, v)
        self.assertTrue(same_bits(v, py_ewma(x, 0.25)))
        print("float zero copy: results are written into the caller's buffer; an output full of NaN is accepted and overwritten")

    def test_dtype_and_layout(self):
        x = RNG.standard_normal(16)
        for bad in (x.astype(np.float32), np.arange(16), x.astype(">f8"), list(x), x.reshape(4, 4), RNG.standard_normal(32)[::2],
                    np.float64(1.0), None, x.astype(np.longdouble), x.astype(np.complex128)):
            self.refuse(k.ewma, bad, 0.5)
            self.refuse(k.sum8, bad)
            self.refuse(k.dot, bad, bad)
            self.refuse(k.rolling_mean, bad, 3)
            self.refuse(k.rolling_var, bad, 3)
        self.refuse(k.dot, x, np.arange(16))                          # int64 where float64 is expected
        self.refuse(k.prefix_sum, x)                                  # float64 where int64 is expected
        ro = np.zeros(16); ro.flags.writeable = False
        self.refuse(k.ewma, x, 0.5, ro)
        self.assertEqual(k.sum8(ro), 0.0)
        mis = np.zeros(8 * 16 + 1, dtype=np.uint8)[1:].view(np.float64)
        self.refuse(k.sum8, mis)
        print("refused: float32, int64, big-endian float64, list, 2-D, strided view, scalar, None, longdouble, complex, read-only out, misaligned")

    def test_requirements_and_scalars(self):
        x = RNG.standard_normal(16)
        self.refuse(k.ewma, x, 0.5, np.zeros(15)); self.refuse(k.ewma, x, 0.5, np.zeros(17))
        self.refuse(k.dot, x, np.zeros(15))
        self.refuse(k.rolling_mean, x, 3, np.zeros(15))
        self.refuse(k.rolling_var, x, 3, np.zeros(17))
        self.refuse(k.call, "tn_sum8", x, np.zeros(0))                # requires 1 <= len(out)
        self.refuse(k.call, "tn_dot", x, x.copy(), np.zeros(0))
        k.call("tn_sum8", x, np.zeros(5))                             # a longer out is allowed by `1 <= len(out)`
        for w in (0, -1, 10**6 + 1, 2.0, None, True):
            self.refuse(k.rolling_mean, x, w); self.refuse(k.rolling_var, x, w); self.refuse(k.rolling_std, x, w)
        k.rolling_mean(x, 10**6); k.rolling_mean(x, np.int64(1))
        for a in ("0.5", None, 1 + 2j, True, 2**53 + 1):
            self.refuse(k.ewma, x, a)
        k.ewma(x, 1); k.ewma(x, np.float32(0.5)); k.ewma(x, np.float64(0.5))
        self.assertTrue(np.all(np.isnan(k.ewma(x, float("nan")))))    # NaN is a legal f64: accepted, NaN out
        print("refused (generated from req): unequal lengths, empty out for sum8/dot; refused: w outside 1..=10^6, "
              "non-integer w, non-float alpha; accepted: alpha = NaN (every double is an f64)")

    def test_aliasing(self):
        x = RNG.standard_normal(16)
        self.refuse(k.ewma, x, 0.5, x)
        buf = np.zeros(32)
        self.refuse(k.ewma, buf[:16], 0.5, buf[8:24])
        self.refuse(k.rolling_mean, buf[:16], 3, buf[8:24])
        k.ewma(buf[:16], 0.5, buf[16:])
        self.assertEqual(k.dot(x, x), lanes(x, x))                    # two by-value arguments may be the same array
        print("refused: float out sharing memory with x; accepted: dot(x, x) (both by value)")

    def test_fpenv(self):
        x = np.array([5e-324, 2.5e-308, 1.0])
        self.assertTrue(k.fpenv_ok())
        k._LIB.tn_fpenv_set_for_test(1)                              # FTZ + DAZ on, as a fast-math library would
        try:
            self.assertFalse(k.fpenv_ok())
            self.refuse(k.sum8, x)
            self.refuse(k.ewma, x, 0.5)
            self.assertEqual(k.lower_bound(np.arange(4), 2), 2)       # integer kernels do not care
        finally:
            k._LIB.tn_fpenv_set_for_test(0)
        self.assertTrue(k.fpenv_ok())
        self.assertEqual(k.sum8(np.array([5e-324, 5e-324])), 1e-323)  # subnormal arithmetic intact
        print("refused: float kernels while flush-to-zero / denormals-are-zero is set (E6); accepted again after reset")

    def test_generated_requirements_against_evalC(self):
        with open(os.path.join(k._BUILD, "tenon_req_tests.json")) as f:
            tests = json.load(f)
        n = t = fl = 0
        for name, cases in tests.items():
            for c in cases:
                self.assertEqual(bool(k.REQ[name](c["v"], c["n"])), c["expect"], (name, c))
                n += 1; t += c["expect"]; fl += not c["expect"]
        self.assertEqual(set(tests), set(k.SIGS))
        self.assertTrue(all(not s["req_ill_shaped"] for s in k.SIGS.values()))
        print(f"requirements: the generated Python checks of {len(tests)} kernels agree with Tenon's evalC on {n} argument shapes "
              f"({t} true, {fl} false)")
        for name, s in k.SIGS.items():
            print(f"    {name}: {s['req_text']}")


if __name__ == "__main__":
    print(f"python {sys.version.split()[0]}, numpy {np.__version__}")
    unittest.main(verbosity=1)
