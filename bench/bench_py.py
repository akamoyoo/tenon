"""Python side of the benchmark: the binding (py/tenon_kernels.py) against NumPy on 10^7 elements, and
the cost of the entry checks.  Run through bench/run.sh (pinned to one core, BLAS threads = 1).

Method: each timed thing is called four times to warm up, then REPS times; the table gives the minimum
and the median in ms. Small calls are timed in loops of `number` calls, in microseconds per call.
"""
import sys
import time

import numpy as np

import tenon_kernels as k

QUICK = len(sys.argv) > 1
N = 10**6 if QUICK else 10**7
REPS = 5 if QUICK else 21


def bench(f, number=1):
    for _ in range(4):
        f()
    ts = []
    for _ in range(REPS):
        t0 = time.perf_counter()
        for _ in range(number):
            f()
        ts.append((time.perf_counter() - t0) / number)
    ts.sort()
    return ts[0], ts[len(ts) // 2]


def row(label, f, unit="ms", number=1):
    lo, med = bench(f, number)
    s = 1e3 if unit == "ms" else 1e6
    print(f"  {label:<78} min {lo * s:9.3f}  median {med * s:9.3f} {unit}")
    return med


def np_rolling_mean_cumsum(x, w):
    """The usual NumPy rolling mean: difference of cumulative sums (full windows from index w-1 on;
    the first w-1 outputs are expanding means)."""
    c = np.cumsum(x)
    out = np.empty_like(x)
    out[:w] = c[:w] / np.arange(1, w + 1)
    out[w:] = (c[w:] - c[:-w]) / w
    return out


def np_rolling_var_cumsum(x, w):
    c1 = np.cumsum(x); c2 = np.cumsum(x * x)
    n = np.minimum(np.arange(1, len(x) + 1), w).astype(np.float64)
    s1 = c1.copy(); s1[w:] -= c1[:-w]
    s2 = c2.copy(); s2[w:] -= c2[:-w]
    return np.maximum((s2 - s1 * s1 / n) / n, 0.0)


def main():
    print(f"python {sys.version.split()[0]}, numpy {np.__version__}, N = {N}")
    try:
        cfg = np.show_config(mode="dicts")["Build Dependencies"]["blas"]
        print(f"numpy BLAS: {cfg.get('name')} {cfg.get('version')}")
    except Exception:
        pass
    rng = np.random.default_rng(1)
    x = rng.uniform(-1.0, 1.0, size=N)
    y = rng.uniform(-1.0, 1.0, size=N)
    out = np.zeros(N)
    o1 = np.zeros(1)
    xp, yp, op, o1p = x.ctypes.data, y.ctypes.data, out.ctypes.data, o1.ctypes.data
    c_sum8, c_dot, c_ewma, c_rm, c_rv = (k.raw(n) for n in ("tn_sum8", "tn_dot", "tn_ewma", "tn_rolling_mean", "tn_rolling_var"))

    print(f"-- sum of {N} doubles")
    row("np.sum(x)                               (pairwise summation, SIMD)", lambda: np.sum(x))
    row("tenon_kernels.sum8(x)                       (all entry checks)", lambda: k.sum8(x))
    row("kernel call alone (ctypes, no checks)", lambda: c_sum8(xp, N, o1p, 1))
    row("np.add.accumulate(x)[-1]                (left to right, strict order, allocates)", lambda: np.add.accumulate(x)[-1])
    print(f"   values: np.sum {float(np.sum(x))!r}  sum8 {k.sum8(x)!r}")

    print(f"-- dot product of two arrays of {N} doubles")
    row("np.dot(x, y)                            (BLAS ddot, one thread)", lambda: np.dot(x, y))
    row("tenon_kernels.dot(x, y)                     (all entry checks)", lambda: k.dot(x, y))
    row("kernel call alone (ctypes, no checks)", lambda: c_dot(xp, N, yp, N, o1p, 1))
    print(f"   values: np.dot {float(np.dot(x, y))!r}  dot {k.dot(x, y)!r}")

    print(f"-- ewma, {N} doubles, alpha = 0.05  (NumPy has no exponentially weighted mean; no NumPy row)")
    row("tenon_kernels.ewma(x, 0.05)                 (allocates np.empty, all checks)", lambda: k.ewma(x, 0.05))
    row("tenon_kernels.ewma(x, 0.05, out)            (all checks)", lambda: k.ewma(x, 0.05, out))
    row("kernel call alone (ctypes, no checks)", lambda: c_ewma(xp, N, 0.05, op, N))

    for w in (20, 1000):
        print(f"-- rolling mean, {N} doubles, w = {w}")
        row("NumPy: cumsum, then (c[w:] - c[:-w]) / w", lambda: np_rolling_mean_cumsum(x, w))
        if w == 20:
            row("NumPy: sliding_window_view(x, w).mean(axis=1)   (from scratch per window)",
                lambda: np.lib.stride_tricks.sliding_window_view(x, w).mean(axis=1))
        row("tenon_kernels.rolling_mean(x, w)            (allocates np.empty, all checks)", lambda: k.rolling_mean(x, w))
        row("tenon_kernels.rolling_mean(x, w, out)       (all checks)", lambda: k.rolling_mean(x, w, out))
        row("kernel call alone (ctypes, no checks)", lambda: c_rm(xp, N, w, op, N))
    w = 20
    print(f"-- rolling variance, {N} doubles, w = {w}")
    row("NumPy: two cumsums, same naive formula, np.maximum(., 0)", lambda: np_rolling_var_cumsum(x, w))
    row("tenon_kernels.rolling_var(x, w, out)        (all checks)", lambda: k.rolling_var(x, w, out))
    row("tenon_kernels.rolling_std(x, w, out)        (all checks)", lambda: k.rolling_std(x, w, out))
    row("kernel call alone, rolling_var (ctypes, no checks)", lambda: c_rv(xp, N, w, op, N))

    print(f"-- integer prefix sum, {N} int64: what an output that needs no entry scan saves")
    xi = rng.integers(-10**9, 10**9, size=N, endpoint=True, dtype=np.int64)
    oi = np.zeros(N, dtype=np.int64)
    narrow = "tn_prefix_sum_10m" if N > 10**6 else "tn_prefix_sum"
    row("np.cumsum(xi, out=oi)", lambda: np.cumsum(xi, out=oi))
    row("prefix_sum(xi, oi, wide=False)   out declared ±10^16: scans x AND out", lambda: k.prefix_sum(xi, oi, wide=False))
    row("prefix_sum(xi, oi)               out declared int64:  scans x only", lambda: k.prefix_sum(xi, oi))
    row("prefix_sum(xi)                   out declared int64, np.empty: scans x only", lambda: k.prefix_sum(xi))
    row("prefix_sum(xi, wide=False)       out declared ±10^16, np.zeros (no scan of out)", lambda: k.prefix_sum(xi, wide=False))
    row("prefix_sum(xi, oi, check=False)  no scan at all", lambda: k.prefix_sum(xi, oi, check=False))
    row("kernel call alone (ctypes, no checks)", lambda: k.raw("tn_prefix_sum_w")(xi.ctypes.data, N, oi.ctypes.data, N))
    px = k.SIGS[narrow]["params"][0]
    row("the scan itself: E1+E2 on x (min and max)", lambda: k.check_array(xi, px))

    print("-- small calls: fixed cost of the wrapper (microseconds per call)")
    for n in (8, 1024, 10**5):
        xs, ys = x[:n].copy(), y[:n].copy()
        outs = np.zeros(n)
        num = 2000 if n <= 1024 else 200
        xsp, ysp, osp = xs.ctypes.data, ys.ctypes.data, outs.ctypes.data
        row(f"len {n}: np.sum(x)", lambda: np.sum(xs), unit="us", number=num)
        row(f"len {n}: tenon_kernels.sum8(x)", lambda: k.sum8(xs), unit="us", number=num)
        row(f"len {n}: sum8 kernel alone (ctypes)", lambda: c_sum8(xsp, n, o1p, 1), unit="us", number=num)
        row(f"len {n}: np.dot(x, y)", lambda: np.dot(xs, ys), unit="us", number=num)
        row(f"len {n}: tenon_kernels.dot(x, y)", lambda: k.dot(xs, ys), unit="us", number=num)
        row(f"len {n}: dot kernel alone (ctypes)", lambda: c_dot(xsp, n, ysp, n, o1p, 1), unit="us", number=num)
        row(f"len {n}: tenon_kernels.ewma(x, 0.05, out)", lambda: k.ewma(xs, 0.05, outs), unit="us", number=num)
        row(f"len {n}: ewma kernel alone (ctypes)", lambda: c_ewma(xsp, n, 0.05, osp, n), unit="us", number=num)
    print("-- the entry checks of one float call, separately (microseconds)")
    xs = x[:1024].copy(); outs = np.zeros(1024)
    pxf = k.SIGS["tn_ewma"]["params"][0]
    row("E1 on a float64 array (dtype, layout; nothing to scan)", lambda: k.check_array(xs, pxf), unit="us", number=5000)
    row("E4: the generated requirement (a Python lambda)", lambda: k.REQ["tn_ewma"]([0, 0, 0], [1024, 0, 1024]), unit="us", number=5000)
    row("E5: np.may_share_memory(x, out)", lambda: np.may_share_memory(xs, outs), unit="us", number=5000)
    row("E6: tn_fpenv_ok() through ctypes", lambda: k.fpenv_ok(), unit="us", number=5000)


main()
