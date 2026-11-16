"""NumPy binding for the C generated from the proved Tenon kernels (Examples.lean, Ewma.lean, Sum8.lean).

Integer kernels (int64 arrays):
    prefix_sum(x, out=None)          running sum                      (np.cumsum)
    rolling_sum(x, w, out=None)      sum of the last min(i+1, w) elements, maintained incrementally
    lower_bound(a, p)                first i with a[i] >= p           (np.searchsorted(a, p, 'left'))
    lower_bound_branchy(a, p)        the same, classical lo/hi search
    argmax(a)                        index of the first maximum       (np.argmax)
Float kernels (float64 arrays); every one computes in ONE FIXED ORDER, so the result is the same bits
on every machine and build that respects the compiler flags:
    ewma(x, alpha, out=None)         prev = alpha * x[i] + (1.0 - alpha) * prev, starting from 0.0
    sum8(x)                          eight lanes (index mod 8), tail into lane 0, ((a0+a1)+(a2+a3))+((a4+a5)+(a6+a7))
    dot(x, y)                        the same lanes over x[i] * y[i] (products rounded, no fused multiply-add)
    rolling_mean(x, w, out=None)     running sum updated by + x[i] - x[i-w], divided by the window length
    rolling_var(x, w, out=None)      (s2 - s1*s1/n)/n from running sums of x and x*x, negative results set to 0
    rolling_std(x, w, out=None)      sqrt of the same (the clamp written as an `if`)

Arrays are passed to C WITHOUT COPYING: the C function receives the address of the NumPy buffer and
its length. Nothing in this file is proved, and the generated C contains no checks at all. The kernel
theorem (`prog_sound`) speaks about calls whose arguments have the parameter types and satisfy the
function's requirement `req`, so every public function establishes exactly that before calling C.
These ENTRY CHECKS are the only thing between a caller and undefined behaviour:

  E1  an array argument is a numpy.ndarray of the parameter's dtype (int64 or float64), native byte
      order, one-dimensional, C-contiguous, aligned; an inout argument is also writeable
  E2  for an integer array: every element is inside the element range of the parameter type. SKIPPED
      when that range is all of int64, and there is nothing to check for a float64 array (every double
      has type f64). An output declared `inout slice(int64 range)` or `inout fslice` therefore needs no
      scan and no zero-fill: any buffer contents are a legal argument.
  E3  integer arguments are integers inside the parameter's range; a float argument is a Python or
      NumPy float (or an integer that converts exactly)
  E4  the function's requirement `req` (equal lengths, maximal length, ...). `req` is a decidable
      condition in the Tenon term; `pygen` translates it to the Python expression `req_py` in
      tenon_kernels.json, and that expression is what is evaluated here. Nothing is retyped by hand.
  E5  an inout array shares no memory with any other array argument. Tenon passes arguments by value and
      copies inout results back; the C works in place through `restrict` pointers, which is the same
      thing only if the buffers are distinct.
  E6  (float kernels) the thread's floating-point environment is round-to-nearest with flush-to-zero
      and denormals-are-zero off (`tn_fpenv_ok`, hand-written C). Otherwise subnormal results differ
      from Tenon's.

At import the library is probed once for contraction (`tn_probe_muladd`): a library compiled so that
a*b+c becomes a fused multiply-add is refused. This is a spot check, not a guarantee; the guarantee is
the compiler flags in py/build.sh.

`check=False` skips E2 only (the O(n) part); the rest is always checked.
"""
import ctypes
import json
import os

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
_BUILD = os.environ.get("TENON_BUILD", os.path.join(_HERE, "build"))
_LIB = ctypes.CDLL(os.environ.get("TENON_LIB", os.path.join(_BUILD, "libtenon_kernels.so")))
with open(os.path.join(_BUILD, "tenon_kernels.json")) as _f:
    SIGS = json.load(_f)

I64_MIN, I64_MAX = -2**63, 2**63 - 1
_INT64 = np.dtype(np.int64)
_FLOAT64 = np.dtype(np.float64)


class EntryCheckError(ValueError):
    """An argument is outside what the kernel function was proved for. The C code was not called."""


def _ctypes_sig(sig):
    argtypes = []
    for p in sig["params"]:
        k = p["kind"]
        if k == "int":
            argtypes.append(ctypes.POINTER(ctypes.c_int64) if p["inout"] else ctypes.c_int64)
        elif k == "float":
            argtypes.append(ctypes.POINTER(ctypes.c_double) if p["inout"] else ctypes.c_double)
        elif k == "array":
            argtypes.append(ctypes.c_void_p)
        else:                                   # slice, fslice: pointer and length
            argtypes += [ctypes.c_void_p, ctypes.c_int64]
    return argtypes


_FN = {}
REQ = {}
for _name, _sig in SIGS.items():
    _f = getattr(_LIB, _name)
    _f.argtypes = _ctypes_sig(_sig)
    _f.restype = ctypes.c_int64
    _FN[_name] = _f
    # E4: the requirement, generated from `Fn.req`. v[i]: value of integer argument i; n[i]: length of
    # array argument i. Python integers are unbounded, as Tenon's `evalCT` is.
    REQ[_name] = eval(compile("lambda v, n: " + _sig["req_py"], f"<req of {_name}>", "eval"), {"__builtins__": {}})
    _sig["has_float"] = any(p["kind"] in ("float", "fslice") for p in _sig["params"])

_LIB.tn_fpenv_ok.restype = ctypes.c_int
_LIB.tn_fpenv_ok.argtypes = []
_LIB.tn_fpenv_set_for_test.restype = None
_LIB.tn_fpenv_set_for_test.argtypes = [ctypes.c_int]
_LIB.tn_probe_muladd.restype = ctypes.c_double
_LIB.tn_probe_muladd.argtypes = [ctypes.c_double] * 3

# 0.1 * 3.0 - 0.3: rounded product then sum gives 2^-54 (0x3c90000000000000); a fused multiply-add
# gives 0x3c8999999999999a.
if _LIB.tn_probe_muladd(0.1, 3.0, -0.3) != 0.1 * 3.0 + -0.3 or (0.1 * 3.0 + -0.3).hex() != "0x1.0000000000000p-54":
    raise ImportError("libtenon_kernels.so contracts a*b+c into a fused multiply-add: it was not built with "
                      "-ffp-contract=off (see py/build.sh); the float kernels would not compute what Tenon defines")


def fpenv_ok():
    """E6."""
    return bool(_LIB.tn_fpenv_ok())


def needs_scan(p):
    """Does an argument for parameter `p` need the O(n) range scan (E2)?"""
    return p["kind"] in ("array", "slice") and (p["lo"] > I64_MIN or p["hi"] < I64_MAX)


def check_array(a, p, values=True):
    """E1 and (if `values` and the type has a range) E2 for one array argument."""
    name = p["name"]
    want = _FLOAT64 if p["kind"] == "fslice" else _INT64
    if not isinstance(a, np.ndarray):
        raise EntryCheckError(f"{name}: expected a numpy.ndarray, got {type(a).__name__}")
    if a.dtype != want or not a.dtype.isnative:
        raise EntryCheckError(f"{name}: dtype must be native {want}, got {a.dtype}")
    if a.ndim != 1:
        raise EntryCheckError(f"{name}: must be one-dimensional, got shape {a.shape}")
    fl = a.flags
    if not (fl.c_contiguous and fl.aligned):
        raise EntryCheckError(f"{name}: must be C-contiguous and aligned (pass np.ascontiguousarray(...))")
    if p["inout"] and not fl.writeable:
        raise EntryCheckError(f"{name}: is written by the kernel and must be writeable")
    if p["kind"] == "array" and a.shape[0] != p["len"]:
        raise EntryCheckError(f"{name}: length must be {p['len']}, got {a.shape[0]}")
    if values and a.shape[0] and needs_scan(p):
        lo, hi = int(a.min()), int(a.max())
        if lo < p["lo"] or hi > p["hi"]:
            raise EntryCheckError(f"{name}: elements must be in {p['lo']}..={p['hi']}, found {lo}..={hi}")


def check_int(v, p):
    """E3 for an integer."""
    if isinstance(v, bool) or not isinstance(v, (int, np.integer)):
        raise EntryCheckError(f"{p['name']}: expected an integer, got {type(v).__name__}")
    v = int(v)
    if not (p["lo"] <= v <= p["hi"]):
        raise EntryCheckError(f"{p['name']}: must be in {p['lo']}..={p['hi']}, got {v}")
    return v


def check_float(v, p):
    """E3 for a float: every double is a legal f64 (NaN and infinities included: the type has no range)."""
    if isinstance(v, (float, np.floating)):
        return float(v)
    if isinstance(v, (int, np.integer)) and not isinstance(v, bool):
        f = float(v)
        if f == v:
            return f
        raise EntryCheckError(f"{p['name']}: the integer {v} is not exactly a double")
    raise EntryCheckError(f"{p['name']}: expected a float, got {type(v).__name__}")


def call(name, *args, check=True):
    """Entry checks E1 to E6, then the C function. Returns the function's integer result."""
    sig = SIGS[name]
    params = sig["params"]
    if len(args) != len(params):
        raise TypeError(f"{name}: {len(params)} arguments expected")
    cargs, arrays, v, n = [], [], [], []
    for a, p in zip(args, params):
        k = p["kind"]
        if k == "int" or k == "float":
            if p["inout"]:
                raise NotImplementedError("inout scalars are not used by the wrapped kernels")
            x = check_int(a, p) if k == "int" else check_float(a, p)
            cargs.append(x)
            v.append(x if k == "int" else 0)
            n.append(0)
        else:
            check_array(a, p, values=check)                                        # E1, E2
            arrays.append((a, p))
            cargs.append(a.ctypes.data)
            if k != "array":
                cargs.append(a.shape[0])
            v.append(0)
            n.append(a.shape[0])
    if not REQ[name](v, n):                                                        # E4
        raise EntryCheckError(f"{name}: the requirement `{sig['req_text']}` does not hold "
                              f"(lengths {[a.shape[0] for a, _ in arrays]})")
    for i, (a, p) in enumerate(arrays):                                            # E5
        if p["inout"]:
            for j, (b, _) in enumerate(arrays):
                if i != j and np.may_share_memory(a, b):
                    raise EntryCheckError(f"{p['name']}: an inout array must not share memory with another argument")
    if sig["has_float"] and not _LIB.tn_fpenv_ok():                                # E6
        raise EntryCheckError("the floating-point environment is not round-to-nearest with FTZ/DAZ off")
    return _FN[name](*cargs)


def raw(name):
    """The bare C function (ctypes), without any check. For benchmarks only."""
    return _FN[name]


# ---- public functions -------------------------------------------------------------------------

def _len(x):
    return x.shape[0] if isinstance(x, np.ndarray) and x.ndim == 1 else 0


def prefix_sum(x, out=None, check=True, wide=True):
    """Running sum of x (int64 elements within ±10^9, at most 10^7 of them). Returns `out`.
    `wide=True` (default) uses `prefixSumW`, whose output parameter is declared with the full int64
    range: `out` is neither scanned nor zero-filled (a fresh one is np.empty). `wide=False` uses the
    kernels of emit4 (out declared ±10^15 / ±10^16), which need the scan or zeros."""
    n = _len(x)
    if wide:
        if out is None:
            out = np.empty(n, dtype=np.int64)
        call("tn_prefix_sum_w", x, out, check=check)
    else:
        if out is None:
            out = np.zeros(n, dtype=np.int64)
        call("tn_prefix_sum" if n <= 10**6 else "tn_prefix_sum_10m", x, out, check=check)
    return out


def rolling_sum(x, w, out=None, check=True, kernel="wide"):
    """out[i] = sum of x[max(0, i-w+1) .. i]. x within ±10^9, 1 <= w <= 10^6, at most 10^7 elements.
    kernel: "wide" (`rollingSumW`, out: full int64, no scan of out), "exact" (`rollingSumExact`,
    out ±10^15) or "loose" (`rollingSum`, out ±2.1·10^16). All three compile to the same loops."""
    name = {"wide": "tn_rolling_sum_w", "exact": "tn_rolling_sum_exact", "loose": "tn_rolling_sum"}[kernel]
    if out is None:
        out = np.empty(_len(x), dtype=np.int64) if kernel == "wide" else np.zeros(_len(x), dtype=np.int64)
    call(name, x, w, out, check=check)
    return out


def lower_bound(a, p):
    """First index i in 0..len(a) with a[i] >= p, for a sorted in ascending order (branch-free search).
    Safe for any int64 contents and any length; the answer is meaningful only if a is sorted."""
    return call("tn_lower_bound", a, p)


def lower_bound_branchy(a, p):
    return call("tn_lower_bound_branchy", a, p)


def argmax(a):
    """Index of the first maximum. Like numpy.argmax, an empty array is an error (the kernel itself
    returns 0 for it)."""
    r = call("tn_argmax", a)
    if a.shape[0] == 0:
        raise ValueError("attempt to get argmax of an empty sequence")
    return r


def _fout(x, out):
    # any float64 contents are a legal `inout fslice` argument: no zero-fill
    return np.empty(_len(x), dtype=np.float64) if out is None else out


def ewma(x, alpha, out=None):
    """out[i] = alpha * x[i] + (1.0 - alpha) * out[i-1], with out[-1] = 0.0. Returns `out`."""
    out = _fout(x, out)
    call("tn_ewma", x, alpha, out)
    return out


def sum8(x):
    """Sum of x in the fixed eight-lane order of Sum8.lean. Returns a Python float."""
    out = np.empty(1, dtype=np.float64)
    call("tn_sum8", x, out)
    return float(out[0])


def dot(x, y):
    """Dot product in the same eight-lane order (len(x) == len(y)). Returns a Python float."""
    out = np.empty(1, dtype=np.float64)
    call("tn_dot", x, y, out)
    return float(out[0])


def rolling_mean(x, w, out=None):
    """out[i] = mean of the last min(i+1, w) elements, from an incrementally updated sum (rounding
    errors accumulate along the array; a NaN or infinity in x makes all later outputs NaN)."""
    out = _fout(x, out)
    call("tn_rolling_mean", x, w, out)
    return out


def rolling_var(x, w, out=None):
    """Population variance of the last n = min(i+1, w) elements as (s2 - s1*s1/n)/n from running sums.
    NUMERICALLY NAIVE: cancels badly when |mean| >> spread; values <= 0 are returned as 0.0."""
    out = _fout(x, out)
    call("tn_rolling_var", x, w, out)
    return out


def rolling_std(x, w, out=None):
    """sqrt of the same quantity as `rolling_var`."""
    out = _fout(x, out)
    call("tn_rolling_std", x, w, out)
    return out
