# The C generator, its tests, the binding and the measurements, in detail

This is the working report of the last development round of the generator. Names of rounds appear in it:
"emit3", "emit4" and "emit5" are the third to fifth rounds of the generator (this tree is emit5), and K1 to
K4 are earlier versions of the kernel (K5 was renamed Tenon). Files it calls `../k1/...` are in the root
of this repository. The top-level README is the summary; where a number here and there differ, the result
files (`*/RESULT.txt`) decide.


Status: the emitter and the binding are **not proved**. The emitter is ordinary Lean code that prints
C; the binding is ordinary Python. Their evidence is a differential test against `evalFn`, an
operation-by-operation comparison of Lean's `Float` with the generated C, tests against NumPy, and
benchmarks. Nothing under `` or `../emit*/` other than this directory was edited.

Kernel copy (`kernel.sha256`), copied from `` and not changed:

    2589c4888866b14b4b5af15db5dd83df74e993d49b087a7519a53d556b4f0d06  Tenon.lean
    81fbda2a099c44dbdb2c047c07d97998162177dcbec5d008461856f6ce9d2ba4  Ewma.lean
    e494c63c195a1bc5ad0c10971c33df39c4aea8111ef10bd615904888269f8d73  Sum8.lean
    0c82f0a1442183a30e92e45a990ac45db8b6bb6b2ac4bae60cd6105a98be5eb6  Surface.lean

History of the copy (four copies in three hours; the kernel moved while I worked):
1. `kernel.sha256.first`, Tenon.lean `171db101...`: no `req`.
2. Tenon.lean `fa6453e3...`: `Fn.req : Cond`, `evalC`, `kvc` inside Tenon.lean; Surface.lean `91abe84b...`,
   then `1e70eead...` when it gained floats (`kernel.sha256.second`). The emitter, the binding and most
   proofs were written against this.
3. The copy above: the call obligation also hands over `hasAll` of the returned values, `kvc` handles
   calls, Surface.lean has `sel(a <= b, t, e)` and calls. Adapting took one extra `intro` in one proof
   of `Legacy.lean` and, again, renaming (`sel` and `call` became reserved words, see below).
**Every result in this file (proofs, floatcheck, difftest, binding tests, benchmark) is from a run
after the last copy**, except that `floatcheck/RESULT.txt` and `bench/RESULT.txt` were produced
between copies 2 and 3; the emitted C is byte-identical across them (`execS`, `evalFn` and the
emitter did not change), and the difftest and the binding tests were rerun in full after copy 3. `PrefixSum.lean` is still a K4 file, so `prefixSum` is restated on Tenon in
`Examples.lean` (same body and invariant, its precondition as `req`).

## Files

| File | Content |
|---|---|
| `Tenon.lean`, `Ewma.lean`, `Sum8.lean`, `Surface.lean` | the kernel copy |
| `Emit.lean` | the emitter: `Tenon.Emit.emitProgram : Options → List Fn → List FnNames → Except String String` |
| `Examples.lean` | 16 `FnOk`/`ProgOk` proofs (9 integer, 7 float; two of them imported from `Ewma.lean`/`Sum8.lean`), 13 unproved programs that exercise the emitter; 47 test entries |
| `Legacy.lean` | the 28 K3 programs of `emitter round 3` moved to Tenon, with their nine proofs |
| `KernelFindings.lean` | reproducers for the observations about the kernel (builds; prints at build time) |
| `floatcheck/FloatCheck.lean`, `run.sh`, `compare_ops.py`, `RESULT.txt` | Lean `Float` against the generated C, operation by operation, on bit patterns |
| `difftest/DiffTest.lean`, `run.sh`, `compare.py`, `RESULT.txt` | random program and input generator, `evalFn` runner, C driver writer, bitwise comparison |
| `py/PyGen.lean`, `py/build.sh` | write `py/build/tenon_kernels.c`, `tenon_kernels.json` (signatures, ranges, the requirement of each kernel as a Python expression), `tenon_req_tests.json`; build `libtenon_kernels.so` |
| `py/tenon_kernels.py`, `py/test_tenon_kernels.py`, `py/RESULT.txt` | the binding (ctypes, zero-copy) with its entry checks; 27 tests |
| `bench/BenchGen.lean`, `hand.c`, `naive.c`, `bench.c`, `bench_py.py`, `run.sh`, `RESULT.txt` | benchmarks and assembly |

## How to run (one command each, from ``)

    PATH=$HOME/.elan/bin:$PATH lake build     # everything; checks the proofs; prints the emitted C of every example and the findings
    ./floatcheck/run.sh                       # Lean Float vs generated C, per operation (about 12 min: the interpreted Lean pass is slow)
    ./difftest/run.sh                         # differential test (cores 8-15; 45 min here)
    ./py/build.sh && (cd py && python3 test_tenon_kernels.py)    # shared library, then the binding against NumPy (13 s)
    ./bench/run.sh                            # C and Python benchmarks and the assembly, pinned to core 12 (11 min)

Smaller runs: `SEEDS="1 2" NPROGS=60 NINPUTS=8 ./difftest/run.sh`, `QUICK=1 ./bench/run.sh`,
`N=2000 ./floatcheck/run.sh`. A single random program: `.lake/build/bin/difftest show <seed> <index>`;
one input and `evalFn`'s answer: `.lake/build/bin/difftest case <seed> <index> 16 <case>`.
Lean 4.35.0, clang 21.1.8, gcc 13.3.0, Python 3.12.7, NumPy 2.2.6 (scipy-openblas 0.3.29); nothing was
installed. Xeon E5-2650 v3 (Haswell: AVX2 and FMA), Linux 6.8.

## What the emitter does with Tenon

Everything `emitter round 4` did is kept and still under test (`Legacy.lean`, the K4 examples). New:

| Tenon | C |
|---|---|
| `Ty.flt` by value / `inout` | `double x` / `double *x_io` (copied in at entry, copied out once before `return`) |
| `Ty.fslice`, by value, not modified | `const double *restrict a, int64_t a_len` |
| `Ty.fslice`, `inout` | `double *restrict a, int64_t a_len`, written in place |
| `Ty.fslice`, by value, stored into | `const double *restrict a_arg, int64_t a_len` and a private heap copy (`tn_fcopy`), freed at the single exit |
| `FExpr.lit f` | a decimal constant for small integers (`0.0`, `-3.0`), otherwise a hexadecimal floating constant (`0x1.999999999999ap-4`), exact by construction; infinities and NaN through `tn_bits(UINT64_C(0x...))` |
| `add sub mul div` | `+ - * /` in the shape of the term; **both** operands that are operators of the same class are parenthesised (`(a + b) + c`, `(s1 * s1) / n`), so the order of the rounding steps is visible in the text |
| `idx a e` | `a[e]`, no bounds check |
| `ofInt e` | `(double)e` (the operand is an `int64_t` expression) |
| `neg`, `abs`, `sqrt` | `-x`, `fabs(x)`, `sqrt(x)` |
| `sel c t e` | `tn_fsel(c != 0, t, e)` (or the comparison itself when `c` is one); `selLe a b t e`: `tn_fsel(a <= b, t, e)`. Four C forms, chosen by `Options.selForm` as for the integer `sel` |
| `fassign`, `fstore`, `fdecl` | `x = e;`, `a[i] = e;`, `double x = e;` |
| `fite a b s t` | `if (a <= b) { s } else { t }`; when `s` is empty: `if (!(a <= b)) { t }`, **never** `if (a > b)` (they differ on NaN) |
| `len a` of a float slice | `a_len` |
| `loopE e I s` | `for (;;) {  /* proof bound: e iterations */ ... }`: the bound is printed as a comment and **not evaluated** |

A file that contains float code starts with guards (`Emit.floatGuard`): `#error` under `__FAST_MATH__`
or `__FINITE_MATH_ONLY__`, `#error` unless `FLT_EVAL_METHOD == 0`, a static assertion that `double` is
binary64, and `#pragma STDC FP_CONTRACT OFF`. What these are worth was measured (below, "Compiler flags").

Generated C of the float kernels (`py/build/tenon_kernels.c`; `lake build` prints all examples):

```c
int64_t tn_ewma(const double *restrict x, int64_t x_len, double alpha, double *restrict out, int64_t out_len)
{
    int64_t res = 0;
    double prev = 0.0;
    for (int64_t i = 0, i_end = x_len; i < i_end; i++) {
        prev = alpha * x[i] + (1.0 - alpha) * prev;
        out[i] = prev;
    }
    return res;
}

int64_t tn_dot(const double *restrict x, int64_t x_len, const double *restrict y, int64_t y_len, double *restrict out, int64_t out_len)
{
    int64_t res = 0;
    double a0 = 0.0;
    /* ... a1 to a7 ... */
    int64_t n8 = tn_div(x_len, 8);
    for (int64_t i = 0, i_end = n8; i < i_end; i++) {
        a0 = a0 + x[8 * i + 0] * y[8 * i + 0];
        /* ... a1 to a6 ... */
        a7 = a7 + x[8 * i + 7] * y[8 * i + 7];
    }
    for (int64_t j = 0, j_end = x_len - 8 * n8; j < j_end; j++) {
        a0 = a0 + x[8 * n8 + j] * y[8 * n8 + j];
    }
    out[0] = ((a0 + a1) + (a2 + a3)) + ((a4 + a5) + (a6 + a7));
    return res;
}

int64_t tn_rolling_mean(const double *restrict x, int64_t x_len, int64_t w, double *restrict out, int64_t out_len)
{
    int64_t res = 0;
    double acc = 0.0;
    int64_t m = w;
    if (w > x_len) {
        m = x_len;
    }
    for (int64_t i = 0, i_end = m; i < i_end; i++) {
        acc = acc + x[i];
        out[i] = acc / (double)(i + 1);
    }
    for (int64_t j = 0, j_end = x_len - m; j < j_end; j++) {
        acc = (acc + x[j + m]) - x[j];
        out[j + m] = acc / (double)m;
    }
    return res;
}

int64_t tn_rolling_var(const double *restrict x, int64_t x_len, int64_t w, double *restrict out, int64_t out_len)
{
    int64_t res = 0;
    double s1 = 0.0;
    double s2 = 0.0;
    int64_t m = tn_sel(w <= x_len, w, x_len);
    for (int64_t i = 0, i_end = m; i < i_end; i++) {
        s1 = s1 + x[i];
        s2 = s2 + x[i] * x[i];
        double n = (double)(i + 1);
        double v = (s2 - (s1 * s1) / n) / n;
        out[i] = tn_fsel(v <= 0.0, 0.0, v);
    }
    double mf = (double)m;
    for (int64_t j = 0, j_end = x_len - m; j < j_end; j++) {
        double a = x[j + m];
        double b = x[j];
        s1 = (s1 + a) - b;
        s2 = (s2 + a * a) - b * b;
        double v2 = (s2 - (s1 * s1) / mf) / mf;
        out[j + m] = tn_fsel(v2 <= 0.0, 0.0, v2);
    }
    return res;
}
```

## Every place the generated code relies on something it does not check

### A. On the theorem (`prog_sound`); marked "RELIES ON T2" in `Emit.lean`

Items 1 to 11 are those of emit4 and are unchanged: (1) no bounds check on integer loads and stores,
(2) no integer overflow check, (3) `div` is unsigned, (4) values assigned and stored are in the
declared range, (5) `loopB` is `for (;;)`, (6) both arms of `sel` are evaluated, (7) a `forE` bound
is not negative, (8) `len a` is the length parameter, (9) calls (types, requirement, result range,
`exclusive`; in-place `inout` equals copy-in copy-out only under `exclusive`, which is still **not
proved** in the kernel), (10) a slice passed where an array is expected has that length, (11) every
value read fits `int64_t`. New with Tenon:

12. **`loopE`: the bound expression is dropped.** Tenon's `execS` evaluates `e` at loop entry and is
    stuck if that evaluation is stuck (an overflow, a division by zero, an index out of range inside
    `e`), and also if `e` is negative (zero iterations, and running out of iterations is stuck). The C
    is `for (;;)` and never computes `e`. A checked program's bound is never stuck (`wpS` sends `e`
    through `wpE`), so for it the difference is unobservable. For an unchecked program the C runs
    where Tenon is stuck: reproducer Tenon in `KernelFindings.lean` (`evalFn` is `none` for a bound
    `1 / 0`, the C returns 7). And as for `loopB`, outside the guarantee the C loop may not terminate.
13. **No bounds check on float loads and stores** (`a[e]`, `a[i] = v` for a float slice): `0 ≤ i <
    len`, the run-time length.
14. **The integer parts of float code**: the condition of a float `sel`, the argument of `ofInt`, and
    the indices are integer expressions with all of items 1 to 11.
15. **Both arms of a float `sel` and all four operands of `selLe` are evaluated**; an index in an arm
    that is not selected must be in range (same as item 6).

Float arithmetic itself relies on nothing from the theorem: no Tenon float operation can be stuck, so
there is no obligation about float values at all (and nothing is proved about them, see finding K4).

### B. On the C compiler and its flags (not covered by any theorem; see "Compiler flags")

16. **`+ - * /`, `sqrt`, `fabs`, `-x`, `(double)int64`, `<=` are the IEEE-754 binary64 operations,
    each rounded once to nearest-even, evaluated in the order written.** True for clang and gcc on
    x86-64 with `-ffp-contract=off` and no fast-math option; false otherwise. This is the
    correspondence the kernel trusts ("Lean's `Float` is what the C computes"); it was measured, per
    operation and through whole programs, not proved.
17. **Hexadecimal floating constants are converted exactly** by the compiler (C11 requires it for
    binary radix).

### C. On the caller: what a binding must establish at entry (the emitted C has no checks)

18. Argument types: buffers of the right element type and the stated length, integers in range.
19. The function's requirement `req` (now data, see the binding: generated, not retyped).
20. No `inout` buffer overlaps another argument (`restrict`; the top-level instance of `exclusive`).
21. **The floating-point environment of the calling thread**: rounding to nearest, flush-to-zero and
    denormals-are-zero off. Tenon has no notion of a rounding mode; the C inherits whatever the process
    set. A library built with `-ffast-math` and loaded into the same process can switch FTZ/DAZ on;
    subnormal results then differ from Tenon's. The binding checks it (E6).

Not from the theorem: `tn_copy`/`tn_fcopy` abort when `malloc` fails (a modified by-value slice).

## Compiler flags: what the float guarantee needs, exactly, and why

    -ffp-contract=off          and none of:  -ffast-math  -Ofast  -funsafe-math-optimizations
    -fassociative-math  -freciprocal-math  -ffinite-math-only  -fno-signed-zeros  -mfpmath=387

on x86-64 (SSE2 arithmetic, which is the default there); `-fno-fast-math` is written in every command
line here to make the absence explicit. `-O` level, `-march=native`, `-fno-math-errno` and
vectorisation do not change values and are allowed (`-O0`, `-O2`, `-O2 -march=native`, and gcc `-O3
-march=native` in floatcheck, all gave identical bits).

- **`-ffp-contract=off`: no fused multiply-add.** `a * b + c` in Tenon is a rounded product followed by a
  rounded sum. With FMA instructions available (`-mfma`, `-march=native` on any CPU since 2013) a
  compiler that is allowed to contract computes `fma(a, b, c)` with one rounding. The defaults differ:
  **gcc defaults to `-ffp-contract=fast` unless `-std=c11` (an ISO mode) is given; clang defaults to
  `on`** (contraction inside one expression). `ewma`, `dot`, `rolling_var` all contain `a * b + c`.
- **No reassociation** (`-fassociative-math`, part of `-ffast-math`): `(a0 + a1) + (a2 + a3)` must
  stay that tree. The whole point of `sum8`/`dot` is the fixed tree.
- **No `-ffinite-math-only`, no `-fno-signed-zeros`**: `selLe` and `fite` are defined on NaN (false),
  and `-0.0` is a value (`neg`, `abs`, `sqrt(-0.0) = -0.0`).
- **`sqrt` correctly rounded**: `sqrt()` of glibc and the `sqrtsd` instruction both are; with
  `-fno-math-errno` the compiler inlines the instruction, without it it calls libm for negative
  arguments only. Same values either way (measured).
- **Double evaluation in double precision** (`FLT_EVAL_METHOD == 0`): x87 arithmetic
  (`-mfpmath=387`, or a 32-bit x86 build without SSE2) rounds twice.

What was measured about the guards in the emitted file (`difftest/RESULT.txt`, section 3e; the same
emitted C, compiled in ways the guarantee forbids, on the hand-written suite and on the random
programs of seed 1):

| Compiled with (the emitted C unchanged unless noted) | hand-written suite (25,583 inputs) | random programs, seed 1 (6,954 inputs) | |
|---|---|---|---|
| `-std=c11 -ffp-contract=off -fno-fast-math`, seven builds | no mismatch | no mismatch | the supported way |
| `gcc -O2 -std=c11 -march=native` | no mismatch | no mismatch | ISO mode: gcc contracts nothing |
| `clang -O2 -std=c11 -march=native` | no mismatch | no mismatch | contraction is `on` by default; **the pragma stops it** |
| `clang -O2 -std=c11 -march=native` | 885 inputs differ, 5558 doubles wrong | 14 inputs differ, 15 doubles wrong | the same file with the `#pragma` line removed: clang contracts |
| `gcc -O2 -std=gnu11 -march=native` | 885 inputs differ, 5560 doubles wrong | 30 inputs differ, 40 doubles wrong | gcc's default dialect: contraction `fast`, **the pragma is ignored** |
| `clang -O2 -std=c11 -mfma -ffp-contract=fast` | 592 inputs differ, 4648 doubles wrong | 14 inputs differ, 15 doubles wrong | `fast` **overrides the pragma** |
| `gcc -O2 -std=c11 -mfma -ffp-contract=fast` | 383 inputs differ, 1793 doubles wrong | 27 inputs differ, 37 doubles wrong |  |
| `gcc -O2 -std=c11 -fassociative-math -fno-signed-zeros -fno-trapping-math` | 306 inputs differ, 1427 doubles wrong | 6444 inputs differ, 12 doubles wrong | reassociation without `-ffast-math`: **no guard fires** |
| `gcc -O2 -std=c11 -ffp-contract=off -fno-signed-zeros` | 2 inputs differ, 2 doubles wrong | 19 inputs differ, 19 doubles wrong | **no guard fires** |
| `clang -O2 -std=c11 -ffast-math` | refused at compile time (`#error`) | refused at compile time (`#error`) | the `__FAST_MATH__` guard |
| `gcc -O2 -std=c11 -ffast-math` | refused at compile time (`#error`) | refused at compile time (`#error`) |  |
| `gcc -O2 -std=c11 -ffp-contract=off -mfpmath=387` | refused at compile time (`#error`) | refused at compile time (`#error`) | the `FLT_EVAL_METHOD` guard |

So: the pragma protects under clang's default but not under `-ffp-contract=fast`, and gcc ignores
it; the `#error` catches `-ffast-math` but not `-fassociative-math` alone. **The flags are the
guarantee; the guards are a partial safety net.** The Python binding adds one run-time probe
(`tn_probe_muladd`: a library that contracts is refused at import).

## Does Lean's `Float` agree with the generated C? (`floatcheck/`)

The kernel's float semantics is Lean's `Float`; the theorem is about `evalFn`; the machine runs C.
`floatcheck` compares the two for every operation Tenon uses. For each operation a one-line Tenon function
is emitted by the real emitter (`out[i] = x[i] + y[i]`, ..., `out[i] = (f64) a[i]`), Lean computes the
expected bits twice (directly, e.g. `x + y`, and through `evalFn` on the Tenon term), once as a compiled
program and once in the interpreter (`lean --run`), and the C is built seven ways. Inputs: all
44 × 44 pairs of special values (NaNs with payloads, quiet and signalling, ±inf, ±0, subnormals,
DBL_MIN, DBL_MAX, values around 1, 2^53 and 2^63), 30,000 random pairs (a third with one special
operand), 35 integer boundary values for `ofInt` (around 2^24, 2^53, ±2^63; the random bit patterns
are also read as `int64`). Operations: `add sub mul div neg abs sqrt`, `x*y + x` (the contraction
shape), `(x + y) + 1`, `selLe` (two forms), `fite` (two forms), `ofInt`.

```
fpcheck: 31971 input pairs (44x44 special, 30000 random, 35 integer), 14 operations, 447594 results; direct Lean operation vs evalFn on the Tenon term: 0 disagreements
compiled and interpreted Lean: identical results (447594 lines)
== C built with: <compiler> -std=c11 -w -ffp-contract=off -fno-fast-math ==
clang-O0: results=447594/447594 bit_equal=423509 both_nan_other_bits=24085 MISMATCH=0
clang-O2: results=447594/447594 bit_equal=423509 both_nan_other_bits=24085 MISMATCH=0
clang-O2-native: results=447594/447594 bit_equal=423509 both_nan_other_bits=24085 MISMATCH=0
gcc-O0: results=447594/447594 bit_equal=423509 both_nan_other_bits=24085 MISMATCH=0
gcc-O2: results=447594/447594 bit_equal=423509 both_nan_other_bits=24085 MISMATCH=0
gcc-O2-native: results=447594/447594 bit_equal=423509 both_nan_other_bits=24085 MISMATCH=0
gcc-O3-native: results=447594/447594 bit_equal=423509 both_nan_other_bits=24085 MISMATCH=0
== for contrast: the same C with contraction allowed (-mfma -ffp-contract=fast); 'muladd' must differ ==
clang-fma-fast: results=447594/447594 bit_equal=419434 both_nan_other_bits=24085 MISMATCH=4075
gcc-fma-fast: results=447594/447594 bit_equal=419433 both_nan_other_bits=24085 MISMATCH=4076
RESULT: Lean Float and the generated C agree on every non-NaN result
```

**Answer: yes, on this machine, for every operation Tenon uses, compiled and interpreted Lean and the
generated C agree bit for bit on every result that is not a NaN** (423,509 of 447,594 results;
`Float.ofInt` on the whole int64 range, `sqrt`, `abs`, negation of zero and of NaN-free values,
comparisons with NaN and with ±0 included). **For the 24,085 NaN results the comparison is only "both
are NaN"**: Lean's `Float.toBits` returns `0x7ff8000000000000` for every NaN, so Lean cannot say which
NaN it has, while the C produced several (`floatcheck/RESULT.txt` lists the patterns per operation:
`fff8000000000000` for `sqrt` of a negative number and for inf − inf at run time, the input's payload
for propagated NaNs, the quieted payload `7ff8000000000001` for a signalling input, flipped signs
after `neg`). This is finding K1; no Tenon operation can observe the difference.

The contrast lines show that the test can fail: with contraction allowed, 4,075 (clang) and 4,076
(gcc) of the 31,971 `x*y + x` results differ, and nothing else does.

## Differential test (`difftest/`)

Method as in emit4: a compiled Lean program generates programs and inputs, runs Tenon's `evalFn` on every
input, and writes one C file per batch (the emitted functions and a `main` that calls them **only on
the inputs where `evalFn` is `some`**) and the expected results. An input where `evalFn` is `none` is
counted as skipped, never as a pass, and a C result for it is an error. After each call the driver
prints the result, the final value of every `inout` scalar and the contents of every array and slice
argument (for by-value ones the expected line holds the input: the callee must not have touched the
caller's buffer); every buffer has a canary element behind it.

New for floats:
- **Doubles are given to C and printed by C as bit patterns** (a union of `uint64_t` and `double`;
  the expected file has `f:` and 16 hexadecimal digits) and `compare.py` compares **the bit pattern**:
  `+0.0` against `-0.0` is a mismatch, one ulp is a mismatch.
- **NaN payload differences are reported separately** (`nan_payload_differs`, per build), not hidden
  and not counted as mismatches: both sides are NaN and the bits differ. The reference cannot do
  better (K1). For by-value float slices the expected bits are the exact input bits, payload included.
- Float inputs: a per-input share (0, 10, 30 or 60 %) from a set of 35 special bit patterns (five
  NaNs, ±inf, ±0, five subnormals, ±DBL_MIN, ±DBL_MAX, 1, −1, 1 + ulp, 1 − ulp/2, 2^53 − 1, 2^53,
  2^53 + 2, 0.1, 1/3, 0.5, 3, 1e308, 1e−308, ±1e16); the rest mostly of moderate magnitude with random
  mantissas (where `a*b + c` and `(a+b)+c` round differently from their contracted or reassociated
  forms), some small integers and halves, some spread over 600 binary orders, some arbitrary bits.
- Builds: clang 21.1.8 and gcc 13.3.0 at `-O0` and `-O2`, clang `-O1 -fsanitize=undefined,address`,
  **and clang and gcc at `-O2 -march=native`** (FMA and AVX2 available to the compiler, and it must
  not use FMA), all with `-std=c11 -ffp-contract=off -fno-fast-math`.

Programs.
- Hand-written, 400 random inputs each: the 47 entries of `Examples.all` (the proved integer kernels;
  the six integer functions of `Surface.lean`, one of them a `loopE`, one with `sel`, one with a call; `ewma`, `sum8`, `ewma_s`,
  `mean_mad`, `rolling_mean`, `rolling_var`, `rolling_std`, `dot`, most of them twice, once with
  special values and once with finite inputs only; and unproved float programs: `fcontract`
  (`a*b + c`, `c − a*b`, `(a+b)+c`, `a*b − c*c` on three slices), `funary` (`fabs`, unary minus, `sqrt`
  directly on inputs), `fconv` (`ofInt` on the whole int64 range and around 2^53), `fmix` (every float
  construct, an `inout` float scalar, a by-value float slice that is stored into, a float-controlled
  `loopE`), `fcall` (float slices by value and `inout` and a float scalar `inout` passed to a callee))
  and the 28 K3 programs of emit3. Plus four known-stuck inputs each for five functions.
- Random: the generator of emit4 extended. 60 % of the programs use floats: float and float-slice
  parameters (two thirds `inout`), a float local, `fassign`, `fstore` (also into by-value slices),
  `fdecl`, `fite`, all thirteen `FExpr` constructors, the contraction shapes `a*b + c`, `c + a*b`,
  `a*b − c` and the reassociation shape `(a+b)+c` generated on purpose, `selLe` often comparing a
  value with itself, calls with float arguments, `loopE` with four kinds of bound expression (a
  literal, `len(a) + k`, `k + clamp(e)`, a product) and, in risky programs, bounds that are too small,
  stuck or negative, and a float-controlled `loopE` (halve until below 1.0; an infinity exhausts the
  bound and is stuck). Float results are observable only through `inout` float parameters and through
  `fite` deciding integer code, so every function with floats ends by writing its float local into
  its `inout` float parameters.

Result of the last full run (`difftest/RESULT.txt`):

```
== 1. hand-written programs (Examples.lean), 400 random inputs each ==
expected: programs=75 programs_with_comparable_input=74 inputs_some=25583 inputs_none(skipped)=3737 values_compared=673777 emit_errors=0
expected floats: float_values=275359 nan=42323 inf=4736 zero=10651 (negative_zero=1369) subnormal=6119
  clang-O0         compared=25583 skipped=3737 mismatches=0 errors=0 | floats_compared_bitwise=275359 float_values_wrong=0 nan_payload_differs=34916
  clang-O2         compared=25583 skipped=3737 mismatches=0 errors=0 | floats_compared_bitwise=275359 float_values_wrong=0 nan_payload_differs=34429
  gcc-O0           compared=25583 skipped=3737 mismatches=0 errors=0 | floats_compared_bitwise=275359 float_values_wrong=0 nan_payload_differs=35064
  gcc-O2           compared=25583 skipped=3737 mismatches=0 errors=0 | floats_compared_bitwise=275359 float_values_wrong=0 nan_payload_differs=35022
  clang-ubsan      compared=25583 skipped=3737 mismatches=0 errors=0 | floats_compared_bitwise=275359 float_values_wrong=0 nan_payload_differs=34993
  clang-O2-native  compared=25583 skipped=3737 mismatches=0 errors=0 | floats_compared_bitwise=275359 float_values_wrong=0 nan_payload_differs=34549
  gcc-O2-native    compared=25583 skipped=3737 mismatches=0 errors=0 | floats_compared_bitwise=275359 float_values_wrong=0 nan_payload_differs=34883
== 1b. the same hand-written programs with the other three C forms of sel (no hint, lazy ?:, bit mask) ==
  (three times the same seven lines: mismatches=0 errors=0, float_values_wrong=0)
== 2. random programs: seeds [1 2 3 4 5 6 7 8], 500 programs per seed, 16 inputs per program ==
-- seed 1: input_sensitive_programs=388 generated: programs=500 functions=1009 emit_errors=0 cases_some=6954 cases_none=1046 tn_features: forE=1627 len=6108 sel=9148 le=5404 lt=3102 eq=3076 slice_params_read_only=130 slice_params_inout=233 slice_params_private_copy=108 tn_features: loopE=695 fassign=1734 fstore=403 fdecl=1049 fi ...
expected: programs=500 programs_with_comparable_input=489 inputs_some=6954 inputs_none(skipped)=1046 values_compared=78157 emit_errors=0
expected floats: float_values=23667 nan=829 inf=362 zero=607 (negative_zero=146) subnormal=749
  clang-O0         compared=6954 skipped=1046 mismatches=0 errors=0 | floats_compared_bitwise=23667 float_values_wrong=0 nan_payload_differs=413
  clang-O2         compared=6954 skipped=1046 mismatches=0 errors=0 | floats_compared_bitwise=23667 float_values_wrong=0 nan_payload_differs=381
  gcc-O0           compared=6954 skipped=1046 mismatches=0 errors=0 | floats_compared_bitwise=23667 float_values_wrong=0 nan_payload_differs=412
  gcc-O2           compared=6954 skipped=1046 mismatches=0 errors=0 | floats_compared_bitwise=23667 float_values_wrong=0 nan_payload_differs=412
  clang-ubsan      compared=6954 skipped=1046 mismatches=0 errors=0 | floats_compared_bitwise=23667 float_values_wrong=0 nan_payload_differs=409
  clang-O2-native  compared=6954 skipped=1046 mismatches=0 errors=0 | floats_compared_bitwise=23667 float_values_wrong=0 nan_payload_differs=381
  gcc-O2-native    compared=6954 skipped=1046 mismatches=0 errors=0 | floats_compared_bitwise=23667 float_values_wrong=0 nan_payload_differs=412
  (seeds 2 to 8: compared 7052, 7022, 7012, 6905, 7085, 7066, 7034; mismatches=0 errors=0 float_values_wrong=0 in all seven builds)
== 2b. random programs of seed 1 with the other three C forms of sel ==
  (three times: compared=6954 skipped=1046 mismatches=0 errors=0 in all seven builds)
== 3. self-tests of the harness ==
3a PASS: the 4 known-stuck inputs of k3_lower_bound are none, 0 of them are called from C
3a PASS: the 4 known-stuck inputs of rolling_sum are none, 0 of them are called from C
3a PASS: the 4 known-stuck inputs of prefix_sum are none, 0 of them are called from C
3a PASS: the 4 known-stuck inputs of ewma are none, 0 of them are called from C
3a PASS: the 4 known-stuck inputs of dot are none, 0 of them are called from C
3a PASS: k3_alias_bad (non-exclusive call): 400 inputs, all none, 0 called from C
3a PASS: k3_alias_branch (non-exclusive call on one branch): 152 inputs compared, 248 none
3b PASS: 1 error reported for a C result on a none input
3c PASS: mismatches=1 for one altered final value of an inout parameter ((final parameter values))
3c2 PASS: an OVERRUN marker in a result line is reported (errors=1)
  (3d and 3e: below)
== total ==
programs=4075 programs_with_comparable_input=4004 inputs_compared(evalFn=some)=81713 inputs_skipped(evalFn=none)=11607 values_compared=1260541 (of which doubles, compared on the bit pattern: 437849); each compared input was run in 7 C builds (the suite and the first seed in 28: four C forms of sel)
sums over all batches: input_sensitive_programs=3121 programs=4075 functions=8133 emit_errors=0 cases_some=81713 cases_none=11607 forE=12912 len=45136 sel=72619 le=43573 lt=25325 eq=24714 slice_params_read_only=1006 slice_params_inout=1753 slice_params_private_copy=765 loopE=5255 fassign=12967 fstore=2862 fdecl=7750 fite=5193 f_lit=19114 f_var=54633 f_add=12067 f_sub=5012 f_mul=8741 f_div=1936 f_idx=1703 f_ofInt=1968 f_sel=3877 f_neg=1903 f_abs=3915 f_sqrt=1906 f_selLe=3940 mul_add_shapes=4085 add_add_shapes=2188 float_params_by_value=786 float_params_inout=1558 fslice_params_by_value=737 fslice_params_inout=1534 total=36273 len0=5324 len1=5122 len2to8=9091 len9plus=16736 forN=9078 loopB=6164 breaks=15553 stores=8358 decls=44591 ifs=117120 assigns=218539 calls=5740 calls_with_inout=2828 calls_not_exclusive=142 int_by_value=4705 int_inout=2323 array_inout=5010 array_by_value_read_only=2190 array_by_value_private_copy=2126 of_those_stored_into=2003 only_passed_inout=123
RESULT: no mismatch
```

**No mismatch**: 4,075 programs (8,133 functions), 81,713 inputs compared and 11,607 skipped,
1,260,541 values of which **437,849 doubles compared on the bit pattern**, in seven C builds each (105
comparison lines, all `mismatches=0 errors=0`); the hand-written programs and seed 1 also in the three
other C forms of the selects. 3,121 programs gave at least two different outcomes on their inputs.
Among the expected doubles of the hand-written suite were 42,323 NaNs, 4,736 infinities, 1,369
negative zeros and 6,119 subnormals.

**NaN payloads, reported separately**: between 344 and 413 doubles per random batch and between 34,429
and 35,064 of the suite's 275,359 are NaN on both sides with different bits (sign or payload). The
count differs from build to build (clang `-O0` 34,916, clang `-O2` 34,429, gcc `-O0` 35,064 on the
suite): the C builds do not agree with each other on which NaN they produce, and Tenon cannot say which is
right (K1). Every non-NaN double was bit-identical in every build.

What the self-tests show. The 26 deliberate emitter breakages (16 of emit4, 10 new) are run against
the hand-written programs and against the random programs of seed 1: 51 of the 52 combinations are
detected, every breakage in at least one of the two. The ten new ones:

```
3d PASS: breakage 'fma' (66 differing lines of C) detected in suite: mismatches=634 (wrong=634 missing=0) float_values_wrong=2446
3d PASS: breakage 'fma' (990 differing lines of C) detected in r: mismatches=20 (wrong=20 missing=0) float_values_wrong=21
3d PASS: breakage 'reassoc' (10 differing lines of C) detected in suite: mismatches=227 (wrong=227 missing=0) float_values_wrong=456
3d PASS: breakage 'reassoc' (554 differing lines of C) detected in r: mismatches=7 (wrong=7 missing=0) float_values_wrong=7
3d PASS: breakage 'selLeNaN' (65 differing lines of C) detected in suite: mismatches=11222 (wrong=824 missing=10398) float_values_wrong=14568
3d PASS: breakage 'selLeNaN' (8378 differing lines of C) detected in r: mismatches=6912 (wrong=6 missing=6906) float_values_wrong=0
3d PASS: breakage 'fleAsLt' (38 differing lines of C) detected in suite: mismatches=146 (wrong=146 missing=0) float_values_wrong=241
3d PASS: breakage 'fleAsLt' (2132 differing lines of C) detected in r: mismatches=6508 (wrong=32 missing=6476) float_values_wrong=21
3d PASS: breakage 'fselSwap' (6 differing lines of C) detected in suite: mismatches=10387 (wrong=44 missing=10343) float_values_wrong=465
3d PASS: breakage 'fselSwap' (582 differing lines of C) detected in r: mismatches=806 (wrong=232 missing=574) float_values_wrong=372
3d PASS: breakage 'ofIntF32' (52 differing lines of C) detected in suite: mismatches=626 (wrong=626 missing=0) float_values_wrong=10516
3d PASS: breakage 'ofIntF32' (512 differing lines of C) detected in r: mismatches=21 (wrong=21 missing=0) float_values_wrong=24
3d PASS: breakage 'sqrtF32' (16 differing lines of C) detected in suite: mismatches=10930 (wrong=730 missing=10200) float_values_wrong=6238
3d PASS: breakage 'sqrtF32' (458 differing lines of C) detected in r: mismatches=4454 (wrong=12 missing=4442) float_values_wrong=11
3d PASS: breakage 'absDrop' (24 differing lines of C) detected in suite: mismatches=126 (wrong=126 missing=0) float_values_wrong=176
3d MISS: breakage 'absDrop' (1020 differing lines of C) NOT detected in r
3d PASS: breakage 'negSub' (16 differing lines of C) detected in suite: mismatches=136 (wrong=136 missing=0) float_values_wrong=160
3d PASS: breakage 'negSub' (454 differing lines of C) detected in r: mismatches=26 (wrong=26 missing=0) float_values_wrong=26
3d PASS: breakage 'loopEEval' (8 differing lines of C) detected in suite: mismatches=34 (wrong=34 missing=0) float_values_wrong=0
3d PASS: breakage 'loopEEval' (1390 differing lines of C) detected in r: mismatches=223 (wrong=223 missing=0) float_values_wrong=60
  (the 16 breakages of emit4, 32 lines: all PASS)
3d summary: 51 detections, 1 misses: absDrop(r)
```

One miss, stated plainly: **`absDrop` is detected by the hand-written suite (126 inputs, through
`funary`) but not by the random programs of seed 1** (1,020 lines of C differ, no result differs).
`x < 0 ? -x : x` differs from `fabs` only on `-0.0` and on the sign of a NaN; the random programs
rarely let a `-0.0` reach an `abs` whose result is stored unchanged. The run counts a breakage as
detected if either set detects it and prints the miss. As in emit4, for several breakages most of the
evidence is "missing" results (the broken binary loops or crashes and the rest of the batch never
prints): detected, not localised.

The four the brief names are among them: `fma` (emit `fma(a, b, c)` for `a*b + c`) and its flag twin
(section 3e: the unbroken C compiled with `-mfma -ffp-contract=fast`), `reassoc` (`(a + b) + c`
emitted as `a + (b + c)`), `selLeNaN` (`selLe` emitted as `!(a > b) ? t : e` and `fite` as
`if (a > b) t else s`: right except on NaN), `fleAsLt` (`<` for `≤`). Two of my first breakages were
**not** detected by the first version of the suite and made me add programs: `ofIntF32` (conversion
through `float`; every integer the random programs converted was small enough to be exact; `fconv`
now covers the int64 range) and `absDrop` (`x < 0 ? -x : x` for `fabs`, wrong only for `-0.0` and for
the sign of a NaN; nothing stored an `abs` directly; `funary` does).

Run time and runaway protection. The generator runs `evalFn` on every input, so a generated program
with a huge loop would hang it (this happened in emit4, and an orphaned generator process of an
earlier emit4 run was found spinning during this work). Loop bounds in generated programs are small by
construction (`forN` ≤ 12; `forE` bounds are `len` ≤ 24 or clamped to ≤ 12, the clamp is never
dropped, not even in risky programs; `loopB`/`loopE` proof bounds ≤ 64, or 1100 for the
float-controlled loop; nesting depth ≤ 2), and `run.sh` now gives every generator invocation a time
limit (`timeout 900`) and every compiled test binary one (600 s; 20 s for deliberately broken ones).
The whole run took 45 min 10 s here (239 CPU-minutes on eight cores, most of it compiling the 19 MB
suite file with seven compilers).

**A mismatch found after this run, by a rerun with other seeds** (seed 401, program
148, one input, clang `-O1 -fsanitize=undefined,address` only): root-caused in
`MISMATCH-401-148.md` to a **clang 21.1.8 bug** (the `Float2Int` pass folds `1.0 <= x + x` to false
for a compile-time constant `x = 1e30`), reproducible with `opt` alone and without any generated
code (`repro/`). Not an emitter, kernel or harness fault; the emitter was not changed. It qualifies
"no mismatch" above: the default seeds did not contain the triggering shape (about one program in a
thousand does, and only one build of seven shows it).

Limits of this evidence: it is testing; slices have at most 24 elements here (40 in the hand-written
programs); the random programs are not checked programs, so they exercise the emitter on `evalFn`'s
semantics, not on the theorem; NaN signs and payloads are not compared (cannot be).

## Proved examples (`Examples.lean`, `Ewma.lean`, `Sum8.lean`)

All are proved `FnOk` and `ProgOk`, no `sorry`; `#print axioms` gives `propext, Classical.choice,
Quot.sound` for each (`lake build` prints them).

| Function | Source form | What is proved | Invariant | Proof |
|---|---|---|---|---|
| `prefixSum`, `prefixSum10M` | core term | safety, `len(x) = len(out) ≤ 10^6 / 10^7` | `\|acc\| ≤ 10^9·i` | `kvc f [psInv]` |
| `prefixSumW` (out: full int64) | core term | the same | the same | `kvc` |
| `lowerBoundS` (branch-free), `lowerBoundBr` | core term | safety for every length; `0 ≤ r ≤ len(a)` | as emit4 | `kvc` |
| `argmax` | core term | safety; `r < len(a)` or empty | as emit4 | `kvc` |
| `rollingSum`, `rollingSumW` (out: full int64) | core term | safety, two loops | `\|acc\| ≤ 10^9·i`; `\|acc\| ≤ 10^15 + 2·10^9·j` | `kvc` |
| `rollingSumExact` | core term | safety with `out` in ±10^15 | `acc = psum x ...` | 80 lines by hand (as emit4) |
| `ewma` | core term (`Ewma.lean`) | safety for every length | `True` | `kvc ewma [ewmaInv]` |
| `sum8` | core term (`Sum8.lean`) | safety, `1 ≤ len(out)` | `True` | `kvc sum8 [sInv]` |
| (a) `rolling_mean(x: fslice, w: int(1, 10^6), out: inout fslice)` | **surface syntax** | safety, `len(x) = len(out)` | `True` | `kvc rolling_mean []` |
| (b) `rollingVar` (same signature), clamp with `selLe` | core term | safety | `True` | `kvc rollingVar [rvInv]` |
| (b) again: `rolling_var_s`, the same function with `sel(v <= 0.0, 0.0, v)` | **surface syntax** (since the last copy) | safety | `True` | `kvc rolling_var_s []`; **the emitter prints byte-identical C for the core term and this one** (checked by an `#eval` in `Examples.lean`) |
| (b') `rolling_std`, clamp with `if`, then `sqrt` | **surface syntax** | safety | `True` | `kvc rolling_std []` |
| (c) `dot(x: fslice, y: fslice, out: inout fslice)`, eight lanes | **surface syntax** | safety, `len(x) = len(y)`, `1 ≤ len(out)` | `True` | `kvc dot []` |

**What is proved for the float kernels is safety only**: no index out of range and no overflow in
the index arithmetic, for all inputs that satisfy `req`, whatever the float values (NaN and
infinities included). **Nothing is proved about the numbers**: not that `out` holds means or
variances, not that the clamped variance is ≥ 0, not that the result is finite. That is not a gap in
effort; with Lean's opaque `Float` no such statement can be proved (finding K4). The numbers are
tested against NumPy below.

(b) is, as asked, the numerically naive formula: `(s2 − s1·s1/n)/n` from running sums of `x` and
`x²`. It cancels catastrophically when the mean is large against the spread, the running sums drift,
and the result can be slightly negative; it is clamped with `selLe v 0 0 v` ("0 if v ≤ 0, else v"),
in that orientation so that a NaN stays a NaN (measured below: on data `1e8 + N(0,1)` it is wrong by
five orders of magnitude and 53,259 window results are clamped to 0 although the true variance is
about 1; it is fine on `N(0,1)`).

### How the proofs went, honestly

| Proof | Build attempts | What went wrong |
|---|---|---|
| the six one-line ports (`prefixSum*`, `lowerBound*`, `argmax`, `rollingSum`) and the two `W` variants | 1 | nothing; the 20-line proofs of emit4 were replaced by `kvc f [inv]` |
| `rollingSumExact` | 3 | the hand proof of emit4: one more `intro` (for `req`), `simp [evalC, evalCT]` instead of unfolding `pre`, and the list of impossible argument shapes doubled because `Val` has four constructors now |
| the nine proofs of `Legacy.lean` | 3 | same two mechanical changes (22 added match arms, written by a script); one call proof needed `evalC` in its `simp` set |
| `rolling_mean` | 1 | nothing |
| `dot` | 1 | needs `set_option maxRecDepth 8000` (copied from `Sum8.lean` before trying) |
| `rolling_std` | 2 | `simp` hit the recursion limit; same option |
| `rolling_var_s` | 1 | nothing (written after the last kernel copy, when the surface syntax had `sel`) |
| `rollingVar` | 3 | none in the proof. Two attempts were lost to a miscounted parenthesis in the 30-line core term with 12 de Bruijn levels; the error message was "fields missing: req, pre, post" and then a failing proof about a term containing `sorry` |

No float proof was hard, and that is the honest summary: the invariants are `True` and every
obligation is an index bound that `omega` closes. `Examples.lean` checks in 22 s.

### The surface syntax and `kvc` (`Surface.lean`): where they applied and what was missing

Used for four float kernels (`rolling_mean`, `dot`, `rolling_std`, and in the end `rolling_var_s`)
and for two unproved test programs (`fcontract`, `funary`). They are 12 to 25 readable lines each, no
positions, and proved by one line. The generated C is what a person would write. What was missing or
got in the way:

1. **`sel`/`selLe` were missing when I needed them and arrived with the last copy.** `rolling_var`
   was therefore first written as a core term (`rollingVar`, kept); `m = min(w, len(x))` in
   `rolling_mean` is `let m = w; if len(x) < w { m = len(x); } else { }`, which also doubles the
   obligations (both loops are checked once per branch). With `sel(a <= b, t, e)` the surface version
   `rolling_var_s` is 24 lines against a 30-line core term with 12 de Bruijn levels, and gives the
   same C. Still missing: the float select takes its orientation from the comparison only
   (`sel(v <= 0.0, 0.0, v)` keeps a NaN, `sel(0.0 <= v, v, 0.0)` does not), and nothing in the syntax
   makes the reader notice.
2. **Its keywords become reserved words in every file that imports it**: `len`, `bound`, `loop`,
   `upto`, `sqrt`, `fabs`, `int`, `slice`, `always`, and since the last copy `sel` and `call`. After
   `import Surface`, `forE (len 2) ...`, `(sel c t e)` and `call 0 [...] 1` (with `open Expr Stmt`) no
   longer parse and a local variable cannot be called `len` or `bound`. Each copy cost a round of
   renaming in `Examples.lean`, `KernelFindings.lean` and `DiffTest.lean` (`(len k)` to `(.len k)`,
   `(sel ...)` to `(.sel ...)`, `call` to `Stmt.call`). Its top-level names leak too: a new example
   called `argmax` in `Surface.lean` made `argmax` ambiguous in two of my files.
3. **A doc comment before `kfn` is a parse error** (`/-- ... -/ kfn f(...)`); only `--` comments work.
4. `invariant (True)` is mandatory even when there is nothing to say (all four float loops).
5. `if` needs an `else { }`; `<` on floats is rejected (sound, see K8), so the clamp is `if v <= 0.0`.
6. The result must be `int(lo, hi)`; a function that returns nothing writes `-> int(0, 0)`.
7. No calls, no fixed arrays, no `ensures` (stated in its header).
8. Integer-to-float conversion is implicit (`acc / (i + 1)`); convenient, but the source no longer
   shows where an `ofInt` happens, and `x / 2` means integer or float division depending on `x`.
9. `kvc` needs `set_option maxRecDepth 8000` for the two eight-lane functions and gives no hint which
   obligation it could not close when it fails (on the malformed `rollingVar` it left a goal mentioning
   `sorry`).

## The Python binding (`py/`)

`py/build.sh` runs `pygen`, which writes `tenon_kernels.c` (the emitted C of 15 proved kernels plus three
hand-written helper functions about the floating-point environment), `tenon_kernels.json` and
`tenon_req_tests.json`, and compiles `libtenon_kernels.so` with `-O2 -std=c11 -ffp-contract=off
-fno-fast-math` (`MARCH=native` adds `-march=native`). `py/tenon_kernels.py` exposes `prefix_sum`,
`rolling_sum`, `lower_bound`, `lower_bound_branchy`, `argmax` (int64) and `ewma`, `sum8`, `dot`,
`rolling_mean`, `rolling_var`, `rolling_std` (float64). Arrays are passed as the address of the NumPy
buffer and its length: **no copy in either direction**.

### The entry checks, and where each comes from

| | Check | Derived from | Cost |
|---|---|---|---|
| E1 | `numpy.ndarray`, dtype native `int64` or `float64` as the parameter says, 1-D, C-contiguous, aligned; writeable if `inout` | `Fn.params` (exported to JSON by `pygen`) | O(1), 0.8 µs |
| E2 | all elements of an **integer** array inside the parameter's element range | `Fn.params` | O(n): `min` and `max`. **Skipped when the range is all of int64; never needed for a float array** |
| E3 | integer arguments are integers in range; a float argument is a float (or an integer that converts exactly) | `Fn.params` | O(1) |
| E4 | the requirement, e.g. `len(x) == len(out) && len(x) <= 10000000` | **`Fn.req`, translated by `pygen` to a Python expression** (`req_py` in the JSON) | O(1), 0.24 µs |
| E5 | an `inout` array shares no memory with another array argument | the calling convention (`restrict`); the top-level instance of `exclusive` | O(1), 0.44 µs |
| E6 | float kernels: rounding to nearest, FTZ and DAZ off (`tn_fpenv_ok`) | item 21 above; **hand-written C** | O(1), 0.33 µs |

**Nothing is retyped by hand any more.** In emit4 the precondition was a `Prop` and lived a second
time in a Python table (`PRE`); that table is gone. `pygen` prints, for each kernel:

```
tn_prefix_sum: requires len(x) == len(out) && len(x) <= 1000000
tn_prefix_sum_10m: requires len(x) == len(out) && len(x) <= 10000000
tn_prefix_sum_w: requires len(x) == len(out) && len(x) <= 10000000
tn_lower_bound: requires always
tn_lower_bound_branchy: requires always
tn_rolling_sum: requires len(x) == len(out) && len(x) <= 10000000
tn_rolling_sum_exact: requires len(x) == len(out) && len(x) <= 10000000
tn_rolling_sum_w: requires len(x) == len(out) && len(x) <= 10000000
tn_argmax: requires always
tn_ewma: requires len(x) == len(out)
tn_sum8: requires 1 <= len(out)
tn_dot: requires len(x) == len(y) && 1 <= len(out)
tn_rolling_mean: requires len(x) == len(out)
tn_rolling_var: requires len(x) == len(out)
tn_rolling_std: requires len(x) == len(out)
```

and the JSON carries e.g. `"req_py": "((n[0] == n[1]) and (n[0] <= (10000000)))"`, which the binding
turns into `lambda v, n: ...` (`v[i]`: value of integer argument i, `n[i]`: length of array argument
i). **Python rather than C** because `evalCT` computes in unbounded integers: a C function would need
overflow-checked arithmetic to mean the same thing, Python integers are unbounded and the translation
is one line per constructor. The translation is itself tested against the kernel: `pygen` evaluates
Tenon's own `evalC f.req` on 48 argument shapes per kernel (lengths 0, 1, 2, 7, 8, 9 and every literal
of the condition ± 1, equal and unequal) and the Python test compares (720 shapes, 533 true, 187
false, all equal).

What is still hand-written in the binding, exactly: (i) the generic checks E1, E3, E5, which
interpret the exported types (30 lines, `check_array`, `check_int`, `check_float`, the
`may_share_memory` loop); (ii) E6 and the contraction probe, hand-written C in `PyGen.helpersC`;
(iii) the public wrappers, which choose a kernel and allocate the result. None of them restates a
fact about a particular kernel.

### Outputs that need no entry scan (implemented)

`hasAll` is about the arguments as passed, so an `inout` integer slice declared ±10^15 must already
hold values in ±10^15 before the call (finding H1 of emit4): the binding had to scan the caller's
output buffer or zero-fill a fresh one. Two kinds of output need neither, and the binding now uses
them:
- **float outputs**: every double has type `f64`; `np.empty` is a legal argument;
- **integer outputs declared with the full int64 range**: `prefixSumW` and `rollingSumW` are the
  kernels of emit4 with `out: inout slice(-2^63, 2^63-1)`; body, invariant and one-line proof are
  unchanged. `prefix_sum` and `rolling_sum` use them by default (`wide=True`, `kernel="wide"`).

`needs_scan(p)` decides it from the exported type. Effect on 10^7 elements (below): 39.7 ms → 26.8 ms
for a call with a caller-supplied `out`, 82.6 ms → 44.1 ms when the binding allocates the result.

What the binding does not and cannot check: that another thread does not write the buffers during
the call (ctypes releases the GIL), and that the shared library is the one generated from the proved
terms and compiled with the right flags (the import probe catches contraction only).

## Tests of the binding against NumPy

`cd py && python3 test_tenon_kernels.py` (`py/RESULT.txt`): **27 tests, all pass.** The 15 integer tests
are those of emit4 plus one for the scan-free outputs. The float results:

```
no scan: outputs declared with the full int64 range accept and overwrite arbitrary contents; no float parameter is ever scanned
refused: float out sharing memory with x; accepted: dot(x, x) (both by value)
refused: float32, int64, big-endian float64, list, 2-D, strided view, scalar, None, longdouble, complex, read-only out, misaligned
refused: float kernels while flush-to-zero / denormals-are-zero is set (E6); accepted again after reset
requirements: the generated Python checks of 15 kernels agree with Tenon's evalC on 720 argument shapes (533 true, 187 false)
refused (generated from req): unequal lengths, empty out for sum8/dot; refused: w outside 1..=10^6, non-integer w, non-float alpha; accepted: alpha = NaN (every double is an f64)
float zero copy: results are written into the caller's buffer; an output full of NaN is accepted and overwritten
dot: 140 inputs bitwise equal to the same lane order written in NumPy (products rounded, then added)
dot vs np.dot, 10^6 normal: bitwise equal: False; relative difference dot - np.dot: 5.52e-15; against fsum of rounded products: dot 9.54e-15, np.dot 4.02e-15
dot vs np.dot, 10^6 offset: bitwise equal: False; relative difference dot - np.dot: 2.52e-15; against fsum of rounded products: dot 2.31e-15, np.dot 2.10e-16
ewma: 1151 inputs (1292950 values, NaN, ±inf, ±0, subnormals included) bitwise equal to the plain Python loop
float kernels accept length 0 (sum8 and dot return 0.0)
rolling_mean: 148 inputs against the mean of each window computed from scratch; max relative difference: N(0,1) 2.05e-11 (|mean| floored at 1e-3), 1e8+N(0,1) 1.39e-14, small integers 0.0e+00 (exact), 600 binary orders of magnitude 2.02e-16 (relative to the largest |x| so far); 10^6 elements, w=1000: 2.74e-12
rolling_mean: an infinity in x makes every output after its window NaN (inf - inf), as documented
rolling_var / rolling_std: 222 inputs against np.var of each window; rolling_std == sqrt(rolling_var) bitwise. Max relative difference where the variance exceeds 1e-3: N(0,1) 2.06e-11, small integers 3.47e-15, 1e8+N(0,1) 1.63e+05 (the naive formula: absolute error 4.6e-14 of x^2); results clamped to 0 where the true variance is positive: N(0,1) 0, small integers 0, 1e8+N(0,1) 53259
rolling_var: NaN propagates through the clamp; a constant window of 0.1 gives values in [0, 5.6e-18], never negative
sum8: 168 inputs bitwise equal to the same lane order written in NumPy
sum8 vs np.sum, 10^6 normal: sum8 == np.sum bitwise: False; relative error against math.fsum: sum8 2.96e-14, np.sum 1.28e-15, left-to-right 3.62e-15
sum8 vs np.sum, 10^6 wide  : sum8 == np.sum bitwise: False; relative error against math.fsum: sum8 3.96e-15, np.sum 0.00e+00, left-to-right 1.29e-14
sum8 vs np.sum, 10^6 offset: sum8 == np.sum bitwise: False; relative error against math.fsum: sum8 1.56e-16, np.sum 0.00e+00, left-to-right 3.44e-14
```

Reading these honestly:
- `ewma`, `sum8`, `dot` are **bitwise equal** to the same order of operations written in Python/NumPy
  (NaN, ±inf, ±0, subnormals in the inputs; "any NaN equals any NaN").
- **`sum8` is not `np.sum` and is less accurate than `np.sum`** on these inputs: NumPy sums pairwise
  (error grows like log n), eight lanes are eight left-to-right sums (error grows like n/8). Against
  the correctly rounded sum (`math.fsum`) of 10^6 values, `sum8` was off by up to 3e-14 relative,
  `np.sum` by at most 1.3e-15; on one input (`N(0,1)`) plain left-to-right happened to be closer than
  `sum8`. The fixed order buys reproducibility, not accuracy.
- `dot` and `np.dot` (OpenBLAS, which uses FMA and its own order) differ by a few 1e-15 relative;
  neither is bitwise the other.
- `rolling_mean` agrees with a from-scratch windowed mean to 2e-11 relative on `N(0,1)` (drift of the
  running sum over 20,000 steps), exactly on small integers.
- `rolling_var`: 2e-11 on `N(0,1)`; **useless on `1e8 + N(0,1)`** (relative error 1.6e5, 53,259
  window results clamped to 0 although the true variance is about 1). That is the naive formula, as
  stated; the clamp keeps it non-negative, not right.

These tests have no deliberate-breakage self-test (the differential test has).

## Benchmark (`bench/`)

Method. C: each implementation is its own translation unit (no LTO), called through a volatile
function pointer; 200 ms warm-up, then 15 timed runs of at least 100 ms; minimum and median, ns per
element; `taskset -c 12`; one link order (emit4 measured link order effects of a few percent; I did not
repeat that). Generated and hand-written code are compiled with the same strict flags
(`-std=c11 -ffp-contract=off -fno-fast-math`), at `-O2` and at `-O2 -march=native`; the "fast-math"
baseline is `bench/naive.c` compiled with `-ffast-math` instead. Every line carries a checksum of the
result bits. N = 10^7 doubles (80 MB per array: bound by memory) as asked, and N = 4096 (in L1: bound
by computation). Python: 4 warm-up calls, 21 timed, BLAS threads = 1.

The run took 11 min 25 s. `mpstat` just before it showed core 12 at 100 % idle and the other cores of
8-15 between 38 % and 98 % idle (other users); the memory-bound numbers (N = 10^7) may carry some of
that. Within one binary, generated and hand-written code always printed the **same checksum**, in all
four builds: the same bits from clang and gcc, with and without `-march=native`.

### (i) Generated against hand-written C, median ns per element

N = 10^7 doubles:

| Kernel | Implementation | clang -O2 | clang -O2 -march=native | gcc -O2 | gcc -O2 -march=native |
|---|---|---|---|---|---|
| `ewma` | generated | 3.197 | 3.210 | 3.202 | 3.215 |
| | hand-written | 3.197 | 3.212 | 3.199 | 3.216 |
| `sum8` | generated | 0.707 | 0.700 | 0.678 | 0.650 |
| | hand-written (`a[k] += x[i+k]`) | 0.734 | 0.710 | 0.736 | 0.650 |
| `dot` | generated | 1.175 | 1.194 | 1.118 | 1.118 |
| | hand-written | 1.222 | 1.236 | 1.212 | 1.116 |
| `rolling_mean`, w = 20 | generated | 5.486 | 5.455 | 5.482 | 5.475 |
| | hand-written | 5.486 | 5.452 | 5.483 | 5.474 |
| `rolling_var`, w = 20 | generated (no hand-written partner) | 10.900 | 10.887 | 10.900 | 10.918 |
| `rolling_std`, w = 20 | generated | 16.376 | 16.371 | 16.325 | 16.342 |

N = 4096 (in L1):

| Kernel | Implementation | clang -O2 | clang -O2 -march=native | gcc -O2 | gcc -O2 -march=native |
|---|---|---|---|---|---|
| `ewma` | generated / hand-written | 3.090 / 3.090 | 3.105 / 3.105 | 3.090 / 3.090 | 3.100 / 3.100 |
| `sum8` | generated | 0.243 | 0.243 | 0.195 | 0.148 |
| | hand-written | 0.247 | 0.244 | 0.487 | 0.148 |
| `dot` | generated | 0.492 | 0.489 | 0.430 | 0.255 |
| | hand-written | 0.542 | 0.550 | 0.605 | 0.256 |
| `rolling_mean` | generated / hand-written | 5.457 / 5.457 | 5.420 / 5.412 | 5.450 / 5.449 | 5.443 / 5.442 |

- **Generated equals hand-written** for `ewma` and `rolling_mean` (within 0.2 %), and is equal or
  faster for `sum8` and `dot`. The one large difference, gcc `-O2` at N = 4096 (`sum8` 0.195 against
  0.487, `dot` 0.430 against 0.605), is the hand-written `double a[8]` with an inner loop over `k`:
  gcc at `-O2` keeps the array in memory and uses one packed addition where the generated eight scalar
  variables get four (assembly counts below). With `-march=native` gcc compiles both to the same code.
- `ewma`, `rolling_mean`, `rolling_var`, `rolling_std` are **serial recurrences**: 3.1 ns per element
  for `ewma` is the latency of multiply + add + the dependency through `prev` (about 7 cycles at
  2.3 GHz), 5.5 ns for the rolling mean is dominated by the division, 16.3 ns by division and `sqrt`.
  Nothing can vectorise them without changing the order of operations, which Tenon fixes, and
  `-march=native` changes nothing. This is the price of the fixed order for these kernels and no
  compiler flag recovers it.

### (ii) Do the eight lanes become vector instructions?

**With gcc: yes, completely.** `gcc -O2` (SSE2): the loop of `sum8` is four `addpd` on `xmm`
registers, two lanes each; `gcc -O2 -march=native` (AVX2): **two `vaddpd` on `ymm` registers, four
lanes each**, and `dot` is two `vmulpd` and two `vaddpd` on `ymm`, no FMA:

```
gcc -O2 -march=native, gen_sum8                 gcc -O2 -march=native, gen_dot
.L3:                                            .L3:
  vaddpd  (%rax), %ymm2, %ymm2                    vmovupd  (%rdx,%rax), %ymm6
  vaddpd  32(%rax), %ymm1, %ymm1                  vmulpd  (%rdi,%rax), %ymm6, %ymm0
  addq  $64, %rax                                 vmovupd  32(%rdx,%rax), %ymm7
  cmpq  %rcx, %rax                                vaddpd  %ymm0, %ymm3, %ymm3
  jne  .L3                                        vmulpd  32(%rdi,%rax), %ymm7, %ymm0
                                                  addq  $64, %rax
                                                  vaddpd  %ymm0, %ymm2, %ymm2
                                                  cmpq  %rax, %r9
                                                  jne  .L3
```

**With clang 21: only partly, and not better with `-march=native`.** Its SLP vectoriser pairs lanes
1-2, 3-4 (through a shuffle) and 5-6 into three `addpd` and leaves lanes 0 and 7 scalar (three
packed and two scalar additions per eight elements; 128-bit even with AVX2 available). The whole
functions are in `bench/RESULT.txt`. Instruction counts of the whole function (loop, tail, combination):

```
gcc-O2           gen_sum8   instructions=68  packed_pd=4  (ymm=0) scalar_sd=10  fma=0
gcc-O2           hand_sum8  instructions=79  packed_pd=1  (ymm=0) scalar_sd=10  fma=0
gcc-O2-native    gen_sum8   instructions=59  packed_pd=2  (ymm=2) scalar_sd=10  fma=0
gcc-O2-native    gen_dot    instructions=54  packed_pd=4  (ymm=4) scalar_sd=9   fma=0
clang-O2         gen_sum8   instructions=63  packed_pd=6  (ymm=0) scalar_sd=10  fma=0
clang-O2-native  gen_sum8   instructions=90  packed_pd=12 (ymm=0) scalar_sd=14  fma=0
clang-O2-native  gen_dot    instructions=86  packed_pd=9  (ymm=0) scalar_sd=19  fma=0
```

`fma=0` in every strict build, also with `-march=native`: `-ffp-contract=off` holds. So the claim of
`Sum8.lean`, "the eight sums can be computed with vector instructions without the compiler having to
reorder anything", is true and gcc does it with plain `-O2`; clang needs help it did not get from this
C (eight scalar variables). An emitter that printed vector-extension types
(`__attribute__((vector_size(32)))`) for a recognised lane pattern would fix clang; I did not do it.

### (iii) `sum8` / `dot` against a left-to-right loop, strict and `-ffast-math`

Median ns per element; the last column says whether the result bits are those of the strict
left-to-right loop.

| N | Implementation | clang -O2 | clang native | gcc -O2 | gcc native | result |
|---|---|---|---|---|---|---|
| 10^7 | `sum8` generated (strict flags) | 0.707 | 0.700 | 0.678 | 0.650 | one value, all four builds |
| | left-to-right, strict flags | 1.255 | 1.271 | 1.264 | 1.264 | one value, all four builds |
| | left-to-right, `-ffast-math` | 0.682 | 0.652 | 1.266 | 1.266 | **three different values** in four builds |
| 4096 | `sum8` generated | 0.243 | 0.243 | 0.195 | 0.148 | |
| | left-to-right, strict | 1.158 | 1.158 | 1.160 | 1.160 | |
| | left-to-right, `-ffast-math` | 0.291 | **0.099** | 1.160 | 1.161 | |
| 10^7 | `dot` generated | 1.175 | 1.194 | 1.118 | 1.118 | one value |
| | left-to-right, strict | 1.434 | 1.441 | 1.435 | 1.454 | one value |
| | left-to-right, `-ffast-math` | 1.101 | 1.104 | 1.435 | 2.079 | **four different values** |
| 4096 | `dot` generated | 0.492 | 0.489 | 0.430 | 0.255 | |
| | left-to-right, strict | 1.159 | 1.159 | 1.161 | 1.161 | |
| | left-to-right, `-ffast-math` | 0.382 | **0.249** | 1.161 | 1.933 | |

- **Against the strict left-to-right loop the fixed eight lanes win everywhere**: in cache `sum8` is
  4.8 to 7.8 times faster and `dot` 2.4 to 4.6 times (1.16 ns is one addition latency per element;
  eight lanes run eight chains); at 10^7, where memory bandwidth takes over, 1.8 to 1.9 times
  (`sum8`) and 1.2 to 1.3 times (`dot`).
- **Against `-ffast-math` the picture depends on the compiler.** gcc at `-O2 -ffast-math` does not
  vectorise the reduction at all (its `-O2` cost model; same time and even the same bits as strict),
  and with `-march=native -ffast-math` its `dot` gets *slower* (1.93 ns: it fuses the multiply into
  the single dependency chain, an FMA has more latency than an add). There the generated code is 2.7
  to 7.8 times faster in cache than the fast-math baseline. clang does vectorise: at `-O2` it is level with `sum8`
  (0.291 against 0.243 in cache, 0.682 against 0.707 at 10^7), and **with `-march=native` it wins:
  0.099 ns against 0.243 ns per element in cache (2.5 times faster than the generated `sum8`), 0.249
  against 0.489 for `dot` (2.0 times)**: four 256-bit accumulators, 16 lanes, and FMA for `dot`.
  At 10^7 elements the same code is 7 % faster for `sum8` (0.652 against 0.700) and 8 % for `dot`.
- **Where the fixed order loses**, then: (a) to clang `-march=native -ffast-math` in cache, by 2 to
  2.5 times, because the order fixes the number of lanes at eight and forbids FMA, and because clang
  does not turn the eight scalar lanes into `ymm` code (gcc does: with gcc's code, 0.148 ns, the loss
  would be 1.5 times); (b) in accuracy to pairwise summation (previous section); (c) for every serial
  kernel (`ewma`, rolling statistics), where a reordering compiler could not help either, but a
  different algorithm could. What it buys is in the last column: the fast-math results differ between
  compilers and between `-O2` and `-march=native` in the last digits, the `sum8`/`dot` results are one
  value.

### (iv) Float `sel` and `selLe`: is the code branch-free?

Three functions in the four C forms (`Options.selForm`): `rolling_var` (one `selLe` behind a serial
recurrence), `clip` (two nested `selLe` per element: `x ≤ lo ? lo : (hi ≤ x ? hi : x)`; unproved) and
`fwhere` (float `sel` on an integer condition with a load in each arm; unproved), plus a hand-written
`clip` with `?:`. Conditional jumps per function beyond loop control, and what replaces them:

| | clang -O2 / native | gcc -O2 / native |
|---|---|---|
| `selLe` in `rolling_var`, all four forms | no branch: `cmplesd` + `andnpd` (the same with `-march=native`, VEX-encoded) | eager, plain, lazy: **a branch** (`comisd`, `jb`) at `-O2`, `vblendvpd` with `-march=native`; mask: no branch (integer mask) |
| `selLe` in `clip`, eager / plain | **vectorised**: `cmplepd` + `andpd`/`andnpd`/`orpd` on `xmm`, `vblendvpd` on `ymm` with `-march=native` | no branch, scalar: `cmplesd` + and/andn (SSE2) or `vblendvpd` (native) |
| `clip`, lazy `?:` and the hand-written `?:` | vectorised, identical code to eager | **one branch per element** (the outer test), the inner select branch-free |
| `clip`, mask | vectorised, identical | no branch (`comisd` + integer `cmov`), 41 instructions against 21 |
| `sel` in `fwhere`, eager / plain | **vectorised** (integer compare and `pand`/`pandn`/`por` at `-O2`, `vblendvpd` with `-march=native`) | **a branch per element** |
| `fwhere`, lazy | **a branch per element** at `-O2`; vectorised (masked loads) with `-march=native` | a branch per element |
| `fwhere`, mask | vectorised like eager | **no branch** (integer `cmov`) |

Median ns per element on unpredictable data (N = 10^7; `clip` bounds ±0.5 on uniform [−1, 1), `fwhere`
condition random bits):

| | clang -O2 | clang native | gcc -O2 | gcc native |
|---|---|---|---|---|
| `clip`, eager (default) | 1.483 | 1.401 | 2.513 | 1.791 |
| `clip`, lazy `?:` | 1.483 | 1.401 | 3.836 | 3.750 |
| `clip`, mask | 1.482 | 1.400 | 3.099 | 3.101 |
| `clip`, hand-written `?:` | 1.485 | 1.400 | 3.838 | 3.760 |
| `fwhere`, eager (default) | 2.452 | 2.457 | 5.460 | 5.471 |
| `fwhere`, lazy | 5.246 | 5.009 | 5.275 | 5.435 |
| `fwhere`, mask | 2.450 | 2.458 | 2.692 | 2.692 |
| `rolling_var`, eager / lazy / mask | 10.90 / 10.90 / 10.89 | 10.89 / 10.88 / 10.89 | 10.90 / 10.90 / 11.00 | 10.92 / 10.92 / 11.02 |

(At N = 4096 the same loop over the same 4096 values is repeated and the branch predictor learns
them: the branching forms look fast there, e.g. gcc `clip` lazy 1.26 ns against eager 2.32 ns. Those
numbers are in `bench/RESULT.txt` and say nothing about real data.)

Answers:
1. **clang**: the default form (`tn_fsel`, operands evaluated first, with the unpredictable hint) is
   branch-free in all three functions and vectorised in `clip`; for `clip` clang produces the same
   vector code from any spelling, including the hand-written one. The eager form matters where an arm
   is a load (`fwhere`): the lazy `?:` is a branch at `-O2` and 2.1 times slower.
2. **gcc**: `selLe` on values already in registers is branch-free in the eager form (1.5 times faster
   than the hand-written `?:` on `clip`, 2.1 times with `-march=native`), but a float `sel` on an
   integer condition with loads in the arms is compiled as a branch in every form except the bit mask
   (5.46 against 2.69 ns). In `rolling_var` at `-O2` gcc also branches (harmless there: the branch is
   almost never taken and the loop is bound by the division).
3. As for the integer `sel` in emit4, no single C spelling is branch-free with both compilers
   everywhere: the default is right for clang and for gcc's `selLe`; `selForm := .mask` is the one
   that is branch-free with gcc when an arm is a load. The emitter keeps one global option; a
   per-compiler choice (`#if defined(__clang__)` inside `tn_fsel`, mask for gcc) would take the best
   of both and I did not implement it.

### (v) Through the Python binding against NumPy, 10^7 elements, median ms

Library built with clang `-O2` (first two columns of numbers) and with gcc `-O2 -march=native`:

| | NumPy | binding, all entry checks (clang -O2) | kernel alone, ctypes (clang -O2) | binding, all checks (gcc native) |
|---|---|---|---|---|
| sum: `np.sum(x)` / `sum8(x)` | 6.25 | 6.83 | 6.79 | 6.36 |
| left-to-right in NumPy: `np.add.accumulate(x)[-1]` | 53.4 | | | |
| dot: `np.dot(x, y)` (OpenBLAS, 1 thread) / `dot(x, y)` | 10.82 | 11.59 | 11.57 | 10.89 |
| `ewma(x, 0.05, out)` (NumPy has none) | | 31.99 | 31.91 | |
| `ewma(x, 0.05)`, result allocated with `np.empty` | | 50.35 | | |
| rolling mean, w = 20: cumsum difference / `rolling_mean(x, w, out)` | 145.2 | 54.80 | 54.72 | 54.5 |
| rolling mean, w = 20: `sliding_window_view(x, w).mean(axis=1)` | 386.2 | | | |
| rolling variance, w = 20: two cumsums, same formula / `rolling_var(x, w, out)` | 468.0 | 108.8 | 108.9 | |
| `rolling_std(x, w, out)` | | 163.2 | | |

- **`sum8` and `dot` are level with NumPy at this size and not faster**: 6.8 against 6.2 ms (9 %
  slower) and 11.6 against 10.8 ms (7 % slower) with the clang library; with the gcc `-march=native`
  library 6.36 against 6.28 and 10.89 against 10.83 (1 % slower). Everything here is memory-bound;
  NumPy's sum is pairwise and SIMD, OpenBLAS's dot uses FMA. In cache (previous tables) the C kernels
  run at 0.15 to 0.25 ns per element, but there the wrapper dominates (below).
- **The rolling kernels are 2.6 times (mean) and 4.3 times (variance) faster than the NumPy
  formulations with cumulative sums**, which make several passes and temporaries, and 7 times faster
  than the from-scratch windowed mean. `ewma` has no NumPy counterpart; a Python loop over 10^7
  elements takes seconds.
- For float kernels **the entry checks cost nothing measurable at this size** (31.99 against 31.91
  ms): no scan. Allocating the result costs 18 ms of page faults (`np.empty`, 80 MB).

Integer prefix sum, 10^7 `int64`, what the scan-free output saves:

| Call | median ms |
|---|---|
| `np.cumsum(xi, out=oi)` | 28.4 |
| `prefix_sum(xi, oi, wide=False)`: out declared ±10^16, scans `x` **and** `out` (emit4) | 39.7 |
| `prefix_sum(xi, oi)`: out declared int64, scans `x` only | **26.8** |
| `prefix_sum(xi, oi, check=False)`: no scan | 13.7 |
| kernel alone | 13.7 |
| the scan of `x` itself (`min`, `max`) | 12.9 |
| `prefix_sum(xi)`: out declared int64, `np.empty` | 44.1 |
| `prefix_sum(xi, wide=False)`: out declared ±10^16, `np.zeros` | 82.6 |

Declaring the output with the full range removes one of the two scans (39.7 → 26.8 ms; now faster
than `np.cumsum(out=)`), and when the binding allocates the result it removes the zero-fill (82.6 →
44.1 ms). The remaining scan of the *input* is half of the call; only a caller who knows the range
(`check=False`) or an input type with the full range avoids it.

Fixed cost per call, median µs:

| Call | NumPy | binding, all checks | kernel alone (ctypes) |
|---|---|---|---|
| sum, 8 / 1024 / 10^5 elements | 3.2 / 3.8 / 47.4 | 10.1 / 10.6 / 49.6 | 1.0 / 1.3 / 36.7 |
| dot, 8 / 1024 / 10^5 | 0.9 / 1.1 / 52.2 | 13.9 / 15.0 / 88.7 | 1.3 / 1.8 / 71.0 |
| `ewma`, 8 / 1024 / 10^5 | | 10.2 / 13.6 / 324.9 | 1.2 / 4.4 / 312.0 |

The wrapper costs about 9 µs for `sum8` and 12 µs for `dot` (argument checks in Python, plus a
one-element NumPy array for the result): **on small arrays the binding is 3 to 15 times slower than
NumPy**, all of it interpreter overhead; the individual checks are 0.8 µs (E1), 0.25 µs (E4, the
generated requirement), 0.44 µs (E5), 0.31 µs (E6). At 10^5 elements `sum8`'s kernel is faster than
`np.sum` (36.7 against 47.4 µs) and the binding about equal; `dot` (clang library, no `ymm`, no FMA)
is slower than OpenBLAS (71 against 52 µs).

## Limitations

- The emitter and the binding are not proved; no formal C semantics is involved. In-place `inout`
  rests on `exclusive` plus `restrict` and an argument that is proved nowhere.
- **The float guarantee is "the C computes what Tenon defines, bit for bit except NaN sign and
  payload", and it holds only with the compiler flags above, on x86-64, in a thread with the default
  floating-point environment.** Other architectures (AArch64 has FMA in the base instruction set, so
  contraction is the default danger there too) were not tested.
- No functional postconditions on any example, and for floats nothing about values can be proved.
- `rolling_mean` and `rolling_var` are incremental and drift; `rolling_var` is the naive formula.
  They are examples of the pipeline, not recommended statistics.
- `sum8`/`dot` return their result through `out[0]`; the binding allocates a one-element array per
  call. The wrapper costs about 10 µs per call; small calls are slower than NumPy.
- Integer kernels are still limited to 10^7 elements and elements within ±10^9, `w ≤ 10^6`.
- A modified by-value slice is copied to the heap; the function aborts if `malloc` fails.
- `TENON_UNPREDICTABLE`/`TENON_FUNPREDICTABLE` are clang builtins; whether a select becomes a branch is up
  to the compiler (measured for clang 21 and gcc 13 only).
- A `loopB`/`loopE` does not terminate on inputs outside the guarantee where Tenon would be stuck.
- The binding handles only the parameter shapes its kernels use (slices and by-value scalars).
- The differential test compares on inputs of at most 24 elements per slice (40 for the hand-written
  programs); large inputs are exercised only through the Python tests and the benchmark checksums.
- **clang 21.1.8 miscompiles some float comparisons on compile-time constants of magnitude ≥ 2^64**
  (`MISMATCH-401-148.md`). Run-time inputs are not affected; a Tenon float literal of that size could be.
  gcc 13 is not affected.
- Tested on one machine: Xeon E5-2650 v3, Linux 6.8, clang 21.1.8, gcc 13.3.0, glibc's `sqrt`.

## Findings about the kernel (reported, not worked around)

Reproducers: `KernelFindings.lean` (`lake build KernelFindings` prints the values). I found no case
where `prog_sound` is contradicted, and no mismatch between `evalFn` and the emitted C. G1, G2, F2, H1
(for integer slices), H2, H3, H4, H6 of emit4 are unchanged; H5 is half answered (`req` is data,
`post` and the result range are not). New:

- **K1. The reference semantics cannot see which NaN it has.** `Float.toBits` gives one pattern for
  all NaNs; the C produces several and they differ between `-O0` and `-O2` (constant folding gives
  `7ff8...`, the same expression at run time gives `fff8...`). "Bit for bit" is checkable for
  everything except NaN sign and payload.
- **K2. The per-operation table** as `#eval`s (−0, `sqrt(−0)`, `ofInt` at 2^53 ± 1 and ±2^63,
  comparisons with NaN): all as the C printed.
- **K3. `Float.ofInt` beyond 64 bits**: I expected a double rounding and did not find one (the
  standard counterexample 2^64 + 2^11 + 1 rounds correctly). Not reachable from Tenon anyway.
- **K4. Nothing can be proved about a float value.** `Float` is opaque: no theorem about `+` or `≤`,
  `decide` does not evaluate them, only `native_decide` (which trusts the compiler). The float
  obligations are index obligations, the invariants are `True`, and a postcondition like "out ≥ 0"
  cannot be proved.
- **Tenon. `loopE` evaluates its bound; the C does not** (item 12 above), with three stuck-bound
  reproducers.
- **K6. `req` is evaluated in unbounded integers and is not shape-checked**: `val` of an array and
  `len` of an integer silently read as 0 (`evalC (.eq (.val 0) (.lit 0)) [.farr [1.0, 2.0]] = true`).
  `pygen` reports such positions (`req_ill_shaped`; none in the 15 kernels).
- **K7. A float parameter has no range and `req` cannot mention float values**: `alpha = NaN` is a
  legal call of `ewma` and returns NaNs.
- **K8. Float comparison exists only as `≤`, in `fite` and `selLe`**; "max(v, 0)" has two spellings
  that differ on NaN and the term does not say which was meant.
- **K9. A float result costs an `inout` slice** (`out[0]`, `1 ≤ len(out)`); an `inout` float scalar
  works in Tenon and in the emitter and would be lighter.

## What in Tenon.lean and Surface.lean made code generation, proving or binding awkward, with a suggestion for each

Ordered by how much it cost here.

1. **Floats are opaque, so the float kernels are proved safe and nothing else (K4).** (proving) The
   most-wanted facts (the variance is ≥ 0 after the clamp; no NaN out for no NaN in; the result is
   within k ulp of the true sum) cannot be stated usefully. Suggestion: a small axiomatised interface
   instead of raw `Float` inside `evalF`: an abstract type with `add`, `le`, ... and axioms for the
   properties that hold of IEEE binary64 and are needed first (`selLe x y u v` is `u` or `v`;
   `x ≤ y ∨ ¬ x ≤ y`; `isFinite` closure under bounded operations; `0 ≤ sqrt x` for `0 ≤ x`), with
   Lean's `Float` as the model the tests run. Each axiom is then a named, testable assumption
   (floatcheck can test it on bit patterns), instead of one unnamed assumption "Lean's Float = C".
2. **NaN identity is invisible in the reference (K1).** (testing) Suggestion: either state in Tenon that
   values are doubles modulo NaN payload (and say so in the guarantee), or carry floats as `UInt64`
   bit patterns in `Val` with operations defined through `Float.ofBits`/`toBits` plus a canonical NaN;
   the emitter would then canonicalise NaNs on store (`x != x ? NAN : x`), which costs a compare per
   store but makes "bit for bit" literally true.
3. **The float environment and the compiler flags are outside the model (items 16, 21).** (code
   generation, binding) Suggestion: make them part of the deliverable rather than of a README: the
   emitter should emit a `static` self-test function per translation unit (the `muladd` probe, a
   reassociation probe, a subnormal probe) and a `#pragma`/`#error` block as now, and `req` should be
   able to carry "the caller is in the default environment" as a named assumption that bindings must
   discharge (the binding does it by hand in E6).
4. **`req` is not shape-checked and uses unbounded integers (K6).** (binding) Suggestion: a decidable
   `Cond.wf : List Ty → Cond → Bool` (every `val` an integer parameter, every `len` an array) required
   by `ProgOk`; and either keep `Int` and say that checks must be evaluated in big integers, or bound
   the literals and prove no intermediate exceeds 128 bits so that a C check function is exact.
5. **The surface syntax's keywords and example names leak into every importer** (Surface item 2;
   three rounds of renaming here). (proving, code generation) Suggestions: `scoped syntax` inside a
   namespace (`open Tenon.Surface in kfn ...`), or one entry keyword (`kfn`) with everything else parsed
   in its own syntax category only, so that importing `Surface` does not reserve `len`, `bound`,
   `loop`, `int`, `sel`, `call`; and put the examples in a namespace or a separate file. For the float
   select, names that carry the NaN behaviour (`max_keep_nan(v, 0.0)`, `clamp(v, lo, hi)`) on top of
   `sel(a <= b, t, e)`.
6. **A float result needs an output slice (K9).** (binding, performance) 10 µs of wrapper per `sum8`
   call. Suggestion: results of type `f64` (a second result register in the C ABI is free), or at
   least use `(.flt, true)` parameters, which the emitter already passes as `double *`.
7. **No float ranges, no float `req` (K7).** (binding) The binding cannot refuse NaN input because
   the kernel cannot require its absence. Suggestion: with item 1, `Ty.flt` could carry an optional
   "finite, within [lo, hi]" refinement checked at entry by a scan (as E2 for integers) and usable in
   proofs through the interface axioms.
8. **Only `≤` on floats, only as statement or select (K8).** (code generation) Suggestion: `flt a b`,
   `fle a b`, `feq a b` as integer expressions (0/1, false on NaN), which also gives `sel` on a float
   comparison and lets a count of "x[i] ≤ t" be written without a branch.
9. **`loopE`'s bound is evaluated by the semantics although it is proof-only (Tenon).** (code generation)
   The emitter must render it only to reject ill-shaped terms and then throw it away. Suggestion: keep
   it as is (it is sound) but say in `execS` that the bound is ghost, or make the stuck-on-stuck-bound
   case `none` only in `wpS` (an obligation) and not in `execS`, so that `evalFn` and the C agree on
   unchecked programs too.
10. **`Val` gained two constructors and every hand proof that matched on argument shapes broke.**
    (proving) 22 new impossible-case arms in `Legacy.lean`. Suggestion: none in the kernel; proofs
    should open arguments with `env_open` (as `kvc` does), never by `match`. `kvc` made this a
    non-issue for everything written after it.
11. **A core term with many nested scopes is unreadable and unwritable** (`rollingVar`: 12 levels,
    two build attempts lost to a parenthesis). (proving) Answered during this work: with `sel` in the
    surface syntax no float kernel in this directory needs a core term any more. Suggestion: move
    `Ewma.lean` and `Sum8.lean` to it as well and keep core terms for tests of the kernel only.
12. **`kvc` failure reporting and limits** (Surface item 9). Suggestion: on failure print the
    statement path of the open obligation (which loop, which statement), and raise `maxRecDepth`
    inside the macro.
13. Unchanged from emit4 and still felt: no `out` mode for integer slices (H1; worked around here by
    declaring the output with the full int64 range, which only works because nothing reads it back),
    `sel` cannot guard a load (H2), result ranges are constants (H5), G1/G2.

Things that made this easy and should be kept: `req` as data (the binding's hand-written table is
gone, and the translation could be tested against `evalC`); float operations that are never stuck
(nothing to check in the emitter, invariants `True`); `selLe` evaluating all four operands (the
emitted code is branch-free and vectorisable where the compiler wants, measured above); lengths
preserved by everything; `kvc`; the surface syntax for floats, which arrived while I was working and
immediately replaced two of three planned core terms.
