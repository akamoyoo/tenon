# Tenon

**Rust guarantees memory safety at compile time. Tenon, at compile time, guarantees memory safety and
also that a function can do exactly what its signature says, and nothing else.**

Tenon is a small compiled language for performance-critical computation kernels: parsers, fixed-capacity
data structures, numeric and statistical routines. A kernel is written in Tenon, checked, compiled to C,
and linked into a C++ or Python program. The check is a machine-verified proof, not a test.

Status: research prototype, not released. Working name. Read "What is not claimed" first if you intend
to rely on anything here.

## Three functions that Rust compiles and Tenon refuses

Each is a few lines, each has a slip that people make, and each fails only on some inputs. The Rust
sources are in `examples/rust/` and the behaviour quoted is what they did here (rustc 1.87, x86-64).

### 1. A rolling sum that reads before the window is full

```rust
fn rolling_sum(x: &[i64], w: usize, out: &mut [i64]) {
    let mut acc: i64 = 0;
    for i in 0..x.len() {
        acc = acc + x[i] - x[i - w];      // i < w on the first w rounds
        out[i] = acc;
    }
}
```

| | What happens |
|---|---|
| C++, same code | Compiles. Reads before the start of the array: undefined behaviour, usually a wrong number |
| Rust, debug build | Compiles. Panics at run time: `attempt to subtract with overflow` |
| Rust, release build | Compiles. Panics at run time: `index out of bounds: the len is 10 but the index is 18446744073709551613` |
| Tenon | Does not compile |

```
$ tenon check examples/rolling_sum_bad.tn
examples/rolling_sum_bad.tn:7: in `rolling_sum`: cannot show
    acc = acc + x[i] - x[i - w];
    needed: w <= i
```

### 2. A notional that overflows, silently in a release build

```rust
fn notional(px: &[i64], qty: &[i64]) -> i64 {       // sum of price * quantity, in ticks and lots
    let mut acc: i64 = 0;
    for i in 0..px.len() {
        acc = acc + px[i] * qty[i];
    }
    acc
}
```

With twelve fills of 10^9 lots at 10^9 ticks the true sum is 1.2 × 10^19, above the 64-bit range.

| | What happens |
|---|---|
| C++ | Compiles. Signed overflow: undefined behaviour |
| Rust, debug build | Compiles. Panics: `attempt to add with overflow` |
| Rust, release build | Compiles. **Prints `-6446744073709551616`**: no panic, a wrong number with the wrong sign |
| Tenon | Does not compile until the ranges of prices, quantities and the number of fills are stated |

```
$ tenon check examples/notional_bad.tn
examples/notional_bad.tn:7: in `notional`: cannot show that this value stays within 64 bits
    acc = acc + px[i] * qty[i];
```

The version that compiles (`examples/notional.tn`) says what the function is good for, in its signature:
prices up to 10^8 ticks, quantities up to ±10^6 lots, at most 100 fills, result within ±10^16. Anyone who
calls it with more must change the signature, and the proof is redone.

### 3. A mean of nothing

```rust
fn mean(x: &[i64]) -> i64 {
    let mut s: i64 = 0;
    for v in x { s += *v; }
    s / x.len() as i64
}
```

| | What happens on an empty slice |
|---|---|
| C++ | Compiles. Division by zero: undefined behaviour, in practice the process is killed |
| Rust, debug and release | Compiles. Panics: `attempt to divide by zero` |
| Tenon | Does not compile until `requires (1 <= len(x))` is in the signature |

```
$ tenon check examples/mean_bad.tn
examples/mean_bad.tn:8: in `mean`: cannot show
    result = s / len(x) - 1000000000;
    needed: 0 < len(x)
```

In all three, Rust keeps memory safe: it turns the fault into a panic, which in a trading system is still
an outage, or (case 2, release build) lets a wrong number through. Tenon moves all three to compile time.

## What a Tenon function looks like

`examples/rolling_sum.tn`, the corrected first example:

```
fn rolling_sum(x: slice(-1000000000, 1000000000), w: int(1, 1000000),
               out: inout slice(-9223372036854775807, 9223372036854775807)) -> int(0, 0)
  requires (len(x) == len(out) && len(x) <= 1000000)
{
  let acc: int(-2000000000000000, 2000000000000000) = 0;
  for i upto len(x) invariant (-2000000000 * i <= acc && acc <= 2000000000 * i) {
    if w <= i { acc = acc + x[i] - x[i - w]; } else { acc = acc + x[i]; }
    out[i] = acc;
  }
}
```

```
$ tenon check examples/rolling_sum.tn
examples/rolling_sum.tn: `rolling_sum`: proved

$ tenon emit examples/rolling_sum.tn
int64_t rolling_sum(const int64_t *restrict x, int64_t x_len, int64_t w, int64_t *restrict out, int64_t out_len)
{
    int64_t result = 0;
    int64_t acc = 0;
    for (int64_t i = 0, i_end = x_len; i < i_end; i++) {
        if (w <= i) {
            acc = acc + x[i] - x[i - w];
        } else {
            acc = acc + x[i];
        }
        out[i] = acc;
    }
    return result;
}
```

What the author wrote beyond the code: the ranges in the types, the `requires` clause, and one loop
invariant. What was proved from that, for every input the signature admits: no index is out of range, no
arithmetic leaves 64 bits or a declared range, the loop terminates, `x` is not modified and `out` keeps
its length. The C that comes out contains no check of any of this, and is the C one would write by hand.

"Proved" means proved: `tenon check` writes one theorem per function and has Lean, a proof checker,
verify it. The rules that turn a function into the facts to be proved are themselves proved sound in
Lean (`Tenon.lean`). There is no "trust me" switch in the language.

## The problem this addresses

In code where performance and reliability both matter, memory safety is not the end of it:

| Problem | What languages give you today |
|---|---|
| Crashes in production | Out-of-range indices, overflow and division by zero are found at run time |
| Paying at run time for safety | Checks stay in hot loops unless removed by hand |
| Hidden costs on the hot path | A signature does not say whether a function allocates, locks or blocks |
| Results that cannot be reproduced | Backtest and production differ through floating point, optimisation, scheduling |
| Review cannot keep up | A signature does not bound the implementation, so the implementation must be read |

The five have one root: a signature is not a complete statement of what a function does.

## The guarantees

For a program that passes the check (`ProgOk`), called with arguments of the declared types that satisfy
`requires`:

| Guarantee | Meaning | How it holds |
|---|---|---|
| No run-time failure | No index out of range, no value outside 64 bits or outside its declared range, no division outside its domain | Theorem `prog_sound`, proved in Lean 4 |
| Bounded resources | Every function terminates; no allocation; no recursion; stack use is static | By construction: the semantics is a total function defined without fuel, and Lean accepts it |
| Reproducible results | The result is a function of the arguments | By construction: the semantics is a function. For floats see the qualification below |
| Unchanged means unchanged | A variable a statement cannot assign has the same value afterwards; no array changes length | Theorems `exec_frame`, `exec_lens` |

Authority confinement (a function reaches the outside world only through capability parameters) is the
design's fifth guarantee. It holds trivially today because the language has no way to reach the outside
world at all: there is no I/O, no clock, no allocation, no global state. Capabilities are not implemented.

## How it compares

| | What it does better than Tenon | What Tenon adds |
|---|---|---|
| SPARK (Ada) | Proves absence of run-time errors too, with decades of industrial use, a far richer language, native code | Its verification chain is tested, not mechanically proved, and it publishes a list of known soundness issues per release; effect contracts are optional and about global state, with ambient calls legal; storage exhaustion and bit-reproducibility are outside its proof |
| Wuffs | Ships in Chrome; same idea of a safe kernel language that emits C | A mechanised soundness proof; kernel-checked obligations per program |
| Rust with Verus | Ecosystem; a mature prover | Rust has ambient authority, so confinement can only be checked, not constructed |
| C++ with care | Everything else | The guarantees |

On "no run-time failure" alone, Tenon is level with SPARK, not ahead of it. The difference is where the
trust lies: every obligation of every program is checked by the Lean kernel, and the rules that generate
the obligations are themselves proved sound.

## Measured

All on one machine (x86-64, clang 21.1.8 and gcc 13, `-O2`), numbers from runs in this tree; see
`docs/EMITTER.md` for method and full tables.

- **Generated code against hand-written C**: equal on prefix sum, rolling sum, exponentially weighted
  mean, rolling mean (for example 3.1 ns per element for the weighted mean, both).
- **Binary search**, ns per independent call, clang: generated branch-free 5.1 / 18.8 / 128.5 at lengths
  8 / 1024 / 10^6, against `std::lower_bound` 11.6 / 28.9 / 199.1. The branch-free form is possible
  because both arms of a select are proved in range. On chained calls (a latency measure) the advantage
  is smaller or absent.
- **Fixed-order dot product** (eight lanes, written in Tenon), ns per element over four compiler
  configurations: in cache (4,096 elements) 0.25 to 0.49 against 1.16 for a strict left-to-right loop;
  out of cache (10^7 elements) 1.12 to 1.20 against 1.44, where memory dominates. A left-to-right loop
  under `-ffast-math` ranges from 0.25 to 1.93 in cache depending on the compiler and flags, and its
  result differs from build to build, which is what the fixed order exists to prevent.
- **From Python** (ctypes, NumPy arrays without copying, 10^7 elements): rolling mean 2.6 times and
  rolling variance 4.3 times faster than cumulative-sum formulations in NumPy; sum and dot product about
  10 % slower than `np.sum` and `np.dot`; calls on small arrays 3 to 15 times slower than NumPy because
  of about 10 µs of wrapper per call.
- **Differential test** of the generated C against the Lean semantics (last full run in this tree,
  `difftest/RESULT.txt`): no mismatch over 4,075 programs and 81,713 inputs in seven builds, 437,849
  doubles compared bit for bit. A run with other seeds (401, 402) found one mismatch in the clang
  sanitizer build, caused by an LLVM bug (below): rerun with new seeds before trusting a change.

## What is not claimed

- **The C generator is not proved.** It is tested differentially against the Lean semantics. A wrong
  generator would break every guarantee.
- **Passing an `inout` argument as a pointer is only partly proved equivalent to copy-in copy-out.** The
  semantics is copy-in copy-out; the generated C passes pointers. Proved: under the rule that an `inout`
  variable occurs once among a call's arguments and is not the destination, the write-back is a
  simultaneous assignment (`writeBack_hit`, `writeBack_dst`, `writeBack_get`): each `inout` variable
  receives exactly the callee's final value, the destination keeps the result, nothing else changes.
  Not proved: that the callee, running on the caller's storage instead of on copies, computes the same
  thing. That follows from its parameters being distinct storage, which the same rule ensures, but there
  is no machine-checked model of pointers here.
- **The C compiler is trusted, and one bug in it is known.** clang/LLVM 21.1.8 folds a comparison on
  compile-time constant doubles of magnitude at least 2^64 to the wrong value (upstream issue 167627,
  fixed for LLVM 22). Inputs that arrive at run time are not affected. gcc 13 is not affected. See
  `docs/MISMATCH-401-148.md`.
- **Floats: only safety is proved.** Nothing is proved about float values: not accuracy, not finiteness,
  not that a variance is non-negative. The naive rolling variance in the examples is badly wrong on data
  with a large offset, and says so. The fixed-order sum is less accurate than NumPy's pairwise sum.
- **Float reproducibility is bit for bit except for NaN sign and payload**, and only with
  `-ffp-contract=off` and no fast-math option on the compiler command line (gcc ignores the pragma and
  contracts by default). That Lean's `Float` operations are the IEEE-754 operations the C performs is
  tested (every non-NaN result of fourteen operations on 31,971 input pairs agreed), not proved.
- **`ensures` does not exist in the surface syntax.** What is proved is safety, not that `prefix_sum`
  computes prefix sums.
- **The language is small.** No structs, no enums, no capabilities, no components, no concurrency, no
  strings. Function results are integers; a float result goes through an `inout` slice.
- **Lean is behind the `tenon` command.** A `.tn` file contains only Tenon, but checking it runs Lean,
  which must be installed, and takes seconds per file. Messages are translated for obligations that could
  not be proved; a syntax error is reported in Lean's words. Longer examples in this tree are still
  written inside Lean files (`SurfaceExamples.lean`, `Examples.lean`).
- **Entry checks are the caller's duty.** The guarantee starts at "arguments of the declared types that
  satisfy `requires`". The Python binding generates and performs these checks; a C++ caller must.
- Nobody but the author has used it.

## Layout

```
tenon             the command: `tenon check file.tn`, `tenon emit file.tn`
examples/         the examples above, correct and incorrect versions, and the Rust counterparts
Tenon.lean        the language: values, types, syntax, semantics, obligations, soundness proofs, tactics
Surface.lean      the surface syntax (Lean macros)
SurfaceExamples.lean   ten functions written in it, each proved in one line
Examples.lean     more proved kernels: rolling mean, rolling variance, dot product, binary searches
Ewma.lean, Sum8.lean   two kernels as core terms
Emit.lean         the C generator
difftest/         random programs and inputs, Lean semantics against compiled C
floatcheck/       Lean Float against C, operation by operation
py/               Python binding with generated entry checks, tests against NumPy
bench/            benchmarks
docs/REFERENCE.md the language in a few pages
docs/EMITTER.md   the generator, the tests and the measurements in detail
```

## Build and run

Needs Lean 4.35.0 (elan), clang and gcc, Python with NumPy for the binding.

```
lake build                                              # every proof; fails if any is missing
./tenon check examples/rolling_sum.tn                   # check one source file
./tenon emit examples/rolling_sum.tn > rolling_sum.c    # and print its C
./py/build.sh && (cd py && python3 test_tenon_kernels.py)   # shared library and binding tests
./difftest/run.sh                                       # differential test (about 45 minutes)
./floatcheck/run.sh                                     # Lean Float against C
./bench/run.sh                                          # benchmarks
```
