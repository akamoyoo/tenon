# Difftest mismatch, seed 401, program 148, case 6: root cause

    SEEDS="401 402" NPROGS=150 NINPUTS=10 ./difftest/run.sh
    clang-ubsan:  MISMATCH prog=148 case=6 (result) evalFn=-830 C=-999872        (the six other builds: -830)

**Verdict: (c), a compiler bug. clang 21.1.8's `Float2Int` pass folds a floating-point comparison
to the wrong constant when an operand is a compile-time constant double whose integer value does not
fit 64 bits.** The emitted C is well defined and correct; Tenon leaves nothing unspecified here (no NaN is
involved); the harness compared correctly. Nothing was changed in the emitter or the kernel.
It is not a sanitizer artefact in the usual sense: the sanitizer checks never fire and are not
involved in the wrong value. `-fsanitize=pointer-overflow` or `-fsanitize=object-size` (both part of
`-fsanitize=undefined`) only change the order of optimisation passes so that the constant reaches the
buggy pass before another pass has folded it.

## Reduced reproducer

Tenon program (one function, no loop, no call, no NaN) and input:

    probe(x: f64) -> 0..=1     { if 1.0 <= x + x { res = 1 } else { res = 0 } }
    body := fite (lit 1.0) (add (var 1) (var 1)) (assign 0 (lit 1)) (assign 0 (lit 0))
    input x = 1e30 (bits 0x46293e5939a08cea);   evalFn [probe] 0 [.flt 1.0e30] = some (1, _)

`repro/probe.c` is the C the emitter prints for it plus a `main` in the style of the difftest driver
(the input is a bit pattern in a `static` union in the same translation unit). `./repro/run.sh`
(`repro/RESULT.txt`):

```
expected (Tenon evalFn): 1
clang -O0                                                                   1
clang -O1                                                                   1
clang -O2                                                                   1
clang -O1 -fsanitize=address                                                1
clang -O1 -fsanitize=pointer-overflow                                       0     <-- wrong
clang -O1 -fsanitize=object-size                                            0     <-- wrong
clang -O1 -fsanitize=undefined,address (the difftest build)                 0     <-- wrong
clang -O2 -fsanitize=undefined                                              0     <-- wrong
clang -O1 -fsanitize=undefined, input through a volatile (-DRUNTIME)        1
gcc -O2                                                                     1
gcc -O1 -fsanitize=undefined,address                                        1
```

The pass in isolation, with no C and no sanitizer (`repro/float2int.ll`,
`opt -passes=float2int`): each function below must return `true`, `instcombine` folds all five to
`true`, `float2int` returns `false` for three of them:

```
%1 = fmul double 0xD28BC4DE7363B01B, 0xD28BC4DE7363B01B ; %2 = fcmp ugt double %1, 0.0     -> ret i1 false   (wrong)
%1 = fmul double 0xD28BC4DE7363B01B, 0xD28BC4DE7363B01B ; %2 = fcmp ogt double %1, 0.0     -> ret i1 false   (wrong)
%1 = fmul double 1.0e+30, 1.0e+30 ; %2 = fcmp ogt double %1, 0.0                            -> ret i1 true
%1 = fmul double 3.0e+09, 3.0e+09 ; %2 = fcmp ogt double %1, 0.0                            -> not folded (correct)
%1 = fadd double 1.0e+30, 1.0e+30 ; %2 = fcmp ogt double %1, 1.0                            -> ret i1 false   (wrong)
```

`Float2Int` rewrites float arithmetic as integer arithmetic when every value involved is an integer
in a known range. Every double of magnitude ≥ 2^52 is an integer, so 1e30 and −1.7·2^297 qualify as
"integer constants", but their value does not fit the pass's 64-bit ranges; the range it then
computes for `x + x` or `x * x` is wrong and the comparison is decided from that range. (I read this
off the behaviour: integral constants below 2^64 are handled correctly, e.g. 2^63 and 3e9 above; I
could not read LLVM's source here and there is no network to look for an upstream report.)

## The original case, and the first value that differs

`.lake/build/bin/difftest show 401 148`; case 6 is `p148_f0(x0 = 0xd28bc4de7363b01b ≈ -1.7·2^297, v1 = -1000000)`.
Up to the statement in question all values are identical in every build (traced by printing at one
point per build, because any print between the statements involved makes the wrong fold go away):

    after the first call `v1 = p148_f1(&x1)`:   x0 = d28bc4de7363b01b, x1 = 0000000000000000 (+0.0), result = -1000000, v1 = 4, x2 = 0
    if (!(x0 * x0 - x1 <= x1 - x1)) { ... x2 = 1000002; }          <-- the statement

`x0 * x0` is about 2^595, finite and positive; `x0*x0 - 0.0 <= 0.0` is false; the branch must be
taken and sets `x2 = 1000002` (Tenon, six builds). **The first differing value is the truth value of this
comparison: the sanitizer build has it folded to "not taken" at compile time, so `x2` stays 0.**
Everything after is a consequence (`x2` feeds the result hash: −1000000 + 999170 = −830 against
−1000000 + 128 = −999872). The floats later in the function (a NaN from `-0.0 / 0.0`, the `loopE`,
the `selLe`s) are not involved.

What the compiler made of the whole function shows that the code itself is right; the standalone
`p148_f0` in the sanitizer build is

    mulsd  %xmm0, %xmm0          ; x0 * x0
    xorpd  %xmm1, %xmm1
    ucomisd %xmm0, %xmm1         ; 0.0 < x0*x0 (or unordered)?
    movq   $-830, %rcx
    movq   $-999872, %rax
    cmovbq %rcx, %rax            ; yes: -830

which returns −830 for this input. The wrong number is produced in `main`, where the call was inlined
with the constant argument: `opt-bisect` gives pass 289, "Float2IntPass on main", turning

    %1 = fmul double 0xD28BC4DE7363B01B, 0xD28BC4DE7363B01B
    %2 = fcmp ugt double %1, 0.0
    %3 = select i1 %2, i64 -830, i64 -999872        into        select i1 false, i64 -830, i64 -999872

Deterministic, no sanitizer report: consistent with a wrong constant computed at compile time.

## Why not (a), (b) or (d)

- (a) The emitted C for the statement is `if (!(x0 * x0 - x1 <= x1 - x1))` on plain `double` locals:
  no undefined or unspecified behaviour, and no difference in any of six other builds, in gcc with
  the same sanitizers, or in clang with the input not known at compile time.
- (b) No NaN, no signed zero and no rounding is involved in the differing value; the operands are
  finite and the comparison is far from a boundary. (The NaN sign differences seen elsewhere in the
  batch are finding K1 and are unrelated; I looked for a path from NaN sign to an integer in Tenon and
  found none: no operation reads a sign or payload.)
- (d) The harness reported a real difference in the executable's output.

## What it means for the float guarantee

The guarantee already depended on the C compiler implementing IEEE arithmetic (README, item 16); this
is a concrete case where clang 21 does not. Conditions, as far as I could establish: a **compile-time
constant** double of magnitude ≥ 2^64 flowing into `+`, `-` or `*` whose result is used only by a
comparison, reaching `Float2Int` before another pass folds it. Kernel inputs from a caller (the
binding) are run-time values and are not affected (`-DRUNTIME` above). A Tenon float **literal** of that
size is a compile-time constant, so a kernel containing e.g. `selLe (add (lit 1e30) x) ...` with other
constants could in principle meet it; I saw it only under `-fsanitize=pointer-overflow` /
`object-size`, never in the plain `-O0`/`-O2`/`-march=native` builds (difftest: 81,713 inputs, 0
mismatches in those), but the pass is in the default pipeline and wrong in isolation, so I cannot
exclude other pass orders. gcc 13 is not affected.

## Why the 45-minute default run did not hit it, and what would have

The trigger needs, in one program: a float argument that the compiler can see as a constant in the driver
(here a by-value scalar), whose test input has magnitude ≥ 2^64 (roughly 9 % of my generated
doubles: 40 % of the "wide exponent" class, half of the arbitrary bit patterns, three of the special
values), used **directly** in an add/sub/mul whose result goes **only** into an
`fite`/`selLe` comparison, the callee inlined into the driver, and the outcome of that comparison
visible in the result; and it shows in one build of seven. I measured the rate afterwards on the
sanitizer build only: seeds 401 to 408, 150 programs and 10 inputs each, 1 hit in 1,200 programs
(this one). The default run has 4,000 random programs and none hit: at such a rate that is bad luck
of the plausible kind, not evidence of absence, and the default seeds are no better than any others.

Changes that would have caught it deterministically (not made to the default run, which would then
fail on every machine with this compiler; `repro/run.sh` is the probe):
1. **An operation-level test with compile-time-constant operands under the sanitizer and plain
   builds.** `floatcheck` feeds its 31,971 operand pairs through arrays, which the compiler does not
   fold; a second driver that calls each emitted one-operation function with the operands as
   `static` constants (so the call is inlined and folded) exercises the compiler's constant folder
   against Lean. 1e30 and DBL_MAX are already in its special set.
2. **Generator**: emit the shape on purpose (`fite`/`selLe` whose compared operand is `x op y` on a
   float scalar parameter, next to the contraction and reassociation shapes it already forces) and
   raise the share of huge-magnitude scalars.
3. **Harness**: build every batch twice per compiler, inputs visible as constants (as now) and inputs
   hidden (`volatile` or a separate translation unit, which is how a real caller looks), and compare
   the two builds with each other: a compiler-folding bug then shows up without needing the
   reference at all.
