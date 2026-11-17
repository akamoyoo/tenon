# Tenon in a few pages

This is the whole language as it exists today. It is meant to be read once, top to bottom, and to be
enough to write a kernel and prove it. The definition is `Tenon.lean`; where this text and that file
differ, the file is right.

## A file

A Tenon source file (`.tn`) contains functions and nothing else:

```
fn name(params) -> int(lo, hi)
  requires (condition)
  uses [callee1, callee2]        -- optional; callees must appear earlier in the file
{
  statements
}
```

```
tenon check file.tn      prove every function; report what could not be proved and where
tenon emit file.tn       the same, then print the C for the file if everything was proved
```

`tenon` writes one theorem per function and has Lean check it. A function is accepted only if Lean
accepted its theorem; nothing in the command is trusted. (The same functions can be written inside a
Lean file with `kfn` in place of `fn`, followed by `theorem nameOk : FnOk [callees] name := by kvc name
[callees]`; that is how `SurfaceExamples.lean` and `Examples.lean` are written, and it allows a proof by
hand where the automatic one fails.)

## Types

| Type | Values | In C |
|---|---|---|
| `int(lo, hi)` | integers from `lo` to `hi` inclusive; both must fit 64 bits | `int64_t` |
| `slice(lo, hi)` | an array of integers, each in `lo..=hi`, of any length known at run time | pointer and length |
| `f64` | IEEE-754 binary64 | `double` |
| `fslice` | an array of `f64` of run-time length | pointer and length |

Every variable has one of these types for its whole life. The range of an integer is part of its type:
assigning a value outside it is an error the proof must exclude. Fixed-length arrays exist in the core
language (`Ty.arr`) but not yet in the surface syntax.

## Parameters and the result

```
kfn f(a: int(0, 100), x: slice(-1000, 1000), out: inout fslice, alpha: f64) -> int(0, 9)
```

- A parameter is passed by value unless marked `inout`. An `inout` parameter is the caller's variable:
  what the function stores in it is what the caller sees afterwards.
- The result is an integer in the declared range. Inside the body it is the variable `result`, initially
  `lo`. Float results go through an `inout fslice`.
- An array never changes length, and a variable the function does not assign does not change. Both are
  theorems; you never state them.

## `ensures`

```
ensures (result < len(x) && forall j in 0 .. len(x): x[j] <= x[result])
```

A postcondition, proved for every call that satisfies the types and `requires`. In it, `result` is the
result, an `inout` parameter stands for its value at return, and every other parameter for its value at
entry. The condition language is the one of invariants (below), with array elements and quantifiers. A
caller may rely on its callees' postconditions: they are available in the caller's proof, and the
callee's body is not looked at.

## `requires`

A condition on the arguments that a caller can check before calling:

```
requires (len(x) == len(out) && len(x) <= 1000000 && 1 <= w)
requires (always)
```

Terms: integer literals, integer parameters, `len(array parameter)`, `+`, `-`, `*`, parentheses.
Comparisons: `<=`, `<`, `==`. Combination: `&&`. Nothing else. Because it is this restricted, an entry
check is generated from it (the Python binding does so), and the proof assumes exactly what that check
tests.

## Statements

```
let x: int(lo, hi) = e;          -- a new integer variable, in scope to the end of the block
let y: f64 = e;                  -- a new float variable
x = e;                           -- assignment (integer or float, by the variable's type)
a[i] = e;                        -- element store (integer or float slice)
if e1 <= e2 { ... } else { ... } -- both branches required; integers or floats
if e1 < e2 { ... } else { ... }  -- integers only
for i upto e invariant (P) { ... }        -- i = 0, 1, ..., e-1; e is evaluated once
loop upto e invariant (P) { ... }         -- repeats until `break`; see below
loop bound n invariant (P) { ... }        -- the same with a literal bound
break;                           -- leaves the innermost loop
x = g(a, inout b);               -- call; g must be listed after `uses`; arguments are variables
```

parallel for i upto e { out[i] = g(a, b, i); }   -- see "Parallel loops" below

There is no `while`, no recursion, no early `return`, no global variable.

**Parallel loops.** `parallel for i upto e { out[i] = g(args, i); }` calls `g` once for every `i` from 0
to `e - 1`, possibly at the same time on several threads, and stores each result in `out[i]`. The body is
exactly one such store. Rules: `g` is listed after `uses`; its last argument is the loop variable; every
other parameter of `g` is by value; `out` is a slice and is not among the arguments; `e` is at most
`len(out)`. If `out` is an integer slice the result of `g` is stored and must fit `out`'s element range;
if `out` is an `fslice`, `g` has a last parameter `r: inout f64` and its final value is stored. The
result is the same whatever the number of threads and whatever order the calls run in (theorem
`parallel_writes`). To reduce in parallel, cut the data into a number of chunks fixed in the source,
compute the chunk results with a parallel loop, and combine them with an ordinary loop (see
`examples/par_sum.tn`). Compile the C with `-fopenmp`; without it the loop runs on one thread and gives
the same result.

**`for`** runs exactly `e` times unless left by `break`. The counter is read-only in spirit: assigning it
has no effect on the iteration.

**`loop upto e`** has no counter. It must be left by `break`, and the proof must show that this happens
within `e` iterations. `e` and the iteration number (written `iter_` in the invariant) exist only for the
proof: the generated code is `for (;;)`. Use it when the number of iterations is not the natural loop
variable, as in binary search:

```
loop upto len(a) + 1 invariant (lo ≤ hi ∧ hi ≤ a_len ∧ hi - lo ≤ a_len - iter_) {
  if hi <= lo { break; } else {
    let mid: int(0, 9223372036854775807) = lo + (hi - lo) / 2;
    if a[mid] < p { lo = mid + 1; } else { hi = mid; }
  }
}
```

**Calls.** An `inout` argument may appear only once among the arguments of a call and may not be the
destination. This is what allows the generated code to pass a pointer.

## Expressions

Integer: literals, variables, `+`, `-`, `*`, `/`, unary `-`, `a[i]`, `len(a)`,
`sel(e1 <= e2, t, e)` (also `<`, `==`).

Float: literals with a decimal point, variables, `+`, `-`, `*`, `/`, unary `-`, `a[i]`, `sqrt(e)`,
`fabs(e)`, `sel(...)`. An integer expression used where a float is expected is converted.

Rules that differ from C:

- **Every integer value fits 64 bits, and the proof must show it.** There is no wrap-around. An
  intermediate result that could overflow is an error even if the final value would fit.
- **`/` on integers is defined only for a non-negative dividend and a positive divisor.** The proof must
  show both.
- **`sel(c, t, e)` evaluates both `t` and `e`.** Both must be safe. In return the generated code has no
  branch. A read `a[i]` inside `sel` must be in range whichever way the condition goes.
- **Float operations are never errors.** Division by zero gives an infinity or a NaN, as IEEE says.
  A comparison involving a NaN is false, so `if a <= b` takes the `else` branch.
- **Floats are evaluated exactly as written:** one rounding per operation, no reordering, no fused
  multiply-add. A sum is computed in the order of the source.

## Invariants

A loop carries an invariant, in parentheses, in the same notation as `requires`:

```
for i upto len(x) invariant (0 <= cnt && cnt <= i) { ... }
loop upto len(a) + 1 invariant (lo <= hi && hi <= len(a) && hi - lo <= len(a) - iter_) { ... }
for i upto len(x) invariant (always) { ... }
```

Terms: integer literals, integer variables in scope, `len(array)`, elements `a[t]` of integer arrays,
`+`, `-`, `*`, unary `-`, parentheses; the loop variable of a `for`, and `iter_` in any loop, stand for
the number of completed iterations. Comparisons: `<=`, `<`, `==`, `>=`, `>`. Combination: `&&`, `||`,
parentheses, and `forall j in lo .. hi: condition` (for every integer j with lo <= j < hi). `always` is
the trivial invariant. Array elements and quantifiers are not allowed in `requires`.
(Inside a Lean file, `invariant_lean (P)` takes an arbitrary Lean proposition instead.)

You do not write, and must not expect to need:

- the ranges of variables (they come from the types);
- that an array keeps its length, or that a variable the body does not assign is unchanged;
- anything about floats (there is nothing to prove about them except indices).

What you do write is what relates the variables the loop changes: `lo <= hi`, `cnt <= i`,
`acc <= 1000000000 * i`. For a loop that only reads and writes floats at index `i`, the invariant is
`always`.

To find an invariant for an integer accumulator, ask how large it can be after `i` iterations and write
that bound; then choose the accumulator's declared range to contain the bound at the largest length
`requires` allows.

## When the check fails

```
examples/notional_bad.tn:7: in `notional`: cannot show that this value stays within 64 bits
    acc = acc + px[i] * qty[i];
    needed: INT64_MIN <= <element> * <element>
    (5 more obligation(s) of `notional` not shown; they often follow from the first. `tenon check -a` shows all.)
```

The message names the statement and the fact that could not be shown, in the names of the source
(`<element>` is a value read from an array). The usual causes, in order of frequency:

1. The invariant is too weak: the fact is true but does not follow from what the invariant says.
2. A declared range is too small for a value the code computes (often an intermediate sum).
3. `requires` does not bound a length or exclude a case (an empty array, a zero divisor).
4. The fact is beyond the automatic procedure. It decides linear integer arithmetic, bounds a product
   of two values from their constant ranges, and bounds a quotient `a / b` from `a <= c * b`. Bit
   operations and anything about the contents of a whole array are not attempted: rewrite the code, or
   move the function into a Lean file and prove it by hand with the tactics `kvc` is made of.

A whole program is a list of functions; besides each function's theorem it needs that declared ranges
fit 64 bits and that each `requires` refers to parameters of the right kind (`ProgOk`; see `prog2Ok` in
`SurfaceExamples.lean`). `tenon check` does not yet state this whole-program theorem.

## What the proof gives you

If `ProgOk p` holds and a function of `p` is called with arguments of its parameter types that satisfy
its `requires`, then (`prog_sound`): evaluation is not stuck; the result is in its declared range; the
final values of the parameters have the parameter types and the same lengths. "Not stuck" covers every
index, every integer operation, every division, every call's requirement, and every `loop` leaving by
`break` within its bound.

What it does not give you: that the function computes what you meant. There is no `ensures` yet.

## From Tenon to a running kernel

`Emit.lean` turns a checked program into C. Integers become `int64_t`, slices a pointer and a length,
`inout` a pointer the callee writes through. There are no checks in the generated code.

The caller must establish what the proof assumed: arrays of the stated length, elements inside the
declared ranges, `requires` true, and `inout` arguments not overlapping any other argument. The Python
binding in `py/` does all of this for NumPy arrays and generates the `requires` check from the source.
A parameter whose declared range is all of 64 bits, and any float parameter, needs no scan.

Compile the C with `-ffp-contract=off` and without any fast-math option.
