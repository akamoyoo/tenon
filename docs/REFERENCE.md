# Tenon in a few pages

This is the whole language as it exists today. It is meant to be read once, top to bottom, and to be
enough to write a kernel and prove it. The definition is `Tenon.lean`; where this text and that file
differ, the file is right.

## A file

A Tenon function is written in a Lean file that imports `Surface`:

```
import Surface

kfn name(params) -> int(lo, hi)
  requires (condition)
  uses [callee1, callee2]        -- optional
{
  statements
}

open Tenon in
theorem nameOk : FnOk [callee1, callee2] name := by
  kvc name [callee1, callee2]
```

`lake build` succeeds only if every theorem is proved. There is no other notion of "compiles".

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

There is no `while`, no recursion, no early `return`, no global variable.

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

A loop carries an invariant: a Lean proposition in parentheses. In it

- a variable's name stands for its integer value,
- `name_len` stands for the length of an array variable,
- the loop variable of a `for` stands for the number of completed iterations (`iter_` in a `loop`).

You do not write, and must not expect to need:

- the ranges of variables (they come from the types);
- that an array keeps its length, or that a variable the body does not assign is unchanged;
- anything about floats (there is nothing to prove about them except indices).

What you do write is what relates the variables the loop changes: `lo ≤ hi`, `cnt ≤ i`,
`|acc| ≤ 10^9 · i`. For a loop that only reads and writes floats at index `i`, the invariant is `True`.

To find an invariant for an integer accumulator, ask how large it can be after `i` iterations and write
that bound; then choose the accumulator's declared range to contain the bound at the largest length
`requires` allows.

## Proving

`kvc f [callees]` proves `FnOk [callees] f`. It unfolds the obligations, uses the types, the unchanged
variables and the lengths, and closes arithmetic with a decision procedure for linear integer
arithmetic. If it fails, Lean shows the goal it could not prove, in terms of the values of your
variables. The usual causes, in order of frequency:

1. The invariant is too weak: the goal is true but does not follow from what the invariant says.
2. A declared range is too small for a value the code computes (often an intermediate sum).
3. `requires` does not bound a length, so a bound that depends on it cannot be shown.
4. The fact is not linear arithmetic (a product of two variables, a bit operation): `kvc` does not
   attempt it. Rewrite the code, or prove the function by hand with the tactics `kvc` is made of
   (`env_open`, `vc_loop`, `vc_leaves` in `Tenon.lean`).

A whole program is a list of functions, newest first; `ProgOk [f, g]` needs `FnOk [g] f`, `FnOk [] g`,
that declared ranges fit 64 bits, and that each `requires` refers to parameters of the right kind. See
`prog2Ok` in `Surface.lean`.

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
