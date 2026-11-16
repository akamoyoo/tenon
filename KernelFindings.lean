import Tenon
import Emit
import Examples
/-! Reproducers for the observations about Tenon.lean reported in README.md. Nothing here changes the
    kernel. Build with `lake build KernelFindings` and read the output.
    The first part (G1, G2, F2, H1 to H6) is the list of emitter round 4, re-run on Tenon; the second part
    (K1 to K9) is new with floats, `loopE` and `req`.

    None of these contradicts `prog_sound`; I found no way to make a checked program misbehave.
    G1, G2 and F2 are the findings of emitter round 3 and are unchanged in Tenon (they concern `evalFn` on
    programs that are not checked). H1 to H6 are new with slices, `sel`, `forE` and the binding. -/
namespace Tenon.Findings
open Tenon Stmt Expr Tenon.Examples

/-! ### G1 (unchanged). `evalFn` ignores the `inout` flag of the parameter -/

def set5 : Fn where
  params := [(.int 0 9, false)]
  rlo := 0
  rhi := 0
  body := assign 1 (lit 5)
  req := .tt
  pre := fun _ => True
  post := fun _ _ _ => True

def callerG1 : Fn where
  params := [(.int 0 9, false)]
  rlo := 0
  rhi := 9
  body := decl 0 0 (lit 0) (seq (Stmt.call 0 [(2, true)] 0) (assign 1 (var 2)))
  req := .tt
  pre := fun _ => True
  post := fun _ _ _ => True

#eval evalFn [callerG1, set5] 0 [.int 1]       -- some (5, [int 5]): set5's by-value x was written back to y
#eval evalFn [set5] 0 [.int 1]                 -- some (0, [int 5]): the final value of a by-value parameter is returned

/-! ### G2 (unchanged). In `execS` a call does not keep the caller's types -/

def to50 : Fn where
  params := [(.int 0 100, true)]
  rlo := 60
  rhi := 60
  body := assign 1 (lit 50)
  req := .tt
  pre := fun _ => True
  post := fun _ _ _ => True

def callerG2 : Fn where
  params := [(.int 0 5, true)]
  rlo := 0
  rhi := 0
  body := decl 0 1 (lit 0) (Stmt.call 0 [(2, true)] 0)
  req := .tt
  pre := fun _ => True
  post := fun _ _ _ => True

#eval evalFn [callerG2, to50] 0 [.int 3]       -- some (0, [int 50]): y : 0..=5 ends as 50

/-! ### F2 (unchanged, and now also for `forE`). The counter is an ordinary assignable variable; the
    change is forgotten at the next iteration. The `forE` counter has type 0..=2^63-1, so the type
    says nothing about `i < bound`: the bound is known only through the loop obligation `i < nv`. -/

#eval evalFn [forEProbe] 0 [.int 6, .arr [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#eval IO.println <| match Tenon.Emit.emitProgram {} [forEProbe] [{ name := "for_e_probe", params := ["n", "a"], result := "res", locals := ["m", "i"] }] with
  | .ok c => c | .error e => s!"emitter: {e}"

/-! ### H1. An `inout` slice must have its type BEFORE the call, also when the function only writes it

`hasAll` is checked on the arguments, so the contents of an output buffer must already lie in the
element range. (Tenon: this still holds for integer slices. A float slice has no element range, so a float output needs
no scan and no zero-fill; see the binding.) `prefix_sum` never reads `out`, yet a buffer holding one large stale value is outside
the guarantee (`evalFn` is `none`). A binding has two choices: scan the caller's buffer (O(n), measured
in bench/) or allocate a zeroed one. There is no "out" mode (write-only: no requirement at entry, the
type holds at exit provided every element was stored). -/

#eval evalFn [prefixSum] 0 [.arr [1, 2, 3], .arr [0, 0, 0]]                    -- some
#eval evalFn [prefixSum] 0 [.arr [1, 2, 3], .arr [0, 0, 1000000000000001]]     -- none, although out[2] is overwritten

/-! ### H2. `sel` cannot guard a load, so "x[i] if i is in range else 0" has no expression form

`sel c t e` evaluates both arms (that is what makes it branch-free). The natural one-loop rolling sum
`acc = acc + x[i] - sel (w <= i) x[i-w] 0` is stuck for i < w. `rollingSum` therefore has two loops.
A guarded load needs a statement (`ite`), and then a mutable temporary. -/

def guarded : Fn where
  params := [(.slice (-9) 9, false), (.int 0 100, false)]
  rlo := -9
  rhi := 9
  body := assign 0 (.sel (lt (var 2) (.len 1)) (idx 1 (var 2)) (lit 0))     -- res = i < len(a) ? a[i] : 0
  req := .tt
  pre := fun _ => True
  post := fun _ _ _ => True

#eval evalFn [guarded] 0 [.arr [1, 2, 3], .int 1]      -- some (2, _)
#eval evalFn [guarded] 0 [.arr [1, 2, 3], .int 7]      -- none: the arm that is not selected is still evaluated

/-! ### H3. An array can be passed to a slice parameter by value, but not `inout`

By value, `wpS` asks only that the VALUE has the parameter's type (`hasAll`), so `[int; 8]` may be
passed where a slice is expected (`ps_arr` in Examples.lean; the emitter passes the pointer and the
constant 8). For `inout`, `argsTyped` asks for syntactically equal types, so a fixed-length array can
never be filled by a function over slices in a checked program, although `evalFn` runs it. -/

/-- fill8(a: inout [int; 8], x: [int]) { t = prefix_sum(x, inout a) } -/
def fill8 : Fn where
  params := [(.arr 8 (-1000000000000000) 1000000000000000, true), (.slice (-1000000000) 1000000000, false)]
  rlo := 0
  rhi := 0
  body := Stmt.call 0 [(2, false), (1, true)] 0
  req := .tt
  pre := fun _ => True
  post := fun _ _ _ => True

#eval evalFn [fill8, prefixSum] 0 [.arr [0, 0, 0, 0, 0, 0, 0, 0], .arr [1, 2, 3, 4, 5, 6, 7, 8]]   -- some: evalFn runs it
example : ¬ argsTyped [.int 0 0, .arr 8 (-1000000000000000) 1000000000000000, .slice (-1000000000) 1000000000]
    prefixSum.params [(2, false), (1, true)] := by
  simp [argsTyped, prefixSum]                    -- but no checked program may contain the call

/-! ### H4. The exhaustion obligation of `loopB` gets less than the other two

`wpS` for `loopB n I s` asks `∀ env', hasAll Γ env' → I env n env' → False`: no `sameAt`, no
`lens env' = lens env`. The variant must therefore be stated entirely through `I` against the entry
environment (`lbsInv` uses `leni env 3`, the length at entry). It works; it is an asymmetry a tactic has
to know about (the one-line `kvc` handles it only because `omega` closes it from `I` alone). -/

/-! ### H5. The result range is a pair of constants

`lower_bound(a, p) -> 0..=len(a)` cannot be a type: `rlo`/`rhi` are integers. The result type is
0..=2^63-1 and `r ≤ len(a)` lives in `post`, which is a `Prop` that neither the emitter nor a binding
can read. Same for the precondition: `len(x) = len(out) ∧ len(x) ≤ 10^7` is retyped by hand in
py/k4kernels.py (`PRE`). The types, in contrast, are data and are exported (py/PyGen.lean). -/

#eval (lowerBoundS.rlo, lowerBoundS.rhi)

/-! ### H6. A slice may be longer than any C object

`Ty.slice` admits lengths up to 2^63-1 elements; a C object has at most 2^63-1 BYTES, so the largest
real slice has 2^60-1 elements. Harmless for the generated code (indices still fit int64_t); it means
`i * 8` style byte arithmetic would not be covered by the type alone. The proofs here needed the bound
only to know that `len` fits int64. -/

/-! ## New in Tenon -/

/-! ### K1. The reference semantics cannot see which NaN it has

`Float.toBits` is the only way to look at the bits of a Lean `Float`, and it returns
0x7ff8000000000000 for every NaN. So "bit for bit" can be checked for every result except the sign
and payload of a NaN. The generated C does produce different NaNs (x86 gives 0xfff8000000000000 for
0/0 and inf-inf computed at run time, compilers fold the same expression to 0x7ff8000000000000, an
input payload propagates or not depending on operand order): difftest/RESULT.txt counts them per
build as `nan_payload_differs`. Nothing in Tenon can depend on the difference (no operation of Tenon reads a
payload or the sign of a NaN: `abs` and `neg` change the sign but nothing tests it). -/

#eval (Float.ofBits 0x7ff8000000000001).toBits == 0x7ff8000000000000     -- true: the payload is not visible
#eval (Float.ofBits 0xfff8000000000000).toBits == 0x7ff8000000000000     -- true: nor the sign
#eval ((0.0 : Float) / 0.0).toBits                                       -- 9221120237041090560 = 0x7ff8000000000000
#eval (-(Float.ofBits 0x7ff8000000000000)).toBits                        -- the same: negation of a NaN is not visible

/-! ### K2. The operations Tenon uses, on the cases where implementations usually differ (interpreter)

The full comparison with the generated C (44 x 44 special pairs, 30,000 random pairs, 14 operations,
compiled and interpreted Lean, seven C builds) is floatcheck/; its output is floatcheck/RESULT.txt.
Here the same cases as `#eval`, so that they are visible at build time. Expected bits in the comments
are what the C printed on this machine. -/

def bitsHex (f : Float) : String := Tenon.Emit.hexPad f.toBits.toNat 16

#eval bitsHex (-(0.0 : Float))                         -- 8000000000000000: -(+0) = -0
#eval bitsHex (-(Float.ofBits 0x8000000000000000))     -- 0000000000000000: -(-0) = +0
#eval bitsHex ((0.0 : Float) - 0.0)                    -- 0000000000000000: 0 - 0 = +0 (so `neg x` is not `0 - x`)
#eval bitsHex (Float.ofBits 0x8000000000000000).abs    -- 0000000000000000: |-0| = +0
#eval bitsHex (Float.ofBits 0x8000000000000000).sqrt   -- 8000000000000000: sqrt(-0) = -0
#eval bitsHex (Float.sqrt 2.0)                         -- 3ff6a09e667f3bcd
#eval bitsHex (Float.sqrt (-1.0))                      -- 7ff8000000000000 (C: fff8000000000000 at run time)
#eval bitsHex (Float.ofInt 9007199254740993)           -- 4340000000000000: 2^53 + 1 rounds to even (down)
#eval bitsHex (Float.ofInt 9007199254740995)           -- 4340000000000002: 2^53 + 3 rounds to even (up)
#eval bitsHex (Float.ofInt 9223372036854775807)        -- 43e0000000000000: 2^63 - 1 rounds to 2^63
#eval bitsHex (Float.ofInt (-9223372036854775808))     -- c3e0000000000000
#eval bitsHex (Float.ofInt 0)                          -- 0000000000000000: +0, also for "-0"
#eval decide ((0.0 : Float) ≤ -0.0)                    -- true: zeros compare equal
#eval decide ((0.0 : Float) / 0.0 ≤ (0.0 : Float) / 0.0)   -- false: NaN ≤ NaN
#eval decide ((1.0 : Float) ≤ (0.0 : Float) / 0.0)     -- false
#eval bitsHex ((0.1 : Float) * 3.0 + (-0.3))           -- 3c90000000000000: the unfused value (fma(0.1, 3.0, -0.3) is 3c8999999999999a)

/-! ### K3. `Float.ofInt` outside 64 bits (not reachable from Tenon): no problem found

`Float.ofInt` goes through `Float.ofScientific`. I expected a double rounding for integers of more
than 64 bits (truncate to 64 bits, then round to 53) and tried the standard counterexample,
2^64 + 2^11 + 1, which lies just above the midpoint between 2^64 and 2^64 + 2^12 and must round up.
Lean rounds it correctly. Tenon never gets there anyway: `FExpr.ofInt e` takes its integer from `evalE`,
which is confined to int64; on that range the conversion was compared with C `(double)int64_t` in
floatcheck/ (35 boundary values and 30,000 random bit patterns). -/

#eval bitsHex (Float.ofInt (18446744073709551616 + 2048 + 1))    -- 43f0000000000001 = 2^64 + 2^12: correct
#eval bitsHex (Float.ofInt (18446744073709551616 + 2048))        -- 43f0000000000000: the tie goes to even
#eval bitsHex (Float.ofInt (18446744073709551616 + 4096))        -- 43f0000000000001

/-! ### K4. Nothing can be proved about a float value

`Float` is an opaque structure in Lean: there are no theorems about `+` or `≤` on it, and `decide`
cannot evaluate them. The obligations of the float kernels are therefore index obligations only, the
invariants are `True`, and a postcondition such as "every element of out is ≥ 0" (the purpose of the
clamp in `rolling_var`) cannot be stated usefully, let alone proved. The only way to get a fact about a
concrete float through the kernel is `native_decide`, which trusts the compiler (and the same C
library this file is checking). -/

example : (1.0 : Float) + 1.0 == 2.0 := by native_decide      -- works, but it is not a kernel proof
-- example : (1.0 : Float) + 1.0 == 2.0 := by decide          -- fails: Float.add does not reduce

/-! ### Tenon. `loopE`: the bound is evaluated by `execS` and may be stuck; the C never evaluates it

Same body, same input, three bounds. With a bound that overflows, divides by zero, or is negative
(`toNat` gives 0 iterations) `evalFn` is `none`, although the loop itself would leave at once. The
generated C is `for (;;)` in all three cases and returns 7. A checked program cannot have such a bound
(`wpS` passes the bound through `wpE`, and the exhaustion obligation fails for 0 iterations), so the
C may drop it; an unchecked one can, and there the C runs where Tenon is stuck. -/

def loopEFn (bnd : Expr) : Fn where
  params := [(.int 0 100, false)]
  rlo := 0
  rhi := 100
  body := loopE bnd (fun _ _ _ => True) (seq (assign 0 (lit 7)) brk)
  req := .tt
  pre := fun _ => True
  post := fun _ _ _ => True

#eval evalFn [loopEFn (lit 1)] 0 [.int 5]                                         -- some (7, _)
#eval evalFn [loopEFn (add (lit 9223372036854775807) (var 1))] 0 [.int 5]         -- none: the bound overflows
#eval evalFn [loopEFn (div (lit 1) (lit 0))] 0 [.int 5]                           -- none: the bound is stuck
#eval evalFn [loopEFn (sub (lit 0) (var 1))] 0 [.int 5]                           -- none: negative bound, zero iterations
#eval IO.println <| match Tenon.Emit.emitProgram {} [loopEFn (div (lit 1) (lit 0))] [{ name := "loop_e", params := ["k"] }] with
  | .ok c => c | .error e => s!"emitter: {e}"

/-! ### K6. `req` is evaluated in unbounded integers and is not shape-checked

`evalCT` computes in `Int` without any 64-bit confinement (unlike `evalE`), so a check function in C
would have to guard every `+ - *` against overflow to mean the same thing; the binding therefore
evaluates the generated condition in Python integers (py/PyGen.lean). And a `CT.val` of a parameter that is
not an integer, or a `CT.len` of one that is not an array, silently reads as 0 instead of being
rejected: the condition below "holds" for a float slice. -/

#eval evalC (.le (.mul (.len 0) (.lit 9223372036854775807)) (.lit 0)) [.farr []]        -- true; 0 * 2^63 in Int
#eval evalC (.eq (.val 0) (.lit 0)) [.farr [1.0, 2.0]]                                  -- true: `val` of an array is 0
#eval evalC (.eq (.len 0) (.lit 0)) [.int 5]                                            -- true: `len` of an integer is 0

/-! ### K7. A float parameter has no range and `req` cannot mention float values

`Val.has (.flt _) .flt` is `true` for every double, NaN and infinities included, and `Cond` speaks
only about integer parameters and lengths. So "alpha in [0, 1]", "w ≤ len(x)" (fine: integers) but not
"x has no NaN" can be required. With K4 above this is consistent (nothing could use the fact), but it
means a binding has nothing to check on float values and a caller gets NaN out for NaN in, silently. -/

#eval evalFn [ewma] 0 [.farr [1.0, 2.0], .flt (0.0 / 0.0), .farr [0.0, 0.0]]       -- some: alpha = NaN is within the type

/-! ### K8. Comparisons of floats exist only as `≤`, in `fite` and `selLe`

No `<`, no `==`, no comparison as an integer expression. "if a < b" is `fite b a ELSE THEN` (swapped
arms), which sends a NaN to the THEN branch; the surface syntax of Surface.lean rejects `<` on
floats for that reason. `selLe v 0 0 v` and `selLe 0 v v 0` are both "max(v, 0)" on numbers and differ
on NaN (the first keeps it, the second returns 0): `rolling_var` had to choose, and nothing in the term
says that the choice was deliberate. -/

/-! ### K9. A result is an integer; a float result costs an `inout` slice

`sum8` and `dot` return one number through `out[0]` and need `1 ≤ len(out)` in `req`; the C signature
gets a pointer and a length for it, the binding allocates a one-element array per call. An `inout`
float scalar parameter (`(.flt, true)`) works in Tenon and in the emitter (`double *`), and would be the
lighter convention; the kernels of ../k1 do not use it. -/

end Tenon.Findings
