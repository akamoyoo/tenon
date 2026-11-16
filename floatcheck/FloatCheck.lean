import Tenon
import Emit
/-! Does Lean's `Float` agree, bit for bit, with the C the emitter generates, operation by operation?

    The kernel's float semantics IS Lean's `Float` (`evalF` calls `+`, `*`, `Float.sqrt`, `Float.abs`,
    `Float.ofInt`, `≤`, unary minus). The generated C uses `+ - * /`, `-x`, `fabs`, `sqrt`,
    `(double)int64`, `<=`. The kernel trusts that the two are the same function on binary64. This
    program measures it on this machine:

      fpcheck <outdir>     writes  ops.c (one emitted Tenon function per operation, plus a driver that
                           holds every input as a bit pattern) and expected.txt (Lean's results)

    It can be run compiled (`.lake/build/bin/fpcheck`) and interpreted (`lean --run`); `run.sh` does
    both, requires the two expected files to be identical, compiles ops.c with several compilers and
    compares (compare_ops.py). Lean's results are computed twice, directly (`x + y`) and through
    `evalFn` on the emitted Tenon function; a disagreement between those two is reported by this program.

    Lean's `Float.toBits` returns 0x7ff8000000000000 for every NaN, so for a NaN result only "is a NaN"
    can be compared; the C NaN bit patterns are tabulated by compare_ops.py. -/
open Tenon Tenon.Emit

def specials : List UInt64 := [
  0x7ff8000000000000, 0xfff8000000000000, 0x7ff8000000000001, 0x7ff0000000000001, 0xfff4000000000000,
  0x7ff0000000000000, 0xfff0000000000000,
  0x0000000000000000, 0x8000000000000000,
  0x0000000000000001, 0x8000000000000001, 0x000fffffffffffff, 0x0008000000000000, 0x800abcdef0123456,
  0x0010000000000000, 0x8010000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
  0x3ff0000000000000, 0xbff0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff, 0x4000000000000000,
  0x4340000000000000, 0x4340000000000001, 0x433fffffffffffff, 0xc340000000000001,
  0x3fb999999999999a, 0x3fd5555555555555, 0x3fe0000000000000, 0x4008000000000000, 0x4010000000000000,
  0x7fe1ccf385ebc8a0, 0x000730d67819e8d2, 0x4341c37937e08000, 0xc341c37937e08000,
  0x3ca0000000000000, 0x3cb0000000000000, 0x7fe0000000000000, 0x0020000000000000,
  0x43e0000000000000, 0xc3e0000000000000, 0x41dfffffffc00000, 0x3ff8000000000000]

/-- int64 values (as two's complement bits) for `ofInt`: around 0, 2^24, 2^53 and 2^63. -/
def intSpecials : List UInt64 := [
  0, 1, 2, 3, 0xffffffffffffffff, 0xfffffffffffffffe, 16777216, 16777217, 16777219, 0xfffffffffeffffff,
  9007199254740992, 9007199254740993, 9007199254740994, 9007199254740995, 9007199254740991,
  0xffdfffffffffffff, 0xffe0000000000000, 0xffe0000000000001, 0xffdffffffffffffd,
  0x7fffffffffffffff, 0x7ffffffffffffc00, 0x7ffffffffffffbff, 0x7ffffffffffffdff, 0x7ffffffffffffe00, 0x7ffffffffffffe01,
  0x8000000000000000, 0x8000000000000001, 0x8000000000000400, 0x8000000000000401, 0x80000000000003ff,
  0x4000000000000001, 0x40000000000000ff, 0x4000000000000100, 0x4000000000000101, 0x4000000000000300]

def next (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A random double: half of them of moderate magnitude with a random mantissa, the others arbitrary bits. -/
def rndBits (s : UInt64) : UInt64 × UInt64 :=
  let (a, s) := next s
  let (b, s) := next s
  if b % 4 == 0 then (a, s)
  else if b % 4 == 1 then ((a &&& (0x800fffffffffffff : UInt64)) ||| (((963 : UInt64) + (b >>> 8) % 120) <<< 52), s)
  else ((a &&& (0x800fffffffffffff : UInt64)) ||| (((1020 : UInt64) + (b >>> 8) % 7) <<< 52), s)

def pairs (nRandom : Nat) : Array (UInt64 × UInt64) := Id.run do
  let mut out : Array (UInt64 × UInt64) := #[]
  for a in specials do
    for b in specials do
      out := out.push (a, b)
  let mut s : UInt64 := 12345
  for k in [0:nRandom] do
    let (a, s1) := rndBits s
    let (b, s2) := rndBits s1
    s := s2
    -- a third of the random pairs take one operand from the special set
    let a := if k % 6 == 0 then specials.getD (k / 6 % specials.length) 0 else a
    let b := if k % 6 == 3 then specials.getD (k / 6 % specials.length) 0 else b
    out := out.push (a, b)
  for a in intSpecials do
    out := out.push (a, a)
  pure out

def toInt64 (b : UInt64) : Int := if b ≥ 0x8000000000000000 then (b.toNat : Int) - 18446744073709551616 else b.toNat

def triv : List Val → Nat → List Val → Prop := fun _ _ _ => True
def X : FExpr := .idx 2 (.var 0)
def Y : FExpr := .idx 3 (.var 0)

/-- op(x: fslice, y: fslice, out: inout fslice): out[i] = e(x[i], y[i]).  Body [i, res, x, y, out]. -/
def binFn (s : Stmt) : Fn :=
  { params := [(.fslice, false), (.fslice, false), (.fslice, true)], rlo := 0, rhi := 0,
    body := .forE (.len 1) triv s, req := .tt, pre := fun _ => True, post := fun _ _ _ => True }

def st (e : FExpr) : Stmt := .fstore 4 (.var 0) e

/-- ofint(a: [int], out: inout fslice): out[i] = (f64) a[i].  Body [i, res, a, out]. -/
def ofIntFn : Fn :=
  { params := [(.slice (-9223372036854775808) 9223372036854775807, false), (.fslice, true)], rlo := 0, rhi := 0,
    body := .forE (.len 1) triv (.fstore 3 (.var 0) (.ofInt (.idx 2 (.var 0)))),
    req := .tt, pre := fun _ => True, post := fun _ _ _ => True }

/-- name, the Tenon statement, and the same operation written directly on Lean floats. -/
def ops : List (String × Stmt × (Float → Float → Float)) := [
  ("add", st (.add X Y), fun x y => x + y),
  ("sub", st (.sub X Y), fun x y => x - y),
  ("mul", st (.mul X Y), fun x y => x * y),
  ("div", st (.div X Y), fun x y => x / y),
  ("neg", st (.neg X), fun x _ => -x),
  ("abs", st (.abs X), fun x _ => x.abs),
  ("sqrt", st (.sqrt X), fun x _ => x.sqrt),
  ("muladd", st (.add (.mul X Y) X), fun x y => x * y + x),
  ("addadd", st (.add (.add X Y) (.lit 1.0)), fun x y => (x + y) + 1.0),
  ("selLe", st (.selLe X Y (.lit 1.0) (.lit 0.0)), fun x y => if x ≤ y then 1.0 else 0.0),
  ("selLeMin", st (.selLe X Y X Y), fun x y => if x ≤ y then x else y),
  ("fite", .fite X Y (st (.lit 1.0)) (st (.lit 0.0)), fun x y => if x ≤ y then 1.0 else 0.0),
  ("fiteNot", .fite X Y .skip (st (.lit 2.0)), fun x y => if x ≤ y then 0.0 else 2.0)]

def hex16 (b : UInt64) : String := hexPad b.toNat 16

def main (argv : List String) : IO UInt32 := do
  let out := argv.headD "."
  let n := (argv.getD 1 "30000").toNat!
  IO.FS.createDirAll out
  let ps := pairs n
  let xs := ps.toList.map (·.1)
  let ys := ps.toList.map (·.2)
  let fx := xs.map Float.ofBits
  let fy := ys.map Float.ofBits
  let zeros := xs.map fun _ => (0.0 : Float)
  let mut expect : Array String := #[]
  let mut c : List String := ["#include <inttypes.h>", "#include <stdio.h>", fullPrelude, ""]
  let mut calls : List String := []
  let mut selfDisagree := 0
  for (name, s, f) in ops do
    let fn := binFn s
    match emitProgram { prelude := false } [fn] [{ name := s!"op_{name}", params := ["x", "y", "out"], locals := ["i"] }] with
    | .error e => IO.eprintln s!"{name}: {e}"; return 1
    | .ok src => c := c ++ [src]
    calls := calls ++ [s!"    for (int i = 0; i < N; i++) OUT.u[i] = 0; op_{name}(XS.d, N, YS.d, N, OUT.d, N); for (int i = 0; i < N; i++) printf(\"{name} %d %016\" PRIx64 \"\\n\", i, OUT.u[i]);"]
    let direct := (fx.zip fy).map fun (x, y) => f x y
    -- the same through the kernel's reference semantics
    match evalFn [fn] 0 [.farr fx, .farr fy, .farr zeros] with
    | some (_, [_, _, .farr r]) =>
      for ((d, e), i) in (direct.zip r).zipIdx do
        if d.toBits != e.toBits then selfDisagree := selfDisagree + 1
        expect := expect.push s!"{name} {i} {hex16 d.toBits}"
    | _ => IO.eprintln s!"{name}: evalFn is not `some`"; return 1
  -- ofInt
  let is := xs.map toInt64
  match emitProgram { prelude := false } [ofIntFn] [{ name := "op_ofint", params := ["a", "out"], locals := ["i"] }] with
  | .error e => IO.eprintln s!"ofint: {e}"; return 1
  | .ok src => c := c ++ [src]
  calls := calls ++ ["    for (int i = 0; i < N; i++) OUT.u[i] = 0; op_ofint((const int64_t *)XS.u, N, OUT.d, N); for (int i = 0; i < N; i++) printf(\"ofint %d %016\" PRIx64 \"\\n\", i, OUT.u[i]);"]
  match evalFn [ofIntFn] 0 [.arr is, .farr zeros] with
  | some (_, [_, .farr r]) =>
    for ((d, e), i) in ((is.map Float.ofInt).zip r).zipIdx do
      if d.toBits != e.toBits then selfDisagree := selfDisagree + 1
      expect := expect.push s!"ofint {i} {hex16 d.toBits}"
  | _ => IO.eprintln "ofint: evalFn is not `some`"; return 1
  let arr (nm : String) (l : List UInt64) : String :=
    s!"static union \{ uint64_t u[N]; double d[N]; } {nm} = \{\{{", ".intercalate (l.map fun b => s!"UINT64_C(0x{hex16 b})")}}};"
  c := c ++ [s!"#define N {ps.size}", arr "XS" xs, arr "YS" ys, "static union { uint64_t u[N]; double d[N]; } OUT;",
    "int main(void)", "{"] ++ calls ++ ["    return 0;", "}", ""]
  IO.FS.writeFile s!"{out}/ops.c" ("\n".intercalate c)
  IO.FS.writeFile s!"{out}/expected.txt" ("\n".intercalate expect.toList ++ "\n")
  IO.FS.writeFile s!"{out}/inputs.txt" ("\n".intercalate (ps.toList.map fun (a, b) => s!"{hex16 a} {hex16 b}") ++ "\n")
  IO.println s!"fpcheck: {ps.size} input pairs ({specials.length}x{specials.length} special, {n} random, {intSpecials.length} integer), {ops.length + 1} operations, {expect.size} results; direct Lean operation vs evalFn on the Tenon term: {selfDisagree} disagreements"
  pure (if selfDisagree == 0 then 0 else 1)
