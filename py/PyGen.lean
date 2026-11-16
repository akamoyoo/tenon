import Tenon
import Emit
import Examples
/-! Writes what the Python binding is built from:   pygen <outdir>
      tenon_kernels.c          the emitted C of the proved kernels (one translation unit), followed by three
                           small HAND-WRITTEN helper functions about the floating-point environment
      tenon_kernels.json       for every kernel: C name, parameters (kind, element or integer range, inout),
                           result range, and its decidable requirement `Fn.req` translated to a Python
                           expression (`req_py`) and to readable text (`req_text`)
      tenon_req_tests.json     for every kernel: argument shapes and what Tenon's own `evalC f.req` answers
                           for them, so that the Python side can test the translation against the kernel

    Everything the binding checks at entry is derived from the Tenon term: the types from `Fn.params`, the
    requirement from `Fn.req`. Nothing is retyped by hand.

    Why Python and not C for the requirement: `evalCT` computes in unbounded integers (`Int`). A C
    function would need overflow-checked arithmetic to mean the same; Python integers are unbounded, so
    the translation is one line per constructor and exact. -/
open Tenon Tenon.Emit Tenon.Examples

def kernels : List (Fn × FnNames) := [
  (prefixSum, { prefixSumNames with name := "tn_prefix_sum" }),
  (prefixSum10M, { prefixSumNames with name := "tn_prefix_sum_10m" }),
  (prefixSumW, { prefixSumNames with name := "tn_prefix_sum_w" }),
  (lowerBoundS, { lowerBoundSNames with name := "tn_lower_bound" }),
  (lowerBoundBr, { lowerBoundBrNames with name := "tn_lower_bound_branchy" }),
  (rollingSum, { rollingSumNames with name := "tn_rolling_sum" }),
  (rollingSumExact, { rollingSumNames with name := "tn_rolling_sum_exact" }),
  (rollingSumW, { rollingSumNames with name := "tn_rolling_sum_w" }),
  (Tenon.Examples.argmax, { argmaxNames with name := "tn_argmax" }),
  (ewma, { ewmaNames with name := "tn_ewma" }),
  (Tenon.sum8, { sum8Names with name := "tn_sum8" }),
  (dot, { dotNames with name := "tn_dot" }),
  (rolling_mean, { rollingMeanNames with name := "tn_rolling_mean" }),
  (rollingVar, { rollingVarNames with name := "tn_rolling_var" }),
  (rolling_std, { rollingStdNames with name := "tn_rolling_std" })]

def tyJson (pn : String) : Ty × Bool → String
  | (.int lo hi, io) => s!"\{\"name\": \"{pn}\", \"kind\": \"int\", \"lo\": {lo}, \"hi\": {hi}, \"inout\": {io}}"
  | (.arr n lo hi, io) => s!"\{\"name\": \"{pn}\", \"kind\": \"array\", \"len\": {n}, \"lo\": {lo}, \"hi\": {hi}, \"inout\": {io}}"
  | (.slice lo hi, io) => s!"\{\"name\": \"{pn}\", \"kind\": \"slice\", \"lo\": {lo}, \"hi\": {hi}, \"inout\": {io}}"
  | (.flt, io) => s!"\{\"name\": \"{pn}\", \"kind\": \"float\", \"inout\": {io}}"
  | (.fslice, io) => s!"\{\"name\": \"{pn}\", \"kind\": \"fslice\", \"inout\": {io}}"

/-! ### `Cond` to Python. `v[i]` is the value of integer argument i, `n[i]` the length of array argument i.
    As in `evalCT`, the value of a non-integer and the length of a non-array are 0. -/

def isIntP (ps : List (Ty × Bool)) (i : Nat) : Bool := match ps[i]? with | some (.int _ _, _) => true | _ => false
def isArrP (ps : List (Ty × Bool)) (i : Nat) : Bool :=
  match ps[i]? with | some (.arr .., _) | some (.slice .., _) | some (.fslice, _) => true | _ => false

def ctPy (ps : List (Ty × Bool)) : CT → String
  | .lit k => s!"({k})"
  | .val i => if isIntP ps i then s!"v[{i}]" else "0"
  | .len i => if isArrP ps i then s!"n[{i}]" else "0"
  | .add a b => s!"({ctPy ps a} + {ctPy ps b})"
  | .sub a b => s!"({ctPy ps a} - {ctPy ps b})"
  | .mul a b => s!"({ctPy ps a} * {ctPy ps b})"

def condPy (ps : List (Ty × Bool)) : Cond → String
  | .tt => "True"
  | .le a b => s!"({ctPy ps a} <= {ctPy ps b})"
  | .lt a b => s!"({ctPy ps a} < {ctPy ps b})"
  | .eq a b => s!"({ctPy ps a} == {ctPy ps b})"
  | .and a b => s!"({condPy ps a} and {condPy ps b})"

def ctText (names : List String) : CT → String
  | .lit k => toString k
  | .val i => names.getD i s!"arg{i}"
  | .len i => s!"len({names.getD i s!"arg{i}"})"
  | .add a b => s!"({ctText names a} + {ctText names b})"
  | .sub a b => s!"({ctText names a} - {ctText names b})"
  | .mul a b => s!"{ctText names a} * {ctText names b}"

def condText (names : List String) : Cond → String
  | .tt => "always"
  | .le a b => s!"{ctText names a} <= {ctText names b}"
  | .lt a b => s!"{ctText names a} < {ctText names b}"
  | .eq a b => s!"{ctText names a} == {ctText names b}"
  | .and a b => s!"{condText names a} && {condText names b}"

/-- Positions where the condition reads a value of a non-integer or a length of a non-array (K6). -/
def ctBad (ps : List (Ty × Bool)) : CT → List Nat
  | .lit _ => []
  | .val i => if isIntP ps i then [] else [i]
  | .len i => if isArrP ps i then [] else [i]
  | .add a b | .sub a b | .mul a b => ctBad ps a ++ ctBad ps b
def condBad (ps : List (Ty × Bool)) : Cond → List Nat
  | .tt => []
  | .le a b | .lt a b | .eq a b => ctBad ps a ++ ctBad ps b
  | .and a b => condBad ps a ++ condBad ps b

def ctLits : CT → List Int
  | .lit k => [k]
  | .val _ | .len _ => []
  | .add a b | .sub a b | .mul a b => ctLits a ++ ctLits b
def condLits : Cond → List Int
  | .tt => []
  | .le a b | .lt a b | .eq a b => ctLits a ++ ctLits b
  | .and a b => condLits a ++ condLits b

def fnJson (f : Fn) (nm : FnNames) : String :=
  let ps := (f.params.zip nm.params).map fun (p, pn) => tyJson pn p
  s!"  \"{nm.name}\": \{\"rlo\": {f.rlo}, \"rhi\": {f.rhi}, \"params\": [{", ".intercalate ps}],\n" ++
  s!"    \"req_py\": \"{condPy f.params f.req}\", \"req_text\": \"{condText nm.params f.req}\", \"req_ill_shaped\": {condBad f.params f.req}}"

/-! ### Test vectors for the translated requirement: Tenon's own `evalC` on argument shapes -/

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def reqTests (f : Fn) : List String := Id.run do
  -- lengths and integer values worth trying: small ones, and the literals of the condition ± 1
  let lits := (condLits f.req).filter fun k => 0 ≤ k ∧ k ≤ 11000000
  let lens : List Nat := [0, 1, 2, 7, 8, 9] ++ lits.foldl (fun l k => l ++ [k.toNat - 1, k.toNat, k.toNat + 1]) []
  let mut out : List String := []
  let mut s := 20261116
  for t in [0:48] do
    let mut args : List Val := []
    let mut vs : List String := []
    let mut ns : List String := []
    -- in two cases out of three all arrays get the same length
    s := lcg s
    let common := lens.getD ((s / 65536) % lens.length) 0
    let same := t % 3 != 0
    for (ty, _) in f.params do
      s := lcg s
      let r := s / 65536
      match ty with
      | .int lo hi =>
        let cands : List Int := [lo, hi, lo + 1, hi - 1, (lo + hi) / 2] ++ (lits.filter fun k => lo ≤ k ∧ k ≤ hi)
        let v := cands.getD (r % cands.length) lo
        args := args ++ [.int v]; vs := vs ++ [toString v]; ns := ns ++ ["0"]
      | .arr n _ _ => args := args ++ [.arr (List.replicate n 0)]; vs := vs ++ ["0"]; ns := ns ++ [toString n]
      | .slice _ _ =>
        let n := if same then common else lens.getD (r % lens.length) 0
        args := args ++ [.arr (List.replicate n 0)]; vs := vs ++ ["0"]; ns := ns ++ [toString n]
      | .flt => args := args ++ [.flt 0.0]; vs := vs ++ ["0"]; ns := ns ++ ["0"]
      | .fslice =>
        let n := if same then common else lens.getD (r % lens.length) 0
        args := args ++ [.farr (List.replicate n 0.0)]; vs := vs ++ ["0"]; ns := ns ++ [toString n]
    let e := evalC f.req args
    out := out ++ [s!"\{\"v\": [{", ".intercalate vs}], \"n\": [{", ".intercalate ns}], \"expect\": {e}}"]
  pure out

/-- HAND-WRITTEN C appended to the generated file. Not derived from Tenon and not covered by anything
    but the tests in py/. -/
def helpersC : String := "
/* ==== hand-written helpers (not generated from Tenon terms) ==================================== */
#include <fenv.h>
#if defined(__SSE2__)
#include <xmmintrin.h>
#endif
/* 1 if the calling thread's floating-point environment is the one Tenon's float semantics assumes:
   rounding to nearest, and (x86) neither flush-to-zero nor denormals-are-zero. Libraries built with
   -ffast-math can switch FTZ/DAZ on for the whole process; subnormal results would then differ. */
int tn_fpenv_ok(void)
{
    if (fegetround() != FE_TONEAREST) return 0;
#if defined(__SSE2__)
    if (_mm_getcsr() & 0xE040u) return 0;       /* rounding control, FTZ (0x8000), DAZ (0x0040) */
#endif
    return 1;
}
/* For the binding's own test of tn_fpenv_ok: switches FTZ and DAZ on (1) or off (0). */
void tn_fpenv_set_for_test(int on)
{
#if defined(__SSE2__)
    unsigned csr = _mm_getcsr();
    _mm_setcsr(on ? (csr | 0x8040u) : (csr & ~0x8040u));
#else
    (void)on;
#endif
}
/* a * b + c exactly as this library was compiled. The binding calls it at import with operands for
   which a fused multiply-add gives another result, to notice a library built with contraction. */
double tn_probe_muladd(double a, double b, double c) { return a * b + c; }
"

def main (argv : List String) : IO Unit := do
  let out := argv.headD "."
  IO.FS.createDirAll out
  let mut c : List String := ["/* Generated by py/PyGen.lean from Tenon terms proved in Examples.lean, Ewma.lean and Sum8.lean.",
    "   No run-time checks: the callers (py/tenon_kernels.py) must establish the parameter types and the",
    "   requirement `req` of each function. Compile with -ffp-contract=off and without any fast-math option. */", fullPrelude]
  for (f, nm) in kernels do
    match emitProgram { prelude := false } [f] [nm] with
    | .ok src => c := c ++ [src]
    | .error e => throw (IO.userError s!"{nm.name}: {e}")
  IO.FS.writeFile s!"{out}/tenon_kernels.c" ("\n".intercalate c ++ helpersC)
  IO.FS.writeFile s!"{out}/tenon_kernels.json" ("{\n" ++ ",\n".intercalate (kernels.map fun (f, nm) => fnJson f nm) ++ "\n}\n")
  let tests := kernels.map fun (f, nm) => s!"  \"{nm.name}\": [\n    " ++ ",\n    ".intercalate (reqTests f) ++ "]"
  IO.FS.writeFile s!"{out}/tenon_req_tests.json" ("{\n" ++ ",\n".intercalate tests ++ "\n}\n")
  for (f, nm) in kernels do
    IO.println s!"{nm.name}: requires {condText nm.params f.req}"
