import Tenon
import Emit
import Examples
/-! Writes the generated C for the float benchmark:  benchgen <outdir>
      gen_ewma.c, gen_sum8.c, gen_dot.c, gen_rmean.c, gen_rstd.c     the proved kernels, as emitted
      gen_rvar{,_plain,_lazy,_mask}.c    rolling_var in the four C forms of `selLe`               proved
      gen_clip{,_plain,_lazy,_mask}.c    clip: two nested `selLe` per element                      NOT proved
      gen_fwhere{,_plain,_lazy,_mask}.c  fwhere: float `sel` on an integer condition               NOT proved
      gen_psum_w.c                       prefixSumW (integer; for the Python entry-check timing)   proved -/
open Tenon Tenon.Emit Tenon.Examples Stmt Expr

/-- clip(x: fslice, lo: f64, hi: f64, out: inout fslice): out[i] = x[i] ≤ lo ? lo : (hi ≤ x[i] ? hi : x[i]).
    A NaN element stays NaN. Stuck unless len(out) ≥ len(x).  Body [i, res, x, lo, hi, out]. -/
def clip : Fn where
  params := [(.fslice, false), (.flt, false), (.flt, false), (.fslice, true)]
  rlo := 0
  rhi := 0
  body := forE (.len 1) triv (
    fstore 5 (var 0) (.selLe (.idx 2 (var 0)) (.var 3) (.var 3)
                        (.selLe (.var 4) (.idx 2 (var 0)) (.var 4) (.idx 2 (var 0)))))
  req := .le (.len 0) (.len 3)
  pre := tpre
  post := tpost

/-- fwhere(c: [int], a: fslice, b: fslice, out: inout fslice): out[i] = c[i] ≠ 0 ? a[i] : b[i].
    Body [i, res, c, a, b, out]. -/
def fwhere : Fn where
  params := [(.slice (-1) 1, false), (.fslice, false), (.fslice, false), (.fslice, true)]
  rlo := 0
  rhi := 0
  body := forE (.len 1) triv (fstore 5 (var 0) (.sel (idx 2 (var 0)) (.idx 3 (var 0)) (.idx 4 (var 0))))
  req := .tt
  pre := tpre
  post := tpost

def write (path : String) (opts : Options) (fns : List Fn) (names : List FnNames) : IO Unit :=
  match emitProgram opts fns names with
  | .ok src => IO.FS.writeFile path src
  | .error e => throw (IO.userError s!"{path}: {e}")

def main (argv : List String) : IO Unit := do
  let out := argv.headD "."
  IO.FS.createDirAll out
  write s!"{out}/gen_ewma.c" {} [ewma] [{ ewmaNames with name := "gen_ewma" }]
  write s!"{out}/gen_sum8.c" {} [Tenon.sum8] [{ sum8Names with name := "gen_sum8" }]
  write s!"{out}/gen_dot.c" {} [dot] [{ dotNames with name := "gen_dot" }]
  write s!"{out}/gen_rmean.c" {} [rolling_mean] [{ rollingMeanNames with name := "gen_rmean" }]
  write s!"{out}/gen_rstd.c" {} [rolling_std] [{ rollingStdNames with name := "gen_rstd" }]
  write s!"{out}/gen_psum_w.c" {} [prefixSumW] [{ prefixSumNames with name := "gen_psum_w" }]
  for (sfx, form) in [("", SelForm.eager), ("_plain", SelForm.eagerPlain), ("_lazy", SelForm.lazy), ("_mask", SelForm.mask)] do
    write s!"{out}/gen_rvar{sfx}.c" { selForm := form } [rollingVar] [{ rollingVarNames with name := s!"gen_rvar{sfx}" }]
    write s!"{out}/gen_clip{sfx}.c" { selForm := form } [clip] [{ name := s!"gen_clip{sfx}", params := ["x", "lo", "hi", "out"], locals := ["i"] }]
    write s!"{out}/gen_fwhere{sfx}.c" { selForm := form } [fwhere] [{ name := s!"gen_fwhere{sfx}", params := ["c", "a", "b", "out"], locals := ["i"] }]
