import Tenon
/-! An exponentially weighted moving average over caller-supplied float buffers:
      ewma(x: in [f64], alpha: f64, out: inout [f64])  requires len(x) == len(out)
      { prev = 0.0; for i in 0..len(x) { prev = alpha * x[i] + (1.0 - alpha) * prev; out[i] = prev } }
    The loop invariant is `True`: that `x` is unchanged and `out` keeps its length is supplied by the kernel,
    and float arithmetic cannot be stuck. What is proved: no index is out of range, for every length. -/
namespace Tenon
open Stmt

def ewmaInv (_ : List Val) (_ : Nat) (_ : List Val) : Prop := True

def ewma : Fn where
  params := [(.fslice, false), (.flt, false), (.fslice, true)]
  rlo := 0
  rhi := 0
  body :=
    fdecl (.lit 0.0) (                                   -- prev = 0.0        [prev, res, x, alpha, out]
      forE (.len 2) ewmaInv (                            --                   [i, prev, res, x, alpha, out]
        seq (fassign 1 (.add (.mul (.var 4) (.idx 3 (.var 0)))
                             (.mul (.sub (.lit 1.0) (.var 4)) (.var 1))))
            (fstore 5 (.var 0) (.var 1))))
  req := .eq (.len 0) (.len 2)
  pre := fun _ => True
  post := fun _ _ _ => True

theorem ewmaOk : FnOk [] ewma := by
  kvc ewma [ewmaInv]

#eval evalFn [ewma] 0 [.farr [1.0, 2.0, 3.0, 4.0], .flt 0.5, .farr [0.0, 0.0, 0.0, 0.0]]
#eval evalFn [ewma] 0 [.farr [1.0, 2.0, 3.0], .flt 0.5, .farr [0.0]]      -- outside the precondition: stuck
#print axioms ewmaOk
end Tenon
