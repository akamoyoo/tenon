import Tenon
/-! Sum of a float slice in a fixed order: eight running sums over the elements with index ≡ k (mod 8),
    then the tail one by one into the first, then a fixed pairwise combination. The order is part of the
    function, so the result is the same on every machine and build, and the eight sums can be computed with
    vector instructions without the compiler having to reorder anything.
      sum8(x: in [f64], out: inout [f64])  requires len(out) >= 1     -- result in out[0]
    Written in the language itself: no kernel support was needed. -/
namespace Tenon
open Stmt

def sInv (_ : List Val) (_ : Nat) (_ : List Val) : Prop := True

def sum8 : Fn where
  params := [(.fslice, false), (.fslice, true)]
  rlo := 0
  rhi := 0
  body :=                                                -- [res, x, out]
    fdecl (.lit 0.0) (fdecl (.lit 0.0) (fdecl (.lit 0.0) (fdecl (.lit 0.0) (
    fdecl (.lit 0.0) (fdecl (.lit 0.0) (fdecl (.lit 0.0) (fdecl (.lit 0.0) (   -- [a7, ..., a0, res, x, out]
    decl 0 1152921504606846975 (.div (.len 9) (.lit 8)) (     -- n8 = len(x) / 8   [n8, a7..a0, res, x, out]
      seq
        (forE (.var 0) sInv (                            -- [i, n8, a7..a0, res, x, out]
          seq (fassign 9 (.add (.var 9) (.idx 11 (.add (.mul (.lit 8) (.var 0)) (.lit 0)))))
          (seq (fassign 8 (.add (.var 8) (.idx 11 (.add (.mul (.lit 8) (.var 0)) (.lit 1)))))
          (seq (fassign 7 (.add (.var 7) (.idx 11 (.add (.mul (.lit 8) (.var 0)) (.lit 2)))))
          (seq (fassign 6 (.add (.var 6) (.idx 11 (.add (.mul (.lit 8) (.var 0)) (.lit 3)))))
          (seq (fassign 5 (.add (.var 5) (.idx 11 (.add (.mul (.lit 8) (.var 0)) (.lit 4)))))
          (seq (fassign 4 (.add (.var 4) (.idx 11 (.add (.mul (.lit 8) (.var 0)) (.lit 5)))))
          (seq (fassign 3 (.add (.var 3) (.idx 11 (.add (.mul (.lit 8) (.var 0)) (.lit 6)))))
          ((fassign 2 (.add (.var 2) (.idx 11 (.add (.mul (.lit 8) (.var 0)) (.lit 7))))))))))))))
      (seq
        (forE (.sub (.len 10) (.mul (.lit 8) (.var 0))) sInv (   -- tail          [j, n8, a7..a0, res, x, out]
          fassign 9 (.add (.var 9) (.idx 11 (.add (.mul (.lit 8) (.var 1)) (.var 0))))))
        (fstore 11 (.lit 0)
          (.add (.add (.add (.var 8) (.var 7)) (.add (.var 6) (.var 5)))
                (.add (.add (.var 4) (.var 3)) (.add (.var 2) (.var 1)))))))))))))))
  req := .le (.lit 1) (.len 1)
  pre := fun _ => True
  post := fun _ _ _ => True

set_option maxRecDepth 8000 in
theorem sum8Ok : FnOk [] sum8 := by
  kvc sum8 [sInv]

#eval evalFn [sum8] 0 [.farr [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0], .farr [0.0]]
#eval evalFn [sum8] 0 [.farr [], .farr [0.0]]
#print axioms sum8Ok
end Tenon
