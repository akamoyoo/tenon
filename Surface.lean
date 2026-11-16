import Tenon
/-! A surface syntax for the kernel, as Lean macros. It resolves names to positions, picks the integer or
    the float form of each construct from the declared types, and builds the core term. It adds nothing
    to the trusted definitions: what is checked and proved is the core term it produces.

      kfn prefix_sum(x: slice(-1000000000, 1000000000), out: inout slice(-1000000000000000, 1000000000000000))
          -> int(0, 0)
        requires (len(x) == len(out) && len(x) <= 1000000)
      {
        let acc: int(-1000000000000000, 1000000000000000) = 0;
        for i upto len(x) invariant (-1000000000 * i ≤ acc ∧ acc ≤ 1000000000 * i) {
          acc = acc + x[i];
          out[i] = acc;
        }
      }

    Types: `int(lo, hi)`, `slice(lo, hi)` (integer array of run-time length), `f64`, `fslice`.
    `requires` is a decidable condition over integer parameters and `len(a)` (comparisons joined by `&&`,
    or `always`): an entry check can be generated from it. In `invariant`, a name stands for the variable's
    integer value and `name_len` for the length of an array; the loop variable stands for the number of
    completed iterations (`iter_` in a `loop`). `kvc f []` (Tenon.lean) proves a function written this way. -/

declare_syntax_cat kx
syntax num : kx
syntax scientific : kx
syntax ident : kx
syntax:65 kx:65 " + " kx:66 : kx
syntax:65 kx:65 " - " kx:66 : kx
syntax:70 kx:70 " * " kx:71 : kx
syntax:70 kx:70 " / " kx:71 : kx
syntax:75 "-" kx:75 : kx
syntax ident "[" kx "]" : kx
syntax "len" "(" ident ")" : kx
syntax "sqrt" "(" kx ")" : kx
syntax "fabs" "(" kx ")" : kx
syntax "sel" "(" kx " <= " kx "," kx "," kx ")" : kx
syntax "sel" "(" kx " < " kx "," kx "," kx ")" : kx
syntax "sel" "(" kx " == " kx "," kx "," kx ")" : kx
syntax "(" kx ")" : kx

declare_syntax_cat kty
syntax "int" "(" term "," term ")" : kty
syntax "slice" "(" term "," term ")" : kty
syntax "f64" : kty
syntax "fslice" : kty

declare_syntax_cat ks
syntax "let " ident ":" "int" "(" term "," term ")" " = " kx ";" : ks
syntax "let " ident ":" "f64" " = " kx ";" : ks
syntax ident " = " kx ";" : ks
syntax ident "[" kx "]" " = " kx ";" : ks
syntax "if " kx " <= " kx " {" ks* "}" " else " "{" ks* "}" : ks
syntax "if " kx " < " kx " {" ks* "}" " else " "{" ks* "}" : ks
syntax "for " ident " upto " kx " invariant " "(" term ")" " {" ks* "}" : ks
syntax "loop " "bound " num " invariant " "(" term ")" " {" ks* "}" : ks
syntax "loop " "upto " kx " invariant " "(" term ")" " {" ks* "}" : ks
declare_syntax_cat karg
syntax ident : karg
syntax "inout " ident : karg
syntax ident " = " "call" "[" num "]" "(" karg,* ")" ";" : ks
syntax ident " = " ident "(" karg,* ")" ";" : ks
syntax "break" ";" : ks

declare_syntax_cat kct
syntax num : kct
syntax ident : kct
syntax "len" "(" ident ")" : kct
syntax:65 kct:65 " + " kct:66 : kct
syntax:65 kct:65 " - " kct:66 : kct
syntax:70 kct:70 " * " kct:71 : kct
syntax "(" kct ")" : kct

declare_syntax_cat kc
syntax "always" : kc
syntax kct " <= " kct : kc
syntax kct " < " kct : kc
syntax kct " == " kct : kc
syntax:35 kc:36 " && " kc:35 : kc

declare_syntax_cat kparam
syntax ident ":" kty : kparam
syntax ident ":" "inout " kty : kparam

namespace Tenon.Surf
open Lean

/-- Kinds of names: integer, integer array, float, float array. -/
inductive Kind where | i | a | f | fa
  deriving BEq, Inhabited

/-- Names in scope, newest first. -/
abbrev Scope := Array (Name × Kind)

def find (sc : Scope) (x : Name) : Option (Nat × Kind) :=
  match sc.findIdx? (fun p => p.1 == x) with
  | some k => some (k, sc[k]!.2)
  | none => none

def need (sc : Scope) (x : TSyntax `ident) : MacroM (Nat × Kind) :=
  match find sc x.getId with
  | some r => pure r
  | none => Macro.throwErrorAt x s!"unknown name {x.getId}"

/-- Does the expression have float type? -/
partial def isFloat (sc : Scope) (e : TSyntax `kx) : Bool :=
  match e with
  | `(kx| $_:num) => false
  | `(kx| $_:scientific) => true
  | `(kx| $x:ident) => match find sc x.getId with | some (_, k) => k == .f | none => false
  | `(kx| $x:ident [ $_ ]) => match find sc x.getId with | some (_, k) => k == .fa | none => false
  | `(kx| len($_)) => false
  | `(kx| $a + $b) => isFloat sc a || isFloat sc b
  | `(kx| $a - $b) => isFloat sc a || isFloat sc b
  | `(kx| $a * $b) => isFloat sc a || isFloat sc b
  | `(kx| $a / $b) => isFloat sc a || isFloat sc b
  | `(kx| - $a) => isFloat sc a
  | `(kx| ($a)) => isFloat sc a
  | `(kx| sqrt($_)) => true
  | `(kx| fabs($_)) => true
  | `(kx| sel($_ <= $_, $t, $e)) => isFloat sc t || isFloat sc e
  | `(kx| sel($_ < $_, $t, $e)) => isFloat sc t || isFloat sc e
  | `(kx| sel($_ == $_, $t, $e)) => isFloat sc t || isFloat sc e
  | _ => false

/-- An integer expression. -/
partial def trI (sc : Scope) (e : TSyntax `kx) : MacroM (TSyntax `term) := do
  match e with
  | `(kx| $n:num) => `(Tenon.Expr.lit $n)
  | `(kx| $x:ident) => do
      let (k, kind) ← need sc x
      unless kind == .i do Macro.throwErrorAt x s!"{x.getId} is not an integer"
      `(Tenon.Expr.var $(quote k))
  | `(kx| $x:ident [ $i ]) => do
      let (k, kind) ← need sc x
      unless kind == .a do Macro.throwErrorAt x s!"{x.getId} is not an integer array"
      `(Tenon.Expr.idx $(quote k) $(← trI sc i))
  | `(kx| len($x)) => do let (k, _) ← need sc x; `(Tenon.Expr.len $(quote k))
  | `(kx| $a + $b) => do `(Tenon.Expr.add $(← trI sc a) $(← trI sc b))
  | `(kx| $a - $b) => do `(Tenon.Expr.sub $(← trI sc a) $(← trI sc b))
  | `(kx| $a * $b) => do `(Tenon.Expr.mul $(← trI sc a) $(← trI sc b))
  | `(kx| $a / $b) => do `(Tenon.Expr.div $(← trI sc a) $(← trI sc b))
  | `(kx| - $a) => do
      match a with
      | `(kx| $n:num) => `(Tenon.Expr.lit (-$n))
      | _ => `(Tenon.Expr.sub (Tenon.Expr.lit 0) $(← trI sc a))
  | `(kx| ($a)) => trI sc a
  | `(kx| sel($a <= $b, $t, $f)) => do `(Tenon.Expr.sel (Tenon.Expr.le $(← trI sc a) $(← trI sc b)) $(← trI sc t) $(← trI sc f))
  | `(kx| sel($a < $b, $t, $f)) => do `(Tenon.Expr.sel (Tenon.Expr.lt $(← trI sc a) $(← trI sc b)) $(← trI sc t) $(← trI sc f))
  | `(kx| sel($a == $b, $t, $f)) => do `(Tenon.Expr.sel (Tenon.Expr.eq $(← trI sc a) $(← trI sc b)) $(← trI sc t) $(← trI sc f))
  | _ => Macro.throwErrorAt e "not an integer expression"

/-- A float expression; integer subexpressions are converted. -/
partial def trF (sc : Scope) (e : TSyntax `kx) : MacroM (TSyntax `term) := do
  if !isFloat sc e then
    return ← `(Tenon.FExpr.ofInt $(← trI sc e))
  match e with
  | `(kx| $s:scientific) => `(Tenon.FExpr.lit $s)
  | `(kx| $x:ident) => do let (k, _) ← need sc x; `(Tenon.FExpr.var $(quote k))
  | `(kx| $x:ident [ $i ]) => do let (k, _) ← need sc x; `(Tenon.FExpr.idx $(quote k) $(← trI sc i))
  | `(kx| $a + $b) => do `(Tenon.FExpr.add $(← trF sc a) $(← trF sc b))
  | `(kx| $a - $b) => do `(Tenon.FExpr.sub $(← trF sc a) $(← trF sc b))
  | `(kx| $a * $b) => do `(Tenon.FExpr.mul $(← trF sc a) $(← trF sc b))
  | `(kx| $a / $b) => do `(Tenon.FExpr.div $(← trF sc a) $(← trF sc b))
  | `(kx| - $a) => do `(Tenon.FExpr.neg $(← trF sc a))
  | `(kx| ($a)) => trF sc a
  | `(kx| sqrt($a)) => do `(Tenon.FExpr.sqrt $(← trF sc a))
  | `(kx| fabs($a)) => do `(Tenon.FExpr.abs $(← trF sc a))
  | `(kx| sel($a <= $b, $t, $f)) => do
      if isFloat sc a || isFloat sc b then `(Tenon.FExpr.selLe $(← trF sc a) $(← trF sc b) $(← trF sc t) $(← trF sc f))
      else `(Tenon.FExpr.sel (Tenon.Expr.le $(← trI sc a) $(← trI sc b)) $(← trF sc t) $(← trF sc f))
  | `(kx| sel($a < $b, $t, $f)) => do
      if isFloat sc a || isFloat sc b then Macro.throwErrorAt e "`<` on floats is not available yet (use `<=`)"
      else `(Tenon.FExpr.sel (Tenon.Expr.lt $(← trI sc a) $(← trI sc b)) $(← trF sc t) $(← trF sc f))
  | `(kx| sel($a == $b, $t, $f)) => do
      if isFloat sc a || isFloat sc b then Macro.throwErrorAt e "`==` on floats is not available"
      else `(Tenon.FExpr.sel (Tenon.Expr.eq $(← trI sc a) $(← trI sc b)) $(← trF sc t) $(← trF sc f))
  | _ => Macro.throwErrorAt e "not a float expression"

/-- An invariant: every name in scope stands for its integer value, `name_len` for its length, and the
    given name for the number of completed iterations. -/
def mkInv (sc : Scope) (it : Name) (p : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut body : TSyntax `term := p
  for h : k in [0:sc.size] do
    let n := mkIdent sc[k].1
    let nlen := mkIdent (sc[k].1.appendAfter "_len")
    body ← `(let $n : Int := Tenon.geti env $(quote k); let $nlen : Int := Tenon.leni env $(quote k); $body)
  let itId := mkIdent it
  `(fun (_env0 : List Tenon.Val) (iter : Nat) (env : List Tenon.Val) => let $itId : Int := (iter : Int); $body)

/-- A block: a `let` scopes over the statements after it. -/
partial def trBlock (callees : Array Name) (sc : Scope) (ss : List (TSyntax `ks)) : MacroM (TSyntax `term) := do
  match ss with
  | [] => `(Tenon.Stmt.skip)
  | s :: rest =>
    let seq (t : TSyntax `term) : MacroM (TSyntax `term) := do
      if rest.isEmpty then pure t else `(Tenon.Stmt.seq $t $(← trBlock callees sc rest))
    match s with
    | `(ks| let $x:ident : int($lo, $hi) = $e ;) =>
        `(Tenon.Stmt.decl $lo $hi $(← trI sc e) $(← trBlock callees (#[(x.getId, Kind.i)] ++ sc) rest))
    | `(ks| let $x:ident : f64 = $e ;) =>
        `(Tenon.Stmt.fdecl $(← trF sc e) $(← trBlock callees (#[(x.getId, Kind.f)] ++ sc) rest))
    | `(ks| $x:ident = $e ;) => do
        let (k, kind) ← need sc x
        match kind with
        | .i => seq (← `(Tenon.Stmt.assign $(quote k) $(← trI sc e)))
        | .f => seq (← `(Tenon.Stmt.fassign $(quote k) $(← trF sc e)))
        | _ => Macro.throwErrorAt x "an array cannot be assigned as a whole"
    | `(ks| $x:ident [ $i ] = $e ;) => do
        let (k, kind) ← need sc x
        match kind with
        | .a => seq (← `(Tenon.Stmt.store $(quote k) $(← trI sc i) $(← trI sc e)))
        | .fa => seq (← `(Tenon.Stmt.fstore $(quote k) $(← trI sc i) $(← trF sc e)))
        | _ => Macro.throwErrorAt x s!"{x.getId} is not an array"
    | `(ks| if $a <= $b { $t* } else { $f* }) => do
        if isFloat sc a || isFloat sc b then
          seq (← `(Tenon.Stmt.fite $(← trF sc a) $(← trF sc b) $(← trBlock callees sc t.toList) $(← trBlock callees sc f.toList)))
        else
          seq (← `(Tenon.Stmt.ite $(← trI sc a) $(← trI sc b) $(← trBlock callees sc t.toList) $(← trBlock callees sc f.toList)))
    | `(ks| if $a < $b { $t* } else { $f* }) => do
        if isFloat sc a || isFloat sc b then
          Macro.throwErrorAt s "`<` on floats is not available yet (use `<=`): its meaning on NaN differs from the negation of `<=`"
        else
          seq (← `(Tenon.Stmt.ite $(← trI sc b) $(← trI sc a) $(← trBlock callees sc f.toList) $(← trBlock callees sc t.toList)))
    | `(ks| for $i:ident upto $e invariant ($p) { $body* }) => do
        seq (← `(Tenon.Stmt.forE $(← trI sc e) $(← mkInv sc i.getId p)
                  $(← trBlock callees (#[(i.getId, Kind.i)] ++ sc) body.toList)))
    | `(ks| loop bound $n:num invariant ($p) { $body* }) => do
        seq (← `(Tenon.Stmt.loopB $n $(← mkInv sc (Name.mkSimple "iter_") p) $(← trBlock callees sc body.toList)))
    | `(ks| loop upto $e invariant ($p) { $body* }) => do
        seq (← `(Tenon.Stmt.loopE $(← trI sc e) $(← mkInv sc (Name.mkSimple "iter_") p) $(← trBlock callees sc body.toList)))
    | `(ks| $x:ident = call[$f:num]($args,*) ;) => do
        let (k, kind) ← need sc x
        unless kind == .i do Macro.throwErrorAt x "the destination of a call is an integer variable"
        let mut as : Array (TSyntax `term) := #[]
        for a in args.getElems do
          match a with
          | `(karg| $y:ident) => do let (j, _) ← need sc y; as := as.push (← `(($(quote j), false)))
          | `(karg| inout $y:ident) => do let (j, _) ← need sc y; as := as.push (← `(($(quote j), true)))
          | _ => Macro.throwErrorAt a "an argument is a variable, or `inout` and a variable"
        let asList : Syntax.TSepArray `term "," := .ofElems as
        seq (← `(Tenon.Stmt.call $f [$asList,*] $(quote k)))
    | `(ks| $x:ident = $g:ident($args,*) ;) => do
        let (k, kind) ← need sc x
        unless kind == .i do Macro.throwErrorAt x "the destination of a call is an integer variable"
        let some fi := callees.findIdx? (· == g.getId)
          | Macro.throwErrorAt g s!"{g.getId} is not listed after `uses`"
        let mut as : Array (TSyntax `term) := #[]
        for a in args.getElems do
          match a with
          | `(karg| $y:ident) => do let (j, _) ← need sc y; as := as.push (← `(($(quote j), false)))
          | `(karg| inout $y:ident) => do let (j, _) ← need sc y; as := as.push (← `(($(quote j), true)))
          | _ => Macro.throwErrorAt a "an argument is a variable, or `inout` and a variable"
        let asList : Syntax.TSepArray `term "," := .ofElems as
        seq (← `(Tenon.Stmt.call $(quote fi) [$asList,*] $(quote k)))
    | `(ks| break ;) => seq (← `(Tenon.Stmt.brk))
    | _ => Macro.throwErrorAt s "unsupported statement"

partial def trCT (sc : Scope) (e : TSyntax `kct) : MacroM (TSyntax `term) := do
  match e with
  | `(kct| $n:num) => `(Tenon.CT.lit $n)
  | `(kct| $x:ident) => do let (k, _) ← need sc x; `(Tenon.CT.val $(quote k))
  | `(kct| len($x)) => do let (k, _) ← need sc x; `(Tenon.CT.len $(quote k))
  | `(kct| $a + $b) => do `(Tenon.CT.add $(← trCT sc a) $(← trCT sc b))
  | `(kct| $a - $b) => do `(Tenon.CT.sub $(← trCT sc a) $(← trCT sc b))
  | `(kct| $a * $b) => do `(Tenon.CT.mul $(← trCT sc a) $(← trCT sc b))
  | `(kct| ($a)) => trCT sc a
  | _ => Macro.throwErrorAt e "unsupported term in requires"

partial def trCond (sc : Scope) (c : TSyntax `kc) : MacroM (TSyntax `term) := do
  match c with
  | `(kc| always) => `(Tenon.Cond.tt)
  | `(kc| $a:kct <= $b:kct) => do `(Tenon.Cond.le $(← trCT sc a) $(← trCT sc b))
  | `(kc| $a:kct < $b:kct) => do `(Tenon.Cond.lt $(← trCT sc a) $(← trCT sc b))
  | `(kc| $a:kct == $b:kct) => do `(Tenon.Cond.eq $(← trCT sc a) $(← trCT sc b))
  | `(kc| $a:kc && $b:kc) => do `(Tenon.Cond.and $(← trCond sc a) $(← trCond sc b))
  | _ => Macro.throwErrorAt c "unsupported condition in requires"

def trParam (p : TSyntax `kparam) : MacroM (Name × Kind × TSyntax `term) := do
  match p with
  | `(kparam| $x:ident : int($lo, $hi)) => pure (x.getId, .i, ← `((Tenon.Ty.int $lo $hi, false)))
  | `(kparam| $x:ident : slice($lo, $hi)) => pure (x.getId, .a, ← `((Tenon.Ty.slice $lo $hi, false)))
  | `(kparam| $x:ident : f64) => pure (x.getId, .f, ← `((Tenon.Ty.flt, false)))
  | `(kparam| $x:ident : fslice) => pure (x.getId, .fa, ← `((Tenon.Ty.fslice, false)))
  | `(kparam| $x:ident : inout int($lo, $hi)) => pure (x.getId, .i, ← `((Tenon.Ty.int $lo $hi, true)))
  | `(kparam| $x:ident : inout slice($lo, $hi)) => pure (x.getId, .a, ← `((Tenon.Ty.slice $lo $hi, true)))
  | `(kparam| $x:ident : inout f64) => pure (x.getId, .f, ← `((Tenon.Ty.flt, true)))
  | `(kparam| $x:ident : inout fslice) => pure (x.getId, .fa, ← `((Tenon.Ty.fslice, true)))
  | _ => Macro.throwErrorAt p "unsupported parameter"

end Tenon.Surf

syntax "kfn " ident "(" kparam,* ")" " -> " "int" "(" term "," term ")" " requires " "(" kc ")" (" uses " "[" ident,* "]")? " {" ks* "}" : command

open Lean Tenon.Surf in
macro_rules
  | `(kfn $name:ident ( $ps:kparam,* ) -> int($rlo, $rhi) requires ($req:kc) $[uses [$us,*]]? { $body* }) => do
      let callees : Array Name := match us with | some u => u.getElems.map (·.getId) | none => #[]
      let mut psc : Scope := #[]
      let mut tys : Array (TSyntax `term) := #[]
      for p in ps.getElems do
        let (n, k, t) ← trParam p
        psc := psc.push (n, k)
        tys := tys.push t
      let sc : Scope := #[(Name.mkSimple "result", Kind.i)] ++ psc
      let tyList : Syntax.TSepArray `term "," := .ofElems tys
      `(def $name : Tenon.Fn where
          params := [$tyList,*]
          rlo := $rlo
          rhi := $rhi
          body := $(← trBlock callees sc body.toList)
          req := $(← trCond psc req)
          pre := fun _ => True
          post := fun _ _ _ => True)

/-! ## The running sum, written in the surface syntax -/

kfn prefix_sum(x: slice(-1000000000, 1000000000), out: inout slice(-1000000000000000, 1000000000000000))
    -> int(0, 0)
  requires (len(x) == len(out) && len(x) <= 1000000)
{
  let acc: int(-1000000000000000, 1000000000000000) = 0;
  for i upto len(x) invariant (-1000000000 * i ≤ acc ∧ acc ≤ 1000000000 * i) {
    acc = acc + x[i];
    out[i] = acc;
  }
}

#eval Tenon.evalFn [prefix_sum] 0 [.arr [1, 2, 3, 4, 5], .arr [0, 0, 0, 0, 0]]
#eval Tenon.evalFn [prefix_sum] 0 [.arr [1, 2, 3], .arr [0, 0]]

open Tenon in
theorem prefix_sumOk : FnOk [] prefix_sum := by
  kvc prefix_sum []

#print axioms prefix_sumOk

/-! ## Two more functions, each proved by the one tactic -/

kfn count_le(x: slice(-1000000000, 1000000000), p: int(-1000000000, 1000000000)) -> int(0, 10000000)
  requires (len(x) <= 10000000)
{
  let cnt: int(0, 10000000) = 0;
  for i upto len(x) invariant (0 ≤ cnt ∧ cnt ≤ i) {
    if x[i] <= p { cnt = cnt + 1; } else { }
  }
  result = cnt;
}

open Tenon in
theorem count_leOk : FnOk [] count_le := by
  kvc count_le []

-- Largest absolute difference between neighbours, a step in many screening rules.
kfn max_step(x: slice(-1000000000, 1000000000)) -> int(0, 2000000000)
  requires (always)
{
  let best: int(0, 2000000000) = 0;
  if len(x) < 2 { } else {
    for i upto len(x) - 1 invariant (0 ≤ best) {
      let d: int(-2000000000, 2000000000) = x[i + 1] - x[i];
      if d < 0 { d = 0 - d; } else { }
      if best < d { best = d; } else { }
    }
  }
  result = best;
}

open Tenon in
theorem max_stepOk : FnOk [] max_step := by
  kvc max_step []

#eval Tenon.evalFn [count_le] 0 [.arr [5, 1, 9, 3, 7], .int 4]
#eval Tenon.evalFn [max_step] 0 [.arr [5, 1, 9, 3, 7]]
#eval Tenon.evalFn [max_step] 0 [.arr []]
#print axioms count_leOk
#print axioms max_stepOk

/-! ## Binary search over a slice of any length, with no loop counter in the code.
    `loop upto e` must leave by `break`; `e` and `iter_` exist only for the proof. -/

kfn lower_bound(a: slice(-1000000000, 1000000000), p: int(-1000000000, 1000000000))
    -> int(0, 9223372036854775807)
  requires (len(a) <= 1000000000000)
{
  let lo: int(0, 9223372036854775807) = 0;
  let hi: int(0, 9223372036854775807) = len(a);
  loop upto len(a) + 1 invariant (lo ≤ hi ∧ hi ≤ a_len ∧ hi - lo ≤ a_len - iter_) {
    if hi <= lo { break; } else {
      let mid: int(0, 9223372036854775807) = lo + (hi - lo) / 2;
      if a[mid] < p { lo = mid + 1; } else { hi = mid; }
    }
  }
  result = lo;
}

open Tenon in
theorem lower_boundOk : FnOk [] lower_bound := by
  kvc lower_bound []

#eval Tenon.evalFn [lower_bound] 0 [.arr [1, 3, 5, 7, 9, 11, 13], .int 8]
#eval Tenon.evalFn [lower_bound] 0 [.arr [], .int 8]
#print axioms lower_boundOk

/-! ## Float kernels in the surface syntax -/

kfn ewma_s(x: fslice, alpha: f64, out: inout fslice) -> int(0, 0)
  requires (len(x) == len(out))
{
  let prev: f64 = 0.0;
  for i upto len(x) invariant (True) {
    prev = alpha * x[i] + (1.0 - alpha) * prev;
    out[i] = prev;
  }
}

open Tenon in
theorem ewma_sOk : FnOk [] ewma_s := by
  kvc ewma_s []

-- Mean and mean absolute deviation of a buffer, written to out[0] and out[1].
kfn mean_mad(x: fslice, out: inout fslice) -> int(0, 0)
  requires (2 <= len(out))
{
  let s: f64 = 0.0;
  for i upto len(x) invariant (True) {
    s = s + x[i];
  }
  let m: f64 = s / len(x);
  let d: f64 = 0.0;
  for j upto len(x) invariant (True) {
    d = d + fabs(x[j] - m);
  }
  out[0] = m;
  out[1] = d / len(x);
}

open Tenon in
theorem mean_madOk : FnOk [] mean_mad := by
  kvc mean_mad []

#eval Tenon.evalFn [ewma_s] 0 [.farr [1.0, 2.0, 3.0, 4.0], .flt 0.5, .farr [0.0, 0.0, 0.0, 0.0]]
#eval Tenon.evalFn [mean_mad] 0 [.farr [1.0, 2.0, 3.0, 6.0], .farr [0.0, 0.0]]
#print axioms ewma_sOk
#print axioms mean_madOk

/-! ## Select without a branch, and a call -/

-- Index of the largest element (first one on ties); -1... is avoided: requires a non-empty slice.
kfn argmax(x: slice(-1000000000, 1000000000)) -> int(0, 9223372036854775807)
  requires (1 <= len(x))
{
  let best: int(0, 9223372036854775807) = 0;
  let bv: int(-1000000000, 1000000000) = x[0];
  for i upto len(x) invariant (0 ≤ best ∧ best ≤ i ∧ best < x_len) {
    let v: int(-1000000000, 1000000000) = x[i];
    best = sel(v <= bv, best, i);
    bv = sel(v <= bv, bv, v);
  }
  result = best;
}

open Tenon in
theorem argmaxOk : FnOk [] argmax := by
  kvc argmax []

-- A caller: running sum in place, then the count of running sums not above a threshold.
kfn count_prefix_le(x: slice(-1000000000, 1000000000), tmp: inout slice(-1000000000000000, 1000000000000000),
                    p: int(-1000000000000000, 1000000000000000)) -> int(0, 1000000)
  requires (len(x) == len(tmp) && len(x) <= 1000000)
{
  let z: int(0, 0) = 0;
  z = call[0](x, inout tmp);
  let cnt: int(0, 1000000) = 0;
  for i upto len(tmp) invariant (0 ≤ cnt ∧ cnt ≤ i) {
    if tmp[i] <= p { cnt = cnt + 1; } else { }
  }
  result = cnt;
}

open Tenon in
theorem count_prefix_leOk : FnOk [prefix_sum] count_prefix_le := by
  kvc count_prefix_le [prefix_sum]

#eval Tenon.evalFn [argmax] 0 [.arr [3, 9, 2, 9, 1]]
#eval Tenon.evalFn [count_prefix_le, prefix_sum] 0 [.arr [1, 2, 3, 4], .arr [0, 0, 0, 0], .int 5]
#print axioms argmaxOk
#print axioms count_prefix_leOk

/-! ## Calls by name: `uses [g, h]` lists the callees; the function is then checked against that list. -/

kfn count_prefix_le2(x: slice(-1000000000, 1000000000), tmp: inout slice(-1000000000000000, 1000000000000000),
                     p: int(-1000000000000000, 1000000000000000)) -> int(0, 1000000)
  requires (len(x) == len(tmp) && len(x) <= 1000000)
  uses [prefix_sum]
{
  let z: int(0, 0) = 0;
  z = prefix_sum(x, inout tmp);
  let cnt: int(0, 1000000) = 0;
  for i upto len(tmp) invariant (0 ≤ cnt ∧ cnt ≤ i) {
    if tmp[i] <= p { cnt = cnt + 1; } else { }
  }
  result = cnt;
}

open Tenon in
theorem count_prefix_le2Ok : FnOk [prefix_sum] count_prefix_le2 := by
  kvc count_prefix_le2 [prefix_sum]

/-- The whole two-function program is checked, so `prog_sound` applies to it. -/
theorem prog2Ok : Tenon.ProgOk [count_prefix_le2, prefix_sum] := by
  refine ⟨by simp [count_prefix_le2, Tenon.inI64], by simp [count_prefix_le2, Tenon.tysI64, Tenon.inI64, Tenon.condWf, Tenon.ctWf],
    count_prefix_le2Ok, ?_⟩
  exact ⟨by simp [prefix_sum, Tenon.inI64], by simp [prefix_sum, Tenon.tysI64, Tenon.inI64, Tenon.condWf, Tenon.ctWf], prefix_sumOk, trivial⟩

#eval Tenon.evalFn [count_prefix_le2, prefix_sum] 0 [.arr [1, 2, 3, 4], .arr [0, 0, 0, 0], .int 5]
#print axioms prog2Ok
