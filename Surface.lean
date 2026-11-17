import Tenon
/-! A surface syntax for the kernel, as Lean macros. It resolves names to positions, picks the integer or
    the float form of each construct from the declared types, and builds the core term. It adds nothing
    to the trusted definitions: what is checked and proved is the core term it produces.

      kfn prefix_sum(x: slice(-1000000000, 1000000000), out: inout slice(-1000000000000000, 1000000000000000))
          -> int(0, 0)
        requires (len(x) == len(out) && len(x) <= 1000000)
      {
        let acc: int(-1000000000000000, 1000000000000000) = 0;
        for i upto len(x) invariant (-1000000000 * i <= acc && acc <= 1000000000 * i) {
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

declare_syntax_cat kct
syntax num : kct
syntax ident : kct
syntax "len" "(" ident ")" : kct
syntax ident "[" kct "]" : kct
syntax "sum" "(" ident "," kct "," kct ")" : kct
syntax ident "(" kct "," kct ")" : kct
syntax:65 kct:65 " + " kct:66 : kct
syntax:65 kct:65 " - " kct:66 : kct
syntax:70 kct:70 " * " kct:71 : kct
syntax "(" kct ")" : kct
syntax:75 "-" kct:75 : kct

declare_syntax_cat kc
syntax "always" : kc
syntax kct " <= " kct : kc
syntax kct " < " kct : kc
syntax kct " == " kct : kc
syntax kct " >= " kct : kc
syntax kct " > " kct : kc
syntax:35 kc:36 " && " kc:35 : kc
syntax:30 kc:31 " || " kc:30 : kc
syntax:max "forall " ident " in " kct ".." kct ": " kc : kc
syntax "(" kc ")" : kc

declare_syntax_cat ks
syntax "let " ident ":" "int" "(" term "," term ")" " = " kx ";" : ks
syntax "let " ident ":" "f64" " = " kx ";" : ks
syntax ident " = " kx ";" : ks
syntax ident "[" kx "]" " = " kx ";" : ks
syntax "if " kx " <= " kx " {" ks* "}" " else " "{" ks* "}" : ks
syntax "if " kx " < " kx " {" ks* "}" " else " "{" ks* "}" : ks
declare_syntax_cat kinvc
syntax " invariant " "(" kc ")" : kinvc
syntax " invariant_lean " "(" term ")" : kinvc
syntax "for " ident " upto " kx kinvc " {" ks* "}" : ks
syntax "loop " "bound " num kinvc " {" ks* "}" : ks
syntax "loop " "upto " kx kinvc " {" ks* "}" : ks
declare_syntax_cat karg
syntax ident : karg
syntax "inout " ident : karg
syntax ident " = " "call" "[" num "]" "(" karg,* ")" ";" : ks
syntax ident " = " ident "(" karg,* ")" ";" : ks
syntax "parallel " "for " ident " upto " kx " {" ident "[" ident "]" " = " ident "(" ident,* ")" ";" "}" : ks
syntax "break" ";" : ks

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
  let envId := mkIdent `env
  let mut body : TSyntax `term := p
  for h : k in [0:sc.size] do
    let n := mkIdent sc[k].1
    let nlen := mkIdent (sc[k].1.appendAfter "_len")
    body ← `(let $n : Int := Tenon.geti $envId $(quote k); let $nlen : Int := Tenon.leni $envId $(quote k); $body)
  let itId := mkIdent it
  let iterId := mkIdent (Name.mkSimple "iter_")
  `(fun (_env0 : List Tenon.Val) (iter : Nat) ($envId : List Tenon.Val) =>
      let $iterId : Int := (iter : Int); let $itId : Int := (iter : Int); $body)

/-- How names of a condition are read: a name in the list stands for a variable of `lst` at a position;
    any other name (the loop variable, `iter_`, `result`, a quantified variable) is a Lean name bound
    around the condition. -/
abbrev Resolver := Name → Option (TSyntax `term × Nat)

/-- A term of an invariant or postcondition, as a Lean integer term. -/
partial def trInvT (res : Resolver) (e : TSyntax `kct) : MacroM (TSyntax `term) := do
  match e with
  | `(kct| $n:num) => `(($n : Int))
  | `(kct| $x:ident) => do
      match res x.getId with
      | some (lst, k) => `(Tenon.geti $lst $(quote k))
      | none => `($x)
  | `(kct| len($x)) => do
      match res x.getId with
      | some (lst, k) => `(Tenon.leni $lst $(quote k))
      | none => Macro.throwErrorAt x s!"unknown array {x.getId}"
  | `(kct| $x:ident [ $t ]) => do
      match res x.getId with
      | some (lst, k) => `(Tenon.geta $lst $(quote k) $(← trInvT res t))
      | none => Macro.throwErrorAt x s!"unknown array {x.getId}"
  | `(kct| sum($x, $lo, $hi)) => do
      match res x.getId with
      | some (lst, k) => `(Tenon.sumA (Tenon.getl $lst $(quote k)) $(← trInvT res lo) $(← trInvT res hi))
      | none => Macro.throwErrorAt x s!"unknown array {x.getId}"
  | `(kct| $f:ident ($a, $b)) => do
      if f.getId == `max then `(Max.max $(← trInvT res a) $(← trInvT res b))
      else if f.getId == `min then `(Min.min $(← trInvT res a) $(← trInvT res b))
      else Macro.throwErrorAt f s!"unknown function {f.getId} (known: max, min, sum, len)"
  | `(kct| $a + $b) => do `($(← trInvT res a) + $(← trInvT res b))
  | `(kct| $a - $b) => do `($(← trInvT res a) - $(← trInvT res b))
  | `(kct| $a * $b) => do `($(← trInvT res a) * $(← trInvT res b))
  | `(kct| - $a) => do `(- $(← trInvT res a))
  | `(kct| ($a)) => do `(($(← trInvT res a)))
  | _ => Macro.throwErrorAt e "unsupported term in a condition"

partial def trInvC (res : Resolver) (c : TSyntax `kc) : MacroM (TSyntax `term) := do
  match c with
  | `(kc| always) => `(True)
  | `(kc| $a:kct <= $b:kct) => do `($(← trInvT res a) ≤ $(← trInvT res b))
  | `(kc| $a:kct < $b:kct) => do `($(← trInvT res a) < $(← trInvT res b))
  | `(kc| $a:kct == $b:kct) => do `($(← trInvT res a) = $(← trInvT res b))
  | `(kc| $a:kct >= $b:kct) => do `($(← trInvT res b) ≤ $(← trInvT res a))
  | `(kc| $a:kct > $b:kct) => do `($(← trInvT res b) < $(← trInvT res a))
  | `(kc| $a:kc && $b:kc) => do `($(← trInvC res a) ∧ $(← trInvC res b))
  | `(kc| $a:kc || $b:kc) => do `($(← trInvC res a) ∨ $(← trInvC res b))
  | `(kc| ($a:kc)) => trInvC res a
  | `(kc| forall $j:ident in $lo .. $hi : $b:kc) => do
      let res' : Resolver := fun n => if n == j.getId then none else res n
      `(∀ $j:ident : Int, $(← trInvT res lo) ≤ $j → $j < $(← trInvT res hi) → $(← trInvC res' b))
  | _ => Macro.throwErrorAt c "unsupported condition"

/-- The resolver of a loop invariant: the names in scope, except the loop variable and `iter_`. -/
def scopeRes (sc : Scope) (it : Name) : Resolver := fun n =>
  if n == it || n == Name.mkSimple "iter_" then none
  else match find sc n with
    | some (k, _) => some (mkIdent `env, k)
    | none => none

/-- The invariant clause of a loop, in either form. -/
def trInvClause (sc : Scope) (it : Name) (c : TSyntax `kinvc) : MacroM (TSyntax `term) := do
  match c with
  | `(kinvc| invariant ($p:kc)) => do mkInv sc it (← trInvC (scopeRes sc it) p)
  | `(kinvc| invariant_lean ($p:term)) => mkInv sc it p
  | _ => Macro.throwErrorAt c "unsupported invariant clause"

/-- The label of a statement: its byte position in the file. The `tenon` command turns the position into
    a line of the source file and prints that line. -/
def label (sc : Scope) (s : Syntax) : TSyntax `term :=
  let pos := match s.getPos? with | some p => p.byteIdx | none => 0
  let names := ",".intercalate (sc.toList.map (fun p => toString p.1))
  quote s!"@{pos}|{names}"

/-- The body of a loop, followed by a labelled no-op: the obligation "the invariant holds again" then
    carries a label that says so. -/
def withInvNote (sc : Scope) (loopStx : Syntax) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let pos := match loopStx.getPos? with | some p => p.byteIdx | none => 0
  let names := ",".intercalate (sc.toList.map (fun p => toString p.1))
  let lbl : TSyntax `term := quote s!"@{pos}|{names}|inv"
  `(Tenon.Stmt.seq $body (Tenon.Stmt.note $lbl Tenon.Stmt.skip))

/-- A block: a `let` scopes over the statements after it. -/
partial def trBlock (callees : Array Name) (sc : Scope) (ss : List (TSyntax `ks)) : MacroM (TSyntax `term) := do
  match ss with
  | [] => `(Tenon.Stmt.skip)
  | s :: rest =>
    let lbl := label sc s
    let seq (t : TSyntax `term) : MacroM (TSyntax `term) := do
      if rest.isEmpty then `(Tenon.Stmt.note $lbl $t) else `(Tenon.Stmt.seq (Tenon.Stmt.note $lbl $t) $(← trBlock callees sc rest))
    match s with
    | `(ks| let $x:ident : int($lo, $hi) = $e ;) =>
        `(Tenon.Stmt.note $lbl (Tenon.Stmt.decl $lo $hi $(← trI sc e) $(← trBlock callees (#[(x.getId, Kind.i)] ++ sc) rest)))
    | `(ks| let $x:ident : f64 = $e ;) =>
        `(Tenon.Stmt.note $lbl (Tenon.Stmt.fdecl $(← trF sc e) $(← trBlock callees (#[(x.getId, Kind.f)] ++ sc) rest)))
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
    | `(ks| for $i:ident upto $e $c:kinvc { $body* }) => do
        seq (← `(Tenon.Stmt.forE $(← trI sc e) $(← trInvClause sc i.getId c)
                  $(← withInvNote (#[(i.getId, Kind.i)] ++ sc) s (← trBlock callees (#[(i.getId, Kind.i)] ++ sc) body.toList))))
    | `(ks| loop bound $n:num $c:kinvc { $body* }) => do
        seq (← `(Tenon.Stmt.loopB $n $(← trInvClause sc (Name.mkSimple "iter_") c) $(← withInvNote sc s (← trBlock callees sc body.toList))))
    | `(ks| loop upto $e $c:kinvc { $body* }) => do
        seq (← `(Tenon.Stmt.loopE $(← trI sc e) $(← trInvClause sc (Name.mkSimple "iter_") c) $(← withInvNote sc s (← trBlock callees sc body.toList))))
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
    | `(ks| parallel for $i:ident upto $e { $o:ident [ $j:ident ] = $g:ident ( $as,* ) ; }) => do
        if j.getId != i.getId then
          Macro.throwErrorAt j s!"a parallel loop writes element `{i.getId}` of its output, not `{j.getId}`"
        let elems := as.getElems
        if elems.size == 0 || elems.back!.getId != i.getId then
          Macro.throwErrorAt g s!"the last argument of `{g.getId}` must be the loop variable `{i.getId}`"
        let some fi := callees.findIdx? (· == g.getId)
          | Macro.throwErrorAt g s!"{g.getId} is not listed after `uses`"
        let (ko, kind) ← need sc o
        let mut idxs : Array (TSyntax `term) := #[]
        for a in elems.pop do
          if a.getId == o.getId then
            Macro.throwErrorAt a s!"the output `{o.getId}` of a parallel loop cannot also be an argument"
          let (k, _) ← need sc a
          idxs := idxs.push (quote k)
        let idxList : Syntax.TSepArray `term "," := .ofElems idxs
        match kind with
        | .a => seq (← `(Tenon.Stmt.pmap $(quote fi) [$idxList,*] $(← trI sc e) $(quote ko)))
        | .fa => seq (← `(Tenon.Stmt.pmapF $(quote fi) [$idxList,*] $(← trI sc e) $(quote ko)))
        | _ => Macro.throwErrorAt o s!"the output `{o.getId}` of a parallel loop must be a slice"
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
  | `(kct| $x:ident [ $_ ]) => Macro.throwErrorAt x "array elements are not allowed in `requires` (yet)"
  | `(kct| sum($x, $_, $_)) => Macro.throwErrorAt x "sums are not allowed in `requires` (yet)"
  | `(kct| $f:ident ($_, $_)) => Macro.throwErrorAt f s!"{f.getId} is not allowed in `requires` (yet)"
  | `(kct| - $a) => do `(Tenon.CT.sub (Tenon.CT.lit 0) $(← trCT sc a))
  | _ => Macro.throwErrorAt e "unsupported term in requires"

partial def trCond (sc : Scope) (c : TSyntax `kc) : MacroM (TSyntax `term) := do
  match c with
  | `(kc| always) => `(Tenon.Cond.tt)
  | `(kc| $a:kct <= $b:kct) => do `(Tenon.Cond.le $(← trCT sc a) $(← trCT sc b))
  | `(kc| $a:kct < $b:kct) => do `(Tenon.Cond.lt $(← trCT sc a) $(← trCT sc b))
  | `(kc| $a:kct == $b:kct) => do `(Tenon.Cond.eq $(← trCT sc a) $(← trCT sc b))
  | `(kc| $a:kct >= $b:kct) => do `(Tenon.Cond.le $(← trCT sc b) $(← trCT sc a))
  | `(kc| $a:kct > $b:kct) => do `(Tenon.Cond.lt $(← trCT sc b) $(← trCT sc a))
  | `(kc| $a:kc && $b:kc) => do `(Tenon.Cond.and $(← trCond sc a) $(← trCond sc b))
  | `(kc| ($a:kc)) => trCond sc a
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

syntax "kfn " ident "(" kparam,* ")" " -> " "int" "(" term "," term ")" " requires " "(" kc ")" (" ensures " "(" kc ")")? (" uses " "[" ident,* "]")? " {" ks* "}" : command

open Lean Tenon.Surf in
macro_rules
  | `(kfn $name:ident ( $ps:kparam,* ) -> int($rlo, $rhi) requires ($req:kc) $[ensures ($ens:kc)]? $[uses [$us,*]]? { $body* }) => do
      let callees : Array Name := match us with | some u => u.getElems.map (·.getId) | none => #[]
      let mut psc : Scope := #[]
      let mut tys : Array (TSyntax `term) := #[]
      let mut inouts : Array Bool := #[]
      for p in ps.getElems do
        let (n, k, t) ← trParam p
        psc := psc.push (n, k)
        tys := tys.push t
        inouts := inouts.push (match p with | `(kparam| $_:ident : inout $_:kty) => true | _ => false)
      let sc : Scope := #[(Name.mkSimple "result", Kind.i)] ++ psc
      let tyList : Syntax.TSepArray `term "," := .ofElems tys
      -- the postcondition: an inout parameter stands for its value at return, any other for its value
      -- at entry; `result` for the result
      let argsId := mkIdent `args
      let outsId := mkIdent `outs
      let resultId := mkIdent (Name.mkSimple "result")
      let pres : Resolver := fun n =>
        match psc.findIdx? (·.1 == n) with
        | some k => some (if inouts[k]! then outsId else argsId, k)
        | none => none
      let post ← match ens with
        | some e => do `(fun ($argsId : List Tenon.Val) ($resultId : Int) ($outsId : List Tenon.Val) => $(← trInvC pres e))
        | none => `(fun _ _ _ => True)
      -- the end of the body carries a label, so that a failed postcondition is reported as such
      let body0 ← trBlock callees sc body.toList
      let body1 ← match ens with
        | some e => do
            let pos := match e.raw.getPos? with | some p => p.byteIdx | none => 0
            let names := ",".intercalate (sc.toList.map (fun p => toString p.1))
            let lbl : TSyntax `term := quote s!"@{pos}|{names}|ensures"
            `(Tenon.Stmt.seq $body0 (Tenon.Stmt.note $lbl Tenon.Stmt.skip))
        | none => pure body0
      `(def $name : Tenon.Fn where
          params := [$tyList,*]
          rlo := $rlo
          rhi := $rhi
          body := $body1
          req := $(← trCond psc req)
          pre := fun _ => True
          post := $post)
