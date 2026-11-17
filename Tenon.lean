import Lean
/-! Tenon = K4 plus floating point: `f64` scalars and slices, float expressions (`FExpr`), and the
    statements that assign, store, declare and compare them. Float operations are Lean's `Float`
    (IEEE-754 binary64); they are never stuck, so the only obligations they add are index bounds.
    Below, the K4 text. K4 = K3 plus slices: arrays whose length is known only at run time (`Ty.slice`), `len a`, and a
    counted loop whose bound is an expression (`forE`). A slice is what a caller's buffer is.
    Below, the K3 text. K3 = K2 with a typing context. Every variable has a type (an integer range, or an array with a length
    and an element range). "The environment has its types" is an invariant that every statement preserves,
    so obligations may assume the declared ranges and shapes without the user restating them in loop
    invariants, and array elements carry their range in the array's type. -/

namespace Tenon

def inI64 (x : Int) : Prop := -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807
instance (x : Int) : Decidable (inI64 x) := by unfold inI64; infer_instance

inductive Val where
  | int : Int → Val
  | arr : List Int → Val
  | flt : Float → Val
  | farr : List Float → Val
  deriving Repr

inductive Ty where
  | int : Int → Int → Ty                       -- lo..=hi
  | arr : Nat → Int → Int → Ty                 -- length, and the range of every element
  | slice : Int → Int → Ty                     -- any length that fits 64 bits, and the element range
  | flt : Ty                                   -- f64
  | fslice : Ty                                -- f64 array of run-time length
  deriving DecidableEq

def Val.has : Val → Ty → Bool
  | .int v, .int lo hi => decide (lo ≤ v ∧ v ≤ hi)
  | .arr l, .arr n lo hi => l.length == n && l.all (fun x => decide (lo ≤ x ∧ x ≤ hi))
  | .arr l, .slice lo hi => decide ((l.length : Int) ≤ 9223372036854775807) && l.all (fun x => decide (lo ≤ x ∧ x ≤ hi))
  | .flt _, .flt => true
  | .farr l, .fslice => decide ((l.length : Int) ≤ 9223372036854775807)
  | _, _ => false

def hasAll : List Ty → List Val → Bool
  | [], [] => true
  | t :: ts, v :: vs => v.has t && hasAll ts vs
  | _, _ => false

inductive Expr where
  | lit : Int → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr                   -- defined for dividend ≥ 0 and divisor > 0
  | idx : Nat → Expr → Expr
  | len : Nat → Expr                           -- the length of an array or slice
  | le  : Expr → Expr → Expr                   -- 1 if a ≤ b, else 0
  | lt  : Expr → Expr → Expr                   -- 1 if a < b, else 0
  | eq  : Expr → Expr → Expr                   -- 1 if a = b, else 0
  | sel : Expr → Expr → Expr → Expr            -- c ≠ 0 ? t : e; both t and e are evaluated (no branch)

/-- Float-valued expressions. Conditions and indices are integer expressions. -/
inductive FExpr where
  | lit   : Float → FExpr
  | var   : Nat → FExpr
  | add   : FExpr → FExpr → FExpr
  | sub   : FExpr → FExpr → FExpr
  | mul   : FExpr → FExpr → FExpr
  | div   : FExpr → FExpr → FExpr
  | idx   : Nat → Expr → FExpr                 -- a[e] for a float slice
  | ofInt : Expr → FExpr
  | sel   : Expr → FExpr → FExpr → FExpr       -- c ≠ 0 ? t : e, both evaluated
  | neg   : FExpr → FExpr
  | abs   : FExpr → FExpr
  | sqrt  : FExpr → FExpr
  | selLe : FExpr → FExpr → FExpr → FExpr → FExpr   -- a ≤ b ? t : e, all evaluated (false when a or b is NaN)

inductive Stmt where
  | skip   : Stmt
  | seq    : Stmt → Stmt → Stmt
  | assign : Nat → Expr → Stmt                 -- x = e; the value must be in x's type
  | store  : Nat → Expr → Expr → Stmt          -- a[i] = e; i in range, the value in the element range
  | ite    : Expr → Expr → Stmt → Stmt → Stmt  -- if a ≤ b then s else t
  | decl   : Int → Int → Expr → Stmt → Stmt    -- { let x : lo..=hi = e; s }
  | forN   : Nat → (List Val → Nat → List Val → Prop) → Stmt → Stmt
  | brk    : Stmt
  | call   : Nat → List (Nat × Bool) → Nat → Stmt
  | fassign : Nat → FExpr → Stmt               -- x = e for a float variable
  | fstore  : Nat → Expr → FExpr → Stmt        -- a[i] = e for a float slice
  | fdecl   : FExpr → Stmt → Stmt              -- { let x : f64 = e; s }
  | fite    : FExpr → FExpr → Stmt → Stmt → Stmt   -- if a ≤ b then s else t (false when either is NaN)
  | forE   : Expr → (List Val → Nat → List Val → Prop) → Stmt → Stmt
      -- for i in 0..e { s }: the bound is evaluated once, before the loop
  | loopB  : Nat → (List Val → Nat → List Val → Prop) → Stmt → Stmt
  | loopE  : Expr → (List Val → Nat → List Val → Prop) → Stmt → Stmt
  | note   : String → Stmt → Stmt
  | pmap   : Nat → List Nat → Expr → Nat → Stmt
      -- parallel for i upto n { out[i] = g(args, i) }: g is a callee, args are variables passed by value,
      -- n is evaluated once, out is an integer slice that is not among args. Every call only reads values
      -- that no call writes, and writes only its own element: any order of execution gives the same result.
  | pmapF  : Nat → List Nat → Expr → Nat → Stmt
      -- the same for a float slice: g takes (args, i, inout r: f64) and out[i] is the final value of r.
      -- the statement, labelled with its source text. It runs exactly like the statement; the label is
      -- carried into the statement's obligations so that a failed proof can say where it comes from.
      -- like loopB, with the proof-only bound given by an expression evaluated at entry (e.g. len(a) + 1)
      -- loop { s } that must leave by `brk` within n iterations. n and the iteration number exist only
      -- for the proof: the body does not see a counter, and the generated code has none.

inductive Out where
  | norm : List Val → Out
  | brk  : List Val → Out

/-! A decidable requirement on the arguments of a function: a boolean combination of comparisons between
    integer terms over the integer parameters and the lengths of the array parameters. Because it is
    data, an entry check can be generated from it; because `evalC` is a function, a caller outside the
    language can run exactly the condition the proof assumed. -/

inductive CT where
  | lit : Int → CT
  | val : Nat → CT                             -- the value of an integer argument, by position
  | len : Nat → CT                             -- the length of an array argument, by position
  | add : CT → CT → CT
  | sub : CT → CT → CT
  | mul : CT → CT → CT

def evalCT : CT → List Val → Int
  | .lit n, _ => n
  | .val i, args => match args[i]? with | some (.int v) => v | _ => 0
  | .len i, args => match args[i]? with
    | some (.arr l) => l.length | some (.farr l) => l.length | _ => 0
  | .add a b, args => evalCT a args + evalCT b args
  | .sub a b, args => evalCT a args - evalCT b args
  | .mul a b, args => evalCT a args * evalCT b args

inductive Cond where
  | tt  : Cond
  | le  : CT → CT → Cond
  | lt  : CT → CT → Cond
  | eq  : CT → CT → Cond
  | and : Cond → Cond → Cond

def evalC : Cond → List Val → Bool
  | .tt, _ => true
  | .le a b, args => decide (evalCT a args ≤ evalCT b args)
  | .lt a b, args => decide (evalCT a args < evalCT b args)
  | .eq a b, args => decide (evalCT a args = evalCT b args)
  | .and a b, args => evalC a args && evalC b args

/-- A requirement is well formed for a parameter list when `val` names an integer parameter and `len` an
    array parameter. (Otherwise `evalCT` would silently read 0.) -/
def ctWf (ps : List Ty) : CT → Bool
  | .lit _ => true
  | .val i => match ps[i]? with | some (.int _ _) => true | _ => false
  | .len i => match ps[i]? with
    | some (.arr _ _ _) => true | some (.slice _ _) => true | some .fslice => true | _ => false
  | .add a b => ctWf ps a && ctWf ps b
  | .sub a b => ctWf ps a && ctWf ps b
  | .mul a b => ctWf ps a && ctWf ps b

def condWf (ps : List Ty) : Cond → Bool
  | .tt => true
  | .le a b => ctWf ps a && ctWf ps b
  | .lt a b => ctWf ps a && ctWf ps b
  | .eq a b => ctWf ps a && ctWf ps b
  | .and a b => condWf ps a && condWf ps b

structure Fn where
  params : List (Ty × Bool)
  rlo    : Int
  rhi    : Int
  body   : Stmt                                -- typed in  int rlo rhi :: params
  req    : Cond                                -- decidable requirement on the arguments (entry check)
  pre    : List Val → Prop                     -- further precondition, not checkable at entry (default: True)
  post   : List Val → Int → List Val → Prop

def lookups (env : List Val) : List Nat → Option (List Val)
  | [] => some []
  | i :: is => match env[i]?, lookups env is with
    | some v, some vs => some (v :: vs)
    | _, _ => none

def evalE : Expr → List Val → Option Int
  | .lit n, _ => if inI64 n then some n else none
  | .var i, env => match env[i]? with | some (.int v) => if inI64 v then some v else none | _ => none
  | .add a b, env => match evalE a env, evalE b env with
    | some x, some y => if inI64 (x + y) then some (x + y) else none | _, _ => none
  | .sub a b, env => match evalE a env, evalE b env with
    | some x, some y => if inI64 (x - y) then some (x - y) else none | _, _ => none
  | .mul a b, env => match evalE a env, evalE b env with
    | some x, some y => if inI64 (x * y) then some (x * y) else none | _, _ => none
  | .div a b, env => match evalE a env, evalE b env with
    | some x, some y => if 0 ≤ x ∧ 0 < y then some (x / y) else none | _, _ => none
  | .idx a e, env => match env[a]?, evalE e env with
    | some (.arr l), some j =>
      if 0 ≤ j ∧ j < l.length then
        match l[j.toNat]? with | some v => if inI64 v then some v else none | none => none
      else none
    | _, _ => none
  | .len a, env => match env[a]? with
    | some (.arr l) => if inI64 (l.length : Int) then some (l.length : Int) else none
    | some (.farr l) => if inI64 (l.length : Int) then some (l.length : Int) else none
    | _ => none
  | .le a b, env => match evalE a env, evalE b env with
    | some x, some y => some (if x ≤ y then 1 else 0) | _, _ => none
  | .lt a b, env => match evalE a env, evalE b env with
    | some x, some y => some (if x < y then 1 else 0) | _, _ => none
  | .eq a b, env => match evalE a env, evalE b env with
    | some x, some y => some (if x = y then 1 else 0) | _, _ => none
  | .sel c t e, env => match evalE c env, evalE t env, evalE e env with
    | some cv, some x, some y => some (if cv ≠ 0 then x else y) | _, _, _ => none

/-- Every value an expression produces fits 64 bits: reads are checked like results of arithmetic. -/
theorem evalE_i64 (e : Expr) (env : List Val) : ∀ (v : Int), evalE e env = some v → inI64 v := by
  induction e with
  | div a b iha ihb =>
    intro v h
    simp only [evalE] at h
    split at h
    next x y hx hy =>
      split at h
      next hc =>
        simp at h; subst h
        have hx64 := iha x hx
        have h1 : 0 ≤ x / y := Int.ediv_nonneg hc.1 (by omega)
        have h2 : x / y ≤ x := Int.ediv_le_self y hc.1
        unfold inI64 at *; omega
      next => simp at h
    next => simp at h
  | len a =>
    intro v h
    simp only [evalE] at h
    split at h
    case h_1 l hl => split at h
                     next hc => simp at h; subst h; exact hc
                     next => simp at h
    case h_2 l hl => split at h
                     next hc => simp at h; subst h; exact hc
                     next => simp at h
    case h_3 => simp at h
  | le a b _ _ => intro v h; simp only [evalE] at h; split at h <;> simp at h; subst h; split <;> simp [inI64]
  | lt a b _ _ => intro v h; simp only [evalE] at h; split at h <;> simp at h; subst h; split <;> simp [inI64]
  | eq a b _ _ => intro v h; simp only [evalE] at h; split at h <;> simp at h; subst h; split <;> simp [inI64]
  | sel c t e _ iht ihe =>
    intro v h
    simp only [evalE] at h
    split at h
    next cv x y hc hx hy => simp at h; subst h; split
                            · exact ihe y hy
                            · exact iht x hx
    next => simp at h
  | _ => intro v h; simp only [evalE] at h; (repeat' split at h) <;> simp_all

def evalF : FExpr → List Val → Option Float
  | .lit f, _ => some f
  | .var i, env => match env[i]? with | some (.flt v) => some v | _ => none
  | .add a b, env => match evalF a env, evalF b env with | some x, some y => some (x + y) | _, _ => none
  | .sub a b, env => match evalF a env, evalF b env with | some x, some y => some (x - y) | _, _ => none
  | .mul a b, env => match evalF a env, evalF b env with | some x, some y => some (x * y) | _, _ => none
  | .div a b, env => match evalF a env, evalF b env with | some x, some y => some (x / y) | _, _ => none
  | .idx a e, env => match env[a]?, evalE e env with
    | some (.farr l), some j => if 0 ≤ j ∧ j < l.length then l[j.toNat]? else none
    | _, _ => none
  | .ofInt e, env => match evalE e env with | some n => some (Float.ofInt n) | none => none
  | .sel c t e, env => match evalE c env, evalF t env, evalF e env with
    | some cv, some x, some y => some (if cv ≠ 0 then x else y) | _, _, _ => none
  | .neg a, env => match evalF a env with | some x => some (-x) | none => none
  | .abs a, env => match evalF a env with | some x => some x.abs | none => none
  | .sqrt a, env => match evalF a env with | some x => some x.sqrt | none => none
  | .selLe a b t e, env => match evalF a env, evalF b env, evalF t env, evalF e env with
    | some x, some y, some u, some v => some (if x ≤ y then u else v) | _, _, _, _ => none

def writeBack (env : List Val) : List (Nat × Bool) → List Val → List Val
  | (i, true) :: as, v :: vs => writeBack (env.set i v) as vs
  | (_, false) :: as, _ :: vs => writeBack env as vs
  | _, _ => env

def exclusive : List (Nat × Bool) → Nat → Bool
  | [], _ => true
  | (i, b) :: as, dst =>
    (!b || (i != dst && as.all (fun a => a.1 != i))) && (as.all (fun a => !a.2 || a.1 != i)) && exclusive as dst

def popOut : Option Out → Option Out
  | some (.norm (_ :: e)) => some (.norm e)
  | some (.brk (_ :: e)) => some (.brk e)
  | _ => none

def loop (f : Nat → List Val → Option Out) : Nat → Nat → List Val → Option (List Val)
  | _, 0, env => some env
  | i, k + 1, env => match f i env with
    | some (.norm env') => loop f (i + 1) k env'
    | some (.brk env') => some env'
    | none => none

/-- The results of `f 0, ..., f (n-1)`, or none if one of them is none. -/
def mapN {α : Type} (f : Nat → Option α) : Nat → Option (List α)
  | 0 => some []
  | k + 1 => match mapN f k, f k with
    | some xs, some x => some (xs ++ [x])
    | _, _ => none

theorem mapN_length {α : Type} (f : Nat → Option α) : ∀ (n : Nat) (rs : List α), mapN f n = some rs → rs.length = n := by
  intro n
  induction n with
  | zero => intro rs h; simp [mapN] at h; subst h; rfl
  | succ k ih =>
    intro rs h
    simp only [mapN] at h
    split at h
    next xs x hxs hx => simp at h; subst h; simp [ih xs hxs]
    next => simp at h

theorem mapN_sound {α : Type} (f : Nat → Option α) (P : α → Prop) : ∀ (n : Nat),
    (∀ i, i < n → ∃ r, f i = some r ∧ P r) → ∃ rs, mapN f n = some rs ∧ rs.length = n ∧ ∀ v ∈ rs, P v := by
  intro n
  induction n with
  | zero => intro _; exact ⟨[], rfl, rfl, by simp⟩
  | succ k ih =>
    intro h
    obtain ⟨xs, hxs, hlen, hall⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨x, hx, hp⟩ := h k (by omega)
    refine ⟨xs ++ [x], by simp [mapN, hxs, hx], by simp [hlen], ?_⟩
    intro v hv
    simp at hv
    rcases hv with hv | hv
    · exact hall v hv
    · subst hv; exact hp

/-! ### Why a parallel loop may run in any order

    The result of `pmap` is defined as if every call ran first and the results were then written. In the
    generated code threads run the calls in chunks, in an order nobody controls. That gives the same
    array because each call only reads values no call writes (the callee's parameters are all by value
    and `out` is not among them), so its result does not depend on the order; and writes to different
    elements commute. The second half is the theorem below: any sequence of writes `out[i] := rs[i]` that
    writes every index below n at least once, in any order and with any repetition, ends in the array
    the semantics defines. -/

theorem set_any_order {α : Type} [Inhabited α] (rs : List α) : ∀ (ps : List Nat) (acc : List α),
    (ps.foldl (fun a i => a.set i rs[i]!) acc).length = acc.length ∧
    ∀ j, (ps.foldl (fun a i => a.set i rs[i]!) acc)[j]? =
      if j ∈ ps ∧ j < acc.length then some rs[j]! else acc[j]? := by
  intro ps
  induction ps with
  | nil => intro acc; simp
  | cons i ps ih =>
    intro acc
    obtain ⟨hl, hj⟩ := ih (acc.set i rs[i]!)
    simp only [List.foldl_cons]
    refine ⟨by simpa using hl, ?_⟩
    intro j
    rw [hj j]
    simp only [List.length_set, List.mem_cons]
    by_cases hjp : j ∈ ps
    · by_cases hlt : j < acc.length <;> simp [hjp, hlt]
    · by_cases hji : j = i
      · subst hji; by_cases hlt : j < acc.length <;> simp [hjp, hlt, List.getElem?_set]
      · have : i ≠ j := fun h => hji h.symm
        simp [hjp, hji, List.getElem?_set_ne this]

theorem parallel_writes {α : Type} [Inhabited α] (l rs : List α) (n : Nat) (hn : n ≤ l.length) (hrs : rs.length = n)
    (ps : List Nat) (hps : ∀ j, j ∈ ps ↔ j < n) :
    ps.foldl (fun a i => a.set i rs[i]!) l = rs ++ l.drop n := by
  obtain ⟨_, hj⟩ := set_any_order rs ps l
  apply List.ext_getElem?
  intro j
  rw [hj j]
  by_cases hjn : j < n
  · have hjl : j < l.length := by omega
    have hjr : j < rs.length := by omega
    simp [(hps j).2 hjn, hjl, List.getElem?_append_left hjr, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjr]
  · have : ¬ j ∈ ps := fun h => hjn ((hps j).1 h)
    simp only [this, false_and, ite_false]
    rw [List.getElem?_append_right (by omega), List.getElem?_drop]
    congr 1
    omega

/-- A loop that must be left by a break: running out of iterations is stuck. -/
def loopBrk (f : List Val → Option Out) : Nat → List Val → Option (List Val)
  | 0, _ => none
  | k + 1, env => match f env with
    | some (.norm env') => loopBrk f k env'
    | some (.brk env') => some env'
    | none => none

/-- The semantics does not look at types, except that a store and an assignment keep the value inside the
    declared range, which the statement carries after elaboration (here: looked up in Γ). -/
def execS (callee : Nat → List Val → Option (Int × List Val)) (Γ : List Ty) : Stmt → List Val → Option Out
  | .skip, env => some (.norm env)
  | .seq s t, env => match execS callee Γ s env with
    | some (.norm env') => execS callee Γ t env'
    | some (.brk env') => some (.brk env')
    | none => none
  | .assign x e, env => match Γ[x]?, env[x]?, evalE e env with
    | some (.int lo hi), some (.int _), some v => if lo ≤ v ∧ v ≤ hi then some (.norm (env.set x (.int v))) else none
    | _, _, _ => none
  | .store a i e, env => match Γ[a]?, env[a]?, evalE i env, evalE e env with
    | some (.arr _ lo hi), some (.arr l), some j, some v =>
      if 0 ≤ j ∧ j < l.length ∧ lo ≤ v ∧ v ≤ hi then some (.norm (env.set a (.arr (l.set j.toNat v)))) else none
    | some (.slice lo hi), some (.arr l), some j, some v =>
      if 0 ≤ j ∧ j < l.length ∧ lo ≤ v ∧ v ≤ hi then some (.norm (env.set a (.arr (l.set j.toNat v)))) else none
    | _, _, _, _ => none
  | .ite a b s t, env => match evalE a env, evalE b env with
    | some x, some y => if x ≤ y then execS callee Γ s env else execS callee Γ t env | _, _ => none
  | .decl lo hi e s, env => match evalE e env with
    | some v => if lo ≤ v ∧ v ≤ hi then popOut (execS callee (.int lo hi :: Γ) s (.int v :: env)) else none
    | none => none
  | .forN n _ s, env =>
    match loop (fun i env => popOut (execS callee (.int 0 n :: Γ) s (.int i :: env))) 0 n env with
    | some env' => some (.norm env')
    | none => none
  | .brk, env => some (.brk env)
  | .fassign x e, env => match Γ[x]?, env[x]?, evalF e env with
    | some .flt, some (.flt _), some v => some (.norm (env.set x (.flt v)))
    | _, _, _ => none
  | .fstore a i e, env => match Γ[a]?, env[a]?, evalE i env, evalF e env with
    | some .fslice, some (.farr l), some j, some v =>
      if 0 ≤ j ∧ j < l.length then some (.norm (env.set a (.farr (l.set j.toNat v)))) else none
    | _, _, _, _ => none
  | .fdecl e s, env => match evalF e env with
    | some v => popOut (execS callee (.flt :: Γ) s (.flt v :: env))
    | none => none
  | .fite a b s t, env => match evalF a env, evalF b env with
    | some x, some y => if x ≤ y then execS callee Γ s env else execS callee Γ t env | _, _ => none
  | .forE e _ s, env => match evalE e env with
    | some n =>
      if 0 ≤ n then
        match loop (fun i env => popOut (execS callee (.int 0 9223372036854775807 :: Γ) s (.int i :: env))) 0 n.toNat env with
        | some env' => some (.norm env')
        | none => none
      else none
    | none => none
  | .loopB n _ s, env => match loopBrk (fun env => execS callee Γ s env) n env with
    | some env' => some (.norm env')
    | none => none
  | .note _ s, env => execS callee Γ s env
  | .pmap f args e out, env =>
    match Γ[out]?, env[out]?, lookups env args, evalE e env with
    | some (.slice lo hi), some (.arr l), some vs, some nv =>
      if args.contains out = false ∧ 0 ≤ nv ∧ nv ≤ l.length then
        match mapN (fun i => match callee f (vs ++ [.int i]) with | some (r, _) => some r | none => none) nv.toNat with
        | some rs =>
          if rs.all (fun v => decide (lo ≤ v ∧ v ≤ hi)) then some (.norm (env.set out (.arr (rs ++ l.drop nv.toNat))))
          else none
        | none => none
      else none
    | _, _, _, _ => none
  | .pmapF f args e out, env =>
    match Γ[out]?, env[out]?, lookups env args, evalE e env with
    | some .fslice, some (.farr l), some vs, some nv =>
      if args.contains out = false ∧ 0 ≤ nv ∧ nv ≤ l.length then
        match mapN (fun i => match callee f (vs ++ [.int i, .flt 0.0]) with
            | some (_, outs) => (match outs.getLast? with | some (.flt v) => some v | _ => none)
            | none => none) nv.toNat with
        | some rs => some (.norm (env.set out (.farr (rs ++ l.drop nv.toNat))))
        | none => none
      else none
    | _, _, _, _ => none
  | .loopE e _ s, env => match evalE e env with
    | some n => match loopBrk (fun env => execS callee Γ s env) n.toNat env with
      | some env' => some (.norm env')
      | none => none
    | none => none
  | .call f args dst, env =>
    if exclusive args dst then
      match lookups env (args.map (·.1)), env[dst]? with
      | some vs, some (.int _) => match callee f vs with
        | some (r, outs) => some (.norm (writeBack (env.set dst (.int r)) args outs))
        | none => none
      | _, _ => none
    else none

def evalFn : List Fn → Nat → List Val → Option (Int × List Val)
  | [], _, _ => none
  | f :: rest, 0, args =>
    if hasAll (f.params.map (·.1)) args then
      match execS (evalFn rest) (.int f.rlo f.rhi :: f.params.map (·.1)) f.body (.int f.rlo :: args) with
      | some (.norm (.int r :: e)) => some (r, e)
      | _ => none
    else none
  | _ :: rest, i + 1, args => evalFn rest i args

/-! ## Lengths: no statement changes the length of an array. -/

def shape : Val → Option Nat
  | .int _ => none
  | .arr l => some l.length
  | .flt _ => none
  | .farr l => some l.length

/-- The shape of every variable: `none` for an integer, the length for an array. -/
def lens (env : List Val) : List (Option Nat) := env.map shape

/-- Callees keep the shapes of their arguments. -/
def LensOk (callee : Nat → List Val → Option (Int × List Val)) : Prop :=
  ∀ i vs r outs, callee i vs = some (r, outs) → lens outs = lens vs

/-! ## Frame: a statement does not change the variables it cannot assign.
    `mods s i` is a syntactic over-approximation of "s may change variable i". -/

def mods : Stmt → Nat → Bool
  | .skip, _ => false
  | .brk, _ => false
  | .seq s t, i => mods s i || mods t i
  | .assign x _, i => x == i
  | .store a _ _, i => a == i
  | .ite _ _ s t, i => mods s i || mods t i
  | .decl _ _ _ s, i => mods s (i + 1)
  | .forN _ _ s, i => mods s (i + 1)
  | .call _ args dst, i => dst == i || args.any (fun a => a.2 && a.1 == i)
  | .loopB _ _ s, i => mods s i
  | .loopE _ _ s, i => mods s i
  | .note _ s, i => mods s i
  | .pmap _ _ _ out, i => out == i
  | .pmapF _ _ _ out, i => out == i
  | .forE _ _ s, i => mods s (i + 1)
  | .fassign x _, i => x == i
  | .fstore a _ _, i => a == i
  | .fdecl _ s, i => mods s (i + 1)
  | .fite _ _ s t, i => mods s i || mods t i

def Out.env : Out → List Val
  | .norm e => e
  | .brk e => e

theorem writeBack_get : ∀ (args : List (Nat × Bool)) (outs env : List Val) (i : Nat),
    args.any (fun a => a.2 && a.1 == i) = false → (writeBack env args outs)[i]? = env[i]? := by
  intro args
  induction args with
  | nil => intro outs env i _; simp [writeBack]
  | cons a as ih =>
    intro outs env i h
    obtain ⟨j, b⟩ := a
    simp at h
    cases outs with
    | nil => cases b <;> simp [writeBack]
    | cons o outs =>
      cases b with
      | false => simp [writeBack]; exact ih outs env i (by simpa using h.2)
      | true =>
        simp [writeBack]
        rw [ih outs _ i (by simpa using h.2)]
        have : j ≠ i := by simpa using h.1
        simp [List.getElem?_set_ne this]

/-! ### Write-back under `exclusive` is a simultaneous assignment

    The semantics of a call is copy-in copy-out. The generated C passes a pointer for an `inout`
    argument. The two agree at the return of the call if the write-back gives every `inout` variable
    exactly the callee's final value of the corresponding parameter, whatever the order of the copies,
    and touches nothing else. That is what the next two theorems say, given `exclusive`. -/

theorem exclusive_tail {a : Nat × Bool} {as : List (Nat × Bool)} {dst : Nat}
    (h : exclusive (a :: as) dst = true) : exclusive as dst = true := by
  obtain ⟨i, b⟩ := a
  simp [exclusive] at h
  exact h.2

/-- An `inout` variable receives the callee's final value of its parameter. -/
theorem writeBack_hit : ∀ (args : List (Nat × Bool)) (outs env : List Val) (dst k i : Nat) (v : Val),
    exclusive args dst = true → args[k]? = some (i, true) → outs[k]? = some v → i < env.length →
    (writeBack env args outs)[i]? = some v := by
  intro args
  induction args with
  | nil => intro outs env dst k i v _ hk; simp at hk
  | cons a as ih =>
    intro outs env dst k i v hex hk ho hlt
    obtain ⟨j, b⟩ := a
    cases outs with
    | nil => simp at ho
    | cons o outs =>
      have hex' := exclusive_tail hex
      cases k with
      | zero =>
        simp at hk ho
        obtain ⟨rfl, rfl⟩ := hk
        subst ho
        simp [exclusive] at hex
        simp only [writeBack]
        have hno : as.any (fun a => a.2 && a.1 == j) = false := by
          simp
          intro x hx
          exact (hex.1.1.2 x).2 hx
        rw [writeBack_get as outs _ j hno]
        simp [hlt]
      | succ k =>
        simp at hk ho
        have hmem : (i, true) ∈ as := List.mem_of_getElem? hk
        cases b with
        | false =>
          simp only [writeBack]
          exact ih outs env dst k i v hex' hk ho hlt
        | true =>
          simp only [writeBack]
          exact ih outs (env.set j o) dst k i v hex' hk ho (by simpa using hlt)

/-- The destination of a call keeps the result: no write-back overwrites it. -/
theorem writeBack_dst : ∀ (args : List (Nat × Bool)) (outs env : List Val) (dst : Nat),
    exclusive args dst = true → (writeBack env args outs)[dst]? = env[dst]? := by
  intro args outs env dst hex
  apply writeBack_get
  induction args with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨j, b⟩ := a
    have hex' := exclusive_tail hex
    simp only [List.any_cons, ih hex', Bool.or_false]
    cases b with
    | false => simp
    | true =>
      simp [exclusive] at hex
      simp
      exact hex.1.1.1

theorem popOut_inv {r : Option Out} {o : Out} (h : popOut r = some o) :
    ∃ o1 w, r = some o1 ∧ o1.env = w :: o.env := by
  match r, h with
  | some (.norm (w :: e)), h => simp [popOut] at h; subst h; exact ⟨_, w, rfl, rfl⟩
  | some (.brk (w :: e)), h => simp [popOut] at h; subst h; exact ⟨_, w, rfl, rfl⟩
  | some (.norm []), h => simp [popOut] at h
  | some (.brk []), h => simp [popOut] at h
  | none, h => simp [popOut] at h

theorem loop_frame (f : Nat → List Val → Option Out) (i : Nat)
    (hf : ∀ k e o, f k e = some o → o.env[i]? = e[i]?) :
    ∀ (n a : Nat) (env env' : List Val), loop f a n env = some env' → env'[i]? = env[i]? := by
  intro n
  induction n with
  | zero => intro a env env' h; simp [loop] at h; subst h; rfl
  | succ n ih =>
    intro a env env' h
    simp only [loop] at h
    split at h
    next e1 h1 => rw [ih _ _ _ h, ← hf _ _ _ h1]; rfl
    next e1 h1 => simp at h; subst h; exact hf _ _ _ h1
    next => simp at h

theorem loopBrk_frame (f : List Val → Option Out) (i : Nat)
    (hf : ∀ e o, f e = some o → o.env[i]? = e[i]?) :
    ∀ (n : Nat) (env env' : List Val), loopBrk f n env = some env' → env'[i]? = env[i]? := by
  intro n
  induction n with
  | zero => intro env env' h; simp [loopBrk] at h
  | succ n ih =>
    intro env env' h
    simp only [loopBrk] at h
    split at h
    next e1 h1 => rw [ih _ _ h, ← hf _ _ h1]; rfl
    next e1 h1 => simp at h; subst h; exact hf _ _ h1
    next => simp at h

/-- What a `pmap` can do: replace a prefix of the integer slice `out`, nothing else. -/
theorem exec_pmap_inv {callee : Nat → List Val → Option (Int × List Val)} {Γ : List Ty} {f : Nat} {args : List Nat}
    {e : Expr} {out : Nat} {env : List Val} {o : Out} (h : execS callee Γ (.pmap f args e out) env = some o) :
    ∃ l rs, env[out]? = some (.arr l) ∧ rs.length ≤ l.length ∧ o = .norm (env.set out (.arr (rs ++ l.drop rs.length))) := by
  simp only [execS] at h
  split at h
  · rename_i lo hi l vs nv _ ho _ _
    split at h
    · rename_i hc
      split at h
      · rename_i rs hrs
        split at h
        · simp at h
          have hlen := mapN_length _ _ _ hrs
          exact ⟨l, rs, ho, by omega, by rw [← h, hlen]⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The same for `pmapF` and a float slice. -/
theorem exec_pmapF_inv {callee : Nat → List Val → Option (Int × List Val)} {Γ : List Ty} {f : Nat} {args : List Nat}
    {e : Expr} {out : Nat} {env : List Val} {o : Out} (h : execS callee Γ (.pmapF f args e out) env = some o) :
    ∃ l rs, env[out]? = some (.farr l) ∧ rs.length ≤ l.length ∧ o = .norm (env.set out (.farr (rs ++ l.drop rs.length))) := by
  simp only [execS] at h
  split at h
  · rename_i l vs nv _ ho _ _
    split at h
    · rename_i hc
      split at h
      · rename_i rs hrs
        simp at h
        have hlen := mapN_length _ _ _ hrs
        exact ⟨l, rs, ho, by omega, by rw [← h, hlen]⟩
      · simp at h
    · simp at h
  · simp at h

theorem exec_frame (callee : Nat → List Val → Option (Int × List Val)) (s : Stmt) :
    ∀ (Γ : List Ty) (env : List Val) (o : Out) (i : Nat),
      execS callee Γ s env = some o → mods s i = false → o.env[i]? = env[i]? := by
  induction s with
  | skip => intro Γ env o i h _; simp [execS] at h; subst h; rfl
  | brk => intro Γ env o i h _; simp [execS] at h; subst h; rfl
  | seq s t ihs iht =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next e1 h1 => rw [iht Γ e1 o i h hm.2, ← ihs Γ env _ i h1 hm.1]; rfl
    next e1 h1 => simp at h; subst h; exact ihs Γ env _ i h1 hm.1
    next => simp at h
  | assign x e =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next => split at h
            next => simp at h; subst h; simp [Out.env, List.getElem?_set_ne hm]
            next => simp at h
    next => simp at h
  | store a j e =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    case h_1 => split at h
                next => simp at h; subst h; simp [Out.env, List.getElem?_set_ne hm]
                next => simp at h
    case h_2 => split at h
                next => simp at h; subst h; simp [Out.env, List.getElem?_set_ne hm]
                next => simp at h
    case h_3 => simp at h
  | ite a b s t ihs iht =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next => split at h
            next => exact ihs Γ env o i h hm.1
            next => exact iht Γ env o i h hm.2
    next => simp at h
  | decl lo hi e s ihs =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next v hv => split at h
                 next =>
                   obtain ⟨o1, w, h1, h2⟩ := popOut_inv h
                   have := ihs _ _ o1 (i + 1) h1 hm
                   rw [h2] at this
                   simpa using this
                 next => simp at h
    next => simp at h
  | forN n I s ihs =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next env' hl =>
      simp at h; subst h
      refine loop_frame _ i ?_ n 0 env env' hl
      intro k e o hk
      obtain ⟨o1, w, h1, h2⟩ := popOut_inv hk
      have := ihs _ _ o1 (i + 1) h1 hm
      rw [h2] at this
      simpa using this
    next => simp at h
  | forE e I s ihs =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next n hn =>
      split at h
      next =>
        split at h
        next env' hl =>
          simp at h; subst h
          refine loop_frame _ i ?_ n.toNat 0 env env' hl
          intro k e o hk
          obtain ⟨o1, w, h1, h2⟩ := popOut_inv hk
          have := ihs _ _ o1 (i + 1) h1 hm
          rw [h2] at this
          simpa using this
        next => simp at h
      next => simp at h
    next => simp at h
  | fassign x e =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next => simp at h; subst h; simp [Out.env, List.getElem?_set_ne hm]
    next => simp at h
  | fstore a j e =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next => split at h
            next => simp at h; subst h; simp [Out.env, List.getElem?_set_ne hm]
            next => simp at h
    next => simp at h
  | fdecl e s ihs =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next v hv =>
      obtain ⟨o1, w, h1, h2⟩ := popOut_inv h
      have := ihs _ _ o1 (i + 1) h1 hm
      rw [h2] at this
      simpa using this
    next => simp at h
  | fite a b s t ihs iht =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next => split at h
            next => exact ihs Γ env o i h hm.1
            next => exact iht Γ env o i h hm.2
    next => simp at h
  | loopB n I s ihs =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next env' hl =>
      simp at h; subst h
      exact loopBrk_frame _ i (fun e o hk => ihs Γ e o i hk hm) n env env' hl
    next => simp at h
  | note t s ihs =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    exact ihs Γ env o i h hm
  | pmap f args e out =>
    intro Γ env o i h hm
    simp [mods] at hm
    obtain ⟨l, rs, _, _, rfl⟩ := exec_pmap_inv h
    simp [Out.env, List.getElem?_set_ne hm]
  | pmapF f args e out =>
    intro Γ env o i h hm
    simp [mods] at hm
    obtain ⟨l, rs, _, _, rfl⟩ := exec_pmapF_inv h
    simp [Out.env, List.getElem?_set_ne hm]
  | loopE e I s ihs =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next n hn =>
      split at h
      next env' hl =>
        simp at h; subst h
        exact loopBrk_frame _ i (fun e o hk => ihs Γ e o i hk hm) n.toNat env env' hl
      next => simp at h
    next => simp at h
  | call f args dst =>
    intro Γ env o i h hm
    simp [mods] at hm
    simp only [execS] at h
    split at h
    next => split at h
            next => split at h
                    next => simp at h; subst h
                            simp only [Out.env]
                            rw [writeBack_get args _ _ i (by simpa using hm.2)]
                            simp [List.getElem?_set_ne hm.1]
                    next => simp at h
            next => simp at h
    next => simp at h

/-- The variables of Γ that the body of a break-only loop cannot assign. -/
def keptB (Γ : List Ty) (s : Stmt) : List Nat := (List.range Γ.length).filter (fun j => !mods s j)

/-- The two environments agree on the listed variables. -/
def sameAt : List Nat → List Val → List Val → Prop
  | [], _, _ => True
  | k :: ks, env, env' => env'[k]? = env[k]? ∧ sameAt ks env env'

theorem sameAt_of (ks : List Nat) (env env' : List Val) (h : ∀ k ∈ ks, env'[k]? = env[k]?) : sameAt ks env env' := by
  induction ks with
  | nil => trivial
  | cons k ks ih => exact ⟨h k (by simp), ih (fun j hj => h j (by simp [hj]))⟩

/-- The variables of Γ that a loop body (which sees them shifted by its counter) cannot assign. -/
def kept (Γ : List Ty) (s : Stmt) : List Nat := (List.range Γ.length).filter (fun j => !mods s (j + 1))

theorem lens_set (env : List Val) (i : Nat) (v w : Val) (h : env[i]? = some v) (hs : shape w = shape v) :
    lens (env.set i w) = lens env := by
  unfold lens
  apply List.ext_getElem?
  intro j
  by_cases hji : i = j
  · subst hji
    have hlt : i < env.length := by
      rcases Nat.lt_or_ge i env.length with h1 | h1
      · exact h1
      · simp [List.getElem?_eq_none h1] at h
    have hv : env[i] = v := by simpa [List.getElem?_eq_getElem hlt] using h
    simp [List.getElem?_set, hlt, hs, hv]
  · simp [List.getElem?_set_ne hji]

theorem lens_get {env env' : List Val} (h : lens env' = lens env) (i : Nat) (v : Val) (hv : env[i]? = some v) :
    ∃ w, env'[i]? = some w ∧ shape w = shape v := by
  have : (lens env')[i]? = (lens env)[i]? := by rw [h]
  simp [lens, hv] at this
  obtain ⟨w, hw, hs⟩ := this
  exact ⟨w, hw, hs⟩

theorem writeBack_lens : ∀ (args : List (Nat × Bool)) (vs outs env0 env : List Val),
    lens env = lens env0 → lookups env0 (args.map (·.1)) = some vs → lens outs = lens vs →
    lens (writeBack env args outs) = lens env0 := by
  intro args
  induction args with
  | nil => intro vs outs env0 env h _ _; simpa [writeBack] using h
  | cons a as ih =>
    intro vs outs env0 env h hl ho
    obtain ⟨i, b⟩ := a
    simp only [List.map, lookups] at hl
    split at hl
    next v vs' hv hvs =>
      simp at hl; subst hl
      cases outs with
      | nil => simp [lens] at ho
      | cons o outs =>
        simp [lens] at ho
        cases b with
        | false => simpa [writeBack] using ih vs' outs env0 env h hvs (by simpa [lens] using ho.2)
        | true =>
          simp only [writeBack]
          obtain ⟨w, hw, hs⟩ := lens_get h i v hv
          refine ih vs' outs env0 _ ?_ hvs (by simpa [lens] using ho.2)
          rw [lens_set env i w o hw (by rw [ho.1, hs]), h]
    next => simp at hl

theorem loop_lens (f : Nat → List Val → Option Out)
    (hf : ∀ k e o, f k e = some o → lens o.env = lens e) :
    ∀ (n a : Nat) (env env' : List Val), loop f a n env = some env' → lens env' = lens env := by
  intro n
  induction n with
  | zero => intro a env env' h; simp [loop] at h; subst h; rfl
  | succ n ih =>
    intro a env env' h
    simp only [loop] at h
    split at h
    next e1 h1 => rw [ih _ _ _ h, ← hf _ _ _ h1]; rfl
    next e1 h1 => simp at h; subst h; exact hf _ _ _ h1
    next => simp at h

theorem loopBrk_lens (f : List Val → Option Out)
    (hf : ∀ e o, f e = some o → lens o.env = lens e) :
    ∀ (n : Nat) (env env' : List Val), loopBrk f n env = some env' → lens env' = lens env := by
  intro n
  induction n with
  | zero => intro env env' h; simp [loopBrk] at h
  | succ n ih =>
    intro env env' h
    simp only [loopBrk] at h
    split at h
    next e1 h1 => rw [ih _ _ h, ← hf _ _ h1]; rfl
    next e1 h1 => simp at h; subst h; exact hf _ _ h1
    next => simp at h

theorem popOut_lens {r : Option Out} {o : Out} {v : Val} {env : List Val} (h : popOut r = some o)
    (hr : ∀ o1, r = some o1 → lens o1.env = lens (v :: env)) : lens o.env = lens env := by
  obtain ⟨o1, w, h1, h2⟩ := popOut_inv h
  have := hr o1 h1
  rw [h2] at this
  simp [lens] at this ⊢
  exact this.2

theorem exec_lens (callee : Nat → List Val → Option (Int × List Val)) (hc : LensOk callee) (s : Stmt) :
    ∀ (Γ : List Ty) (env : List Val) (o : Out), execS callee Γ s env = some o → lens o.env = lens env := by
  induction s with
  | skip => intro Γ env o h; simp [execS] at h; subst h; rfl
  | brk => intro Γ env o h; simp [execS] at h; subst h; rfl
  | seq s t ihs iht =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next e1 h1 => rw [iht Γ e1 o h, ← ihs Γ env _ h1]; rfl
    next e1 h1 => simp at h; subst h; exact ihs Γ env _ h1
    next => simp at h
  | assign x e =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next lo hi x0 v hty hx hv =>
      split at h
      next => simp at h; subst h; exact lens_set env x _ _ hx rfl
      next => simp at h
    next => simp at h
  | store a j e =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    case h_1 n lo hi l jv v hty ha hj hv =>
      split at h
      next => simp at h; subst h; exact lens_set env a _ _ ha (by simp [shape])
      next => simp at h
    case h_2 lo hi l jv v hty ha hj hv =>
      split at h
      next => simp at h; subst h; exact lens_set env a _ _ ha (by simp [shape])
      next => simp at h
    case h_3 => simp at h
  | ite a b s t ihs iht =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next => split at h
            next => exact ihs Γ env o h
            next => exact iht Γ env o h
    next => simp at h
  | decl lo hi e s ihs =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next v hv => split at h
                 next => exact popOut_lens h (fun o1 h1 => ihs _ _ o1 h1)
                 next => simp at h
    next => simp at h
  | forN n I s ihs =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next env' hl =>
      simp at h; subst h
      exact loop_lens _ (fun k e o hk => popOut_lens hk (fun o1 h1 => ihs _ _ o1 h1)) n 0 env env' hl
    next => simp at h
  | forE e I s ihs =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next n hn =>
      split at h
      next =>
        split at h
        next env' hl =>
          simp at h; subst h
          exact loop_lens _ (fun k e o hk => popOut_lens hk (fun o1 h1 => ihs _ _ o1 h1)) n.toNat 0 env env' hl
        next => simp at h
      next => simp at h
    next => simp at h
  | fassign x e =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next x0 v hty hx hv => simp at h; subst h; exact lens_set env x _ _ hx rfl
    next => simp at h
  | fstore a j e =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next l jv v hty ha hj hv =>
      split at h
      next => simp at h; subst h; exact lens_set env a _ _ ha (by simp [shape])
      next => simp at h
    next => simp at h
  | fdecl e s ihs =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next v hv => exact popOut_lens h (fun o1 h1 => ihs _ _ o1 h1)
    next => simp at h
  | fite a b s t ihs iht =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next => split at h
            next => exact ihs Γ env o h
            next => exact iht Γ env o h
    next => simp at h
  | loopB n I s ihs =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next env' hl =>
      simp at h; subst h
      exact loopBrk_lens _ (fun e o hk => ihs Γ e o hk) n env env' hl
    next => simp at h
  | note t s ihs =>
    intro Γ env o h
    simp only [execS] at h
    exact ihs Γ env o h
  | pmap f args e out =>
    intro Γ env o h
    obtain ⟨l, rs, ho, hle, rfl⟩ := exec_pmap_inv h
    exact lens_set env out _ _ ho (by simp [shape]; omega)
  | pmapF f args e out =>
    intro Γ env o h
    obtain ⟨l, rs, ho, hle, rfl⟩ := exec_pmapF_inv h
    exact lens_set env out _ _ ho (by simp [shape]; omega)
  | loopE e I s ihs =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next n hn =>
      split at h
      next env' hl =>
        simp at h; subst h
        exact loopBrk_lens _ (fun e o hk => ihs Γ e o hk) n.toNat env env' hl
      next => simp at h
    next => simp at h
  | call f args dst =>
    intro Γ env o h
    simp only [execS] at h
    split at h
    next => split at h
            next vs x0 hl hd =>
              split at h
              next r outs hr =>
                simp at h; subst h
                simp only [Out.env]
                have h1 : lens (env.set dst (.int r)) = lens env := lens_set env dst _ _ hd rfl
                exact writeBack_lens args vs outs env _ h1 hl (hc f vs r outs hr)
              next => simp at h
            next => simp at h
    next => simp at h

theorem evalFn_lens : ∀ (fns : List Fn), LensOk (evalFn fns) := by
  intro fns
  induction fns with
  | nil => intro i vs r outs h; simp [evalFn] at h
  | cons f rest ih =>
    intro i vs r outs h
    cases i with
    | zero =>
      simp only [evalFn] at h
      split at h
      next =>
        split at h
        next r' e hex =>
          simp at h; obtain ⟨_, rfl⟩ := h
          have h2 := exec_lens (evalFn rest) ih f.body _ _ _ hex
          simp [lens, Out.env] at h2 ⊢
          exact h2.2
        next => simp at h
      next => simp at h
    | succ j => simp only [evalFn] at h; exact ih j vs r outs h

/-! ## Obligations. They may assume that the environment has the types of Γ. -/

def wpE (Γ : List Ty) : Expr → List Val → (Int → Prop) → Prop
  | .lit n, _, Q => inI64 n ∧ Q n
  | .var i, env, Q => match Γ[i]? with
    | some (.int lo hi) => inI64 lo ∧ inI64 hi ∧ ∀ v, env[i]? = some (.int v) → lo ≤ v → v ≤ hi → Q v
    | _ => False
  | .add a b, env, Q => wpE Γ a env (fun x => wpE Γ b env (fun y => inI64 (x + y) ∧ Q (x + y)))
  | .sub a b, env, Q => wpE Γ a env (fun x => wpE Γ b env (fun y => inI64 (x - y) ∧ Q (x - y)))
  | .mul a b, env, Q => wpE Γ a env (fun x => wpE Γ b env (fun y => inI64 (x * y) ∧ Q (x * y)))
  | .div a b, env, Q => wpE Γ a env (fun x => wpE Γ b env (fun y => (0 ≤ x ∧ 0 < y) ∧ Q (x / y)))
  | .idx a e, env, Q => match Γ[a]? with
    | some (.arr n lo hi) => inI64 lo ∧ inI64 hi ∧ wpE Γ e env (fun j => 0 ≤ j ∧ j < n ∧
        ∀ l v, env[a]? = some (.arr l) → l[j.toNat]? = some v → lo ≤ v → v ≤ hi → Q v)
    | some (.slice lo hi) => inI64 lo ∧ inI64 hi ∧ wpE Γ e env (fun j =>
        ∀ l, env[a]? = some (.arr l) → 0 ≤ j ∧ j < l.length ∧
          ∀ v, l[j.toNat]? = some v → lo ≤ v → v ≤ hi → Q v)
    | _ => False
  | .le a b, env, Q => wpE Γ a env (fun x => wpE Γ b env (fun y => Q (if x ≤ y then 1 else 0)))
  | .lt a b, env, Q => wpE Γ a env (fun x => wpE Γ b env (fun y => Q (if x < y then 1 else 0)))
  | .eq a b, env, Q => wpE Γ a env (fun x => wpE Γ b env (fun y => Q (if x = y then 1 else 0)))
  | .sel c t e, env, Q => wpE Γ c env (fun cv => wpE Γ t env (fun x => wpE Γ e env (fun y =>
      Q (if cv ≠ 0 then x else y))))
  | .len a, env, Q => match Γ[a]? with
    | some (.arr n _ _) => inI64 (n : Int) ∧ Q n
    | some (.slice _ _) => ∀ l, env[a]? = some (.arr l) → (l.length : Int) ≤ 9223372036854775807 → Q l.length
    | some .fslice => ∀ l, env[a]? = some (.farr l) → (l.length : Int) ≤ 9223372036854775807 → Q l.length
    | _ => False

def wpF (Γ : List Ty) : FExpr → List Val → (Float → Prop) → Prop
  | .lit f, _, Q => Q f
  | .var i, env, Q => match Γ[i]? with
    | some .flt => ∀ v, env[i]? = some (.flt v) → Q v
    | _ => False
  | .add a b, env, Q => wpF Γ a env (fun x => wpF Γ b env (fun y => Q (x + y)))
  | .sub a b, env, Q => wpF Γ a env (fun x => wpF Γ b env (fun y => Q (x - y)))
  | .mul a b, env, Q => wpF Γ a env (fun x => wpF Γ b env (fun y => Q (x * y)))
  | .div a b, env, Q => wpF Γ a env (fun x => wpF Γ b env (fun y => Q (x / y)))
  | .idx a e, env, Q => match Γ[a]? with
    | some .fslice => wpE Γ e env (fun j => ∀ l, env[a]? = some (.farr l) → 0 ≤ j ∧ j < l.length ∧
        ∀ v, l[j.toNat]? = some v → Q v)
    | _ => False
  | .ofInt e, env, Q => wpE Γ e env (fun n => Q (Float.ofInt n))
  | .sel c t e, env, Q => wpE Γ c env (fun cv => wpF Γ t env (fun x => wpF Γ e env (fun y =>
      Q (if cv ≠ 0 then x else y))))
  | .neg a, env, Q => wpF Γ a env (fun x => Q (-x))
  | .abs a, env, Q => wpF Γ a env (fun x => Q x.abs)
  | .sqrt a, env, Q => wpF Γ a env (fun x => Q x.sqrt)
  | .selLe a b t e, env, Q => wpF Γ a env (fun x => wpF Γ b env (fun y => wpF Γ t env (fun u =>
      wpF Γ e env (fun v => Q (if x ≤ y then u else v)))))

/-- A label in the context of an obligation: always true, never unfolded by the tactics. It records
    which source statement an obligation comes from. -/
def Tag (_ : String) : Prop := True

theorem Tag.intro (s : String) : Tag s := trivial

attribute [irreducible] Tag

def popped (Q : List Val → Prop) : List Val → Prop
  | _ :: e3 => Q e3
  | [] => False

/-- Which caller variables receive the callee's inout parameters, with equal types. -/
def argsTyped (Γ : List Ty) : List (Ty × Bool) → List (Nat × Bool) → Prop
  | [], [] => True
  | (t, true) :: ps, (i, true) :: as => Γ[i]? = some t ∧ argsTyped Γ ps as
  | (_, false) :: ps, (_, false) :: as => argsTyped Γ ps as
  | _, _ => False

def wpS (rest : List Fn) (Γ : List Ty) : Stmt → List Val → (List Val → Prop) → (List Val → Prop) → Prop
  | .skip, env, Q, _ => Q env
  | .seq s t, env, Q, B => wpS rest Γ s env (fun env' => wpS rest Γ t env' Q B) B
  | .assign x e, env, Q, _ => match Γ[x]? with
    | some (.int lo hi) => wpE Γ e env (fun v => lo ≤ v ∧ v ≤ hi ∧ Q (env.set x (.int v)))
    | _ => False
  | .store a i e, env, Q, _ => match Γ[a]? with
    | some (.arr n lo hi) => wpE Γ i env (fun j => 0 ≤ j ∧ j < n ∧
        wpE Γ e env (fun v => lo ≤ v ∧ v ≤ hi ∧
          ∀ l, env[a]? = some (.arr l) → Q (env.set a (.arr (l.set j.toNat v)))))
    | some (.slice lo hi) => wpE Γ i env (fun j =>
        wpE Γ e env (fun v => lo ≤ v ∧ v ≤ hi ∧
          ∀ l, env[a]? = some (.arr l) → 0 ≤ j ∧ j < l.length ∧ Q (env.set a (.arr (l.set j.toNat v)))))
    | _ => False
  | .ite a b s t, env, Q, B => wpE Γ a env (fun x => wpE Γ b env (fun y =>
      (x ≤ y → wpS rest Γ s env Q B) ∧ (¬ x ≤ y → wpS rest Γ t env Q B)))
  | .decl lo hi e s, env, Q, B => wpE Γ e env (fun v => lo ≤ v ∧ v ≤ hi ∧
      wpS rest (.int lo hi :: Γ) s (.int v :: env) (popped Q) (popped B))
  | .forN n I s, env, Q, _ => I env 0 env ∧
      (∀ i env', i < n → hasAll Γ env' = true → sameAt (kept Γ s) env env' → lens env' = lens env → I env i env' →
        wpS rest (.int 0 n :: Γ) s (.int i :: env') (popped (I env (i + 1))) (popped Q)) ∧
      (∀ env', hasAll Γ env' = true → sameAt (kept Γ s) env env' → lens env' = lens env → I env n env' → Q env')
  | .brk, env, _, B => B env
  | .fassign x e, env, Q, _ => match Γ[x]? with
    | some .flt => wpF Γ e env (fun v => Q (env.set x (.flt v)))
    | _ => False
  | .fstore a i e, env, Q, _ => match Γ[a]? with
    | some .fslice => wpE Γ i env (fun j => wpF Γ e env (fun v =>
        ∀ l, env[a]? = some (.farr l) → 0 ≤ j ∧ j < l.length ∧ Q (env.set a (.farr (l.set j.toNat v)))))
    | _ => False
  | .fdecl e s, env, Q, B => wpF Γ e env (fun v => wpS rest (.flt :: Γ) s (.flt v :: env) (popped Q) (popped B))
  | .fite a b s t, env, Q, B => wpF Γ a env (fun x => wpF Γ b env (fun y =>
      (x ≤ y → wpS rest Γ s env Q B) ∧ (¬ x ≤ y → wpS rest Γ t env Q B)))
  | .forE e I s, env, Q, _ => wpE Γ e env (fun nv => 0 ≤ nv ∧ I env 0 env ∧
      (∀ (i : Nat) env', (i : Int) < nv → hasAll Γ env' = true → sameAt (kept Γ s) env env' → lens env' = lens env →
        I env i env' →
        wpS rest (.int 0 9223372036854775807 :: Γ) s (.int i :: env') (popped (I env (i + 1))) (popped Q)) ∧
      (∀ env', hasAll Γ env' = true → sameAt (kept Γ s) env env' → lens env' = lens env → I env nv.toNat env' → Q env'))
  | .note t s, env, Q, B => Tag t → wpS rest Γ s env Q B
  | .pmap f args e out, env, Q, _ => match rest[f]?, Γ[out]?, lookups env args, env[out]? with
    | some g, some (.slice lo hi), some vs, some (.arr l) =>
        args.contains out = false ∧ g.params.all (fun p => !p.2) = true ∧ lo ≤ g.rlo ∧ g.rhi ≤ hi ∧
        wpE Γ e env (fun nv => 0 ≤ nv ∧ nv ≤ l.length ∧
          (∀ i : Nat, (i : Int) < nv → hasAll (g.params.map (·.1)) (vs ++ [.int i]) = true ∧
              evalC g.req (vs ++ [.int i]) = true ∧ g.pre (vs ++ [.int i])) ∧
          ∀ rs : List Int, rs.length = nv.toNat → (∀ v ∈ rs, g.rlo ≤ v ∧ v ≤ g.rhi) →
            Q (env.set out (.arr (rs ++ l.drop nv.toNat))))
    | _, _, _, _ => False
  | .pmapF f args e out, env, Q, _ => match rest[f]?, Γ[out]?, lookups env args, env[out]? with
    | some g, some .fslice, some vs, some (.farr l) =>
        args.contains out = false ∧ g.params.dropLast.all (fun p => !p.2) = true ∧
        g.params.getLast? = some (.flt, true) ∧
        wpE Γ e env (fun nv => 0 ≤ nv ∧ nv ≤ l.length ∧
          (∀ i : Nat, (i : Int) < nv → hasAll (g.params.map (·.1)) (vs ++ [.int i, .flt 0.0]) = true ∧
              evalC g.req (vs ++ [.int i, .flt 0.0]) = true ∧ g.pre (vs ++ [.int i, .flt 0.0])) ∧
          ∀ rs : List Float, rs.length = nv.toNat → Q (env.set out (.farr (rs ++ l.drop nv.toNat))))
    | _, _, _, _ => False
  | .loopE e I s, env, Q, _ => wpE Γ e env (fun nv => I env 0 env ∧
      (∀ (i : Nat) env', i < nv.toNat → hasAll Γ env' = true → sameAt (keptB Γ s) env env' → lens env' = lens env →
        I env i env' → wpS rest Γ s env' (I env (i + 1)) Q) ∧
      (∀ env', hasAll Γ env' = true → sameAt (keptB Γ s) env env' → lens env' = lens env → I env nv.toNat env' → False))
  | .loopB n I s, env, Q, _ => I env 0 env ∧
      (∀ i env', i < n → hasAll Γ env' = true → sameAt (keptB Γ s) env env' → lens env' = lens env → I env i env' →
        wpS rest Γ s env' (I env (i + 1)) Q) ∧
      (∀ env', hasAll Γ env' = true → I env n env' → False)
  | .call f args dst, env, Q, _ => match rest[f]?, Γ[dst]?, lookups env (args.map (·.1)) with
    | some g, some (.int lo hi), some vs => exclusive args dst = true ∧ lo ≤ g.rlo ∧ g.rhi ≤ hi ∧
        argsTyped Γ g.params args ∧ hasAll (g.params.map (·.1)) vs = true ∧ evalC g.req vs = true ∧ g.pre vs ∧
        ∀ r outs, g.post vs r outs → g.rlo ≤ r → r ≤ g.rhi →
          hasAll (g.params.map (·.1)) outs = true → lens outs = lens vs →
          Q (writeBack (env.set dst (.int r)) args outs)
    | _, _, _ => False

def FnOk (rest : List Fn) (f : Fn) : Prop :=
  ∀ args, hasAll (f.params.map (·.1)) args = true → evalC f.req args = true → f.pre args →
    wpS rest (.int f.rlo f.rhi :: f.params.map (·.1)) f.body (.int f.rlo :: args)
      (fun e => match e with | .int r :: e' => f.post args r e' | _ => False) (fun _ => False)

/-- Declared ranges are inside 64 bits, also for parameters that are never read. -/
def tysI64 : List Ty → Prop
  | [] => True
  | .int lo hi :: ts => inI64 lo ∧ inI64 hi ∧ tysI64 ts
  | .arr _ lo hi :: ts => inI64 lo ∧ inI64 hi ∧ tysI64 ts
  | .slice lo hi :: ts => inI64 lo ∧ inI64 hi ∧ tysI64 ts
  | .flt :: ts => tysI64 ts
  | .fslice :: ts => tysI64 ts

def ProgOk : List Fn → Prop
  | [] => True
  | f :: rest => (f.rlo ≤ f.rhi ∧ inI64 f.rlo ∧ inI64 f.rhi) ∧
      (tysI64 (f.params.map (·.1)) ∧ condWf (f.params.map (·.1)) f.req = true) ∧ FnOk rest f ∧ ProgOk rest

def CalleesOk (rest : List Fn) (callee : Nat → List Val → Option (Int × List Val)) : Prop :=
  ∀ i g vs, rest[i]? = some g → hasAll (g.params.map (·.1)) vs = true → evalC g.req vs = true → g.pre vs →
    ∃ r outs, callee i vs = some (r, outs) ∧ g.rlo ≤ r ∧ r ≤ g.rhi ∧
      hasAll (g.params.map (·.1)) outs = true ∧ lens outs = lens vs ∧ g.post vs r outs

/-! ## Soundness -/

theorem has_int {v : Val} {lo hi : Int} (h : v.has (.int lo hi) = true) : ∃ x, v = .int x ∧ lo ≤ x ∧ x ≤ hi := by
  cases v <;> simp [Val.has] at h
  exact ⟨_, rfl, h⟩

theorem has_arr {v : Val} {n : Nat} {lo hi : Int} (h : v.has (.arr n lo hi) = true) :
    ∃ l, v = .arr l ∧ l.length = n ∧ ∀ x ∈ l, lo ≤ x ∧ x ≤ hi := by
  cases v <;> simp [Val.has] at h
  exact ⟨_, rfl, h.1, h.2⟩

theorem has_slice {v : Val} {lo hi : Int} (h : v.has (.slice lo hi) = true) :
    ∃ l, v = .arr l ∧ (l.length : Int) ≤ 9223372036854775807 ∧ ∀ x ∈ l, lo ≤ x ∧ x ≤ hi := by
  cases v <;> simp [Val.has] at h
  exact ⟨_, rfl, h.1, h.2⟩

theorem has_flt {v : Val} (h : v.has .flt = true) : ∃ x, v = .flt x := by
  cases v <;> simp [Val.has] at h
  exact ⟨_, rfl⟩

theorem has_fslice {v : Val} (h : v.has .fslice = true) :
    ∃ l, v = .farr l ∧ (l.length : Int) ≤ 9223372036854775807 := by
  cases v <;> simp [Val.has] at h
  exact ⟨_, rfl, h⟩

theorem hasAll_get : ∀ (Γ : List Ty) (env : List Val) (i : Nat) (t : Ty),
    hasAll Γ env = true → Γ[i]? = some t → ∃ v, env[i]? = some v ∧ v.has t = true := by
  intro Γ
  induction Γ with
  | nil => intro env i t _ h; simp at h
  | cons t0 Γ ih =>
    intro env i t h hi
    cases env with
    | nil => simp [hasAll] at h
    | cons v env =>
      simp [hasAll] at h
      cases i with
      | zero => simp at hi; subst hi; exact ⟨v, rfl, h.1⟩
      | succ j => simp at hi; simpa using ih env j t h.2 hi

theorem hasAll_set : ∀ (Γ : List Ty) (env : List Val) (i : Nat) (t : Ty) (v : Val),
    hasAll Γ env = true → Γ[i]? = some t → v.has t = true → hasAll Γ (env.set i v) = true := by
  intro Γ
  induction Γ with
  | nil => intro env i t v _ h; simp at h
  | cons t0 Γ ih =>
    intro env i t v h hi hv
    cases env with
    | nil => simp [hasAll] at h
    | cons w env =>
      simp [hasAll] at h
      cases i with
      | zero => simp at hi; subst hi; simp [hasAll, hv, h.2]
      | succ j => simp at hi; simp [hasAll, h.1, ih env j t v h.2 hi hv]

theorem writeBack_ok (Γ : List Ty) : ∀ (ps : List (Ty × Bool)) (args : List (Nat × Bool)) (outs env : List Val),
    hasAll Γ env = true → argsTyped Γ ps args → hasAll (ps.map (·.1)) outs = true →
    hasAll Γ (writeBack env args outs) = true := by
  intro ps
  induction ps with
  | nil =>
    intro args outs env h ha _
    cases args with
    | nil => simpa [writeBack] using h
    | cons a as => simp [argsTyped] at ha
  | cons p ps ih =>
    intro args outs env h ha ho
    obtain ⟨t, b⟩ := p
    cases args with
    | nil => cases b <;> simp [argsTyped] at ha
    | cons a as =>
      obtain ⟨i, b'⟩ := a
      cases outs with
      | nil => simp [hasAll] at ho
      | cons o outs =>
        simp [hasAll] at ho
        cases b <;> cases b' <;> simp [argsTyped] at ha
        · simpa [writeBack] using ih as outs env h ha ho.2
        · simpa [writeBack] using ih as outs _ (hasAll_set Γ env i t o h ha.1 ho.1) ha.2 ho.2

def Out.sat (Q B : List Val → Prop) : Out → Prop
  | .norm e => Q e
  | .brk e => B e

theorem wpE_sound (Γ : List Ty) (env : List Val) (hΓ : hasAll Γ env = true) (e : Expr) :
    ∀ (Q : Int → Prop), wpE Γ e env Q → ∃ r, evalE e env = some r ∧ Q r := by
  induction e with
  | lit n => intro Q h; exact ⟨n, by simp [evalE, h.1], h.2⟩
  | var i =>
    intro Q h
    simp only [wpE] at h
    split at h
    case h_2 => exact h.elim
    next lo hi hty =>
    obtain ⟨hwlo, hwhi, hq⟩ := h
    obtain ⟨v, hv, hhas⟩ := hasAll_get Γ env i _ hΓ hty
    obtain ⟨x, hx, h1, h2⟩ := has_int hhas
    subst hx
    have hx64 : inI64 x := by unfold inI64 at *; omega
    exact ⟨x, by simp [evalE, hv, hx64], hq x hv h1 h2⟩
  | add a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, hw, h2⟩ := ihb _ h1
    exact ⟨x + y, by simp [evalE, hx, hy, hw], h2⟩
  | sub a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, hw, h2⟩ := ihb _ h1
    exact ⟨x - y, by simp [evalE, hx, hy, hw], h2⟩
  | mul a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, hw, h2⟩ := ihb _ h1
    exact ⟨x * y, by simp [evalE, hx, hy, hw], h2⟩
  | div a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, hw, h2⟩ := ihb _ h1
    exact ⟨x / y, by simp [evalE, hx, hy, hw], h2⟩
  | idx a e ihe =>
    intro Q h
    simp only [wpE] at h
    split at h
    case h_1 n lo hi hty =>
      obtain ⟨hwlo, hwhi, h1⟩ := h
      obtain ⟨j, hj, h0, hlt, hq⟩ := ihe _ h1
      obtain ⟨v, hv, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen, hall⟩ := has_arr hhas
      subst hl
      have hlt' : j.toNat < l.length := by omega
      have hr := hall _ (List.getElem_mem hlt')
      have : j < l.length := by omega
      have hx64 : inI64 l[j.toNat] := by unfold inI64 at *; omega
      exact ⟨l[j.toNat], by simp [evalE, hv, hj, h0, this, hlt', hx64], hq l _ hv (by simp [hlt']) hr.1 hr.2⟩
    case h_2 lo hi hty =>
      obtain ⟨hwlo, hwhi, h1⟩ := h
      obtain ⟨j, hj, hq⟩ := ihe _ h1
      obtain ⟨v, hv, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen, hall⟩ := has_slice hhas
      subst hl
      obtain ⟨h0, hlt, hq⟩ := hq l hv
      have hlt' : j.toNat < l.length := by omega
      have hr := hall _ (List.getElem_mem hlt')
      have hx64 : inI64 l[j.toNat] := by unfold inI64 at *; omega
      exact ⟨l[j.toNat], by simp [evalE, hv, hj, h0, hlt, hlt', hx64], hq _ (by simp [hlt']) hr.1 hr.2⟩
    case h_3 => exact h.elim
  | le a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, h2⟩ := ihb _ h1
    exact ⟨_, by simp [evalE, hx, hy], h2⟩
  | lt a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, h2⟩ := ihb _ h1
    exact ⟨_, by simp [evalE, hx, hy], h2⟩
  | eq a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, h2⟩ := ihb _ h1
    exact ⟨_, by simp [evalE, hx, hy], h2⟩
  | sel c t e ihc iht ihe =>
    intro Q h
    obtain ⟨cv, hc, h1⟩ := ihc _ h
    obtain ⟨x, hx, h2⟩ := iht _ h1
    obtain ⟨y, hy, h3⟩ := ihe _ h2
    exact ⟨_, by simp [evalE, hc, hx, hy], h3⟩
  | len a =>
    intro Q h
    simp only [wpE] at h
    split at h
    case h_1 n lo hi hty =>
      obtain ⟨v, hv, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen, _⟩ := has_arr hhas
      subst hl
      have h64 : inI64 (l.length : Int) := by rw [hlen]; exact h.1
      exact ⟨l.length, by simp [evalE, hv, h64], by rw [hlen]; exact h.2⟩
    case h_2 lo hi hty =>
      obtain ⟨v, hv, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen, _⟩ := has_slice hhas
      subst hl
      have h64 : inI64 (l.length : Int) := by unfold inI64; omega
      exact ⟨l.length, by simp [evalE, hv, h64], h l hv hlen⟩
    case h_3 hty =>
      obtain ⟨v, hv, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen⟩ := has_fslice hhas
      subst hl
      have h64 : inI64 (l.length : Int) := by unfold inI64; omega
      exact ⟨l.length, by simp [evalE, hv, h64], h l hv hlen⟩
    case h_4 => exact h.elim

theorem wpF_sound (Γ : List Ty) (env : List Val) (hΓ : hasAll Γ env = true) (e : FExpr) :
    ∀ (Q : Float → Prop), wpF Γ e env Q → ∃ r, evalF e env = some r ∧ Q r := by
  induction e with
  | lit f => intro Q h; exact ⟨f, rfl, h⟩
  | var i =>
    intro Q h
    simp only [wpF] at h
    split at h
    case h_1 hty =>
      obtain ⟨v, hv, hhas⟩ := hasAll_get Γ env i _ hΓ hty
      obtain ⟨x, hx⟩ := has_flt hhas
      subst hx
      exact ⟨x, by simp [evalF, hv], h x hv⟩
    case h_2 => exact h.elim
  | add a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, h2⟩ := ihb _ h1
    exact ⟨_, by simp [evalF, hx, hy], h2⟩
  | sub a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, h2⟩ := ihb _ h1
    exact ⟨_, by simp [evalF, hx, hy], h2⟩
  | mul a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, h2⟩ := ihb _ h1
    exact ⟨_, by simp [evalF, hx, hy], h2⟩
  | div a b iha ihb =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, h2⟩ := ihb _ h1
    exact ⟨_, by simp [evalF, hx, hy], h2⟩
  | idx a e =>
    intro Q h
    simp only [wpF] at h
    split at h
    case h_1 hty =>
      obtain ⟨j, hj, hq⟩ := wpE_sound Γ env hΓ e _ h
      obtain ⟨v, hv, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen⟩ := has_fslice hhas
      subst hl
      obtain ⟨h0, hlt, hq⟩ := hq l hv
      have hlt' : j.toNat < l.length := by omega
      exact ⟨l[j.toNat], by simp [evalF, hv, hj, h0, hlt, hlt'], hq _ (by simp [hlt'])⟩
    case h_2 => exact h.elim
  | ofInt e =>
    intro Q h
    obtain ⟨n, hn, hq⟩ := wpE_sound Γ env hΓ e _ h
    exact ⟨_, by simp [evalF, hn], hq⟩
  | sel c t e iht ihe =>
    intro Q h
    obtain ⟨cv, hc, h1⟩ := wpE_sound Γ env hΓ c _ h
    obtain ⟨x, hx, h2⟩ := iht _ h1
    obtain ⟨y, hy, h3⟩ := ihe _ h2
    exact ⟨_, by simp [evalF, hc, hx, hy], h3⟩
  | neg a iha => intro Q h; obtain ⟨x, hx, h1⟩ := iha _ h; exact ⟨_, by simp [evalF, hx], h1⟩
  | abs a iha => intro Q h; obtain ⟨x, hx, h1⟩ := iha _ h; exact ⟨_, by simp [evalF, hx], h1⟩
  | sqrt a iha => intro Q h; obtain ⟨x, hx, h1⟩ := iha _ h; exact ⟨_, by simp [evalF, hx], h1⟩
  | selLe a b t e iha ihb iht ihe =>
    intro Q h
    obtain ⟨x, hx, h1⟩ := iha _ h
    obtain ⟨y, hy, h2⟩ := ihb _ h1
    obtain ⟨u, hu, h3⟩ := iht _ h2
    obtain ⟨v, hv, h4⟩ := ihe _ h3
    exact ⟨_, by simp [evalF, hx, hy, hu, hv], h4⟩

theorem popOut_sound (t : Ty) (Γ : List Ty) (o : Out) (Q B : List Val → Prop)
    (h : o.sat (fun e => hasAll (t :: Γ) e = true ∧ popped Q e) (fun e => hasAll (t :: Γ) e = true ∧ popped B e)) :
    ∃ o', popOut (some o) = some o' ∧ o'.sat (fun e => hasAll Γ e = true ∧ Q e) (fun e => hasAll Γ e = true ∧ B e) := by
  cases o with
  | norm e => cases e with
    | nil => exact absurd h.2 (by simp [popped])
    | cons w e3 => exact ⟨.norm e3, rfl, by have := h.1; simp [hasAll] at this; exact this.2, h.2⟩
  | brk e => cases e with
    | nil => exact absurd h.2 (by simp [popped])
    | cons w e3 => exact ⟨.brk e3, rfl, by have := h.1; simp [hasAll] at this; exact this.2, h.2⟩

theorem loop_sound (f : Nat → List Val → Option Out) (I : Nat → List Val → Prop) (Q : List Val → Prop) (n : Nat)
    (hstep : ∀ i env, i < n → I i env → ∃ o, f i env = some o ∧ o.sat (I (i + 1)) Q) :
    ∀ (k i : Nat) (env : List Val), i + k = n → I i env → ∃ env', loop f i k env = some env' ∧ (I n env' ∨ Q env') := by
  intro k
  induction k with
  | zero =>
    intro i env h hi
    have : i = n := by omega
    subst this; exact ⟨env, rfl, Or.inl hi⟩
  | succ k ih =>
    intro i env h hi
    obtain ⟨o, h1, ho⟩ := hstep i env (by omega) hi
    cases o with
    | norm env1 =>
      obtain ⟨env2, h2, hq⟩ := ih (i + 1) env1 (by omega) ho
      exact ⟨env2, by simp [loop, h1, h2], hq⟩
    | brk env1 => exact ⟨env1, by simp [loop, h1], Or.inr ho⟩

theorem loopBrk_sound (f : List Val → Option Out) (I : Nat → List Val → Prop) (Q : List Val → Prop) (n : Nat)
    (hstep : ∀ i env, i < n → I i env → ∃ o, f env = some o ∧ o.sat (I (i + 1)) Q)
    (hend : ∀ env, I n env → False) :
    ∀ (k i : Nat) (env : List Val), i + k = n → I i env → ∃ env', loopBrk f k env = some env' ∧ Q env' := by
  intro k
  induction k with
  | zero =>
    intro i env h hi
    have : i = n := by omega
    subst this; exact (hend env hi).elim
  | succ k ih =>
    intro i env h hi
    obtain ⟨o, h1, ho⟩ := hstep i env (by omega) hi
    cases o with
    | norm env1 =>
      obtain ⟨env2, h2, hq⟩ := ih (i + 1) env1 (by omega) ho
      exact ⟨env2, by simp [loopBrk, h1, h2], hq⟩
    | brk env1 => exact ⟨env1, by simp [loopBrk, h1], ho⟩

/-- The last value of a typed list whose last type is `f64` is a float. -/
theorem hasAll_last_flt : ∀ (ts : List Ty) (vs : List Val), hasAll ts vs = true → ts.getLast? = some .flt →
    ∃ v, vs.getLast? = some (.flt v) := by
  intro ts
  induction ts with
  | nil => intro vs _ h; simp at h
  | cons t ts ih =>
    intro vs hv ht
    cases vs with
    | nil => simp [hasAll] at hv
    | cons v vs =>
      simp [hasAll] at hv
      cases ts with
      | nil =>
        cases vs with
        | nil => simp at ht; subst ht; obtain ⟨x, rfl⟩ := has_flt hv.1; exact ⟨x, rfl⟩
        | cons _ _ => simp [hasAll] at hv
      | cons t' ts' =>
        cases vs with
        | nil => simp [hasAll] at hv
        | cons v' vs' =>
          have := ih (v' :: vs') hv.2 (by simpa [List.getLast?_cons_cons] using ht)
          simpa [List.getLast?_cons_cons] using this

/-- Statements: not stuck, the postcondition holds, and the environment still has its types. -/
theorem wpS_sound (rest : List Fn) (callee : Nat → List Val → Option (Int × List Val)) (hc : CalleesOk rest callee)
    (hlc : LensOk callee) (s : Stmt) : ∀ (Γ : List Ty) (env : List Val) (Q B : List Val → Prop),
      hasAll Γ env = true → wpS rest Γ s env Q B →
      ∃ o, execS callee Γ s env = some o ∧
        o.sat (fun e => hasAll Γ e = true ∧ Q e) (fun e => hasAll Γ e = true ∧ B e) := by
  induction s with
  | skip => intro Γ env Q B hΓ h; exact ⟨.norm env, rfl, hΓ, h⟩
  | brk => intro Γ env Q B hΓ h; exact ⟨.brk env, rfl, hΓ, h⟩
  | seq s t ihs iht =>
    intro Γ env Q B hΓ h
    obtain ⟨o1, h1, hq1⟩ := ihs Γ env _ B hΓ h
    cases o1 with
    | norm e1 =>
      obtain ⟨o2, h2, hq2⟩ := iht Γ e1 Q B hq1.1 hq1.2
      exact ⟨o2, by simp [execS, h1, h2], hq2⟩
    | brk e1 => exact ⟨.brk e1, by simp [execS, h1], hq1⟩
  | assign x e =>
    intro Γ env Q B hΓ h
    simp only [wpS] at h
    split at h
    case h_2 => exact h.elim
    next lo hi hty =>
    have he := h
    obtain ⟨v, hv, hlo, hhi, hq⟩ := wpE_sound Γ env hΓ e _ he
    obtain ⟨w0, hw0, hhas0⟩ := hasAll_get Γ env x _ hΓ hty
    obtain ⟨x0, hx0, _, _⟩ := has_int hhas0
    subst hx0
    refine ⟨.norm _, by simp [execS, hty, hw0, hv, hlo, hhi], ?_, hq⟩
    exact hasAll_set Γ env x _ _ hΓ hty (by simp [Val.has, hlo, hhi])
  | store a i e =>
    intro Γ env Q B hΓ h
    simp only [wpS] at h
    split at h
    case h_1 n lo hi hty =>
      obtain ⟨j, hj, h0, hlt, he⟩ := wpE_sound Γ env hΓ i _ h
      obtain ⟨v, hv, hlo, hhi, hq⟩ := wpE_sound Γ env hΓ e _ he
      obtain ⟨w, hw, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen, hall⟩ := has_arr hhas
      subst hl
      have hjl : j < l.length := by omega
      refine ⟨.norm _, by simp [execS, hty, hw, hj, hv, h0, hjl, hlo, hhi], ?_, hq l hw⟩
      apply hasAll_set Γ env a _ _ hΓ hty
      simp [Val.has, hlen]
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | hx
      · exact hall x hx
      · subst hx; exact ⟨hlo, hhi⟩
    case h_2 lo hi hty =>
      obtain ⟨j, hj, he⟩ := wpE_sound Γ env hΓ i _ h
      obtain ⟨v, hv, hlo, hhi, hq⟩ := wpE_sound Γ env hΓ e _ he
      obtain ⟨w, hw, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen, hall⟩ := has_slice hhas
      subst hl
      obtain ⟨h0, hjl, hq⟩ := hq l hw
      refine ⟨.norm _, by simp [execS, hty, hw, hj, hv, h0, hjl, hlo, hhi], ?_, hq⟩
      apply hasAll_set Γ env a _ _ hΓ hty
      simp [Val.has, hlen]
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | hx
      · exact hall x hx
      · subst hx; exact ⟨hlo, hhi⟩
    case h_3 => exact h.elim
  | ite a b s t ihs iht =>
    intro Γ env Q B hΓ h
    obtain ⟨x, hx, h1⟩ := wpE_sound Γ env hΓ a _ h
    obtain ⟨y, hy, hs, ht⟩ := wpE_sound Γ env hΓ b _ h1
    by_cases hxy : x ≤ y
    · obtain ⟨o, ho, hq⟩ := ihs Γ env Q B hΓ (hs hxy)
      exact ⟨o, by simp [execS, hx, hy, hxy, ho], hq⟩
    · obtain ⟨o, ho, hq⟩ := iht Γ env Q B hΓ (ht hxy)
      exact ⟨o, by simp [execS, hx, hy, hxy, ho], hq⟩
  | decl lo hi e s ihs =>
    intro Γ env Q B hΓ h
    obtain ⟨v, hv, hlo, hhi, h1⟩ := wpE_sound Γ env hΓ e _ h
    have hΓ' : hasAll (.int lo hi :: Γ) (.int v :: env) = true := by simp [hasAll, Val.has, hlo, hhi, hΓ]
    obtain ⟨o, ho, hsat⟩ := ihs _ _ _ _ hΓ' h1
    obtain ⟨o', ho', hsat'⟩ := popOut_sound _ Γ o Q B hsat
    exact ⟨o', by simp [execS, hv, hlo, hhi, ho, ho'], hsat'⟩
  | forN n I s ihs =>
    intro Γ env Q B hΓ h
    obtain ⟨h0, hstep, hend⟩ := h
    have hfr : ∀ (e : List Val), (∀ j, mods s (j + 1) = false → e[j]? = env[j]?) → sameAt (kept Γ s) env e := by
      intro e he
      apply sameAt_of
      intro k hk
      simp [kept] at hk
      exact he k hk.2
    have := loop_sound (fun i env => popOut (execS callee (.int 0 n :: Γ) s (.int i :: env)))
      (fun i e => (hasAll Γ e = true ∧ (∀ j, mods s (j + 1) = false → e[j]? = env[j]?) ∧ lens e = lens env) ∧ I env i e)
      (fun e => hasAll Γ e = true ∧ Q e) n
      (by
        intro i env' hi hI
        obtain ⟨⟨hty, hsm, hln⟩, hinv⟩ := hI
        have hΓ' : hasAll (.int 0 n :: Γ) (.int i :: env') = true := by
          simp [hasAll, Val.has, hty]; omega
        obtain ⟨o, ho, hsat⟩ := ihs _ _ _ _ hΓ' (hstep i env' hi hty (hfr env' hsm) hln hinv)
        obtain ⟨o', ho', hsat'⟩ := popOut_sound _ Γ o _ _ hsat
        have hpo : popOut (execS callee (.int 0 n :: Γ) s (.int i :: env')) = some o' := by rw [ho]; exact ho'
        have hkeep : ∀ j, mods s (j + 1) = false → o'.env[j]? = env[j]? := by
          intro j hj
          obtain ⟨o1, w, h1, h2⟩ := popOut_inv hpo
          have := exec_frame callee s _ _ o1 (j + 1) h1 hj
          rw [h2] at this
          rw [← hsm j hj]
          simpa using this
        have hlen : lens o'.env = lens env := by
          rw [← hln]; exact popOut_lens hpo (fun o1 h1 => exec_lens callee hlc s _ _ o1 h1)
        refine ⟨o', by simp [ho, ho'], ?_⟩
        cases o' with
        | norm e => exact ⟨⟨hsat'.1, hkeep, hlen⟩, hsat'.2⟩
        | brk e => exact hsat')
      n 0 env (by omega) ⟨⟨hΓ, fun _ _ => rfl, rfl⟩, h0⟩
    obtain ⟨env', hl, hI⟩ := this
    refine ⟨.norm env', by simp [execS, hl], ?_⟩
    cases hI with
    | inl h => exact ⟨h.1.1, hend env' h.1.1 (hfr env' h.1.2.1) h.1.2.2 h.2⟩
    | inr h => exact h
  | fassign x e =>
    intro Γ env Q B hΓ h
    simp only [wpS] at h
    split at h
    case h_1 hty =>
      obtain ⟨v, hv, hq⟩ := wpF_sound Γ env hΓ e _ h
      obtain ⟨w0, hw0, hhas0⟩ := hasAll_get Γ env x _ hΓ hty
      obtain ⟨x0, hx0⟩ := has_flt hhas0
      subst hx0
      refine ⟨.norm _, by simp [execS, hty, hw0, hv], ?_, hq⟩
      exact hasAll_set Γ env x _ _ hΓ hty (by simp [Val.has])
    case h_2 => exact h.elim
  | fstore a i e =>
    intro Γ env Q B hΓ h
    simp only [wpS] at h
    split at h
    case h_1 hty =>
      obtain ⟨j, hj, he⟩ := wpE_sound Γ env hΓ i _ h
      obtain ⟨v, hv, hq⟩ := wpF_sound Γ env hΓ e _ he
      obtain ⟨w, hw, hhas⟩ := hasAll_get Γ env a _ hΓ hty
      obtain ⟨l, hl, hlen⟩ := has_fslice hhas
      subst hl
      obtain ⟨h0, hjl, hq⟩ := hq l hw
      refine ⟨.norm _, by simp [execS, hty, hw, hj, hv, h0, hjl], ?_, hq⟩
      apply hasAll_set Γ env a _ _ hΓ hty
      simp [Val.has, hlen]
    case h_2 => exact h.elim
  | fdecl e s ihs =>
    intro Γ env Q B hΓ h
    obtain ⟨v, hv, h1⟩ := wpF_sound Γ env hΓ e _ h
    have hΓ' : hasAll (.flt :: Γ) (.flt v :: env) = true := by simp [hasAll, Val.has, hΓ]
    obtain ⟨o, ho, hsat⟩ := ihs _ _ _ _ hΓ' h1
    obtain ⟨o', ho', hsat'⟩ := popOut_sound _ Γ o Q B hsat
    exact ⟨o', by simp [execS, hv, ho, ho'], hsat'⟩
  | fite a b s t ihs iht =>
    intro Γ env Q B hΓ h
    obtain ⟨x, hx, h1⟩ := wpF_sound Γ env hΓ a _ h
    obtain ⟨y, hy, hs, ht⟩ := wpF_sound Γ env hΓ b _ h1
    by_cases hxy : x ≤ y
    · obtain ⟨o, ho, hq⟩ := ihs Γ env Q B hΓ (hs hxy)
      exact ⟨o, by simp [execS, hx, hy, hxy, ho], hq⟩
    · obtain ⟨o, ho, hq⟩ := iht Γ env Q B hΓ (ht hxy)
      exact ⟨o, by simp [execS, hx, hy, hxy, ho], hq⟩
  | forE e I s ihs =>
    intro Γ env Q B hΓ h
    obtain ⟨nv, hnv, hn0, h0, hstep, hend⟩ := wpE_sound Γ env hΓ e _ h
    have hn64 := evalE_i64 e env nv hnv
    have hfr : ∀ (e' : List Val), (∀ j, mods s (j + 1) = false → e'[j]? = env[j]?) → sameAt (kept Γ s) env e' := by
      intro e' he
      apply sameAt_of
      intro k hk
      simp [kept] at hk
      exact he k hk.2
    have := loop_sound (fun i env => popOut (execS callee (.int 0 9223372036854775807 :: Γ) s (.int i :: env)))
      (fun i e' => (hasAll Γ e' = true ∧ (∀ j, mods s (j + 1) = false → e'[j]? = env[j]?) ∧ lens e' = lens env) ∧ I env i e')
      (fun e' => hasAll Γ e' = true ∧ Q e') nv.toNat
      (by
        intro i env' hi hI
        obtain ⟨⟨hty, hsm, hln⟩, hinv⟩ := hI
        have hΓ' : hasAll (.int 0 9223372036854775807 :: Γ) (.int i :: env') = true := by
          simp [hasAll, Val.has, hty]; unfold inI64 at hn64; omega
        obtain ⟨o, ho, hsat⟩ := ihs _ _ _ _ hΓ' (hstep i env' (by omega) hty (hfr env' hsm) hln hinv)
        obtain ⟨o', ho', hsat'⟩ := popOut_sound _ Γ o _ _ hsat
        have hpo : popOut (execS callee (.int 0 9223372036854775807 :: Γ) s (.int i :: env')) = some o' := by
          rw [ho]; exact ho'
        have hkeep : ∀ j, mods s (j + 1) = false → o'.env[j]? = env[j]? := by
          intro j hj
          obtain ⟨o1, w, h1, h2⟩ := popOut_inv hpo
          have := exec_frame callee s _ _ o1 (j + 1) h1 hj
          rw [h2] at this
          rw [← hsm j hj]
          simpa using this
        have hlen : lens o'.env = lens env := by
          rw [← hln]; exact popOut_lens hpo (fun o1 h1 => exec_lens callee hlc s _ _ o1 h1)
        refine ⟨o', by simp [ho, ho'], ?_⟩
        cases o' with
        | norm e' => exact ⟨⟨hsat'.1, hkeep, hlen⟩, hsat'.2⟩
        | brk e' => exact hsat')
      nv.toNat 0 env (by omega) ⟨⟨hΓ, fun _ _ => rfl, rfl⟩, h0⟩
    obtain ⟨env', hl, hI⟩ := this
    refine ⟨.norm env', by simp [execS, hnv, hn0, hl], ?_⟩
    cases hI with
    | inl h => exact ⟨h.1.1, hend env' h.1.1 (hfr env' h.1.2.1) h.1.2.2 h.2⟩
    | inr h => exact h
  | loopB n I s ihs =>
    intro Γ env Q B hΓ h
    obtain ⟨h0, hstep, hend⟩ := h
    have hfr : ∀ (e : List Val), (∀ j, mods s j = false → e[j]? = env[j]?) → sameAt (keptB Γ s) env e := by
      intro e he
      apply sameAt_of
      intro k hk
      simp [keptB] at hk
      exact he k hk.2
    have := loopBrk_sound (fun env => execS callee Γ s env)
      (fun i e => (hasAll Γ e = true ∧ (∀ j, mods s j = false → e[j]? = env[j]?) ∧ lens e = lens env) ∧ I env i e)
      (fun e => hasAll Γ e = true ∧ Q e) n
      (by
        intro i env' hi hI
        obtain ⟨⟨hty, hsm, hln⟩, hinv⟩ := hI
        obtain ⟨o, ho, hsat⟩ := ihs Γ env' _ _ hty (hstep i env' hi hty (hfr env' hsm) hln hinv)
        have hkeep : ∀ j, mods s j = false → o.env[j]? = env[j]? := by
          intro j hj
          rw [← hsm j hj]
          exact exec_frame callee s Γ env' o j ho hj
        have hlen : lens o.env = lens env := by rw [← hln]; exact exec_lens callee hlc s Γ env' o ho
        refine ⟨o, ho, ?_⟩
        cases o with
        | norm e => exact ⟨⟨hsat.1, hkeep, hlen⟩, hsat.2⟩
        | brk e => exact hsat)
      (by intro e he; exact hend e he.1.1 he.2)
      n 0 env (by omega) ⟨⟨hΓ, fun _ _ => rfl, rfl⟩, h0⟩
    obtain ⟨env', hl, hq⟩ := this
    exact ⟨.norm env', by simp [execS, hl], hq⟩
  | note t s ihs =>
    intro Γ env Q B hΓ h
    obtain ⟨o, ho, hs⟩ := ihs Γ env Q B hΓ (h (Tag.intro t))
    exact ⟨o, by simp [execS, ho], hs⟩
  | pmap f args e out =>
    intro Γ env Q B hΓ h
    simp only [wpS] at h
    split at h
    · rename_i g lo hi vs l hg hty hl ho
      obtain ⟨hno, _, hlo, hhi, he⟩ := h
      obtain ⟨nv, hnv, h0, hle, hcalls, hQ⟩ := wpE_sound Γ env hΓ e _ he
      obtain ⟨rs, hrs, hlen, hrange⟩ := mapN_sound
        (fun i => match callee f (vs ++ [.int i]) with | some (r, _) => some r | none => none)
        (fun r => g.rlo ≤ r ∧ r ≤ g.rhi) nv.toNat (by
          intro i hi
          obtain ⟨h1, h2, h3⟩ := hcalls i (by omega)
          obtain ⟨r, outs, hr, hr1, hr2, _, _, _⟩ := hc f g _ hg h1 h2 h3
          exact ⟨r, by simp [hr], hr1, hr2⟩)
      obtain ⟨w, hw, hhas⟩ := hasAll_get Γ env out _ hΓ hty
      rw [ho] at hw
      cases hw
      obtain ⟨l', hl', hlen', hall⟩ := has_slice hhas
      cases hl'
      have hall_rs : rs.all (fun v => decide (lo ≤ v ∧ v ≤ hi)) = true := by
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro v hv; have := hrange v hv; omega
      refine ⟨.norm _, by
        simp [execS, hty, ho, hl, hnv, h0, hle, hrs]
        exact ⟨by simpa using hno, fun v hv => by have := hrange v hv; omega⟩, ?_, hQ rs hlen hrange⟩
      apply hasAll_set Γ env out _ _ hΓ hty
      simp only [Val.has, List.length_append, List.length_drop, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_append]
      refine ⟨by omega, ?_⟩
      intro v hv
      rcases hv with hv | hv
      · have := hrange v hv; exact ⟨by omega, by omega⟩
      · exact hall v (List.mem_of_mem_drop hv)
    · exact h.elim
  | pmapF f args e out =>
    intro Γ env Q B hΓ h
    simp only [wpS] at h
    split at h
    · rename_i g vs l hg hty hl ho
      obtain ⟨hno, _, hlast, he⟩ := h
      obtain ⟨nv, hnv, h0, hle, hcalls, hQ⟩ := wpE_sound Γ env hΓ e _ he
      obtain ⟨rs, hrs, hlen, _⟩ := mapN_sound
        (fun i => match callee f (vs ++ [.int i, .flt 0.0]) with
            | some (_, outs) => (match outs.getLast? with | some (.flt v) => some v | _ => none)
            | none => none)
        (fun _ => True) nv.toNat (by
          intro i hi
          obtain ⟨h1, h2, h3⟩ := hcalls i (by omega)
          obtain ⟨r, outs, hr, _, _, houts, _, _⟩ := hc f g _ hg h1 h2 h3
          have hl2 : (g.params.map (·.1)).getLast? = some .flt := by
            rw [List.getLast?_map, hlast]; rfl
          obtain ⟨v, hv⟩ := hasAll_last_flt _ outs houts hl2
          exact ⟨v, by simp [hr, hv], trivial⟩)
      obtain ⟨w, hw, hhas⟩ := hasAll_get Γ env out _ hΓ hty
      rw [ho] at hw
      cases hw
      obtain ⟨l', hl', hlen'⟩ := has_fslice hhas
      cases hl'
      refine ⟨.norm _, by
        simp [execS, hty, ho, hl, hnv, h0, hle, hrs]
        simpa using hno, ?_, hQ rs hlen⟩
      apply hasAll_set Γ env out _ _ hΓ hty
      simp only [Val.has, List.length_append, List.length_drop, decide_eq_true_eq]
      omega
    · exact h.elim
  | loopE e I s ihs =>
    intro Γ env Q B hΓ h
    obtain ⟨nv, hnv, h0, hstep, hend⟩ := wpE_sound Γ env hΓ e _ h
    have hfr : ∀ (e' : List Val), (∀ j, mods s j = false → e'[j]? = env[j]?) → sameAt (keptB Γ s) env e' := by
      intro e' he
      apply sameAt_of
      intro k hk
      simp [keptB] at hk
      exact he k hk.2
    have := loopBrk_sound (fun env => execS callee Γ s env)
      (fun i e' => (hasAll Γ e' = true ∧ (∀ j, mods s j = false → e'[j]? = env[j]?) ∧ lens e' = lens env) ∧ I env i e')
      (fun e' => hasAll Γ e' = true ∧ Q e') nv.toNat
      (by
        intro i env' hi hI
        obtain ⟨⟨hty, hsm, hln⟩, hinv⟩ := hI
        obtain ⟨o, ho, hsat⟩ := ihs Γ env' _ _ hty (hstep i env' hi hty (hfr env' hsm) hln hinv)
        have hkeep : ∀ j, mods s j = false → o.env[j]? = env[j]? := by
          intro j hj
          rw [← hsm j hj]
          exact exec_frame callee s Γ env' o j ho hj
        have hlen : lens o.env = lens env := by rw [← hln]; exact exec_lens callee hlc s Γ env' o ho
        refine ⟨o, ho, ?_⟩
        cases o with
        | norm e' => exact ⟨⟨hsat.1, hkeep, hlen⟩, hsat.2⟩
        | brk e' => exact hsat)
      (by intro e' he; exact hend e' he.1.1 (hfr e' he.1.2.1) he.1.2.2 he.2)
      nv.toNat 0 env (by omega) ⟨⟨hΓ, fun _ _ => rfl, rfl⟩, h0⟩
    obtain ⟨env', hl, hq⟩ := this
    exact ⟨.norm env', by simp [execS, hnv, hl], hq⟩
  | call f args dst =>
    intro Γ env Q B hΓ h
    simp only [wpS] at h
    split at h
    case h_2 => exact h.elim
    next g lo hi vs hg hdst hl =>
    obtain ⟨hex, hlo, hhi, hat, hin, hreq, hpre, hpost⟩ := h
    obtain ⟨r, outs, hr, hr1, hr2, houts, hlo', hp⟩ := hc f g vs hg hin hreq hpre
    obtain ⟨w, hw, hhas⟩ := hasAll_get Γ env dst _ hΓ hdst
    obtain ⟨x, hx, _, _⟩ := has_int hhas
    subst hx
    refine ⟨.norm _, by simp [execS, hex, hl, hw, hr], ?_, hpost r outs hp hr1 hr2 houts hlo'⟩
    apply writeBack_ok Γ g.params args outs _ _ hat houts
    exact hasAll_set Γ env dst _ _ hΓ hdst (by simp [Val.has]; omega)

/-- T2 for K3. A checked function called with arguments of its parameter types that satisfy its
    precondition is never stuck; its result is in its declared range, the final parameter values still
    have the parameter types, and the postcondition holds. -/
theorem prog_sound : ∀ (fns : List Fn), ProgOk fns → CalleesOk fns (evalFn fns) := by
  intro fns
  induction fns with
  | nil => intro _ i g vs h; simp at h
  | cons f rest ih =>
    intro hok i g vs hg hin hreq hpre
    obtain ⟨⟨hrange, _, _⟩, _, hf, hrest⟩ := hok
    cases i with
    | zero =>
      simp at hg; subst hg
      have hΓ : hasAll (.int f.rlo f.rhi :: f.params.map (·.1)) (.int f.rlo :: vs) = true := by
        simp [hasAll, Val.has, hin, hrange]
      obtain ⟨o, ho, hsat⟩ := wpS_sound rest (evalFn rest) (ih hrest) (evalFn_lens rest) f.body _ _ _ _ hΓ (hf vs hin hreq hpre)
      cases o with
      | norm e =>
        obtain ⟨hty, hp⟩ := hsat
        match e, hty, hp with
        | .int r :: e', hty, hp =>
          simp [hasAll, Val.has] at hty
          have hev : evalFn (f :: rest) 0 vs = some (r, e') := by simp [evalFn, hin, ho]
          exact ⟨r, e', hev, hty.1.1, hty.1.2, hty.2, evalFn_lens (f :: rest) 0 vs r e' hev, hp⟩
        | [], _, hp => exact absurd hp (by simp)
        | .arr _ :: _, _, hp => exact absurd hp (by simp)
      | brk e => exact absurd hsat.2 (by simp)
    | succ j =>
      simp at hg
      obtain ⟨r, outs, hr, h1, h2, h3, hq⟩ := ih hrest j g vs hg hin hreq hpre
      exact ⟨r, outs, by simp [evalFn, hr], h1, h2, h3, hq⟩

theorem hasAll_cons_inv {t : Ty} {Γ : List Ty} {env : List Val} (h : hasAll (t :: Γ) env = true) :
    ∃ v env', env = v :: env' ∧ v.has t = true ∧ hasAll Γ env' = true := by
  cases env with
  | nil => simp [hasAll] at h
  | cons v env' => simp [hasAll] at h; exact ⟨v, env', rfl, h.1, h.2⟩

theorem hasAll_nil_inv {env : List Val} (h : hasAll [] env = true) : env = [] := by
  cases env with
  | nil => rfl
  | cons v env' => simp [hasAll] at h

theorem open_int {lo hi : Int} {Γ : List Ty} {env : List Val} {P : Prop}
    (k : ∀ x env', env = .int x :: env' → lo ≤ x → x ≤ hi → hasAll Γ env' = true → P) :
    hasAll (.int lo hi :: Γ) env = true → P := by
  intro h
  obtain ⟨v, env', rfl, hv, hrest⟩ := hasAll_cons_inv h
  obtain ⟨x, rfl, h1, h2⟩ := has_int hv
  exact k x env' rfl h1 h2 hrest

theorem open_arr {n : Nat} {lo hi : Int} {Γ : List Ty} {env : List Val} {P : Prop}
    (k : ∀ l env', env = .arr l :: env' → l.length = n → (∀ x ∈ l, lo ≤ x ∧ x ≤ hi) → hasAll Γ env' = true → P) :
    hasAll (.arr n lo hi :: Γ) env = true → P := by
  intro h
  obtain ⟨v, env', rfl, hv, hrest⟩ := hasAll_cons_inv h
  obtain ⟨l, rfl, h1, h2⟩ := has_arr hv
  exact k l env' rfl h1 h2 hrest

theorem open_slice {lo hi : Int} {Γ : List Ty} {env : List Val} {P : Prop}
    (k : ∀ l env', env = .arr l :: env' → (l.length : Int) ≤ 9223372036854775807 → (∀ x ∈ l, lo ≤ x ∧ x ≤ hi) →
      hasAll Γ env' = true → P) :
    hasAll (.slice lo hi :: Γ) env = true → P := by
  intro h
  obtain ⟨v, env', rfl, hv, hrest⟩ := hasAll_cons_inv h
  obtain ⟨l, rfl, h1, h2⟩ := has_slice hv
  exact k l env' rfl h1 h2 hrest

theorem open_flt {Γ : List Ty} {env : List Val} {P : Prop}
    (k : ∀ x env', env = .flt x :: env' → hasAll Γ env' = true → P) : hasAll (.flt :: Γ) env = true → P := by
  intro h
  obtain ⟨v, env', rfl, hv, hrest⟩ := hasAll_cons_inv h
  obtain ⟨x, rfl⟩ := has_flt hv
  exact k x env' rfl hrest

theorem open_fslice {Γ : List Ty} {env : List Val} {P : Prop}
    (k : ∀ l env', env = .farr l :: env' → (l.length : Int) ≤ 9223372036854775807 → hasAll Γ env' = true → P) :
    hasAll (.fslice :: Γ) env = true → P := by
  intro h
  obtain ⟨v, env', rfl, hv, hrest⟩ := hasAll_cons_inv h
  obtain ⟨l, rfl, h1⟩ := has_fslice hv
  exact k l env' rfl h1 hrest

theorem open_nil {env : List Val} {P : Prop} (k : env = [] → P) : hasAll [] env = true → P :=
  fun h => k (hasAll_nil_inv h)

/-- Turn "the environment has the types of Γ" (Γ a literal list) into one value per variable, each with
    its range or shape as a hypothesis. -/
macro "env_open" h:ident : tactic =>
  `(tactic| (
      revert $h
      repeat (first
        | (apply open_int; intro _ _ heq _ _; subst heq)
        | (apply open_arr; intro _ _ heq _ _; subst heq)
        | (apply open_slice; intro _ _ heq _ _; subst heq)
        | (apply open_flt; intro _ _ heq; subst heq)
        | (apply open_fslice; intro _ _ heq _; subst heq))
      apply open_nil; intro heq; subst heq))

open Lean Elab Tactic Meta in
/-- Like `env_open`, but the values get the names of the source variables when the context contains a
    label (`Tag "@pos|n0,n1,..."`, newest label wins) whose name list fits. Names only make failed
    obligations readable; they change nothing in what is proved. -/
elab "env_open_tagged" h:ident : tactic => withMainContext do
  let lctx ← getLCtx
  let mut names : List String := []
  for d in lctx do
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Tenon.Tag 1 then
      if let .lit (.strVal str) := t.appArg! then
        names := ((str.splitOn "|").getD 1 "").splitOn ","
  evalTactic (← `(tactic| revert $h))
  for n in names do
    if n.isEmpty then continue
    let id := mkIdent (Name.mkSimple n)
    evalTactic (← `(tactic| first
      | (apply open_int; intro $id:ident _ heq _ _; subst heq)
      | (apply open_arr; intro $id:ident _ heq _ _; subst heq)
      | (apply open_slice; intro $id:ident _ heq _ _; subst heq)
      | (apply open_flt; intro $id:ident _ heq; subst heq)
      | (apply open_fslice; intro $id:ident _ heq _; subst heq)
      | skip))
  evalTactic (← `(tactic| repeat (first
      | (apply open_int; intro _ _ heq _ _; subst heq)
      | (apply open_arr; intro _ _ heq _ _; subst heq)
      | (apply open_slice; intro _ _ heq _ _; subst heq)
      | (apply open_flt; intro _ _ heq; subst heq)
      | (apply open_fslice; intro _ _ heq _; subst heq))))
  evalTactic (← `(tactic| (apply open_nil; intro heq; subst heq)))

/-! ### Products of two bounded integers (price times quantity)
    The arithmetic procedure is linear. For a product of two variables it needs the product's bounds as
    a fact; this lemma and tactic supply them from the constant bounds of the factors. -/

theorem mul_abs_bound (a b A B : Int) (ha : -A ≤ a ∧ a ≤ A) (hb : -B ≤ b ∧ b ≤ B) :
    -(A * B) ≤ a * b ∧ a * b ≤ A * B := by
  have hA : (a.natAbs : Int) ≤ A := by omega
  have hB : (b.natAbs : Int) ≤ B := by omega
  have hA0 : 0 ≤ A := by omega
  have hm : ((a * b).natAbs : Int) = (a.natAbs : Int) * (b.natAbs : Int) := by
    rw [Int.natAbs_mul]; simp
  have hle : (a.natAbs : Int) * (b.natAbs : Int) ≤ A * B :=
    Int.mul_le_mul hA hB (by omega) hA0
  have h12 : -((a * b).natAbs : Int) ≤ a * b ∧ a * b ≤ ((a * b).natAbs : Int) := by omega
  omega

open Lean Elab Tactic Meta in
/-- For every product of two non-constant integer terms in the goal whose factors have constant bounds
    among the hypotheses, add the bound of the product. Fails if it adds nothing. -/
elab "mul_bounds" : tactic => withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let lctx ← getLCtx
  -- constant bounds of a term: (lower, upper)
  let boundsOf (e : Lean.Expr) : MetaM (Option Int × Option Int) := do
    let mut lo : Option Int := none
    let mut hi : Option Int := none
    for d in lctx do
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``LE.le 4 then
        let l := t.getArg! 2
        let r := t.getArg! 3
        if r == e then
          if let some n := l.int? then lo := some (match lo with | some m => max m n | none => n)
        if l == e then
          if let some n := r.int? then hi := some (match hi with | some m => min m n | none => n)
    return (lo, hi)
  -- collect products
  let prods : IO.Ref (Array (Lean.Expr × Lean.Expr)) ← IO.mkRef #[]
  let _ ← Meta.transform tgt (pre := fun e => do
    if e.isAppOfArity ``HMul.hMul 6 then
      let a := e.getArg! 4
      let b := e.getArg! 5
      if a.int?.isNone && b.int?.isNone && (← inferType e).isConstOf ``Int then
        prods.modify (fun ps => if ps.contains (a, b) then ps else ps.push (a, b))
    return .continue)
  let mut added := 0
  for (a, b) in (← prods.get) do
    let (la, ua) ← boundsOf a
    let (lb, ub) ← boundsOf b
    match la, ua, lb, ub with
    | some la, some ua, some lb, some ub =>
      let A : Int := max la.natAbs ua.natAbs
      let B : Int := max lb.natAbs ub.natAbs
      let sa ← Term.exprToSyntax a
      let sb ← Term.exprToSyntax b
      let sA := Syntax.mkNumLit (toString A.toNat)
      let sB := Syntax.mkNumLit (toString B.toNat)
      evalTactic (← `(tactic| have := mul_abs_bound $sa $sb $sA $sB (by omega) (by omega)))
      added := added + 1
    | _, _, _, _ => pure ()
  if added == 0 then throwError "mul_bounds: no product with constant bounds found"

/-! ### Division by a variable (a mean: a sum divided by a length) -/

theorem div_bound (a b c : Int) (ha : 0 ≤ a) (hb : 0 < b) (h : a ≤ c * b) : 0 ≤ a / b ∧ a / b ≤ c :=
  ⟨Int.ediv_nonneg ha (by omega), Int.ediv_le_of_le_mul hb h⟩

theorem div_self_bound (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b ∧ a / b ≤ a :=
  ⟨Int.ediv_nonneg ha (by omega), Int.ediv_le_self b ha⟩

open Lean Elab Tactic Meta in
/-- For every quotient `a / b` in the goal with a non-constant divisor, add `0 ≤ a / b ≤ c` when a
    hypothesis `a ≤ c * b` with a constant `c` exists, else `0 ≤ a / b ≤ a`. Fails if it adds nothing. -/
elab "div_bounds" : tactic => withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let lctx ← getLCtx
  let quots : IO.Ref (Array (Lean.Expr × Lean.Expr)) ← IO.mkRef #[]
  let _ ← Meta.transform tgt (pre := fun e => do
    if e.isAppOfArity ``HDiv.hDiv 6 then
      let a := e.getArg! 4
      let b := e.getArg! 5
      if b.int?.isNone && (← inferType e).isConstOf ``Int then
        quots.modify (fun ps => if ps.contains (a, b) then ps else ps.push (a, b))
    return .continue)
  let mut added := 0
  for (a, b) in (← quots.get) do
    let sa ← Term.exprToSyntax a
    let sb ← Term.exprToSyntax b
    let mut c : Option Int := none
    for d in lctx do
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``LE.le 4 && t.getArg! 2 == a then
        let r := t.getArg! 3
        if r.isAppOfArity ``HMul.hMul 6 && r.getArg! 5 == b then
          if let some n := (r.getArg! 4).int? then
            c := some (match c with | some m => min m n | none => n)
    try
      match c with
      | some n =>
        let sc := Syntax.mkNumLit (toString n.toNat)
        if n < 0 then throwError "negative bound"
        evalTactic (← `(tactic| have := div_bound $sa $sb $sc (by omega) (by omega) (by omega)))
      | none =>
        evalTactic (← `(tactic| have := div_self_bound $sa $sb (by omega) (by omega)))
      added := added + 1
    catch _ => pure ()
  if added == 0 then throwError "div_bounds: no quotient with a provable bound found"

/-! ### Element reasoning, for postconditions and invariants about array contents

    `elem_facts`: for every hypothesis `l[i]? = some v` add `l[i]?.getD 0 = v`, and for every two element
    reads of the same list whose indices are provably equal (by `omega`) add that they are equal; then
    linear arithmetic can treat element reads as variables. `inst_foralls`: instantiate every hypothesis
    `∀ j : Int, a ≤ j → j < b → P j` at every integer variable in scope for which `a ≤ j < b` is provable.
    Both run their sub-proofs without error recovery, so a failed attempt adds nothing (it cannot turn
    into an unproved fact). -/

open Lean in
/-- `l[i]?.getD 0` for a list of integers: the atoms of element reasoning. -/
def elemAtom? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``Option.getD 3 then
    let o := e.getArg! 1
    if o.isAppOf ``GetElem?.getElem? && o.getAppNumArgs ≥ 2 then
      let n := o.getAppNumArgs
      some (o.getArg! (n - 2), o.getArg! (n - 1))
    else none
  else none

open Lean Elab Tactic Meta in
/-- For every hypothesis `l[i]? = some v`, add `l[i]?.getD 0 = v`. -/
def hypFacts : Lean.Elab.Tactic.TacticM Unit := withMainContext do
  -- hypotheses l[i]? = some v
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Eq 3 then
      let lhs := t.getArg! 1
      let rhs := t.getArg! 2
      if lhs.isAppOf ``GetElem?.getElem? && rhs.isAppOfArity ``Option.some 2 then
        let h ← Term.exprToSyntax d.toExpr
        let sl ← Term.exprToSyntax lhs
        let sv ← Term.exprToSyntax (rhs.getArg! 1)
        try withoutRecover <| evalTactic (← `(tactic| have : Option.getD $sl (0 : Int) = $sv := by rw [$h:term]; rfl))
        catch _ => pure ()

open Lean Elab Tactic Meta in
/-- For every element read in the goal and every other read of the same list (in the goal or in a
    hypothesis), add "equal indices give equal elements" as an implication. -/
def pairFacts : Lean.Elab.Tactic.TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let collect (e : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
      MetaM (Array (Lean.Expr × Lean.Expr × Lean.Expr)) := do
    let r ← IO.mkRef acc
    let _ ← Meta.transform e (pre := fun x => do
      if let some (l, i) := elemAtom? x then
        r.modify (fun a => if a.any (fun p => p.1 == x) then a else a.push (x, l, i))
      return .continue)
    r.get
  let inGoal ← collect (← instantiateMVars (← goal.getType)) #[]
  let mut all := inGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    all ← collect (← instantiateMVars d.type) all
  for a in inGoal do
    for b in all do
      if a.1 == b.1 then continue
      if !(← isDefEq a.2.1 b.2.1) then continue
      let ia ← Term.exprToSyntax a.2.2
      let ib ← Term.exprToSyntax b.2.2
      let la ← Term.exprToSyntax a.2.1
      let sa ← Term.exprToSyntax a.1
      let sb ← Term.exprToSyntax b.1
      try
        withoutRecover <| evalTactic (← `(tactic| have : $ia = $ib → $sa = $sb :=
          fun hk => congrArg (fun k => Option.getD (($la)[k]?) (0 : Int)) hk))
      catch _ => pure ()

open Lean Elab Tactic in
elab "elem_facts" : tactic => do
  hypFacts
  pairFacts


open Lean Elab Tactic Meta in
/-- Instantiate every hypothesis `∀ j : Int, ...` at every integer variable that occurs in an index of
    an element read in the goal, as an implication `a ≤ v → v < b → P v`. -/
elab "inst_foralls" : tactic => withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let idxVars : IO.Ref (Array Lean.Expr) ← IO.mkRef #[]
  let _ ← Meta.transform tgt (pre := fun x => do
    if let some (_, i) := elemAtom? x then
      let _ ← Meta.transform i (pre := fun y => do
        if y.isFVar && (← inferType y).isConstOf ``Int then
          idxVars.modify (fun a => if a.contains y then a else a.push y)
        return .continue)
    return .continue)
  let vs ← idxVars.get
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let .forallE _ ty _ _ := t then
      if ty.isConstOf ``Int then
        for v in vs do
          let sh ← Term.exprToSyntax d.toExpr
          let sv ← Term.exprToSyntax v
          try withoutRecover <| evalTactic (← `(tactic| have := $sh $sv))
          catch _ => pure ()

macro "elem_close" : tactic =>
  `(tactic| ((try simp only [Option.getD_some, Option.getD_none] at *); inst_foralls; elem_facts; omega))

macro "vc_leaves" : tactic =>
  `(tactic| repeat' (first | (intro _) | omega | (apply And.intro) | assumption | (with_reducible rfl) |
      (simp [inI64]; done) | (simp only [inI64]; omega) | constructor))

/-- One loop obligation, after `intro`: open the typed environment, use what the kernel knows about the
    unchanged variables and the array lengths, unfold with the given definitions (the invariant and the
    accessors it uses), and close the arithmetic. -/
syntax "vc_loop" ident ident ident "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| vc_loop $hΓ:ident $hsame:ident $hlens:ident [$defs,*]) =>
    `(tactic| (
        env_open $hΓ
        try simp [sameAt, kept, keptB, mods, List.range, List.range.loop, List.filter] at $hsame:ident
        try simp [lens, shape] at $hlens:ident
        (repeat cases ‹_ ∧ _›)
        subst_vars
        try simp [wpS, wpE, wpF, popped, inI64, $defs,*]
        vc_leaves))

/-- The integer in variable i, and the length of the array in variable i (0 when the variable is of the
    other kind). Used to write invariants. -/
def geti (env : List Val) (i : Nat) : Int := match env[i]? with | some (.int v) => v | _ => 0
/-- Element j of the integer array in variable i (0 when there is none). Used to write invariants and
    postconditions. -/
def geta (env : List Val) (i : Nat) (j : Int) : Int := match env[i]? with
  | some (.arr l) => (l[j.toNat]?).getD 0
  | _ => 0

def leni (env : List Val) (i : Nat) : Int := match env[i]? with
  | some (.arr l) => l.length | some (.farr l) => l.length | _ => 0

syntax "kvc_open" ident ident ident "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| kvc_open $hΓ:ident $hsame:ident $hlens:ident [$defs,*]) =>
    `(tactic| (
        env_open_tagged $hΓ
        try simp [sameAt, kept, keptB, mods, List.range, List.range.loop, List.filter] at $hsame:ident
        try simp [lens, shape] at $hlens:ident
        (repeat cases ‹_ ∧ _›)
        subst_vars
        try simp [-List.length_eq_zero_iff, -List.length_pos_iff, wpS, wpE, wpF, popped, inI64, geti, leni, geta, List.getElem?_set, $defs,*]))

/-- `kvc f [defs]` proves `FnOk rest f`: open the typed arguments, turn the decidable requirement into
    facts, unfold the obligations, then repeat: arithmetic, splitting, and for every loop obligation
    opening the typed environment and using what the kernel knows about unchanged variables and lengths.
    `defs` are extra definitions to unfold (an invariant given by name). -/
syntax "kvc" ident "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| kvc $f:ident [$defs,*]) =>
    `(tactic| (
        intro args hin hreq hpre
        simp only [$f:ident, List.map] at hin
        env_open_tagged hin
        try simp [$f:ident, evalC, evalCT] at hreq
        try simp [$f:ident, geti, leni, geta, List.getElem?_set, $defs,*] at hpre
        simp [-List.length_eq_zero_iff, -List.length_pos_iff, $f:ident, wpS, wpE, wpF, popped, inI64, geti, leni, geta, List.getElem?_set, exclusive, argsTyped, lookups, hasAll, Val.has,
          evalC, evalCT, $defs,*]
        repeat' (first
          | omega
          | (mul_bounds; omega)
          | (div_bounds; omega)
          | elem_close
          | apply And.intro
          | (intro (_ : _ ≤ _))
          | (intro (_ : _ < _))
          | (intro (i : Nat) (env' : List Val) hi (hΓ : hasAll _ _ = true) hsame hlens; kvc_open hΓ hsame hlens [$defs,*])
          | (intro (env' : List Val) (hΓ : hasAll _ _ = true) hsame hlens; kvc_open hΓ hsame hlens [$defs,*])
          | (intro (hΓ : hasAll _ _ = true) (hl : lens _ = _); env_open hΓ; simp [lens, shape] at hl;
             (repeat cases ‹_ ∧ _›);
             try simp [-List.length_eq_zero_iff, -List.length_pos_iff, writeBack, wpS, wpE, wpF, popped, inI64, geti, leni, geta, List.getElem?_set, exclusive, argsTyped, lookups, hasAll,
               Val.has, evalC, evalCT, $defs,*])
          | (intro _)
          | assumption
          | (with_reducible rfl)
          | (simp [inI64]; done)
          | split)))

#print axioms prog_sound

end Tenon
#print axioms Tenon.parallel_writes
