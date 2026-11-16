import Tenon
import Emit
/-! The hand-written programs of emitter round 3 (written for K3), moved to Tenon unchanged except for the
    extra hypothesis `lens env' = lens env` that Tenon's loop obligations supply. They use only fixed-length
    arrays and K3 statements, and keep the emitter's K3 behaviour under test. See the list at the end
    for which are proved against Tenon. -/
namespace Tenon
open Stmt Expr


/-- Loop environment: [hi, lo, res, a, n, p].  The whole invariant: lo ≤ hi ≤ n.
    That n, p and the array are unchanged comes from the frame rule; ranges and shapes come from the types. -/
def lbInv (_ : List Val) (_ : Nat) (env : List Val) : Prop :=
  geti env 1 ≤ geti env 0 ∧ geti env 0 ≤ geti env 4

/-- lower_bound(a: [int in -10^6..=10^6; 8], n: 0..=8, p: -10^6..=10^6) -> 0..=8.  Body: [res, a, n, p]. -/
def lowerBound : Fn where
  params := [(.arr 8 (-1000000) 1000000, false), (.int 0 8, false), (.int (-1000000) 1000000, false)]
  rlo := 0
  rhi := 8
  body :=
    decl 0 8 (lit 0) (                                   -- lo = 0          [lo, res, a, n, p]
    decl 0 8 (var 3) (                                   -- hi = n          [hi, lo, res, a, n, p]
      seq
        (forN 64 lbInv (                                 --                 [i, hi, lo, res, a, n, p]
          ite (var 1) (var 2) brk (                      -- if hi ≤ lo break
          decl 0 7 (add (var 2) (div (sub (var 1) (var 2)) (lit 2))) (   -- mid   [mid, i, hi, lo, res, a, n, p]
            ite (idx 5 (var 0)) (sub (var 7) (lit 1))    -- if a[mid] ≤ p - 1
              (assign 3 (add (var 0) (lit 1)))           --   lo = mid + 1
              (assign 2 (var 0))))))                     -- else hi = mid
        (assign 2 (var 1))))                             -- res = lo
  req := .tt
  pre := fun _ => True
  post := fun a r _ => match a with | [_, .int n, _] => r ≤ n | _ => False

theorem lowerBoundOk : FnOk [] lowerBound := by
  intro args hin _ _
  match args with
  | [.arr l, .int n, .int p] =>
    simp [hasAll, Val.has, lowerBound] at hin
    simp [lowerBound, wpS, wpE, popped, inI64, lbInv, geti]
    repeat' (first | omega | apply And.intro | (intro (_ : _ ≤ _)))
    · intro i env' _ hΓ hsame _hlens
      env_open hΓ
      simp [sameAt, kept, mods, List.range, List.range.loop, List.filter] at hsame
      simp [wpS, wpE, popped, inI64, lbInv, geti]
      vc_leaves
    · intro env' hΓ hsame _hlens
      env_open hΓ
      simp [sameAt, kept, mods, List.range, List.range.loop, List.filter] at hsame
      simp [geti]
      vc_leaves
  | [] => simp [hasAll, lowerBound] at hin
  | [_] => simp [hasAll, lowerBound] at hin
  | [_, _] => simp [hasAll, lowerBound] at hin
  | _ :: _ :: _ :: _ :: _ => simp [hasAll, lowerBound] at hin
  | [.int _, _, _] => simp [hasAll, Val.has, lowerBound] at hin
  | [.flt _, _, _] => simp [hasAll, Val.has, lowerBound] at hin
  | [.farr _, _, _] => simp [hasAll, Val.has, lowerBound] at hin
  | [.arr _, .arr _, _] => simp [hasAll, Val.has, lowerBound] at hin
  | [.arr _, .flt _, _] => simp [hasAll, Val.has, lowerBound] at hin
  | [.arr _, .farr _, _] => simp [hasAll, Val.has, lowerBound] at hin
  | [.arr _, .int _, .arr _] => simp [hasAll, Val.has, lowerBound] at hin
  | [.arr _, .int _, .flt _] => simp [hasAll, Val.has, lowerBound] at hin
  | [.arr _, .int _, .farr _] => simp [hasAll, Val.has, lowerBound] at hin

/-! ## The same function with a break-only loop: no counter in the code. The bound 9 and the iteration
    number appear only in the invariant, as a variant: the interval shrinks by at least one each time. -/

/-- Loop environment: [hi, lo, res, a, n, p]. -/
def lbInvB (_ : List Val) (i : Nat) (env : List Val) : Prop :=
  geti env 1 ≤ geti env 0 ∧ geti env 0 ≤ geti env 4 ∧ geti env 0 - geti env 1 ≤ 8 - (i : Int)

def lowerBoundB : Fn where
  params := [(.arr 8 (-1000000) 1000000, false), (.int 0 8, false), (.int (-1000000) 1000000, false)]
  rlo := 0
  rhi := 8
  body :=
    decl 0 8 (lit 0) (                                   -- lo = 0          [lo, res, a, n, p]
    decl 0 8 (var 3) (                                   -- hi = n          [hi, lo, res, a, n, p]
      seq
        (loopB 9 lbInvB (
          ite (var 0) (var 1) brk (                      -- if hi ≤ lo break
          decl 0 7 (add (var 1) (div (sub (var 0) (var 1)) (lit 2))) (   -- mid   [mid, hi, lo, res, a, n, p]
            ite (idx 4 (var 0)) (sub (var 6) (lit 1))    -- if a[mid] ≤ p - 1
              (assign 2 (add (var 0) (lit 1)))           --   lo = mid + 1
              (assign 1 (var 0))))))                     -- else hi = mid
        (assign 2 (var 1))))                             -- res = lo
  req := .tt
  pre := fun _ => True
  post := fun a r _ => match a with | [_, .int n, _] => r ≤ n | _ => False

theorem lowerBoundBOk : FnOk [] lowerBoundB := by
  intro args hin _ _
  match args with
  | [.arr l, .int n, .int p] =>
    simp [hasAll, Val.has, lowerBoundB] at hin
    simp [lowerBoundB, wpS, wpE, popped, inI64, lbInvB, geti]
    repeat' (first | omega | apply And.intro | (intro (_ : _ ≤ _)))
    · intro i env' _ hΓ hsame _hlens
      env_open hΓ
      simp [sameAt, keptB, mods, List.range, List.range.loop, List.filter] at hsame
      simp [wpS, wpE, popped, inI64, lbInvB, geti]
      vc_leaves
  | [] => simp [hasAll, lowerBoundB] at hin
  | [_] => simp [hasAll, lowerBoundB] at hin
  | [_, _] => simp [hasAll, lowerBoundB] at hin
  | _ :: _ :: _ :: _ :: _ => simp [hasAll, lowerBoundB] at hin
  | [.int _, _, _] => simp [hasAll, Val.has, lowerBoundB] at hin
  | [.flt _, _, _] => simp [hasAll, Val.has, lowerBoundB] at hin
  | [.farr _, _, _] => simp [hasAll, Val.has, lowerBoundB] at hin
  | [.arr _, .arr _, _] => simp [hasAll, Val.has, lowerBoundB] at hin
  | [.arr _, .flt _, _] => simp [hasAll, Val.has, lowerBoundB] at hin
  | [.arr _, .farr _, _] => simp [hasAll, Val.has, lowerBoundB] at hin
  | [.arr _, .int _, .arr _] => simp [hasAll, Val.has, lowerBoundB] at hin
  | [.arr _, .int _, .flt _] => simp [hasAll, Val.has, lowerBoundB] at hin
  | [.arr _, .int _, .farr _] => simp [hasAll, Val.has, lowerBoundB] at hin


end Tenon

namespace Tenon.Legacy
open Tenon Stmt Expr Tenon.Emit

/-- An invariant for programs that are not proved. -/
def triv : List Val → Nat → List Val → Prop := fun _ _ _ => True

structure Example where
  name   : String
  fns    : List Fn                      -- newest first; function 0 is the entry point
  names  : List FnNames
  elemLo : Int := -1000000              -- test inputs: range of array elements (intersected with the type)
  elemHi : Int := 1000000
  proved : String := "unproved"

/-- The array at variable i ([] if it is not an array; the types exclude that). -/
def geta (env : List Val) (i : Nat) : List Int := match env[i]? with | some (.arr l) => l | _ => []

def lowerBoundNames : FnNames :=
  { name := "lower_bound", params := ["a", "n", "p"], result := "res", locals := ["lo", "hi", "i", "mid"] }
def lowerBoundBNames : FnNames :=
  { name := "lower_bound_b", params := ["a", "n", "p"], result := "res", locals := ["lo", "hi", "mid"] }

/-! ### lower_bound on 1024 elements: counted loop (forN 64), and break-only loop (loopB) -/

def lowerBound1024 : Fn where
  params := [(.arr 1024 (-1000000000) 1000000000, false), (.int 0 1024, false), (.int (-1000000000) 1000000000, false)]
  rlo := 0
  rhi := 1024
  body :=
    decl 0 1024 (lit 0) (
    decl 0 1024 (var 3) (
      seq
        (forN 64 lbInv (
          ite (var 1) (var 2) brk (
          decl 0 1023 (add (var 2) (div (sub (var 1) (var 2)) (lit 2))) (
            ite (idx 5 (var 0)) (sub (var 7) (lit 1))
              (assign 3 (add (var 0) (lit 1)))
              (assign 2 (var 0))))))
        (assign 2 (var 1))))
  req := .tt
  pre := fun _ => True
  post := fun a r _ => match a with | [_, .int n, _] => r ≤ n | _ => False

theorem lowerBound1024Ok : FnOk [] lowerBound1024 := by
  intro args hin _ _
  match args with
  | [.arr l, .int n, .int p] =>
    simp [hasAll, Val.has, lowerBound1024] at hin
    simp [lowerBound1024, wpS, wpE, popped, inI64, lbInv, geti]
    repeat' (first | omega | apply And.intro | (intro (_ : _ ≤ _)))
    · intro i env' _ hΓ hsame _hlens
      env_open hΓ
      simp [sameAt, kept, mods, List.range, List.range.loop, List.filter] at hsame
      simp [wpS, wpE, popped, inI64, lbInv, geti]
      vc_leaves
    · intro env' hΓ hsame _hlens
      env_open hΓ
      simp [sameAt, kept, mods, List.range, List.range.loop, List.filter] at hsame
      simp [geti]
      vc_leaves
  | [] => simp [hasAll, lowerBound1024] at hin
  | [_] => simp [hasAll, lowerBound1024] at hin
  | [_, _] => simp [hasAll, lowerBound1024] at hin
  | _ :: _ :: _ :: _ :: _ => simp [hasAll, lowerBound1024] at hin
  | [.int _, _, _] => simp [hasAll, Val.has, lowerBound1024] at hin
  | [.flt _, _, _] => simp [hasAll, Val.has, lowerBound1024] at hin
  | [.farr _, _, _] => simp [hasAll, Val.has, lowerBound1024] at hin
  | [.arr _, .arr _, _] => simp [hasAll, Val.has, lowerBound1024] at hin
  | [.arr _, .flt _, _] => simp [hasAll, Val.has, lowerBound1024] at hin
  | [.arr _, .farr _, _] => simp [hasAll, Val.has, lowerBound1024] at hin
  | [.arr _, .int _, .arr _] => simp [hasAll, Val.has, lowerBound1024] at hin
  | [.arr _, .int _, .flt _] => simp [hasAll, Val.has, lowerBound1024] at hin
  | [.arr _, .int _, .farr _] => simp [hasAll, Val.has, lowerBound1024] at hin

/-- Loop environment: [hi, lo, res, a, n, p]. The variant is linear: the interval shrinks by at least
    one per iteration, so the proof bound is 1025. The bound is not in the generated code, so its size
    costs nothing at run time. -/
def lbInvB1024 (_ : List Val) (i : Nat) (env : List Val) : Prop :=
  geti env 1 ≤ geti env 0 ∧ geti env 0 ≤ geti env 4 ∧ geti env 0 - geti env 1 ≤ 1024 - (i : Int)

def lowerBoundB1024 : Fn where
  params := [(.arr 1024 (-1000000000) 1000000000, false), (.int 0 1024, false), (.int (-1000000000) 1000000000, false)]
  rlo := 0
  rhi := 1024
  body :=
    decl 0 1024 (lit 0) (
    decl 0 1024 (var 3) (
      seq
        (loopB 1025 lbInvB1024 (
          ite (var 0) (var 1) brk (
          decl 0 1023 (add (var 1) (div (sub (var 0) (var 1)) (lit 2))) (
            ite (idx 4 (var 0)) (sub (var 6) (lit 1))
              (assign 2 (add (var 0) (lit 1)))
              (assign 1 (var 0))))))
        (assign 2 (var 1))))
  req := .tt
  pre := fun _ => True
  post := fun a r _ => match a with | [_, .int n, _] => r ≤ n | _ => False

theorem lowerBoundB1024Ok : FnOk [] lowerBoundB1024 := by
  intro args hin _ _
  match args with
  | [.arr l, .int n, .int p] =>
    simp [hasAll, Val.has, lowerBoundB1024] at hin
    simp [lowerBoundB1024, wpS, wpE, popped, inI64, lbInvB1024, geti]
    repeat' (first | omega | apply And.intro | (intro (_ : _ ≤ _)))
    · intro i env' _ hΓ hsame _hlens
      env_open hΓ
      simp [sameAt, keptB, mods, List.range, List.range.loop, List.filter] at hsame
      simp [wpS, wpE, popped, inI64, lbInvB1024, geti]
      vc_leaves
  | [] => simp [hasAll, lowerBoundB1024] at hin
  | [_] => simp [hasAll, lowerBoundB1024] at hin
  | [_, _] => simp [hasAll, lowerBoundB1024] at hin
  | _ :: _ :: _ :: _ :: _ => simp [hasAll, lowerBoundB1024] at hin
  | [.int _, _, _] => simp [hasAll, Val.has, lowerBoundB1024] at hin
  | [.flt _, _, _] => simp [hasAll, Val.has, lowerBoundB1024] at hin
  | [.farr _, _, _] => simp [hasAll, Val.has, lowerBoundB1024] at hin
  | [.arr _, .arr _, _] => simp [hasAll, Val.has, lowerBoundB1024] at hin
  | [.arr _, .flt _, _] => simp [hasAll, Val.has, lowerBoundB1024] at hin
  | [.arr _, .farr _, _] => simp [hasAll, Val.has, lowerBoundB1024] at hin
  | [.arr _, .int _, .arr _] => simp [hasAll, Val.has, lowerBoundB1024] at hin
  | [.arr _, .int _, .flt _] => simp [hasAll, Val.has, lowerBoundB1024] at hin
  | [.arr _, .int _, .farr _] => simp [hasAll, Val.has, lowerBoundB1024] at hin

def lowerBound1024Names : FnNames :=
  { name := "lower_bound_1024", params := ["a", "n", "p"], result := "res", locals := ["lo", "hi", "i", "mid"] }
def lowerBoundB1024Names : FnNames :=
  { name := "lower_bound_b_1024", params := ["a", "n", "p"], result := "res", locals := ["lo", "hi", "mid"] }

/-! ### The inout example of InoutExample.lean (written there for K2), re-expressed in Tenon. Proved.
    Differences from the K2 text: the array type carries its element range; `assign` has no range;
    the invariant no longer states the shape of the environment (the types give it); the
    postcondition must still state the shape of `outs`, because the call rule of `wpS` does not give
    the caller `hasAll params outs` (see README, kernel suggestions). -/

/-- clear(inout a: [int; 8]) -> 0.   Body environment: [res, a].  for i in 0..8 { a[i] = 0 } -/
def clearInv (_ : List Val) (i : Nat) (env : List Val) : Prop :=
  ∀ j : Nat, j < i → (geta env 1)[j]? = some 0

def clearFn : Fn where
  params := [(.arr 8 (-1000000) 1000000, true)]
  rlo := 0
  rhi := 0
  body := forN 8 clearInv (store 2 (var 0) (lit 0))
  req := .tt
  pre := fun _ => True
  post := fun _ _ outs => ∃ l, outs = [.arr l] ∧ l.length = 8 ∧ ∀ j : Nat, j < 8 → l[j]? = some 0

theorem clearOk : FnOk [] clearFn := by
  intro args hin _ _
  match args with
  | [.arr l] =>
    simp [hasAll, Val.has, clearFn] at hin
    simp [clearFn, wpS, wpE, popped, inI64, clearInv, geta]
    refine ⟨?_, ?_⟩
    · intro i env' hi hΓ hsame _hlens hI
      env_open hΓ
      simp [wpS, wpE, popped, inI64, clearInv, geta] at hI ⊢
      intro _
      refine ⟨by omega, ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst hji; simp [List.getElem?_set]; omega
      · have := hI j (by omega)
        simp [List.getElem?_set, this]
        intro h; omega
    · intro env' hΓ hsame _hlens hI
      env_open hΓ
      simp [geta] at hI
      exact ⟨_, rfl, by assumption, hI⟩
  | [.int _] => simp [hasAll, Val.has, clearFn] at hin
  | [.flt _] => simp [hasAll, Val.has, clearFn] at hin
  | [.farr _] => simp [hasAll, Val.has, clearFn] at hin
  | [] => simp [hasAll, clearFn] at hin
  | _ :: _ :: _ => simp [hasAll, clearFn] at hin

/-- swap(inout a: [int; 8], i: 0..=7, j: 0..=7) -> 0.   Body environment: [res, a, i, j]. Proved. -/
def swapFn : Fn where
  params := [(.arr 8 (-1000000) 1000000, true), (.int 0 7, false), (.int 0 7, false)]
  rlo := 0
  rhi := 0
  body :=
    decl (-1000000) 1000000 (idx 1 (var 2)) (            -- t = a[i]      [t, res, a, i, j]
      seq (store 2 (var 3) (idx 2 (var 4)))              -- a[i] = a[j]
          (store 2 (var 4) (var 0)))                     -- a[j] = t
  req := .tt
  pre := fun _ => True
  post := fun _ _ _ => True

theorem swapOk : FnOk [] swapFn := by
  intro args hin _ _
  match args with
  | [.arr l, .int i, .int j] =>
    simp [hasAll, Val.has, swapFn] at hin
    simp [swapFn, wpS, wpE, popped, inI64]
    vc_leaves
  | [] => simp [hasAll, swapFn] at hin
  | [_] => simp [hasAll, swapFn] at hin
  | [_, _] => simp [hasAll, swapFn] at hin
  | _ :: _ :: _ :: _ :: _ => simp [hasAll, swapFn] at hin
  | [.int _, _, _] => simp [hasAll, Val.has, swapFn] at hin
  | [.flt _, _, _] => simp [hasAll, Val.has, swapFn] at hin
  | [.farr _, _, _] => simp [hasAll, Val.has, swapFn] at hin
  | [.arr _, .arr _, _] => simp [hasAll, Val.has, swapFn] at hin
  | [.arr _, .flt _, _] => simp [hasAll, Val.has, swapFn] at hin
  | [.arr _, .farr _, _] => simp [hasAll, Val.has, swapFn] at hin
  | [.arr _, .int _, .arr _] => simp [hasAll, Val.has, swapFn] at hin
  | [.arr _, .int _, .flt _] => simp [hasAll, Val.has, swapFn] at hin
  | [.arr _, .int _, .farr _] => simp [hasAll, Val.has, swapFn] at hin

/-- useClear(a: [int; 8]) -> 0..=0.   { let t = 0; t = clear(inout a); res = a[3] }
    `a` is a by-value parameter that is passed on as inout: the emitter must give it a private copy. -/
def useClear : Fn where
  params := [(.arr 8 (-1000000) 1000000, false)]
  rlo := 0
  rhi := 0
  body := decl 0 0 (lit 0) (                             -- [t, res, a]
            seq (call 0 [(2, true)] 0)                   -- t = clear(inout a)
                (assign 1 (idx 2 (lit 3))))              -- res = a[3]
  req := .tt
  pre := fun _ => True
  post := fun _ r _ => r = 0

theorem useClearOk : FnOk [clearFn] useClear := by
  intro args hin _ _
  match args with
  | [.arr l] =>
    simp [hasAll, Val.has, useClear] at hin
    simp [useClear, wpS, wpE, popped, inI64, evalC, exclusive, lookups, clearFn, hasAll, Val.has, hin, writeBack, argsTyped]
    refine ⟨hin.2, ?_⟩
    intro r outs x ho hl1 hz _ _
    subst ho
    simp [writeBack]
    intro _ _ l1 v hl hv _ _
    subst hl
    have h3 := hz 3 (by omega)
    rw [h3] at hv
    simp at hv
    omega
  | [] => simp [hasAll, useClear] at hin
  | [.int _] => simp [hasAll, Val.has, useClear] at hin
  | [.flt _] => simp [hasAll, Val.has, useClear] at hin
  | [.farr _] => simp [hasAll, Val.has, useClear] at hin
  | _ :: _ :: _ => simp [hasAll, useClear] at hin

/-- ring_push(inout buf: [int; 8], inout head: 0..=7, inout count: 0..=8, v) -> 0..=7: the new head.
    Body environment: [res, buf, head, count, v]. Proved (no loop: unfold and `vc_leaves`). -/
def ringPush : Fn where
  params := [(.arr 8 (-1000000) 1000000, true), (.int 0 7, true), (.int 0 8, true), (.int (-1000000) 1000000, false)]
  rlo := 0
  rhi := 7
  body :=
    seq (store 1 (var 2) (var 4))                                                  -- buf[head] = v
   (seq (ite (var 2) (lit 6) (assign 2 (add (var 2) (lit 1))) (assign 2 (lit 0)))  -- head = head ≤ 6 ? head + 1 : 0
   (seq (ite (var 3) (lit 7) (assign 3 (add (var 3) (lit 1))) skip)                -- if count ≤ 7 { count = count + 1 }
        (assign 0 (var 2))))                                                       -- res = head
  req := .tt
  pre := fun _ => True
  post := fun _ r outs => r = geti outs 1

theorem ringPushOk : FnOk [] ringPush := by
  intro args hin _ _
  match args with
  | [.arr l, .int h, .int c, .int v] =>
    simp [hasAll, Val.has, ringPush] at hin
    simp [ringPush, wpS, wpE, popped, inI64, geti]
    vc_leaves
  | [] => simp [hasAll, ringPush] at hin
  | [_] => simp [hasAll, ringPush] at hin
  | [_, _] => simp [hasAll, ringPush] at hin
  | [_, _, _] => simp [hasAll, ringPush] at hin
  | _ :: _ :: _ :: _ :: _ :: _ => simp [hasAll, ringPush] at hin
  | [.int _, _, _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.flt _, _, _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.farr _, _, _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .arr _, _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .flt _, _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .farr _, _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .int _, .arr _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .int _, .flt _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .int _, .farr _, _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .int _, .int _, .arr _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .int _, .int _, .flt _] => simp [hasAll, Val.has, ringPush] at hin
  | [.arr _, .int _, .int _, .farr _] => simp [hasAll, Val.has, ringPush] at hin

/-! ### In-place prefix sum with a proved bound.
    prefix_sum(inout a: [int in -8·10^6..=8·10^6; 8]) -> the total; requires every element in ±10^6.
    The proof shows that the running sum stays within ±10^6·(i+1), hence in the element range, and that
    the elements not yet visited are still within ±10^6. -/
def psInv (_ : List Val) (i : Nat) (env : List Val) : Prop :=
  -1000000 * (i : Int) ≤ geti env 0 ∧ geti env 0 ≤ 1000000 * (i : Int) ∧
  ∀ (j : Nat) (v : Int), i ≤ j → (geta env 2)[j]? = some v → -1000000 ≤ v ∧ v ≤ 1000000

def prefixSum8 : Fn where
  params := [(.arr 8 (-8000000) 8000000, true)]
  rlo := -8000000
  rhi := 8000000
  body :=
    decl (-8000000) 8000000 (lit 0) (                    -- acc = 0       [acc, res, a]
      seq (forN 8 psInv (                                --               [i, acc, res, a]
            seq (assign 1 (add (var 1) (idx 3 (var 0)))) -- acc = acc + a[i]
                (store 3 (var 0) (var 1))))              -- a[i] = acc
          (assign 1 (var 0)))                            -- res = acc
  req := .tt
  pre := fun args => ∀ x ∈ geta args 0, -1000000 ≤ x ∧ x ≤ 1000000
  post := fun _ _ _ => True

theorem prefixSum8Ok : FnOk [] prefixSum8 := by
  intro args hin _ hpre
  match args with
  | [.arr l] =>
    simp [hasAll, Val.has, prefixSum8] at hin
    simp [prefixSum8, geta] at hpre
    simp [prefixSum8, wpS, wpE, popped, inI64, psInv, geti, geta]
    refine ⟨?_, ?_, ?_⟩
    · intro j v hj
      exact hpre v (List.mem_of_getElem? hj)
    · intro i env' hi hΓ hsame _hlens
      env_open hΓ
      simp
      intro h1 h2 h3 _ _ _
      refine ⟨by omega, ?_⟩
      intro l1 v1 hl hv1 _ _
      subst hl
      have hb := h3 i v1 (Nat.le_refl i) hv1
      refine ⟨by omega, by omega, by omega, ?_⟩
      intro _
      refine ⟨by omega, ?_⟩
      intro _ _
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      intro j v3 hj hv3
      rw [List.getElem?_set_ne (by omega)] at hv3
      exact h3 j v3 (by omega) hv3
    · intro env' hΓ hsame _hlens
      env_open hΓ
      simp
      vc_leaves
  | [] => simp [hasAll, prefixSum8] at hin
  | [.int _] => simp [hasAll, Val.has, prefixSum8] at hin
  | [.flt _] => simp [hasAll, Val.has, prefixSum8] at hin
  | [.farr _] => simp [hasAll, Val.has, prefixSum8] at hin
  | _ :: _ :: _ => simp [hasAll, prefixSum8] at hin

/-! The same for 1024 elements (used by the benchmark): same proof with the constants changed. -/
def psInv1024 (_ : List Val) (i : Nat) (env : List Val) : Prop :=
  -1000000 * (i : Int) ≤ geti env 0 ∧ geti env 0 ≤ 1000000 * (i : Int) ∧
  ∀ (j : Nat) (v : Int), i ≤ j → (geta env 2)[j]? = some v → -1000000 ≤ v ∧ v ≤ 1000000

def prefixSum1024 : Fn where
  params := [(.arr 1024 (-1024000000) 1024000000, true)]
  rlo := -1024000000
  rhi := 1024000000
  body :=
    decl (-1024000000) 1024000000 (lit 0) (                    -- acc = 0       [acc, res, a]
      seq (forN 1024 psInv1024 (                                --               [i, acc, res, a]
            seq (assign 1 (add (var 1) (idx 3 (var 0)))) -- acc = acc + a[i]
                (store 3 (var 0) (var 1))))              -- a[i] = acc
          (assign 1 (var 0)))                            -- res = acc
  req := .tt
  pre := fun args => ∀ x ∈ geta args 0, -1000000 ≤ x ∧ x ≤ 1000000
  post := fun _ _ _ => True

theorem prefixSum1024Ok : FnOk [] prefixSum1024 := by
  intro args hin _ hpre
  match args with
  | [.arr l] =>
    simp [hasAll, Val.has, prefixSum1024] at hin
    simp [prefixSum1024, geta] at hpre
    simp [prefixSum1024, wpS, wpE, popped, inI64, psInv1024, geti, geta]
    refine ⟨?_, ?_, ?_⟩
    · intro j v hj
      exact hpre v (List.mem_of_getElem? hj)
    · intro i env' hi hΓ hsame _hlens
      env_open hΓ
      simp
      intro h1 h2 h3 _ _ _
      refine ⟨by omega, ?_⟩
      intro l1 v1 hl hv1 _ _
      subst hl
      have hb := h3 i v1 (Nat.le_refl i) hv1
      refine ⟨by omega, by omega, by omega, ?_⟩
      intro _
      refine ⟨by omega, ?_⟩
      intro _ _
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      intro j v3 hj hv3
      rw [List.getElem?_set_ne (by omega)] at hv3
      exact h3 j v3 (by omega) hv3
    · intro env' hΓ hsame _hlens
      env_open hΓ
      simp
      vc_leaves
  | [] => simp [hasAll, prefixSum1024] at hin
  | [.int _] => simp [hasAll, Val.has, prefixSum1024] at hin
  | [.flt _] => simp [hasAll, Val.has, prefixSum1024] at hin
  | [.farr _] => simp [hasAll, Val.has, prefixSum1024] at hin
  | _ :: _ :: _ => simp [hasAll, prefixSum1024] at hin

/-! ### Unproved examples (compared with the C only where `evalFn` is `some`) -/

abbrev E6 : Ty := .arr 8 (-1000000) 1000000
def tpost : List Val → Int → List Val → Prop := fun _ _ _ => True
def tpre : List Val → Prop := fun _ => True

/-- ring_fill(inout buf: [int; 8], inout head: 0..=7, src: [int; 4]) -> 0..=8: pushes the four
    elements of src, forwarding its own inout parameters. Body environment: [res, buf, head, src]. -/
def ringFill : Fn where
  params := [(E6, true), (.int 0 7, true), (.arr 4 (-1000000) 1000000, false)]
  rlo := 0
  rhi := 8
  body :=
    decl 0 8 (lit 0) (                                   -- count          [count, res, buf, head, src]
      seq (forN 4 triv (                                 --                [i, count, res, buf, head, src]
            decl (-1000000) 1000000 (idx 5 (var 0)) (    -- v = src[i]     [v, i, count, res, buf, head, src]
              decl 0 7 (lit 0) (                         -- t              [t, v, i, count, res, buf, head, src]
                call 0 [(5, true), (6, true), (3, true), (1, false)] 0))))   -- t = ring_push(buf, head, count, v)
          (assign 1 (var 0)))                            -- res = count
  req := .tt
  pre := tpre
  post := tpost

/-- insert_sorted(inout a: [int; 8], k: 0..=7, v) -> 0..=7: a[0..k) is sorted; shift the larger
    elements up by one and put v in the gap; returns its position. A break-only loop.
    Body environment: [res, a, k, v]. -/
def insertSorted : Fn where
  params := [(E6, true), (.int 0 7, false), (.int (-1000000) 1000000, false)]
  rlo := 0
  rhi := 7
  body :=
    decl 0 7 (var 2) (                                   -- j = k          [j, res, a, k, v]
      seq (loopB 9 triv (
            ite (var 0) (lit 0) brk (                              -- if j ≤ 0 break
            ite (idx 2 (sub (var 0) (lit 1))) (var 4) brk (        -- if a[j-1] ≤ v break
            seq (store 2 (var 0) (idx 2 (sub (var 0) (lit 1))))    -- a[j] = a[j-1]
                (assign 0 (sub (var 0) (lit 1)))))))               -- j = j - 1
      (seq (store 2 (var 0) (var 4))                     -- a[j] = v
           (assign 1 (var 0))))                          -- res = j
  req := .tt
  pre := tpre
  post := tpost

/-- insertion_sort(inout a: [int; 8]) -> 0..=28: sorts a in place by repeated insert_sorted and
    returns the total distance moved. Body environment: [res, a]. -/
def insertionSort : Fn where
  params := [(E6, true)]
  rlo := 0
  rhi := 28
  body :=
    forN 8 triv (                                        --                [k, res, a]
      decl (-1000000) 1000000 (idx 2 (var 0)) (          -- v = a[k]       [v, k, res, a]
        decl 0 7 (lit 0) (                               -- pos            [pos, v, k, res, a]
          seq (call 0 [(4, true), (2, false), (1, false)] 0)       -- pos = insert_sorted(inout a, k, v)
              (assign 3 (add (var 3) (sub (var 2) (var 0)))))))    -- res = res + (k - pos)
  req := .tt
  pre := tpre
  post := tpost

/-- reverse(inout a: [int; 8]) -> 0: four calls of swap. Body environment: [res, a]. -/
def reverseFn : Fn where
  params := [(E6, true)]
  rlo := 0
  rhi := 0
  body :=
    forN 4 triv (                                        --                [i, res, a]
      decl 0 7 (sub (lit 7) (var 0)) (                   -- j = 7 - i      [j, i, res, a]
        decl 0 0 (lit 0) (                               -- t              [t, j, i, res, a]
          call 0 [(4, true), (2, false), (1, false)] 0)))
  req := .tt
  pre := tpre
  post := tpost

abbrev E9 : Ty := .arr 8 (-1000000000) 1000000000

/-- axpy(inout y: [int; 8], x: [int; 8], k: -3..=3) -> 0: y[i] = y[i] + k * x[i].
    Body environment: [res, y, x, k]. -/
def axpy : Fn where
  params := [(E9, true), (E9, false), (.int (-3) 3, false)]
  rlo := 0
  rhi := 0
  body := forN 8 triv (store 2 (var 0) (add (idx 2 (var 0)) (mul (var 4) (idx 3 (var 0)))))
  req := .tt
  pre := tpre
  post := tpost

/-- axpy_twice(a, b: [int; 8], k) -> b'[0] + b'[7] where b' = b + 2·k·a, computed on a private copy of
    the by-value parameter b (it is passed inout). The C caller's a and b must be unchanged.
    Body environment: [res, a, b, k]. -/
def axpyTwice : Fn where
  params := [(E9, false), (E9, false), (.int (-3) 3, false)]
  rlo := -2000000000
  rhi := 2000000000
  body :=
    decl 0 0 (lit 0) (                                   -- t              [t, res, a, b, k]
      seq (call 0 [(3, true), (2, false), (4, false)] 0)
     (seq (call 0 [(3, true), (2, false), (4, false)] 0)
          (assign 1 (add (idx 3 (lit 0)) (idx 3 (lit 7))))))
  req := .tt
  pre := tpre
  post := tpost

/-- alias_bad(inout y: [int; 8], k) -> 0: t = axpy(inout y, y, k). NOT exclusive: `evalFn` is `none`
    on every input. The harness must skip all of them. Body environment: [res, y, k]. -/
def aliasBad : Fn where
  params := [(E9, true), (.int (-3) 3, false)]
  rlo := 0
  rhi := 0
  body := decl 0 0 (lit 0) (call 0 [(2, true), (2, false), (3, false)] 0)
  req := .tt
  pre := tpre
  post := tpost

/-- alias_branch(inout y, x: [int; 8], k) -> 0: if k ≤ 0 { t = axpy(inout y, y, k) } else
    { t = axpy(inout y, x, k) }. `none` exactly when k ≤ 0. Body environment: [res, y, x, k]. -/
def aliasBranch : Fn where
  params := [(E9, true), (E9, false), (.int (-3) 3, false)]
  rlo := 0
  rhi := 0
  body := decl 0 0 (lit 0) (                             -- [t, res, y, x, k]
    ite (var 4) (lit 0) (call 0 [(2, true), (2, false), (4, false)] 0)
                        (call 0 [(2, true), (3, false), (4, false)] 0))
  req := .tt
  pre := tpre
  post := tpost

/-- bump(inout x: 0..=100) -> 0..=100: x = x + 3; res = x. Body environment: [res, x]. -/
def bump : Fn where
  params := [(.int 0 100, true)]
  rlo := 0
  rhi := 100
  body := seq (assign 1 (add (var 1) (lit 3))) (assign 0 (var 1))
  req := .tt
  pre := tpre
  post := tpost

/-- counter_inout(k: 0..=3) -> int. The loop counter is passed as an inout argument (first loop) and
    is the destination of a call (second loop); the next iteration must still start from the loop's
    own count. First loop adds (i + 3) + (i + 3) for i < 5 = 50; second adds (k + 3) five times.
    Body environment: [s, k]. -/
def counterInout : Fn where
  params := [(.int 0 3, false)]
  rlo := 0
  rhi := 1000
  body := seq
    (forN 5 triv (                                       -- [i, s, k]
      decl 0 100 (lit 0) (                               -- [t, i, s, k]
        seq (call 0 [(1, true)] 0)                       -- t = bump(inout i)
            (assign 2 (add (var 2) (add (var 1) (var 0)))))))
    (forN 5 triv (                                       -- [i, s, k]
      decl 0 100 (var 2) (                               -- kk = k   [kk, i, s, k]
        seq (call 0 [(0, true)] 1)                       -- i = bump(inout kk)
            (assign 2 (add (var 2) (var 1))))))
  req := .tt
  pre := tpre
  post := tpost

/-- sum(a: [int in 0..=1100; 8]) -> 0..=6000. Stuck when the running sum leaves 0..=6000. -/
def sum8 : Fn where
  params := [(.arr 8 0 1100, false)]
  rlo := 0
  rhi := 6000
  body := forN 8 triv (assign 1 (add (var 1) (idx 2 (var 0))))        -- [i, s, a]
  req := .tt
  pre := tpre
  post := tpost

/-- fill_sum(a: [int; 8], v: -1000..=1000) -> int: a[i] = v + i on the callee's own copy, then the sum.
    Body environment: [s, a, v]. -/
def fillSum : Fn where
  params := [(E6, false), (.int (-1000) 1000, false)]
  rlo := -10000
  rhi := 10000
  body := seq (assign 0 (lit 0))                                      -- the result starts at rlo, not 0
    (seq (forN 8 triv (store 2 (var 0) (add (var 3) (var 0))))        -- [i, s, a, v]
         (forN 8 triv (assign 1 (add (var 1) (idx 2 (var 0))))))
  req := .tt
  pre := tpre
  post := tpost

/-- max(a: [int; 8]) -> int. Body environment: [m, a]. -/
def max8 : Fn where
  params := [(E6, false)]
  rlo := -1000000
  rhi := 1000000
  body := seq
    (assign 0 (idx 1 (lit 0)))
    (forN 8 triv (ite (var 1) (idx 2 (var 0)) (assign 1 (idx 2 (var 0))) skip))   -- [i, m, a]
  req := .tt
  pre := tpre
  post := tpost

/-- rank_sum(a: [int; 8], q: [int; 4]) -> 0..=32: the sum over j of lower_bound(a, 8, q[j]).
    `first` selects the callee. Body environment: [t, a, q]. -/
def rankSum : Fn where
  params := [(E6, false), (.arr 4 (-1000000) 1000000, false)]
  rlo := 0
  rhi := 32
  body :=
    decl 8 8 (lit 8) (                                   -- n              [n, t, a, q]
      forN 4 triv (                                      --                [j, n, t, a, q]
        decl (-1000000) 1000000 (idx 4 (var 0)) (        -- p = q[j]       [p, j, n, t, a, q]
          decl 0 8 (lit 0) (                             -- r              [r, p, j, n, t, a, q]
            seq (call 0 [(5, false), (3, false), (1, false)] 0)
                (assign 4 (add (var 4) (var 0)))))))
  req := .tt
  pre := tpre
  post := tpost

/-- clobber(a: [int; 4]) -> int: overwrites its by-value a with 99 and returns a[0] + a[3] (= 198). -/
def clobber : Fn where
  params := [(.arr 4 (-1000000) 1000000, false)]
  rlo := 0
  rhi := 198
  body := seq (forN 4 triv (store 2 (var 0) (lit 99))) (assign 0 (add (idx 1 (lit 0)) (idx 1 (lit 3))))
  req := .tt
  pre := tpre
  post := tpost

/-- probe(a: [int; 4]) -> int: a[1] = 7; r = clobber(a); result = r + a[0] + a[1].
    The caller must still see its own a[0] and the 7 it stored. Body environment: [res, a]. -/
def probe : Fn where
  params := [(.arr 4 (-1000000) 1000000, false)]
  rlo := -2000000
  rhi := 2000000
  body := seq (store 1 (lit 1) (lit 7))
    (decl 0 198 (lit 0) (                                -- [r, res, a]
      seq (call 0 [(2, false)] 0)
          (assign 1 (add (add (var 0) (idx 2 (lit 0))) (idx 2 (lit 1))))))
  req := .tt
  pre := tpre
  post := tpost

/-- counter_assign(k: 0..=3) -> int: the body assigns the loop counter. s = Σ_{i<5} (i * k). -/
def counterAssign : Fn where
  params := [(.int 0 3, false)]
  rlo := 0
  rhi := 100
  body := forN 20 triv (seq                              -- [i, s, k]
    (ite (lit 5) (var 0) brk skip)
    (seq (assign 0 (mul (var 0) (var 2)))
         (assign 1 (add (var 1) (var 0)))))
  req := .tt
  pre := tpre
  post := tpost

/-- break_nested(a: [int; 8], t) -> int: for each i < 3, count the j before the first a[j] > t + i,
    with a break-only inner loop whose `brk` is inside two `decl`s. Body environment: [c, a, t]. -/
def breakNested : Fn where
  params := [(E6, false), (.int (-1000) 1000, false)]
  rlo := 0
  rhi := 64
  body := forN 3 triv (                                  -- [i, c, a, t]
    decl 0 8 (lit 0) (                                   -- j = 0          [j, i, c, a, t]
      loopB 9 triv (
        ite (lit 8) (var 0) brk (                        -- if 8 ≤ j break
        decl (-2000) 2000 (add (var 4) (var 1)) (        -- lim = t + i    [lim, j, i, c, a, t]
          ite (idx 4 (var 1)) (var 0)
            (seq (assign 3 (add (var 3) (lit 1))) (assign 1 (add (var 1) (lit 1))))
            brk)))))
  req := .tt
  pre := tpre
  post := tpost

/-- arith(x: 0..=10^9, y: 1..=1000) -> int: literals, precedence, division, large products. -/
def arith : Fn where
  params := [(.int 0 1000000000, false), (.int 1 1000, false)]
  rlo := -9223372036854775808
  rhi := 9223372036854775807
  body := assign 0
    (sub (add (mul (mul (lit 100000) (lit 100000)) (div (var 1) (var 2)))
              (sub (lit 7) (sub (var 2) (lit (-3)))))
         (mul (sub (var 1) (add (var 2) (lit 1))) (div (lit 4000000000) (lit 3))))
  req := .tt
  pre := tpre
  post := tpost

/-- gcd_steps(inout a: 0..=10^9, inout b: 0..=10^9) -> the number of subtraction-free Euclid steps:
    loop { if b ≤ 0 break; t = a - (a / b) * b; a = b; b = t; res = res + 1 }. Break-only loop with
    inout integers. Body environment: [res, a, b]. -/
def gcdSteps : Fn where
  params := [(.int 0 1000000000, true), (.int 0 1000000000, true)]
  rlo := 0
  rhi := 64
  body := loopB 64 triv (
    ite (var 2) (lit 0) brk (
      decl 0 1000000000 (sub (var 1) (mul (div (var 1) (var 2)) (var 2))) (   -- [t, res, a, b]
        seq (assign 2 (var 3))
       (seq (assign 3 (var 0))
            (assign 1 (add (var 1) (lit 1)))))))
  req := .tt
  pre := tpre
  post := tpost

def clearNames : FnNames := { name := "clear", params := ["a"] }
def swapNames : FnNames := { name := "swap", params := ["a", "i", "j"], locals := ["t"] }
def ringPushNames : FnNames := { name := "ring_push", params := ["buf", "head", "count", "v"], result := "res" }
def insertSortedNames : FnNames := { name := "insert_sorted", params := ["a", "k", "v"], result := "res", locals := ["j"] }
def axpyNames : FnNames := { name := "axpy", params := ["y", "x", "k"] }
def prefixSumNames : FnNames := { name := "prefix_sum", params := ["a"], result := "res", locals := ["acc", "i"] }

def all : List Example := [
  { name := "lower_bound", fns := [lowerBound], names := [lowerBoundNames], elemLo := -20, elemHi := 20, proved := "FnOk proved (from LowerBound3.lean)" },
  { name := "lower_bound_b", fns := [lowerBoundB], names := [lowerBoundBNames], elemLo := -20, elemHi := 20, proved := "FnOk proved (from LowerBound3.lean)" },
  { name := "lower_bound_1024", fns := [lowerBound1024], names := [lowerBound1024Names], elemLo := -2000, elemHi := 2000, proved := "FnOk proved" },
  { name := "lower_bound_b_1024", fns := [lowerBoundB1024], names := [lowerBoundB1024Names], elemLo := -2000, elemHi := 2000, proved := "FnOk proved" },
  { name := "use_clear", fns := [useClear, clearFn],
    names := [{ name := "use_clear", params := ["a"], result := "res", locals := ["t"] }, clearNames], proved := "FnOk proved, both functions" },
  { name := "clear", fns := [clearFn], names := [clearNames], proved := "FnOk proved" },
  { name := "swap", fns := [swapFn], names := [swapNames], proved := "FnOk proved" },
  { name := "ring_push", fns := [ringPush], names := [ringPushNames], proved := "FnOk proved" },
  { name := "prefix_sum", fns := [prefixSum8], names := [prefixSumNames], elemLo := -1100000, elemHi := 1100000,
    proved := "FnOk proved (inputs outside the precondition that are not stuck are also compared)" },
  { name := "ring_fill", fns := [ringFill, ringPush],
    names := [{ name := "ring_fill", params := ["buf", "head", "src"], result := "res", locals := ["count", "i", "v", "t"] }, ringPushNames] },
  { name := "insert_sorted", fns := [insertSorted], names := [insertSortedNames] },
  { name := "insertion_sort", fns := [insertionSort, insertSorted],
    names := [{ name := "insertion_sort", params := ["a"], result := "res", locals := ["k", "v", "pos"] }, insertSortedNames] },
  { name := "reverse", fns := [reverseFn, swapFn],
    names := [{ name := "reverse", params := ["a"], locals := ["i", "j", "t"] }, swapNames] },
  { name := "axpy", fns := [axpy], names := [axpyNames], elemLo := -1000, elemHi := 1000 },
  { name := "axpy_twice", fns := [axpyTwice, axpy],
    names := [{ name := "axpy_twice", params := ["a", "b", "k"], result := "res", locals := ["t"] }, axpyNames], elemLo := -1000, elemHi := 1000 },
  { name := "alias_bad", fns := [aliasBad, axpy],
    names := [{ name := "alias_bad", params := ["y", "k"], locals := ["t"] }, axpyNames], elemLo := -1000, elemHi := 1000 },
  { name := "alias_branch", fns := [aliasBranch, axpy],
    names := [{ name := "alias_branch", params := ["y", "x", "k"], locals := ["t"] }, axpyNames], elemLo := -1000, elemHi := 1000 },
  { name := "counter_inout", fns := [counterInout, bump],
    names := [{ name := "counter_inout", params := ["k"], result := "s" }, { name := "bump", params := ["x"], result := "res" }] },
  { name := "gcd_steps", fns := [gcdSteps], names := [{ name := "gcd_steps", params := ["a", "b"], result := "res", locals := ["t"] }] },
  { name := "sum8", fns := [sum8], names := [{ name := "sum8", params := ["a"], result := "s" }] },
  { name := "fill_sum", fns := [fillSum], names := [{ name := "fill_sum", params := ["a", "v"], result := "s" }] },
  { name := "max8", fns := [max8], names := [{ name := "max8", params := ["a"], result := "m" }] },
  { name := "rank_sum", fns := [rankSum, lowerBound],
    names := [{ name := "rank_sum", params := ["a", "q"], result := "t", locals := ["n", "j", "p", "r"] }, lowerBoundNames],
    elemLo := -20, elemHi := 20 },
  { name := "rank_sum_b", fns := [rankSum, lowerBoundB],
    names := [{ name := "rank_sum_b", params := ["a", "q"], result := "t", locals := ["n", "j", "p", "r"] }, lowerBoundBNames],
    elemLo := -20, elemHi := 20 },
  { name := "probe", fns := [probe, clobber],
    names := [{ name := "probe", params := ["a"], result := "res", locals := ["r"] }, { name := "clobber", params := ["a"] }] },
  { name := "counter_assign", fns := [counterAssign], names := [{ name := "counter_assign", params := ["k"], result := "s" }] },
  { name := "break_nested", fns := [breakNested],
    names := [{ name := "break_nested", params := ["a", "t"], result := "c", locals := ["i", "j", "lim"] }],
    elemLo := -1100, elemHi := 1100 },
  { name := "arith", fns := [arith], names := [{ name := "arith", params := ["x", "y"] }] }
]

theorem lbProgOk : ProgOk [lowerBound] := ⟨by simp [lowerBound, inI64], by simp [lowerBound, tysI64, inI64, condWf, ctWf], lowerBoundOk, trivial⟩
theorem lbBProgOk : ProgOk [lowerBoundB] := ⟨by simp [lowerBoundB, inI64], by simp [lowerBoundB, tysI64, inI64, condWf, ctWf], lowerBoundBOk, trivial⟩
theorem lb1024ProgOk : ProgOk [lowerBound1024] := ⟨by simp [lowerBound1024, inI64], by simp [lowerBound1024, tysI64, inI64, condWf, ctWf], lowerBound1024Ok, trivial⟩
theorem lbB1024ProgOk : ProgOk [lowerBoundB1024] := ⟨by simp [lowerBoundB1024, inI64], by simp [lowerBoundB1024, tysI64, inI64, condWf, ctWf], lowerBoundB1024Ok, trivial⟩
theorem useClearProgOk : ProgOk [useClear, clearFn] :=
  ⟨by simp [useClear, inI64], by simp [useClear, tysI64, inI64, condWf, ctWf], useClearOk, by simp [clearFn, inI64], by simp [clearFn, tysI64, inI64, condWf, ctWf], clearOk, trivial⟩
theorem swapProgOk : ProgOk [swapFn] := ⟨by simp [swapFn, inI64], by simp [swapFn, tysI64, inI64, condWf, ctWf], swapOk, trivial⟩
theorem ringPushProgOk : ProgOk [ringPush] := ⟨by simp [ringPush, inI64], by simp [ringPush, tysI64, inI64, condWf, ctWf], ringPushOk, trivial⟩
theorem prefixSum8ProgOk : ProgOk [prefixSum8] := ⟨by simp [prefixSum8, inI64], by simp [prefixSum8, tysI64, inI64, condWf, ctWf], prefixSum8Ok, trivial⟩
theorem prefixSum1024ProgOk : ProgOk [prefixSum1024] := ⟨by simp [prefixSum1024, inI64], by simp [prefixSum1024, tysI64, inI64, condWf, ctWf], prefixSum1024Ok, trivial⟩

end Tenon.Legacy

#print axioms Tenon.Legacy.lbBProgOk
#print axioms Tenon.Legacy.lbB1024ProgOk
#print axioms Tenon.Legacy.useClearProgOk
#print axioms Tenon.Legacy.swapProgOk
#print axioms Tenon.Legacy.ringPushProgOk
#print axioms Tenon.Legacy.prefixSum8ProgOk
#print axioms Tenon.Legacy.prefixSum1024ProgOk

#eval Tenon.evalFn [Tenon.Legacy.useClear, Tenon.Legacy.clearFn] 0 [.arr [5, 6, 7, 8, 9, 10, 11, 12]]
#eval Tenon.evalFn [Tenon.Legacy.useClear, Tenon.Legacy.clearFn] 1 [.arr [5, 6, 7, 8, 9, 10, 11, 12]]
#eval Tenon.evalFn [Tenon.Legacy.insertionSort, Tenon.Legacy.insertSorted] 0 [.arr [5, 3, 7, 1, 9, 0, 11, 2]]
#eval Tenon.evalFn [Tenon.Legacy.ringFill, Tenon.Legacy.ringPush] 0 [.arr [0, 0, 0, 0, 0, 0, 0, 0], .int 6, .arr [1, 2, 3, 4]]
#eval Tenon.evalFn [Tenon.Legacy.prefixSum8] 0 [.arr [1, 2, 3, 4, 5, 6, 7, 8]]
#eval Tenon.evalFn [Tenon.Legacy.counterInout, Tenon.Legacy.bump] 0 [.int 2]
#eval Tenon.evalFn [Tenon.Legacy.gcdSteps] 0 [.int 48, .int 18]
#eval Tenon.evalFn [Tenon.Legacy.aliasBad, Tenon.Legacy.axpy] 0 [.arr [1, 2, 3, 4, 5, 6, 7, 8], .int 2]
#eval Tenon.evalFn [Tenon.Legacy.reverseFn, Tenon.Legacy.swapFn] 0 [.arr [1, 2, 3, 4, 5, 6, 7, 8]]

-- Emitted C for every example (shown at build time).
#eval show IO Unit from do
  for ex in Tenon.Legacy.all do
    match Tenon.Emit.emitProgram {} ex.fns ex.names with
    | .ok c => IO.println s!"/* ---- {ex.name}: {ex.proved} ---- */\n{c}"
    | .error e => IO.println s!"/* ---- {ex.name}: ERROR {e} */"
