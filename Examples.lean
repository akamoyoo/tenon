import Tenon
import Ewma
import Sum8
import SurfaceExamples
import Emit
import Legacy
/-! Tenon examples. First the K4 examples of emitter round 4 moved to Tenon (slices, `len`, `forE`, comparisons,
    `sel`), then the float kernels.

    Proved `FnOk` and `ProgOk` (no `sorry`): `prefixSum`, `prefixSum10M`, `prefixSumW`, `lowerBoundS`
    (branch-free), `lowerBoundBr` (branching), `rollingSum`, `rollingSumExact`, `rollingSumW`, `argmax`;
    `ewma` and `sum8` (imported from Ewma.lean and Sum8.lean); `rolling_mean`, `dot`, `rolling_std`
    (surface syntax), `rollingVar` (core term) and the same as `rolling_var_s` (surface syntax).
    The functions in the section "Not proved" are NOT checked programs: they exist to exercise the
    emitter and are compared with the C only on inputs where `evalFn` is `some`. -/
namespace Tenon.Examples
open Tenon Stmt Expr Tenon.Emit

def triv : List Val → Nat → List Val → Prop := fun _ _ _ => True
def tpost : List Val → Int → List Val → Prop := fun _ _ _ => True
def tpre : List Val → Prop := fun _ => True

/-! ### (a) prefix sum: `Tenon.prefixSum` of PrefixSum.lean, len ≤ 10^6, out in ±10^15.
    The same function for len ≤ 10^7 (out in ±10^16), for the 10^7-element benchmark: the proof is the
    one of PrefixSum.lean with the constants changed. -/

/-- Loop environment: [acc, res, x, out]: |acc| ≤ 10^9 · i. -/
def psInv (_ : List Val) (i : Nat) (env : List Val) : Prop :=
  -1000000000 * (i : Int) ≤ geti env 0 ∧ geti env 0 ≤ 1000000000 * (i : Int)

/-- `prefixSum` of PrefixSum.lean (a K4 file), restated on Tenon with its precondition as `req`. -/
def prefixSum : Fn where
  params := [(.slice (-1000000000) 1000000000, false), (.slice (-1000000000000000) 1000000000000000, true)]
  rlo := 0
  rhi := 0
  body :=
    decl (-1000000000000000) 1000000000000000 (lit 0) (
      forE (.len 2) psInv (
        seq (assign 1 (add (var 1) (idx 3 (var 0))))
            (store 4 (var 0) (var 1))))
  req := .and (.eq (.len 0) (.len 1)) (.le (.len 0) (.lit 1000000))
  pre := fun _ => True
  post := fun _ _ _ => True

theorem prefixSumOk : FnOk [] prefixSum := by kvc prefixSum [psInv]

def prefixSum10M : Fn where
  params := [(.slice (-1000000000) 1000000000, false), (.slice (-10000000000000000) 10000000000000000, true)]
  rlo := 0
  rhi := 0
  body :=
    decl (-10000000000000000) 10000000000000000 (lit 0) (
      forE (.len 2) psInv (
        seq (assign 1 (add (var 1) (idx 3 (var 0))))
            (store 4 (var 0) (var 1))))
  req := .and (.eq (.len 0) (.len 1)) (.le (.len 0) (.lit 10000000))
  pre := fun _ => True
  post := fun _ _ _ => True

theorem prefixSum10MOk : FnOk [] prefixSum10M := by kvc prefixSum10M [psInv]

/-! ### The same two integer kernels with the output declared as the full int64 range.
    The body, the invariant and the proof are unchanged (`acc` keeps its tight range, so every stored
    value is in range trivially). What changes is the ENTRY condition: any contents of `out` have the
    parameter type, so a binding need not scan or zero-fill the output buffer (finding H1 of emit4). -/

def prefixSumW : Fn where
  params := [(.slice (-1000000000) 1000000000, false), (.slice (-9223372036854775808) 9223372036854775807, true)]
  rlo := 0
  rhi := 0
  body :=
    decl (-10000000000000000) 10000000000000000 (lit 0) (
      forE (.len 2) psInv (
        seq (assign 1 (add (var 1) (idx 3 (var 0))))
            (store 4 (var 0) (var 1))))
  req := .and (.eq (.len 0) (.len 1)) (.le (.len 0) (.lit 10000000))
  pre := fun _ => True
  post := fun _ _ _ => True

theorem prefixSumWOk : FnOk [] prefixSumW := by kvc prefixSumW [psInv]

/-! ### (b) lower_bound over a slice, branch-free: `lower_bound(a: [int], p: int) -> 0..=len(a)`

    base = 0; n = len(a)
    loop { if n <= 1 break; half = n / 2; base = a[base + half - 1] < p ? base + half : base; n = n - half }
    if n <= 0 { res = base } else { res = base + (a[base] < p) }

The number of iterations depends only on the length. The loop is a `loopB`; its proof bound is 2^63
and the variant is `n ≤ len(a) - i` (both exist only in the proof). Safe for every length, 0 included.
Elements and `p` are any int64 values (they are only compared). -/

/-- Loop environment [n, base, res, a, p]: 0 ≤ n, 0 ≤ base, base + n ≤ len(a), and the variant. -/
def lbsInv (env : List Val) (i : Nat) (env' : List Val) : Prop :=
  0 ≤ geti env' 0 ∧ 0 ≤ geti env' 1 ∧ geti env' 1 + geti env' 0 ≤ leni env 3 ∧ geti env' 0 ≤ leni env 3 - (i : Int)

def lowerBoundS : Fn where
  params := [(.slice (-9223372036854775808) 9223372036854775807, false), (.int (-9223372036854775808) 9223372036854775807, false)]
  rlo := 0
  rhi := 9223372036854775807
  body :=
    decl 0 9223372036854775807 (lit 0) (                 -- base = 0          [base, res, a, p]
    decl 0 9223372036854775807 (.len 2) (                 -- n = len(a)        [n, base, res, a, p]
      seq
        (loopB 9223372036854775808 lbsInv (
          ite (var 0) (lit 1) brk (                      -- if n ≤ 1 break
          decl 0 9223372036854775807 (div (var 0) (lit 2)) (   -- half = n / 2  [half, n, base, res, a, p]
            seq (assign 2 (.sel (lt (idx 4 (sub (add (var 2) (var 0)) (lit 1))) (var 5))
                               (add (var 2) (var 0)) (var 2)))  -- base = a[base+half-1] < p ? base+half : base
                (assign 1 (sub (var 1) (var 0)))))))     -- n = n - half
        (ite (var 0) (lit 0)                             -- if n ≤ 0
          (assign 2 (var 1))                             --   res = base
          (assign 2 (add (var 1) (lt (idx 3 (var 1)) (var 4)))))))   -- else res = base + (a[base] < p)
  req := .tt
  pre := fun _ => True
  post := fun a r _ => match a with | [.arr l, _] => 0 ≤ r ∧ r ≤ l.length | _ => False

theorem lowerBoundSOk : FnOk [] lowerBoundS := by kvc lowerBoundS [lbsInv]

/-! ### lower_bound over a slice with a data-dependent branch (the classical lo/hi search), for the
    benchmark. `if a[mid] < p` has to be written `ite 1 (a[mid] < p)`: `ite` tests only `≤`. -/

/-- Loop environment [hi, lo, res, a, p]. -/
def lbrInv (env : List Val) (i : Nat) (env' : List Val) : Prop :=
  geti env' 1 ≤ geti env' 0 ∧ geti env' 0 ≤ leni env 3 ∧ geti env' 0 - geti env' 1 ≤ leni env 3 - (i : Int)

def lowerBoundBr : Fn where
  params := [(.slice (-9223372036854775808) 9223372036854775807, false), (.int (-9223372036854775808) 9223372036854775807, false)]
  rlo := 0
  rhi := 9223372036854775807
  body :=
    decl 0 9223372036854775807 (lit 0) (                 -- lo = 0            [lo, res, a, p]
    decl 0 9223372036854775807 (.len 2) (                 -- hi = len(a)       [hi, lo, res, a, p]
      seq
        (loopB 9223372036854775808 lbrInv (
          ite (var 0) (var 1) brk (                      -- if hi ≤ lo break
          decl 0 9223372036854775807 (add (var 1) (div (sub (var 0) (var 1)) (lit 2))) (   -- mid  [mid, hi, lo, res, a, p]
            ite (lit 1) (lt (idx 4 (var 0)) (var 5))     -- if a[mid] < p
              (assign 2 (add (var 0) (lit 1)))           --   lo = mid + 1
              (assign 1 (var 0))))))                     -- else hi = mid
        (assign 2 (var 1))))                             -- res = lo
  req := .tt
  pre := fun _ => True
  post := fun a r _ => match a with | [.arr l, _] => 0 ≤ r ∧ r ≤ l.length | _ => False

theorem lowerBoundBrOk : FnOk [] lowerBoundBr := by kvc lowerBoundBr [lbrInv]

/-! ### (d) argmax over a slice, branch-free: `argmax(a: [int]) -> index of the first maximum`
    (0 for an empty slice; the binding refuses an empty array, as NumPy does).

    bv = INT64_MIN; for i in 0..len(a) { c = bv < a[i]; res = c ? i : res; bv = c ? a[i] : bv }

Elements are any int64 values. If every element is INT64_MIN the answer stays 0, which is right. -/

/-- Loop environment [bv, res, a]: res < i, or nothing has been seen yet. -/
def amInv (_ : List Val) (i : Nat) (env' : List Val) : Prop :=
  geti env' 1 < (i : Int) ∨ ((i : Int) = 0 ∧ geti env' 1 = 0)

def argmax : Fn where
  params := [(.slice (-9223372036854775808) 9223372036854775807, false)]
  rlo := 0
  rhi := 9223372036854775807
  body :=
    decl (-9223372036854775808) 9223372036854775807 (lit (-9223372036854775808)) (  -- bv = INT64_MIN   [bv, res, a]
      forE (.len 2) amInv (                               --                   [i, bv, res, a]
        decl 0 1 (lt (var 1) (idx 3 (var 0))) (          -- c = bv < a[i]     [c, i, bv, res, a]
          seq (assign 3 (.sel (var 0) (var 1) (var 3)))                 -- res = c ? i : res
              (assign 2 (.sel (var 0) (idx 4 (var 1)) (var 2))))))      -- bv = c ? a[i] : bv
  req := .tt
  pre := fun _ => True
  post := fun a r _ => match a with
    | [.arr l] => 0 ≤ r ∧ (r < l.length ∨ (l.length = 0 ∧ r = 0))
    | _ => False

theorem argmaxOk : FnOk [] argmax := by kvc argmax [amInv]

/-! ### (c) rolling window sum, maintained incrementally
    `rolling_sum(x: [int in ±10^9], w: 1..=10^6, out: inout [int in ±2.1·10^16])`
       requires len(x) == len(out) && len(x) <= 10^7
    out[i] = x[i] + x[i-1] + ... over the last min(i+1, w) elements.

    acc = 0; m = min(w, len(x))                     -- `sel (w <= len) w len`
    for i in 0..m          { acc = acc + x[i];            out[i] = acc }       -- the window grows
    for j in 0..len(x) - m { acc = acc + x[j+m] - x[j];   out[j+m] = acc }     -- the window slides

Two loops and no test in either body. (One loop with `sel (w <= i) x[i-w] 0` is not possible: `sel`
evaluates both arms and `x[i-w]` is stuck for i < w.)

What is proved: no index out of range, no overflow, every stored value inside the declared range of
`out`. What is NOT proved: that the stored values are the window sums (no functional postcondition).
Because the proof does not know that `acc` is a sum of at most w elements, it bounds it by what the
loop does to it: |acc| ≤ 10^9·m after the first loop (m ≤ 10^6, so 10^15) and it moves by at most
2·10^9 per step of the second (at most 10^7 steps): |acc| ≤ 10^15 + 2·10^16 = 2.1·10^16. That is why
`out` is declared ±2.1·10^16 and not ±10^15. `rollingSumExact` below proves the tight range. -/

/-- First loop, [m, acc, res, x, w, out]: |acc| ≤ 10^9 · i. -/
def rsInv1 (_ : List Val) (i : Nat) (env' : List Val) : Prop :=
  -1000000000 * (i : Int) ≤ geti env' 1 ∧ geti env' 1 ≤ 1000000000 * (i : Int)

/-- Second loop, [m, acc, res, x, w, out]: |acc| ≤ 10^15 + 2 · 10^9 · j. -/
def rsInv2 (_ : List Val) (j : Nat) (env' : List Val) : Prop :=
  -1000000000000000 - 2000000000 * (j : Int) ≤ geti env' 1 ∧ geti env' 1 ≤ 1000000000000000 + 2000000000 * (j : Int)

def rollingSum : Fn where
  params := [(.slice (-1000000000) 1000000000, false), (.int 1 1000000, false),
             (.slice (-21000000000000000) 21000000000000000, true)]
  rlo := 0
  rhi := 0
  body :=
    decl (-21000000000000000) 21000000000000000 (lit 0) (            -- acc = 0     [acc, res, x, w, out]
    decl 0 1000000 (.sel (le (var 3) (.len 2)) (var 3) (.len 2)) (      -- m = min(w, len(x))   [m, acc, res, x, w, out]
      seq
        (forE (var 0) rsInv1 (                                       -- for i in 0..m     [i, m, acc, res, x, w, out]
          seq (assign 2 (add (var 2) (idx 4 (var 0))))               --   acc = acc + x[i]
              (store 6 (var 0) (var 2))))                            --   out[i] = acc
        (forE (sub (.len 3) (var 0)) rsInv2 (                         -- for j in 0..len(x)-m   [j, m, acc, res, x, w, out]
          seq (assign 2 (sub (add (var 2) (idx 4 (add (var 0) (var 1)))) (idx 4 (var 0))))  -- acc = acc + x[j+m] - x[j]
              (store 6 (add (var 0) (var 1)) (var 2))))))            --   out[j+m] = acc
  req := .and (.eq (.len 0) (.len 2)) (.le (.len 0) (.lit 10000000))
  pre := fun _ => True
  post := fun _ _ _ => True

theorem rollingSumOk : FnOk [] rollingSum := by kvc rollingSum [rsInv1, rsInv2]

/-- `rollingSum` with `out` declared as the full int64 range (see `prefixSumW`). -/
def rollingSumW : Fn where
  params := [(.slice (-1000000000) 1000000000, false), (.int 1 1000000, false),
             (.slice (-9223372036854775808) 9223372036854775807, true)]
  rlo := 0
  rhi := 0
  body :=
    decl (-21000000000000000) 21000000000000000 (lit 0) (
    decl 0 1000000 (.sel (le (var 3) (.len 2)) (var 3) (.len 2)) (
      seq
        (forE (var 0) rsInv1 (
          seq (assign 2 (add (var 2) (idx 4 (var 0))))
              (store 6 (var 0) (var 2))))
        (forE (sub (.len 3) (var 0)) rsInv2 (
          seq (assign 2 (sub (add (var 2) (idx 4 (add (var 0) (var 1)))) (idx 4 (var 0))))
              (store 6 (add (var 0) (var 1)) (var 2))))))
  req := .and (.eq (.len 0) (.len 2)) (.le (.len 0) (.lit 10000000))
  pre := fun _ => True
  post := fun _ _ _ => True

theorem rollingSumWOk : FnOk [] rollingSumW := by kvc rollingSumW [rsInv1, rsInv2]

def geta (env : List Val) (i : Nat) : List Int := match env[i]? with | some (.arr l) => l | _ => []

/-! ### (c') rolling window sum with the tight range: `out` in ±10^15
    The same program as `rollingSum` with `acc` and `out` declared ±10^15. Now the proof must know what
    `acc` is: the invariants say acc = x[0] + ... + x[i-1] (first loop) and acc = x[j] + ... + x[j+m-1]
    (second loop), and a lemma bounds a sum of d elements by 10^9·d. The recipe (`vc_loop`) is not
    enough here; see README.md. Still no functional postcondition about `out`. -/

/-- Sum of the first k elements. -/
def psum (l : List Int) : Nat → Int
  | 0 => 0
  | k + 1 => psum l k + l[k]?.getD 0

theorem psum_step (l : List Int) (k : Nat) (v : Int) (h : l[k]? = some v) : psum l (k + 1) = psum l k + v := by
  simp [psum, h]

/-- A sum of b - a consecutive elements, each within ±10^9. -/
theorem psum_bound (l : List Int) (hl : ∀ x ∈ l, -1000000000 ≤ x ∧ x ≤ 1000000000) :
    ∀ (d a : Nat), a + d ≤ l.length →
      -1000000000 * (d : Int) ≤ psum l (a + d) - psum l a ∧ psum l (a + d) - psum l a ≤ 1000000000 * (d : Int) := by
  intro d
  induction d with
  | zero => intro a _; simp
  | succ d ih =>
    intro a h
    have h1 := ih a (by omega)
    have hlt : a + d < l.length := by omega
    have hm := hl l[a + d] (List.getElem_mem hlt)
    have hs := psum_step l (a + d) l[a + d] (List.getElem?_eq_getElem hlt)
    have e : a + (d + 1) = a + d + 1 := by omega
    rw [e, hs]
    omega

theorem get_some (l : List Int) (k : Nat) (h : k < l.length) : ∃ v, l[k]? = some v :=
  ⟨l[k], List.getElem?_eq_getElem h⟩

/-- First loop, [m, acc, res, x, w, out]: acc is the sum of the first i elements. -/
def rsxInv1 (env : List Val) (i : Nat) (env' : List Val) : Prop :=
  geti env' 1 = psum (geta env 3) i

/-- Second loop, [m, acc, res, x, w, out]: acc is the sum of x[j .. j+m). -/
def rsxInv2 (env : List Val) (j : Nat) (env' : List Val) : Prop :=
  geti env' 1 = psum (geta env 3) (j + (geti env 0).toNat) - psum (geta env 3) j

def rollingSumExact : Fn where
  params := [(.slice (-1000000000) 1000000000, false), (.int 1 1000000, false),
             (.slice (-1000000000000000) 1000000000000000, true)]
  rlo := 0
  rhi := 0
  body :=
    decl (-1000000000000000) 1000000000000000 (lit 0) (
    decl 0 1000000 (.sel (le (var 3) (.len 2)) (var 3) (.len 2)) (
      seq
        (forE (var 0) rsxInv1 (
          seq (assign 2 (add (var 2) (idx 4 (var 0))))
              (store 6 (var 0) (var 2))))
        (forE (sub (.len 3) (var 0)) rsxInv2 (
          seq (assign 2 (sub (add (var 2) (idx 4 (add (var 0) (var 1)))) (idx 4 (var 0))))
              (store 6 (add (var 0) (var 1)) (var 2))))))
  req := .and (.eq (.len 0) (.len 2)) (.le (.len 0) (.lit 10000000))
  pre := fun _ => True
  post := fun _ _ _ => True

theorem rollingSumExactOk : FnOk [] rollingSumExact := by
  intro args hin hpre _
  match args, hin, hpre with
  | [.arr x, .int w, .arr o], hin, hpre =>
    simp [hasAll, Val.has, rollingSumExact] at hin
    simp [rollingSumExact, evalC, evalCT] at hpre
    simp [rollingSumExact, wpS, wpE, popped, inI64, rsxInv1, rsxInv2, geti, geta]
    intro _ _ hxl _ _ _
    have hm0 : (0 : Int) ≤ if w ≤ ↑x.length then w else ↑x.length := by split <;> omega
    have hm1 : (if w ≤ ↑x.length then w else ↑x.length) ≤ 1000000 := by split <;> omega
    have hm2 : (if w ≤ ↑x.length then w else ↑x.length) ≤ (x.length : Int) := by split <;> omega
    generalize (if w ≤ ↑x.length then w else ↑x.length) = m at hm0 hm1 hm2 ⊢
    obtain ⟨mN, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
    have hB := psum_bound x hin.1.2
    have h0 : psum x 0 = 0 := rfl
    have hG : ∀ k, k < x.length → ∃ v, x[k]? = some v ∧ psum x (k + 1) = psum x k + v := by
      intro k hk
      obtain ⟨v, hv⟩ := get_some x k hk
      exact ⟨v, hv, psum_step x k v hv⟩
    refine ⟨hm0, hm1, fun _ _ => ⟨hm0, by simp [psum], ?_, ?_⟩⟩
    · intro i env' hi hΓ hsame hlens
      obtain ⟨xi, hxi⟩ := get_some x i (by omega)
      have hs := psum_step x i xi hxi
      have hb := hB (i + 1) 0 (by omega)
      simp only [Nat.zero_add, h0] at hb
      env_open hΓ
      simp [sameAt, kept, mods, List.range, List.range.loop, List.filter] at hsame
      simp [lens, shape] at hlens
      (repeat cases ‹_ ∧ _›)
      subst_vars
      simp [wpS, wpE, popped, inI64, rsxInv1, rsxInv2, geti, geta]
      intro hacc _ _ _
      refine ⟨by omega, ?_⟩
      intro v hv _ _
      have e : v = xi := by rw [hxi] at hv; exact (Option.some.inj hv).symm
      subst e
      vc_leaves
    · intro env' hΓ hsame hlens
      env_open hΓ
      simp [sameAt, kept, mods, List.range, List.range.loop, List.filter] at hsame
      simp [lens, shape] at hlens
      (repeat cases ‹_ ∧ _›)
      subst_vars
      simp [geti, geta]
      intro hacc _ _
      refine ⟨by omega, by omega, by omega, ?_, ?_⟩
      · intro j env'' hj hΓ2 hsame2 hlens2
        obtain ⟨xa, hxa, hsa⟩ := hG j (by omega)
        obtain ⟨xb, hxb, hsb⟩ := hG (j + mN) (by omega)
        have hb := hB mN (j + 1) (by omega)
        have e2 : j + 1 + mN = j + mN + 1 := by omega
        rw [e2] at hb
        env_open hΓ2
        simp [sameAt, kept, mods, List.range, List.range.loop, List.filter] at hsame2
        simp [lens, shape] at hlens2
        (repeat cases ‹_ ∧ _›)
        subst_vars
        simp [wpS, wpE, popped, inI64, rsxInv2, geti, geta]
        have e1 : (↑j + ↑mN : Int).toNat = j + mN := by omega
        rw [e1, e2]
        intro hacc _ _ _ _
        refine ⟨by omega, by omega, by omega, ?_⟩
        intro v hv _ _
        have ev : v = xb := by rw [hxb] at hv; exact (Option.some.inj hv).symm
        subst ev
        refine ⟨by omega, fun _ => ⟨by omega, ?_⟩⟩
        intro v1 hv1 _ _
        have ev1 : v1 = xa := by rw [hxa] at hv1; exact (Option.some.inj hv1).symm
        subst ev1
        vc_leaves
      · intro env'' hΓ2 hsame2 hlens2
        vc_loop hΓ2 hsame2 hlens2 [rsxInv2, geti, geta]
  | [], hin, _ => simp [hasAll, rollingSumExact] at hin
  | [_], hin, _ => simp [hasAll, rollingSumExact] at hin
  | [_, _], hin, _ => simp [hasAll, rollingSumExact] at hin
  | _ :: _ :: _ :: _ :: _, hin, _ => simp [hasAll, rollingSumExact] at hin
  | [.int _, _, _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin
  | [.flt _, _, _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin
  | [.farr _, _, _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin
  | [.arr _, .arr _, _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin
  | [.arr _, .flt _, _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin
  | [.arr _, .farr _, _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin
  | [.arr _, .int _, .int _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin
  | [.arr _, .int _, .flt _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin
  | [.arr _, .int _, .farr _], hin, _ => simp [hasAll, Val.has, rollingSumExact] at hin

/-! ## Not proved: programs that exercise the emitter on Tenon features -/

/-- scale_sum(a: [int in ±1000], k: ±1000) -> sum of the clamped products.
    `a` is by value and stored into: the emitter gives it a private heap copy; the caller's buffer
    must be unchanged.  Body [res, a, k]. -/
def scaleSum : Fn where
  params := [(.slice (-1000) 1000, false), (.int (-1000) 1000, false)]
  rlo := -1000000000000
  rhi := 1000000000000
  body :=
    seq (assign 0 (lit 0)) (
    forE (.len 1) triv (                                              -- [i, res, a, k]
      decl (-1000000) 1000000 (mul (idx 2 (var 0)) (var 3)) (        -- t = a[i] * k   [t, i, res, a, k]
        seq (store 3 (var 1) (.sel (le (var 0) (lit 1000))
                                (.sel (le (lit (-1000)) (var 0)) (var 0) (lit (-1000))) (lit 1000)))
            (assign 2 (add (var 2) (idx 3 (var 1)))))))
  req := .tt
  pre := tpre
  post := tpost

/-- ps_last(x: [int], out: inout [int]) -> the last running sum (0 if empty): forwards a by-value
    slice and an inout slice to `prefixSum`.  Body [res, x, out]; callee 0 = prefixSum. -/
def psLast : Fn where
  params := [(.slice (-1000000000) 1000000000, false), (.slice (-1000000000000000) 1000000000000000, true)]
  rlo := -1000000000000000
  rhi := 1000000000000000
  body :=
    seq (assign 0 (lit 0)) (
    decl 0 0 (lit 0) (                                               -- [t, res, x, out]
      seq (Stmt.call 0 [(2, false), (3, true)] 0)                         -- t = prefix_sum(x, inout out)
          (ite (lit 1) (.len 3) (assign 1 (idx 3 (sub (.len 3) (lit 1)))) skip)))
  req := .tt
  pre := tpre
  post := tpost

/-- ps_arr(a: [int; 8], out: inout [int]): a fixed-length array passed where a slice is expected.
    `evalFn` is `some` only when len(out) ≥ 8.  Body [res, a, out]. -/
def psArr : Fn where
  params := [(.arr 8 (-1000000000) 1000000000, false), (.slice (-1000000000000000) 1000000000000000, true)]
  rlo := 0
  rhi := 100
  body := decl 0 0 (lit 0) (seq (Stmt.call 0 [(2, false), (3, true)] 0) (assign 1 (add (.len 2) (.len 3))))
  req := .tt
  pre := tpre
  post := tpost

/-- sum8(a: [int; 8]) and sum_slice8(x: [int]): a slice passed where an array of 8 is expected;
    `evalFn` is `some` only when len(x) = 8. -/
def sumArr8 : Fn where
  params := [(.arr 8 (-1000000) 1000000, false)]
  rlo := -8000000
  rhi := 8000000
  body := seq (assign 0 (lit 0)) (forE (.len 1) triv (assign 1 (add (var 1) (idx 2 (var 0)))))
  req := .tt
  pre := tpre
  post := tpost

def sumSlice8 : Fn where
  params := [(.slice (-1000000) 1000000, false)]
  rlo := -8000000
  rhi := 8000000
  body := Stmt.call 0 [(1, false)] 0
  req := .tt
  pre := tpre
  post := tpost

/-- for_e(n: 0..=20, a: inout [int in 0..=10^6]): the bound of a `forE` is a variable that the body
    changes (the bound was evaluated once), and the body also assigns the counter (F2: the next
    iteration continues from the loop's own count).  Body [res, n, a]. -/
def forEProbe : Fn where
  params := [(.int 0 20, false), (.slice 0 1000000, true)]
  rlo := 0
  rhi := 1000000
  body :=
    decl 0 40 (var 1) (                                              -- m = n          [m, res, n, a]
      forE (var 0) triv (                                            --                [i, m, res, n, a]
        seq (assign 1 (add (var 1) (lit 1)))                         -- m = m + 1
       (seq (ite (var 0) (lit 3) (assign 0 (add (var 0) (lit 5))) skip)   -- if i ≤ 3 { i = i + 5 }
       (seq (assign 2 (add (var 2) (add (var 0) (var 1))))           -- res = res + (i + m)
            (ite (var 0) (sub (.len 4) (lit 1)) (store 4 (var 0) (var 2)) skip)))))   -- if i ≤ len-1 { a[i] = res }
  req := .tt
  pre := tpre
  post := tpost

/-- sel_mix(a: [int], b: [int], k: 0..=10^6): loads in both arms of a `sel`, a condition that is not
    a comparison, `eq`, `le`, comparisons inside arithmetic. Stuck unless len(a) ≤ len(b).
    Body [res, a, b, k]. -/
def selMix : Fn where
  params := [(.slice (-100) 100, false), (.slice (-100) 100, false), (.int 0 1000000, false)]
  rlo := -1000000000
  rhi := 1000000000
  body :=
    seq (assign 0 (lit 0)) (
    forE (.len 1) triv (                                              -- [i, res, a, b, k]
      assign 1 (add (add (add (add (var 1)
        (.sel (lt (idx 2 (var 0)) (idx 3 (var 0))) (idx 3 (var 0)) (idx 2 (var 0))))     -- max(a[i], b[i])
        (mul (eq (idx 2 (var 0)) (idx 3 (var 0))) (lit 3)))
        (le (idx 2 (var 0)) (var 4)))
        (.sel (sub (idx 2 (var 0)) (idx 3 (var 0))) (.sel (var 4) (lit 7) (lit 9)) (lit (-2))))))
  req := .tt
  pre := tpre
  post := tpost

/-- len_mix(a: [int; 5], s: [int]) -> 10 · len(a) + len(s) (stuck when len(s) > 50). -/
def lenMix : Fn where
  params := [(.arr 5 (-10) 10, false), (.slice (-10) 10, false)]
  rlo := 0
  rhi := 100
  body := assign 0 (add (mul (.len 1) (lit 10)) (.len 2))
  req := .tt
  pre := tpre
  post := tpost

/-- reverse(a: inout [int]): in place, a `loopB` over a slice.  Body [res, a]. -/
def reverseS : Fn where
  params := [(.slice (-1000000) 1000000, true)]
  rlo := 0
  rhi := 0
  body :=
    decl 0 9223372036854775807 (lit 0) (                             -- lo             [lo, res, a]
    decl 0 9223372036854775807 (.len 2) (                             -- hi             [hi, lo, res, a]
      loopB 4611686018427387904 triv (
        ite (var 0) (add (var 1) (lit 1)) brk (                      -- if hi ≤ lo + 1 break
        decl (-1000000) 1000000 (idx 3 (var 1)) (                    -- t = a[lo]      [t, hi, lo, res, a]
          seq (store 4 (var 2) (idx 4 (sub (var 1) (lit 1))))        -- a[lo] = a[hi-1]
         (seq (store 4 (sub (var 1) (lit 1)) (var 0))                -- a[hi-1] = t
         (seq (assign 2 (add (var 2) (lit 1)))
              (assign 1 (sub (var 1) (lit 1))))))))))
  req := .tt
  pre := tpre
  post := tpost

/-! ## Float kernels

`ewma` and `sum8` are Ewma.lean and Sum8.lean (imported, proved there with `kvc`).
The three new ones follow. For every one of them what is proved is SAFETY (no index out of range, no
integer overflow in the index arithmetic) for all inputs satisfying `req`; float arithmetic cannot be
stuck, so the invariants are `True`. Nothing is proved about the numbers that come out. -/

/-! ### (a) rolling mean, maintained incrementally, in the surface syntax of Surface.lean

    out[i] = mean of the last min(i + 1, w) elements.
    The running sum is updated as `acc = acc + x[j+m] - x[j]`: rounding errors accumulate over the whole
    array (no compensation), and one infinity or NaN in `x` makes every later output NaN. That is the
    function as defined, in a fixed order; it is not the most accurate rolling mean.
    `m = min(w, len(x))` is written with an `if`, because the surface syntax has no `sel`. -/

kfn rolling_mean(x: fslice, w: int(1, 1000000), out: inout fslice) -> int(0, 0)
  requires (len(x) == len(out))
{
  let acc: f64 = 0.0;
  let m: int(0, 1000000) = w;
  if len(x) < w { m = len(x); } else { }
  for i upto m invariant_lean (True) {
    acc = acc + x[i];
    out[i] = acc / (i + 1);
  }
  for j upto len(x) - m invariant_lean (True) {
    acc = acc + x[j + m] - x[j];
    out[j + m] = acc / m;
  }
}

theorem rolling_meanOk : FnOk [] rolling_mean := by kvc rolling_mean []

/-! ### (c) dot product in the fixed eight-lane order of Sum8, in the surface syntax

    lane k accumulates x[8i+k] * y[8i+k]; the tail goes into lane 0; then ((a0+a1)+(a2+a3))+((a4+a5)+(a6+a7)).
    Result in out[0]. Every product is rounded, then added (no fused multiply-add). -/

kfn dot(x: fslice, y: fslice, out: inout fslice) -> int(0, 0)
  requires (len(x) == len(y) && 1 <= len(out))
{
  let a0: f64 = 0.0;
  let a1: f64 = 0.0;
  let a2: f64 = 0.0;
  let a3: f64 = 0.0;
  let a4: f64 = 0.0;
  let a5: f64 = 0.0;
  let a6: f64 = 0.0;
  let a7: f64 = 0.0;
  let n8: int(0, 1152921504606846975) = len(x) / 8;
  for i upto n8 invariant_lean (True) {
    a0 = a0 + x[8 * i + 0] * y[8 * i + 0];
    a1 = a1 + x[8 * i + 1] * y[8 * i + 1];
    a2 = a2 + x[8 * i + 2] * y[8 * i + 2];
    a3 = a3 + x[8 * i + 3] * y[8 * i + 3];
    a4 = a4 + x[8 * i + 4] * y[8 * i + 4];
    a5 = a5 + x[8 * i + 5] * y[8 * i + 5];
    a6 = a6 + x[8 * i + 6] * y[8 * i + 6];
    a7 = a7 + x[8 * i + 7] * y[8 * i + 7];
  }
  for j upto len(x) - 8 * n8 invariant_lean (True) {
    a0 = a0 + x[8 * n8 + j] * y[8 * n8 + j];
  }
  out[0] = ((a0 + a1) + (a2 + a3)) + ((a4 + a5) + (a6 + a7));
}

set_option maxRecDepth 8000 in
theorem dotOk : FnOk [] dot := by kvc dot []

/-! ### (b) rolling variance over a window, from running sums of x and x², as a core term

    out[i] = clamp((s2 - s1·s1/n) / n) over the last n = min(i + 1, w) elements (population variance).
    THIS IS THE NUMERICALLY NAIVE FORMULA: s2 - s1²/n cancels catastrophically when the mean is large
    compared with the spread, and the incremental updates of s1 and s2 drift. The computed value can be
    slightly negative; it is clamped with `selLe v 0 0 v` ("0 if v ≤ 0, else v"), in that orientation so
    that a NaN is NOT turned into 0 (the comparison is false on NaN and the else arm is `v`).
    A core term because the surface syntax has neither `sel` nor `selLe`. -/

def rvInv (_ : List Val) (_ : Nat) (_ : List Val) : Prop := True

def rollingVar : Fn where
  params := [(.fslice, false), (.int 1 1000000, false), (.fslice, true)]
  rlo := 0
  rhi := 0
  body :=                                                            -- [res, x, w, out]
    fdecl (.lit 0.0) (                                               -- s1 = 0.0   [s1, res, x, w, out]
    fdecl (.lit 0.0) (                                               -- s2 = 0.0   [s2, s1, res, x, w, out]
    decl 0 1000000 (.sel (le (var 4) (.len 3)) (var 4) (.len 3)) (      -- m = min(w, len(x))   [m, s2, s1, res, x, w, out]
      seq
        (forE (var 0) rvInv (                                        -- [i, m, s2, s1, res, x, w, out]
          seq (fassign 3 (.add (.var 3) (.idx 5 (var 0))))           -- s1 = s1 + x[i]
         (seq (fassign 2 (.add (.var 2) (.mul (.idx 5 (var 0)) (.idx 5 (var 0)))))   -- s2 = s2 + x[i]*x[i]
              (fdecl (.ofInt (add (var 0) (lit 1))) (                -- n = i + 1  [n, i, m, s2, s1, res, x, w, out]
               fdecl (.div (.sub (.var 3) (.div (.mul (.var 4) (.var 4)) (.var 0))) (.var 0)) (   -- v = (s2 - s1*s1/n)/n
                 fstore 9 (var 2) (.selLe (.var 0) (.lit 0.0) (.lit 0.0) (.var 0))))))))   -- out[i] = v ≤ 0 ? 0 : v
        (fdecl (.ofInt (var 0)) (                                    -- mf = m     [mf, m, s2, s1, res, x, w, out]
          forE (sub (.len 5) (var 1)) rvInv (                         -- [j, mf, m, s2, s1, res, x, w, out]
            fdecl (.idx 6 (add (var 0) (var 2))) (                   -- a = x[j+m] [a, j, mf, m, s2, s1, res, x, w, out]
            fdecl (.idx 7 (var 1)) (                                 -- b = x[j]   [b, a, j, mf, m, s2, s1, res, x, w, out]
              seq (fassign 6 (.sub (.add (.var 6) (.var 1)) (.var 0)))                 -- s1 = s1 + a - b
             (seq (fassign 5 (.sub (.add (.var 5) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.var 0))))   -- s2 = s2 + a*a - b*b
                  (fdecl (.div (.sub (.var 5) (.div (.mul (.var 6) (.var 6)) (.var 3))) (.var 3)) (       -- v
                    fstore 11 (add (var 3) (var 5)) (.selLe (.var 0) (.lit 0.0) (.lit 0.0) (.var 0)))))))))))))
  req := .eq (.len 0) (.len 2)
  pre := fun _ => True
  post := fun _ _ _ => True

theorem rollingVarOk : FnOk [] rollingVar := by kvc rollingVar [rvInv]

/-! ### (b again) the same function in the surface syntax, possible since Surface.lean gained
    `sel(a <= b, t, e)` (the last re-copy; the core term above was written before). `kvc` proves it;
    the `#eval` at the end of this file checks that the emitter prints the same C for both. -/

kfn rolling_var_s(x: fslice, w: int(1, 1000000), out: inout fslice) -> int(0, 0)
  requires (len(x) == len(out))
{
  let s1: f64 = 0.0;
  let s2: f64 = 0.0;
  let m: int(0, 1000000) = sel(w <= len(x), w, len(x));
  for i upto m invariant_lean (True) {
    s1 = s1 + x[i];
    s2 = s2 + x[i] * x[i];
    let n: f64 = i + 1;
    let v: f64 = (s2 - s1 * s1 / n) / n;
    out[i] = sel(v <= 0.0, 0.0, v);
  }
  let mf: f64 = m;
  for j upto len(x) - m invariant_lean (True) {
    let a: f64 = x[j + m];
    let b: f64 = x[j];
    s1 = s1 + a - b;
    s2 = s2 + a * a - b * b;
    let v: f64 = (s2 - s1 * s1 / mf) / mf;
    out[j + m] = sel(v <= 0.0, 0.0, v);
  }
}

set_option maxRecDepth 8000 in
theorem rolling_var_sOk : FnOk [] rolling_var_s := by kvc rolling_var_s []

/-! ### rolling standard deviation in the surface syntax: the same sums, the clamp written as an `if`
    (a branch in the source; whether the machine code has one is up to the compiler), then `sqrt`.
    `if v <= 0.0 { v = 0.0 }` leaves a NaN alone, like the `selLe` above. -/

kfn rolling_std(x: fslice, w: int(1, 1000000), out: inout fslice) -> int(0, 0)
  requires (len(x) == len(out))
{
  let s1: f64 = 0.0;
  let s2: f64 = 0.0;
  let m: int(0, 1000000) = w;
  if len(x) < w { m = len(x); } else { }
  for i upto m invariant_lean (True) {
    s1 = s1 + x[i];
    s2 = s2 + x[i] * x[i];
    let v: f64 = (s2 - s1 * s1 / (i + 1)) / (i + 1);
    if v <= 0.0 { v = 0.0; } else { }
    out[i] = sqrt(v);
  }
  for j upto len(x) - m invariant_lean (True) {
    s1 = s1 + x[j + m] - x[j];
    s2 = s2 + x[j + m] * x[j + m] - x[j] * x[j];
    let v: f64 = (s2 - s1 * s1 / m) / m;
    if v <= 0.0 { v = 0.0; } else { }
    out[j + m] = sqrt(v);
  }
}

set_option maxRecDepth 8000 in
theorem rolling_stdOk : FnOk [] rolling_std := by kvc rolling_std []

/-! ## Not proved: float programs that exercise the emitter -/

-- Expressions whose value changes under contraction (fused multiply-add) or reassociation.
kfn fcontract(a: fslice, b: fslice, c: fslice, o1: inout fslice, o2: inout fslice, o3: inout fslice, o4: inout fslice)
    -> int(0, 0)
  requires (always)
{
  for i upto len(a) invariant_lean (True) {
    o1[i] = a[i] * b[i] + c[i];
    o2[i] = c[i] - a[i] * b[i];
    o3[i] = (a[i] + b[i]) + c[i];
    o4[i] = a[i] * b[i] - c[i] * c[i];
  }
}

-- Every unary operation applied directly to an input element, so that the sign of a zero is visible.
kfn funary(x: fslice, o1: inout fslice, o2: inout fslice, o3: inout fslice, o4: inout fslice) -> int(0, 0)
  requires (always)
{
  for i upto len(x) invariant_lean (True) {
    o1[i] = fabs(x[i]);
    o2[i] = -x[i];
    o3[i] = sqrt(x[i]);
    o4[i] = fabs(-x[i]) - x[i];
  }
}

/-- fconv(a: [int], o1: inout fslice, o2: inout fslice): int64 to double on the whole int64 range
    (rounding to nearest even above 2^53), alone and in a sum.  Body [res, a, o1, o2]. -/
def fconv : Fn where
  params := [(.slice (-9223372036854775808) 9223372036854775807, false), (.fslice, true), (.fslice, true)]
  rlo := 0
  rhi := 0
  body :=
    forE (.len 1) triv (                                             -- [i, res, a, o1, o2]
      seq (fstore 3 (var 0) (.ofInt (idx 2 (var 0))))
          (fstore 4 (var 0) (.add (.ofInt (idx 2 (var 0))) (.ofInt (var 0)))))
  req := .tt
  pre := tpre
  post := tpost

/-- fmix(x: fslice, k: int, s: inout f64, out: inout fslice) -> number of halvings: every float construct.
    `x` is by value and stored into (private copy).  Body [res, x, k, s, out]. -/
def fmix : Fn where
  params := [(.fslice, false), (.int (-1000) 1000, false), (.flt, true), (.fslice, true)]
  rlo := 0
  rhi := 5000
  body :=
    seq
      (forE (.len 1) triv (                                           -- [i, res, x, k, s, out]
        fdecl (.idx 2 (var 0)) (                                     -- v = x[i]   [v, i, res, x, k, s, out]
          seq (fstore 3 (var 1) (.neg (.var 0)))                     -- x[i] = -v
         (seq (fassign 5 (.add (.var 5) (.sel (lt (var 4) (var 1)) (.abs (.var 0)) (.sqrt (.var 0)))))   -- s += k < i ? |v| : sqrt(v)
         (seq (fite (.var 0) (.var 5)                                -- if v <= s
                (fassign 5 (.sub (.var 5) (.ofInt (var 4))))         --   s = s - k
                (fassign 5 (.div (.var 5) (.ofInt (add (var 1) (lit 1))))))   -- else s = s / (i + 1)
              (fstore 6 (var 1) (.selLe (.var 0) (.var 5) (.mul (.var 0) (.idx 3 (var 1))) (.neg (.abs (.var 5))))))))))
      (fdecl (.abs (.var 3)) (                                       -- t = |s|    [t, res, x, k, s, out]
        loopE (add (.len 2) (lit 1100)) triv (                        -- loop upto len(x) + 1100
          fite (.lit 1.0) (.var 0)                                   -- if 1.0 <= t (false for NaN: leave)
            (seq (fassign 0 (.mul (.var 0) (.lit 0.5))) (assign 1 (add (var 1) (lit 1))))
            brk)))
  req := .tt
  pre := tpre
  post := tpost

/-- fcall(x: fslice, y: inout fslice, z: inout f64): passes a float slice by value and `inout` and a
    float scalar `inout` to `fmix`.  Body [res, x, y, z]. -/
def fcall : Fn where
  params := [(.fslice, false), (.fslice, true), (.flt, true)]
  rlo := 0
  rhi := 5000
  body := decl (-1000) 1000 (lit 3) (Stmt.call 0 [(2, false), (0, false), (4, true), (3, true)] 1)
  req := .tt
  pre := tpre
  post := tpost

/-! ## Names and the list used by the differential test -/

def prefixSumNames : FnNames := { name := "prefix_sum", params := ["x", "out"], result := "res", locals := ["acc", "i"] }
def lowerBoundSNames : FnNames :=
  { name := "lower_bound", params := ["a", "p"], result := "res", locals := ["base", "n", "half"] }
def lowerBoundBrNames : FnNames :=
  { name := "lower_bound_branchy", params := ["a", "p"], result := "res", locals := ["lo", "hi", "mid"] }
def rollingSumNames : FnNames :=
  { name := "rolling_sum", params := ["x", "w", "out"], result := "res", locals := ["acc", "m", "i", "j"] }
def argmaxNames : FnNames := { name := "argmax", params := ["a"], result := "best", locals := ["bv", "i", "c"] }

def ewmaNames : FnNames := { name := "ewma", params := ["x", "alpha", "out"], result := "res", locals := ["prev", "i"] }
def sum8Names : FnNames :=
  { name := "sum8", params := ["x", "out"], result := "res", locals := ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "n8", "i", "j"] }
def dotNames : FnNames :=
  { name := "dot", params := ["x", "y", "out"], result := "res", locals := ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "n8", "i", "j"] }
def rollingMeanNames : FnNames := { name := "rolling_mean", params := ["x", "w", "out"], result := "res", locals := ["acc", "m", "i", "j"] }
def rollingVarNames : FnNames :=
  { name := "rolling_var", params := ["x", "w", "out"], result := "res", locals := ["s1", "s2", "m", "i", "n", "v", "mf", "j", "a", "b", "v2"] }
def rollingStdNames : FnNames :=
  { name := "rolling_std", params := ["x", "w", "out"], result := "res", locals := ["s1", "s2", "m", "i", "v", "j", "v2"] }
def fcontractNames : FnNames := { name := "fcontract", params := ["a", "b", "c", "o1", "o2", "o3", "o4"], result := "res", locals := ["i"] }
def fmixNames : FnNames := { name := "fmix", params := ["x", "k", "s", "out"], result := "res", locals := ["i", "v", "t"] }

structure Example where
  name    : String
  fns     : List Fn                     -- newest first; function 0 is the entry point
  names   : List FnNames
  elemLo  : Int := -1000000             -- test inputs: range of array elements (intersected with the type)
  elemHi  : Int := 1000000
  maxLen  : Nat := 40                   -- test inputs: slice lengths are 0..maxLen
  sameLen : Nat := 85                   -- percent of the inputs in which all slices have the same length
  proved  : String := "unproved"
  fspecial : Nat := 30                  -- test inputs: percent of float values drawn from the special set

def all : List Example := [
  { name := "prefix_sum", fns := [prefixSum], names := [prefixSumNames], elemLo := -1000000000, elemHi := 1000000000,
    proved := "FnOk proved (PrefixSum.lean)" },
  { name := "prefix_sum_10m", fns := [prefixSum10M], names := [{ prefixSumNames with name := "prefix_sum_10m" }],
    elemLo := -1000000000, elemHi := 1000000000, proved := "FnOk proved" },
  { name := "prefix_sum_w", fns := [prefixSumW], names := [{ prefixSumNames with name := "prefix_sum_w" }],
    elemLo := -1000000000, elemHi := 1000000000, proved := "FnOk proved (out: full int64)" },
  { name := "rolling_sum_w", fns := [rollingSumW], names := [{ rollingSumNames with name := "rolling_sum_w" }],
    elemLo := -1000000000, elemHi := 1000000000, proved := "FnOk proved (out: full int64)" },
  { name := "lower_bound", fns := [lowerBoundS], names := [lowerBoundSNames], elemLo := -30, elemHi := 30, proved := "FnOk proved" },
  { name := "lower_bound_wide", fns := [lowerBoundS], names := [lowerBoundSNames],
    elemLo := -9223372036854775808, elemHi := 9223372036854775807, proved := "FnOk proved" },
  { name := "lower_bound_branchy", fns := [lowerBoundBr], names := [lowerBoundBrNames], elemLo := -30, elemHi := 30, proved := "FnOk proved" },
  { name := "rolling_sum", fns := [rollingSum], names := [rollingSumNames], elemLo := -1000000000, elemHi := 1000000000,
    proved := "FnOk proved (safety; range ±2.1e16)" },
  { name := "rolling_sum_exact", fns := [rollingSumExact], names := [{ rollingSumNames with name := "rolling_sum_exact" }],
    elemLo := -1000000000, elemHi := 1000000000, proved := "FnOk proved (safety; range ±1e15)" },
  { name := "argmax", fns := [argmax], names := [argmaxNames], elemLo := -5, elemHi := 5, proved := "FnOk proved" },
  { name := "argmax_wide", fns := [argmax], names := [argmaxNames],
    elemLo := -9223372036854775808, elemHi := 9223372036854775807, proved := "FnOk proved" },
  { name := "scale_sum", fns := [scaleSum], names := [{ name := "scale_sum", params := ["a", "k"], result := "s", locals := ["i", "t"] }] },
  { name := "ps_last", fns := [psLast, prefixSum],
    names := [{ name := "ps_last", params := ["x", "out"], result := "res", locals := ["t"] }, prefixSumNames],
    elemLo := -1000000000, elemHi := 1000000000 },
  { name := "ps_arr", fns := [psArr, prefixSum],
    names := [{ name := "ps_arr", params := ["a", "out"], result := "res", locals := ["t"] }, prefixSumNames],
    elemLo := -1000000000, elemHi := 1000000000, maxLen := 10 },
  { name := "sum_slice8", fns := [sumSlice8, sumArr8],
    names := [{ name := "sum_slice8", params := ["x"], result := "s" }, { name := "sum_arr8", params := ["a"], result := "s" }], maxLen := 9 },
  { name := "for_e_probe", fns := [forEProbe], names := [{ name := "for_e_probe", params := ["n", "a"], result := "res", locals := ["m", "i"] }] },
  { name := "sel_mix", fns := [selMix], names := [{ name := "sel_mix", params := ["a", "b", "k"], result := "res" }],
    elemLo := -3, elemHi := 3 },
  { name := "len_mix", fns := [lenMix], names := [{ name := "len_mix", params := ["a", "s"], result := "res" }], maxLen := 60 },
  { name := "reverse_slice", fns := [reverseS], names := [{ name := "reverse_slice", params := ["a"], locals := ["lo", "hi", "t"] }] },
  -- the four integer functions of Surface.lean (proved there with `kvc`); `lower_bound` is a `loopE`
  { name := "s_prefix_sum", fns := [_root_.prefix_sum], names := [{ prefixSumNames with name := "s_prefix_sum" }],
    elemLo := -1000000000, elemHi := 1000000000, proved := "FnOk proved (Surface.lean)" },
  { name := "s_count_le", fns := [_root_.count_le], names := [{ name := "s_count_le", params := ["x", "p"], locals := ["cnt", "i"] }],
    elemLo := -20, elemHi := 20, proved := "FnOk proved (Surface.lean)" },
  { name := "s_max_step", fns := [_root_.max_step], names := [{ name := "s_max_step", params := ["x"], locals := ["best", "i", "d"] }],
    elemLo := -1000000000, elemHi := 1000000000, proved := "FnOk proved (Surface.lean)" },
  { name := "s_lower_bound", fns := [_root_.lower_bound], names := [{ name := "s_lower_bound", params := ["a", "p"], locals := ["lo", "hi", "mid"] }],
    elemLo := -30, elemHi := 30, proved := "FnOk proved (Surface.lean; loopE)" },
  { name := "s_argmax", fns := [_root_.argmax], names := [{ name := "s_argmax", params := ["x"], locals := ["best", "bv", "i", "v"] }],
    elemLo := -5, elemHi := 5, proved := "FnOk proved (Surface.lean; sel)" },
  { name := "s_count_prefix_le", fns := [_root_.count_prefix_le, _root_.prefix_sum],
    names := [{ name := "s_count_prefix_le", params := ["x", "tmp", "p"], locals := ["z", "cnt", "i"] }, { prefixSumNames with name := "s_prefix_sum" }],
    elemLo := -1000, elemHi := 1000, proved := "FnOk proved (Surface.lean; a call)" },
  { name := "rolling_var_s", fns := [rolling_var_s], names := [{ rollingVarNames with name := "rolling_var_s" }], proved := "FnOk proved (surface syntax)" },
  -- float kernels
  { name := "ewma", fns := [ewma], names := [ewmaNames], proved := "FnOk proved (Ewma.lean)" },
  { name := "ewma_finite", fns := [ewma], names := [ewmaNames], fspecial := 0, proved := "FnOk proved (Ewma.lean)" },
  { name := "sum8", fns := [Tenon.sum8], names := [sum8Names], proved := "FnOk proved (Sum8.lean)" },
  { name := "sum8_finite", fns := [Tenon.sum8], names := [sum8Names], fspecial := 0, proved := "FnOk proved (Sum8.lean)" },
  { name := "s_ewma", fns := [_root_.ewma_s], names := [{ ewmaNames with name := "s_ewma" }], proved := "FnOk proved (Surface.lean)" },
  { name := "s_mean_mad", fns := [_root_.mean_mad], names := [{ name := "s_mean_mad", params := ["x", "out"], locals := ["s", "i", "m", "d", "j"] }],
    proved := "FnOk proved (Surface.lean)" },
  { name := "rolling_mean", fns := [rolling_mean], names := [rollingMeanNames], proved := "FnOk proved" },
  { name := "rolling_mean_finite", fns := [rolling_mean], names := [rollingMeanNames], fspecial := 0, proved := "FnOk proved" },
  { name := "rolling_var", fns := [rollingVar], names := [rollingVarNames], proved := "FnOk proved" },
  { name := "rolling_var_finite", fns := [rollingVar], names := [rollingVarNames], fspecial := 0, proved := "FnOk proved" },
  { name := "rolling_std", fns := [rolling_std], names := [rollingStdNames], proved := "FnOk proved" },
  { name := "rolling_std_finite", fns := [rolling_std], names := [rollingStdNames], fspecial := 0, proved := "FnOk proved" },
  { name := "dot", fns := [dot], names := [dotNames], proved := "FnOk proved" },
  { name := "dot_finite", fns := [dot], names := [dotNames], fspecial := 0, proved := "FnOk proved" },
  { name := "fcontract", fns := [fcontract], names := [fcontractNames], fspecial := 5, maxLen := 24, sameLen := 100 },
  { name := "funary", fns := [funary], names := [{ name := "funary", params := ["x", "o1", "o2", "o3", "o4"], locals := ["i"] }],
    fspecial := 60, maxLen := 24, sameLen := 100 },
  { name := "fconv", fns := [fconv], names := [{ name := "fconv", params := ["a", "o1", "o2"], locals := ["i"] }],
    elemLo := -9223372036854775808, elemHi := 9223372036854775807, maxLen := 24, sameLen := 100 },
  { name := "fconv_53", fns := [fconv], names := [{ name := "fconv", params := ["a", "o1", "o2"], locals := ["i"] }],
    elemLo := 9007199254740980, elemHi := 9007199254741010, maxLen := 24, sameLen := 100 },
  { name := "fmix", fns := [fmix], names := [fmixNames] },
  { name := "fmix_finite", fns := [fmix], names := [fmixNames], fspecial := 3 },
  { name := "fcall", fns := [fcall, fmix], names := [{ name := "fcall", params := ["x", "y", "z"], locals := ["k"] }, fmixNames], fspecial := 10 }
]

theorem ewmaProgOk : ProgOk [ewma] := ⟨by simp [ewma, inI64], by simp [ewma, tysI64, condWf, ctWf], ewmaOk, trivial⟩
theorem sum8ProgOk : ProgOk [Tenon.sum8] := ⟨by simp [Tenon.sum8, inI64], by simp [Tenon.sum8, tysI64, condWf, ctWf], sum8Ok, trivial⟩
theorem rollingMeanProgOk : ProgOk [rolling_mean] :=
  ⟨by simp [rolling_mean, inI64], by simp [rolling_mean, tysI64, inI64, condWf, ctWf], rolling_meanOk, trivial⟩
theorem rollingVarProgOk : ProgOk [rollingVar] :=
  ⟨by simp [rollingVar, inI64], by simp [rollingVar, tysI64, inI64, condWf, ctWf], rollingVarOk, trivial⟩
theorem rollingStdProgOk : ProgOk [rolling_std] :=
  ⟨by simp [rolling_std, inI64], by simp [rolling_std, tysI64, inI64, condWf, ctWf], rolling_stdOk, trivial⟩
theorem rollingVarSProgOk : ProgOk [rolling_var_s] :=
  ⟨by simp [rolling_var_s, inI64], by simp [rolling_var_s, tysI64, inI64, condWf, ctWf], rolling_var_sOk, trivial⟩
theorem dotProgOk : ProgOk [dot] := ⟨by simp [dot, inI64], by simp [dot, tysI64, condWf, ctWf], dotOk, trivial⟩

theorem prefixSumWProgOk : ProgOk [prefixSumW] :=
  ⟨by simp [prefixSumW, inI64], by simp [prefixSumW, tysI64, inI64, condWf, ctWf], prefixSumWOk, trivial⟩
theorem rollingSumWProgOk : ProgOk [rollingSumW] :=
  ⟨by simp [rollingSumW, inI64], by simp [rollingSumW, tysI64, inI64, condWf, ctWf], rollingSumWOk, trivial⟩
theorem prefixSumProgOk : ProgOk [prefixSum] :=
  ⟨by simp [prefixSum, inI64], by simp [prefixSum, tysI64, inI64, condWf, ctWf], prefixSumOk, trivial⟩
theorem prefixSum10MProgOk : ProgOk [prefixSum10M] :=
  ⟨by simp [prefixSum10M, inI64], by simp [prefixSum10M, tysI64, inI64, condWf, ctWf], prefixSum10MOk, trivial⟩
theorem lowerBoundSProgOk : ProgOk [lowerBoundS] :=
  ⟨by simp [lowerBoundS, inI64], by simp [lowerBoundS, tysI64, inI64, condWf, ctWf], lowerBoundSOk, trivial⟩
theorem lowerBoundBrProgOk : ProgOk [lowerBoundBr] :=
  ⟨by simp [lowerBoundBr, inI64], by simp [lowerBoundBr, tysI64, inI64, condWf, ctWf], lowerBoundBrOk, trivial⟩
theorem rollingSumProgOk : ProgOk [rollingSum] :=
  ⟨by simp [rollingSum, inI64], by simp [rollingSum, tysI64, inI64, condWf, ctWf], rollingSumOk, trivial⟩
theorem rollingSumExactProgOk : ProgOk [rollingSumExact] :=
  ⟨by simp [rollingSumExact, inI64], by simp [rollingSumExact, tysI64, inI64, condWf, ctWf], rollingSumExactOk, trivial⟩
theorem argmaxProgOk : ProgOk [argmax] :=
  ⟨by simp [argmax, inI64], by simp [argmax, tysI64, inI64, condWf, ctWf], argmaxOk, trivial⟩

end Tenon.Examples

#print axioms Tenon.Examples.ewmaProgOk
#print axioms Tenon.Examples.sum8ProgOk
#print axioms Tenon.Examples.rollingMeanProgOk
#print axioms Tenon.Examples.rollingVarProgOk
#print axioms Tenon.Examples.rollingStdProgOk
#print axioms Tenon.Examples.dotProgOk
#print axioms Tenon.Examples.rollingVarSProgOk
#print axioms Tenon.Examples.prefixSumWProgOk
#print axioms Tenon.Examples.rollingSumWProgOk
#print axioms Tenon.Examples.prefixSumProgOk
#print axioms Tenon.Examples.prefixSum10MProgOk
#print axioms Tenon.Examples.lowerBoundSProgOk
#print axioms Tenon.Examples.lowerBoundBrProgOk
#print axioms Tenon.Examples.rollingSumProgOk
#print axioms Tenon.Examples.rollingSumExactProgOk
#print axioms Tenon.Examples.argmaxProgOk

open Tenon Tenon.Examples in
#eval evalFn [lowerBoundS] 0 [.arr [1, 3, 5, 7, 9], .int 6]
open Tenon Tenon.Examples in
#eval evalFn [lowerBoundS] 0 [.arr [], .int 6]
open Tenon Tenon.Examples in
#eval evalFn [rollingSum] 0 [.arr [1, 2, 3, 4, 5, 6], .int 3, .arr [0, 0, 0, 0, 0, 0]]
open Tenon Tenon.Examples in
#eval evalFn [rollingSum] 0 [.arr [1, 2, 3], .int 5, .arr [0, 0, 0]]
open Tenon Tenon.Examples in
#eval evalFn [rollingSum] 0 [.arr [1, 2, 3], .int 5, .arr [0, 0]]          -- lengths differ: stuck
open Tenon Tenon.Examples in
#eval evalFn [Tenon.Examples.argmax] 0 [.arr [3, 9, 2, 9, 1]]
open Tenon Tenon.Examples in
#eval evalFn [Tenon.Examples.argmax] 0 [.arr []]
open Tenon Tenon.Examples in
#eval evalFn [reverseS] 0 [.arr [1, 2, 3, 4, 5]]
open Tenon Tenon.Examples in
#eval evalFn [forEProbe] 0 [.int 6, .arr [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

open Tenon Tenon.Examples in
#eval evalFn [rolling_mean] 0 [.farr [1.0, 2.0, 3.0, 4.0, 5.0, 6.0], .int 3, .farr [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]]
open Tenon Tenon.Examples in
#eval evalFn [rollingVar] 0 [.farr [1.0, 2.0, 3.0, 4.0, 5.0, 6.0], .int 3, .farr [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]]
open Tenon Tenon.Examples in
#eval evalFn [rolling_std] 0 [.farr [1.0, 2.0, 3.0, 4.0, 5.0, 6.0], .int 3, .farr [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]]
open Tenon Tenon.Examples in
#eval evalFn [dot] 0 [.farr [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0], .farr [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 2.0, 0.5], .farr [0.0]]
open Tenon Tenon.Examples in
#eval evalFn [fmix] 0 [.farr [1.0, -2.0, 3.0e300, 4.0], .int 1, .flt 0.5, .farr [0.0, 0.0, 0.0, 0.0]]
open Tenon Tenon.Examples in
#eval evalFn [fcall, fmix] 0 [.farr [1.0, -2.0, 9.0], .farr [0.0, 0.0, 0.0], .flt 2.0]

-- The surface-syntax rolling variance and the core-term one: the same C?
#eval show IO Unit from do
  let c1 := Tenon.Emit.emitProgram { prelude := false } [Tenon.Examples.rollingVar] [Tenon.Examples.rollingVarNames]
  let c2 := Tenon.Emit.emitProgram { prelude := false } [Tenon.Examples.rolling_var_s] [Tenon.Examples.rollingVarNames]
  match c1, c2 with
  | .ok a, .ok b => IO.println s!"rolling_var: core term and surface syntax emit identical C: {a == b}"
  | _, _ => IO.println "rolling_var: emit error"

-- Emitted C for every example (shown at build time).
#eval show IO Unit from do
  for ex in Tenon.Examples.all do
    match Tenon.Emit.emitProgram {} ex.fns ex.names with
    | .ok c => IO.println s!"/* ---- {ex.name}: {ex.proved} ---- */\n{c}"
    | .error e => IO.println s!"/* ---- {ex.name}: ERROR {e} */"
