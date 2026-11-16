import Surface
/-! Functions written in the surface syntax, each proved by `kvc`. -/

/-! ## The running sum, written in the surface syntax -/

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
  for i upto len(x) invariant (0 <= cnt && cnt <= i) {
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
    for i upto len(x) - 1 invariant (0 <= best) {
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
  loop upto len(a) + 1 invariant (lo <= hi && hi <= len(a) && hi - lo <= len(a) - iter_) {
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
  for i upto len(x) invariant (always) {
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
  for i upto len(x) invariant (always) {
    s = s + x[i];
  }
  let m: f64 = s / len(x);
  let d: f64 = 0.0;
  for j upto len(x) invariant (always) {
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
  for i upto len(x) invariant (0 <= best && best <= i && best < len(x)) {
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
  for i upto len(tmp) invariant (0 <= cnt && cnt <= i) {
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
  for i upto len(tmp) invariant (0 <= cnt && cnt <= i) {
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
