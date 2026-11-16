import Tenon
import Emit
import Legacy
import Examples
/-! Differential test driver: generates Tenon programs and inputs, evaluates them with the reference
    semantics `evalFn`, and writes (1) a C file containing the emitted functions and a `main` that calls
    them on exactly the inputs where `evalFn` is `some`, and (2) the expected results: the result and
    the final values of the parameters (inout: from `evalFn`; by-value arrays: the input, because the
    C caller's array must be unchanged).
    `run.sh` compiles the C file with several compilers and `compare.py` compares.

      difftest suite  <outdir> <seed> <ninputs> [sabotage]            hand-written programs (Examples.lean)
      difftest random <outdir> <seed> <nprogs> <ninputs> [sabotage]   random programs
      difftest show   <seed> <index>                                  print random program <index> of <seed>
      difftest case   <seed> <index> <ninputs> <case>                 print one input and evalFn's answer -/

open Tenon Tenon.Emit Tenon.Examples

/-! ## Random numbers (splitmix64) -/

abbrev G := StateM UInt64

def nextU64 : G UInt64 := do
  let s ← get
  let s := s + 0x9E3779B97F4A7C15
  set s
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  pure (z ^^^ (z >>> 31))

/-- Uniform in 0..n-1 (0 when n = 0). The modulo bias is irrelevant here. -/
def rnd (n : Nat) : G Nat := do
  if n == 0 then pure 0 else
  let a ← nextU64
  let b ← nextU64
  pure ((a.toNat * 18446744073709551616 + b.toNat) % n)

def rndInt (lo hi : Int) : G Int := do
  if hi ≤ lo then pure lo else
  let k ← rnd (hi - lo + 1).toNat
  pure (lo + k)

def chance (num den : Nat) : G Bool := do pure ((← rnd den) < num)

def pick {α} (dflt : α) (l : List α) : G α := do
  let k ← rnd l.length
  pure (l.getD k dflt)

/-- A value in lo..=hi, biased towards the ends and towards small magnitudes. -/
def rndBiased (lo hi : Int) : G Int := do
  match ← rnd 10 with
  | 0 => pure lo
  | 1 => pure hi
  | 2 => rndInt (max lo (hi - 3)) hi
  | 3 => rndInt lo (min hi (lo + 3))
  | 4 | 5 => rndInt (max lo (-8)) (max (max lo (-8)) (min hi 8))
  | _ => rndInt lo hi

/-! ## Generator of well-formed programs

Every integer variable has a type (a range) for its whole life; the generator keeps an interval for
every expression and only builds arithmetic whose interval fits int64, indexes whose interval is
inside the array, and assignments whose value is inside the variable's range (clamping with `ite` when
needed). All arrays of one program have the element range −E..=E. Calls go through fresh locals that
have exactly the callee's parameter and result ranges. Break-only loops get a private counter or a
halving variable that the body cannot change. So `evalFn` is `some` for inputs within the parameter
types, by construction, unless the program is "risky" (drops these precautions at random places) or
contains a deliberately non-exclusive call. `evalFn` remains the only judge of which inputs count. -/

inductive GS where
  | int (lo hi : Int) (ro : Bool) (sidx : Bool := false)
      -- ro: the generator never changes this variable
      -- sidx: a valid index into the slices of the program, if they all have the same length
  | arr (alen : Nat)
  | slice
  | flt (ro : Bool)
  | fslice

/-- Slice lengths in the test inputs are at most this; the generator uses it as the interval of `len`. -/
def maxSliceLen : Nat := 24

structure Cfg where
  E       : Int                              -- array elements are within -E..=E
  risky   : Bool
  callees : List (List (Ty × Bool) × Int × Int)   -- parameters and result range of the later functions
  lens    : List Nat                         -- array lengths used in this program
  floats  : Bool := false                    -- the program uses floats

def fits (lo hi : Int) : Bool := decide (i64Min ≤ lo) && decide (hi ≤ i64Max)

def intVars (env : List GS) : List (Nat × Int × Int) :=
  (env.zipIdx).filterMap fun (s, i) => match s with | .int lo hi _ _ => some (i, lo, hi) | _ => none

/-- Integer variables the generator may change. -/
def wrVars (env : List GS) : List (Nat × Int × Int) :=
  (env.zipIdx).filterMap fun (s, i) => match s with | .int lo hi false _ => some (i, lo, hi) | _ => none

def slVars (env : List GS) : List Nat :=
  (env.zipIdx).filterMap fun (s, i) => match s with | .slice => some i | _ => none

/-- Variables known to be valid slice indexes. -/
def sidxVars (env : List GS) : List Nat :=
  (env.zipIdx).filterMap fun (s, i) => match s with | .int _ _ _ true => some i | _ => none

def fltVars (env : List GS) : List Nat :=
  (env.zipIdx).filterMap fun (s, i) => match s with | .flt _ => some i | _ => none

/-- Float variables the generator may change. -/
def fwrVars (env : List GS) : List Nat :=
  (env.zipIdx).filterMap fun (s, i) => match s with | .flt false => some i | _ => none

def fslVars (env : List GS) : List Nat :=
  (env.zipIdx).filterMap fun (s, i) => match s with | .fslice => some i | _ => none

def arrVars (env : List GS) : List (Nat × Nat) :=
  (env.zipIdx).filterMap fun (s, i) => match s with | .arr n => some (i, n) | _ => none

def genLit : G Int := do
  match ← rnd 12 with
  | 0 => rndInt (-1099511627776) 1099511627776
  | 1 => rndInt (-4611686018427387904) 4611686018427387904
  | 2 | 3 => rndInt (-1000) 1000
  | _ => rndInt (-3) 9

def genLeaf (env : List GS) : G (Expr × Int × Int) := do
  let vs := intVars env
  if vs.isEmpty || (← chance 1 4) then
    let n ← genLit
    pure (.lit n, n, n)
  else
    let (i, lo, hi) ← pick (0, 0, 0) vs
    pure (.var i, lo, hi)

/-- Should a precaution be dropped here? Only in risky programs. -/
def careless (cfg : Cfg) : G Bool := do
  if cfg.risky then chance 1 30 else pure false

/-- An index expression for an array of length `len > 0`. -/
def genIndex (cfg : Cfg) (env : List GS) (alen : Nat) (cand : Expr × Int × Int) : G Expr := do
  let (e, lo, hi) := cand
  if (0 ≤ lo && hi < alen) || (← careless cfg) then pure e
  else
    let ok := (intVars env).filter fun (_, lo, hi) => 0 ≤ lo && hi < alen
    if !ok.isEmpty && (← chance 3 4) then
      let (i, _, _) ← pick (0, 0, 0) ok
      pure (.var i)
    else
      pure (.lit (← rnd alen))

def genExpr (cfg : Cfg) (env : List GS) : Nat → G (Expr × Int × Int)
  | 0 => genLeaf env
  | fuel + 1 => do
    let a ← genExpr cfg env fuel
    let b ← genExpr cfg env fuel
    let (ea, alo, ahi) := a
    let (eb, blo, bhi) := b
    let c ← careless cfg
    match ← rnd 19 with
    | 11 =>
      -- alen of an array, of a slice or of a float slice
      let cands : List (Nat × Int × Int) := (arrVars env).map (fun (i, n) => (i, (n : Int), (n : Int))) ++
        ((slVars env) ++ (fslVars env)).map (fun i => (i, (0 : Int), (maxSliceLen : Int)))
      if cands.isEmpty then pure a else
      let (i, lo, hi) ← pick (0, 0, 0) cands
      pure (.len i, lo, hi)
    | 12 => pure (.le ea eb, 0, 1)
    | 13 => pure (.lt ea eb, 0, 1)
    | 14 => pure (.eq ea eb, 0, 1)
    | 15 | 16 | 17 =>
      -- sel: the condition is a comparison, or any expression (tested against 0)
      let c ← genExpr cfg env fuel
      let (ec, _, _) := c
      let cond ← match ← rnd 5 with
        | 0 => pure (Expr.le ec ea)
        | 1 => pure (Expr.lt ec eb)
        | 2 => pure (Expr.eq ec ea)
        | _ => pure ec
      pure (.sel cond ea eb, min alo blo, max ahi bhi)
    | 18 =>
      -- a slice element at a variable known to be a valid index
      let sl := slVars env
      let ix := sidxVars env
      if sl.isEmpty then pure b
      else if ix.isEmpty then
        if c then pure (.idx (← pick 0 sl) ea, -cfg.E, cfg.E) else pure b
      else pure (.idx (← pick 0 sl) (.var (← pick 0 ix)), -cfg.E, cfg.E)
    | 0 | 1 => genLeaf env
    | 2 | 3 | 4 =>
      if fits (alo + blo) (ahi + bhi) || c then pure (.add ea eb, alo + blo, ahi + bhi) else pure a
    | 5 | 6 =>
      if fits (alo - bhi) (ahi - blo) || c then pure (.sub ea eb, alo - bhi, ahi - blo) else pure a
    | 7 =>
      let ps := [alo * blo, alo * bhi, ahi * blo, ahi * bhi]
      let lo := ps.foldl min (alo * blo)
      let hi := ps.foldl max (alo * blo)
      if fits lo hi || c then pure (.mul ea eb, lo, hi) else pure b
    | 8 =>
      -- make the dividend non-negative by shifting it, and the divisor positive
      let (ea, alo, ahi) :=
        if alo < 0 && fits 0 (ahi - alo) then (Expr.sub ea (.lit alo), (0 : Int), ahi - alo) else (ea, alo, ahi)
      let k ← rndInt 1 9
      let (eb, blo, bhi) := if blo > 0 then (eb, blo, bhi) else (Expr.lit k, k, k)
      if alo ≥ 0 || c then pure (.div ea eb, alo / bhi, ahi / blo) else pure (ea, alo, ahi)
    | _ =>
      let arrs := (arrVars env).filter fun (_, n) => n > 0
      if arrs.isEmpty then pure a else
      let (ai, alen) ← pick (0, 1) arrs
      let ie ← genIndex cfg env alen a
      pure (.idx ai ie, -cfg.E, cfg.E)

/-- `x = e` where x has range xlo..=xhi; clamps with `ite` when the interval of `e` is not inside. -/
def clampAssign (cfg : Cfg) (x : Nat) (xlo xhi : Int) (cand : Expr × Int × Int) : G Stmt := do
  let (e, elo, ehi) := cand
  if (xlo ≤ elo && ehi ≤ xhi) || (← careless cfg) then pure (.assign x e)
  else if elo == ehi then pure (.assign x (.lit (← rndBiased xlo xhi)))   -- a constant out of range
  else pure (.ite e (.lit xhi)
          (.ite (.lit xlo) e (.assign x e) (.assign x (.lit xlo)))
          (.assign x (.lit xhi)))

def clampStore (cfg : Cfg) (a : Nat) (ie : Expr) (cand : Expr × Int × Int) : G Stmt := do
  let (e, elo, ehi) := cand
  if (-cfg.E ≤ elo && ehi ≤ cfg.E) || (← careless cfg) then pure (.store a ie e)
  else pure (.ite e (.lit cfg.E)
          (.ite (.lit (-cfg.E)) e (.store a ie e) (.store a ie (.lit (-cfg.E))))
          (.store a ie (.lit cfg.E)))

def genRange : G (Int × Int) := do
  match ← rnd 10 with
  | 0 => let c ← rndInt (-5) 5; pure (c, c)
  | 1 | 2 => let k ← rndInt 1 12; pure (0, k)
  | 3 | 4 => let k ← rndInt 1 100; pure (-k, k)
  | 5 | 6 => pure (-1000000, 1000000)
  | 7 => pure (-1099511627776, 1099511627776)
  | 8 => pure (-4611686018427387904, 4611686018427387904)
  | _ => if ← chance 1 3 then pure (i64Min, i64Max) else pure (0, 1000)

/-! ### Floats: values and expressions -/

/-- Bit patterns that every float test must meet: NaNs (quiet and signalling, both signs, payloads),
    infinities, zeros, subnormals, the extremes, and values around 1 and 2^53 that expose rounding. -/
def specialBits : List UInt64 := [
  0x7ff8000000000000, 0xfff8000000000000, 0x7ff8000000000001, 0x7ff0000000000001, 0xfff4000000000000,   -- NaN
  0x7ff0000000000000, 0xfff0000000000000,                                                               -- ±inf
  0x0000000000000000, 0x8000000000000000,                                                               -- ±0
  0x0000000000000001, 0x8000000000000001, 0x000fffffffffffff, 0x0008000000000000, 0x800abcdef0123456,   -- subnormal
  0x0010000000000000, 0x8010000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,                       -- DBL_MIN, DBL_MAX
  0x3ff0000000000000, 0xbff0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff,                       -- ±1, 1+ulp, 1-ulp/2
  0x4340000000000000, 0x4340000000000001, 0x433fffffffffffff,                                           -- 2^53, 2^53+2, 2^53-1
  0x3fb999999999999a, 0x3fd5555555555555, 0x3fe0000000000000, 0x4008000000000000,                       -- 0.1, 1/3, 0.5, 3
  0x7fe1ccf385ebc8a0, 0x000730d67819e8d2, 0x4341c37937e08000, 0xc341c37937e08000]                       -- 1e308, 1e-308, ±1e16

/-- A double as bits. `special`: percent drawn from `specialBits`. The rest: mostly moderate magnitudes
    with random mantissas (where rounding of sums and products matters), some small integers and
    halves, some wide exponents, some arbitrary bit patterns. -/
def genFBits (special : Nat) : G UInt64 := do
  if (← rnd 100) < special then pick 0 specialBits else
  let mant ← rnd 4503599627370496
  let sign : Nat := if ← chance 1 2 then 9223372036854775808 else 0
  match ← rnd 10 with
  | 0 | 1 => pure (Float.ofInt (← rndInt (-6) 6) * (if ← chance 1 3 then 0.5 else 1.0)).toBits
  | 2 => pure (UInt64.ofNat (sign + (1023 - 300 + (← rnd 600)) * 4503599627370496 + mant))
  | 3 => nextU64
  | _ => pure (UInt64.ofNat (sign + (1020 + (← rnd 7)) * 4503599627370496 + mant))

def genFLeaf (env : List GS) : G FExpr := do
  let vs := fltVars env
  let sl := fslVars env
  let ix := sidxVars env
  match ← rnd 6 with
  | 0 => pure (.lit (Float.ofBits (← genFBits 25)))
  | 1 | 2 =>
    if sl.isEmpty || ix.isEmpty then
      if vs.isEmpty then pure (.lit (Float.ofBits (← genFBits 25))) else pure (.var (← pick 0 vs))
    else pure (.idx (← pick 0 sl) (.var (← pick 0 ix)))
  | _ => if vs.isEmpty then pure (.lit (Float.ofBits (← genFBits 25))) else pure (.var (← pick 0 vs))

/-- A float expression. Float operations are never stuck, so no intervals are needed; the integer
    sub-expressions (conditions, `ofInt`) come from `genExpr`, indices are variables known to be valid. -/
def genFExpr (cfg : Cfg) (env : List GS) : Nat → G FExpr
  | 0 => genFLeaf env
  | fuel + 1 => do
    let a ← genFExpr cfg env fuel
    let b ← genFExpr cfg env fuel
    match ← rnd 20 with
    | 0 | 1 => genFLeaf env
    | 2 | 3 => pure (.add a b)
    | 4 | 5 => pure (.sub a b)
    | 6 | 7 => pure (.mul a b)
    | 8 => pure (.div a b)
    | 9 | 10 =>
      -- shapes that a contracting compiler turns into a fused multiply-add
      let c ← genFLeaf env
      match ← rnd 3 with
      | 0 => pure (.add (.mul a b) c)
      | 1 => pure (.add c (.mul a b))
      | _ => pure (.sub (.mul a b) c)
    | 11 => let c ← genFLeaf env; pure (.add (.add a b) c)       -- a reassociating compiler changes this
    | 12 => let (e, _, _) ← genExpr cfg env 1; pure (.ofInt e)
    | 13 | 14 =>
      let (ec, _, _) ← genExpr cfg env 1
      let (ed, _, _) ← genExpr cfg env 0
      let cond ← match ← rnd 4 with
        | 0 => pure (Expr.le ec ed)
        | 1 => pure (Expr.lt ec ed)
        | 2 => pure (Expr.eq ec ed)
        | _ => pure ec
      pure (.sel cond a b)
    | 15 | 16 =>
      let c ← genFExpr cfg env fuel
      let d ← genFLeaf env
      -- often compare a value with itself or with a leaf, so that equality and NaN cases occur
      match ← rnd 4 with
      | 0 => pure (.selLe a a c d)
      | 1 => pure (.selLe a d a d)
      | _ => pure (.selLe a b c d)
    | 17 => let l ← genFLeaf env; pure (.neg (if ← chance 1 2 then l else a))
    | 18 => let l ← genFLeaf env; pure (.abs (if ← chance 1 2 then l else a))
    | _ => pure (.sqrt (if ← chance 1 2 then .abs a else a))

def genAssign (cfg : Cfg) (env : List GS) (fuel : Nat) : G Stmt := do
  let vs := wrVars env
  if vs.isEmpty then pure .skip else
  let (x, lo, hi) ← pick (0, 0, 0) vs
  clampAssign cfg x lo hi (← genExpr cfg env fuel)

/-- Clamp an integer expression into lo..=hi (hi ≥ lo) with two `sel`s. -/
def clampSel (e : Expr) (lo hi : Expr) : Expr :=
  .sel (.le e hi) (.sel (.le lo e) e lo) hi

def genFAssign (cfg : Cfg) (env : List GS) (fuel : Nat) : G Stmt := do
  let vs := fwrVars env
  if vs.isEmpty then genAssign cfg env fuel else
  pure (.fassign (← pick 0 vs) (← genFExpr cfg env fuel))

def genFStore (cfg : Cfg) (env : List GS) (fuel : Nat) : G Stmt := do
  let sl := fslVars env
  if sl.isEmpty then genFAssign cfg env fuel else
  let a ← pick 0 sl
  let ix := sidxVars env
  let v ← genFExpr cfg env fuel
  if !ix.isEmpty && (← chance 2 3) then pure (.fstore a (.var (← pick 0 ix)) v)
  else
    -- if 1 ≤ len(a) { a[clamp(e, 0, len(a) - 1)] = v }
    let (e, _, _) ← genExpr cfg env (min fuel 1)
    let st := Stmt.fstore a (clampSel e (.lit 0) (.sub (.len a) (.lit 1))) v
    if ← careless cfg then pure st else pure (.ite (.lit 1) (.len a) st .skip)

def genStore (cfg : Cfg) (env : List GS) (fuel : Nat) : G Stmt := do
  let sl := slVars env
  if !sl.isEmpty && (← chance 1 2) then
    let a ← pick 0 sl
    let ix := sidxVars env
    let v ← genExpr cfg env fuel
    if !ix.isEmpty && (← chance 2 3) then
      return (← clampStore cfg a (.var (← pick 0 ix)) v)
    else
      -- if 1 ≤ len(a) { a[clamp(e, 0, len(a) - 1)] = v }
      let (e, _, _) ← genExpr cfg env (min fuel 1)
      let st ← clampStore cfg a (clampSel e (.lit 0) (.sub (.len a) (.lit 1))) v
      if ← careless cfg then return st
      return .ite (.lit 1) (.len a) st .skip
  let arrs := (arrVars env).filter fun (_, n) => n > 0
  if arrs.isEmpty then genAssign cfg env fuel else
  let (a, alen) ← pick (0, 1) arrs
  let ie ← genIndex cfg env alen (← genExpr cfg env (min fuel 1))
  clampStore cfg a ie (← genExpr cfg env fuel)

/-- A call statement:
    `{ let t; let p0; ..; p0 = e0; ..; t = f(args); y = p_inout; ..; x = t }`
    t has exactly the callee's result range and every integer parameter gets a fresh local of exactly
    its range (so the write-back of an inout integer keeps the caller's types). An inout integer
    parameter sometimes takes an existing variable of the same range instead; array arguments are
    existing arrays of the right length, an inout array never repeated (unless `violate`).
    About one call in 10 that has an inout argument is made non-exclusive on purpose. -/
def genCallStmt (cfg : Cfg) (env : List GS) (fuel : Nat) : G Stmt := do
  let ws := wrVars env
  if cfg.callees.isEmpty || ws.isEmpty then genAssign cfg env fuel else
  let j ← rnd cfg.callees.length
  let (ps, rlo, rhi) := cfg.callees.getD j ([], 0, 0)
  let intPs := ps.filterMap fun p => match p with | (Ty.int lo hi, io) => some (lo, hi, io) | _ => none
  let m := intPs.length
  -- inner environment: [p_{m-1}, .., p_0, t] ++ env      (p_q at position m-1-q, t at position m)
  let sh := m + 1
  let inner : List GS := (intPs.reverse.map fun (lo, hi, _) => GS.int lo hi false) ++ [GS.int rlo rhi false] ++ env
  let mut args : List (Nat × Bool) := []
  let mut usedInout : List Nat := []       -- variables passed inout
  let mut usedAny : List Nat := []         -- variables passed at all
  let mut q := 0
  let mut outsInt : List Nat := []         -- positions of inout integer arguments (inner numbering)
  for p in ps do
    match p with
    | (.int lo hi, io) =>
      let mut pos := m - 1 - q
      if io && (← chance 1 3) then
        -- an existing variable with exactly this range, not used otherwise
        let cands := ws.filter fun (i, l, h) => l == lo && h == hi && !usedAny.contains (i + sh)
        if !cands.isEmpty then
          let (i, _, _) ← pick (0, 0, 0) cands
          pos := i + sh
      args := args ++ [(pos, io)]
      usedAny := pos :: usedAny
      if io then usedInout := pos :: usedInout; outsInt := outsInt ++ [pos]
      q := q + 1
    | (.arr n _ _, io) =>
      let cands := (arrVars inner).filter fun (i, k) =>
        k == n && !usedInout.contains i && (!io || !usedAny.contains i)
      -- sometimes a slice where an array is expected (by value): stuck unless the lengths agree
      let slc := (slVars inner).filter fun i => !usedInout.contains i
      let cands := if cands.isEmpty && !io && (n : Nat) ≤ maxSliceLen then slc.map (fun i => (i, n)) else cands
      if cands.isEmpty then return (← genAssign cfg env fuel)
      let (i, _) ← pick (0, 0) cands
      args := args ++ [(i, io)]
      usedAny := i :: usedAny
      if io then usedInout := i :: usedInout
    | (.flt, io) =>
      -- an existing float variable (an inout one must be writable and not passed otherwise)
      let cands := (if io then fwrVars inner else fltVars inner).filter fun i =>
        !usedInout.contains i && (!io || !usedAny.contains i)
      if cands.isEmpty then return (← genAssign cfg env fuel)
      let i ← pick 0 cands
      args := args ++ [(i, io)]
      usedAny := i :: usedAny
      if io then usedInout := i :: usedInout
    | (.fslice, io) =>
      let cands := (fslVars inner).filter fun i => !usedInout.contains i && (!io || !usedAny.contains i)
      if cands.isEmpty then return (← genAssign cfg env fuel)
      let i ← pick 0 cands
      args := args ++ [(i, io)]
      usedAny := i :: usedAny
      if io then usedInout := i :: usedInout
    | (.slice _ _, io) =>
      -- a slice of the caller; by value also an array (its length becomes the slice length)
      let free := fun (i : Nat) => !usedInout.contains i && (!io || !usedAny.contains i)
      let sls := (slVars inner).filter free
      let ars := if io then [] else ((arrVars inner).map (·.1)).filter free
      let cands ← if !sls.isEmpty && (ars.isEmpty || (← chance 3 4)) then pure sls else pure ars
      if cands.isEmpty then return (← genAssign cfg env fuel)
      let i ← pick 0 cands
      args := args ++ [(i, io)]
      usedAny := i :: usedAny
      if io then usedInout := i :: usedInout
  let mut dst := m
  let (x, xlo, xhi) ← pick (0, 0, 0) ws
  -- sometimes the destination is an existing variable whose range contains the result range
  if xlo ≤ rlo && rhi ≤ xhi && !usedInout.contains (x + sh) && (← chance 1 4) then dst := x + sh
  -- deliberate violation of `exclusive`
  if !usedInout.isEmpty && (← chance 1 10) then
    let v ← pick 0 usedInout
    let isInt := match inner[v]? with | some (.int ..) => true | _ => false
    let others := (args.zipIdx).filter fun ((i, _), _) => i != v &&
      (match inner[i]?, inner[v]? with
       | some (.int ..), some (.int ..) => true
       | some (.arr a), some (.arr b) => a == b
       | some .slice, some .slice => true
       | some (.flt _), some (.flt _) => true
       | some .fslice, some .fslice => true
       | _, _ => false)
    if isInt && (others.isEmpty || (← chance 1 2)) then dst := v
    else if !others.isEmpty then
      let (_, k) ← pick ((0, false), 0) others
      args := (args.zipIdx).map fun ((i, io), k') => if k' == k then (v, io) else (i, io)
  let mut body : Stmt ← if dst == m then clampAssign cfg (x + sh) xlo xhi (.var m, rlo, rhi) else pure .skip
  -- use the values that came back through inout integers
  for pos in outsInt do
    match inner[pos]? with
    | some (.int lo hi _ _) =>
      let (y, ylo, yhi) ← pick (0, 0, 0) ws
      body := .seq (← clampAssign cfg (y + sh) ylo yhi (.var pos, lo, hi)) body
    | _ => pure ()
  body := .seq (.call j args dst) body
  for ((lo, hi, _), q2) in intPs.zipIdx.reverse do
    let st ← clampAssign cfg (m - 1 - q2) lo hi (← genExpr cfg inner fuel)
    body := .seq st body
  -- wrap in the declarations, t outermost, then the parameters in order; initial values are in range
  for (lo, hi, _) in intPs.reverse do
    let v ← rndBiased lo hi
    body := .decl lo hi (.lit v) body
  let v ← rndBiased rlo rhi
  pure (.decl rlo rhi (.lit v) body)

def genStmt (cfg : Cfg) : Nat → List GS → (inLoop : Bool) → (loopDepth : Nat) → G Stmt
  | 0, env, inLoop, _ => do
    match ← rnd (if cfg.floats then 12 else 8) with
    | 8 | 9 | 10 => genFAssign cfg env 1
    | 11 => genFStore cfg env 1
    | 0 | 1 | 2 | 3 => genAssign cfg env 1
    | 4 | 5 => genStore cfg env 1
    | 6 => if inLoop then pure .brk else pure .skip
    | _ => genCallStmt cfg env 1
  | fuel + 1, env, inLoop, depth => do
    match ← rnd (if cfg.floats then 42 else 31) with
    | 31 | 32 | 33 => genFAssign cfg env 2
    | 34 | 35 => genFStore cfg env 2
    | 36 | 37 =>
      -- { let f: f64 = e; s; s2 }
      let e ← genFExpr cfg env 2
      let s ← genStmt cfg fuel (.flt false :: env) inLoop depth
      let s2 ← genStmt cfg fuel (.flt false :: env) inLoop depth
      pure (.fdecl e (.seq s s2))
    | 38 | 39 | 40 =>
      -- if a <= b on floats (the else branch when either is NaN)
      let a ← genFExpr cfg env 1
      let b ← if ← chance 1 5 then pure a else genFExpr cfg env 1
      let s ← genStmt cfg fuel env inLoop depth
      let t ← if ← chance 1 3 then pure Stmt.skip else genStmt cfg fuel env inLoop depth
      if ← chance 1 4 then pure (.fite a b t s) else pure (.fite a b s t)
    | 41 =>
      -- { let t = |e|; loop upto 1100 { if 1.0 <= t { t = t * 0.5; body } else break } }
      -- leaves by `brk` for every finite t and for NaN; an infinite t exhausts the bnd (stuck)
      if depth ≥ 2 then genFAssign cfg env 2 else
      let e ← genFExpr cfg env 1
      let s ← genAssign cfg (.flt true :: env) 1
      pure (.fdecl (.abs e) (.loopE (.lit 1100) triv
        (.fite (.lit 1.0) (.var 0) (.seq (.fassign 0 (.mul (.var 0) (.lit 0.5))) s) .brk)))
    | 29 | 30 =>
      -- loopE: { let c = 0; loop upto BOUND { if K ≤ c break; body; c = c + 1 } }, the body cannot
      -- change c. BOUND is an expression that is evaluated only by Tenon (the C never computes it):
      -- a literal, or len(a) + K + 1, or K + 1 + (some expression clamped to 0..3)
      if depth ≥ 2 then genAssign cfg env 2 else
      let k : Int := (← rnd 9)
      let benv := GS.int 0 k true :: env
      let s ← genStmt cfg fuel benv true (depth + 1)
      let s2 ← genStmt cfg fuel benv true (depth + 1)
      let lens := (arrVars benv).map (·.1) ++ slVars benv ++ fslVars benv
      let (e, _, _) ← genExpr cfg benv 1
      let bnd : Expr ← match ← rnd 4 with
        | 0 => pure (Expr.lit (k + 1))
        | 1 => if lens.isEmpty then pure (Expr.lit (k + 1)) else pure (Expr.add (.len (← pick 0 lens)) (.lit (k + 1)))
        | 2 => pure (Expr.add (.lit (k + 1)) (clampSel e (.lit 0) (.lit 3)))
        | _ => pure (Expr.mul (.lit 2) (.lit (k + 1)))
      -- risky: a bnd that is one too small, a bnd whose evaluation is stuck (Tenon is stuck although
      -- the C would run), or a negative bnd
      let bnd ← if cfg.risky && (← chance 1 5) then
          pick (Expr.lit k) [Expr.lit k, Expr.div (.lit 100) (.lit 0), Expr.lit (-1),
                             Expr.add (.lit 9223372036854775807) (.lit (k + 1))]
        else pure bnd
      pure (.decl 0 k (.lit 0) (.loopE bnd triv
        (.seq (.ite (.lit k) (.var 0) .brk .skip) (.seq (.seq s s2) (.assign 0 (.add (.var 0) (.lit 1)))))))
    | 21 | 22 | 23 =>
      -- for i in 0..len(a): the counter is a valid index (the generator does not change it)
      if depth ≥ 2 then genAssign cfg env 2 else
      let cands : List (Nat × Bool × Nat) := (slVars env).map (fun i => (i, true, maxSliceLen)) ++
        (arrVars env).map (fun (i, n) => (i, false, n))
      if cands.isEmpty then genAssign cfg env 2 else
      let (a, isSl, n) ← pick (0, false, 0) cands
      let ro ← chance 3 4
      let benv := GS.int 0 ((n : Int) - 1) ro (isSl && ro) :: env
      let s ← genStmt cfg fuel benv true (depth + 1)
      let s2 ← genStmt cfg fuel benv true (depth + 1)
      pure (.forE (.len a) triv (.seq s s2))
    | 24 | 25 =>
      -- for i in 0..clamp(e): any bnd expression; the body may change what the bnd was computed from
      if depth ≥ 2 then genAssign cfg env 2 else
      let (e, elo, ehi) ← genExpr cfg env 2
      let k : Int := (← rnd 10)
      -- the clamp is never dropped, not even in a risky program: `evalFn` would have to run the loop
      -- (a bnd of 2^62 is not stuck, it just never finishes)
      let bnd := if 0 ≤ elo && ehi ≤ 12 then e else clampSel e (.lit 0) (.lit k)
      let hi : Int := if 0 ≤ elo && ehi ≤ 12 then ehi else k
      let benv := GS.int 0 (max (hi - 1) 0) false :: env
      let s ← genStmt cfg fuel benv true (depth + 1)
      let s2 ← genStmt cfg fuel benv true (depth + 1)
      pure (.forE bnd triv (.seq s s2))
    | 26 =>
      -- { let m = clamp(e, 0, k); for i in 0..m { body; m = clamp(m + 1) } }: the bnd is evaluated once
      if depth ≥ 2 then genAssign cfg env 2 else
      let (e, _, _) ← genExpr cfg env 1
      let k : Int := 1 + (← rnd 6)
      let benv := GS.int 0 (k - 1) false :: GS.int 0 (2 * k) false :: env
      let s ← genStmt cfg fuel benv true (depth + 1)
      let bump ← clampAssign cfg 1 0 (2 * k) (.add (.var 1) (.lit 1), 1, 2 * k + 1)
      pure (.decl 0 (2 * k) (clampSel e (.lit 0) (.lit k)) (.forE (.var 0) triv (.seq s bump)))
    | 27 =>
      -- if 1 ≤ len(a) { let k = clamp(e, 0, len(a) - 1); body with k a valid index }
      let sl := slVars env
      if sl.isEmpty then genStore cfg env 2 else
      let a ← pick 0 sl
      let (e, _, _) ← genExpr cfg env 2
      let benv := GS.int 0 ((maxSliceLen : Int) - 1) true true :: env
      let s ← genStmt cfg fuel benv inLoop depth
      let s2 ← genStmt cfg fuel benv inLoop depth
      pure (.ite (.lit 1) (.len a)
        (.decl 0 i64Max (clampSel e (.lit 0) (.sub (.len a) (.lit 1))) (.seq s s2)) .skip)
    | 28 =>
      -- if (comparison) s else t, written with `ite 1 c`
      let a ← genExpr cfg env 1
      let b ← genExpr cfg env 1
      let c ← pick (Expr.lt a.1 b.1) [Expr.lt a.1 b.1, Expr.eq a.1 b.1, Expr.le a.1 b.1]
      let s ← genStmt cfg fuel env inLoop depth
      let t ← genStmt cfg fuel env inLoop depth
      pure (.ite (.lit 1) c s t)
    | 0 | 1 => genAssign cfg env 2
    | 2 => genStore cfg env 2
    | 3 | 4 | 5 =>
      let a ← genExpr cfg env 1
      let b ← genExpr cfg env 1
      let s ← genStmt cfg fuel env inLoop depth
      let t ← if ← chance 1 3 then pure Stmt.skip else genStmt cfg fuel env inLoop depth
      pure (.ite a.1 b.1 s t)
    | 6 | 7 =>
      let (e, elo, ehi) ← genExpr cfg env 2
      -- declared range: the interval of the initial value, sometimes widened
      let (lo, hi) ← do
        if ← chance 1 2 then pure (elo, ehi) else
          let (rl, rh) ← genRange
          pure (min elo rl, max ehi rh)
      let s ← genStmt cfg fuel (.int lo hi false :: env) inLoop depth
      let s2 ← genStmt cfg fuel (.int lo hi false :: env) inLoop depth
      pure (.decl lo hi e (.seq s s2))
    | 8 | 9 | 10 =>
      if depth ≥ 2 then genAssign cfg env 2 else
      let lens := (arrVars env).map (·.2)
      let n ← if !lens.isEmpty && (← chance 1 2) then pick 0 lens else rnd 9
      let n := min n 12
      -- the counter's values are 0..n-1 (its Tenon type is 0..=n); the body may assign it
      let s ← genStmt cfg fuel (.int 0 (n - 1 : Nat) false :: env) true (depth + 1)
      let s2 ← genStmt cfg fuel (.int 0 (n - 1 : Nat) false :: env) true (depth + 1)
      pure (.forN n triv (.seq s s2))
    | 11 | 12 =>
      let s ← genStmt cfg fuel env inLoop depth
      let t ← genStmt cfg fuel env inLoop depth
      pure (.seq s t)
    | 13 =>
      if inLoop then
        let a ← genExpr cfg env 1
        let b ← genExpr cfg env 1
        if ← chance 1 2 then pure (.ite a.1 b.1 .brk .skip)
        else pure (.ite a.1 b.1 (← genStmt cfg fuel env inLoop depth) .brk)
      else genAssign cfg env 2
    | 14 | 15 | 16 =>
      -- break-only loops
      if depth ≥ 2 then genAssign cfg env 2 else
      match ← rnd 6 with
      | 0 | 1 | 2 =>
        -- { let c = 0; loop { if K ≤ c break; body; c = c + 1 } }   the body cannot change c
        let k : Int := (← rnd 9)
        let benv := GS.int 0 k true :: env
        let s ← genStmt cfg fuel benv true (depth + 1)
        let s2 ← genStmt cfg fuel benv true (depth + 1)
        -- risky: a proof bnd that is one too small (stuck unless the body breaks earlier)
        let n : Nat := if (← careless cfg) || (cfg.risky && (← chance 1 6)) then k.toNat else k.toNat + 1
        pure (.decl 0 k (.lit 0) (.loopB n triv
          (.seq (.ite (.lit k) (.var 0) .brk .skip) (.seq (.seq s s2) (.assign 0 (.add (.var 0) (.lit 1)))))))
      | 3 | 4 =>
        -- { let h = 0; h = clamp(e); loop { if h ≤ 0 break; body; h = h / 2 } }   the body cannot change h
        let hmax ← pick 100 [7, 100, 1000000, 4611686018427387904]
        let init ← clampAssign cfg 0 0 hmax (← genExpr cfg (GS.int 0 hmax true :: env) 2)
        let benv := GS.int 0 hmax true :: env
        let s ← genStmt cfg fuel benv true (depth + 1)
        pure (.decl 0 hmax (.lit 0) (.seq init (.loopB 64 triv
          (.ite (.var 0) (.lit 0) .brk (.seq s (.assign 0 (.div (.var 0) (.lit 2))))))))
      | _ =>
        -- { let c = 0; loop { body; if K ≤ c break; c = c + 1 } }   the body may change c: sometimes stuck
        let k : Int := (← rnd 6)
        let benv := GS.int 0 k false :: env
        let s ← genStmt cfg fuel benv true (depth + 1)
        pure (.decl 0 k (.lit 0) (.loopB (k.toNat + 1) triv
          (.seq s (.ite (.lit k) (.var 0) .brk (.assign 0 (.add (.var 0) (.lit 1)))))))
    | _ => genCallStmt cfg env 2

def hashM : Int := 1000003

/-- e mod m for e ≥ 0, m > 0, written with what Tenon has: e - (e / m) * m. -/
def modE (e : Expr) (m : Int) : Expr := .sub e (.mul (.div e (.lit m)) (.lit m))

/-- With u (0..=i64Max) at position `u` and h (0..=M-1) at position `u + 1`: fold the integer
    expression `e` (any int64 value) into the hash h. Never stuck: u = e or -1 - e (non-negative),
    h = (h * 31 + u mod M) mod M. -/
def mixStmt (u : Nat) (e : Expr) : Stmt :=
  .seq (.ite (.lit 0) e (.assign u e) (.assign u (.sub (.lit (-1)) e)))
       (.assign (u + 1) (modE (.add (.mul (.var (u + 1)) (.lit 31)) (modE (.var u) hashM)) hashM))

/-- A tail that makes the result depend on the whole final state: every integer variable and every
    array element is folded into a hash, and the result is the hash reduced into the result range.
    Environment where it runs: [h, result, params...]; it declares u in front. -/
def hashTail (rlo rhi : Int) (params : List Ty) (sh : Nat := 0) : Stmt :=
  -- inside: [u, h, (fh if sh = 1,) result, params...]
  let mixes : List Stmt := (.int rlo rhi :: params).zipIdx.map fun (ty, k) =>
    match ty with
    | .int _ _ => mixStmt 0 (.var (k + 2 + sh))
    | .arr n _ _ => .forN n triv (mixStmt 1 (.idx (k + 3 + sh) (.var 0)))      -- [i, u, h, result, params...]
    | .slice _ _ => .seq (mixStmt 0 (.len (k + 2 + sh))) (.forE (.len (k + 2 + sh)) triv (mixStmt 1 (.idx (k + 3 + sh) (.var 0))))
    | .flt => .skip                      -- floats cannot enter the integer hash: they are compared directly
    | .fslice => mixStmt 0 (.len (k + 2 + sh))
  let w := rhi - rlo
  let hm : Expr := if w ≥ hashM - 1 then .var 1 else modE (.var 1) (w + 1)
  let fin : Stmt := .assign (2 + sh) (.add (.lit rlo) hm)
  .decl 0 i64Max (.lit 0) (mixes.foldr .seq fin)

def genFn (cfg : Cfg) : G Fn := do
  let np ← if ← chance 1 12 then pure 0 else (do pure (1 + (← rnd 4)))
  let mut params : List (Ty × Bool) := []
  for _ in [0:np] do
    if cfg.floats && (← chance 2 5) then
      -- float parameters: most are inout, because that is where float results are observable
      if ← chance 1 2 then params := params ++ [(.fslice, ← chance 2 3)]
      else params := params ++ [(.flt, ← chance 2 3)]
    else if ← chance 1 4 then
      params := params ++ [(.arr (← pick 4 cfg.lens) (-cfg.E) cfg.E, ← chance 1 2)]
    else if ← chance 1 3 then
      params := params ++ [(.slice (-cfg.E) cfg.E, ← chance 1 2)]
    else
      let (lo, hi) ← genRange
      params := params ++ [(.int lo hi, ← chance 1 3)]
  let (rlo, rhi) ← genRange
  let ptys := params.map (·.1)
  let penv : List GS := ptys.map fun
    | .int lo hi => GS.int lo hi false
    | .arr n _ _ => GS.arr n
    | .slice _ _ => GS.slice
    | .flt => GS.flt false
    | .fslice => GS.fslice
  let ns ← rnd 4
  if cfg.floats && (← chance 4 5) then
    -- body in [h, fh, result, params...]: fh is a float local; then a float tail that makes fh
    -- observable through the inout float parameters, then the hash tail
    let env : List GS := .int 0 (hashM - 1) false :: .flt false :: .int rlo rhi false :: penv
    let mut body : Stmt := hashTail rlo rhi ptys 1
    for (ty, io) in params.zipIdx.map (fun ((t, io), k) => ((t, k), io)) do
      match ty, io with
      | (.flt, k), true => if ← chance 1 2 then body := .seq (.fassign (k + 3) (.add (.var (k + 3)) (.var 1))) body
      | (.fslice, k), true =>
        body := .seq (.ite (.lit 1) (.len (k + 3)) (.fstore (k + 3) (.lit 0) (.add (.idx (k + 3) (.lit 0)) (.var 1))) .skip) body
      | _, _ => pure ()
    for _ in [0:ns + 2] do
      let s ← genStmt cfg 3 env false 0
      body := .seq s body
      if !cfg.callees.isEmpty && (← chance 1 2) then
        body := .seq (← genCallStmt cfg env 2) body
    pure { params := params, rlo := rlo, rhi := rhi,
           body := .fdecl (.lit (Float.ofBits (← genFBits 10))) (.decl 0 (hashM - 1) (.lit 0) body),
           req := .tt, pre := fun _ => True, post := fun _ _ _ => True }
  else if ← chance 3 4 then
    -- body in [h, result, params...], followed by the hash tail
    let env : List GS := .int 0 (hashM - 1) false :: .int rlo rhi false :: penv
    let mut body : Stmt := hashTail rlo rhi ptys
    for _ in [0:ns + 1] do
      let s ← genStmt cfg 3 env false 0
      body := .seq s body
      -- make calls frequent: half of the top-level statements are followed by a call
      if !cfg.callees.isEmpty && (← chance 1 2) then
        body := .seq (← genCallStmt cfg env 2) body
    if ← chance 1 2 then
      -- also fold the integer parameters into h before the body, so that the body starts from an
      -- input-dependent variable            [u, h, result, params...]
      let pre : List Stmt := ptys.zipIdx.filterMap fun (ty, k) =>
        match ty with | Ty.int _ _ => some (mixStmt 0 (.var (k + 3))) | _ => none
      body := .seq (.decl 0 i64Max (.lit 0) (pre.foldr .seq .skip)) body
    pure { params := params, rlo := rlo, rhi := rhi, body := .decl 0 (hashM - 1) (.lit 0) body,
           req := .tt, pre := fun _ => True, post := fun _ _ _ => True }
  else
    let env : List GS := .int rlo rhi false :: penv
    let mut body : Stmt ← clampAssign cfg 0 rlo rhi (← genExpr cfg env 2)
    for _ in [0:ns + 1] do
      let s ← genStmt cfg 3 env false 0
      body := .seq s body
    pure { params := params, rlo := rlo, rhi := rhi, body := body, req := .tt, pre := fun _ => True, post := fun _ _ _ => True }

structure Prog where
  fns   : List Fn
  names : List FnNames
  E     : Int
  risky : Bool

def fnNamesFor (pfx : String) (k : Nat) (f : Fn) : FnNames :=
  { name := s!"{pfx}f{k}",
    params := (f.params.zipIdx).map fun ((ty, _), i) => match ty with
      | .int _ _ => s!"v{i}"
      | .arr .. => s!"a{i}"
      | .slice .. => s!"s{i}"
      | .flt => s!"x{i}"
      | .fslice => s!"fs{i}" }

def genProg (pfx : String) : G Prog := do
  let E ← pick 1000 [10, 1000, 1000, 1000000000, 4611686018427387904]
  let risky ← chance 1 6
  let floats ← chance 3 5
  let l1 ← pick 4 [1, 2, 3, 4, 5, 8, 16]
  let l2 ← pick 4 [0, 1, 2, 4, 8]
  let nf ← rnd 3
  let mut fns : List Fn := []
  for _ in [0:nf + 1] do
    let cfg : Cfg := { E := E, risky := risky, lens := [l1, l1, l2], floats := floats,
                       callees := fns.map fun f => (f.params, f.rlo, f.rhi) }
    let f ← genFn cfg
    fns := f :: fns
  pure { fns := fns, names := (fns.zipIdx).map fun (f, k) => fnNamesFor pfx k f, E := E, risky := risky }

/-- Arguments for a function: mostly inside the parameter types, sometimes deliberately outside
    (wrong array length, element or integer one past the range), which `evalFn` must answer with
    `none`. Array elements are drawn from the intersection of the type's range and elo..=ehi. -/
def genArgs (params : List (Ty × Bool)) (elo ehi : Int) (maxLen : Nat := 12) (samePct : Nat := 85) (fspecial : Nat := 30) :
    G (List (Val × List UInt64)) := do
  -- slice lengths: 0 and 1 are frequent; in most inputs all slices have the same length
  let genLen : G Nat := do
    match ← rnd 8 with
    | 0 => pure 0
    | 1 => pure (min 1 maxLen)
    | 2 => pure (min 8 maxLen)
    | 3 => pure maxLen
    | _ => rnd (maxLen + 1)
  let common ← genLen
  let same ← chance samePct 100
  let bad ← chance 1 20
  let badAt ← rnd params.length
  let badKind ← rnd 2
  let sorted ← chance 1 3
  (params.zipIdx).mapM fun ((ty, _), i) => do
    match ty with
    | .int lo hi =>
      if bad && i == badAt then pure (.int (if ← chance 1 2 then hi + 1 else lo - 1), [])
      else pure (.int (← rndBiased lo hi), [])
    | .flt =>
      -- there is no float outside the type; a bad argument is an integer where a float is expected
      if bad && i == badAt then pure (.int 0, []) else
      let b ← genFBits fspecial
      pure (.flt (Float.ofBits b), [b])
    | .fslice =>
      if bad && i == badAt then pure (.arr [], []) else
      let n ← if same then pure common else genLen
      let mut l : List UInt64 := []
      for _ in [0:n] do
        l := (← genFBits fspecial) :: l
      pure (.farr (l.map Float.ofBits), l)
    | .arr n tlo thi =>
      let isBad := bad && i == badAt
      let n' := if isBad && (badKind == 0 || n == 0) then n + 1 else n
      let lo := max elo tlo
      let hi := max lo (min ehi thi)
      let mut l : List Int := []
      for _ in [0:n'] do
        l := (← rndBiased lo hi) :: l
      let l2 := if sorted then (l.toArray.qsort (· < ·)).toList else l
      if isBad && n' == n then pure (.arr (l2.set (← rnd n) (thi + 1)), []) else pure (.arr l2, [])
    | .slice tlo thi =>
      let isBad := bad && i == badAt
      let n ← if same then pure common else genLen
      let lo := max elo tlo
      let hi := max lo (min ehi thi)
      let mut l : List Int := []
      for _ in [0:n] do
        l := (← rndBiased lo hi) :: l
      let l2 := if sorted then (l.toArray.qsort (· < ·)).toList else l
      -- a bad slice has an element outside the element range (there is no wrong length for a slice)
      if isBad && n > 0 then pure (.arr (l2.set (← rnd n) (if ← chance 1 2 then thi + 1 else tlo - 1)), []) else pure (.arr l2, [])

/-! ## Printing Tenon terms (for reproducers) -/

def reprE : Expr → String
  | .lit n => if n < 0 then s!"(lit ({n}))" else s!"(lit {n})"
  | .var i => s!"(var {i})"
  | .add a b => s!"(add {reprE a} {reprE b})"
  | .sub a b => s!"(sub {reprE a} {reprE b})"
  | .mul a b => s!"(mul {reprE a} {reprE b})"
  | .div a b => s!"(div {reprE a} {reprE b})"
  | .idx a e => s!"(idx {a} {reprE e})"
  | .len a => s!"(alen {a})"
  | .le a b => s!"(le {reprE a} {reprE b})"
  | .lt a b => s!"(lt {reprE a} {reprE b})"
  | .eq a b => s!"(eq {reprE a} {reprE b})"
  | .sel c t e => s!"(.sel {reprE c} {reprE t} {reprE e})"

def hex16 (b : UInt64) : String := hexPad b.toNat 16

def reprF : FExpr → String
  | .lit f => s!"(.lit (Float.ofBits 0x{hex16 f.toBits}))"
  | .var i => s!"(.var {i})"
  | .add a b => s!"(.add {reprF a} {reprF b})"
  | .sub a b => s!"(.sub {reprF a} {reprF b})"
  | .mul a b => s!"(.mul {reprF a} {reprF b})"
  | .div a b => s!"(.div {reprF a} {reprF b})"
  | .idx a e => s!"(.idx {a} {reprE e})"
  | .ofInt e => s!"(.ofInt {reprE e})"
  | .sel c t e => s!"(.sel {reprE c} {reprF t} {reprF e})"
  | .neg a => s!"(.neg {reprF a})"
  | .abs a => s!"(.abs {reprF a})"
  | .sqrt a => s!"(.sqrt {reprF a})"
  | .selLe a b t e => s!"(.selLe {reprF a} {reprF b} {reprF t} {reprF e})"

def pInt (n : Int) : String := if n < 0 then s!"({n})" else s!"{n}"

def reprS (d : Nat) : Stmt → String
  | .skip => "skip"
  | .brk => "brk"
  | .seq s t => s!"(seq {reprS d s}\n{ind d ""}{reprS d t})"
  | .assign x e => s!"(assign {x} {reprE e})"
  | .store a i e => s!"(store {a} {reprE i} {reprE e})"
  | .ite a b s t => s!"(ite {reprE a} {reprE b}\n{ind (d+1) ""}{reprS (d+1) s}\n{ind (d+1) ""}{reprS (d+1) t})"
  | .decl lo hi e s => s!"(decl {pInt lo} {pInt hi} {reprE e}\n{ind (d+1) ""}{reprS (d+1) s})"
  | .forN n _ s => s!"(forN {n} triv\n{ind (d+1) ""}{reprS (d+1) s})"
  | .loopB n _ s => s!"(loopB {n} triv\n{ind (d+1) ""}{reprS (d+1) s})"
  | .forE e _ s => s!"(forE {reprE e} triv\n{ind (d+1) ""}{reprS (d+1) s})"
  | .call f args dst => s!"(call {f} {args} {dst})"
  | .fassign x e => s!"(fassign {x} {reprF e})"
  | .fstore a i e => s!"(fstore {a} {reprE i} {reprF e})"
  | .fdecl e s => s!"(fdecl {reprF e}\n{ind (d+1) ""}{reprS (d+1) s})"
  | .fite a b s t => s!"(fite {reprF a} {reprF b}\n{ind (d+1) ""}{reprS (d+1) s}\n{ind (d+1) ""}{reprS (d+1) t})"
  | .loopE e _ s => s!"(loopE {reprE e} triv\n{ind (d+1) ""}{reprS (d+1) s})"

def reprTy : Ty × Bool → String
  | (.int lo hi, io) => s!"(.int {pInt lo} {pInt hi}, {io})"
  | (.arr n lo hi, io) => s!"(.arr {n} {pInt lo} {pInt hi}, {io})"
  | (.slice lo hi, io) => s!"(.slice {pInt lo} {pInt hi}, {io})"
  | (.flt, io) => s!"(.flt, {io})"
  | (.fslice, io) => s!"(.fslice, {io})"

def reprFn (f : Fn) : String :=
  "{ params := [" ++ ", ".intercalate (f.params.map reprTy) ++ s!"], rlo := {f.rlo}, rhi := {f.rhi},\n" ++
  "  req := .tt, pre := fun _ => True, post := fun _ _ _ => True,\n  body :=\n    " ++ reprS 2 f.body ++ " }"

def reprVal : Val → String
  | .int v => s!".int {pInt v}"
  | .arr l => s!".arr {l}"
  | .flt f => s!".flt (Float.ofBits 0x{hex16 f.toBits})"
  | .farr l => ".farr [" ++ ", ".intercalate (l.map fun f => s!"Float.ofBits 0x{hex16 f.toBits}") ++ "]"

def reprArgs (vs : List Val) : String := "[" ++ ", ".intercalate (vs.map reprVal) ++ "]"

/-! ## Writing a batch -/

structure Case where
  fnIdx : Nat
  args  : List Val
  res   : Option (Int × List Val)
  /-- For float arguments: the exact input bit patterns (Lean's `Float.toBits` would turn every NaN
      into 0x7ff8000000000000). Empty for integer arguments. -/
  fbits : List (List UInt64) := []

structure Item where
  id    : Nat
  label : String
  fns   : List Fn
  names : List FnNames
  cases : List Case

def cInt (n : Int) : String := if n == i64Min then "INT64_MIN" else s!"INT64_C({n})"

/-- What the C side must show after the call, in parameter order: an inout integer's final value, an
    inout array's final elements, and a by-value array's ORIGINAL elements (the caller's array must
    be untouched). By-value integers are not observable. -/
def expectedOuts (params : List (Ty × Bool)) (args outs : List Val) (fbits : List (List UInt64) := []) : List String :=
  let ft (f : Float) : String := "f:" ++ hex16 f.toBits
  let fb (b : UInt64) : String := "f:" ++ hex16 b
  (((params.zip args).zip outs).zipIdx).foldl (fun acc ((((_, io), a), o), k) =>
    match a, o, io with
    | .int _, .int v, true => acc ++ [toString v]
    | .arr _, .arr l, true => acc ++ l.map toString
    | .arr l, _, false => acc ++ l.map toString
    -- floats: the final value of an inout scalar and of an inout slice as Tenon computed them (through
    -- `Float.toBits`, so a NaN is always 7ff8000000000000); a by-value slice as the exact input bits
    | .flt _, .flt v, true => acc ++ [ft v]
    | .farr _, .farr l, true => acc ++ l.map ft
    | .farr l, _, false => acc ++ (match fbits[k]? with
        | some bs => if bs.length == l.length then bs.map fb else l.map ft
        | none => l.map ft)
    | _, _, _ => acc) []

/-- The C text that runs the comparable cases of one item, and the lines of the expected file. -/
def itemDriver (it : Item) : List String × List String := Id.run do
  let mut data : List String := []
  let mut calls : List String := []
  let mut expect : List String := []
  for (c, ci) in it.cases.zipIdx do
    match c.res, it.fns[c.fnIdx]? with
    | some (r, outs), some f =>
      let ex := expectedOuts f.params c.args outs c.fbits
      expect := expect ++ [s!"{it.id} {ci} {c.fnIdx} some {" ".intercalate (toString r :: ex)}"]
      let fname := (it.names.getD c.fnIdx { name := "?", params := [] }).name
      let mut args : List String := []
      let mut ints : List String := []
      let mut flts : List String := []
      let mut prints : List String := []
      let bitsOf (k : Nat) (l : List Float) : List UInt64 := match c.fbits[k]? with
        | some bs => if bs.length == l.length then bs else l.map Float.toBits
        | none => l.map Float.toBits
      for ((v, (pty, io)), k) in (c.args.zip f.params).zipIdx do
        let isSlice := match pty with | .slice .. => true | _ => false
        match v with
        | .int x =>
          let ref := s!"s_{it.id}_{ci}[{ints.length}]"
          args := args ++ [if io then "&" ++ ref else ref]
          if io then prints := prints ++ [s!"pr1({ref});"]
          ints := ints ++ [cInt x]
        | .arr l =>
          -- every array has one extra element, a canary that the driver checks after the call
          data := data ++ [s!"int64_t d_{it.id}_{ci}_{k}[{l.length + 1}] = \{{", ".intercalate (l.map cInt ++ ["CANARY"])}};"]
          -- a slice is a pointer and the true length
          args := args ++ [s!"d_{it.id}_{ci}_{k}"] ++ (if isSlice then [s!"{l.length}"] else [])
          prints := prints ++ [s!"pr(d_{it.id}_{ci}_{k}, {l.length});"]
        | .flt x =>
          -- float scalars live in a union so that they are given and printed as bit patterns
          let ref := s!"fs_{it.id}_{ci}"
          let j := flts.length
          args := args ++ [if io then s!"&{ref}.d[{j}]" else s!"{ref}.d[{j}]"]
          if io then prints := prints ++ [s!"prf1({ref}.u[{j}]);"]
          flts := flts ++ [s!"UINT64_C(0x{hex16 ((bitsOf k [x]).headD 0)})"]
        | .farr l =>
          let bs := (bitsOf k l).map fun b => s!"UINT64_C(0x{hex16 b})"
          data := data ++ [s!"static FU({l.length + 1}) fd_{it.id}_{ci}_{k} = \{\{{", ".intercalate (bs ++ ["FCANARY"])}}};"]
          args := args ++ [s!"fd_{it.id}_{ci}_{k}.d", s!"{l.length}"]
          prints := prints ++ [s!"prf(fd_{it.id}_{ci}_{k}.u, {l.length});"]
      if !flts.isEmpty then
        data := data ++ [s!"static FU({flts.length}) fs_{it.id}_{ci} = \{\{{", ".intercalate flts}}};"]
      if !ints.isEmpty then
        data := data ++ [s!"int64_t s_{it.id}_{ci}[{ints.length}] = \{{", ".intercalate ints}};"]
      calls := calls ++ [s!"    printf(\"{it.id} {ci} %\" PRId64, {fname}({", ".intercalate args})); {" ".intercalate prints} putchar('\\n');"]
    | _, _ => expect := expect ++ [s!"{it.id} {ci} {c.fnIdx} none"]
  let body := data ++ [s!"static void run_{it.id}(void)", "{"] ++ calls ++ ["}", ""]
  (body, expect)

def countS (p : Stmt → Bool) : Stmt → Nat
  | .seq s t => countS p s + countS p t + (if p (.seq s t) then 1 else 0)
  | .ite a b s t => countS p s + countS p t + (if p (.ite a b s t) then 1 else 0)
  | .decl lo hi e s => countS p s + (if p (.decl lo hi e s) then 1 else 0)
  | .forN n I s => countS p s + (if p (.forN n I s) then 1 else 0)
  | .loopB n I s => countS p s + (if p (.loopB n I s) then 1 else 0)
  | .forE e I s => countS p s + (if p (.forE e I s) then 1 else 0)
  | .loopE e I s => countS p s + (if p (.loopE e I s) then 1 else 0)
  | .fdecl e s => countS p s + (if p (.fdecl e s) then 1 else 0)
  | .fite a b s t => countS p s + countS p t + (if p (.fite a b s t) then 1 else 0)
  | s => if p s then 1 else 0

def countF (p : FExpr → Bool) : FExpr → Nat
  | .add a b => countF p a + countF p b + (if p (.add a b) then 1 else 0)
  | .sub a b => countF p a + countF p b + (if p (.sub a b) then 1 else 0)
  | .mul a b => countF p a + countF p b + (if p (.mul a b) then 1 else 0)
  | .div a b => countF p a + countF p b + (if p (.div a b) then 1 else 0)
  | .sel c t e => countF p t + countF p e + (if p (.sel c t e) then 1 else 0)
  | .neg a => countF p a + (if p (.neg a) then 1 else 0)
  | .abs a => countF p a + (if p (.abs a) then 1 else 0)
  | .sqrt a => countF p a + (if p (.sqrt a) then 1 else 0)
  | .selLe a b t e => countF p a + countF p b + countF p t + countF p e + (if p (.selLe a b t e) then 1 else 0)
  | e => if p e then 1 else 0

/-- Occurrences of float expression nodes satisfying `p` in a statement. -/
def countFS (p : FExpr → Bool) : Stmt → Nat
  | .seq s t | .ite _ _ s t => countFS p s + countFS p t
  | .decl _ _ _ s | .forN _ _ s | .forE _ _ s | .loopB _ _ s | .loopE _ _ s => countFS p s
  | .fassign _ e | .fstore _ _ e => countF p e
  | .fdecl e s => countF p e + countFS p s
  | .fite a b s t => countF p a + countF p b + countFS p s + countFS p t
  | _ => 0

def countE (p : Expr → Bool) : Expr → Nat
  | .add a b => countE p a + countE p b + (if p (.add a b) then 1 else 0)
  | .sub a b => countE p a + countE p b + (if p (.sub a b) then 1 else 0)
  | .mul a b => countE p a + countE p b + (if p (.mul a b) then 1 else 0)
  | .div a b => countE p a + countE p b + (if p (.div a b) then 1 else 0)
  | .le a b => countE p a + countE p b + (if p (.le a b) then 1 else 0)
  | .lt a b => countE p a + countE p b + (if p (.lt a b) then 1 else 0)
  | .eq a b => countE p a + countE p b + (if p (.eq a b) then 1 else 0)
  | .idx a e => countE p e + (if p (.idx a e) then 1 else 0)
  | .sel c t e => countE p c + countE p t + countE p e + (if p (.sel c t e) then 1 else 0)
  | e => if p e then 1 else 0

/-- Occurrences of expression nodes satisfying `p` in a statement. -/
def countES (p : Expr → Bool) : Stmt → Nat
  | .seq s t => countES p s + countES p t
  | .assign _ e => countE p e
  | .store _ i e => countE p i + countE p e
  | .ite a b s t => countE p a + countE p b + countES p s + countES p t
  | .decl _ _ e s => countE p e + countES p s
  | .forN _ _ s => countES p s
  | .forE e _ s => countE p e + countES p s
  | .loopB _ _ s => countES p s
  | .loopE e _ s => countE p e + countES p s
  | .fdecl _ s => countES p s
  | .fite _ _ s t => countES p s + countES p t
  | _ => 0

def isCall (io : Bool) (excl : Option Bool) : Stmt → Bool
  | .call _ args dst => (!io || args.any (·.2)) && (match excl with | some b => exclusive args dst == b | none => true)
  | _ => false

def parseSabotage : String → Option Sabotage
  | "none" => some .none
  | "lt" => some .lt
  | "noCopy" => some .noCopy
  | "counter" => some .counter
  | "noWriteBack" => some .noWriteBack
  | "inoutCopy" => some .inoutCopy
  | "loopBOnce" => some .loopBOnce
  | "loopBShort" => some .loopBShort
  | "selSwap" => some .selSwap
  | "selTruthy" => some .selTruthy
  | "ltAsLe" => some .ltAsLe
  | "eqAsLe" => some .eqAsLe
  | "leAsLt" => some .leAsLt
  | "lenOff" => some .lenOff
  | "forEReeval" => some .forEReeval
  | "forEShort" => some .forEShort
  | "sliceNoCopy" => some .sliceNoCopy
  | "fma" => some .fma
  | "reassoc" => some .reassoc
  | "selLeNaN" => some .selLeNaN
  | "fleAsLt" => some .fleAsLt
  | "fselSwap" => some .fselSwap
  | "ofIntF32" => some .ofIntF32
  | "sqrtF32" => some .sqrtF32
  | "absDrop" => some .absDrop
  | "negSub" => some .negSub
  | "loopEEval" => some .loopEEval
  | _ => none

def writeBatch (outdir : String) (sab : Sabotage) (form : SelForm) (items : List Item) : IO Unit := do
  IO.FS.createDirAll outdir
  let opts : Options := { sabotage := sab, selForm := form, prelude := false }
  let mut c : Array String := #["#include <inttypes.h>", "#include <stdio.h>", fullPrelude, "",
    "#define CANARY INT64_C(0x5A5A5A5A5A5A5A5A)",
    "static void pr1(int64_t v) { printf(\" %\" PRId64, v); }",
    "/* prints n elements, then checks the canary that follows them */",
    "static void pr(const int64_t *p, int n) { for (int i = 0; i < n; i++) printf(\" %\" PRId64, p[i]); if (p[n] != CANARY) printf(\" OVERRUN\"); }",
    "/* doubles are given and printed as bit patterns: a union of the bits and the values */",
    "#define FU(n) union { uint64_t u[n]; double d[n]; }",
    "#define FCANARY UINT64_C(0x7ff5a5a5a5a5a5a5)",
    "static void prf1(uint64_t b) { printf(\" f:%016\" PRIx64, b); }",
    "static void prf(const uint64_t *p, int n) { for (int i = 0; i < n; i++) printf(\" f:%016\" PRIx64, p[i]); if (p[n] != FCANARY) printf(\" OVERRUN\"); }"]
  let mut expect : Array String := #[]
  let mut nSome := 0
  let mut nNone := 0
  let mut nEmitErr := 0
  let mut ids : Array Nat := #[]
  for it in items do
    match emitProgram opts it.fns it.names with
    | .error e =>
      nEmitErr := nEmitErr + 1
      expect := expect.push s!"# {it.id} emit-error {e}"
    | .ok src =>
      let lines := src.splitOn "\n"
      c := c.push s!"/* ==== program {it.id}: {it.label} ==== */"
      c := c ++ lines.toArray
      let (drv, ex) := itemDriver it
      c := c ++ drv.toArray
      expect := expect ++ ex.toArray
      ids := ids.push it.id
      for cs in it.cases do
        if cs.res.isSome then nSome := nSome + 1 else nNone := nNone + 1
  c := c ++ #["int main(int argc, char **argv)", "{", "    long only = argc > 1 ? atol(argv[1]) : -1;",
    "    if (getenv(\"DT_LINEBUF\")) setvbuf(stdout, NULL, _IOLBF, 0);   /* keep results if the run is killed */"]
  for id in ids do
    c := c.push s!"    if (only < 0 || only == {id}) run_{id}();"
  c := c ++ #["    return 0;", "}", ""]
  IO.FS.writeFile (outdir ++ "/batch.c") ("\n".intercalate c.toList)
  IO.FS.writeFile (outdir ++ "/expected.txt") ("\n".intercalate expect.toList ++ "\n")
  let allFns := items.foldl (fun l it => l ++ it.fns) []
  let cnt (p : Stmt → Bool) := allFns.foldl (fun n f => n + countS p f.body) 0
  -- programs whose entry function gave at least two different outcomes on its comparable inputs
  let nSens := items.foldl (fun n it =>
    let rs := it.cases.filterMap fun c => if c.fnIdx == 0 then
      (match c.res, it.fns[0]? with
       | some (r, outs), some f => some (toString r :: expectedOuts (f.params.map fun (t, _) => (t, true)) c.args outs)
       | _, _ => none) else none
    if rs.eraseDups.length > 1 then n + 1 else n) 0
  -- parameter passing, counted statically over all functions
  let pass := allFns.foldl (fun l f => l ++ ((passing {} f).zip (f.params.zipIdx)).map fun (p, (_, k)) => (p, storesInto f.body (k + 1))) []
  let np (q : Passing × Bool → Bool) := (pass.filter q).length
  IO.println s!"input_sensitive_programs={nSens}"
  IO.println s!"generated: programs={items.length} functions={allFns.length} emit_errors={nEmitErr} cases_some={nSome} cases_none={nNone}"
  let cntE (p : Expr → Bool) := allFns.foldl (fun n f => n + countES p f.body) 0
  let nSl (q : Passing → Bool) := (allFns.foldl (fun l f => l ++ ((passing {} f).zip f.params).filterMap fun (p, (ty, _)) =>
    match ty with | Ty.slice .. => some p | _ => none) []).filter q |>.length
  let lensSeen := items.foldl (fun l it => l ++ it.cases.foldl (fun l2 c => l2 ++ (if c.res.isSome then
    ((it.fns[c.fnIdx]?.map (·.params)).getD [] |>.zip c.args).filterMap fun ((ty, _), v) =>
      match ty, v with | Ty.slice .., .arr x => some x.length | _, _ => none else [])) []) []
  let nLen (q : Nat → Bool) := (lensSeen.filter q).length
  IO.println s!"tn_features: forE={cnt (· matches .forE ..)} len={cntE (· matches .len ..)} sel={cntE (· matches .sel ..)} le={cntE (· matches .le ..)} lt={cntE (· matches .lt ..)} eq={cntE (· matches .eq ..)} slice_params_read_only={nSl (· == .arrRead)} slice_params_inout={nSl (· == .arrInout)} slice_params_private_copy={nSl (· == .arrCopy)}"
  let cntF (p : FExpr → Bool) := allFns.foldl (fun n f => n + countFS p f.body) 0
  let nFP (q : Ty × Bool → Bool) := (allFns.foldl (fun l f => l ++ f.params) []).filter q |>.length
  IO.println s!"tn_features: loopE={cnt (· matches .loopE ..)} fassign={cnt (· matches .fassign ..)} fstore={cnt (· matches .fstore ..)} fdecl={cnt (· matches .fdecl ..)} fite={cnt (· matches .fite ..)} f_lit={cntF (· matches .lit ..)} f_var={cntF (· matches .var ..)} f_add={cntF (· matches .add ..)} f_sub={cntF (· matches .sub ..)} f_mul={cntF (· matches .mul ..)} f_div={cntF (· matches .div ..)} f_idx={cntF (· matches .idx ..)} f_ofInt={cntF (· matches .ofInt ..)} f_sel={cntF (· matches .sel ..)} f_neg={cntF (· matches .neg ..)} f_abs={cntF (· matches .abs ..)} f_sqrt={cntF (· matches .sqrt ..)} f_selLe={cntF (· matches .selLe ..)} mul_add_shapes={cntF (fun e => match e with | .add (.mul ..) _ | .add _ (.mul ..) | .sub (.mul ..) _ => true | _ => false)} add_add_shapes={cntF (fun e => match e with | .add (.add ..) _ => true | _ => false)} float_params_by_value={nFP (fun p => p.1 == .flt && !p.2)} float_params_inout={nFP (fun p => p.1 == .flt && p.2)} fslice_params_by_value={nFP (fun p => p.1 == .fslice && !p.2)} fslice_params_inout={nFP (fun p => p.1 == .fslice && p.2)}"
  IO.println s!"slices_in_compared_inputs: total={lensSeen.length} len0={nLen (· == 0)} len1={nLen (· == 1)} len2to8={nLen (fun n => 2 ≤ n && n ≤ 8)} len9plus={nLen (· ≥ 9)}"
  IO.println s!"features: forN={cnt (· matches .forN ..)} loopB={cnt (· matches .loopB ..)} breaks={cnt (· matches .brk)} stores={cnt (· matches .store ..)} decls={cnt (· matches .decl ..)} ifs={cnt (· matches .ite ..)} assigns={cnt (· matches .assign ..)} calls={cnt (isCall false none)} calls_with_inout={cnt (isCall true none)} calls_not_exclusive={cnt (isCall false (some false))}"
  IO.println s!"params: int_by_value={np (·.1 == .intVal)} int_inout={np (·.1 == .intInout)} array_inout={np (·.1 == .arrInout)} array_by_value_read_only={np (·.1 == .arrRead)} array_by_value_private_copy={np (·.1 == .arrCopy)} (of_those_stored_into={np (fun p => p.1 == .arrCopy && p.2)} only_passed_inout={np (fun p => p.1 == .arrCopy && !p.2)})"

def mkCases (fns : List Fn) (elo ehi : Int) (n : Nat) (entryOnly : Bool) (maxLen : Nat := maxSliceLen) (samePct : Nat := 85)
    (fspecial : Option Nat := none) : G (List Case) := do
  let mut cases : List Case := []
  for k in [0:n] do
    let fi ← if entryOnly || k % 2 == 0 then pure 0 else rnd fns.length
    match fns[fi]? with
    | none => pure ()
    | some f =>
      -- float inputs: the share of special values (NaN, inf, zeros, subnormals, ...) varies per input
      let fsp ← match fspecial with | some p => pure p | none => pick 30 [0, 0, 10, 30, 60]
      let ab ← genArgs f.params elo ehi maxLen samePct fsp
      let args := ab.map (·.1)
      cases := cases ++ [{ fnIdx := fi, args := args, res := evalFn fns fi args, fbits := ab.map (·.2) }]
  pure cases

def progSeed (seed idx : Nat) : UInt64 :=
  let (_, s) := (nextU64 *> nextU64).run (UInt64.ofNat (seed * 1000003 + idx * 7919 + 1))
  s

def randomItem (seed idx ninputs : Nat) : Item :=
  let ((p, cases), _) := (do
    let p ← genProg s!"p{idx}_"
    let cases ← mkCases p.fns (-p.E) p.E ninputs false
    pure (p, cases)).run (progSeed seed idx)
  { id := idx, label := s!"random seed={seed} index={idx} E={p.E} risky={p.risky}", fns := p.fns, names := p.names, cases := cases }

/-- Inputs that are known to be outside the guarantee; the harness must skip them (see compare.py). -/
def knownStuck : List (String × List (List Val)) := [
  ("k3_lower_bound", [
    [.arr [1, 3, 5], .int 8, .int 100],                       -- wrong array length
    [.arr [1, 3, 5, 7, 9, 11, 13, 15], .int 9, .int 7],       -- n = 9 outside 0..=8
    [.arr [1, 3, 5, 7, 9, 11, 13, 15], .int 8, .int 1000001], -- p outside its range
    [.arr [1, 3, 5, 7, 9, 11, 13, 1000001], .int 8, .int 7]]),-- an element outside the element range
  ("rolling_sum", [
    [.arr [1, 2, 3], .int 5, .arr [0, 0]],                    -- len(out) < len(x): the store out[2] is stuck
    [.arr [1, 2, 3], .int 0, .arr [0, 0, 0]],                 -- w = 0 outside 1..=10^6
    [.arr [1, 2, 3], .int 1000001, .arr [0, 0, 0]],           -- w outside 1..=10^6
    [.arr [1, 1000000001, 3], .int 2, .arr [0, 0, 0]]]),      -- an element outside ±10^9
  ("prefix_sum", [
    [.arr [1, 2, 3], .arr [0, 0]],                            -- len(out) < len(x)
    [.arr [1, 2, -1000000001], .arr [0, 0, 0]],
    [.arr [1, 2, 3], .arr [0, 0, 1000000000000001]],          -- out's initial content outside its range
    [.arr [1, 2, 3], .int 0]]),
  ("ewma", [
    [.farr [1.0, 2.0, 3.0], .flt 0.5, .farr [0.0, 0.0]],      -- len(out) < len(x): outside `req`
    [.farr [1.0, 2.0, 3.0], .int 1, .farr [0.0, 0.0, 0.0]],   -- an integer where a float is expected
    [.arr [1, 2, 3], .flt 0.5, .farr [0.0, 0.0, 0.0]],        -- an integer array where a float slice is expected
    [.farr [1.0], .flt 0.5]]),
  ("dot", [
    [.farr [1.0, 2.0], .farr [1.0], .farr [0.0]],             -- len(x) != len(y)
    [.farr [1.0, 2.0], .farr [1.0, 2.0], .farr []],           -- len(out) = 0
    [.farr [1.0, 2.0], .int 3, .farr [0.0]],                  -- an integer where a float slice is expected
    [.farr [], .farr [], .farr []]])]

/-- The hand-written programs: the Tenon examples, then the K3 examples of emit3 moved to Tenon (`k3_` prefix). -/
def suiteExamples : List Example :=
  Examples.all ++ Tenon.Legacy.all.map fun ex =>
    { name := "k3_" ++ ex.name, fns := ex.fns, names := ex.names, elemLo := ex.elemLo, elemHi := ex.elemHi, proved := ex.proved }

def suiteItems (seed ninputs : Nat) : List Item :=
  (suiteExamples.zipIdx).map fun (ex, k) =>
    -- programs with long arrays get an eighth of the inputs (the C file holds every input as data)
    let long := ex.fns.any fun f => f.params.any fun p => match p.1 with | .arr n _ _ => n > 64 | _ => false
    let (cases, _) := (mkCases ex.fns ex.elemLo ex.elemHi (if long then ninputs / 8 else ninputs) true ex.maxLen ex.sameLen (some ex.fspecial)).run (progSeed seed k)
    let extra : List Case := ((knownStuck.filter (·.1 == ex.name)).foldl (fun l p => l ++ p.2) []).map fun a =>
      { fnIdx := 0, args := a, res := evalFn ex.fns 0 a }
    let names := ex.names.map fun nm => { nm with name := s!"p{k}_{nm.name}" }
    { id := k, label := s!"{ex.name} ({ex.proved})", fns := ex.fns, names := names, cases := extra ++ cases }

def parseForm : String → Option SelForm
  | "eager" => some .eager
  | "lazy" => some .lazy
  | "plain" => some .eagerPlain
  | "mask" => some .mask
  | _ => none

def main (argv : List String) : IO UInt32 := do
  let sabOf (l : List String) : Sabotage := (l.head?.bind parseSabotage).getD .none
  let formOf (l : List String) : SelForm := ((l.drop 1).head?.bind parseForm).getD .eager
  match argv with
  | "suite" :: outdir :: seed :: ninputs :: rest =>
    let items := suiteItems seed.toNat! ninputs.toNat!
    writeBatch outdir (sabOf rest) (formOf rest) items
    for it in items do
      let s := (it.cases.filter (·.res.isSome)).length
      IO.println s!"suite-program {it.id} some={s} none={it.cases.length - s} {it.label}"
    pure 0
  | "random" :: outdir :: seed :: nprogs :: ninputs :: rest =>
    writeBatch outdir (sabOf rest) (formOf rest) ((List.range nprogs.toNat!).map fun i => randomItem seed.toNat! i ninputs.toNat!)
    pure 0
  | ["show", seed, idx] =>
    let it := randomItem seed.toNat! idx.toNat! 0
    IO.println s!"-- {it.label}\n-- Tenon program (newest first); `triv` is `fun _ _ _ => True`\n["
    IO.println (",\n".intercalate (it.fns.map reprFn))
    IO.println "]\n"
    match emitProgram {} it.fns it.names with
    | .ok src => IO.println src
    | .error e => IO.println s!"emit error: {e}"
    pure 0
  | ["case", seed, idx, ninputs, ci] =>
    let it := randomItem seed.toNat! idx.toNat! ninputs.toNat!
    match it.cases[ci.toNat!]? with
    | some c => IO.println s!"evalFn prog {c.fnIdx} {reprArgs c.args}  =  {c.res.map fun (r, outs) => s!"({r}, {reprArgs outs})"}"
    | none => IO.println "no such case"
    pure 0
  | _ =>
    IO.eprintln "usage: difftest suite <outdir> <seed> <ninputs> [sabotage [eager|plain|lazy|mask]] | random <outdir> <seed> <nprogs> <ninputs> [sabotage [eager|plain|lazy|mask]] | show <seed> <index> | case <seed> <index> <ninputs> <case>"
    pure 2
