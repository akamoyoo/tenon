import Tenon
/-! C code generator for Tenon programs (K4 plus floats and `loopE`). NOT PROVED: this file is ordinary, untrusted Lean code that prints
    C text. Its only evidence of correctness is the differential test in `difftest/`.

    Entry point: `Tenon.Emit.emitProgram : Options → List Fn → List FnNames → Except String String`.

    The generated C contains no run-time checks. It is meant to be run only on inputs for which
    `evalFn` is `some` (which `prog_sound` guarantees for a checked program called within its parameter
    types and precondition). Every place that depends on that is marked "RELIES ON T2" below.

    Parameter passing:
      by-value integer              int64_t x
      inout integer                 int64_t *x_io; the body works on a local `x` loaded at entry and
                                    stored back once, just before `return`
      by-value array, not modified  const int64_t *restrict a
      by-value array, modified      const int64_t *restrict a_arg, and a private copy `a` made at entry
      inout array                   int64_t *restrict a; the body writes in place
      by-value slice, not modified  const int64_t *restrict a, int64_t a_len
      by-value slice, modified      const int64_t *restrict a_arg, int64_t a_len, and a private heap copy
      inout slice                   int64_t *restrict a, int64_t a_len; the body writes in place
    "modified" means: the body stores into it, or passes it as `inout` to a call.
      by-value float                double x;  inout float: double *x_io (copy in, copy out)
      float slice                   as an integer slice, with `double` for `int64_t`
    A slice is a pointer and a length; `len a` reads the length parameter (RELIES ON the caller passing
    the true length, 0 ≤ length ≤ 2^63-1: that is the meaning of `Val.has _ (.slice ..)`). -/

namespace Tenon.Emit
open Tenon

/-- Names for one function. Tenon has no names, so the caller supplies them. -/
structure FnNames where
  name   : String
  params : List String                 -- one per parameter, in order
  result : String := "result"
  /-- Names for `decl` variables and `forN` counters, in order of appearance in the body (pre-order,
      then-branch before else-branch). `loopB` has no counter and takes no name. Missing names are
      generated (`x1`, `i1`, ...). -/
  locals : List String := []

/-- Deliberate emitter breakages, used ONLY by the self-tests of the differential test, which must
    detect each of them. `none` is the emitter. -/
inductive Sabotage where
  | none
  | lt              -- `ite a b` tests `a < b` instead of `a <= b`
  | noCopy          -- a modified by-value array works on the caller's array instead of a private copy
  | counter         -- a `forN` whose body modifies its counter uses that variable as the real counter
  | noWriteBack     -- an inout integer is not stored back at function exit
  | inoutCopy       -- an inout array is treated like a modified by-value array (the callee writes a copy)
  | loopBOnce       -- a `loopB` body runs at most once
  | loopBShort      -- a `loopB n` is emitted as a counted loop of n - 2 iterations (n - 1 would be
                    -- unobservable whenever the last iteration only executes `brk`)
  | selSwap         -- `sel c t e` selects `e` when c ≠ 0
  | selTruthy       -- `sel c t e` tests `c == 1` instead of `c != 0`
  | ltAsLe          -- `lt a b` is emitted as `a <= b`
  | eqAsLe          -- `eq a b` is emitted as `a <= b`
  | leAsLt          -- `le a b` is emitted as `a < b`
  | lenOff          -- `len a` of a slice is one too large
  | forEReeval      -- the bound of a `forE` is evaluated again before every iteration
  | forEShort       -- a `forE` runs one iteration less
  | sliceNoCopy     -- a modified by-value slice works on the caller's buffer
  | fma             -- `a * b + c` and `c + a * b` on floats are emitted as `fma(a, b, c)`
  | reassoc         -- `(a + b) + c` on floats is emitted as `a + (b + c)`
  | selLeNaN        -- `selLe a b t e` is emitted as `!(a > b) ? t : e`, and `fite a b s t` as
                    -- `if (a > b) t else s`: right unless a or b is NaN
  | fleAsLt         -- float `a <= b` (in `selLe` and `fite`) is emitted as `a < b`
  | fselSwap        -- float `sel c t e` selects `e` when c ≠ 0
  | ofIntF32        -- `ofInt e` converts through `float`
  | sqrtF32         -- `sqrt` is computed in single precision
  | absDrop         -- `abs x` is emitted as `x < 0 ? -x : x` (wrong for -0.0 and for NaN signs)
  | negSub          -- `neg x` is emitted as `0.0 - x` (wrong for +0.0)
  | loopEEval       -- a `loopE e` is emitted as a counted loop of e - 2 iterations
  deriving DecidableEq, Repr

/-- How `sel c t e` is written in C.
    `eager` (default): a call of the inline function `tn_sel(c, t, e)`, whose body is
       `TENON_UNPREDICTABLE(c) ? t : e`. Both arms are evaluated before the selection, as in Tenon, so loads
       in the arms are unconditional and the compiler is free to use a conditional move. RELIES ON
       T2: both arms are not stuck. `TENON_UNPREDICTABLE` is `__builtin_unpredictable` under clang:
       without it clang 21 turns the conditional move of the binary search back into a branch
       (measured in bench/; README.md).
    `eagerPlain`: the same without the hint.
    `lazy`: the C expression `(c ? t : e)`. Only one arm is evaluated; a compiler may not turn an arm
       that loads from memory into a conditional move.
    `mask`: `tn_selm`, bit operations with an all-ones or all-zeros mask; no `?:` at all. -/
inductive SelForm where
  | eager | eagerPlain | lazy | mask
  deriving DecidableEq, Repr

structure Options where
  selForm : SelForm := .eager
  /-- `div a b` is emitted as an unsigned 64-bit division (`tn_div`). RELIES ON T2: `div` is stuck
      unless a ≥ 0 and b > 0, so the unsigned and the signed quotient agree. With `false` a plain signed
      `/` is emitted (also correct, slower for division by a constant). -/
  unsignedDiv : Bool := true
  /-- Emit `static` on every function except function 0 (the newest). -/
  staticHelpers : Bool := false
  /-- Emit the `#include` lines and the helper functions. With `false` only the functions are
      printed (for a file that holds several programs; see `fullPrelude`). -/
  prelude : Bool := true
  /-- Text placed before the function definitions (after the includes), e.g. a banner comment. -/
  banner : String := ""
  sabotage : Sabotage := .none

/-- What the emitter knows about one environment position. All integers are C locals of type
    `int64_t` (parameters included), so `&x` is always available for an inout argument.
    `writable`: the C expression has type `int64_t *` (inout parameter or private copy), not
    `const int64_t *`. -/
inductive Slot where
  | int (cname : String)
  | arr (cname : String) (len : Nat) (writable : Bool)
  | slice (cname : String) (lenName : String) (writable : Bool)   -- pointer and the C variable holding the length
  | flt (cname : String)
  | fslice (cname : String) (lenName : String) (writable : Bool)

def Slot.cname : Slot → String
  | .int c | .arr c _ _ | .slice c _ _ | .flt c | .fslice c _ _ => c

def Slot.kind : Slot → String
  | .int _ => "an integer" | .arr .. => "an array" | .slice .. => "a slice"
  | .flt _ => "a float" | .fslice .. => "a float slice"

/-- A callee as seen from a call site. -/
structure Sig where
  cname  : String
  params : List (Ty × Bool)

/-! ## Syntactic analyses -/

/-- May `s` change the array at position `k` (where `s` starts)? A `store` into it, or passing it as
    an `inout` argument. This is `Tenon.mods` restricted to what matters for arrays; the emitter keeps
    its own copy because it must not depend on how the kernel uses `mods` in its proofs. -/
def modsArr : Stmt → Nat → Bool
  | .skip, _ | .brk, _ | .assign .., _ | .fassign .., _ => false
  | .fstore a _ _, k => a == k
  | .fdecl _ s, k => modsArr s (k + 1)
  | .fite _ _ s t, k => modsArr s k || modsArr t k
  | .loopE _ _ s, k => modsArr s k
  | .note _ s, k => modsArr s k
  | .pmap _ _ _ out, k | .pmapF _ _ _ out, k => out == k
  | .seq s t, k => modsArr s k || modsArr t k
  | .store a _ _, k => a == k
  | .ite _ _ s t, k => modsArr s k || modsArr t k
  | .decl _ _ _ s, k => modsArr s (k + 1)
  | .forN _ _ s, k => modsArr s (k + 1)
  | .forE _ _ s, k => modsArr s (k + 1)
  | .loopB _ _ s, k => modsArr s k
  | .call _ args _, k => args.any (fun a => a.2 && a.1 == k)

/-- Only the `store` part of `modsArr` (for statistics). -/
def storesInto : Stmt → Nat → Bool
  | .skip, _ | .brk, _ | .assign .., _ | .call .., _ | .fassign .., _ => false
  | .fstore a _ _, k => a == k
  | .fdecl _ s, k => storesInto s (k + 1)
  | .fite _ _ s t, k => storesInto s k || storesInto t k
  | .loopE _ _ s, k => storesInto s k
  | .note _ s, k => storesInto s k
  | .pmap _ _ _ out, k | .pmapF _ _ _ out, k => out == k
  | .seq s t, k => storesInto s k || storesInto t k
  | .store a _ _, k => a == k
  | .ite _ _ s t, k => storesInto s k || storesInto t k
  | .decl _ _ _ s, k => storesInto s (k + 1)
  | .forN _ _ s, k => storesInto s (k + 1)
  | .forE _ _ s, k => storesInto s (k + 1)
  | .loopB _ _ s, k => storesInto s k

/-- May `s` change the integer at position `k`: an `assign`, a call's destination, or an `inout`
    argument. Used for `forN` counters. -/
def modsInt : Stmt → Nat → Bool
  | .skip, _ | .brk, _ | .store .., _ | .fassign .., _ | .fstore .., _ => false
  | .fdecl _ s, k => modsInt s (k + 1)
  | .fite _ _ s t, k => modsInt s k || modsInt t k
  | .loopE _ _ s, k => modsInt s k
  | .note _ s, k => modsInt s k
  | .pmap _ _ _ _, _ | .pmapF _ _ _ _, _ => false
  | .seq s t, k => modsInt s k || modsInt t k
  | .assign x _, k => x == k
  | .ite _ _ s t, k => modsInt s k || modsInt t k
  | .decl _ _ _ s, k => modsInt s (k + 1)
  | .forN _ _ s, k => modsInt s (k + 1)
  | .forE _ _ s, k => modsInt s (k + 1)
  | .loopB _ _ s, k => modsInt s k
  | .call _ args dst, k => dst == k || args.any (fun a => a.2 && a.1 == k)

/-- Does the expression contain a node satisfying `p`? -/
def exprAny (p : Expr → Bool) : Expr → Bool
  | .lit n => p (.lit n)
  | .var i => p (.var i)
  | .len a => p (.len a)
  | .add a b => p (.add a b) || exprAny p a || exprAny p b
  | .sub a b => p (.sub a b) || exprAny p a || exprAny p b
  | .mul a b => p (.mul a b) || exprAny p a || exprAny p b
  | .div a b => p (.div a b) || exprAny p a || exprAny p b
  | .le a b => p (.le a b) || exprAny p a || exprAny p b
  | .lt a b => p (.lt a b) || exprAny p a || exprAny p b
  | .eq a b => p (.eq a b) || exprAny p a || exprAny p b
  | .idx a e => p (.idx a e) || exprAny p e
  | .sel c t e => p (.sel c t e) || exprAny p c || exprAny p t || exprAny p e

/-- Does an integer sub-expression of the float expression contain a node satisfying `p`? -/
def fexprAnyE (p : Expr → Bool) : FExpr → Bool
  | .lit _ | .var _ => false
  | .add a b | .sub a b | .mul a b | .div a b => fexprAnyE p a || fexprAnyE p b
  | .idx _ e | .ofInt e => exprAny p e
  | .sel c t e => exprAny p c || fexprAnyE p t || fexprAnyE p e
  | .neg a | .abs a | .sqrt a => fexprAnyE p a
  | .selLe a b t e => fexprAnyE p a || fexprAnyE p b || fexprAnyE p t || fexprAnyE p e

/-- Does the float expression contain a node satisfying `p`? -/
def fexprAny (p : FExpr → Bool) : FExpr → Bool
  | .lit f => p (.lit f)
  | .var i => p (.var i)
  | .idx a e => p (.idx a e)
  | .ofInt e => p (.ofInt e)
  | .add a b => p (.add a b) || fexprAny p a || fexprAny p b
  | .sub a b => p (.sub a b) || fexprAny p a || fexprAny p b
  | .mul a b => p (.mul a b) || fexprAny p a || fexprAny p b
  | .div a b => p (.div a b) || fexprAny p a || fexprAny p b
  | .sel c t e => p (.sel c t e) || fexprAny p t || fexprAny p e
  | .neg a => p (.neg a) || fexprAny p a
  | .abs a => p (.abs a) || fexprAny p a
  | .sqrt a => p (.sqrt a) || fexprAny p a
  | .selLe a b t e => p (.selLe a b t e) || fexprAny p a || fexprAny p b || fexprAny p t || fexprAny p e

def stmtAnyF (p : FExpr → Bool) : Stmt → Bool
  | .skip | .brk | .call .. | .assign .. | .store .. => false
  | .seq s t | .ite _ _ s t => stmtAnyF p s || stmtAnyF p t
  | .decl _ _ _ s | .forN _ _ s | .forE _ _ s | .loopB _ _ s | .loopE _ _ s | .note _ s => stmtAnyF p s
  | .pmap _ _ _ _ | .pmapF _ _ _ _ => false
  | .fassign _ e | .fstore _ _ e => fexprAny p e
  | .fdecl e s => fexprAny p e || stmtAnyF p s
  | .fite a b s t => fexprAny p a || fexprAny p b || stmtAnyF p s || stmtAnyF p t

def stmtAnyE (p : Expr → Bool) : Stmt → Bool
  | .fassign _ e => fexprAnyE p e
  | .fstore _ i e => exprAny p i || fexprAnyE p e
  | .fdecl e s => fexprAnyE p e || stmtAnyE p s
  | .fite a b s t => fexprAnyE p a || fexprAnyE p b || stmtAnyE p s || stmtAnyE p t
  | .loopE e _ s => exprAny p e || stmtAnyE p s
  | .note _ s => stmtAnyE p s
  | .pmap _ _ e _ | .pmapF _ _ e _ => exprAny p e
  | .skip | .brk | .call .. => false
  | .seq s t => stmtAnyE p s || stmtAnyE p t
  | .assign _ e => exprAny p e
  | .store _ i e => exprAny p i || exprAny p e
  | .ite a b s t => exprAny p a || exprAny p b || stmtAnyE p s || stmtAnyE p t
  | .decl _ _ e s => exprAny p e || stmtAnyE p s
  | .forN _ _ s => stmtAnyE p s
  | .forE e _ s => exprAny p e || stmtAnyE p s
  | .loopB _ _ s => stmtAnyE p s

def exprUsesDiv : Expr → Bool := exprAny (· matches .div ..)

def stmtUsesDiv : Stmt → Bool := stmtAnyE (· matches .div ..)
def stmtUsesSel : Stmt → Bool := stmtAnyE (· matches .sel ..)
def stmtUsesFSel : Stmt → Bool := stmtAnyF (fun e => e matches .sel .. || e matches .selLe ..)
def stmtUsesMath : Stmt → Bool := stmtAnyF (fun e => e matches .sqrt .. || e matches .abs ..)
def isFinite (f : Float) : Bool := !f.isNaN && !f.isInf
def stmtUsesBits : Stmt → Bool := stmtAnyF (fun e => match e with | .lit f => !isFinite f | _ => false)
def stmtUsesFloat : Stmt → Bool
  | .skip | .brk | .call .. | .assign .. | .store .. => false
  | .seq s t | .ite _ _ s t => stmtUsesFloat s || stmtUsesFloat t
  | .decl _ _ _ s | .forN _ _ s | .forE _ _ s | .loopB _ _ s | .loopE _ _ s | .note _ s => stmtUsesFloat s
  | .pmap _ _ _ _ => false
  | .pmapF _ _ _ _ => true
  | .fassign .. | .fstore .. | .fdecl .. | .fite .. => true

/-! ## Expressions -/

def i64Min : Int := -9223372036854775808
def i64Max : Int := 9223372036854775807

/-- A literal as a C constant expression of a type at least as wide as needed. -/
def litC (n : Int) : Except String String :=
  if n < i64Min ∨ n > i64Max then
    .error s!"literal {n} is outside int64_t (always stuck in Tenon)"
  else if n == i64Min then .ok "INT64_MIN"
  else .ok (toString n)

def paren (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

/-- A rendered expression. `wide`: its C type is certainly `int64_t` (or `long` on LP64); `false` for
    a decimal literal that may have type `int`. Arithmetic on two narrow operands would be done in
    `int`, so `binC` widens the left operand in that case. -/
structure CE where
  s    : String
  wide : Bool
  lit  : Option Int := none
  cond : Option String := none        -- for a comparison: the bare C condition

/-- Force the C type to be 64 bits wide. -/
def CE.w (e : CE) : String :=
  if e.wide then e.s else match e.lit with
    | some n => s!"INT64_C({n})"
    | none => s!"(int64_t){e.s}"

/-- Join two rendered operands of a binary arithmetic operator. -/
def binC (op : String) (a b : CE) (level prec : Nat) : CE :=
  let sa := if !a.wide && !b.wide then a.w else a.s
  { s := paren (prec > level) s!"{sa} {op} {b.s}", wide := true }

/-- `prec`: 0 = statement level / argument, 1 = operand of + or -, 2 = operand of * or /,
    3 = must be atomic. The shape of the Tenon expression is kept exactly (no reassociation), because C
    signed overflow in an intermediate result would be undefined and Tenon only promises that the
    intermediates *of this shape* fit. RELIES ON T2: every add/sub/mul result fits int64_t.
    Expressions have no side effects and contain no calls, so C evaluation order is irrelevant. -/
def exprC (opts : Options) (env : List Slot) : Expr → Nat → Except String CE
  | .lit n, prec => do
    let s ← litC n
    -- a negative literal as an operand is parenthesised: `a - (-1)`, never `a - -1`
    pure { s := paren (n < 0 && prec > 0 && n != i64Min) s, wide := n == i64Min,
           lit := if n == i64Min then none else some n }
  | .var i, _ =>
    -- RELIES ON T2 (through `evalE`'s `inI64` check on reads): the value fits int64_t.
    match env[i]? with
    | some (.int c) => pure { s := c, wide := true }
    | some sl => .error s!"var {i}: `{sl.cname}` is {sl.kind}, not an integer"
    | none => .error s!"var {i}: no such variable"
  | .add a b, prec => do
    pure (binC "+" (← exprC opts env a 1) (← exprC opts env b 2) 1 prec)
  | .sub a b, prec => do
    pure (binC "-" (← exprC opts env a 1) (← exprC opts env b 2) 1 prec)
  | .mul a b, prec => do
    pure (binC "*" (← exprC opts env a 2) (← exprC opts env b 3) 2 prec)
  | .div a b, prec => do
    if opts.unsignedDiv then
      let sa ← exprC opts env a 0
      let sb ← exprC opts env b 0
      pure { s := s!"tn_div({sa.s}, {sb.s})", wide := true }
    else
      pure (binC "/" (← exprC opts env a 2) (← exprC opts env b 3) 2 prec)
  | .idx a e, _ => do
    -- RELIES ON T2: 0 ≤ e < length (for a slice: the run-time length). No bounds check.
    match env[a]? with
    | some (.arr c _ _) | some (.slice c _ _) =>
      let se ← exprC opts env e 0; pure { s := s!"{c}[{se.s}]", wide := true }
    | some sl => .error s!"idx {a}: `{sl.cname}` is {sl.kind}, not an integer array"
    | none => .error s!"idx {a}: no such variable"
  | .len a, prec =>
    match env[a]? with
    | some (.arr _ n _) => pure { s := toString n, wide := false, lit := some n }
    | some (.slice _ ln _) | some (.fslice _ ln _) =>
      if opts.sabotage == .lenOff then pure { s := paren (prec > 1) s!"{ln} + 1", wide := true }
      else pure { s := ln, wide := true }
    | some sl => .error s!"len {a}: `{sl.cname}` is {sl.kind}, not an array"
    | none => .error s!"len {a}: no such variable"
  -- Comparisons: C gives an `int` 0 or 1; the cast makes the type int64_t whatever the context.
  | .le a b, _ => do
    let op := if opts.sabotage == .leAsLt then "<" else "<="
    let c := s!"{(← exprC opts env a 1).s} {op} {(← exprC opts env b 1).s}"
    pure { s := s!"(int64_t)({c})", wide := true, cond := some c }
  | .lt a b, _ => do
    let op := if opts.sabotage == .ltAsLe then "<=" else "<"
    let c := s!"{(← exprC opts env a 1).s} {op} {(← exprC opts env b 1).s}"
    pure { s := s!"(int64_t)({c})", wide := true, cond := some c }
  | .eq a b, _ => do
    let op := if opts.sabotage == .eqAsLe then "<=" else "=="
    let c := s!"{(← exprC opts env a 1).s} {op} {(← exprC opts env b 1).s}"
    pure { s := s!"(int64_t)({c})", wide := true, cond := some c }
  | .sel c t e, _ => do
    -- The condition as a C truth value: a comparison is used directly, anything else is `!= 0`.
    let sc ← exprC opts env c 1
    let cond := match sc.cond with
      | some s => s
      | none => if opts.sabotage == Sabotage.selTruthy then s!"{sc.s} == 1" else s!"{sc.s} != 0"
    let st ← exprC opts env t 0
    let se ← exprC opts env e 0
    let (st, se) := if opts.sabotage == .selSwap then (se, st) else (st, se)
    match opts.selForm with
    | .eager =>
      -- RELIES ON T2: `sel` is stuck unless both arms evaluate, so evaluating both in C is defined
      -- (no out-of-range load, no overflow) even for the arm that is not selected.
      pure { s := s!"tn_sel({cond}, {st.s}, {se.s})", wide := true }
    | .eagerPlain => pure { s := s!"tn_selp({cond}, {st.s}, {se.s})", wide := true }
    | .mask => pure { s := s!"tn_selm({cond}, {st.s}, {se.s})", wide := true }
    | .lazy =>
      -- one arm widened so that the result type is int64_t even for two small literals
      pure { s := s!"({cond} ? ({st.w}) : ({se.s}))", wide := true }

/-! ## Float expressions

Tenon floats are IEEE-754 binary64 and every operation is the IEEE operation, in the order the term gives.
The C keeps the term's shape exactly (same parenthesisation as for integers) and uses only `+ - * /`,
unary minus, `fabs`, `sqrt`, conversions from `int64_t` and comparisons, each of which is the IEEE
operation on a platform where `double` is binary64 evaluated in double precision (x86-64 SSE2; the
prelude refuses `FLT_EVAL_METHOD != 0` and `__FAST_MATH__`). What the C text cannot enforce is that the
COMPILER does not contract `a * b + c` into a fused multiply-add or reassociate: that needs
`-ffp-contract=off` and no fast-math option (README.md, "Compiler flags"). Float operations are never
stuck, so nothing here relies on the theorem except the index of `idx`. -/

def hexPad (n width : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (width - d.length) '0' ++ d)

/-- The 52 mantissa bits as hexadecimal fraction digits, without trailing zeros. -/
def hexFrac (m : Nat) : String :=
  String.ofList ((hexPad m 13).toList.reverse.dropWhile (· == '0')).reverse

/-- A double as a C constant expression with exactly that value: small integers in decimal, other
    finite values as hexadecimal floating constants (exact by construction), infinities and NaN through
    `tn_bits`. Lean's `Float.toBits` gives every NaN the bit pattern 0x7ff8000000000000, so a NaN literal
    is always emitted as that one. -/
def flitC (f : Float) : String :=
  let b := f.toBits.toNat
  let sign := if b ≥ 2 ^ 63 then "-" else ""
  let ex := (b / 2 ^ 52) % 2048
  let m := b % 2 ^ 52
  if ex == 2047 then s!"tn_bits(UINT64_C(0x{hexPad b 16}))"
  else if ex == 0 && m == 0 then sign ++ "0.0"
  else if ex == 0 then s!"{sign}0x0.{hexFrac m}p-1022"
  else
    let en : Nat := ex - 1023
    if ex ≥ 1023 && en ≤ 52 && m % 2 ^ (52 - en) == 0 then s!"{sign}{(2 ^ 52 + m) / 2 ^ (52 - en)}.0"
    else if m == 0 then s!"{sign}0x1p{(ex : Int) - 1023}"
    else s!"{sign}0x1.{hexFrac m}p{(ex : Int) - 1023}"

/-- The C truth value of an integer condition (for `sel`). -/
def condC (opts : Options) (env : List Slot) (c : Expr) : Except String String := do
  let sc ← exprC opts env c 1
  pure (match sc.cond with
    | some s => s
    | none => if opts.sabotage == Sabotage.selTruthy then s!"{sc.s} == 1" else s!"{sc.s} != 0")

/-- How a float select is written, by `Options.selForm` (same four forms as the integer `sel`). -/
def fselC (opts : Options) (cond t e : String) : String :=
  match opts.selForm with
  | .eager => s!"tn_fsel({cond}, {t}, {e})"
  | .eagerPlain => s!"tn_fselp({cond}, {t}, {e})"
  | .mask => s!"tn_fselm({cond}, {t}, {e})"
  | .lazy => s!"({cond} ? {t} : {e})"

/-- `prec` as in `exprC`. No reassociation, no contraction, no reordering of operands: `a + b` is
    printed as `a + b` (NaN payloads could otherwise differ; values could not). Unlike for integers,
    BOTH operands of a float operator are parenthesised when they are operators of the same class:
    `(a + b) + c`, `(a * b) / c`. C would parse `a + b + c` the same way; the parentheses make the
    order of the rounding steps visible in the text. -/
partial def fexprC (opts : Options) (env : List Slot) : FExpr → Nat → Except String String
  | .lit f, prec => let s := flitC f; pure (paren (s.startsWith "-" && prec > 0) s)
  | .var i, _ =>
    match env[i]? with
    | some (.flt c) => pure c
    | some sl => .error s!"float var {i}: `{sl.cname}` is {sl.kind}, not a float"
    | none => .error s!"float var {i}: no such variable"
  | .add a b, prec => do
    if opts.sabotage == .fma then
      match a, b with
      | .mul x y, _ => return s!"fma({← fexprC opts env x 0}, {← fexprC opts env y 0}, {← fexprC opts env b 0})"
      | _, .mul x y => return s!"fma({← fexprC opts env x 0}, {← fexprC opts env y 0}, {← fexprC opts env a 0})"
      | _, _ => pure ()
    if opts.sabotage == .reassoc then
      match a with
      | .add x y => return paren (prec > 1) s!"{← fexprC opts env x 2} + ({← fexprC opts env y 2} + {← fexprC opts env b 2})"
      | _ => pure ()
    pure (paren (prec > 1) s!"{← fexprC opts env a 2} + {← fexprC opts env b 2}")
  | .sub a b, prec => do
    if opts.sabotage == .fma then
      match a with
      | .mul x y => return s!"fma({← fexprC opts env x 0}, {← fexprC opts env y 0}, -({← fexprC opts env b 0}))"
      | _ => pure ()
    pure (paren (prec > 1) s!"{← fexprC opts env a 2} - {← fexprC opts env b 2}")
  | .mul a b, prec => do pure (paren (prec > 2) s!"{← fexprC opts env a 3} * {← fexprC opts env b 3}")
  | .div a b, prec => do pure (paren (prec > 2) s!"{← fexprC opts env a 3} / {← fexprC opts env b 3}")
  | .idx a e, _ => do
    -- RELIES ON T2: 0 ≤ e < the run-time length. No bounds check.
    match env[a]? with
    | some (.fslice c _ _) => let se ← exprC opts env e 0; pure s!"{c}[{se.s}]"
    | some sl => .error s!"float idx {a}: `{sl.cname}` is {sl.kind}, not a float slice"
    | none => .error s!"float idx {a}: no such variable"
  | .ofInt e, _ => do
    -- int64_t to double: rounds to nearest even, as `Float.ofInt` does on the int64 range.
    let se ← exprC opts env e 3
    pure (if opts.sabotage == .ofIntF32 then s!"(double)(float){se.s}" else s!"(double){se.s}")
  | .sel c t e, _ => do
    -- RELIES ON T2 only through the integer condition and the indices inside the arms: both arms
    -- are evaluated in Tenon as well.
    let cond ← condC opts env c
    let st ← fexprC opts env t 0
    let se ← fexprC opts env e 0
    let (st, se) := if opts.sabotage == .selSwap || opts.sabotage == .fselSwap then (se, st) else (st, se)
    pure (fselC opts cond st se)
  | .neg a, prec => do
    -- unary minus flips the sign bit, also of a zero and of a NaN
    if opts.sabotage == .negSub then return s!"(0.0 - {← fexprC opts env a 2})"
    pure (paren (prec > 0) s!"-{← fexprC opts env a 3}")
  | .abs a, _ => do
    if opts.sabotage == .absDrop then
      let sa ← fexprC opts env a 1
      return s!"({sa} < 0.0 ? -({sa}) : {sa})"
    pure s!"fabs({← fexprC opts env a 0})"
  | .sqrt a, _ => do
    if opts.sabotage == .sqrtF32 then return s!"(double)sqrtf((float){← fexprC opts env a 3})"
    pure s!"sqrt({← fexprC opts env a 0})"
  | .selLe a b t e, _ => do
    -- `a <= b` is false when either is NaN, in C as in Tenon (not under -ffinite-math-only).
    let sa ← fexprC opts env a 1
    let sb ← fexprC opts env b 1
    let st ← fexprC opts env t 0
    let se ← fexprC opts env e 0
    let cond := match opts.sabotage with
      | .selLeNaN => s!"!({sa} > {sb})"
      | .fleAsLt => s!"{sa} < {sb}"
      | _ => s!"{sa} <= {sb}"
    pure (fselC opts cond st se)

/-! ## Statements -/

structure St where
  used   : List String                 -- C identifiers already taken in this function
  locals : List String                 -- user-supplied names not yet consumed
  nDecl  : Nat := 0
  nLoop  : Nat := 0

abbrev M := StateT St (Except String)

def validIdent (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => c.isAlphanum || c == '_') && !(s.toList.head?.any Char.isDigit)

def cKeywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else", "enum",
   "extern", "float", "for", "goto", "if", "inline", "int", "long", "register", "restrict", "return",
   "short", "signed", "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned", "void",
   "volatile", "while", "int64_t", "uint64_t", "memcpy", "malloc", "free", "abort", "tn_div", "tn_sel",
   "tn_selm", "tn_selp", "TENON_UNPREDICTABLE", "tn_copy", "main", "INT64_MIN", "INT64_C", "NULL",
   "tn_fsel", "tn_fselp", "tn_fselm", "tn_fcopy", "tn_bits", "fabs", "sqrt", "sqrtf", "fma", "UINT64_C", "size_t"]

/-- Make `base` unique among the names used so far and reserve it. -/
def reserve (base : String) : M String := do
  let st ← get
  let rec go (fuel k : Nat) : String :=
    let cand := if k == 0 then base else s!"{base}_{k + 1}"
    match fuel with
    | 0 => cand
    | fuel + 1 => if st.used.contains cand then go fuel (k + 1) else cand
  let name := go (st.used.length + 1) 0
  set { st with used := name :: st.used }
  pure name

/-- Name for a new `decl` variable (`loop = false`) or loop counter (`loop = true`). -/
def freshLocal (loop : Bool) : M String := do
  let st ← get
  match st.locals with
  | n :: rest =>
    if !validIdent n then throw s!"`{n}` is not a C identifier"
    set { st with locals := rest }
    reserve n
  | [] =>
    if loop then
      set { st with nLoop := st.nLoop + 1 }; reserve s!"i{st.nLoop + 1}"
    else
      set { st with nDecl := st.nDecl + 1 }; reserve s!"x{st.nDecl + 1}"

def ind (n : Nat) (s : String) : String := "".pushn ' ' (4 * n) ++ s

def liftE {α} (e : Except String α) : M α := match e with
  | .ok a => pure a
  | .error m => throw m

/-- The statement always ends by executing `brk`. -/
def endsInBrk : Stmt → Bool
  | .brk => true
  | .seq _ t => endsInBrk t
  | _ => false

/-- The C argument list of a call, or an error if the call is ill-shaped. -/
def callArgsC (env : List Slot) (sig : Sig) (args : List (Nat × Bool)) : Except String (List String) := do
  if sig.params.length != args.length then
    throw s!"call {sig.cname}: {args.length} arguments for {sig.params.length} parameters"
  (args.zip sig.params).mapM fun ((i, io), (ty, pio)) => do
    -- `evalFn` writes back whatever the CALL SITE marks inout, whether or not the parameter is
    -- declared inout (see KernelFindings.lean, G1). A checked program has them equal (`argsTyped`).
    -- The emitter only supports that case.
    if io != pio then
      throw s!"call {sig.cname}: argument {i} is {if io then "" else "not "}marked inout but the parameter is {if pio then "" else "not "}inout (rejected by `argsTyped`)"
    -- An inout argument must have exactly the parameter's type (`argsTyped`), so array to array of
    -- the same length, slice to slice. By value, Tenon only asks that the VALUE has the parameter's
    -- type: an array may be passed where a slice is expected (its length is the constant), and a
    -- slice where an array is expected (RELIES ON T2: its run-time length is the array length).
    match env[i]?, ty with
    | some (.int c), .int _ _ => pure (if io then s!"&{c}" else c)
    | some (.arr c n w), .arr m _ _ =>
      if n != m then throw s!"call {sig.cname}: array `{c}` has length {n}, expected {m}"
      else if io && !w then throw s!"internal: inout argument `{c}` is not writable"
      else pure c
    | some (.slice c ln w), .slice _ _ =>
      if io && !w then throw s!"internal: inout argument `{c}` is not writable"
      else pure s!"{c}, {ln}"
    | some (.arr c n _), .slice _ _ =>
      if io then throw s!"call {sig.cname}: array `{c}` passed inout to a slice parameter (rejected by `argsTyped`)"
      else pure s!"{c}, {n}"
    | some (.slice c _ _), .arr _ _ _ =>
      if io then throw s!"call {sig.cname}: slice `{c}` passed inout to an array parameter (rejected by `argsTyped`)"
      else pure c
    | some (.flt c), .flt => pure (if io then s!"&{c}" else c)
    | some (.fslice c ln w), .fslice =>
      if io && !w then throw s!"internal: inout argument `{c}` is not writable"
      else pure s!"{c}, {ln}"
    | some _, _ => throw s!"call {sig.cname}: argument {i} has the wrong kind"
    | none, _ => throw s!"call {sig.cname}: no variable at position {i}"

/-- A parallel map. Each iteration calls the callee with the by-value arguments and the index, and
    writes element i of `out`; nothing else is written. RELIES ON T2 (the callee's parameters other than
    the result are by value, `out` is not among the arguments, the bound is between 0 and len(out), and
    every call satisfies the callee's requirement) and on `parallel_writes` (writes to distinct elements
    in any order give the semantics' result). Without OpenMP the pragma is ignored and the loop runs in
    order, which by the same theorem gives the same result. -/
def pmapC (opts : Options) (callees : List Sig) (f : Nat) (args : List Nat) (e : Expr) (out : Nat)
    (env : List Slot) (d : Nat) (isFloat : Bool) : M (List String) := do
  match callees[f]? with
  | none => throw s!"parallel map {f}: no such earlier function"
  | some sig =>
    let k := if isFloat then 2 else 1
    if sig.params.length != args.length + k then
      throw s!"parallel map {sig.cname}: {args.length} arguments for {sig.params.length - k} parameters"
    let cs ← liftE (callArgsC env { cname := sig.cname, params := sig.params.take args.length }
      (args.map fun a => (a, false)))
    let se := (← liftE (exprC opts env e 0)).s
    let i ← reserve "tn_i"
    let n ← reserve "tn_n"
    match env[out]?, isFloat with
    | some (.slice c _ true), false =>
      pure [ind d "{",
            ind (d + 1) s!"int64_t {n} = {se};",
            ind (d + 1) "#pragma omp parallel for schedule(static)",
            ind (d + 1) s!"for (int64_t {i} = 0; {i} < {n}; {i}++)",
            ind (d + 2) s!"{c}[{i}] = {sig.cname}({", ".intercalate (cs ++ [i])});",
            ind d "}"]
    | some (.fslice c _ true), true =>
      pure [ind d "{",
            ind (d + 1) s!"int64_t {n} = {se};",
            ind (d + 1) "#pragma omp parallel for schedule(static)",
            ind (d + 1) s!"for (int64_t {i} = 0; {i} < {n}; {i}++) \{",
            ind (d + 2) "double tn_r = 0.0;",
            ind (d + 2) s!"{sig.cname}({", ".intercalate (cs ++ [i, "&tn_r"])});",
            ind (d + 2) s!"{c}[{i}] = tn_r;",
            ind (d + 1) "}",
            ind d "}"]
    | some sl, _ => throw s!"parallel map {sig.cname}: `{sl.cname}` is not a writable {if isFloat then "float " else ""}slice"
    | none, _ => throw s!"parallel map {sig.cname}: no variable at position {out}"

/-- Emit `s` as a list of C lines at indentation `d`.
    `tail`: `s` is the last thing in its enclosing C block, so a `decl` may declare its variable
    directly in that block (same extent as the Tenon scope) instead of opening a block of its own. -/
partial def stmtC (opts : Options) (callees : List Sig) :
    Stmt → (env : List Slot) → (inLoop : Bool) → (tail : Bool) → (d : Nat) → M (List String)
  | .skip, _, _, _, _ => pure []
  | .note _ s, env, inLoop, tail, d => stmtC opts callees s env inLoop tail d   -- a label: no code
  | .seq s t, env, inLoop, tail, d => do
    let ls ← stmtC opts callees s env inLoop false d
    let lt ← stmtC opts callees t env inLoop tail d
    pure (ls ++ lt)
  | .assign x e, env, _, _, d => do
    -- RELIES ON T2: the value is within the declared range of x; not checked and not emitted.
    match env[x]? with
    | some (.int c) => let se ← liftE (exprC opts env e 0); pure [ind d s!"{c} = {se.s};"]
    | some sl => throw s!"assign {x}: `{sl.cname}` is {sl.kind} (always stuck in Tenon)"
    | none => throw s!"assign {x}: no such variable"
  | .store a i e, env, _, _, d => do
    -- RELIES ON T2: 0 ≤ i < length, and the value is in the element range. No check.
    match env[a]? with
    | some (.arr c _ w) | some (.slice c _ w) =>
      if !w then throw s!"internal: store into `{c}`, which is not writable"
      let si ← liftE (exprC opts env i 0)
      let se ← liftE (exprC opts env e 0)
      pure [ind d s!"{c}[{si.s}] = {se.s};"]
    | some sl => throw s!"store {a}: `{sl.cname}` is {sl.kind}"
    | none => throw s!"store {a}: no such variable"
  | .fassign x e, env, _, _, d => do
    match env[x]? with
    | some (.flt c) => let se ← liftE (fexprC opts env e 0); pure [ind d s!"{c} = {se};"]
    | some sl => throw s!"fassign {x}: `{sl.cname}` is {sl.kind} (always stuck in Tenon)"
    | none => throw s!"fassign {x}: no such variable"
  | .fstore a i e, env, _, _, d => do
    -- RELIES ON T2: 0 ≤ i < the run-time length. No check.
    match env[a]? with
    | some (.fslice c _ w) =>
      if !w then throw s!"internal: store into `{c}`, which is not writable"
      let si ← liftE (exprC opts env i 0)
      let se ← liftE (fexprC opts env e 0)
      pure [ind d s!"{c}[{si.s}] = {se};"]
    | some sl => throw s!"fstore {a}: `{sl.cname}` is {sl.kind}"
    | none => throw s!"fstore {a}: no such variable"
  | .fdecl e s, env, inLoop, tail, d => do
    let se ← liftE (fexprC opts env e 0)
    let c ← freshLocal false
    if tail then
      let ls ← stmtC opts callees s (.flt c :: env) inLoop true d
      pure (ind d s!"double {c} = {se};" :: ls)
    else
      let ls ← stmtC opts callees s (.flt c :: env) inLoop true (d + 1)
      pure ([ind d "{", ind (d + 1) s!"double {c} = {se};"] ++ ls ++ [ind d "}"])
  | .fite a b s t, env, inLoop, tail, d => do
    -- `if (a <= b) s else t`: a NaN on either side takes the else branch, in C as in Tenon. The negated
    -- form is `!(a <= b)`, never `a > b`.
    let sa ← liftE (fexprC opts env a 1)
    let sb ← liftE (fexprC opts env b 1)
    let (s, t, cond, neg) := match opts.sabotage with
      | .selLeNaN => (t, s, s!"{sa} > {sb}", s!"!({sa} > {sb})")
      | .fleAsLt => (s, t, s!"{sa} < {sb}", s!"!({sa} < {sb})")
      | _ => (s, t, s!"{sa} <= {sb}", s!"!({sa} <= {sb})")
    let ls ← stmtC opts callees s env inLoop true (d + 1)
    if tail && endsInBrk s && inLoop then
      let lt ← stmtC opts callees t env inLoop true d
      return [ind d s!"if ({cond}) \{"] ++ ls ++ [ind d "}"] ++ lt
    let lt ← stmtC opts callees t env inLoop true (d + 1)
    if ls.isEmpty && lt.isEmpty then pure []
    else if lt.isEmpty then pure ([ind d s!"if ({cond}) \{"] ++ ls ++ [ind d "}"])
    else if ls.isEmpty then pure ([ind d s!"if ({neg}) \{"] ++ lt ++ [ind d "}"])
    else pure ([ind d s!"if ({cond}) \{"] ++ ls ++ [ind d "} else {"] ++ lt ++ [ind d "}"])
  | .loopE e _ s, env, _, _, d => do
    -- The bound expression exists only for the proof and is NOT evaluated in C. RELIES ON T2 twice:
    -- (1) the loop leaves through `brk` within the bound; (2) Tenon's `execS` does evaluate `e` and is
    -- stuck if that is stuck (overflow, index out of range in `e`, a negative value gives zero
    -- iterations and is stuck too); a checked program's bound is never stuck, so dropping it is
    -- unobservable. On an unchecked program the C loop may run where Tenon is stuck.
    let se := (← liftE (exprC opts env e 0)).s      -- rendered only to reject an ill-shaped bound
    let ls ← stmtC opts callees s env true true (d + 1)
    let cmt := (se.replace "*/" "* /")
    match opts.sabotage with
    | .loopBOnce => pure ([ind d "for (;;) {"] ++ ls ++ [ind (d + 1) "break;", ind d "}"])
    | .loopEEval =>
      let it ← reserve "sab_iter"
      pure ([ind d s!"for (int64_t {it} = 0, {it}_end = {se} - 2; {it} < {it}_end; {it}++) \{"] ++ ls ++ [ind d "}"])
    | _ => pure ([ind d s!"for (;;) \{  /* proof bound: {cmt} iterations */"] ++ ls ++ [ind d "}"])
  | .ite a b s t, env, inLoop, tail, d => do
    let ca ← liftE (exprC opts env a 1)
    let cb ← liftE (exprC opts env b 1)
    -- `ite` tests only `≤`, so "if c" for a comparison c is written `ite 1 c` in Tenon. Print that as
    -- `if (c)`: 1 ≤ c holds exactly when the comparison does.
    let (sa, le, sb) := match a, cb.cond with
      | .lit 1, some c => ("", "", c)
      | _, _ => (ca.s ++ " ", if opts.sabotage == Sabotage.lt then "<" else "<=", " " ++ cb.s)
    let neg := match a, cb.cond with
      | .lit 1, some c => s!"!({c})"
      | _, _ => s!"{ca.s} > {cb.s}"
    let ls ← stmtC opts callees s env inLoop true (d + 1)
    if tail && endsInBrk s && inLoop then
      -- `if (c) { ...; break; } else { t }` at the end of a block is written without the `else`:
      -- control cannot fall out of the then-branch, and nothing follows `t` in this block.
      let lt ← stmtC opts callees t env inLoop true d
      return [ind d s!"if ({sa}{le}{sb}) \{"] ++ ls ++ [ind d "}"] ++ lt
    let lt ← stmtC opts callees t env inLoop true (d + 1)
    if ls.isEmpty && lt.isEmpty then pure []          -- the conditions have no side effects
    else if lt.isEmpty then pure ([ind d s!"if ({sa}{le}{sb}) \{"] ++ ls ++ [ind d "}"])
    else if ls.isEmpty && opts.sabotage != Sabotage.lt then pure ([ind d s!"if ({neg}) \{"] ++ lt ++ [ind d "}"])
    else pure ([ind d s!"if ({sa}{le}{sb}) \{"] ++ ls ++ [ind d "} else {"] ++ lt ++ [ind d "}"])
  | .decl _ _ e s, env, inLoop, tail, d => do
    -- RELIES ON T2: the initial value is within lo..=hi; not checked.
    let se := (← liftE (exprC opts env e 0)).s  -- `e` is evaluated in the outer environment
    let c ← freshLocal false
    if tail then
      let ls ← stmtC opts callees s (.int c :: env) inLoop true d
      pure (ind d s!"int64_t {c} = {se};" :: ls)
    else
      let ls ← stmtC opts callees s (.int c :: env) inLoop true (d + 1)
      pure ([ind d "{", ind (d + 1) s!"int64_t {c} = {se};"] ++ ls ++ [ind d "}"])
  | .forN n _ s, env, _, _, d => do
    if (n : Int) > i64Max then throw s!"forN {n}: bound does not fit int64_t"
    let c ← freshLocal true
    if modsInt s 0 && opts.sabotage != .counter then
      -- In Tenon the body may change the counter (assign, call destination, inout argument), but the
      -- next iteration starts from the loop's own count. Keep the real counter in a separate C
      -- variable.
      let it ← reserve s!"{c}_iter"
      let ls ← stmtC opts callees s (.int c :: env) true true (d + 1)
      pure ([ind d s!"for (int64_t {it} = 0; {it} < {n}; {it}++) \{",
             ind (d + 1) s!"int64_t {c} = {it};"] ++ ls ++ [ind d "}"])
    else
      let ls ← stmtC opts callees s (.int c :: env) true true (d + 1)
      pure ([ind d s!"for (int64_t {c} = 0; {c} < {n}; {c}++) \{"] ++ ls ++ [ind d "}"])
  | .forE e _ s, env, _, _, d => do
    -- The bound is evaluated once, in the outer environment, in the `for` initialiser. RELIES ON T2:
    -- the bound is ≥ 0 (a negative bound is stuck in Tenon; the C loop would run zero times).
    let se := (← liftE (exprC opts env e 0)).s
    let c ← freshLocal true
    let lim ← reserve s!"{c}_end"
    let ls ← stmtC opts callees s (.int c :: env) true true (d + 1)
    let limE := if opts.sabotage == .forEShort then s!"{lim} - 1" else lim
    if opts.sabotage == .forEReeval then
      -- broken on purpose: the bound expression is re-evaluated before every iteration
      pure ([ind d s!"for (int64_t {c} = 0; {c} < {se}; {c}++) \{"] ++ ls ++ [ind d "}"])
    else if modsInt s 0 then
      -- the body may change the counter (F2): the real counter is a separate C variable
      let it ← reserve s!"{c}_iter"
      pure ([ind d s!"for (int64_t {it} = 0, {lim} = {se}; {it} < {limE}; {it}++) \{",
             ind (d + 1) s!"int64_t {c} = {it};"] ++ ls ++ [ind d "}"])
    else
      pure ([ind d s!"for (int64_t {c} = 0, {lim} = {se}; {c} < {limE}; {c}++) \{"] ++ ls ++ [ind d "}"])
  | .loopB n _ s, env, _, _, d => do
    -- RELIES ON T2: the loop leaves through `brk` within n iterations (otherwise it is stuck in Tenon).
    -- The generated loop has no counter and no bound: on an input outside the guarantee it may not
    -- terminate.
    let ls ← stmtC opts callees s env true true (d + 1)
    match opts.sabotage with
    | .loopBOnce => pure ([ind d "for (;;) {"] ++ ls ++ [ind (d + 1) "break;", ind d "}"])
    | .loopBShort =>
      let it ← reserve "sab_iter"
      pure ([ind d s!"for (int64_t {it} = 0; {it} < {(n : Int) - 2}; {it}++) \{"] ++ ls ++ [ind d "}"])
    | _ => pure ([ind d "for (;;) {"] ++ ls ++ [ind d "}"])
  | .brk, _, inLoop, _, d =>
    if inLoop then pure [ind d "break;"]
    else throw "brk outside a loop (always stuck in Tenon when reached)"
  | .pmap f args e out, env, _, _, d => pmapC opts callees f args e out env d false
  | .pmapF f args e out, env, _, _, d => pmapC opts callees f args e out env d true
  | .call f args dst, env, _, _, d => do
    -- RELIES ON T2: the arguments have the callee's parameter types and satisfy its precondition;
    -- the result is within dst's range; `exclusive args dst` holds (so no two pointer arguments
    -- designate the same variable and no inout argument is also the destination).
    match callees[f]? with
    | none => throw s!"call {f}: no such earlier function"
    | some sig =>
      let cs ← liftE (callArgsC env sig args)
      match env[dst]? with
      | some (.int c) =>
        let note := if exclusive args dst then "" else "  /* not exclusive: stuck in Tenon if reached */"
        pure [ind d s!"{c} = {sig.cname}({", ".intercalate cs});{note}"]
      | some sl => throw s!"call {sig.cname}: destination `{sl.cname}` is {sl.kind}"
      | none => throw s!"call {sig.cname}: no destination variable at position {dst}"

/-! ## Functions and programs -/

/-- How one parameter is passed. -/
inductive Passing where
  | intVal | intInout | arrRead | arrCopy | arrInout | fltVal | fltInout
  deriving DecidableEq

def passing (opts : Options) (f : Fn) : List Passing :=
  (f.params.zipIdx).map fun ((ty, io), k) => match ty, io with
    | .int _ _, false => .intVal
    | .int _ _, true => .intInout
    | .flt, false => .fltVal
    | .flt, true => .fltInout
    | .arr .., true | .slice .., true | .fslice, true => if opts.sabotage == .inoutCopy then .arrCopy else .arrInout
    | .arr .., false | .slice .., false | .fslice, false => if modsArr f.body (k + 1) then .arrCopy else .arrRead

/-- Emit one function. `callees` are the functions after it in the program (the ones it may call).
    `taken` are identifiers the function must not reuse (all function names of the program). -/
def fnC (opts : Options) (callees : List Sig) (taken : List String) (isStatic : Bool)
    (f : Fn) (nm : FnNames) : Except String (List String) := do
  if nm.params.length != f.params.length then
    throw s!"{nm.name}: {nm.params.length} parameter names for {f.params.length} parameters"
  for n in nm.name :: nm.result :: nm.params do
    if !validIdent n || cKeywords.contains n then throw s!"`{n}` is not usable as a C identifier"
  if f.rlo < i64Min ∨ f.rlo > i64Max then
    throw s!"{nm.name}: initial result value {f.rlo} is outside int64_t"
  -- `ProgOk` does not require parameter types to lie inside int64 (a parameter that is never read
  -- may have any type; KernelFindings.lean, G3). The C parameter is int64_t, so refuse.
  for ((ty, _), pn) in f.params.zip nm.params do
    let (lo, hi) : Int × Int := match ty with
      | .int lo hi => (lo, hi) | .arr _ lo hi => (lo, hi) | .slice lo hi => (lo, hi) | .flt | .fslice => (0, 0)
    if lo ≤ hi ∧ (lo < i64Min ∨ hi > i64Max) then
      throw s!"{nm.name}: the type of parameter `{pn}` ({lo}..={hi}) is not inside int64_t"
  let run : M (List String) := do
    let res ← reserve nm.result
    -- parameters: position k+1 in the body environment [result, params...]
    let mut slots : List Slot := []
    let mut cparams : List String := []
    let mut entry : List String := []
    let mut exit : List String := []
    for (((ty, _), pn), pass) in (f.params.zip nm.params).zip (passing opts f) do
      let c ← reserve pn
      match ty, pass with
      | .int _ _, .intInout =>
        -- Copy-in at entry, copy-out at the single exit: exactly the Tenon semantics for this
        -- parameter. No `restrict`: the pointer is read once and written once.
        let p ← reserve s!"{c}_io"
        cparams := cparams ++ [s!"int64_t *{p}"]
        entry := entry ++ [ind 1 s!"int64_t {c} = *{p};"]
        if opts.sabotage != .noWriteBack then exit := exit ++ [ind 1 s!"*{p} = {c};"]
        slots := slots ++ [.int c]
      | .int _ _, _ =>
        slots := slots ++ [.int c]
        cparams := cparams ++ [s!"int64_t {c}"]
      | .arr len _ _, .arrInout =>
        -- In place. RELIES ON T2 (`exclusive`) and on an argument about aliasing that is NOT
        -- proved in the kernel; see README.md.
        cparams := cparams ++ [s!"int64_t *restrict {c} /* length {len}, inout */"]
        slots := slots ++ [.arr c len true]
      | .arr len _ _, .arrCopy =>
        if opts.sabotage == .noCopy then
          let src ← reserve s!"{c}_arg"
          cparams := cparams ++ [s!"const int64_t *{src} /* length {len} */"]
          entry := entry ++ [ind 1 s!"int64_t *{c} = (int64_t *){src};"]
        else
          -- By value and modified: the callee's changes must not reach the caller.
          let src ← reserve s!"{c}_arg"
          cparams := cparams ++ [s!"const int64_t *restrict {src} /* length {len} */"]
          entry := entry ++ [ind 1 s!"int64_t {c}[{max len 1}];"] ++
            (if len == 0 then [] else [ind 1 s!"memcpy({c}, {src}, sizeof {c});"])
        slots := slots ++ [.arr c len true]
      | .arr len _ _, _ =>
        cparams := cparams ++ [s!"const int64_t *restrict {c} /* length {len} */"]
        slots := slots ++ [.arr c len false]
      | .slice _ _, .arrInout =>
        -- In place; same remarks as for an inout array.
        let ln ← reserve s!"{c}_len"
        cparams := cparams ++ [s!"int64_t *restrict {c}", s!"int64_t {ln}"]
        slots := slots ++ [.slice c ln true]
      | .slice _ _, .arrCopy =>
        let src ← reserve s!"{c}_arg"
        let ln ← reserve s!"{c}_len"
        if opts.sabotage == .noCopy || opts.sabotage == .sliceNoCopy then
          cparams := cparams ++ [s!"const int64_t *{src}", s!"int64_t {ln}"]
          entry := entry ++ [ind 1 s!"int64_t *{c} = (int64_t *){src};"]
        else
          -- By value and modified: a private copy of run-time length, on the heap (the length has
          -- no static bound). `tn_copy` aborts if the allocation fails: the only run-time check in
          -- the generated code, and it is about memory, not about the program's values.
          cparams := cparams ++ [s!"const int64_t *restrict {src}", s!"int64_t {ln}"]
          entry := entry ++ [ind 1 s!"int64_t *{c} = tn_copy({src}, {ln});"]
          exit := exit ++ [ind 1 s!"free({c});"]
        slots := slots ++ [.slice c ln true]
      | .slice _ _, _ =>
        let ln ← reserve s!"{c}_len"
        cparams := cparams ++ [s!"const int64_t *restrict {c}", s!"int64_t {ln}"]
        slots := slots ++ [.slice c ln false]
      | .flt, .fltInout =>
        let p ← reserve s!"{c}_io"
        cparams := cparams ++ [s!"double *{p}"]
        entry := entry ++ [ind 1 s!"double {c} = *{p};"]
        if opts.sabotage != .noWriteBack then exit := exit ++ [ind 1 s!"*{p} = {c};"]
        slots := slots ++ [.flt c]
      | .flt, _ =>
        slots := slots ++ [.flt c]
        cparams := cparams ++ [s!"double {c}"]
      | .fslice, .arrInout =>
        -- In place; same remarks as for an inout integer slice.
        let ln ← reserve s!"{c}_len"
        cparams := cparams ++ [s!"double *restrict {c}", s!"int64_t {ln}"]
        slots := slots ++ [.fslice c ln true]
      | .fslice, .arrCopy =>
        let src ← reserve s!"{c}_arg"
        let ln ← reserve s!"{c}_len"
        if opts.sabotage == .noCopy || opts.sabotage == .sliceNoCopy then
          cparams := cparams ++ [s!"const double *{src}", s!"int64_t {ln}"]
          entry := entry ++ [ind 1 s!"double *{c} = (double *){src};"]
        else
          cparams := cparams ++ [s!"const double *restrict {src}", s!"int64_t {ln}"]
          entry := entry ++ [ind 1 s!"double *{c} = tn_fcopy({src}, {ln});"]
          exit := exit ++ [ind 1 s!"free({c});"]
        slots := slots ++ [.fslice c ln true]
      | .fslice, _ =>
        let ln ← reserve s!"{c}_len"
        cparams := cparams ++ [s!"const double *restrict {c}", s!"int64_t {ln}"]
        slots := slots ++ [.fslice c ln false]
    let body ← stmtC opts callees f.body (.int res :: slots) false true 1
    let rinit ← liftE (litC f.rlo)
    let sig := s!"{if isStatic then "static " else ""}int64_t {nm.name}({if cparams.isEmpty then "void" else ", ".intercalate cparams})"
    pure ([sig, "{"] ++ entry ++ [ind 1 s!"int64_t {res} = {rinit};"] ++ body ++ exit ++ [ind 1 s!"return {res};", "}"])
  let (ls, _) ← run.run { used := taken ++ cKeywords, locals := nm.locals }
  pure ls

def needsMemcpy (opts : Options) (f : Fn) : Bool :=
  ((passing opts f).zip f.params).any fun (p, (ty, _)) => match ty with
    | .arr len _ _ => p == .arrCopy && len != 0
    | .slice .. | .fslice => p == .arrCopy
    | _ => false

def needsHeapCopy (opts : Options) (f : Fn) : Bool :=
  opts.sabotage != .noCopy && opts.sabotage != .sliceNoCopy &&
  ((passing opts f).zip f.params).any fun (p, (ty, _)) => match ty with
    | .slice .. | .fslice => p == .arrCopy
    | _ => false

/-- The C prototype text of a function, for headers and test drivers. -/
def protoC (f : Fn) (nm : FnNames) : String :=
  let ps := (f.params.zip nm.params).map fun ((ty, io), pn) => match ty, io with
    | .int _ _, false => s!"int64_t {pn}"
    | .int _ _, true => s!"int64_t *{pn}"
    | .arr .., false => s!"const int64_t *restrict {pn}"
    | .arr .., true => s!"int64_t *restrict {pn}"
    | .slice .., false => s!"const int64_t *restrict {pn}, int64_t {pn}_len"
    | .slice .., true => s!"int64_t *restrict {pn}, int64_t {pn}_len"
    | .flt, false => s!"double {pn}"
    | .flt, true => s!"double *{pn}"
    | .fslice, false => s!"const double *restrict {pn}, int64_t {pn}_len"
    | .fslice, true => s!"double *restrict {pn}, int64_t {pn}_len"
  s!"int64_t {nm.name}({if ps.isEmpty then "void" else ", ".intercalate ps});"

def divHelper : String :=
  "/* Tenon `div`: defined only for x >= 0 and y > 0, where it equals unsigned division. */\n" ++
  "static inline int64_t tn_div(int64_t x, int64_t y) { return (int64_t)((uint64_t)x / (uint64_t)y); }"
def selHelper : String :=
  "/* Tenon `sel`: both arms are already evaluated (Tenon guarantees neither is stuck), so no branch is needed.\n" ++
  "   The hint keeps clang from turning the conditional move back into a branch. */\n" ++
  "#if defined(__clang__)\n#define TENON_UNPREDICTABLE(c) __builtin_unpredictable(c)\n#else\n#define TENON_UNPREDICTABLE(c) (c)\n#endif\n" ++
  "static inline int64_t tn_sel(int c, int64_t t, int64_t e) { return TENON_UNPREDICTABLE(c != 0) ? t : e; }"
def selpHelper : String :=
  "/* Tenon `sel` without the hint. */\n" ++
  "static inline int64_t tn_selp(int c, int64_t t, int64_t e) { return c ? t : e; }"
def selmHelper : String :=
  "/* Tenon `sel` with a mask: no conditional operator. */\n" ++
  "static inline int64_t tn_selm(int c, int64_t t, int64_t e) { uint64_t m = -(uint64_t)(c != 0); return (int64_t)(((uint64_t)t & m) | ((uint64_t)e & ~m)); }"
def copyHelper : String :=
  "/* Private copy of a by-value slice that the function modifies. */\n" ++
  "static int64_t *tn_copy(const int64_t *src, int64_t n)\n{\n" ++
  "    int64_t *p = malloc(n > 0 ? (size_t)n * sizeof(int64_t) : 1);\n" ++
  "    if (!p) abort();\n" ++
  "    if (n > 0) memcpy(p, src, (size_t)n * sizeof(int64_t));\n" ++
  "    return p;\n}"

/-- Guards that a C compiler can check about the float environment. They do NOT cover contraction
    (`-ffp-contract`): no macro reports it. The pragma is the standard way to forbid it; clang obeys it
    (but not under `-ffp-contract=fast`, measured in difftest/), gcc ignores it. -/
def floatGuard : String :=
  "/* Tenon floats are IEEE-754 binary64 with every operation rounded once, in the written order. */\n" ++
  "#include <float.h>\n" ++
  "#if defined(__FAST_MATH__) || defined(__FINITE_MATH_ONLY__) && __FINITE_MATH_ONLY__\n" ++
  "#error \"Tenon float code must not be compiled with -ffast-math, -Ofast or -ffinite-math-only\"\n#endif\n" ++
  "#if !defined(FLT_EVAL_METHOD) || FLT_EVAL_METHOD != 0\n" ++
  "#error \"Tenon float code needs double arithmetic evaluated in double precision (FLT_EVAL_METHOD == 0)\"\n#endif\n" ++
  "_Static_assert(sizeof(double) == 8 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024, \"double must be IEEE-754 binary64\");\n" ++
  "#pragma STDC FP_CONTRACT OFF"
def bitsHelper : String :=
  "/* A double from its bit pattern (infinities and NaN literals). */\n" ++
  "static inline double tn_bits(uint64_t b) { double d; memcpy(&d, &b, sizeof d); return d; }"
def fselHelper : String :=
  "/* Tenon float `sel` and `selLe`: all operands are already evaluated, the condition picks one. */\n" ++
  "#if defined(__clang__)\n#define TENON_FUNPREDICTABLE(c) __builtin_unpredictable(c)\n#else\n#define TENON_FUNPREDICTABLE(c) (c)\n#endif\n" ++
  "static inline double tn_fsel(int c, double t, double e) { return TENON_FUNPREDICTABLE(c != 0) ? t : e; }"
def fselpHelper : String :=
  "static inline double tn_fselp(int c, double t, double e) { return c ? t : e; }"
def fselmHelper : String :=
  "/* Tenon float select with a bit mask: no conditional operator. */\n" ++
  "static inline double tn_fselm(int c, double t, double e)\n{\n" ++
  "    uint64_t m = -(uint64_t)(c != 0), a, b; double r;\n" ++
  "    memcpy(&a, &t, 8); memcpy(&b, &e, 8); a = (a & m) | (b & ~m); memcpy(&r, &a, 8); return r;\n}"
def fcopyHelper : String :=
  "/* Private copy of a by-value float slice that the function modifies. */\n" ++
  "static double *tn_fcopy(const double *src, int64_t n)\n{\n" ++
  "    double *p = malloc(n > 0 ? (size_t)n * sizeof(double) : 1);\n" ++
  "    if (!p) abort();\n" ++
  "    if (n > 0) memcpy(p, src, (size_t)n * sizeof(double));\n" ++
  "    return p;\n}"

/-- Everything `emitProgram` may put before the functions, for use with `prelude := false`. -/
def fullPrelude : String :=
  "\n".intercalate ["#include <stdint.h>", "#include <string.h>", "#include <stdlib.h>", "#include <math.h>", floatGuard,
    divHelper, selHelper, selpHelper, selmHelper, copyHelper, bitsHelper, fselHelper, fselpHelper, fselmHelper, fcopyHelper]

/-- Emit a whole program as one C translation unit. `fns` is newest first, as in `evalFn`; `names` is
    parallel to it. Functions are written oldest first, so every callee is defined before its callers. -/
def emitProgram (opts : Options) (fns : List Fn) (names : List FnNames) : Except String String := do
  if fns.length != names.length then throw "emitProgram: one FnNames per function is required"
  let fnNames := names.map (·.name)
  if fnNames.eraseDups.length != fnNames.length then throw "emitProgram: duplicate function names"
  let sigs : List Sig := (fns.zip names).map fun (f, nm) => { cname := nm.name, params := f.params }
  let mut out : List (List String) := []
  -- oldest first
  for k in (List.range fns.length).reverse do
    match fns[k]?, names[k]? with
    | some f, some nm =>
      let ls ← fnC opts (sigs.drop (k + 1)) fnNames (opts.staticHelpers && k != 0) f nm
      out := out ++ [ls]
    | _, _ => pure ()
  let usesDiv := opts.unsignedDiv && fns.any (fun f => stmtUsesDiv f.body)
  let usesSel := fns.any (fun f => stmtUsesSel f.body)
  let heap := fns.any (needsHeapCopy opts)
  let hasFParam (f : Fn) : Bool := f.params.any fun p => p.1 == .flt || p.1 == .fslice
  let fheap := fns.any fun f => needsHeapCopy opts f && f.params.any (·.1 == .fslice)
  let iheap := fns.any fun f => needsHeapCopy opts f && f.params.any (· matches (.slice .., _))
  let usesFloat := fns.any fun f => stmtUsesFloat f.body || hasFParam f
  let usesFSel := fns.any (fun f => stmtUsesFSel f.body)
  let usesBits := fns.any (fun f => stmtUsesBits f.body)
  let usesMath := opts.sabotage == .fma || fns.any (fun f => stmtUsesMath f.body)
  let header := if !opts.prelude then [] else
    ["#include <stdint.h>"] ++
    (if fns.any (needsMemcpy opts) || usesBits || (usesFSel && opts.selForm == .mask) then ["#include <string.h>"] else []) ++
    (if heap then ["#include <stdlib.h>"] else []) ++
    (if usesMath then ["#include <math.h>"] else []) ++
    (if usesFloat then ["", floatGuard] else []) ++
    (if opts.banner.isEmpty then [] else ["", opts.banner]) ++
    (if usesDiv then ["", divHelper] else []) ++
    (if usesSel && opts.selForm == .eager then ["", selHelper] else []) ++
    (if usesSel && opts.selForm == .eagerPlain then ["", selpHelper] else []) ++
    (if usesSel && opts.selForm == .mask then ["", selmHelper] else []) ++
    (if iheap then ["", copyHelper] else []) ++
    (if usesBits then ["", bitsHelper] else []) ++
    (if usesFSel && opts.selForm == .eager then ["", fselHelper] else []) ++
    (if usesFSel && opts.selForm == .eagerPlain then ["", fselpHelper] else []) ++
    (if usesFSel && opts.selForm == .mask then ["", fselmHelper] else []) ++
    (if fheap then ["", fcopyHelper] else [])
  pure ("\n".intercalate (header ++ (out.map fun ls => "\n" ++ "\n".intercalate ls)) ++ "\n")

end Tenon.Emit
