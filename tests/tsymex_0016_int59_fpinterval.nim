## RFC-0016 INT-59: a float-to-int conversion's range side over a rounded
## division (`int(trunc(float(t) / 3.0))`) is refuted by an interval
## argument (`fpIntervalRefutes`) instead of a bit-blast of the division.
##
## `fpIntervalRefutes` answers a query UNSAT without the solver, so this
## suite checks it against Z3 differentially (its soundness argument is
## its doc comment in `runtime.nim`):
##   (1) a property test over random `Float64` terms of every shape it
##       reads (and some it does not), rounding modes, literals (signed
##       zeros, subnormals, values past 1e300, infinities, NaN) and
##       comparisons near a value the term takes: every root it refutes
##       is false at all 256 values of the 8-bit input, each evaluated by
##       Z3's own floating-point semantics (`simplify` of the substituted
##       root), and a sample of them is confirmed UNSAT by the solver;
##   (2) fixed cases: the conversion side it exists for, a zero extension
##       by no bits (the operand read signed, so not narrowed), a divisor
##       interval holding zero;
##   (3) the cost: the K8b stdlib row `int(trunc(float(t) / 3.0))` walks
##       in at most `int59Budget` rlimit units (12,066,441 measured: the
##       SAT target query alone; 35.2M before, each range side bit-blasting
##       the division to an UNSAT);
##   (4) the version floor.
import std/[unittest, strutils, math, random, sequtils]
import z3
import z3/ffi
import nelli
import nelli/symex
import nelli/smt/runtime
import nelli/smt/admission
import ./s8cu_helpers

# ---- (1) the differential property ------------------------------------------

type Gen = object
  cs: seq[int]
  i: int

proc next(g: var Gen; n: int): int =
  ## The next choice in `0 ..< n` (0 once the choices run out).
  if g.i < g.cs.len: result = abs(g.cs[g.i]) mod n
  inc g.i

const literalPool = [0.0, -0.0, 1.0, -1.0, 3.0, 0.5, 1.0 / 3.0, 127.0,
  128.0, -128.0, 255.0, 256.0, 1e-310, -1e-310, 5e-324, -5e-324,
  2.2250738585072014e-308, 1e300, -1e300, 1.7e308, -1.7e308,
  9.2233720368547758e18, 1.8446744073709552e19, Inf, NegInf, NaN]

proc cNextAfter(x, y: cdouble): cdouble {.importc: "nextafter",
                                           header: "<math.h>".}

type Case = object
  ctx: Z3Context
  v: Z3BitVec[8]

proc held(cs: Case; x: RawZ3Ast): Z3Float64 =
  wrap[Z3Float64](cs.ctx, cs.ctx.checkErr x)

proc rm(cs: Case; g: var Gen): Z3RoundingMode =
  case g.next(5)
  of 0: rmRNE(cs.ctx)
  of 1: rmRNA(cs.ctx)
  of 2: rmRTP(cs.ctx)
  of 3: rmRTN(cs.ctx)
  else: rmRTZ(cs.ctx)

proc valueAt(cs: Case; t: Z3Float64; x: int): float64 =
  ## `t`'s value at `v = x`, by Z3's simplifier; NaN when it is not a
  ## finite numeral there.
  let s = wrap[Z3Float64](cs.ctx, cs.ctx.checkErr Z3_simplify(cs.ctx.raw,
    substitute(t, cs.v, mkBitVec[8](cs.ctx, x)).raw))
  let c = cs.ctx.raw
  if not Z3_is_numeral_ast(c, s.raw) or Z3_fpa_is_numeral_nan(c, s.raw) or
     Z3_fpa_is_numeral_inf(c, s.raw): return NaN
  let r = wrap[Z3AnyAst](cs.ctx, cs.ctx.checkErr Z3_simplify(c,
    cs.ctx.checkErr Z3_mk_fpa_to_real(c, s.raw)))
  float64(Z3_get_numeral_double(c, r.raw))

proc term(cs: Case; g: var Gen; depth: int): Z3Float64 =
  let c = cs.ctx.raw
  let v = cs.v
  let leaf = depth >= 3 or g.next(3) == 0
  if leaf:
    if g.next(3) == 0:
      return mkFp[11, 53](cs.ctx, literalPool[g.next(literalPool.len)])
    let r = cs.rm(g)
    let operand = case g.next(6)
      of 0: wrap[Z3AnyAst](cs.ctx, cs.ctx.checkErr Z3_mk_sign_ext(c, 56, v.raw))
      of 1: wrap[Z3AnyAst](cs.ctx, cs.ctx.checkErr Z3_mk_zero_ext(c, 56, v.raw))
      of 2: wrap[Z3AnyAst](cs.ctx, cs.ctx.checkErr Z3_mk_zero_ext(c, 0, v.raw))
      of 3: wrap[Z3AnyAst](cs.ctx, cs.ctx.checkErr Z3_mk_sign_ext(c, 0, v.raw))
      of 4: wrap[Z3AnyAst](cs.ctx, cs.ctx.checkErr Z3_mk_sign_ext(c, 8, v.raw))
      else: wrap[Z3AnyAst](cs.ctx, v.raw)
    let zero = mkFp[11, 53](cs.ctx, 0.0)   # holds the sort below
    let sort = Z3_get_sort(c, zero.raw)
    if g.next(2) == 0:
      return cs.held(Z3_mk_fpa_to_fp_signed(c, r.raw, operand.raw, sort))
    else:
      return cs.held(Z3_mk_fpa_to_fp_unsigned(c, r.raw, operand.raw, sort))
  case g.next(12)
  of 0, 1, 2, 3, 4, 5, 6:
    let op = g.next(4)
    let r = cs.rm(g)
    let a = cs.term(g, depth + 1)
    let b = cs.term(g, depth + 1)
    case op
    of 0: cs.held(Z3_mk_fpa_add(c, r.raw, a.raw, b.raw))
    of 1: cs.held(Z3_mk_fpa_sub(c, r.raw, a.raw, b.raw))
    of 2: cs.held(Z3_mk_fpa_mul(c, r.raw, a.raw, b.raw))
    else: cs.held(Z3_mk_fpa_div(c, r.raw, a.raw, b.raw))
  of 7:
    let a = cs.term(g, depth + 1)
    cs.held(Z3_mk_fpa_neg(c, a.raw))
  of 8, 9:
    let r = cs.rm(g)
    let a = cs.term(g, depth + 1)
    cs.held(Z3_mk_fpa_round_to_integral(c, r.raw, a.raw))
  of 10:  # not read by the interval argument
    let r = cs.rm(g)
    let a = cs.term(g, depth + 1)
    cs.held(Z3_mk_fpa_sqrt(c, r.raw, a.raw))
  else:
    let a = cs.term(g, depth + 1)
    cs.held(Z3_mk_fpa_abs(c, a.raw))

proc comparison(cs: Case; g: var Gen): Z3Bool =
  let c = cs.ctx.raw
  let a = cs.term(g, 0)
  var b: Z3Float64
  let shape = g.next(4)
  if shape == 0:
    b = cs.term(g, 0)
  elif shape == 3:
    b = mkFp[11, 53](cs.ctx, literalPool[g.next(literalPool.len)])
  else:
    # A literal near a value `a` takes: a few ulps off (the boundary the
    # one-ulp widening has to cover), or past it by a margin (where the
    # intervals decide).
    # Half the time at an extreme input, where an interval's bound is met.
    let input = if g.next(2) == 0: [0, 127, 128, 255][g.next(4)]
                else: g.next(256)
    var x = cs.valueAt(a, input)
    if x != x: x = literalPool[g.next(literalPool.len)]
    if shape == 1:
      for k in 0 ..< g.next(4):
        x = float64(cNextAfter(x, (if g.next(2) == 0: Inf else: NegInf)))
    else:
      let m = float64(1 + g.next(400))
      x = (if g.next(2) == 0: x + m * (1.0 + abs(x)) else: x - m * (1.0 + abs(x)))
    b = mkFp[11, 53](cs.ctx, x)
  let raw = case g.next(4)
    of 0: Z3_mk_fpa_leq(c, a.raw, b.raw)
    of 1: Z3_mk_fpa_lt(c, a.raw, b.raw)
    of 2: Z3_mk_fpa_geq(c, a.raw, b.raw)
    else: Z3_mk_fpa_gt(c, a.raw, b.raw)
  wrap[Z3Bool](cs.ctx, cs.ctx.checkErr raw)

proc root(cs: Case; g: var Gen; depth = 0): Z3Bool =
  if depth >= 2: return cs.comparison(g)
  case g.next(6)
  of 0: not cs.root(g, depth + 1)
  of 1: cs.root(g, depth + 1) and cs.root(g, depth + 1)
  of 2: cs.root(g, depth + 1) or cs.root(g, depth + 1)
  else: cs.comparison(g)

var stats = (cases: 0, refuted: 0, solverConfirmed: 0, undecidedValues: 0)
var disagreement = ""

proc confirm(cs: Case; r: Z3Bool) =
  ## The property: a root `fpIntervalRefutes` refutes is false at every
  ## value of `v`, by Z3's evaluation (and, for a sample, by its solver).
  inc stats.cases
  if not fpIntervalRefutes(cs.ctx, [r]): return
  inc stats.refuted
  for x in 0 .. 255:
    let s = wrap[Z3Bool](cs.ctx, cs.ctx.checkErr Z3_simplify(cs.ctx.raw,
      substitute(r, cs.v, mkBitVec[8](cs.ctx, x)).raw))
    case Z3_get_bool_value(cs.ctx.raw, s.raw)
    of Z3_L_TRUE:
      disagreement = "refuted, but true at v = " & $x & ": " & $r
      doAssert false, disagreement
    of Z3_L_FALSE: discard
    else: inc stats.undecidedValues
  if stats.solverConfirmed < 12:
    # The solver itself, under a step bound (a timeout is inconclusive).
    let st = querySolver(cs.ctx, [r], 20_000_000'u).check()
    if st == zsSat:
      disagreement = "refuted, but the solver found a model: " & $r
      doAssert false, disagreement
    if st == zsUnsat: inc stats.solverConfirmed

proc newCase(): Case =
  let ctx = newContext()
  Case(ctx: ctx, v: mkBitVecVar[8](ctx, "v"))

proc agrees(choices: seq[int]) =
  let cs = newCase()
  var g = Gen(cs: choices)
  cs.confirm(cs.root(g))

const boundaryPool = [3.0, -3.0, 0.1, 1.0 / 3.0, 7.0, 1e-3, 10.0, 0.7]
  ## Operands whose products and quotients with an integer are inexact.

proc agreesAtBound(choices: seq[int]) =
  ## One rounded operation of a converted input and an inexact literal,
  ## compared with a literal 0-2 ulps from its value at an extreme input:
  ## where the interval's bound is the operation's rounding, so a bound not
  ## widened past it is refuted wrongly.
  let cs = newCase()
  let c = cs.ctx.raw
  var g = Gen(cs: choices)
  let zero = mkFp[11, 53](cs.ctx, 0.0)   # holds the sort below
  let sort = Z3_get_sort(c, zero.raw)
  let r1 = cs.rm(g)
  let conv = if g.next(2) == 0:
      let e = wrap[Z3AnyAst](cs.ctx, cs.ctx.checkErr Z3_mk_sign_ext(c, 56, cs.v.raw))
      cs.held(Z3_mk_fpa_to_fp_signed(c, r1.raw, e.raw, sort))
    else:
      cs.held(Z3_mk_fpa_to_fp_unsigned(c, r1.raw, cs.v.raw, sort))
  let lit = mkFp[11, 53](cs.ctx, boundaryPool[g.next(boundaryPool.len)])
  let (a, b) = if g.next(2) == 0: (conv, lit) else: (lit, conv)
  let r2 = cs.rm(g)
  let t = case g.next(4)
    of 0: cs.held(Z3_mk_fpa_add(c, r2.raw, a.raw, b.raw))
    of 1: cs.held(Z3_mk_fpa_sub(c, r2.raw, a.raw, b.raw))
    of 2: cs.held(Z3_mk_fpa_mul(c, r2.raw, a.raw, b.raw))
    else: cs.held(Z3_mk_fpa_div(c, r2.raw, a.raw, b.raw))
  var x = cs.valueAt(t, [0, 127, 128, 255][g.next(4)])
  if x != x: return
  let dir = if g.next(2) == 0: Inf else: NegInf
  for k in 0 ..< g.next(3): x = float64(cNextAfter(x, dir))
  let l = mkFp[11, 53](cs.ctx, x)
  let raw = case g.next(4)
    of 0: Z3_mk_fpa_leq(c, t.raw, l.raw)
    of 1: Z3_mk_fpa_lt(c, t.raw, l.raw)
    of 2: Z3_mk_fpa_geq(c, t.raw, l.raw)
    else: Z3_mk_fpa_gt(c, t.raw, l.raw)
  cs.confirm(wrap[Z3Bool](cs.ctx, cs.ctx.checkErr raw))

suite "INT-59 (1): every refutation is confirmed by Z3":
  test "random Float64 terms, rounding modes, literals and comparisons":
    let rep = forAll(lists(integers(0, 1_000_000), 8, 80), agrees,
                     Settings(maxExamples: 1000, seed: 20261118))
    echo "INT59STATS ", stats
    checkpoint $stats & " " & disagreement
    check rep.outcome == otPassed
    check disagreement == ""
    # The generator reaches the argument: enough refutations to mean
    # something, each checked at all 256 inputs.
    check stats.refuted >= 40
    check stats.solverConfirmed >= 6
    check stats.undecidedValues == 0

  test "one rounded operation, compared at its bound":
    stats = (cases: 0, refuted: 0, solverConfirmed: 0, undecidedValues: 0)
    let rep = forAll(lists(integers(0, 1_000_000), 10, 10), agreesAtBound,
                     Settings(maxExamples: 600, seed: 20261118))
    echo "INT59STATS bound ", stats
    checkpoint $stats & " " & disagreement
    check rep.outcome == otPassed
    check disagreement == ""
    # The generator reaches the argument at its bound: at this seed the real
    # code refutes 20 of 581 cases (most comparisons sit inside the widened
    # bound, which is the point), and the mutant with the one-ulp widening
    # removed refutes 149 of 1081 and is caught. Half the measured count.
    check stats.refuted >= 10
    check stats.undecidedValues == 0

# ---- (2) fixed cases ---------------------------------------------------------

suite "INT-59 (2): the shapes at their edges":
  setup:
    let ctx {.inject.} = newContext()
    let c {.inject.} = ctx.raw
    let v {.inject.} = mkBitVecVar[8](ctx, "v")
    let zero {.inject.} = mkFp[11, 53](ctx, 0.0)   # holds the sort below
    let sort {.inject.} = Z3_get_sort(c, zero.raw)
  template f(x: RawZ3Ast): Z3Float64 {.dirty.} = wrap[Z3Float64](ctx, ctx.checkErr x)
  template lit(x: float64): Z3Float64 {.dirty.} = mkFp[11, 53](ctx, x)
  template lt(a, b: Z3Float64): Z3Bool {.dirty.} =
    wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_fpa_lt(c, a.raw, b.raw))

  test "the conversion's range side over trunc(float(t) / 3.0) is refuted":
    let ext = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_sign_ext(c, 56, v.raw))
    let x = f Z3_mk_fpa_to_fp_signed(c, rmRNE(ctx).raw, ext.raw, sort)
    let q = f Z3_mk_fpa_round_to_integral(c, rmRTZ(ctx).raw,
              f(Z3_mk_fpa_div(c, rmRNE(ctx).raw, x.raw, lit(3.0).raw)).raw)
    let inRange = lt(lit(-9.223372036854775808e18), q) and
                  lt(q, lit(9.223372036854775808e18))
    check fpIntervalRefutes(ctx, [not inRange])
    check not fpIntervalRefutes(ctx, [inRange])

  test "a zero extension by no bits is not read as unsigned":
    # `v` read signed takes -128; `to_fp(zext0(v)) < 0` is SAT.
    let z0 = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_zero_ext(c, 0, v.raw))
    let x = f Z3_mk_fpa_to_fp_signed(c, rmRNE(ctx).raw, z0.raw, sort)
    check not fpIntervalRefutes(ctx, [lt(x, lit(0.0))])
    let z8 = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_zero_ext(c, 8, v.raw))
    let y = f Z3_mk_fpa_to_fp_signed(c, rmRNE(ctx).raw, z8.raw, sort)
    check fpIntervalRefutes(ctx, [lt(y, lit(0.0))])

  test "a divisor interval holding zero gives no interval":
    let x = f Z3_mk_fpa_to_fp_signed(c, rmRNE(ctx).raw, v.raw, sort)
    let d = f Z3_mk_fpa_div(c, rmRNE(ctx).raw, lit(1.0).raw, x.raw)
    check not fpIntervalRefutes(ctx, [lt(lit(1e300), d)])
    check not fpIntervalRefutes(ctx, [lt(d, lit(-1e300))])

  test "a subnormal literal is either bounded exactly or not at all":
    # Both roots are true: whatever interval the literal gets, it must
    # hold its value.
    let s = lit(5e-324)
    check not fpIntervalRefutes(ctx, [lt(lit(0.0), s)])
    check not fpIntervalRefutes(ctx, [lt(s, lit(1e-300))])
    check not fpIntervalRefutes(ctx, [lt(lit(-1e-300), lit(-5e-324))])

# ---- (3) the cost ------------------------------------------------------------

let int59Budget =
  if z3FullVersion().startsWith("5."): 15_000_000 else: 24_100_000
  ## The walk's units, bounded. The 5.1 row, 15M: 12,066,441 measured on
  ## c at walker 421 (the
  ## SAT target query, which bit-blasts the division to find `t = 21`),
  ## with 24% headroom for a Z3 search-order drift. Before the interval
  ## argument the walk took 35.2M (each conversion range side bit-blasted
  ## to an UNSAT, the walk's and the tail walk's); 15M also sits under
  ## `seqQueryRLimit` (40M), so the row cannot pass by exhausting a budget.
  ## The 4.13.4 row (the Windows legs' pin), 24.1M: Z3 4.13.4 searches the
  ## same query harder, 19,421,121 measured on the z3-4.13.4 dev image, and
  ## the same 24% headroom rule gives 24.08M; it is also under 40M. The 5.1
  ## bound is not loosened: the version the test sees selects the row.

proc i59Trunc(a, b: int8) =
  let t = int(a)
  if int(trunc(float(t) / 3.0)) == 7: symexTarget("hit")

suite "INT-59 (3): the trunc row walks in a bounded number of units":
  test "int(trunc(float(t) / 3.0)) == 7 is exact under the budget":
    # The verdict is pinned (K9): the witness hits natively.
    let all = exhaustive(toSeq(low(int8) .. high(int8)))
    symexQueryStats.setLen 0
    let r = pinExact(i59Trunc, cellKey(axStdlibBody, "math.trunc"),
                     tLabel("hit"), all)
    var units = 0
    for q in symexQueryStats: units += q.rlimitDelta
    checkpoint $r.status & " trusted=" & $r.trusted & " units=" & $units
    check r.status == sxSat
    check r.trusted
    check units > 0
    check units <= int59Budget

# ---- (4) the version floor ---------------------------------------------------

suite "INT-59 (4)":
  test "symexWalkerVersion >= 421":
    check parseInt(symexWalkerVersion) >= 421
