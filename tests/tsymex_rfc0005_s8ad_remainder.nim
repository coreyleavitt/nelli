## RFC-0005 (soundness channels) slice S8ad -- S8ac's remainder.
##
## This slice closes:
##   (1) a local distinct value with no distinct-typed parameter. `D(x)` is
##       the parser's identity (S8p), so `var m = Meters(0)` binds the bare
##       base, and the first borrowed arithmetic on it (`m + Meters(1)`)
##       re-boxed into a distinct sort no allocation had created:
##       `weInternalWalkerFault` ("reboxDistinct: distinct sort `Meters`
##       not allocated"). The borrow node now carries the distinct TYPE and
##       the re-box allocates the sort (`ensureDistinctSort`). A boxed value
##       met its bare base in the element fold of a symbolic array read
##       (`iteSV: kind mismatch`); the merge is of the bases;
##   (2) `start < 0 and y > 1 and start div y == start` (UNSAT) over a scan
##       offset (`start` a width-stamped Int, `y` a bitvector read through
##       `bv2int`) ran out of `seqQueryRLimit` (40M steps with the
##       theory-free re-check) to `sxUnknown`: Z3 relates `a div b` to `a`
##       only through its nonlinear core. Every query is now decided with
##       the linear bounds of its Int quotients and remainders beside it
##       (`divRangeFacts`; the pair itself when `|a| < |b|`, which Z3
##       4.13.4 needs), and with the Int value of a negated bitvector
##       (`start mod y <= -y`, the remainder's twin, same 40M). Those are
##       theorems, so the query's models are unchanged; (3) checks each one
##       against Z3's own `div`/`mod`/`bv2int` on a grid of numerals.
## Step counts come from `-d:symexQueryStats` (this file's `.nim.cfg`):
## `rlimitDelta` is one query's own count, deterministic for a Z3 build.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8ad_remainder needs -d:symexQueryStats (its .nim.cfg)".}

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc walkSteps(): int =
  ## The walk's Z3 steps: the sum of each query's own count.
  for q in symexQueryStats: result += q.rlimitDelta

# ---- (1) a local distinct value ---------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}

proc dLine(x: int) =
  var m = Meters(0)
  m = m + Meters(1)
  if m == Meters(1) and x == 3: symexTarget("line")
  if m == Meters(2): symexTarget("line_dead")

proc dJoin(x: int) =
  var m = Meters(0)
  if x > 0: m = m + Meters(1)
  if m == Meters(1): symexTarget("join")
  if x <= 0 and m == Meters(1): symexTarget("join_dead")

proc dLoop(x: int) =
  symexAssume(x >= -100 and x <= 100)
  var m = Meters(0)
  for i in 0 ..< 3: m = m + Meters(x)
  if m == Meters(9): symexTarget("loop")
  if m == Meters(10): symexTarget("loop_dead")

proc dOr(x: int) =
  var m = Meters(0)
  if (x > 3 or (m = m + Meters(1); true)) and m == Meters(1):
    symexTarget("or")

proc dArr(i: int) =
  var a = [Meters(1), Meters(2), Meters(3)]
  a[0] = a[0] + Meters(2)
  if i >= 0 and i < 3 and a[i] == Meters(3): symexTarget("arr")
  if i >= 0 and i < 3 and a[i] == Meters(1): symexTarget("arr_dead")

suite "S8ad (1): a local distinct value is modelled":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "a borrowed sum of a local distinct value":
    ## RED: `weInternalWalkerFault` (reboxDistinct: distinct sort `Meters`
    ## not allocated), both targets.
    let r = run(dLine, "line", sxSat)
    if r.status == sxSat: check r.witness[0] == 3
    discard run(dLine, "line_dead", sxUnsat)

  test "a borrowed sum on one branch":
    ## RED: `weInternalWalkerFault`, both targets.
    let r = run(dJoin, "join", sxSat)
    if r.status == sxSat: check r.witness[0] > 0
    discard run(dJoin, "join_dead", sxUnsat)

  test "a borrowed sum in a loop":
    ## RED: `weInternalWalkerFault`, both targets.
    let r = run(dLoop, "loop", sxSat)
    if r.status == sxSat: check r.witness[0] == 3
    discard run(dLoop, "loop_dead", sxUnsat)

  test "a borrowed sum in a short-circuit operand":
    ## RED: `weInternalWalkerFault`.
    let r = run(dOr, "or", sxSat)
    if r.status == sxSat: check r.witness[0] <= 3

  test "a boxed element beside bare ones, read at a symbolic index":
    ## RED: `weInternalWalkerFault` (the re-box), then, with only the sort
    ## allocated, `iteSV: kind mismatch svBV64 vs svDistinct`.
    let r = run(dArr, "arr", sxSat)
    if r.status == sxSat: check r.witness[0] in [0, 2]
    discard run(dArr, "arr_dead", sxUnsat)

# ---- (2) division under the sequence theory ---------------------------------

type ScanError = object of CatchableError

proc readCStr(data: seq[byte], offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (acc, i + 1)
    acc.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

template scan() =
  ## Makes `start` a scan offset (a width-stamped Int, B4) and puts `data`,
  ## a seq, in every query of the walk.
  if start < 0: return
  try:
    let (k, p) = readCStr(data, start)
    if k.len == 2 and p == start + 3: symexTarget("hit")
  except ScanError:
    discard

proc sNegDiv(data: seq[byte], start, y: int) =
  if start < 0 and y > 1 and start div y == start: symexTarget("t")
  scan()
proc sPosDiv(data: seq[byte], start, y: int) =
  if start > 0 and y > 1 and start div y == start: symexTarget("t")
  scan()
proc sNegDivNegY(data: seq[byte], start, y: int) =
  if start < -1 and y < -1 and start div y <= start: symexTarget("t")
  scan()
proc sNegModPos(data: seq[byte], start, y: int) =
  if start < 0 and y > 1 and start mod y > 0: symexTarget("t")
  scan()
proc sNegModLow(data: seq[byte], start, y: int) =
  if start < 0 and y > 1 and start mod y <= -y: symexTarget("t")
  scan()
proc sPosModHi(data: seq[byte], start, y: int) =
  if start > 0 and y > 1 and start mod y >= y: symexTarget("t")
  scan()
proc sNegModLowSat(data: seq[byte], start, y: int) =
  if start < 0 and y > 1 and start mod y <= 1 - y: symexTarget("t")
  scan()
proc sNegDivSat(data: seq[byte], start, y: int) =
  if start < 0 and y > 1 and start div y == start + 1: symexTarget("t")
  scan()
{.push overflowChecks: off.}
proc uNegDiv(data: seq[byte], start, y: int) =
  if start < 0 and y > 1 and start div y == start: symexTarget("t")
  scan()
proc uPosDiv(data: seq[byte], start, y: int) =
  if start > 0 and y > 1 and start div y == start: symexTarget("t")
  scan()
{.pop.}

const exactUnchecked = SymexSettings(integerSemantics: isExact,
                                     arithChecks: {acDivByZero, acRange})

suite "S8ad (2): an Int quotient under the sequence theory decides":

  template bounded(fn: typed, want: SymexStatusKind, maxSteps: int,
                   st: static SymexSettings = SymexSettings()): untyped =
    block:
      symexQueryStats = @[]
      let r = symexFind(fn, tLabel("t"), st)
      checkpoint astToStr(fn) & " " & $r.status & " " & show(r.errors)
      checkpoint symexQueryStatsSummary()
      check r.status == want
      check not r.errors.hasKind(beSolverUndef)
      check walkSteps() <= maxSteps
      r

  test "start < 0 and y > 1 and start div y == start is refuted":
    ## RED: `sxUnknown` (`beSolverUndef`, seqQueryRLimit): 40.4M steps,
    ## ~260 s. Now 0.88M (Z3 5.1), 1.19M (4.13.4, which the bounds alone
    ## left at 40M: it needs the `|a| < |b|` pair).
    discard bounded(sNegDiv, sxUnsat, 3_000_000)

  test "the symmetric quotients are refuted":
    ## RED: `start > 0` `sxUnknown` at 80.5M steps (~490 s). Now 0.85M
    ## (5.1), 1.08M (4.13.4).
    discard bounded(sPosDiv, sxUnsat, 3_000_000)
    discard bounded(sNegDivNegY, sxUnsat, 3_000_000)

  test "the remainder shapes are refuted":
    ## RED: `start mod y <= -y` `sxUnknown` at 40.4M (~150 s); it needs the
    ## negated bitvector's Int value too. The other two decided at the base.
    discard bounded(sNegModLow, sxUnsat, 3_000_000)
    discard bounded(sNegModPos, sxUnsat, 3_000_000)
    discard bounded(sPosModHi, sxUnsat, 3_000_000)

  test "the live neighbours keep their models":
    ## The facts are theorems: the SAT shapes next to the dead ones stay
    ## SAT, with witnesses the compiled code agrees with.
    let r1 = bounded(sNegModLowSat, sxSat, 3_000_000)
    if r1.status == sxSat:
      let (start, y) = (r1.witness[1], r1.witness[2])
      check start < 0 and y > 1 and start mod y <= 1 - y
    let r2 = bounded(sNegDivSat, sxSat, 3_000_000)
    if r2.status == sxSat:
      let (start, y) = (r2.witness[1], r2.witness[2])
      check start < 0 and y > 1 and start div y == start + 1

  test "the exact unchecked quotients are refuted":
    ## RED: past the 1500 s probe bound at the base.
    discard bounded(uNegDiv, sxUnsat, 3_000_000, exactUnchecked)
    discard bounded(uPosDiv, sxUnsat, 3_000_000, exactUnchecked)

# ---- (3) the facts are theorems ---------------------------------------------

suite "S8ad (3): every fact divRangeFacts asserts is valid":

  proc allValid(ctx: Z3Context, facts: seq[Z3Bool]): bool =
    ## Each fact is ground here, so its negation is UNSAT iff it holds.
    result = true
    for f in facts:
      if querySolver(ctx, [not f], 0).check() != zsUnsat: return false

  test "the quotient and remainder bounds hold for Z3's div and mod":
    let ctx = newContext()
    var n = 0
    for a in -13 .. 13:
      for b in -6 .. 6:
        if b == 0: continue
        let ai = mkInt(ctx, a)
        let bi = mkInt(ctx, b)
        let q = (ai div bi) == (ai div bi)
        let r = (ai mod bi) == (ai mod bi)
        let facts = divRangeFacts(ctx, [q, r])
        check facts.len == 19
        checkpoint $a & " div/mod " & $b
        check allValid(ctx, facts)
        n += facts.len
    check n > 0

  test "the negated bitvector's Int value holds at every width-8 value":
    let ctx = newContext()
    for v in 0 .. 255:
      let y = mkBitVec[8](ctx, v)
      let z = mkBitVec[8](ctx, 0)
      var roots: seq[Z3Bool]
      for neg in [-y, z - y]:
        for signed in [false, true]:
          let t = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw,
                                                             neg.raw, signed))
          roots.add t == t
      let facts = divRangeFacts(ctx, roots)
      check facts.len >= 2
      checkpoint "y = " & $v
      check allValid(ctx, facts)

  test "symexWalkerVersion >= 175":
    check parseInt(symexWalkerVersion) >= 175
