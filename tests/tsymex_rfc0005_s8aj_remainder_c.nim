## RFC-0005 (soundness channels) slice S8aj -- S8ad's remainder.
##
## This slice closes:
##   (1) an uninitialised local array with an element write
##       (`var a: array[3, int]; a[0] = a[0] + 2; a[i]`). The parser
##       declined the zero-init (`zeroValueForType` had no array arm), left
##       the name unbound, and the element write bound it to a scalar: the
##       read then asserted (`weInternalWalkerFault`, "iekIndex on non-array
##       kind=svBV64"). An array, an object (`itTuple`) and a seq now take
##       Nim's `default(T)` (`mkZeroValue`, lowered by `defaultZero`), so
##       arrays of objects, objects holding arrays and seq fields are
##       zero-initialised too. A loop's element merge met an Int on one
##       path and a bitvector on the other (`iteSV` asserted); both are the
##       same Nim integer, so the merge reconciles them.
##   (2) an unchecked sum that wraps (`start >= 0 and y > 1 and
##       start + (y + 1) == start`, UNSAT, beside a sequence): `sxUnknown`
##       at 40.6M steps on Z3 5.1 and 40.9M on 4.13.4. `wrapIntToWidth`
##       wraps as `lo + (r - lo) mod 2^W`, and an overflowing sum puts
##       `r - lo` in `[2^W, 2^(W+1))`, one window past S8ad's `|a| < |b|`
##       pair. `divRangeFacts` now asserts that window too.
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8aj_remainder`, `tsymex_rfc0005_s8aj_remainder_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 66 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8aj_remainder needs -d:symexQueryStats (its .nim.cfg)".}

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

# ---- (1) zero-init of local aggregates --------------------------------------

type
  Meters = distinct int
  P = object
    x, y: int
  H = object
    arr: array[3, int]
    n: int
  SQ = object
    s: seq[int]
    n: int
  PA = object
    ps: array[2, P]
  VK = enum vkA, vkB
  V = object
    n: int
    case k: VK
    of vkA: a: int
    of vkB: b: array[2, int]

proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}

# ---- (2) an unchecked sum that wraps ----------------------------------------

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
  ## Makes `start` a scan offset (a width-stamped Int) and puts `data`, a
  ## seq, in every query of the walk, as S8ad's suite does.
  if start < 0: return
  try:
    let (k, p) = readCStr(data, start)
    if k.len == 2 and p == start + 3: symexTarget("hit")
  except ScanError:
    discard

{.push overflowChecks: off.}
proc uAddWrap(data: seq[byte], start, y: int) =
  if start >= 0 and y > 1 and start + (y + 1) == start: symexTarget("t")
  scan()
proc uAddWrapSat(data: seq[byte], start, y: int) =
  if start >= 0 and y > 1 and start + (y + 1) < start: symexTarget("t")
  scan()
proc uSubWrap(data: seq[byte], start, y: int) =
  if start >= 0 and y > 1 and start - (y + 1) == start: symexTarget("t")
  scan()
{.pop.}

const exactUnchecked = SymexSettings(integerSemantics: isExact,
                                     arithChecks: {acDivByZero, acRange})

proc walkSteps(): int =
  ## The walk's Z3 steps: the sum of each query's own count.
  for q in symexQueryStats: result += q.rlimitDelta

suite "S8aj (2): an unchecked sum that wraps decides":

  template bounded(fn: typed, want: SymexStatusKind, maxSteps: int): untyped =
    block:
      symexQueryStats = @[]
      let r = symexFind(fn, tLabel("t"), exactUnchecked)
      checkpoint astToStr(fn) & " " & $r.status & " " & show(r.errors)
      checkpoint symexQueryStatsSummary()
      check r.status == want
      check not r.errors.hasKind(beSolverUndef)
      check walkSteps() <= maxSteps
      r

  test "start >= 0 and y > 1 and start + (y + 1) == start is refuted":
    ## RED: `sxUnknown` (`beSolverUndef`, seqQueryRLimit): 40.6M steps
    ## (Z3 5.1, ~410 s), 40.9M (4.13.4).
    discard bounded(uAddWrap, sxUnsat, 3_000_000)

  test "the difference twin is refuted":
    discard bounded(uSubWrap, sxUnsat, 3_000_000)

  test "the overflowing sum is still found, and it does overflow":
    let r = bounded(uAddWrapSat, sxSat, 3_000_000)
    if r.status == sxSat:
      let (start, y) = (r.witness[1], r.witness[2])
      check start >= 0 and y > 1 and start +% (y +% 1) < start

suite "S8aj (2): the window facts are theorems":

  proc allValid(ctx: Z3Context, facts: seq[Z3Bool]): bool =
    ## Each fact is ground here, so its negation is UNSAT iff it holds.
    result = true
    for f in facts:
      if querySolver(ctx, [not f], 0).check() != zsUnsat: return false

  proc intNum(ctx: Z3Context, text: string): Z3Int =
    wrap[Z3Int](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring,
                                               ctx.checkErr Z3_mk_int_sort(ctx.raw)))

  test "they hold at 2^64, the wrap's own divisor":
    let ctx = newContext()
    const m = "18446744073709551616"
    for a in ["0", "1", "18446744073709551615", m, "18446744073709551617",
              "27670116110564327424", "36893488147419103231",
              "36893488147419103232", "-1", "-18446744073709551616",
              "-18446744073709551617"]:
      for b in [m, "-" & m]:
        let (ai, bi) = (intNum(ctx, a), intNum(ctx, b))
        let facts = divRangeFacts(ctx, [(ai div bi) == (ai div bi),
                                        (ai mod bi) == (ai mod bi)])
        checkpoint a & " div/mod " & b
        check facts.len == 23
        check allValid(ctx, facts)

  test "the check rejects a window one too wide":
    ## The window facts with `2b` in place of `2b - 1`: false at `a == 2b`,
    ## so the grid must catch it there and nowhere else.
    let ctx = newContext()
    let (one, two) = (mkInt(ctx, 1), mkInt(ctx, 2))
    var rejected: seq[(int, int)]
    for a in -13 .. 13:
      for b in -6 .. 6:
        if b == 0: continue
        let (ai, bi) = (mkInt(ctx, a), mkInt(ctx, b))
        let wide = (bi >= one) and (bi <= ai) and (ai <= two * bi)
        let broken = @[implies(wide, (ai mod bi) == ai - bi),
                       implies(wide, (ai div bi) == one)]
        if not allValid(ctx, broken): rejected.add (a, b)
    check rejected == @[(2, 1), (4, 2), (6, 3), (8, 4), (10, 5), (12, 6)]

  test "symexWalkerVersion >= 179 (item 2)":
    check parseInt(symexWalkerVersion) >= 179
