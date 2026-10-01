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

proc zSelf(i: int) =
  ## S8ad's exhibit, verbatim.
  var a: array[3, int]
  a[0] = a[0] + 2
  if i >= 0 and i < 3 and a[i] == 2: symexTarget("self")
  if i >= 0 and i < 3 and a[i] == 1: symexTarget("self_dead")

proc zLine(x, i: int) =
  var a: array[3, int]
  a[1] = x
  if i >= 0 and i < 3 and a[i] == 5 and a[0] == 0: symexTarget("line")
  if a[0] != 0 or a[2] != 0: symexTarget("line_dead")

proc zSymRead(x, i, j: int) =
  ## Writes at literal indices, reads at two symbolic ones.
  symexAssume(x >= -100 and x <= 100)
  var a: array[4, int]
  a[2] = x
  a[3] = x + 1
  if i >= 0 and i < 4 and j >= 0 and j < 4 and a[i] + a[j] == 15:
    symexTarget("symr")
  if i >= 0 and i < 2 and j >= 0 and j < 2 and a[i] + a[j] != 0:
    symexTarget("symr_dead")

proc zLoop(x: int) =
  symexAssume(x >= -100 and x <= 100)
  var a: array[3, int]
  for k in 0 ..< 3:
    a[0] = a[0] + x
    a[2] = a[2] + k
  if a[0] == 9 and a[1] == 0: symexTarget("loop")
  if a[0] == 10 or a[2] != 3: symexTarget("loop_dead")

proc iLoop(x, i: int) =
  ## The same loop over an initialised array, read at a symbolic index.
  symexAssume(x >= -100 and x <= 100)
  var a = [0, 0, 0]
  for k in 0 ..< 3:
    a[0] = a[0] + x
    a[2] = a[2] + k
  if i >= 0 and i < 3 and a[i] == 9: symexTarget("iloop")
  if i >= 0 and i < 3 and a[i] == 10: symexTarget("iloop_dead")

proc zBranch(x: int) =
  var a: array[2, int]
  if x > 0: a[1] = x
  if a[1] == 0: symexTarget("branch")
  if a[1] == 0 and x > 0: symexTarget("branch_dead")

proc zOr(x: int) =
  var a: array[2, int]
  if (x > 3 or (a[0] = 1; true)) and a[0] == 1: symexTarget("or")
  if x > 3 and a[0] != 0: symexTarget("or_dead")

proc zAnd(x: int) =
  var a: array[2, bool]
  if x > 3 and (a[1] = true; true): discard
  if a[1]: symexTarget("and")
  if a[1] and x <= 3: symexTarget("and_dead")

proc zArrObj(v, i: int) =
  ## An array of objects: every element's every field is zero.
  var ps: array[2, P]
  ps[1].x = v
  if i >= 0 and i < 2 and ps[i].x == 4 and ps[i].y == 0: symexTarget("arrobj")
  if ps[0].x != 0 or ps[1].y != 0: symexTarget("arrobj_dead")

proc zObjArr(v, i: int) =
  ## An object holding an array.
  var h: H
  h.arr[1] = v
  h.n = h.n + 1
  if i >= 0 and i < 3 and h.arr[i] == 6 and h.n == 1: symexTarget("objarr")
  if h.arr[2] != 0 or h.n != 1: symexTarget("objarr_dead")

proc zObjArrObj(v: int) =
  ## An object holding an array of objects.
  var o: PA
  o.ps[0].y = v
  if o.ps[0].y == 3 and o.ps[1].x == 0: symexTarget("nest")
  if o.ps[1].y != 0: symexTarget("nest_dead")

proc zSeqEmpty(v: int) =
  ## A seq field is empty.
  var o: SQ
  if o.s.len == 0 and o.n == 0 and v == 1: symexTarget("seq0")
  if o.s.len != 0: symexTarget("seq0_dead")

proc zSeqField(v: int) =
  var o: SQ
  o.s = @[v]
  if o.s.len == 1 and o.s[0] == 8 and o.n == 0: symexTarget("seq")
  if o.s.len != 1 or o.n != 0: symexTarget("seq_dead")

proc zSeqLocal(v: int) =
  var s: seq[int]
  s.add v
  if s.len == 1 and s[0] == 2: symexTarget("seql")
  if s.len == 2: symexTarget("seql_dead")

proc zDistinct(i: int) =
  ## `array[3, Meters]`, which S8ad found faults the same way.
  var a: array[3, Meters]
  a[0] = a[0] + Meters(2)
  if i >= 0 and i < 3 and a[i] == Meters(2): symexTarget("dist")
  if i >= 0 and i < 3 and a[i] == Meters(1): symexTarget("dist_dead")

proc zVariant(x: int) =
  ## A variant object: tag 0, its arm's fields and the plain ones zero.
  var v: V
  if v.k == vkA and v.a == 0 and v.n == 0 and x == 1: symexTarget("var")
  if v.k != vkA or v.a != 0 or v.n != 0: symexTarget("var_dead")

proc zMatrix(v, i, j: int) =
  ## An array of arrays.
  var m: array[2, array[2, int]]
  m[1][0] = v
  if i >= 0 and i < 2 and j >= 0 and j < 2 and m[i][j] == 9: symexTarget("mat")
  if m[0][0] != 0 or m[1][1] != 0: symexTarget("mat_dead")

suite "S8aj (1): a local aggregate is zero-initialised":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "an element write then a symbolic read (S8ad's exhibit)":
    let r = run(zSelf, "self", sxSat)
    if r.status == sxSat: check r.witness[0] == 0
    discard run(zSelf, "self_dead", sxUnsat)

  test "untouched elements read zero":
    let r = run(zLine, "line", sxSat)
    if r.status == sxSat: check r.witness[1] == 1 and r.witness[0] == 5
    discard run(zLine, "line_dead", sxUnsat)

  test "reads at symbolic indices":
    let r = run(zSymRead, "symr", sxSat)
    if r.status == sxSat:
      let (x, i, j) = (r.witness[0], r.witness[1], r.witness[2])
      var a: array[4, int]
      a[2] = x
      a[3] = x + 1
      check i >= 0 and i < 4 and j >= 0 and j < 4 and a[i] + a[j] == 15
    discard run(zSymRead, "symr_dead", sxUnsat)

  test "writes in a loop":
    let r = run(zLoop, "loop", sxSat)
    if r.status == sxSat: check r.witness[0] == 3
    discard run(zLoop, "loop_dead", sxUnsat)
    ## RED, even over an initialised array: `weInternalWalkerFault`
    ## (`iteSV: kind mismatch svBV64 vs svInt`).
    let r2 = run(iLoop, "iloop", sxSat)
    if r2.status == sxSat: check r2.witness[0] == 3 and r2.witness[1] == 0
    discard run(iLoop, "iloop_dead", sxUnsat)

  test "a write on one branch":
    let r = run(zBranch, "branch", sxSat)
    if r.status == sxSat: check r.witness[0] <= 0
    discard run(zBranch, "branch_dead", sxUnsat)

  test "a write in a short-circuit operand":
    let r = run(zOr, "or", sxSat)
    if r.status == sxSat: check r.witness[0] <= 3
    discard run(zOr, "or_dead", sxUnsat)
    let r2 = run(zAnd, "and", sxSat)
    if r2.status == sxSat: check r2.witness[0] > 3
    discard run(zAnd, "and_dead", sxUnsat)

  test "an array of objects":
    let r = run(zArrObj, "arrobj", sxSat)
    if r.status == sxSat: check r.witness[0] == 4 and r.witness[1] == 1
    discard run(zArrObj, "arrobj_dead", sxUnsat)

  test "an object holding an array":
    let r = run(zObjArr, "objarr", sxSat)
    if r.status == sxSat: check r.witness[0] == 6 and r.witness[1] == 1
    discard run(zObjArr, "objarr_dead", sxUnsat)

  test "an object holding an array of objects":
    let r = run(zObjArrObj, "nest", sxSat)
    if r.status == sxSat: check r.witness[0] == 3
    discard run(zObjArrObj, "nest_dead", sxUnsat)

  test "a seq field is empty":
    let r0 = run(zSeqEmpty, "seq0", sxSat)
    if r0.status == sxSat: check r0.witness[0] == 1
    discard run(zSeqEmpty, "seq0_dead", sxUnsat)
    let r = run(zSeqField, "seq", sxSat)
    if r.status == sxSat: check r.witness[0] == 8
    discard run(zSeqField, "seq_dead", sxUnsat)

  test "a local seq is empty":
    let r = run(zSeqLocal, "seql", sxSat)
    if r.status == sxSat: check r.witness[0] == 2
    discard run(zSeqLocal, "seql_dead", sxUnsat)

  test "an array of a distinct type":
    let r = run(zDistinct, "dist", sxSat)
    if r.status == sxSat: check r.witness[0] == 0
    discard run(zDistinct, "dist_dead", sxUnsat)

  test "an array of arrays":
    let r = run(zMatrix, "mat", sxSat)
    if r.status == sxSat:
      check r.witness[0] == 9 and r.witness[1] == 1 and r.witness[2] == 0
    discard run(zMatrix, "mat_dead", sxUnsat)

  test "a variant object":
    let r = run(zVariant, "var", sxSat)
    if r.status == sxSat: check r.witness[0] == 1
    discard run(zVariant, "var_dead", sxUnsat)

  test "symexWalkerVersion >= 179":
    check parseInt(symexWalkerVersion) >= 179

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
