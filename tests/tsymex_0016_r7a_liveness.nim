## RFC-0016 review R6-1 .. R6-4. The liveness of each `reconcileCells` point,
## for the shapes whose closure is a NAMED LOCAL PROC.
##
## The parser hoists a named local proc's call into a statement of its own
## (`call(__sym_f_N := f(..))`, a leaf), wherever it stands in an expression:
## a `while` test, an `if`/`elif` condition, a short-circuit operand, a
## `return` value that is not the call itself, an `if`/`case` expression, a
## `case` scrutinee. So for these shapes an effect on a capture, an
## address-taken variable or an element is produced at a leaf statement, and
## that is the only place a reconcile can matter. This file pins exactly that.
##
## It is NOT true of every call. A by-value closure call (a lambda, a
## proc-valued `let`, a proc field) stays INLINE when it is the whole
## expression of a `return` or of a bare guard (`if c():`, `elif c():`,
## `while c():`, and `while n < 5 and c():`, which lowers to a guard `if`).
## Those are reconcile points that matter (R7-1, R7-3), each with a red-able
## test in `tsymex_0016_r8a_inlinecalls`. No shape tried reaches
## the `ifJoin` guard with a call (pinned there). The invariant: every evaluation point
## that can produce an effect reconciles where it produces it.
##
## What these tests pin:
##
## * `noInlineCall`: the parsed IR of each shape below has no site whose
##   expression applies a call (`inlineSites` is empty), and the closure is
##   still called (`bump#` is mentioned), so each shape's call is a leaf and the
##   reconcile there is the one that matters;
## * the end-to-end verdicts of the same shapes, a final `while` test after the
##   last unrolled body included (an exhausted loop is tainted, not wrong);
## * a raise resumed in its handler (`syncCapCellsFromCells`,
##   `syncAddrCellsFromHeap`, `syncElemCellsFromHeap`): each of a capture, an
##   address-taken variable and an element a raising callee wrote through its
##   cell, read after the `except`. Removing any one of the three calls fails
##   its own test.
##
## Every label is checked natively as well (`exitVerdict`).

from ./s8cu_helpers import named
import std/[unittest, strutils, macros]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/dsl_parser
import "./inline_sites"

macro irOf(p: typed): untyped =
  newLit(render(parseProc(p.getImpl).body))

template noInlineCall(fn: typed; callee: static string) =
  ## The closure is called, and no guard or return value applies a call.
  block:
    let ir = irOf(fn)
    checkpoint ir
    check ir.count(callee & "#") > 0
    check inlineSites(fn) == newSeq[string]()

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template nsut(nm, rn: untyped; want: int) =
  proc nm(v: int) =
    if v != 1: return
    let r = rn(v)
    if r == want: symexTarget("ok")
    if r != want: symexTarget("bad")

template exitVerdict(fn: typed) =
  block:
    check "ok" in hits(fn(1))
    let ok = symexFind(fn, tLabel("ok"))
    checkpoint "ok " & $ok.status & "\n" & show(ok.errors)
    check ok.status == sxSat
    let bad = symexFind(fn, tLabel("bad"))
    checkpoint "bad " & $bad.status & "\n" & show(bad.errors)
    check bad.status == sxUnsat

# ---- R6-1: guards carry no call --------------------------------------------

proc rSc(v: int): int =
  var x = v
  proc bump(): bool =
    x = x + 4
    true
  if v > 0 and bump():
    result = x * 10
  result += x
nsut(sSc, rSc, 55)

proc rScP(v: int): int =
  var x = v
  let p = addr x
  proc bump(): bool =
    x = x + 4
    true
  if v > 0 and bump():
    result = p[] * 10
  result += x
nsut(sScP, rScP, 55)

proc rWg(v: int): int =
  var x = v
  var n = 0
  proc bump(): bool =
    x = x + 2
    x < 6
  while bump():
    inc n
  result = x * 10 + n
nsut(sWg, rWg, 72)

proc rWh(v: int): int =
  var x = v
  var n = 0
  proc bump(): bool =
    x = x + 2
    x < 6
  while n < 5 and bump():
    inc n
  result = x * 10 + n
nsut(sWh, rWh, 72)

suite "R6-1: a guard's closure call is a statement of its own":
  test "short-circuit `if` guard":
    noInlineCall(rSc, "bump")
    exitVerdict(sSc)
  test "short-circuit `if` guard, read through a pointer":
    noInlineCall(rScP, "bump")
    exitVerdict(sScP)
  test "plain `while` test":
    noInlineCall(rWg, "bump")
    exitVerdict(sWg)
  test "short-circuit `while` test":
    noInlineCall(rWh, "bump")
    exitVerdict(sWh)

# ---- R6-2: the final while test after the last unrolled body ---------------

proc rWf(v: int): int =
  var x = v
  var n = 0
  proc bump(): bool =
    x = x + 1
    x < 7
  while bump():
    inc n
  result = x * 10 + n
nsut(sWf, rWf, 75)

proc rWfP(v: int): int =
  var x = v
  let p = addr x
  var n = 0
  proc bump(): bool =
    p[] = p[] + 1
    p[] < 7
  while bump():
    inc n
  result = x * 10 + n
nsut(sWfP, rWfP, 75)

# The same loops, one iteration longer than the bound: the path leaves
# exhausted and tainted, so neither label is decided.
proc rWx(v: int): int =
  var x = v
  var n = 0
  proc bump(): bool =
    x = x + 1
    x < 8
  while bump():
    inc n
  result = x * 10 + n
nsut(sWx, rWx, 86)

proc rWxP(v: int): int =
  var x = v
  let p = addr x
  var n = 0
  proc bump(): bool =
    p[] = p[] + 1
    p[] < 8
  while bump():
    inc n
  result = x * 10 + n
nsut(sWxP, rWxP, 86)

template exhausted(fn: typed) =
  block:
    check "ok" in hits(fn(1))
    let ok = symexFind(fn, tLabel("ok"))
    checkpoint "ok " & $ok.status & "\n" & show(ok.errors)
    check ok.status == sxUnknown
    check ok.errors.named(beBudgetExhausted)
    let bad = symexFind(fn, tLabel("bad"))
    checkpoint "bad " & $bad.status & "\n" & show(bad.errors)
    check bad.status == sxUnknown
    check bad.errors.named(beBudgetExhausted)

suite "R6-2: the final test after the unroll bound":
  test "default bound is 5":
    check defaultSymexSettings().budget.maxLoopUnwind == 5
  test "a guard closure ends the loop on the final test (capture)":
    exitVerdict(sWf)
  test "a guard closure ends the loop on the final test (pointer)":
    exitVerdict(sWfP)
  test "a loop still active after the bound is tainted (capture)":
    exhausted(sWx)
  test "a loop still active after the bound is tainted (pointer)":
    exhausted(sWxP)

# ---- R6-3: probes for the return value and the unhoisted guards ------------

proc bumpedT1(v: int): bool =
  var x = v
  proc bump(): bool =
    x = x + 4
    true
  try:
    return v > 0 and bump()
  finally:
    result = result and x == 5
proc rT1(v: int): int = ord(bumpedT1(v))
nsut(sT1, rT1, 1)

proc rT2(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    10
  try:
    return (if v > 0: bump() else: 0)
  finally:
    result = result + x
nsut(sT2, rT2, 15)

proc rT3(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    10
  try:
    return (case v
            of 1: bump()
            else: 0)
  finally:
    result = result + x
nsut(sT3, rT3, 15)

proc rT4(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    10
  try:
    return (if v > 0 and x > 0: bump() else: 0)
  finally:
    result = result + x
nsut(sT4, rT4, 15)

proc rI1(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    1
  if bump() + x > 0:
    result = 10
  result += x
nsut(sI1, rI1, 15)

proc rI2(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    1
  if v < 0:
    result = 1
  elif bump() + x > 0:
    result = 10
  result += x
nsut(sI2, rI2, 15)

proc rI3(v: int): int =
  var x = v
  proc bump(): bool =
    x = x + 4
    true
  if (if v > 0: bump() else: false):
    result = 10
  result += x
nsut(sI3, rI3, 15)

proc rI4(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    1
  case bump()
  of 1: result = 10
  else: discard
  result += x
nsut(sI4, rI4, 15)

proc rI5(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    1
  case bump()
  of 0: result = 1
  of 1: result = 10
  else: discard
  result += x
nsut(sI5, rI5, 15)

suite "R6-3: a return value, an `elif`, an expression and a `case` scrutinee":
  test "T1 return short-circuit":
    noInlineCall(bumpedT1, "bump")
    exitVerdict(sT1)
  test "T2 return if-expression":
    noInlineCall(rT2, "bump")
    exitVerdict(sT2)
  test "T3 return case-expression":
    noInlineCall(rT3, "bump")
    exitVerdict(sT3)
  test "T4 return if-expression with short-circuit":
    noInlineCall(rT4, "bump")
    exitVerdict(sT4)
  test "I1 if condition with an operand call":
    noInlineCall(rI1, "bump")
    exitVerdict(sI1)
  test "I2 elif condition with an operand call":
    noInlineCall(rI2, "bump")
    exitVerdict(sI2)
  test "I3 if condition an if-expression":
    noInlineCall(rI3, "bump")
    exitVerdict(sI3)
  test "I5 a `case` scrutinee with two `of` arms is evaluated once":
    noInlineCall(rI5, "bump")
    check irOf(rI5).count("bump#") == 1
    exitVerdict(sI5)
  test "I4 case scrutinee":
    noInlineCall(rI4, "bump")
    exitVerdict(sI4)

# ---- raise resumes ----------------------------------------------------------

proc rRzC(v: int): int =
  var x = v
  proc thrower() =
    x = x + 4
    raise newException(ValueError, "boom")
  try:
    thrower()
  except ValueError:
    discard
  result = x * 10 + 1
nsut(sRzC, rRzC, 51)

proc runIt(f: proc ()) =
  f()
  raise newException(ValueError, "boom")

proc rRzF(v: int): int =
  var x = v
  proc inc4() =
    x = x + 4
  try:
    runIt(inc4)
  except ValueError:
    discard
  result = x * 10 + 1
nsut(sRzF, rRzF, 51)

proc rRzP(v: int): int =
  var y = v
  let p = addr y
  proc thrower() =
    p[] = 6
    raise newException(ValueError, "boom")
  try:
    thrower()
  except ValueError:
    discard
  result = y * 10 + 1
nsut(sRzP, rRzP, 61)

proc rRzE(v: int): int =
  var s = @[v, v]
  let e = addr s[0]
  proc thrower() =
    e[] = 7
    raise newException(ValueError, "boom")
  try:
    thrower()
  except ValueError:
    discard
  result = s[0] * 10 + 1
nsut(sRzE, rRzE, 71)

proc rRz(v: int): int =
  var x = v
  var y = v
  let p = addr y
  var s = @[v, v]
  let e = addr s[0]
  proc thrower() =
    x = x + 4
    p[] = 6
    e[] = 7
    raise newException(ValueError, "boom")
  try:
    thrower()
  except ValueError:
    discard
  result = x * 100 + y * 10 + s[0]
nsut(sRz, rRz, 567)

suite "R6-4: a raise resumes with the cells' values":
  test "a raising callee wrote a capture":
    exitVerdict(sRzC)
  test "a callee applied the capture's closure, then raised":
    exitVerdict(sRzF)
  test "a raising callee wrote an address-taken variable through a pointer":
    exitVerdict(sRzP)
  test "a raising callee wrote an element through a pointer":
    exitVerdict(sRzE)
  test "all three at once":
    exitVerdict(sRz)

suite "R6-walker version":
  test "walker version floor":
    check symexWalkerVersion.parseInt >= 366
