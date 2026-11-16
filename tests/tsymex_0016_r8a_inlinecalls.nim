## RFC-0016 review R7-1 .. R7-3. The closure calls the parser leaves INLINE.
##
## The parser hoists a named local proc's call into a statement of its own
## (`call(__sym_f_N := f(..))`, a leaf), and an operand of a larger
## expression (`c() * 10`, `c() > 0`, `v > 0 and c()`) with it. It does NOT
## hoist a value that IS the call: `closureCallIR` leaves an `iekClosureCall`
## in the expression for a by-value call with no `var` formal and no `addr`
## actual (a lambda, a proc-valued `let`, a proc field of a by-value object),
## and a bare `return c()`, a bare `if c():` / `elif c():` and a bare
## `while c():` keep it in `retExpr` / `branches.cond` / `wcond`. A guard
## cannot be hoisted anyway: short-circuit and the loop re-test must
## re-evaluate it. So a closure's effect on a capture or an address-taken
## variable is produced INSIDE the guard or the `return` value, and each of
## those is a reconcile point (`reconcileCells`): `evalCondSynced` for a guard,
## `evalReturnSynced` for the value.
##
## What these tests pin:
##
## * `inlineSites`: the parsed IR of each fixture, walked structurally, names
##   the sites (`if`, `while`, `return`) whose expression still applies a
##   closure. The list is exact per fixture: `@[]` for the shapes the parser
##   hoists (the controls), the one site for each bare shape;
## * a `return` value's reconcile (R7-1): a lambda, a proc-valued `let`, a
##   proc field, and an address-taken variable written by name and read
##   through the pointer, and the reverse;
## * each guard reconcile (R7-3), with the closure's effect read after it: a
##   plain `if`, an `elif`, a `while` test, the final test after the last
##   unrolled body, `while n < 5 and c()`, and the concolic follow `if` and
##   `while`;
## * the `ifJoin` guard is the one site no source shape reaches: its guard is
##   the synthetic `__sym_sc_N` (or `not` of it) or a bitset membership test,
##   never a call (`ifJoinCalls`).
##
## Every label is checked natively as well (`exitVerdict`).

import std/unittest
import std/strutils
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types
import "./inline_sites"

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

template exhausted(fn: typed) =
  block:
    check "ok" in hits(fn(1))
    let ok = symexFind(fn, tLabel("ok"))
    checkpoint "ok " & $ok.status & "\n" & show(ok.errors)
    check ok.status == sxUnknown
    let bad = symexFind(fn, tLabel("bad"))
    checkpoint "bad " & $bad.status & "\n" & show(bad.errors)
    check bad.status == sxUnknown

# ---- R7-1: a bare `return` of a closure call -------------------------------

proc rA1(v: int): int =
  var x = v
  let c = proc(): int =
    x = x + 4
    10
  try:
    return c()
  finally:
    result = result + x
nsut(sA1, rA1, 15)

proc rA2(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    10
  let c = bump
  try:
    return c()
  finally:
    result = result + x
nsut(sA2, rA2, 15)

type Holder = object
  f: proc(): int {.closure.}

proc rA3(v: int): int =
  var x = v
  let h = Holder(f: proc(): int =
    x = x + 4
    10)
  try:
    return h.f()
  finally:
    result = result + x
nsut(sA3, rA3, 15)

proc rA4(v: int): int =
  var x = v
  let p = addr x
  let c = proc(): int =
    x = x + 4
    10
  try:
    return c()
  finally:
    result = result + p[]
nsut(sA4, rA4, 15)

proc rA5(v: int): int =
  var x = v
  let p = addr x
  let c = proc(): int =
    p[] = p[] + 4
    10
  try:
    return c()
  finally:
    result = result + x
nsut(sA5, rA5, 15)

# Control: the call is an operand, so the parser hoists it to a leaf.
proc rH1(v: int): int =
  var x = v
  let c = proc(): int =
    x = x + 4
    10
  try:
    return c() * 10
  finally:
    result = result + x
nsut(sH1, rH1, 105)

suite "R7-1: a bare `return` of a closure call reconciles":
  test "lambda":
    check inlineSites(rA1) == @["return"]
    exitVerdict(sA1)
  test "proc-valued let":
    check inlineSites(rA2) == @["return"]
    exitVerdict(sA2)
  test "proc field of a by-value object":
    check inlineSites(rA3) == @["return"]
    exitVerdict(sA3)
  test "address-taken local written by name, read through the pointer":
    check inlineSites(rA4) == @["return"]
    exitVerdict(sA4)
  test "address-taken local written through the pointer, read by name":
    check inlineSites(rA5) == @["return"]
    exitVerdict(sA5)
  test "control: an operand call is hoisted":
    check inlineSites(rH1) == newSeq[string]()
    exitVerdict(sH1)

# ---- R7-3: bare guards that apply a closure ---------------------------------

proc rI1(v: int): int =
  var x = v
  let c = proc(): bool =
    x = x + 4
    true
  if c():
    result = 10
  result += x
nsut(sI1, rI1, 15)

proc rI1P(v: int): int =
  var x = v
  let p = addr x
  let c = proc(): bool =
    p[] = p[] + 4
    true
  if c():
    result = 10
  result += x
nsut(sI1P, rI1P, 15)

proc rI2(v: int): int =
  var x = v
  let c = proc(): bool =
    x = x + 4
    true
  if v < 0:
    result = 1
  elif c():
    result = 10
  result += x
nsut(sI2, rI2, 15)

# Controls: hoisted, so no guard holds a call.
proc rH2(v: int): int =
  var x = v
  let c = proc(): int =
    x = x + 4
    1
  if c() > 0:
    result = 10
  result += x
nsut(sH2, rH2, 15)

proc rH3(v: int): int =
  var x = v
  let c = proc(): bool =
    x = x + 4
    true
  if v > 0 and c():
    result = 10
  result += x
nsut(sH3, rH3, 15)

proc rH4(v: int): int =
  var x = v
  let c = proc(): bool =
    x = x + 4
    true
  if c() and v > 0:
    result = 10
  result += x
nsut(sH4, rH4, 15)

proc rW1(v: int): int =
  var x = v
  var n = 0
  let c = proc(): bool =
    x = x + 2
    x < 6
  while c():
    inc n
  result = x * 10 + n
nsut(sW1, rW1, 72)

proc rW1P(v: int): int =
  var x = v
  let p = addr x
  var n = 0
  let c = proc(): bool =
    p[] = p[] + 2
    p[] < 6
  while c():
    inc n
  result = x * 10 + n
nsut(sW1P, rW1P, 72)

proc rW2(v: int): int =
  var x = v
  var n = 0
  let c = proc(): bool =
    x = x + 1
    x < 7
  while c():
    inc n
  result = x * 10 + n
nsut(sW2, rW2, 75)

proc rW2P(v: int): int =
  var x = v
  let p = addr x
  var n = 0
  let c = proc(): bool =
    p[] = p[] + 1
    p[] < 7
  while c():
    inc n
  result = x * 10 + n
nsut(sW2P, rW2P, 75)

proc rW3(v: int): int =
  var x = v
  var n = 0
  let c = proc(): bool =
    x = x + 1
    x < 8
  while c():
    inc n
  result = x * 10 + n
nsut(sW3, rW3, 86)

proc rW4(v: int): int =
  var x = v
  var n = 0
  let c = proc(): bool =
    x = x + 2
    x < 6
  while n < 5 and c():
    inc n
  result = x * 10 + n
nsut(sW4, rW4, 72)

suite "R7-3: a bare guard applying a closure reconciles":
  test "if guard (capture)":
    check inlineSites(rI1) == @["if"]
    exitVerdict(sI1)
  test "if guard (pointer)":
    check inlineSites(rI1P) == @["if"]
    exitVerdict(sI1P)
  test "elif guard":
    check inlineSites(rI2) == @["if"]
    exitVerdict(sI2)
  test "controls: an operand call is hoisted out of the guard":
    check inlineSites(rH2) == newSeq[string]()
    exitVerdict(sH2)
    check inlineSites(rH3) == newSeq[string]()
    exitVerdict(sH3)
    check inlineSites(rH4) == newSeq[string]()
    exitVerdict(sH4)
  test "while test (capture)":
    check inlineSites(rW1) == @["while"]
    exitVerdict(sW1)
  test "while test (pointer)":
    check inlineSites(rW1P) == @["while"]
    exitVerdict(sW1P)
  test "final test after the last unrolled body (capture)":
    check inlineSites(rW2) == @["while"]
    exitVerdict(sW2)
  test "final test after the last unrolled body (pointer)":
    check inlineSites(rW2P) == @["while"]
    exitVerdict(sW2P)
  test "a loop still active after the bound is tainted":
    check inlineSites(rW3) == @["while"]
    exhausted(sW3)
  test "`while n < 5 and c()` lowers to a guard `if` in the body":
    check inlineSites(rW4) == @["if"]
    exitVerdict(sW4)

# ---- the `ifJoin` guard: no source shape puts a call in it -------------------

proc jAnd(v: int): int =
  var x = v
  let c = proc(): bool =
    x = x + 4
    true
  if v > 0 and c() and x > 0:
    result = 10
  result += x

proc jOr(v: int): int =
  var x = v
  let c = proc(): bool =
    x = x + 4
    true
  if v < 0 or c() or x < 0:
    result = 10
  result += x

proc jNest(v: int): int =
  var x = v
  let c = proc(): bool =
    x = x + 4
    true
  if (v < 0 or c()) and (c() or v > 3):
    result = 10
  result += x

type Digit = range[0 .. 3]

proc jSet(v: int): int =
  var s: set[Digit] = {1, 3}
  for d in s:
    result += d.int

suite "R7-3: the ifJoin guard holds no call":
  test "short-circuit chains and a bitset loop: every join guard is call-free":
    for (joins, withCall) in [ifJoinCalls(jAnd), ifJoinCalls(jOr),
                              ifJoinCalls(jNest), ifJoinCalls(jSet)]:
      check joins > 0
      check withCall == 0

# ---- the concolic follow walks ----------------------------------------------

proc cIf(v: int) =
  var x = v
  var r = 0
  let c = proc(): bool =
    x = x + 4
    true
  if c():
    r = 1
  if x > 6:
    r = r + 2
  if r == 3:
    r = 4

proc cWh(v: int) =
  var x = v
  var n = 0
  let c = proc(): bool =
    x = x + 2
    x < 6
  while c():
    inc n
  if x * 10 + n == 71:
    n = 100

suite "R7-3: the concolic follow guards":
  test "follow `if` (witness 3: x is 7 after the guard)":
    check inlineSites(cIf) == @["if"]
    let trace = @[integerChoice(3, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cIf, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 3
    if r.branchTrace.len == 3:
      check r.branchTrace[0].armTaken == 0
      check r.branchTrace[1].armTaken == 0
      check r.branchTrace[2].armTaken == 0
  test "follow `while` (witness 3: x is 7 after the loop)":
    check inlineSites(cWh) == @["while"]
    let trace = @[integerChoice(3, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cWh, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0

suite "R7-walker version":
  test "walker version floor":
    check symexWalkerVersion.parseInt >= 367
