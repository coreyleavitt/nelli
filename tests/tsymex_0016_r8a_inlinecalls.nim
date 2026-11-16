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
##   unrolled body, `while n < 5 and c()`, and the concolic follow `if`. The
##   follow `while` test (`walkWhileFollowConcrete`) has the capture fixture
##   `cWh` and two pointer fixtures (R7-4): `cWhP` reads the loop count after
##   it, `cWhQ` reads `x` by name, which is current only if the test's
##   reconcile ran (red with it removed). The follow `while` also asks each
##   test under the facts its lowering added, as the follow `if` does: a
##   pointer write left the closure's result undecided under the pins, so the
##   loop stopped at its first test;
## * the `ifJoin` guard: no shape tried (4 fixtures: `and`, `or`, a nested
##   chain, a bitset loop) reaches it with a call. Its guard is the synthetic
##   `__sym_sc_N` (or `not` of it) or a bitset membership test (`ifJoinCalls`);
## * R8-1: a closure call that is a `case` scrutinee, or the key of a set or
##   slice membership test under a loop guard, is applied once, not once per
##   guard or member compared (`closureApplications` pins the IR, the verdict
##   fixtures the walk);
## * the return reconcile's `var` write-back (`rV1`), and the follow `while`'s
##   skip of a continuation whose new facts the pins contradict (`cWhI`).
##
## Which reconcile each fixture needs (checked by removing it in a scratch
## tree): the `if`/`elif` guard (`rI1F`, `rI2F`), the `while` test (`rW1P`),
## the final `while` test (`rW2P`), the follow `if` (`cIfF`), the `return`
## value (`rA5`), the follow `while` test (`cWhQ`).
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

# A guard that is FALSE: no arm follows, so nothing but the guard's own
# reconcile brings the local up to the pointer's write before `result += x`
# reads it (a true guard's arm is a leaf, which reconciles it first).
proc rI1F(v: int): int =
  var x = v
  let p = addr x
  let c = proc(): bool =
    p[] = p[] + 4
    false
  if c():
    result = 10
  result += x
nsut(sI1F, rI1F, 5)

proc rI2F(v: int): int =
  var x = v
  let p = addr x
  let c = proc(): bool =
    p[] = p[] + 4
    false
  if v < 0:
    result = 1
  elif c():
    result = 10
  result += x
nsut(sI2F, rI2F, 5)

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
  test "if guard that is false (pointer)":
    check inlineSites(rI1F) == @["if"]
    exitVerdict(sI1F)
  test "elif guard that is false (pointer)":
    check inlineSites(rI2F) == @["if"]
    exitVerdict(sI2F)
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

# ---- the `ifJoin` guard: no shape tried puts a call in it -------------------

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

# The follow walk's `if` guard, with a pointer write and a guard
# that does not take its arm (so no arm leaf reconciles first): the branch
# after reads `x`, which is only current if the guard reconciled.
proc cIfF(v: int) =
  var x = v
  let p = addr x
  var r = 0
  let c = proc(): bool =
    p[] = p[] + 4
    false
  if c():
    r = 1
  if x > 6:
    r = 2

proc cWhP(v: int) =
  var x = v
  let p = addr x
  var n = 0
  let c = proc(): bool =
    p[] = p[] + 2
    p[] < 6
  while c():
    inc n
  if n == 1:
    n = 100

# The follow `while` test's reconcile: the branch after the loop reads `x` by
# name, current only if the last test reconciled.
proc cWhQ(v: int) =
  var x = v
  let p = addr x
  var n = 0
  let c = proc(): bool =
    p[] = p[] + 2
    p[] < 6
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

suite "R7-3: the concolic follow guards, pointer":
  test "follow `if` that takes no arm (witness 3: x is 7 after the guard)":
    check inlineSites(cIfF) == @["if"]
    let trace = @[integerChoice(3, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cIfF, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 2
    if r.branchTrace.len == 2:
      check r.branchTrace[0].armTaken == -1
      check r.branchTrace[1].armTaken == 0

suite "R7-4: the concolic follow while, pointer":
  test "follow `while` (witness 3: two tests, so n is 1)":
    check inlineSites(cWhP) == @["while"]
    let trace = @[integerChoice(3, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cWhP, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0
  test "follow `while`, `x` read by name after the loop (reconcile live)":
    check inlineSites(cWhQ) == @["while"]
    let trace = @[integerChoice(3, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cWhQ, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0

# R8: the follow `while`'s guard divides by a drawn value that may be zero.
# Drawn 0, the first test raises `DivByZeroDefect` natively and the handler
# runs. The drain's non-raising continuation carries the new fact `d != 0`,
# which the pin `d == 0` contradicts: it is not this trace, so it is dropped
# (`followGuard`). Without that skip the pins read that continuation's guard
# as undecided, the walk stopped there and counted an ambiguous branch, and
# the bogus survivor reached the trailing `if` as a second branch record.
proc cWhI(v: int) =
  var d = v
  try:
    while 100 div d > 3:
      d += 10
  except DivByZeroDefect:
    d = -1
  if d == -1:
    d = 100

suite "R8: the concolic follow while drops a continuation the pins contradict":
  test "a drained in-bounds continuation (witness 0: the first test raises)":
    let trace = @[integerChoice(0, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(cWhI, trace, bindings)
    check r.counters.ambiguousBranches == 0
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0

# R8: a `return` whose value applies a closure that writes, through a pointer,
# the target of the callee's `var` formal. The write-back to the caller's
# variable reads the frame after the value, so the value's reconcile makes the
# formal current first.
proc vCallee(a: var int): int =
  let p = addr a
  let c = proc(): int =
    p[] = p[] + 4
    10
  return c()

proc rV1(v: int): int =
  var x = v
  let r = vCallee(x)
  r + x
nsut(sV1, rV1, 15)

suite "R8: a bare `return` reconciles before a `var` write-back":
  test "closure writes the formal's target through a pointer":
    exitVerdict(sV1)

suite "R7-walker version":
  test "walker version floor":
    check symexWalkerVersion.parseInt >= 369

# ---- R8-1: a bare closure call as a `case` scrutinee ------------------------
#
# Nim applies the scrutinee once. The parser used to embed the inline call in
# every `of` guard, so the walker applied it once per guard evaluated. Every
# fixture starts with `n` at 1, so the call returns 2: Nim takes the `2` label
# and leaves `n` at 2; a per-guard re-application sees 3 at the second guard.

proc rK1(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  case next()
  of 1: result = 100
  of 2: result = 200
  else: result = 300
  result += n
nsut(sK1, rK1, 202)

proc rK2(v: int): int =
  var n = v
  proc bump(): int =
    inc n
    n
  let next = bump
  case next()
  of 1: result = 100
  of 2: result = 200
  else: result = 300
  result += n
nsut(sK2, rK2, 202)

proc rK3(v: int): int =
  var n = v
  let h = Holder(f: proc(): int =
    inc n
    n)
  case h.f()
  of 1: result = 100
  of 2: result = 200
  else: result = 300
  result += n
nsut(sK3, rK3, 202)

# Several labels of one arm.
proc rK4(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  case next()
  of 1, 2: result = 100
  else: result = 300
  result += n
nsut(sK4, rK4, 102)

# A range label declines (`nnkRange` is not in the expression fragment), so
# it is not a site where the scrutinee could be compared twice.
proc rK5(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  case next()
  of 5 .. 9: result = 100
  of 2 .. 3: result = 200
  else: result = 300
  result += n
nsut(sK5, rK5, 202)

# A case EXPRESSION (`hoistCaseExpr`).
proc rK6(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  let r = case next()
    of 1: 100
    of 2: 200
    else: 300
  result = r + n
nsut(sK6, rK6, 202)

# The `var` write-back and a capture read after the case, by pointer.
proc rK7(v: int): int =
  var n = v
  let p = addr n
  let next = proc(): int =
    p[] = p[] + 1
    p[]
  case next()
  of 1: result = 100
  of 2: result = 200
  else: result = 300
  result += n
nsut(sK7, rK7, 202)

# Control: a scrutinee that is not a call.
proc rK0(v: int): int =
  case v + 1
  of 1: result = 100
  of 2: result = 200
  else: result = 300
nsut(sK0, rK0, 200)

# Other sites that repeat one parsed expression. A set or a slice membership
# test compares its key once per member (`k in {2, 3}` is `k == 2 or k == 3`,
# `k in a .. b` is `a <= k and k <= b`); under a loop guard the parse leaves a
# call inline (it cannot hoist: the guard re-runs), so the key was applied
# once per comparison. Bound once per test now, the loop taking the rotation.
# Under an `if` the key was bound already (controls).
proc rK8(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  var k = 0
  while next() in {2, 3}: inc k
  result = k * 10 + n
nsut(sK8, rK8, 24)

proc rK9(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  var k = 0
  while next() in 2 .. 3: inc k
  result = k * 10 + n
nsut(sK9, rK9, 24)

proc rK10(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  var k = 0
  while v > 0 and next() in {2, 3}: inc k
  result = k * 10 + n
nsut(sK10, rK10, 24)

proc rK11(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  var r = 0
  if next() in {1, 2}: r = 7
  result = r * 10 + n
nsut(sK11, rK11, 72)

proc rK12(v: int): int =
  var n = v
  let next = proc(): int =
    inc n
    n
  var r = 0
  if next() in 1 .. 2: r = 7
  result = r * 10 + n
nsut(sK12, rK12, 72)

suite "R8-1: a closure-call `case` scrutinee is applied once":
  test "lambda":
    exitVerdict(sK1)
  test "proc-valued let":
    exitVerdict(sK2)
  test "proc field of a by-value object":
    exitVerdict(sK3)
  test "multi-label arm":
    exitVerdict(sK4)
  test "range labels decline, so no second comparison":
    exhausted(sK5)
  test "case expression":
    exitVerdict(sK6)
  test "address-taken local":
    exitVerdict(sK7)
  test "control: a plain scrutinee":
    exitVerdict(sK0)
  test "set membership under a loop guard":
    exitVerdict(sK8)
  test "slice membership under a loop guard":
    exitVerdict(sK9)
  test "set membership after `and` under a loop guard":
    exitVerdict(sK10)
  test "control: set membership under an `if`":
    exitVerdict(sK11)
  test "control: slice membership under an `if`":
    exitVerdict(sK12)

suite "R8-1: the closure call appears once in the IR":
  test "case statement, every label shape":
    check closureApplications(rK1) == 1
    check closureApplications(rK2) == 1
    check closureApplications(rK3) == 1
    check closureApplications(rK4) == 1
    check closureApplications(rK7) == 1
  test "case expression":
    check closureApplications(rK6) == 1
  test "no guard holds the call any longer":
    check inlineSites(rK1) == newSeq[string]()
    check inlineSites(rK4) == newSeq[string]()
