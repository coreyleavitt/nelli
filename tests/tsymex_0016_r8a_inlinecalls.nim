## RFC-0016 review R7-1 .. R7-3. The closure calls the parser leaves INLINE.
##
## The parser hoists a named local proc's call into a statement of its own
## (`call(__sym_f_N := f(..))`, a leaf). It does not hoist every closure
## application: `closureCallIR` leaves an `iekClosureCall` in the expression
## for a by-value call with no `var` formal and no `addr` actual (a lambda, a
## proc-valued `let`, a proc field of a by-value object), `mkHofCall` builds a
## `map`/`filter`/`fold` with a closure inline, and a `return` value or a
## guard under `inGuardCond` is not hoisted. A guard cannot be: short-circuit
## and the loop re-test must re-evaluate it. So a closure's effect on a
## capture or an address-taken variable is produced INSIDE a guard or a
## `return` value, and each of those is a reconcile point
## (`reconcileCells`): `evalCondSynced` for a guard, `isReturn` for the value.
##
## What these tests pin:
##
## * `inlineSites`: the parsed IR of each shape, walked structurally, names the
##   sites (`if`, `while`, `return`) whose expression still applies a closure.
##   It documents that an inline call occurs, so each site needs an effect
##   test; the expected list per fixture is exact;
## * a `return` value's reconcile (R7-1), for a lambda, a proc-valued `let`, a
##   proc field, `map`/`filter` and an address-taken variable;
## * each guard reconcile (R7-3), with the lambda's effect read after it: the
##   plain `if`, an `elif`, the short-circuit join, a `while` test, the final
##   test after the last unrolled body, and the concolic follow `if` and
##   `while`.
##
## Every label is checked natively as well (`exitVerdict`).

import std/[unittest, strutils, macros, sequtils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types
import nelli/smt/dsl_parser

proc collectSites(s: IRStmt; acc: var seq[string]) =
  if s == nil: return
  case s.kind
  of isBlock:
    for c in s.stmts: collectSites(c, acc)
  of isIf:
    for b in s.branches:
      if irHasCall(b.cond): acc.add "if"
      collectSites(b.body, acc)
    collectSites(s.elseBody, acc)
  of isWhile:
    if irHasCall(s.wcond): acc.add "while"
    collectSites(s.wbody, acc)
  of isTry:
    collectSites(s.tryBody, acc)
    for h in s.tryHandlers: collectSites(h.body, acc)
    collectSites(s.tryFinally, acc)
  of isReturn:
    if irHasCall(s.retExpr): acc.add "return"
  else: discard

macro inlineSites(p: typed): untyped =
  var acc: seq[string]
  collectSites(parseProc(p.getImpl).body, acc)
  newLit(acc)

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

# ---- R7-1: a `return` value that applies a closure -------------------------

proc rA1(v: int): int =
  var x = v
  let c = proc(): int =
    x = x + 4
    10
  try:
    return c() * 10
  finally:
    result = result + x
nsut(sA1, rA1, 105)

proc rA2(v: int): int =
  var x = v
  proc bump(): int =
    x = x + 4
    10
  let c = bump
  try:
    return c() * 10
  finally:
    result = result + x
nsut(sA2, rA2, 105)

type Holder = object
  f: proc(): int {.closure.}

proc rA3(v: int): int =
  var x = v
  let h = Holder(f: proc(): int =
    x = x + 4
    10)
  try:
    return h.f() * 10
  finally:
    result = result + x
nsut(sA3, rA3, 105)

proc rA4(v: int): int =
  var x = v
  let s = @[1, 2]
  let f = proc(a: int): int =
    x = x + a
    a
  try:
    return s.map(f).len * 10
  finally:
    result = result + x
nsut(sA4, rA4, 24)

proc rA5(v: int): int =
  var x = v
  let s = @[1, 2]
  let f = proc(a: int): bool =
    x = x + a
    true
  try:
    return s.filter(f).len * 10
  finally:
    result = result + x
nsut(sA5, rA5, 24)

proc rA6(v: int): int =
  var x = v
  let p = addr x
  let c = proc(): int =
    p[] = p[] + 4
    10
  try:
    return c() * 10
  finally:
    result = result + p[]
nsut(sA6, rA6, 105)

proc rA7(v: int): int =
  var x = v
  let p = addr x
  let c = proc(): int =
    x = x + 4
    10
  try:
    return c() * 10
  finally:
    result = result + p[]
nsut(sA7, rA7, 105)

suite "R7-1: a return value applying a closure reconciles":
  test "lambda":
    check inlineSites(rA1) == @["return"]
    exitVerdict(sA1)
  test "proc-valued let":
    check inlineSites(rA2) == @["return"]
    exitVerdict(sA2)
  test "proc field of a by-value object":
    check inlineSites(rA3) == @["return"]
    exitVerdict(sA3)
  test "map with a closure":
    check inlineSites(rA4) == @["return"]
    exitVerdict(sA4)
  test "filter with a closure":
    check inlineSites(rA5) == @["return"]
    exitVerdict(sA5)
  test "address-taken local written through the pointer":
    check inlineSites(rA6) == @["return"]
    exitVerdict(sA6)
  test "address-taken local written by name, read through the pointer":
    check inlineSites(rA7) == @["return"]
    exitVerdict(sA7)

# ---- R7-3: guards that apply a closure --------------------------------------

proc rI1(v: int): int =
  var x = v
  let c = proc(): int =
    x = x + 4
    1
  if c() > 0:
    result = 10
  result += x
nsut(sI1, rI1, 15)

proc rI1P(v: int): int =
  var x = v
  let p = addr x
  let c = proc(): int =
    p[] = p[] + 4
    1
  if c() > 0:
    result = 10
  result += x
nsut(sI1P, rI1P, 15)

proc rI2(v: int): int =
  var x = v
  let c = proc(): int =
    x = x + 4
    1
  if v < 0:
    result = 1
  elif c() > 0:
    result = 10
  result += x
nsut(sI2, rI2, 15)

proc rI3(v: int): int =
  var x = v
  let c = proc(): bool =
    x = x + 4
    true
  if v > 0 and c():
    result = 10
  result += x
nsut(sI3, rI3, 15)

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

suite "R7-3: a guard applying a closure reconciles":
  test "if guard (capture)":
    check inlineSites(rI1) == @["if"]
    exitVerdict(sI1)
  test "if guard (pointer)":
    check inlineSites(rI1P) == @["if"]
    exitVerdict(sI1P)
  test "elif guard":
    check inlineSites(rI2) == @["if"]
    exitVerdict(sI2)
  test "short-circuit join":
    check inlineSites(rI3) == @["if"]
    exitVerdict(sI3)
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
  test "short-circuit while test":
    check inlineSites(rW4) == @["while"]
    exitVerdict(sW4)

# ---- the concolic follow walks ----------------------------------------------

proc cIf(v: int) =
  var x = v
  var r = 0
  let c = proc(): int =
    x = x + 4
    1
  if c() > 0:
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
