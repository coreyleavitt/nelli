## RFC-0016 review R2-2. A routine body is a claiming stamped `isBlock`, and
## `walkCapSynced` / `syncAddrCells` once synced it as one statement against a
## snapshot from before the body, after each of its statements had synced.
## A compound statement's effects are exactly its statements' effects, so a
## block-level pass reconciles nothing. Each program writes an address-taken
## or captured variable by name in one statement and through a pointer or a
## closure in another, inside a called routine: the verdict must be the
## native one, with no clash decline.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    for e in r.errors:
      check e.kind notin {feUnsupportedOp, ceCaptureByRefUnmodelled}

proc r2bAddr(v: int): int =
  var x = v
  let p = addr x
  x = x + 1
  p[] = p[] * 2
  x = x + 3
  result = x

proc sutAddr(v: int) =
  if v != 1: return
  let r = r2bAddr(v)
  if r == 7: symexTarget("ok")
  if r != 7: symexTarget("bad")

proc r2bAddrIf(v: int): int =
  var x = v
  let p = addr x
  if v > 0:
    x = x + 1
    p[] = p[] * 2
  else:
    p[] = 5
    x = x + 3
  result = x

proc sutAddrIf(v: int) =
  if v != 1: return
  let r = r2bAddrIf(v)
  if r == 4: symexTarget("ok")
  if r != 4: symexTarget("bad")

proc r2bClosure(v: int): int =
  var x = v
  proc bump() = x += 1
  bump()
  x = x * 2
  let p = addr x
  p[] += 1
  bump()
  result = x

proc sutClosure(v: int) =
  if v != 1: return
  let r = r2bClosure(v)
  if r == 6: symexTarget("ok")
  if r != 6: symexTarget("bad")

proc r2bLoop(v: int): int =
  var x = v
  let p = addr x
  var i = 0
  while i < 2:
    x = x + 1
    p[] = p[] + 10
    inc i
  result = x

proc sutLoop(v: int) =
  if v != 1: return
  let r = r2bLoop(v)
  if r == 23: symexTarget("ok")
  if r != 23: symexTarget("bad")

proc sutLambda(v: int) =
  if v != 1: return
  let f = proc (a: int): int =
    var x = a
    let p = addr x
    x = x + 1
    p[] = p[] * 2
    x
  if v != 1: return
  let r = f(v)
  if r == 4: symexTarget("ok")
  if r != 4: symexTarget("bad")

suite "R2-2: a block-level sync pass reconciles nothing":
  test "addr var written by name and through a pointer in a callee":
    verdict(sutAddr, "ok", sxSat)
    verdict(sutAddr, "bad", sxUnsat)
  test "the same across if arms":
    verdict(sutAddrIf, "ok", sxSat)
    verdict(sutAddrIf, "bad", sxUnsat)
  test "a closure capture also taken by address":
    verdict(sutClosure, "ok", sxSat)
    verdict(sutClosure, "bad", sxUnsat)
  test "a loop body":
    verdict(sutLoop, "ok", sxSat)
    verdict(sutLoop, "bad", sxUnsat)
  test "a lambda body":
    verdict(sutLambda, "ok", sxSat)
    verdict(sutLambda, "bad", sxUnsat)

type R2bObj = object
  a, b: int

proc r2bObj(v: int): int =
  var o = R2bObj(a: v, b: 0)
  let p = addr o
  o.a = o.a + 1
  p[].b = p[].a * 3
  o.a = o.a + p[].b
  result = o.a + o.b

proc sutObj(v: int) =
  if v != 1: return
  let r = r2bObj(v)
  if r == 14: symexTarget("ok")
  if r != 14: symexTarget("bad")

proc r2bStr(v: int): int =
  var s = "ab"
  let p = addr s
  s = s & "c"
  p[] = p[] & "d"
  s.add 'e'
  result = s.len + v

proc sutStr(v: int) =
  if v != 1: return
  let r = r2bStr(v)
  if r == 6: symexTarget("ok")
  if r != 6: symexTarget("bad")

proc r2bSeq(v: int): int =
  var q = @[v, 2]
  let p = addr q
  q[0] = q[0] + 1
  p[][1] = p[][0] * 5
  q[0] = q[0] + p[][1]
  result = q[0] + q[1]

proc sutSeq(v: int) =
  if v != 1: return
  let r = r2bSeq(v)
  if r == 22: symexTarget("ok")
  if r != 22: symexTarget("bad")

proc r2bVar(x: var int) =
  let p = addr x
  x = x + 1
  p[] = p[] * 2
  x = x + 3

proc sutVarFormal(v: int) =
  if v != 1: return
  var y = v
  r2bVar(y)
  if y == 7: symexTarget("ok")
  if y != 7: symexTarget("bad")

proc r2bCapVar(v: int): int =
  var x = v
  let p = addr x
  proc bump() =
    x += 1
    p[] += 10
  bump()
  x = x * 2
  bump()
  result = x

proc sutCapVar(v: int) =
  if v != 1: return
  let r = r2bCapVar(v)
  if r == 35: symexTarget("ok")
  if r != 35: symexTarget("bad")

suite "R2-2: more shapes":
  test "object":
    verdict(sutObj, "ok", sxSat)
    verdict(sutObj, "bad", sxUnsat)
  test "string":
    verdict(sutStr, "ok", sxSat)
    verdict(sutStr, "bad", sxUnsat)
  test "seq":
    verdict(sutSeq, "ok", sxSat)
    verdict(sutSeq, "bad", sxUnsat)
  test "var formal":
    verdict(sutVarFormal, "ok", sxSat)
    verdict(sutVarFormal, "bad", sxUnsat)
  test "capture also addressed":
    verdict(sutCapVar, "ok", sxSat)
    verdict(sutCapVar, "bad", sxUnsat)

# No program was found whose block-level pass declines spuriously: the inner
# statements' syncs leave local and cell equal, so the passes were no-ops by
# accident. The rule is pinned structurally: one named predicate, read by
# every reconcile loop of both sync procs, and no per-entry `isBlock` skips.
const runtimeSrc = staticRead("../src/nelli/smt/runtime.nim")

proc procBody(name: string): string =
  let a = runtimeSrc.find("\nproc " & name & "(")
  doAssert a >= 0, name
  let b = runtimeSrc.find("\nproc ", a + 1)
  runtimeSrc[a ..< b]

suite "R2-2: the rule is one named predicate":
  test "syncAddrCells and walkCapSynced read syncedByItsParts":
    check runtimeSrc.count("\nfunc syncedByItsParts(") == 1
    check procBody("syncAddrCells").contains("syncedByItsParts(stmt)")
    check procBody("walkCapSynced").contains("syncedByItsParts(stmt)")
  test "no per-entry isBlock skip is left in syncAddrCells":
    check not procBody("syncAddrCells").contains("stmt.kind == isBlock")
