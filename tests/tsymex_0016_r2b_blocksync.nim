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
import nelli/smt/canonicalize

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
  # RFC-0016 review R4-1 renamed it `reconciledHere`, read per survivor.
  test "syncAddrCells and walkCapSynced read reconciledHere":
    check runtimeSrc.count("\nfunc reconciledHere(") == 1
    check procBody("syncAddrCells").contains("reconciledHere(stmt, joined[i])")
    check procBody("walkCapSynced").contains("reconciledHere(stmt, joined[i])")
  test "no per-entry isBlock skip is left in syncAddrCells":
    check not procBody("syncAddrCells").contains("stmt.kind == isBlock")

# RFC-0016 review R3-1. A LABELLED block is not synced by its parts: a path
# that took `break L` from inside an `if` is parked before any enclosing
# statement's post-sync sees it, and the block's own pass is the one reconcile
# that reaches it. The condition's call writes a captured or address-taken
# variable; the verdict after the block must read that write.
proc r3Cap(v: int): int =
  var cnt = v
  proc cntr(): int =
    cnt += 1
    cnt
  block L:
    if cntr() > 0: break L
    cnt = cnt + 100
  result = cnt

proc sutR3Cap(v: int) =
  if v != 1: return
  let r = r3Cap(v)
  if r == 2: symexTarget("ok")
  if r != 2: symexTarget("bad")

proc r3Bump(p: ptr int): int =
  p[] += 5
  p[]

proc r3Addr(v: int): int =
  var x = v
  block L:
    if r3Bump(addr x) > 0: break L
    x = x + 100
  result = x

proc sutR3Addr(v: int) =
  if v != 1: return
  let r = r3Addr(v)
  if r == 6: symexTarget("ok")
  if r != 6: symexTarget("bad")

proc r3Ptr(v: int): int =
  var x = v
  let p = addr x
  block L:
    if r3Bump(p) > 0: break L
    x = x + 100
  result = x

proc sutR3Ptr(v: int) =
  if v != 1: return
  let r = r3Ptr(v)
  if r == 6: symexTarget("ok")
  if r != 6: symexTarget("bad")

proc r3Cont(v: int): int =
  var x = v
  var i = 0
  while i < 3:
    inc i
    if r3Bump(addr x) > 0: continue
    x = x + 100
  result = x

proc sutR3Cont(v: int) =
  if v != 1: return
  let r = r3Cont(v)
  if r == 16: symexTarget("ok")
  if r != 16: symexTarget("bad")

proc r3ContCap(v: int): int =
  var cnt = v
  proc cntr(): int =
    cnt += 1
    cnt
  var i = 0
  while i < 3:
    inc i
    if cntr() > 0: continue
    cnt = cnt + 100
  result = cnt

proc sutR3ContCap(v: int) =
  if v != 1: return
  let r = r3ContCap(v)
  if r == 4: symexTarget("ok")
  if r != 4: symexTarget("bad")

# A call under a short-circuit stays in the condition: the `if` statement's
# own effect, which no inner statement synced.
proc r3CapSc(v: int): int =
  var cnt = v
  proc cntr(): int =
    cnt += 1
    cnt
  block L:
    if v > 0 and cntr() > 0: break L
    cnt = cnt + 100
  result = cnt

proc sutR3CapSc(v: int) =
  if v != 1: return
  let r = r3CapSc(v)
  if r == 2: symexTarget("ok")
  if r != 2: symexTarget("bad")

proc r3AddrSc(v: int): int =
  var x = v
  block L:
    if v > 0 and r3Bump(addr x) > 0: break L
    x = x + 100
  result = x

proc sutR3AddrSc(v: int) =
  if v != 1: return
  let r = r3AddrSc(v)
  if r == 6: symexTarget("ok")
  if r != 6: symexTarget("bad")

proc r3ContSc(v: int): int =
  var x = v
  var i = 0
  while i < 3:
    inc i
    if i > 0 and r3Bump(addr x) > 0: continue
    x = x + 100
  result = x

proc sutR3ContSc(v: int) =
  if v != 1: return
  let r = r3ContSc(v)
  if r == 16: symexTarget("ok")
  if r != 16: symexTarget("bad")

suite "R3-1: a labelled block reconciles its break paths":
  test "break L from an if whose condition mutates a capture":
    verdict(sutR3Cap, "ok", sxSat)
    verdict(sutR3Cap, "bad", sxUnsat)
  test "break L from an if whose condition writes through addr":
    verdict(sutR3Addr, "ok", sxSat)
    verdict(sutR3Addr, "bad", sxUnsat)
  test "break L through a stored pointer":
    verdict(sutR3Ptr, "ok", sxSat)
    verdict(sutR3Ptr, "bad", sxUnsat)
  test "continue from an if whose condition writes through addr":
    verdict(sutR3Cont, "ok", sxSat)
    verdict(sutR3Cont, "bad", sxUnsat)
  test "continue from an if whose condition mutates a capture":
    verdict(sutR3ContCap, "ok", sxSat)
    verdict(sutR3ContCap, "bad", sxUnsat)
  test "break L under a short-circuit condition, capture":
    verdict(sutR3CapSc, "ok", sxSat)
    verdict(sutR3CapSc, "bad", sxUnsat)
  test "break L under a short-circuit condition, addr":
    verdict(sutR3AddrSc, "ok", sxSat)
    verdict(sutR3AddrSc, "bad", sxUnsat)
  test "continue under a short-circuit condition, addr":
    verdict(sutR3ContSc, "ok", sxSat)
    verdict(sutR3ContSc, "bad", sxUnsat)

suite "R3-1: the predicate keeps a labelled block's exits":
  # RFC-0016 review R4-1: only the survivors that rejoined the block from a
  # parked exit; the verdicts are pinned in `tsymex_0016_r5a_exitsync`.
  test "reconciledHere keeps a block's joined exits":
    let a = runtimeSrc.find("\nfunc reconciledHere(")
    doAssert a >= 0
    let b = runtimeSrc.find("\nproc ", a + 1)
    check runtimeSrc[a ..< b].contains("stmt.kind != isBlock or joinedExit")
  test "walker version floor (R3-1)":
    check symexWalkerVersion.parseInt >= 364
