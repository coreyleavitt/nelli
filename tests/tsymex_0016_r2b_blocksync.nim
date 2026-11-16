## RFC-0016 review R2-2. A routine body is a claiming stamped `isBlock`, and
## `walkCapSynced` / `syncAddrCells` once synced it as one statement against a
## snapshot from before the body, after each of its statements had synced.
## A compound statement's effects are exactly its statements' effects, so a
## block-level pass reconciles nothing. Each program writes an address-taken
## or captured variable by name in one statement and through a pointer or a
## closure in another, inside a called routine: the verdict must be the
## native one, with no clash decline.

import std/[unittest, strutils, os]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import audit_scan_utils

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

# The rule is pinned behaviourally above and in `tsymex_0016_r5a_exitsync`
# (R4-1, R5-1, R5-2), and structurally here over the walker's code with its
# comments and strings removed (`codeOf`): one reconcile, which no compound
# statement reaches, and every guard a compound evaluates itself goes through
# `evalCondSynced`.
let runtimeCode = codeOf(readFile(smtSrcDir / "runtime.nim"))

proc procBody(name: string): string =
  ## The definition: the last `proc name(` or `func name(`, after any forward
  ## declaration, to the next routine.
  let a = max(runtimeCode.rfind("\nproc " & name & "("),
              runtimeCode.rfind("\nfunc " & name & "("))
  doAssert a >= 0, name
  var b = runtimeCode.len
  for kw in ["\nproc ", "\nfunc "]:
    let k = runtimeCode.find(kw, a + 1)
    if k > a and k < b: b = k
  runtimeCode[a ..< b]

suite "R5-2: reconciled only where effects are produced":
  test "no compound statement reaches the reconcile":
    check runtimeCode.count("const compoundStmtKinds = {isBlock, isIf, isWhile, isTry}") == 1
    # R6: the three syncs take a `CellProducer`, never a statement; the one
    # place a statement becomes one is `producerOf`, which refuses a compound.
    for p in ["reconcileCells", "syncAddrCells", "syncElemCells"]:
      check procBody(p).contains("src: CellProducer")
      check not procBody(p).contains("IRStmt")
    check procBody("producerOf").contains("doAssert stmt.kind notin compoundStmtKinds")
    check procBody("walkCapSynced").contains("reconcileCells(producerOf(stmt),")
    check procBody("walkCapSynced").contains("if stmt.kind in compoundStmtKinds:")
  test "the per-span machinery is gone":
    for id in ["reconciledHere", "joinedExitMask", "blockJoinedExits"]:
      check id notin runtimeCode
  test "every guard a compound evaluates is reconciled where it runs":
    for p in ["walkIfFollowConcrete", "walkWhileFollowConcrete"]:
      check procBody(p).contains("evalCondSynced(")
      check not procBody(p).contains("lowerBoolInExpr(")
    # `walkStmt`: the `ifJoin` guard, each `if` condition, and the `while`
    # guard's per-iteration and final tests. Its two other boolean lowerings
    # are the leaves `isAssert` and `isAssume`.
    check procBody("walkStmt").count("evalCondSynced(") == 4
    check procBody("walkStmt").count("lowerBoolInExpr(") == 2
    # R6: each site is anchored to its own guard (the `ifJoin` guard, the
    # `if`/`elif` condition, the `while` test and the final test after the
    # last unrolled body), not to a whole-body count. All are defensive: the
    # parser leaves no call in a guard (`tsymex_0016_r7a_liveness`).
    check procBody("walkStmt").contains("evalCondSynced(p, br.cond, w)")
    check procBody("walkStmt").contains("evalCondSynced(cp0, br.cond, w)")
    check procBody("walkStmt").count("evalCondSynced(p, stmt.wcond, w)") == 2
  test "a guard hands the reconcile no statement":
    check procBody("evalCondSynced").contains("reconcileCells(CellProducer(),")
    check not procBody("evalCondSynced").contains("IRStmt(")
  test "a `return` is no reconcile point (R6-3: unreachable, deleted)":
    check "leafSyncDepth" notin runtimeCode
    check not procBody("walkStmt").contains("reconcileCells(")

# RFC-0016 review R3-1. A path that took `break L` from inside an `if` is
# parked before any enclosing statement's post-sync sees it. The condition's
# call writes a captured or address-taken variable; the verdict after the
# block must read that write. Since R5-2 the condition is reconciled where it
# is evaluated (a hoisted call is a leaf; a guard is `evalCondSynced`).
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

suite "R3-1: walker version":
  test "walker version floor (R5-2)":
    check symexWalkerVersion.parseInt >= 366
