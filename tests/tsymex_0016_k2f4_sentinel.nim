## RFC-0016 K2F-4 -- sentinel polarity.
##
## E6's census found 55 NimNode `case` sites whose `else` is a literal
## sentinel (`false`, `nil`, `""`, `-1`, `none`, a bare `return`). Whether the
## caller reads that literal as "decline / may" (fail-closed) or as "no effect
## / not aliased" (fail-open) was unaudited. Every sentinel `else` now carries
## its audited polarity as an in-source `# k2: fail-closed: ...` or `# k2:
## n/a: ...` tag, which `tsymex_0016_k2a_census.nim` requires.
##
## The audit's RED was in the arms beside an `else`:
## * `iterArgPath` (an inline iterator's by-value formal, S8bs) bound an array
##   or set constructor argument (`[v, 0]`, `{a, 2}`) as a copy taken where the
##   loop starts. `transf.putArgInto` maps a constructor of direct operands
##   DIRECTLY: the inlined body re-reads it at each use, so a write to `v` in
##   the loop body is seen by the next `yield`. The walk read the old value: a
##   clean sxSat on the dead label. It now substitutes the constructor
##   (`bindIterArg`), as Nim does.
## Defensive fixes with no reachable RED (the walker declines the shapes
## upstream, e.g. `addr gv(v)` is `heUnsafeCast`): a "rooted at x?" question
## over `lvalueRoot` reads a shape it does not read, but which names `x`, as
## yes (`mayBeRootedAt`); `byValueWritten` compares a path actual's root.
##
## Walker version: 313 (from 312).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 0, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000 or n == 99: return

iterator twiceFirst(xs: array[2, int]): int =
  yield xs[0]
  yield xs[0]

proc itBr(n: int) =
  guardN()
  var v = n
  var last = 0
  for k in twiceFirst([v, 0]):
    last = k
    v = n + 1
  if last == n + 1: symexTarget("ib_live")
  if last == n: symexTarget("ib_dead")

iterator twiceCard(s: set[uint8]): int =
  yield card(s)
  yield card(s)

proc itCurly(n: int) =
  guardN()
  var a = 1'u8
  var last = 0
  for k in twiceCard({a, 2'u8}):
    last = k
    a = 2'u8
  if last == 1: symexTarget("ic_live")
  if last == 2: symexTarget("ic_dead")

proc twoOf(n: int): int = n + 1

proc itBrCall(n: int) =
  ## Precision: an element that calls is not direct; Nim copies it once.
  guardN()
  var v = n
  var last = 0
  for k in twiceFirst([twoOf(v), 0]):
    last = k
    v = n + 5
  if last == n + 1: symexTarget("ibc_live")
  if last == n + 6: symexTarget("ibc_dead")

proc itVar(n: int) =
  ## Precision: a variable argument is the variable (S8bs), unchanged.
  guardN()
  var arr = [n, 0]
  var last = 0
  for k in twiceFirst(arr):
    last = k
    arr[0] = n + 1
  if last == n + 1: symexTarget("iv_live")
  if last == n: symexTarget("iv_dead")

template verdicts(fn: typed; live, dead: static string) =
  block:
    var l = false
    var d = false
    for n in ns:
      let h = hits(fn(n))
      if live in h: l = true
      if dead in h: d = true
    check l
    check not d
    let a = symexFind(fn, tLabel(live))
    checkpoint live & " " & $a.status & "\n" & show(a.errors)
    check a.status == sxSat
    let b = symexFind(fn, tLabel(dead))
    checkpoint dead & " " & $b.status & "\n" & show(b.errors)
    check b.status == sxUnsat

suite "K2F-4: an inline iterator's constructor argument is re-read":
  test "RED was sxSat on the dead label (a copy); now the walk agrees with native":
    verdicts(itBr, "ib_live", "ib_dead")
    verdicts(itCurly, "ic_live", "ic_dead")
  test "precision: a calling element is copied once, a variable stays bound":
    verdicts(itBrCall, "ibc_live", "ibc_dead")
    verdicts(itVar, "iv_live", "iv_dead")

suite "K2F-4: the walker version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 313
