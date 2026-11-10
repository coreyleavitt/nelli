## RFC-0016 W3-z P2 (wiring audit A2) -- a `--boundChecks:off` build (its
## `.nim.cfg`). A closure iterator pushed `boundChecks: on` is compiled with the
## check, whoever calls it, so its out-of-range index raises `IndexDefect`. The
## inliner parsed its body under the caller's scope (unchecked here), so the
## raise was a false trusted unsat. The for-body is the caller's own and stays
## unchecked.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

{.push boundChecks: on.}
iterator idxClosure(k: int): int {.closure.} =
  var a = [1, 2, 3]
  yield a[k]
{.pop.}

iterator okClosure(): int {.closure.} =
  yield 1

proc sutIter(x: int) =
  if x == 7:
    try:
      for v in idxClosure(x): discard v
    except IndexDefect:
      symexTarget("hit")

proc sutIterNoRaise(x: int) =
  if x == 7:
    try:
      for v in idxClosure(x): discard v
    except IndexDefect:
      return
    symexTarget("hit")

proc sutBody(x: int) =
  ## The for-body indexes with the caller's (unchecked) build.
  var a = [1, 2, 3]
  if x == 7:
    try:
      for v in okClosure(): discard a[x]
    except IndexDefect:
      symexTarget("hit")

suite "W3-z P2: closure iterator check scope, boundChecks off":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 313

  test "native: the pushed iterator raises":
    check native(sutIter(7)) == "hit"
    check native(sutIterNoRaise(7)) == "ran"

  test "a pushed boundChecks iterator raises IndexDefect":
    let r = symexFind(sutIter, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check r.trusted

  test "and the no-raise path is unsat":
    let r = symexFind(sutIterNoRaise, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status != sxSat

  test "the for-body keeps the caller's unchecked index: no IndexDefect hit":
    let r = symexFind(sutBody, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check not (r.status == sxSat and r.trusted)
