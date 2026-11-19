## RFC-0016 int6-t: the opaque defect scan finds a check push in a routine's
## typed body, wherever the push came from.
##
## The scan reads a body under its owner's options, as one scope; a body that
## pushes check options is not one scope, so int6-a5 and int6-m6 made it
## unreadable ("may raise any Defect", "may be undefined"). They read the
## routine's definition *text*, which a push expanded from a template or
## emitted by a macro is not in: such a callee was read as one scope, and a
## label past an `overflowChecks: off` region was a trusted sxSat whose tail
## held an undefined signed overflow. The typed body keeps every push and pop
## as a pragma statement (template, macro or text), and the scan now reads it.
##
## Native, on the pinned toolchain (c backend, x86-64 Linux): a region a
## template or a macro pushes `overflowChecks: off` around is the plain C
## addition, so `v + 1` at `high(int)` raises no `OverflowDefect` (it is
## undefined; nothing is pinned about its value).
##
## One push region is exempt, from an audited allowlist
## (`tests/0016-allowlist/pushexempt.txt`): the body of the toolchain's
## `system/iterators.nim` template `unCheckedInc`, inside a routine of that
## module, which steps a loop counter its loop has already bounded. Without
## the exemption every opaque `for x in s` was unreadable; with it their
## verdicts are those of int6-m6 (pinned below). A template of that name
## anywhere else is not exempt.

import std/[unittest, strutils, os]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s8cu_helpers
import ./int6tlib/s0016_int6t_pushers

proc id(x: int): int {.noinline.} = x

proc opTmpl(v: int) {.symexOpaque.} =
  unchecked:
    discard id(v) + 1

proc sutTmpl(v: int) =
  if v == 5: symexTarget("hit")
  opTmpl(v)

proc opMacro(v: int) {.symexOpaque.} =
  emitUnchecked:
    discard id(v) + 1

proc sutMacro(v: int) =
  if v == 5: symexTarget("hit")
  opMacro(v)

proc helperTmpl(v: int): int =
  unchecked:
    result = id(v) + 1

proc opNested(v: int) {.symexOpaque.} =
  discard helperTmpl(v)

proc sutNested(v: int) =
  if v == 5: symexTarget("hit")
  opNested(v)

proc opUserInc(v: int) {.symexOpaque.} =
  var i = id(v)
  unCheckedInc(i)
  discard id(i)

proc sutUserInc(v: int) =
  if v == 5: symexTarget("hit")
  opUserInc(v)

proc opSeqLoop(s: seq[int]) {.symexOpaque.} =
  for x in s: discard id(x)

proc sutSeqLoop(v: int) =
  if v == 5: symexTarget("hit")
  opSeqLoop(@[v, 2])

proc opStrPairs(s: string) {.symexOpaque.} =
  for i, c in s: discard id(i + ord(c))

proc sutStrPairs(v: int) =
  if v == 5: symexTarget("hit")
  opStrPairs("ab")

proc opArrLoop(a: array[3, int]) {.symexOpaque.} =
  for x in a: discard id(x)

proc sutArrLoop(v: int) =
  if v == 5: symexTarget("hit")
  opArrLoop([v, 1, 2])

proc nativeOvf(f: proc (v: int) {.nimcall.}; v: int): string =
  try:
    f(v)
    ""
  except OverflowDefect:
    "OverflowDefect"

template untrusted(fn: untyped) =
  let r = pinFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
  check r.status == sxSat
  check not r.trusted
  check UbKind(ubTailUnverified) in r.soundness.undefinedKinds

template keepsVerdict(fn: untyped) =
  ## int6-m6's verdict (base 986e77ab, walker 479): sxSat, untrusted by the
  ## loop's own bound and index checks (the witness's undefined kinds), never
  ## by an unreadable tail.
  let r = pinFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
  echo "  ", astToStr(fn), ": ", r.status, " trusted=", r.trusted,
    " undefinedKinds=", r.soundness.undefinedKinds,
    " witnessUndefined=", r.soundness.witnessUndefined
  check r.status == sxSat
  check UbKind(ubTailUnverified) notin r.soundness.undefinedKinds

suite "int6-t: a push the typed body holds makes an opaque body unreadable":
  test "the build checks overflow":
    check coOverflow in buildSemantics.checks

  test "a user template's push in an opaque callee":
    check nativeOvf(sutTmpl, high(int)) == ""
    untrusted(sutTmpl)

  test "a macro's push in an opaque callee":
    check nativeOvf(sutMacro, high(int)) == ""
    untrusted(sutMacro)

  test "a template's push in a routine an opaque callee calls":
    check nativeOvf(sutNested, high(int)) == ""
    untrusted(sutNested)

  test "a user template named unCheckedInc is not the audited one":
    check nativeOvf(sutUserInc, high(int)) == ""
    untrusted(sutUserInc)

suite "int6-t: the stdlib loop counter stays readable":
  test "an opaque for over a seq":
    check native(sutSeqLoop(5)) == "hit"
    keepsVerdict(sutSeqLoop)

  test "an opaque pairs over a string":
    check native(sutStrPairs(5)) == "hit"
    keepsVerdict(sutStrPairs)

  test "an opaque for over an array":
    check native(sutArrLoop(5)) == "hit"
    keepsVerdict(sutArrLoop)

suite "int6-t: walker version":
  test "walker version floor >= 480":
    check parseInt(symexWalkerVersion) >= 480
