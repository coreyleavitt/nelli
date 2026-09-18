## Rectify #137 — effect tracking for opaque IO procs, as narrowed by #163.
##
## #137's original contract: a call to a known-effectful proc (`echo`,
## `write`, …) is modelled as opaque — the body is not walked, the return is
## fresh-symbolic, and the path is marked uncertain, so a target reached only
## on such a path degrades to `sxUnknown` rather than emitting an unsound
## witness.
##
## **Issue #163 narrowed the second half of that.** Keeping the walker out of
## the body is still right for every opaque call. TAINTING the path is right
## only when the call could actually affect what the SUT observes — and for a
## void call taking only values it cannot. `echo "diagnostic"` binds no
## result and hands over nothing writable, so the only channel left to it is
## a module-level global, and a SUT that reads one has already degraded at
## its own read site (the walker models no globals at all: it answers
## `sxUnknown` with a raw `KeyError`). Tainting it anyway cost the answer for
## free, and cost it on every path of every `{.cover.}`-instrumented proc,
## which is what made the solver-to-fuzzer handoff impossible.
##
## So the first two tests below now pin the OPPOSITE of what they pinned
## before #163, deliberately, in the same way #162 retired the `mul32`
## trip-wire #161 planted. What #137 was protecting — never an unsound
## witness from an unmodelled effect — is unchanged and is pinned by the
## `stillTaints` cases: an opaque call whose result is USED, or that takes a
## `var` argument, taints exactly as it always did.
##
## What is knowingly given up: `echo` can raise `IOError`, and an inert call
## is no longer a barrier to reaching a target behind it. That gap is not new
## and it was never symmetric — before #163, an `echo` AFTER the branch
## already left the verdict intact while one BEFORE it erased the verdict.
## Ordering, not soundness, is what changed.
import std/[unittest, strutils]
import nelli/symex

var effectSink = 0   ## module-level: the walker binds no global, by design

proc readsBack(): int {.symexOpaque.} = effectSink
proc mutates(x: var int) {.symexOpaque.} = x.inc

suite "symex effects #137, as narrowed by #163":

  test "echo on a path no longer makes the path uncertain":
    proc withSideEffect(x: int) =
      if x > 5:
        echo "diagnostic"
        symexTarget("reach")
    let r = symexFind(withSideEffect, tLabel("reach"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    check r.witness[0] > 5

  test "a user proc that only calls echo no longer degrades its caller":
    proc innerEffect(y: int) =
      echo "from inner"
    proc outer(x: int) =
      if x > 5:
        innerEffect(x)
        symexTarget("reach")
    let r = symexFind(outer, tLabel("reach"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

  test "no echo on the only reaching path → sxSat as before":
    proc pure(x: int) =
      if x > 5:
        symexTarget("clean")
    let r = symexFind(pure, tLabel("clean"))
    check r.status == sxSat
    check r.witness[0] > 5

  test "#137 still holds where it must: a USED opaque result taints":
    proc usesResult(x: int) =
      let v = readsBack()
      if x + v > 5:
        symexTarget("reach")
    let r = symexFind(usesResult, tLabel("reach"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "readsBack" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

  test "#137 still holds where it must: a var-argument opaque call taints":
    proc passesVar(x: int) =
      var local = x
      mutates(local)
      if local > 5:
        symexTarget("reach")
    let r = symexFind(passesVar, tLabel("reach"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "mutates" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified
