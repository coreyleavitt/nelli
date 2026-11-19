## RFC-0016 int6-t: the `--rangeChecks:off --boundChecks:off` twin of
## `tsymex_0016_int6t_typedpush` (this file's `.nim.cfg`). A template or a
## macro that pushes `boundChecks: on` inside an opaque callee checks its
## region: natively `s[5]` there raises `IndexDefect`, and an `except
## IndexDefect` around the call catches it. The opaque defect scan read the
## callee as one scope under the build's options (unchecked): `s[v]` was
## undefined out of the seq, never an `IndexDefect`, and the handler was a
## trusted false sxUnsat. The typed body holds the push, so the callee is
## unreadable now ("may raise any Defect").

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers
import ./int6tlib/s0016_int6t_pushers

proc opTmpl(v: int) {.symexOpaque.} =
  let s = @[10, 20, 30]
  boundsOn:
    discard s[v]

proc sutTmpl(v: int) =
  try:
    opTmpl(v)
  except IndexDefect:
    symexTarget("hit")

proc opMacro(v: int) {.symexOpaque.} =
  let s = @[10, 20, 30]
  emitBoundsOn:
    discard s[v]

proc sutMacro(v: int) =
  try:
    opMacro(v)
  except IndexDefect:
    symexTarget("hit")

template reachable(fn: untyped) =
  let r = pinFind(fn, tLabel("hit"))
  echo "  ", astToStr(fn), ": ", r.status, " trusted=", r.trusted, " ",
    show(r.errors)
  check r.status != sxUnsat

suite "int6-t (off build): a pushed-on region from a template or macro":
  test "the build has range and bound checks off":
    check coRange notin buildSemantics.checks
    check coBound notin buildSemantics.checks

  test "a template's boundChecks: on region raises in an opaque callee":
    check native(sutTmpl(5)) == "hit"
    check native(sutTmpl(2)) == "ran"
    reachable(sutTmpl)

  test "a macro's boundChecks: on region raises in an opaque callee":
    check native(sutMacro(5)) == "hit"
    check native(sutMacro(2)) == "ran"
    reachable(sutMacro)

suite "int6-t (off build): walker version":
  test "walker version floor >= 481":
    check parseInt(symexWalkerVersion) >= 481
