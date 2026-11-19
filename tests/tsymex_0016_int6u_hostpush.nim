## RFC-0016 int6-u: a routine declared inside a region a template or a macro
## pushes check options around is placed under that push.
##
## int6-a5 made a routine declared inside a body that pushes check options
## decline ("declared inside ..."): it compiles under the push where it
## stands, which the scan of the module's statements never reads. The host
## was found by the definition's *text*, which a push a template expands or a
## macro emits is not in: such a routine was walked under its host's scope.
## int6-t read the opaque scan's pushes from the typed body; the host is now
## found there too.
##
## Native, on the pinned toolchain (c backend, x86-64 Linux): a routine
## declared inside a template's or a macro's `rangeChecks: off` region keeps
## `R(300)` unchecked (`outerTmpl(300)` and `outerMacro(300)` reach the
## label). Walked under its host's checks it raised `RangeDefect` there, and
## the label was a false sxUnsat. The control: a template that pushes nothing
## leaves the routine its host's checks (`R(300)` raises), and it is walked.
##
## The templates live in their own module (`int6tlib`): the check scan reads
## a push in a template's text as a possible state of its own module's
## positions, which would make this suite's routines deviate.

import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s8cu_helpers
import ./int6tlib/s0016_int6t_pushers

type R = range[0 .. 10]

const sk = cellKey(faGeneric, "int6u_hostpush")

proc outerTmpl(v: int) =
  rangeOff:
    proc inner(w: int): int = int(R(w))
  if inner(v) == 300: symexTarget("hit")

proc outerMacro(v: int) =
  emitRangeOff:
    proc inner(w: int): int = int(R(w))
  if inner(v) == 300: symexTarget("hit")

proc outerPlain(v: int) =
  plainRegion:
    proc inner(w: int): int = int(R(w))
  if inner(v) == 300: symexTarget("hit")

suite "int6-u: a routine declared inside a template's or macro's push":
  test "the build checks range":
    check coRange in buildSemantics.checks

  test "a template's rangeChecks: off region":
    check native(outerTmpl(300)) == "hit"
    pinDecline(outerTmpl, sk, feCheckOption, needle = "declared inside")

  test "a macro's rangeChecks: off region":
    check native(outerMacro(300)) == "hit"
    pinDecline(outerMacro, sk, feCheckOption, needle = "declared inside")

  test "a template that pushes nothing (control)":
    check native(outerPlain(300)) == "RangeDefect"
    let x = pinFind(outerPlain, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised

suite "int6-u: walker version":
  test "walker version floor >= 482":
    check parseInt(symexWalkerVersion) >= 482
