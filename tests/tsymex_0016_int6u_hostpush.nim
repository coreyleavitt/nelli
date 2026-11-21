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

import std/[unittest, strutils, macros]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s8cu_helpers
import ./int6tlib/s0016_int6t_pushers
import ./int6tlib/s0016_int6u_transx
import ./int6tlib/s0016_int6u_zinc
import ./int6tlib/s0016_int6u_zrev
import ./int6tlib/s0016_int6u_deep

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

# CR4-H1, round 3: routines declared inside `suite` and `test` blocks, in a
# file that imports nelli, nelli/symex and the shared helpers, compile at the
# default `maxLoopIterationsVM` (the scan once walked every module reachable
# from the imports once per identifier of every template body it met).
suite "int6-u: routines inside test blocks (compile cost)":
  test "a routine in a test block is walked":
    proc innerBlk(w: int): int = int(R(w))
    proc outerBlk(v: int) =
      if innerBlk(v) == 300: symexTarget("hit")
    check native(outerBlk(300)) == "RangeDefect"
    let x = pinFind(outerBlk, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised

# CR4-H1: the same regions around a routine at the MODULE's level. The
# helper module's template and macro are expanded here; the scan reads this
# module's text alone, in which the matched push and pop are not.
rangeOff:
  proc innerTmplTop(w: int): int = int(R(w))
proc outerTmplTop(v: int) =
  if innerTmplTop(v) == 300: symexTarget("hit")

emitRangeOff:
  proc innerMacroTop(w: int): int = int(R(w))
proc outerMacroTop(v: int) =
  if innerMacroTop(v) == 300: symexTarget("hit")

plainRegion:
  proc innerPlainTop(w: int): int = int(R(w))
proc outerPlainTop(v: int) =
  if innerPlainTop(v) == 300: symexTarget("hit")

# CR4-H1, round 3: a template resolved by scope. The pushing template is
# defined in no module this one imports directly or defines itself.
wrapX:
  proc innerTransTop(w: int): int = int(R(w))
proc outerTransTop(v: int) =
  if innerTransTop(v) == 300: symexTarget("hit")

rangeOffInc:
  proc innerIncTop(w: int): int = int(R(w))
proc outerIncTop(v: int) =
  if innerIncTop(v) == 300: symexTarget("hit")

deepT0:
  proc innerDeepTop(w: int): int = int(R(w))
proc outerDeepTop(v: int) =
  if innerDeepTop(v) == 300: symexTarget("hit")

proc innerNoCallTop(w: int): int = int(R(w))
proc outerNoCallTop(v: int) =
  if innerNoCallTop(v) == 300: symexTarget("hit")

# The same-module forms stand last: a push a template's text holds is a
# possible state of every later position of its own module.
template rangeOffHere(body: untyped) =
  {.push rangeChecks: off.}
  body
  {.pop.}

macro emitRangeOffHere(body: untyped): untyped =
  result = newStmtList(
    nnkPragma.newTree(ident"push",
      nnkExprColonExpr.newTree(ident"rangeChecks", ident"off")),
    body,
    nnkPragma.newTree(ident"pop"))

rangeOffHere:
  proc innerTmplHere(w: int): int = int(R(w))
proc outerTmplHere(v: int) =
  if innerTmplHere(v) == 300: symexTarget("hit")

emitRangeOffHere:
  proc innerMacroHere(w: int): int = int(R(w))
proc outerMacroHere(v: int) =
  if innerMacroHere(v) == 300: symexTarget("hit")

template sameVerdict(imported, here: untyped) =
  let a = symexFind(imported, tLabel("hit"))
  let b = symexFind(here, tLabel("hit"))
  checkpoint show(a.errors)
  checkpoint show(b.errors)
  check a.status == b.status
  check a.trusted == b.trusted
  # The kinds, not their count: the same-module form also declines the
  # caller, which stands after the template's text (a possible push).
  var ka, kb: set[SymexErrorKind]
  for e in a.errors: ka.incl e.kind
  for e in b.errors: kb.incl e.kind
  check ka == kb

suite "int6-u: a routine at the module's level inside a template's or macro's push":
  test "an imported template's rangeChecks: off region":
    check native(outerTmplTop(300)) == "hit"
    pinDecline(outerTmplTop, sk, feCheckOption, needle = "declared inside")

  test "an imported macro's rangeChecks: off region":
    check native(outerMacroTop(300)) == "hit"
    pinDecline(outerMacroTop, sk, feCheckOption, needle = "declared inside")

  test "a template that calls a pushing template of a module not imported":
    check native(outerTransTop(300)) == "hit"
    pinDecline(outerTransTop, sk, feCheckOption, needle = "declared inside")

  test "a pushing template a module defines by `include`":
    check native(outerIncTop(300)) == "hit"
    pinDecline(outerIncTop, sk, feCheckOption, needle = "declared inside")

  test "a routine in an included file, the template in its includer":
    check native(outerRev(300)) == "hit"
    pinDecline(outerRev, sk, feCheckOption, needle = "declared inside")

  test "an expansion nested past the read depth declines (fails closed)":
    check native(outerDeepTop(300)) == "hit"
    pinDecline(outerDeepTop, sk, feCheckOption, needle = "declared inside")

  test "the walker version carries the round-3 scope index (floor)":
    check parseInt(symexWalkerVersion) >= 490

  test "the verdict equals the same-module template's":
    check native(outerTmplHere(300)) == "hit"
    sameVerdict(outerTmplTop, outerTmplHere)

  test "the verdict equals the same-module macro's":
    check native(outerMacroHere(300)) == "hit"
    sameVerdict(outerMacroTop, outerMacroHere)

  test "an imported template that pushes nothing is walked (control)":
    check native(outerPlainTop(300)) == "RangeDefect"
    let x = pinFind(outerPlainTop, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised

  test "a routine in no template call is walked (control)":
    check native(outerNoCallTop(300)) == "RangeDefect"
    let x = pinFind(outerNoCallTop, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised

suite "int6-u: walker version":
  test "walker version floor >= 486":
    check parseInt(symexWalkerVersion) >= 486
