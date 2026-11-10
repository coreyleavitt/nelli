## RFC-0016 W3-z P7: the float-check gate reads the routine as the walker sees it.
##
## `touchesFloat` (check_options.nim) decides whether a routine's nanChecks /
## infChecks matter. It was syntactic over the routine's own typed body, so a
## routine whose only float arithmetic sits inside an inline iterator it loops
## over read those checks as off: a false unsat where the native run raises.
## The routines here take and hold ints and bools only; every float is inside
## the iterator or template.
import std/[unittest, options, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import ./s8cu_helpers

const
  nanK = cellKey(axPragma, "routine/nanChecks")
  ints = sampled([0, 1, 2, -1])

{.push nanChecks: on.}
iterator selfDivOn(n: int): bool {.inline.} =
  let z = float(n)
  yield z / z != z / z

template selfDivT(n: int): bool =
  let z = float(n)
  z / z != z / z

proc itDiv(n: int) =
  for b in selfDivOn(n):
    if b: symexTarget("hit")

proc tmplDiv(n: int) =
  if selfDivT(n): symexTarget("hit")
{.pop.}

iterator selfDivOff(n: int): bool {.inline.} =
  let z = float(n)
  yield z / z != z / z

{.push nanChecks: on.}
proc itDivOffDef(n: int) =
  ## The iterator is defined outside the push: the native run decides.
  for b in selfDivOff(n):
    if b: symexTarget("hit")
{.pop.}

template decided(body: untyped) =
  if hostAdmission().isSome: skipUnadmitted() else: body

suite "W3-z P7: float checks reach inline iterators and templates":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 315

  test "inline iterator defined under the push":
    decided:
      check native(itDiv(0)) == "FloatInvalidOpDefect"
      let r = pinExact(itDiv, nanK, target = tRaisedExn("FloatInvalidOpDefect"),
                       domain = ints)
      check r.status == sxRaised

  test "inline iterator defined outside the push":
    decided:
      let nat = native(itDivOffDef(0))
      checkpoint nat
      let r = pinExact(itDivOffDef, nanK, target = tRaisedExn(), domain = ints)
      if nat == "FloatInvalidOpDefect": check r.status == sxRaised
      else: check r.status == sxUnsat

  test "template":
    decided:
      check native(tmplDiv(0)) == "FloatInvalidOpDefect"
      let r = pinExact(tmplDiv, nanK, target = tRaisedExn("FloatInvalidOpDefect"),
                       domain = ints)
      check r.status == sxRaised
