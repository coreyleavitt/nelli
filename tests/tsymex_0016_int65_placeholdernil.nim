## RFC-0016 INT-65: `nil` of a placeholder sort. A `pointer` local
## initialised to `nil` and compared with it, and a closure local compared
## with `nil`, are both sat for `a = 5`.
##
## Red at 7746d32a: the `pointer` local declines `feUnsupportedExprKind`
## ("nil literal of an unmodelled type": `pointer` classifies as a
## placeholder sort, which has no nil), and the closure comparison declines
## `ceUnsupportedHof` ("proc value compared with nil"). Found while probing
## INT-63 (K8b's typeop axis suite, INT-56), whose row a closure local
## reaches without either.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc i65PointerNil(a, b: int8) =
  let t = int(a)
  var x: pointer = nil
  if t + 1 == 6 and x == nil: symexTarget("hit")

proc i65PointerLet(a, b: int8) =
  let t = int(a)
  var x: pointer = nil
  let c = x
  if t + 1 == 6 and c == nil: symexTarget("hit")

proc i65ClosureNil(a, b: int8) =
  let t = int(a)
  let f = proc (x: int): int = x + t
  if t + 1 == 6 and f != nil: symexTarget("hit")

suite "INT-65: `nil` of a placeholder sort is exact":
  for (name, verdict) in [
      ("a `pointer` local compared with nil",
       symexFind(i65PointerNil, tLabel("hit"), pinSettingsConst)),
      ("a `let` copy of a `pointer` local compared with nil",
       symexFind(i65PointerLet, tLabel("hit"), pinSettingsConst)),
      ("a closure local compared with nil",
       symexFind(i65ClosureNil, tLabel("hit"), pinSettingsConst))]:
    test name & " is exact (sat)":
      checkpoint $verdict.status & " trusted=" & $verdict.trusted &
        " errors " & $verdict.errors
      check verdict.trusted
      check verdict.status == sxSat
