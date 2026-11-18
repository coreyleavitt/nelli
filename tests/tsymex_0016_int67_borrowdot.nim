## RFC-0016 INT-67: a field read through a distinct object type that
## borrows `.` (`type D {.borrow: `.`.} = distinct O`). `D(O(x: t)).x == 5`
## is sat at `a = 5`.
##
## Red at fc08fd17: the read declines `feUnsupportedExprKind` ("`.` on
## unsupported type distinct D(O{x:i64})"): the distinct barrier is not
## lifted for a borrowed field access. Found by K8b's pragma axis suite
## (INT-56), row `type/borrow`.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type
  I67O = object
    x: int
  I67D {.borrow: `.`.} = distinct I67O

proc i67BorrowDot(a, b: int8) =
  let t = int(a)
  if I67D(I67O(x: t)).x == 5: symexTarget("hit")

suite "INT-67: a borrowed `.` on a distinct object is exact":
  test "`D(O(x: t)).x == 5` is exact (sat)":
    let r = symexFind(i67BorrowDot, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
