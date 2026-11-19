## RFC-0016 INT-67: a field read through a distinct object type that
## borrows `.` (`type D {.borrow: `.`.} = distinct O`). `D(O(x: t)).x == 5`
## is sat at `a = 5`.
##
## Red at fc08fd17 (and 2206eb51): the read declines `feUnsupportedExprKind`
## ("`.` on unsupported type distinct D(O{x:i64})"): the distinct barrier is
## not lifted for a borrowed field access. Found by K8b's pragma axis suite
## (INT-56), row `type/borrow`. The read is the base object's field read,
## with the operand viewed at its base type.
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

type
  I67O = object
    x: int
    y: int
  I67D {.borrow: `.`.} = distinct I67O

proc i67BorrowDot(a, b: int8) =
  let t = int(a)
  if I67D(I67O(x: t)).x == 5: symexTarget("hit")

proc i67TwoFields(a, b: int8) =
  let d = I67D(I67O(x: int(a), y: int(b)))
  if d.x - d.y == 7 and d.y > 3: symexTarget("hit")

proc i67Unsat(a, b: int8) =
  let d = I67D(I67O(x: int(a), y: int(a) + 1))
  if d.y - d.x == 2: symexTarget("hit")

proc i67Param(d: I67D) =
  if d.x == 3 and d.y == -4: symexTarget("hit")

suite "INT-67: a borrowed `.` on a distinct object is exact":
  let all = exhaustive(toSeq(low(int8) .. high(int8)))
  test "`D(O(x: t)).x == 5` is exact (sat)":
    let r = pinExact(i67BorrowDot, cellKey(axPragma, "type/borrow"),
                     tLabel("hit"), all)
    check r.status == sxSat
  test "two fields of a `let` of the distinct (sat)":
    let r = pinExact(i67TwoFields, cellKey(axPragma, "type/borrow"),
                     tLabel("hit"), all)
    check r.status == sxSat
  test "an unsat relation between two fields (unsat)":
    let r = pinExact(i67Unsat, cellKey(axPragma, "type/borrow"),
                     tLabel("hit"), all)
    check r.status == sxUnsat
  test "a distinct parameter's fields":
    let r = symexFind(i67Param, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & show(r.errors)
    check r.status == sxSat
    check r.trusted
    if r.status == sxSat:
      check r.witness[0].I67O.x == 3
