## RFC-0016 INT-63: a `let` copy of a placeholder-sort value (typeop
## `letCursor/uninterp`, a modelled exact row: the handle is copied). A
## closure local is the `__closure` placeholder sort, so `let c = f` over
## one is the row, and a call through the copy reads the closure it names.
##
## Found at 7746d32a by K8b's typeop axis suite (INT-56): the row's fragment
## was `var x: pointer = nil; let c = x`, which declined
## `feUnsupportedExprKind` before the `let` was judged: no `pointer` value is
## modelled, so a `nil` of `pointer` has no representation (INT-65, red pin
## `tests/tsymex_0016_int65_placeholdernil.nim`). The row itself was never
## the cause: a closure local reaches it and is exact, and the axis fragment
## is now that shape.
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

proc i63ClosureCall(a, b: int8) =
  let t = int(a)
  let f = proc (x: int): int = x + t
  let c = f
  if c(int(b)) == 9: symexTarget("hit")

proc i63ClosureUnsat(a, b: int8) =
  let t = int(a)
  let f = proc (x: int): int = x * 2 + t
  let c = f
  if c(int(b)) == 1000: symexTarget("hit")

suite "INT-63: a `let` copy of a placeholder-sort value is exact":
  let all = exhaustive(toSeq(low(int8) .. high(int8)))
  test "a call through a `let` copy of a closure local is exact (sat)":
    let r = pinExact(i63ClosureCall, cellKey(axTypeOp, "letCursor/uninterp"),
                     tLabel("hit"), all)
    check r.status == sxSat
  test "an unsat target through the copy is exact (unsat)":
    let r = pinExact(i63ClosureUnsat, cellKey(axTypeOp, "letCursor/uninterp"),
                     tLabel("hit"), all)
    check r.status == sxUnsat
