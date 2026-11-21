## RFC-0016 CI: pins the stdlib row `system.==` (system's generic `==` on a
## record with a non-atom field, walked per field through the instance's own
## `==`, `isSystemRecordEq`). The row was added with PRC-34 and no pin named
## it, so the universe left its cell unclassified. A small object-in-object
## `==`, sat and unsat, each with the compiled program's run beside it.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

type
  Inner = object
    v: int
  Outer = object
    i: Inner
    k: int

proc eqHit(a: int) =
  if Outer(i: Inner(v: a), k: 1) == Outer(i: Inner(v: 4), k: 1):
    symexTarget("hit")

proc eqDead(a: int) =
  if Outer(i: Inner(v: a), k: 1) == Outer(i: Inner(v: 4), k: 1) and a != 4:
    symexTarget("hit")

let eqCell = cellKey(axStdlibBody, "system.==")

suite "CI: system.== on a record with a record field":
  test "sat: the field-wise conjunction holds at a == 4":
    let r = pinExact(eqHit, eqCell)
    check r.status == sxSat

  test "unsat: equal records with a != 4 never meet":
    let r = pinExact(eqDead, eqCell)
    check r.status == sxUnsat
