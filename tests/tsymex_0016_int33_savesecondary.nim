## RFC-0016 INT-33 (R1-26). The targeted phase's write of its Pareto front to
## the secondary corpus is guarded like every other database write of
## `forAll`: a `DbError` it raises is reported in `Report.dbErrors`, and with
## `strictDb` it ends the run with a report, never as an exception out of
## `forAll`.
##
## RED before the fix: `saveSecondary` was called bare, so a read-only or
## failing database raised `DbError` out of `forAll` and the caller got no
## report at all.
import std/[unittest, strutils]
import nelli
import nelli/db
from nelli/smt/admission import cellKey, axConstruct
from ./s8cu_helpers import pinNever

const cell = cellKey(axConstruct, "db/secondary/guard")

proc prop(x: int) =
  target(float(x))
  ensure x <= 1000

proc readOnly(): ExampleDatabase =
  readOnlyDatabase(inMemoryDatabase())

suite "INT-33: saveSecondary's DbError does not escape forAll":

  test "the error is reported and the run passes":
    let s = Settings(maxExamples: 30, maxRejections: 1000, seed: 1,
                     testId: "int33-sec", useSA: false, targetedSAIters: 0)
    var r: Report[int]
    var escaped = ""
    try:
      r = forAllUsing(readOnly(), integers(0, 1000), prop, s)
    except DbError as e:
      escaped = e.msg
    check escaped == ""
    check r.outcome == otPassed
    var named = false
    for e in r.dbErrors:
      if "saveSecondary" in e: named = true
    checkpoint $r.dbErrors
    check named
    pinNever(cell, escaped == "" and named,
      "a failing secondary-corpus write is reported, not raised out of forAll")

  test "with strictDb the run ends with a report naming the write":
    let s = Settings(maxExamples: 30, maxRejections: 1000, seed: 1,
                     testId: "int33-sec-strict", useSA: false,
                     targetedSAIters: 0, strictDb: true)
    var r: Report[int]
    var escaped = ""
    try:
      r = forAllUsing(readOnly(), integers(0, 1000), prop, s)
    except DbError as e:
      escaped = e.msg
    check escaped == ""
    check r.outcome == otFalsified
    check "saveSecondary" in r.message
