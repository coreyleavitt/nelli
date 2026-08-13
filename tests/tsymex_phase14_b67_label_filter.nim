## Phase 14 cycle B67 — label-by-name `excludeTargets` filter.
##
## Pre-B67: `tLabel("name")` in `excludeTargets` excluded ALL
## labels (by kind). Post-B67: it excludes ONLY the named label.
## Other kinds (`tIndexError`, `tFieldDefect`,
## `tAssertionViolation`) continue to filter by kind.
##
## The parse-time `isUnsupported` diagnostic side of B67 emits a
## `{.hint.}` — that's a compiler emission that's hard to assert
## from a unittest without depending on stderr capture, so this
## file pins only the label-by-name behavior. The hint is
## documented in the parser source.
import std/[unittest, options]
import nelli
import nelli/symex
import nelli/engine/types

proc twoLabels(x: int) =
  if x == 0: symexTarget("zero")
  if x == 1: symexTarget("one")

suite "symex Phase 14 cycle B67 — label-by-name excludeTargets":
  test "excludeTargets = @[tLabel(\"zero\")] suppresses ONLY \"zero\"":
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(
      twoLabels, db, excludeTargets = @[tLabel("zero")])
    var sawZero, sawOne = false
    for f in findings:
      if f.targetDesc == "label(\"zero\")": sawZero = true
      if f.targetDesc == "label(\"one\")":  sawOne  = true
    check not sawZero
    check sawOne

  test "no excludeTargets: both labels discovered (control)":
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(twoLabels, db)
    var sawZero, sawOne = false
    for f in findings:
      if f.targetDesc == "label(\"zero\")": sawZero = true
      if f.targetDesc == "label(\"one\")":  sawOne  = true
    check sawZero
    check sawOne
