## RFC-0016 INT-33 (R1-27, PRC-25). A concolic flip's solve is a walker query:
## it asserts the run-wide facts every walker query asserts (`globalRoots`:
## the closure-call axioms, the entry values' type facts, the containers'
## cardinality, the string decompositions) and runs under the walker's caps
## (`checkCapped`: `maxSeqLen`, `seqQueryRLimit`), with `queryTimeoutMs`
## capped at the flip's own `z3TimeoutMs`.
##
## RED before the fix: the flip solved its prefix and negated target alone
## (`z3CheckBounded`). A closure call's result is defined only by its ground
## axioms, which that solve never saw, so the result was free: the solve set
## it to the flipped value, left the draw where it was, and the materialized
## input took the same arm again (`ccoUnrelatedCoverage`, a wasted flip).
##
## The `maxSeqLen` and `seqQueryRLimit` caps change no concolic verdict here:
## concolic symbolicates no string, bytes or float draw (`unsupportedDrawKinds`),
## so no flip query holds a sequence leaf for them to bound.
import std/unittest
import nelli
import nelli/symex
import std/strutils
import nelli/smt/canonicalize
from nelli/smt/admission import cellKey, axConstruct
from ./s8cu_helpers import pinNever

const cell = cellKey(axConstruct, "concolic/flip/roots")

proc closureGate(x: int) =
  let twice = proc (v: int): int = v * 2
  if twice(x) == 14: symexTarget("int33_flip")

suite "INT-33: a concolic flip solves with the walker's run-wide facts":

  test "oracle":
    symexCaptureBegin()
    closureGate(7)
    check "int33_flip" in symexCaptureEnd()

  test "a closure condition flips onto the input that takes it":
    let trace = @[integerChoice(3, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(closureGate, trace, bindings, 0)
    checkpoint "outcome=" & $r.outcome & " coverage=" & $r.coverage &
      " materialized=" & $r.materialized
    check r.outcome == cfoSolvedExact
    check r.materialized.len == 1
    if r.materialized.len == 1:
      check $r.materialized[0] == "int(7)"
    check r.coverage == ccoIntendedCovered
    pinNever(cell, r.coverage == ccoIntendedCovered,
      "a closure condition's flip, materialized " & $r.materialized)

suite "INT-31/INT-33: the walker version floor":
  test "the toolchain segment and the flip's roots moved every key: 407":
    check parseInt(symexWalkerVersion) >= 407
