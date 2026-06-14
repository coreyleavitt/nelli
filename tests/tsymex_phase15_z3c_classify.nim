import std/unittest
import proptest/symex

# Phase 15 — Z3c: classifyType `char` branch + `sink`/`lent` strip
# (see docs/symex/RFC-phase15-reconciliation.md §F / Cluster Z).
# char is modelled as uint8; sink T / lent T are ownership annotations that
# symex (by-value) strips to T.

proc charSut(c: char) =
  if c == 'A': symexTarget("hitA")

proc sinkIntSut(x: sink int) =
  if x == 7: symexTarget("hitSink")

suite "symex Phase 15 — Z3c classifyType (char, sink)":

  test "char parameter is modelled (uint8) and symex finds a witness":
    let r = symexFind(charSut, tLabel("hitA"))
    check r.status == sxSat

  test "sink int parameter is stripped to int and symex finds a witness":
    let r = symexFind(sinkIntSut, tLabel("hitSink"))
    check r.status == sxSat
