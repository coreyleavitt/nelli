import std/unittest
import nelli/symex

# Phase 15 — Z3c: classifyType `char` branch + `sink`/`lent` strip
# (see docs/symex/RFC-phase15-reconciliation.md §F / Cluster Z).
# char is modelled as an 8-bit unsigned int cell (RFC-0005 S8am: rendered
# as Nim's own `char`, not `uint8` -- see `IRType.isChar`'s own doc
# comment); sink T / lent T are ownership annotations that symex (by-value)
# strips to T.

proc charSut(c: char) =
  if c == 'A': symexTarget("hitA")

proc sinkIntSut(x: sink int) =
  if x == 7: symexTarget("hitSink")

suite "symex Phase 15 — Z3c classifyType (char, sink)":

  test "char parameter is modelled and symex finds a witness":
    let r = symexFind(charSut, tLabel("hitA"))
    check r.status == sxSat

  test "sink int parameter is stripped to int and symex finds a witness":
    let r = symexFind(sinkIntSut, tLabel("hitSink"))
    check r.status == sxSat
