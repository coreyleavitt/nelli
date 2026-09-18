## Issue #163 — an opaque call ahead of the target must not cost the answer.
##
## Two defects, one arm. `walk`'s `#137` opaque-call arm (`runtime.nim`) set
## `w.sawUnknown` bare and tainted every continuation, so:
##
##  1. nelli's OWN instrumentation (`{.cover.}`'s `recordEdge`, `{.covercmp.}`'s
##     `logCmp`) degraded the whole run — the fuzzer needs `{.cover.}` on the
##     code under test, and the solver could not see through it, so one proc
##     could not serve both;
##  2. the degrade was UNCLASSIFIED, tripping the Invariant-7 backstop
##     (`weInternalWalkerFault`, "the walker itself hit a bug here") instead of
##     naming the call that cost the answer.
##
## Method note (inherited from #162): every symbolic expectation below is
## paired with the SAME computation run for real in this file. A taint bug is
## exactly the shape where a test can encode the engine's own wrong model and
## pass; running Nim removes the model from the loop.
import std/unittest
import nelli/symex
import nelli/coverage

const Magic = 0x5A4D

# --- the instrumented SUTs -------------------------------------------------
# `{.cover.}` injects `recordEdge(id)` at the top of every branch arm, so the
# raise below sits BEHIND an opaque call on its own path.

proc covered(x: int) {.cover.} =
  if x == Magic: raise newException(ValueError, "magic")

suite "issue 163 -- nelli's own instrumentation is transparent to the solver":

  test "oracle: the instrumented proc really does raise on Magic":
    expect ValueError:
      covered(Magic)
    covered(0)  ## and really does not, otherwise

  test "a {.cover.}'d proc's raise is FOUND, not degraded to sxUnknown":
    let r = symexFind(covered, tRaisedExn("ValueError"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised
