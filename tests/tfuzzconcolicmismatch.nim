## RFC-z3-optional §The coherence invariant — the assist/capture mismatch.
##
## The 4-argument primitive makes `fuzz(sA, pA, settings, assist = <built
## from sB, pB>)` expressible for the first time. On mismatch the classifier
## builds bindings from the wrong strategy chain and Z3 solves the wrong
## equation. This file pins both halves of what the RFC says about that:
##
## 1. for the **written-inline** form the mismatch is REMOVED, not merely
##    tolerated — `assist` is an `untyped` macro parameter, so `fuzz` sees
##    the raw `concolicAssist(...)` syntax and overwrites its strategy and
##    property arguments with its own captured pair before typechecking;
## 2. for a **pre-built assist value** there is no call node to align, so
##    the mismatch survives — and the damage is bounded: the campaign
##    completes, nothing is falsely admitted, and the cost is wasted solver
##    work (yield-poisoning), never a wrong answer.
##
## Half 2 is required regardless of how half 1 turns out, which is why it
## is pinned separately rather than folded into the same test.
import std/[unittest, tables]
import nelli
import nelli/concolic

proc magicGate(drawnInt: int) {.cover.} =
  if drawnInt == 0xCAFEBABE:
    discard "gate"
  else:
    discard "miss"

proc otherGate(drawnInt: int) {.cover.} =
  ## A DIFFERENT property targeting a DIFFERENT branch value. An assist
  ## built from this one solves for 12345, which does nothing for
  ## `magicGate`'s 0xCAFEBABE gate.
  if drawnInt == 12345:
    discard "other"
  else:
    discard "miss"

suite "RFC-z3-optional — an inline mismatched assist is aligned to the captured pair":

  test "an assist written against a different (strategy, property) still breaks the outer gate":
    # Written against `(integers(0, 100), otherGate)` — a different strategy
    # AND a different property, the worst case the invariant names. If
    # alignment works, the assist that actually runs was built from
    # `(integers(0, 0xFFFFFFFF), magicGate)` and the gate breaks anyway.
    let report = fuzz(integers(0, 0xFFFFFFFF), magicGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = concolicAssist(integers(0, 100), otherGate))
    check report.coverageHits == 2
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic > 0
    check report.stats.provenanceCounts[pvConcolic] > 0

  test "the named spelling is aligned too":
    # `concolicAssist(strat = ..., prop = ...)` must be rewritten the same
    # way as the positional spelling. An alignment pass that silently
    # skipped named arguments would leave exactly the hole it exists to
    # close, and would do it invisibly.
    let report = fuzz(integers(0, 0xFFFFFFFF), magicGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = concolicAssist(strat = integers(0, 100),
                                              prop = otherGate))
    check report.coverageHits == 2
    check report.stats.provenanceCounts[pvConcolic] > 0

suite "RFC-z3-optional — a PRE-BUILT mismatched assist bypasses alignment, bounded":

  test "the campaign completes, admits nothing falsely, and pays only in wasted solves":
    # A `ConcolicAssist` bound to a variable is not a syntactic
    # `concolicAssist(...)` call node, so there is nothing to align — this
    # is the residual the RFC says stays "bounded, not unsound", and this
    # test is what turns that from a claim into a pinned behavior.
    let mismatched = concolicAssist(integers(0, 100), otherGate)
    let report = fuzz(integers(0, 0xFFFFFFFF), magicGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60),
                      assist = mismatched)

    # Bounded: the campaign runs to completion, no exception escapes.
    check report.iterations == 60
    # Not unsound: the gate is NOT reported broken, and nothing is
    # attributed to the solver.
    check report.coverageHits == 1
    check report.stats.provenanceCounts[pvConcolic] == 0

    # The cost is real and is exactly yield-poisoning: the solver DID solve,
    # repeatedly, and every one of those seeds earned nothing.
    #
    # RFC CORRECTION (measured, 2026-08-28). §The coherence invariant
    # attributes the rejections to the re-verify gate
    # (`caoRejectedAtReplay`). That is not what happens, and this suite
    # observed `caoRejectedAtReplay == 0` across every mismatch shape tried
    # (narrow-domain and same-domain). The mismatched seeds are valid draws
    # for the campaign's own strategy, so they replay CLEANLY; they are
    # turned away one layer later, by `admit`'s interestingness fold, as
    # `caoSupersededByRace`. The RFC's conclusion is unchanged and better
    # supported — bounded, not unsound — but the mechanism is admission,
    # not replay.
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic > 0
    check report.stats.concolicYield.admitOutcomes[caoSupersededByRace] > 0
    check report.stats.concolicYield.admitOutcomes[caoAdmitted] == 0
