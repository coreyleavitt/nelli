## RFC-0005 (soundness channels) slice S2 -- the replay substrate (§4.2).
##
## `replayWitness(fn, witness, target, pathTaint): ReplayOutcome` executes a
## witness against the REAL `fn`. Pinned here, end to end against real SUT
## procs (and, wherever today's engine can produce one, a real `symexFind`
## witness): all three outcomes; the `dcFreshSymbol`-only eligibility gate;
## witness fidelity (a lossy `ref` render confirms on a hit but never
## refutes, an unexecutable `ptr` placeholder is never run); target-kind
## scope (`tNilAccess` declined); escaping-raise semantics; `var` params;
## and the stackable capture context (`engine/markers.nim`) that keeps an
## engine-internal replay from clobbering a user's in-flight capture.
## Not yet wired into the verdict -- that is S10. No walker bump: no walker
## semantics change.

import std/[unittest, sets]
import nelli/symex

var sideEffects = 0   ## counts real SUT executions; proves "declined" means
                      ## "never ran", not "ran and was ignored"

proc tick() {.symexTransparent.} =
  ## A REAL side effect the walker is promised it cannot observe (statement
  ## position, void) -- so the SUTs below stay fully modelled and `symexFind`
  ## returns genuine clean witnesses, while replay's execution is countable.
  inc sideEffects

proc magicSut(x: int) =
  tick()
  if x == 42:
    symexTarget("magic")

var probeState = 7    ## module-level: unmodellable, and deliberately so

proc probe(): int {.symexTransparent.} = probeState
  ## Its result is USED below, so the transparency promise is not honoured and
  ## the call falls back to OPAQUE: the walker substitutes a fresh,
  ## unconstrained symbol for it -- RFC-0005's `dcFreshSymbol` shape exactly.

proc probedSut(x: int) =
  tick()
  let p = probe()
  if x + p == 100:
    symexTarget("probed")

proc refSut(p: ref int) =
  tick()
  if p[] == 5:
    symexTarget("refHit")

proc ptrSut(p: ptr int) =
  tick()
  if p[] == 3:
    symexTarget("ptrHit")

proc raiser(x: int) =
  tick()
  if x == 7:
    raise newException(ValueError, "seven")

proc indexer(i: int) =
  tick()
  let a = [1, 2, 3]
  discard a[i]

proc caughtRaiser(x: int) =
  tick()
  try:
    if x == 7:
      raise newException(ValueError, "seven")
  except ValueError:
    discard

proc bumper(x: var int) =
  tick()
  x = x + 1
  if x == 10:
    symexTarget("bumped")

suite "RFC-0005 S2 -- replayWitness":
  test "roConfirmed: a real symexFind witness replays onto its label":
    let r = symexFind(magicSut, tLabel("magic"))
    check r.status == sxSat
    sideEffects = 0
    check replayWitness(magicSut, r.witness, tLabel("magic"), {}) == roConfirmed
    check sideEffects == 1

  test "roRefuted: a fresh-symbol witness the real fn does not reach":
    ## The model of `probedSut` havocs `probe()`, so it admits `x = 100`
    ## (with the havoc at 0); reality's `probe()` returns 7, so on x = 100
    ## `fn` runs to completion without reaching the label. Since RFC-0005
    ## S1c the engine DOES solve this tainted path -- but the model is a
    ## CANDIDATE (`RawResult.candidates`, an untyped `RawWitness`), and the
    ## public surface cannot hand it over until S10: under the all-⊤
    ## `classOf` default the path carries `scSpurious`, so `symexFind`
    ## reports `sxUnknown` (§2.3 rule 4), and typing a candidate's witness
    ## into `fn`'s parameter tuple is the macro codegen S10 adds. So the
    ## solver's choice is written out; it is the INPUT to replay, and the
    ## outcome is what replay observes.
    let r = symexFind(probedSut, tLabel("probed"))
    check r.status == sxUnknown   ## solved into a candidate, not surfaced (pre-S10)
    sideEffects = 0
    check replayWitness(probedSut, (100,), tLabel("probed"),
                        pathTaint(dcFreshSymbol)) == roRefuted
    check sideEffects == 1
    ## The same fresh-symbol-tainted candidate on the input reality agrees
    ## with confirms -- the eligible gate does not decline it.
    check replayWitness(probedSut, (93,), tLabel("probed"),
                        pathTaint(dcFreshSymbol)) == roConfirmed

  test "eligibility gate: only an entirely-dcFreshSymbol path taint replays":
    ## Real witness, reaching input -- so any non-confirmed answer below is the
    ## GATE, not the SUT. Every declined case must also leave `fn` unrun.
    let r = symexFind(magicSut, tLabel("magic"))
    check r.status == sxSat
    check replayEligible({})
    check replayEligible(pathTaint(dcFreshSymbol))
    check replayEligible(pathTaint(dcOmitted))
    for c in [dcSubstituted, dcFabricated, dcNoAnswer]:
      check not replayEligible(pathTaint(c))
      sideEffects = 0
      check replayWitness(magicSut, r.witness, tLabel("magic"),
                          pathTaint(c)) == roInconclusive
      check sideEffects == 0
    ## A fresh-symbol join with any other class is no longer "entirely"
    ## fresh-symbol.
    check not replayEligible(pathTaint(dcFreshSymbol) + pathTaint(dcFabricated))

  test "witness fidelity: a lossy ref witness confirms on a hit, never refutes":
    ## `ref int` renders as a fresh non-nil cell with no alias structure
    ## (`emitTyAndReader`'s `itRef` arm) -- safe to run, not the model.
    let r = symexFind(refSut, tLabel("refHit"))
    check r.status == sxSat
    sideEffects = 0
    check replayWitness(refSut, r.witness, tLabel("refHit"), {}) == roConfirmed
    check sideEffects == 1
    ## A miss on a lossy render says nothing about the model's witness.
    var cell = new int
    cell[] = 0
    check replayWitness(refSut, (cell,), tLabel("refHit"), {}) == roInconclusive
    check sideEffects == 2

  test "witness fidelity: an unexecutable ptr witness is never run":
    ## `ptr T` renders as a nil placeholder: running it would SIGSEGV.
    ## Declined at macro time, so even a reaching, valid input is not run.
    var cellVal = 3
    sideEffects = 0
    check replayWitness(ptrSut, (addr cellVal,), tLabel("ptrHit"), {}) ==
          roInconclusive
    check sideEffects == 0

  test "target scope: tNilAccess is declined without running":
    let r = symexFind(magicSut, tLabel("magic"))
    check r.status == sxSat
    sideEffects = 0
    check replayWitness(magicSut, r.witness, tNilAccess(), {}) == roInconclusive
    check sideEffects == 0

  test "raise targets: an escaping raise confirms; a miss or wrong type refutes":
    let r = symexFind(raiser, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    sideEffects = 0
    check replayWitness(raiser, r.raisedWitness, tRaisedExn(r.raisedTypeId),
                        {}) == roConfirmed
    check replayWitness(raiser, r.raisedWitness, tRaisedExn(), {}) == roConfirmed
    check replayWitness(raiser, r.raisedWitness, tRaisedExn("KeyError"),
                        {}) == roRefuted
    check replayWitness(raiser, (1,), tRaisedExn("ValueError"), {}) == roRefuted
    check sideEffects == 4

  test "raise targets: a handler-caught raise is not an escaping raise":
    ## The walker reports only raises that escape the SUT frame; replay
    ## observes exactly that, so a caught raise refutes.
    sideEffects = 0
    check replayWitness(caughtRaiser, (7,), tRaisedExn("ValueError"), {}) ==
          roRefuted
    check sideEffects == 1

  test "defect targets: an IndexDefect witness confirms (catchable, panics:off)":
    let r = symexFind(indexer, tIndexError())
    check r.status == sxRaised
    sideEffects = 0
    check replayWitness(indexer, r.raisedWitness, tIndexError(), {}) ==
          roConfirmed
    check replayWitness(indexer, r.raisedWitness,
                        tRaisedExn(r.raisedTypeId), {}) == roConfirmed
    check replayWitness(indexer, (1,), tIndexError(), {}) == roRefuted
    check sideEffects == 3

  test "var params: the witness is splatted through a var local":
    let r = symexFind(bumper, tLabel("bumped"))
    check r.status == sxSat
    sideEffects = 0
    check replayWitness(bumper, r.witness, tLabel("bumped"), {}) == roConfirmed
    check sideEffects == 1

suite "RFC-0005 S2 -- stackable capture context":
  test "a nested capture neither clears nor leaks into the enclosing one":
    symexCaptureBegin()
    symexTarget("outerBefore")
    symexCaptureBegin()
    symexTarget("inner")
    let inner = symexCaptureEnd()
    symexTarget("outerAfter")
    let outer = symexCaptureEnd()
    check inner == toHashSet(["inner"])
    check outer == toHashSet(["outerBefore", "outerAfter"])
    ## Fully unwound: the marker is inert again.
    symexTarget("stray")
    symexCaptureBegin()
    check symexCaptureEnd().len == 0

  test "replay inside a user's active capture leaves that capture intact":
    ## The §4.2 reentrancy hazard, end to end: S10 runs replay INSIDE
    ## `symexFind`, which a user may call during their own capture.
    let r = symexFind(magicSut, tLabel("magic"))
    check r.status == sxSat
    symexCaptureBegin()
    symexTarget("userBefore")
    check replayWitness(magicSut, r.witness, tLabel("magic"), {}) == roConfirmed
    symexTarget("userAfter")
    let userHits = symexCaptureEnd()
    check userHits == toHashSet(["userBefore", "userAfter"])
    check "magic" notin userHits

  test "replay nested in replay: each execution reads only its own frame":
    proc outerSut(x: int) =
      symexTarget("outerLabel")
      ## The inner replay reaches "magic"; the outer frame must not see it.
      doAssert replayWitness(magicSut, (42,), tLabel("magic"), {}) ==
               roConfirmed
    check replayWitness(outerSut, (0,), tLabel("outerLabel"), {}) ==
          roConfirmed
    check replayWitness(outerSut, (0,), tLabel("magic"), {}) == roRefuted
