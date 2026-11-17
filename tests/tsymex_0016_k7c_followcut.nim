## RFC-0016 K7c -- a cap recorded on a concolic walk reaches its callers.
##
## `walkWhileFollowConcrete` stops following a replay that still iterates past
## `maxLoopUnwind` and records `ckLoopUnwindFollow`. The decisions walked after
## that cut are on a fabricated continuation (the guard is still TRUE on the
## path, which the real trace never takes there), so a flip of one of them is
## solved against a prefix no input produces. Before this slice the collect
## result carried no error list, so the cut was invisible and a flip past it
## answered `cfoUnsat` with a trusted verdict for a branch a real input flips.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import ./s8cu_helpers

proc k7cFollowGate(n: int) =
  var i = 0
  while i < n:
    i = i + 1
  if i > 100:
    symexTarget("big")
  else:
    symexTarget("small")

const unwindTwo = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(queryRLimit: 0'u, maxFrontierSize: 0,
                         maxCallDepth: 3, maxLoopUnwind: 2))

const unwindRoomy = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(queryRLimit: 0'u, maxFrontierSize: 0,
                         maxCallDepth: 3, maxLoopUnwind: 20))

let cutTrace = @[integerChoice(5, 0, 1000, 0)]
let cutBindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]

suite "RFC-0016 K7c -- the concolic follow cut is visible":

  test "RED: a flip past the cut is not a trusted unsat":
    # The cut walk's prefix is `i == 2 and i < n`, a continuation the n = 5
    # trace never takes (it exits at i == 5): `i > 100` is false on it, so the
    # solve answered a trusted `cfoUnsat` about a path no input produces.
    let f = concolicFlip(k7cFollowGate, cutTrace, cutBindings, 0, unwindTwo)
    check f.outcome != cfoUnsat
    check not f.soundness.trustedUnsat

  test "the collect result carries the cap it recorded (ckLoopUnwindFollow)":
    pinCapConcolic(k7cFollowGate, "ckLoopUnwindFollow", cutTrace, cutBindings,
                   unwindTwo)
    let r = concolicCollect(k7cFollowGate, cutTrace, cutBindings, unwindTwo)
    check r.errors.len > 0
    check r.soundBranches == 0          ## the one decision is past the cut
    check r.branchTrace.len == 1

  test "the same SUT within its unwind budget records no cap and keeps its trace":
    let r = concolicCollect(k7cFollowGate, cutTrace, cutBindings, unwindRoomy)
    check r.errors.len == 0
    check r.soundBranches == r.branchTrace.len
    check r.branchTrace.len == 1

  test "a flip past the cut is unmodelable and not trusted":
    let f = concolicFlip(k7cFollowGate, cutTrace, cutBindings, 0, unwindTwo)
    check f.outcome == cfoUnmodelable
    check not f.soundness.trustedUnsat
    check scIncomplete in f.soundness.runTaint

  test "the uncut replay's flip is solved over its real prefix and stays trusted":
    # The real prefix pins n == 5 (the loop's exit at i == 5), so `i > 100`
    # is unsat there too, and nothing taints that answer.
    let f = concolicFlip(k7cFollowGate, cutTrace, cutBindings, 0, unwindRoomy)
    check f.outcome == cfoUnsat
    check f.soundness.trustedUnsat

  test "walker version floor: the cut-aware flip is 370 or later":
    check parseInt(symexWalkerVersion) >= 370
