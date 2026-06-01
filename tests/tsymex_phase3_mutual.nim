## Phase 3 — mutual recursion terminates via the cache cycle break.
##
## Without the active-call set, mutual or direct recursion with
## identical args would walk infinitely until `maxCallDepth` fired.
## With the cycle break, the second occurrence of `(callee, argShape)`
## detects the in-progress entry and short-circuits to a fresh
## symbolic retval marked uncertain.
##
## The behavioral observable: the call terminates without exhausting
## the maxCallDepth budget, and the cycle-broken call shows up as a
## `cacheHits` increment.
import std/unittest
import std/sequtils
import proptest/symex

proc selfRef(n: int): int =
  return selfRef(n)

proc f8(x: int) =
  if selfRef(x) == 42:
    symexTarget("never")

suite "symex Phase 3 — mutual recursion cycle break":
  test "self-recursive with same args terminates without depth overflow":
    let r = symexFind(f8, tLabel("never"))
    # Any path reaching the target is uncertain (the cycle break
    # injected a fresh unconstrained retSym), so the verdict is
    # sxUnknown not sxSat.
    check r.status == sxUnknown
    # And the cycle break was exercised at least once.
    let stats = r.callStats.filterIt(it.name == "selfRef")
    check stats.len == 1
    check stats[0].cacheHits >= 1
