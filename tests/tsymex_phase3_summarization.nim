## Phase 3 — call-summary cache observable via `SymexResult.callStats`.
##
## When a callee is invoked twice with arguments of the same Z3
## representation (astHash-equal), the second invocation is served
## from the cache; the body is walked once.
import std/unittest
import std/sequtils
import proptest/symex

proc helper(x: int): int = x + 1

proc twinHelpers(x: int) =
  let a = helper(x)
  let b = helper(x)
  if a + b == 12:
    symexTarget("twin")

suite "symex Phase 3 — summarization cache":
  test "same callee with same args: body walked once, cache hits once":
    let r = symexFind(twinHelpers, tLabel("twin"))
    check r.status == sxSat
    check r.witness[0] == 5
    let stats = r.callStats.filterIt(it.name == "helper")
    check stats.len == 1
    check stats[0].walked == 1
    check stats[0].cacheHits == 1
