## Phase 3 — call-summary cache observable via `SymexResult.callStats`.
##
## When a callee is invoked twice with arguments of the same Z3
## representation (astHash-equal), the second invocation is served
## from the cache; the body is walked once.
import std/unittest
import std/sequtils
import nelli/symex

proc helper(x: int): int = x + 1

proc twinHelpers(x: int) =
  let a = helper(x)
  let b = helper(x)
  if a + b == 12:
    symexTarget("twin")

## RFC-chapulin-hardening R1 (isReturn drain gap, `symexWalkerVersion` 61):
## `isReturn` now correctly drains the scalar-raise-fork sinks after lowering
## the return-value expr — `helper`'s `return x + 1` (implicit via the
## single-expr body) forks an `OverflowDefect` sub-path under the DEFAULT
## `acOverflow` arithmetic check, so `helper`'s return survivor now carries a
## defect-survivor fact. The summarization cache-eligibility guard
## (runtime.nim, "only cache a clean defect-free return") correctly declines
## to cache a survivor with a defect-survivor fact attached — this is a SOUND
## correction of a PRE-R1 false cache-hit (a return path that could have
## raised was being cached and reused as if it were unconditionally clean).
## To keep testing the cache's positive behaviour (that it DOES serve a
## second identical call from the cache), this test now runs with
## `acOverflow` disabled — `x + 1` on an unconstrained `int` can no longer
## fork an OverflowDefect, so `helper`'s return survivor is clean/defect-free
## again and cache-eligible, restoring the original walked==1/cacheHits==1
## intent. The witness (5) and sxSat verdict are unchanged: they exercise a
## PRE-overflow region (x==5, x+1==6) regardless of arithChecks.
const noOverflowSettings = withSymexSettings() do (s: var SymexSettings):
  s.arithChecks = {acDivByZero, acRange}   ## acOverflow OFF; others untouched

suite "symex Phase 3 — summarization cache":
  test "same callee with same args: body walked once, cache hits once":
    let r = symexFind(twinHelpers, tLabel("twin"), noOverflowSettings)
    check r.status == sxSat
    check r.witness[0] == 5
    let stats = r.callStats.filterIt(it.name == "helper")
    check stats.len == 1
    check stats[0].walked == 1
    check stats[0].cacheHits == 1
