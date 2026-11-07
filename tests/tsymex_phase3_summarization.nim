## Phase 3 — call-summary cache observable via `SymexResult.callStats`.
##
## When a callee is invoked twice with arguments of the same Z3
## representation (astHash-equal), the second invocation is served
## from the cache; the body is walked once.
import std/unittest
import std/sequtils
import nelli/symex

## RFC-0016 W1-d2 (rule b: the property is the call cache, not the overflow
## opt-out). The helper is UNSIGNED so `x + 1` has no OverflowDefect fork and
## no undefined side in any build: its return survivor is clean and
## cache-eligible under the DEFAULT settings, which agree with the build. The
## guard keeps the witness unique (a wrapped 2x + 2 == 12 has a second root).
proc helper(x: uint): uint = x + 1'u

proc twinHelpers(x: uint) =
  let a = helper(x)
  let b = helper(x)
  if x < 100'u and a + b == 12'u:
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
## `acOverflow` disabled (W1-d2: now an unsigned helper under the default
## settings) — `x + 1` can no longer fork an OverflowDefect, so `helper`'s return survivor is clean/defect-free
## again and cache-eligible, restoring the original walked==1/cacheHits==1
## intent. The witness (5) and sxSat verdict are unchanged: they exercise a
## PRE-overflow region (x==5, x+1==6) regardless of arithChecks.
suite "symex Phase 3 — summarization cache":
  test "same callee with same args: body walked once, cache hits once":
    let r = symexFind(twinHelpers, tLabel("twin"))
    check r.status == sxSat
    check r.witness[0] == 5
    let stats = r.callStats.filterIt(it.name == "helper")
    check stats.len == 1
    check stats[0].walked == 1
    check stats[0].cacheHits == 1
