## Phase 16 SND-2 (RFC-chapulin-hardening, Cluster 1 — Soundness, CRIT).
##
## Bug: `dsl_parser.nim` parsed `symexAssume(cond)` to `mkAssert(cond)` —
## byte-identical to `symexAssert`. But `symexAssume` has FILTER/PRUNE
## semantics (conjoin cond into the path condition), NOT assert semantics.
## The `isAssert` walker arm unconditionally forks an `AssertionDefect`, so
## a violatable `symexAssume` produced a false `sxRaised(AssertionDefect)`
## that could mask a correct `sxUnsat` proof.
##
## Fix (ADR-0019): a DISTINCT `isAssume` IR kind (not a bool flag), so Nim's
## `case`-exhaustiveness compiler-forces every switch site to decide.
## `symexAssume` shares assert's cond-evaluation raise surfacing (div-by-zero
## etc.) and its path-condition conjunction, but NEVER forks the
## AssertionDefect.
import std/[unittest, strutils]
import proptest/symex
import proptest/db
import proptest/smt/[types, canonicalize]

suite "SND-2 — flagship repro: symexAssume must not mask sxUnsat with false sxRaised":

  test "unreachable target alone (no assume): sxUnsat":
    ## `s.len == 3 and s.len == 4` can never hold — the label is genuinely
    ## unreachable. (MIGRATED by SND-4/ADR-0024: the prior `s[0]=='a' and
    ## s[0]=='b'` form indexed a FREE string, so `s==""` makes `s[0]` a real
    ## reachable `IndexDefect` — sxRaised now correctly dominates sxUnsat, which
    ## would mask what THIS test checks. A `s.len`-based unreachable condition
    ## tests the same symexAssume masking property with no incidental OOB.)
    proc unreachableAlone(s: string) =
      if s.len == 3 and s.len == 4:
        symexTarget("bug")
    let r = symexFind(unreachableAlone, tLabel("bug"))
    check r.status == sxUnsat

  test "FLAGSHIP: same unreachable target, with a prepended violatable symexAssume, STILL sxUnsat":
    ## `s.len <= 5` is violatable (a longer string exists), but that must
    ## NOT matter — symexAssume is filter/prune, never an assert fork. The
    ## target is still genuinely unreachable and must STILL prove sxUnsat,
    ## not a false sxRaised(AssertionDefect). (Unreachable condition migrated
    ## to `s.len`-based per SND-4/ADR-0024 — see the test above.)
    proc unreachableWithAssume(s: string) =
      symexAssume(s.len <= 5)
      if s.len == 3 and s.len == 4:
        symexTarget("bug")
    let r = symexFind(unreachableWithAssume, tLabel("bug"))
    check r.status == sxUnsat

suite "SND-2 — scan trap (a): assume-only SUT must not auto-discover tAssertionViolation":

  test "a SUT using ONLY symexAssume (no symexAssert) does not auto-discover an assertion-violation target":
    discard consumeSymexFindings()
    proc assumeOnly(x: int) =
      symexAssume(x >= 0)
      if x == 42:
        symexTarget("hit")
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(assumeOnly, db)
    for f in findings:
      check f.targetDesc != "assertion-violation"

suite "SND-2 — cond-eval raise (b): symexAssume still surfaces raises from evaluating cond":

  test "symexAssume(1 div x == 0) with symbolic x able to be 0 still surfaces DivByZeroDefect":
    proc assumeDiv(x: int) =
      symexAssume(1 div x == 0)
      symexTarget("reached")
    let r = symexFind(assumeDiv, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

suite "SND-2 — cache-key distinctness: mkAssume must NOT collide with mkAssert":

  test "canonicalize(mkAssume(c)) != canonicalize(mkAssert(c)) for identical c":
    ## Round-2 finding: sharing the `isAssert` cache-key tag would let
    ## `symexAssert(c)`/`symexAssume(c)` on the same `c` collapse to the
    ## SAME cache key despite different verdict semantics — silent-wrong
    ## cache reuse.
    let cond = mkBinop(bGt, mkVar("x"), mkIntLit(0))
    let assertKey = canonicalize(mkAssert(cond))
    let assumeKey = canonicalize(mkAssume(cond))
    check assertKey != assumeKey

suite "SND-2 — abstraction narrowing: symexAssume narrows the abstraction like symexAssert":

  test "symexAssume(x >= 0) narrows the abstraction the same way symexAssert(x >= 0) does":
    ## Round-2 finding: `collectAssertRanges` had an `else: discard` that
    ## silently dropped assume-derived range facts (a completeness
    ## regression the scan-trap tests above don't catch). Both variants
    ## must produce the SAME assertion/assume-derived abstraction entry
    ## under `isOptimised`.
    proc withAssert(x: int) =
      symexAssert(x >= 0)
      if x == 42:
        symexTarget("hit")
    proc withAssume(x: int) =
      symexAssume(x >= 0)
      if x == 42:
        symexTarget("hit")
    let rA = symexFind(withAssert, tLabel("hit"), optimisedSymexSettings())
    let rB = symexFind(withAssume, tLabel("hit"), optimisedSymexSettings())
    check rA.status == sxSat
    check rB.status == sxSat
    check rA.abstractions.len == 1
    check rB.abstractions.len == 1
    check rB.abstractions[0].name == rA.abstractions[0].name
    check rB.abstractions[0].interval.lo == rA.abstractions[0].interval.lo
    check rB.abstractions[0].interval.hi == rA.abstractions[0].interval.hi
    check rB.abstractions[0].interval.lo == 0

suite "SND-2 — version pin":

  test "walker version floor: symexWalkerVersion >= 40 (SND-2 landed at 40)":
    # Floor-idiom pin (RFC §Version-pin discipline, Corey-decided synthesis):
    # incidental feature-test pins use a `>=` floor so they auto-track future
    # bumps; only the canonical tsymex_phase15_CR2_cachekey.nim keeps the
    # brittle `==` conscious-bump gate.
    check parseInt(symexWalkerVersion) >= 40
