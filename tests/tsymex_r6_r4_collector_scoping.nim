## Round-6 R4 — collector scoping + guard hardening (findings W1/N8/N2/W2/W3).
##
## Escalated + design-resolved in `docs/rfc/0001-chapulin-hardening.handoff.md`'s
## round-6 STAGE-4-STYLE REVIEW bullet. Root causes:
##
## W1 (High, cross-proc leak): `ctx.stringBackedParams`/
## `ctx.intOffsetLiteralLocals` (`dsl_parser.nim`) are populated ONCE for the
## TOP-LEVEL entry proc and consulted throughout the ENTIRE parse, including
## every recursive callee body `ensureProcRegistered` parses — with NO
## save/clear/restore around that recursion (unlike `ctx.caseNarrow`, which
## already gets exactly this treatment, ADR-0029). An unrelated callee whose
## own param/local happens to share a NAME with the entry's qualifying
## param/local inherits its classification by bare name collision.
##
## N8 (High, design) + N2 (Medium, narrowed): both collectors compute
## matches by TRUE symbol identity (`sameSym`) internally but flatten the
## result to bare NAME strings, and every consult site tests by bare
## `strVal` — so even WITHIN one proc, an unrelated same-named binding in a
## different lexical scope can inherit a classification that was never its
## own.
##
## W2 (High, crash): the scan-shape mutation veto
## (`scanShapeReceiverMutated`) only recognized DIRECT mutation forms
## (bracket-assign / `.add`/`.del`/`.insert` on the receiver itself) — a
## receiver mutated through a `var`-aliased HELPER CALL slipped through,
## stayed classified string-backed, and its `svString` value could reach
## `iekSeqAdd`'s raw `doAssert recv.kind == svSeq` (runtime.nim) — an
## AssertionDefect crash masked to `weInternalWalkerFault`, instead of an
## honest classified decline.
##
## W3 (Medium, latent crash): `considerCandidate` (the B1a classifier's
## candidate walk) called `classifyType` without the standing DoD's
## `typeKind != ntyNone` guard, and the one-level call trace's callee
## resolution used raw `getImpl` instead of the shared `resolveRoutineImpl`
## core — the exact A5 hard-crash class (a non-catchable compile error on
## unsemchecked AST), reachable once the trace recurses onto a
## monomorphized/generic callee's raw impl.
##
## Fix: both collector fields RE-KEYED to `seq[NimNode]` (the qualifying
## symbol's own Sym node) consulted via a new `containsSym` built on the
## codebase's own established `sameSym` (R6) — closes N8/N2 — PLUS
## proc-boundary save/clear/restore around `ensureProcRegistered`'s
## recursive callee parse, mirroring `caseNarrow` exactly — closes W1.
## `scanShapeReceiverMutated` widened to treat a `var`-mode argument
## position at ANY call in the proc body as mutation too (over-approximate:
## declining a classification that was actually harmless only costs a
## missed optimization, never a wrong verdict) — closes W2's root cause;
## `iekSeqAdd`'s raw `doAssert` converted to a classified
## `weInternalWalkerFault` decline as defense in depth. `considerCandidate`
## gained the `typeKind != ntyNone` guard and the trace's callee resolution
## switched to `resolveRoutineImpl` — closes W3.
##
## VERDICT-AFFECTING: bumps `symexWalkerVersion` 91->92 (name-collision
## shapes can change classification, hence verdict).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# Shared scan helper (B4-shaped accumulating scan over a seq[byte] receiver —
# the same idiom `tsymex_r6_b7r_bytescan.nim`/`tsymex_r6_b7r2_pathscope.nim`
# already pin, reused here so the one-level call trace's DELIBERATE promotion
# path (test 6) exercises the real, established shape).
# =============================================================================

type ScanError = object of CatchableError

proc readCStringR4(data: seq[byte], offset: int): (string, int) =
  var s = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (s, i + 1)
    s.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

# =============================================================================
# 1. W1 -- cross-proc leak: an UNRELATED callee's own param, coincidentally
#    named the same as the entry's genuinely-qualifying scan receiver,
#    must get its OWN honest classification, not the entry's.
# =============================================================================

proc probeArrayIndex(data: seq[byte]): int =
  ## Callee's own formal happens to be named `data` too (the round-6 corpus
  ## convention every finding note cites), but this callee has NO scan loop
  ## of its own at all -- an ordinary array index read. Pre-fix, the AMBIENT
  ## `ctx.stringBackedParams` leaked from the ENTRY's own classification of
  ## its `data` makes this callee's UNRELATED `data` parse as a string op
  ## even though the value actually bound here (the caller's `other`) was
  ## never itself classified string-backed.
  data[0].int

proc sutW1CrossProcLeak(data: seq[byte], other: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  # `other` is passed at `probeArrayIndex`'s OWN `data` formal position --
  # a plain, never-scanned, array-modeled seq[byte], UNRELATED to the
  # entry's own genuinely string-backed `data`.
  if i == 3 and probeArrayIndex(other) == 42:
    symexTarget("w1_cross_proc_leak")

suite "symex round-6 R4 -- W1 cross-proc leak closed":

  test "R4-W1: an unrelated callee param sharing the entry's receiver name gets its OWN honest classification -> sxSat":
    let r = symexFind(sutW1CrossProcLeak, tLabel("w1_cross_proc_leak"))
    check r.status == sxSat
    check r.witness[1][0] == 42'u8   ## `other[0] == 42`, read honestly as an array

# =============================================================================
# 2. N2 -- same-proc, same-name colliding LOCAL with a literal initializer.
#    Exploits `iekSeqAdd`'s own documented "fallback (shouldn't happen)"
#    branch (runtime.nim, ~3762): appending an `svInt`-represented value
#    onto a `seq[int]` silently stores 0 instead of the real value --
#    exactly the SILENT-WRONG-ANSWER class N2 warns about. Pre-fix, the
#    UNRELATED inner `pos` (never itself a scan counter) inherits the outer
#    loop's `pos` classification by bare name and gets forced `svInt`;
#    post-fix it stays the type-driven BV64 default and the real value (7)
#    survives the `.add`.
# =============================================================================

proc sutN2NameCollision(data: seq[byte]) =
  # The collision target is reached UNCONDITIONALLY, BEFORE the outer scan
  # -- its own reaching path never touches the loop below at all, so the
  # loop's own solvability/unroll cost cannot affect this target's verdict.
  # The outer loop exists purely for `collectIntOffsetLiteralLocals`'s
  # STATIC structural walk to find (a blanket recursive search over the
  # whole proc body, order-independent) -- it needs no bound on its own.
  block:
    var acc2 = @[0]     ## non-empty seed -- an EMPTY `seq[int]` literal
                         ## (`@[]`) hits a separate, pre-existing, UNRELATED
                         ## allocation gap in this engine (confirmed via
                         ## isolated probe: a raw Z3 sort-mismatch error on
                         ## the initial empty array, nothing to do with R4);
                         ## side-stepped here since it is not this test's
                         ## concern.
    var pos = 7        ## SAME NAME as the loop counter below, DIFFERENT
                        ## binding (distinct lexical scope) -- never itself
                        ## a scan counter.
    acc2.add(pos)
    if acc2[1] == 7:
      symexTarget("n2_collision_add")
  var pos = 0                      ## literal-seeded B6 pair-loop counter --
  var opts: seq[(string, string)] = @[]   ## genuinely qualifies for
  while pos < data.len:                    ## `ctx.intOffsetLiteralLocals`
    let (key, nextPos) = readCStringR4(data, pos)
    if key.len == 0:
      break
    let (val, finalPos) = readCStringR4(data, nextPos)
    opts.add (key, val)
    pos = finalPos

suite "symex round-6 R4 -- N2 same-proc name-collision closed":

  test "R4-N2: an unrelated same-named local literal does not inherit svInt promotion -> sxSat (real value 7 survives .add)":
    let r = symexFind(sutN2NameCollision, tLabel("n2_collision_add"))
    check r.status == sxSat

# =============================================================================
# 3. W2a -- var-aliased helper-call mutation: the receiver must NOT be
#    classified string-backed, falling back to honest array modeling
#    instead (no crash, no misclassification).
# =============================================================================

proc growByteSeqR4(s: var seq[byte]) =
  s.add 0'u8

proc sutW2aVarAliasedMutation(data: var seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  # `data` is passed to `growByteSeqR4`'s `var seq[byte]` formal -- a
  # var-aliased mutation the ORIGINAL veto's direct-form checks (bracket-
  # assign / `.add`/`.del`/`.insert` on the receiver ITSELF) never saw.
  growByteSeqR4(data)
  if i == 2:
    symexTarget("w2a_honest_verdict")

suite "symex round-6 R4 -- W2a var-aliased mutation veto widened":

  test "R4-W2a: a var-aliased helper-call mutation excludes the receiver from string-backing -> honest classified decline, no crash":
    let r = symexFind(sutW2aVarAliasedMutation, tLabel("w2a_honest_verdict"))
    # The receiver correctly stays ARRAY-modeled (not string-backed) post-fix
    # -- reaching `iekSeqAdd`'s PRE-EXISTING, width-8-unsupported degrade
    # (`.add` mutation lowering is width-64-only, a documented pre-existing
    # gap unrelated to string-backing) is itself the proof: a wrongly
    # string-backed receiver would have reached a DIFFERENT failure (the
    # kind-mismatch route W2b's decline targets), not this one. No crash
    # either way -- an honest classified decline, exactly what W2a's DoD
    # allows ("falls to honest array modeling or classified decline").
    check r.status == sxUnknown
    var sawWidthDecline = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault and "unsupported width" in e.msg:
        sawWidthDecline = true
    check sawWidthDecline

# =============================================================================
# 4. W2b -- kind-mismatch decline reachability. TWO-HOP construction: the
#    var-aliased mutation lives in an INTERMEDIATE proc, whose OWN
#    parameter is ALSO (independently) a qualifying scan receiver, exercised
#    through the one-level call trace. Confirms the veto closes this route
#    too (recursively, at every collector invocation) -- see the final
#    report for the reachability finding on the runtime.nim decline branch
#    itself.
# =============================================================================

proc growViaWrapperR4(s: var seq[byte]) =
  growByteSeqR4(s)

proc intermediateScanAndMutate(s: var seq[byte]): int =
  ## This callee's OWN `s` would otherwise qualify string-backed (it has a
  ## genuine Q1-shaped scan loop over `s`) -- but `s` is ALSO passed, in
  ## this SAME body, to `growViaWrapperR4`'s `var seq[byte]` formal. The
  ## veto must exclude `s` from THIS callee's own classification, so the
  ## one-level call trace never promotes the caller's argument either.
  var j = 0
  while j < s.len and s[j] != 0'u8:
    inc j
  growViaWrapperR4(s)
  j

proc sutW2bTwoHopClosure(data: var seq[byte]) =
  if intermediateScanAndMutate(data) == 2:
    symexTarget("w2b_two_hop_closure")

suite "symex round-6 R4 -- W2b two-hop mutation closure":

  test "R4-W2b: a two-hop var-aliased mutation (through an intermediate proc) is still excluded -> honest classified decline, no crash":
    let r = symexFind(sutW2bTwoHopClosure, tLabel("w2b_two_hop_closure"))
    # Same reasoning as R4-W2a: the width-8 decline (not a kind-mismatch
    # decline) is itself the proof `s` stayed array-modeled two hops out.
    check r.status == sxUnknown
    var sawWidthDecline = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault and "unsupported width" in e.msg:
        sawWidthDecline = true
    check sawWidthDecline

# =============================================================================
# 5. W3 -- considerCandidate's classifyType hits a monomorphized/generic
#    callee via the one-level call trace (the A5 hard-crash class).
# =============================================================================

proc barR4[T, U](a: T, b: U): bool =
  ## Verbatim shape of `tsymex_phase15_g8_multi_param.nim`'s own proven-
  ## working `bar[T, U]` (A5's exit-gate pin) -- NOT scan-shaped, so
  ## `considerCandidate` is never invoked for it at all.
  a and b > 5

proc sutW3ResolverRegression(data: seq[byte], flag: bool, n: int) =
  ## `data` carries a genuine Q1 scan (UNRELATED to `barR4`) so the
  ## collector's one-level call trace has real work to do; `barR4` is a
  ## direct call the trace's `walkCalls` visits via `resolveRoutineImpl`
  ## (not raw `getImpl` -- W3's second fix) and recurses
  ## `collectStringBackedByteSeqParamsImpl` onto its raw generic impl,
  ## finding no scan shape there (empty `calleeMarked`, no promotion).
  ##
  ## NOTE (residual, out of scope for this slice, escalated in the round's
  ## report): a construction where the SCAN RECEIVER itself is the
  ## generic-typed formal -- the shape that would exercise
  ## `considerCandidate`'s own `classifyType(sNode)` guard specifically at
  ## the `ntyNone` branch -- was attempted (several shapes/argument forms)
  ## and every attempt hit a DIFFERENT, pre-existing, unguarded
  ## `classifyType` call elsewhere in the REAL (monomorphized) parse path
  ## the instant the generic receiver is actually indexed/`.len`'d in a
  ## full callee body (`parseCalleeImpl`'s per-formal/return-type
  ## classification, the `nnkVarSection` local-binding arm) -- a WIDER,
  ## systemic gap: no existing test in the corpus operates on a generic
  ## proc's own generic-typed parameter via indexing/`.len`/`.add`; every
  ## existing generic test, including G8, only ever COMPARES the generic
  ## value directly. `considerCandidate`'s own guard is still implemented
  ## exactly per the established `typeKind != ntyNone` idiom (code-review-
  ## verified, not exercised live here).
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  if i == 3 and barR4(flag, n):
    symexTarget("w3_resolver_regression")

suite "symex round-6 R4 -- W3 resolveRoutineImpl regression":

  test "R4-W3: a generic (non-scan-shaped) callee reached via the one-level call trace resolves without crashing":
    let r = symexFind(sutW3ResolverRegression, tLabel("w3_resolver_regression"))
    check r.status == sxSat

# =============================================================================
# 6. Regression companion -- B7r's DELIBERATE one-level call-trace promotion
#    must still work: a helper-scan shape with no qualifying loop of the
#    ENTRY's own, promoted purely because the CALLEE's own body qualifies.
# =============================================================================

proc sutRegressionOneLevelTrace(data: seq[byte]) =
  let (payload, _) = readCStringR4(data, 0)
  if payload == "AB":
    symexTarget("regression_trace_sat")

suite "symex round-6 R4 -- regression: B7r one-level call trace still promotes":

  test "R4-REG: entry with no scan of its own, promoted via the callee's own qualifying loop -> sxSat":
    let r = symexFind(sutRegressionOneLevelTrace, tLabel("regression_trace_sat"))
    check r.status == sxSat
    check r.witness[0][0] == byte('A')
    check r.witness[0][1] == byte('B')
    check r.witness[0][2] == 0'u8

suite "symex round-6 R4 -- walker version pin":

  test "walker version floor >= 92 (collector scoping + guard hardening)":
    check parseInt(symexWalkerVersion) >= 92
