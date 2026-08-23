## Round-6 B5 (ADR-0028 Leg 1, chained composition) — walker v83.
##
## Catalog #6 (`docs/proptest-findings.md`, chapulin-side; re-triaged in
## `tests/tsymex_retest_c6_tuple_chain.nim` at walker v64): a SECOND scan
## whose start offset is a FIRST scan's own result. The retest ledger's
## `chained` repro (`let (_, p1) = readCStringTwin(data, 2); discard
## readCStringTwin(data, p1)`) never got past `retBindEq`'s tuple-bind gap
## pre-v64, then sat at a classified `sxUnknown` degrade (composite retSym
## drain guard, later `beBudgetExhausted`) through v81 — the loop itself was
## simply unrecognized until B3/B4 landed their closed forms.
##
## **This slice was NOT green-on-arrival (the RFC's `Ver: —` prediction was
## wrong for this exact shape) — a REAL engine fix landed, walker v82->v83.**
## B0/B3/B4's closed forms all guard entry by `i < bound`, so a zero-
## iteration second scan (`tests/tsymex_r6_b0_scanlift_bound.nim`'s own
## `chainedNotFound` precedent) DOES compose for free, confirmed by B5-3/
## B5-3b below with no production change. But a second scan seeded from a
## FIRST scan's own RETURNED position (the faithful catalog-#6 shape, B5-1/
## B5-2/B5-5) hit a genuine gap: `retBindEq`'s fresh call-return placeholder
## (`freshRetSym` -> `allocateSym`, runtime.nim) allocates every `itInt`
## tuple field at its TYPE-DRIVEN BV default regardless of what the callee
## actually computed -- `reconcileInt` (CR-9(c)) only widens the pair used
## IN THE retBindEq EQUALITY CONSTRAINT itself, it never changes the
## CALLER's own env binding for the destructured local, so a chained
## scan's second offset stayed BV-represented and failed `iekStrSubstr`'s
## CR-17 Int-sortedness check. Fixed via `calleeIntOffsetReturnPositions`
## (`dsl_parser.nim`, new): traces which tuple positions of a callee's OWN
## recognized B3/B4 closed form are genuinely Sequence-theory Int, threaded
## onto the `isCall` IR statement (`IRStmt.retIntOffsetPositions`) so the
## call's retSym allocates `svInt` directly there -- mirroring
## `IRParam.isIntOffset`'s existing top-level-param promotion, applied at
## the call-RETURN end of the data flow instead of the param-entry end.
## Two companion fixes landed alongside it (both required for the closed
## form to actually PROVE, not just parse): `parseCalleeImpl` now also
## marks a CALLEE's own `isIntOffset` params (previously only `parseProc*`'s
## top-level entry loop did), so a LITERAL scan-offset argument
## (`readCStringHelper(s, 0)`) gets an svInt proto instead of
## `intLitProto`'s BV default at the call-argument-lowering site; and
## `emitStmt`'s `isCall` NimNode-literal reconstruction (the macro-time
## round trip that rebuilds the parsed IR into the generated proc) now
## serializes the new `retIntOffsetPositions` field -- an IRStmt field the
## emit arm doesn't serialize is silently dropped back to `mkCall`'s `@[]`
## default, which is exactly the failure mode this file's RED run first
## surfaced. Purely additive: an untraced position keeps the pre-existing
## BV default, so no already-decided verdict changes anywhere in the
## corpus. `renderAsChoicesVersion` stays unchanged -- no new witness shape
## (a chained scan's `string`/`int` witnesses render exactly as any other
## already-modeled `string`/`int` param).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

proc readCStringHelper(s: string, offset: int): (string, int) =
  ## B4's accumulating shape (`tests/tsymex_r6_b4_readcstring.nim`'s own
  ## `readCStringTracer`, renamed here only to avoid a duplicate-symbol
  ## collision across test files). Delimiter is `':'`, not chapulin's real
  ## `'\0'` — B4's file doc flags a pre-existing, orthogonal witness-
  ## EXTRACTION bug for solved strings containing an embedded NUL byte
  ## (the byte round-trips as the 5-character SMT-LIB escape text
  ## `\u{0}`); every content-bearing pin in this file follows B3/B4's own
  ## precedent and stays on `':'` to avoid it.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc scanPairHelper(s: string, offset: int): (int, int) =
  ## B3's plain int-result shape (no accumulation) — the other sibling
  ## `readCStringHelper` chains against below for the mixed-composition pin.
  var i = offset
  while i < s.len:
    if s[i] == ';':
      return (i, i + 1)
    i.inc
  raise newException(ScanError, "unterminated")

# ---------------------------------------------------------------------------
# 1. Faithful catalog #6 repro — retires the finding.
# ---------------------------------------------------------------------------
# Position-only (payload content is orthogonal to #6's own report, which was
# about the SECOND scan's offset tracking the first's result, not payload
# bytes) — mirrors Q1-2/Q1-2b's own SAT+UNSAT companion style exactly, the
# proven template for "the dependent chain's start offset is honored, not
# just each scan in isolation", generalized from Q1's skip-while form to
# B4's accumulating closed form (the retest ledger's own `readCStringTwin`
# shape).

proc faithfulSixChain(s: string) =
  let (_, p1) = readCStringHelper(s, 0)
  let (_, p2) = readCStringHelper(s, p1)
  if p1 == 3 and p2 == 6:
    symexTarget("hit")

proc faithfulSixChainImpossible(s: string) =
  ## UNSAT companion: the second scan starts AT `p1`, so a found match can
  ## only report `p2 >= p1 + 1` — `p2 < p1` is unreachable whenever this
  ## line is reached at all (the not-found path raises `ScanError` instead,
  ## never falling through to the check).
  let (_, p1) = readCStringHelper(s, 0)
  let (_, p2) = readCStringHelper(s, p1)
  if p2 < p1:
    symexTarget("impossible")

suite "symex round-6 B5 — faithful catalog #6 repro (retires the finding)":

  test "B5-1: chained accumulating scans (readCStringHelper twice), 2nd offset = 1st result -> sxSat":
    let r = symexFind(faithfulSixChain, tLabel("hit"))
    check r.status == sxSat

  test "B5-1b UNSAT companion: 2nd scan's result can never precede its own (1st-derived) start":
    let r = symexFind(faithfulSixChainImpossible, tLabel("impossible"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# 2. Two-sequential-readCString composition (B4 . B4) — the canonical
#    consumer pattern (filename then mode), non-NUL delimiter, witness shows
#    BOTH payloads.
# ---------------------------------------------------------------------------

proc sutChainedTwoPayloads(s: string) =
  let (payload1, p1) = readCStringHelper(s, 0)
  let (payload2, p2) = readCStringHelper(s, p1)
  if payload1 == "filename" and payload2 == "mode" and p2 == p1 + 5:
    symexTarget("hit_both")

suite "symex round-6 B5 — two-sequential-readCString (filename then mode)":

  test "B5-2: both payloads reachable in one witness (filename, then mode from its terminator) -> sxSat":
    let r = symexFind(sutChainedTwoPayloads, tLabel("hit_both"))
    check r.status == sxSat

  test "B5-2-cross: the witness, replayed through the real function twice, reproduces both payloads":
    let r = symexFind(sutChainedTwoPayloads, tLabel("hit_both"))
    check r.status == sxSat
    let s = r.witness[0]
    let (payload1, p1) = readCStringHelper(s, 0)
    check payload1 == "filename"
    let (payload2, p2) = readCStringHelper(s, p1)
    check payload2 == "mode"
    check p2 == p1 + 5

# ---------------------------------------------------------------------------
# 3. Zero/degenerate chain seed: first scan not-found -> second scan seeded
#    exactly at the bound, honest (zero-iteration) behavior — no clamp
#    resurrection (B0's own guard, generalized past the Q1 shape it was
#    pinned against).
# ---------------------------------------------------------------------------

proc mixedChainNotFoundIntoB3(s: string) =
  ## Mirrors `tests/tsymex_r6_b0_scanlift_bound.nim`'s own `chainedNotFound`
  ## pin verbatim in spirit: the FIRST loop is Q1's skip-while shape (never
  ## raises; a not-found scan leaves `i` exactly at `s.len`, B0's preserved-
  ## not-clamped discipline); the SECOND loop is generalized from Q1's own
  ## sibling to B3's int-result shape (an early-return scan) seeded at
  ## `i + 1` — past `s.len` whenever `i == s.len`, so the second scan's own
  ## entry guard (`j < bound`) is false from the start: a genuinely
  ## zero-iteration second scan, not a "resurrected"/re-clamped one.
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  var j = i + 1
  while j < s.len:
    if s[j] == ';':
      return
    j.inc
  if i == s.len and j == s.len + 1:
    symexTarget("seed-preserved")

proc mixedChainNotFoundImpossible(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  var j = i + 1
  while j < s.len:
    if s[j] == ';':
      return
    j.inc
  if i == s.len and j < s.len + 1:
    symexTarget("impossible")

suite "symex round-6 B5 — zero/degenerate chain seed (no clamp resurrection)":

  test "B5-3: not-found 1st scan seeds a genuinely zero-iteration 2nd scan (i==s.len, j preserved at s.len+1) -> sxSat":
    let r = symexFind(mixedChainNotFoundIntoB3, tLabel("seed-preserved"))
    check r.status == sxSat

  test "B5-3b UNSAT companion: the zero-iteration seed is never re-clamped below its true value":
    let r = symexFind(mixedChainNotFoundImpossible, tLabel("impossible"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# 4. Trip-wire: a chain whose SECOND bound is NOT the scanned string's own
#    `.len` still k-unrolls (recognizer narrowness composes across a chain —
#    the FIRST scan lifting does not "unlock" an unrecognized SECOND one).
# ---------------------------------------------------------------------------

proc scanBoundAlias(s: string, offset: int): int =
  ## Same runtime behavior as `scanPairHelper`, but the bound is a LOCAL
  ## ALIAS (`let n = s.len`) rather than syntactically `s.len` itself —
  ## B0/B3/B4's own recorded near-miss class ("re-lifting the provably-clean
  ## alias is a possible future recognizer, not a bug"): this loop stays
  ## UNRECOGNIZED and k-unrolls honestly, even though the sibling call below
  ## (through `readCStringHelper`) IS recognized.
  let n = s.len
  var i = offset
  while i < n:
    if s[i] == ':':
      return i
    i.inc
  raise newException(ScanError, "unterminated")

proc sutChainSecondNonLenBoundImpossible(s: string) =
  let (_, p1) = readCStringHelper(s, 0)
  let p2 = scanBoundAlias(s, p1)
  if p2 > s.len:
    symexTarget("impossible")

# B5-4 runs under a reduced unroll budget: the pin discriminates RECOGNITION
# (a wrongly-recognized closed form would answer sxSat/sxUnsat at any budget,
# while the honest unrecognized path exhausts the k-unroll -> sxUnknown either
# way), so k=2 pins the same property as k=5. At the default budget this one
# query's chained k-unroll compounds with the v91 overflow forks and the v95
# pair grammar into a 35+ minute Z3 search on CI hardware (it starved the
# 0.5.1 release runners to death) and an intermittent 1 MB-stack overflow
# locally.
const b5TripWireBudget = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxLoopUnwind = 2

# -d:symexCiLeanB5 (symex-windows CI leg only) skips B5-4. Even at k=2 the
# query that finishes in ~40 s under the MSVC-built walker ran a dedicated
# hosted runner to death (>80 min, "runner lost communication") under the
# mingw-built walker at walker v105 -- a toolchain-sensitive divergence in
# this one query family while every other suite runs at CI/local parity.
# The pin remains fully exercised by the nimble task in the MSVC container
# (the environment that reproduces the field toolchain). Root-causing the
# mingw divergence is a filed follow-up; do NOT widen this define to other
# checks.
when not defined(symexCiLeanB5):
  suite "symex round-6 B5 — trip wire (2nd bound not .len stays unrecognized)":

    test "B5-4: chain's 2nd scan has a non-.len (local-alias) bound -> NOT recognized, sxUnknown (unchanged, real trip-wire)":
      let r = symexFind(sutChainSecondNonLenBoundImpossible, tLabel("impossible"),
                        b5TripWireBudget)
      check r.status == sxUnknown

# ---------------------------------------------------------------------------
# 5. Mixed sibling composition: B4 (accumulating) then B3 (plain int-result)
#    chained on the SAME string — proves the closed forms compose across a
#    sibling-recognizer boundary, not just with themselves.
# ---------------------------------------------------------------------------

proc sutB4ThenB3(s: string) =
  let (payload, p1) = readCStringHelper(s, 0)
  let (p2, p3) = scanPairHelper(s, p1)
  if payload == "AB" and p2 == p1 + 2 and p3 == p1 + 3:
    symexTarget("hit_mixed")

suite "symex round-6 B5 — mixed sibling composition (B4 then B3)":

  test "B5-5: B4's accumulating scan chained into B3's plain int-result scan -> sxSat":
    let r = symexFind(sutB4ThenB3, tLabel("hit_mixed"))
    check r.status == sxSat

suite "symex round-6 B5 — walker version pin":

  test "walker version floor >= 83 (chained-scan-composition fix landed this slice)":
    check parseInt(symexWalkerVersion) >= 83
