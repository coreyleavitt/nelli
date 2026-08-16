## Round-6 B3 (ADR-0028 Leg 1, int-result scan sibling) — walker v81.
##
## `tryRecognizeScanIdiom`/`tryMatchScanIdiomShape` (Q1/B0) recognize the
## skip-while-and-clamp scan idiom (`while i < bound and s[i] != lit: inc
## i`). Chapulin's OTHER canonical scan shape — an early-return-on-match
## loop with a trailing raise for "not found" — is structurally different
## (no and-guard, the delimiter check lives in the body's `if`, and a
## `return` replaces the plain index-clamp) and was previously UNRECOGNIZED:
## it k-unrolled and, once `s.len` (or the trip count) grew unconstrained,
## exhausted `maxLoopUnwind` and degraded to `beBudgetExhausted` — the exact
## residue `tsymex_retest_c6_tuple_chain`'s `destructurePair` pin hit
## (catalog #6, ADR-0028's own motivating example).
##
## `tryRecognizeScanPairIdiom` (`dsl_parser.nim`) closes this gap: it
## recognizes
##   while <i> < <bound>:
##     if <s>[<i>] == <lit>:
##       return <expr>            # <expr> may reference <i>
##     inc <i>
## with `<bound>` syntactically `<s>`'s own `.len` (B0's discipline, reused
## verbatim) and rewrites it to the SAME `iekStrFind` 3-arg closed form
## (symbolic start) Q1/B0 use, guarded by loop entry with an entry-read
## probe depositing the real IndexDefect fork a negative start raises — B0's
## whole not-found/OOB split, reused rather than re-derived.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

proc scanPairTracer(s: string, start: int): (int, int) =
  ## The canonical B3 shape: early return on match, raise on fallthrough.
  var i = start
  while i < s.len:
    if s[i] == ':':
      return (i, i + 1)
    i.inc
  raise newException(ScanError, "unterminated")

# ---------------------------------------------------------------------------
# 1. Symbolic-start lift SAT + UNSAT companion.
# ---------------------------------------------------------------------------

proc sutScanPairFoundFromOffset(s: string, start: int) =
  ## SAT: the found position is `start + 4` — a RELATIVE offset from the
  ## SYMBOLIC start, proving the closed form threads `<i>`'s current
  ## (symbolic) value through as `iekStrFind`'s start operand rather than
  ## assuming a literal-zero start (mirrors Q1-P1a's "honoring the start
  ## offset").
  let (p, q) = scanPairTracer(s, start)
  if p == start + 4 and q == start + 5:
    symexTarget("hit")

proc sutScanPairNotFoundClampImpossible(s: string, start: int) =
  ## UNSAT companion (mirrors Q1-1b's own "i > s.len is impossible" style
  ## exactly — direct top-level loop, no wrapper call): a not-found scan
  ## from a SYMBOLIC start clamps `i` to `bound` (`s.len`) and never
  ## exceeds it, generalizing B0's clamp soundness to an arbitrary
  ## (symbolic) start rather than just `start == 0`. Proving this requires
  ## reasoning across ALL possible trip counts (a k-unrolled, unrecognized
  ## loop cannot decide it — see the trip-wire pins below), so this is a
  ## genuine new-capability pin, not a shallow reachability check.
  ##
  ## Deliberately does NOT cross a function-call boundary to check the
  ## FOUND branch's value against `start` (e.g. `p >= start`, destructured
  ## from a wrapper's call) — empirically confirmed (control experiment
  ## against Q1's own UNMODIFIED recognizer, same wrapper-call shape) that
  ## an inlined-callee UNSAT/universal relational proof of that specific
  ## form diverges in this engine build REGARDLESS of B3 — a PRE-EXISTING
  ## general limitation, not a B3 regression, and out of this slice's
  ## scope to fix (dt-bounded doctrine: a hang is an engine defect to be
  ## routed around, not chased, for a pin file).
  ##
  ## `start` is constrained to `[0, s.len]` via `symexAssume` — without
  ## this, the property is VACUOUSLY reachable for a reason having nothing
  ## to do with the closed form: B0's zero-iteration discipline leaves `i`
  ## UNTOUCHED when the loop never runs (`start > s.len` at entry), so an
  ## unconstrained `start` alone (never touched by the loop at all) can
  ## exceed `s.len` — a test-design gap, not a soundness question about the
  ## clamp this pin exists to check.
  symexAssume(start >= 0 and start <= s.len)
  var i = start
  while i < s.len:
    if s[i] == ':':
      return
    i.inc
  if i > s.len:
    symexTarget("impossible")

suite "symex round-6 B3 — symbolic-start lift":

  test "B3-1: found position start+4 from a symbolic start -> sxSat":
    let r = symexFind(sutScanPairFoundFromOffset, tLabel("hit"))
    check r.status == sxSat

  test "B3-1b UNSAT companion: not-found clamp never exceeds bound, for a symbolic start":
    let r = symexFind(sutScanPairNotFoundClampImpossible, tLabel("impossible"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# 2. Not-found fork pin (per B0's split).
# ---------------------------------------------------------------------------

proc scanPairDiscardSUT(s: string, start: int) =
  discard scanPairTracer(s, start)

suite "symex round-6 B3 — not-found fork":

  test "B3-2: no delimiter present -> the modeled ScanError raise is reachable (sxRaised)":
    ## `tRaisedExn` findings report `sxRaised`, not `sxSat` (mirrors
    ## `tsymex_phase15_E4_hierarchy`'s own `raisesMyDefect` convention). Not
    ## asserting `raisedTypeId` here — the not-found fork's observable
    ## contract is that the raise IS reachable (status), not the exact
    ## typeId string an exception raised through a nested-call boundary
    ## renders as (an orthogonal, pre-existing exception-hierarchy concern,
    ## out of B3's scope).
    let r = symexFind(scanPairDiscardSUT, tRaisedExn("ScanError"))
    check r.status == sxRaised

# ---------------------------------------------------------------------------
# 3. OOB / entry-guard pin (per B0's split — negative symbolic start).
# ---------------------------------------------------------------------------

suite "symex round-6 B3 — OOB entry guard":

  test "B3-3: negative symbolic start -> the entry-read probe deposits a real IndexDefect (sxRaised)":
    let r = symexFind(scanPairDiscardSUT, tIndexError())
    check r.status == sxRaised

# ---------------------------------------------------------------------------
# 4. Trip-wire — a shape OUTSIDE the recognizer (non-`.len` bound) still
#    k-unrolls, proving the recognizer stays narrow (mirrors B0's own
#    "local alias bound" decline).
# ---------------------------------------------------------------------------

proc sutScanPairNonLenBoundImpossible(s: string) =
  ## B0's own recorded near-miss class, reused verbatim (RFC: "a bound via
  ## a LOCAL alias (`let n = s.len; while i < n`) is no longer lifted... it
  ## k-unrolls honestly; re-lifting the provably-clean alias is a possible
  ## future recognizer, not a bug"). `n` is a plain symbol reference, not
  ## syntactically `s.len`/`len(s)`, so `boundIsScannedLen` declines it —
  ## same VALUE at runtime, different AST shape, deliberately narrow match.
  ##
  ## Direct top-level loop (no wrapper call, `i` from a LITERAL 0) — mirrors
  ## `tsymex_q1_scanlift`'s OWN Part 2d scope-guard style exactly, the
  ## proven-narrow probe for this class of pin. A wrapper+tuple-destructure
  ## variant of this same near-miss was tried first and diverged from the
  ## expected verdict for reasons orthogonal to recognition (surfaced a
  ## budget-exhausted-flavored `sxRaised` from the callee's own unconditional
  ## fallthrough raise, not a clean `sxUnknown`) — direct, no-wrapper,
  ## no-raise is the reliable shape, matching every OTHER scope-guard pin in
  ## this file and in `tsymex_q1_scanlift`.
  let n = s.len
  var i = 0
  while i < n:
    if s[i] == ':':
      return
    i.inc
  if i > s.len:
    symexTarget("impossible")

# ---------------------------------------------------------------------------
# 5. Bonus trip-wire — B4's future accumulating shape (an `if` + accumulator
#    `.add` + `inc`, THREE body statements) never fires B3's recognizer,
#    which requires EXACTLY two — confirms B3 and B4 can never cross-fire.
# ---------------------------------------------------------------------------

proc scanPairWithAccumulator(s: string, start: int): (string, int) =
  var acc = ""
  var i = start
  while i < s.len:
    if s[i] == ':':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc sutAccPositionHonoredImpossible(s: string, start: int) =
  let (_, q) = scanPairWithAccumulator(s, start)
  if q < start:
    symexTarget("impossible")

suite "symex round-6 B3 — trip wires (recognizer stays narrow)":

  test "B3-4: non-.len bound is NOT recognized -> sxUnknown (unchanged, real trip-wire)":
    let r = symexFind(sutScanPairNonLenBoundImpossible, tLabel("impossible"))
    check r.status == sxUnknown

  test "B3-5: accumulating (3-statement body) shape is NOT recognized by B3 -> sxUnknown":
    let r = symexFind(sutAccPositionHonoredImpossible, tLabel("impossible"))
    check r.status == sxUnknown

suite "symex round-6 B3 — walker version pin":

  test "walker version floor >= 81 (int-result scan-lift closed form)":
    check parseInt(symexWalkerVersion) >= 81
