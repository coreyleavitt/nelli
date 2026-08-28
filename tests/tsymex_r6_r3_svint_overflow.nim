## R3 (post-0.4.0 remediation slice) — svInt overflow honesty, S2,
## walker v91.
##
## ---- Root cause ------------------------------------------------------
## `overflowCond` (`runtime.nim`) forks an `OverflowDefect` path ONLY for
## signed BV operands — its own doc comment said "svInt is skipped entirely
## (BV overflow predicates on Int terms hang Z3)". But round-6's int-offset
## machinery (`IRParam.isIntOffset`/`collectIntOffsetParams`,
## `IRStmt.isLet.lIsIntOffsetLocal`/`collectIntOffsetLiteralLocals`, v88)
## deliberately promotes typed Nim ints (declared `int`/`int64` counters and
## params) to `svInt` so Sequence-theory ops (`iekStrSubstr`/`iekStrFind`)
## accept them. Consequence: post-loop or in-loop arithmetic on a promoted
## counter could NEVER fork `OverflowDefect` in the model, even though real
## Nim WOULD raise — a false `sxUnsat` for any defect-reachability search
## touching a promoted value.
##
## ---- Fix ---------------------------------------------------------------
## The BV-predicate-hang concern does not apply to Int terms: for LINEAR
## Integer arithmetic, overflow of a WIDTH-TYPED value is just a range
## check. `SymVal.svInt` gains `ziWidth`/`ziSigned` (the promoted value's
## static Nim type), populated at every promotion/reconciliation site
## (`allocateSym`'s `isIntOffset`/`intOffsetPositions` arms, the top-level
## param promotion, the `lIsIntOffsetLocal` literal-seeded-local proto, the
## call-arg `formal.isIntOffset` proto, `coerceIntLit`, `reconcileInt`,
## `arithInt`, `iteSV`). `lowerArith` gains an `overflowCondInt` fork
## (svInt's sibling to `overflowCond`) for `bAdd`/`bSub`/`bMul` when the
## operand's width is known and signed — parity with the BV path's own op
## restriction (div/mod are never overflow-forked on either side).
##
## ---- Version discipline --------------------------------------------------
## Verdict-affecting (a previously-false `sxUnsat` now correctly reports
## `sxRaised`): `symexWalkerVersion` bumps 90→91. `renderAsChoicesVersion`
## stays UNCHANGED (11) — no new witness-rendering shape.
##
## ---- Discovered scope note (see section 3 below for the full writeup) ---
## A genuinely `lIsIntOffsetLocal`-seeded LOCAL's width metadata has no
## reachable arithmetic-overflow consequence in the two closed-form idioms
## `collectIntOffsetLiteralLocals` covers — section 3 pins the closely
## related literal-CALL-ARGUMENT case instead (`argProto`, exercised
## end-to-end) and documents why in place of forcing an unreachable pin.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

# =============================================================================
# 1. Tracer (the B4-shaped scan). The promoted counter `q` (call-return
#    int-offset threading, B5) feeds post-loop arithmetic that overflows
#    int64 for any reachable found-branch value (`q >= 1`).
# =============================================================================

proc readCStringR3(s: string, offset: int): (string, int) =
  ## The canonical B4 shape (`tsymex_r6_b4_readcstring.nim`'s
  ## `readCStringTracer`, renamed): early-return-on-match, accumulating scan.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc sutScanCounterOverflowReachable(s: string, start: int) =
  ## `q` is `i + 1` on the found branch, so `q >= 1` whenever the scan
  ## succeeds at all (`start >= 0`). `q + high(int)` REALLY overflows int64
  ## for any `q >= 1`. Under Z3's unbounded Int arithmetic (no fork), `q +
  ## high(int) < q` reduces to the numeral fact `high(int) < 0` — impossible
  ## regardless of `q` — so pre-fix this is (falsely) `sxUnsat`. Post-fix,
  ## the `bAdd` forks `OverflowDefect` before the comparison is even
  ## evaluated on the (mathematically-unreachable) non-raise continuation,
  ## exactly mirroring `tsymex_phase2_overflow`'s own `wrapNeeded` shape.
  symexAssume(start >= 0 and start <= s.len)
  let (_, q) = readCStringR3(s, start)
  if q + high(int) < q:
    symexTarget("scan_overflow_reachable")

suite "symex round-6 R3 — tracer: promoted scan counter forks OverflowDefect":

  test "R3-1: q + high(int) overflows int64 for the found branch (sxRaised, not the pre-fix false sxUnsat)":
    let r = symexFind(sutScanCounterOverflowReachable, tLabel("scan_overflow_reachable"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

# =============================================================================
# 2. UNSAT companion: same shape, bounds make overflow genuinely impossible.
#    Proves the new fork isn't spuriously SAT (a bugged bound formula would
#    show up here as a false sxRaised/sxSat).
# =============================================================================

proc sutScanCounterNoOverflowUnsat(s: string, start: int) =
  ## `q <= s.len + 1 <= 1001` here — nowhere near int64's bounds, so `q + 1`
  ## cannot possibly overflow, AND `q + 1 < q` is impossible regardless
  ## (true in both wrap and no-wrap semantics). Must stay sxUnsat.
  symexAssume(start >= 0 and start <= s.len and s.len <= 1000)
  let (_, q) = readCStringR3(s, start)
  if q + 1 < q:
    symexTarget("scan_no_overflow_impossible")

suite "symex round-6 R3 — UNSAT companion: bounded counter cannot overflow":

  test "R3-2: q + 1 < q is impossible when q is bounded well within int64 (sxUnsat)":
    let r = symexFind(sutScanCounterNoOverflowUnsat, tLabel("scan_no_overflow_impossible"))
    check r.status == sxUnsat

# =============================================================================
# 3. Literal feeding an int-offset position: a LITERAL argument (`0`) at a
#    call site whose formal is `isIntOffset`-traced (`readCStringR3`'s
#    `offset`) — the `argProto` literal-shaping path (`runtime.nim`'s
#    `isCall` arm), sibling to the `lIsIntOffsetLocal` local-declaration
#    proto (both stamp `ziWidth`/`ziSigned` on a proto that then propagates
#    through `coerceIntLit` onto the literal).
#
# ---- Scope note on `lIsIntOffsetLocal` proper (bare local declaration,
# `var pos = 0`) ----------------------------------------------------------
# A genuinely `lIsIntOffsetLocal`-seeded counter's width metadata turns out
# to have NO reachable arithmetic-overflow consequence in either of the two
# closed-form idioms `collectIntOffsetLiteralLocals` covers, discovered
# while building this pin:
#   * Accumulating-scan (`tryRecognizeAccumulatingScan`): BOTH exits
#     reassign the counter via `mkAssign` to a value sourced from a
#     `.find`/`.len`-derived Z3 Int sentinel (`iekStrFind`'s raw
#     `indexOf`/the loop bound) BEFORE any user code past the loop runs —
#     these sentinel constructions are deliberately OUT of this slice's
#     width-population scope (`s.len`/`.find`/`parseInt` results carry no
#     static-width story the way a PROMOTED counter does), so the counter's
#     OWN entry-time promotion is overwritten by an unstamped (`ziWidth ==
#     0`) value before any subsequent arithmetic could observe it.
#   * Pair-loop (`tryRecognizePairLoopIdiom`): the "no defect possible"
#     member branch is an EMPTY block (ADR-0028's own "no fold" design) —
#     nothing about the counter's post-loop value is even computed there.
# `lIsIntOffsetLocal`'s actual, DOCUMENTED job (feeding `iekStrSubstr`'s low
# bound as Int-sorted, avoiding the CR-17 decline) is unaffected by this
# slice and stays covered by `tsymex_r6_b7r2_pathscope.nim` (mandated in
# this slice's sweep, unchanged). Widening `.find`/`.len`/`parseInt`
# sentinels to also carry static width is a legitimate FOLLOW-UP but is
# explicitly out of THIS slice's declared scope (the recorded fork
# resolution's named promotion sites) — reported here rather than forcing
# an unreachable pin or silently dropping the item.
# =============================================================================

proc sutLiteralArgOverflowReachable(s: string) =
  ## `offset` is `readCStringR3`'s `isIntOffset`-traced formal; the literal
  ## `0` argument exercises `argProto`'s literal-shaping path instead of a
  ## symbolic variable argument (R3-1's own shape).
  let (_, q) = readCStringR3(s, 0)
  if q + high(int) < q:
    symexTarget("literal_arg_overflow_reachable")

proc sutLiteralArgNoOverflowUnsat(s: string) =
  symexAssume(s.len <= 1000)
  let (_, q) = readCStringR3(s, 0)
  if q + 1 < q:
    symexTarget("literal_arg_no_overflow_impossible")

suite "symex round-6 R3 — literal argument feeding an isIntOffset formal":

  test "R3-3a: q + high(int) overflows int64 via a literal `0` argument (sxRaised)":
    let r = symexFind(sutLiteralArgOverflowReachable,
                       tLabel("literal_arg_overflow_reachable"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

  test "R3-3b UNSAT companion: bounded counter via a literal argument cannot overflow (sxUnsat)":
    let r = symexFind(sutLiteralArgNoOverflowUnsat,
                       tLabel("literal_arg_no_overflow_impossible"))
    check r.status == sxUnsat

# =============================================================================
# 4. Regression: non-promoted BV arithmetic overflow forking is unchanged
#    (the `tsymex_phase2_overflow` shape, reused inline).
# =============================================================================

proc wrapNeededR3(x: int8) =
  if x + 1 < x:
    symexTarget("bv_regression_wrap")

suite "symex round-6 R3 — regression: non-promoted BV overflow forking unchanged":

  test "R3-4: plain int8 BV overflow still forks and reports the exact witness (sxRaised)":
    let r = symexFind(wrapNeededR3, tLabel("bv_regression_wrap"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"
    check r.raisedWitness[0] == 127

# =============================================================================
# 5. Mixed svInt/svBV via reconcileInt: overflow forking still correct after
#    reconciliation — `m` (a plain, non-promoted `int` param, `svBV64`) is
#    added to `q` (the promoted, `svInt` scan counter) with `m` on the LEFT
#    (`a` position `lowerArith` reads for its fork check), so this exercises
#    `reconcileInt`'s width-stamping on the CONVERTED operand specifically,
#    not merely an already-`svInt` one.
# =============================================================================

proc sutMixedReconcileOverflowReachable(s: string, start: int, m: int) =
  symexAssume(start >= 0 and start <= s.len)
  let (_, q) = readCStringR3(s, start)
  if m + q < m:
    symexTarget("mixed_reconcile_overflow_reachable")

proc sutMixedReconcileNoOverflowUnsat(s: string, start: int, m: int) =
  symexAssume(start >= 0 and start <= s.len and s.len <= 1000)
  symexAssume(m >= -1000 and m <= 1000)
  let (_, q) = readCStringR3(s, start)
  if m + q < m:
    symexTarget("mixed_reconcile_no_overflow_impossible")

suite "symex round-6 R3 — mixed svInt/svBV operand overflow forking (reconcileInt)":

  test "R3-5a: m + q overflows int64 for m near high(int) (sxRaised)":
    let r = symexFind(sutMixedReconcileOverflowReachable,
                       tLabel("mixed_reconcile_overflow_reachable"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

  test "R3-5b UNSAT companion: both operands bounded well within int64 (sxUnsat)":
    let r = symexFind(sutMixedReconcileNoOverflowUnsat,
                       tLabel("mixed_reconcile_no_overflow_impossible"))
    check r.status == sxUnsat

# =============================================================================
# Version pins
# =============================================================================

suite "symex round-6 R3 — version pins":

  test "walker version floor >= 91 (soundness fix -- svInt overflow honesty)":
    check parseInt(symexWalkerVersion) >= 91

  test "renderAsChoicesVersion floor >= 11 (no new witness shape this slice)":
    check parseInt(renderAsChoicesVersion) >= 11
