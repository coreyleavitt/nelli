## RFC-parser-normalization Cluster A, slice A1 — context 2: COMPARISON
## compound operands (`<`, `<=`, `==`, etc.).
##
## Same discipline as tsymex_phase15_A1_bitwise.nim (read that file's header
## for the full rationale, the hoist-after-assume caution, and the twin
## helper convention). This file covers: inline-arith on both sides, a
## call-result operand at depth 1 and depth 2, and the rune-compare bypass
## site (`isRuneTyped` intercept, dsl_parser.nim ~:2430) with a compound
## call-result operand — one of the RFC's named bypass classes that would
## skip a naive "hoist in the general infix arm" chokepoint.
import std/[unittest, unicode]
import nelli/symex

proc checkTwins[T](rInline, rHoisted: SymexResult[T]) =
  check rInline.status == rHoisted.status
  if rInline.status == sxSat and rHoisted.status == sxSat:
    check rInline.witness == rHoisted.witness
  if rInline.status == sxRaised and rHoisted.status == sxRaised:
    check rInline.raisedTypeId == rHoisted.raisedTypeId
    check rInline.raisedWitness == rHoisted.raisedWitness

# ---------------------------------------------------------------------------
# Cell 1 — atomic coverage (no twin): plain `<` on two atomic int operands.
# ---------------------------------------------------------------------------
proc cmpAtomicLt(a, b: int) =
  if a < b:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 2 — inline-arith on both sides: `(x + 1) <= (x + y + 1)`, true
# whenever `y >= 0` (assumed). depth: 0. Domain bounded so `x + y + 1` cannot
# overflow — an unbounded `x`/`y` makes `OverflowDefect` reachable (a real,
# genuinely dominant raise per Phase 15 E6), which would test overflow-fork
# behavior instead of the intended compound-comparison-operand shape.
# ---------------------------------------------------------------------------
proc cmpInlineArithBothSides(x, y: int) =
  symexAssume(y >= 0 and x > -1_000_000 and x < 1_000_000 and y < 1_000_000)
  symexAssert((x + 1) <= (x + y + 1))

proc cmpInlineArithBothSidesHoisted(x, y: int) =
  symexAssume(y >= 0 and x > -1_000_000 and x < 1_000_000 and y < 1_000_000)
  let lhs = x + 1
  let rhs = x + y + 1
  symexAssert(lhs <= rhs)

# ---------------------------------------------------------------------------
# Cell 3 — call-result operand, depth 1: `doubleIt(n) >= n` for `n >= 0`.
# Domain bounded for the same overflow reason (n*2 must not overflow).
# ---------------------------------------------------------------------------
func doubleIt(n: int): int {.inline.} =
  n * 2

proc cmpCallResultD1(n: int) =
  symexAssume(n >= 0 and n < 1_000_000)
  symexAssert(doubleIt(n) >= n)

proc cmpCallResultD1Hoisted(n: int) =
  symexAssume(n >= 0 and n < 1_000_000)
  let d = doubleIt(n)
  symexAssert(d >= n)

# ---------------------------------------------------------------------------
# Cell 4 — call-result operand, depth 2: `doubleIt2` calls `doubleIt`.
# ---------------------------------------------------------------------------
func doubleIt2(n: int): int {.inline.} =
  doubleIt(n) + 0

proc cmpCallResultD2(n: int) =
  symexAssume(n >= 0 and n < 1_000_000)
  symexAssert(doubleIt2(n) >= n)

proc cmpCallResultD2Hoisted(n: int) =
  symexAssume(n >= 0 and n < 1_000_000)
  let d2 = doubleIt2(n)
  symexAssert(d2 >= n)

# ---------------------------------------------------------------------------
# Cell 5 — rune-compare bypass site: `r1 < nextRune(r2)`, a compound
# (call-result) operand of a Rune comparison. `isRuneTyped` intercepts
# BEFORE the generic itInt comparison path (dsl_parser.nim ~:2430), so this
# is one of the RFC's named bypass-site classes that a naive infix-arm-only
# chokepoint would miss entirely.
# ---------------------------------------------------------------------------
func nextRune(r: Rune): Rune {.inline.} =
  Rune(int32(r) + 1)

## std/unicode's `Rune` ships only a hand-written `==` (not `{.borrow.}`), so
## `<` needs an explicit borrowed definition to exercise the intercept at all
## (`hasBorrowPragma(ci)` is part of its gate).
proc `<`(a, b: Rune): bool {.borrow.}

proc runeCompareCallResult(r1, r2: Rune) =
  if r1 < nextRune(r2):
    symexTarget("hit")

proc runeCompareCallResultHoisted(r1, r2: Rune) =
  let nr = nextRune(r2)
  if r1 < nr:
    symexTarget("hit")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A1 — comparison operand-shape characterization corpus":

  test "cell 1 (atomic <, coverage): reachable, sxSat":
    let r = symexFind(cmpAtomicLt, tLabel("hit"))
    check r.status == sxSat

  test "cell 2 (inline-arith both sides): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(cmpInlineArithBothSides, tAssertionViolation())
    let rHoisted = symexFind(cmpInlineArithBothSidesHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 3 (call-result operand, depth 1): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(cmpCallResultD1, tAssertionViolation())
    let rHoisted = symexFind(cmpCallResultD1Hoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 4 (call-result operand, depth 2): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(cmpCallResultD2, tAssertionViolation())
    let rHoisted = symexFind(cmpCallResultD2Hoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 5 (rune-compare bypass site, call-result operand): twin-identical baseline":
    let rInline  = symexFind(runeCompareCallResult, tLabel("hit"))
    let rHoisted = symexFind(runeCompareCallResultHoisted, tLabel("hit"))
    checkTwins(rInline, rHoisted)
    check rInline.status in {sxSat, sxUnsat, sxRaised, sxUnknown}
    if rInline.status == sxUnknown:
      check rInline.errors.len > 0
