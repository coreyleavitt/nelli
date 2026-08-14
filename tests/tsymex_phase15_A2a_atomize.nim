## RFC-parser-normalization (#146), Cluster A, slice A2a — small DEMONSTRATION
## corpus: the `parseAtomicOperand` chokepoint is now LIVE (walker v72), so
## these previously-bypass-site shapes (RFC Mechanism census: borrow
## intercept, rune-compare intercept, `not` over a boolean-typed bitwise
## infix) route their compound operands through the same hoist machinery
## their hand-written "Hoisted" twin already used. This file re-asserts, on
## the POST-atomization version, exactly the invariance A1 pinned at v71 —
## same shapes, same twin-equality helper convention (see
## `tsymex_phase15_A1_bitwise.nim`'s header) — as a small, dedicated,
## version-gated proof the boundary guarantee actually holds under the SW
## bump, not merely a restatement of A1 (which stays frozen at its own
## baseline and is not touched by this slice).
import std/[unittest, unicode, strutils]
import nelli/symex

proc checkTwins[T](rInline, rHoisted: SymexResult[T]) =
  check rInline.status == rHoisted.status
  if rInline.status == sxSat and rHoisted.status == sxSat:
    check rInline.witness == rHoisted.witness
  if rInline.status == sxRaised and rHoisted.status == sxRaised:
    check rInline.raisedTypeId == rHoisted.raisedTypeId
    check rInline.raisedWitness == rHoisted.raisedWitness

# ---------------------------------------------------------------------------
# Cell 1 — borrowed-op bypass site: a NESTED borrowed `+` operand
# (`(m1 + m1) + m2`) on a `distinct int`. Twin of
# `tsymex_phase15_A1_arithmetic.nim`'s cell 5.
# ---------------------------------------------------------------------------
type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}    ## needed for tuple-witness equality in checkTwins

proc a2aBorrowNestedArith(m1, m2: Meters) =
  if (m1 + m1) + m2 < Meters(1_000_000_000):
    symexTarget("hit")

proc a2aBorrowNestedArithHoisted(m1, m2: Meters) =
  let m1x2 = m1 + m1
  if m1x2 + m2 < Meters(1_000_000_000):
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 2 — rune-compare bypass site: `r1 < nextRune(r2)`, a compound
# (call-result) operand of a Rune comparison. Twin of
# `tsymex_phase15_A1_comparison.nim`'s cell 5.
# ---------------------------------------------------------------------------
func a2aNextRune(r: Rune): Rune {.inline.} =
  Rune(int32(r) + 1)

proc `<`(a, b: Rune): bool {.borrow.}

proc a2aRuneCompareCallResult(r1, r2: Rune) =
  if r1 < a2aNextRune(r2):
    symexTarget("hit")

proc a2aRuneCompareCallResultHoisted(r1, r2: Rune) =
  let nr = a2aNextRune(r2)
  if r1 < nr:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 3 — the RFC's named cell: `not ((cap and (cap - 1)) == 0)`, i.e. "cap
# is NOT a power of two" — `not` over a BITWISE-typed compound infix (not a
# boolean and/or, so constraint 1 does not exclude it). Twin of
# `tsymex_phase15_A1_unary.nim`'s cell 2.
# ---------------------------------------------------------------------------
proc a2aUnaryNotBitwise(cap: int) =
  symexAssume(cap > 0)
  if not ((cap and (cap - 1)) == 0):
    symexTarget("notPow2")

proc a2aUnaryNotBitwiseHoisted(cap: int) =
  symexAssume(cap > 0)
  let capm1 = cap - 1
  if not ((cap and capm1) == 0):
    symexTarget("notPow2")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A2a — parseAtomicOperand chokepoint demonstration (post-atomization)":

  test "walker version floor: symexWalkerVersion >= 72 (the chokepoint is live)":
    check parseInt(symexWalkerVersion) >= 72

  test "cell 1 (borrow bypass site, nested borrowed +): twin-identical post-atomization":
    let rInline  = symexFind(a2aBorrowNestedArith, tLabel("hit"))
    let rHoisted = symexFind(a2aBorrowNestedArithHoisted, tLabel("hit"))
    checkTwins(rInline, rHoisted)
    check rInline.status in {sxSat, sxUnsat, sxRaised, sxUnknown}
    if rInline.status == sxUnknown:
      check rInline.errors.len > 0

  test "cell 2 (rune-compare bypass site, call-result operand): twin-identical post-atomization":
    let rInline  = symexFind(a2aRuneCompareCallResult, tLabel("hit"))
    let rHoisted = symexFind(a2aRuneCompareCallResultHoisted, tLabel("hit"))
    checkTwins(rInline, rHoisted)
    check rInline.status in {sxSat, sxUnsat, sxRaised, sxUnknown}
    if rInline.status == sxUnknown:
      check rInline.errors.len > 0

  test "cell 3 (not over bitwise compound, #149-named): twin-identical, sxSat, post-atomization":
    let rInline  = symexFind(a2aUnaryNotBitwise, tLabel("notPow2"))
    let rHoisted = symexFind(a2aUnaryNotBitwiseHoisted, tLabel("notPow2"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)
