## RFC-parser-normalization Cluster A, slice A1 (test-only characterization
## corpus) — context 1: BITWISE compound operands.
##
## Purpose: pin TODAY's behavior (walker v71, base commit 8defbf9) as the
## safety net BEFORE A2a/A2b introduce `parseAtomicOperand` and restructure
## the D1c `and`/`or` block. This file covers compound operands of `and`,
## `or`, `xor`, `shl`, `shr` on ints/uints: inline-arith operands, call-result
## operands (interprocedural depth 1 and 2), and one nested-mixed cell.
##
## Every cell is one of:
##   * an ATOMIC-coverage cell (no twin — hoisting an already-atomic operand
##     is a no-op by definition);
##   * a TWIN PAIR: an inline-spelling proc and its let-hoisted twin, where
##     the hoist happens in the SAME proc, AFTER any `symexAssume` the
##     hoisted sub-expression depends on (see the CAUTION note below — this
##     is load-bearing, not stylistic).
##
## CAUTION (RFC drafting history, reproduced here): `scratchpad/probe_146_anf.nim`
## contains a MISTAKEN hoist (`let capm1 = cap - 1` placed BEFORE
## `symexAssume(cap > 0 and ...)`), which legitimately flips the verdict from
## `sxUnsat` to `sxRaised` at `cap = low(int)` — the hoisted temp is no longer
## protected by the assumption that made `cap - 1` overflow-safe. This file's
## twins hoist AFTER the assume they depend on (verified against a corrected
## probe before authoring this corpus), so twin equality holds throughout.
##
## Includes the #149 verbatim reproducer (`(cap and (cap - 1)) == 0`, cell 2)
## and the chronos-faithful `slotIndex`/`capMask` depth-2 shape (cell 6),
## both empirically confirmed clean `sxUnsat` at HEAD (Ground truth item 2).
##
## Runtime discipline (F5 precedent): cheap cells first, the nested-mixed
## cell last; run via `scripts/dt-bounded.sh <c|cpp> tests/tsymex_phase15_A1_bitwise.nim 300`.
import std/[unittest, strutils]
import nelli/symex

# ---------------------------------------------------------------------------
# Twin-equality helper (verdict AND witness/raised-witness). Duplicated per
# A1 file by convention (each test file in this repo is self-contained).
# ---------------------------------------------------------------------------
proc checkTwins[T](rInline, rHoisted: SymexResult[T]) =
  check rInline.status == rHoisted.status
  if rInline.status == sxSat and rHoisted.status == sxSat:
    check rInline.witness == rHoisted.witness
  if rInline.status == sxRaised and rHoisted.status == sxRaised:
    check rInline.raisedTypeId == rHoisted.raisedTypeId
    check rInline.raisedWitness == rHoisted.raisedWitness

# ---------------------------------------------------------------------------
# Cell 1 — atomic coverage (no twin): plain `and` on two atomic int operands.
# ---------------------------------------------------------------------------
proc bitAtomicAnd(a, b: int) =
  if (a and b) == 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell 2 — inline-arith AND, the #149 named cell: `(cap and (cap - 1)) == 0`
# guarded by an assumption that also names the same compound sub-expression.
# depth: 0 (no call). Expected baseline: sxUnsat (proven pow2-mask identity).
# ---------------------------------------------------------------------------
proc bitAndInlineArith(cap: int) =
  symexAssume(cap > 0 and (cap and (cap - 1)) == 0)
  symexAssert((cap and (cap - 1)) == 0)

proc bitAndInlineArithHoisted(cap: int) =
  symexAssume(cap > 0 and (cap and (cap - 1)) == 0)
  let capm1 = cap - 1               ## hoisted AFTER the assume it depends on
  symexAssert((cap and capm1) == 0)

# ---------------------------------------------------------------------------
# Cell 3 — inline-arith OR: `flags or (flags + 1)` is monotonically >= flags
# for non-negative flags (OR only sets bits). depth: 0.
# ---------------------------------------------------------------------------
proc bitOrInlineArith(flags: int) =
  symexAssume(flags >= 0 and flags < 1_000_000)
  symexAssert((flags or (flags + 1)) >= flags)

proc bitOrInlineArithHoisted(flags: int) =
  symexAssume(flags >= 0 and flags < 1_000_000)
  let fp1 = flags + 1
  symexAssert((flags or fp1) >= flags)

# ---------------------------------------------------------------------------
# Cell 4 — inline-arith XOR: `v xor (v shr 1)` (Gray-code shape) stays
# non-negative for a bounded non-negative v. depth: 0.
# ---------------------------------------------------------------------------
proc bitXorInlineArith(v: int) =
  symexAssume(v >= 0 and v < 256)
  symexAssert((v xor (v shr 1)) >= 0)

proc bitXorInlineArithHoisted(v: int) =
  symexAssume(v >= 0 and v < 256)
  let vs1 = v shr 1
  symexAssert((v xor vs1) >= 0)

# ---------------------------------------------------------------------------
# Cell 5 — call-result AND, depth 1: non-let-bound call result used directly
# as a bitwise operand (#149 issue's probe shape 2, `pos and capMask(cap)`).
# ---------------------------------------------------------------------------
func capMaskD1(cap: int): int {.inline.} =
  cap - 1

proc bitAndCallResultD1(pos, cap: int) =
  symexAssume(cap > 0)
  symexAssert((pos and capMaskD1(cap)) <= pos or pos < 0)

proc bitAndCallResultD1Hoisted(pos, cap: int) =
  symexAssume(cap > 0)
  let m = capMaskD1(cap)
  symexAssert((pos and m) <= pos or pos < 0)

# ---------------------------------------------------------------------------
# Cell 6 — call-result AND, depth 2: the chronos-faithful CallbackQueue shape
# (`slotIndex(pos, cap) = pos and capMask(cap)`, called from `checkSlotIndex`).
# Reproduces scratchpad/probe_146_anf2.nim verbatim for the inline twin;
# the hoisted twin rewrites `slotIndex`'s body (the compound operand lives
# THERE, not at the `checkSlotIndex` call site).
# ---------------------------------------------------------------------------
func capMaskD2(cap: int): uint {.inline.} =
  uint(cap - 1)

func slotIndexD2(pos: uint, cap: int): uint {.inline.} =
  pos and capMaskD2(cap)                      ## compound (call-result) operand

proc bitAndCallResultD2(pos: uint, cap: int) =
  symexAssume(cap > 0 and cap <= 1024 and (cap and (cap - 1)) == 0)
  symexAssert(slotIndexD2(pos, cap) < uint(cap))

func slotIndexD2Hoisted(pos: uint, cap: int): uint {.inline.} =
  let cm = capMaskD2(cap)                     ## hoisted call-result operand
  pos and cm

proc bitAndCallResultD2Hoisted(pos: uint, cap: int) =
  symexAssume(cap > 0 and cap <= 1024 and (cap and (cap - 1)) == 0)
  symexAssert(slotIndexD2Hoisted(pos, cap) < uint(cap))

# ---------------------------------------------------------------------------
# Cell 7 — nested-mixed (stresses mixed-theory territory; ordered LAST):
# a call-result operand of `and` combined via `or` with an inline-arith `shr`
# operand of a second `and`. Covers `shl`/`shr` operator coverage for this
# file (`(cap - 1) shr 1`) alongside the AND/OR already exercised above.
# ---------------------------------------------------------------------------
proc bitNestedMixed(pos, cap: int) =
  symexAssume(cap > 0 and cap <= 1024 and (cap and (cap - 1)) == 0 and pos >= 0)
  symexAssert(((pos and capMaskD1(cap)) or ((cap - 1) shr 1)) >= 0)

proc bitNestedMixedHoisted(pos, cap: int) =
  symexAssume(cap > 0 and cap <= 1024 and (cap and (cap - 1)) == 0 and pos >= 0)
  let m = capMaskD1(cap)
  let sh = (cap - 1) shr 1
  symexAssert(((pos and m) or sh) >= 0)

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A1 — bitwise operand-shape characterization corpus":

  test "walker version floor >= 71 (A1 lands on top of Cluster N, base 8defbf9)":
    check parseInt(symexWalkerVersion) >= 71

  test "cell 1 (atomic AND, coverage): reachable, sxSat":
    let r = symexFind(bitAtomicAnd, tLabel("hit"))
    check r.status == sxSat

  test "cell 2 (#149 inline-arith AND): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(bitAndInlineArith, tAssertionViolation())
    let rHoisted = symexFind(bitAndInlineArithHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 3 (inline-arith OR): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(bitOrInlineArith, tAssertionViolation())
    let rHoisted = symexFind(bitOrInlineArithHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 4 (inline-arith XOR): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(bitXorInlineArith, tAssertionViolation())
    let rHoisted = symexFind(bitXorInlineArithHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 5 (call-result AND, depth 1): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(bitAndCallResultD1, tAssertionViolation())
    let rHoisted = symexFind(bitAndCallResultD1Hoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 6 (call-result AND, depth 2, chronos slotIndex/capMask): sxUnsat baseline, twin-identical":
    let rInline  = symexFind(bitAndCallResultD2, tAssertionViolation())
    let rHoisted = symexFind(bitAndCallResultD2Hoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 7 (nested-mixed, AND/OR/SHR): twin-identical baseline (whatever HEAD proves)":
    let rInline  = symexFind(bitNestedMixed, tAssertionViolation())
    let rHoisted = symexFind(bitNestedMixedHoisted, tAssertionViolation())
    checkTwins(rInline, rHoisted)
    # Baseline recorded empirically: no crash, no un-classified degrade.
    check rInline.status in {sxSat, sxUnsat, sxRaised, sxUnknown}
    if rInline.status == sxUnknown:
      check rInline.errors.len > 0
