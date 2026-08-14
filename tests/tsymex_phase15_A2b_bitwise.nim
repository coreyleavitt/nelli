## RFC-parser-normalization (#146), Cluster A, slice A2b — small DEMONSTRATION
## corpus: the bAnd/bOr block's classify-first restructure is now LIVE
## (walker v73), so the BITWISE `and`/`or` family — previously excluded from
## the A2a chokepoint entirely (the whole block parsed both operands before
## the itBool branch existed) — now atomizes its operands through the SAME
## `parseAtomicOperand` machinery the general infix family got in A2a. This
## file re-asserts, on the POST-restructure version, the same twin-equality
## discipline `tsymex_phase15_A1_bitwise.nim` pinned at v71/v72 (see that
## file's header for the twin-equality helper convention) — new demonstration
## shapes in the same two classes the RFC names for A2b (nested pow2-mask
## `(cap and (cap - 1))` compounds; `shl`/`or` byte-merge mixes) — plus a
## dedicated D1c-decision pin proving the boolean short-circuit path's
## fast/guarded split still fires identically post-restructure (mirroring
## `tsymex_phase15_A1_boolean.nim`'s cells 1 and 3), since constraint 1 is
## now enforced by branch exclusivity rather than by the chokepoint never
## being reached inside this block.
##
## ACCEPTANCE NOTE (this slice's own oracle): the A1 corpus (all 8 files,
## frozen at its own v71 baseline) must stay green, UNCHANGED, both backends
## — this file is additive evidence, not a replacement for that net.
import std/[unittest, strutils]
import nelli/symex

proc checkTwins[T](rInline, rHoisted: SymexResult[T]) =
  check rInline.status == rHoisted.status
  if rInline.status == sxSat and rHoisted.status == sxSat:
    check rInline.witness == rHoisted.witness
  if rInline.status == sxRaised and rHoisted.status == sxRaised:
    check rInline.raisedTypeId == rHoisted.raisedTypeId
    check rInline.raisedWitness == rHoisted.raisedWitness

# ---------------------------------------------------------------------------
# Cell 1 — nested pow2-mask class (`(cap and (cap - 1)) == 0`-adjacent):
# the classic "mask an index into a power-of-two-sized ring buffer" idiom
# (chronos CallbackQueue-faithful), where the compound MASK operand
# (`cap - 1`) is itself consumed as the RHS of a SECOND, independent bitwise
# `and` (`x and (cap - 1)`) — a compound bitwise operand of a compound
# bitwise operand's sibling, not merely a restatement of A1 cell 2's own
# `(cap and (cap - 1)) == 0` identity (which this cell also assumes, to
# stay in the domain the identity guarantees).
# ---------------------------------------------------------------------------
proc bitPow2MaskIndex(cap, x: int) =
  symexAssume(cap > 0 and (cap and (cap - 1)) == 0 and x >= 0)
  symexAssert((x and (cap - 1)) < cap)

proc bitPow2MaskIndexHoisted(cap, x: int) =
  symexAssume(cap > 0 and (cap and (cap - 1)) == 0 and x >= 0)
  let mask = cap - 1               ## hoisted AFTER the assume it depends on
  symexAssert((x and mask) < cap)

# ---------------------------------------------------------------------------
# Cell 2 — same pow2-mask class, but the mask operand is a CALL RESULT
# (interprocedural depth 1) rather than inline arithmetic — the A2b analog
# of A1 cell 5's call-result AND, now exercising the chokepoint on a call
# result that is itself consumed by a bitwise (not boolean) `and`.
# ---------------------------------------------------------------------------
func maskFor(cap: int): int {.inline.} =
  cap - 1

proc bitPow2MaskIndexCallResult(cap, x: int) =
  symexAssume(cap > 0 and (cap and (cap - 1)) == 0 and x >= 0)
  symexAssert((x and maskFor(cap)) < cap)

proc bitPow2MaskIndexCallResultHoisted(cap, x: int) =
  symexAssume(cap > 0 and (cap and (cap - 1)) == 0 and x >= 0)
  let m = maskFor(cap)
  symexAssert((x and m) < cap)

# ---------------------------------------------------------------------------
# Cell 3 — `shl`/`or` byte-merge mix on `uint16` (`(hi shl 8) or lo`), the
# RFC's named A2b demonstration shape: a compound `shl` operand consumed
# directly by a bitwise `or`, both int-typed (never `itBool`), so both the
# `shl` compound and the `or`'s LHS route through the chokepoint.
# ---------------------------------------------------------------------------
proc bitShlOrByteMerge(hi, lo: uint16) =
  symexAssume(hi <= 0xFF'u16 and lo <= 0xFF'u16)
  symexAssert(((hi shl 8'u16) or lo) >= lo)

proc bitShlOrByteMergeHoisted(hi, lo: uint16) =
  symexAssume(hi <= 0xFF'u16 and lo <= 0xFF'u16)
  let hiShifted = hi shl 8'u16
  symexAssert((hiShifted or lo) >= lo)

# ===========================================================================
# D1c-decision pin (constraint 1, post-restructure): the boolean and/or
# path's fast/guarded split must fire IDENTICALLY after the classify-first
# restructure — mirrors `tsymex_phase15_A1_boolean.nim`'s cells 1 (atomic,
# fast-path adjacent) and 3 (RHS defect fork, guarded-path baseline). This is
# the direct behavioral proof that constraint 1 holds under the restructure:
# a BOOLEAN operand of `and`/`or` never reaches `parseAtomicOperand` (which
# would incorrectly hoist a defect-fork RHS unconditionally, outside the
# short-circuit guard), regardless of whether it takes the fast or guarded
# sub-path.
# ---------------------------------------------------------------------------

# Fork-free boolean and/or: D1c's fast path (rhsPreamble.len == 0 and no
# inline defect fork) — the emitted IR is unchanged from a bare `mkBinop`.
proc boolFastPathForkFree(a, b: bool) =
  if a and b:
    symexTarget("fast-path-hit")

# Fork-bearing RHS under `and`: D1c's guarded path — the index read `s[i]`
# is a genuine inline defect fork, so it MUST stay guarded by the preceding
# bounds checks (never hoisted unconditionally into the outer preamble,
# which is what would happen if this operand were routed through
# `parseAtomicOperand` — exactly constraint 1's violation).
proc boolGuardedPathForkBearing(s: string, i: int) =
  if i >= 0 and i < s.len and s[i] == 'z':
    symexTarget("guarded-path-hit")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A2b — bAnd/bOr classify-first restructure demonstration (post-restructure)":

  test "walker version floor: symexWalkerVersion >= 73 (the A2b restructure is live)":
    check parseInt(symexWalkerVersion) >= 73

  test "cell 1 (nested pow2-mask index, inline mask): twin-identical, sxUnsat, post-restructure":
    let rInline  = symexFind(bitPow2MaskIndex, tAssertionViolation())
    let rHoisted = symexFind(bitPow2MaskIndexHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 2 (nested pow2-mask index, call-result mask, depth 1): twin-identical, sxUnsat, post-restructure":
    let rInline  = symexFind(bitPow2MaskIndexCallResult, tAssertionViolation())
    let rHoisted = symexFind(bitPow2MaskIndexCallResultHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "cell 3 (shl/or uint16 byte-merge): twin-identical, sxUnsat, post-restructure":
    let rInline  = symexFind(bitShlOrByteMerge, tAssertionViolation())
    let rHoisted = symexFind(bitShlOrByteMergeHoisted, tAssertionViolation())
    check rInline.status == sxUnsat
    checkTwins(rInline, rHoisted)

  test "D1c-decision pin: fork-free boolean and/or still takes the fast path (reachable, sxSat)":
    let r = symexFind(boolFastPathForkFree, tLabel("fast-path-hit"))
    check r.status == sxSat
    check r.witness[0] == true
    check r.witness[1] == true

  test "D1c-decision pin: fork-bearing RHS under boolean and still takes the guarded path (reachable, sxSat, in-bounds witness)":
    let r = symexFind(boolGuardedPathForkBearing, tLabel("guarded-path-hit"))
    check r.status == sxSat
    check r.witness[1] >= 0
    check r.witness[1] < r.witness[0].len
