import std/unittest
import std/sequtils
import proptest/symex

# Phase 15 — F5 hang regression: `p[] = int(f)` + ordering goal hangs Z3.
#
# ROOT CAUSE (NI-2 + int64 int(f) anomaly):
#   commit df1ca6b (NI-2) added an `intToBv[64]` coercion in `isDerefWrite` to
#   store an `svInt` value into a `ref int` (BV64) heap cell. The int64 case of
#   `iekConvFloatToInt` was returning `svInt` via `bvToZ3Int(bv64_term)`, so
#   `int(f)` produced `bv2int(fp.to.sbv 64 RTZ f)` as a Z3Int. The NI-2
#   coercion then wrapped it with `int2bv`, giving the stored heap value:
#
#     int2bv 64 (bv2int (fp.to.sbv 64 RTZ f))
#
#   When a later `q[]` read is compared with an ordering goal (`q[] > k`),
#   Z3 is given a BV-ordering constraint over the Int+BV+FP round-trip term
#   and hangs indefinitely (the F5 pathology: mixed Int+BV+FP theory).
#
# FIX: the int64 `iekConvFloatToInt` case must return `svBV64` directly
#   (symmetric with the int32 case that already returns `svBV32`). Then:
#   - `int(f)` yields `svBV64` with term `fp.to.sbv 64 RTZ f` (pure QF_BVFP)
#   - the `isDerefWrite` `svInt` coercion never fires (valSV.kind != svInt)
#   - stored heap value = clean `fp.to.sbv 64 RTZ f`
#   - ordering goal `q[] > k` is a pure BV-ordering goal: Z3 terminates fast
#
# RED STATE (before fix): dt-bounded.sh exits 137 (hung at 45s timeout).
# GREEN STATE (after fix): sxSat with a round-tripping witness promptly.

proc f5HangSut(f: float, k: int) =
  ## SUT that reproduces the F5 hang:
  ##   1. Allocate a ref int via `let p = new int`.
  ##   2. Write int(f) through the pointer.
  ##   3. Pose an ordering goal over the read-back value (via a direct re-deref).
  ## Before the fix: `p[] = int(f)` stores `int2bv(bv2int(fp.to.sbv f))`
  ## into the heap. When `p[] > k` is lowered as a read-back, Z3 gets a
  ## BV-ordering goal with an Int+BV+FP round-trip sub-term and hangs.
  ## After the fix: stored term is `fp.to.sbv 64 RTZ f`; goal is pure BV.
  let p = new int
  p[] = int(f)
  if p[] > k:
    symexTarget("f5HangHit")   # ordering goal over the stored float→int value

suite "symex Phase 15 — F5 hang regression: p[]=int(f) ordering goal":

  test "F5-hang: q[]=int(f); q[] > k yields sxSat promptly (RED: hangs before fix)":
    ## The core regression test. Before the fix this query hangs Z3 (BV-ordering
    ## goal over int2bv(bv2int(fp.to.sbv f))). After the fix the stored term is
    ## pure BV and Z3 terminates with sxSat. A concrete (f, k) witness is
    ## returned; plugging it in confirms q[] > k at runtime.
    let r = symexFind(f5HangSut, tLabel("f5HangHit"))
    check r.status == sxSat
    # Witness round-trip: the returned (f, k) must satisfy the predicate.
    let f = r.witness[0]   # float
    let k = r.witness[1]   # int
    # int(f) == p[] at runtime; k is the compared-against value.
    check int(f) > k

  test "F5-hang: feConvDomainExcluded hint emitted (domain bounded, honest-incomplete)":
    ## The domain-bounding hint (CR-3) must survive the svBV64 change since
    ## the same `convFloatToIntBoundConds` deposit path is unchanged.
    let r = symexFind(f5HangSut, tLabel("f5HangHit"))
    check r.status == sxSat
    check r.errors.anyIt(it.kind == feConvDomainExcluded and it.severity == sevHint)
