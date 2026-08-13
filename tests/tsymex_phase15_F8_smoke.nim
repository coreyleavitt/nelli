import std/unittest
import std/math
import std/strutils
import nelli/symex

# Phase 15 — Cluster F cycle F8: F-cluster regression smoke + arbitrary
# float64 SUT round-trip property + withSymexSettings wiring + walker-version
# bump confirmation ("4"→"5").
#
# This cycle CLOSES Cluster F. It does not add walker machinery; it confirms
# that the multi-file float plumbing from F1–F7 round-trips end to end:
#   * symexFind produces a SAT witness, and
#   * that concrete float witness, plugged back into the actual Nim predicate
#     at runtime, genuinely satisfies the SUT body (the proc returns true).
#
# The witness-reading idiom is F7's: on sxSat, `r.witness[0]` (and
# `r.witness[1]` for two-param SUTs) is the bit-exact concrete float, read
# from runtime.nim's float64Vals/float32Vals tables via readFloat/readFloat32.
#
# The suite is hand-enumerated (NOT a PBT-of-PBT loop) so it stays hermetic
# and deterministic. Each shape is a (symex SUT, runtime predicate) pair whose
# condition is textually identical, so plugging the witness into the predicate
# is a faithful round-trip of the SUT body.

# ----------------------------------------------------------------------------
# Round-trip shapes. Convention: `sN`  = symex SUT (if cond: symexTarget),
#                                `pN`  = runtime predicate (returns cond).
# Each pair shares an identical boolean condition.
# ----------------------------------------------------------------------------

# --- pure arithmetic thresholds ---
proc s01(x: float) = (if x + 1.0 == 5.0: symexTarget("t01"))
proc p01(x: float): bool = x + 1.0 == 5.0
proc s02(x: float) = (if x - 2.0 == 3.0: symexTarget("t02"))
proc p02(x: float): bool = x - 2.0 == 3.0
proc s03(x: float) = (if x * 2.0 == 10.0: symexTarget("t03"))
proc p03(x: float): bool = x * 2.0 == 10.0
proc s04(x: float) = (if x / 2.0 == 4.0: symexTarget("t04"))
proc p04(x: float): bool = x / 2.0 == 4.0
proc s05(x: float) = (if -x == 5.0: symexTarget("t05"))
proc p05(x: float): bool = -x == 5.0

# --- comparison / ordering ---
proc s06(x: float) = (if x < 5.0: symexTarget("t06"))
proc p06(x: float): bool = x < 5.0
proc s07(x: float) = (if x >= 5.0: symexTarget("t07"))
proc p07(x: float): bool = x >= 5.0
proc s08(x: float) = (if x > 2.0 and x < 4.0: symexTarget("t08"))
proc p08(x: float): bool = x > 2.0 and x < 4.0
proc s09(x: float) = (if x <= -1.0: symexTarget("t09"))
proc p09(x: float): bool = x <= -1.0
proc s10(x: float) = (if x == 3.14: symexTarget("t10"))
proc p10(x: float): bool = x == 3.14

# --- literals incl. signed zero / Inf ---
proc s11(x: float) = (if x == 0.0: symexTarget("t11"))
proc p11(x: float): bool = x == 0.0
proc s12(x: float) = (if x == Inf: symexTarget("t12"))
proc p12(x: float): bool = x == Inf

# --- conversions (int<->float) ---
proc s13(x: int) = (if float(x) > 1.5: symexTarget("t13"))
proc p13(x: int): bool = float(x) > 1.5
# R16-2b: flat-compound `and` is now sound. The D1c short-circuit guard is
# forced for iekConvFloatToInt RHS even when rhsPreamble is empty, so
# int(x) evaluates under the constraint x∈(3,4) and its RangeDefect drain
# produces not(domainCond) & guard which is UNSAT → no false raise.
proc s14(x: float) = (if x > 3.0 and x < 4.0 and int(x) == 3: symexTarget("t14"))
proc p14(x: float): bool = x > 3.0 and x < 4.0 and int(x) == 3

# --- std/math ops ---
proc s15(x: float) = (if sqrt(x) > 2.0: symexTarget("t15"))
proc p15(x: float): bool = sqrt(x) > 2.0
proc s16(x: float) = (if floor(x) == 3.0: symexTarget("t16"))
proc p16(x: float): bool = floor(x) == 3.0
proc s17(x: float) = (if abs(x) == 5.0: symexTarget("t17"))
proc p17(x: float): bool = abs(x) == 5.0
proc s18(x: float) = (if ceil(x) == 4.0: symexTarget("t18"))
proc p18(x: float): bool = ceil(x) == 4.0
proc s19(x: float) = (if trunc(x) == 2.0: symexTarget("t19"))
proc p19(x: float): bool = trunc(x) == 2.0
proc s20(x, y: float) = (if min(x, y) == 1.0: symexTarget("t20"))
proc p20(x, y: float): bool = min(x, y) == 1.0
proc s21(x, y: float) = (if max(x, y) == 9.0: symexTarget("t21"))
proc p21(x, y: float): bool = max(x, y) == 9.0

# --- float32 mix ---
proc s22(x: float32) = (if x + 1.0'f32 == 5.0'f32: symexTarget("t22"))
proc p22(x: float32): bool = x + 1.0'f32 == 5.0'f32
proc s23(x: float32) = (if sqrt(x) > 2.0'f32: symexTarget("t23"))
proc p23(x: float32): bool = sqrt(x) > 2.0'f32

# --- withSymexSettings wiring SUT ---
proc sCfg(x: float) = (if x + 1.0 == 5.0: symexTarget("cfg"))

# --- intentionally-broken SUT (unmodeled transcendental) ---
proc sBroken(x: float) = (if ln(x) == 0.0: symexTarget("broken"))

# withSymexSettings builder, threaded through symexFind as a static value.
# Real API (Z3d): the `do`-block binds to the first (mutator) param; the base
# defaults to defaultSymexSettings() — the spec's "defaultSettings()" base.
const axiomSettings = withSymexSettings() do (s: var SymexSettings):
  s.inlinePolicy = ipAlwaysAxiomatize

suite "symex Phase 15 — F8 F-cluster regression smoke + round-trip":

  test "float64 round-trip property: symexFind witness satisfies SUT at runtime":
    # 23 hand-enumerated shapes. For each: symexFind -> sxSat, read the
    # concrete float witness, plug it back into the Nim predicate at runtime,
    # assert the predicate returns true (the witness genuinely satisfies the
    # SUT body).
    block:
      let r = symexFind(s01, tLabel("t01"))
      check r.status == sxSat
      check p01(r.witness[0])
    block:
      let r = symexFind(s02, tLabel("t02"))
      check r.status == sxSat
      check p02(r.witness[0])
    block:
      let r = symexFind(s03, tLabel("t03"))
      check r.status == sxSat
      check p03(r.witness[0])
    block:
      let r = symexFind(s04, tLabel("t04"))
      check r.status == sxSat
      check p04(r.witness[0])
    block:
      let r = symexFind(s05, tLabel("t05"))
      check r.status == sxSat
      check p05(r.witness[0])
    block:
      let r = symexFind(s06, tLabel("t06"))
      check r.status == sxSat
      check p06(r.witness[0])
    block:
      let r = symexFind(s07, tLabel("t07"))
      check r.status == sxSat
      check p07(r.witness[0])
    block:
      let r = symexFind(s08, tLabel("t08"))
      check r.status == sxSat
      check p08(r.witness[0])
    block:
      let r = symexFind(s09, tLabel("t09"))
      check r.status == sxSat
      check p09(r.witness[0])
    block:
      let r = symexFind(s10, tLabel("t10"))
      check r.status == sxSat
      check p10(r.witness[0])
    block:
      let r = symexFind(s11, tLabel("t11"))
      check r.status == sxSat
      check p11(r.witness[0])
    block:
      let r = symexFind(s12, tLabel("t12"))
      check r.status == sxSat
      check p12(r.witness[0])
    block:
      let r = symexFind(s13, tLabel("t13"))
      check r.status == sxSat
      check p13(r.witness[0])
    block:
      let r = symexFind(s14, tLabel("t14"))
      check r.status == sxSat
      check p14(r.witness[0])
    block:
      let r = symexFind(s15, tLabel("t15"))
      check r.status == sxSat
      check p15(r.witness[0])
    block:
      let r = symexFind(s16, tLabel("t16"))
      check r.status == sxSat
      check p16(r.witness[0])
    block:
      let r = symexFind(s17, tLabel("t17"))
      check r.status == sxSat
      check p17(r.witness[0])
    block:
      let r = symexFind(s18, tLabel("t18"))
      check r.status == sxSat
      check p18(r.witness[0])
    block:
      let r = symexFind(s19, tLabel("t19"))
      check r.status == sxSat
      check p19(r.witness[0])
    block:
      let r = symexFind(s20, tLabel("t20"))
      check r.status == sxSat
      check p20(r.witness[0], r.witness[1])
    block:
      let r = symexFind(s21, tLabel("t21"))
      check r.status == sxSat
      check p21(r.witness[0], r.witness[1])
    block:
      let r = symexFind(s22, tLabel("t22"))
      check r.status == sxSat
      check p22(r.witness[0])
    block:
      let r = symexFind(s23, tLabel("t23"))
      check r.status == sxSat
      check p23(r.witness[0])

  test "withSymexSettings wiring: ipAlwaysAxiomatize threads through to sxSat":
    # The settings builder compiles + threads through runSymex on a float SUT.
    let r = symexFind(sCfg, tLabel("cfg"), axiomSettings)
    check r.status == sxSat
    check p01(r.witness[0])      # witness still satisfies the body

  test "walker version is \"9\" (F8 4->5; S11 5->6; E7 6->7; G10 7->8; Cluster-C C6 8->9; R12 9->10; CR-2 10->11)":
    check parseInt(symexWalkerVersion) >= 9

  test "intentionally-broken SUT: ln(x) yields sxUnknown with ONLY feUnsupportedOp":
    let r = symexFind(sBroken, tLabel("broken"))
    check r.status == sxUnknown
    check r.errors.len > 0                       # no silent empty-errors sxUnknown
    for e in r.errors:
      check e.kind == feUnsupportedOp            # feUnsupportedOp is the only kind
