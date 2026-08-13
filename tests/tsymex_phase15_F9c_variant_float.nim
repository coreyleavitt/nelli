import std/unittest
import std/math
import nelli/symex

# Phase 15 — Cluster F cycle F9c: object-variant arm fields of type
# float32/float64 (closes Cluster F).
#
# The discriminant is an existing type (bool/enum); the arm FIELDS are the new
# territory. The Phase-11 variant walker allocates arm fields via
# allocateSym(fieldTy) recursion (so svFloat32/svFloat64 fields allocate),
# arm-field access is parser-routed through isVariantField (binding the float
# SymVal into the env), and extractFromSymVal's svVariant arm recurses to
# extractLeaf (populating float64Vals/float32Vals for the active arm). These
# tests confirm both a float64 and a float32 variant arm round-trip, and that
# both arms of one variant are reachable/witnessable.

type
  V = object
    case k: bool
    of true:  x: float64
    of false: y: int

  V32 = object
    case k: bool
    of true:  a: float32
    of false: b: int

# Each branch carries its own target so symexFind can witness each arm.
proc fTrue(v: V) =
  if v.k:
    if v.x > 0.0: symexTarget("vtrue")
proc fFalse(v: V) =
  if not v.k:
    if v.y < 0: symexTarget("vfalse")
proc fTrue32(v: V32) =
  if v.k:
    if v.a > 0.0'f32: symexTarget("vtrue32")

suite "symex Phase 15 — F9c object-variant float arm fields":

  test "variant true-arm (float64 field): sxSat with x > 0.0":
    let r = symexFind(fTrue, tLabel("vtrue"))
    check r.status == sxSat
    check r.witness[0].k == true
    check r.witness[0].x > 0.0

  test "variant false-arm (int field): sxSat with y < 0":
    let r = symexFind(fFalse, tLabel("vfalse"))
    check r.status == sxSat
    check r.witness[0].k == false
    check r.witness[0].y < 0

  test "variant true-arm (float32 field): sxSat with a > 0.0":
    let r = symexFind(fTrue32, tLabel("vtrue32"))
    check r.status == sxSat
    check r.witness[0].k == true
    check r.witness[0].a > 0.0'f32
