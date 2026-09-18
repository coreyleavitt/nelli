## Issue #163 wiring audit, wave 2 — the last four gaps.
##
## Four independent findings, one suite each. Method note (inherited from
## #162/#163 wave 1): every symbolic expectation is paired with the same
## computation run for real in this file wherever the shape allows it — a
## taint/soundness bug is exactly the shape where a test can encode the
## engine's own wrong model and pass, and running Nim removes the model
## from the loop.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# W6 — a range-typed (non-enum) variant discriminator with an `else:` arm.
# =============================================================================
## Both discriminator-domain builders (the BV path and the isOptimised
## promoted-Int path) fan an `else:` arm's coverage out over `ty.vDiscTags`,
## which is populated ONLY from an enum impl (`dsl_typebridge.nim`). A
## non-enum (range-alias) discriminator leaves it empty, so the else-arm
## domain silently narrowed to just the explicit `of N:` literals and every
## else-arm value was falsely unreachable.

type
  W6Tag = range[0..10]
  W6Obj = object
    case kind: W6Tag
    of 1: a: int
    of 2: b: int
    else: e: int

proc gatedElseArm(v: W6Obj) =
  if v.kind == 5:
    if v.e == 42:
      symexTarget("else-hit")

proc gatedOfArm(v: W6Obj) =
  ## Non-regression companion: the fix must not cost the explicit arms
  ## their own reachability.
  if v.kind == 1:
    if v.a == 7:
      symexTarget("of-hit")

const Exact = SymexSettings(integerSemantics: isExact)

suite "#163 W6 -- range-alias variant discriminator with an else arm":

  test "oracle -- kind=5 is not an explicit `of` literal, so it really lands in the else arm":
    let v = W6Obj(kind: 5, e: 42)
    check v.kind == 5
    check v.e == 42

  test "isExact (the BV discriminator-domain builder) finds the else-arm target":
    let r = symexFind(gatedElseArm, tLabel("else-hit"), Exact)
    check r.status == sxSat

  test "isOptimised (the promoted-Int discriminator-domain builder) finds it too":
    let r = symexFind(gatedElseArm, tLabel("else-hit"))
    check r.status == sxSat

  test "non-regression -- an explicit `of` arm is still reachable in both modes":
    check symexFind(gatedOfArm, tLabel("of-hit"), Exact).status == sxSat
    check symexFind(gatedOfArm, tLabel("of-hit")).status == sxSat
