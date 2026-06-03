## Phase 14 cycle A6 — Z3Int promotion of variant discriminator
## under `isOptimised` (ADR-0003 D6, mandatory).
##
## Pre-A6 the disc was always svBV*; under `isOptimised` the rest
## of the int representation stack runs as Z3Int, so a disc that
## participates in mixed comparisons (rare today, common after
## A4's symbolic-RHS reassign feeds an int-typed expression in)
## could expose representation cracks. A6 promotes the disc to
## svInt under `isOptimised` and adds the svInt case to:
## allocateSym's arm-disjunction emission, walk(isVariantField)'s
## discEq, and walk(isVariantReassign)/walk(isVariantReassignSymbolic).
##
## RED test: under `isOptimised`, the variant SUT still solves AND
## the abstraction log records the disc promotion via
## `aeVariantDisc` evidence. Under `isExact`, neither the
## promotion nor the entry appears.
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/types

type
  K = enum kA, kB, kC
  V = object
    case kind: K
    of kA: a: int
    of kB: b: int
    of kC: c: int

proc hitKB(v: V) =
  if v.kind == kB:
    symexTarget("kB-found")

suite "symex Phase 14 cycle A6 — Z3Int disc promotion":
  test "isOptimised: walker reaches target AND logs aeVariantDisc":
    let r = symexFind(hitKB, tLabel("kB-found"))
    check r.status == sxSat
    var sawPromotion = false
    for ab in r.abstractions:
      if ab.evidence == aeVariantDisc and ab.name.contains("kind"):
        sawPromotion = true
        # The convex hull of {kA, kB, kC} ordinals.
        check ab.interval.lo == 0
        check ab.interval.hi == 2
    check sawPromotion

  test "isExact: no disc promotion entry (BV path is taken)":
    const exactSettings = block:
      var s = defaultSymexSettings()
      s.integerSemantics = isExact
      s
    let r = symexFind(hitKB, tLabel("kB-found"), exactSettings)
    check r.status == sxSat
    for ab in r.abstractions:
      check ab.evidence != aeVariantDisc
