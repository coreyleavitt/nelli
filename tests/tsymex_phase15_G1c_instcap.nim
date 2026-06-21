## Phase 15 — Cluster G, cycle G1c: generic instantiation cap.
##
## LOCKED DECISION (see RFC-phase15-reconciliation.md §F Cluster G): generics
## symex via PARSE-TIME monomorphization; G1a's instKey'd `ctx.procs` IS the
## per-walker instantiation cache. G1c adds the CAP from ADR-0008 D7 / OQ5:
## `SymexSettings.maxInstantiationsPerProc` (net-new, default 64). When a SINGLE
## generic proc is instantiated at MORE than the cap's worth of DISTINCT types,
## the over-cap instantiation is NOT registered; instead a
## `SymexErrorInfo{kind: geInstantiationCapped, severity: sevError}` is emitted
## so the affected path resolves to `sxUnknown` (Invariant 3 — never silent).
##
## The cap is PER-BASE-PROC: 64 distinct instantiations of ONE generic proc hit
## the cap; different generic procs have independent counts. To make this
## testable without 65 instantiations, we use `withSymexSettings` to set a small
## cap (2) and a SUT that instantiates ONE generic at 3 distinct types.
import std/unittest
import proptest/symex

# Monomorphized body differs by T (sizeof) — same load-bearing generic as G1a.
proc szof[T](x: T): int = sizeof(T)

# ONE generic (`szof`) instantiated at THREE distinct types (int8/int16/int32).
# Under a cap of 2 the third instantiation (int32) is over-cap → not registered
# → geInstantiationCapped + sxUnknown.
proc threeInsts(a: int8, b: int16, c: int32) =
  if szof(a) == 1 and szof(b) == 2 and szof(c) == 4:
    symexTarget("found")

# Negative case: same SUT under the DEFAULT (high) cap resolves cleanly to
# sxSat with NO geInstantiationCapped — the cap must not false-positive on a
# handful of instantiations.
proc fewInsts(a: int8, b: int16, c: int32) =
  if szof(a) == 1 and szof(b) == 2 and szof(c) == 4:
    symexTarget("found")

const lowCap = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxInstantiationsPerProc = 2

suite "symex Phase 15 G1c — generic instantiation cap (maxInstantiationsPerProc)":

  test "exceeding the per-proc cap → sxUnknown + geInstantiationCapped (sevError)":
    let r = symexFind(threeInsts, tLabel("found"), lowCap)
    check r.status == sxUnknown
    check r.errors.len > 0                     # no silent empty-errors sxUnknown
    var sawCap = false
    for e in r.errors:
      if e.kind == geInstantiationCapped:
        sawCap = true
        check e.severity == sevError
    check sawCap

  test "default high cap: a few instantiations work, no false-positive cap":
    let r = symexFind(fewInsts, tLabel("found"))
    check r.status == sxSat
    for e in r.errors:
      check e.kind != geInstantiationCapped
