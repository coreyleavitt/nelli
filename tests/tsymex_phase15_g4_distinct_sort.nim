## Phase 15 — Cluster G, cycle G4: `distinct T` as a fresh uninterpreted Z3 sort.
##
## LOCKED DECISION (RFC-phase15-reconciliation.md §F Cluster G + ADR-0008 D4):
## a `distinct T` type maps to a NEW uninterpreted Z3 sort (a type wall between
## the distinct type and its base). Two uninterpreted functions per distinct
## type model the round-trip — `inject_T: Base→Distinct` and `eject_T:
## Distinct→Base`. The round-trip is modelled, for the DECIDABLE base fragment
## `{int, BV, bool}`, as a GROUND per-occurrence pin `eject(dConst) == baseSym`
## (NOT a universal quantifier: a `∀x. eject(inject(x))==x` axiom — and even a
## ground reverse `inject(baseSym)==dConst` — make Z3 NON-TERMINATE on the
## uninterpreted-function-over-BV combination; verified under the bounded
## runner). For `{float32, float64, string}` the round-trip is SKIPPED entirely
## and a `geDistinctBijectivitySkipped` (sevHint) is emitted instead.
##
## The distinct sort cache lives on `WalkerStatics.distinctSorts` (per-walker,
## shared across frames); the live populator is a per-run threadvar that
## `allocateSym` reads (`allocateSym` has no `WalkCtx` access, mirroring E8's
## in-flight-exn threadvar mechanism).
##
## G4 is ADDITIVE under walker version "7" (no bump; Cluster G bumps at G10).
import std/unittest
import proptest/symex
import proptest/smt/[dsl, runtime]

# --- 1. distinct float64 (FP base → bijectivity SKIPPED) --------------------
# `Meters = distinct float64`: a fresh "Meters" sort, NOT the float64 sort.
# The base is FP, so bijectivity is skipped and a geDistinctBijectivitySkipped
# hint is emitted (sevHint). The target is reachable (the body ejects to the
# base float and compares it).
type Meters = distinct float64

proc useMeters(m: Meters): bool =
  if float64(m) > 1.5:
    symexTarget("meters_reached")
  result = true

# --- 2. distinct int (decidable base → bijectivity ASSERTED, NO HANG) -------
# `UserId = distinct int`: bijectivity axioms are asserted over the int base.
# The query MUST be decidable (sxSat/sxUnsat, NOT sxUnknown-from-hang) and
# complete fast under the bounded runner.
type UserId = distinct int

proc useUserId(u: UserId): bool =
  if int(u) == 42:
    symexTarget("userid_reached")
  result = true

# --- 3. nested distinct (two sorts allocated) ------------------------------
type KiloMeters = distinct Meters

proc useKilo(k: KiloMeters): bool =
  if float64(Meters(k)) > 3.0:
    symexTarget("kilo_reached")
  result = true

suite "symex Phase 15 G4 — distinct T as a fresh uninterpreted Z3 sort":
  test "G4: distinct-FP base reaches target; bijectivity SKIPPED hint emitted":
    let r = symexFind(useMeters, tLabel("meters_reached"))
    check r.status == sxSat
    # FP base → geDistinctBijectivitySkipped (sevHint), result still sxSat.
    var sawSkip = false
    for e in r.errors:
      if e.kind == geDistinctBijectivitySkipped:
        check e.severity == sevHint
        sawSkip = true
    check sawSkip

  test "G4: distinct-INT base round-trip pinned, query decidable (no hang)":
    let r = symexFind(useUserId, tLabel("userid_reached"))
    # Decidable: a concrete sat (NOT sxUnknown from a quantifier hang, NOT a
    # 180s engine HANG). The ground eject-pin keeps the query in QF_UFBV.
    check r.status == sxSat
    # int base → round-trip pinned (no skip), so NO skip hint for this run.
    for e in r.errors:
      check e.kind != geDistinctBijectivitySkipped

  test "G4: distinct-FP witness is non-empty (eject-reader chain)":
    let r = symexFind(useMeters, tLabel("meters_reached"))
    check r.status == sxSat
    # The witness renders through the eject-then-base-reader chain: the
    # Meters param's base float is > 1.5 (Breadth-CRIT-1: a distinct param
    # must not produce a silent empty reader).
    check float64(r.witness[0]) > 1.5

  test "G4: nested distinct allocates two sorts, target reachable":
    let r = symexFind(useKilo, tLabel("kilo_reached"))
    check r.status == sxSat
