## Phase 15 — Cluster G, cycle G5: `distinct` borrow semantics.
##
## LOCKED DECISION (RFC-phase15-reconciliation.md §F Cluster G + RFC §G5 + the
## G4 HANG finding): a `{.borrow.}` proc on a `distinct T` threads the operation
## through the BASE type's operator. Crucially, G4 found that a Z3 `inject`
## FUNCTION application chain (`inject_T(eject_T(a) + eject_T(b))`) HANGS (the
## uninterpreted-fn-over-BV / MBQI combination). So G5 does NOT model the borrow
## that way. Instead it operates at the SymVal level on the carried BASE value:
## G4's `svDistinct` boxes the base SymVal (`distinctBaseSym`), so the borrow
## takes `m1.distinctBaseSym` and `m2.distinctBaseSym` (via `ejectBase`), applies
## the BASE operator (float `+`/`<` via arithFloat/cmpFloat), and:
##   - arithmetic (`+ - * /`, returning the distinct type) → RE-BOXES the base
##     result as a fresh `svDistinct` with the same distinctName;
##   - comparison (`< <= > >= == !=`, returning bool) → returns the raw svBool.
## This avoids the hanging Z3 inject function entirely and is sound (the G4
## eject-pin ties each dConst to its base).
##
## A NON-borrowed proc on a distinct type called WITHOUT a parseable body (e.g.
## an `{.importc.}` magic) → `geDistinctBarrier` (sxUnknown), NOT a silent
## fallback (Invariant 3).
##
## G5 is ADDITIVE under walker version "7" (no bump; Cluster G bumps at G10).
import std/unittest
import proptest/symex
import proptest/smt/[dsl, runtime]

# --- distinct float64 with borrowed `+` and `<` ----------------------------
type Meters = distinct float64

proc `+`(a, b: Meters): Meters {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

proc useBorrowAdd(m1, m2: Meters): bool =
  # `m1 + m2` routes through the borrowed `+`: the base floats are added and
  # the result is re-boxed as a `Meters`. `Meters(10.0)` is a distinct
  # construction (lowers to its base float literal 10.0). No explicit lifts at
  # the call site.
  if m1 + m2 > Meters(10.0):
    symexTarget("borrow_add_reached")
  result = true

proc useBorrowLt(m1, m2: Meters): bool =
  # `m1 < m2` routes through the borrowed `<`: a base float comparison
  # returning a raw Z3 bool.
  if m1 < m2:
    symexTarget("borrow_lt_reached")
  result = true

# --- non-borrowed proc on a distinct type with NO parseable body -----------
# An `{.importc.}` magic taking a distinct param compiles, has an empty body,
# and is NOT a borrow shim → the type wall forbids silently walking it.
proc magicScale(a: Meters): bool {.importc: "magic_scale".}

proc useDistinctBarrier(m1: Meters): bool =
  if magicScale(m1):
    symexTarget("barrier_reached")
  result = true

suite "symex Phase 15 G5 — distinct borrow semantics":
  test "G5: borrowed `+` threads arithmetic through base; target reachable":
    let r = symexFind(useBorrowAdd, tLabel("borrow_add_reached"))
    check r.status == sxSat
    # Witness: m1, m2 as Meters whose base sum exceeds 10.0 (the eject-reader
    # chain renders each through its base float).
    let s = float64(r.witness[0]) + float64(r.witness[1])
    check s > 10.0

  test "G5: borrowed `<` produces a correct Z3 bool; target reachable":
    let r = symexFind(useBorrowLt, tLabel("borrow_lt_reached"))
    check r.status == sxSat
    check float64(r.witness[0]) < float64(r.witness[1])

  test "G5: non-borrowed bodyless distinct op → geDistinctBarrier (sxUnknown)":
    let r = symexFind(useDistinctBarrier, tLabel("barrier_reached"))
    check r.status == sxUnknown
    var sawBarrier = false
    for e in r.errors:
      if e.kind == geDistinctBarrier:
        check e.severity == sevError
        sawBarrier = true
    check sawBarrier
