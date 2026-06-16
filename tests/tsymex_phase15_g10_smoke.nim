## Phase 15 — Cluster G, cycle G10: hermetic G-cluster regression smoke + walker
## version bump "7"→"8" (CLOSES Cluster G).
##
## A single in-process test file that exercises the FULL generics machinery
## (G1a–G8) TOGETHER, to catch state-threading bugs introduced by the multi-file
## G1a–G8 edits to the parse-time monomorphization path (`ensureProcRegistered`
## + `instKeyFor` + `gatherTypeSubst` + `monomorphize`, the per-walker
## `WalkerStatics.distinctSorts` cache, the `ProcSig.conceptConstraints`
## metadata, and the `maxInstantiationsPerProc` cap). It composes, in one file:
##   - a MULTI-PARAM generic at mixed types (G8): `foo[T, U]` at int+string, T/U
##     resolving independently (not conflated).
##   - the SAME generic instantiated at TWO different types in one SUT (G1a
##     collision fix): `szof[T] = sizeof(T)` at int8 + int64, whose per-T
##     constant DIFFERS, so a bare-name collision would mis-dispatch.
##   - a `distinct T` (G4) with a BORROWED operator (G5): `Meters = distinct
##     float64` with a borrowed `+`, threading the base op + re-boxing.
##   - a `static[int]` param generic at TWO values (G7): `array[N, int]` at N=3
##     and N=5 dispatching to distinct bodies (x[2] vs x[4]).
##   - a concept-constrained generic at a CONFORMING type (G6): `T: SomeNumber`
##     at `T = int`, the constraint resolving as metadata.
##   - the instantiation CAP (G1c): one generic at 3 distinct types under
##     `maxInstantiationsPerProc = 2` → `geInstantiationCapped` → sxUnknown.
##   - the walker version pin: `symexWalkerVersion == "8"` (this cycle's bump).
import std/unittest
import proptest/symex
import proptest/smt/dsl   ## re-exports dsl_parser (conformsToStdlibConcept)

# === SUTs ====================================================================

# --- G8: multi-param generic at int+string (T/U independent) ----------------
proc g10foo[T, U](a: T, b: U): bool = a > 0 and b == "ok"

proc g10MultiParam(a: int, b: string) =
  # T binds int (a > 0 is integer arithmetic); U binds string (b == "ok" is a
  # Z3 string equality). Conflation would mis-lower one comparison.
  if g10foo(a, b):
    symexTarget("multiparam_hit")

# --- G1a: same generic at TWO types in one SUT (collision fix) --------------
# `sizeof(T)` is the semchecker-baked per-T constant: 1 at int8, 8 at int64.
# A bare-name collision would reuse the int8 sig for the int64 call → szof(b)
# yields 1 → conjunction UNSAT. The G1a instKey keeps them DISTINCT.
proc g10szof[T](x: T): int = sizeof(T)

proc g10TwoInsts(a: int8, b: int64) =
  if g10szof(a) == 1 and g10szof(b) == 8:
    symexTarget("twoinsts_hit")

# --- G4 + G5: distinct float64 with a BORROWED `+` --------------------------
type G10Meters = distinct float64
proc `+`(a, b: G10Meters): G10Meters {.borrow.}
proc `<`(a, b: G10Meters): bool {.borrow.}

proc g10Borrow(m1, m2: G10Meters): bool =
  # `m1 + m2` routes through the borrowed `+`: the base floats are added and
  # the result is re-boxed as a G10Meters (G5), compared via the borrowed `<`
  # against a distinct construction `G10Meters(10.0)` whose base float is the
  # G4 eject-pinned literal. The distinct param's witness renders through the
  # eject-reader.
  if G10Meters(10.0) < m1 + m2:
    symexTarget("borrow_hit")
  result = true

# --- G7: static[int] param generic at TWO values ----------------------------
proc g10lastPos[N: static int](x: array[N, int]): bool = x[N-1] > 0

proc g10StaticTwo(a3: array[3, int], a5: array[5, int]) =
  # N=3 ⇒ x[2]; N=5 ⇒ x[4]. The two static instantiations must dispatch to
  # DISTINCT bodies (the G7 per-instantiation bodyHash key, G1a collision
  # class for static-only generics).
  if g10lastPos(a3) and g10lastPos(a5):
    symexTarget("static_hit")

# --- G6: concept-constrained generic at a CONFORMING type -------------------
proc g10clamp[T: SomeNumber](x: T): bool =
  # `T: SomeNumber` is metadata captured in `ProcSig.conceptConstraints`;
  # at `T = int` (conforming) it monomorphizes like an unconstrained generic.
  if x > T(10):
    symexTarget("concept_hit")
  result = true

proc g10UseConcept(a: int): bool =
  result = g10clamp(a)

# --- G1c: instantiation cap (one generic at 3 distinct types) ---------------
proc g10capSzof[T](x: T): int = sizeof(T)

proc g10ThreeInsts(a: int8, b: int16, c: int32) =
  # Under a cap of 2 the third instantiation (int32) is over-cap → not
  # registered → geInstantiationCapped + sxUnknown (Invariant 3).
  if g10capSzof(a) == 1 and g10capSzof(b) == 2 and g10capSzof(c) == 4:
    symexTarget("cap_hit")

const g10LowCap = withSymexSettings() do (s: var SymexSettings):
  s.maxInstantiationsPerProc = 2

suite "symex Phase 15 G10 — Cluster-G regression smoke + walker version 8":

  # ---- G8: multi-param at mixed types ----
  test "G10: multi-param generic at int+string resolves T/U independently":
    let r = symexFind(g10MultiParam, tLabel("multiparam_hit"))
    check r.status == sxSat
    check r.witness[0] > 0
    check r.witness[1] == "ok"

  # ---- G1a: same generic at two types, one SUT ----
  test "G10: same generic at two types both dispatch (szof@int8 + szof@int64)":
    let r = symexFind(g10TwoInsts, tLabel("twoinsts_hit"))
    check r.status == sxSat

  # ---- G4 + G5: distinct + borrowed operator ----
  test "G10: distinct float64 with borrowed `+` threads base op; reachable":
    let r = symexFind(g10Borrow, tLabel("borrow_hit"))
    check r.status == sxSat
    let s = float64(r.witness[0]) + float64(r.witness[1])
    check s > 10.0

  # ---- G7: static[int] at two values ----
  test "G10: static[int] generic at two values dispatches to distinct bodies":
    let r = symexFind(g10StaticTwo, tLabel("static_hit"))
    check r.status == sxSat
    check r.witness[0][2] > 0    ## a3[N-1] = a3[2] (N=3)
    check r.witness[1][4] > 0    ## a5[N-1] = a5[4] (N=5)

  # ---- G6: concept-constrained at a conforming type ----
  test "G10: concept-constrained generic at conforming type reaches target":
    let r = symexFind(g10UseConcept, tLabel("concept_hit"))
    check r.status == sxSat
    check r.witness[0] > 10
    # The G6 membership helper still classifies a non-conforming pair (no
    # silent accept) — composed here to confirm the table survived the edits.
    check conformsToStdlibConcept("SomeNumber", "string") == false
    check conformsToStdlibConcept("SomeNumber", "int") == true

  # ---- G1c: instantiation cap ----
  test "G10: exceeding the per-proc cap → sxUnknown + geInstantiationCapped":
    let r = symexFind(g10ThreeInsts, tLabel("cap_hit"), g10LowCap)
    check r.status == sxUnknown
    check r.errors.len > 0                     # no silent empty-errors sxUnknown
    var sawCap = false
    for e in r.errors:
      if e.kind == geInstantiationCapped:
        check e.severity == sevError
        sawCap = true
    check sawCap

  # ---- walker version pin (advanced to 9 at Cluster-C close-out C6) ----
  test "G10: walker version is \"9\" (G10 bumped 7->8; Cluster-C close-out C6 8->9)":
    check symexWalkerVersion == "9"
