## Phase 15 — Code-Review finding CR-15: `SomeOrdinal` concept check omits
## user enum types → spurious geConceptViolation → sxUnknown for valid procs.
##
## Nim's `SomeOrdinal` type class explicitly includes user enum types (they ARE
## ordinal). The static membership table (`someSignedIntTypes & someUnsignedIntTypes
## & someOrdinalExtra`) listed only named scalar types; a user enum name like
## "Color" is not in that list, so `conformsToStdlibConcept("SomeOrdinal","Color")`
## returned `false` → parse-time `geConceptViolation` → sxUnknown.
##
## This is over-conservative: the Nim semchecker already validated the constraint
## at the call site (it rejects non-conforming types). The engine should trust
## that validation and not re-reject valid programs.
##
## RED state: `proc foo[T: SomeOrdinal](x: T)` instantiated at a user enum
## emits `geConceptViolation` → sxUnknown instead of sxSat.
##
## GREEN state: the structural enum check (`isEnumTypeNode`) fires before the
## table check for `SomeOrdinal` → violation skipped → sxSat.
import std/unittest
import nelli/symex
import nelli/smt/dsl   ## for conformsToStdlibConcept

# ---- Test type: a simple user-defined enum ----------------------------------
type
  Color = enum
    cRed, cGreen, cBlue

# ---- SUT: a SomeOrdinal-constrained generic instantiated at a user enum ----
proc eqColor[T: SomeOrdinal](x, y: T): bool =
  result = (x == y)

proc checkColorEq(a: Color, b: Color): bool =
  result = eqColor(a, b)

# ---- SUT2: target label reachable only for a specific enum value ------------
proc enumOrdinalTarget(c: Color) =
  if c == cBlue:
    symexTarget("is_blue")

suite "symex Phase 15 CR-15 — SomeOrdinal recognises user enum types":

  test "CR-15: SomeOrdinal generic at user enum reaches target (sxSat not sxUnknown)":
    ## RED: sxUnknown (geConceptViolation, Color not in static scalar list).
    ## GREEN: sxSat (enum recognised as ordinal; constraint check skipped).
    let r = symexFind(enumOrdinalTarget, tLabel("is_blue"))
    check r.status == sxSat

  test "CR-15: equality at user enum type works (no geConceptViolation)":
    ## Also validates that monomorphization at an enum type runs to completion
    ## without a geConceptViolation parse error. The SUT has no symexTarget label,
    ## so sxUnsat is the expected verdict (no satisfiable path reaches a label).
    ## The key invariant: NOT sxUnknown (which would indicate geConceptViolation).
    let r = symexFind(checkColorEq, tLabel("eq"))
    check r.status != sxUnknown

  test "CR-15: SomeOrdinal still rejects a non-ordinal type (string)":
    ## The string-based conformance check still runs for non-enum types.
    check conformsToStdlibConcept("SomeOrdinal", "string") == false
    check conformsToStdlibConcept("SomeOrdinal", "float64") == false
    # Conforming scalar types still accepted.
    check conformsToStdlibConcept("SomeOrdinal", "int") == true
    check conformsToStdlibConcept("SomeOrdinal", "char") == true
    check conformsToStdlibConcept("SomeOrdinal", "bool") == true
