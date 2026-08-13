## Phase 15 — Cluster G, cycle G6: concept constraints / trust boundary.
##
## LOCKED DECISION (RFC-phase15-reconciliation.md §F Cluster G + RFC §G6):
## generic procs already symex via PARSE-TIME monomorphization. There is NO
## `isGenericCall` IR and NO `gcTypeArgs`. The RFC's §G6 GREEN (a walk-time
## `of isGenericCall:` conformance guard reading `gcTypeArgs`) is written
## against that dropped design — RECONCILED here:
##
##   * The concept-conformance check happens at PARSE TIME, on the RESOLVED
##     concrete type (from `gatherTypeSubst`'s binding for the constrained
##     param), NOT in a walker arm.
##   * `ProcSig.conceptConstraints: seq[string]` captures the per-generic-param
##     type-class constraint names (`T: SomeNumber` → "SomeNumber").
##   * For STDLIB concepts (SomeNumber/SomeInteger/SomeFloat/SomeOrdinal/
##     SomeUnsignedInt/SomeSignedInt) the resolved concrete type is validated
##     against a static membership table; a non-conforming binding emits
##     `geConceptViolation` (sevError) via the G1c/G5 `ctx.parseErrors` →
##     sxUnknown plumbing.
##   * For USER-DEFINED concepts validation is SKIPPED — the Nim semchecker
##     already enforced the constraint at the call site (trust boundary).
##
## NEGATIVE-TEST ADAPTATION (no `isGenericCall` node to malform): the RFC's
## "construct a malicious IR node with a non-conforming `gcTypeArgs`" is NOT
## constructible — Nim's semchecker rejects a non-conforming `T` at the call
## site, so such a type NEVER reaches the macro. `geConceptViolation` is thus
## test-injectable only (like `geDistinctBarrier`). We inject through the REAL
## conformance-check entry point: `conformsToStdlibConcept(conceptName,
## resolvedTypeName)` — the exact helper the parse-time validator uses. We call
## it directly with a non-conforming pair (e.g. SomeNumber + "string") and
## assert it returns FALSE (the violation is detected, not silently accepted).
##
## G6 is ADDITIVE under walker version "7" (no bump; Cluster G bumps at G10).
import std/unittest
import nelli/symex
import nelli/smt/dsl   ## re-exports dsl_parser (conformsToStdlibConcept)

# --- POSITIVE: concept-constrained generic at a CONFORMING type ------------
# `T: SomeNumber` instantiated at `T = int` (int conforms). Monomorphizes and
# symexes exactly like an unconstrained generic — the constraint is metadata.
proc clampPos[T: SomeNumber](x: T): bool =
  if x > T(10):
    symexTarget("over_ten")
  result = true

proc useConformingNum(a: int): bool =
  result = clampPos(a)

# --- COMPOUND: a stdlib-elaborated constraint at a conforming type ---------
# `SomeInteger` is itself a compound of the signed/unsigned integer set; the
# semchecker resolves the membership, G6 does no special-casing. Instantiated
# at `int` (conforming).
proc onlyInts[T: SomeInteger](x: T): bool =
  if x == T(42):
    symexTarget("is_42")
  result = true

proc useCompoundInt(a: int): bool =
  result = onlyInts(a)

suite "symex Phase 15 G6 — concept-constraint trust boundary":
  test "G6: concept-constrained generic at conforming type reaches target":
    let r = symexFind(useConformingNum, tLabel("over_ten"))
    check r.status == sxSat
    check r.witness[0] > 10

  test "G6: malformed/non-conforming type at stdlib concept is classified":
    # Negative — adapted: no `isGenericCall` node exists to malform. Inject a
    # non-conforming (concept, resolvedType) pair straight into the real
    # membership helper the parse-time validator calls. A `string` does NOT
    # satisfy `SomeNumber`, so the helper must report the violation (false),
    # NOT silently accept it (Invariant 3).
    check conformsToStdlibConcept("SomeNumber", "string") == false
    check conformsToStdlibConcept("SomeFloat", "int") == false
    check conformsToStdlibConcept("SomeInteger", "float64") == false
    # Conforming pairs return true (the positive direction of the same helper).
    check conformsToStdlibConcept("SomeNumber", "int") == true
    check conformsToStdlibConcept("SomeInteger", "int8") == true
    check conformsToStdlibConcept("SomeFloat", "float64") == true
    # A non-stdlib concept name is NOT in the table → trust-the-semchecker
    # (the validator skips it); the helper signals "not a stdlib concept" by
    # returning true (no violation to assert against a user concept).
    check conformsToStdlibConcept("MyUserConcept", "string") == true

  test "G6: compound-constrained generic works without special-casing":
    let r = symexFind(useCompoundInt, tLabel("is_42"))
    check r.status == sxSat
    check r.witness[0] == 42
