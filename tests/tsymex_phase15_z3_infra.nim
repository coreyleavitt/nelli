import std/unittest
import std/sequtils
import proptest/smt/runtime
import proptest/smt/types

# Phase 15 — Z3 cross-cutting infrastructure (staged; see
# docs/symex/RFC-phase15-reconciliation.md §F / Cluster Z).
# This slice (Z3a): the enum/type scaffolding — SymexErrorKind/Severity,
# DefectKind, InlinePolicy, the SymexErrorInfo migration, and the new
# SymexSettings fields. (svUninterpRef/itUninterp, classifyType, cacheKeyRaised,
# withSymexSettings, and SYMEX_PLAN.md land in later Z3 sub-slices.)

# Invariant-7 checker (test helper, not production): an sxUnknown result must
# carry at least one sevError entry.
proc checkInvariant7(r: RawResult): bool =
  if r.status == sxUnknown:
    r.errors.anyIt(it.severity == sevError)
  else:
    true

suite "symex Phase 15 — Z3 infrastructure":

  test "z3 infra: SymexErrorInfo.kind is SymexErrorKind, severity is SymexErrorSeverity":
    static:
      let e = SymexErrorInfo(kind: feUnsupportedOp, severity: sevError, msg: "t")
      doAssert typeof(e.kind) is SymexErrorKind
      doAssert typeof(e.severity) is SymexErrorSeverity
    let e = SymexErrorInfo(kind: feUnsupportedOp, severity: sevError, msg: "test")
    check e.kind == feUnsupportedOp
    check e.severity == sevError

  test "z3 infra: invariant 7 — sxUnknown implies a sevError entry":
    let viol = RawResult(status: sxUnknown,
      errors: @[SymexErrorInfo(kind: feUnsupportedOp, severity: sevHint, msg: "")])
    check checkInvariant7(viol) == false
    let ok = RawResult(status: sxUnknown,
      errors: @[SymexErrorInfo(kind: feUnsupportedOp, severity: sevError, msg: "")])
    check checkInvariant7(ok) == true

  test "z3 infra: SymexErrorKind ordinals — Phase-15 kinds follow Phase-14 kinds":
    check ord(feUnsupportedOp) > ord(ekZ3SolverError)
    check $heDepthExhausted == "heDepthExhausted"
    check $ekZ3MemoryError == "ekZ3MemoryError"

  test "z3 infra: SymexSettings defaults — defectExclusions + inlinePolicy":
    let s = defaultSymexSettings()
    check s.defectExclusions == {dkOutOfMemoryDefect, dkStackOverflowDefect}
    check s.inlinePolicy == ipHybrid

  test "z3 infra: InlinePolicy resolves unqualified from types":
    check ipHybrid != ipAlwaysInline
    check ord(ipAlwaysInline) == 0

  # ---- Z3b: svUninterpRef + itUninterp/tUninterp -------------------------

  test "z3b: svUninterpRef is an SVKind variant carrying sort/type names":
    let sv = SymVal(kind: svUninterpRef,
                    sortName: "ExnRef_ValueError", typeTag: "ValueError")
    check sv.kind == svUninterpRef
    check sv.sortName == "ExnRef_ValueError"
    check sv.typeTag == "ValueError"

  test "z3b: tUninterp / itUninterp — constructor, render, equality":
    let a = tUninterp("ExnRef_X")
    check a.kind == itUninterp
    check a.uninterpName == "ExnRef_X"
    check $a == "uninterp[ExnRef_X]"
    check a == tUninterp("ExnRef_X")
    check a != tUninterp("ExnRef_Y")
