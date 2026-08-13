import std/unittest
import std/sequtils
import nelli/smt/runtime
import nelli/smt/types
import nelli/smt/canonicalize

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

  # ---- Z3d: withSymexSettings builder + `+` merge ------------------------

  test "z3d: withSymexSettings overrides chosen fields, rest are defaults":
    let s = withSymexSettings() do (s: var SymexSettings):
      s.budget.maxFrontierSize = 1
      s.defectExclusions = {}
    let d = defaultSymexSettings()
    check s.budget.maxFrontierSize == 1
    check s.defectExclusions == {}
    check s.budget.maxCallDepth == d.budget.maxCallDepth
    check s.integerSemantics == d.integerSemantics
    check s.inlinePolicy == d.inlinePolicy

  test "z3d: `+` takes b's non-default fields, keeps a's elsewhere":
    let a = withSymexSettings() do (s: var SymexSettings):
      s.budget.maxCallDepth = 10
    let b = withSymexSettings() do (s: var SymexSettings):
      s.budget.maxFrontierSize = 5
    let m = a + b
    check m.budget.maxCallDepth == 10      # a's override (b has default here)
    check m.budget.maxFrontierSize == 5    # b's non-default override
    check m.budget.maxLoopUnwind == defaultSymexSettings().budget.maxLoopUnwind

  # ---- Z3e: cacheKeyRaised + standardized suffixes -----------------------

  test "z3e: cacheKeyRaised builds a per-type :raised key":
    check cacheKeyRaised("ValueError") == ":raised:ValueError"
    check cacheKeyRaised("IOError") == ":raised:IOError"

  test "z3e: suffix constants standardized to full English words":
    check cacheKeySat == ":sat"
    check cacheKeyUnsat == ":unsat"
    check cacheKeyUnknown == ":unknown"
