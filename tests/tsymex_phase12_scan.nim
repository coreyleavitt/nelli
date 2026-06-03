## Phase 12 cycle 4 — IR scan helpers with transitive `isCall`
## traversal.
##
## Auto-discovery in Layer 1 needs to know which symex targets are
## reachable from the SUT. The four target-relevant IR primitives:
##
##   tLabel("name")          ← isTargetLabel
##   tAssertionViolation()   ← isAssert
##   tIndexError()           ← isIndex
##   tFieldDefect()          ← isVariantField
##
## Each scanner walks the SUT's body AND descends into callee
## bodies via `procs[calleeName].body` on encountering `isCall`.
## Bounded by what `parseProc` actually placed in the procs map
## (cross-module / unsupported callees stop there).
import std/[unittest, tables]
import proptest/smt/types
import proptest/smt/scan

suite "symex Phase 12 cycle 4 — IR scan helpers":
  test "irCollectLabels finds a marker directly in the body":
    let body = mkBlock(@[mkTargetLabel("hit")])
    let procs = initTable[string, ProcSig]()
    check irCollectLabels(body, procs) == @["hit"]

  test "irCollectLabels finds a marker inside a callee body via isCall":
    # SUT body: just a call to `helper`. Marker lives in helper's
    # body. Transitive scan must descend into procs["helper"].body.
    let helperBody = mkBlock(@[mkTargetLabel("inside-helper")])
    let helperSig = ProcSig(name: "helper", body: helperBody,
                             retTy: tBool(), isVoid: true)
    var procs = initTable[string, ProcSig]()
    procs["helper"] = helperSig
    let topBody = mkBlock(@[mkCall("helper", "", @[], tBool())])
    check irCollectLabels(topBody, procs) == @["inside-helper"]

  test "irHasAssert / irHasIndex / irHasVariantField — top-level":
    let bAssert = mkBlock(@[IRStmt(kind: isAssert, acond: mkBoolLit(true))])
    let bIndex  = mkBlock(@[mkIndexStmt("r", mkVar("arr"), mkVar("i"),
                                         tInt(64, true))])
    let bVField = mkBlock(@[mkVariantFieldStmt(
      "r", mkVar("o"), "f", tInt(64, true), @[0])])
    let procs = initTable[string, ProcSig]()
    check irHasAssert(bAssert, procs)
    check not irHasAssert(bIndex, procs)
    check irHasIndex(bIndex, procs)
    check not irHasIndex(bVField, procs)
    check irHasVariantField(bVField, procs)
    check not irHasVariantField(bAssert, procs)

  test "irHasAssert finds an assert inside a callee body":
    let helperBody = mkBlock(@[IRStmt(kind: isAssert, acond: mkBoolLit(true))])
    var procs = initTable[string, ProcSig]()
    procs["helper"] = ProcSig(name: "helper", body: helperBody,
                              retTy: tBool(), isVoid: true)
    let topBody = mkBlock(@[mkCall("helper", "", @[], tBool())])
    check irHasAssert(topBody, procs)

  test "cyclic calls don't infinite-loop":
    # f() calls g(); g() calls f(). Both bodies have a marker.
    # The scan must terminate (visited-set guard) and find labels
    # from both arms.
    let fBody = mkBlock(@[mkTargetLabel("in-f"),
                           mkCall("g", "", @[], tBool())])
    let gBody = mkBlock(@[mkTargetLabel("in-g"),
                           mkCall("f", "", @[], tBool())])
    var procs = initTable[string, ProcSig]()
    procs["f"] = ProcSig(name: "f", body: fBody,
                         retTy: tBool(), isVoid: true)
    procs["g"] = ProcSig(name: "g", body: gBody,
                         retTy: tBool(), isVoid: true)
    let top = mkBlock(@[mkCall("f", "", @[], tBool())])
    let labels = irCollectLabels(top, procs)
    check "in-f" in labels
    check "in-g" in labels

  test "missing-callee in procs map is a no-op (cross-module limit)":
    # `parseProc` only populates `procs` for callees it could
    # resolve. A missing entry corresponds to a cross-module
    # private helper or an unsupported callee — the scan stops at
    # the boundary. Phase 3 deferral #138.
    let top = mkBlock(@[mkCall("private-helper", "", @[], tBool())])
    let procs = initTable[string, ProcSig]()
    check irCollectLabels(top, procs).len == 0
    check not irHasAssert(top, procs)
