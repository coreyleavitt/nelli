## Phase 12 cycle 7 — `symexFindAllWitnesses` tLabel tracer.
##
## Layer 1 primitive: at macro time, scan the SUT's IR (transitively
## through `parseProc`'s callee table) for `symexTarget("name")`
## markers; at runtime, run symex once per discovered target and
## return one `SymexFinding` per. Each finding is also deposited via
## `recordSymexFinding` so the engine's `finalizePhase` later drains
## them into `Report.symexFindings`.
##
## Cycles 8-10 will auto-include defect targets
## (tAssertionViolation / tIndexError / tFieldDefect); cycle 11
## adds `excludeTargets`; cycle 12 wires DB cache. Cycle 7 covers
## labels only.
import std/unittest
import proptest/symex
import proptest/db
import proptest/engine/types

# SUT must live at module scope so its symbol survives `getImpl`
# inspection by the macro.
proc fnTwoLabels(x: int) =
  if x == 0:
    symexTarget("zero")
  elif x == 7:
    symexTarget("magic")

proc fnAssertable(x: int) =
  # `symexAssert(cond)` lowers to an `isAssert` IR node. Cycle 8 of
  # auto-discovery must surface this as a `tAssertionViolation`
  # target without the user listing it explicitly.
  symexAssert(x != 7)

proc fnIndexable(arr: array[5, int], i: int) =
  # `arr[i]` lowers to an `isIndex` IR node. Cycle 9 must surface
  # this as a `tIndexError` auto-discovered target.
  let v = arr[i]
  discard v

type
  ShapeKind10 = enum skCircle10, skSquare10
  Shape10 = object
    case kind: ShapeKind10
    of skCircle10: radius: int
    of skSquare10: side: int

proc fnVariantField(s: Shape10) =
  # Unconditional read of an arm-specific field. Lowers to an
  # `isVariantField` IR node, which cycle 10 must surface as a
  # `tFieldDefect` auto-discovered target.
  let r = s.radius
  discard r

proc fnIndexAndAssert(arr: array[3, int], i: int) =
  # Two auto-discovered targets at once: an indexing op (lowers
  # to `isIndex`) and a symexAssert (lowers to `isAssert`). Cycle
  # 11 lets the caller suppress one via excludeTargets while the
  # other still surfaces.
  let v = arr[i]
  symexAssert(v != 999)

proc fnNoTargets(x: int) =
  # No `symexTarget`, no `symexAssert`, no `arr[i]`, no variant
  # arm-field reads — nothing for the IR scan to surface. The
  # zero-targets fallback must still produce one audit entry.
  discard x

proc fnVarParam(x: var int) =
  # Macro must reject this at compile time — there's no witness
  # reconstruction story for `var T` and the walker treats them as
  # opaque mutable cells.
  if x == 0:
    symexTarget("zero")

suite "symex Phase 12 cycle 7 — symexFindAllWitnesses (labels)":
  test "returns one SymexFinding per discovered label, all sfSat":
    discard consumeSymexFindings()  # clear sink from any prior test
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(fnTwoLabels, db)
    check findings.len == 2
    for f in findings:
      check f.status == sfSat
      check f.witnessChoices.len > 0
    let descs = @[findings[0].targetDesc, findings[1].targetDesc]
    check "label(\"zero\")" in descs
    check "label(\"magic\")" in descs

  test "findings flow into the per-thread sink for finalizePhase":
    # `recordSymexFinding` deposits to a threadvar that
    # `consumeSymexFindings()` drains. The macro must record every
    # finding it returns so the engine's finalize step picks them
    # up at end-of-run regardless of whether the user inspects the
    # return value.
    discard consumeSymexFindings()  # clear sink
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(fnTwoLabels, db)
    let drained = consumeSymexFindings()
    check drained.len == findings.len
    # Drained findings carry the same targetDescs (order-preserving).
    for i in 0 ..< findings.len:
      check drained[i].targetDesc == findings[i].targetDesc

  test "rejects a non-proc first argument at macro time":
    # The macro inspects `fn.getImpl` and demands `nnkProcDef`. A
    # value (here: an int variable) is rejected before any runtime
    # code is emitted.
    check not compiles(symexFindAllWitnesses(42, inMemoryDatabase()))

  test "accepts a fn with a `var T` parameter (Phase 14 A7b)":
    # Phase 14 A7b lifted Phase 12's `var T` guard. Witness
    # semantics: the walker reports the INITIAL value of each
    # `var` param via `initialEnv`. The downstream test runtime
    # (assertCoveredBy, splat) wraps each param in a fresh `var`
    # local so the SUT call sees an addressable lvalue.
    check compiles(symexFindAllWitnesses(fnVarParam, inMemoryDatabase()))

  test "auto-includes tAssertionViolation when SUT contains symexAssert":
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(fnAssertable, db)
    var descs: seq[string]
    for f in findings: descs.add f.targetDesc
    check "assertion-violation" in descs
    # And the corresponding finding is sfSat (Z3 can solve x != 7
    # with x = 7 → violation witness).
    for f in findings:
      if f.targetDesc == "assertion-violation":
        check f.status == sfSat
        check f.witnessChoices.len > 0

  test "auto-includes tIndexError when SUT contains an indexing op":
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(fnIndexable, db)
    var descs: seq[string]
    for f in findings: descs.add f.targetDesc
    check "index-error" in descs
    for f in findings:
      if f.targetDesc == "index-error":
        check f.status == sfSat
        check f.witnessChoices.len > 0

  test "auto-includes tFieldDefect when SUT contains an arm-field read":
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(fnVariantField, db)
    var descs: seq[string]
    for f in findings: descs.add f.targetDesc
    check "field-defect" in descs
    for f in findings:
      if f.targetDesc == "field-defect":
        check f.status == sfSat
        check f.witnessChoices.len > 0

  test "excludeTargets suppresses an auto-discovered kind":
    # `fnIndexAndAssert` triggers BOTH `tIndexError` (from `arr[i]`)
    # and `tAssertionViolation` (from `symexAssert`). With
    # `excludeTargets = [tIndexError()]` the assertion still
    # surfaces but the index-error does not.
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(
      fnIndexAndAssert, db,
      excludeTargets = @[tIndexError()])
    var descs: seq[string]
    for f in findings: descs.add f.targetDesc
    check "assertion-violation" in descs
    check "index-error" notin descs

  test "DB cache: pre-seeded witness is returned without re-running symex":
    # Pre-seed the DB with a distinctive witness for tLabel("zero")
    # that `runSymex` would never freshly produce (the SUT branch
    # is `if x == 0`; Z3's natural witness is x = 0, never 1234567).
    # If the macro consults the DB first, the returned finding's
    # witnessChoices match the pre-seed; if it ignored the cache
    # and ran symex fresh, the choices would carry x = 0.
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let preseed = renderAsChoices((1234567,))
    saveSymexWitness(db, fnTwoLabels, tLabel("zero"),
                     defaultSymexSettings(),
                     SymexFinding(targetDesc: "label(\"zero\")",
                                  status: sfSat,
                                  witnessChoices: preseed,
                                  z3Version: z3FullVersion()))
    let findings = symexFindAllWitnesses(fnTwoLabels, db)
    var saw = false
    for f in findings:
      if f.targetDesc == "label(\"zero\")":
        saw = true
        check f.witnessChoices == preseed
        check f.status == sfSat
    check saw

  test "zero-targets fallback: single sfNotApplicable audit entry":
    discard consumeSymexFindings()
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(fnNoTargets, db)
    check findings.len == 1
    check findings[0].status == sfNotApplicable
    check findings[0].targetDesc == "no-targets-discovered"
    # The finding also flowed into the sink so the engine's
    # finalize-time drain picks it up.
    let drained = consumeSymexFindings()
    check drained.len == 1
    check drained[0].status == sfNotApplicable
