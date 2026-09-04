## Phase 7 — `assertCoveredBy`: the CI primitive that proves a user's
## test function exercises a symex-reachable target on its concrete
## witness. See docs/SYMEX_PLAN.md § Phase 7.
import std/[unittest, strutils]
import nelli/symex
import nelli/int128
import nelli/engine/types

suite "symex Phase 7 — assertCoveredBy":
  test "tracer: passes when testFn (= fn by default) reaches symexTarget":
    proc fn(x: int) =
      if x == 42:
        symexTarget("magic")
    # Default testFn is `fn` itself — the common case.
    assertCoveredBy(fn, tLabel("magic"))

  test "raises with descriptive message when testFn skips the target":
    proc fn(x: int) =
      if x == 42:
        symexTarget("magic")
    proc skip(x: int) = discard  # never reaches the target
    var raised = false
    var msg = ""
    try:
      assertCoveredBy(fn, tLabel("magic"), skip)
    except AssertionDefect as e:
      raised = true
      msg = e.msg
    check raised
    check "magic" in msg

  test "UNSAT (unreachable target) vacuously passes even if testFn ignores it":
    proc fn(x: int) =
      # `x != x` is UNSAT — Z3 proves no input reaches the target.
      if x != x:
        symexTarget("ghost")
    proc skip(x: int) = discard
    assertCoveredBy(fn, tLabel("ghost"), skip)

  test "UNKNOWN raises by default; settings flag downgrades to soft pass":
    # Loop needs > maxLoopUnwind iterations to reach the target, so
    # the surviving path is marked uncertain → sxUnknown.
    proc fn(x: int) =
      var i = 0
      while i < x:
        i = i + 1
      if i == 100:
        symexTarget("deep")
    proc noop(x: int) = discard
    var raised = false
    try:
      assertCoveredBy(fn, tLabel("deep"), noop)
    except AssertionDefect:
      raised = true
    check raised

    # Downgrade via settings.
    const lax = SymexSettings(
      integerSemantics: isOptimised,
      budget: ResourceBudget(
        queryRLimit: 5000, maxFrontierSize: 256,
        maxCallDepth: 3, maxLoopUnwind: 5),
      acceptUnknownAsCovered: true)
    assertCoveredBy(fn, tLabel("deep"), noop, lax)

  test "tAssertionViolation: AssertionDefect under testFn satisfies coverage":
    proc fn(x: int) =
      symexAssert(x > 0)
    # Default testFn is fn itself, which raises on the witness.
    assertCoveredBy(fn, tAssertionViolation())

  test "tAssertionViolation: silent testFn fails to cover":
    proc fn(x: int) =
      symexAssert(x > 0)
    proc silent(x: int) = discard
    var raised = false
    try:
      assertCoveredBy(fn, tAssertionViolation(), silent)
    except AssertionDefect as e:
      # Distinguish our message from a stray symexAssert violation.
      raised = "did not raise AssertionDefect" in e.msg
    check raised

  test "tIndexError: IndexDefect under testFn satisfies coverage":
    proc unsafeRead(arr: array[5, int], i: int) =
      let v = arr[i]
      discard v
    assertCoveredBy(unsafeRead, tIndexError())

  test "tIndexError: testFn that clamps the index fails to cover":
    proc unsafeRead(arr: array[5, int], i: int) =
      let v = arr[i]
      discard v
    proc safeRead(arr: array[5, int], i: int) =
      let clamped = (if i < 0: 0 elif i >= 5: 4 else: i)
      let v = arr[clamped]
      discard v
    var raised = false
    try:
      assertCoveredBy(unsafeRead, tIndexError(), safeRead)
    except AssertionDefect as e:
      raised = "did not raise IndexDefect" in e.msg
    check raised

  test "multi-target: passes when testFn covers every target":
    proc fn(x: int) =
      if x == 7: symexTarget("seven")
      if x == 7: symexTarget("also-seven")
    assertCoveredBy(fn, [tLabel("seven"), tLabel("also-seven")])

  test "multi-target: reports per-target failures in aggregate":
    proc fn(x: int) =
      if x == 1: symexTarget("a")
      if x == 2: symexTarget("b")
      if x == 3: symexTarget("c")
    # No-op testFn — every target uncovered.
    proc noop(x: int) = discard
    var msg = ""
    try:
      assertCoveredBy(fn, [tLabel("a"), tLabel("b"), tLabel("c")], noop)
    except AssertionDefect as e:
      msg = e.msg
    check "3 of 3" in msg
    check "\"a\"" in msg
    check "\"b\"" in msg
    check "\"c\"" in msg

  test "renderAsChoices: int witness → single ckInteger node":
    let cs = renderAsChoices((42,))
    check cs.len == 1
    check cs[0].kind == ckInteger
    check cs[0].intVal == toInt128(42)

  test "renderAsChoices: (int, bool) witness → two nodes":
    let cs = renderAsChoices((7, true))
    check cs.len == 2
    check cs[0].kind == ckInteger
    check cs[1].kind == ckBoolean
    check cs[1].boolVal == true

  test "renderAsChoices: seq[int] witness → continue-bool + element":
    # Phase 12 cycle 6 swapped the collection encoding from a
    # length-prefix integer to a per-element `bool(true)` continue
    # marker terminated by `bool(false)`, matching the `lists`
    # strategy's replay contract (strategy.nim:406-475). For a
    # 3-element seq: 3 × (continue, elem) + 1 stop = 7 nodes.
    let cs = renderAsChoices((@[5, 9, 13],))
    check cs.len == 7
    check cs[0].kind == ckBoolean and cs[0].boolVal == true
    check cs[1].intVal == toInt128(5)
    check cs[2].kind == ckBoolean and cs[2].boolVal == true
    check cs[3].intVal == toInt128(9)
    check cs[4].kind == ckBoolean and cs[4].boolVal == true
    check cs[5].intVal == toInt128(13)
    check cs[6].kind == ckBoolean and cs[6].boolVal == false

  test "renderAsChoices: string witness skips UTF-16 surrogate block":
    # Regression: an earlier draft used `intervals(@[(0, maxCodepoint)])`
    # which intersects the surrogate block `[0xD800, 0xDFFF]` and
    # raises at runtime. Phase 9 cycle 4 surfaced it.
    let cs = renderAsChoices(("alice",))
    check cs.len == 1
    check cs[0].kind == ckString
    check cs[0].strVal == "alice"

  test "renderAsChoices: variant witness — discriminator + active-arm fields":
    # Phase 11 cycle 8. For a Nim variant value, the choice
    # sequence must encode the discriminator first, then the
    # arm-specific fields in declaration order. Inactive arms'
    # fields must NOT appear (they have no defined runtime
    # value — accessing them raises FieldDefect).
    type
      ShapeKind = enum skCircle, skSquare
      Shape = object
        case kind: ShapeKind
        of skCircle: radius: int
        of skSquare: side: int
    let circle = Shape(kind: skCircle, radius: 42)
    let cs1 = renderAsChoices((circle,))
    check cs1.len == 2
    check cs1[0].kind == ckInteger     # discriminator
    check cs1[0].intVal == toInt128(ord(skCircle))
    check cs1[1].kind == ckInteger     # radius
    check cs1[1].intVal == toInt128(42)

    let square = Shape(kind: skSquare, side: 7)
    let cs2 = renderAsChoices((square,))
    check cs2.len == 2
    check cs2[0].intVal == toInt128(ord(skSquare))
    check cs2[1].intVal == toInt128(7)

  test "successful assertCoveredBy records a covered SymexFinding":
    discard consumeSymexFindings()  # clear any prior findings
    proc fn(x: int) =
      if x == 42:
        symexTarget("magic")
    assertCoveredBy(fn, tLabel("magic"))
    let findings = consumeSymexFindings()
    check findings.len == 1
    check findings[0].status == sfSat
    check findings[0].covered
    check findings[0].targetDesc == "label(\"magic\")"
    check findings[0].witnessChoices.len == 1
    check findings[0].witnessChoices[0].intVal == toInt128(42)
    check findings[0].z3Version.len > 0

  test "uncovered assertCoveredBy records a finding before raising":
    discard consumeSymexFindings()
    proc fn(x: int) =
      if x == 42: symexTarget("missed")
    proc skip(x: int) = discard
    try:
      assertCoveredBy(fn, tLabel("missed"), skip)
    except AssertionDefect:
      discard
    let findings = consumeSymexFindings()
    check findings.len == 1
    check findings[0].status == sfSat
    check not findings[0].covered

  test "UNSAT records a vacuous (covered) finding":
    discard consumeSymexFindings()
    proc fn(x: int) =
      if x != x: symexTarget("ghost")
    assertCoveredBy(fn, tLabel("ghost"))
    let findings = consumeSymexFindings()
    check findings.len == 1
    check findings[0].status == sfUnsat
    check findings[0].covered
    check findings[0].witnessChoices.len == 0

  test "Report[T].symexFindings preserves findings when set":
    var r: Report[int]
    r.symexFindings.add SymexFinding(
      targetDesc: "label(\"x\")", status: sfSat, covered: true,
      z3Version: "test")
    check r.symexFindings.len == 1
    check r.symexFindings[0].covered

  test "DB round-trip: same SUT/target/settings load, distinct SUT does not":
    proc fnA(x: int) =
      if x == 99: symexTarget("db")
    proc fnB(x: int) =
      if x == 100: symexTarget("db")  # different SUT — different cache key
    let db = inMemoryDatabase()
    let f = SymexFinding(
      targetDesc: "label(\"db\")", status: sfSat, covered: true,
      witnessChoices: @[integerChoice(99'i64, low(int64), high(int64), 0'i64)],
      z3Version: z3FullVersion())
    saveSymexWitness(db, fnA, tLabel("db"), defaultSymexSettings(), f)
    let same = loadSymexWitnesses(db, fnA, tLabel("db"), defaultSymexSettings())
    check same.len == 1
    check same[0][0].intVal == toInt128(99)
    # Distinct SUT — content-addressed key differs, nothing visible.
    let mismatched = loadSymexWitnesses(db, fnB, tLabel("db"),
      defaultSymexSettings())
    check mismatched.len == 0

  test "saveSymexWitness ignores UNSAT/UNKNOWN findings":
    proc fnC(x: int) =
      if x == 0: symexTarget("never")
    let db = inMemoryDatabase()
    saveSymexWitness(db, fnC, tLabel("never"), defaultSymexSettings(),
      SymexFinding(status: sfUnsat, z3Version: z3FullVersion()))
    saveSymexWitness(db, fnC, tLabel("never"), defaultSymexSettings(),
      SymexFinding(status: sfUnknown, z3Version: z3FullVersion()))
    check loadSymexWitnesses(db, fnC, tLabel("never"),
      defaultSymexSettings()).len == 0

  test "SymexFinding.discoveredBy carries through Report.symexFindings":
    var r: Report[int]
    var f = SymexFinding(targetDesc: "label(\"x\")",
                         status: sfSat, covered: true,
                         z3Version: "test")
    f.discoveredBy.add "myPropertyTest_A"
    f.discoveredBy.add "myPropertyTest_B"
    r.symexFindings.add f
    check r.symexFindings.len == 1
    check r.symexFindings[0].discoveredBy == @["myPropertyTest_A",
                                                "myPropertyTest_B"]
