## Phase 15 — Cluster E, cycle E2a: STRUCTURAL `sxRaised` cascade + multi-finding
## cache protocol. PURELY MECHANICAL — `sxRaised` is wired through
## `SymexStatusKind`, the `RawResult` variant, the three exhaustive
## `case raw.status` dispatch sites in `symex.nim`, `cacheKeyRaised` (reused from
## Z3e), `sfRaised` (`SymexFindingStatus`) and `stkRaisedExn` (`SymexTargetKind`).
## The walker's `isRaise` arm emits one `sxRaised` `RawResult` per raise-path
## (STRUCTURAL — NO handler matching, NO propagation, NO witness; those land
## E2b+). `WalkCtx.found: seq[RawResult]` (Z4) and `cacheKeyRaised` (Z3e) already
## existed; E2a consumes them.
import std/[unittest, tables]
import nelli/symex
import nelli/db
import nelli/smt/[types, dsl, runtime]
import nelli/engine/types

# --- a typed SUT containing an unconditional raise --------------------------
proc raiseSut(x: int) =
  raise newException(ValueError, "x")

suite "symex Phase 15 E2a — structural sxRaised cascade + multi-finding cache":
  test "E2a: sxRaised is structurally wired; toFindingStatus maps it to sfRaised":
    # The cascade compiles (no exhaustiveness panic) and the status mapping
    # is in place. This pins the structural wiring independent of walker
    # semantics.
    check toFindingStatus(sxRaised) == sfRaised

  test "E2a: SUT with raise compiles; structural sxRaised arm fires":
    # `symexFind` returns SymexResult whose `status` is SymexStatusKind. After
    # E2a the structural `isRaise` arm emits sxRaised (was eeRaiseUnimplemented
    # in E1). No witness, no semantics — purely structural.
    let res = symexFind(raiseSut, tAssertionViolation())
    check res.status == sxRaised

  test "E2a: multi-sxRaised DB round-trip — both findings reload without Z3":
    # Mirror the Phase-13 verdict round-trip tests: drive the save/load `*Impl`
    # procs directly on a constructed `seq[RawResult]`. A SUT with two distinct
    # raise paths (ValueError on x<0, IOError on x==0) yields two sxRaised
    # findings. Save persists both under their per-type cache keys; a load with
    # an empty in-memory cache reconstructs BOTH without invoking Z3.
    let db = inMemoryDatabase()
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    let found = @[
      RawResult(status: sxRaised, raisedTypeId: "ValueError"),
      RawResult(status: sxRaised, raisedTypeId: "IOError"),
    ]
    var errors: seq[string] = @[]
    saveSymexRaisedImpl(db, prog, target, defaultSymexSettings(), found, errors)
    check errors.len == 0

    # Fresh load — reconstruct the full seq from the DB (no Z3). RFC-0005
    # S8az: `loadSymexRaisedImpl` now returns `seq[CachedRaised]` (the
    # `RawResult` paired with its stored `gaps`), not a bare `seq[RawResult]`.
    var loadErrors: seq[string] = @[]
    let reloaded = loadSymexRaisedImpl(db, prog, target,
                                       defaultSymexSettings(), loadErrors)
    check reloaded.len == 2
    var typeIds: seq[string]
    for r in reloaded:
      check r.raw.status == sxRaised
      typeIds.add r.raw.raisedTypeId
    check "ValueError" in typeIds
    check "IOError" in typeIds

  test "S1: a torn multi-type save never reads back as a partial set":
    # Whichever save throws, a later load sees the whole set or nothing.
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    let found = @[
      RawResult(status: sxRaised, raisedTypeId: "ValueError"),
      RawResult(status: sxRaised, raisedTypeId: "IOError"),
    ]
    for failAt in 1 .. 4:
      let db0 = inMemoryDatabase()
      var db = db0
      var n = 0
      let inner = db0.saveWithMetaImpl
      let plain = db0.saveImpl
      db.saveWithMetaImpl = proc (t: string; c: seq[ChoiceNode];
                                  m: Table[string, string]; mx: int) =
        inc n
        if n == failAt: raise newException(IOError, "injected")
        inner(t, c, m, mx)
      db.saveImpl = proc (t: string; c: seq[ChoiceNode]; mx: int) =
        inc n
        if n == failAt: raise newException(IOError, "injected")
        plain(t, c, mx)
      var errors: seq[string] = @[]
      saveSymexRaisedImpl(db, prog, target, defaultSymexSettings(), found,
                          errors)
      var loadErrors: seq[string] = @[]
      let got = loadSymexRaisedImpl(db0, prog, target,
                                    defaultSymexSettings(), loadErrors)
      checkpoint "failAt=" & $failAt & " loaded=" & $got.len
      check got.len == 0 or got.len == 2

  test "Q1: a torn re-save never reads back as a mixed old/new set":
    # Old save [A,B] (isDefect=false), then a re-save of the same key
    # (isDefect=true) that throws at each position. Every load is the whole
    # old set, the whole new set, or a miss -- never new A with old B.
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    proc mk(defect: bool): seq[RawResult] =
      @[RawResult(status: sxRaised, raisedTypeId: "ValueError", isDefect: defect),
        RawResult(status: sxRaised, raisedTypeId: "IOError", isDefect: defect)]
    for failAt in 1 .. 5:
      let db0 = inMemoryDatabase()
      var errors0: seq[string] = @[]
      saveSymexRaisedImpl(db0, prog, target, defaultSymexSettings(),
                          mk(false), errors0)
      check errors0.len == 0
      var db = db0
      var n = 0
      let inner = db0.saveWithMetaImpl
      let plain = db0.saveImpl
      db.saveWithMetaImpl = proc (t: string; c: seq[ChoiceNode];
                                  m: Table[string, string]; mx: int) =
        inc n
        if n == failAt: raise newException(IOError, "injected")
        inner(t, c, m, mx)
      db.saveImpl = proc (t: string; c: seq[ChoiceNode]; mx: int) =
        inc n
        if n == failAt: raise newException(IOError, "injected")
        plain(t, c, mx)
      var errors: seq[string] = @[]
      saveSymexRaisedImpl(db, prog, target, defaultSymexSettings(),
                          mk(true), errors)
      var loadErrors: seq[string] = @[]
      let got = loadSymexRaisedImpl(db0, prog, target,
                                    defaultSymexSettings(), loadErrors)
      checkpoint "failAt=" & $failAt & " loaded=" & $got.len
      if got.len > 0:
        check got.len == 2
        check got[0].raw.isDefect == got[1].raw.isDefect

  test "K4: re-saving a type with a different witness replaces the slot":
    # The db dedups by witness, so a sentinel saved with a roomy cap grew a
    # second entry and the loader (exactly one entry) missed forever.
    let db = inMemoryDatabase()
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    let found = @[RawResult(status: sxRaised, raisedTypeId: "ValueError")]
    let w1 = @[integerChoice(1, 0, 10, 0)]
    let w2 = @[integerChoice(2, 0, 10, 0)]
    var errors: seq[string] = @[]
    check saveSymexRaisedImpl(db, prog, target, defaultSymexSettings(), found,
                              errors, @[], @[w1])
    check saveSymexRaisedImpl(db, prog, target, defaultSymexSettings(), found,
                              errors, @[], @[w2])
    check errors.len == 0
    var loadErrors: seq[string] = @[]
    let got = loadSymexRaisedImpl(db, prog, target, defaultSymexSettings(),
                                  loadErrors)
    check loadErrors.len == 0
    check got.len == 1
    if got.len == 1:
      check got[0].choices == w2

  test "R7 Q2: an index listing the same type id twice is a miss":
    let db = inMemoryDatabase()
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    var errors: seq[string] = @[]
    saveSymexRaisedImpl(db, prog, target, defaultSymexSettings(),
      @[RawResult(status: sxRaised, raisedTypeId: "ValueError")], errors)
    let baseKey = symexCacheKey(prog, target, defaultSymexSettings(),
      z3Version = z3FullVersion(), nimVersion = NimVersion,
      walkerVersion = symexWalkerVersion,
      renderingVersion = renderAsChoicesVersion)
    let tid = "ValueError"
    let node = bytesChoice(cast[seq[byte]](tid), 0, tid.len)
    db.save(baseKey & ":raised2", @[node, node], 1)
    var loadErrors: seq[string] = @[]
    check loadSymexRaisedImpl(db, prog, target, defaultSymexSettings(),
                              loadErrors).len == 0

  test "E2a: stkRaisedExn target kind exists with typeFilter":
    let t = SymexTarget(kind: stkRaisedExn, typeFilter: "ValueError")
    check t.kind == stkRaisedExn
    check t.typeFilter == "ValueError"
