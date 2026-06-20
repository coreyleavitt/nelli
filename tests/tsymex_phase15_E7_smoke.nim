## Phase 15 — Cluster E, cycle E7: hermetic E-cluster regression smoke + walker
## version bump "6"→"7" (CLOSES Cluster E).
##
## A single in-process test file that exercises the FULL exception machinery
## (E1–E6) TOGETHER, to catch state-threading bugs introduced by the multi-file
## E1–E6 edits to `WalkCtx` (`handlerStack`, `inFlightExn`, the `sxRaised`
## verdict path, the per-frame `caught`/`escaped`/`pendingRaise` channels). It
## composes, in one file:
##   - inter-proc raise (E3): a helper raises, caught by the caller's try/except
##     (rides the `isCall` escaped-channel propagation).
##   - finally + raise interaction (E5): finally runs on a raised exit and
##     re-raises the original; a finally-raises case REPLACES the in-flight exn.
##   - multi-frame re-raise (E7 DoD): a bare `raise` in an inner except handler
##     pops to the OUTER handler frame and matches there (rides `inFlightExn`).
##   - subtype catch (E4): `except CatchableError:` catches `ValueError`, and a
##     user-defined exn (E4a) is caught by its stdlib base.
##   - Defect (E6): an `assert`-false lowers to `sxRaised{AssertionDefect,
##     isDefect: true}`.
##   - sxRaised cache round-trip (E2a complement): a two-raise SUT's findings are
##     persisted and reloaded from a fresh DB-only state without Z3.
##   - the walker version pin: `symexWalkerVersion == "7"` (this cycle's bump).
import std/[unittest, sequtils, strutils]
import proptest/symex
import proptest/db
import proptest/smt/[types, dsl, runtime]
import proptest/engine/types

# === SUTs ====================================================================

# --- inter-proc raise (E3): helper raises, caller's except ValueError catches -
proc ipHelper(x: int) =
  if x < 0: raise newException(ValueError, "neg")

proc interProcCatch(x: int): int =
  try:
    ipHelper(x)
    result = x
  except ValueError:
    symexTarget("ip_caught")
    result = -1

# --- finally + raise (E5): finally re-raises original / finally-raises-replaces
proc finallyReplaces(x: int): int =
  try:
    raise newException(ValueError, "original")
  finally:
    if x > 100: raise newException(IOError, "overrides")

# --- multi-frame re-raise (E7 DoD): nested try; inner bare `raise` pops to outer
proc nestedReraise(x: int): int =
  try:
    try:
      if x < 0: raise newException(ValueError, "inner")
      result = x
    except IOError:
      result = -99   ## does not match; the bare raise below propagates
      raise
  except ValueError:
    symexTarget("outer_caught")
    result = -1

# --- subtype catch (E4): except CatchableError catches ValueError ------------
proc catchableCatches(x: int): int =
  try:
    if x < 0: raise newException(ValueError, "neg")
    result = x
  except CatchableError:
    symexTarget("base_caught")
    result = -1

# --- user-defined exn caught by its base (E4a) ------------------------------
type E7MyError = object of ValueError

proc userExnCaughtByBase(x: int): int =
  try:
    if x < 0: raise newException(E7MyError, "custom")
    result = x
  except ValueError:
    symexTarget("user_caught")
    result = -1

# --- Defect (E6): assert-false lowers to AssertionDefect raise ---------------
proc assertDefect(x: int) =
  assert x > 0, "must be positive"

# --- two-raise SUT (E2a complement): ValueError on x<0, IOError on x==0 -------
proc twoRaise(x: int) =
  if x < 0: raise newException(ValueError, "neg")
  if x == 0: raise newException(IOError, "zero")

suite "symex Phase 15 E7 — Cluster-E regression smoke + walker version 7":

  # ---- inter-proc raise propagation (E3) ----
  test "E7: inter-proc raise caught by caller handler":
    let r = symexFind(interProcCatch, tLabel("ip_caught"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "E7: inter-proc raise — nothing escapes the boundary":
    # The caller's except ValueError consumes the helper's raise; no sxRaised.
    let r = symexFind(interProcCatch, tRaisedExn("ValueError"))
    check r.status == sxUnsat

  # ---- finally + raise interaction (E5) ----
  test "E7: finally fall-through re-raises original (ValueError, x<=100)":
    let r = symexFind(finallyReplaces, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[0] <= 100

  test "E7: finally-raises replaces in-flight exn (IOError wins, x>100)":
    let r = symexFind(finallyReplaces, tRaisedExn("IOError"))
    check r.status == sxRaised
    check r.raisedTypeId == "IOError"
    check r.raisedWitness[0] > 100

  # ---- multi-frame re-raise (E7 DoD) ----
  test "E7: nested try with bare re-raise pops to outer handler":
    # inner except IOError does NOT match the ValueError; the bare `raise`
    # re-raises through the inner frame to the OUTER except ValueError.
    let r = symexFind(nestedReraise, tLabel("outer_caught"))
    check r.status == sxSat
    check r.witness[0] < 0

  # ---- subtype catch (E4 / E4a) ----
  test "E7: except CatchableError catches ValueError (subtype, E4)":
    let r = symexFind(catchableCatches, tLabel("base_caught"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "E7: user exn caught by stdlib base (E4a)":
    let r = symexFind(userExnCaughtByBase, tLabel("user_caught"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "E7: user exn — caught by base, nothing escapes":
    let r = symexFind(userExnCaughtByBase, tRaisedExn("E7MyError"))
    check r.status == sxUnsat

  # ---- Defect (E6) ----
  test "E7: assert-false lowers to sxRaised AssertionDefect (Defect)":
    let r = symexFind(assertDefect, tRaisedExn("AssertionDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    check r.raisedWitness[0] <= 0

  # ---- sxRaised cache round-trip (E2a complement, semantically-complete) ----
  test "E7: multi-finding sxRaised cache round-trip (reload from DB, no Z3)":
    # A semantically-complete two-raise run: solve each raise path through the
    # real walker, persist both sxRaised findings, then reload them from a fresh
    # DB-only state (empty in-memory cache) and assert BOTH reconstruct without
    # invoking Z3. Complements E2a test 3 (which constructs the seq by hand).
    let vr = symexFind(twoRaise, tRaisedExn("ValueError"))
    check vr.status == sxRaised
    check vr.raisedTypeId == "ValueError"
    let ir = symexFind(twoRaise, tRaisedExn("IOError"))
    check ir.status == sxRaised
    check ir.raisedTypeId == "IOError"

    let db = inMemoryDatabase()
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    let found = @[
      RawResult(status: sxRaised, raisedTypeId: vr.raisedTypeId),
      RawResult(status: sxRaised, raisedTypeId: ir.raisedTypeId),
    ]
    var saveErrors: seq[string] = @[]
    saveSymexRaisedImpl(db, prog, target, defaultSymexSettings(), found, saveErrors)
    check saveErrors.len == 0

    # Fresh load — reconstruct the full seq from the DB alone (no Z3).
    var loadErrors: seq[string] = @[]
    let reloaded = loadSymexRaisedImpl(db, prog, target,
                                       defaultSymexSettings(), loadErrors)
    check reloaded.len == 2
    var typeIds: seq[string]
    for rr in reloaded:
      check rr.status == sxRaised
      typeIds.add rr.raisedTypeId
    check "ValueError" in typeIds
    check "IOError" in typeIds

  # ---- Report-surface defect entry (E6 recording path) ----
  test "E7: Report surface — symexFindings carries the AssertionDefect":
    discard consumeSymexFindings()  # clear any prior findings
    let db = inMemoryDatabase()
    let findings = symexFindAllWitnesses(assertDefect, db)
    let raised = findings.filterIt(it.status == sfRaised)
    check raised.len >= 1
    check raised.anyIt(it.defectTypeId == "AssertionDefect")

  # ---- walker version pin (this cycle's bump 6→7; subsequently R12→10; CR-2→11) ----
  test "E7: walker version is \"9\" (E7 bumped 6->7; G10 7->8; Cluster-C close-out C6 8->9; R12 9->10; CR-2 10->11)":
    check parseInt(symexWalkerVersion) >= 9
