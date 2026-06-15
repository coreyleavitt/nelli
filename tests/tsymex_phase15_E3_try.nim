## Phase 15 — Cluster E, cycle E3: `try`/`except` matching by type
## (first-match, catch-all) + inter-procedural `ivRaised` propagation.
##
## E2b made `walk(isRaise)` real but the `isTry` arm was still the E1
## classified stub. E3 implements the `isTry` walker path: the try body is
## walked with the try's handlers pushed onto the per-frame handler stack;
## a raise inside the body consults that stack top-down and the FIRST
## matching `except` clause wins (exact-string type membership — subtype
## matching is E4; a bare `except:` is catch-all). A matched raise is
## CONSUMED: the path transfers into the handler body and continues. An
## unmatched raise propagates (to an outer try, the caller's try via the
## inter-proc path, or out the SUT boundary as `sxRaised`).
import std/unittest
import proptest/symex
import proptest/smt/[dsl, runtime]

# --- 1. raise caught by a matching `except ValueError` ----------------------
proc caughtMatch(x: int): int =
  try:
    if x < 0: raise newException(ValueError, "neg")
    result = x
    symexTarget("done")
  except ValueError:
    symexTarget("caught")
    result = -1

# --- 2. unmatched type (`except IOError`) propagates past the try -----------
proc unmatchedType(x: int): int =
  try:
    if x < 0: raise newException(ValueError, "neg")
    result = x
  except IOError:
    result = -1

# --- 3. bare `except:` catches everything -----------------------------------
proc bareCatchAll(x: int): int =
  try:
    if x < 0: raise newException(ValueError, "neg")
    result = x
  except:
    symexTarget("caught")
    result = -1

# --- 4. inter-proc: raise in `helper` caught by `f`'s `except ValueError` ---
proc helper(x: int) =
  if x < 0: raise newException(ValueError, "neg")

proc interProc(x: int): int =
  try:
    helper(x)
    result = x
  except ValueError:
    symexTarget("caught")
    result = -1

# --- 5. NEGATIVE: `except CatchableError:` does NOT catch ValueError at E3 ---
proc catchableNoMatch(x: int): int =
  try:
    if x < 0: raise newException(ValueError, "neg")
    result = x
  except CatchableError:
    symexTarget("caught")
    result = -1

suite "symex Phase 15 E3 — try/except matching + inter-proc propagation":
  test "E3: raise inside try caught by matching except (normal path)":
    # The `done` label is on the normal (non-raising) path; reachable with x >= 0.
    let r = symexFind(caughtMatch, tLabel("done"))
    check r.status == sxSat
    check r.witness[0] >= 0

  test "E3: raise inside try caught by matching except (handler body reached)":
    # The handler-body `caught` marker is reachable; witness x < 0.
    let r = symexFind(caughtMatch, tLabel("caught"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "E3: unmatched exception type propagates past try (isExact)":
    let r = symexFind(unmatchedType, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[0] < 0

  test "E3: unmatched exception type propagates past try (isOptimised)":
    let r = symexFind(unmatchedType, tRaisedExn("ValueError"), optimisedSymexSettings())
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"

  test "E3: bare except catches all (handler body reached)":
    let r = symexFind(bareCatchAll, tLabel("caught"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "E3: bare except catches all (no escaping raise)":
    # With the bare except consuming the raise, nothing escapes the boundary.
    let r = symexFind(bareCatchAll, tRaisedExn("ValueError"))
    check r.status == sxUnsat

  test "E3: inter-proc raise propagates into caller handler (isExact)":
    let r = symexFind(interProc, tLabel("caught"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "E3: inter-proc raise propagates into caller handler (isOptimised)":
    let r = symexFind(interProc, tLabel("caught"), optimisedSymexSettings())
    check r.status == sxSat
    check r.witness[0] < 0

  test "E3: CatchableError handler does NOT catch ValueError at E3 (negative)":
    # Transitional exact-string matching: CatchableError != ValueError, so the
    # raise escapes as sxRaised. Superseded by E4's isSubtypeOf.
    let r = symexFind(catchableNoMatch, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"

  test "E3: CatchableError handler does NOT catch ValueError — handler unreached":
    let r = symexFind(catchableNoMatch, tLabel("caught"))
    check r.status == sxUnsat
