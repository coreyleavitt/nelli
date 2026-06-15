## Phase 15 — Cluster E, cycle E4: exception type hierarchy (subtype catch).
##
## E3 matched handlers by EXACT-STRING type membership (`typeId in
## handler.typeIds`). E4 replaces that with `isSubtypeOf`, which walks the
## raised type's ancestor chain through a static `ExnTypeTable` (built from
## Nim's real exception hierarchy) plus the (E4a-populated, empty here)
## `userExnHierarchy`. So `except CatchableError:` now catches a raised
## `ValueError` (ValueError is-a CatchableError is-a Exception). A bare
## `except:` (empty typeIds) still catches everything. An unknown exception
## type (not in either table) matches ONLY a bare `except:` and emits a
## `sevWarning` classified error (Invariant 3 — no silent false-negative).
##
## `isDefect(table, typeId, userExnHierarchy)` returns true for any known
## Defect subtype, and — via the dkOther fallback — for an unknown type
## whose ancestor chain (in `userExnHierarchy`, populated by E4a) traces to
## `Defect`. E4 ships the membership logic; the dynamic capture that fills
## `userExnHierarchy` is E4a, so test 3 supplies the chain the way E4a will.
import std/[unittest, tables]
import proptest/symex
import proptest/smt/[dsl, runtime]
import proptest/smt/exn_hierarchy

# --- 1. base-type except catches derived raise ------------------------------
proc baseCatchesDerived(x: int): int =
  try:
    if x < 0: raise newException(ValueError, "neg")
    result = x
  except CatchableError:
    symexTarget("caught_by_base")
    result = -1

# --- 2. sibling type does not match -----------------------------------------
proc siblingNoMatch(x: int): int =
  try:
    if x < 0: raise newException(ValueError, "neg")
    result = x
  except IOError:
    result = -1

# --- 3. user-defined Defect subtype -----------------------------------------
type MyDefect = object of Defect

proc raisesMyDefect(x: int) =
  if x < 0: raise newException(MyDefect, "boom")

suite "symex Phase 15 E4 — exception subtype hierarchy":
  test "E4: base-type except catches derived raise":
    # `except CatchableError:` now catches a raised `ValueError` (subtype).
    let r = symexFind(baseCatchesDerived, tLabel("caught_by_base"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "E4: sibling type does not match (propagates)":
    # IOError is a sibling of ValueError under CatchableError; no catch.
    let r = symexFind(siblingNoMatch, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"

  test "E4: ExnTypeTable encodes Nim's real hierarchy (subtype membership)":
    # ValueError is-a CatchableError is-a Exception.
    check isSubtypeOf("ValueError", "ValueError", exnTypeTable, initTable[string, string]())
    check isSubtypeOf("ValueError", "CatchableError", exnTypeTable, initTable[string, string]())
    check isSubtypeOf("ValueError", "Exception", exnTypeTable, initTable[string, string]())
    # KeyError is-a ValueError (the real Nim ancestry, NOT directly CatchableError).
    check isSubtypeOf("KeyError", "ValueError", exnTypeTable, initTable[string, string]())
    # Siblings / unrelated do not match.
    check not isSubtypeOf("ValueError", "IOError", exnTypeTable, initTable[string, string]())
    check not isSubtypeOf("ValueError", "Defect", exnTypeTable, initTable[string, string]())
    # Defect subtypes.
    check isSubtypeOf("IndexDefect", "Defect", exnTypeTable, initTable[string, string]())
    check isSubtypeOf("AssertionDefect", "Defect", exnTypeTable, initTable[string, string]())

  test "E4: user-defined Defect subtype routes to dkOther; inclusion works":
    # Standard Defect subtypes are isDefect via the static table.
    check isDefect(exnTypeTable, "IndexDefect")
    check isDefect(exnTypeTable, "AssertionDefect")
    check not isDefect(exnTypeTable, "ValueError")
    # An unknown user Defect subtype routes to dkOther: with its parent chain
    # in `userExnHierarchy` (what E4a captures dynamically), isDefect is true.
    var userHier = initTable[string, string]()
    userHier["MyDefect"] = "Defect"
    check isDefect(exnTypeTable, "MyDefect", userHier)
    check isSubtypeOf("MyDefect", "Defect", exnTypeTable, userHier)
    # Observable walker behavior: the MyDefect raise surfaces (no handler).
    let r = symexFind(raisesMyDefect, tRaisedExn("MyDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "MyDefect"
