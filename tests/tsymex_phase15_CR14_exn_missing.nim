## Phase 15 — Code-Review finding CR-14: missing stdlib exception types in
## exnTypeTable (EOFError, LibraryError, ResourceExhaustedError).
##
## Before the fix `exnTypeTable` omits:
##   EOFError          (parent: IOError)
##   LibraryError      (parent: OSError)
##   ResourceExhaustedError (parent: CatchableError)
##
## Consequence: `raise newException(EOFError, ...)` caught by `except IOError:`
## falls to the unknown-type path (sxUnknown + sevWarning) instead of
## correctly matching the handler.
##
## RED state: the engine yields sxUnknown for `raise EOFError` caught by
## `except IOError` (EOFError unknown → no-match → propagates → uncaught
## → sxUnknown).
##
## GREEN state: with the three types added to `exnTypeTable`, the engine
## resolves EOFError as a subtype of IOError and yields sxRaised (handled)
## — i.e. the `except IOError:` handler fires, the label is reached.
import std/[unittest, tables]
import proptest/symex
import proptest/smt/[dsl, runtime]
import proptest/smt/exn_hierarchy

# --- CR-14 test proc: EOFError caught by IOError handler --------------------
proc eofCaughtByIOError(x: int): int =
  try:
    if x < 0: raise newException(EOFError, "eof")
    result = x
  except IOError:
    symexTarget("caught_eof")
    result = -1

# --- CR-14 isSubtypeOf table checks ----------------------------------------
suite "symex Phase 15 CR-14 — missing stdlib exception types":

  test "CR-14: EOFError is-a IOError in static table":
    check isSubtypeOf("EOFError", "IOError", exnTypeTable, initTable[string, string]())
    check isSubtypeOf("EOFError", "CatchableError", exnTypeTable, initTable[string, string]())
    check isSubtypeOf("EOFError", "Exception", exnTypeTable, initTable[string, string]())
    # EOFError is NOT a sibling/unrelated
    check not isSubtypeOf("EOFError", "OSError", exnTypeTable, initTable[string, string]())
    check not isSubtypeOf("EOFError", "Defect", exnTypeTable, initTable[string, string]())

  test "CR-14: LibraryError is-a OSError in static table":
    check isSubtypeOf("LibraryError", "OSError", exnTypeTable, initTable[string, string]())
    check isSubtypeOf("LibraryError", "CatchableError", exnTypeTable, initTable[string, string]())
    check isSubtypeOf("LibraryError", "Exception", exnTypeTable, initTable[string, string]())
    check not isSubtypeOf("LibraryError", "IOError", exnTypeTable, initTable[string, string]())

  test "CR-14: ResourceExhaustedError is-a CatchableError in static table":
    check isSubtypeOf("ResourceExhaustedError", "CatchableError", exnTypeTable, initTable[string, string]())
    check isSubtypeOf("ResourceExhaustedError", "Exception", exnTypeTable, initTable[string, string]())
    check not isSubtypeOf("ResourceExhaustedError", "IOError", exnTypeTable, initTable[string, string]())

  test "CR-14: raise EOFError caught by except IOError reaches label (sxSat)":
    ## RED: sxUnknown (EOFError unknown → no match → uncaught → sxUnknown).
    ## GREEN: sxSat (EOFError is-a IOError → handler fires → label reached).
    let r = symexFind(eofCaughtByIOError, tLabel("caught_eof"))
    check r.status == sxSat
    check r.witness[0] < 0
