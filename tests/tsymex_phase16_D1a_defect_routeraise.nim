## Phase 16 D1a — route target defects through routeRaise (sxSat→sxRaised).
##
## Before D1a, the defect fork at each site (IndexDefect, FieldDefect,
## AssertionDefect, NilAccessDefect) was guarded by `if w.target.kind ==
## stkXxx:` and called trySolve directly → sxSat.  This meant a SUT that
## catches the defect still returned sxSat (the handler was invisible to
## the engine).
##
## After D1a the fork is UNCONDITIONAL and routes through routeRaise:
##   • A caught defect yields sxUnsat for that target (no finding).
##   • An uncaught defect reaches the SUT boundary as sxRaised
##     (raisedTypeId set; witness in raisedWitness, NOT witness).
##   • A wrong-type handler does NOT catch the defect → sxRaised.
import std/unittest
import nelli/symex

# ---- SUT fixtures -------------------------------------------------------

proc caughtIndexed(i: int) =
  ## Catches IndexDefect inline. After D1a, symex models this handler —
  ## the defect path is CONSUMED → no finding under tIndexError.
  let a = [1, 2, 3]
  try:
    let v = a[i]
    discard v
  except IndexDefect:
    discard

proc uncaughtIndexed(arr: array[5, int], i: int) =
  ## Unconditional array index — never catches. Under tIndexError this
  ## should surface sxRaised with raisedTypeId == "IndexDefect" and the
  ## OOB index in raisedWitness[1].
  let v = arr[i]
  discard v

proc wrongHandlerIndexed(i: int) =
  ## `except ValueError` does NOT cover IndexDefect; the defect escapes.
  let a = [1, 2, 3]
  try:
    let v = a[i]
    discard v
  except ValueError:
    discard

# ---- Tests --------------------------------------------------------------

suite "symex Phase 16 D1a — defect fork routed through routeRaise":

  # ---------- tracer: the killer new capability ----------------------------

  test "IndexDefect fully caught by handler → sxUnsat (no finding)":
    ## Core D1a capability: the fork is unconditional so routeRaise sees the
    ## handler and CONSUMES the raise. No finding → sxUnsat.
    let r = symexFind(caughtIndexed, tIndexError())
    check r.status == sxUnsat

  # ---------- uncaught OOB now returns sxRaised ----------------------------

  test "uncaught OOB → sxRaised with raisedTypeId=IndexDefect":
    let r = symexFind(uncaughtIndexed, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

  test "uncaught OOB witness is in raisedWitness, not witness":
    let r = symexFind(uncaughtIndexed, tIndexError())
    check r.status == sxRaised
    let i = r.raisedWitness[1]
    check (i < 0 or i >= 5)

  # ---------- wrong-type handler does NOT catch defect ----------------------

  test "wrong-type handler (except ValueError) does not catch IndexDefect":
    ## The defect escapes past the ValueError handler → sxRaised.
    let r = symexFind(wrongHandlerIndexed, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
