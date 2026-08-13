## `func` (nnkFuncDef) support across the symex resolver.
##
## `func` is pure sugar for `proc {.noSideEffect.}` but lowers to
## `nnkFuncDef`, a node kind with the exact same child layout as
## `nnkProcDef`. Nine resolver sites accepted only `nnkProcDef`, so a
## `func` anywhere on the walked path either degraded the run to
## `sxUnknown` (`ensureProcRegistered`'s classified-degrade arm), died on
## `expectKind` (`parseCalleeImpl`, `parseProc`), or was silently
## misclassified (generics helpers treating a generic `func` as
## non-generic; `hasBorrowPragma`/`hasSymexOpaquePragma`/the rune-compare
## intercept skipping `func`s). First hit as Finding 1 of the chronos
## CallbackQueue verification harness, whose shipped index primitives are
## `func`s.
##
## Tests:
##   1. Interprocedural `func` callee proves sxUnsat — registration and
##      `parseCalleeImpl` walk the body. A degrade would be sxUnknown,
##      never sxUnsat, so UNSAT here is proof of a real walk.
##   2. The same callee's semantics are really encoded: a falsifiable
##      variant reports the violation (sxRaised/AssertionDefect per
##      Phase 16 D1a) and the witness satisfies the func's body.
##   3. Generic `func` callee monomorphizes: `isGenericImpl`/
##      `genericParamsNode`/`gatherTypeSubst` treat nnkFuncDef like
##      nnkProcDef instead of silently classifying the callee as
##      non-generic.
##   4. `func` as the DIRECT `symexFind` target (`parseProc`).
##
## The `hasBorrowPragma`/`hasSymexOpaquePragma`/rune-intercept widenings
## share the same one-line shape but have no dedicated cases here; the
## borrow and opaque paths keep their own suites (phase15 g5, phase 3).

import std/unittest
import nelli/symex

# ===========================================================================
# SUTs
# ===========================================================================

func maskLow3(x: int): int =
  x and 7

proc checkMaskLow3Bound(x: int) =
  let m = maskLow3(x)
  symexAssert(m >= 0 and m < 8)

proc checkMaskLow3Falsifiable(x: int) =
  let m = maskLow3(x)
  symexAssert(m != 5)

func addG[T](a, b: T): T =
  a + b

proc checkGenericFuncCallee(a, b: int) =
  symexAssume(a >= 0 and a < 100 and b >= 0 and b < 100)
  let s = addG(a, b)
  symexAssert(s == a + b)

func directRaise(x: int) =
  ## A `func` cannot call the side-effectful `symexAssert` marker, so a
  ## direct-target func's only observable is a raw `doAssert` — which the
  ## walker classifies as sxRaised when reachable, never as the
  ## tAssertionViolation target class.
  doAssert x != 42, "reachable for exactly one input"

func directUnreachable(x: int) =
  let low3 = x and 7
  doAssert low3 < 8, "unreachable: masking bounds the value"

# ===========================================================================
# Tests
# ===========================================================================

suite "symex: nnkFuncDef acceptance":

  test "interprocedural func callee proves sxUnsat (walked, not degraded)":
    let r = symexFind(checkMaskLow3Bound, tAssertionViolation())
    check r.status == sxUnsat

  test "func callee body really encoded: falsifiable variant + witness":
    let r = symexFind(checkMaskLow3Falsifiable, tAssertionViolation())
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    check (r.raisedWitness[0] and 7) == 5

  test "generic func callee monomorphizes (not silently non-generic)":
    let r = symexFind(checkGenericFuncCallee, tAssertionViolation())
    check r.status == sxUnsat

  test "func as direct symexFind target: reachable raise found (sxRaised, not a degrade)":
    let r = symexFind(directRaise, tAssertionViolation())
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    check r.raisedWitness[0] == 42

  test "func as direct symexFind target: unreachable raise proven (sxUnsat)":
    let r = symexFind(directUnreachable, tAssertionViolation())
    check r.status == sxUnsat
