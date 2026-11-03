## RFC-0005 S8cu -- a callee in another module, an `include`, generics, generated
## routines, and the stdlib routines the walker walks.
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets, math, macros, strutils]
import nelli
import nelli/symex
import ./s8cu_fix_callee
import ./s8cu_helpers

template hitIfWraps(call: untyped) =
  if v == high(int):
    let w = call
    if w < 0: symexTarget("hit")

proc viaCheckedField(v: int) =
  checkedField(v)
  symexTarget("hit")
proc viaUncheckedField(v: int) =
  uncheckedField(v)
  symexTarget("hit")
proc viaCheckedAdd(v: int) = hitIfWraps(checkedAdd(v))
proc viaUncheckedAdd(v: int) = hitIfWraps(uncheckedAdd(v))

# A generic takes the options at its definition, wherever it is instantiated.
proc viaGenericUnder(v: int) = hitIfWraps(genericUnder(v))
{.push overflowChecks: off.}
proc genericCleanInPush(v: int): int = genericClean(v)
{.pop.}
proc viaGenericCleanInPush(v: int) = hitIfWraps(genericCleanInPush(v))
proc viaGenericClean(v: int) = hitIfWraps(genericClean(v))

# An `include`: the push is in the including file.
{.push overflowChecks: off.}
include ./s8cu_fix_included
{.pop.}
proc viaIncludedPlain(v: int) = hitIfWraps(includedPlain(v))
proc viaIncludedOn(v: int) = hitIfWraps(includedOn(v))

# A routine a template generates: line info at the template, options at the
# expansion. The other module's template, then this file's.
{.push overflowChecks: off.}
makeAdder(adderFromThere)
{.pop.}
proc viaAdderThere(v: int) = hitIfWraps(adderFromThere(v))

template makeLocalAdder(name: untyped) =
  proc name(v: int): int = v + 1
{.push overflowChecks: off.}
makeLocalAdder(adderFromHere)
{.pop.}
proc viaAdderHere(v: int) = hitIfWraps(adderFromHere(v))

# A routine a macro generates: its line info is the macro's call.
macro makeByMacro(name: untyped): untyped =
  result = quote do:
    proc `name`(v: int): int = v + 1
{.push overflowChecks: off.}
makeByMacro(adderByMacro)
{.pop.}
makeByMacro(adderByMacroClean)
proc viaMacro(v: int) = hitIfWraps(adderByMacro(v))
proc viaMacroClean(v: int) = hitIfWraps(adderByMacroClean(v))

# The stdlib: `math.nim` is under `{.push checks: off.}` from line 157.
proc viaFloorDiv(a: int) =
  if a == 7 and floorDiv(a, 2) == 3: symexTarget("hit")
proc viaIsPowerOfTwo(a: int) =
  if a == 8 and isPowerOfTwo(a): symexTarget("hit")
# Models and routines outside any such region keep deciding.
proc viaAbs(a: int) =
  if a == -3 and abs(a) == 3: symexTarget("hit")
proc viaMin(a: int) =
  if a == 5 and min(a, 3) == 3: symexTarget("hit")
proc viaSqrt(a: float) =
  if a == 9.0 and sqrt(a) == 3.0: symexTarget("hit")
proc viaStrip(a: string) =
  if a == " x" and a.strip == "x": symexTarget("hit")

suite "S8cu: a callee in another module":

  test "a checked callee keeps its raise (control)":
    check native(viaCheckedField(4)) == "FieldDefect"
    decides(viaCheckedField, sxRaised)
    check native(viaCheckedAdd(high(int))) == "OverflowDefect"
    decides(viaCheckedAdd, sxRaised)

  test "an unchecked callee declines":
    check native(viaUncheckedField(4)) == "hit"
    declines(viaUncheckedField, feCheckOption)
    check native(viaUncheckedAdd(high(int))) == "hit"
    declines(viaUncheckedAdd, feOverflowCheckOption)

suite "S8cu: generics":

  test "defined under a push, instantiated here: unchecked":
    check native(viaGenericUnder(high(int))) == "hit"
    declines(viaGenericUnder, feOverflowCheckOption)

  test "defined clean, instantiated under a push: checked":
    check native(viaGenericCleanInPush(high(int))) == "OverflowDefect"
    # The instantiating routine is itself under the push, and declines; the generic
    # alone, from a clean routine, decides.
    declines(viaGenericCleanInPush, feOverflowCheckOption)
    check native(viaGenericClean(high(int))) == "OverflowDefect"
    decides(viaGenericClean, sxRaised)

suite "S8cu: include":

  test "a push in the including file reaches the included routine":
    check native(viaIncludedPlain(high(int))) == "hit"
    declines(viaIncludedPlain, feOverflowCheckOption)

  test "an inner push in the included file turns it back on":
    check native(viaIncludedOn(high(int))) == "OverflowDefect"
    decides(viaIncludedOn, sxRaised)

suite "S8cu: generated routines":

  test "a template in another module":
    check native(viaAdderThere(high(int))) == "hit"
    declines(viaAdderThere, feOverflowCheckOption)

  test "a template in this file":
    check native(viaAdderHere(high(int))) == "hit"
    declines(viaAdderHere, feOverflowCheckOption)

  test "a macro, under the push and not":
    check native(viaMacro(high(int))) == "hit"
    declines(viaMacro, feOverflowCheckOption)
    check native(viaMacroClean(high(int))) == "OverflowDefect"
    decides(viaMacroClean, sxRaised)

suite "S8cu: the stdlib":

  test "a walked routine under `math.nim`'s push declines":
    check native(viaFloorDiv(7)) == "hit"
    declines(viaFloorDiv, feCheckOption)
    check native(viaIsPowerOfTwo(8)) == "hit"
    declines(viaIsPowerOfTwo, feCheckOption)

  test "models and routines outside those regions still decide (control)":
    check native(viaAbs(-3)) == "hit"
    decides(viaAbs, sxSat)
    check native(viaMin(5)) == "hit"
    decides(viaMin, sxSat)
    check native(viaSqrt(9.0)) == "hit"
    decides(viaSqrt, sxSat)
    check native(viaStrip(" x")) == "hit"
    decides(viaStrip, sxSat)
