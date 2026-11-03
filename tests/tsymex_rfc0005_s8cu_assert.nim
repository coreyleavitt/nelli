## RFC-0005 S8cu -- assertions, and a global's initialiser under a push.
##
## A routine's own `assert` is decided at its definition's semantic pass, so the
## typed AST the walker reads already has it or lacks it. The walker's own model
## of a stdlib iterator's `assert` (`mitems`, `pairs`: the length check) cannot be
## read that way: the iterator's instance takes the options of its first
## instantiation. In a module that may compile `assert` out it declines.
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_assert
import ./s8cu_helpers

# A module with no assertions push: the iterator's assert is modelled. `uint16`
# is instantiated nowhere else under a push.
proc mitemsClean(v: int) =
  if v == 4:
    var s = @[1'u16, 2, 3]
    for x in s.mitems:
      if s.len == 3: s.add 9
    symexTarget("hit")

suite "S8cu: assertions":

  test "a routine's own assert follows its definition's push":
    check native(aOff(4)) == "hit"
    decides(aOff, sxSat)
    check native(aOn(4)) == "AssertionDefect"
    decides(aOn, sxRaised)

  test "doAssert is never compiled out":
    check native(daOff(4)) == "AssertionDefect"
    decides(daOff, sxRaised)

  test "a generic's assert follows the instantiation site":
    check native(viaGAOff(4)) == "AssertionDefect"
    decides(viaGAOff, sxRaised)
    check native(viaGACleanInPush(4)) == "hit"
    decides(viaGACleanInPush, sxSat)

  test "a template's assert follows the expansion site":
    check native(viaTAOff(4)) == "AssertionDefect"
    decides(viaTAOff, sxRaised)
    check native(viaTAClean(4)) == "hit"
    decides(viaTAClean, sxSat)

  test "`push checks: off` drops assert too, and the routine declines":
    check native(aChecksOff(4)) == "hit"
    declines(aChecksOff, feCheckOption)

  test "an iterator's first instantiation under the push: no assert, declines":
    # Was a false sxRaised: the walker modelled the length check.
    check native(mitemsFirstOff(4)) == "hit"
    declines(mitemsFirstOff, feCheckOption)
    check native(pairsFirstOff(4)) == "hit"
    declines(pairsFirstOff, feCheckOption)

  test "outside the push, in the same module, it declines too":
    check native(mitemsOutside(4)) == "AssertionDefect"
    declines(mitemsOutside, feCheckOption)

  test "a module with no assertions push keeps the model (control)":
    check native(mitemsClean(4)) == "AssertionDefect"
    decides(mitemsClean, sxRaised)

suite "S8cu: a global's initialiser under a push":

  test "is not evaluated: the global is havoc":
    check native(readWrapped(4)) == "hit"
    let r = symexFind(readWrapped, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status in {sxSat, sxUnknown}
    check r.errors.named(feGlobalHavoc)
    check native(readWrappedNot(4)) == "ran"
    declines(readWrappedNot, feGlobalHavoc)
