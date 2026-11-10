## RFC-0016 W3-z R3 -- the default build: a checked callee is not undefined,
## so the main walk lists nothing and `tUndefined` stays a trusted unsat.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

proc oAdd(a: int64) {.symexOpaque.} =
  discard a + 1

proc sutOnlyInCallee(x: int64) =
  if x > 0: oAdd(x)

proc sutLabelAfter(x: int64) =
  oAdd(x)
  if x == 5: symexTarget("hit")

suite "W3-z R3: checked opaque callee, default build":
  test "tUndefined(overflow) finds nothing (the callee raises OverflowDefect)":
    let r = symexFind(sutOnlyInCallee, tUndefined({ubSignedOverflow}),
                      pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status != sxSat
    check UbKind(ubSignedOverflow) notin r.soundness.undefinedKinds

  test "a plain run lists nothing":
    let r = symexFind(sutLabelAfter, tLabel("hit"), pinSettingsConst)
    check r.status == sxSat
    check r.undefined.len == 0
    check UbKind(ubSignedOverflow) notin r.soundness.undefinedKinds
