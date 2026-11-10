## RFC-0016 W3-z R3 (wiring audit U2) -- the main walk reads
## `IRStmt.opaqueUndefined`. Only the K10b tail walk did, so on the explore
## walk an opaque call whose body may be undefined was invisible: `tUndefined`
## returned a trusted `sxUnsat` over a reachable overflow inside the callee,
## and `SymexResult.undefined` never listed it. Builds with
## `--overflowChecks:off` (its `.nim.cfg`), where the callee's `+` is undefined.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

proc oAdd(a: int64) {.symexOpaque.} =
  ## An inert opaque callee with a Nim body: it overflows for `a == high`.
  discard a + 1

proc sutOnlyInCallee(x: int64) =
  if x > 0: oAdd(x)

proc sutLabelAfter(x: int64) =
  oAdd(x)
  if x == 5: symexTarget("hit")

suite "W3-z R3: the main walk and opaque undefined behaviour":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 315

  test "tUndefined(overflow) over an overflow only in the callee is not a trusted unsat":
    let r = symexFind(sutOnlyInCallee, tUndefined({ubSignedOverflow}),
                      pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check not r.trusted
    check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds

  test "tUndefined of a kind the callee cannot reach is unaffected":
    let r = symexFind(sutOnlyInCallee, tUndefined({ubArrayOutOfBounds}),
                      pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status != sxSat

  test "a plain run lists the kind":
    let r = symexFind(sutLabelAfter, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check not r.trusted
    check r.undefined.len >= 1
    check r.undefined[0].kind == UbKind(ubSignedOverflow)
