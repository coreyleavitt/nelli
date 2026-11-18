## RFC-0016 INT-58 (RED, open): `int(round(x))` and `int(floor(x))` of a
## small float decline `ubFloatToIntRange` when the target is unreachable.
## `float(a) / 4.0` for an `int8` lies in [-32, 31.75], so its rounding is
## always in `int` range and `== 103` never holds: the verdict is `sxUnsat`.
## The walk instead ends the path at the conversion with `ubFloatToIntRange`
## and returns an untrusted `sxUnknown`, in about 2 s, on two modelled exact
## stdlib rows (`math.round`, `math.floor`). A reachable target over the same
## conversion (`<= 3`) is exact, so the decline is on the unsat side only.
##
## K8b's stdlib axis suite found it (INT-56): the `math.round` fragment,
## alone in a program (`per` = 1), declined under every relation it took.
## Not registered in the nimble test task while it is red.
import std/[unittest, math]
import nelli
import nelli/symex
import ./s8cu_helpers

proc i58Round(a, b: int8) =
  let x = int(round(float(a) / 4.0))
  if x == 103: symexTarget("hit")

proc i58Floor(a, b: int8) =
  let x = int(floor(float(a) / 4.0))
  if x == 103: symexTarget("hit")

suite "INT-58 (red): an unreachable target past a float rounding declines":
  test "math.round: `int(round(float(a) / 4.0)) == 103` is exact (unsat)":
    let r = symexFind(i58Round, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxUnsat
  test "math.floor: `int(floor(float(a) / 4.0)) == 103` is exact (unsat)":
    let r = symexFind(i58Floor, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxUnsat
