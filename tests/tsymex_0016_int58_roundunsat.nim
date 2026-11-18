## RFC-0016 INT-58: `int(round(x))` and `int(floor(x))` of a small float,
## with an unreachable target. `float(a) / 4.0` for an `int8` lies in
## [-32, 31.75], so its rounding is always in `int` range and `== 103` never
## holds: the verdict is `sxUnsat`, trusted.
##
## Red at 39efd92b: the walk ended the path at the conversion with
## `ubFloatToIntRange` and returned an untrusted `sxUnknown`. The
## conversion's out-of-range side is decided at the op (`decideUndefined`),
## and that check ran under the pruning budget alone (`loopPruneRLimit`,
## 250k units); a rounding (`roundToIntegral`) bit-blasts past it, so the
## side was undecided and an undecided side halts. The plain conversion
## (`int(float(a) / 4.0) == 103`, no rounding) fit the budget and was
## exact. An undecided side is now asked again under `queryRLimit`.
##
## K8b's stdlib axis suite found it (INT-56): the `math.round` fragment,
## alone in a program (`per` = 1), declined under every relation it took.
import std/[unittest, math, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

proc i58Plain(a, b: int8) =
  let x = int(float(a) / 4.0)
  if x == 103: symexTarget("hit")

proc i58Round(a, b: int8) =
  let x = int(round(float(a) / 4.0))
  if x == 103: symexTarget("hit")

proc i58Floor(a, b: int8) =
  let x = int(floor(float(a) / 4.0))
  if x == 103: symexTarget("hit")

suite "INT-58: an unreachable target past a float rounding is exact":
  let all = exhaustive(toSeq(low(int8) .. high(int8)))
  test "walker 417: the version floor":
    check parseInt(symexWalkerVersion) >= 417
  test "control: the plain conversion `int(float(a) / 4.0) == 103` is exact (unsat)":
    let r = symexFind(i58Plain, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxUnsat
  test "math.round: `int(round(float(a) / 4.0)) == 103` is exact (unsat)":
    let r = pinExact(i58Round, cellKey(axStdlibBody, "math.round"), tLabel("hit"), all)
    check r.status == sxUnsat
  test "math.floor: `int(floor(float(a) / 4.0)) == 103` is exact (unsat)":
    let r = pinExact(i58Floor, cellKey(axStdlibBody, "math.floor"), tLabel("hit"), all)
    check r.status == sxUnsat
