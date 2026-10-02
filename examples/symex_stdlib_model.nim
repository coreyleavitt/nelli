## examples/symex_stdlib_model.nim
##
## Extending the supported fragment via the `{.symexOpaque.}` pragma —
## the user-facing seam for bringing arbitrary procs under symex
## without hand-editing the stdlib model registry.
##
## When the walker encounters a call to an opaque proc, it:
##   * does **not** enter the body;
##   * synthesises a fresh symbolic value of the proc's return type;
##   * records a `feOpaqueCallUnmodelled` gap of class `dcSubstituted`
##     (RFC-0005): the paths through the call may be spurious, and the
##     run may have missed behaviour. So a witness found past the call
##     is `sxSat` only once replay has run the real proc on it and
##     reproduced the target, and an `sxUnsat` is never `trusted()`.
##     `gaps()` names the call.
##
## This is the right model for procs whose body is unimportant to
## symex either because:
##   * the body is uninterpreted (FFI, IO, hardware reads);
##   * the body is well-understood but expensive to walk;
##   * the body is intentionally a black box for verification
##     purposes (Hoare-style abstraction).
##
## The pattern mirrors KLEE's `klee_make_symbolic` and CrossHair's
## `crosshair.SymbolicFactory` — make-symbolic-of-type. The Nim
## ergonomic is a pragma on the proc itself, no extra registration.

import std/[strformat, strutils]
import nelli/symex

# A user-defined opaque proc. Pretend it reads from an IMU.
# Outside symex, this proc runs as written (returns 0). Inside
# symex, the walker treats it as a black box.
proc readSensor(channel: int): int {.symexOpaque.} =
  # Real impl would go here; symex never enters this body.
  0

proc dispatch(channel: int) =
  let v = readSensor(channel)
  if v > 1000:
    symexTarget("alarm")

# The path `v > 1000` is *not* unsat — even though readSensor's
# concrete body returns 0, the opaque-effectful model gives `v` a
# fresh symbolic integer that Z3 can drive into the high range.
# Z3's witness is a candidate only: replay runs `dispatch` on it,
# the real readSensor returns 0, the alarm does not fire, and the
# candidate is refuted. The status is sxUnknown.
let r = symexFind(dispatch, tLabel("alarm"))
doAssert r.status == sxUnknown,
  &"expected sxUnknown for opaque-proc path, got {r.status}"
doAssert not r.trusted
# The gap names the opaque call and its class.
var named = false
for g in r.gaps():
  if g.e.kind == feOpaqueCallUnmodelled:
    doAssert g.class == dcSubstituted
    if "readSensor" in g.e.msg: named = true
doAssert named
echo "symex(dispatch, alarm): status = sxUnknown (honest under {.symexOpaque.})"

# Without the pragma, symex would walk readSensor's body, conclude
# v = 0 always, and report sxUnsat for the alarm branch. That would
# be *unsound* (it would tell you the alarm path is unreachable
# even though at runtime v is whatever the sensor produces). The
# pragma is the price of soundness over fragmentary models.
echo "Phase 9 cycle 6: {.symexOpaque.} brings user procs under symex."
