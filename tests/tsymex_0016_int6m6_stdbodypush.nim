## RFC-0016 int6-m6: the opaque defect scan reads a stdlib routine whose body
## pushes check options as unreadable, as int6-a5 made it read a user one.
##
## The scan reads a body under its owner's options, as one scope. int6-a5
## made a user routine whose definition text holds a check pragma unreadable
## to it ("may raise any Defect", "may be undefined"); a stdlib routine with
## such a body was still read as one scope.
##
## No stdlib routine of the pinned toolchain (2.2.10) can be reached that
## way: the only stdlib definition whose own text pushes a check is
## `system/seqs_v2.nim`'s `setLen[T]`, which a call never names (`setLen` is
## the `SetLengthSeq` magic, lowered by the compiler); every other in-body
## stdlib push comes from a template (`unCheckedInc`), around increments its
## loop bounds. So the fixture is a module the scan classifies as the stdlib
## by its path (`tests/m6lib/lib/std/`, `isStdlibFile`), shaped as int6-a5's
## user pin: an `overflowChecks: off` region whose `v + 1` is the plain C
## addition, undefined at `high(int)`. Read as one scope (checked), `+` was an
## `OverflowDefect`, never undefined, and the label past the opaque call was
## trusted.

import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s8cu_helpers
import ./m6lib/lib/std/s0016_m6_stdpush

proc opStd(v: int) {.symexOpaque.} =
  discard stdOvfRegion(v)

proc sutStd(v: int) =
  if v == 5: symexTarget("hit")
  opStd(v)

proc nativeOvf(f: proc (v: int) {.nimcall.}; v: int): string =
  try:
    f(v)
    ""
  except OverflowDefect:
    "OverflowDefect"

suite "int6-m6: a stdlib body that pushes is unreadable to the opaque scan":
  test "an opaque callee's stdlib callee with an in-body region":
    # Natively the region's `+` wraps (no `OverflowDefect`): undefined in C.
    check nativeOvf(sutStd, high(int)) == ""
    check stdOvfRegion(5) == 6
    let r = pinFind(sutStd, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check not r.trusted
    check UbKind(ubTailUnverified) in r.soundness.undefinedKinds

suite "int6-m6: walker version":
  test "walker version floor >= 479":
    check parseInt(symexWalkerVersion) >= 479
