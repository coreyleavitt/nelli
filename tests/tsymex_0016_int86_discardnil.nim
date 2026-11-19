## RFC-0016 INT-86 (soundness): a discarded read through a nil reference is a
## `sxRaised(NilAccessDefect)` claim, but natively it does not fault. Nim
## lowers `discard p.n` to `(void)((*p).n);`, which the C compiler does not
## load, so the call returns and a label after it is reached. The walker
## models the read as a dereference: the crash is claimed, the label behind it
## refuted. Found converting `tsymex_0016_wa_runtime` (K9d-12): its
## `lossyNil`'s claim, run in a child on its only nil input, exited 0.
##
## The bar: each verdict below agrees with the native run. A read that is
## kept (`let v = p.n`, used) still faults natively, and stays the control.
## Unregistered while red (`tests/0016-allowlist/ids.txt`).
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type B = object
  n: int

proc discardField(p: ref B) =
  if p == nil:
    discard p.n
    symexTarget("after")

proc discardPtr(p: ptr int) =
  if p == nil:
    discard p[]
    symexTarget("after")

proc keptField(p: ref B): int =
  if p == nil:
    result = p.n
    symexTarget("after")

crashForms:
  case crashForm()
  of "keptField": discard keptField(nil)
  else: discard

suite "INT-86: a discarded nil read does not fault natively":
  test "natively: the discarded reads return and reach the label":
    check nativeRun(discardField(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardPtr(nil)).hitsTarget(tLabel("after"))

  test "natively: a kept read faults (the control)":
    pinCrashSelf(cellKey(faGeneric, "k9d/tsymex_0016_int86_discardnil/keptField/tNilAccess()"),
                 "keptField", ceSegv)

  test "the walker reaches the label behind a discarded nil read":
    for r in [pinFind(discardField, tLabel("after")).status,
              pinFind(discardPtr, tLabel("after")).status]:
      check r == sxSat

  test "and claims no nil access there":
    let a = symexFind(discardField, tNilAccess())
    let b = symexFind(discardPtr, tNilAccess())
    checkpoint $a.status & " " & $b.status
    check a.status != sxRaised
    check b.status != sxRaised

  test "the kept read is still a nil-access claim":
    check symexFind(keptField, tNilAccess()).status == sxRaised

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 444
