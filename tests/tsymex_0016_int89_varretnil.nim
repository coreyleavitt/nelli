## RFC-0016 INT-89 (soundness): a `var T` result naming a field of a nil
## `ref` is an address, not a read, but the walker walks the callee's
## `result = p.n` as a dereference. Natively `varN(nil)` computes
## `&(*p).n` (address arithmetic, no load) and `discard varN(nil)` drops the
## `(void)(*T)` read, so the call returns and the label after it is reached
## (pinned toolchain, gcc and g++, c and cpp, `-O0` through `-d:danger`).
## The walker claims `sxRaised(NilAccessDefect)` and the label behind it is
## refuted. Found probing INT-86's class (K9d-12). A copy of the result
## (`result = varN(p)`) loads it and faults natively, as the walker says.
## Unregistered while red (`tests/0016-allowlist/ids.txt`).
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type B = object
  n: int

proc varN(p: ref B): var int = p.n

proc discardVar(p: ref B) =
  if p == nil:
    discard varN(p)
    symexTarget("after")

proc keptVar(p: ref B): int =
  if p == nil:
    result = varN(p)
    symexTarget("after")

crashForms:
  case crashForm()
  of "keptVar": discard keptVar(nil)
  else: discard

suite "INT-89: a `var` result through nil is an address":
  test "natively: the discarded call returns and reaches the label":
    check nativeRun(discardVar(nil)).hitsTarget(tLabel("after"))

  test "natively: a copy of the result faults (the control)":
    pinCrashSelf(cellKey(faGeneric, "k9d/tsymex_0016_int89_varretnil/keptVar/tNilAccess()"),
                 "keptVar", ceSegv)

  test "the walker reaches the label and claims no nil access":
    let a = symexFind(discardVar, tLabel("after"))
    let b = symexFind(discardVar, tNilAccess())
    checkpoint $a.status & " " & $b.status
    check a.status != sxRaised
    check b.status != sxRaised

  test "the copied result is still a nil-access claim":
    check symexFind(keptVar, tNilAccess()).status == sxRaised

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 447
