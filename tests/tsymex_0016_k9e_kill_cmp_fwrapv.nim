## RFC-0016 K9e -- pin strength, the cmp cluster's unchecked-build half. Built
## with `--overflowChecks:off -d:nelliFwrapv` (its `.nim.cfg`), like
## `tsymex_0016_k5a_fwrapv`: the regime in which a signed Int-sorted result is a
## DEFINED wrap (`wrapDefined`), so `lowerArith` reduces it to its window, and
## in which an 8 or 16 bit signed quotient `low(T) div -1` wraps back to
## `low(T)`. The checks-on half is `tsymex_0016_k9e_kill_cmp`.
import std/options
import nelli/smt/buildprofile
const admission = admitBuild(buildSemantics, buildProvenance)
when admission.isSome:
  import std/unittest

  suite "K9e cmp fwrapv: refused build":
    test "symex refuses the build by name":
      check admission.get.field == bfFwrapv
else:
  import std/[unittest, strutils]
  import nelli
  import nelli/symex
  import ./s8cu_helpers

  type ScanError = object of CatchableError

  proc readCStr(data: seq[byte], offset: int): (string, int) =
    var acc = ""
    var i = offset
    while i < data.len:
      if data[i] == 0'u8:
        return (acc, i + 1)
      acc.add char(data[i])
      i.inc
    raise newException(ScanError, "unterminated")

  proc sutWrapB4(data: seq[byte], start: int) =
    ## `start + 1` is a defined wrap at `high(int)`.
    let bump = start + 1
    if bump < start:
      symexTarget("hit")
    let (k, p) = readCStr(data, start)
    if k.len == 2 and p == start + 3:
      symexTarget("other")

  proc sutI8DivWrap(x, y: int8) =
    ## `low(int8) div -1` is 128 in C's `int` and narrows back to -128.
    symexAssume(x >= -128 and x <= 127)
    symexAssume(y >= -128 and y <= 127)
    # Nested, not `and`: a boolean `and` is a bit-twiddling operand, which
    # bans `x` and `y` from the Int sort (the arm under test).
    if y == -1:
      if x < 0:
        if x div y < 0:
          symexTarget("hit")

  suite "K9e cmp fwrapv: the unchecked arithmetic of an Int-sorted value":
    test "version floor":
      check parseInt(symexWalkerVersion) >= 288

    test "a signed offset wraps at high(int)":
      let r = pinFind(sutWrapB4, tLabel("hit"))
      check r.status == sxSat
      check r.trusted

    test "an int8 quotient low(T) div -1 wraps back to low(T)":
      let r = pinFind(sutI8DivWrap, tLabel("hit"))
      check r.status == sxSat
      check r.trusted
