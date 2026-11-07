## RFC-0005 S8w (3), checks-off build half, RFC-0016 W1-d2 (W-07). Built with
## `--overflowChecks:off` (its `.nim.cfg`). The B4 offset whose promotion is
## turned down: `start + 1` wrapping at high(int) is UNDEFINED in C, not a
## wrap, so the wrap-reachable rows (rule a) are now halts, no trusted sxSat.
## The faithful B4 hit (rule b) is kept at full strength.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import ./s8cu_helpers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

type ScanError = object of CatchableError

proc readCStr(data: seq[byte], offset: int): (string, int) =
  ## B4's accumulating scan (chapulin's `readCString`).
  var acc = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (acc, i + 1)
    acc.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

proc sutWrapB4(data: seq[byte], start: int) =
  ## Built without overflow checks (`-d:danger`'s arithmetic): `start + 1`
  ## wraps to `low(int)` at `high(int)`.
  let bump = start + 1
  if bump < start:
    symexTarget("s8w_wrap_b4")
  let (k, p) = readCStr(data, start)
  if k.len == 2 and p == start + 3:
    symexTarget("s8w_wrap_b4_hit")

proc sutWrapMulB4(data: seq[byte], start: int) =
  ## `start * 4` wraps: `start == high(int) div 2` gives a negative product.
  let q = start * 4
  if start > 0 and q < 0:
    symexTarget("s8w_wrapmul_b4")
  let (k, p) = readCStr(data, start)
  if k.len == 1 and p == start + 2:
    symexTarget("s8w_wrapmul_b4_hit")

const exactUnchecked = SymexSettings(integerSemantics: isExact)
const optUnchecked = SymexSettings(integerSemantics: isOptimised)

suite "S8w (3): a B4 offset whose promotion is turned down, checks-off build":

  test "oracle: without overflow checks start + 1 wraps":
    var hit = false
    try: sutWrapB4(@[], high(int))
    except ScanError: hit = true
    check hit
    check (block:
      var x = high(int) div 2
      {.push overflowChecks: off.}
      let q = x * 4
      {.pop.}
      q < 0)

  test "isExact, unchecked: the wrap is is no longer a witness":
    ## Rule (a): was a trusted sxSat at high(int). The overflow is undefined.
    let r = symexFind(sutWrapB4, tLabel("s8w_wrap_b4"), exactUnchecked)
    checkpoint show(r.errors)
    ## The verdict may be the scan's own raise (trusted); it is not the label.
    check r.status != sxSat
    check r.errors.named(ubSignedOverflow)

  test "isOptimised, unchecked: the same":
    ## Rule (a): was a trusted sxSat at high(int).
    let r = symexFind(sutWrapB4, tLabel("s8w_wrap_b4"), optUnchecked)
    checkpoint show(r.errors)
    ## The verdict may be the scan's own raise (trusted); it is not the label.
    check r.status != sxSat
    check r.errors.named(ubSignedOverflow)

  test "isOptimised, unchecked: a multiplication's wrap is is no longer a witness":
    ## Rule (a): was a trusted sxSat with start * 4 < 0.
    let r = symexFind(sutWrapMulB4, tLabel("s8w_wrapmul_b4"), optUnchecked)
    checkpoint show(r.errors)
    ## The verdict may be the scan's own raise (trusted); it is not the label.
    check r.status != sxSat
    check r.errors.named(ubSignedOverflow)

  test "unchecked: the B4 hit is still reachable, and replays":
    let r = symexFind(sutWrapB4, tLabel("s8w_wrap_b4_hit"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      let (k, p) = readCStr(data, start)
      check k.len == 2 and p == start + 3

