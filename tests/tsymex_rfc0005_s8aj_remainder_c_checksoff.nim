## RFC-0016 W1-d2 (W-07), the signed twins of `tsymex_rfc0005_s8aj_remainder_c`
## (2), built with `--overflowChecks:off` (its `.nim.cfg`). A signed sum that
## wraps is undefined there, not a wrap: the overflowing side is a
## `ubSignedOverflow` halt, so neither the dead shapes nor the live one is a
## trusted verdict any more (they were trusted `sxUnsat`/`sxSat`).
import std/unittest
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

template scan() =
  if start < 0: return
  try:
    let (k, p) = readCStr(data, start)
    if k.len == 2 and p == start + 3: symexTarget("hit")
  except ScanError:
    discard

proc sAddWrap(data: seq[byte], start, y: int) =
  if start >= 0 and y > 1 and start + (y + 1) == start: symexTarget("t")
  scan()
proc sAddWrapSat(data: seq[byte], start, y: int) =
  if start >= 0 and y > 1 and start + (y + 1) < start: symexTarget("t")
  scan()
proc sSubWrap(data: seq[byte], start, y: int) =
  if start >= 0 and y > 1 and start - (y + 1) == start: symexTarget("t")
  scan()

const exactSigned = SymexSettings(integerSemantics: isExact)

suite "S8aj (2): a signed sum that wraps, checks-off build":
  test "(rule a) the overflow side halts; no trusted verdict on any of the three":
    check not arithChecksDisagree(exactSigned)
    let r1 = symexFind(sAddWrap, tLabel("t"), exactSigned)
    let r2 = symexFind(sAddWrapSat, tLabel("t"), exactSigned)
    let r3 = symexFind(sSubWrap, tLabel("t"), exactSigned)
    for r in [r1, r2, r3]:
      check not r.trusted
      check r.errors.named(ubSignedOverflow)
