## RFC-0005 (soundness channels) slice S8w -- S8t's remainder.
##
## This slice closes:
##   (1) an alternating `and`/`or` chain (`(a or b) and (c or d) and ...`)
##       forked 2^m paths when its inner operands had raising reads: S8t's
##       nested lowering (`lowerShortCircuitParts`) covered one operator,
##       and an operand of the other operator was lowered by its own
##       recursive parse, whose guard forked two paths that both went on
##       into the rest of the chain;
##   (2) a `while` guard whose first operand hoists a read, in a body that
##       uses `continue`, declined (R14 Case 2);
##   (3) an `isIntOffset` param that `promoteSound` turned down stayed an
##       unstamped, unbounded Int that never wrapped;
##   (4) the base's false `OverflowDefect` witness `(@[], -1)` on a B4 scan.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build); the probe is quoted beside the test.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8w_remainder`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 63 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- (3) a B4 offset promotion turned down: wrap, or a scoped decline -------

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


proc sutBitB4(data: seq[byte], start: int) =
  ## A bit operation on the offset bans its promotion (ADR-0001), and the
  ## arithmetic is checked: `start + 1` raises OverflowDefect at high(int).
  ## A negative offset returns first, so no read can raise IndexDefect and
  ## the only reachable Defect is the overflow.
  if start < 0: return
  let low8 = start and 0xFF
  let bump = start + 1
  let (k, p) = readCStr(data, start)
  if low8 == 7 and k.len == 1 and p == bump + 1:
    symexTarget("s8w_bit_b4")

proc sutSignBitB4(data: seq[byte], start: int) =
  ## A mask keeps the sign: `start and -2` is negative for a negative
  ## `start`. The bridge to bit-vectors is signed, as `int` is.
  if (start and -2) < 0:
    symexTarget("s8w_signbit_b4")
  if start < 0: return
  let (k, p) = readCStr(data, start)
  if k.len == 1 and p == start + 2:
    symexTarget("s8w_signbit_b4_hit")

proc sutShiftB4(data: seq[byte], start: int) =
  ## A shift on the offset: before S8w an unstamped Int reached the shift
  ## and failed the walker's assertion.
  if start < 0: return
  let hi = start shr 2
  let (k, p) = readCStr(data, start)
  if hi == 1 and k.len == 1 and p == start + 2:
    symexTarget("s8w_shift_b4")

proc sutFindMask(s: string) =
  ## An UNSTAMPED Int (`find`'s result, -1 when absent) through a mask:
  ## `find` returns `int`, so `-1 and -2` is `-2`, negative.
  if (s.find('a') and -2) < 0:
    symexTarget("s8w_findmask")

proc sutFindShift(s: string) =
  ## A shift on an unstamped Int: `find`'s -1 shifted right stays -1
  ## (`shr` on `int` is arithmetic).
  if (s.find('a') shr 1) < 0 and s.len > 2:
    symexTarget("s8w_findshift")

proc sutB4(data: seq[byte], start: int) =
  ## The base (a58856d) shape behind S8t's "false OverflowDefect" note.
  let (k, p) = readCStr(data, start)
  if k.len == 2 and p == start + 3:
    symexTarget("s8w_b4")

suite "S8w (3): a B4 offset whose promotion is turned down stays faithful":

  ## RFC-0016 W1-d2: the five tests about a signed wrap with overflow checks off
  ## (the oracle, the wrap, the multiplication's wrap, and the B4 hit beside
  ## them) moved to `tsymex_rfc0005_s8w_remainder_b_checksoff.nim`, built with
  ## `--overflowChecks:off`: a `push overflowChecks: off` routine declines in
  ## this checks-on build.

  test "a bit-banned offset keeps its OverflowDefect":
    ## Probe: `sutBitB4(@[], high(int))` raises OverflowDefect.
    var raised = false
    try: sutBitB4(@[], high(int))
    except OverflowDefect: raised = true
    check raised
    let r = symexFind(sutBitB4, tRaisedExn("OverflowDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"
      var real = ""
      try: sutBitB4(r.raisedWitness[0], r.raisedWitness[1])
      except OverflowDefect: real = "OverflowDefect"
      check real == "OverflowDefect"

  test "a bit-banned offset's hit is reachable, and replays":
    let r = symexFind(sutBitB4, tLabel("s8w_bit_b4"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      check (start and 0xFF) == 7
      let (k, p) = readCStr(data, start)
      check k.len == 1 and p == start + 2

  test "a mask on a signed offset keeps its sign":
    ## Probe: `(-1 and -2) < 0`.
    check (-1 and -2) < 0
    let r = symexFind(sutSignBitB4, tLabel("s8w_signbit_b4"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check (r.witness[1] and -2) < 0

  test "a shift on a banned offset is modelled":
    ## RED: the walker's "shift on promoted Z3Int" assertion.
    let r = symexFind(sutShiftB4, tLabel("s8w_shift_b4"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      check (start shr 2) == 1
      let (k, p) = readCStr(data, start)
      check k.len == 1 and p == start + 2

  test "a mask on an unstamped int keeps its sign":
    ## Probe: `"b".find('a') == -1` and `(-1 and -2) < 0`.
    check "b".find('a') == -1
    let r = symexFind(sutFindMask, tLabel("s8w_findmask"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check (r.witness[0].find('a') and -2) < 0

  test "a shift on an unstamped int is modelled":
    ## Probe: `(-1 shr 1) == -1`.
    check (-1 shr 1) == -1
    let r = symexFind(sutFindShift, tLabel("s8w_findshift"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check (r.witness[0].find('a') shr 1) < 0 and r.witness[0].len > 2

suite "S8w (4): the base's B4 OverflowDefect finding":

  test "a negative offset raises IndexDefect, reported as IndexDefect":
    ## S8t's note read the base's `(@[], -1)` finding under
    ## `tRaisedExn("OverflowDefect")` as a false OverflowDefect. It was
    ## E6: a reachable Defect surfaces as `sxRaised` with ITS OWN type,
    ## whatever the target, and the type was IndexDefect. Probe:
    ## `sutB4(@[], -1)` raises IndexDefect (`data[-1]`).
    var real = ""
    try: sutB4(@[], -1)
    except IndexDefect: real = "IndexDefect"
    check real == "IndexDefect"
    template checkB4(tgt: static SymexTarget) =
      block:
        let r = symexFind(sutB4, tgt)
        checkpoint show(r.errors)
        check r.status == sxRaised
        if r.status == sxRaised:
          check r.raisedTypeId == "IndexDefect"
          var got = ""
          try: sutB4(r.raisedWitness[0], r.raisedWitness[1])
          except IndexDefect: got = "IndexDefect"
          except CatchableError, Defect: got = $getCurrentException().name
          check got == "IndexDefect"
    checkB4(tRaisedExn("OverflowDefect"))
    checkB4(tIndexError())

suite "S8w: walker version":

  test "symexWalkerVersion >= 171":
    check parseInt(symexWalkerVersion) >= 171
