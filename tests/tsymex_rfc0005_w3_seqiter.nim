## RFC-0005 W3 (WA-3) -- `items` and `pairs` over a seq, whose length changes.
##
## `system.items` / `pairs` over a seq is
##
##   var i = 0; let L = len(a)
##   while i < L: yield a[i]; inc(i); assert(len(a) == L)
##
## so a body that changes the seq's length ends the iteration in
## `AssertionDefect`. The walk lowered the loop to `while i < s.len` with no
## assert: `for _ in s: discard s.pop()` reached a target after the loop (a
## clean false `sxSat`) and never one in `except AssertionDefect` (a clean false
## `sxUnsat`). `mitems` / `mpairs` (S8ca) and the Table iterators (S8bl) model
## the assert; `items` and `pairs` now share `mitems`'s (`seqIterLenChanged`),
## with S8cu's decline where the module may compile `assert` out.
##
## `lentLoopDecline` (S8cn) caught a body that names the loop variable over a
## seq of anything but scalars under `pairs`; every row here escaped it.
##
## Each row runs the routine natively (`native`, on this build) beside the
## walk's verdict. `main` at 6cbfe8f answered `sxUnknown`
## (`weInternalWalkerFault`) for every row but `popParam` (`sxSat`, with
## `beBudgetExhausted`); the candidate 523dffe6 answered the verdicts named
## "was" below.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers
import ./w3_fix_assertoff

const declKey = cellKey(faGeneric, "w3_seqiter")

proc popAfter(v: int) =
  if v == 4:
    var s = @[1'i32, 2, 3]
    for _ in s: discard s.pop()
    symexTarget("hit")

proc popExc(v: int) =
  if v == 4:
    var s = @[1'i32, 2, 3]
    try:
      for _ in s: discard s.pop()
    except AssertionDefect:
      symexTarget("hit")

proc delAfter(v: int) =
  if v == 4:
    var s = @[1'i32, 0, 3]
    for i, x in s:
      if x == 0: s.del(i)
    symexTarget("hit")

proc delExc(v: int) =
  if v == 4:
    var s = @[1'i32, 0, 3]
    try:
      for i, x in s:
        if x == 0: s.del(i)
    except AssertionDefect:
      symexTarget("hit")

proc addAfter(v: int) =
  if v == 4:
    var s = @[1'i32, 2]
    for _ in s:
      if s.len < 5: s.add 1
    symexTarget("hit")

proc addExc(v: int) =
  if v == 4:
    var s = @[1'i32, 2]
    try:
      for _ in s:
        if s.len < 5: s.add 1
    except AssertionDefect:
      symexTarget("hit")

proc addForever(v: int) =
  if v == 4:
    var s = @[1'i32]
    for _ in s: s.add 1
    symexTarget("hit")

proc popParam(s0: seq[int32]) =
  var s = s0
  if s.len == 2:
    for _ in s: discard s.pop()
    symexTarget("hit")

proc setLenNamedExc(v: int) =
  if v == 4:
    var s = @[1'i32, 0, 3]
    try:
      for i, x in s:
        if x == 0: s.setLen(1)
    except AssertionDefect:
      symexTarget("hit")

# Controls: a `break` leaves before the assert; a `continue` does not; a body
# that keeps the length, or puts it back, raises nothing.
proc popBreak(v: int) =
  if v == 4:
    var s = @[1'i32, 2, 3]
    for _ in s:
      discard s.pop()
      break
    symexTarget("hit")

proc popContinueExc(v: int) =
  if v == 4:
    var s = @[1'i32, 2, 3]
    try:
      for _ in s:
        discard s.pop()
        if s.len > 0: continue
    except AssertionDefect:
      symexTarget("hit")

proc keepLen(v: int) =
  var s = @[1'i32, 2, 3]
  var n = 0
  for i, x in s:
    s[i] = x + 1
    n += 1
  if v == 4 and n == 3 and s[2] == 4: symexTarget("hit")

proc putBack(v: int) =
  if v == 4:
    var s = @[1'i32, 2, 3]
    for _ in s:
      let y = s.pop()
      s.add y
    symexTarget("hit")

proc popRaise(v: int) =
  if v == 4:
    var s = @[1'i32, 2, 3]
    for _ in s: discard s.pop()

suite "W3 WA-3: items and pairs over a seq whose length changes":

  test "the walker version carries the fix":
    check parseInt(symexWalkerVersion) >= 267

  test "pop under items: AssertionDefect after the first iteration":
    check native(popAfter(4)) == "AssertionDefect"
    decides(popAfter, sxRaised)         # was a clean sxSat
    check native(popExc(4)) == "hit"
    decides(popExc, sxSat)              # was a clean sxUnsat
    check native(popParam(@[1'i32, 2])) == "AssertionDefect"
    decides(popParam, sxRaised)         # was a clean sxSat

  test "del under pairs over scalars":
    check native(delAfter(4)) == "AssertionDefect"
    decides(delAfter, sxRaised)         # was a clean sxSat
    check native(delExc(4)) == "hit"
    decides(delExc, sxSat)              # was a clean sxUnsat
    check native(setLenNamedExc(4)) == "hit"
    decides(setLenNamedExc, sxSat)      # was a clean sxUnsat

  test "add under items: the loop does not chase the new length":
    check native(addAfter(4)) == "AssertionDefect"
    decides(addAfter, sxRaised)         # was a clean sxSat
    check native(addExc(4)) == "hit"
    decides(addExc, sxSat)              # was a clean sxUnsat
    check native(addForever(4)) == "AssertionDefect"
    decides(addForever, sxRaised)       # was beBudgetExhausted

  test "the assert is a raise target":
    check native(popRaise(4)) == "AssertionDefect"
    let r = symexFind(popRaise, tAssertionViolation())
    checkpoint show(r.errors)
    check r.status in {sxSat, sxRaised}  # was a clean sxUnsat

  test "break leaves before the assert, continue does not":
    check native(popBreak(4)) == "hit"
    decides(popBreak, sxSat)
    check native(popContinueExc(4)) == "hit"
    decides(popContinueExc, sxSat)

  test "a body that keeps the length raises nothing":
    check native(keepLen(4)) == "hit"
    decides(keepLen, sxSat)
    check native(putBack(4)) == "hit"
    decides(putBack, sxSat)

  test "a module that may compile assert out declines (S8cu)":
    let nat = native(itemsPopOff(4))
    checkpoint "native " & nat
    check nat in ["IndexDefect", "AssertionDefect"]
    pinDecline(itemsPopOff, declKey, feCheckOption)
    check native(itemsPopOutside(4)) == "AssertionDefect"
    pinDecline(itemsPopOutside, declKey, feCheckOption)
