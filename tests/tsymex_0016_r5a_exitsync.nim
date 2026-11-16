## RFC-0016 review R4-1. A labelled block (a source `block L:`, or a loop body
## a `continue` leaves) reconciles, in its post-statement pass, only the
## survivors that rejoined it from a parked exit (`reconciledHere`), never its
## fall-through, whose statements each synced already.
##
## R3-1 ran the whole pass over every survivor of a labelled block. In a
## callee that holds an `mpairs` view and its Table, the block's pass compared
## the fall-through against a snapshot from before the body: the view and the
## Table both differ from it (each was synced, statement by statement), so it
## read as two writes in one statement and declined (sxUnknown, red at
## 1502cad1). Every label is checked natively over `xs`.
##
## The parked exits are still reconciled: each `h*` program leaves a labelled
## block from a condition that writes an address-taken variable by name or
## through its pointer, then reads it both ways.

import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const xs = [-1, 0, 1, 3, 5, 7, 9, 12, 49, 50, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template decided(fn: typed; lbl: static string; want: typed) =
  ## `fn` over a one-key table: the walker's verdict, every native run's
  ## agreement, and the witness replayed.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == want
    var live = false
    for x in xs:
      if lbl in hits(fn({"a": x}.toTable)): live = true
    check live == (want == sxSat)
    if r.status == sxSat:
      check lbl in hits(fn(r.witness[0]))

template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return

# ---- the fall-through of a labelled block is not reconciled again ----------

proc delL(v: var int; t: var Table[string, int]; k: string) =
  block L:
    if k.len > 100: break L
    t.del(k)

proc sDelL(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      delL(v, t, k)
      if v == 0: symexTarget("dl_live")
      if v == x and x != 0: symexTarget("dl_dead")
      if k in t: symexTarget("dl_dead2")
  except AssertionDefect:
    discard

proc wrDelL(v: var int; t: var Table[string, int]; k: string) =
  block L:
    if k.len > 100: break L
    v = 9
    t.del("zz")

proc sWrDelL(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      wrDelL(v, t, k)
      if v == 9 and t[k] == 9: symexTarget("wl_live")
      if v != 9 or t[k] != 9: symexTarget("wl_dead")
  except AssertionDefect:
    discard

proc wrDelC(v: var int; t: var Table[string, int]; k: string) =
  for i in 0 .. 0:
    if k.len > 100: continue
    v = 9
    t.del("zz")

proc sWrDelC(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      wrDelC(v, t, k)
      if v == 9 and t[k] == 9: symexTarget("wc_live")
      if v != 9 or t[k] != 9: symexTarget("wc_dead")
  except AssertionDefect:
    discard

template loopDeclined(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check "the view and the table were both written in one statement" in
      show(r.errors)

suite "R4-1: a labelled block's fall-through is synced by its statements":
  test "a callee removes the view's key inside `block L:`":
    decided(sDelL, "dl_live", sxSat)
    decided(sDelL, "dl_dead", sxUnsat)
    decided(sDelL, "dl_dead2", sxUnsat)
  test "a callee writes the view and removes another key inside `block L:`":
    decided(sWrDelL, "wl_live", sxSat)
    decided(sWrDelL, "wl_dead", sxUnsat)
  test "the same in a loop body a `continue` leaves: the loop's own pass declines":
    # The body block no longer reconciles its fall-through, but the enclosing
    # loop is an `isWhile`, whose pass spans the whole loop (its guard's
    # effects are its own) and reads the view's and the Table's synced writes
    # as two writes in one statement. So does an `if` around them: a compound
    # statement other than a block, outside this finding. It stays a
    # decline, never a wrong verdict.
    loopDeclined(sWrDelC, "wc_live")
    loopDeclined(sWrDelC, "wc_dead")

# ---- the parked exits of a labelled block are reconciled where they rejoin --

proc wr(q: ptr int; c: int): bool =
  q[] = 5
  c > 0

template hsut(nm, rn: untyped) =
  proc nm(v: int) =
    if v != 1: return
    let r = rn(v)
    if r == 55: symexTarget("ok")
    if r != 55: symexTarget("bad")

proc rH1(v: int): int =
  var x = v
  let p = addr x
  proc bump(): bool =
    p[] = 5
    true
  block L:
    while bump():
      break L
  let a = x
  let b = p[]
  result = a * 10 + b
hsut(sH1, rH1)

proc rH2(v: int): int =
  var x = v
  let p = addr x
  block L:
    while wr(p, v):
      break L
  let a = x
  let b = p[]
  result = a * 10 + b
hsut(sH2, rH2)

proc rH3(v: int): int =
  var x = v
  let p = addr x
  proc bump(): bool =
    x = 5
    true
  block L:
    while bump():
      break L
  let b = p[]
  let a = x
  result = a * 10 + b
hsut(sH3, rH3)

proc rH4(v: int): int =
  var x = v
  let p = addr x
  proc bumpI(): int =
    p[] = 5
    1
  block L:
    case bumpI()
    of 1: break L
    else: discard
    x = 1
  let a = x
  let b = p[]
  result = a * 10 + b
hsut(sH4, rH4)

proc rH5(v: int): int =
  var x = v
  let p = addr x
  for i in 0 .. 0:
    if v > 0 and wr(p, v): continue
    x = 1
  let a = x
  let b = p[]
  result = a * 10 + b
hsut(sH5, rH5)

proc rH6(v: int): int =
  var x = v
  let p = addr x
  proc bump(): bool =
    x = 5
    true
  block L:
    if v < 0 or bump(): break L
    x = 1
  let b = p[]
  let a = x
  result = a * 10 + b
hsut(sH6, rH6)

template exitVerdict(fn: typed) =
  block:
    check "ok" in hits(fn(1))
    let ok = symexFind(fn, tLabel("ok"))
    checkpoint "ok " & $ok.status & "\n" & show(ok.errors)
    check ok.status == sxSat
    let bad = symexFind(fn, tLabel("bad"))
    checkpoint "bad " & $bad.status & "\n" & show(bad.errors)
    check bad.status == sxUnsat

suite "R4-1: a parked exit is reconciled where it rejoins":
  test "break L from a while guard whose closure writes through the pointer":
    exitVerdict(sH1)
  test "break L from a while guard whose call writes through the pointer":
    exitVerdict(sH2)
  test "break L from a while guard whose closure writes by name":
    exitVerdict(sH3)
  test "break L from a case whose discriminator writes through the pointer":
    exitVerdict(sH4)
  test "continue from a short-circuit condition writing through the pointer":
    exitVerdict(sH5)
  test "break L from a short-circuit `or` whose closure writes by name":
    exitVerdict(sH6)

suite "R4-1: walker version":
  test "walker version floor (R4-1)":
    check symexWalkerVersion.parseInt >= 365
