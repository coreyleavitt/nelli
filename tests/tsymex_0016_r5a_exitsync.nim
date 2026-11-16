## RFC-0016 review R4-1, R5-1 and R5-2. Reconciliation happens only where
## effects are produced: at each leaf statement, at each guard a compound
## statement evaluates itself, and at a `return`'s value before it parks
## (`reconcileCells`). No compound statement is reconciled over its span.
##
## A pass over a compound's span compared effects its statements had already
## synced against a snapshot from before it. In a callee that holds an
## `mpairs` view and its Table, the view and the Table both differ from that
## snapshot (each was synced, statement by statement), so it read as two
## writes in one statement and declined (sxUnknown): a labelled block's
## fall-through (R4-1, red at 1502cad1), a `break` taken after the writes
## (R5-1), the same writes under an `if` or in a loop body a `continue` leaves
## (R5-2; red at 3a808b7e). Every label is checked natively over `xs`.
##
## The guards' effects are still reconciled: each `h*` program leaves a
## labelled block from a condition that writes an address-taken variable by
## name or through its pointer, then reads it both ways; the R5 programs read
## a capture a guard's closure wrote, after an `if`, across `while` tests, and
## in a `finally` after a `return` whose value wrote it.

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

proc wrBrkL(v: var int; t: var Table[string, int]; k: string) =
  block L:
    v = 9
    t.del("zz")
    if k.len > 100: break L

proc sWrBrkL(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      wrBrkL(v, t, k)
      if v == 9 and t[k] == 9: symexTarget("wb_live")
      if v != 9 or t[k] != 9: symexTarget("wb_dead")
  except AssertionDefect:
    discard

proc wrBrkT(v: var int; t: var Table[string, int]; k: string) =
  block L:
    v = 9
    t.del("zz")
    if k.len > 0: break L
    v = 1

proc sWrBrkT(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      wrBrkT(v, t, k)
      if v == 9 and t[k] == 9: symexTarget("wt_live")
      if v != 9 or t[k] != 9: symexTarget("wt_dead")
  except AssertionDefect:
    discard

proc wrDelI(v: var int; t: var Table[string, int]; k: string) =
  if k.len < 100:
    v = 9
    t.del("zz")

proc sWrDelI(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      wrDelI(v, t, k)
      if v == 9 and t[k] == 9: symexTarget("wi_live")
      if v != 9 or t[k] != 9: symexTarget("wi_dead")
  except AssertionDefect:
    discard

suite "R4-1: a labelled block's fall-through is synced by its statements":
  test "a callee removes the view's key inside `block L:`":
    decided(sDelL, "dl_live", sxSat)
    decided(sDelL, "dl_dead", sxUnsat)
    decided(sDelL, "dl_dead2", sxUnsat)
  test "a callee writes the view and removes another key inside `block L:`":
    decided(sWrDelL, "wl_live", sxSat)
    decided(sWrDelL, "wl_dead", sxUnsat)
  test "the same in a loop body a `continue` leaves":
    # R5-2: the enclosing `isWhile` ran a pass over its whole span against a
    # snapshot from before the loop, and read the view's and the Table's
    # synced writes as two writes in one statement. A compound statement
    # runs no pass now: its leaves and its guard evaluations reconcile.
    decided(sWrDelC, "wc_live", sxSat)
    decided(sWrDelC, "wc_dead", sxUnsat)
  test "a callee writes the view and the Table, then breaks out of `block L:`":
    # R5-1: the parked `break` carried effects its statements had synced,
    # and the block's pass compared it against the block-entry snapshot.
    decided(sWrBrkL, "wb_live", sxSat)
    decided(sWrBrkL, "wb_dead", sxUnsat)
    decided(sWrBrkT, "wt_live", sxSat)
    decided(sWrBrkT, "wt_dead", sxUnsat)
  test "a callee writes the view and the Table under an `if`":
    decided(sWrDelI, "wi_live", sxSat)
    decided(sWrDelI, "wi_dead", sxUnsat)

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

# ---- a compound's own evaluations reconcile where they run (R5) ----------

template nsut(nm, rn: untyped; want: int) =
  proc nm(v: int) =
    if v != 1: return
    let r = rn(v)
    if r == want: symexTarget("ok")
    if r != want: symexTarget("bad")

proc rSc(v: int): int =
  var x = v
  proc bump(): bool =
    x = x + 4
    true
  if v > 0 and bump():
    result = x * 10
  result += x
nsut(sSc, rSc, 55)

proc rScP(v: int): int =
  var x = v
  let p = addr x
  proc bump(): bool =
    x = x + 4
    true
  if v > 0 and bump():
    result = p[] * 10
  result += x
nsut(sScP, rScP, 55)

proc rWg(v: int): int =
  var x = v
  var n = 0
  proc bump(): bool =
    x = x + 2
    x < 6
  while bump():
    inc n
  result = x * 10 + n
nsut(sWg, rWg, 72)

proc rWgP(v: int): int =
  var x = v
  let p = addr x
  var n = 0
  proc bump(): bool =
    x = x + 2
    x < 6
  while bump():
    n = n * 10 + p[]
  result = p[] * 100 + n
nsut(sWgP, rWgP, 735)

proc rRetFin(v: int): int =
  var x = v
  let p = addr x
  proc c(): int =
    p[] = 5
    1
  try:
    return c() * 10
  finally:
    result = result + x
nsut(sRetFin, rRetFin, 15)

proc rRetFinCap(v: int): int =
  var x = v
  proc c(): int =
    x = x + 4
    1
  try:
    return c() * 10
  finally:
    result = result + x
nsut(sRetFinCap, rRetFinCap, 15)

proc retThrough(x: var int): int =
  let p = addr x
  proc c(): int =
    p[] = 5
    1
  return c()

proc rRet(v: int): int =
  var y = v
  let r = retThrough(y)
  result = y * 10 + r
nsut(sRet, rRet, 51)

suite "R5: a compound's guard evaluations reconcile where they run":
  test "a short-circuit guard whose closure writes a capture":
    exitVerdict(sSc)
  test "a short-circuit guard whose closure writes an address-taken capture":
    exitVerdict(sScP)
  test "a while guard whose closure writes a capture":
    exitVerdict(sWg)
  test "a while guard whose closure writes an address-taken capture":
    exitVerdict(sWgP)
  test "a `return` whose closure writes a `var` formal through its pointer":
    exitVerdict(sRet)
  test "a `finally` reads what a `return`'s closure wrote through a pointer":
    exitVerdict(sRetFin)
  test "a `finally` reads the capture a `return`'s closure wrote":
    exitVerdict(sRetFinCap)

suite "R5: walker version":
  test "walker version floor (R5-1/R5-2)":
    check symexWalkerVersion.parseInt >= 366
