## RFC-0005 slice S8cn, items 3 and 4 -- an `mpairs` view and its Table.
##
## In Nim `v` IS the slot, so a callee holding both formals has one location.
## S8bx kept the two equal statement by statement, and declined where a write
## might remove the key, where both were written in one statement, and where
## the object holding the Table came instead of the Table. Batch 8 declined
## every key removed under a live view. Each is decided here where Nim's own
## behaviour is defined (every label is checked natively over `xs`); what stays
## declined says why, and has a native run that shows the hash dependence.
##
## A one-entry table's only entry is in its home slot: `delImplIdx` empties it
## and backshifts the cluster, and an insert probes from the home slot.
##
## RFC-0005 S8cm: six parts, by `s8cnViewsPart` (`_b` to `_f` set 1 to 5), so
## that each file compiles and runs in under 60 s on the Windows legs where it
## can: part 0 took 123 s there, part 1 84 s. Part 2's first test alone runs
## 80 to 103 s on Windows.
import std/[unittest, strutils, tables]
when not declared(s8cnViewsPart):
  const s8cnViewsPart = 0

import nelli/symex

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
    if want == sxUnsat: check not live
    if r.status == sxSat:
      check lbl in hits(fn(r.witness[0]))

template declined(fn: typed; lbl: static string; why: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check why in show(r.errors)

template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return

# ---- (3) The table written at a key whose presence is not literal ------------

proc wrOther(v: var int; t: var Table[string, int]; j: string): int =
  t[j] = 50
  v

proc sOther(t0: Table[string, int]; j: string) =
  guardT()
  var t = t0
  try:   # a new key changes the length: the iterator's assert, past the body
    for k, v in t.mpairs:
      let r = wrOther(v, t, j)
      if j == "a" and r == 50: symexTarget("nl_same_live")
      if j != "a" and r == x and t[j] == 50: symexTarget("nl_other_live")
      if j == "a" and r == x and x != 50: symexTarget("nl_same_dead")
      if j != "a" and r == 50 and x != 50: symexTarget("nl_other_dead")
  except AssertionDefect:
    discard

proc wrRead(v: var int; t: var Table[string, int]; j: string): int =
  t[j] = v + 1
  v = v + 2
  if j == "a": t[j] else: v

proc sOther2(t0: Table[string, int]; j: string) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      let r = wrRead(v, t, j)
      if j == "a" and r == x + 3: symexTarget("nl2_same_live")
      if j != "a" and r == x + 2: symexTarget("nl2_other_live")
      if j == "a" and r == x + 1: symexTarget("nl2_same_dead")
  except AssertionDefect:
    discard

# ---- (3) Both written in one statement ----------------------------------------

proc wv(v: var int): int =
  v = 3
  9

proc wrTab(t: var Table[string, int]; k: string): int =
  t[k] = 3
  9

proc tabLast(v: var int; t: var Table[string, int]; k: string): int =
  t[k] = wv(v)     # Nim: the value first, then the store
  v

proc sTabLast(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    let r = tabLast(v, t, k)
    if r == 9 and t["a"] == 9: symexTarget("tl_live")
    if r == 3: symexTarget("tl_dead")

proc viewLast(v: var int; t: var Table[string, int]; k: string): int =
  v = wrTab(t, k)
  t[k]

proc sViewLast(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    let r = viewLast(v, t, k)
    if r == 9 and t["a"] == 9: symexTarget("vl_live")
    if r == 3: symexTarget("vl_dead")

proc twoCalls(v: var int; t: var Table[string, int]; k: string): int =
  # Each call writes the location, in the expression's order: 9 + 9, and the
  # second call's 3 stands. (Hoisted, each is its own statement.)
  result = wv(v) + wrTab(t, k)
  v = v + result

proc sTwoCalls(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    let r = twoCalls(v, t, k)
    if r == 18 and t["a"] == 21: symexTarget("two_live")
    if r != 18: symexTarget("two_dead")

# ---- (3) The object holding the Table ----------------------------------------

type Box = object
  tab: Table[string, int]
  n: int

proc readBox(v: var int; b: Box): int =
  v += 1
  b.tab["a"]

proc writeBox(v: var int; b: var Box): int =
  b.tab["a"] = 50
  v

proc passOn(v: var int; b: var Box): int =
  writeBox(v, b) + 1

proc passOnTab(v: var int; b: var Box): int =
  wrOther(v, b.tab, "a")

proc sReadBox(t0: Table[string, int]) =
  guardT()
  var b = Box(tab: t0, n: 0)
  for k, v in b.tab.mpairs:
    let r = readBox(v, b)
    if r == x + 1: symexTarget("hr_live")
    if r == x: symexTarget("hr_dead")

proc sWriteBox(t0: Table[string, int]) =
  guardT()
  var b = Box(tab: t0, n: 0)
  for k, v in b.tab.mpairs:
    let r = writeBox(v, b)
    if r == 50: symexTarget("hw_live")
    if r == x and x != 50: symexTarget("hw_dead")

proc sPassOn(t0: Table[string, int]) =
  guardT()
  var b = Box(tab: t0, n: 0)
  for k, v in b.tab.mpairs:
    let r = passOn(v, b)
    if r == 51: symexTarget("ho_live")
    if r == x + 1 and x != 50: symexTarget("ho_dead")

proc sPassOnTab(t0: Table[string, int]) =
  guardT()
  var b = Box(tab: t0, n: 0)
  for k, v in b.tab.mpairs:
    let r = passOnTab(v, b)
    if r == 50: symexTarget("ht_live")
    if r == x and x != 50: symexTarget("ht_dead")

# ---- (3) A pointer to the view -----------------------------------------------

type Hold = object
  w: ptr int

proc viaPtr(h: Hold; t: var Table[string, int]; k: string): int =
  h.w[] += 1
  t[k]

proc sHoldPtr(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    let r = viaPtr(Hold(w: addr v), t, k)
    if r == x + 1: symexTarget("hp_live")
    if r == x: symexTarget("hp_dead")

proc sBodyPtr(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    let p = addr v
    p[] = x + 2
    if t[k] == x + 2: symexTarget("bp_live")
    if t[k] == x: symexTarget("bp_dead")
    t[k] = x + 4
    if p[] == x + 4: symexTarget("bq_live")
    if p[] == x + 2: symexTarget("bq_dead")

# ---- (4) A key removed under a live view -------------------------------------

proc sRemOwn(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      t.del(k)
      if v == 0: symexTarget("ro_live")
      if v == x and x != 0: symexTarget("ro_dead")
      if t.len == 0: symexTarget("ro_empty")
  except AssertionDefect:
    symexTarget("ro_assert")

proc sRemOwnReadd(t0: Table[string, int]) =
  guardT()
  var t = t0
  var n = 0
  for k, v in t.mpairs:
    inc n
    t.del(k)
    t[k] = 7
    if v == 7: symexTarget("rr_live")
    if v == x and x != 7: symexTarget("rr_dead")
    if v == 0: symexTarget("rr_dead2")
  if n == 1: symexTarget("rr_once")
  if n != 1: symexTarget("rr_twice_dead")

proc sRemAbsent(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    t.del("zz")
    if v == x: symexTarget("ra_live")
    if v != x: symexTarget("ra_dead")

proc sRemSym(t0: Table[string, int]; j: string) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      t.del(j)
      if j != "a" and v == x: symexTarget("rs_absent_live")
      if j == "a" and v == 0: symexTarget("rs_own_live")
      if j != "a" and v != x: symexTarget("rs_absent_dead")
      if j == "a" and v == x and x != 0: symexTarget("rs_own_dead")
  except AssertionDefect:
    discard

proc sWriteAfterDel(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      t.del(k)
      v = 9
      if k notin t and v == 9: symexTarget("wd_live")
      if k in t: symexTarget("wd_dead")
      t.del("zz")
      if v == 9: symexTarget("wd2_live")
      if v == 0: symexTarget("wd2_dead")
  except AssertionDefect:
    discard

proc delIt(v: var int; t: var Table[string, int]; k: string) =
  t.del(k)

proc sRemCallee(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      delIt(v, t, k)
      if v == 0: symexTarget("rc_live")
      if v == x and x != 0: symexTarget("rc_dead")
      if k in t: symexTarget("rc_dead2")
  except AssertionDefect:
    discard

proc delRead(v: var int; t: var Table[string, int]; k: string): int =
  t.del(k)
  v

proc sRemCallee2(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      let r = delRead(v, t, k)
      if r == 0: symexTarget("rd_live")
      if r == x and x != 0: symexTarget("rd_dead")
  except AssertionDefect:
    discard

proc delWrite(v: var int; t: var Table[string, int]; k: string): int =
  t.del(k)
  v = 9
  if k in t: return 1
  v

proc sRemCallee3(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      let r = delWrite(v, t, k)
      if r == 9 and k notin t: symexTarget("rw_live")
      if r == 1: symexTarget("rw_dead")
      if k in t: symexTarget("rw_dead2")
  except AssertionDefect:
    discard

proc delReadd(v: var int; t: var Table[string, int]; k: string): int =
  t.del(k)
  t[k] = 7
  v

proc sRemCallee4(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    let r = delReadd(v, t, k)
    if r == 7 and v == 7: symexTarget("ra2_live")
    if r == 0: symexTarget("ra2_dead")

proc delSym(v: var int; t: var Table[string, int]; j: string): int =
  t.del(j)
  v

proc sRemCalleeSym(t0: Table[string, int]; j: string) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      let r = delSym(v, t, j)
      if j != "a" and r == x: symexTarget("rj_absent_live")
      if j == "a" and r == 0: symexTarget("rj_own_live")
      if j != "a" and r != x: symexTarget("rj_absent_dead")
      if j == "a" and r == x and x != 0: symexTarget("rj_own_dead")
  except AssertionDefect:
    discard

# Hash-dependent: del, then another key. The new key's home slot is the view's
# or it is not. `hashDep` shows both happen among short keys.
proc viewAfterOtherKey(k2: string): int =
  var t = {"a": 5}.toTable
  for k, v in t.mpairs:
    t.del(k)
    t[k2] = 1
    return v

proc sRemAdd(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    t.del(k)
    t["b"] = 1
    if v == 0 or v == 1: symexTarget("rb_hash")
    break

proc delAdd(v: var int; t: var Table[string, int]; k: string): int =
  t.del(k)
  t["b"] = 1
  v

proc sRemAddCallee(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    let r = delAdd(v, t, k)
    if r == 0 or r == 1: symexTarget("rb2_hash")
    break

proc sRemTwo(t0: Table[string, int]) =
  if t0.len != 2: return
  var t = t0
  for k, v in t.mpairs:
    t.del(k)
    if v == 0: symexTarget("r2_zero")
    break

when s8cnViewsPart == 0:
  suite "S8cn (3): the callee's table write at a non-literal key":
    test "the view reads the write at its own key, and only there":
      let r = symexFind(sOther, tLabel("nl_same_live"))
      checkpoint show(r.errors)
      check r.status == sxSat
      let o = symexFind(sOther, tLabel("nl_other_live"))
      checkpoint show(o.errors)
      check o.status == sxSat
      check symexFind(sOther, tLabel("nl_same_dead")).status == sxUnsat
      check symexFind(sOther, tLabel("nl_other_dead")).status == sxUnsat
      check "nl_same_live" in hits(sOther({"a": 5}.toTable, "a"))
      check "nl_other_live" in hits(sOther({"a": 5}.toTable, "q"))
      check "nl_same_dead" notin hits(sOther({"a": 5}.toTable, "a"))
      check "nl_other_dead" notin hits(sOther({"a": 5}.toTable, "q"))

  suite "S8cn (3): both written in one statement":
    test "the table's store is the statement's last effect":
      decided(sTabLast, "tl_live", sxSat)
      decided(sTabLast, "tl_dead", sxUnsat)
    test "the view's assignment is":
      decided(sViewLast, "vl_live", sxSat)
      decided(sViewLast, "vl_dead", sxUnsat)
    test "two calls in one expression":
      decided(sTwoCalls, "two_live", sxSat)
      decided(sTwoCalls, "two_dead", sxUnsat)


when s8cnViewsPart == 1:
  suite "S8cn (4): a key removed under a live view":
    test "its own key, from a one-entry table: the slot reads zero":
      decided(sRemOwn, "ro_live", sxSat)
      decided(sRemOwn, "ro_empty", sxSat)
      decided(sRemOwn, "ro_assert", sxSat)
      decided(sRemOwn, "ro_dead", sxUnsat)
    test "its own key put back: the same slot":
      decided(sRemOwnReadd, "rr_live", sxSat)
      decided(sRemOwnReadd, "rr_once", sxSat)
      decided(sRemOwnReadd, "rr_dead", sxUnsat)
      decided(sRemOwnReadd, "rr_dead2", sxUnsat)
      decided(sRemOwnReadd, "rr_twice_dead", sxUnsat)
    test "an absent key: nothing happens":
      decided(sRemAbsent, "ra_live", sxSat)
      decided(sRemAbsent, "ra_dead", sxUnsat)
    test "a symbolic key: either":
      check symexFind(sRemSym, tLabel("rs_absent_live")).status == sxSat
      check symexFind(sRemSym, tLabel("rs_own_live")).status == sxSat
      check symexFind(sRemSym, tLabel("rs_absent_dead")).status == sxUnsat
      check symexFind(sRemSym, tLabel("rs_own_dead")).status == sxUnsat
      check "rs_absent_live" in hits(sRemSym({"a": 5}.toTable, "q"))
      check "rs_own_live" in hits(sRemSym({"a": 5}.toTable, "a"))
      check "rs_absent_dead" notin hits(sRemSym({"a": 5}.toTable, "q"))
      check "rs_own_dead" notin hits(sRemSym({"a": 5}.toTable, "a"))
    test "a write to the emptied slot does not put the key back":
      decided(sWriteAfterDel, "wd_live", sxSat)
      decided(sWriteAfterDel, "wd2_live", sxSat)
      decided(sWriteAfterDel, "wd_dead", sxUnsat)
      decided(sWriteAfterDel, "wd2_dead", sxUnsat)


when s8cnViewsPart == 2:
  suite "S8cn (4): a key removed under a live view":
    test "the callee removes a symbolic key":
      check symexFind(sRemCalleeSym, tLabel("rj_absent_live")).status == sxSat
      check symexFind(sRemCalleeSym, tLabel("rj_own_live")).status == sxSat
      check symexFind(sRemCalleeSym, tLabel("rj_absent_dead")).status == sxUnsat
      check symexFind(sRemCalleeSym, tLabel("rj_own_dead")).status == sxUnsat

    test "another key after it: the slot depends on the hash, so it declines":
      var zero, one = false
      for c in 'a' .. 'z':
        for d in 'a' .. 'z':
          let r = viewAfterOtherKey($c & $d)
          if r == 0: zero = true
          if r == 1: one = true
      # Both happen among two-letter keys: the view reads the new value, or 0.
      check zero and one
      declined(sRemAdd, "rb_hash", "del")
      declined(sRemAddCallee, "rb2_hash", "removed")
    test "two entries: `del`'s backshift depends on the hashes, so it declines":
      declined(sRemTwo, "r2_zero", "del")

when s8cnViewsPart == 3:
  suite "S8cn (3): the callee's table write at a non-literal key":
    test "writes both ways":
      check symexFind(sOther2, tLabel("nl2_same_live")).status == sxSat
      # A new key, and the view written past it: a rehash may lose the write.
      check symexFind(sOther2, tLabel("nl2_other_live")).status == sxUnknown
      # The other arm's decline covers the query too.
      check symexFind(sOther2, tLabel("nl2_same_dead")).status == sxUnknown
      check "nl2_same_live" in hits(sOther2({"a": 5}.toTable, "a"))
      check "nl2_other_live" in hits(sOther2({"a": 5}.toTable, "q"))
      check "nl2_same_dead" notin hits(sOther2({"a": 5}.toTable, "a"))


when s8cnViewsPart == 4:
  suite "S8cn (3): the object holding the Table":
    test "a read through the holder":
      decided(sReadBox, "hr_live", sxSat)
      decided(sReadBox, "hr_dead", sxUnsat)
    test "a write through the holder":
      decided(sWriteBox, "hw_live", sxSat)
      decided(sWriteBox, "hw_dead", sxUnsat)
    test "the holder passed on":
      decided(sPassOn, "ho_live", sxSat)
      decided(sPassOn, "ho_dead", sxUnsat)
    test "the holder's Table passed on":
      decided(sPassOnTab, "ht_live", sxSat)
      decided(sPassOnTab, "ht_dead", sxUnsat)

  suite "S8cn (3): a pointer to the view (was a false verdict both ways)":
    test "in the body":
      decided(sBodyPtr, "bp_live", sxSat)
      decided(sBodyPtr, "bp_dead", sxUnsat)
      decided(sBodyPtr, "bq_live", sxSat)
      decided(sBodyPtr, "bq_dead", sxUnsat)
    test "carried into a callee that reaches the Table":
      check "hp_live" in hits(sHoldPtr({"a": 5}.toTable))
      check "hp_dead" notin hits(sHoldPtr({"a": 5}.toTable))
      declined(sHoldPtr, "hp_live", "pointer")
      declined(sHoldPtr, "hp_dead", "pointer")


when s8cnViewsPart == 5:
  import std/os
  import nelli/smt/runtime

  proc tailUnitLines(log: string): seq[int] =
    ## The units of each tail walk (`k10b-tail` lines of the K7 units log).
    for line in readFile(log).splitLines:
      let f = line.split('\t')
      if f.len >= 2 and f[1] == "k10b-tail": result.add parseInt(f[0])

  suite "S8cn (4): the live witness's tail walk":
    # RFC-0016 W3-z int6. The tail walk forks a branch the pins leave open
    # (`__tabKeys`, the iteration's key slot, is not pinned). An arm the run
    # did not take then asked every later branch with both sides UNSAT, read
    # that as open, and forked both ways again: 1,379 branch asks (948 both
    # UNSAT) and 43 s for this tail alone, where main's whole check took 5 s,
    # and the file passed the Windows legs' 240 s bound (killed on mingw). A path the pins
    # contradict is not the run and is no longer followed.
    test "walker 353: a tail walk does not follow a path the pins contradict":
      check parseInt(symexWalkerVersion) >= 353
      let log = getTempDir() / ("s8cn_rc_live_units_" & $getCurrentProcessId() & ".log")
      removeFile(log)
      putEnv(walkUnitsLogEnv, log)
      let r = try: symexFind(sRemCallee, tLabel("rc_live"))
              finally: delEnv(walkUnitsLogEnv)
      checkpoint $r.status & "\n" & show(r.errors)
      check r.status == sxSat
      let tails = if fileExists(log): tailUnitLines(log) else: @[]
      removeFile(log)
      checkpoint "tail walk units: " & $tails
      check tails.len > 0
      # Red at 52dc9769: one tail of 43,054,950 units, past two whole
      # `concreteBranchRLimit`s of cheap asks. Green: 509,854.
      for u in tails:
        check u < int(concreteBranchRLimit(defaultSymexSettings())) div 10

  suite "S8cn (4): a key removed under a live view":
    test "removed by the callee, seen in the body":
      decided(sRemCallee, "rc_live", sxSat)
      decided(sRemCallee, "rc_dead", sxUnsat)
      decided(sRemCallee, "rc_dead2", sxUnsat)
    test "removed by the callee, seen in the callee":
      decided(sRemCallee2, "rd_live", sxSat)
      decided(sRemCallee2, "rd_dead", sxUnsat)
    test "the callee writes the emptied slot":
      decided(sRemCallee3, "rw_live", sxSat)
      decided(sRemCallee3, "rw_dead", sxUnsat)
      decided(sRemCallee3, "rw_dead2", sxUnsat)
    test "the callee puts it back":
      decided(sRemCallee4, "ra2_live", sxSat)
      decided(sRemCallee4, "ra2_dead", sxUnsat)
