## RFC-0005 (soundness channels) slice S8bx, item 3 -- an `mpairs` view
## passed to one call together with its Table.
##
## `for k, v in t.mpairs` yields `var V`: `v` IS the slot of `t` at `k`.
## S8bl bound `v` to the value and stored `t[k] = v` after every statement
## that writes it, which is exact between statements. A call receiving both
## `v` and `t` (`f(v, t, k)`) got two copies of the one location: the callee
## read `t` without the write it made through `v`, and `v` without its write
## through `t`, and the copy-out of `v` overwrote the callee's table write.
## Verdicts swapped against native runs (a live label `sxUnsat`, a dead one
## `sxSat`): SOUNDNESS, not the PRECISION gap S8bl reported.
##
## The parser marks such a call (`IRStmt.cViewAliases`), and the walker keeps
## the two formals equal statement by statement in the callee
## (`syncViewAliases`), carrying the pair into a callee they are passed on
## to. Every live / dead pair below was checked against a native run (the
## values in each SUT's comment). This is the local model of what S8bs's
## address cells do for `addr`-taken variables (`bindVarLocs`), which this
## base does not have; see the RFC's "As landed (S8bx)" for the
## reconciliation.
import std/[unittest, strutils, tables]
import nelli
import nelli/symex

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

type Box = object
  tab: Table[string, int]
  n: int

proc readAfterBump(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]

proc writeTabReadV(v: var int; t: var Table[string, int]; k: string): int =
  t[k] = 50
  v

proc writeBoth(v: var int; t: var Table[string, int]; k: string) =
  v = 7
  t[k] = t[k] + 100

proc byValView(v: int; t: var Table[string, int]; k: string): int =
  t[k] = 50
  v

proc nested(v: var int; t: var Table[string, int]; k: string): int =
  result = readAfterBump(v, t, k)

proc readBox(v: var int; b: Box): int =
  v += 1
  b.tab["a"]

# Native, t = {"a": 5}: readAfterBump returns 6 (the callee reads its own
# write through `v`).
proc sBump(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  for k, v in t.mpairs:
    let r = readAfterBump(v, t, k)
    if r == x + 1: symexTarget("bump_live")
    if r == x: symexTarget("bump_dead")

# Native: returns 50 (the view reads the callee's table write), t["a"] 50.
proc sTabWrite(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  for k, v in t.mpairs:
    let r = writeTabReadV(v, t, k)
    if r == 50 and t["a"] == 50: symexTarget("tabw_live")
    if r == x and x != 50: symexTarget("tabw_dead")

# Native: t["a"] == 107 (the table write reads the view's write).
proc sBoth(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  for k, v in t.mpairs:
    writeBoth(v, t, k)
    if t["a"] == 107: symexTarget("both_live")
    if t["a"] == 7 or (t["a"] == x + 100 and x != 7): symexTarget("both_dead")

# Native: a by-value `int` view is a copy: returns 5, t["a"] 50.
proc sByVal(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  for k, v in t.mpairs:
    let r = byValView(v, t, k)
    if r == x and t["a"] == 50: symexTarget("byval_live")
    if r == 50 and x != 50: symexTarget("byval_dead")

# Native: the pair passed on from a callee: returns 6.
proc sNested(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  for k, v in t.mpairs:
    let r = nested(v, t, k)
    if r == x + 1: symexTarget("nested_live")
    if r == x: symexTarget("nested_dead")

# Native: over a field path, returns 6.
proc sField(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var b = Box(tab: t0, n: 0)
  for k, v in b.tab.mpairs:
    let r = readAfterBump(v, b.tab, k)
    if r == x + 1: symexTarget("field_live")
    if r == x: symexTarget("field_dead")

# Native: `mvalues`, returns 6.
proc sValues(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  for v in t.mvalues:
    let r = readAfterBump(v, t, "a")
    if r == x + 1: symexTarget("values_live")
    if r == x: symexTarget("values_dead")

# The object holding the Table, passed with the view: declines.
proc sHolder(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var b = Box(tab: t0, n: 0)
  for k, v in b.tab.mpairs:
    let r = readBox(v, b)
    if r == x: symexTarget("holder_dead")

suite "S8bx (3): an mpairs view and its Table in one call":

  test "the callee reads the table after a write through the view":
    let r = symexFind(sBump, tLabel("bump_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(sBump(r.witness[0]), "bump_live")
    let d = symexFind(sBump, tLabel("bump_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "the view reads a write through the table":
    let r = symexFind(sTabWrite, tLabel("tabw_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(sTabWrite(r.witness[0]), "tabw_live")
    let d = symexFind(sTabWrite, tLabel("tabw_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "writes through both, in order":
    let r = symexFind(sBoth, tLabel("both_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(sBoth(r.witness[0]), "both_live")
    let d = symexFind(sBoth, tLabel("both_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a by-value scalar view is a copy":
    let r = symexFind(sByVal, tLabel("byval_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(sByVal(r.witness[0]), "byval_live")
    let d = symexFind(sByVal, tLabel("byval_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "the pair passed on by the callee":
    let r = symexFind(sNested, tLabel("nested_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(sNested(r.witness[0]), "nested_live")
    let d = symexFind(sNested, tLabel("nested_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a Table reached through a field path":
    let r = symexFind(sField, tLabel("field_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(sField(r.witness[0]), "field_live")
    let d = symexFind(sField, tLabel("field_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "mvalues":
    let r = symexFind(sValues, tLabel("values_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(sValues(r.witness[0]), "values_live")
    let d = symexFind(sValues, tLabel("values_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "the object holding the Table, passed with the view, declines":
    let d = symexFind(sHolder, tLabel("holder_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnknown
    check hasKind(d.errors, feUnsupportedOp)
