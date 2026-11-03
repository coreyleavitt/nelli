## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part b: array-element insert, newSeq, mgetOrPut and inc / dec / += on an element
## (items 4, 5, 7).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_b`, `tsymex_rfc0005_s8bc_remainder_b2`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 74 s).

import std/[unittest, strutils, sequtils, tables, sets, hashes]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

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

# ---- (4) insert on an array element ------------------------------------------
#
# RFC-0005 S8bc: `a[i].insert(x, j)` takes the bare arm's two phases (S8ar):
# grow, write back, then place on the grown element. It fell to the generic
# call (`system.insert` inlined to an unsupported `when`).

type AIHold = object
  a: array[2, seq[int]]

# ---- (7) mgetOrPut, and inc / dec / += on an element ----------------------
#
# RFC-0005 S8bc: `mgetOrPut(t, k, d)` is a get-or-insert whose result is a
# reference to the cell; its writers (`.add`, `+=`, `inc`, `=`) write back
# through `t[k]`. Found en route (SOUNDNESS): `inc`/`dec` on any receiver
# but a bare int variable walked the bodiless `{.magic.}` as an empty body,
# dropping the write with no record -- a clean, wrong sxSat. Also: an empty
# `@[]` passed as a `seq[T]` argument was built over the unbacked sort (a
# walker fault on the first store).

proc mgAdd(k, v: int) =
  var t = initTable[int, seq[int]]()
  t.mgetOrPut(k, @[]).add v
  t.mgetOrPut(k, @[]).add 4
  if t[k].len == 2 and t[k][0] == 9 and t[k][1] == 4: symexTarget("mg_add")
  if t[k].len != 2 or t.len != 1: symexTarget("mg_add_dead")

proc mgCount(a, b: int) =
  var t = initTable[int, int]()
  let xs = [a, b]   # (`for x in [a, b]` is a walker fault: reported, not fixed here)
  for x in xs:
    inc t.mgetOrPut(x, 0)
  t.mgetOrPut(a, 0) += 10
  if t[b] == 12: symexTarget("mg_count")
  if t[a] == 11 and a == b: symexTarget("mg_count_dead")

proc mgRead(k: int) =
  var t = initTable[int, int]()
  t[1] = 7
  let x = t.mgetOrPut(k, 5)
  if x == 7 and t.len == 1: symexTarget("mg_read_hit")
  if x == 5 and t.len == 2 and t[k] == 5: symexTarget("mg_read_miss")
  if x == 5 and t.len == 1: symexTarget("mg_read_dead")

proc mgAsg(k: int) =
  var t = initTable[int, int]()
  t.mgetOrPut(k, 3) = 8
  if t[k] == 8 and k == 6 and t.len == 1: symexTarget("mg_asg")
  if t[k] == 3: symexTarget("mg_asg_dead")

type IncObj = object
  f: int

proc incDropped(k: int) =
  var t = initTable[int, int]()
  t[k] = 1
  inc t[k]
  var a: array[3, int]
  inc a[1], 2
  var o = IncObj(f: 1)
  dec o.f
  var s = @[1, 2]
  dec s[1]
  if t[k] == 2 and a[1] == 2 and o.f == 0 and s[1] == 1 and k == 3:
    symexTarget("inc_ok")
  if t[k] == 1 or a[1] == 0 or o.f == 1 or s[1] == 2:
    symexTarget("inc_dropped")

proc incRanged(k: int) =
  var a: array[2, range[0 .. 5]]
  inc a[0]
  if k == 1: symexTarget("inc_ranged")

proc augAbsent(k: int) =
  var t = initTable[int, int]()
  t[1] = 1
  try:
    t[k] += 1
    if t[k] == 2: symexTarget("aug_present")
  except KeyError:
    symexTarget("aug_absent")

proc emptyArg(k: int) =
  var t = initTable[int, seq[int]]()
  t[k] = @[]
  t[k].add 3
  let g = t.getOrDefault(k + 1, @[])
  if t[k][0] == 3 and g.len == 0 and k == 1: symexTarget("empty_arg")

suite "S8bc (7): mgetOrPut":
  test "mgetOrPut(...).add":
    let r = symexFind(mgAdd, tLabel("mg_add"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == 9
      check reproduces(mgAdd(r.witness[0], r.witness[1]), "mg_add")
    let d = symexFind(mgAdd, tLabel("mg_add_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "inc and += through mgetOrPut: the counting idiom":
    let r = symexFind(mgCount, tLabel("mg_count"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == r.witness[1]
      check reproduces(mgCount(r.witness[0], r.witness[1]), "mg_count")
    let d = symexFind(mgCount, tLabel("mg_count_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "mgetOrPut read: a present key, and an inserted one":
    let h = symexFind(mgRead, tLabel("mg_read_hit"))
    checkpoint $h.status & " " & show(h.errors)
    check h.status == sxSat
    if h.status == sxSat:
      check h.witness[0] == 1
      check reproduces(mgRead(h.witness[0]), "mg_read_hit")
    let m = symexFind(mgRead, tLabel("mg_read_miss"))
    checkpoint $m.status & " " & show(m.errors)
    check m.status == sxSat
    if m.status == sxSat:
      check m.witness[0] != 1
      check reproduces(mgRead(m.witness[0]), "mg_read_miss")
    let d = symexFind(mgRead, tLabel("mg_read_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "mgetOrPut(...) = v":
    let r = symexFind(mgAsg, tLabel("mg_asg"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(mgAsg(r.witness[0]), "mg_asg")
    let d = symexFind(mgAsg, tLabel("mg_asg_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "inc / dec on an element or a field is no longer dropped":
    # Was sxSat with no errors for `inc_dropped` (the write dropped).
    let r = symexFind(incDropped, tLabel("inc_ok"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(incDropped(r.witness[0]), "inc_ok")
    let d = symexFind(incDropped, tLabel("inc_dropped"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "inc on a ranged element declines, never the silent no-op":
    let r = symexFind(incRanged, tLabel("inc_ranged"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.anyIt(it.kind == feUnsupportedOp and "`inc`" in it.msg)

  test "t[k] += v raises KeyError for an absent key":
    let a = symexFind(augAbsent, tLabel("aug_absent"))
    checkpoint $a.status & " " & show(a.errors)
    check a.status == sxSat
    if a.status == sxSat:
      check a.witness[0] != 1
      check reproduces(augAbsent(a.witness[0]), "aug_absent")
    let p = symexFind(augAbsent, tLabel("aug_present"))
    checkpoint $p.status & " " & show(p.errors)
    check p.status == sxSat
    if p.status == sxSat: check reproduces(augAbsent(p.witness[0]), "aug_present")

  test "an empty @[] argument is a seq of the parameter's element":
    let r = symexFind(emptyArg, tLabel("empty_arg"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat: check reproduces(emptyArg(r.witness[0]), "empty_arg")
