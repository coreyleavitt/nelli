## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part b: array-element insert, newSeq, mgetOrPut and inc / dec / += on an element
## (items 4, 5, 7).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
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

template replays(call: untyped; label: string) =
  ## The witness is typed (the parameter was not demoted) and replays.
  when compiles(call):
    check reproduces(call, label)
  else:
    checkpoint "the witness of `" & astToStr(call) & "` is not typed"
    check false

# ---- (4) insert on an array element ------------------------------------------
#
# RFC-0005 S8bc: `a[i].insert(x, j)` takes the bare arm's two phases (S8ar):
# grow, write back, then place on the grown element. It fell to the generic
# call (`system.insert` inlined to an unsupported `when`).

type AIHold = object
  a: array[2, seq[int]]

proc aiMid(v: int, j: int) =
  if j < 0 or j > 2: return
  var a: array[2, seq[int]]
  a[1] = @[5, 6]
  a[1].insert(v, j)
  if a[1].len == 3 and a[1][1] == v and a[1][0] == 5 and a[1][2] == 6:
    symexTarget("ai_mid")
  if a[1].len != 3: symexTarget("ai_mid_dead")
  if a[0].len != 0: symexTarget("ai_other_dead")

proc aiRange(j: int) =
  var a: array[2, seq[int]]
  a[0] = @[1, 2]
  try:
    a[0].insert(9, j)
  except RangeDefect:
    if a[0].len == 2: symexTarget("ai_range")
  except IndexDefect:
    if a[0].len == 3 and a[0][2] == 0: symexTarget("ai_index_grown")
    if a[0].len != 3: symexTarget("ai_index_dead")

proc aiField(h: AIHold, v: int) =
  var g = h
  let n0 = g.a[0].len
  g.a[0].insert(v, 0)
  if g.a[0].len == n0 + 1 and g.a[0][0] == v and n0 == 1 and g.a[0][1] == 4:
    symexTarget("ai_field")
  if g.a[0].len != n0 + 1: symexTarget("ai_field_dead")

proc aiTab(t: Table[string, seq[int]], v: int) =
  var u = t
  if "k" in u:
    u["k"].insert(v, 0)
    if u["k"][0] == v and u["k"].len == 2 and u["k"][1] == 3:
      symexTarget("ai_tab")

suite "S8bc (4): insert on an array element":
  test "insert in the middle of an array element":
    let r = symexFind(aiMid, tLabel("ai_mid"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == 1
      check reproduces(aiMid(r.witness[0], r.witness[1]), "ai_mid")
    let d = symexFind(aiMid, tLabel("ai_mid_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let o = symexFind(aiMid, tLabel("ai_other_dead"))
    checkpoint $o.status & " " & show(o.errors)
    check o.status == sxUnsat

  test "RangeDefect before any change, IndexDefect after the grow":
    let r = symexFind(aiRange, tLabel("ai_range"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(aiRange(r.witness[0]), "ai_range")
    let g = symexFind(aiRange, tLabel("ai_index_grown"))
    checkpoint $g.status & " " & show(g.errors)
    check g.status == sxSat
    if g.status == sxSat:
      check g.witness[0] > 2
      check reproduces(aiRange(g.witness[0]), "ai_index_grown")
    let d = symexFind(aiRange, tLabel("ai_index_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an array field of a value object":
    let r = symexFind(aiField, tLabel("ai_field"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(aiField(r.witness[0], r.witness[1]), "ai_field")
    let d = symexFind(aiField, tLabel("ai_field_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a Table value":
    let r = symexFind(aiTab, tLabel("ai_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(aiTab(r.witness[0], r.witness[1]), "ai_tab")

# ---- (5) newSeq ---------------------------------------------------------------
#
# RFC-0005 S8bc: `newSeq[T](n)` / `newSeq(s, n)` is `n` zero elements; a
# negative `n` raises `RangeDefect` (the `Natural` parameter); a length above
# 2^20 declines, scoped to its path. The stdlib body was walked and declined
# (an unsupported `when`, the payload cast).

proc nsLen(n: int) =
  if n < 0 or n > 50: return
  let s = newSeq[int](n)
  if s.len == 3 and s[2] == 0 and s[0] == 0: symexTarget("ns_len")
  if s.len == 3 and s[1] != 0: symexTarget("ns_zero_dead")
  if s.len != n and n >= 0: symexTarget("ns_len_dead")

proc nsRange(n: int) =
  try:
    let s = newSeq[int](n)
    if s.len < 0: symexTarget("ns_range_dead")
  except RangeDefect:
    if n < 0: symexTarget("ns_range")
    if n >= 0: symexTarget("ns_range_dead2")

proc nsHuge(n: int) =
  if n == 7: symexTarget("ns_small")
  if n < 0: return
  let s = newSeq[bool](n)
  if s.len == 2_000_000: symexTarget("ns_huge")

proc nsVar(n: int) =
  if n < 1 or n > 9: return
  var s: seq[string]
  newSeq(s, n)
  s[n - 1] = "x"
  if s.len == 4 and s[3] == "x" and s[0] == "": symexTarget("ns_var")
  if s.len == 4 and s[2] != "": symexTarget("ns_var_dead")

proc nsWrite(i: int) =
  var s = newSeq[int8]()
  s.add 3
  var t = newSeq[int8](3)
  t[i] = 5
  if t[0] == 5 and s[0] == 3 and t[1] == 0 and t.len == 3: symexTarget("ns_write")

proc itBound(n: int) =
  # `initTable`'s own size guard (S8at), behind a bound: its decline arm is
  # infeasible here, so it is dropped, not walked into a taint.
  if n < 0 or n > 9: return
  var t = initTable[int, int](n)
  t[1] = 2
  if t.len != 1: symexTarget("it_bound_dead")

suite "S8bc (5): newSeq":
  test "a scoped decline on an infeasible arm does not taint":
    let d = symexFind(itBound, tLabel("it_bound_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let n = symexFind(nsLen, tLabel("ns_len_dead"))
    checkpoint $n.status & " " & show(n.errors)
    check n.status == sxUnsat


  test "newSeq[T](n) is n zero elements":
    let r = symexFind(nsLen, tLabel("ns_len"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces(nsLen(r.witness[0]), "ns_len")
    let d = symexFind(nsLen, tLabel("ns_zero_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let d2 = symexFind(nsLen, tLabel("ns_len_dead"))
    checkpoint $d2.status & " " & show(d2.errors)
    check d2.status == sxUnsat

  test "a negative length raises RangeDefect":
    let r = symexFind(nsRange, tLabel("ns_range"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(nsRange(r.witness[0]), "ns_range")
    # A length above 2^20 is the declined path, so this dead label is
    # sxUnknown, not sxUnsat: the decline must never be a false sxUnsat.
    let d = symexFind(nsRange, tLabel("ns_range_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnknown
    check d.errors.hasKind(feUnsupportedOp)
    check not d.errors.hasKind(weInternalWalkerFault)
    let d2 = symexFind(nsRange, tLabel("ns_range_dead2"))
    checkpoint $d2.status & " " & show(d2.errors)
    check d2.status in {sxUnsat, sxUnknown}
    check not d2.errors.hasKind(weInternalWalkerFault)

  test "a length above the bound declines, scoped":
    # The label before the call is found; the one past the 2^20 bound is
    # an honest sxUnknown, never a false sxUnsat.
    let r = symexFind(nsHuge, tLabel("ns_small"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let h = symexFind(nsHuge, tLabel("ns_huge"))
    checkpoint $h.status & " " & show(h.errors)
    check h.status == sxUnknown
    check h.errors.hasKind(feUnsupportedOp)

  test "newSeq(s, n) on a seq[string]":
    let r = symexFind(nsVar, tLabel("ns_var"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check reproduces(nsVar(r.witness[0]), "ns_var")
    let d = symexFind(nsVar, tLabel("ns_var_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "newSeq[int8]() and a write into newSeq[int8](3)":
    let r = symexFind(nsWrite, tLabel("ns_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 0
      check reproduces(nsWrite(r.witness[0]), "ns_write")

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
