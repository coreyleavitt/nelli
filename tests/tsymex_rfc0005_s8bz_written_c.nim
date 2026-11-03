## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part A:
## the written-ness of a part (items 3, 4 and 7) and the address of an array
## element (item 5). Every expectation is Nim's (the "nim" tests run the same
## code).
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8bz_written`, `tsymex_rfc0005_s8bz_written_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 65 s).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import s8ct_platform
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

template confirmed(fn: typed, lbl: string): untyped =
  ## A clean `sxSat` whose witness replays `roConfirmed` against Nim.
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

template candidate(fn: typed, lbl: string,
                   raised: set[SymexStatusKind] = {}): untyped =
  ## An observed part no write reached: `feGlobalHavoc`, never `sxUnsat`.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown} + raised
    var havoc = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feGlobalHavoc: havoc = true
    check havoc

# ---- 3. a partial write into an unwritten part ---------------------------------
#
# RFC-0005 S8bz item 3. The written-ness of a global is per part: a symbolic
# element write copies the element's other parts (it does not observe them), a
# case object global's entry value is modelled as any other's, and a `var` or
# `addr` actual is copied in without being read; the callee's read of it is the
# observation.

type
  O3 = object
    x, y: int
  VK3 = enum vkA, vkB
  V3 = object
    n: int
    case k: VK3
    of vkA: a: int
    of vkB: b: int

# ---- 4. a dereference onto an unwritten candidate ------------------------------
#
# RFC-0005 S8bz item 4. The pointer may address a part no write reached; only
# that sub-path observes it. A scalar part of a global whose entry value is not
# modelled (a `ref` beside it) holds some value of its type all the same.

type NE4 = object
  r: ref int
  n: int

var gD4: tuple[a, b: int]
var gDw4: tuple[a, b: int]
var gNE4: NE4

proc sutDeref(p: ptr int) =
  if p == nil: return
  gD4.a = 0
  if p[] == 9 and gD4.a == 0: symexTarget("d")
  if p[] == 9 and p[] != 9: symexTarget("d_dead")

proc sutDerefWritten(p: ptr int) =
  ## Every candidate written: no sub-path observes anything.
  if p == nil: return
  gDw4.a = 1
  gDw4.b = 1
  if p[] == 9: symexTarget("dw")

proc sutDerefRefSibling(p: ptr int) =
  if p == nil: return
  gNE4.r = nil
  if p[] == 9: symexTarget("dr")

suite "S8bz (4): a dereference onto an unwritten candidate":

  test "only the sub-path that names the part observes it":
    ## RED: every path carried `feGlobalHavoc` (the whole dereference), so
    ## a hit through the pointer's own cell did too.
    block:
      let r = symexFind(sutDeref, tLabel("d"))
      checkpoint show(r.errors)
      check r.status == sxSat
      check replayedOrNotMarshallable(replayWitness(sutDeref, r.witness, tLabel("d"), {}), roConfirmed)
    block:
      let r = symexFind(sutDeref, tLabel("d_dead"))
      checkpoint show(r.errors)
      check r.status == sxUnsat

  test "no candidate unwritten":
    confirmed(sutDerefWritten, "dw")

  test "a scalar part beside a `ref`":
    ## RED: sxUnknown, `feGlobalReadUnmodelled` on `gNE4.n`.
    candidate(sutDerefRefSibling, "dr")

# ---- 7. `{.noinit.}` locals ----------------------------------------------------
#
# RFC-0005 S8bz item 7. S8be modelled `{.global.}` (`isRoutineGlobal`); a
# `{.noinit.}` local with no initialiser declined. It is unwritten: any value
# of its type, per part, and a read of a part no write reached taints the path.

template noinitRead(fn: typed, lbl: string): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feGlobalHavoc and "{.noinit.}" in e.msg: named = true
    check named

proc sutNoinitWrite(k: int) =
  var c {.noinit.}: int
  c = k
  if c == 5: symexTarget("nw")
  if c != k: symexTarget("nw_dead")

proc sutNoinitRead(k: int) =
  var c {.noinit.}: int
  if k == 5 and c == 3: symexTarget("nr")
  if k == 5 and c != c: symexTarget("nr_dead")

proc sutNoinitArr(k: int) =
  var a {.noinit.}: array[3, int]
  a[1] = k
  if a[1] == 5: symexTarget("na")
  if a[1] != k: symexTarget("na_dead")

proc sutNoinitArrOther(k: int) =
  var a {.noinit.}: array[3, int]
  a[1] = k
  if a[0] == 5: symexTarget("nao")

proc sutNoinitTuple(k: int) =
  var t {.noinit.}: tuple[a, b: int]
  t.a = k
  if t.a == 5: symexTarget("nt")

proc sutNoinitTupleOther(k: int) =
  var t {.noinit.}: tuple[a, b: int]
  t.a = k
  if t.b == 5: symexTarget("nto")

proc sutNoinitLoop(k: int) =
  ## Each evaluation of the declaration is its own value.
  for i in 0 .. 1:
    var c {.noinit.}: int
    c = i + k
    if i == 1 and c == 6: symexTarget("nl")

proc sutNoinitString(k: int) =
  var s {.noinit.}: string
  s = "a"
  if k == 5 and s == "a": symexTarget("ns")

proc sutGlobalLocal(k: int) =
  var c {.global.}: int
  c = k
  if c == 5: symexTarget("gl")

suite "S8bz (7): {.global.} and {.noinit.} locals":

  test "nim":
    sutNoinitWrite(5)
    sutNoinitArr(5)
    sutNoinitTuple(5)
    sutNoinitLoop(5)

  test "written before any read":
    ## RED: sxUnknown, `feUnsupportedStmtKind` ("its value is undefined").
    confirmed(sutNoinitWrite, "nw")
    discard clean(sutNoinitWrite, "nw_dead", sxUnsat)
    confirmed(sutNoinitArr, "na")
    discard clean(sutNoinitArr, "na_dead", sxUnsat)
    confirmed(sutNoinitTuple, "nt")
    confirmed(sutNoinitLoop, "nl")

  test "a read of a part no write reached":
    ## RED: sxUnknown, `feUnsupportedStmtKind`, and the name unbound.
    noinitRead(sutNoinitRead, "nr")
    block:
      let r = symexFind(sutNoinitRead, tLabel("nr_dead"))
      checkpoint show(r.errors)
      check r.status == sxUnsat
    noinitRead(sutNoinitArrOther, "nao")
    noinitRead(sutNoinitTupleOther, "nto")

  test "a managed type stays a decline":
    ## Nim destroys the garbage a `{.noinit.}` string holds at its first
    ## assignment (never run here), which no value of the type stands for.
    let r = symexFind(sutNoinitString, tLabel("ns"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feUnsupportedStmtKind and "managed" in e.msg: named = true
    check named

  test "a {.global.} local":
    confirmed(sutGlobalLocal, "gl")

suite "S8bz: walker version":

  test "the walker version is at least S8bz's":
    check parseInt(symexWalkerVersion) >= 249
