## RFC-0005 (soundness channels) slice S8at -- S8ar's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 4 of 6 of this suite, with
## `tsymex_rfc0005_s8at_remainder`, `tsymex_rfc0005_s8at_remainder_b`,
## `tsymex_rfc0005_s8at_remainder_c`, `tsymex_rfc0005_s8at_remainder_e`,
## `tsymex_rfc0005_s8at_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 115 s).

import std/[unittest, strutils, sequtils, tables, sets]
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

# ---- (3) a symbolic index into an array of seqs ----------------------------

type ASH = ref object
  a: array[3, seq[int]]

# ---- (5) a `distinct` over a composite base ---------------------------------

type
  DSq = distinct seq[int]
  DTp = distinct (int, bool)
  DSH = ref object
    ds: DSq
    dt: DTp
    n: int

proc dsRead(p: DSH) =
  if p != nil and seq[int](p.ds).len == 2 and seq[int](p.ds)[1] == 7 and
     (int, bool)(p.dt)[0] == 3:
    symexTarget("ds_read")

proc dsWrite(p: DSH, v: int) =
  if p != nil:
    p.ds = DSq(@[v])
    if seq[int](p.ds).len == 1 and seq[int](p.ds)[0] == 6: symexTarget("ds_write")
    if seq[int](p.ds)[0] != v: symexTarget("ds_write_dead")

proc dsNew(n: int) =
  let h = DSH(n: n)
  if seq[int](h.ds).len == 0 and n == 2: symexTarget("ds_new")
  if seq[int](h.ds).len != 0: symexTarget("ds_new_dead")

proc dsParam(d: DSq) =
  if seq[int](d).len == 1 and seq[int](d)[0] == 3: symexTarget("ds_param")

type
  DOb = object
    a: int
    s: string
  DO = distinct DOb
  DOH = ref object
    d: DO

proc len(d: DSq): int {.borrow.}

proc dtWrite(p: DSH, x: int) =
  if p != nil:
    p.dt = DTp((x, true))
    if (int, bool)(p.dt)[0] == 9 and (int, bool)(p.dt)[1]: symexTarget("dt_write")
    if not (int, bool)(p.dt)[1]: symexTarget("dt_write_dead")

proc doRead(p: DOH) =
  if p != nil and DOb(p.d).a == 4 and DOb(p.d).s == "q": symexTarget("do_read")

proc dsBorrow(d: DSq) =
  if d.len == 2: symexTarget("ds_borrow")

suite "S8at (5): a distinct over a composite base":
  test "a field read":
    let r = symexFind(dsRead, tLabel("ds_read"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(heUnsupportedPointeeRead)
    if r.status == sxSat: check reproduces(dsRead(r.witness[0]), "ds_read")

  test "a field write":
    let r = symexFind(dsWrite, tLabel("ds_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(dsWrite, tLabel("ds_write_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "construction zeroes it":
    let r = symexFind(dsNew, tLabel("ds_new"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(dsNew, tLabel("ds_new_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a parameter":
    let r = symexFind(dsParam, tLabel("ds_param"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(dsParam(r.witness[0]), "ds_param")

  test "a distinct tuple field write":
    let r = symexFind(dtWrite, tLabel("dt_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(dtWrite(r.witness[0], r.witness[1]), "dt_write")
    let d = symexFind(dtWrite, tLabel("dt_write_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a distinct object field":
    let r = symexFind(doRead, tLabel("do_read"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(doRead(r.witness[0]), "do_read")

  test "a borrowed proc":
    # RFC-0005 S8at pinned this declined: a `{.borrow.}` routine that is not
    # an operator had the borrowed symbol as its body
    # (`feUnsupportedStmtKind`). RFC-0005 S8bc (item 2) lowers it as the base
    # routine on the unwrapped argument.
    let r = symexFind(dsBorrow, tLabel("ds_borrow"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedStmtKind)
    if r.status == sxSat: replays(dsBorrow(r.witness[0]), "ds_borrow")

# ---- (6) a value object that recurs through a container ---------------------
#
# RFC-0005 S8at: the recursion is not what declines here. A seq whose
# element is a tuple or object is backed in no position (a parameter, a
# field, a local: `isBackedSeqElemTy`), recursive or not; `seq[P]` with a
# plain `P = object a: int` declines the same way. That is a different
# mechanism (a leaf-split seq element) and stays a scoped, stated decline:
# a path that does not read the seq is exact.

type
  VRc = object
    kids: seq[VRc]
    v: int
  VFlat = object
    a: int
  VHold = object
    ps: seq[VFlat]

proc vrKids(p: VRc) =
  if p.v == 1: symexTarget("vr_v")
  if p.kids.len == 1 and p.kids[0].v == 3: symexTarget("vr_kids")

proc vrFlat(h: VHold) =
  if h.ps.len == 1 and h.ps[0].a == 3: symexTarget("vr_flat")

suite "S8at (6): a value object recurring through a seq":
  test "a path that does not read the seq is exact":
    let r = symexFind(vrKids, tLabel("vr_v"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)

  test "its elements are read (RFC-0005 S8bc: a leaf-split seq element)":
    # RFC-0005 S8bc re-pinned this. S8at declined both reads
    # (`seNestedSeqUnsupported`): a seq of a tuple or object was backed in
    # no position. S8bc holds such a seq leaf-split and unrolls the
    # recursive value object to a bounded depth, so both are exact.
    let r = symexFind(vrKids, tLabel("vr_kids"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat: check reproduces(vrKids(r.witness[0]), "vr_kids")
    let f = symexFind(vrFlat, tLabel("vr_flat"))
    checkpoint $f.status & " " & show(f.errors)
    check f.status == sxSat
    if f.status == sxSat: check reproduces(vrFlat(f.witness[0]), "vr_flat")

proc tfZero(x: int) =
  var t = initTable[float, int]()
  t[0.0] = 1
  if (-0.0) in t and t[-0.0] == 1 and x == 2: symexTarget("tf_zero")
  if (-0.0) notin t: symexTarget("tf_zero_dead")

proc tfNan(x: int) =
  var t = initTable[float, int]()
  let n = NaN
  t[n] = 1
  if n notin t and x == 1: symexTarget("tf_nan")
  if n in t: symexTarget("tf_nan_dead")

proc tfNanTwice(x: int) =
  # Each NaN insert is its own entry; `del(NaN)` finds none of them.
  var t = initTable[float, int]()
  let n = NaN
  t[n] = 1
  t[n] = 2
  t.del(n)
  if t.len == 2 and x == 3: symexTarget("tf_nan2")
  if t.len != 2: symexTarget("tf_nan2_dead")

suite "S8at (7): Table float keys and container values":
  test "-0.0 and 0.0 are one key":
    let r = symexFind(tfZero, tLabel("tf_zero"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tfZero, tLabel("tf_zero_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a NaN key is never found":
    let r = symexFind(tfNan, tLabel("tf_nan"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tfNan, tLabel("tf_nan_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "each NaN insert is an entry, and del(NaN) removes none":
    let r = symexFind(tfNanTwice, tLabel("tf_nan2"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tfNanTwice, tLabel("tf_nan2_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
