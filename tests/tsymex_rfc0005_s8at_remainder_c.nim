## RFC-0005 (soundness channels) slice S8at -- S8ar's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 3 of 6 of this suite, with
## `tsymex_rfc0005_s8at_remainder`, `tsymex_rfc0005_s8at_remainder_b`,
## `tsymex_rfc0005_s8at_remainder_d`, `tsymex_rfc0005_s8at_remainder_e`,
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

# ---- (1) a `ref` to an anonymous tuple --------------------------------------

proc rtRead(p: ref (int, int)) =
  if p != nil and p[0] == 3 and p[1] == 4: symexTarget("rt_read")

proc rtWrite(p: ref (int, int), x: int) =
  if p != nil:
    p[0] = x
    if p[0] == 9 and p[1] == 2: symexTarget("rt_write")
    if p[0] != x: symexTarget("rt_write_dead")

proc rtWhole(p: ref (int, bool)) =
  if p != nil:
    let before = p[1]
    p[] = (5, not before)
    if p[0] == 5 and p[1] != before: symexTarget("rt_whole")
    if p[0] != 5: symexTarget("rt_whole_dead")

proc rtNew(x: int) =
  var p: ref (int, int)
  new(p)
  if p[0] == 0 and p[1] == 0 and x == 1: symexTarget("rt_new")
  if p[1] != 0: symexTarget("rt_new_dead")

proc rtAlias(p, q: ref (int, int)) =
  if p != nil and q != nil:
    p[0] = 1
    q[0] = 2
    if p[0] == 2: symexTarget("rt_alias")

suite "S8at (1): a ref to an anonymous tuple":
  test "a read of its elements":
    let r = symexFind(rtRead, tLabel("rt_read"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(rtRead(r.witness[0]), "rt_read")

  test "an element write":
    let r = symexFind(rtWrite, tLabel("rt_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(rtWrite(r.witness[0], r.witness[1]), "rt_write")
    let d = symexFind(rtWrite, tLabel("rt_write_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a whole store":
    let r = symexFind(rtWhole, tLabel("rt_whole"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(rtWhole(r.witness[0]), "rt_whole")
    let d = symexFind(rtWhole, tLabel("rt_whole_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "new zeroes it":
    let r = symexFind(rtNew, tLabel("rt_new"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(rtNew, tLabel("rt_new_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "two refs may alias":
    let r = symexFind(rtAlias, tLabel("rt_alias"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(rtAlias(r.witness[0], r.witness[1]), "rt_alias")

# ---- (3) a symbolic index into an array of seqs ----------------------------

type ASH = ref object
  a: array[3, seq[int]]

proc asHeap(p: ASH, i: int) =
  if p != nil and i >= 0 and i < 3 and p.a[i].len == 2 and p.a[i][1] == 5 and
     p.a[0].len == 0:
    symexTarget("as_heap")
  if p != nil and i >= 0 and i < 3 and p.a[i].len > 1024:
    symexTarget("as_heap_dead")

proc asLocal(i, x: int) =
  var a: array[2, seq[int]]
  a[1].add x
  if i >= 0 and i < 2 and a[i].len == 1 and a[i][0] == 8: symexTarget("as_local")
  if i >= 0 and i < 2 and a[i].len == 1 and i == 0: symexTarget("as_local_dead")

proc asParam(a: array[2, seq[int]], i: int) =
  if i >= 0 and i < 2 and a[i].len == 3 and i == 1: symexTarget("as_param")

proc asMut(p: ASH, i, x: int) =
  if p != nil and i >= 0 and i < 3:
    p.a[i].add x
    if p.a[2].len == 1 and p.a[2][0] == 6: symexTarget("as_mut")
    if p.a[i].len == 0: symexTarget("as_mut_dead")

proc asOob(i: int) =
  var a: array[2, seq[int]]
  try:
    a[i].add 1
  except IndexDefect:
    if i == 2 and a[0].len == 0 and a[1].len == 0: symexTarget("as_oob")
    if i == 1: symexTarget("as_oob_dead")

proc asTab(k: string) =
  var a: array[2, Table[string, int]]
  a[1][k] = 4
  a[0].del k
  if a[1].hasKey(k) and a[1][k] == 4 and k == "z" and a[0].len == 0:
    symexTarget("as_tab")
  if not a[1].hasKey(k): symexTarget("as_tab_dead")

suite "S8at (3): a symbolic index into an array of seqs":
  test "through a ref":
    let r = symexFind(asHeap, tLabel("as_heap"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedOpHavoc)
    if r.status == sxSat:
      check reproduces(asHeap(r.witness[0], r.witness[1]), "as_heap")
    let d = symexFind(asHeap, tLabel("as_heap_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a local array":
    let r = symexFind(asLocal, tLabel("as_local"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(asLocal(r.witness[0], r.witness[1]), "as_local")
    let d = symexFind(asLocal, tLabel("as_local_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a parameter":
    let r = symexFind(asParam, tLabel("as_param"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      replays(asParam(r.witness[0], r.witness[1]), "as_param")

  test "a mutation of an element":
    let r = symexFind(asMut, tLabel("as_mut"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(asMut(r.witness[0], r.witness[1], r.witness[2]), "as_mut")
    let d = symexFind(asMut, tLabel("as_mut_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an out-of-range element mutation raises":
    let r = symexFind(asOob, tLabel("as_oob"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(asOob(r.witness[0]), "as_oob")
    let d = symexFind(asOob, tLabel("as_oob_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a Table element":
    let r = symexFind(asTab, tLabel("as_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(asTab(r.witness[0]), "as_tab")
    let d = symexFind(asTab, tLabel("as_tab_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

# ---- (5) a `distinct` over a composite base ---------------------------------

type
  DSq = distinct seq[int]
  DTp = distinct (int, bool)
  DSH = ref object
    ds: DSq
    dt: DTp
    n: int

proc len(d: DSq): int {.borrow.}
