## RFC-0005 (soundness channels) slice S8ap -- S8ao's "Different mechanisms,
## reported and not fixed here" remainder.
##
## This slice closes:
##   (1) A compound-sort field of a `ref`/`ptr` object had no heap storage:
##       `p.s = @[v]`, any read of `p.s`, and `RNode(...)`'s zero-write of a
##       seq/Table/HashSet field all degraded (`seUnsupportedCompoundSortLeaf`,
##       `heUnsupportedPointeeRead`, `heNewFieldZeroUnsupported`), and a
##       `string` field could be written but not read. A compound field is
##       now held in one heap array per LEAF of its value (a seq's data and
##       length, a table's data, presence and size, a set's members and
##       size), every leaf keyed on the same `Ref_T` address, so aliasing,
##       the nil fork and path merges are the scalar heap's own. The INPUT
##       cell is well-formed where it is read (a length or size in
##       `[0, 1024]`, a string of bytes, a table's or set's size tied to its
##       content), and the witness renders it from the input heap.
##   (2) `del`/`insert`/`incl`/`excl`/`[]=` and `<field>[i] = v` on a dotted
##       field (value path or ref path) were N49 / "unsupported nnkAsgn
##       shape". They now take the bare-symbol arm's IR over the field-write
##       primitive S8ao's `add` uses.
##   (3) `add` on a dotted string field was N49. It is `iekStrConcat`, as on
##       a bare string.
##   (4) The uninitialised `var` of an `itUninterp` placeholder declined as
##       `feUnsupportedStmtKind`; it now carries the precise kind
##       `allocateSym` gives the same placeholder.
## Every clean `sxSat` over a `ref` param is checked by RUNNING the SUT on
## the witness.
##
## RFC-0005 S8cm: part 3 of 4 of this suite, with
## `tsymex_rfc0005_s8ap_remainder`, `tsymex_rfc0005_s8ap_remainder_b`,
## `tsymex_rfc0005_s8ap_remainder_d`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 84 s).

import std/[unittest, strutils, sequtils, tables, sets, atomics]
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
  ## Runs the SUT on the witness in a capture frame.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

type
  RNode = ref object
    s: seq[int]
    name: string
    t: Table[string, int]
    hs: HashSet[int]
    n: int
  VO = object
    s: seq[int]
    name: string
    t: Table[string, int]
    hs: HashSet[int]
    n: int
  FNode = ref object
    fs: seq[float]
    k: int
  CNode = ref object
    v: int
  LNode = ref object
    kids: seq[CNode]
    v: int

proc dVIdx(v, i: int) =
  var o: VO
  o.s = @[0, 0]
  o.s[i] = v
  if o.s[1] == 6 and o.s[0] == 0: symexTarget("dv_idx")

proc dVIdxDead(v, i: int) =
  ## The dead twin, with the index in bounds: the out-of-bounds write's
  ## IndexDefect is pinned separately below, and an escaping raise would
  ## make this `sxRaised` rather than `sxUnsat`.
  if i < 0 or i > 1: return
  var o: VO
  o.s = @[0, 0]
  o.s[i] = v
  if o.s.len != 2 or o.s[i] != v: symexTarget("dv_idx_dead")

proc dVTab(v: int) =
  var o: VO
  o.t["a"] = v
  o.t["b"] = 1
  o.t.del("b")
  if o.t["a"] == 4 and o.t.len == 1: symexTarget("dv_tab")
  if o.t.hasKey("b"): symexTarget("dv_tab_dead")

proc dVSet(v: int) =
  var o: VO
  o.hs.incl v
  o.hs.incl 9
  o.hs.excl 9
  if v in o.hs and v == 2 and o.hs.len == 1: symexTarget("dv_set")
  if 9 in o.hs and v != 9: symexTarget("dv_set_dead")

proc dVInsert(v: int) =
  var o: VO
  o.s.insert(v, 0)
  if o.s.len == 1: symexTarget("dv_ins")

proc bareInsert(v: int) =
  var s: seq[int]
  s.insert(v, 0)
  if s.len == 1: symexTarget("bare_ins")

proc dRDel(p: RNode, v: int) =
  if p != nil:
    p.s = @[v, 5]
    p.s.del(0)
    if p.s.len == 1 and p.s[0] == 5 and v == 1: symexTarget("dr_del")
    if p.s.len != 1: symexTarget("dr_del_dead")

proc dRIdx(p: RNode, v: int) =
  if p != nil and p.s.len == 2:
    p.s[1] = v
    if p.s[1] == 6: symexTarget("dr_idx")
    if p.s[1] != v: symexTarget("dr_idx_dead")

proc dRIdxOob(p: RNode, v: int) =
  if p != nil:
    p.s = @[1]
    p.s[v] = 3

proc dRTab(p: RNode, v: int) =
  if p != nil:
    p.t.del("a")
    p.t["a"] = v
    if p.t["a"] == 2: symexTarget("dr_tab")
    if not p.t.hasKey("a"): symexTarget("dr_tab_dead")

suite "S8ap (2): del/insert/incl/excl/[]= on a dotted field":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      check not r.errors.anyIt("N49" in it.msg)
      r

  test "value path: o.s[i] = v (and its IndexDefect)":
    let r = run(dVIdx, "dv_idx", sxSat)
    if r.status == sxSat: check r.witness[0] == 6 and r.witness[1] == 1
    discard run(dVIdxDead, "dv_idx_dead", sxUnsat)
    let r2 = symexFind(dVIdx, tIndexError())
    check r2.status == sxRaised

  test "value path: o.t[k] = v and o.t.del(k)":
    discard run(dVTab, "dv_tab", sxSat)
    discard run(dVTab, "dv_tab_dead", sxUnsat)

  test "value path: o.hs.incl / o.hs.excl":
    discard run(dVSet, "dv_set", sxSat)
    discard run(dVSet, "dv_set_dead", sxUnsat)

  test "o.s.insert takes the bare insert's IR":
    ## RFC-0005 S8ar models `insert` (it was the bare arm's lowering
    ## decline, which this pin shared): both now reach the target.
    let rb = symexFind(bareInsert, tLabel("bare_ins"))
    let rd = symexFind(dVInsert, tLabel("dv_ins"))
    checkpoint "bare " & $rb.status & " " & show(rb.errors)
    checkpoint "dotted " & $rd.status & " " & show(rd.errors)
    check rd.status == rb.status
    check rd.status == sxSat
    check not rd.errors.anyIt("N49" in it.msg)
    for e in rb.errors:
      if e.severity == sevError: check rd.errors.hasKind(e.kind)

  test "ref path: p.s.del(i)":
    discard run(dRDel, "dr_del", sxSat)
    discard run(dRDel, "dr_del_dead", sxUnsat)

  test "ref path: p.s[i] = v":
    let r = run(dRIdx, "dr_idx", sxSat)
    if r.status == sxSat:
      check r.witness[1] == 6
      check reproduces(dRIdx(r.witness[0], r.witness[1]), "dr_idx")
    discard run(dRIdx, "dr_idx_dead", sxUnsat)

  test "ref path: p.s[i] = v out of bounds raises IndexDefect":
    let r = symexFind(dRIdxOob, tIndexError())
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxRaised

  test "ref path: p.t.del(k) and p.t[k] = v":
    discard run(dRTab, "dr_tab", sxSat)
    discard run(dRTab, "dr_tab_dead", sxUnsat)
