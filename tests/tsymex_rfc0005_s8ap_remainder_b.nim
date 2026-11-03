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
## RFC-0005 S8cm: part 2 of 4 of this suite, with
## `tsymex_rfc0005_s8ap_remainder`, `tsymex_rfc0005_s8ap_remainder_c`,
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

proc hStrWrite(p: RNode, c: char) =
  if p != nil:
    p.name = "a"
    p.name.add c
    if p.name == "ax": symexTarget("h_strwrite")
    if p.name.len != 2: symexTarget("h_strwrite_dead")

proc hTable(p: RNode, v: int) =
  if p != nil:
    p.t["a"] = v
    if p.t["a"] == 3: symexTarget("h_tab")
    if p.t["a"] != v: symexTarget("h_tab_dead")

proc hTableRead(p: RNode) =
  if p != nil and p.t.hasKey("k") and p.t["k"] == 9: symexTarget("h_tabread")
  if p != nil and p.t.len == 0 and p.t.hasKey("k"): symexTarget("h_tabread_dead")

proc hSet(p: RNode, v: int) =
  if p != nil:
    p.hs.incl v
    if v in p.hs and v == 4: symexTarget("h_set")
    if v notin p.hs: symexTarget("h_set_dead")

proc hSetRead(p: RNode) =
  if p != nil and 4 in p.hs and p.hs.len == 1: symexTarget("h_setread")
  if p != nil and p.hs.len == 0 and 4 in p.hs: symexTarget("h_setread_dead")

proc hFloatBool(p: FNode) =
  if p != nil and p.fs.len == 1 and p.fs[0] == 1.5 and p.k == 2:
    symexTarget("h_fb")

proc hKids(p: LNode) =
  if p != nil and p.kids.len == 2 and p.kids[1] != nil and p.kids[1].v == 3:
    symexTarget("h_kids")

proc hMerge(p: RNode, b: bool) =
  ## Two paths write different seqs to the field; the join keeps both.
  if p != nil:
    if b: p.s = @[1]
    else: p.s = @[2, 2]
    if p.s.len == 2 and p.s[0] == 2 and not b: symexTarget("h_merge")
    if b and p.s.len != 1: symexTarget("h_merge_dead")

proc hBare(p: ref seq[int]) =
  if p != nil and p[].len == 1 and p[][0] == 2: symexTarget("h_bare")

suite "S8ap (1): compound-sort fields of a ref object are heap cells":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      check not r.errors.hasKind(seUnsupportedCompoundSortLeaf)
      check not r.errors.hasKind(heUnsupportedPointeeRead)
      check not r.errors.hasKind(heNewFieldZeroUnsupported)
      r

  test "a string field written, appended through the ref, and read":
    let r = run(hStrWrite, "h_strwrite", sxSat)
    if r.status == sxSat: check char(r.witness[1]) == 'x'
    discard run(hStrWrite, "h_strwrite_dead", sxUnsat)

  test "a Table field: []= through the ref, then read":
    let r = run(hTable, "h_tab", sxSat)
    if r.status == sxSat: check r.witness[1] == 3
    discard run(hTable, "h_tab_dead", sxUnsat)

  test "a Table field of a param: rendered, and its size is tied to its content":
    let r = run(hTableRead, "h_tabread", sxSat)
    if r.status == sxSat:
      check r.witness[0].t.getOrDefault("k", 0) == 9
      check reproduces(hTableRead(r.witness[0]), "h_tabread")
    discard run(hTableRead, "h_tabread_dead", sxUnsat)

  test "a HashSet field: incl through the ref, then read":
    let r = run(hSet, "h_set", sxSat)
    if r.status == sxSat: check r.witness[1] == 4
    discard run(hSet, "h_set_dead", sxUnsat)

  test "a HashSet field of a param: rendered, and its size is tied to its content":
    let r = run(hSetRead, "h_setread", sxSat)
    if r.status == sxSat:
      check 4 in r.witness[0].hs
      check reproduces(hSetRead(r.witness[0]), "h_setread")
    discard run(hSetRead, "h_setread_dead", sxUnsat)

  test "a float seq field renders":
    let r = run(hFloatBool, "h_fb", sxSat)
    if r.status == sxSat:
      check r.witness[0].fs == @[1.5]
      check reproduces(hFloatBool(r.witness[0]), "h_fb")

  test "a seq-of-ref field renders its elements as heap positions":
    let r = run(hKids, "h_kids", sxSat)
    if r.status == sxSat:
      check r.witness[0].kids.len == 2
      check r.witness[0].kids[1] != nil
      check reproduces(hKids(r.witness[0]), "h_kids")

  test "a path join merges every leaf of the field":
    discard run(hMerge, "h_merge", sxSat)
    discard run(hMerge, "h_merge_dead", sxUnsat)

  test "a bare ref seq pointee is a heap cell too":
    let r = run(hBare, "h_bare", sxSat)
    if r.status == sxSat:
      check r.witness[0] != nil
      check reproduces(hBare(r.witness[0]), "h_bare")

# ---- (2) dotted-field mutations -----------------------------------------------

proc dVDel(v: int) =
  var o: VO
  o.s = @[v, 2, 3]
  o.s.del(0)
  if o.s.len == 2 and o.s[0] == 3 and v == 1: symexTarget("dv_del")
  if o.s.len != 2: symexTarget("dv_del_dead")

proc dVDelOob(i: int) =
  var o: VO
  o.s = @[1]
  o.s.del(i)

suite "S8ap (2): del/insert/incl/excl/[]= on a dotted field":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      check not r.errors.anyIt("N49" in it.msg)
      r

  test "value path: o.s.del(i)":
    discard run(dVDel, "dv_del", sxSat)
    discard run(dVDel, "dv_del_dead", sxUnsat)

  test "value path: o.s.del out of bounds raises IndexDefect":
    let r = symexFind(dVDelOob, tIndexError())
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxRaised
