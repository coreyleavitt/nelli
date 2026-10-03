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

# ---- (1) compound-sort heap storage -------------------------------------------

proc hAssign(p: RNode, v: int) =
  if p != nil:
    p.s = @[v]
    if p.s.len == 1 and p.s[0] == 7: symexTarget("h_assign")
    if p.s.len != 1 or p.s[0] != v: symexTarget("h_assign_dead")

proc hRead(p: RNode) =
  if p != nil and p.s.len == 2 and p.s[1] == 5: symexTarget("h_read")
  if p != nil and p.s.len < 0: symexTarget("h_read_neglen_dead")
  if p != nil and p.s.len > 1024: symexTarget("h_read_bigLen_dead")

proc hReadAfterWrite(p: RNode, v: int) =
  ## `p.s == 0`-style read, then a write: the witness is the INPUT cell.
  if p != nil and p.s.len == 3:
    p.s = @[]
    if p.s.len == 0 and v == 1: symexTarget("h_raw")

proc hAlias(p, q: RNode, v: int) =
  if p != nil and q != nil:
    p.s = @[v, v]
    if p == q and q.s.len == 2 and q.s[1] == 4: symexTarget("h_alias")
    if p == q and q.s[0] != v: symexTarget("h_alias_dead")
    if p != q and q.s.len == 3 and q.s[2] == 6: symexTarget("h_noalias")

proc hNil(p: RNode, v: int) =
  p.s = @[v]
  if p.s.len == 1: symexTarget("h_nil_after")

proc hNilRead(p: RNode) =
  if p.s.len == 1: symexTarget("h_nilread_after")

proc hNew(v: int) =
  let p = RNode(n: v)
  if p.s.len == 0 and p.t.len == 0 and p.hs.len == 0 and p.name.len == 0 and
     v == 3:
    symexTarget("h_new")

proc hNewDead(v: int) =
  ## The dead twin in its own proc: one path through both `if`s makes nine
  ## heap reads, past the walker's per-path heap-depth budget of 8
  ## (`heDepthExhausted`, unchanged by this slice).
  let p = RNode(n: v)
  if p.s.len != 0 or p.t.len != 0 or p.hs.len != 0 or p.name.len != 0:
    symexTarget("h_new_dead")

proc hNewSeq(v: int) =
  let p = RNode(s: @[v, 2], name: "ab")
  if p.s.len == 2 and p.s[0] == 5 and p.name == "ab": symexTarget("h_newseq")
  if p.s[1] != 2 or p.name != "ab": symexTarget("h_newseq_dead")

proc hNewRef(v: int) =
  var p: RNode
  new(p)
  p.s.add v
  if p.s.len == 1 and p.s[0] == 8: symexTarget("h_newref")
  if p.s.len != 1: symexTarget("h_newref_dead")

proc hStr(p: RNode) =
  if p != nil and p.name == "hi": symexTarget("h_str")
  if p != nil and p.name.len < 0: symexTarget("h_str_dead")

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

  test "a seq field written then read (p.s = @[v])":
    let r = run(hAssign, "h_assign", sxSat)
    if r.status == sxSat:
      check r.witness[1] == 7
      check reproduces(hAssign(r.witness[0], r.witness[1]), "h_assign")
    discard run(hAssign, "h_assign_dead", sxUnsat)

  test "a seq field of a param read from the input heap; the witness renders it":
    let r = run(hRead, "h_read", sxSat)
    if r.status == sxSat:
      check r.witness[0] != nil
      check r.witness[0].s.len == 2
      check r.witness[0].s[1] == 5
      check reproduces(hRead(r.witness[0]), "h_read")
    discard run(hRead, "h_read_neglen_dead", sxUnsat)
    discard run(hRead, "h_read_bigLen_dead", sxUnsat)

  test "the witness is the input cell, not the end-of-path value":
    let r = run(hReadAfterWrite, "h_raw", sxSat)
    if r.status == sxSat:
      check r.witness[0].s.len == 3
      check reproduces(hReadAfterWrite(r.witness[0], r.witness[1]), "h_raw")

  test "aliasing: a write through p is read through q when p == q":
    let r = run(hAlias, "h_alias", sxSat)
    if r.status == sxSat:
      check r.witness[0] == r.witness[1]
      check reproduces(hAlias(r.witness[0], r.witness[1], r.witness[2]), "h_alias")
    discard run(hAlias, "h_alias_dead", sxUnsat)
    let r2 = run(hAlias, "h_noalias", sxSat)
    if r2.status == sxSat:
      check r2.witness[0] != r2.witness[1]
      check reproduces(hAlias(r2.witness[0], r2.witness[1], r2.witness[2]), "h_noalias")

  test "a write and a read through a nil ref raise NilAccessDefect":
    let r = symexFind(hNil, tNilAccess())
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxRaised
    let r1 = run(hNil, "h_nil_after", sxSat)
    if r1.status == sxSat: check r1.witness[0] != nil
    let r2 = symexFind(hNilRead, tNilAccess())
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxRaised

  test "a constructor zero-writes its seq/Table/HashSet/string fields":
    discard run(hNew, "h_new", sxSat)
    discard run(hNewDead, "h_new_dead", sxUnsat)

  test "a constructor's seq and string field values are stored":
    let r = run(hNewSeq, "h_newseq", sxSat)
    if r.status == sxSat: check r.witness[0] == 5
    discard run(hNewSeq, "h_newseq_dead", sxUnsat)

  test "new(p) zero-initialises a seq field (p.s.add after new)":
    let r = run(hNewRef, "h_newref", sxSat)
    if r.status == sxSat: check r.witness[0] == 8
    discard run(hNewRef, "h_newref_dead", sxUnsat)

  test "a string field is read from the heap and rendered":
    let r = run(hStr, "h_str", sxSat)
    if r.status == sxSat:
      check r.witness[0].name == "hi"
      check reproduces(hStr(r.witness[0]), "h_str")
    discard run(hStr, "h_str_dead", sxUnsat)

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

proc dRSet(p: RNode, v: int) =
  if p != nil:
    p.hs.incl v
    p.hs.excl 3
    if v in p.hs and v == 5: symexTarget("dr_set")
    if 3 in p.hs: symexTarget("dr_set_dead")

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

  test "ref path: p.hs.incl / p.hs.excl":
    discard run(dRSet, "dr_set", sxSat)
    discard run(dRSet, "dr_set_dead", sxUnsat)

# ---- (3) add on a dotted string field -------------------------------------------

proc sVChar(c: char) =
  var o: VO
  o.name = "a"
  o.name.add c
  if o.name == "az": symexTarget("sv_char")
  if o.name.len != 2: symexTarget("sv_char_dead")

proc sVStr(x: string) =
  var o: VO
  o.name.add "q"
  o.name.add x
  if o.name == "qrs": symexTarget("sv_str")
  if o.name.len < 1: symexTarget("sv_str_dead")

proc sRChar(p: RNode, c: char) =
  if p != nil and p.name == "m":
    p.name.add c
    if p.name == "mn": symexTarget("sr_char")
    if p.name.len != 2: symexTarget("sr_char_dead")

suite "S8ap (3): add on a dotted string field":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      check not r.errors.anyIt("N49" in it.msg)
      r

  test "value path, a char argument":
    let r = run(sVChar, "sv_char", sxSat)
    if r.status == sxSat: check char(r.witness[0]) == 'z'
    discard run(sVChar, "sv_char_dead", sxUnsat)

  test "value path, a string argument":
    let r = run(sVStr, "sv_str", sxSat)
    if r.status == sxSat: check r.witness[0] == "rs"
    discard run(sVStr, "sv_str_dead", sxUnsat)

  test "ref path, a char argument":
    let r = run(sRChar, "sr_char", sxSat)
    if r.status == sxSat:
      check char(r.witness[1]) == 'n'
      check reproduces(sRChar(r.witness[0], char(r.witness[1])), "sr_char")
    discard run(sRChar, "sr_char_dead", sxUnsat)

# ---- (4) the uninitialised var of an itUninterp placeholder ---------------------

type
  # RFC-0005 S8bn classifies a generic object instance (`G[int]`); a generic
  # CASE object is still unrecognised, so it stands in for the placeholder.
  Weird[T] = object
    case k: bool
    of true: x: T
    of false: discard

proc uClosureVar(x: int) =
  var f: proc(y: int): int
  if x == 1: symexTarget("u_closure")

proc uAtomicVar(x: int) =
  var a: Atomic[int]
  if x == 1: symexTarget("u_atomic")

proc uUnsupportedVar(x: int) =
  var w: Weird[int]
  if x == 1: symexTarget("u_weird")

suite "S8ap (4): an itUninterp var declines with its placeholder's own kind":

  template declines(fn: typed, lbl: string, kind: SymexErrorKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check not r.errors.hasKind(weInternalWalkerFault)
      check r.errors.hasKind(kind)
      check not r.errors.hasKind(feUnsupportedStmtKind)

  test "__closure -> ceUnsupportedHof":
    declines(uClosureVar, "u_closure", ceUnsupportedHof)

  test "__ownership:Atomic -> heUnsupportedOwnership":
    declines(uAtomicVar, "u_atomic", heUnsupportedOwnership)

  test "__unsupported:* -> feUnsupportedParamType":
    declines(uUnsupportedVar, "u_weird", feUnsupportedParamType)

suite "S8ap: walker version":
  test "symexWalkerVersion >= 183":
    check parseInt(symexWalkerVersion) >= 183
