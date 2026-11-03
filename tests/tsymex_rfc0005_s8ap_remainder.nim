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
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_s8ap_remainder_b`, `tsymex_rfc0005_s8ap_remainder_c`,
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
