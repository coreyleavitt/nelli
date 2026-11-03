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
## RFC-0005 S8cm: part 4 of 4 of this suite, with
## `tsymex_rfc0005_s8ap_remainder`, `tsymex_rfc0005_s8ap_remainder_b`,
## `tsymex_rfc0005_s8ap_remainder_c`. Split so that each part compiles and runs
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
  # RFC-0005 S8bw classifies a generic case object; a generic case object
  # below another (a case part at two levels) is still unrecognised.
  WeirdK = enum wkA, wkB
  WeirdBase[T] = object of RootObj
    case wk: WeirdK
    of wkA: wx: T
    of wkB: discard
  Weird[T] = object of WeirdBase[T]
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
