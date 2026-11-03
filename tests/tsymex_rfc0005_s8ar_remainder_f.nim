## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 8 of 8 of this suite, with
## `tsymex_rfc0005_s8ar_remainder`, `tsymex_rfc0005_s8ar_remainder_b`,
## `tsymex_rfc0005_s8ar_remainder_c`, `tsymex_rfc0005_s8ar_remainder_d`,
## `tsymex_rfc0005_s8ar_remainder_g`, `tsymex_rfc0005_s8ar_remainder_e`,
## `tsymex_rfc0005_s8ar_remainder_h`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 120 s).

import std/[unittest, strutils, sequtils, tables, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

type
  WKind = enum wkA, wkB
  WVar = ref object
    case kind: WKind
    of wkA: xs: seq[int]
    of wkB: hs: HashSet[int8]
  WHolder = ref object
    tp: (seq[int], int)
    a2: array[2, seq[int]]
    tt: Table[int, int]
    hs: HashSet[int8]
  ByValVar = object
    case kind: WKind
    of wkA: a: int
    of wkB: b: bool
  DSeq = distinct seq[int]
  DeclHolder = ref object
    bv: ByValVar
    n: int
  DeclHolder2 = ref object
    ds: DSeq
    n: int

proc declBV(p: DeclHolder) =
  if p != nil and p.n == 1: symexTarget("decl_bv")

proc declBVRead(p: DeclHolder) =
  if p != nil and p.bv.kind == wkB: symexTarget("decl_bv_read")

proc declDS(p: DeclHolder2) =
  if p != nil and p.n == 1: symexTarget("decl_ds")

proc declDSRead(p: DeclHolder2) =
  if p == nil: return
  let d = p.ds
  if p.n == 2: symexTarget("decl_ds_read")

proc declDSWrite(p: DeclHolder2) =
  if p == nil: return
  p.ds = DSeq(@[1])
  if p.n == 2: symexTarget("decl_ds_write")

type
  DeclHolder3 = ref object
    tc: (int, ByValVar)
    n: int

proc declTC(p: DeclHolder3) =
  if p != nil and p.n == 1: symexTarget("decl_tc")

proc declTCRead(p: DeclHolder3) =
  if p == nil: return
  let t = p.tc
  if p.n == 2: symexTarget("decl_tc_read")

proc declU8(t: Table[uint8, int]) =
  if 7'u8 in t and t[7'u8] == 3: symexTarget("decl_u8")

proc declChar(t: Table[char, string]) =
  if 'k' in t and t['k'] == "v": symexTarget("decl_char")

suite "S8ar: the declines that remained (closed by RFC-0005 S8at)":
  test "a by-value case object field: the field, not the parameter":
    let r = symexFind(declBV, tLabel("decl_bv"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(declBV(r.witness[0]), "decl_bv")
    # A scoped decline (`heUnsupportedPointeeRead`) until RFC-0005 S8at made
    # a by-value case object a tree-valued heap cell; the read is exact.
    let r2 = symexFind(declBVRead, tLabel("decl_bv_read"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    check r2.errors.len == 0
    if r2.status == sxSat:
      check reproduces(declBVRead(r2.witness[0]), "decl_bv_read")

  test "a distinct over a composite base: the field, not the parameter":
    let r = symexFind(declDS, tLabel("decl_ds"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(declDS(r.witness[0]), "decl_ds")
    # A scoped decline (`heUnsupportedPointeeRead`) until RFC-0005 S8at held
    # a distinct over a composite base as its base's leaves; the read and the
    # store are exact.
    let r2 = symexFind(declDSRead, tLabel("decl_ds_read"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    # Only `geDistinctBijectivitySkipped`, a `sevHint`, remains.
    check not r2.errors.anyIt(it.severity == sevError)
    if r2.status == sxSat:
      check reproduces(declDSRead(r2.witness[0]), "decl_ds_read")
    let r3 = symexFind(declDSWrite, tLabel("decl_ds_write"))
    checkpoint $r3.status & " " & show(r3.errors)
    check r3.status == sxSat
    check not r3.errors.anyIt(it.severity == sevError)   # an ill-sorted store before S8ar
    if r3.status == sxSat:
      check reproduces(declDSWrite(r3.witness[0]), "decl_ds_write")

  test "a tuple holding a by-value case object: the field, not the parameter":
    let r = symexFind(declTC, tLabel("decl_tc"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(declTC(r.witness[0]), "decl_tc")
    # The read was a havoc (`heUnsupportedPointeeRead`, replay-gated) until
    # RFC-0005 S8at made the case object a heap cell part; it is exact.
    let r2 = symexFind(declTCRead, tLabel("decl_tc_read"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    check r2.errors.len == 0
    if r2.status == sxSat:
      check reproduces(declTCRead(r2.witness[0]), "decl_tc_read")

  test "uint8- and char-keyed Table parameters render (S8am's isChar tells them apart)":
    let r = symexFind(declU8, tLabel("decl_u8"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(declU8(r.witness[0]), "decl_u8")
    let r2 = symexFind(declChar, tLabel("decl_char"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat: check reproduces(declChar(r2.witness[0]), "decl_char")

suite "S8ar: walker version floor":
  test "walker version floor >= 191":
    check parseInt(symexWalkerVersion) >= 191
