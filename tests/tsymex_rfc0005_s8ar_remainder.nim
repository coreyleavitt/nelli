## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 1 of 6 of this suite, with
## `tsymex_rfc0005_s8ar_remainder_b`, `tsymex_rfc0005_s8ar_remainder_c`,
## `tsymex_rfc0005_s8ar_remainder_d`, `tsymex_rfc0005_s8ar_remainder_e`,
## `tsymex_rfc0005_s8ar_remainder_f`. Split so that each part compiles and runs
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

type
  TNode = ref object
    kids: seq[TNode]
    v: int

  NObj = object
    kids: seq[NRef]
    v: int
  NRef = ref NObj
  VRec = object
    kids: seq[VRec]
    v: int

proc rKids(p: TNode) =
  if p != nil and p.kids.len == 2 and p.kids[1] != nil and p.kids[1].v == 3:
    symexTarget("r_kids")

proc rInd(p: NRef) =
  if p != nil and p.kids.len == 1 and p.kids[0] != nil and p.kids[0].v == 4:
    symexTarget("r_ind")

proc rVRec(p: VRec) =
  if p.v == 2: symexTarget("vrec_v")
  if p.kids.len == 1: symexTarget("vrec_kids")

suite "S8ar (1): a seq of the object's own ref type":
  test "classifies and is walked":
    let r = symexFind(rKids, tLabel("r_kids"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      check reproduces(rKids(r.witness[0]), "r_kids")

  test "a sym-indirection ref (NRef = ref NObj) through a seq field":
    let r = symexFind(rInd, tLabel("r_ind"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      check reproduces(rInd(r.witness[0]), "r_ind")

  test "a value object recurring through a seq is modelled to a bounded depth":
    # RFC-0005 S8bc re-pinned this. S8ar declined the field (a scoped
    # decline at the first recurrence); S8bc unrolls the value object to a
    # bounded depth, the seq at each level a leaf-split seq of the next, so
    # the length read is exact.
    let r = symexFind(rVRec, tLabel("vrec_v"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let r2 = symexFind(rVRec, tLabel("vrec_kids"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    check not r2.errors.hasKind(weInternalWalkerFault)
    if r2.status == sxSat: check reproduces(rVRec(r2.witness[0]), "vrec_kids")

proc sAdd(v: string) =
  var s: seq[string]
  s.add v
  if s.len == 1 and s[0] == "q": symexTarget("s_add")
  if s.len != 1: symexTarget("s_add_dead")

proc sAddCmp(a, b: string) =
  var s = @[a]
  s.add b
  if s[0] == s[1] and a.len == 2: symexTarget("s_eq")

proc sParam(s: seq[string]) =
  if s.len == 2 and s[1] == "zz": symexTarget("s_param")

suite "S8ar (2): a plain seq[string] is modelled, never a walker fault":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "add then read":
    let r = run(sAdd, "s_add", sxSat)
    if r.status == sxSat: check r.witness[0] == "q"
    discard run(sAdd, "s_add_dead", sxUnsat)

  test "element equality after add":
    let r = run(sAddCmp, "s_eq", sxSat)
    if r.status == sxSat: check r.witness[0] == r.witness[1]

  test "a seq[string] param renders":
    let r = run(sParam, "s_param", sxSat)
    if r.status == sxSat:
      check r.witness[0].len == 2 and r.witness[0][1] == "zz"
      check reproduces(sParam(r.witness[0]), "s_param")
