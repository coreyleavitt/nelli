## RFC-0005 (soundness channels) slice S8bl, items 3 and 4 -- S8bc's smaller
## remainders: `add` to a local seq of an unbacked element, a plain type
## alias, `for x in [a, b]`, `mpairs` / `mvalues`, a Table length change
## while iterating, a witness seq element with a ref part, and an element's
## nested seq longer than 1024.
##
## RFC-0005 S8cm: part 4 of 4 of this suite, with `tsymex_rfc0005_s8bl_gaps`,
## `tsymex_rfc0005_s8bl_gaps_b`, `tsymex_rfc0005_s8bl_gaps_d`. Split so that
## each part compiles and runs in under 60 s on the Windows legs (the whole
## file took 71 s).

import std/[unittest, strutils, tables, hashes]
import nelli
import nelli/symex
import nelli/smt/types

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

# ---- (4) a Table length change while iterating ------------------------------

proc lenChange(t: Table[string, int]) =
  if t.len > 2: return
  var u = t
  try:
    for k, v in u.pairs:
      if k == "a": u["zz"] = 1
  except AssertionDefect:
    if "a" in t and "zz" notin t: symexTarget("len_change")

# ---- (4) witnesses ----------------------------------------------------------

type RW = object
  id: int
  p: ref int

proc refElem(s: seq[RW]) =
  if s.len == 2 and s[1].p != nil and s[1].p[] == 6 and s[0].p == nil:
    symexTarget("ref_elem")

type LW = object
  v: seq[int]

proc longNested(s: seq[LW]) =
  if s.len == 1 and s[0].v.len > 1500: symexTarget("long_nested")

suite "S8bl (4): mpairs / mvalues / length change":
  test "a length change raises AssertionDefect (was a decline)":
    let r = symexFind(lenChange, tLabel("len_change"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(lenChange(r.witness[0]), "len_change")

suite "S8bl (4): witnesses":
  test "a seq element with a ref part renders":
    let r = symexFind(refElem, tLabel("ref_elem"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(refElem(r.witness[0]), "ref_elem")

  test "an element's nested seq longer than 1024 renders":
    let r = symexFind(longNested, tLabel("long_nested"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(longNested(r.witness[0]), "long_nested")
