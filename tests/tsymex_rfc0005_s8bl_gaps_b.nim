## RFC-0005 (soundness channels) slice S8bl, items 3 and 4 -- S8bc's smaller
## remainders: `add` to a local seq of an unbacked element, a plain type
## alias, `for x in [a, b]`, `mpairs` / `mvalues`, a Table length change
## while iterating, a witness seq element with a ref part, and an element's
## nested seq longer than 1024.
##
## RFC-0005 S8cm: part 2 of 4 of this suite, with `tsymex_rfc0005_s8bl_gaps`,
## `tsymex_rfc0005_s8bl_gaps_d`, `tsymex_rfc0005_s8bl_gaps_c`. Split so that
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

# ---- (4) mpairs / mvalues ---------------------------------------------------

proc mpairsP(t: Table[string, int]) =
  if t.len > 2: return
  for k, v in t:
    if v < -100 or v > 100: return
  var u = t
  for k, v in u.mpairs:
    v += 1
  if "a" in t and u["a"] != t["a"] + 1: symexTarget("mpairs_dead")
  if "a" in t and u["a"] == 5: symexTarget("mpairs")

proc mvaluesP(t: Table[string, seq[int]]) =
  if t.len > 2: return
  var u = t
  for v in u.mvalues:
    v.add 7
  if "a" in t and u["a"].len != t["a"].len + 1: symexTarget("mvalues_dead")

type LW = object
  v: seq[int]

suite "S8bl (4): mpairs / mvalues / length change":
  test "mpairs writes the table (was a decline)":
    let d = symexFind(mpairsP, tLabel("mpairs_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(mpairsP, tLabel("mpairs"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(mpairsP(r.witness[0]), "mpairs")

  test "mvalues on a seq value":
    let d = symexFind(mvaluesP, tLabel("mvalues_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
