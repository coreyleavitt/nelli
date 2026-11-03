## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part b: array-element insert, newSeq, mgetOrPut and inc / dec / += on an element
## (items 4, 5, 7).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_b2`, `tsymex_rfc0005_s8bc_remainder_b3`.
## Split so that each part compiles and runs in under 60 s on the Windows legs
## (the whole file took 74 s).

import std/[unittest, strutils, sequtils, tables, sets, hashes]
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

template replays(call: untyped; label: string) =
  ## The witness is typed (the parameter was not demoted) and replays.
  when compiles(call):
    check reproduces(call, label)
  else:
    checkpoint "the witness of `" & astToStr(call) & "` is not typed"
    check false

# ---- (4) insert on an array element ------------------------------------------
#
# RFC-0005 S8bc: `a[i].insert(x, j)` takes the bare arm's two phases (S8ar):
# grow, write back, then place on the grown element. It fell to the generic
# call (`system.insert` inlined to an unsupported `when`).

type AIHold = object
  a: array[2, seq[int]]

proc aiMid(v: int, j: int) =
  if j < 0 or j > 2: return
  var a: array[2, seq[int]]
  a[1] = @[5, 6]
  a[1].insert(v, j)
  if a[1].len == 3 and a[1][1] == v and a[1][0] == 5 and a[1][2] == 6:
    symexTarget("ai_mid")
  if a[1].len != 3: symexTarget("ai_mid_dead")
  if a[0].len != 0: symexTarget("ai_other_dead")

proc aiRange(j: int) =
  var a: array[2, seq[int]]
  a[0] = @[1, 2]
  try:
    a[0].insert(9, j)
  except RangeDefect:
    if a[0].len == 2: symexTarget("ai_range")
  except IndexDefect:
    if a[0].len == 3 and a[0][2] == 0: symexTarget("ai_index_grown")
    if a[0].len != 3: symexTarget("ai_index_dead")

proc aiField(h: AIHold, v: int) =
  var g = h
  let n0 = g.a[0].len
  g.a[0].insert(v, 0)
  if g.a[0].len == n0 + 1 and g.a[0][0] == v and n0 == 1 and g.a[0][1] == 4:
    symexTarget("ai_field")
  if g.a[0].len != n0 + 1: symexTarget("ai_field_dead")

proc aiTab(t: Table[string, seq[int]], v: int) =
  var u = t
  if "k" in u:
    u["k"].insert(v, 0)
    if u["k"][0] == v and u["k"].len == 2 and u["k"][1] == 3:
      symexTarget("ai_tab")

suite "S8bc (4): insert on an array element":
  test "insert in the middle of an array element":
    let r = symexFind(aiMid, tLabel("ai_mid"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == 1
      check reproduces(aiMid(r.witness[0], r.witness[1]), "ai_mid")
    let d = symexFind(aiMid, tLabel("ai_mid_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let o = symexFind(aiMid, tLabel("ai_other_dead"))
    checkpoint $o.status & " " & show(o.errors)
    check o.status == sxUnsat

  test "RangeDefect before any change, IndexDefect after the grow":
    let r = symexFind(aiRange, tLabel("ai_range"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(aiRange(r.witness[0]), "ai_range")
    let g = symexFind(aiRange, tLabel("ai_index_grown"))
    checkpoint $g.status & " " & show(g.errors)
    check g.status == sxSat
    if g.status == sxSat:
      check g.witness[0] > 2
      check reproduces(aiRange(g.witness[0]), "ai_index_grown")
    let d = symexFind(aiRange, tLabel("ai_index_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an array field of a value object":
    let r = symexFind(aiField, tLabel("ai_field"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(aiField(r.witness[0], r.witness[1]), "ai_field")
    let d = symexFind(aiField, tLabel("ai_field_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a Table value":
    let r = symexFind(aiTab, tLabel("ai_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(aiTab(r.witness[0], r.witness[1]), "ai_tab")
