## RFC-0005 (soundness channels) slice S8bl, items 3 and 4 -- S8bc's smaller
## remainders: `add` to a local seq of an unbacked element, a plain type
## alias, `for x in [a, b]`, `mpairs` / `mvalues`, a Table length change
## while iterating, a witness seq element with a ref part, and an element's
## nested seq longer than 1024.
##
## RFC-0005 S8cm: part 3 of 4 of this suite, with `tsymex_rfc0005_s8bl_gaps`,
## `tsymex_rfc0005_s8bl_gaps_b`, `tsymex_rfc0005_s8bl_gaps_c`. Split so that
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

proc mpairsBreak(t: Table[string, int]) =
  if t.len > 2: return
  var u = t
  for k, v in u.mpairs:
    v = 9
    break
  if t.len > 0 and u.len != t.len: symexTarget("mpb_dead")
  if t.len == 1 and "a" in t and u["a"] != 9: symexTarget("mpb_dead2")

# Two iterations of one input table. Each enumerates the keys afresh, so a
# key term of one path's enumeration is free on another; unconstrained, it
# took a codepoint above 255 in the model, and the table extractor's read of
# it raised inside the walk: a walker fault on C++, a false sxUnsat on C.
proc twoIters(t: Table[string, int]) =
  if t.len > 2: return
  for k, v in t:
    if v < -100 or v > 100: return
  var s = 0
  for k, v in t.pairs:
    s += v
  if "a" in t and t["a"] == 4 and t.len == 1: symexTarget("two_iters")

type LW = object
  v: seq[int]

suite "S8bl (4): mpairs / mvalues / length change":
  test "a write before a break is kept":
    block:
      let d = symexFind(mpairsBreak, tLabel("mpb_dead"))
      checkpoint "mpb_dead" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(mpairsBreak, tLabel("mpb_dead2"))
      checkpoint "mpb_dead2" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat

  test "two iterations of one table (was a false sxUnsat on C)":
    let r = symexFind(twoIters, tLabel("two_iters"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(twoIters(r.witness[0]), "two_iters")
