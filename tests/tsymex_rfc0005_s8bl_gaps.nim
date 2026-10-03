## RFC-0005 (soundness channels) slice S8bl, items 3 and 4 -- S8bc's smaller
## remainders: `add` to a local seq of an unbacked element, a plain type
## alias, `for x in [a, b]`, `mpairs` / `mvalues`, a Table length change
## while iterating, a witness seq element with a ref part, and an element's
## nested seq longer than 1024.
import std/[unittest, strutils, tables, hashes]
import nelli
import nelli/symex
import nelli/smt/types

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

# ---- (3) add to a local seq of an unbacked element --------------------------

proc addUnbacked(x: int) =
  var p: seq[seq[int]] = @[]
  p.add(@[x])
  if x == 4: symexTarget("add_unbacked")

# ---- (4) a plain alias ------------------------------------------------------

type Meters = int

proc aliasHash(s: string) =
  var hc: Hash
  hc = hash(s)
  if (hc and 7) == 3 and s.len == 1: symexTarget("alias_hash")

proc aliasParam(m: Meters) =
  if m < -100 or m > 100: return
  if m * 2 == 14: symexTarget("alias_param")
  if m * 2 == 15: symexTarget("alias_param_dead")

# ---- (4) for over an array literal ------------------------------------------

proc forLit(a, b: int) =
  if a < -100 or a > 100 or b < -100 or b > 100: return
  var s = 0
  for x in [a, b]: s += x
  if s == 9 and a == 4: symexTarget("for_lit")
  if s != a + b: symexTarget("for_lit_dead")

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

suite "S8bl (3): add to a seq of an unbacked element":
  test "a placeholder decline, not a walker fault":
    let r = symexFind(addUnbacked, tLabel("add_unbacked"))
    checkpoint $r.status & " " & show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)
    check r.status in {sxSat, sxUnknown}

suite "S8bl (4): plain alias, array literal loop":
  test "`Hash = int` is an int (was a scoped decline)":
    let r = symexFind(aliasHash, tLabel("alias_hash"))
    checkpoint $r.status & " " & show(r.errors)
    check not r.errors.hasKind(feUnsupportedParamType)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a user alias param":
    let r = symexFind(aliasParam, tLabel("alias_param"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(aliasParam(r.witness[0]), "alias_param")
    let d = symexFind(aliasParam, tLabel("alias_param_dead"))
    check d.status == sxUnsat

  test "for x in [a, b] (was a walker fault)":
    let r = symexFind(forLit, tLabel("for_lit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(forLit(r.witness[0], r.witness[1]), "for_lit")
    let d = symexFind(forLit, tLabel("for_lit_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

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
