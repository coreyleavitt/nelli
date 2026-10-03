## RFC-0005 (soundness channels) slice S8bl, item 1 -- `setLen`, `add` to a
## seq element, `new` on a field, and the magics that decline by name.
## Before S8bl a string's `setLen` and `s[0].add c` were dropped (the magic
## registered with an empty body): a false sxSat.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasMsg(errs: seq[SymexErrorInfo], needle: string): bool =
  for e in errs:
    if needle in e.msg: return true
  false

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

proc slStr(s: string, n: int) =
  if n < 0 or n > 12 or s.len > 8: return
  var t = s
  t.setLen(n)
  if t.len != n: symexTarget("sl_str_dead")
  # The pad is NUL bytes, and a shrink keeps the prefix. Pinned on ground
  # strings here; over a symbolic one (a `str.at` of the concat, undecided
  # by both pinned Z3s until RFC-0005 S8bx) in `tsymex_rfc0005_s8bx_setlenstr`.
  if s == "ab" and n == 5 and t != "ab\0\0\0": symexTarget("sl_str_pad_dead")
  if n == s.len + 2 and s == "ab" and t[3] == '\0' and t[1] == 'b':
    symexTarget("sl_str_pad")
  if s == "abcdef" and n == 3 and t != "abc": symexTarget("sl_str_keep_dead")
  if n == 3 and s == "abcdef" and t == "abc": symexTarget("sl_str")

proc slSeq(s: seq[int], n: int) =
  if n < 0 or n > 50: return
  var t = s
  t.setLen(n)
  if t.len != n: symexTarget("sl_seq_dead")
  if n > s.len and t[n - 1] != 0: symexTarget("sl_seq_pad_dead")
  if s.len == 2 and n == 4 and t[1] == 5: symexTarget("sl_seq")

proc slTwice(s: seq[int]) =
  var t = s
  if t.len < 3: return
  t.setLen(1)
  t.setLen(3)
  if t[2] != 0: symexTarget("sl_twice_dead")

proc slNeg(n: int) =
  if n > 50: return
  var t = @[1, 2]
  try:
    t.setLen(n)
    if t.len < 0: symexTarget("sl_neg_dead")
  except RangeDefect:
    if n < 0: symexTarget("sl_neg")
    if n >= 0: symexTarget("sl_neg_dead2")

proc slUninit(s: seq[int], n: int) =
  if n < 0 or n > 50: return
  var t = s
  t.setLenUninit(n)
  if n > s.len: symexTarget("slu_grow")

proc slShrink(s: seq[int], n: int) =
  if n < 0 or n > s.len: return
  var t = s
  t.setLenUninit(n)
  if t.len != n: symexTarget("slu_dead")
  if n > 0 and t[n - 1] != s[n - 1]: symexTarget("slu_dead2")

proc addElem(s: seq[string]) =
  var t = s
  if t.len == 0: return
  t[0].add 'x'
  if t[0].len == 0: symexTarget("ae_dead")
  if t[0] == "qx": symexTarget("ae")

type Box = ref object
  v: int
type Holder = object
  b: Box

proc newField(x: int) =
  var h: Holder
  new(h.b)
  if h.b == nil or h.b.v != 0: symexTarget("nf_dead")
  if x == 2: symexTarget("nf")

proc plusEqCall(x: int) =
  var a = [x, 0]
  `+=`(a[1], 5)
  if a[1] != 5: symexTarget("pe_dead")

suite "S8bl (1): setLen":
  test "a string: the prefix, or the string padded with NUL bytes (was a false sxSat)":
    block:
      let d = symexFind(slStr, tLabel("sl_str_dead"))
      checkpoint "sl_str_dead" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(slStr, tLabel("sl_str_pad_dead"))
      checkpoint "sl_str_pad_dead" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(slStr, tLabel("sl_str_keep_dead"))
      checkpoint "sl_str_keep_dead" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    let r = symexFind(slStr, tLabel("sl_str"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(slStr(r.witness[0], r.witness[1]), "sl_str")
    let p = symexFind(slStr, tLabel("sl_str_pad"))
    checkpoint $p.status & " " & show(p.errors)
    check p.status == sxSat
    if p.status == sxSat:
      check reproduces(slStr(p.witness[0], p.witness[1]), "sl_str_pad")

  test "a seq: the prefix, or the seq padded with zeros":
    block:
      let d = symexFind(slSeq, tLabel("sl_seq_dead"))
      checkpoint "sl_seq_dead" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(slSeq, tLabel("sl_seq_pad_dead"))
      checkpoint "sl_seq_pad_dead" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    let r = symexFind(slSeq, tLabel("sl_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(slSeq(r.witness[0], r.witness[1]), "sl_seq")
    let t = symexFind(slTwice, tLabel("sl_twice_dead"))
    checkpoint $t.status & " " & show(t.errors)
    check t.status == sxUnsat

  test "a negative length raises RangeDefect":
    let r = symexFind(slNeg, tLabel("sl_neg"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(slNeg(r.witness[0]), "sl_neg")
    block:
      let d = symexFind(slNeg, tLabel("sl_neg_dead"))
      checkpoint "sl_neg_dead" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(slNeg, tLabel("sl_neg_dead2"))
      checkpoint "sl_neg_dead2" & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat

  test "setLenUninit: a shrink is exact, a grow declines by name":
    let d = symexFind(slShrink, tLabel("slu_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let d2 = symexFind(slShrink, tLabel("slu_dead2"))
    checkpoint $d2.status & " " & show(d2.errors)
    check d2.status == sxUnsat
    let g = symexFind(slUninit, tLabel("slu_grow"))
    checkpoint $g.status & " " & show(g.errors)
    check g.status == sxUnknown
    check g.errors.hasMsg("setLenUninit")

suite "S8bl (1): add to a seq element, new on a field, `+=` as a call":
  test "s[0].add c (was a false sxSat)":
    let d = symexFind(addElem, tLabel("ae_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(addElem, tLabel("ae"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(addElem(r.witness[0]), "ae")

  test "new(h.b)":
    let d = symexFind(newField, tLabel("nf_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(newField, tLabel("nf"))
    check r.status == sxSat

  test "`+=`(a[1], 5) spelled as a call":
    let d = symexFind(plusEqCall, tLabel("pe_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
