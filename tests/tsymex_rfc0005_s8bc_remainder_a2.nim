## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part a: getOrDefault, inlined-iterator parameter conversions, seq[char] / seq[enum]
## witnesses, non-operator {.borrow.} routines (items 1, 8, 9, 2).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_a`, `tsymex_rfc0005_s8bc_remainder_a3`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 69 s).

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

# ---- (8) a conversion of an inlined iterator's parameter --------------------

iterator twice(n: int): int =
  yield int(n)
  yield int(n) + 1

proc icPlain(x: int) =
  if x < -1000 or x > 1000: return
  var s = 0
  for y in twice(x): s += y
  if s == 7: symexTarget("ic_plain")
  if s mod 2 == 0: symexTarget("ic_plain_dead")

iterator widen(n: int8): int =
  yield int(n) * 2

proc icWiden(x: int8) =
  for y in widen(x):
    if y == -256: symexTarget("ic_widen")
    if y > 254: symexTarget("ic_widen_dead")

iterator narrowed(n: int32): int =
  # `yield n` is a hidden int32 -> int conversion of the parameter.
  yield n

proc icHidden(x: int32) =
  for y in narrowed(x):
    if y == -5: symexTarget("ic_hidden")
    if y > int(high(int32)): symexTarget("ic_hidden_dead")

iterator asU8(n: int): uint8 =
  yield uint8(n and 0xFF)

proc icMasked(x: int) =
  for y in asU8(x):
    if y == 200'u8 and x > 1000: symexTarget("ic_masked")

proc litConv(y: int) =
  # `high(int32)` folds to an int32 literal; its explicit widening was a
  # walker fault (`lowerConvIntWidth`: a 64-bit operand), with no iterator.
  if y > int(high(int32)) and y < int(high(int32)) + 3: symexTarget("lit_conv")
  if y < int(low(int8)) and y > int(-131'i16): symexTarget("lit_conv2")
  if y > int(high(int32)) and y < int(high(int32)) + 1:
    symexTarget("lit_conv_dead")

suite "S8bc (8): a conversion of an inlined iterator's parameter":
  test "an explicit widening of a typed literal (not a walker fault)":
    let r = symexFind(litConv, tLabel("lit_conv"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] in 2147483648 .. 2147483649
      check reproduces(litConv(r.witness[0]), "lit_conv")
    let r2 = symexFind(litConv, tLabel("lit_conv2"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat: check reproduces(litConv(r2.witness[0]), "lit_conv2")
    let d = symexFind(litConv, tLabel("lit_conv_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "int(n) of an int parameter":
    let r = symexFind(icPlain, tLabel("ic_plain"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(icPlain(r.witness[0]), "ic_plain")
    let d = symexFind(icPlain, tLabel("ic_plain_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a widening conversion of an int8 parameter":
    let r = symexFind(icWiden, tLabel("ic_widen"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(icWiden(r.witness[0]), "ic_widen")
    let d = symexFind(icWiden, tLabel("ic_widen_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a hidden conversion of an int32 parameter":
    let r = symexFind(icHidden, tLabel("ic_hidden"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(icHidden(r.witness[0]), "ic_hidden")
    let d = symexFind(icHidden, tLabel("ic_hidden_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a narrowing conversion of an expression over the parameter":
    let r = symexFind(icMasked, tLabel("ic_masked"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(icMasked(r.witness[0]), "ic_masked")

# ---- (9) seq[char] / seq[enum] witnesses ------------------------------------

type Col = enum cRed, cGreen, cBlue

proc chSeq(s: seq[char]) =
  if s.len == 2 and s[0] == 'q' and s[1] == 'z': symexTarget("ch_seq")

proc enSeq(s: seq[Col]) =
  if s.len == 1 and s[0] == cBlue: symexTarget("en_seq")

proc enArr(a: array[2, Col]) =
  if a[0] == cGreen and a[1] == cBlue: symexTarget("en_arr")

type CHold = object
  cs: seq[char]
  es: seq[Col]

proc chObj(h: CHold) =
  if h.cs.len == 1 and h.cs[0] == 'x' and h.es.len == 1 and h.es[0] == cRed:
    symexTarget("ch_obj")

proc chTabSeq(t: Table[string, seq[char]]) =
  if "k" in t and t["k"].len == 1 and t["k"][0] == 'm': symexTarget("ch_tabseq")

proc enSet(s: HashSet[Col]) =
  if s.len == 1 and cGreen in s: symexTarget("en_set")

suite "S8bc (9): a seq[char] / seq[enum] witness replays at its own type":
  test "seq[char]":
    let r = symexFind(chSeq, tLabel("ch_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      checkpoint $r.witness
      replays(chSeq(r.witness[0]), "ch_seq")

  test "seq[enum]":
    let r = symexFind(enSeq, tLabel("en_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      checkpoint $r.witness
      replays(enSeq(r.witness[0]), "en_seq")

  test "array[2, enum]":
    let r = symexFind(enArr, tLabel("en_arr"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(enArr(r.witness[0]), "en_arr")

  test "seq[char] and seq[enum] object fields":
    let r = symexFind(chObj, tLabel("ch_obj"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(chObj(r.witness[0]), "ch_obj")

  test "a seq[char] Table value":
    let r = symexFind(chTabSeq, tLabel("ch_tabseq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(chTabSeq(r.witness[0]), "ch_tabseq")

  test "HashSet[enum]":
    let r = symexFind(enSet, tLabel("en_set"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(enSet(r.witness[0]), "en_set")

# ---- (2) a non-operator {.borrow.} routine ----------------------------------
#
# RFC-0005 S8bc: a borrowed routine has no body (its `getImpl` body is the
# base routine's symbol); `f(a)` is the base routine on `T(a)`, rewrapped
# when `f` returns the distinct. It was walked as a user routine whose body,
# that bare symbol, declined (`feUnsupportedStmtKind`).

type
  BSq = distinct seq[int]
  BM = distinct int
  BName = distinct string
  BBox = object
    w: int
  BDBox = distinct BBox

proc len(d: BSq): int {.borrow.}
proc `$`(m: BM): string {.borrow.}
proc len(n: BName): int {.borrow.}
proc add(d: var BSq, x: int) {.borrow.}
