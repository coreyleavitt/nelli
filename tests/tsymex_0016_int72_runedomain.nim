## RFC-0016 INT-72: a `Rune` the walker does not produce itself ranges over
## its native domain.
##
## `Rune` is `distinct int32` (std/unicode), and no constructor checks a code
## point: a caller passes any int32, negatives included. The walker pinned a
## free `Rune` to [0, 0x10FFFF] (ADR-0017), so `r.ord > 0x10FFFF` was
## `sxUnsat` while native `Rune(2147483646)` reached it. A free `Rune` now
## ranges over int32, and each operation the walker models on one follows
## std/unicode 2.2.10 for an out-of-range value:
##   * `$r` / `toUTF8(r)`: `fastToUTF8Copy` compares unsigned, so a value up
##     to 0x1FFFFF is four bytes, up to 0x3FFFFFF five, up to 0x7FFFFFFF six,
##     and a negative one falls through every arm: the empty string;
##   * `size(r)`: the same thresholds over `r.uint32`, and 1 for a negative;
##   * `Rune(n)`: an int32 conversion, `RangeDefect` outside int32;
##   * `uint32(r)` and every int conversion of a Rune: of its int32 value;
##   * a decoded literal is decoded by Nim's own decoder, so a valid UTF-8
##     literal yields code points and an invalid one what the decoder makes of
##     it (`"\xF7\xBF\xBF\xBF"` is 0x1FFFFF).
## Every verdict is pinned natively (`pinFind`, `s8cu_helpers`).

import std/[unittest, unicode, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

proc aboveMax(r: Rune) =
  if r.ord > 0x10FFFF: symexTarget("above")

proc negative(r: Rune) =
  if r.ord < 0: symexTarget("neg")

proc utf8Four(r: Rune) =
  if r.ord > 0x10FFFF and $r == "\xF4\x90\x80\x80": symexTarget("four")

proc utf8Five(r: Rune) =
  if $r == "\xF8\x88\x80\x80\x80": symexTarget("five")

proc utf8Six(r: Rune) =
  if toUTF8(r) == "\xFD\xBF\xBF\xBF\xBF\xBF": symexTarget("six")

proc utf8Empty(r: Rune) =
  if r.ord < 0 and ($r).len == 0: symexTarget("empty")

proc utf8EmptyNonNeg(r: Rune) =
  if r.ord >= 0 and toUTF8(r).len == 0: symexTarget("never")

proc sizeSix(r: Rune) =
  if size(r) == 6: symexTarget("six")

proc sizeNeg(r: Rune) =
  if r.ord < 0 and size(r) == 1: symexTarget("negOne")

proc sizeFiveInRange(r: Rune) =
  if size(r) == 5 and r.ord <= 0x10FFFF: symexTarget("never")

proc fromIntNeg(n: int) =
  let r = Rune(n)
  if r.ord < 0: symexTarget("neg")

proc fromIntWide(n: int) =
  let r = Rune(n)
  if n > int(high(int32)): symexTarget("wide")
  discard r

proc asUint32(r: Rune) =
  if r.uint32 > 0x8000_0000'u32: symexTarget("big")

proc decodedValid(x: int) =
  for r in "aé€😀".runes:
    if r.ord > 0x10FFFF or r.ord < 0: symexTarget("never")

proc decodedInvalid(x: int) =
  for r in "\xF7\xBF\xBF\xBF".runes:
    if r.ord > 0x10FFFF: symexTarget("above")

suite "INT-72: a free Rune is any int32":
  test "a Rune parameter above 0x10FFFF is reachable":
    let r = pinFind(aboveMax, tLabel("above"))
    check r.status == sxSat
    check r.witness[0] > 0x10FFFF

  test "a negative Rune parameter is reachable":
    let r = pinFind(negative, tLabel("neg"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "Rune(n) keeps a negative int32":
    let r = pinFind(fromIntNeg, tLabel("neg"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "Rune(n) outside int32 raises RangeDefect before the target":
    let r = pinFind(fromIntWide, tLabel("wide"))
    check r.status == sxRaised   # the label is past the raise on every path
    let e = pinFind(fromIntWide, tRaisedExn("RangeDefect"))
    check e.status == sxRaised
    if e.status == sxRaised:
      check e.raisedWitness[0] > int(high(int32)) or
            e.raisedWitness[0] < int(low(int32))

  test "uint32(r) of a negative Rune keeps its low 32 bits":
    let r = pinFind(asUint32, tLabel("big"))
    check r.status == sxSat
    check r.witness[0] < 0

suite "INT-72: $r, toUTF8 and size follow std/unicode out of range":
  test "0x110000 encodes as four bytes":
    let r = pinFind(utf8Four, tLabel("four"))
    check r.status == sxSat
    check r.witness[0] == 0x110000

  test "0x200000 encodes as five bytes":
    let r = pinFind(utf8Five, tLabel("five"))
    check r.status == sxSat
    check r.witness[0] == 0x200000

  test "0x7FFFFFFF encodes as six bytes (toUTF8)":
    let r = pinFind(utf8Six, tLabel("six"))
    check r.status == sxSat
    check r.witness[0] == 0x7FFFFFFF

  test "a negative Rune encodes as the empty string":
    let r = pinFind(utf8Empty, tLabel("empty"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "a non-negative Rune never encodes as the empty string":
    let r = pinFind(utf8EmptyNonNeg, tLabel("never"))
    check r.status == sxUnsat

  test "size is 6 above 0x3FFFFFF":
    let r = pinFind(sizeSix, tLabel("six"))
    check r.status == sxSat
    check r.witness[0] > 0x3FFFFFF

  test "size of a negative Rune is 1":
    let r = pinFind(sizeNeg, tLabel("negOne"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "size is never 5 for a code point":
    let r = pinFind(sizeFiveInRange, tLabel("never"))
    check r.status == sxUnsat

suite "INT-72: a decoded Rune is what Nim's decoder returns":
  test "a valid UTF-8 literal decodes to code points only":
    let r = pinFind(decodedValid, tLabel("never"))
    check r.status == sxUnsat

  test "an invalid four-byte lead decodes above 0x10FFFF":
    let r = pinFind(decodedInvalid, tLabel("above"))
    check r.status == sxSat

suite "INT-72: walker version":
  test "walker version floor >= 426":
    check parseInt(symexWalkerVersion) >= 426
