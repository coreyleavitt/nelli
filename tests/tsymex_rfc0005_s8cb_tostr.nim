## RFC-0005 S8cb, item 5 -- the system magics a walk can reach and no parser arm
## modelled, part 2: conversions to string and the ordering of strings and
## bools, and the hook and identity magics. `$` of a char or an enum was the
## decimal of its ordinal, a false `sxUnsat`; so was `$x` of a negative int
## (Z3's `int.to.str` of a negative is empty). `ensureMove` walked its `discard`
## body and yielded zero. Every expected value is checked against native Nim in
## the first test.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import ./s8cu_helpers except show

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if e.severity != sevHint: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

# RFC-0016 SND-02..04: each decided verdict is also a K9 pin, keyed to the magic
# row the `$` lowers through. `curKey` is set between groups of `c` calls.
var curKey = CellKey(scope: axMagic, key: "IntToStr")

template c(name: untyped, want: SymexStatusKind, body: untyped) {.dirty.} =
  proc name(x: int, y: int) =
    body
  test astToStr(name):
    let r = symexFind(name, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == want
    discard pinExact(name, curKey, tLabel("t"))

type
  E = enum ea, eb, ec
  F = enum fa = "hello", fb = (5, "five"), fc = 7
  Sub = range[3 .. 9]

suite "RFC-0005 S8cb tostr: the walker floor":
  test "symexWalkerVersion is at least 243":
    check parseInt(symexWalkerVersion) >= 243

suite "RFC-0005 S8cb tostr: native Nim":
  test "the expected values":
    var n = -5; var ch = 'a'; var en = eb; var fv = fa; var t = true
    var s = "ab"; var r = "b"
    check $n == "-5" and $low(int) == "-9223372036854775808"
    check $ch == "a" and $en == "eb" and $fv == "hello" and $t == "true"
    fv = fb
    check $fv == "five" and ord(fv) == 5
    fv = fc
    check $fv == "fc" and ord(fv) == 7
    check $s == "ab" and s < r and s <= r and r > s and r >= s and not (r < s)
    check "" < "a" and "a" <= "a" and not ("a" < "a")
    var f = false
    check f < t and f <= t and t > f and t >= f and not (t < f) and not (t <= f)
    check t <= t and not (t < t)
    check repr(t) == "true" and repr(en) == "eb"
    let arr = [1, 2, 3]
    check @arr == @[1, 2, 3]
    var m = 1
    let mm = ensureMove(m)
    check mm == 1
    let d = `=dup`(n)
    check d == -5

suite "RFC-0005 S8cb tostr: dollar of a negative int":
  c(negs, sxSat): (if $x == "-5" and x == -5: symexTarget("t"))
  c(negsu, sxUnsat): (if $x == "-5" and x != -5: symexTarget("t"))
  c(negsempty, sxUnsat): (if $x == "": symexTarget("t"))
  c(lowintu, sxUnsat): (if x == low(int) and $x != "-9223372036854775808": symexTarget("t"))
  c(poss, sxSat): (if $x == "12" and x == 12: symexTarget("t"))
  c(int8neg, sxSat):
    let a = int8(x and 7) - 8'i8
    if $a == "-8" and a == -8'i8: symexTarget("t")
  c(unsignedhighu, sxUnsat):
    let u = uint64(x and 1) + 18446744073709551614'u64
    if $u == "-1" or $u == "-2": symexTarget("t")

suite "RFC-0005 S8cb tostr: dollar of a char, enum, bool, string":
  curKey = CellKey(scope: axMagic, key: "CharToStr")
  c(charname, sxSat):
    let a = if x > 0: 'a' else: 'b'
    if $a == "a": symexTarget("t")
  c(charordu, sxUnsat):
    let a = if x > 0: 'a' else: 'b'
    if $a == "97": symexTarget("t")
  curKey = CellKey(scope: axMagic, key: "EnumToStr")
  c(enumname, sxSat):
    let a = if x > 0: ea else: eb
    if $a == "ea" and x > 0: symexTarget("t")
  c(enumother, sxUnsat):
    let a = if x > 0: ea else: eb
    if $a == "ea" and x <= 0: symexTarget("t")
  c(enumordu, sxUnsat):
    let a = if x > 0: ea else: eb
    if $a == "0": symexTarget("t")
  c(enumstrname, sxSat):
    let a = if x > 0: fa else: fb
    if $a == "hello" and x > 0: symexTarget("t")
  c(enumstrnameb, sxSat):
    let a = if x > 0: fa else: fb
    if $a == "five" and x <= 0: symexTarget("t")
  c(enumstrnameu, sxUnsat):
    let a = if x > 0: fa else: fc
    if $a == "fa": symexTarget("t")
  c(enumstrnamec, sxSat):
    let a = if x > 0: fa else: fc
    if $a == "fc" and x <= 0: symexTarget("t")
  curKey = CellKey(scope: axMagic, key: "BoolToStr")
  c(booltrue, sxSat): (if $(x > 0) == "true" and x == 1: symexTarget("t"))
  c(booltrueu, sxUnsat): (if $(x > 0) == "true" and x == 0: symexTarget("t"))
  c(boolfalse, sxSat): (if $(x > 0) == "false" and x == 0: symexTarget("t"))
  c(boolother, sxUnsat): (if $(x > 0) == "1": symexTarget("t"))
  curKey = CellKey(scope: axMagic, key: "StrToStr")
  c(strid, sxSat):
    let s = if x > 0: "a" else: "b"
    if $s == "a" and x == 1: symexTarget("t")
  c(stridu, sxUnsat):
    let s = if x > 0: "a" else: "b"
    if $s == "a" and x == 0: symexTarget("t")
  curKey = CellKey(scope: axMagic, key: "CharToStr")
  c(callformchar, sxUnsat):
    let a = if x > 0: 'a' else: 'b'
    if `$`(a) == "97": symexTarget("t")
  curKey = CellKey(scope: faCallShape, key: "repr")
  c(reprbool, sxUnsat): (if repr(x > 0) == "true" and x == 0: symexTarget("t"))
  c(reprenum, sxUnsat):
    let a = if x > 0: ea else: eb
    if repr(a) == "ea" and x <= 0: symexTarget("t")
  curKey = CellKey(scope: axMagic, key: "Echo")
  c(echochar, sxSat):
    let a = if x > 0: 'a' else: 'b'
    echo a
    if x == 1: symexTarget("t")
  c(debugechoint, sxSat):
    debugEcho x
    if x == 1: symexTarget("t")
