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

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if e.severity != sevHint: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

template c(name: untyped, want: SymexStatusKind, body: untyped) {.dirty.} =
  proc name(x: int, y: int) =
    body
  test astToStr(name):
    let r = symexFind(name, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == want

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
  c(charname, sxSat):
    let a = if x > 0: 'a' else: 'b'
    if $a == "a": symexTarget("t")
  c(charordu, sxUnsat):
    let a = if x > 0: 'a' else: 'b'
    if $a == "97": symexTarget("t")
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
  c(booltrue, sxSat): (if $(x > 0) == "true" and x == 1: symexTarget("t"))
  c(booltrueu, sxUnsat): (if $(x > 0) == "true" and x == 0: symexTarget("t"))
  c(boolfalse, sxSat): (if $(x > 0) == "false" and x == 0: symexTarget("t"))
  c(boolother, sxUnsat): (if $(x > 0) == "1": symexTarget("t"))
  c(strid, sxSat):
    let s = if x > 0: "a" else: "b"
    if $s == "a" and x == 1: symexTarget("t")
  c(stridu, sxUnsat):
    let s = if x > 0: "a" else: "b"
    if $s == "a" and x == 0: symexTarget("t")
  c(callformchar, sxUnsat):
    let a = if x > 0: 'a' else: 'b'
    if `$`(a) == "97": symexTarget("t")
  c(reprbool, sxUnsat): (if repr(x > 0) == "true" and x == 0: symexTarget("t"))
  c(reprenum, sxUnsat):
    let a = if x > 0: ea else: eb
    if repr(a) == "ea" and x <= 0: symexTarget("t")
  c(echochar, sxSat):
    let a = if x > 0: 'a' else: 'b'
    echo a
    if x == 1: symexTarget("t")
  c(debugechoint, sxSat):
    debugEcho x
    if x == 1: symexTarget("t")

suite "RFC-0005 S8cb tostr: string and bool ordering":
  proc strSut(s: string, r: string) =
    if s < r and s == "ab" and r == "b": symexTarget("t")
  proc strUnsat(s: string, r: string) =
    if s < r and r == "": symexTarget("t")
  proc strLe(s: string, r: string) =
    if s <= r and r == "a" and s == "a": symexTarget("t")
  proc strLeu(s: string, r: string) =
    if s <= r and r == "a" and s == "b": symexTarget("t")
  proc strGt(s: string, r: string) =
    if s > r and s == "b" and r == "ab": symexTarget("t")
  proc strGeu(s: string, r: string) =
    if s >= r and s == "ab" and r == "b": symexTarget("t")
  proc strIrr(s: string) =
    if s < s: symexTarget("t")
  test "string lt":
    check symexFind(strSut, tLabel("t")).status == sxSat
  test "nothing is below the empty string":
    check symexFind(strUnsat, tLabel("t")).status == sxUnsat
  test "string le":
    check symexFind(strLe, tLabel("t")).status == sxSat
  test "string le refuted":
    check symexFind(strLeu, tLabel("t")).status == sxUnsat
  test "string gt":
    check symexFind(strGt, tLabel("t")).status == sxSat
  test "string ge refuted":
    check symexFind(strGeu, tLabel("t")).status == sxUnsat
  test "string lt is irreflexive":
    check symexFind(strIrr, tLabel("t")).status == sxUnsat
  c(boollt, sxSat): (if (x > 0) < (y > 0) and x == 0 and y == 1: symexTarget("t"))
  c(boolltu, sxUnsat): (if (x > 0) < (y > 0) and x == 1: symexTarget("t"))
  c(boolle, sxSat): (if (x > 0) <= (y > 0) and x == 0 and y == 0: symexTarget("t"))
  c(boolleu, sxUnsat): (if (x > 0) <= (y > 0) and x == 1 and y == 0: symexTarget("t"))
  c(boolgtu, sxUnsat): (if (x > 0) > (y > 0) and x == 0: symexTarget("t"))
  c(boolgeu, sxUnsat): (if (x > 0) >= (y > 0) and x == 0 and y == 1: symexTarget("t"))

suite "RFC-0005 S8cb tostr: identity, hook and exit magics":
  c(ensuremove, sxSat):
    var a = x
    let b = ensureMove(a)
    if b == 1 and x == 1: symexTarget("t")
  c(ensuremoveu, sxUnsat):
    var a = x
    let b = ensureMove(a)
    if b == 1 and x == 2: symexTarget("t")
  c(dup, sxSat):
    let a = `=dup`(x)
    if a == 3 and x == 3: symexTarget("t")
  c(dupu, sxUnsat):
    let a = `=dup`(x)
    if a == 3 and x == 4: symexTarget("t")
  c(sinkcall, sxUnsat):
    var a = 1
    `=sink`(a, x)
    if a != x: symexTarget("t")
  c(arrtoseq, sxSat):
    let a = [x, y]
    let s = @a
    if s[1] == 4 and y == 4 and s.len == 2: symexTarget("t")
  c(arrtoseq2, sxUnsat):
    let a = [x, y]
    let s = @a
    if s[1] == 4 and y == 5: symexTarget("t")
  c(quitends, sxUnsat):
    if x > 0: quit(1)
    if x == 1: symexTarget("t")
  c(quitother, sxSat):
    if x > 0: quit(1)
    if x == 0: symexTarget("t")
  c(quitarg, sxUnsat):
    var a = 0
    if x > 0:
      a = 1
      quit(a)
    if a == 1: symexTarget("t")
  c(quitnofinally, sxUnsat):
    try:
      if x > 0: quit(1)
    finally:
      if x == 1: symexTarget("t")
  c(quitexpr, sxUnsat):
    let a = if x > 0: quit(1) else: 2
    if a != 2: symexTarget("t")
  c(quitmsg, sxUnsat):
    if x > 0: quit("stop", 2)
    if x == 1: symexTarget("t")
  c(quitexprstr, sxUnsat):
    let a = if x > 0: quit(1) else: "b"
    if a != "b": symexTarget("t")

proc reprSut(s: string) =
  if repr(s) == "x": symexTarget("t")

suite "RFC-0005 S8cb tostr: what stays declined":
  test "repr of a string declines at the call":
    let r = symexFind(reprSut, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
