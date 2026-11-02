## RFC-0005 (soundness channels) slice S8cb, item 5, continued from
## `tsymex_rfc0005_s8cb_tostr` (split for the per-file time convention).
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
