## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 4 of 7 of this suite, with
## `tsymex_rfc0005_s8ax_remainder`, `tsymex_rfc0005_s8ax_remainder_b`,
## `tsymex_rfc0005_s8ax_remainder_c`, `tsymex_rfc0005_s8ax_remainder_e`,
## `tsymex_rfc0005_s8ax_remainder_f`, `tsymex_rfc0005_s8ax_remainder_g`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 132 s).

import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template clean(fn: typed, lbl: string, want: SymexStatusKind) =
  ## The verdict, with nothing recorded at all.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0

template declines(fn: typed, lbl: string, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (4) every signed int heap cell is Int-sorted -----------------------------
#
# S8as made the plain `int` heap Int-sorted only when every `int` parameter
# was an Int; a ranged or narrower cell stayed a bit-vector. A cell of one
# sort holding a value of the other went through `int2bv`/`bv2int` and back,
# which Z3 decides only slowly. Measured (Linux, Z3 5.1), before -> after:
# `mx_dead` 50.6 s -> 0.03 s, `rg_dead` 71.1 s -> 0.03 s, `nw_dead`
# 18.0 s -> 0.02 s; `mw_dead` and the S8an `ab_dead` shape stay under 0.02 s.
# Each cell's sort is its type's; a bit-vector stored and read back meets
# its source unconverted (`intOfBV`, and a read at the address the heap's
# last store wrote is that store's value). The rlimit below is far under
# what the slow forms needed.

type S8axBox = object
  s: range[-5000..5000]

# ---- (7) a read and a later call that writes what it reads ------------------
#
# WRONG VERDICTS before S8ax (each `bad` was sxSat, nothing recorded): the
# parser hoisted each operand's statements where it stood, so an operand
# Nim reads inline was read BEFORE a later operand's call that writes it,
# and a constructor element Nim stores before the call was read after it.
# Nim (c and cpp, probed): a variable, a field, a ref field, a dereference
# or an element is read with its enclosing operation, after the later
# operands' calls; a call, a checked `+ - *` and every constructor element
# are evaluated where they stand. `-x` and `x div y` check where they stand
# and read late; an element read checks its bound where it stands.

proc s8axK(a, b: int): int = a * 100 + b

type S8axRR = ref object
  a: int

var gS8axOrd: int
proc s8axSetOrd(): int =
  gS8axOrd = 10
  0

proc sutOrdField(v: int) =
  var x = (a: v, b: 2)
  proc g(): int =
    x.a = 10
    0
  let r = x.a + g()
  if r == 10 and v == 1: symexTarget("ok")
  if r == 1 and v == 1: symexTarget("bad")

proc sutOrdRefField(v: int) =
  var rr = S8axRR(a: v)
  proc g(): int =
    rr.a = 10
    0
  let r = rr.a + g()
  if r == 10 and v == 1: symexTarget("ok")
  if r == 1 and v == 1: symexTarget("bad")

proc sutOrdGlobal(v: int) =
  gS8axOrd = v
  let r = (gS8axOrd and 15) + s8axSetOrd()
  if r == 10 and v == 1: symexTarget("ok")
  if r == 1 and v == 1: symexTarget("bad")

proc sutOrdArg(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  proc g(): int =
    x = 10
    0
  let r = s8axK(x + 0, g())
  if r == 100 and v == 1: symexTarget("ok")
  if r == 1000 and v == 1: symexTarget("bad")

proc sutOrdNeg(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  proc g(): int =
    x = 10
    0
  let r = -x + g()
  if r == -10 and v == 1: symexTarget("ok")
  if r == -1 and v == 1: symexTarget("bad")

proc sutOrdNegKept(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  var y = 0
  proc g(): int =
    y = x
    0
  let r = -x + g()
  if r == -1 and v == 1: symexTarget("ok")
  if r != -v: symexTarget("bad")

proc sutOrdDiv(v: int) =
  var x = v
  proc g(): int =
    x = 40
    0
  let r = x div 2 + g()
  if r == 20 and v == 4: symexTarget("ok")
  if r == 2 and v == 4: symexTarget("bad")

proc sutOrdIndex(v: int) =
  var s = @[1, v, 3]
  proc g(): int =
    s[1] = 20
    0
  let r = s[1] + g()
  if r == 20 and v == 1: symexTarget("ok")
  if r == 1 and v == 1: symexTarget("bad")

suite "RFC-0005 S8ax (7): evaluation order":
  test "a field, a ref field and a global are read after the call":
    clean(sutOrdField, "ok", sxSat)
    clean(sutOrdField, "bad", sxUnsat)
    clean(sutOrdRefField, "ok", sxSat)
    clean(sutOrdRefField, "bad", sxUnsat)
    clean(sutOrdGlobal, "ok", sxSat)
    clean(sutOrdGlobal, "bad", sxUnsat)
  test "a checked `+` argument is evaluated before a later argument":
    verdict(sutOrdArg, "ok", sxSat)
    verdict(sutOrdArg, "bad", sxUnsat)
  test "a checked read whose value a later call changes declines":
    declines(sutOrdNeg, "ok", feEvalOrderUnmodelled, "reads after a later")
    declines(sutOrdDiv, "ok", feEvalOrderUnmodelled, "reads after a later")
  test "an element is checked where it stands and read after the call":
    ## S8ax declined it; RFC-0005 S8be checks the index before `g()` and
    ## reads the element after it, as Nim does.
    clean(sutOrdIndex, "ok", sxSat)
    clean(sutOrdIndex, "bad", sxUnsat)
  test "a checked read the call leaves alone is exact":
    clean(sutOrdNegKept, "ok", sxSat)
    clean(sutOrdNegKept, "bad", sxUnsat)

type S8axPair = object
  a, b: int
