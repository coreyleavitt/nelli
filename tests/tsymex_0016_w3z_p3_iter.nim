## RFC-0016 W3-z P3 (A4): the stdlib-body axis on the two paths that walk a
## stdlib body without `parseCalleeImpl`: the iterator inliner and a stdlib proc
## taken as a value (`parseProcAsValue`). Absent is a decline (`feUnadmitted`),
## naming the cell; a routine with a row is walked exactly as before.
import std/[unittest, math, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/stdlib_rows
import ./s8cu_helpers

# An iterator of `strutils` with no row. (P3b: `system.countdown` has a
# declined row now.)
proc sNoRowIter(a: int) =
  var n = 0
  for w in "a,b".split(','): inc n
  if n == 2 and a == 1: symexTarget("hit")

proc apply(f: proc (c: char): bool; c: char): bool = f(c)
proc apply2(f: proc (c: int): bool; c: int): bool = f(c)

proc sSplit(a: int) =
  var n = 0
  for l in "x\ny".splitLines: inc n
  if n == 2 and a == 1: symexTarget("hit")

# A stdlib proc with no row, taken as a value.
proc sNoRowValue(a: int) =
  if apply(isAlphaAscii, 'a') and a == 1: symexTarget("hit")

# A stdlib proc with a row, taken as a value.
proc sRowValue(a: int) =
  if apply2(isPowerOfTwo, a) and a == 8: symexTarget("hit")

template declinesUnadmitted(fn: untyped; cell: string) =
  ## A routine with no row is absent, so not a cell to pin (a record needs a
  ## row): the verdict is untrusted, `feUnadmitted` names the cell.
  block:
    let r = symexFind(fn, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check not r.trusted
    var found = false
    for e in r.errors:
      if e.kind == feUnadmitted and cell in e.msg: found = true
    check found

suite "W3-z P3: the walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 314

suite "W3-z P3: the stdlib-body axis reaches the iterator inliner":
  test "the key of an iterator names its kind":
    check not hasStdlibRow("strutils.split/iterator")
  test "a ledger iterator (the corpus walks it) is admitted":
    check admitStdlibBody("strutils.splitLines/iterator", ssBodyWalk).admitted
    # The K7 SUT walks it to a cap: no `feUnadmitted` on the way.
    let r = symexFind(sSplit, tLabel("hit"), pinSettingsConst)
    for e in r.errors: check e.kind != feUnadmitted
  test "an iterator with no row declines, naming its cell":
    declinesUnadmitted(sNoRowIter, "strutils.split/iterator")

suite "W3-z P3: the stdlib-body axis reaches a stdlib proc taken as a value":
  test "a proc with no row declines":
    declinesUnadmitted(sNoRowValue, "strutils.isAlphaAscii")
  test "a proc with a row is walked exactly":
    let r = pinExact(sRowValue, cellKey(axStdlibBody, "math.isPowerOfTwo"),
                     domain = sampled([0, 1, 4, 7, 8, 9]))
    check r.status == sxSat
