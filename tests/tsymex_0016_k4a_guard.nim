## RFC-0016 K4a-guard (section 8.1): the opaque-call defect scan reads the
## magic axis.
##
## `scanOpaqueDefects` (smt/dsl_parser) used to keep four name lists
## (`overflowMagics`, `divMagics`, `rangeMagics`, `floatArithMagics`). Which
## Defect a magic raises is now a property of its row: the defect sites
## `msDefOverflow`, `msDefDivZero`, `msDefRange`, `msDefFloat`, read with
## `admitMagic`. This file pins
##   * the table: each site's rows are exactly the magics the lists held that
##     Nim 2.2.10 has (`AddI64` and its siblings are not `TMagic` members, so
##     they never had a row), and every defect row is admitted;
##   * the guard: the library-wide row guard (`tsymex_0016_k4a_table`) means a
##     magic the scan can meet has a row; here, a row that carries a defect
##     property must be an admitted one, and the unsigned zero divisor is
##     none;
##   * the behaviour through `symexFind`: a defect forked from each family.
import std/[unittest, strutils, algorithm]
import nelli/symex
import nelli/smt/admission
import nelli/smt/magic_rows
import nelli/smt/canonicalize
import s8cu_helpers

proc at(site: MagicSite): seq[string] =
  for k in magicAxis.keysAt(site): result.add k
  result.sort

suite "K4a-guard: the defect properties of the magic axis":
  test "the walker version is at the dispatch floor":
    check parseInt(symexWalkerVersion) >= 295

  test "each defect site is exactly the old list, less names Nim lacks":
    check at(msDefOverflow) == @["AbsI", "AddI", "Dec", "Inc", "DivI", "ModI",
      "MulI", "Pred", "SubI", "Succ", "UnaryMinusI", "UnaryMinusI64"].sorted
    check at(msDefDivZero) == @["DivI", "ModI"]
    check at(msDefRange) == @["Chr", "Dec", "Inc", "Pred", "Succ"]
    check at(msDefFloat) == @["AddF64", "DivF64", "MulF64", "SubF64"]

  test "the 64-suffixed names were never magics":
    for m in ["AddI64", "SubI64", "MulI64", "DivI64", "ModI64"]:
      checkpoint m
      check not magicAxis.hasRow(m)

  test "a refused or absent magic carries no defect":
    for site in magicDefectSites:
      for m in ["Spawn", "XorSet", "NoSuchMagic", "nextafter"]:
        checkpoint m & " " & $site
        check not admitMagic(m, site).admitted

  test "an unsigned zero divisor is no DivByZeroDefect":
    for m in ["DivU", "ModU", "DivU64", "ModU64"]:
      checkpoint m
      check not admitMagic(m, msDefDivZero).admitted

  test "every defect row is admitted at msArm, and no case dispatches on it":
    for site in magicDefectSites:
      check site notin magicDispatchSites
      for k in magicAxis.keysAt(site):
        checkpoint k
        check admitMagic(k, msArm).admitted

# One opaque routine per family; the real compiler raises each (probed).
type Day = enum dMon, dTue, dWed

proc gDiv(a, b: int) {.symexOpaque.} =
  discard a div b

proc gMod(a, b: int) {.symexOpaque.} =
  discard a mod b

proc gAdd(a: int) {.symexOpaque.} =
  discard a + 1

proc gChr(a: int) {.symexOpaque.} =
  discard chr(a)

proc gSucc(d: Day) {.symexOpaque.} =
  discard succ(d)

proc sutDiv(b: int) =
  symexAssume(b == 0)
  gDiv(5, b)

proc sutMod(b: int) =
  symexAssume(b == 0)
  gMod(5, b)

proc sutAdd(v: int) =
  symexAssume(v == high(int))
  gAdd(v)

proc sutChr(v: int) =
  symexAssume(v == 300)
  gChr(v)

proc sutSucc(v: int) =
  symexAssume(v == 2)
  gSucc(Day(v))

suite "K4a-guard: the scan forks each defect, through symexFind":
  test "div and mod by zero raise DivByZeroDefect":
    let r1 = symexFind(sutDiv, tRaisedExn("DivByZeroDefect"))
    checkpoint $r1.status
    check r1.status == sxRaised
    let r2 = symexFind(sutMod, tRaisedExn("DivByZeroDefect"))
    checkpoint $r2.status
    check r2.status == sxRaised

  test "an overflowing add raises OverflowDefect":
    let r = symexFind(sutAdd, tRaisedExn("OverflowDefect"))
    checkpoint $r.status
    check r.status == sxRaised

  test "chr past 255 raises RangeDefect":
    let r = symexFind(sutChr, tRaisedExn("RangeDefect"))
    checkpoint $r.status
    check r.status == sxRaised

  test "succ past the last enum value raises RangeDefect":
    let r = symexFind(sutSucc, tRaisedExn("RangeDefect"))
    checkpoint $r.status
    check r.status == sxRaised
