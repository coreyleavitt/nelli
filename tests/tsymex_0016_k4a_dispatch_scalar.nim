## RFC-0016 K4a-dispatch (section 8.1): the magic axis is consumed per site.
##
## `dispatchMagic` (smt/magic_dispatch) checks a site's `case` against the table
## at compile time. This file pins
##   * the once-per-site registry: every dispatched site was expanded in this
##     compilation (the parser is imported, so its expansions have run), none
##     twice, and a `case` that disagrees with the table does not compile;
##   * the sites' rows: what each site's arms are, read from the table;
##   * a pin per row family through `symexFind`: a SUT that reaches the magic,
##     the walker's verdict reproduced natively, one record per `magic:` cell.
## The cells no SUT can reach (compile-time-only, folded, macro and DrNim
## magics) stay allowlisted with their reason.
##
## Split (RFC-0016 INT-51) into three files so each compiles inside the CI
## ceiling: `tsymex_0016_k4a_dispatch_signed` (the registry, and the signed
## integer magics), `tsymex_0016_k4a_dispatch_scalar` (unsigned, float, bool
## and char) and `tsymex_0016_k4a_dispatch_stmt` (the statement-position
## magics, strings, sequences, arrays and sets). Every pin of the one file is
## in exactly one of them.
import std/unittest
import nelli
import nelli/symex
import ./s8cu_helpers

# --- SUTs ------------------------------------------------------------------

template sutI2(name, cond: untyped) {.dirty.} =
  proc name(a, b: int) =
    if cond: symexTarget("hit")
template sutI1(name, cond: untyped) {.dirty.} =
  proc name(a: int) =
    if cond: symexTarget("hit")
template sutU2(name, cond: untyped) {.dirty.} =
  proc name(a, b: uint) =
    if cond: symexTarget("hit")
template sutF2(name, cond: untyped) {.dirty.} =
  proc name(a, b: float) =
    if cond: symexTarget("hit")
template sutF1(name, cond: untyped) {.dirty.} =
  proc name(a: float) =
    if cond: symexTarget("hit")
template sutC1(name, cond: untyped) {.dirty.} =
  proc name(a, b: char) =
    if cond: symexTarget("hit")

# Unsigned
sutU2(sAddU, a + b == 7)
sutU2(sSubU, a - b == 7)
sutU2(sMulU, a * b == 12)
sutU2(sDivU, b != 0 and a div b == 3)
sutU2(sModU, b != 0 and a mod b == 2)
sutU2(sLeU, a <= b and b == 3)
sutU2(sLtU, a < b and b == 3)
# Float
sutF2(sAddF, a + b == 7.5)
sutF2(sSubF, a - b == 7.5)
sutF2(sMulF, a * b == 6.0 and a == 2.0)
# b is pinned like sMulF pins a: the division circuit over two free operands is
# a query some Z3 builds answer unknown (CI Z3 5.1.0.0 did); b == 2.5 leaves
# a / 2.5 == 2.0, witness a == 5.0, inside fDom.
sutF2(sDivF, b == 2.5 and a / b == 2.0)
sutF1(sNegF, -a == 2.5)
sutF1(sPlusF, +a == 2.5)
sutF2(sEqF, a == b and a == 2.5)
sutF2(sLeF, a <= b and b == 3.0)
sutF2(sLtF, a < b and b == 3.0)
# Bool and char
sutI2(sEqB, (a > 0) == (b > 0) and a == 3 and b == 4)
sutI2(sLeB, (a > 0) <= (b > 0) and a < 0)
sutI2(sLtB, (a > 0) < (b > 0) and b > 0)
sutI2(sNotB, not (a > 0) and b == 2)
sutI2(sAnd, a > 0 and b > 0 and a + b == 7)
sutI2(sOr, a > 0 or b > 0 and a + b == 7)
sutI2(sXorB, (a > 0) xor (b > 0) and a == 3)
sutC1(sEqCh, a == b and a == 'x')
sutC1(sLeCh, a <= b and b == 'x')
sutC1(sLtCh, a < b and b == 'x')
sutI1(sOrd, ord(a > 3) == 1 and a == 9)
sutI1(sChr, a >= 0 and a <= 255 and chr(a) == 'x')

const
  uDom = sampled([0'u, 1, 3, 4, 5, 7, 10, 12, high(uint)])
  fDom = sampled([0.0, 1.0, 2.0, 2.5, 3.0, 5.0, 7.5, -2.5, 1.5, 6.0])
  sDom = sampled(["", "a", "ab", "abc", "x"])
  qDom = sampled(@[@[], @[1], @[1, 2], @[1, 2, 3]])
  chDom = sampled(['a', 'b', 'x', 'y'])
  cDom = sampled(['a', 'x', 'z'])
  smallInts = sampled([-3, -1, 0, 1, 2, 3, 4, 5, 7, 9, 12, 20, 255])

template pinSat(sut: untyped; cell: static string; dom: untyped = smallInts) =
  test cell:
    let r = pinExact(sut, cellKey(axMagic, cell), domain = dom)
    check r.status == sxSat

template pinSatStd(sut: untyped; cell: static string) =
  test cell:
    let r = pinExact(sut, cellKey(axStdlibBody, cell), domain = smallInts)
    check r.status == sxSat

suite "K4a-dispatch: pins through symexFind, one record per cell":
  pinSat(sAddU, "AddU", uDom)
  pinSat(sSubU, "SubU", uDom)
  pinSat(sMulU, "MulU", uDom)
  pinSat(sDivU, "DivU", uDom)
  pinSat(sModU, "ModU", uDom)
  pinSat(sLeU, "LeU", uDom)
  pinSat(sLtU, "LtU", uDom)
  pinSat(sAddF, "AddF64", fDom)
  pinSat(sSubF, "SubF64", fDom)
  pinSat(sMulF, "MulF64", fDom)
  pinSat(sDivF, "DivF64", fDom)
  pinSat(sNegF, "UnaryMinusF64", fDom)
  pinSat(sPlusF, "UnaryPlusF64", fDom)
  pinSat(sEqF, "EqF64", fDom)
  pinSat(sLeF, "LeF64", fDom)
  pinSat(sLtF, "LtF64", fDom)
  pinSat(sEqB, "EqB")
  pinSat(sLeB, "LeB")
  pinSat(sLtB, "LtB")
  pinSat(sNotB, "Not")
  pinSat(sAnd, "And")
  pinSat(sOr, "Or")
  pinSat(sXorB, "Xor")
  pinSat(sEqCh, "EqCh", cDom)
  pinSat(sLeCh, "LeCh", cDom)
  pinSat(sLtCh, "LtCh", cDom)
  pinSat(sOrd, "Ord")
  pinSat(sChr, "Chr")
