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
import std/[unittest, options, sets, sequtils, strutils]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/errorkind
import nelli/smt/magic_dispatch
import nelli/smt/stdlib_rows
import nelli/smt/dsl_parser
import nelli/smt/canonicalize
import ./s8cu_helpers

static:
  # The parser expanded `dispatchMagic` once at each dispatched site.
  doAssert dispatchedMagicSites() == magicDispatchSites,
    "a dispatched site was not expanded: " & $dispatchedMagicSites()

template dispatchOk(site: untyped; body: untyped): bool =
  compiles(dispatchMagic(site, body))

suite "K4a-dispatch: the registry and the generated case":
  test "every dispatched site was expanded exactly once":
    const seen = dispatchedMagicSites()
    check seen == magicDispatchSites
    check msArm notin seen
    check msProcRegister notin seen

  test "the walker version is at the dispatch floor":
    check parseInt(symexWalkerVersion) >= 295

  test "a site cannot be dispatched twice":
    # `msNewString` is already expanded by the parser.
    let ok1 = dispatchOk(msNewString):
      case "x"
      of "NewString", "NewStringOfCap": 1
      else: 0
    check not ok1

  test "a case that disagrees with the table does not compile":
    let ok2 = dispatchOk(msVarStmt):
      case "x"
      of "NoSuchMagic": 1
      else: 0
    check not ok2
    let ok3 = dispatchOk(msVarStmt):
      case "x"
      of "Swap": 1
      else: 0                        # the other arms are missing
    check not ok3
    let ok4 = dispatchOk(msVarStmt):
      case "x"
      of "Destroy": 1                 # a refused row
      else: 0
    check not ok4
    let ok5 = dispatchOk(msArm):
      case "x"
      of "Swap": 1
      else: 0                        # not a dispatched site
    check not ok5

  test "the table names each site's arms":
    check toHashSet(toSeq(magicAxis.keysAt(msCallSwitch))) ==
      ["AshrI", "Ord", "Chr", "EnsureMove"].toHashSet
    # K4c: the unsigned operators are `system` routines, rows of stdlibAxis.
    let unsignedKeys = ["system.+%", "system.-%", "system.*%", "system./%",
                        "system.%%", "system.<%", "system.<=%"].toHashSet
    check toHashSet(toSeq(stdlibAxis.keysAt(ssCallSwitch))) == unsignedKeys
    check toHashSet(toSeq(stdlibAxis.keysAt(ssInfix))) == unsignedKeys
    check toHashSet(toSeq(magicAxis.keysAt(msInfix))).len == 0
    check toHashSet(toSeq(magicAxis.keysAt(msNewString))) ==
      ["NewString", "NewStringOfCap"].toHashSet
    check "Swap" in toHashSet(toSeq(magicAxis.keysAt(msVarStmt)))

  test "an arm's row declines at another site, naming its cell":
    let a = admitMagic("AshrI", msVarStmt)
    check not a.admitted
    check a.decline[0] == some(feUnsupportedOp)
    check "magic:AshrI" in a.decline[1]
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

# Arithmetic
sutI2(sAddI, a + b == 7)
sutI2(sSubI, a - b == 7)
sutI2(sMulI, a * b == 12 and a > 1 and b > 1)
sutI2(sDivI, b > 0 and a div b == 3)
sutI2(sModI, b > 0 and a mod b == 2)
sutI1(sNegI, -a == 5)
sutI1(sPlusI, +a == 5)
sutI1(sAbsI, abs(a) == 5 and a < 0)
sutI1(sSucc, succ(a) == 5)
sutI1(sPred, pred(a) == 5)
sutI2(sMinI, min(a, b) == 3 and a > b)
sutI2(sMaxI, max(a, b) == 3 and a < b)
# Bits
sutI1(sNotI, not a == 5)
sutI2(sAndI, (a and b) == 5)
sutI2(sOrI, (a or b) == 5)
sutI2(sXorI, (a xor b) == 5)
sutI1(sShlI, (a shl 2) == 20)
sutI1(sShrI, (a shr 1) == 3)
sutI1(sAshrI, ashr(a, 1) == -3)
# Comparisons
sutI2(sEqI, a == b and a == 7)
sutI2(sLeI, a <= b and b == 3)
sutI2(sLtI, a < b and b == 3)
# The unsigned operators over the signed ints
sutI2(sAddUs, a +% b == 7)
sutI2(sSubUs, a -% b == 7)
sutI2(sMulUs, a *% b == 12)
sutI2(sDivUs, b != 0 and a /% b == 3)
sutI2(sModUs, b != 0 and a %% b == 2)
sutI2(sLtUs, a <% b and b == 3)
sutI2(sLeUs, a <=% b and b == 3)

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
  pinSat(sAddI, "AddI")
  pinSat(sSubI, "SubI")
  pinSat(sMulI, "MulI")
  pinSat(sDivI, "DivI")
  pinSat(sModI, "ModI")
  pinSat(sNegI, "UnaryMinusI")
  pinSat(sPlusI, "UnaryPlusI")
  pinSat(sAbsI, "AbsI")
  pinSat(sSucc, "Succ")
  pinSat(sPred, "Pred")
  pinSat(sMinI, "MinI")
  pinSat(sMaxI, "MaxI")
  pinSat(sNotI, "BitnotI")
  pinSat(sAndI, "BitandI")
  pinSat(sOrI, "BitorI")
  pinSat(sXorI, "BitxorI")
  pinSat(sShlI, "ShlI")
  pinSat(sShrI, "ShrI")
  pinSat(sAshrI, "AshrI")
  pinSat(sEqI, "EqI")
  pinSat(sLeI, "LeI")
  pinSat(sLtI, "LtI")
  pinSatStd(sAddUs, "system.+%")
  pinSatStd(sSubUs, "system.-%")
  pinSatStd(sMulUs, "system.*%")
  pinSatStd(sDivUs, "system./%")
  pinSatStd(sModUs, "system.%%")
  pinSatStd(sLtUs, "system.<%")
  pinSatStd(sLeUs, "system.<=%")
