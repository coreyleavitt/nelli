## RFC-0016 K4b (section 8.4, K4): an unadmitted bodied magic declines.
##
## A `{.magic.}` routine with a real Nim body is walked through that body
## only when its row says so (`mmBody`, admitted at `msBodyWalk`). Any other
## row (modelled, partial, folded by an arm elsewhere; declined; unverified;
## never) declines with the row's named kind, and a magic with no row
## declines `feUnadmitted`: the body is documentation or a VM fallback, never
## what the call does. This file pins
##   * the table: `msBodyWalk` admits exactly the `mmBody` rows;
##   * the behaviour through `symexFind`, both outcomes;
##   * a pin for each `magic:` cell the SUT reaches that K4a-dispatch did not.
import std/[unittest, strutils, options]
import nelli/symex
import nelli/smt/admission
import nelli/smt/errorkind
import nelli/smt/magic_rows
import nelli/smt/canonicalize
import ./s8cu_helpers

suite "K4b: the table":
  test "the walker version is at the K4b floor":
    check parseInt(symexWalkerVersion) >= 292

  test "msBodyWalk admits exactly the mmBody rows":
    for k in magicAxis.keysAt(msBodyWalk):
      check admitMagic(k, msBodyWalk).payload == mmBody
    for k in ["AbsI", "MinI", "MaxI", "EqCString"]:
      check admitMagic(k, msBodyWalk).admitted
    check not admitMagic("Succ", msBodyWalk).admitted
    check not admitMagic("XorSet", msBodyWalk).admitted
    check admitMagic("NoSuchMagic", msBodyWalk).decline[0] ==
      some(feUnadmitted)

# --- user routines carrying a magic pragma and a real body ------------------

proc myAbs(x: int): int {.magic: "AbsI".} =
  if x < 0: -x else: x
proc mySucc(x: int, n: int): int {.magic: "Succ".} =
  x + n + 1000
proc myXorSet(x, y: set[char]): set[char] {.magic: "XorSet".} =
  x + y

proc sBodyAdmitted(a: int) =
  if myAbs(a) == 5 and a < 0: symexTarget("hit")
proc sBodyModelledRow(a: int) =
  if mySucc(a, 1) == 1005: symexTarget("hit")
proc sBodyDeclinedRow(c: char) =
  if myXorSet({c}, {'a'}) == {'a'}: symexTarget("hit")

suite "K4b: bodied magics through symexFind":
  test "an admitted bodied magic is walked through its body":
    let r = pinExact(sBodyAdmitted, cellKey(axMagic, "AbsI"),
                     domain = sampled([-5, -1, 0, 5, 7]))
    check r.status == sxSat
  test "a bodied magic whose row is an arm elsewhere declines":
    pinDecline(sBodyModelledRow, cellKey(axMagic, "Succ"), feUnsupportedOp,
               needle = "magic:Succ")
  test "a bodied magic whose row is refused declines":
    pinDecline(sBodyDeclinedRow, cellKey(axMagic, "XorSet"), feUnsupportedOp,
               needle = "magic:XorSet")
