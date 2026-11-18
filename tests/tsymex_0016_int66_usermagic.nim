## RFC-0016 INT-66: a routine the program declares with `{.magic.}`. A
## `proc plus(x, y: int): int {.magic: "AddI".}` is `system.+` under another
## name; `plus(t, u) == 5` is sat at `a = 2, b = 3`.
##
## Red at fc08fd17 (and 2206eb51): the call declines `feUnsupportedOp` ("the
## compiler magic `N_plus` ({.magic: "AddI".}) has no symbolic model"): the
## walk models a magic where it meets the system routine's name, so the
## magic axis's row `AddI` (exact) is never consulted for another name.
## Found by K8b's pragma axis suite (INT-56), row `routine/magic`. The call
## is now the infix of the system routine of the same magic and signature
## (`userMagicRewrite`).
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

proc i66Plus(x, y: int): int {.magic: "AddI", noSideEffect.}
proc i66Less(x, y: int): bool {.magic: "LtI", noSideEffect.}
proc i66Mul8(x, y: int8): int8 {.magic: "MulI", noSideEffect.}
proc i66Abs(x: int): int {.magic: "AbsI", noSideEffect.}

proc i66UserMagic(a, b: int8) =
  let t = int(a)
  let u = int(b)
  if i66Plus(t, u) == 5 and t == 2: symexTarget("hit")

proc i66Unsat(a, b: int8) =
  let t = int(a)
  if i66Plus(t, 1) == t: symexTarget("hit")

proc i66Compare(a, b: int8) =
  if i66Less(int(a), int(b)) and int(b) - int(a) == 1 and a > 100:
    symexTarget("hit")

proc i66Mul(a, b: int8) =
  let p = i66Mul8(a, b)
  if p == 100: symexTarget("hit")

proc i66Overflow(a, b: int8) =
  # `int8` multiplication raises `OverflowDefect` past 127, as `*` does
  if a > 20 and b > 20:
    discard i66Mul8(a, b)
    symexTarget("hit")

proc i66Unary(a, b: int8) =
  if i66Abs(int(a)) == 5: symexTarget("hit")

suite "INT-66: a routine declared with `{.magic.}` is exact":
  let all = exhaustive(toSeq(low(int8) .. high(int8)))
  test "`plus(t, u) == 5` over `{.magic: \"AddI\".}` is exact (sat)":
    let r = pinExact(i66UserMagic, cellKey(axPragma, "routine/magic"),
                     tLabel("hit"), all)
    check r.status == sxSat
  test "`plus(t, 1) == t` is exact (unsat)":
    let r = pinExact(i66Unsat, cellKey(axPragma, "routine/magic"),
                     tLabel("hit"), all)
    check r.status == sxUnsat
  test "a comparison magic (`LtI`) is exact (sat)":
    let r = pinExact(i66Compare, cellKey(axPragma, "routine/magic"),
                     tLabel("hit"), all)
    check r.status == sxSat
  test "an `int8` `MulI` is exact (sat)":
    let r = pinExact(i66Mul, cellKey(axPragma, "routine/magic"),
                     tLabel("hit"), all)
    check r.status == sxSat
  test "an `int8` `MulI` past its range raises `OverflowDefect`":
    let r = pinExact(i66Overflow, cellKey(axPragma, "routine/magic"),
                     tRaisedExn("OverflowDefect"), all)
    check r.status == sxRaised
  test "a magic the infix arm does not model still declines":
    pinDecline(i66Unary, cellKey(axPragma, "routine/magic"), feUnsupportedOp)

  test "walker 423: the version floor":
    check parseInt(symexWalkerVersion) >= 423
