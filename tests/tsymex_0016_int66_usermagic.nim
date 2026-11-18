## RFC-0016 INT-66: a routine the program declares with `{.magic.}`. A
## `proc plus(x, y: int): int {.magic: "AddI".}` is `system.+` under another
## name; `plus(t, u) == 5` is sat at `a = 2, b = 3`.
##
## Red at fc08fd17: the call declines `feUnsupportedOp` ("the compiler magic
## `N_plus` ({.magic: "AddI".}) has no symbolic model"): the walk models a
## magic where it meets the system routine's name, so the magic axis's row
## `AddI` (exact) is never consulted for another name. Found by K8b's pragma
## axis suite (INT-56), row `routine/magic`.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc i66Plus(x, y: int): int {.magic: "AddI", noSideEffect.}

proc i66UserMagic(a, b: int8) =
  let t = int(a)
  let u = int(b)
  if i66Plus(t, u) == 5 and t == 2: symexTarget("hit")

suite "INT-66: a routine declared with `{.magic.}` is exact":
  test "`plus(t, u) == 5` over `{.magic: \"AddI\".}` is exact (sat)":
    let r = symexFind(i66UserMagic, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
