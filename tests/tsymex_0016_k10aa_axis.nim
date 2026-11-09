## RFC-0016 K10a-axis (sections 8.1 and 9.1 item 1) -- the definedness axis.
##
## `smt/definedness.nim` is the table; the walker's undefined-behaviour
## decision sites read it. This file pins, through `symexFind`:
## * STY-03 (`<` over `ptr`), STY-07 (`addr s[i]` then a resize) and `noalias`
##   as `never` / declined cells of the axis;
## * the `{.noinit.}` read, the one `ub*` kind that rides a witness instead of
##   halting, so its error-kind row is evidenced (`pinUndefined`);
## * that the arithmetic sites read the table (a profile x row sweep) and that
##   a `noalias` parameter beside no peer is still a trusted verdict.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/definedness
import nelli/smt/errorkind
import nelli/smt/replayproc
import ./s8cu_helpers

proc scrub() {.noinline.} =
  var a {.volatile.}: array[8192, int]
  for i in 0 ..< a.len: a[i] = 0

# STY-03: pointer order.
proc sutPtrLt(k: int) =
  var a, b: int
  let p = addr a
  let q = addr b
  if p < q or q < p: symexTarget("hit")

# STY-07: `addr s[0]` then growth (B 1.2).
proc sutGrow(k: int) =
  var s = @[0, 0]
  let p = addr s[0]
  s.add k
  p[] = 5
  if s[0] == 5 and k == 3: symexTarget("hit")

# `noalias` beside another pointer-like parameter.
proc sutNoalias(a {.noalias.}: ptr int; b {.noalias.}: ptr int) =
  a[] = 1
  b[] = 2
  if a[] == 1: symexTarget("hit")

proc sutNoaliasVar(a {.noalias.}: var int; b: var int) =
  a = 1
  b = 2
  if a == 1: symexTarget("hit")

# `noalias` with no peer: nothing for it to alias.
proc sutNoaliasOne(a {.noalias.}: ptr int; k: int) =
  a[] = k
  if a[] == 1: symexTarget("hit")

# Without the pragma the same shape is not declined.
proc sutPlainPtrs(a: ptr int; b: ptr int) =
  a[] = 1
  b[] = 2
  if a[] == 1: symexTarget("hit")

proc sutNoinit(k: int) =
  var x {.noinit.}: int
  if k > 0 and x == x: symexTarget("hit")

suite "K10a-axis: the definedness axis":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 294

  test "the table: profile x row answers the build's arithmetic":
    check definedness(aoAdd, ocSignedWide, dpChecked).kind == dkDefect
    check definedness(aoAdd, ocSignedWide, dpUnchecked) ==
      Definedness(kind: dkUndefined, ub: ubSignedOverflow)
    check definedness(aoMul, ocSignedWide, dpFwrapv).kind == dkDefined
    check definedness(aoSub, ocSignedNarrow, dpUnchecked).kind == dkDefined
    check definedness(aoMod, ocLowByMinusOneWide, dpChecked) ==
      Definedness(kind: dkUndefined, ub: ubIntMinModMinusOne)
    check definedness(aoDiv, ocLowByMinusOneWide, dpFwrapv).ub ==
      ubSignedOverflow
    check definedness(aoDiv, ocZeroDivisorSigned, dpChecked).kind == dkDefect
    check definedness(aoDiv, ocZeroDivisorSigned, dpUnchecked).ub ==
      ubSignedDivZero
    check definedness(aoMod, ocZeroDivisorUnsigned, dpChecked).ub ==
      ubUnsignedDivZero

  test "every refused row names the decline kind the site reports":
    for (op, c, s) in [(aoOrder, ocPointer, dsOrder),
                       (aoGrow, ocElemAddr, dsGrow),
                       (aoCall, ocNoalias, dsRoutine)]:
      let a = admitDefined(op, c, s)
      check not a.admitted
      check a.decline[0] == some(feUnsupportedOp)
      check "defined:" & defKey(op, c) in a.decline[1]

  test "STY-03: < over ptr is a named decline (a never cell)":
    pinDecline(sutPtrLt, cellKey(axDefinedness, "order/pointer"),
               feUnsupportedOp, needle = "defined:order/pointer")

  test "STY-07: addr s[0] then growth is a named decline (a never cell)":
    pinDecline(sutGrow, cellKey(axDefinedness, "grow/elemAddr"),
               feUnsupportedOp, needle = "defined:grow/elemAddr",
               excluding = {weInternalWalkerFault})

  test "noalias beside another pointer-like parameter is declined":
    pinDecline(sutNoalias, cellKey(axDefinedness, "call/noalias"),
               feUnsupportedOp, needle = "defined:call/noalias")
    pinDecline(sutNoaliasVar, cellKey(axDefinedness, "call/noalias"),
               feUnsupportedOp, needle = "noalias")

  test "noalias with no pointer-like peer, or no pragma, is not declined":
    template notDeclined(r: untyped) =
      checkpoint show(r.errors)
      check r.status == sxSat
      check r.trusted
      check not r.errors.named(feUnsupportedOp)
    notDeclined(symexFind(sutNoaliasOne, tLabel("hit")))
    notDeclined(symexFind(sutPlainPtrs, tLabel("hit")))

  when defined(cpp) or replayReexecs:
    test "skipped: the replay stack is not the scrubbed one":
      skip()
  else:
    test "the {.noinit.} read rides the witness (ubIndeterminateRead)":
      scrub()
      pinUndefined(sutNoinit, cellKey(axDefinedness, "read/uninitialised"),
                   UbKind(ubIndeterminateRead))
