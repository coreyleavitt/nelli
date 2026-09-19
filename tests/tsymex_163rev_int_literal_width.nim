## Issue #163 item 2 (rev) -- an un-suffixed int literal above `int32.high`
## defaults to `int64` in real Nim; confirmed the engine modeled it at a
## DIFFERENT (narrower) width in one concrete shape, and fixed it.
##
## REPRODUCED (this session, `scratchpad/probe_163item2_symex_width.nim` /
## `scratchpad/probe_163item2_treerepr.nim`, not committed): `a: int32`
## compared directly against the untyped literal `3_000_000_000` COMPILES in
## real Nim -- `treeRepr`/`getTypeInst` confirm the compiler inserts an
## `nnkHiddenStdConv` widening `a` from `int32` to `int64` (the literal
## itself is already typed `int64`, since it does not fit `int32`), so the
## comparison happens entirely at 64 bits. `a > 3_000_000_000` is therefore
## UNSATISFIABLE for every possible `int32` value (`int32.high` is
## 2_147_483_647, far below three billion).
##
## Before this fix, `dsl_parser.parseExpr`'s `nnkHiddenStdConv` arm was a
## BLIND pass-through (`parseExpr(n[n.len-1], ...)`), justified only for the
## representation-preserving subrange-strip case (`range[T]` -> its base
## type). Applied to a genuine WIDTH-changing hidden conversion, it parsed
## `a` at its narrow (32-bit) width with no record of the widening; the
## comparison's literal then got folded into a same-sized BV downstream and
## silently WRAPPED (`3_000_000_000` truncated into 32 bits reads back as
## the negative `-1_294_967_296`), so `symexFind` reported `sxSat` with
## witness `a = -1294967295` for a target genuinely unreachable in real Nim
## -- a soundness bug (a false SAT), not merely an imprecision.
##
## THE FIX: the same `nnkHiddenStdConv`/`nnkHiddenSubConv` arm now detects a
## genuine width change between the hidden conversion's own resolved type
## and its wrapped operand's type (`classifyType(n).ty.width !=
## classifyType(wrapped).ty.width`) and routes it through the same
## `mkConvIntWidth` widening machinery the explicit `nnkConv` case already
## used. A same-width hidden conversion (the subrange-strip case, and
## `nnkHiddenAddr`) is untouched.
##
## House rule: every symbolic expectation is paired with an oracle computed
## by real Nim execution in this same file.

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

proc reachOversizedLiteral(a: int32) =
  if a > 3_000_000_000:
    symexTarget("hit")

proc reachOversizedLiteralLe(a: int32) =
  ## The mirror comparison direction -- `a >= 3_000_000_001` reduces to the
  ## same width question from the other side, catching a fix that only
  ## patches one specific infix spelling.
  if a >= 3_000_000_001:
    symexTarget("hit")

suite "#163 item 2 -- an oversized untyped literal compared against a narrower int":

  test "oracle -- no int32 value satisfies a > 3_000_000_000":
    check int32.high.int64 < 3_000_000_000'i64
    for a in [int32.low, -1'i32, 0'i32, 1'i32, int32.high]:
      check not (a > 3_000_000_000)
      check not (a >= 3_000_000_001)

  test "the comparison genuinely compiles as a real Nim widening (not a type error)":
    # If this ever stopped compiling, the whole scenario would be moot --
    # pin that the widening conversion this fix relies on is real.
    var a: int32 = 5
    let ok = a > 3_000_000_000
    check ok == false

  test "RED (pre-fix): symex must agree the target is UNSAT, not falsely SAT":
    let r = symexFind(reachOversizedLiteral, tLabel("hit"))
    check r.status == sxUnsat

  test "the mirror comparison direction agrees too":
    let r = symexFind(reachOversizedLiteralLe, tLabel("hit"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Non-regression: a literal that genuinely IS reachable at the operand's
# real (widened) width must still be found -- the fix must not overcorrect
# into banning every oversized literal outright.
# ---------------------------------------------------------------------------

proc reachViaWideParam(a: int) =
  ## `a` is a plain 64-bit `int` -- no hidden conversion at all here (both
  ## operands are already int64) -- must be unaffected by this fix.
  if a > 3_000_000_000:
    symexTarget("hit")

suite "#163 item 2 non-regression -- a same-width (no hidden conv) oversized literal comparison":

  test "oracle -- a plain 64-bit int can genuinely exceed 3 billion":
    check 4_000_000_000 > 3_000_000_000

  test "symex still finds it reachable":
    let r = symexFind(reachViaWideParam, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] > 3_000_000_000


suite "#163 item 2 -- walker version pin":

  test "walker version floor >= 138 (the round this fix lands in)":
    check parseInt(symexWalkerVersion) >= 139
