## RFC-0016 0.10.0 review, finding H5. A routine `{.noinit.}` leaves its
## `result` uninitialised: Nim does not zero it, so a read before a write
## sees whatever the stack held (natively `f(false)` returned 4663 after a
## stack-dirtying call). The routine row admitted `noinit` as "read", but
## nothing read it, so the walker zeroed `result` (`unwrittenResultZero`)
## and proved `f(false) != 0` UNSAT, trusted. `result` now starts as a
## `{.noinit.}` local does (`noinitValue`): a read of a part no write
## reached carries `ubIndeterminateRead`.
##
## The routine row's other "read" members are audited in the same slice:
## `nodestroy`, `codegenDecl`, `constructor`, `asmNoStackFrame`, `emit`,
## `varargs` and `importCompilerProc` had no reader and now decline.
## The native value of an indeterminate read is not reproducible, so the
## checks here are on the verdict's soundness, not on a native comparison.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/pragmaaxes
import ./s8cu_helpers

proc fNoinit(c: bool): int {.noinit.} =
  if c: result = 1

proc sutNoinitNonzero(c: bool) =
  let v = fNoinit(c)
  if not c and v != 0: symexTarget("nz")

proc sutNoinitZero(c: bool) =
  let v = fNoinit(c)
  if not c and v == 0: symexTarget("z")

proc sutNoinitWritten(c: bool) =
  ## Every path that reads `v` wrote `result` first: exact.
  let v = fNoinit(c)
  if c and v != 1: symexTarget("bad")

proc fNoinitSelfRead(c: bool): int {.noinit.} =
  ## Reads its own `result` before any write when `c` is false.
  if c: result = 2
  result = result + 1

proc sutNoinitSelfRead(c: bool) =
  if fNoinitSelfRead(c) == 1: symexTarget("one")

proc fNoinitAsgn(x: int): int {.noinit.} =
  ## The single-assignment shape (`result = expr`) still reads `result`.
  result = result + x

proc sutNoinitAsgn(x: int) =
  if fNoinitAsgn(x) == x: symexTarget("same")

proc sutTargetNoinit(c: bool): int {.noinit.} =
  ## The target routine itself carries `{.noinit.}`.
  if c: result = 1
  if result == 0: symexTarget("z")

proc fNoinitStr(c: bool): string {.noinit.} =
  if c: result = "a"

proc sutNoinitStr(c: bool) =
  if fNoinitStr(c).len == 0: symexTarget("empty")

proc fNoDestroy(x: int): int {.nodestroy.} = x + 1
proc sutNoDestroy(x: int) =
  if fNoDestroy(x) == 5: symexTarget("hit")

proc fCodegen(x: int): int {.codegenDecl: "$# $#$#".} = x + 1
proc sutCodegen(x: int) =
  if fCodegen(x) == 5: symexTarget("hit")

proc fPlain(c: bool): int =
  if c: result = 1

proc sutPlainZero(c: bool) =
  ## No pragma: `result` is zeroed, the proof stays exact and trusted.
  let v = fPlain(c)
  if not c and v != 0: symexTarget("nz")

suite "CR-4 H5: a routine {.noinit.} leaves result unwritten":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 357

  test "v != 0 after no write is no trusted UNSAT":
    let r = symexFind(sutNoinitNonzero, tLabel("nz"))
    checkpoint show(r.errors) & " " & $r.soundness
    check not (r.status == sxUnsat and r.trusted)

  test "v == 0 after no write is no trusted SAT":
    let r = symexFind(sutNoinitZero, tLabel("z"))
    checkpoint show(r.errors) & " " & $r.soundness
    check not (r.status == sxSat and r.trusted)

  test "tUndefined finds the indeterminate read of result":
    let r = symexFind(sutNoinitNonzero, tUndefined())
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds
    check r.witness[0] == false
    check not r.trusted

  test "a written result is exact: trusted UNSAT":
    let r = symexFind(sutNoinitWritten, tLabel("bad"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check r.trusted

  test "the routine's own read of result is indeterminate":
    let r = symexFind(sutNoinitSelfRead, tUndefined())
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds
    let r2 = symexFind(sutNoinitSelfRead, tLabel("one"))
    check not (r2.status == sxSat and r2.trusted)

  test "result = result + x reads an indeterminate result":
    let r = symexFind(sutNoinitAsgn, tLabel("same"))
    checkpoint show(r.errors) & " " & $r.soundness
    check not (r.status == sxSat and r.trusted)
    let r2 = symexFind(sutNoinitAsgn, tUndefined())
    check r2.status == sxSat
    check UbKind(ubIndeterminateRead) in r2.soundness.undefinedKinds

  test "the target routine's own {.noinit.} result":
    let r = symexFind(sutTargetNoinit, tUndefined())
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds
    let r2 = symexFind(sutTargetNoinit, tLabel("z"))
    check not (r2.status == sxSat and r2.trusted)

  test "a managed result under {.noinit.} declines":
    let r = symexFind(sutNoinitStr, tLabel("empty"))
    checkpoint show(r.errors)
    check not r.trusted

  test "without the pragma result is zeroed: trusted UNSAT":
    let r = symexFind(sutPlainZero, tLabel("nz"))
    check r.status == sxUnsat
    check r.trusted

  test "routine {.nodestroy.} declines":
    pinDecline(sutNoDestroy, cellKey(axPragma, "routine/nodestroy"),
               feUnsupportedOp, needle = "nodestroy")

  test "routine {.codegenDecl.} declines":
    pinDecline(sutCodegen, cellKey(axPragma, "routine/codegenDecl"),
               feUnsupportedOp, needle = "codegenDecl")

  test "the routine row: every read member has a reader":
    for n in ["nodestroy", "codegenDecl", "constructor", "asmNoStackFrame",
              "emit", "varargs", "importCompilerProc"]:
      checkpoint n
      check not admitPragma(ppRoutine, n, psRoutineDecl).admitted
    check admitPragma(ppRoutine, "noinit", psRoutineDecl).admitted
