## RFC-0016 INT-86 (soundness): a discarded read through a nil reference is a
## `sxRaised(NilAccessDefect)` claim, but natively it does not fault. Nim
## lowers `discard p.n` to `(void)((*p).n);`, which the C compiler does not
## load, so the call returns and a label after it is reached. The walker
## modelled the read as a dereference: the crash was claimed, the label behind
## it refuted. Found converting `tsymex_0016_wa_runtime` (K9d-12): its
## `lossyNil`'s claim, run in a child on its only nil input, exited 0.
##
## Native truth (pinned toolchain, gcc and g++, c and cpp; the default build,
## `-d:release`, `-d:danger`, `--opt:none`, `--mm:refc`, `--panics:on`;
## `--nilChecks` is a deprecated no-op in 2.2.10). Nim never elides a read
## itself: it emits every discarded expression as `(void)(E);`. What happens
## then is three classes:
##   * elided: `E` has no check and no call, so the C compiler drops the
##     statement at every optimisation level (`-O0` included). No load, no
##     fault: a path through `.`, `[]`, a literal array index, a comparison,
##     a conversion with no range check, and arithmetic only where the routine
##     is compiled without the check (`discard p.n + 1` under `-d:danger`).
##   * kept: a check reads the loaded value (`discard p.n + 1` with overflow
##     checks, `p.s[0]`'s index check, a variant field's field check) or a
##     call takes it (`discard side(p.n)`), or the value is used
##     (`result = p.n`). Faults under every build.
##   * optimiser-dependent: the value lands in a dead C variable (`let _ =
##     p.n`, an unused `let x = p.n`, `discard (p.n, 1)`, `discard p.s.len`).
##     It faults at `-O0` and does not at `-O2` (`-d:release`). The C
##     compiler's level is not a fact the walker has (`OptLevel` is
##     `optUnknown`), so it claims neither side: the nil path declines.
## A `var ref` parameter is read as `p[]` then `.n`: elided the same way. A
## `var` result through nil (`discard varN(p)`) is INT-89, not this row.
## Each verdict below agrees with that.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type
  B = object
    n: int
    q: ref B
  A = object
    arr: array[3, int]
  C = object
    s: seq[int]

var sideSink: int

proc side(x: int): int =
  sideSink = x
  x

# -- elided: the C compiler drops `(void)(E)` -------------------------------

proc discardField(p: ref B) =
  if p == nil:
    discard p.n
    symexTarget("after")

proc discardPtr(p: ptr int) =
  if p == nil:
    discard p[]
    symexTarget("after")

proc discardDeref(p: ref B) =
  if p == nil:
    discard p[]
    symexTarget("after")

proc discardPtrField(p: ptr B) =
  if p == nil:
    discard p.n
    symexTarget("after")

proc discardChain(p: ref B) =
  if p == nil or p.q == nil:
    discard p.q.n
    symexTarget("after")

proc discardCmp(p: ref B) =
  if p == nil:
    discard p.n == 0
    symexTarget("after")

proc discardConv(p: ref B) =
  if p == nil:
    discard p.n.float
    symexTarget("after")

proc discardArr(p: ref A) =
  if p == nil:
    discard p.arr[1]
    symexTarget("after")

proc discardVarParam(p: var ref B) =
  if p == nil:
    discard p.n
    symexTarget("after")

# -- kept: the read is loaded under every build ------------------------------

proc keptField(p: ref B): int =
  if p == nil:
    result = p.n
    symexTarget("after")

proc discardChecked(p: ref B) =
  if p == nil:
    discard p.n + 1
    symexTarget("after")

proc discardCall(p: ref B) =
  if p == nil:
    discard side(p.n)
    symexTarget("after")

proc discardSeqIdx(p: ref C) =
  if p == nil:
    discard p.s[0]
    symexTarget("after")

# -- optimiser-dependent: a dead C variable holds the value ------------------

proc letUnder(p: ref B) =
  if p == nil:
    let _ = p.n
    symexTarget("after")

proc letUnused(p: ref B) =
  if p == nil:
    let x = p.n
    symexTarget("after")

proc discardTuple(p: ref B) =
  if p == nil:
    discard (p.n, 1)
    symexTarget("after")

proc discardLen(p: ref C) =
  if p == nil:
    discard p.s.len
    symexTarget("after")

crashForms:
  case crashForm()
  of "keptField": discard keptField(nil)
  of "discardChecked": discardChecked(nil)
  of "discardCall": discardCall(nil)
  of "discardSeqIdx": discardSeqIdx(nil)
  of "letUnder": letUnder(nil)
  of "letUnused": letUnused(nil)
  of "discardTuple": discardTuple(nil)
  of "discardLen": discardLen(nil)
  else: discard

template keyOf(form: static string): CellKey =
  cellKey(faGeneric, "k9d/tsymex_0016_int86_discardnil/" & form & "/tNilAccess()")

suite "INT-86: an elided nil read does not fault":
  test "natively: each returns and reaches the label":
    check nativeRun(discardField(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardPtr(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardDeref(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardPtrField(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardChain(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardChain((ref B)())).hitsTarget(tLabel("after"))
    check nativeRun(discardCmp(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardConv(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardArr(nil)).hitsTarget(tLabel("after"))
    var vp: ref B = nil
    check nativeRun(discardVarParam(vp)).hitsTarget(tLabel("after"))

  test "the walker reaches the label behind it":
    for r in [pinFind(discardField, tLabel("after")).status,
              pinFind(discardPtr, tLabel("after")).status,
              pinFind(discardDeref, tLabel("after")).status,
              pinFind(discardPtrField, tLabel("after")).status,
              pinFind(discardChain, tLabel("after")).status,
              pinFind(discardCmp, tLabel("after")).status,
              pinFind(discardConv, tLabel("after")).status,
              pinFind(discardArr, tLabel("after")).status,
              symexFind(discardVarParam, tLabel("after")).status]:
      check r == sxSat

  test "and claims no nil access there":
    for r in [pinFind(discardField, tNilAccess()).status,
              pinFind(discardPtr, tNilAccess()).status,
              pinFind(discardDeref, tNilAccess()).status,
              pinFind(discardPtrField, tNilAccess()).status,
              pinFind(discardChain, tNilAccess()).status,
              pinFind(discardCmp, tNilAccess()).status,
              pinFind(discardConv, tNilAccess()).status,
              pinFind(discardArr, tNilAccess()).status,
              symexFind(discardVarParam, tNilAccess()).status]:
      check r == sxUnsat

suite "INT-86: a kept nil read faults":
  test "natively: each crashes":
    pinCrashSelf(keyOf("keptField"), "keptField", ceSegv)
    pinCrashSelf(keyOf("discardChecked"), "discardChecked", ceSegv)
    pinCrashSelf(keyOf("discardCall"), "discardCall", ceSegv)
    pinCrashSelf(keyOf("discardSeqIdx"), "discardSeqIdx", ceSegv)

  test "the walker claims the nil access, before the label":
    check symexFind(keptField, tNilAccess()).status == sxRaised
    check symexFind(discardChecked, tNilAccess()).status == sxRaised
    check symexFind(discardCall, tNilAccess()).status == sxRaised
    check symexFind(discardSeqIdx, tNilAccess()).status == sxRaised
    check symexFind(keptField, tLabel("after")).status == sxRaised
    check symexFind(discardChecked, tLabel("after")).status == sxRaised
    check symexFind(discardCall, tLabel("after")).status == sxRaised
    check symexFind(discardSeqIdx, tLabel("after")).status == sxRaised

suite "INT-86: a dead nil read is the optimiser's":
  test "natively, in this (unoptimised) build, each crashes":
    # Under `-d:release` each returns instead (the probe table in the
    # header): the outcome is the C compiler's, not the program's.
    pinCrashSelf(keyOf("letUnder"), "letUnder", ceSegv)
    pinCrashSelf(keyOf("letUnused"), "letUnused", ceSegv)
    pinCrashSelf(keyOf("discardTuple"), "discardTuple", ceSegv)
    pinCrashSelf(keyOf("discardLen"), "discardLen", ceSegv)

  test "the walker claims neither side: the nil path declines":
    template declines(fn: untyped) =
      ## Both targets, recorded through `pinDecline` (K9b).
      pinDecline(fn, keyOf(astToStr(fn)), feUnsupportedOp, tNilAccess())
      pinDecline(fn, keyOf(astToStr(fn)), feUnsupportedOp, tLabel("after"))
    declines(letUnder)
    declines(letUnused)
    declines(discardTuple)
    declines(discardLen)

suite "INT-86: the walker's version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 447
