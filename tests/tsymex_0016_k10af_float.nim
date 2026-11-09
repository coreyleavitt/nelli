## RFC-0016 K10a-float (section 9.1 item 2) -- a float -> int conversion whose
## operand is NaN, infinite or out of the target's range is undefined
## behaviour: Nim 2.2.10 emits a plain C cast and range-checks the CAST value,
## so no check profile raises. The conversion drain (`convert/floatToInt` of
## the definedness axis) ends that side through `haltUndefined` with
## `ubFloatToIntRange`; the in-range side is exact (truncation toward zero).
##
## Native agreement is pinned where the conversion is defined (the label is
## reproduced by the witness in the host); the undefined side is pinned by
## `tUndefined` findings, which are never run.
import std/[unittest, strutils, math]
import nelli
import nelli/symex
import nelli/smt/definedness
import nelli/smt/errorkind
import ./s8cu_helpers

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

proc sutInt(f: float) =
  let i = int(f)
  if i == 7: symexTarget("hit")

proc sutIntBig(f: float) =
  let i = int(f)
  if i == high(int): symexTarget("hit")

proc sutInt32(f: float) =
  let i = int32(f)
  if i == -5: symexTarget("hit")

proc sutU8(f: float) =
  let i = uint8(f)
  if i == 200: symexTarget("hit")

proc sutF32(f: float32) =
  let i = int(f)
  if i == 3: symexTarget("hit")

proc sutGuarded(f: float) =
  if f > -1000.0 and f < 1000.0:
    let i = int(f)
    if i == 7: symexTarget("hit")

proc sutTruncNeg(f: float) =
  let i = int(f)
  if i == 0 and f < 0.0: symexTarget("hit")   # -0.5 truncates to 0

proc sutNatural(f: float) =
  let n = Natural(f)
  discard n

proc sutBoundary(f: float) =
  if f == 9223372036854775807.0: symexTarget("hit")  # that literal is 2^63

proc sutBelow(f: float) =
  if f == 9223372036854774784.0:                     # largest float below 2^63
    let i = int(f)
    if i == 9223372036854774784: symexTarget("hit")

proc sutTwo63(f: float) =
  if f == 9223372036854775808.0:
    let i = int(f)
    discard i
    symexTarget("hit")

proc sutNegZero(f: float) =
  if f == 0.0 and 1.0 / f < 0.0:
    let i = int(f)
    if i == 0: symexTarget("hit")

proc sutHalf(f: float) =
  if f == 0.5:
    let i = int(f)
    if i == 0: symexTarget("hit")

suite "K10a-float: float -> int is undefined out of range":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 300

  test "the table: every profile is undefined, and the kind is appended":
    for p in DefProfile:
      check convertDefinedness(p) ==
        Definedness(kind: dkUndefined, ub: ubFloatToIntRange)
    check admitDefined(aoConvert, ocFloatToInt, dsConvert).admitted
    check not admitDefined(aoConvert, ocFloatToInt, dsArith).admitted
    check ord(ubFloatToIntRange) == ord(ubSignedDivZero) + 1

  test "tUndefined finds NaN, an infinity or a too-large operand":
    let r = symexFind(sutInt, tUndefined({UbKind(ubFloatToIntRange)}))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.soundness.undefinedKinds == {UbKind(ubFloatToIntRange)}
    check not r.trusted
    let w = r.witness[0]
    check w.isNaN or abs(w) >= 9.2e18

  test "a narrow target is undefined past its own range":
    let r = symexFind(sutInt32, tUndefined())
    check r.status == sxSat
    check abs(r.witness[0]) >= 2147483648.0 or r.witness[0].isNaN
    let u = symexFind(sutU8, tUndefined())
    check u.status == sxSat
    check u.witness[0].isNaN or u.witness[0] <= -1.0 or u.witness[0] >= 256.0

  test "a float32 operand":
    let r = symexFind(sutF32, tUndefined())
    check r.status == sxSat
    check r.soundness.undefinedKinds == {UbKind(ubFloatToIntRange)}

  test "a guarded conversion has no undefined side: trusted sxUnsat":
    let r = symexFind(sutGuarded, tUndefined())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check r.trusted

  test "under a label search the conversion is listed as a finding":
    let r = symexFind(sutInt, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 7.0 or (r.witness[0] >= 7.0 and r.witness[0] < 8.0)
    check reproduces(sutInt(r.witness[0]), "hit")
    check r.undefined.len == 1
    check r.undefined[0].kind == UbKind(ubFloatToIntRange)
    check r.undefined[0].site.len > 0
    check r.trusted == false or r.undefined.len == 1

  test "int(NaN) == low(int) is no longer a reachable label":
    # the native value is platform-defined; the halt does not claim it
    let r = symexFind(sutIntBig, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status != sxUnsat or not r.trusted
    check not r.trusted

  test "in range the truncation is exact and replay-confirmed":
    let r = symexFind(sutGuarded, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] >= 7.0 and r.witness[0] < 8.0
    check reproduces(sutGuarded(r.witness[0]), "hit")
    check r.undefined.len == 0
    check r.trusted

  test "-0.5 truncates toward zero":
    let r = symexFind(sutTruncNeg, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] < 0.0 and r.witness[0] > -1.0
    check reproduces(sutTruncNeg(r.witness[0]), "hit")

  test "boundary: the largest float below 2^63 converts, 2^63 is undefined":
    let below = symexFind(sutBelow, tLabel("hit"))
    checkpoint show(below.errors)
    check below.status == sxSat
    check below.undefined.len == 0
    check reproduces(sutBelow(9223372036854774784.0), "hit")
    let at = symexFind(sutTwo63, tUndefined())
    check at.status == sxSat
    check at.witness[0] == 9223372036854775808.0

  test "0.5 and -0.0 convert to 0":
    let h = symexFind(sutHalf, tLabel("hit"))
    check h.status == sxSat and h.undefined.len == 0
    check reproduces(sutHalf(0.5), "hit")
    let z = symexFind(sutNegZero, tLabel("hit"))
    check z.status == sxSat and z.undefined.len == 0
    check reproduces(sutNegZero(-0.0), "hit")

  test "a range target still raises RangeDefect in range of the base type":
    let r = symexFind(sutNatural, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "RangeDefect"

  test "int(f) never raises RangeDefect: the undefined side halts, sxUnknown":
    let r = symexFind(sutInt, tRaisedExn("RangeDefect"))
    check r.status == sxUnknown
    check not r.trusted
    check r.errors.named(ubFloatToIntRange)

  test "the cell is evidenced: the halt records ubFloatToIntRange":
    pinDecline(sutInt, cellKey(axDefinedness, "convert/floatToInt"),
               ubFloatToIntRange, tRaisedExn("RangeDefect"))
