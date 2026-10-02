## RFC-0005 (soundness channels) slice S8am -- S8z's remainder.
##
## Six items from S8z's "Different mechanisms, reported and not fixed
## here" list (RFC §2.5):
##   (1) `s[i] += v`/`-=`/`*=`/`&=` on a SEQ ELEMENT -- `valueFieldTy`/
##       `fieldStep` had no `itSeq` case (only array/tuple/object), so this
##       declined `feUnsupportedStmtKind` even though `a[i] += v` on an
##       ARRAY already worked.
##   (2) `s[i] = f()` on a seq -- Nim checks the index bound BEFORE
##       evaluating `f()` (probed against a compiled binary: an OOB
##       `s[i] = raiser()` never runs `raiser`'s side effect, raising
##       `IndexDefect` immediately), but A-normalisation (`userCallStmt`)
##       hoisted `f()`'s call into the preamble ahead of the
##       `isIndexAssign` statement's own WALK-time bounds check, so the
##       call ran first regardless of the index -- an unsound evaluation
##       order. The array write arm already had the correct order (S8z's
##       `valueFieldChecked`); a bare seq element assignment did not.
##   (3) a `char` witness parameter (or `char` Table value / HashSet
##       element) rendered `uint8`, not `char` -- `char`/`byte`/`uint8`
##       share one structural `IRType`.
##   (4) `low(a)`/`high(a)` on an ARRAY VALUE declined
##       `feUnsupportedExprKind` (the non-int-family branch), the
##       symmetric gap to the pre-existing `isStringLow`/`isStringHigh`
##       carve-out for strings.
##   (5) a non-zero-based array witness (`array[1..3, int]`) rendered
##       `array[0..2, int]` -- the element VALUES were already positionally
##       correct (S8z), only the witness's own declared array type's index
##       origin was wrong.
##   (6) `array[bool, T]` declined (`arrayIndexBounds` had no `itBool`
##       case), and a `char`/`byte`/`uint8` Table value / HashSet element
##       PARAMETER was routed to the `__unsupported_witness:` placeholder
##       at parse time (`isRenderableTableTy`/`isRenderableSetElemTy`'s
##       `isCharAmbiguous` exclusion), forcing every property over such a
##       parameter to `sxUnknown` regardless of the property.
##
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build) by the oracle test of each suite, which runs the SUT
## itself.
import std/[unittest, strutils, tables, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

template expectSat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxSat

template expectUnsat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxUnsat

template expectExactSat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxSat
  check r.errors.len == 0

template expectUnknown(r: untyped; k: SymexErrorKind) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxUnknown
  check hasKind(r.errors, k)

# ---- (1) compound assignment on a seq element -------------------------------

proc seqPlusEq(i: int) =
  var s = @[1, 2, 3]
  s[i] += 10
  if i >= 0 and i < 3 and s[i] == 12: symexTarget("s8am_pe")

proc seqMinusEq(i: int) =
  var s = @[10, 20, 30]
  s[i] -= 5
  if i >= 0 and i < 3 and s[i] == 15: symexTarget("s8am_me")

proc seqTimesEq(i: int) =
  var s = @[1, 2, 3]
  s[i] *= 4
  if i >= 0 and i < 3 and s[i] == 8: symexTarget("s8am_te")

proc seqAmpEq(i: int) =
  var s = @["a", "b", "c"]
  s[i] &= "z"
  if i >= 0 and i < 3 and s[i] == "bz": symexTarget("s8am_ae")

suite "S8am (1) compound assignment on a seq element":
  test "oracle":
    symexCaptureBegin()
    seqPlusEq(1); seqMinusEq(1); seqTimesEq(1); seqAmpEq(1)
    let hits = symexCaptureEnd()
    check "s8am_pe" in hits
    check "s8am_me" in hits
    check "s8am_te" in hits
    check "s8am_ae" in hits

  test "s[i] += v (int)":
    let r = seqPlusEq.symexFind(tLabel("s8am_pe"))
    expectExactSat(r)
    if r.status == sxSat: check reproduces(seqPlusEq(r.witness[0]), "s8am_pe")

  test "s[i] -= v (int)":
    expectExactSat(seqMinusEq.symexFind(tLabel("s8am_me")))

  test "s[i] *= v (int)":
    expectExactSat(seqTimesEq.symexFind(tLabel("s8am_te")))

  test "s[i] &= v (string)":
    expectExactSat(seqAmpEq.symexFind(tLabel("s8am_ae")))

# ---- (2) seq element assignment checks the index before the RHS -------------

var s8amOrderLog {.threadvar.}: seq[string]

proc orderRaiser(tag: string): int =
  s8amOrderLog.add tag
  raise newException(ValueError, "orderRaiser")

proc seqAsgnOrder(i: int) =
  var s = @[1, 2, 3]
  s[i] = orderRaiser("called")

proc seqCompoundOrder(i: int) =
  var s = @[1, 2, 3]
  s[i] += orderRaiser("called")

suite "S8am (2) seq element assignment checks the index before the RHS":
  test "oracle: a real OOB `s[i] = raiser()` never calls raiser (Nim semantics)":
    s8amOrderLog = @[]
    expect(IndexDefect):
      seqAsgnOrder(9)
    check s8amOrderLog.len == 0

  test "oracle: a real OOB `s[i] += raiser()` never calls raiser either":
    s8amOrderLog = @[]
    expect(IndexDefect):
      seqCompoundOrder(9)
    check s8amOrderLog.len == 0

  test "walker: s[i] = f() still reaches ValueError (forward/in-bounds direction intact)":
    let r = seqAsgnOrder.symexFind(tRaisedExn("ValueError"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    ## NOT asserted: `r.raisedWitness[0]` lands in 0..2. `i` plays no role
    ## in `orderRaiser`'s OWN raise condition (it raises unconditionally
    ## once called), so nothing in `routeRaise`'s query need pin it down --
    ## a witness-extraction characteristic confirmed PRE-EXISTING (same
    ## free `i`, same sentinel, on the already-S8z-fixed ARRAY write's
    ## identical shape), not a S8am order regression.

  test "walker: s[i] = f() reaches IndexDefect through an OUT-OF-BOUNDS index":
    ## Unlike `ValueError` above, `i` IS part of `IndexDefect`'s own raise
    ## condition (`not (inLoCond and inHiCond)`), so its witness genuinely
    ## is pinned outside the bound here.
    let r = seqAsgnOrder.symexFind(tRaisedExn("IndexDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedWitness[0] notin 0 .. 2

  test "walker: s[i] += f() still reaches ValueError (compound form)":
    let r = seqCompoundOrder.symexFind(tRaisedExn("ValueError"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised

  test "walker: s[i] += f() reaches IndexDefect through an OUT-OF-BOUNDS index (compound form)":
    let r = seqCompoundOrder.symexFind(tRaisedExn("IndexDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedWitness[0] notin 0 .. 2

# ---- (3) char witness rendering ----------------------------------------------

proc charParam(c: char) =
  if c == 'q': symexTarget("s8am_char")

suite "S8am (3) char witness rendering":
  test "oracle":
    check (block:
      symexCaptureBegin()
      charParam('q')
      "s8am_char" in symexCaptureEnd())

  test "a char parameter's witness is Nim's own char type":
    let r = charParam.symexFind(tLabel("s8am_char"))
    expectExactSat(r)
    if r.status == sxSat:
      check r.witness[0] is char
      check r.witness[0] == 'q'

# ---- (4) low(a)/high(a) on an array -------------------------------------------

proc arrLowHigh(i: int) =
  var a = [10, 20, 30]
  if i == low(a): symexTarget("s8am_lo")
  if i == high(a): symexTarget("s8am_hi")

proc arrLowHighNonZero(i: int) =
  var a: array[1..3, int] = [10, 20, 30]
  if i == low(a): symexTarget("s8am_lo1")
  if i == high(a): symexTarget("s8am_hi1")

suite "S8am (4) low(a)/high(a) on an array value":
  test "oracle":
    symexCaptureBegin()
    arrLowHigh(0); arrLowHigh(2); arrLowHighNonZero(1); arrLowHighNonZero(3)
    let hits = symexCaptureEnd()
    for l in ["s8am_lo", "s8am_hi", "s8am_lo1", "s8am_hi1"]: check l in hits

  test "low(a)/high(a) of a zero-based array":
    let rLo = arrLowHigh.symexFind(tLabel("s8am_lo"))
    expectExactSat(rLo)
    if rLo.status == sxSat: check rLo.witness[0] == 0
    let rHi = arrLowHigh.symexFind(tLabel("s8am_hi"))
    expectExactSat(rHi)
    if rHi.status == sxSat: check rHi.witness[0] == 2

  test "low(a)/high(a) of a non-zero-based array":
    let rLo = arrLowHighNonZero.symexFind(tLabel("s8am_lo1"))
    expectExactSat(rLo)
    if rLo.status == sxSat: check rLo.witness[0] == 1
    let rHi = arrLowHighNonZero.symexFind(tLabel("s8am_hi1"))
    expectExactSat(rHi)
    if rHi.status == sxSat: check rHi.witness[0] == 3

# ---- (5) non-zero array witness renders its declared index range -------------

proc nonZeroArrParam(a: array[1..3, int]) =
  if a[1] == 7 and a[2] == 8 and a[3] == 9: symexTarget("s8am_nz")

suite "S8am (5) non-zero array witness renders its declared index range":
  test "oracle":
    check (block:
      symexCaptureBegin()
      nonZeroArrParam([7, 8, 9])
      "s8am_nz" in symexCaptureEnd())

  test "array[1..3, int] witness is array[1..3, int], not array[0..2, int]":
    let r = nonZeroArrParam.symexFind(tLabel("s8am_nz"))
    expectExactSat(r)
    if r.status == sxSat:
      check r.witness[0].low == 1
      check r.witness[0].high == 3
      check r.witness[0][1] == 7
      check r.witness[0][2] == 8
      check r.witness[0][3] == 9

# ---- (6a) array[bool, T] ------------------------------------------------------

proc boolArrRead(flag: bool) =
  var a: array[bool, int] = [10, 20]
  if a[flag] == 20: symexTarget("s8am_ba_r")

proc boolArrWrite(flag: bool, v: int) =
  var a: array[bool, int] = [10, 20]
  a[flag] = v
  if a[true] == 99: symexTarget("s8am_ba_w")

suite "S8am (6a) array[bool, T]":
  test "oracle":
    symexCaptureBegin()
    boolArrRead(true); boolArrWrite(true, 99)
    let hits = symexCaptureEnd()
    check "s8am_ba_r" in hits
    check "s8am_ba_w" in hits

  test "array[bool, T] read at a symbolic bool index":
    let r = boolArrRead.symexFind(tLabel("s8am_ba_r"))
    expectExactSat(r)
    if r.status == sxSat: check r.witness[0] == true

  test "array[bool, T] write at a symbolic bool index":
    let r = boolArrWrite.symexFind(tLabel("s8am_ba_w"))
    expectExactSat(r)
    if r.status == sxSat:
      check r.witness[0] == true
      check r.witness[1] == 99

# ---- (6b) char/byte/uint8 Table values and HashSet elements -------------------

proc charSetParam(s: HashSet[char]) =
  if 'q' in s: symexTarget("s8am_cs")

proc byteSetParam(s: HashSet[byte]) =
  if 200.byte in s: symexTarget("s8am_bs")

proc charTableParam(t: Table[string, char]) =
  if "k" in t and t["k"] == 'z': symexTarget("s8am_ct")

suite "S8am (6b) char/byte/uint8 Table values and HashSet elements are reachable witness parameters":
  test "oracle":
    symexCaptureBegin()
    var s1 = toHashSet(['q'])
    var s2 = toHashSet([200.byte])
    var t1 = {"k": 'z'}.toTable
    charSetParam(s1); byteSetParam(s2); charTableParam(t1)
    let hits = symexCaptureEnd()
    check "s8am_cs" in hits
    check "s8am_bs" in hits
    check "s8am_ct" in hits

  test "HashSet[char] parameter witness, was __unsupported_witness:":
    let r = charSetParam.symexFind(tLabel("s8am_cs"))
    expectExactSat(r)
    if r.status == sxSat: check 'q' in r.witness[0]

  test "HashSet[byte] parameter witness":
    let r = byteSetParam.symexFind(tLabel("s8am_bs"))
    expectExactSat(r)
    if r.status == sxSat: check 200.byte in r.witness[0]

  test "Table[string, char] parameter witness, was __unsupported_witness:":
    expectExactSat(charTableParam.symexFind(tLabel("s8am_ct")))

# ---- (6c) remaining scoped declines, pinned ------------------------------------
#
# A non-string Table key, or a non-int-family Table value / HashSet
# element, is still out of scope -- no sound Z3 representation exists for
# either (the engine's Table is hard-wired to a String-sorted Z3 array;
# float has no `fpToIEEEBV` FFI binding in this codebase, and
# string/composite have no fixed-width cell encoding). RFC-0005 S8z already
# reasoned and pinned the INTERNALLY-CONSTRUCTED-value shape of this decline
# (`allocDegrade` call sites in runtime.nim, exercised by
# tsymex_r6_n39/n40/n43's heap-field tests: `seUnsupportedTableKeyType` /
# `seUnsupportedTableValType` / `seUnsupportedSetCharInterop`). As a
# top-level WITNESS PARAMETER, the shape is instead caught earlier, at
# `parseProc*`'s own `isRenderableWitnessTy` classification (CR-2c): the
# whole parameter is replaced by the `__unsupported_witness:` placeholder
# before allocation ever runs, reported `feUnsupportedWitnessType`. This
# suite pins THAT shape (the one item 6 is actually about) to confirm this
# slice's `isCharAmbiguous` relaxation did not widen the gate past what is
# actually backed.
#
# RFC-0005 S8ar backs every string or integer-like key and every
# integer-like, string or float value, so `Table[int, int]` and
# `Table[string, float]` now render (pinned `sxSat` in
# tsymex_rfc0005_s8ar_remainder). The two pins below moved to shapes S8ar
# still does not back: a `float` key and a container value.

proc intKeyTable(t: Table[float, int]) =
  if t.len > 0: symexTarget("s8am_ikt")

proc floatValTable(t: Table[string, seq[int]]) =
  if t.len > 0: symexTarget("s8am_fvt")

proc stringSet(s: HashSet[string]) =
  if s.len > 0: symexTarget("s8am_ss")

suite "S8am (6c) non-string Table keys and non-int-family values/elements stay scoped declines":
  test "Table[float, int] param -- unbacked key -- feUnsupportedWitnessType":
    let r = intKeyTable.symexFind(tLabel("s8am_ikt"))
    expectUnknown(r, feUnsupportedWitnessType)

  test "Table[string, seq[int]] param -- container value -- feUnsupportedWitnessType":
    let r = floatValTable.symexFind(tLabel("s8am_fvt"))
    expectUnknown(r, feUnsupportedWitnessType)

  test "HashSet[string] param -- non-int-family element -- feUnsupportedWitnessType":
    let r = stringSet.symexFind(tLabel("s8am_ss"))
    expectUnknown(r, feUnsupportedWitnessType)

# ---- walker version -----------------------------------------------------------

suite "S8am walker version":
  test "symexWalkerVersion is at least S8am's":
    check parseInt(symexWalkerVersion) >= 183
