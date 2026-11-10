## RFC-0016 K10b -- whole-run definedness (section 9.1 item 3), a round.
##
## A trusted `sxSat` needs the whole run defined, not only its prefix: the
## explore walk stops at the label (`shouldStop`), so what follows it was
## never seen (the 0.9.2 known gap). Under `SymexSettings.wholeRunDefinedness`
## the winner is checked by a second walk from the entry in concrete-follow
## mode under the witness's model pins, past the label to a routine exit. An
## undefined side the pins do not rule out, an opaque call whose body may be
## undefined (the parameterised `scanOpaqueDefects`), a decline, a budget or a
## lossy witness whose pins are missing untrusts the verdict through `Soundness.witnessUndefined`,
## which replay cannot lift. Gate off: 0.9.2's behaviour exactly.
import std/[unittest, strutils, os]
import nelli
import nelli/symex
import nelli/db
import ./s8cu_helpers

const gateOff = block:
  var s = pinSettingsConst
  s.wholeRunDefinedness = false
  s

# The file builds with `--overflowChecks:off` (its `.nim.cfg`): the
# `dpUnchecked` profile, under which a signed overflow is `ubSignedOverflow`
# (K10c pins the row). A per-routine push is W1-d2's decline route instead.
proc sutTailOverflow(x: int64): int64 =
  ## The label, then a signed overflow every input past the label takes.
  if x > 100: symexTarget("hit")
  result = x + high(int64)

proc sutTailBranch(x: int64) =
  ## The label at `x == 5`; the overflow sits on a branch the witness does
  ## not take.
  if x == 5: symexTarget("hit")
  if x > 100:
    let y {.used.} = x + high(int64)

proc sutTwoLabels(x: int64): int64 =
  ## Two labels: `a` is followed by an overflow, `b` is not.
  if x > 100:
    symexTarget("a")
    result = x + high(int64)
  elif x == 3:
    symexTarget("b")
    result = x

proc cAbs(x: cint): cint {.importc: "abs", header: "<stdlib.h>".}

proc sutTailForeign(x: int32) =
  ## The label, then a foreign call with no row: its body may be undefined.
  if x == 5: symexTarget("hit")
  discard cAbs(cint(x))

type
  LossyStub = object
    ## A plain object that looks like a variant (a leading `kind` and more
    ## than two fields): the witness reader renders it as `default(LossyStub)`,
    ## not as the model (`rendersAsDefaultObject`, `wfLossy`), so the witness
    ## cannot be followed past the label.
    kind: int
    a: int
    b: int

proc sutLossy(v: LossyStub; x: int64) =
  if x == 7: symexTarget("hit")

proc sutLossyOverflow(v: LossyStub; x: int64): int64 =
  ## The same lossy shape, with an overflow after the label.
  if x == 7: symexTarget("hit")
  result = x + high(int64)

type TailColor = enum tcRed, tcGreen, tcBlue

proc tailCol(a: int): TailColor =
  if a > 3: tcBlue elif a > 0: tcGreen else: tcRed

proc sutTailCallBranch(a: int) =
  ## The label, then a branch on a routine's result (`$tailCol(a)` matches the
  ## call's result against each member, and then compares the name). The pins
  ## cover `a` only; the result constant is bound in the path's `pc`.
  if $tailCol(a) == "tcGreen" and a == 2: symexTarget("hit")

suite "K10b: whole-run definedness":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 301

  test "(a) an undefined op after the label untrusts the sxSat, carrying its kind":
    pinUndefined(sutTailOverflow, cellKey(axDefinedness, "add/signedWide"),
                 UbKind(ubSignedOverflow))
    let r = symexFind(sutTailOverflow, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.trusted
    check r.soundness.undefinedKinds == {UbKind(ubSignedOverflow)}
    check r.witness[0] > 100

  test "(b) an undefined op on a branch the witness does not take: trusted":
    let r = pinExact(sutTailBranch, cellKey(axDefinedness, "add/signedWide"),
                     tLabel("hit"))
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 5

  test "(c) an opaque foreign call with no row after the label: untrusted":
    pinUndefined(sutTailForeign, cellKey(axDefinedness, "call/opaqueBody"),
                 UbKind(ubTailUnverified))
    let r = symexFind(sutTailForeign, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.trusted
    check UbKind(ubTailUnverified) in r.soundness.undefinedKinds
    check r.witness[0] == 5'i32

  test "(d) a lossy witness whose pins cover the choices: tail-checked, trusted":
    # The second walk needs the model's pins, not the rendered value
    # (section 9.1 item 3: "cannot be followed" is the condition).
    let r = symexFind(sutLossy, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted
    check r.soundness.undefinedKinds == {}
    check r.witness[1] == 7

  test "(d2) a lossy witness with an undefined tail: untrusted, by the tail's kind":
    let r = symexFind(sutLossyOverflow, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.trusted
    check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds

  test "(e) gate off: 0.9.2's verdict, trusted on its prefix":
    let r = symexFind(sutTailOverflow, tLabel("hit"), gateOff)
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted
    check r.soundness.undefinedKinds == {}
    check r.witness[0] > 100
    let r2 = symexFind(sutTailForeign, tLabel("hit"), gateOff)
    check r2.status == sxSat
    check r2.trusted
    let r3 = symexFind(sutLossy, tLabel("hit"), gateOff)
    check r3.status == sxSat
    check r3.trusted

  test "(f) symexFindAllWitnesses: trust per finding, one walk each":
    let fs = symexFindAllWitnesses(sutTwoLabels, inMemoryDatabase(),
                                   pinSettingsConst)
    var sawA, sawB = false
    for f in fs:
      checkpoint f.targetDesc & ": " & $f.soundness
      if "\"a\"" in f.targetDesc:
        sawA = true
        check f.status == sfSat
        check not f.trusted
        check f.soundness.undefinedKinds == {UbKind(ubSignedOverflow)}
      elif "\"b\"" in f.targetDesc:
        sawB = true
        check f.status == sfSat
        check f.trusted
        check f.soundness.undefinedKinds == {}
    check sawA and sawB

  test "(g) the pins fold: a defined tail over object params costs few units":
    # The pin on an int leaf of a heap-held object was an equality on the
    # leaf's Int projection (`ubv_to_int` under a sign `ite`), so every query
    # the second walk issued was mixed-theory over 64-bit words: 477,838 units
    # for a tail with nothing in it. Pinned on the bit-vector itself it folds.
    let log = getTempDir() / "k10b_g_units.log"
    removeFile(log)
    putEnv("NELLI_WALK_UNITS_LOG", log)
    defer:
      delEnv("NELLI_WALK_UNITS_LOG")
      removeFile(log)
    let r = symexFind(sutLossy, tLabel("hit"), pinSettingsConst)
    check r.status == sxSat
    check r.trusted
    var tail = -1
    for line in readFile(log).splitLines:
      let f = line.split('\t')
      if f.len >= 2 and f[1] == "k10b-tail": tail = parseInt(f[0])
    checkpoint "tail units: " & $tail
    check tail >= 0 and tail < 20_000

  test "(h) a branch on a call's result in the tail is decided by the pc: no walker fault":
    # The tail walk asked the pins alone whether `tailCol(a) == tcGreen`; the
    # call's result is a fresh constant bound in the path's `pc`, so the
    # branch read as undecided and the walk went on without the arm's
    # bindings: `weInternalWalkerFault` (`eqBV` on an unbound string).
    let r = symexFind(sutTailCallBranch, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted
    check r.soundness.undefinedKinds == {}
    check r.witness[0] == 2
    for e in r.errors:
      check e.kind != weInternalWalkerFault

var tailGlobal = 0
proc setTailGlobal(v: int) =
  ## Natively reachable state: an earlier call of the program sets it.
  tailGlobal = v

proc sutTailUndecided(x: int64) =
  ## The label, then a branch on a module global the SUT never writes. Neither
  ## the parameter pins nor the path's `pc` say what it holds (the walk reads
  ## it as a free constant), so the branch is undecided. Natively the arm is
  ## reachable: `setTailGlobal(6)` ran before the call, and then
  ## `x + high(int64)` overflows (checks off: undefined).
  if x == 5: symexTarget("hit")
  if tailGlobal > 5:
    let y {.used.} = x + high(int64)

suite "K10b: an undecided branch in the tail fails closed":
  test "(i) a branch the pins and the pc leave open untrusts the sxSat":
    # RFC section 9.1 item 3: an undecided side counts as undefined. Taking
    # neither arm's bindings and walking on would skip the overflow. Since
    # W3-z R6 the tail walk forks the open branch and walks both arms, so the
    # verdict carries the overflow's own kind, not `ubTailUnverified`.
    let r = symexFind(sutTailUndecided, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.trusted
    check r.soundness.undefinedKinds == {UbKind(ubSignedOverflow)}
    check r.witness[0] == 5

proc sutTailUndecidedDefined(x: int64): int64 =
  ## The label, then the same open branch on `tailGlobal`, defined on both
  ## arms: natively the run is defined whatever an earlier call left there.
  if x == 5: symexTarget("hit")
  if tailGlobal > 5: result = x + 1
  else: result = x - 1

proc sutTailUndecidedLoop(x: int64): int64 =
  ## The label, then a loop whose guard reads `tailGlobal`: the pins leave
  ## the guard open on every unrolled step, and the body is defined.
  if x == 5: symexTarget("hit")
  var i = 0
  while i < tailGlobal and i < 3:
    inc i
  result = x + int64(i)

proc nativeDefinedOnBothArms(f: proc (x: int64): int64 {.nimcall.};
                             x: int64; lo, hi: int64): bool =
  ## Natively, under every global an earlier call can leave (`0` and `6`),
  ## the run's result stays in `x + lo .. x + hi`: no arm wrapped.
  result = true
  for g in [0, 6]:
    setTailGlobal(g)
    let v = f(x)
    if v < x + lo or v > x + hi: result = false
  setTailGlobal(0)

suite "W3-z R6: the winner's tail walk over-approximates an open branch":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 317

  test "(i2) an open branch in the tail, defined on both arms: trusted":
    # The winner's tail walk forks the open branch both ways, as a
    # candidate's does (R2), and finds no undefined arm. Before R6 it read
    # the branch as undecided and failed closed (`ubTailUnverified`).
    let r = symexFind(sutTailUndecidedDefined, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.witness[0] == 5
    check r.trusted
    check r.soundness.undefinedKinds == {}
    # Native agreement: defined whatever the global holds.
    check nativeDefinedOnBothArms(sutTailUndecidedDefined, r.witness[0], -1, 1)

  test "(i3) an open loop guard in the tail, defined body: trusted":
    let r = symexFind(sutTailUndecidedLoop, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.witness[0] == 5
    check r.trusted
    check r.soundness.undefinedKinds == {}
    check nativeDefinedOnBothArms(sutTailUndecidedLoop, r.witness[0], 0, 3)

type TailRef = ref object
  v: int

proc sutTailRefNil(p: TailRef; x: int64) =
  ## The label, then a branch on a ref param's nil-ness. The explore path
  ## (`x == 5`) never mentions `p`, so the model leaves `p` and the sort's
  ## `nil` constant unconstrained. An unconstrained constant takes any value
  ## consistent with the witness, so the branch is decided under the pins
  ## and is not an undecided one.
  if x == 5: symexTarget("hit")
  if p == nil:
    let y {.used.} = x + high(int64)

suite "K10b: an unconstrained ref's nil constant is pinned by completion":
  test "version floor (the pins complete an unmentioned nil at 304)":
    check parseInt(symexWalkerVersion) >= 304
  test "version floor (modelPins over the path's own heaps at 308)":
    check parseInt(symexWalkerVersion) >= 308
  test "(j) a tail branch on a ref param's nil-ness decides; native agrees":
    let r = symexFind(sutTailRefNil, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check r.status == sxSat
    # Never undecided: the branch follows the witness's own `p`.
    check UbKind(ubTailUnverified) notin r.soundness.undefinedKinds
    # Native agreement: the overflow (undefined, checks off) is reached
    # exactly when the witness's `p` is nil.
    let pNil = r.witness[0] == nil
    check r.trusted == not pNil
    if pNil:
      check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds

proc sutTailByteScan(data: seq[byte]; x: int64) =
  ## The label, then a NUL scan over a `seq[byte]` the scan makes
  ## string-backed (round-6 B1: one Z3 String, not a seq cell), then an
  ## overflow on a branch the scan's result decides. The explore path never
  ## mentions `data`, so only the witness's pin on it decides the branch.
  if x == 5: symexTarget("hit")
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  if i > 3:
    let y {.used.} = x + high(int64)

proc nativeScanLen(data: seq[byte]): int =
  while result < data.len and data[result] != 0'u8:
    inc result

suite "W3-z int2: a string-backed seq[byte] parameter is pinned":
  test "version floor (modelPins pins the string at 342)":
    check parseInt(symexWalkerVersion) >= 342
  test "(k) a tail branch on a string-backed param's bytes decides; native agrees":
    # The parameter was left out of the pins (its String fits no seq cell),
    # so the branch was open and the tail walk, forking it (R6), walked the
    # overflow arm the witness does not take: untrusted. Each such branch
    # was also asked at the scratch-check cap, which a pair-loop over the
    # receiver multiplied past any bound (`tsymex_r6_b7r_bytescan` B7R-6).
    let log = getTempDir() / "k10b_k_units.log"
    removeFile(log)
    putEnv("NELLI_WALK_UNITS_LOG", log)
    defer:
      delEnv("NELLI_WALK_UNITS_LOG")
      removeFile(log)
    let r = symexFind(sutTailByteScan, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.witness[1] == 5
    check UbKind(ubTailUnverified) notin r.soundness.undefinedKinds
    # Native agreement: the overflow is reached exactly when the witness's
    # scan runs past index 3.
    let past = nativeScanLen(r.witness[0]) > 3
    check r.trusted == not past
    if past:
      check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds
    var tail = -1
    for line in readFile(log).splitLines:
      let f = line.split('\t')
      if f.len >= 2 and f[1] == "k10b-tail": tail = parseInt(f[0])
    checkpoint "tail units: " & $tail
    check tail >= 0 and tail < 2_000_000
