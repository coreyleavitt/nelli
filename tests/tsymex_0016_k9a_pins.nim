## RFC-0016 K9a -- the native-pin verbs and the pin record.
import std/[unittest, os, options, strutils, sets, sequtils]
import nelli
import nelli/symex
import ./s8cu_helpers
import ./s8cu_fix_assert

let pinTmp = getTempDir() / ("k9a_pins_" & $getCurrentProcessId())
createDir(pinTmp)
# Always private, never the caller's dir: this file plants deliberately wrong
# claims (pinExactOn, entry "caller") and counts records, so its records must
# not reach a sweep-wide or K1 pin directory.
putEnv("NELLI_PIN_DIR", pinTmp)

proc recordsFor(cell: CellKey): seq[PinRecord] =
  for r in pinRecords(pinTmp):
    if r.cell == cell: result.add r

let probeDir = currentSourcePath().parentDir

template failsWith(body: untyped; part: string) =
  ## The pin must fail, and for the reason named.
  var msg = ""
  try: body
  except PinFailure as e: msg = e.msg
  check msg.len > 0
  check part in msg

proc ignore[T](x: T) = discard

proc sutSimple(x: int) =
  if x == 7: symexTarget("hit")

proc sutNever(x: int) =
  if x > 5 and x < 3: symexTarget("hit")

suite "K9a":
  test "CellKey render and parse round-trip":
    for sc in Scope:
      for k in ["DivU", "a/b", "x:y:z", "with space"]:
        let c = CellKey(scope: sc, key: k)
        check parseCellKey(render(c)) == some(c)
    check render(cellKey(axMagic, "DivU")) == "magic:DivU"
    check render(cellKey(faCallShape, "s")) == "family:callshape:s"
    check parseCellKey("nosuch:x").isNone
    check parseCellKey("magic:").isNone

  test "pinExact on a sat SUT records and reads back field for field":
    let key = cellKey(faGeneric, "k9a/sat")
    let r = pinExact(sutSimple, key)
    check r.status == sxSat
    let recs = recordsFor(key)
    check recs.len == 1
    let rec = recs[0]
    check rec.testFile == "tsymex_0016_k9a_pins.nim"
    check rec.entry == "symexFind"
    check rec.target == describeTarget(tLabel("hit"))
    check rec.domain == describe(boundaryInts)
    check not rec.exhaustive
    check rec.verdict == pvExact
    check rec.walker == "sxSat"
    check rec.native.startsWith("witness hit")
    check rec.build == pinBuildSegment()
    check rec.runId.len > 0
    check rec.flags.len == 0

  test "pinExact on an unsat SUT checks the domain":
    let key = cellKey(faGeneric, "k9a/unsat")
    discard pinExact(sutNever, key, domain = exhaustive([0, 1, 2, 7]))
    let recs = recordsFor(key)
    check recs.len == 1
    check recs[0].walker == "sxUnsat"
    check recs[0].exhaustive
    check recs[0].native == "no domain value hit (4)"

  test "a planted wrong exact pin fails":
    # The walker is right about sutSimple, so the lie is planted in the claim:
    # an sxUnsat for a label the domain reaches natively, and an sxSat whose
    # witness does not.
    type W = tuple[x: int]
    let key = cellKey(faGeneric, "k9a/planted")
    let settled = Soundness(replay: rsNotNeeded)
    let lieUnsat = SymexResult[W](status: sxUnsat, soundness: settled)
    failsWith(
      ignore(pinExactOn(sutSimple, lieUnsat, key)), "hits it natively")
    let lieSat = SymexResult[W](status: sxSat, witness: (x: 3), soundness: settled)
    failsWith(
      ignore(pinExactOn(sutSimple, lieSat, key)), "does not hit natively")
    # The same claims, told truthfully, pass.
    let truthSat = SymexResult[W](status: sxSat, witness: (x: 7), soundness: settled)
    discard pinExactOn(sutSimple, truthSat, key)
    check recordsFor(key).len == 1

  test "pinDecline passes with the right kind and fails with a wrong one":
    let key = cellKey(faGeneric, "k9a/decline")
    pinDecline(readWrappedNot, key, feGlobalHavoc)
    let recs = recordsFor(key)
    check recs.len == 1
    check recs[0].verdict == pvDeclined
    check recs[0].declineKind == "feGlobalHavoc"
    check recs[0].walker in ["sxSat", "sxUnknown", "sxUnsat"]
    failsWith(pinDecline(readWrappedNot, key, feCheckOption), "no feCheckOption")
    # A trusted verdict is not a decline.
    failsWith(pinDecline(sutSimple, key, feGlobalHavoc), "is trusted")
    check recordsFor(key).len == 1

  test "pinCrash: a division trap passes, an exit 0 fails":
    let key = cellKey(faGeneric, "k9a/crash")
    pinCrash(key, probeDir / "s0016_k9a_probe_div.nim",
             [], ceDivTrap)
    let recs = recordsFor(key)
    check recs.len == 1
    check recs[0].verdict == pvCrashed
    check recs[0].entry == "pinCrash"
    check recs[0].flags.len > 0
    check recs[0].native.startsWith("rc=")
    when not defined(windows): check recs[0].native.startsWith("rc=136")
    failsWith(pinCrash(key, probeDir / "s0016_k9a_probe_ok.nim", [], ceDivTrap),
              "exited 0")
    # a crash of the wrong class is refused too
    failsWith(pinCrash(key, probeDir / "s0016_k9a_probe_div.nim", [], ceSegv),
              "is not the expected")
    # source text is accepted in place of a path
    pinCrash(key, "quit(3)\n", [], ceAbnormal)
    check recordsFor(key).len == 2

  test "crashClassOn: Windows classification is by evidence":
    const fpe = "SIGFPE: Arithmetic error.\n"
    const segv = "SIGSEGV: Illegal storage access. (Attempt to read from nil?)\n"
    # Windows: raw SEH codes and Nim's mapped report (exit 1)
    check crashClassOn(int(cast[int32](0xC0000094'u32)), "", ceDivTrap, true)
    check crashClassOn(int(cast[int32](0xC0000095'u32)), "", ceDivTrap, true)
    check crashClassOn(1, fpe, ceDivTrap, true)
    check not crashClassOn(1, "", ceDivTrap, true)
    check not crashClassOn(1, segv, ceDivTrap, true)
    check not crashClassOn(0, fpe, ceDivTrap, true)
    check crashClassOn(int(cast[int32](0xC0000005'u32)), "", ceSegv, true)
    check crashClassOn(1, segv, ceSegv, true)
    check not crashClassOn(1, fpe, ceSegv, true)
    check not crashClassOn(1, "boom", ceSegv, true)
    check crashClassOn(1, "x [ValueDefect]", ceDefect, true)
    check crashClassOn(3, "", ceAbnormal, true)
    check not crashClassOn(0, "", ceAbnormal, true)
    # POSIX: unchanged, and a Windows-shaped result is not a POSIX trap
    check crashClassOn(136, "", ceDivTrap, false)
    check crashClassOn(139, "", ceSegv, false)
    check not crashClassOn(1, fpe, ceDivTrap, false)

  test "skipCell writes a skipped record":
    let key = cellKey(axMagic, "DivU")
    skipCell(key, "no native oracle on this build")
    let recs = recordsFor(key)
    check recs.len == 1
    check recs[0].verdict == pvSkipped
    check recs[0].why == "no native oracle on this build"
    check recs[0].entry == "skipCell"
  test "K9b: no test file defines its own nativeHits":
    # The one definition is s8cu_helpers'; every suite imports it.
    var offenders: seq[string]
    for f in walkFiles(probeDir / "*.nim"):
      if f.extractFilename == "s8cu_helpers.nim": continue
      for i, line in toSeq(lines(f)):
        for kw in ["proc", "func", "template", "macro", "iterator"]:
          if line.startsWith(kw & " nativeHits") or
             line.startsWith(kw & " `nativeHits`"):
            offenders.add f.extractFilename & ":" & $(i + 1)
    check offenders.len == 0
    if offenders.len > 0: checkpoint offenders.join(", ")

removeDir(pinTmp)
