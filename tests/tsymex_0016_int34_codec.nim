## RFC-0016 INT-34 C1: the symex cache's record encodings (`symex_codec`),
## read without a database. Every encode reads back through its inverse, for
## every value each field can take; the bytes a record carries are pinned, so
## a change to them is a format change (a new encoding version), never a
## silent one; and a decode refuses what its encode never writes.
##
## Z3-free: `symex_codec` does no I/O and names no solver.
import std/[unittest, options, tables, sets]
import nelli/choice
import nelli/smt/[types, symex_codec]
import nelli/engine/types
from nelli/smt/admission import cellKey, axConstruct
import ./s8cu_helpers

var held = true   # cleared by any test of this file that fails

template trackFailure() =
  teardown:
    if testStatusIMPL != TestStatus.OK: held = false

const ubSpan = ord(high(UbKind)) - ord(low(UbKind))

proc subsets[E: enum](): seq[set[E]] =
  ## Every subset of `E`'s members.
  result = @[default(set[E])]
  for e in E:
    for i in 0 ..< result.len:
      result.add(result[i] + {e})

suite "INT-34 C1: Soundness":
  trackFailure()
  test "every soundness round-trips":
    var undef: seq[set[UbOrdinal]] = @[{}]
    for o in 0 .. ubSpan: undef.add {UbOrdinal(o)}
    var all: set[UbOrdinal]
    for o in 0 .. ubSpan: all.incl UbOrdinal(o)
    undef.add all
    var n = 0
    for p in subsets[SoundnessChannel]():
      for r in subsets[SoundnessChannel]():
        for rs in ReplayStatus:
          for unsafe in [false, true]:
            for d in subsets[RunDependence]():
              for u in undef:
                let s = Soundness(pathTaint: p, runTaint: r, replay: rs,
                                  witnessUnsafe: unsafe, witnessUndefined: u,
                                  runDependence: d)
                let back = decodeSoundness(encodeSoundness(s))
                check back.isSome and back.get == s
                let viaMeta = storedSoundness(soundnessMeta(s))
                check viaMeta.isSome and viaMeta.get == s
                inc n
    check n > 1000

  test "the encoding's bytes":
    check encodeSoundness(Soundness()) == "4:0:0:0:0:0"
    check encodeSoundness(Soundness(pathTaint: {scSpurious},
                                    runTaint: {scSpurious, scIncomplete},
                                    replay: rsConfirmed, witnessUnsafe: true,
                                    witnessUndefined: {UbOrdinal(0), UbOrdinal(3)},
                                    runDependence: {rdReplay})) ==
      "4:1:3:2:1:9:4"
    check soundnessMeta(Soundness()) == {"soundness": "4:0:0:0:0:0"}.toTable

  test "a decode refuses what no encode writes":
    for v in ["", "4", "3:0:0:0:0", "5:0:0:0:0:0", "4:0:0:0:0:00",
              "4:0:0:0:0:01", "4:4:0:0:0:0", "4:0:0:5:0:0", "4:0:0:0:2:0",
              "4:0:0:0:0:0:0", "4:0:0:0:0:0:8", "4:0:0:0:0:x",
              "4:10:0:0:0:0", "4:0:0:0:0:0:1:1", "4:0:0:0:0:" & $(1 shl 30)]:
      check decodeSoundness(v).isNone
    check storedSoundness(initTable[string, string]()).isNone

suite "INT-34 C1: gaps":
  trackFailure()
  test "every gap kind and class round-trips":
    var gaps: seq[FindingGap]
    for c in DegradeClass:
      for k in SymexErrorKind:
        gaps.add FindingGap(class: c, kind: k, msg: $c & "/" & $k & ":x")
    let back = storedGaps(gapsMeta(gaps))
    check back.isSome and back.get == gaps
    let none0 = storedGaps(gapsMeta(@[]))
    check none0.isSome and none0.get.len == 0

  test "the encoding's bytes":
    check gapsMeta(@[FindingGap(class: DegradeClass(1), kind: SymexErrorKind(0),
                                msg: "m")]) ==
      {"gapsv": "1", "gapsn": "1", "gapsc0": "1",
       "gapsk0": $SymexErrorKind(0), "gapsm0": "m"}.toTable

  test "absent gaps are none recorded; malformed gaps are a miss":
    let absent = storedGaps(initTable[string, string]())
    check absent.isSome and absent.get.len == 0
    var m = gapsMeta(@[FindingGap(class: DegradeClass(0),
                                  kind: SymexErrorKind(0), msg: "m")])
    var bad = m; bad["gapsv"] = "2"
    check storedGaps(bad).isNone
    bad = m; bad["gapsn"] = "x"
    check storedGaps(bad).isNone
    bad = m; bad["gapsn"] = "2"
    check storedGaps(bad).isNone
    bad = m; bad["gapsk0"] = "noSuchKind"
    check storedGaps(bad).isNone
    bad = m; bad["gapsc0"] = $(ord(high(DegradeClass)) + 1)
    check storedGaps(bad).isNone

suite "INT-34 C1: the notes record":
  trackFailure()
  test "every hint kind and severity round-trips through the head":
    var hints: seq[FindingHint]
    for k in SymexErrorKind:
      for s in SymexErrorSeverity:
        hints.add FindingHint(kind: k, severity: s, msg: $k & $s)
    let head = notesHeadMeta(hints, 3, 2)
    let n = storedNotesCounts(head)
    check n.isSome
    check n.get.hints == hints.len and n.get.diagnostics == 3 and
          n.get.undefined == 2
    check storedHints(head, n.get.hints) == hints

  test "the head's bytes":
    check notesHeadMeta(@[FindingHint(kind: SymexErrorKind(0),
                                      severity: sevHint, msg: "h")], 1, 0) ==
      {"notesv": "1", "hintn": "1", "hintk0": $SymexErrorKind(0),
       "hints0": "sevHint", "hintm0": "h", "diagn": "1",
       "undefn": "0"}.toTable

  test "a head not in this encoding has no counts":
    check storedNotesCounts({notesVersionMetaKey: "-"}.toTable).isNone
    check storedNotesCounts(initTable[string, string]()).isNone
    var h = notesHeadMeta(@[], 0, 0)
    h["diagn"] = "x"
    check storedNotesCounts(h).isNone
    h = notesHeadMeta(@[], 1, 0)
    h.del "undefn"   # a head written before K10a-target
    let n = storedNotesCounts(h)
    check n.isSome and n.get.undefined == 0 and n.get.diagnostics == 1

  test "an unknown hint ends the list":
    var h = notesHeadMeta(@[FindingHint(kind: SymexErrorKind(0),
                                        severity: sevHint, msg: "a"),
                            FindingHint(kind: SymexErrorKind(0),
                                        severity: sevWarning, msg: "b")], 0, 0)
    h["hints1"] = "sevNoSuch"
    check storedHints(h, 2).len == 1

  test "every diagnostic round-trips":
    let w = @[bytesChoice(@[1'u8, 2], 0, 2)]
    for def in [false, true]:
      for unsafe in [false, true]:
        let d = FindingDiagnostic(raisedTypeId: "ValueError", isDefect: def,
                                  raisedMsg: "boom", witnessChoices: w,
                                  witnessUnsafe: unsafe)
        let back = storedDiagnostic(diagnosticMeta(d), w)
        check back.isSome and back.get == d
    check diagnosticMeta(FindingDiagnostic(raisedTypeId: "E", isDefect: true,
                                           raisedMsg: "m")) ==
      {"tid": "E", "def": "1", "msg": "m", "wx": "0"}.toTable
    check storedDiagnostic(initTable[string, string](), w).isNone

  test "every undefined kind round-trips":
    let w = @[bytesChoice(@[7'u8], 0, 1)]
    for o in 0 .. ubSpan:
      let u = FindingUndefined(kind: $UbKind(ord(low(UbKind)) + o),
                               site: "s" & $o, witnessChoices: w)
      let back = storedUndefined(undefinedMeta(u), w)
      check back.isSome and back.get == u
    check undefinedMeta(FindingUndefined(kind: "k", site: "s")) ==
      {"kind": "k", "site": "s"}.toTable
    check storedUndefined(initTable[string, string](), w).isNone

suite "INT-34 C1: verdict and raised metadata":
  trackFailure()
  test "a verdict carries its soundness and gaps":
    let s = Soundness(pathTaint: {scIncomplete}, replay: rsNotNeeded)
    let g = @[FindingGap(class: DegradeClass(0), kind: SymexErrorKind(0),
                         msg: "m")]
    let m = verdictMeta(s, g)
    check storedSoundness(m).get == s
    check storedGaps(m).get == g
    var keys: HashSet[string]
    for k in m.keys: keys.incl k
    check keys == toHashSet(["soundness", "gapsv", "gapsn", "gapsc0",
                             "gapsk0", "gapsm0"])

  test "a raised sentinel carries its defect-ness":
    for def in [false, true]:
      let m = raisedMeta(Soundness(), @[], def)
      check storedRaisedDefect(m) == def
      check m["rdef"] == (if def: "1" else: "0")
      check storedSoundness(m).get == Soundness()
    check not storedRaisedDefect(initTable[string, string]())

suite "INT-34 C1: the pin":
  test "the verdict cache's records round-trip":
    pinNever(cellKey(axConstruct, "cache/record/codec"), held,
      "every soundness, gap, hint, diagnostic, undefined kind, verdict and " &
      "raised sentinel the verdict cache stores round-trips through " &
      "`symex_codec`'s encoding, and a decode refuses what no encode writes, " &
      "a malformed record being a miss")
