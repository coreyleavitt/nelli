## RFC-0016 K5a, part 2 (section 8.3, "Three things derive from the profile").
## The cache key's build and host half is `buildSegment`, which iterates
## `fieldPairs` over `BuildSemantics` and `HostSemantics` under a versioned
## tag; `canonicalize(SymexSettings)` keys every settings field but the ones in
## the explicit neutral const. A host the build profile does not admit declines
## the run, named (`feHostUnadmitted`), and a finding renders the build that
## decided it. The goldens per run leg are in `tsymex_phase15_CR2_cachekey`.
import std/[unittest, strutils, options, sets]
import nelli
import nelli/symex
import nelli/smt/runtime
import nelli/smt/canonicalize
import nelli/smt/buildprofile
import nelli/smt/soundness
import nelli/coverage

# ---- generic "change this field" for the structural tests -------------------

proc bumped[T](x: T): T =
  when T is bool: not x
  elif T is set[CheckOption]: (if x == {}: {coField} else: {})
  elif T is set[DefectKind]: (if x == {}: {dkIndexDefect} else: {})
  elif T is set[ArithCheck]: (if x == {}: {acOverflow} else: {})
  elif T is enum: (if x == high(T): low(T) else: succ(x))
  elif T is SomeInteger: x + 1
  elif T is string: x & "x"
  else: {.error: "a field of a type the segment tests cannot change: " &
         $T & "; teach `bumped` (and check the field is keyed)".}

proc countFields[T: object](x: T): int =
  for _, v in x.fieldPairs:
    when v is object: result += countFields(v)
    else: inc result

proc bumpNth[T: object](x: var T; n: var int; prefix: string;
                        path: var string) =
  {.push warning[Deprecated]: off.}
  for name, v in x.fieldPairs:
    when v is object:
      bumpNth(v, n, prefix & name & ".", path)
    else:
      if n == 0:
        v = bumped(v)
        path = prefix & name
      dec n
  {.pop.}

proc sutHost(v: int) =
  if v == 7: symexTarget("hit")

const host4 = HostSemantics(pcre: peInterp, pcreVersion: "8.45", pcreJit: false,
                            z3: z3v4_13_4, z3Full: "4.13.4.0")
const hostOld = HostSemantics(pcre: peInterp, pcreVersion: "8.45", pcreJit: false,
                              z3: z3Other, z3Full: "4.12.2.0")

suite "K5a-2: buildSegment, by fieldPairs":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 289

  test "the format is a versioned tag over name=value fields":
    let seg = buildSegment(buildSemantics, host4)
    check seg.startsWith(buildSegmentTag & "<build:checks=")
    check seg.endsWith(">")
    check "|host:pcre=peInterp;pcreVersion=\"8.45\";pcreJit=0;z3=4.13.4;" &
          "z3Full=\"4.13.4.0\">" in seg
    check seg.segmentValue("mm") == "orc"
    check seg.segmentValue("z3Full") == "\"4.13.4.0\""

  test "every field of both objects is in the text, by name":
    let seg = buildSegment(buildSemantics, host4)
    for name, _ in buildSemantics.fieldPairs: check (name & "=") in seg
    for name, _ in host4.fieldPairs: check (name & "=") in seg

  test "changing any one field of either object changes the segment":
    let h0 = host4
    let base = buildSegment(buildSemantics, h0)
    for i in 0 ..< countFields(buildSemantics):
      var b = buildSemantics
      var n = i
      var path = ""
      bumpNth(b, n, "", path)
      checkpoint "BuildSemantics." & path
      if b == buildSemantics: continue   # `opt` has one member: nothing to change
      check buildSegment(b, h0) != base
    for i in 0 ..< countFields(h0):
      var h = h0
      var n = i
      var path = ""
      bumpNth(h, n, "", path)
      checkpoint "HostSemantics." & path
      check buildSegment(buildSemantics, h) != base

  test "the PCRE builds the old key told apart still differ":
    # `pcre` maps 8.37 without the JIT and 8.45 to `peInterp`; the version and
    # the JIT flag keep their keys apart (`pcre-interp-8.37` vs `-8.45`).
    var a = host4
    var b = host4
    b.pcreVersion = "8.37"
    var c = host4
    c.pcreVersion = "8.37"; c.pcre = peJit837; c.pcreJit = true
    check a.pcre == b.pcre
    check buildSegment(buildSemantics, a) != buildSegment(buildSemantics, b)
    check buildSegment(buildSemantics, b) != buildSegment(buildSemantics, c)

  test "two unverified Z3 versions keep two keys":
    var a = hostOld
    var b = hostOld
    b.z3Full = "4.12.3.0"
    check a.z3 == b.z3
    check buildSegment(buildSemantics, a) != buildSegment(buildSemantics, b)

  test "a verdict read under another profile is a different key":
    let prog = SymexProgram(body: IRStmt(kind: isBlock))
    proc keyFor(b: BuildSemantics; h: HostSemantics): string =
      symexCacheKey(prog, tIndexError(), defaultSymexSettings(), "z", "n",
                    "w", "r", replayMode = "fork",
                    buildSeg = buildSegment(b, h))
    let k0 = keyFor(buildSemantics, host4)
    check keyFor(buildSemantics, host4) == k0
    var other = buildSemantics
    other.mm = mmArc
    check keyFor(other, host4) != k0
    check keyFor(buildSemantics, hostOld) != k0
    # the hand-written `|z3=`, `|pcre=` and `|bf=` pieces are gone
    check symexCacheKey(prog, tIndexError(), defaultSymexSettings(), "z1", "n",
                        "w", "r", replayMode = "fork") !=
          symexCacheKey(prog, tIndexError(), defaultSymexSettings(), "z2", "n",
                        "w", "r", replayMode = "fork")

suite "K5a-2: SymexSettings is keyed by fieldPairs":
  test "the neutral const is exactly the two fields the hand list omitted":
    check symexSettingsNeutral.toHashSet ==
          ["acceptUnknownAsCovered", "budget.maxInstantiationsPerProc"].toHashSet

  test "every field is keyed unless named neutral; a neutral one is not":
    # A new field is classified here by what it does to the key: if it is not
    # named neutral and does not change `canonicalize`, this fails; the
    # `bumped` above refuses (at compile time) a field of a type it cannot
    # change, so a field cannot slip past unmentioned.
    let s0 = defaultSymexSettings()
    let base = canonicalize(s0)
    var seen = 0
    for i in 0 ..< countFields(s0):
      var s = s0
      var n = i
      var path = ""
      bumpNth(s, n, "", path)
      checkpoint "SymexSettings." & path
      if path in symexSettingsNeutral: check canonicalize(s) == base
      else: check canonicalize(s) != base
      inc seen
    check seen > 15

suite "K5a-2: a host the profile does not admit declines the run":
  teardown: clearHostOverride()

  test "admitHost names the field and the value":
    let r = admitHost(hostOld)
    check r.isSome
    check r.get.field == bfZ3
    check r.get.reason == "z3 4.12.2 is not a verified Z3 (4.13.4, 5.1)"
    # this process's own host is admitted (cpp under Z3 4.13.4 has no row)
    check admitHost(readHost(z3FullVersion())).isNone
    when not defined(cpp): check admitHost(host4).isNone

  test "symexFind: sxUnknown, feHostUnadmitted, no raise":
    overrideHostForTest(hostOld)
    let r = symexFind(sutHost, tLabel("hit"))
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == feHostUnadmitted:
        named = true
        check "z3 4.12.2 is not a verified Z3 (4.13.4, 5.1)" in e.msg
        check "z3" in e.msg
    check named
    check classOf(feHostUnadmitted) == dcNoAnswer
    check not trusted(r)

  test "the same call on a verified host runs":
    overrideHostForTest(readHost(z3FullVersion()))
    let r = symexFind(sutHost, tLabel("hit"))
    check r.status == sxSat
    for e in r.errors: check e.kind != feHostUnadmitted

  test "symexFindAllWitnesses: an sfUnknown finding carrying the refusal":
    overrideHostForTest(hostOld)
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(sutHost, db)
    check fs.len >= 1
    for f in fs:
      if f.targetDesc == "label(\"hit\")":
        check f.status == sfUnknown
        var kinds: seq[string]
        for g in f.gaps: kinds.add g.kind
        check "feHostUnadmitted" in kinds

  test "concolicCollect: the refusal rides parseErrors":
    overrideHostForTest(hostOld)
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(sutHost, trace, bindings)
    var named = false
    for e in r.parseErrors:
      if e.kind == feHostUnadmitted: named = true
    check named
    check r.branchTrace.len == 0

  test "the host is read once: a run after the seam is cleared reads the process's":
    overrideHostForTest(hostOld)
    check hostAdmission().isSome
    clearHostOverride()
    check hostAdmission() == hostAdmission()

suite "K5a-2: the verdict carries the build":
  test "a finding's soundness has the segment and the row":
    let r = symexFind(sutHost, tLabel("hit"))
    check r.soundness.buildSegment.startsWith(buildSegmentTag & "<build:")
    check r.soundness.buildSegment ==
          buildSegment(buildSemantics, readHost(z3FullVersion()))
    let row = rowOf(buildSemantics, readHost(z3FullVersion()), buildProvenance)
    check row.isSome
    check r.soundness.buildRow == $row.get

  test "a finding renders 'decided on c/orc/goto/64-bit, panics off'":
    let db = inMemoryDatabase()
    var f: SymexFinding
    for x in symexFindAllWitnesses(sutHost, db):
      if x.targetDesc == "label(\"hit\")": f = x
    check f.soundness.buildSegment.len > 0
    let line = buildSummary(f.soundness)
    let be = when defined(cpp): "cpp" else: "c"
    let ex = when defined(cpp): "cpp" else: "goto"
    check line.startsWith("decided on " & be & "/orc/" & ex & "/64-bit, panics ")
    check "(row " in line
    let rep = Report[int](outcome: otPassed, examples: 1, symexFindings: @[f])
    check line in renderReport(rep, ofText)
    check "buildSegment" in renderReport(rep, ofJson)

  test "a cache hit is stamped too":
    let db = inMemoryDatabase()
    discard symexFindAllWitnesses(sutHost, db)
    for f in symexFindAllWitnesses(sutHost, db):
      if f.targetDesc == "label(\"hit\")":
        check f.fromCache
        check f.soundness.buildSegment ==
              buildSegment(buildSemantics, readHost(z3FullVersion()))
