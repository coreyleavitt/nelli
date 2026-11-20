## RFC-0016 K8b -- the cells-exercised record, the pairwise figure and its
## floor (§8.2, §12 item 4), over fixtures: no walk runs here. The family
## suites (`tsymex_0016_k8b_<family>_a`/`_b`) write the real records; K1
## (`tsymex_0016_universe`) reads them.
import std/[unittest, os, strutils, sets, json, options]
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8b_pairs

let tmp = getTempDir() / ("k8b_pairs_" & $getCurrentProcessId())
removeDir(tmp)
createDir(tmp)

proc rec(fam: FamilyScope; choice: seq[int]; outcome = "exact";
         row = "linux-c"): ExercisedRecord =
  ExercisedRecord(testFile: "fixture.nim", family: fam, outcome: outcome,
                  cells: cellsOf(fam, choice), row: row, variant: "orig")

suite "K8b: the pair universe":
  test "each family's universe is every cross-dimension value pair":
    check pairUniverse(faCallShape).len == 5*3 + 5*5 + 3*5
    check pairUniverse(faExnMemory).len == 5*3 + 5*3 + 5*2 + 3*3 + 3*2 + 3*2
    check pairUniverse(faGeneric).len == 5*4 + 5*3 + 4*3

  test "every family cell renders and parses back to itself":
    for fam in FamilyScope:
      for c in familyCells(fam):
        let k = parseCellKey(c)
        check k.isSome
        check k.get.scope == fam
        check render(k.get) == c
    check render(valueCell(faGeneric, "uninst", "sibling")) ==
      "family:generic:k8b/uninst/sibling"

  test "the covering stream is deterministic and prefix-stable":
    for fam in FamilyScope:
      check coverChoices(fam, 3, 6) == coverChoices(fam, 3, 10)[0 ..< 6]
      check coverChoices(fam, 3, 6) != coverChoices(fam, 4, 6)

  test "the covering stream covers new pairs while any are left":
    for fam in FamilyScope:
      var seen: HashSet[string]
      let u = pairUniverse(fam)
      for c in coverChoices(fam, 20261117, 40):
        let fig = pairwiseFigure(@[rec(fam, c)])
        check fig[fam].covered == famDims[fam].len * (famDims[fam].len - 1) div 2
        var grew = false
        let cs = cellsOf(fam, c)
        for i in 0 ..< cs.len:
          for j in i + 1 ..< cs.len:
            let a = render(cs[i])
            let b = render(cs[j])
            let k = if a < b: a & "|" & b else: b & "|" & a
            if k notin seen: grew = true
            seen.incl k
        check grew or seen.len == u.len
      check seen.len == u.len   # 40 programs cover every pair on paper

suite "K8b: the pairwise figure":
  test "a pair is covered only by an exact record":
    let f = pairwiseFigure(@[rec(faCallShape, @[0, 0, 0]),
                             rec(faCallShape, @[1, 1, 1], "declined"),
                             rec(faCallShape, @[2, 2, 2], "disagree")])
    check f[faCallShape].covered == 3
    check f[faCallShape].total == 55
    check f[faGeneric].covered == 0

  test "records overlapping on a pair count it once":
    let f = pairwiseFigure(@[rec(faGeneric, @[0, 0, 0]),
                             rec(faGeneric, @[0, 0, 1])])
    check f[faGeneric].covered == 3 + 2

  test "a row filter counts that row's records only":
    let rs = @[rec(faExnMemory, @[0, 0, 0, 0]),
               rec(faExnMemory, @[1, 1, 1, 1], row = "msvc")]
    check pairwiseFigure(rs)[faExnMemory].covered == 12
    check pairwiseFigure(rs, "msvc")[faExnMemory].covered == 6

  test "RED: a cell that is no value of its family is a problem":
    var r = rec(faCallShape, @[0, 0, 0])
    check exercisedProblems(@[r]).len == 0
    r.cells[0] = CellKey(scope: faCallShape, key: "k8b/callee/macro")
    let p = exercisedProblems(@[r])
    check p.len == 1
    check "k8b/callee/macro" in p[0]
    var q = rec(faGeneric, @[0, 0, 0])
    q.outcome = "maybe"
    check exercisedProblems(@[q]).len == 1

suite "K8b: the cells-exercised record":
  test "it round-trips, and shares a file with pin records without confusion":
    let d = tmp / "mixed"
    createDir(d)
    let r = rec(faExnMemory, @[4, 2, 1, 0])
    writeExercisedTo(d, @[r])
    putEnv("NELLI_PIN_DIR", d)
    writePinRecord(PinRecord(testFile: "fixture.nim", entry: "symexFind",
      cell: valueCell(faExnMemory, "mem", "local"), target: "label hit",
      verdict: pvExact, walker: "sxSat"))
    var pins = 0
    for p in pinRecords(d): inc pins
    check pins == 1
    let back = loadExercised(d)
    check back.len == 1
    check back[0].cells == r.cells
    check back[0].family == faExnMemory
    check back[0].outcome == "exact"
    check back[0].row.len > 0 or pinBuildRow().len == 0
    check back[0].date.len > 0

  test "RED: an unparsable cell or an unknown family raises":
    var n = parseJson(exercisedLine(rec(faGeneric, @[0, 0, 0])))
    n["cells"].elems[0] = %"nosuchscope:x"
    expect ValueError: discard exercisedFromJson(n)
    var m = parseJson(exercisedLine(rec(faGeneric, @[0, 0, 0])))
    m["family"] = %"family:nosuch"
    expect ValueError: discard exercisedFromJson(m)

suite "K8b: the floor":
  test "the committed floor parses, and its universes are the families'":
    let f = loadFloor()
    for fam in FamilyScope:
      check f[fam].total == pairUniverse(fam).len
      check f[fam].covered in 0 .. f[fam].total
    check parseFloor(renderFloor(f)) == f

  test "RED: a figure below the floor fails naming the family":
    var floor: PairFigure
    var fig: PairFigure
    for fam in FamilyScope:
      floor[fam] = FamFigure(covered: 10, total: pairUniverse(fam).len)
      fig[fam] = floor[fam]
    check floorProblems(fig, floor, {faCallShape .. faGeneric}).len == 0
    fig[faGeneric].covered = 9
    let p = floorProblems(fig, floor, {faCallShape .. faGeneric})
    check p.len == 1
    check "family:generic" in p[0] and "below the floor" in p[0]
    # a family that did not run is not judged
    check floorProblems(fig, floor, {faCallShape}).len == 0
    # above the floor passes, unless the run is full (the ratchet)
    fig[faGeneric].covered = 11
    check floorProblems(fig, floor, {faGeneric}).len == 0
    let up = floorProblems(fig, floor, {faGeneric}, ratchet = true)
    check up.len == 1 and "raise the floor to 11" in up[0]

  test "RED: a changed pair universe must be re-measured":
    var floor: PairFigure
    var fig: PairFigure
    floor[faCallShape] = FamFigure(covered: 1, total: 54)
    fig[faCallShape] = FamFigure(covered: 30, total: 55)
    let p = floorProblems(fig, floor, {faCallShape})
    check p.len == 1
    check "re-measure" in p[0]

  test "RED: a floor with a missing, unknown or duplicated family fails":
    expect ValueError: discard parseFloor("family:callshape\t1\t55\n")
    expect ValueError: discard parseFloor(
      "family:callshape\t1\t55\nfamily:exnmemory\t1\t61\nfamily:nosuch\t1\t1\n")
    expect ValueError: discard parseFloor(
      "family:callshape\t1\t55\nfamily:callshape\t1\t55\n" &
      "family:exnmemory\t1\t61\nfamily:generic\t1\t47\n")
    expect ValueError: discard parseFloor("family:callshape 1 55\n")

suite "K8b: a family split into halves is judged on their union":
  # A family's batch runs as two suites (`familyFiles`), each a slice of one
  # seeded stream (`k8bFirst`), so each fits the per-test time ceiling. The
  # floor is the family's figure over the union of its halves' records: a
  # pair one half covers and the other does not is covered.
  proc halfRec(fam: FamilyScope; half: int; choice: seq[int]): ExercisedRecord =
    result = rec(fam, choice)
    result.testFile = familyFiles[fam][half]

  proc withOthers(recs: seq[ExercisedRecord]; keep: FamilyScope;
                  row = "linux-c"): seq[ExercisedRecord] =
    ## `recs` plus a `declined` record from both halves of every OTHER family:
    ## each ran on the row and covered no pair, so a full run's "every family
    ## has records" check passes and the test judges only `keep`.
    result = recs
    for fam in FamilyScope:
      if fam == keep: continue
      for h in 0 .. 1:
        var r = halfRec(fam, h, newSeq[int](famDims[fam].len))
        r.outcome = "declined"
        r.row = row
        result.add r

  test "every family names its halves, each a suite on disk":
    for fam in FamilyScope:
      check familyFiles[fam].len == 2
      for f in familyFiles[fam]:
        check f.startsWith("tsymex_0016_k8b_")
        check fileExists(currentSourcePath().parentDir / f)

  test "the union of the halves meets a floor neither half meets alone":
    var floor: PairFigure
    for fam in FamilyScope: floor[fam] = FamFigure(total: pairUniverse(fam).len)
    floor[faGeneric].covered = 6
    let a = halfRec(faGeneric, 0, @[0, 0, 0])
    let b = halfRec(faGeneric, 1, @[1, 1, 1])
    check exercisedJoinProblems(withOthers(@[a, b], faGeneric), "linux-c",
                                floor).len == 0
    check pairwiseFigure(@[a])[faGeneric].covered == 3
    check pairwiseFigure(@[b])[faGeneric].covered == 3

  test "RED: a family with a half missing fails naming the half, unless partial":
    var floor: PairFigure
    for fam in FamilyScope: floor[fam] = FamFigure(total: pairUniverse(fam).len)
    let a = halfRec(faCallShape, 0, @[0, 0, 0])
    let p = exercisedJoinProblems(withOthers(@[a], faCallShape), "linux-c", floor)
    check p.len == 1
    check familyFiles[faCallShape][1] in p[0]
    # a narrowed run (a slice of the suites) evidences no union: not judged
    check exercisedJoinProblems(@[a], "linux-c", floor, partial = true).len == 0

  test "RED: a full run fails a family whose suites wrote nothing on the row":
    var floor: PairFigure
    for fam in FamilyScope: floor[fam] = FamFigure(total: pairUniverse(fam).len)
    let recs = withOthers(@[], faGeneric)
    let p = exercisedJoinProblems(recs, "linux-c", floor)
    check p.len == 1
    check "family:generic" in p[0] and "no cells-exercised records" in p[0]
    # records of another row do not count on this leg
    check exercisedJoinProblems(withOthers(@[], faGeneric, "msvc"), "linux-c",
                                floor).len == 3   # one per family
    # a narrowed run does not judge it
    check exercisedJoinProblems(recs, "linux-c", floor, partial = true).len == 0

  test "RED: a figure above its floor fails a full run, naming the new floor":
    var floor: PairFigure
    for fam in FamilyScope: floor[fam] = FamFigure(total: pairUniverse(fam).len)
    floor[faGeneric].covered = 5
    let a = halfRec(faGeneric, 0, @[0, 0, 0])
    let b = halfRec(faGeneric, 1, @[1, 1, 1])
    let recs = withOthers(@[a, b], faGeneric)
    let p = exercisedJoinProblems(recs, "linux-c", floor)
    check p.len == 1
    check "above the floor" in p[0] and "raise the floor to 6" in p[0]
    check exercisedJoinProblems(recs, "linux-c", floor, partial = true).len == 0

  test "RED: a partial run still judges a family whose halves both ran":
    var floor: PairFigure
    for fam in FamilyScope: floor[fam] = FamFigure(total: pairUniverse(fam).len)
    floor[faGeneric].covered = 7
    let a = halfRec(faGeneric, 0, @[0, 0, 0])
    let b = halfRec(faGeneric, 1, @[1, 1, 1])
    let p = exercisedJoinProblems(@[a, b], "linux-c", floor, partial = true)
    check p.len == 1
    check "below the floor" in p[0]

removeDir(tmp)
