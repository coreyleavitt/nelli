## RFC-0016 K8b (INT-56) -- the axis figure, its floor and K1's reading of
## the axis records (section 12 item 4, first clause), over fixtures: no walk
## runs here. The axis suites (`tsymex_0016_k8b_axes_*`, `axisFiles`) write
## the real records; K1 (`tsymex_0016_universe`) reads them.
import std/[unittest, os, strutils, sets, sequtils]
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8b_axes
import ./s0016_k8a_gen

proc rec(axis: AxisScope; keys: seq[string]; outcome = "exact";
         row = "linux-c"; file = ""): ExercisedRecord =
  var cs: seq[CellKey]
  for k in keys: cs.add CellKey(scope: axis, key: k)
  ExercisedRecord(testFile: (if file.len > 0: file else: axisFiles[axis][0]),
                  family: axis, outcome: outcome, cells: cs, row: row,
                  variant: "orig")

proc allFiles(axis: AxisScope; keys: seq[string]; row = "linux-c"):
    seq[ExercisedRecord] =
  for f in axisFiles[axis]: result.add rec(axis, keys, row = row, file = f)

suite "K8b axes: the fragments and the denominator":
  test "every fragment names an exact row of its axis, once":
    let p = snippetProblems()
    checkpoint p.join("\n")
    check p.len == 0

  test "the denominator is the axis table's admitted rows":
    for a in AxisScope:
      check modelledRows(a).len > 0
    check "AddI" in modelledRows(axMagic)
    check "mm=arc" in modelledRows(axBuild)

  test "every axis with fragments has suites, and every suite is registered":
    let nimble = readFile(currentSourcePath().parentDir / ".." / "nelli.nimble")
    for a in AxisScope:
      check (axisSnippets[a].len > 0) == (axisFiles[a].len > 0)
      for f in axisFiles[a]:
        check fileExists(currentSourcePath().parentDir / f)
        check ("\"" & f.changeFileExt("") & "\"") in nimble

  test "the axis stream covers every fragment, rows once per lap":
    for a in AxisScope:
      if axisSnippets[a].len == 0: continue
      let per = 6
      let n = (axisSnippets[a].len + per - 1) div per
      var seen: HashSet[string]
      for p in genAxis(a, 20261117, n, per):
        check p.axis == a
        for k in p.rows: seen.incl k
      check seen.len == axisSnippets[a].len
      check genAxis(a, 3, 2, per) == genAxis(a, 3, 4, per)[0 ..< 2]
      check genAxis(a, 3, 2, per, 2) == genAxis(a, 3, 4, per)[2 ..< 4]

  test "a raising fragment's program takes no reordering relation":
    let ps = genAxis(axDefinedness, 1, 3, 2)
    for p in ps:
      check axisRaises(p) == (twComm notin applicable(p))

  test "a one-row program takes no reordering relation (reversing is a no-op)":
    for p in genAxis(axMagic, 1, 3, 1):
      check twComm notin applicable(p)
      for tw in applicable(p):
        check render(p, "g", tw) != render(p, "g", twNone)

suite "K8b axes: the figure":
  test "a row is exercised only by an exact record":
    let f = axisFigure(@[rec(axMagic, @["AddI", "SubI"]),
                         rec(axMagic, @["MulI"], "declined"),
                         rec(axMagic, @["DivI"], "disagree")])
    check f[axMagic].exercised == 2
    check f[axMagic].total == modelledRows(axMagic).len
    check f[axPragma].exercised == 0

  test "the figure is per build row":
    let rs = @[rec(axMagic, @["AddI"]), rec(axMagic, @["SubI"], row = "msvc")]
    check axisFigure(rs, "linux-c")[axMagic].exercised == 1
    check axisFigure(rs)[axMagic].exercised == 2

  test "family records are not axis records, and the reverse":
    let fam = ExercisedRecord(testFile: "x.nim", family: faGeneric,
                              outcome: "exact", row: "linux-c",
                              cells: cellsOf(faGeneric, @[0, 0, 0]))
    check axisFigure(@[fam])[axMagic].exercised == 0
    check exercisedProblems(@[rec(axMagic, @["AddI"])]).len == 0
    check axisRecordProblems(@[fam]).len == 0

suite "K8b axes: the floor and K1's join":
  let floorNow = loadAxisFloor(currentSourcePath().parentDir / ".." /
                               axisFloorFile)

  test "the committed floor parses, names every axis, and matches the tables":
    for a in AxisScope:
      check floorNow[a].total == modelledRows(a).len
      check floorNow[a].exercised <= floorNow[a].total
      if axisFiles[a].len == 0: check floorNow[a].exercised == 0
    check parseAxisFloor(renderAxisFloor(floorNow)) == floorNow

  test "RED: a malformed or partial floor is rejected":
    expect ValueError: discard parseAxisFloor("magic\t1\n")
    expect ValueError: discard parseAxisFloor("magic\t1\t2\n")
    expect ValueError: discard parseAxisFloor("nosuch\t1\t2\n")

  test "RED: an axis below its floor fails, naming the unexercised rows":
    var floor = floorNow
    for a in AxisScope: floor[a].exercised = 0
    floor[axMagic].exercised = 2
    let one = allFiles(axMagic, @["AddI"])
    let p = axisJoinProblems(one, "linux-c", floor)
    check p.len == 1
    check "magic" in p[0] and "SubI" in p[0]
    check axisJoinProblems(allFiles(axMagic, @["AddI", "SubI"]), "linux-c",
                           floor).len == 0
    # another row's records do not count on this leg
    check axisJoinProblems(allFiles(axMagic, @["AddI", "SubI"], "msvc"),
                           "linux-c", floor).len == 0

  test "RED: an axis with some of its suites' records fails unless partial":
    var floor = floorNow
    for a in AxisScope: floor[a].exercised = 0
    let half = @[rec(axMagic, @["AddI"], file = axisFiles[axMagic][0])]
    let p = axisJoinProblems(half, "linux-c", floor)
    check p.len == 1 and axisFiles[axMagic][1] in p[0]
    check axisJoinProblems(half, "linux-c", floor, partial = true).len == 0

  test "RED: a changed exact-row count must be re-measured":
    var floor = floorNow
    floor[axStdlibBody].total += 1
    check axisJoinProblems(@[], "", floor).len == 1

  test "RED: a record naming no exact row of its axis fails":
    var floor = floorNow
    for a in AxisScope: floor[a].exercised = 0
    let bad = rec(axMagic, @["NoSuchMagic"])
    check axisJoinProblems(@[bad], "", floor).anyIt("NoSuchMagic" in it)
