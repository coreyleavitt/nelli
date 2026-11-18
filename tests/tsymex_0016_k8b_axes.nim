## RFC-0016 K8b (INT-56) -- the axis figure, its floor and K1's reading of
## the axis records (section 12 item 4, first clause), over fixtures: no walk
## runs here. The axis suites (`tsymex_0016_k8b_axes_*`, `axisFiles`) write
## the real records; K1 (`tsymex_0016_universe`) reads them.
import std/[unittest, os, strutils, sets, sequtils]
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8b_axes
import ./s0016_k8a_gen
import ./worklist_toml

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

  test "the axis stream covers every unblocked fragment, rows once per lap":
    for a in AxisScope:
      if axisSnippets[a].len == 0: continue
      let per = 6
      let n = (streamRows(a) + per - 1) div per
      var seen: HashSet[string]
      for p in genAxis(a, 20261117, n, per):
        check p.axis == a
        for k in p.rows: seen.incl k
      check seen.len == streamRows(a)
      for s in axisSnippets[a]:
        check (s.key in seen) == not isBlocked(a, s.key)
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

suite "K8b axes: the blocked rows (an open defect keeps a row out of the stream)":
  let wl = parseWorklist(readFile(currentSourcePath().parentDir / ".." /
    "docs" / "rfc-data" / "0016-worklist.toml"))

  proc fixture(id, state: string): Worklist =
    parseWorklist("[[row]]\nid = \"" & id & "\"\nstate = \"" & state & "\"\n")

  test "every blocked row has a fragment and names an open worklist row":
    let p = blockedProblems(wl)
    checkpoint p.join("\n")
    check p.len == 0
    check blockedRows.len > 0
    for b in blockedRows:
      check b.why.len > 0

  test "the INT-57 rows are blocked against their row":
    for (a, k, r) in [(axMagic, "IntToStr", "INT-57"),
                      (axTypeClass, "string", "INT-57"),
                      (axTypeOp, "letCursor/string", "INT-57")]:
      check isBlocked(a, k)
      check blockedRows.anyIt(it.axis == a and it.key == k and it.row == r)
    check not isBlocked(axMagic, "AddI")

  test "the INT-58, INT-59, INT-60 and INT-61 rows are readmitted (all closed)":
    for (a, k) in [(axStdlibBody, "math.round"), (axStdlibBody, "math.floor"),
                   (axMagic, "LengthArray"), (axStdlibBody, "math.trunc"),
                   (axMagic, "CharToStr"), (axMagic, "AppendStrCh")]:
      check not isBlocked(a, k)
      check streamSnippets(a).anyIt(it.key == k)

  test "RED: an entry whose row closed must be readmitted":
    let b = @[Blocked(axis: axMagic, key: "IntToStr", row: "INT-57", why: "x")]
    check blockedProblems(fixture("INT-57", "open"), b).len == 0
    for st in ["closed", "merged", "moved", "never"]:
      let p = blockedProblems(fixture("INT-57", st), b)
      check p.len == 1
      check "INT-57" in p[0] and "readmit" in p[0] and "IntToStr" in p[0]

  test "RED: an entry naming no worklist row, or no fragment, fails":
    let none = @[Blocked(axis: axMagic, key: "IntToStr", row: "INT-999", why: "x")]
    check blockedProblems(fixture("INT-57", "open"), none).len == 1
    let nofrag = @[Blocked(axis: axMagic, key: "NoSuch", row: "INT-57", why: "x")]
    check blockedProblems(fixture("INT-57", "open"), nofrag).len == 1
    let twice = @[Blocked(axis: axMagic, key: "IntToStr", row: "INT-57", why: "x"),
                  Blocked(axis: axMagic, key: "IntToStr", row: "INT-57", why: "y")]
    check blockedProblems(fixture("INT-57", "open"), twice).len == 1

  test "a blocked row is never exercised, so it counts against the figure":
    var all: seq[ExercisedRecord]
    for a in AxisScope:
      if axisSnippets[a].len == 0: continue
      for p in genAxis(a, 20261117, streamRows(a), 1):
        all.add rec(a, p.rows)
    let f = axisFigure(all)
    for a in AxisScope:
      if axisSnippets[a].len == 0: continue
      check f[a].exercised == streamRows(a)
      for b in blockedRows:
        if b.axis == a: check b.key in unexercised(all, a)

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
