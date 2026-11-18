## RFC-0016 K8b (INT-56, §10 "Families from the axes", §12 item 4 first
## clause): the axis figure, "every exact row exercised on its build rows",
## as a number per admission axis.
##
## THE DENOMINATOR is the axis table itself: every row `cells(axis)` reports
## admitted (`modelledRows`), read from the same `const` tables the walker
## admits through. Nothing here lists rows by hand, so a row that becomes
## exact enters the denominator the day it lands.
##
## THE NUMERATOR. An axis suite (`axisFiles`) runs generated programs, each
## packing several rows' fragments (`tests/s0016_k8b_snippets.nim`), through
## `symexFind` and the native differential, and writes one cells-exercised
## record per run (the program under one variant) whose `family` is the axis
## and whose cells are the rows. A row is EXERCISED on a build row when an
## `exact` record of that row names it: the walker reached a trusted verdict
## and the native run on the same build reproduced it. A declined or
## disagreeing run exercises nothing. The figure is per build row because a
## record carries its row (`pinBuildRow`), and K1 judges each leg on its own.
##
## THE FLOOR. `tests/0016-axis-rows.floor` holds each axis's exercised count
## and its exact-row count. As with the pairwise floor it only rises, and a
## changed denominator must be re-measured. An axis is judged on a leg only
## when every one of its suites ran there (a partial run does not judge it).
import std/[strutils, sets, os, options]
import nelli/smt/admission
import nelli/smt/magic_rows
import nelli/smt/typeaxes
import nelli/smt/pragmaaxes
import nelli/smt/readonlyaxes
import nelli/smt/stdlib_rows
import nelli/smt/definedness
import nelli/smt/buildprofile
import nelli/smt/pcre_engine
import ./s8cu_helpers
import ./s0016_k8b_snippets

export s0016_k8b_snippets

const axisFloorFile* = "tests" / "0016-axis-rows.floor"

const axisFiles*: array[AxisScope, seq[string]] = [
  axTypeClass: @["tsymex_0016_k8b_axes_types.nim"],
  axTypeOp: @["tsymex_0016_k8b_axes_types.nim"],
  axPragma: @["tsymex_0016_k8b_axes_pragma.nim"],
  axMagic: @["tsymex_0016_k8b_axes_magic_a.nim",
             "tsymex_0016_k8b_axes_magic_b.nim"],
  axStdlibBody: @["tsymex_0016_k8b_axes_pragma.nim"],
  axBuild: @[],
  axReadOnly: @[],
  axDefinedness: @["tsymex_0016_k8b_axes_defined.nim"]]
  ## The suites that run each axis. An axis with no suite is not generated:
  ## its figure is 0 over its exact rows, judged against a floor of 0.

proc modelledRows*(axis: AxisScope): seq[string] =
  ## Every row of the axis's table that is admitted at some site.
  template take(t: untyped) =
    for c in t.cells:
      if c.admitted: result.add c.cell.key
  case axis
  of axTypeClass: take(typeClassTable)
  of axTypeOp: take(typeOpTable)
  of axPragma: take(pragmaAxis)
  of axMagic: take(magicAxis)
  of axStdlibBody: take(stdlibAxis)
  of axBuild:
    take(buildCells)
    take(pcreLibs)
  of axReadOnly: take(readOnlyAxis)
  of axDefinedness: take(definednessTable)

proc snippetProblems*(): seq[string] =
  ## A fragment whose key is no exact row of its axis (a typo, or a row that
  ## left `exact`), or two fragments for one row.
  for axis in AxisScope:
    let rows = modelledRows(axis).toHashSet
    var seen: HashSet[string]
    for s in axisSnippets[axis]:
      if s.key notin rows:
        result.add scopePrefix[axis] & ":" & s.key &
          " has a fragment but is no exact row of the axis"
      if s.key in seen:
        result.add scopePrefix[axis] & ":" & s.key & " has two fragments"
      seen.incl s.key

# --- the figure ------------------------------------------------------------------

type
  AxisFigure* = array[AxisScope, tuple[exercised, total: int]]

func isAxisRecord*(r: ExercisedRecord): bool =
  r.family in {axTypeClass .. axDefinedness}

proc axisRecordProblems*(recs: seq[ExercisedRecord]): seq[string] =
  ## An axis record naming a cell of another scope or no exact row.
  var rows: array[AxisScope, HashSet[string]]
  for a in AxisScope: rows[a] = modelledRows(a).toHashSet
  for r in recs:
    if not isAxisRecord(r): continue
    let ax = AxisScope(r.family)
    for c in r.cells:
      if c.scope != r.family or c.key notin rows[ax]:
        result.add "exercised record " & r.testFile & " prog=" & $r.progId &
          ": cell " & render(c) & " is no exact row of " & scopePrefix[ax]
    if r.outcome notin ["exact", "declined", "disagree"]:
      result.add "exercised record " & r.testFile & " prog=" & $r.progId &
        ": unknown outcome " & r.outcome

proc exercisedRows*(recs: seq[ExercisedRecord]; row = ""):
    array[AxisScope, HashSet[string]] =
  for r in recs:
    if not isAxisRecord(r) or r.outcome != "exact": continue
    if row.len > 0 and r.row != row: continue
    for c in r.cells: result[AxisScope(r.family)].incl c.key

proc axisFigure*(recs: seq[ExercisedRecord]; row = ""): AxisFigure =
  let ex = exercisedRows(recs, row)
  for a in AxisScope:
    let all = modelledRows(a).toHashSet
    result[a] = (exercised: card(ex[a] * all), total: all.len)

proc `$`*(f: AxisFigure): string =
  var e, t: int
  var parts: seq[string]
  for a in AxisScope:
    parts.add scopePrefix[a] & " " & $f[a].exercised & "/" & $f[a].total
    e += f[a].exercised
    t += f[a].total
  "axis rows exercised " & $e & "/" & $t & " (" & parts.join(", ") & ")"

proc unexercised*(recs: seq[ExercisedRecord]; axis: AxisScope;
                  row = ""): seq[string] =
  let ex = exercisedRows(recs, row)
  for k in modelledRows(axis):
    if k notin ex[axis]: result.add k

# --- the floor -------------------------------------------------------------------

proc parseAxisFloor*(text: string): AxisFigure =
  ## `<axis><TAB>exercised<TAB>exact rows` per line; `#` comments; every axis
  ## once.
  var seen: set[AxisScope]
  for raw in text.splitLines:
    let l = raw.strip
    if l.len == 0 or l.startsWith("#"): continue
    let fs = l.split('\t')
    if fs.len != 3:
      raise newException(ValueError, "axis floor: malformed line: " & l)
    var hit = false
    for a in AxisScope:
      if scopePrefix[a] == fs[0]:
        if a in seen:
          raise newException(ValueError, "axis floor: duplicate " & fs[0])
        seen.incl a
        result[a] = (exercised: parseInt(fs[1]), total: parseInt(fs[2]))
        hit = true
    if not hit:
      raise newException(ValueError, "axis floor: unknown axis " & fs[0])
  for a in AxisScope:
    if a notin seen:
      raise newException(ValueError, "axis floor: no line for " & scopePrefix[a])

proc renderAxisFloor*(f: AxisFigure): string =
  result = "# RFC-0016 K8b (section 12 item 4, first clause): exact rows\n" &
    "# exercised by the axis suites (s0016_k8b_axes `axisFiles`), per axis.\n" &
    "# axis<TAB>exercised<TAB>exact rows. K1 judges it per leg. It only rises;\n" &
    "# a changed exact-row count must be re-measured.\n"
  for a in AxisScope:
    result.add scopePrefix[a] & "\t" & $f[a].exercised & "\t" & $f[a].total & "\n"

proc loadAxisFloor*(path = axisFloorFile): AxisFigure =
  parseAxisFloor(readFile(path))

proc axisJoinProblems*(ex: seq[ExercisedRecord]; legRow: string;
                       floor: AxisFigure; partial = false): seq[string] =
  ## K1's reading of the axis records: every one well formed; every axis's
  ## exact-row count equal to the floor's (a changed denominator is
  ## re-measured); and each axis whose suites all ran on the leg at or above
  ## its floor. An axis with some of its suites' records and not all fails,
  ## naming the missing ones, unless the run is partial.
  result = axisRecordProblems(ex)
  var mine: seq[ExercisedRecord]
  for r in ex:
    if isAxisRecord(r) and (legRow.len == 0 or r.row == legRow): mine.add r
  let fig = axisFigure(mine)
  for a in AxisScope:
    if fig[a].total != floor[a].total:
      result.add scopePrefix[a] & ": the axis has " & $fig[a].total &
        " exact rows but the floor was measured over " & $floor[a].total &
        "; re-measure " & axisFloorFile
      continue
    if axisFiles[a].len == 0: continue
    var missing, present: seq[string]
    for f in axisFiles[a]:
      var ran = false
      for r in mine:
        if r.family == a and r.testFile == f: ran = true
      if ran: present.add f else: missing.add f
    if present.len == 0: continue
    if missing.len > 0:
      if not partial:
        result.add scopePrefix[a] & ": no cells-exercised records from " &
          missing.join(", ") & (if legRow.len > 0: " on row " & legRow else: "") &
          "; the axis figure is judged on all of " & axisFiles[a].join(", ")
      continue
    if fig[a].exercised < floor[a].exercised:
      result.add scopePrefix[a] & ": " & $fig[a].exercised & "/" &
        $fig[a].total & " exact rows exercised is below the floor " &
        $floor[a].exercised & " in " & axisFloorFile & "; unexercised: " &
        unexercised(mine, a).join(", ")
