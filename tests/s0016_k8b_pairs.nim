## RFC-0016 K8b (§8.2, §10, §12 item 4): the test-side pin families'
## dimensions, the cells a generated program exercises, the pairwise figure
## and its floor.
##
## FAMILIES. `faCallShape` (call site x callee shape), `faExnMemory`
## (exceptions x memory) and `faGeneric` (generic instantiation) have no
## single dispatch point in the walker (§8.1 "Not axes"), so each is a fuzzer
## family: a few DIMENSIONS, each a short list of values. A generated program
## picks one value per dimension (`tests/s0016_k8a_gen.nim`, its `fam`
## field); the value `v` of dimension `d` is the cell
## `family:<family>:k8b/<d>/<v>`.
##
## THE PAIRWISE FIGURE. A family's pair universe is every pair of values of
## two different dimensions (classic t = 2 combinatorial coverage). A pair is
## COVERED when some cells-exercised record of the family names both cells
## and its outcome is `exact`: the program reached a trusted verdict that the
## native run reproduced. A declined or disagreeing run covers nothing, so the
## figure measures the combinations the walker is exact on, not the ones the
## generator emitted. The figure is per family (`covered/total`) and summed.
##
## THE FLOOR. `tests/0016-pairwise.floor` holds each family's covered count
## and its universe size. The figure must not drop below the floor; a changed
## universe size fails until the floor is re-measured (a dimension added or
## removed changes what the figure means). The floor only rises (§12 item 4).
import std/[strutils, sets, random, os]
import nelli/smt/admission
import ./s8cu_helpers

type
  FamilyScope* = range[faCallShape .. faGeneric]
  FamDim* = object
    name*: string
    values*: seq[string]

const famDims*: array[FamilyScope, seq[FamDim]] = [
  faCallShape: @[
    FamDim(name: "callee",
           values: @["proc", "func", "template", "closure", "nested"]),
    FamDim(name: "mode", values: @["value", "varParam", "openArray"]),
    FamDim(name: "site",
           values: @["let", "arg", "cond", "arith", "assign"])],
  faExnMemory: @[
    FamDim(name: "mem", values: @["local", "seqElem", "objField",
                                  "refField", "arrayElem"]),
    FamDim(name: "writeAt", values: @["beforeRaise", "handler", "finally"]),
    FamDim(name: "handler",
           values: @["exceptType", "exceptBare", "finallyOnly"]),
    FamDim(name: "raise", values: @["direct", "viaCall"])],
  faGeneric: @[
    FamDim(name: "form", values: @["plain", "static", "whenIs", "nested",
                                   "procFormal"]),
    FamDim(name: "targ", values: @["int", "int16", "int64", "distinct"]),
    FamDim(name: "uninst", values: @["none", "sibling", "whenFalse"])]]

const floorFile* = "tests" / "0016-pairwise.floor"

func valueCell*(fam: FamilyScope; dim, value: string): CellKey =
  CellKey(scope: fam, key: "k8b/" & dim & "/" & value)

func cellsOf*(fam: FamilyScope; choice: seq[int]): seq[CellKey] =
  ## The cells a program with these dimension values exercises.
  doAssert choice.len == famDims[fam].len, "one value per dimension"
  for i, d in famDims[fam]:
    result.add valueCell(fam, d.name, d.values[choice[i]])

func familyCells*(fam: FamilyScope): HashSet[string] =
  for d in famDims[fam]:
    for v in d.values: result.incl render(valueCell(fam, d.name, v))

func pairKey(a, b: string): string =
  if a < b: a & "|" & b else: b & "|" & a

func pairUniverse*(fam: FamilyScope): HashSet[string] =
  let ds = famDims[fam]
  for i in 0 ..< ds.len:
    for j in i + 1 ..< ds.len:
      for v in ds[i].values:
        for w in ds[j].values:
          result.incl pairKey(render(valueCell(fam, ds[i].name, v)),
                              render(valueCell(fam, ds[j].name, w)))

func pairsOf(cells: seq[string]): seq[string] =
  for i in 0 ..< cells.len:
    for j in i + 1 ..< cells.len:
      result.add pairKey(cells[i], cells[j])

# --- generation: a greedy covering stream ----------------------------------

proc coverChoices*(fam: FamilyScope; seed, count: int): seq[seq[int]] =
  ## `count` dimension-value choices for the family, each the candidate (of
  ## 48 seeded draws) that covers the most pairs no earlier choice covered
  ## (ties: the first draw). Deterministic per seed and prefix-stable: choice
  ## `i` is the same for any `count > i`. About the universe's largest
  ## dimension product of two dimensions' sizes covers every pair.
  var r = initRand(seed)
  var seen: HashSet[string]
  let ds = famDims[fam]
  for _ in 0 ..< count:
    var best: seq[int]
    var bestNew = -1
    # draw 0 is built around the first uncovered pair (dimension order), so
    # a choice covers a new pair whenever one is left
    var anchor: seq[int]
    block find:
      for i in 0 ..< ds.len:
        for j in i + 1 ..< ds.len:
          for vi in 0 .. ds[i].values.high:
            for wj in 0 .. ds[j].values.high:
              let k = pairKey(render(valueCell(fam, ds[i].name, ds[i].values[vi])),
                              render(valueCell(fam, ds[j].name, ds[j].values[wj])))
              if k notin seen:
                anchor = newSeq[int](ds.len)
                for d in 0 ..< ds.len: anchor[d] = -1
                anchor[i] = vi
                anchor[j] = wj
                break find
    for draw in 0 ..< 48:
      var c: seq[int]
      for di, d in ds:
        let v = r.rand(d.values.high)
        c.add (if draw == 0 and anchor.len > 0 and anchor[di] >= 0: anchor[di]
               else: v)
      var n = 0
      var cs: seq[string]
      for k in cellsOf(fam, c): cs.add render(k)
      for p in pairsOf(cs):
        if p notin seen: inc n
      if n > bestNew:
        bestNew = n
        best = c
    var cs: seq[string]
    for k in cellsOf(fam, best): cs.add render(k)
    for p in pairsOf(cs): seen.incl p
    result.add best

# --- the figure ----------------------------------------------------------------

type
  FamFigure* = object
    covered*, total*: int
  PairFigure* = array[FamilyScope, FamFigure]

proc exercisedProblems*(recs: seq[ExercisedRecord]): seq[string] =
  ## A record naming a family that is not a pin family, or a cell that is not
  ## one of its family's dimension values.
  for r in recs:
    if r.family notin {faCallShape .. faGeneric}:
      result.add "exercised record " & r.testFile & " prog=" & $r.progId &
        ": " & $r.family & " is not a fuzzer family"
      continue
    let known = familyCells(r.family)
    for c in r.cells:
      if render(c) notin known:
        result.add "exercised record " & r.testFile & " prog=" & $r.progId &
          ": cell " & render(c) & " is no value of " & $r.family
    if r.outcome notin ["exact", "declined", "disagree"]:
      result.add "exercised record " & r.testFile & " prog=" & $r.progId &
        ": unknown outcome " & r.outcome

proc pairwiseFigure*(recs: seq[ExercisedRecord]; row = ""): PairFigure =
  ## Each family's covered pairs over its universe, from the `exact` records
  ## (of `row` only, when given).
  var covered: array[FamilyScope, HashSet[string]]
  for r in recs:
    if r.outcome != "exact" or r.family notin {faCallShape .. faGeneric}: continue
    if row.len > 0 and r.row != row: continue
    let u = pairUniverse(r.family)
    var cs: seq[string]
    for c in r.cells: cs.add render(c)
    for p in pairsOf(cs):
      if p in u: covered[r.family].incl p
  for f in FamilyScope:
    result[f] = FamFigure(covered: covered[f].len, total: pairUniverse(f).len)

func familiesIn*(recs: seq[ExercisedRecord]): set[FamilyScope] =
  for r in recs:
    if r.family in {faCallShape .. faGeneric}: result.incl FamilyScope(r.family)

proc `$`*(f: PairFigure): string =
  var c, t: int
  var parts: seq[string]
  for fam in FamilyScope:
    parts.add scopePrefix[fam] & " " & $f[fam].covered & "/" & $f[fam].total
    c += f[fam].covered
    t += f[fam].total
  "pairwise " & $c & "/" & $t & " (" & parts.join(", ") & ")"

# --- the floor -------------------------------------------------------------------

proc parseFloor*(text: string): PairFigure =
  ## `family:<name><TAB>covered<TAB>total` per line; `#` comments. Every
  ## family must have a line, once.
  var seen: set[FamilyScope]
  for raw in text.splitLines:
    let l = raw.strip
    if l.len == 0 or l.startsWith("#"): continue
    let fs = l.split('\t')
    if fs.len != 3:
      raise newException(ValueError, "pairwise floor: malformed line: " & l)
    var hit = false
    for fam in FamilyScope:
      if scopePrefix[fam] == fs[0]:
        if fam in seen:
          raise newException(ValueError, "pairwise floor: duplicate " & fs[0])
        seen.incl fam
        result[fam] = FamFigure(covered: parseInt(fs[1]), total: parseInt(fs[2]))
        hit = true
    if not hit:
      raise newException(ValueError, "pairwise floor: unknown family " & fs[0])
  for fam in FamilyScope:
    if fam notin seen:
      raise newException(ValueError, "pairwise floor: no line for " &
                         scopePrefix[fam])

proc renderFloor*(f: PairFigure): string =
  result = "# RFC-0016 K8b (section 12 item 4): the pairwise figure's floor.\n" &
    "# family<TAB>covered pairs<TAB>pair universe. Measured by the K8b family\n" &
    "# suites (tsymex_0016_k8b_*); it only rises. A changed universe size\n" &
    "# (a dimension changed) must be re-measured.\n"
  for fam in FamilyScope:
    result.add scopePrefix[fam] & "\t" & $f[fam].covered & "\t" &
      $f[fam].total & "\n"

proc floorProblems*(fig, floor: PairFigure; families: set[FamilyScope]):
    seq[string] =
  ## The ratchet, over the families that ran: a figure below its floor, or a
  ## universe that no longer has the floor's size.
  for fam in families:
    if fig[fam].total != floor[fam].total:
      result.add scopePrefix[fam] & ": the pair universe is " &
        $fig[fam].total & " pairs but the floor was measured over " &
        $floor[fam].total & "; re-measure " & floorFile
    elif fig[fam].covered < floor[fam].covered:
      result.add scopePrefix[fam] & ": pairwise figure " & $fig[fam].covered &
        "/" & $fig[fam].total & " is below the floor " & $floor[fam].covered &
        " in " & floorFile

proc loadFloor*(path = floorFile): PairFigure = parseFloor(readFile(path))

proc loadExercised*(dir: string): seq[ExercisedRecord] =
  for r in exercisedRecords(dir): result.add r


proc exercisedJoinProblems*(ex: seq[ExercisedRecord]; legRow: string;
                            floor: PairFigure): seq[string] =
  ## K1's reading of the second record kind: every record well formed, and
  ## each family that has records (on the leg's row, when one is given) at or
  ## above its floor.
  result = exercisedProblems(ex)
  var mine: seq[ExercisedRecord]
  for r in ex:
    if legRow.len == 0 or r.row == legRow: mine.add r
  if mine.len > 0:
    result.add floorProblems(pairwiseFigure(mine), floor, familiesIn(mine))
