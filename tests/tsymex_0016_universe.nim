## RFC-0016 K1a-cells (section 8.2) -- the universe ledger as an output.
##
## The universe is DERIVED, never hand-listed:
##   * every cell of every admission table that exists (`varParamMagics`,
##     the magic axis; `pcreLibs`, the PCRE-library cells of the build axis),
##     read through `cells()`;
##   * the five `BuildRow`s (`build:row/<row>`);
##   * every `SymexErrorKind`, with its `classOf` (`errorkind:<member>`);
##   * every `CapKind` member but `ckNone` (`capkind:<member>`).
## An axis with no table yet (construct, type class, type op, pragma, stdlib
## body, read-only, definedness) contributes no cell; the ledger prints it as
## a comment line, so an axis landing shows as a diff.
##
## The error-kind and cap-kind sets are "Not axes" (section 8.1): they are
## coverage derivations, not `CellKey` scopes, so their keys are rendered here
## (`errorkind:`, `capkind:`) and live only in the ledger and the allowlists.
## `CapKind` is private to `runtime.nim`, so its members are read from the
## declaration, as `tsymex_0016_k7a_survivors` does.
##
## The join. A cell is CLASSIFIED when a pin record evidences it:
##   * a `CellKey` cell: a record with that cell and an `exact`/`raised`/
##     `declined` verdict from one of section 10's six entry points; a
##     `declined` or `never` cell also takes a `pinCrash` or `admitBuild` record;
##   * a build row: a record whose `row` field is the row. The record carries
##     `rowOf`'s row, filled at write time (`pinBuildRow`); `rowOf` reads the
##     C compiler family, so mingw and msvc are told apart, and neither
##     `buildSegment` nor the cache key changes;
##   * an error kind: a `declined` record whose `declineKind` is the member;
##   * a cap kind: a `declined` record whose `cap` field is the member
##     (`pinCap`: the run halted on that cap, asserted from the cap site's
##     kind and message). A cap without such a pin is allowlisted under the
##     slice that adds it.
## Records naming a cell no table derives (an axis with no table yet, or an
## id K1a-ids joins) are ORPHANS: the test prints them as a named list and
## does not fail on them.
## An unclassified cell with no allowlist entry FAILS; an allowlist entry for
## a classified cell FAILS as stale (so entries ratchet out).
##
## Where the records come from. The join runs over `$NELLI_PIN_DIR`, the
## directory the pin-writing suites of ONE run wrote into (`scripts/k1lite.sh`
## shows the shape). It is evaluated only when that variable is set and the
## directory holds records. The in-repo default `tests/.pins/` is NOT read: it
## is shared by every run, so under a parallel sweep its content is whatever
## other tests had written so far, and a stale record would satisfy a cell
## (k1lite's reason, too). Without records the structural checks still run
## (the committed ledger, the allowlist entries against the universe, the
## self-tests over fixtures) and the test prints that the join was not
## evaluated. Failing on an empty directory, and the sweep that makes one, is
## K1a-last's; the CI join job is K1a-ci's.
##
## The allowlists are `tests/0016-allowlist/<scope>.txt` for scope magic,
## build, errorkind and capkind. A line is `cell<TAB>slice<TAB>reason`; the
## slice is an id from the RFC's slice tables. `UNASSIGNED` is rejected: an
## entry with no owning slice is not allowed.
##
## The committed ledger `docs/rfc/0016-universe.tsv` is compared with the
## derived one on every run. To regenerate after reviewing the growth:
##   scripts/dt-bounded.sh c tests/tsymex_0016_universe.nim 900
##   cp tests/.pins/universe.derived.tsv docs/rfc/0016-universe.tsv
import std/[unittest, os, strutils, sequtils, sets, tables, algorithm, options]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/admission
import nelli/smt/pcre_engine
import nelli/smt/dsl_parser
import nelli/smt/buildprofile
import nelli/smt/soundness
import ./s8cu_helpers

const
  root = currentSourcePath().parentDir() / ".."
  ledgerPath = root / "docs" / "rfc" / "0016-universe.tsv"
  derivedPath = root / "tests" / ".pins" / "universe.derived.tsv"
  allowDir = root / "tests" / "0016-allowlist"
  rfcPath = root / "docs" / "rfc" / "0016-native-parity-hardening.md"
  fixtureDir = root / "tests" / "0016-fixtures" / "universe-pins"
  runtimePath = root / "src" / "nelli" / "smt" / "runtime.nim"
  scopes = ["magic", "build", "errorkind", "capkind"]
  unassigned = "UNASSIGNED"   ## rejected as a slice id
  publicEntries = ["symexFind", "symexFindAllWitnesses", "symexForAll",
                   "assertCoveredBy", "concolic", "loadSymexVerdict"]

type
  UCell = object
    key: string      ## rendered: `magic:Swap`, `errorkind:feX`, `build:row/msvc`
    state: string    ## modelled | declined | never | row | cap | the DegradeClass
    detail: string

  Allow = object
    key, slice, reason: string

# --- the universe ----------------------------------------------------------

func scopeOf(key: string): string = key[0 ..< key.find(':')]

func stateOf(admitted: bool; intent: Intent): string =
  if admitted: "modelled" elif intent == iNever: "never" else: "declined"

proc capMembers(): seq[string] =
  ## The `CapKind` members other than `ckNone`, from the declaration.
  var inEnum = false
  for raw in readFile(runtimePath).splitLines():
    let t = raw.strip()
    if t.len == 0 or t.startsWith("#"): continue
    if t.startsWith("CapKind = enum"): inEnum = true; continue
    if inEnum:
      let word = t.split({' ', '\t'})[0]
      if not word.startsWith("ck"): break
      if word != "ckNone": result.add word

proc deriveUniverse(): seq[UCell] =
  for c in varParamMagics.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-")
  for c in pcreLibs.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-")
  for r in BuildRow:
    result.add UCell(key: "build:row/" & $r, state: "row", detail: "-")
  for k in SymexErrorKind:
    result.add UCell(key: "errorkind:" & $k, state: "kind",
                     detail: $classOf(k))
  for m in capMembers():
    result.add UCell(key: "capkind:" & m, state: "cap", detail: "-")
  result.sort(proc (a, b: UCell): int = cmp(a.key, b.key))

proc countIn(u: seq[UCell]; prefix: string): int =
  u.countIt(it.key.startsWith(prefix))

proc ledgerText(u: seq[UCell]): string =
  result = "# RFC-0016 section 8.2 universe ledger. GENERATED by " &
           "tests/tsymex_0016_universe.nim; do not edit.\n"
  result.add "# regenerate: scripts/dt-bounded.sh c tests/tsymex_0016_universe.nim " &
             "900 && cp tests/.pins/universe.derived.tsv docs/rfc/0016-universe.tsv\n"
  for a in Axis:
    let p = scopePrefix[a] & ":"
    result.add "# axis " & scopePrefix[a] & ": " &
               $(u.countIn(p) - (if a == axBuild: u.countIn("build:row/") else: 0)) &
               " cells" & (if a == axBuild: " (pcre libs; rows below)" else: "") & "\n"
  result.add "# build rows: " & $u.countIn("build:row/") & "\n"
  result.add "# error kinds: " & $u.countIn("errorkind:") & "\n"
  result.add "# cap kinds: " & $u.countIn("capkind:") & "\n"
  result.add "cell\tstate\tdetail\n"
  for c in u: result.add c.key & "\t" & c.state & "\t" & c.detail & "\n"

proc lineDiff(committed, derived: string): string =
  ## `- line` for what only the committed ledger has, `+ line` for what only
  ## the derived one does.
  let a = committed.splitLines().toHashSet
  let b = derived.splitLines().toHashSet
  for l in committed.splitLines():
    if l notin b: result.add "- " & l & "\n"
  for l in derived.splitLines():
    if l notin a: result.add "+ " & l & "\n"

# --- records and the join --------------------------------------------------

func evidences(u: UCell; r: PinRecord): bool =
  case scopeOf(u.key)
  of "errorkind":
    r.verdict == pvDeclined and "errorkind:" & r.declineKind == u.key
  of "capkind":
    r.verdict == pvDeclined and r.cap.len > 0 and
      "capkind:" & r.cap == u.key
  else:
    if u.key.startsWith("build:row/"):
      r.verdict != pvSkipped and r.row == u.key[10 .. ^1]
    else:
      if render(r.cell) != u.key: false
      else:
        let strong = r.verdict in {pvExact, pvRaised, pvDeclined} and
                     r.entry in publicEntries
        let weak = (r.verdict == pvCrashed and r.entry == "pinCrash") or
                   r.entry == "admitBuild"
        strong or (u.state in ["declined", "never"] and weak)

proc sliceIds(): HashSet[string] =
  ## The ids in the first column of the RFC's tables.
  for line in readFile(rfcPath).splitLines():
    if line.startsWith("| "):
      let cell = line[2 .. ^1].split('|')[0].strip()
      if cell.len > 0 and ' ' notin cell and not cell.startsWith("-"):
        for part in cell.split('/'): result.incl part.strip(chars = {'`', ' '})
        result.incl cell.strip(chars = {'`', ' '})

proc parseAllow(text, file: string): seq[Allow] =
  for raw in text.splitLines():
    let l = raw.strip(trailing = true)
    if l.len == 0 or l.startsWith("#"): continue
    let f = l.split('\t')
    result.add Allow(key: f[0], slice: (if f.len > 1: f[1].strip else: ""),
                     reason: (if f.len > 2: f[2].strip else: ""))

proc loadAllow(dir: string): seq[Allow] =
  for s in scopes:
    let p = dir / (s & ".txt")
    if fileExists(p): result.add parseAllow(readFile(p), p)

proc structural(u: seq[UCell]; allow: seq[Allow]; ids: HashSet[string]):
    seq[string] =
  ## Allowlist entries against the universe, with no records involved.
  let keys = u.mapIt(it.key).toHashSet
  var seen = initHashSet[string]()
  for a in allow:
    if a.key notin keys:
      result.add "allowlist entry " & a.key & " names no cell of the universe"
    if a.key in seen: result.add "allowlist entry " & a.key & " is listed twice"
    seen.incl a.key
    if a.slice notin ids:
      result.add "allowlist entry " & a.key & ": slice \"" & a.slice &
                 "\" is not a slice id of the RFC (" & unassigned &
                 " is not allowed: name the slice that fills it)"
    if a.reason.len == 0:
      result.add "allowlist entry " & a.key & " has no reason"

proc joinUniverse(u: seq[UCell]; recs: seq[PinRecord]; allow: seq[Allow]):
    seq[string] =
  ## One message per failing cell. Needs the records of one run.
  let allowed = allow.mapIt(it.key).toHashSet
  for c in u:
    let covered = recs.anyIt(c.evidences(it))
    if not covered and c.key notin allowed:
      result.add "unclassified cell " & c.key & " (" & c.state &
        "): no pin record evidences it and no allowlist entry names it"
    if covered and c.key in allowed:
      result.add "stale allowlist entry " & c.key &
        ": a pin record evidences it now; remove the line"

proc orphanCells(u: seq[UCell]; recs: seq[PinRecord]): seq[string] =
  ## The distinct cells records name that no table derives, sorted. Not a
  ## failure yet: K1a-ids joins ids and the axes without tables.
  let known = u.mapIt(it.key).toHashSet
  var seen = initHashSet[string]()
  for r in recs:
    let k = render(r.cell)
    if k notin known and k notin seen:
      seen.incl k
      result.add k
  result.sort()

# --- the run ---------------------------------------------------------------

let
  universe = deriveUniverse()
  pinDirEnv = getEnv("NELLI_PIN_DIR", "")

proc loadRecords(dir: string): seq[PinRecord] =
  for r in pinRecords(dir): result.add r

proc seg(os, backend, z3: string): string =
  "bs1<build:os=" & os & ";backend=" & backend & "|host:z3Full=" & z3 & ">"

proc synth(c: UCell): PinRecord =
  ## A record that evidences `c` (the self-tests' stand-in for a run).
  result = PinRecord(testFile: "synth.nim", entry: "symexFind",
    cell: cellKey(axConstruct, "synth"), target: "t", domain: "-",
    verdict: pvExact, build: seg("linux", "c", "5.1.0"), row: "linux-c")
  case scopeOf(c.key)
  of "errorkind":
    result.verdict = pvDeclined
    result.declineKind = c.key["errorkind:".len .. ^1]
  of "capkind":
    result.verdict = pvDeclined
    result.cap = c.key["capkind:".len .. ^1]
  else:
    if c.key.startsWith("build:row/"):
      result.row = c.key[10 .. ^1]
    else:
      result.cell = parseCellKey(c.key).get
      if c.state in ["declined", "never"]: result.verdict = pvDeclined

proc synthAll(skip: string = ""): seq[PinRecord] =
  ## Records for every cell, except `skip`.
  for c in universe:
    if c.key != skip: result.add synth(c)

proc allowFor(cells: seq[string]): seq[Allow] =
  cells.mapIt(Allow(key: it, slice: "K9c", reason: "r"))

proc mustFirst(u: seq[UCell]; scope: string): UCell =
  u.filterIt(scopeOf(it.key) == scope)[0]

suite "RFC-0016 K1a-cells: the universe is derived":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 282

  test "every source contributes cells":
    check universe.countIn("magic:") >= 10
    check universe.countIn("build:") >= 3 + 5
    check universe.countIn("build:row/") == ord(high(BuildRow)) + 1
    check universe.countIn("errorkind:") == ord(high(SymexErrorKind)) + 1
    check universe.countIn("capkind:") >= 9

  test "keys are unique and every CellKey cell parses back":
    check universe.mapIt(it.key).toHashSet.len == universe.len
    for c in universe:
      if scopeOf(c.key) in ["magic", "build"] and
         not c.key.startsWith("build:row/"):
        check parseCellKey(c.key).isSome

  test "an error-kind cell carries its classOf":
    let c = universe.filterIt(it.key == "errorkind:feUnadmitted")
    check c.len == 1
    check c[0].detail == $classOf(feUnadmitted)

  test "the committed ledger equals the derived one":
    createDir(derivedPath.parentDir)
    let derived = ledgerText(universe)
    writeFile(derivedPath, derived)
    let committed = if fileExists(ledgerPath): readFile(ledgerPath) else: ""
    checkpoint "the derived universe differs from docs/rfc/0016-universe.tsv " &
      "(review the growth, then regenerate: scripts/dt-bounded.sh c " &
      "tests/tsymex_0016_universe.nim 900 && cp tests/.pins/" &
      "universe.derived.tsv docs/rfc/0016-universe.tsv):\n" &
      lineDiff(committed, derived)
    check committed == derived

suite "RFC-0016 K1a-cells: the allowlists":
  let ids = sliceIds()

  test "the RFC's slice table is read":
    check "K4a-table" in ids
    check "K9c" in ids
    check "CI-B" in ids

  test "the committed allowlists are well formed against the universe":
    let fails = structural(universe, loadAllow(allowDir), ids)
    checkpoint fails.join("\n")
    check fails.len == 0

  test "RED: an entry for a cell outside the universe fails":
    let fails = structural(universe, @[Allow(key: "magic:NoSuchCell",
      slice: "K9c", reason: "r")], ids)
    check fails.len == 1
    check "magic:NoSuchCell" in fails[0]

  test "RED: an invented slice id, or no reason, fails":
    let k = universe.mustFirst("magic").key
    check structural(universe, @[Allow(key: k, slice: "K99z", reason: "r")],
                     ids).anyIt("K99z" in it)
    check structural(universe, @[Allow(key: k, slice: "K9c", reason: "")],
                     ids).anyIt("no reason" in it)

  test "a duplicate entry fails":
    let k = universe.mustFirst("magic").key
    check structural(universe, allowFor(@[k, k]), ids).anyIt("twice" in it)

  test "the allowlist parser reads cell, slice and reason":
    let a = parseAllow("# c\n\nmagic:Swap\tK4a-table\tno pin yet\n", "x")
    check a == @[Allow(key: "magic:Swap", slice: "K4a-table",
                       reason: "no pin yet")]

suite "RFC-0016 K1a-cells: the join (self-test over synthetic records)":
  test "records for every cell leave no gap":
    let gaps = newSeq[string]()
    let fails = joinUniverse(universe, synthAll(), allowFor(gaps))
    checkpoint fails.join("\n")
    check fails.len == 0

  test "RED: a planted missing record fails naming the cell":
    let gaps = newSeq[string]()
    for victim in ["magic:Swap", "errorkind:feUnadmitted", "build:row/linux-cpp",
                   "build:8.45 2021-06-15|interp"]:
      let fails = joinUniverse(universe, synthAll(victim), allowFor(gaps))
      checkpoint victim & ": " & fails.join(" | ")
      check fails.len == 1
      check victim in fails[0] and "unclassified" in fails[0]

  test "RED: a stale allowlist entry fails":
    let gaps = newSeq[string]()
    let fails = joinUniverse(universe, synthAll(),
                             allowFor(gaps & "magic:Swap"))
    check fails.len == 1
    check "stale" in fails[0] and "magic:Swap" in fails[0]

  test "an allowlisted cell with no record passes":
    let recs = synthAll("magic:Swap")
    let gaps = @["magic:Swap"]
    check joinUniverse(universe, recs, allowFor(gaps)).len == 0

  test "a skipped or non-public record is not evidence":
    let c = universe.filterIt(it.key == "magic:Swap")[0]
    var r = synth(c)
    r.verdict = pvSkipped
    check not c.evidences(r)
    r = synth(c)
    r.entry = "caller"
    check not c.evidences(r)
    r.entry = "symexFind"
    check c.evidences(r)
    r.verdict = pvCrashed
    r.entry = "pinCrash"
    check not c.evidences(r)             # a modelled cell needs a verdict

  test "a crash or an admitBuild record evidences a declined or never cell":
    let d = UCell(key: "magic:Destroy", state: "never", detail: "-")
    var r = PinRecord(cell: cellKey(axMagic, "Destroy"), verdict: pvCrashed,
                      entry: "pinCrash")
    check d.evidences(r)
    r.verdict = pvDeclined
    r.entry = "admitBuild"
    check d.evidences(r)

  test "a build row is named by the record's row field, not its segment":
    let c = UCell(key: "build:row/mingw", state: "row", detail: "-")
    var r = synth(c)
    check c.evidences(r)
    r.row = "msvc"
    check not c.evidences(r)
    r = synth(c)
    r.row = ""
    check not c.evidences(r)
    r.row = "mingw"
    r.verdict = pvSkipped
    check not c.evidences(r)

  test "an error kind is evidenced by a declined record's declineKind only":
    let c = universe.filterIt(it.key == "errorkind:feUnadmitted")[0]
    var r = synth(c)
    check c.evidences(r)
    r.verdict = pvExact
    check not c.evidences(r)

  test "a cap is evidenced by a declined record naming it":
    let c = UCell(key: "capkind:ckFrontier", state: "cap", detail: "-")
    var r = synth(c)
    check c.evidences(r)
    r.cap = "ckCallDepth"
    check not c.evidences(r)
    r = synth(c)
    r.verdict = pvExact
    check not c.evidences(r)

  test "RED: UNASSIGNED is not a slice id":
    let k = universe.mustFirst("magic").key
    check structural(universe, @[Allow(key: k, slice: unassigned,
      reason: "r")], sliceIds()).anyIt("UNASSIGNED" in it)

  test "orphan cells are the distinct, sorted cells no table derives":
    var a = synth(universe.mustFirst("magic"))
    var b = a
    b.cell = cellKey(axMagic, "NoSuchMagicB")
    var c = a
    c.cell = cellKey(axMagic, "NoSuchMagicA")
    check orphanCells(universe, @[a, b, c, c]) ==
      @["magic:NoSuchMagicA", "magic:NoSuchMagicB"]

  test "the fixture directory loads and evidences its cells":
    let recs = loadRecords(fixtureDir)
    check recs.len == 2
    let swap = universe.filterIt(it.key == "magic:Swap")[0]
    check recs.anyIt(swap.evidences(it))
    check recs[0].row == "linux-c"

suite "RFC-0016 K1a-cells: the join over this run's records":
  test "the committed allowlists against NELLI_PIN_DIR":
    let recs = if pinDirEnv.len > 0: loadRecords(pinDirEnv) else: @[]
    if recs.len == 0:
      echo "universe: the join was NOT evaluated (NELLI_PIN_DIR " &
           (if pinDirEnv.len == 0: "is unset" else: pinDirEnv & " holds no records") &
           "); K1a-last makes this a failure"
    else:
      let fails = joinUniverse(universe, recs, loadAllow(allowDir))
      checkpoint "NELLI_PIN_DIR=" & pinDirEnv & " (" & $recs.len &
                 " records)\n" & fails.join("\n")
      check fails.len == 0
      let orphans = orphanCells(universe, recs)
      echo "universe: " & $universe.len & " cells, " & $recs.len &
           " records, " & $orphans.len & " cells that records name and no " &
           "table has yet (K1a-ids joins them): " & orphans.join(", ")
