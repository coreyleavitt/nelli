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
import ./worklist_toml
import ./rfc0016_ids

const
  root = currentSourcePath().parentDir() / ".."
  ledgerPath = root / "docs" / "rfc" / "0016-universe.tsv"
  derivedPath = root / "tests" / ".pins" / "universe.derived.tsv"
  allowDir = root / "tests" / "0016-allowlist"
  rfcPath = root / "docs" / "rfc" / "0016-native-parity-hardening.md"
  handoffPath = root / "docs" / "rfc" / "0016-native-parity-hardening.handoff.md"
  worklistPath = root / "docs" / "rfc-data" / "0016-worklist.toml"
  nimblePath = root / "nelli.nimble"
  testsDir = root / "tests"
  fixtureDir = root / "tests" / "0016-fixtures" / "universe-pins"
  runtimePath = root / "src" / "nelli" / "smt" / "runtime.nim"
  scopes = ["magic", "build", "errorkind", "capkind"]
  publicEntries = ["symexFind", "symexFindAllWitnesses", "symexForAll",
                   "assertCoveredBy", "concolic", "loadSymexVerdict"]

type
  UCell = object
    key: string      ## rendered: `magic:Swap`, `errorkind:feX`, `build:row/msvc`
    state: string    ## modelled | declined | never | row | cap | the DegradeClass
    detail: string

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

proc loadAllow(dir: string): seq[Allow] =
  for s in scopes:
    let p = dir / (s & ".txt")
    if fileExists(p): result.add parseAllow(readFile(p))

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
    result.add entryProblems(a, ids)

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
  let ids = sliceIds(readFile(rfcPath))

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
    let a = parseAllow("# c\n\nmagic:Swap\tK4a-table\tno pin yet\n")
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
      reason: "r")], sliceIds(readFile(rfcPath))).anyIt("UNASSIGNED" in it)

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

# --- K1a-ids: the work list ------------------------------------------------

proc mutate(w: Worklist; id: string; key: string; val: seq[string]): Worklist =
  result = w
  for r in result.rows.mitems:
    if r.id == id: r.arr[key] = val

proc setState(w: Worklist; id, state: string): Worklist =
  result = w
  for r in result.rows.mitems:
    if r.id == id: r.str["state"] = state

proc firstWith(w: Worklist; pred: proc (r: WRow): bool): WRow =
  for r in w.rows:
    if pred(r): return r
  raise newException(ValueError, "no such row")

suite "RFC-0016 K1a-ids: the work list is data":
  let
    wl = parseWorklist(readFile(worklistPath), worklistPath)
    slices = sliceIds11(readFile(rfcPath))
    ukeys = universe.mapIt(it.key).toHashSet
    registered = registeredTests(readFile(nimblePath))
    idsAllow = parseAllow(readFile(allowDir / "ids.txt"))

  proc join(w: Worklist; a: seq[Allow]): seq[string] =
    joinIds(w, a, slices, ukeys, registered, testsDir)

  test "the committed work list, ids.txt and slice ids agree":
    let fails = join(wl, idsAllow)
    checkpoint fails.join("\n")
    check fails.len == 0

  test "every section 5 table is a [[table]] and the rows are all there":
    check wl.tables.len == 16
    check wl.rows.len >= 200
    check "K1a-ids" in slices and "W4-z" in slices
    check "SND-01" notin slices        # a work-list id is not a filling slice

  test "the RFC's tables are the render of the TOML (the staleness check)":
    let have = readFile(rfcPath)
    let (want, problems) = renderRfc(have, wl)
    checkpoint problems.join("\n") & "\n" & lineDiff(have, want) &
      "\nregenerate: scripts/check-worklist.sh write"
    check problems.len == 0
    check want == have

  test "RED: a hand edit to a rendered row is stale":
    let have = readFile(rfcPath)
    let edited = have.replace("| SND-02 | ", "| SND-02 (hand edit) | ")
    check edited != have
    let (want, problems) = renderRfc(edited, wl)
    check problems.len == 0
    check want != edited
    check want == have                 # the render restores the TOML's text

  test "RED: a table with no marker pair, or a marker naming no table, fails":
    let have = readFile(rfcPath)
    check renderRfc(have.replace("<!-- worklist:begin 5.1 -->\n", ""),
                    wl).problems.len >= 1
    check renderRfc(have.replace("worklist:begin 5.1 ", "worklist:begin 9.9 "),
                    wl).problems.anyIt("9.9" in it)

  test "a rendered status cell begins with the vocabulary word":
    for r in wl.rows:
      if r.get("state") == "open": continue
      let c = r.statusCell
      let word = if r.stateWord == "owned": r.get("state")[6 .. ^1]
                 else: r.get("state")
      check c.startsWith(word)

  test "F ledger ids are aliases of the W rows, with the ledger's sha":
    var n = 0
    for l in readFile(handoffPath).splitLines():
      if l.startsWith("| F-0"):
        let f = l.split('|').mapIt(it.strip())
        let row = wl.resolve(f[1])
        check row.isSome
        if row.isSome:
          inc n
          check row.get.id.startsWith("W-")
          check row.get.get("state") == "closed"
          check ("`" & row.get.get("sha") & "`") in f[^2]
          check ("(" & row.get.id & ")") in f[6]
    check n == 7
    check wl.resolve("F-0001").get.id == "W-01"
    check wl.resolve("F-9999").isNone

  test "the renumbered rows keep their notes and the old ids are the 5.2 rows":
    check wl.resolve("PRC-39").get.get("note").contains("renumbered from PRC-36")
    check wl.resolve("PRC-40").get.get("note").contains("renumbered from PRC-37")
    check wl.resolve("PRC-36").get.get("title").contains("var")
    check wl.resolve("PRC-37").get.get("title").contains("uncheckedAssign")

suite "RFC-0016 K1a-ids: the id join (RED self-tests)":
  let
    wl = parseWorklist(readFile(worklistPath), worklistPath)
    slices = sliceIds11(readFile(rfcPath))
    ukeys = universe.mapIt(it.key).toHashSet
    registered = registeredTests(readFile(nimblePath))
    idsAllow = parseAllow(readFile(allowDir / "ids.txt"))
    openRow = wl.firstWith(proc (r: WRow): bool = r.get("state") == "open" and
                                                  not r.evidenced)
    closedRow = wl.firstWith(proc (r: WRow): bool = r.get("state") == "closed")
    aKind = universe.mustFirst("errorkind").key

  proc join(w: Worklist; a: seq[Allow]): seq[string] =
    joinIds(w, a, slices, ukeys, registered, testsDir)
  proc entry(id: string; slice = "K9c"; reason = "r"): Allow =
    Allow(key: id, slice: slice, reason: reason)

  test "RED: an open id with no evidence and no entry fails naming the id":
    let a = idsAllow.filterIt(it.key != openRow.id)
    let fails = join(wl, a)
    check fails.len == 1
    check openRow.id in fails[0] and "open id" in fails[0]

  test "an open id with a cell is evidenced and needs no entry":
    let w = wl.mutate(openRow.id, "cells", @[aKind])
    let a = idsAllow.filterIt(it.key != openRow.id)
    check join(w, a).len == 0

  test "RED: an entry for an evidenced id is stale":
    let w = wl.mutate(openRow.id, "cells", @[aKind])
    let fails = join(w, idsAllow)
    check fails.len == 1
    check "stale" in fails[0] and openRow.id in fails[0]

  test "RED: an entry for a closed id is stale":
    let fails = join(wl, idsAllow & entry(closedRow.id))
    check fails.len == 1
    check "stale" in fails[0] and "closed" in fails[0]

  test "RED: a closing open id leaves its entry stale":
    let w = wl.setState(openRow.id, "closed")
    let fails = join(w, idsAllow)
    check fails.len == 1
    check "stale" in fails[0] and openRow.id in fails[0]

  test "an alias resolves to its row (an entry naming it counts for the row)":
    let r = wl.firstWith(proc (x: WRow): bool = x.list("aliases").len > 0)
    let w = wl.setState(r.id, "open")
    check join(w, idsAllow).anyIt("open id " & r.id in it)
    let a = idsAllow & entry(r.list("aliases")[0])
    check join(w, a).len == 0
    check join(w, a & entry(r.id)).anyIt("twice" in it)

  test "RED: an entry for an unknown id, a duplicate, UNASSIGNED, an invented":
    check join(wl, idsAllow & entry("NOPE-99")).anyIt("NOPE-99" in it)
    check join(wl, idsAllow & entry(idsAllow[0].key)).anyIt("twice" in it)
    check join(wl, idsAllow & entry("NOPE-99", unassigned)).anyIt(
      "UNASSIGNED" in it)
    check join(wl, idsAllow & entry("NOPE-99", "K99z")).anyIt("K99z" in it)
    check join(wl, idsAllow & entry("NOPE-99", "K9c", "")).anyIt(
      "no reason" in it)

  test "RED: a typo in a cells entry fails instead of naming nothing":
    let w = wl.mutate(openRow.id, "cells", @["magic:NoSuchCell"])
    check join(w, idsAllow).anyIt("NoSuchCell" in it)
    let w2 = wl.mutate(openRow.id, "cells", @["errorkind:feNoSuchKind"])
    check join(w2, idsAllow).anyIt("feNoSuchKind" in it)

  test "RED: an unregistered or missing pin file fails":
    let w = wl.mutate(openRow.id, "pins", @["tsymex_0016_no_such_test"])
    let fails = join(w, idsAllow)
    check fails.anyIt("not registered" in it)
    check fails.anyIt("not a file" in it)

  test "RED: a state outside the vocabulary, or a duplicate id, fails":
    check join(wl.setState(openRow.id, "done"), idsAllow).anyIt("vocabulary" in it)
    var w = wl
    w.rows.add wl.rows[0]
    check join(w, idsAllow).anyIt("listed twice" in it)

  test "the flat reader rejects an unknown key and reads escapes":
    expect AssertionDefect:
      discard parseWorklist("[[row]]\nidd = \"x\"\n")
    let w = parseWorklist("[[row]]\nid = \"a\\\\|b \\\"q\\\"\"\ncells = [\"x\", \"y\"]\n")
    check w.rows[0].id == "a\\|b \"q\""
    check w.rows[0].list("cells") == @["x", "y"]
