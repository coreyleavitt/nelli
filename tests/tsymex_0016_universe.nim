## RFC-0016 K1a-cells (section 8.2) -- the universe ledger as an output.
##
## The universe is DERIVED, never hand-listed:
##   * every cell of every admission table that exists (`magicAxis`,
##     the magic axis; `pcreLibs`, the PCRE-library cells of the build axis,
##     and `buildCells`, its refusal, hazard and cfg-suite cells;
##     `typeClassTable` and `typeOpTable`, K3a's type-class and type x
##     memory-op axes; `pragmaAxis`, K3c's pragma axis; `definednessTable`,
##     K10a-axis's), read through
##     `cells()`;
##   * the five `BuildRow`s (`build:row/<row>`);
##   * every `SymexErrorKind`, with its `classOf` (`errorkind:<member>`);
##   * every `CapKind` member but `ckNone` (`capkind:<member>`).
## An axis with no table yet (construct, read-only) contributes no cell; the ledger prints it as
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
##     `declined` or `never` cell also takes a `pinCrash` or `admitBuild` record,
##     and a `never` cell a `pinNever` record (K5b);
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
## evaluated. When the variable IS set, an empty directory fails (K1a-last):
## `scripts/sweep.sh` sets it to a per-sweep directory and runs this file
## last. The same run fails a row whose newest record is over seven days old
## (`freshnessProblems`, the clock `$NELLI_PIN_NOW` or the wall clock). The
## CI join job is K1a-ci's.
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
import std/[unittest, os, strutils, sequtils, sets, tables, algorithm, options,
            times]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/admission
import nelli/smt/pcre_engine
import nelli/smt/magic_rows
import nelli/smt/buildprofile
import nelli/smt/typeaxes
import nelli/smt/pragmaaxes
import nelli/smt/readonlyaxes
import nelli/smt/constructaxes
import nelli/smt/stdlib_rows
import nelli/smt/definedness
import nelli/smt/soundness
import ./s8cu_helpers
import ./worklist_toml
import ./rfc0016_ids

const
  root = currentSourcePath().parentDir() / ".."
  ledgerPath = root / "docs" / "rfc" / "0016-universe.tsv"
  derivedPath = root / "tests" / ".pins" / "universe.derived.tsv"
  allowDir = root / "tests" / "0016-allowlist"
  introPath = root / "tests" / "0016-allowlist" / "intro-counts.txt"
  overPath = root / "tests" / "0016-allowlist" / "over-intro.txt"
  rfcPath = root / "docs" / "rfc" / "0016-native-parity-hardening.md"
  handoffPath = root / "docs" / "rfc" / "0016-native-parity-hardening.handoff.md"
  worklistPath = root / "docs" / "rfc-data" / "0016-worklist.toml"
  nimblePath = root / "nelli.nimble"
  testsDir = root / "tests"
  fixtureDir = root / "tests" / "0016-fixtures" / "universe-pins"
  runtimePath = root / "src" / "nelli" / "smt" / "runtime.nim"
  scopes = ["magic", "build", "errorkind", "capkind", "typeclass", "typeop", "pragma", "stdlib",
            "defined"]
  publicEntries = ["symexFind", "symexFindAllWitnesses", "symexForAll",
                   "assertCoveredBy", "concolic", "loadSymexVerdict"]

type
  UCell = object
    key: string      ## rendered: `magic:Swap`, `errorkind:feX`, `build:row/msvc`
    kind: string     ## a declined/never cell's SymexErrorKind ("" when none)
    state: string    ## modelled | declined | never | row | cap | the DegradeClass
    detail: string
    ub: seq[string]  ## a modelled defined-axis cell: the UbKinds its rule
                     ## names, sorted ("" none). A cell with any is
                     ## undefined behaviour in some build profile.
    ubOnly: bool     ## every profile of the rule is undefined behaviour

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

func kindOf(k: Option[SymexErrorKind]): string =
  if k.isSome: $k.get else: ""

proc deriveUniverse(): seq[UCell] =
  for c in magicAxis.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
  for c in pcreLibs.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
  for c in typeClassTable.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
  for c in typeOpTable.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
  for c in definednessTable.cells:
    var ubs: seq[string]
    var allUb = false
    if c.admitted:
      for s in DefSite:
        let a = definednessTable.admit(c.cell.key, s)
        if a.payload[dpChecked].kind == dkDefined and
           a.payload[dpUnchecked].kind == dkDefined and
           a.payload[dpFwrapv].kind == dkDefined:
          continue   # a refused or defaulted payload, or an all-defined rule
        allUb = true
        for p in DefProfile:
          if a.payload[p].kind == dkUndefined:
            ubs.add $a.payload[p].ub
          else: allUb = false
        break
    ubs = ubs.deduplicate()
    ubs.sort()
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind), ub: ubs, ubOnly: allUb and ubs.len > 0)
  for c in buildCells.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
  for c in pragmaAxis.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
  for c in readOnlyAxis.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
  for c in constructAxis.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
  for c in stdlibAxis.cells:
    result.add UCell(key: render(c.cell),
                     state: stateOf(c.admitted, c.intent), detail: "-",
                     kind: kindOf(c.kind))
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
               " cells" & (if a == axBuild: " (pcre libs and build cells; rows below)" else: "") & "\n"
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

func sampledUnsat(r: PinRecord): bool =
  ## RFC-0016 section 10: an `sxUnsat` is `exact` only when the native check
  ## covered an exhaustive domain. A sampled one is evidence of a kind (it is
  ## counted, section 12 item 1) but classifies no cell.
  r.verdict == pvExact and r.walker == "sxUnsat" and not r.exhaustive

func evidences(u: UCell; r: PinRecord; legRow = ""): bool =
  ## Section 8.2: a record evidences a cell only from the leg's row (when the
  ## leg has one) and only with a verdict that fits the cell's state.
  if legRow.len > 0 and r.row != legRow: return false
  case scopeOf(u.key)
  of "errorkind":
    r.verdict == pvDeclined and "errorkind:" & r.declineKind == u.key
  of "capkind":
    r.verdict == pvDeclined and r.cap.len > 0 and
      "capkind:" & r.cap == u.key
  else:
    if u.key.startsWith("build:row/"):
      r.verdict != pvSkipped and r.row == u.key[10 .. ^1]
    elif render(r.cell) != u.key: false
    else:
      let pub = r.entry in publicEntries
      case u.state
      of "modelled":
        # RFC-0016 section 9: a row modelled as undefined behaviour (in every
        # profile) is evidenced by a public-entry record that REPORTS the
        # kind: a decline carrying it, or a sat whose `witnessUndefined`
        # holds it (`pinUndefined` records both as `pvDeclined` with the kind
        # as `declineKind`). Its exact companion would be a run of a path the
        # row does not claim. A row that is undefined in only some profiles
        # may be evidenced either way.
        let ubShape = pub and r.verdict == pvDeclined and
                      r.declineKind in u.ub
        let exactShape = pub and r.verdict in {pvExact, pvRaised} and
                         not r.sampledUnsat
        if u.ubOnly: ubShape else: exactShape or ubShape
      of "declined", "never":
        # a decline names the kind the table declares (none: the axis reports
        # in its own vocabulary, so any decline fits). K5b: a `never` cell
        # stays as it is; `pinNever` records the native fact that says so.
        (pub and r.verdict == pvDeclined and
           (u.kind.len == 0 or r.declineKind == u.kind)) or
          (r.verdict == pvCrashed and r.entry == "pinCrash") or
          r.entry == "admitBuild" or
          (u.state == "never" and r.entry == "pinNever")
      else: false

func sampledOnlyBy(u: UCell; r: PinRecord; legRow: string): bool =
  ## `r` would evidence `u` if its unsat domain were exhaustive.
  var e = r
  e.exhaustive = true
  r.sampledUnsat and u.evidences(e, legRow)

proc loadAllow(dir: string): seq[Allow] =
  for s in scopes:
    let p = dir / (s & ".txt")
    if fileExists(p): result.add parseAllow(readFile(p))

let knownRows = toSeq(BuildRow).mapIt($it)

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
    for r in a.rows:
      if r notin knownRows:
        result.add "allowlist entry " & a.key & ": row scope \"" & r &
                   "\" is not a build row (" & knownRows.join(", ") & ")"

proc joinUniverse(u: seq[UCell]; recs: seq[PinRecord]; allow: seq[Allow];
                  legRow = ""; partial = false): seq[string] =
  ## One message per failing cell. Needs the records of one run.
  ##
  ## `legRow` (K1a-ci) scopes the join to one CI leg: a leg runs ONE build row,
  ## so every other `build:row/` cell is not its business (and no allowlist
  ## line for a row excuses the leg's own: its records must evidence it).
  ## `partial` is a narrowed run (a `tests_regex` dispatch): the records are a
  ## slice, so an unclassified cell proves nothing and is not reported; a
  ## record that contradicts an allowlist entry still is.
  ## An entry with a `rows` scope (K1a-ci) is live only on a leg whose row is
  ## in it: it excuses the cell there, is stale there, and is inert elsewhere.
  let allowed = allow
    .filterIt(it.rows.len == 0 or legRow in it.rows)
    .mapIt(it.key)
    .filterIt(legRow.len == 0 or not it.startsWith("build:row/"))
    .toHashSet
  for c in u:
    if legRow.len > 0 and c.key.startsWith("build:row/") and
       c.key != "build:row/" & legRow:
      continue
    let covered = recs.anyIt(c.evidences(it, legRow))
    if not covered and not partial and c.key notin allowed:
      var why = "no pin record evidences it"
      if c.state == "modelled" and recs.anyIt(c.sampledOnlyBy(it, legRow)):
        why = "only sampled unsat records evidence it (not exhaustive)"
      result.add "unclassified cell " & c.key & " (" & c.state & "): " & why &
        " and no allowlist entry names it"
    if covered and c.key in allowed:
      result.add "stale allowlist entry " & c.key &
        ": a pin record evidences it now; remove the line"

# --- W3-z: the per-axis criterion (RFC section 11, W3-z) -------------------

type
  IntroCount = object
    ## One committed line of `intro-counts.txt`: the entries an allowlist held
    ## in the commit that introduced it, with that commit.
    scope, sha: string
    n: int
  Over = object
    ## One line of `over-intro.txt`: a scope whose allowlist is not yet shorter
    ## than at its introduction. `ceiling` is its count now; it never grows.
    scope: string
    ceiling: int
    slice, reason: string

proc parseIntro(text: string): seq[IntroCount] =
  for raw in text.splitLines():
    let t = raw.strip()
    if t.len == 0 or t.startsWith("#"): continue
    let f = raw.split('\t')
    if f.len >= 3:
      result.add IntroCount(scope: f[0], n: parseInt(f[1]), sha: f[2])

proc parseOver(text: string): seq[Over] =
  for raw in text.splitLines():
    let t = raw.strip()
    if t.len == 0 or t.startsWith("#"): continue
    let f = raw.split('\t')
    if f.len >= 4:
      result.add Over(scope: f[0], ceiling: parseInt(f[1]), slice: f[2],
                      reason: f[3])

proc allowCount(allow: seq[Allow]; scope: string): int =
  ## The scope's debt: its entries that name work somebody still owes. An
  ## entry with a `rows=` scope is a platform classification (another leg's
  ## row cannot evidence the cell, and that is permanent, not owed), so it is
  ## in neither this count nor the introduction count (W3-z decision (a)).
  for a in allow:
    if scopeOf(a.key) == scope and a.rows.len == 0: inc result

proc shrinkProblems(allow: seq[Allow]; intro: seq[IntroCount];
                    over: seq[Over]; ids: HashSet[string]): seq[string] =
  ## Each cell scope's allowlist is shorter than at its introduction. A scope
  ## that is not yet is named in `over-intro.txt` with a ceiling equal to its
  ## count, so it can only shrink; one that is shorter must not be listed.
  for sc in scopes:
    let now = allow.allowCount(sc)
    let i = intro.filterIt(it.scope == sc)
    if i.len != 1:
      result.add "scope " & sc & ": intro-counts.txt must hold exactly one line"
      continue
    if i[0].sha.len < 7:
      result.add "scope " & sc & ": the introduction count cites no commit"
    let o = over.filterIt(it.scope == sc)
    if now < i[0].n:
      if o.len > 0:
        result.add "scope " & sc & ": " & $now & " entries are shorter than " &
                   $i[0].n & " at " & i[0].sha &
                   "; remove it from over-intro.txt"
    elif o.len != 1:
      result.add "scope " & sc & ": " & $now & " entries are not shorter than " &
                 $i[0].n & " at " & i[0].sha &
                 " and over-intro.txt does not name it"
    elif o[0].ceiling != now:
      result.add "scope " & sc & ": over-intro.txt says " & $o[0].ceiling &
                 " and the allowlist holds " & $now &
                 (if now > o[0].ceiling: " (it grew)" else: " (lower the ceiling)")
  for o in over:
    if o.scope notin scopes:
      result.add "over-intro.txt names " & o.scope &
                 ", which is no allowlist scope"
    if o.slice notin ids:
      result.add "over-intro.txt " & o.scope & ": \"" & o.slice &
                 "\" is no slice id"
    if o.reason.len == 0: result.add "over-intro.txt " & o.scope & " has no reason"

proc axisCells(u: seq[UCell]; prefix: string): seq[UCell] =
  u.filterIt(scopeOf(it.key) == prefix and not it.key.startsWith("build:row/"))

proc axisCellProblems(u: seq[UCell]; pending: Table[string, string]):
    seq[string] =
  ## Every axis has cells. An axis with none is named in `pending` with the
  ## slice that gives it some; one that has cells must not be.
  for a in Axis:
    let p = scopePrefix[a]
    let n = u.axisCells(p).len
    if n == 0 and p notin pending:
      result.add "axis " & p & " has no cell in the universe and is not pending"
    if n > 0 and p in pending:
      result.add "axis " & p & " has " & $n &
                 " cells now; remove its pending entry"

proc axisExactProblems(u: seq[UCell]; recs: seq[PinRecord]; legRow: string;
                       pending: Table[string, string]): seq[string] =
  ## Every axis with cells has at least one modelled cell that a `pvExact`
  ## record from the leg's row evidences (not a decline, not a witnessed
  ## undefined behaviour: a verdict the native run reproduced).
  for a in Axis:
    let p = scopePrefix[a]
    let cells = u.axisCells(p)
    if cells.len == 0 or p in pending: continue
    var ok = false
    for c in cells:
      if c.state != "modelled": continue
      for r in recs:
        if r.verdict == pvExact and c.evidences(r, legRow):
          ok = true
          break
      if ok: break
    if not ok:
      result.add "axis " & p & " has no modelled cell evidenced by an exact " &
                 "record" & (if legRow.len > 0: " on row " & legRow else: "")

const
  ## Axes with no cells yet: the slice that gives each some. None: the
  ## construct axis gained its pinned-subset table in W3-z E2b.
  pendingAxes = initTable[string, string]()

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

type RecordCensus = object
  ## W2-z: what a leg's records cover beyond cells. A SUT is a distinct
  ## `target` (skipped cells name none); `verdicts` counts every record.
  suts: int
  verdicts: array[PinVerdict, int]
  exhaustiveUnsat, sampledUnsat: int

proc recordCensus(recs: seq[PinRecord]): RecordCensus =
  var targets = initHashSet[string]()
  for r in recs:
    inc result.verdicts[r.verdict]
    if r.verdict == pvExact and r.walker == "sxUnsat":
      if r.exhaustive: inc result.exhaustiveUnsat else: inc result.sampledUnsat
    if r.target.len > 0: targets.incl r.target
  result.suts = targets.len

proc censusProblems(c: RecordCensus; partial: bool): seq[string] =
  ## A join whose records reach no SUT evaluated nothing. A full join must
  ## also reproduce at least one walker verdict natively (`pvExact`); a
  ## narrowed run may select only declining cells.
  if c.suts == 0:
    result.add "census: the records name no SUT (no record has a target)"
  if not partial and c.verdicts[pvExact] == 0:
    result.add "census: a full join with no exact verdict proved nothing"

proc `$`(c: RecordCensus): string =
  result = $c.suts & " SUTs, verdicts"
  for v in PinVerdict:
    result.add " " & ($v)[2 .. ^1] & "=" & $c.verdicts[v]
  result.add "; sampled-unsat=" & $c.sampledUnsat & " exhaustive-unsat=" &
             $c.exhaustiveUnsat

const maxEvidenceAgeDays = 7

proc freshnessProblems(recs: seq[PinRecord]; now: Time;
                       maxDays = maxEvidenceAgeDays): seq[string] =
  ## RFC-0016 section 8.2: each BuildRow with a run leg needs evidence dated
  ## within seven days. For every row the records name, its NEWEST record must
  ## be no older than `maxDays` (a record with no date counts as undated, and
  ## undated is stale). A row with no record at all is the join's business (the
  ## build:row cell), not this check's. `now` is a parameter so tests fix it.
  var newest = initTable[string, Time]()
  var undated = initHashSet[string]()
  for r in recs:
    if r.row.len == 0: continue
    if r.date.len == 0:
      undated.incl r.row
      continue
    let t = try: parse(r.date, pinDateFmt, utc()).toTime
            except TimeParseError: (undated.incl r.row; continue)
    if r.row notin newest or t > newest[r.row]: newest[r.row] = t
  for row in undated:
    if row notin newest:
      result.add "row " & row & ": its records carry no parsable date"
  for row, t in newest:
    let age = now - t
    if age > initDuration(days = maxDays):
      result.add "row " & row & ": newest record is " & $age.inDays &
        " days old (" & pinDate(t) & "), over " & $maxDays & " days"
  result.sort()

proc joinDirProblems(dirEnv: string; recs: seq[PinRecord]; now: Time):
    seq[string] =
  ## What a set `$NELLI_PIN_DIR` must satisfy before the join runs at all.
  if dirEnv.len > 0 and recs.len == 0:
    result.add "empty record directory: NELLI_PIN_DIR=" & dirEnv &
      " holds no records, so the join would evaluate nothing"
  else:
    result.add freshnessProblems(recs, now)

# --- the run ---------------------------------------------------------------

let
  universe = deriveUniverse()
  pinDirEnv = getEnv("NELLI_PIN_DIR", "")
  ## K1a-ci: the CI join job names its leg's build row and whether the run was
  ## narrowed (`scripts/universe-join.sh` sets both).
  legRowEnv = getEnv("NELLI_UNIVERSE_ROW", "")
  partialEnv = getEnv("NELLI_UNIVERSE_PARTIAL", "") == "1"

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
      if c.state in ["declined", "never"]:
        result.verdict = pvDeclined
        result.declineKind = c.kind
      elif c.ubOnly:
        result.verdict = pvDeclined
        result.declineKind = c.ub[0]

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
    check universe.countIn("typeclass:") == toSeq(typeClassTable.cells).len
    check universe.countIn("pragma:") == toSeq(pragmaAxis.cells).len
    check universe.countIn("typeop:") == toSeq(typeOpTable.cells).len
    check universe.countIn("readonly:") == toSeq(readOnlyAxis.cells).len
    check universe.countIn("construct:") == toSeq(constructAxis.cells).len
    check universe.countIn("construct:") > 0
    check universe.countIn("defined:") == toSeq(definednessTable.cells).len
    check universe.countIn("build:") >= 3 + 5
    check universe.countIn("build:row/") == ord(high(BuildRow)) + 1
    check universe.countIn("errorkind:") == ord(high(SymexErrorKind)) + 1
    check universe.countIn("capkind:") >= 9

  test "keys are unique and every CellKey cell parses back":
    check universe.mapIt(it.key).toHashSet.len == universe.len
    for c in universe:
      if scopeOf(c.key) in ["magic", "build", "typeclass", "typeop", "pragma", "stdlib", "defined"] and
         not c.key.startsWith("build:row/"):
        check parseCellKey(c.key).isSome

  test "an error-kind cell carries its classOf":
    let c = universe.filterIt(it.key == "errorkind:feUnadmitted")
    check c.len == 1
    check c[0].detail == $classOf(feUnadmitted)

  test "INT-47: the checkout is LF on every platform":
    # This file compares the committed ledger and the RFC's tables with text it
    # renders byte for byte, and edits them with `\n`-terminated patterns. A
    # Windows checkout with `core.autocrlf` turns the files into CRLF and every
    # such comparison fails, so the repository pins the line ending itself.
    let attrs = if fileExists(root / ".gitattributes"):
                  readFile(root / ".gitattributes") else: ""
    check attrs.splitLines.anyIt(
      it.strip.splitWhitespace.len >= 3 and it.strip.startsWith("* ") and
      "text=auto" in it and "eol=lf" in it)
    # and what this build read is LF
    check '\r' notin readFile(ledgerPath)

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

  test "K1a-ci: a leg's join owns its own build row only":
    # mingw's records carry the mingw row and nothing else; the other four
    # rows are other legs' business, and the mingw row is allowlisted nowhere
    # for this leg even though the unscoped allowlist excuses it.
    let rowsOnly = synthAll().filterIt(it.row == "linux-c")
    var recs = rowsOnly
    for r in recs.mitems: r.row = "mingw"
    let rowAllow = @["build:row/mingw", "build:row/msvc"]
    check joinUniverse(universe, recs, allowFor(rowAllow), "mingw").len == 0

  test "RED: a leg whose records lack its own row fails naming the row":
    var recs = synthAll()
    for r in recs.mitems: r.row = "linux-c"
    let fails = joinUniverse(universe, recs, allowFor(@["build:row/mingw"]),
                             "mingw")
    # E1: nothing a linux-c record names is the mingw leg's evidence, so the
    # row cell fails with every other cell the leg has no record for.
    check fails.anyIt("build:row/mingw" in it and "unclassified" in it)
    check fails.len > 1

  test "RED: a scoped leg still fails an unclassified non-row cell":
    var recs = synthAll("errorkind:feUnadmitted")
    for r in recs.mitems: r.row = "msvc"
    let fails = joinUniverse(universe, recs, allowFor(@[]), "msvc")
    check fails.len == 1 and "errorkind:feUnadmitted" in fails[0]

  test "K1a-ci: a row-scoped entry excuses its cell on a scoped row only":
    let k = "errorkind:feUnadmitted"
    let scoped = @[Allow(key: k, slice: "K9c", reason: "r",
                         rows: @["mingw", "msvc"])]
    var recs = synthAll(k)
    for r in recs.mitems: r.row = "mingw"
    check joinUniverse(universe, recs, scoped, "mingw").len == 0
    # RED: on a row outside the scope the cell is unclassified
    var other = synthAll(k)
    for r in other.mitems: r.row = "linux-cpp"
    let fails = joinUniverse(universe, other, scoped, "linux-cpp")
    check fails.len == 1 and k in fails[0] and "unclassified" in fails[0]

  test "K1a-ci: a row-scoped entry is stale only on its scoped rows":
    let k = "errorkind:feUnadmitted"
    let scoped = @[Allow(key: k, slice: "K9c", reason: "r", rows: @["mingw"])]
    var onScoped = synthAll()
    for r in onScoped.mitems: r.row = "mingw"
    let fails = joinUniverse(universe, onScoped, scoped, "mingw")
    check fails.len == 1 and "stale" in fails[0] and k in fails[0]
    var onOther = synthAll()
    for r in onOther.mitems: r.row = "linux-c"
    check joinUniverse(universe, onOther, scoped, "linux-c").len == 0

  test "K1a-ci: an unknown row name in a scope is an error":
    let ids = sliceIds(readFile(rfcPath))
    let k = universe.mustFirst("magic").key
    let fails = structural(universe, @[Allow(key: k, slice: "K9c", reason: "r",
                                             rows: @["mingw", "winders"])], ids)
    check fails.len == 1 and "winders" in fails[0]
    check structural(universe, @[Allow(key: k, slice: "K9c", reason: "r",
                                       rows: @["mingw", "msvc"])], ids).len == 0

  test "K1a-ci: the parser reads an optional rows= field":
    let a = parseAllow("errorkind:heX\tK9c\twhy\trows=mingw,msvc\n" &
                       "errorkind:heY\tK9c\twhy\n")
    check a[0].rows == @["mingw", "msvc"]
    check a[1].rows.len == 0

  test "a partial run reports no unclassified cell but still a stale entry":
    let recs = synthAll("magic:Swap")
    check joinUniverse(universe, recs, allowFor(@[]), "", true).len == 0
    let fails = joinUniverse(universe, recs, allowFor(@["errorkind:feUnadmitted"]),
                             "", true)
    check fails.len == 1 and "stale" in fails[0]

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

suite "RFC-0016 W3-z E1: the join demands a verdict that fits the cell":
  proc firstCell(state: string; withKind = false): UCell =
    for c in universe:
      if c.state == state and scopeOf(c.key) == "magic" and
         (not withKind or c.kind.len > 0): return c
    raise newException(ValueError, "no " & state & " magic cell")

  proc recFor(c: UCell; v: PinVerdict; kind = ""; walker = "";
              exhaustive = false; row = "linux-c"): PinRecord =
    PinRecord(testFile: "synth.nim", entry: "symexFind",
              cell: parseCellKey(c.key).get, target: "t", domain: "-",
              verdict: v, declineKind: kind, walker: walker,
              exhaustive: exhaustive, row: row)

  test "RED: a decline record does not classify a modelled cell":
    let c = firstCell("modelled")
    check c.evidences(recFor(c, pvExact))
    check c.evidences(recFor(c, pvRaised))
    check not c.evidences(recFor(c, pvDeclined))

  test "RED: an exact record does not classify a declined cell":
    let c = firstCell("declined", withKind = true)
    check c.evidences(recFor(c, pvDeclined, c.kind))
    check not c.evidences(recFor(c, pvExact))
    check not c.evidences(recFor(c, pvRaised))

  test "RED: a decline of another kind does not classify a declined cell":
    let c = firstCell("declined", withKind = true)
    let other = if c.kind == "feUnsupportedOp": "feUnadmitted"
                else: "feUnsupportedOp"
    check not c.evidences(recFor(c, pvDeclined, other))
    check not c.evidences(recFor(c, pvDeclined, ""))

  test "RED: a sampled unsat does not classify; an exhaustive one does":
    let c = firstCell("modelled")
    check not c.evidences(recFor(c, pvExact, walker = "sxUnsat"))
    check c.evidences(recFor(c, pvExact, walker = "sxUnsat", exhaustive = true))
    # a sat witness is reproduced natively whatever the domain was
    check c.evidences(recFor(c, pvExact, walker = "sxSat"))

  test "RED: a sampled-only modelled cell fails the join and says why":
    let c = firstCell("modelled")
    var recs = synthAll(c.key)
    recs.add recFor(c, pvExact, walker = "sxUnsat")
    let fails = joinUniverse(universe, recs, allowFor(@[]), "linux-c")
    check fails.len == 1
    if fails.len == 1: check c.key in fails[0] and "sampled" in fails[0]
    recs.add recFor(c, pvExact, walker = "sxUnsat", exhaustive = true)
    check joinUniverse(universe, recs, allowFor(@[]), "linux-c").len == 0

  test "RED: on a leg, a record from another row or from no row evidences nothing":
    let c = firstCell("modelled")
    for row in ["", "mingw"]:
      var recs = synthAll(c.key)
      recs.add recFor(c, pvExact, row = row)
      let fails = joinUniverse(universe, recs, allowFor(@[]), "linux-c")
      check fails.len == 1
      if fails.len == 1: check c.key in fails[0]
    # without a leg the row does not scope
    var any = synthAll(c.key)
    any.add recFor(c, pvExact, row = "")
    check joinUniverse(universe, any, allowFor(@[])).len == 0

  test "RED: the same row rule holds for error-kind and cap-kind cells":
    for victim in ["errorkind:feUnadmitted", "capkind:ckFrontier"]:
      let c = universe.filterIt(it.key == victim)[0]
      var recs = synthAll(c.key)
      var r = synth(c)
      r.row = ""
      recs.add r
      let fails = joinUniverse(universe, recs, allowFor(@[]), "linux-c")
      check fails.len == 1
      if fails.len == 1: check c.key in fails[0]

  test "RED: the census counts sampled and exhaustive unsat separately":
    let c = firstCell("modelled")
    let census = recordCensus(@[recFor(c, pvExact, walker = "sxUnsat"),
                                recFor(c, pvExact, walker = "sxUnsat"),
                                recFor(c, pvExact, walker = "sxUnsat",
                                       exhaustive = true),
                                recFor(c, pvExact, walker = "sxSat")])
    check census.sampledUnsat == 2
    check census.exhaustiveUnsat == 1
    check "sampled-unsat=2" in $census and "exhaustive-unsat=1" in $census

suite "RFC-0016 W3-z E2: the defined axis is evidenced by the UB kind":
  proc rec(c: UCell; v: PinVerdict; declineKind = "";
           entry = "symexFind"): PinRecord =
    result = synth(c)
    result.verdict = v
    result.declineKind = declineKind
    result.entry = entry

  proc ubCell(): UCell =
    for c in universe:
      if c.ubOnly: return c
    raise newException(AssertionDefect, "no UB-only cell in the universe")

  proc mixedCell(): UCell =
    for c in universe:
      if c.ub.len > 0 and not c.ubOnly: return c
    raise newException(AssertionDefect, "no mixed cell in the universe")

  test "the universe carries each defined cell's UB kinds":
    let c = universe.filterIt(it.key == "defined:conv/objDowncast")
    check c.len == 1
    check c[0].ub == @["ubInvalidObjConversion"] and c[0].ubOnly
    let m = universe.filterIt(it.key == "defined:add/signedWide")
    check m.len == 1
    check m[0].ub == @["ubSignedOverflow"] and not m[0].ubOnly
    # a refused row has no payload to read
    check universe.filterIt(it.key == "defined:field/inactiveBytes")[0].ub.len == 0

  test "a record that reports the kind evidences a UB-only cell":
    let c = ubCell()
    check c.evidences(rec(c, pvDeclined, c.ub[0]))

  test "RED: an exact record does not evidence a UB-only cell":
    let c = ubCell()
    check not c.evidences(rec(c, pvExact))
    check not c.evidences(rec(c, pvRaised))

  test "RED: a decline of another kind, or of no kind, does not":
    let c = ubCell()
    check not c.evidences(rec(c, pvDeclined, "feUnsupportedOp"))
    check not c.evidences(rec(c, pvDeclined, ""))
    let other = if c.ub[0] == "ubSignedOverflow": "ubUnsignedDivZero"
                else: "ubSignedOverflow"
    check not c.evidences(rec(c, pvDeclined, other))

  test "RED: a record from a non-public entry does not":
    let c = ubCell()
    check not c.evidences(rec(c, pvDeclined, c.ub[0], entry = "caller"))

  test "RED: on a leg, a record from another row does not":
    let c = ubCell()
    var r = rec(c, pvDeclined, c.ub[0])
    r.row = "linux-c"
    check c.evidences(r, "linux-c")
    check not c.evidences(r, "mingw")

  test "a cell undefined in only some profiles takes either shape":
    let c = mixedCell()
    check c.evidences(rec(c, pvExact))
    check c.evidences(rec(c, pvDeclined, c.ub[0]))
    check not c.evidences(rec(c, pvDeclined, "feUnsupportedOp"))

  test "the join accepts the UB shape and fails a UB cell with no record":
    let c = ubCell()
    check joinUniverse(universe, synthAll(), allowFor(@[])).len == 0
    let fails = joinUniverse(universe, synthAll(c.key), allowFor(@[]))
    check fails.len == 1 and c.key in fails[0]

suite "RFC-0016 W3-z E2: the per-axis criterion":
  test "every axis with cells has an exact record on the leg's row":
    for row in ["linux-c", "mingw"]:
      var recs = synthAll()
      for r in recs.mitems: r.row = row
      check axisExactProblems(universe, recs, row, pendingAxes).len == 0

  test "RED: an axis whose only evidence is a decline or a UB report fails":
    # strip every exact record of one axis, keep the rest
    for ax in ["typeclass", "magic", "defined"]:
      var recs: seq[PinRecord]
      for r in synthAll():
        if not (r.verdict == pvExact and scopeOf(render(r.cell)) == ax):
          recs.add r
      let fails = axisExactProblems(universe, recs, "", pendingAxes)
      checkpoint fails.join("\n")
      check fails.len == 1 and ("axis " & ax) in fails[0]

  test "RED: an exact record from another row is not the leg's evidence":
    var recs = synthAll()
    for r in recs.mitems: r.row = "linux-c"
    check axisExactProblems(universe, recs, "mingw", pendingAxes).len > 0

  test "an axis with no cell is pending, and a pending axis that has cells is stale":
    check axisCellProblems(universe, pendingAxes).len == 0
    check axisCellProblems(universe, initTable[string, string]()).len ==
      pendingAxes.len
    let bare = universe.filterIt(not it.key.startsWith("construct:"))
    check axisCellProblems(bare, pendingAxes).anyIt(
      "construct" in it and "not pending" in it)
    var stale = pendingAxes
    stale["magic"] = "x"
    let fails = axisCellProblems(universe, stale)
    check fails.len == 1 and "magic" in fails[0] and "pending entry" in fails[0]

  let ids = sliceIds(readFile(rfcPath))

  test "the committed allowlists are shorter than at their introduction, or named":
    let fails = shrinkProblems(loadAllow(allowDir),
                               parseIntro(readFile(introPath)),
                               parseOver(readFile(overPath)), ids)
    checkpoint fails.join("\n")
    check fails.len == 0

  test "RED: a longer allowlist than the introduction count fails unless named":
    let a = parseIntro("magic\t1\tabcdef0\nbuild\t5\tabcdef0\n")
    let allow = allowFor(@["magic:Swap", "magic:Add"])
    let one = a.filterIt(it.scope == "magic")
    # the other scopes have no intro line: reported
    check shrinkProblems(allow, one, @[], ids).anyIt("magic" in it and
      "does not name it" in it)
    let named = parseOver("magic\t2\tW4-z\tr\n")
    check not shrinkProblems(allow, one, named, ids).anyIt(
      it.startsWith("scope magic"))

  test "RED: a named scope cannot grow, and must be lowered when it shrinks":
    let intro = parseIntro("magic\t1\tabcdef0\n")
    let allow = allowFor(@["magic:Swap", "magic:Add"])
    check shrinkProblems(allow, intro, parseOver("magic\t1\tW4-z\tr\n"),
                         ids).anyIt("it grew" in it)
    check shrinkProblems(allow, intro, parseOver("magic\t3\tW4-z\tr\n"),
                         ids).anyIt("lower the ceiling" in it)

  test "RED: a scope that is shorter must not stay named":
    let intro = parseIntro("magic\t5\tabcdef0\n")
    let allow = allowFor(@["magic:Swap"])
    check shrinkProblems(allow, intro, parseOver("magic\t1\tW4-z\tr\n"),
                         ids).anyIt("remove it from over-intro.txt" in it)

  test "a rows-scoped platform entry is a classification, not debt":
    let intro = parseIntro("build\t2\tabcdef0\n")
    let keys = @["build:a", "build:b", "build:c|x", "build:d|y"]
    var allow = allowFor(keys[0 .. 1])
    check allow.allowCount("build") == 2
    allow.add parseAllow("build:c|x\tCI-B\tr\trows=msvc\n" &
                         "build:d|y\tCI-B\tr\trows=mingw\n")
    check allow.len == 4
    check allow.allowCount("build") == 2
    # two debt entries are not shorter than 2 whatever the platform entries
    check shrinkProblems(allow, intro, @[], ids).anyIt(
      it.startsWith("scope build") and "does not name it" in it)
    allow = allowFor(@["build:a"]) & allow[2 .. 3]
    check allow.allowCount("build") == 1
    check not shrinkProblems(allow, intro, @[], ids).anyIt(
      it.startsWith("scope build"))

  test "RED: an introduction line without a commit fails":
    let intro = parseIntro("magic\t5\tab\n")
    check shrinkProblems(allowFor(@["magic:Swap"]), intro, @[],
                         ids).anyIt("cites no commit" in it)

suite "RFC-0016 K1a-cells: the join over this run's records":
  test "the committed allowlists against NELLI_PIN_DIR":
    let recs = if pinDirEnv.len > 0: loadRecords(pinDirEnv) else: @[]
    let dirProblems = joinDirProblems(pinDirEnv, recs, pinNow())
    checkpoint dirProblems.join("\n")
    check dirProblems.len == 0
    if pinDirEnv.len == 0:
      echo "universe: the join was NOT evaluated (NELLI_PIN_DIR is unset)"
    elif recs.len > 0:
      let fails = joinUniverse(universe, recs, loadAllow(allowDir),
                               legRowEnv, partialEnv)
      checkpoint "NELLI_PIN_DIR=" & pinDirEnv & " (" & $recs.len &
                 " records)\n" & fails.join("\n")
      check fails.len == 0
      let axisFails = axisExactProblems(universe, recs, legRowEnv, pendingAxes)
      checkpoint axisFails.join("\n")
      if not partialEnv: check axisFails.len == 0
      let census = recordCensus(recs)
      let censusFails = censusProblems(census, partialEnv)
      checkpoint censusFails.join("\n")
      check censusFails.len == 0
      echo "universe census: " & $census
      let orphans = orphanCells(universe, recs)
      echo "universe: " & $universe.len & " cells, " & $recs.len &
           " records, " & $orphans.len & " cells that records name and no " &
           "table has yet (K1a-ids joins them): " & orphans.join(", ")

suite "RFC-0016 W2-z: the record census":
  proc rec(target: string; v: PinVerdict): PinRecord =
    PinRecord(target: target, verdict: v, row: "linux-c")

  test "SUTs are distinct targets and every verdict is counted":
    let c = recordCensus(@[rec("a", pvExact), rec("a", pvDeclined),
                           rec("b", pvExact), rec("", pvSkipped)])
    check c.suts == 2
    check c.verdicts[pvExact] == 2
    check c.verdicts[pvDeclined] == 1
    check c.verdicts[pvSkipped] == 1
    check c.verdicts[pvCrashed] == 0
    check censusProblems(c, partial = false).len == 0

  test "RED: a full join with no SUT or no exact verdict fails":
    let none = recordCensus(@[rec("", pvSkipped)])
    let p = censusProblems(none, partial = false)
    check p.len == 2
    check p.anyIt("no SUT" in it)
    check p.anyIt("no exact verdict" in it)

  test "a partial join needs a SUT but not an exact verdict":
    let c = recordCensus(@[rec("a", pvDeclined)])
    check censusProblems(c, partial = true).len == 0
    check censusProblems(c, partial = false).len == 1

suite "RFC-0016 K1a-last: empty and stale record directories fail":
  let now = fromUnix(1_800_000_000)
  proc rec(row: string; ageDays: int): PinRecord =
    PinRecord(row: row, verdict: pvExact,
              date: pinDate(now - initDuration(days = ageDays)))

  test "RED: a set but empty NELLI_PIN_DIR fails":
    let p = joinDirProblems("/some/sweep.pins", @[], now)
    check p.len == 1
    check "empty record directory" in p[0]

  test "an unset NELLI_PIN_DIR is not a failure (plain single-test run)":
    check joinDirProblems("", @[], now).len == 0

  test "RED: a record dated eight days before now fails the freshness check":
    let p = freshnessProblems(@[rec("linux-c", 8)], now)
    check p.len == 1
    check "linux-c" in p[0] and "8 days old" in p[0]

  test "records of seven days or less pass; the newest record of a row counts":
    check freshnessProblems(@[rec("linux-c", 7)], now).len == 0
    check freshnessProblems(@[rec("linux-c", 30), rec("linux-c", 1)], now).len == 0

  test "each row is judged on its own newest record":
    let p = freshnessProblems(@[rec("linux-c", 1), rec("mingw", 9),
                                rec("mingw", 10)], now)
    check p.len == 1 and p[0].startsWith("row mingw")

  test "an undated record is stale; a record with no row is not judged":
    check freshnessProblems(@[PinRecord(row: "linux-c")], now).len == 1
    check freshnessProblems(@[PinRecord(row: "")], now).len == 0

  test "the clock is injectable":
    check freshnessProblems(@[rec("linux-c", 0)], now + initDuration(days = 8)).len == 1
    putEnv("NELLI_PIN_NOW", "1800000000")
    check pinNow().toUnix == 1_800_000_000
    delEnv("NELLI_PIN_NOW")

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

proc cellStates(): CellStates =
  for c in universe: result[c.key] = c.state

suite "RFC-0016 K1a-ids: the work list is data":
  let
    wl = parseWorklist(readFile(worklistPath), worklistPath)
    slices = sliceIds11(readFile(rfcPath))
    ukeys = universe.mapIt(it.key).toHashSet
    registered = registeredTests(readFile(nimblePath))
    idsAllow = parseAllow(readFile(allowDir / "ids.txt"))
    legacy = parseLegacy(readFile(allowDir / "closed-legacy.txt"))

  proc join(w: Worklist; a: seq[Allow]): seq[string] =
    joinIds(w, a, slices, ukeys, registered, testsDir, cellStates(), legacy)

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
    legacy = parseLegacy(readFile(allowDir / "closed-legacy.txt"))
    openRow = wl.firstWith(proc (r: WRow): bool = r.get("state") == "open" and
                                                  not r.evidenced)
    closedRow = wl.firstWith(proc (r: WRow): bool = r.get("state") == "closed")
    aKind = universe.mustFirst("errorkind").key

  proc join(w: Worklist; a: seq[Allow]): seq[string] =
    joinIds(w, a, slices, ukeys, registered, testsDir, cellStates(), legacy)
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
    # the closed row also fails the E4 evidence rule: that is the point
    check fails.anyIt("stale" in it and openRow.id in it)
    check fails.anyIt("closed row" in it and openRow.id in it)

  test "an alias resolves to its row (an entry naming it counts for the row)":
    let r = wl.firstWith(proc (x: WRow): bool = x.list("aliases").len > 0)
    let w = wl.setState(r.id, "open").mutate(r.id, "pins", @[]).mutate(
      r.id, "cells", @[])
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


suite "RFC-0016 W3-z E4: closed and never rows are evidenced (section 8.2)":
  ## Synthetic work lists: the rules, not the committed data.
  let
    registered = ["tpin_writes", "tpin_silent"].toHashSet
    dir = getTempDir() / "nelli_e4_ids"
  var
    states: CellStates
    ukeys: HashSet[string]
  setup:
    createDir(dir)
    writeFile(dir / "tpin_writes.nim", "pinExact(f, k, x)\n")
    writeFile(dir / "tpin_silent.nim", "echo \"pinExactly nothing\"\n")
    states = {"magic:Mod": "modelled", "magic:Sort": "declined",
              "magic:Hash": "never", "errorkind:feX": "kind"}.toTable
    ukeys = toSeq(states.keys).toHashSet

  proc row(body: string): Worklist =
    parseWorklist("[[table]]\nname = \"t\"\ncolumns = [\"ID\"]\nfields = [\"id\"]\n" &
                  "[[row]]\nid = \"T-01\"\ntable = \"t\"\ntitle = \"t\"\n" & body)

  proc j(w: Worklist; legacy: seq[Allow] = @[]): seq[string] =
    joinIds(w, @[], initHashSet[string](), ukeys, registered, dir, states, legacy)

  test "a closed row with an exact cell, a never cell, or a recording pin passes":
    check j(row("state = \"closed\"\ncells = [\"magic:Mod\"]\n")).len == 0
    check j(row("state = \"closed\"\ncells = [\"magic:Hash\"]\n")).len == 0
    check j(row("state = \"closed\"\npins = [\"tpin_writes\"]\n")).len == 0

  test "RED: a closed row naming nothing fails":
    let f = j(row("state = \"closed\"\n"))
    check f.len == 1 and "T-01" in f[0] and "closed-legacy" in f[0]

  test "RED: a closed row naming a declined (open-work) cell fails":
    let f = j(row("state = \"closed\"\ncells = [\"magic:Sort\", \"magic:Mod\"]\n"))
    check f.len == 1 and "declined" in f[0] and "magic:Sort" in f[0]

  test "RED: a closed row whose only pin writes no records fails":
    let f = j(row("state = \"closed\"\npins = [\"tpin_silent\"]\n"))
    check f.len == 1 and "write no pin records" in f[0]
    check j(row("state = \"closed\"\npins = [\"tpin_silent\", \"tpin_writes\"]\n")).len == 0

  test "RED: a never row with no never cell fails":
    let f = j(row("state = \"never\"\nnever_reason = \"nrByDesign\"\ncells = [\"magic:Mod\"]\n"))
    check f.len == 1 and "no `never` cell" in f[0]
    check j(row("state = \"never\"\nnever_reason = \"nrByDesign\"\n")).len == 1

  test "RED: a never_reason outside the enum fails":
    let f = j(row("state = \"never\"\nnever_reason = \"stays by design\"\ncells = [\"magic:Hash\"]\n"))
    check f.len == 1 and "NeverReason" in f[0]
    check j(row("state = \"never\"\nnever_reason = \"nrTheory\"\ncells = [\"magic:Hash\"]\n")).len == 0
    check j(row("state = \"never\"\ncells = [\"magic:Hash\"]\n")).len == 1

  test "the legacy list covers a bare closed row, and ratchets out":
    let a = Allow(key: "T-01", reason: "pre-K9")
    check j(row("state = \"closed\"\n"), @[a]).len == 0
    let f = j(row("state = \"closed\"\ncells = [\"magic:Mod\"]\n"), @[a])
    check f.len == 1 and "stale" in f[0]
    check j(row("state = \"open\"\n"), @[a]).anyIt("stale" in it)
    check j(row("state = \"closed\"\n"), @[Allow(key: "T-01")]).anyIt("no reason" in it)
    check j(row("state = \"closed\"\n"), @[Allow(key: "Z-9", reason: "r")]).anyIt("Z-9" in it)

  test "callsVerb is a whole-word match":
    check callsVerb("  pinNever(k, true, \"x\")")
    check not callsVerb("let myskipCellx = 1")
    check not callsVerb("# no verbs here")
