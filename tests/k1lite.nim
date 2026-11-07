## RFC-0016 K1-0 -- the load-bearing property on Wave 1's cells, as a join.
##
## File name. The RFC's K1-0 row names `tests/tsymex_0016_k1lite.nim`. It is
## `tests/k1lite.nim` instead, outside the `t*.nim` globs: this join is
## meaningless alone (it needs the records of seven other suites from one run),
## yet the per-file runners (`scripts/sweep.sh`, the fuzzer-msvc W1-m glob of
## `tests/tsymex_0016_*.nim`, symex-mingw's per-file corpus from `nelli.nimble`)
## would run it with no pin directory and fail it. It runs only through
## `scripts/k1lite.sh`, which the symex-linux workflow calls on every run.
##
## The property (section 8): every trusted definite verdict a consumer can
## obtain through a public entry point has been reproduced natively on this
## build row, or its cell declines. K9a's pin record is the evidence; this is
## the `K1a-lite` check: the seven section 5.0 rows (W-01 .. W-07) each name
## the cell key(s) their W1 slice pinned, and each key must have an `exact`
## (`pvExact`, `pvRaised`) or `declined` (`pvDeclined`) record in the records
## directory, written by THIS build row.
##
## Where the records come from. The join reads `$NELLI_PIN_DIR`, which MUST be
## set and MUST hold the records of the W1 suites run on this build row in one
## go: `scripts/k1lite.sh [-b c|cpp] [-i z3-4.13.4]` makes a fresh directory, runs
## the W1 suites into it and then this test; that is the property on one build
## row. Do not run this file bare. There is no default directory (the in-repo `tests/.pins/` is
## shared across runs, and a record from an older run would satisfy the join).
## An unset, missing or empty directory FAILS; it never skips.
##
## Run scope. A record counts only when its build segment names this test's
## backend and Z3 version. Suites differ in other flags on purpose (`--panics:on`
## for W-03, `--overflowChecks:off` for W-05/W-07), so the rest of the segment
## is not compared. A record from another backend or Z3 version is not
## evidence for this row; it makes the join fail as foreign (a mixed directory
## is a stale one).
##
## Crash records. `pinCrash` bypasses every public entry point (section 8.4:
## "declined/never only"), so a crash record alone never satisfies a key. It
## is accepted alone in exactly one place: W-03, whose walker verdict is a
## crash-channel `sxRaised` (`witnessUnsafe`) that no in-process pin can
## execute, so no `exact` record can exist; the walker half is asserted by
## `tsymex_0016_panics.nim` and the native half is the crash record.
import std/[unittest, os, strutils, sequtils]
import nelli
import nelli/symex
import ./s8cu_helpers

type
  Need = object
    key: CellKey
    crashOk: bool        ## a crash record alone is enough (W-03 only)
  Row = object
    id, slice: string
    needs: seq[Need]

proc need(k: CellKey; crashOk = false): Need = Need(key: k, crashOk: crashOk)

let rows = @[
  Row(id: "W-01", slice: "W1-a", needs: @[
    need(cellKey(axConstruct, "except-as-label")),
    need(cellKey(axConstruct, "except-as-raise"))]),
  Row(id: "W-02", slice: "W1-b", needs: @[
    need(cellKey(axPragma, "local/cursor"))]),
  Row(id: "W-03", slice: "W1-c2", needs: @[
    need(cellKey(axConstruct, "panic-overflow-defect"), crashOk = true)]),
  Row(id: "W-04", slice: "W1-e", needs: @[
    need(cellKey(axConstruct, "conv/float32<-float64"))]),
  Row(id: "W-05", slice: "W1-d1a", needs: @[
    need(cellKey(axDefinedness, "mod/intMin/minusOne"))]),
  Row(id: "W-06", slice: "W1-d1b", needs: @[
    need(cellKey(axDefinedness, "div/unsigned/zero")),
    need(cellKey(axDefinedness, "mod/unsigned/zero"))]),
  Row(id: "W-07", slice: "W1-d2", needs: @[
    need(cellKey(axDefinedness, "add/signed/checksOff"))])]

proc buildRow(segment: string): string =
  ## The part of a build segment that names the build row: backend and Z3.
  var be = ""
  for tok in segment.split(';')[0].split('+'):
    if tok.startsWith("be="): be = tok
  let at = segment.find(";z3=")
  be & (if at >= 0: segment[at .. ^1] else: ";z3=?")

func isEvidence(v: PinVerdict): bool = v in {pvExact, pvRaised, pvDeclined}

proc joinRows(recs: seq[PinRecord]; rows: seq[Row]; here: string): seq[string] =
  ## One message per failing key, each naming the W row, the slice and the key;
  ## then one per foreign-build record. Empty: the property holds on `here`.
  if recs.len == 0:
    return @["no pin records at all: the W1 suites did not run into this directory"]
  for row in rows:
    for n in row.needs:
      let mine = recs.filterIt(it.cell == n.key and buildRow(it.build) == here)
      let ok = mine.anyIt(isEvidence(it.verdict)) or
               (n.crashOk and mine.anyIt(it.verdict == pvCrashed))
      if not ok:
        let seen = mine.mapIt($it.verdict).join(",")
        result.add row.id & " (" & row.slice & ") key " & render(n.key) &
          " has no exact or declined record on " & here &
          " (records here: " & (if seen.len == 0: "none" else: seen) & ")"
  for r in recs:
    if buildRow(r.build) != here:
      result.add "foreign record " & render(r.cell) & " from " &
        buildRow(r.build) & " in a directory for " & here

let
  here = buildRow(pinBuildSegment())
  dir = getEnv("NELLI_PIN_DIR", "")

proc loadRecords(): seq[PinRecord] =
  for r in pinRecords(dir): result.add r

proc without(recs: seq[PinRecord]; k: CellKey): seq[PinRecord] =
  recs.filterIt(it.cell != k)

proc named(msgs: seq[string]; id: string; k: CellKey): bool =
  msgs.anyIt(id in it and render(k) in it)

suite "K1-0: the seven section 5.0 rows have evidence on this build row":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 282

  test "the records directory is explicit and holds records":
    checkpoint "NELLI_PIN_DIR=" & dir & ": this file joins the records the W1 " &
      "suites wrote on this build; run it through scripts/k1lite.sh " &
      "never bare"
    check dir.len > 0
    check dirExists(dir)
    check loadRecords().len > 0

  test "the join on this build row (the property, K1-0)":
    let fails = joinRows(loadRecords(), rows, here)
    checkpoint fails.join("\n")
    check fails.len == 0

  test "each W row has at least one key":
    check rows.mapIt(it.id) == @["W-01", "W-02", "W-03", "W-04", "W-05",
                                 "W-06", "W-07"]
    for row in rows: check row.needs.len > 0

  test "RED: dropping any one key's records fails naming that key and row":
    let recs = loadRecords()
    for row in rows:
      for n in row.needs:
        let fails = joinRows(recs.without(n.key), rows, here)
        checkpoint row.id & " " & render(n.key) & ": " & fails.join(" | ")
        check fails.len == 1
        check fails.named(row.id, n.key)

  test "an empty directory fails":
    check joinRows(@[], rows, here).len == 1

  test "a crash record alone does not satisfy a declined row":
    let recs = loadRecords()
    let k = cellKey(axDefinedness, "mod/intMin/minusOne")
    check recs.anyIt(it.cell == k and it.verdict == pvCrashed)
    let crashOnly = recs.filterIt(it.cell != k or it.verdict == pvCrashed)
    check joinRows(crashOnly, rows, here).named("W-05", k)

  test "a crash record alone satisfies W-03, and only W-03":
    let recs = loadRecords()
    let k = cellKey(axConstruct, "panic-overflow-defect")
    let mine = recs.filterIt(it.cell == k)
    check mine.len > 0
    check mine.allIt(it.verdict == pvCrashed)
    check joinRows(recs, rows, here).len == 0
    check rows.filterIt(it.needs.anyIt(it.crashOk)).mapIt(it.id) == @["W-03"]

  test "a skipped record is not evidence":
    var recs = loadRecords()
    let k = cellKey(axPragma, "local/cursor")
    for r in recs.mitems:
      if r.cell == k: r.verdict = pvSkipped
    check joinRows(recs, rows, here).named("W-02", k)

  test "a record from another build row does not satisfy the join":
    var recs = loadRecords()
    let k = cellKey(axConstruct, "conv/float32<-float64")
    for r in recs.mitems:
      if r.cell == k: r.build = r.build.replace("+be=", "+be=other")
    let fails = joinRows(recs, rows, here)
    check fails.named("W-04", k)
    check fails.anyIt("foreign record" in it)
