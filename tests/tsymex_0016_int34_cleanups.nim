## RFC-0016 INT-34 (0005 review R1-28, R4-08) and INT-38 (R8-04): design
## cleanups of the symex cache's records.
##
## * `FindingGap.kind`, `FindingHint.kind` and `FindingHint.severity` are the
##   `SymexErrorKind`/`SymexErrorSeverity` enums, not their names. The cache
##   still stores each by name, so a record written before reads back; a name
##   this build does not know is a miss (gaps) or ends the list (hints).
## * A key starts with the walker version that wrote it (`w416:`), not the
##   fixed `sx2:`: the version is what changes a key's meaning, and keeping it
##   in clear lets a sweep tell one version's records from another's.
## * `pruneForeignSymexRecords` (R8-04): an explicit, opt-in sweep of the
##   records of every other walker version (the `sx:`/`sx2:` keys before this
##   change among them, with their `:raised` slots). It reports how many it
##   removed. Nothing removes them on its own: a run leaves them in place.
import std/[unittest, options, strutils, tables, os]
import nelli
import nelli/symex
import nelli/db
import nelli/smt/[types, dsl, canonicalize]
import nelli/engine/types

const hex64 = repeat('a', 64)

proc int34Fn(x: int) =
  if x == 42: symexTarget("int34")

suite "INT-34: walker version floor":
  test "the key form changed at 416":
    check parseInt(symexWalkerVersion) >= 416

suite "INT-34 (1): gap and hint kinds are enums":
  test "the fields are the enums":
    check FindingGap().kind is SymexErrorKind
    check FindingHint().kind is SymexErrorKind
    check FindingHint().severity is SymexErrorSeverity

  test "a gaps record stored by name reads back as the enum":
    let db = inMemoryDatabase()
    let key = symexCacheKeyForFn(int34Fn, tLabel("int34"),
                                 defaultSymexSettings())
    var meta = {"soundness": "4:0:0:1:0:0", "gapsv": "1", "gapsn": "1",
                "gapsc0": "0", "gapsk0": "feOpaqueCallUnmodelled",
                "gapsm0": "m"}.toTable
    db.save(key & cacheKeyUnknown, @[], meta, verdictCacheMaxEntries)
    let hit = loadSymexVerdict(db, int34Fn, tLabel("int34"),
                               defaultSymexSettings())
    check hit.isSome
    check hit.get.gaps.len == 1
    check hit.get.gaps[0].kind == feOpaqueCallUnmodelled
    # A name this build does not know is a miss of the whole record.
    meta["gapsk0"] = "feNoSuchKind"
    db.save(key & cacheKeyUnknown, @[], meta, verdictCacheMaxEntries)
    check loadSymexVerdict(db, int34Fn, tLabel("int34"),
                           defaultSymexSettings()).isNone

  test "hints round-trip, and an unknown name ends the list":
    let db = inMemoryDatabase()
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    var errors: seq[string]
    let hs = @[FindingHint(kind: feReplayCrashed, severity: sevHint, msg: "a"),
               FindingHint(kind: seUnsupportedRegex, severity: sevWarning,
                           msg: "b")]
    saveSymexNotesImpl(db, prog, target, defaultSymexSettings(), hs, @[], @[],
                       errors)
    check errors.len == 0
    let got = loadSymexNotesImpl(db, prog, target, defaultSymexSettings(),
                                 errors)
    check got.hints == hs
    # The rendered text names the kind as before.
    var f = SymexFinding(status: sfUnknown, hints: hs,
                         gaps: @[FindingGap(class: dcNoAnswer,
                                            kind: beBudgetExhausted, msg: "g")])
    let r = Report[int](outcome: otPassed, symexFindings: @[f])
    let text = renderReport(r, ofText)
    check "hint feReplayCrashed: a" in text
    check "gap dcNoAnswer beBudgetExhausted: g" in text
    let json = renderReport(r, ofJson)
    check "\"kind\":\"seUnsupportedRegex\",\"severity\":\"sevWarning\"" in json
    # Tamper the second hint's kind: the list ends before it.
    let key = symexCacheKey(prog, target, defaultSymexSettings(),
      z3Version = z3FullVersion(), nimVersion = NimVersion,
      walkerVersion = symexWalkerVersion,
      renderingVersion = renderAsChoicesVersion) & ":notes"
    var head = db.loadPrimaryWithMeta(key)
    check head.len == 1
    var meta = head[0].meta
    meta["hintk1"] = "feNoSuchKind"
    db.save(key, @[], meta, verdictCacheMaxEntries)
    let cut = loadSymexNotesImpl(db, prog, target, defaultSymexSettings(),
                                 errors)
    check cut.hints == hs[0 .. 0]

suite "INT-34 (3): a key starts with its walker version":
  test "this build's keys":
    let key = symexCacheKeyForFn(int34Fn, tLabel("int34"),
                                 defaultSymexSettings())
    check symexCacheKeyPrefix == "w" & symexWalkerVersion & ":"
    check key.startsWith(symexCacheKeyPrefix)
    check key.len == symexCacheKeyPrefix.len + 64
    check not key.startsWith("sx")

  test "another walker version's keys":
    let prog = SymexProgram(body: mkBlock(@[]))
    let k = symexCacheKey(prog, tAssertionViolation(), defaultSymexSettings(),
      z3Version = "z", nimVersion = "n", walkerVersion = "415",
      renderingVersion = "1", buildSeg = "b")
    check k.startsWith(symexCacheKeyPrefixFor("415"))
    check symexCacheKeyPrefixFor("415") == "w415:"
    check walkerVersionOfKey(k) == some("415")
    check walkerVersionOfKey("sx2:" & hex64 & ":raised") == some("")
    check walkerVersionOfKey("myTestId").isNone

# =============================================================================
# R8-04: the opt-in prune
# =============================================================================

proc foreignKeys(): seq[string] =
  ## One record of each foreign shape: the keys before INT-34 (`sx:` over a
  ## SHA-1, `sx2:` over a SHA-256) with the `:raised` index and slot R8-04
  ## names, and a key of another walker version.
  let prog = SymexProgram(body: mkBlock(@[]))
  let older = symexCacheKey(prog, tAssertionViolation(),
    defaultSymexSettings(), z3Version = z3FullVersion(),
    nimVersion = NimVersion, walkerVersion = "415",
    renderingVersion = renderAsChoicesVersion)
  @["sx:" & repeat('b', 40) & ":sat",
    "sx2:" & hex64 & ":unknown",
    "sx2:" & hex64 & ":raised",
    "sx2:" & hex64 & ":raised:ValueError",
    "sx2:" & hex64 & ":raised2",
    older & ":unsat",
    older & ":raised2:IOError"]

proc seed(db: ExampleDatabase): seq[string] =
  ## Stores the foreign records, a record of this walker and a user test's
  ## entry; returns the keys of the last two.
  for k in foreignKeys():
    db.save(k, @[integerChoice(1, 0, 9, 0)], {"soundness": "x"}.toTable, 4)
  let mine = symexCacheKeyForFn(int34Fn, tLabel("int34"),
                                defaultSymexSettings()) & cacheKeyUnknown
  db.save(mine, @[], {"soundness": "4:0:0:1:0:0"}.toTable, 4)
  db.save("myTestId", @[integerChoice(3, 0, 9, 0)], 4)
  db.save("sx2-looking but not a key", @[integerChoice(4, 0, 9, 0)], 4)
  @[mine, "myTestId", "sx2-looking but not a key"]

proc checkPruned(db: ExampleDatabase) =
  let kept = seed(db)
  let removed = pruneForeignSymexRecords(db)
  check removed == foreignKeys().len
  for k in foreignKeys():
    check db.loadPrimary(k).len == 0
  for k in kept:
    check db.loadPrimary(k).len == 1
  # A second sweep finds nothing.
  check pruneForeignSymexRecords(db) == 0

suite "INT-38 (R8-04): pruning other walker versions' records is opt-in":
  test "the prune removes only foreign-version records (in memory)":
    checkPruned(inMemoryDatabase())

  test "the prune removes only foreign-version records (on disk)":
    let dir = getTempDir() / "nelli_int34_prune"
    removeDir(dir)
    checkPruned(directoryBasedDatabase(dir))
    # What it removed is gone from a fresh handle on the same directory.
    let again = directoryBasedDatabase(dir)
    for k in foreignKeys():
      check again.loadPrimary(k).len == 0
    removeDir(dir)

  test "a run removes no record of another walker version":
    let db = inMemoryDatabase()
    discard seed(db)
    discard symexFindAllWitnesses(int34Fn, db)
    for k in foreignKeys():
      check db.loadPrimary(k).len == 1

  test "a backend that cannot list its keys says so":
    var db = inMemoryDatabase()
    db.primaryKeysImpl = nil
    expect DbError:
      discard pruneForeignSymexRecords(db)
