## RFC-0016 K10d. `SymexSettings.arithChecks` and `SymexResult.fromCache` are
## removed (not deprecated). The build alone decides which arithmetic checks
## a run models (`--overflowChecks`, `--rangeChecks`; K5a's profile and
## K10a-axis's definedness axis answer the unchecked side), so a setting that
## could disagree with it, and the `feCheckOption` taint that reported the
## disagreement, are gone. A cache hit is read from `SymexFinding.fromCache`.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc addOne(x: int8) =
  if x + 1 < x: symexTarget("wrapped")

suite "K10d: removed surface":
  test "SymexSettings has no arithChecks":
    check not compiles(defaultSymexSettings().arithChecks)
    check not compiles(SymexSettings(arithChecks: {}))

  test "SymexResult has no fromCache":
    check not compiles(symexFind(addOne, tLabel("wrapped")).fromCache)

  test "no setting can disagree with the build":
    check not compiles(arithChecksDisagree(defaultSymexSettings()))
    check not compiles(effectiveArithChecks(defaultSymexSettings()))

  test "canonical form carries no arithChecks key":
    check ";arithChecks=" notin canonicalize(defaultSymexSettings())

  test "defaults draw no incoherence warning":
    check validateSymexSettings(defaultSymexSettings()).len == 0

  test "version floor":
    check parseInt(symexWalkerVersion) >= 302

suite "K10d: behaviour follows the build":
  test "the default build models the checks it compiles in":
    let r = symexFind(addOne, tLabel("wrapped"))
    check r.status != sxSat
    check not r.errors.named(feCheckOption)

suite "K10d: cache hits are read from the finding":
  test "symexFindAllWitnesses reports a hit on the second call":
    let db = inMemoryDatabase()
    let cold = symexFindAllWitnesses(addOne, db)
    let warm = symexFindAllWitnesses(addOne, db)
    check cold.len == warm.len
    for f in cold: check not f.fromCache
    check warm.len == 0 or warm[0].fromCache
