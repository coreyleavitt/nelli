## RFC-0016 K10a-target -- undefined behaviour is a target and a finding:
## `stkUndefined` / `tUndefined(kinds)`, `UndefinedFinding`, `FindingUndefined`
## (section 9.1 item 5), and replay refusal by target kind (item 6).
##
## The producer is the existing `haltUndefined` site (W1-d1b: an unsigned
## division by zero); K10a-axis adds the rest of the definedness rows.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/db
import nelli/smt/replaywire
import ./s8cu_helpers

proc sutUDiv(k: uint64) =
  let r = 10'u64 div k
  if r == 11: symexTarget("hit")

proc sutUDivSat(k: uint64) =
  let r = 10'u64 div k
  if r == 5: symexTarget("hit")

proc sutUDivGuarded(k: uint64) =
  if k != 0:
    let r = 10'u64 div k
    if r == 5: symexTarget("hit")

proc sutDefined(k: uint64) =
  if k == 3: symexTarget("hit")

suite "K10a-target: tUndefined as a target":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 293

  test "the zero divisor is found: sxSat with a witness":
    let r = symexFind(sutUDiv, tUndefined())
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 0'u64
    check r.soundness.undefinedKinds == {UbKind(ubUnsignedDivZero)}
    check not r.trusted

  test "a listed kind that is not reachable is not a hit":
    let r = symexFind(sutUDiv, tUndefined({UbKind(ubIntMinModMinusOne)}))
    check r.status != sxSat
    check not r.trusted          # the halted zero side still voids a proof

  test "the listed kind is a hit":
    let r = symexFind(sutUDiv, tUndefined({UbKind(ubUnsignedDivZero)}))
    check r.status == sxSat
    check r.witness[0] == 0'u64

  test "a guarded op has no undefined side: trusted sxUnsat":
    let r = symexFind(sutUDivGuarded, tUndefined())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check r.trusted
    check r.undefined.len == 0

  test "a program with no undefined op is a trusted sxUnsat":
    let r = symexFind(sutDefined, tUndefined())
    check r.status == sxUnsat
    check r.trusted

  test "describeTarget renders the list":
    check describeTarget(tUndefined()) == "undefined(all)"
    check describeTarget(tUndefined({UbKind(ubSignedOverflow)})) ==
      "undefined(ubSignedOverflow)"

suite "K10a-target: UndefinedFinding under another target":
  test "a label search lists the undefined behaviour it reached":
    let r = symexFind(sutUDivSat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 2'u64
    check r.undefined.len == 1
    check r.undefined[0].kind == UbKind(ubUnsignedDivZero)
    check r.undefined[0].witness[0] == 0'u64
    check r.undefined[0].site.len > 0
    check r.diagnostics.len == 0   # typed for raised Defects only

  test "the halt names tUndefined as the next query":
    let r = symexFind(sutUDivSat, tLabel("hit"))
    var named = false
    for e in r.errors:
      if e.kind == ubUnsignedDivZero and "tUndefined" in e.msg: named = true
    check named

  test "a guarded op lists nothing":
    let r = symexFind(sutUDivGuarded, tLabel("hit"))
    check r.undefined.len == 0

suite "K10a-target: SymexFinding projection and cache":
  test "FindingUndefined, cold and served from the cache":
    let db = inMemoryDatabase()
    let cold = symexFindAllWitnesses(sutUDivSat, db)
    var found = false
    for f in cold:
      if f.targetDesc == "label(\"hit\")":
        found = true
        check f.undefined.len == 1
        check f.undefined[0].kind == "ubUnsignedDivZero"
        check f.undefined[0].witnessChoices.len > 0
        check not f.fromCache
    check found
    let warm = symexFindAllWitnesses(sutUDivSat, db)
    for f in warm:
      if f.targetDesc == "label(\"hit\")":
        check f.fromCache
        check f.undefined.len == 1
        check f.undefined[0].kind == "ubUnsignedDivZero"
        check f.undefined[0].witnessChoices.len > 0

suite "K10a-target: replay, cache key, wire":
  test "replay never runs a tUndefined witness":
    check not replayInScope(tUndefined())
    check replayInScope(tLabel("x"))

  test "the kind list is part of the cache key":
    let a = symexCacheKeyForFn(sutUDiv, tUndefined())
    let b = symexCacheKeyForFn(sutUDiv, tUndefined({UbKind(ubSignedOverflow)}))
    let c = symexCacheKeyForFn(sutUDiv, tUndefined())
    check a != b
    check a == c

  test "wire round trip keeps the kinds":
    var w = WireWriter()
    wireTarget(w, tUndefined({UbKind(ubSignedOverflow), UbKind(ubUnsignedDivZero)}))
    var rd = initWireReader(w.data)
    let t = readTarget(rd)
    check t.kind == stkUndefined
    check t.ubKinds == {UbKind(ubSignedOverflow), UbKind(ubUnsignedDivZero)}

  test "assertCoveredBy never runs the witness in the host":
    var failed = false
    try:
      assertCoveredBy(sutUDiv, tUndefined(), proc (k: uint64) = discard)
    except SymexCoverageDefect:
      failed = true
    check failed
