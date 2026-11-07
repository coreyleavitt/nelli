## RFC-0016 W1-d3 -- undefined behaviour rides the path and the verdict
## (section 9.1 item 4). The `{.noinit.}` read of an unwritten slot records
## `ubIndeterminateRead` on the reading path; the winner's set becomes
## `Soundness.witnessUndefined`, which replay cannot lift: not `trusted()`,
## not run in the host. Codec version 4 carries it as the sixth field.
import std/[unittest, strutils, tables, options]
import nelli
import nelli/symex
import nelli/db
import nelli/smt/[types, dsl, runtime, canonicalize, replayproc]
import nelli/engine/types
import ./s8cu_helpers

proc scrub() {.noinline.} =
  ## Called by the harness (never walked): zero the stack below the caller,
  ## where the replay's frames land, so the `{.noinit.}` slot reads zero
  ## natively.
  var a {.volatile.}: array[8192, int]
  for i in 0 ..< a.len: a[i] = 0

proc sutNoinitRead() =
  var x {.noinit.}: int
  if x == 0: symexTarget("z")

proc sutNoinitWritten() =
  var y {.noinit.}: int
  y = 5
  if y == 5: symexTarget("w")

proc sutUDivWitness(k: uint64) =
  ## A defined path reaches the label; the zero divisor is a halted side.
  let r = 10'u64 div k
  if r == 5: symexTarget("hit")

suite "W1-d3 the noinit read":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 281

  test "read of an unwritten slot: confirmed, not trusted, not host-run":
    scrub()
    let r = symexFind(sutNoinitRead, tLabel("z"))
    checkpoint show(r.errors) & " " & $r.soundness
    check not r.trusted
    when defined(cpp) or replayReexecs:
      ## The scrubbed slot is not zero in the cpp build's replay frames (a
      ## different stack layout), nor in a re-executed replay's child (a fresh
      ## stack the host's `scrub` never touched; Windows, or
      ## `-d:nelliReplayReexec`), so the replay refutes the witness: the
      ## claim stays unconfirmed, which is the same untrusted outcome.
      check r.status in {sxSat, sxUnknown}
      if r.status == sxSat:
        check r.soundness.undefinedKinds == {UbKind(ubIndeterminateRead)}
        check not hostRunnable(r.soundness)
    else:
      check r.status == sxSat
      check r.soundness.replay == rsConfirmed
      check r.soundness.undefinedKinds == {UbKind(ubIndeterminateRead)}
      check scSpurious in r.soundness.pathTaint
      check not hostRunnable(r.soundness)

  test "written before the read stays trusted":
    let r = symexFind(sutNoinitWritten, tLabel("w"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.soundness.witnessUndefined == {}
    check r.trusted
    check hostRunnable(r.soundness)

  test "a halted undefined side does not reach the winner":
    ## Halted paths are terminal and parked nowhere, so a winner through an
    ## undefined op carries nothing: the defined path is clean.
    let r = symexFind(sutUDivWitness, tLabel("hit"))
    check r.status == sxSat
    check r.soundness.witnessUndefined == {}
    check r.trusted

suite "W1-d3 Soundness.witnessUndefined gates":
  test "trustedSat and hostRunnable require it empty":
    var s = Soundness(replay: rsConfirmed, pathTaint: {scSpurious})
    check trustedSat(s)
    check hostRunnable(s)
    s.witnessUndefined = ubOrdinals({UbKind(ubIndeterminateRead)})
    check not trustedSat(s)
    check not hostRunnable(s)
    var clean = Soundness(replay: rsNotNeeded)
    clean.witnessUndefined = ubOrdinals({UbKind(ubUnsignedDivZero)})
    check not trustedSat(clean)

  test "ubOrdinals round-trips every kind":
    for k in UbKind:
      var s = Soundness()
      s.witnessUndefined = ubOrdinals({k})
      check s.undefinedKinds == {k}
    check ubOrdinals({UbKind(ubUnsignedDivZero)}) == {UbOrdinal(0)}
    check ubOrdinals({UbKind(ubIndeterminateRead)}) == {UbOrdinal(4)}

let w1d3Prog = SymexProgram(body: mkBlock(@[]))
let w1d3Target = tLabel("w1d3_codec")

proc w1d3Fn(x: int) =
  if x == 42: symexTarget("w1d3_codec")

suite "W1-d3 soundness codec version 4":
  test "witnessUndefined with a bitmask of 10 or more round-trips":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    var s = Soundness(replay: rsConfirmed, pathTaint: {scSpurious},
                      runDependence: {rdReplay})
    s.witnessUndefined = ubOrdinals({UbKind(ubSignedOverflow),
                                     UbKind(ubIndeterminateRead)})
    ## bits 2 and 4: the field is "20", two digits.
    let finding = SymexFinding(status: sfSat, witnessChoices: @[],
                               soundness: s)
    saveSymexWitnessImpl(db, w1d3Prog, w1d3Target,
                         defaultSymexSettings(), finding, errors)
    check errors.len == 0
    let loaded = loadSymexWitnessesImpl(db, w1d3Prog, w1d3Target,
                                        defaultSymexSettings(), errors)
    check loaded.len == 1
    check loaded[0].soundness == s
    check loaded[0].soundness.undefinedKinds ==
          {UbKind(ubSignedOverflow), UbKind(ubIndeterminateRead)}

  test "every kind alone round-trips; the full set too":
    for k in UbKind:
      let db = inMemoryDatabase()
      var errors: seq[string] = @[]
      var s = Soundness(replay: rsConfirmed, pathTaint: {scSpurious})
      s.witnessUndefined = ubOrdinals({k})
      saveSymexWitnessImpl(db, w1d3Prog, w1d3Target,
                           defaultSymexSettings(),
                           SymexFinding(status: sfSat, witnessChoices: @[],
                                        soundness: s), errors)
      let loaded = loadSymexWitnessesImpl(db, w1d3Prog, w1d3Target,
                                          defaultSymexSettings(), errors)
      check loaded.len == 1
      check loaded[0].soundness == s

  test "a version 3 record is a miss, not an error":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    let key = symexCacheKeyForFn(w1d3Fn, tLabel("w1d3_codec"),
                                 defaultSymexSettings())
    db.save(key & cacheKeySat, @[], {"soundness": "3:0:0:1:0"}.toTable, 64)
    let loaded = loadSymexWitnesses(db, w1d3Fn, tLabel("w1d3_codec"),
                                    defaultSymexSettings())
    check loaded.len == 0
    errors = @[]

  test "malformed sixth fields are misses":
    for bad in ["4:0:0:1:0", "4:0:0:1:0:", "4:0:0:1:0:05", "4:0:0:1:0:a",
                "4:0:0:1:0:64", "4:0:0:1:0:99999999999", "4:0:0:1:0:0:0",
                "4:0:0:1:0:0:9", "4:0:0:1:0:0:1:0"]:
      let db = inMemoryDatabase()
      let key = symexCacheKeyForFn(w1d3Fn, tLabel("w1d3_codec"),
                                   defaultSymexSettings())
      db.save(key & cacheKeySat, @[], {"soundness": bad}.toTable, 64)
      let loaded = loadSymexWitnesses(db, w1d3Fn, tLabel("w1d3_codec"),
                                      defaultSymexSettings())
      checkpoint bad
      check loaded.len == 0
