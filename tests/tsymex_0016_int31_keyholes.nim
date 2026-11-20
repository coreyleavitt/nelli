## RFC-0016 INT-31 (W-18): the verdict cache never serves a stale claim after a
## body the key does not read changes.
##
## A cached `rsConfirmed`, `witnessUnsafe` or `:raised` claim is a fact about
## the real `fn`, which a replay ran, and so about every routine `fn` reaches
## natively. `;impl=` (R1-09) keyed the source of the user routines `fn` names,
## and left four holes (`docs/migration/0.9.1.md`): the external body of an
## `importc` routine, the callees of a method's overrides, the target of a call
## through a proc value, and the compiler's `lib/`. Each pair of helper modules
## below holds the same SUT; only a body behind one of those differs. The
## second module, run against the first one's database, must never be served a
## witness that does not reach its target natively in the second module.
##
## RED before the fix: the `importc`, the override and the proc-value pairs
## were each served the first module's witness from the cache, and that witness
## misses the target in the second.
##
## A `{.push.}` inside `fn` itself is not keyed either (the key reads the check
## options a routine is defined under). The walk declines such a body
## (`feCheckOption`), so no trusted claim is made of it, and none is cached.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import nelli/smt/[types, dsl]
import nelli/db
from nelli/smt/symex_cache import replayedUnknown
import nelli/engine/types as engineTypes
from nelli/smt/admission import cellKey, axConstruct
from nelli/smt/replayproc import replayForks
from ./s8cu_helpers import pinNever, show, named
import ./int31_ffi_a as fa
import ./int31_ffi_b as fb
import ./int31_meth_a as ma
import ./int31_meth_b as mb
import ./int31_pv_a as pa
import ./int31_pv_b as pb

const cell = cellKey(axConstruct, "cache/key/impl")

proc firstInt(f: SymexFinding): int =
  for n in f.witnessChoices:
    if n.kind == ckInteger: return int(n.intVal.toInt64)
  doAssert false, "no integer choice in " & $f.witnessChoices

func claim(f: SymexFinding): string =
  ## What a finding says about the program, without where it came from.
  f.targetDesc & "|" & $f.status & "|" & $f.soundness.replay & "|" &
    $f.soundness.witnessUnsafe

template neverStale(sutA, sutB: untyped; settled = true) =
  ## `sutA`'s run fills the database; in `sutB` the same witness ends the
  ## process. Its run against that database may be served only the claim a
  ## cold run of `sutB` makes: a cached claim about another body is stale.
  ##
  ## Where a replay forks (Linux, macOS), `sutA`'s claim is replay-confirmed
  ## and safe, which is the claim INT-31 kept from being served to `sutB`.
  ## Where it re-executes (Windows, `-d:nelliReplayReexec`), the child cannot
  ## be handed a foreign routine or a proc value's target, so the replay is
  ## refused (`rsRefused`): a claim that never ran the body, and that a cold
  ## run of `sutB` makes as well.
  let db = inMemoryDatabase()
  let first = symexFindAllWitnesses(sutA, db)
  checkpoint "first: " & $first
  var cold, refused = false
  for f in first:
    if f.status == sfSat and f.soundness.replay == rsConfirmed and
       not f.soundness.witnessUnsafe: cold = true
    if f.status == sfSat and f.soundness.replay == rsRefused: refused = true
  # `settled = false`: the walk itself declines the SUT (its routes run code
  # it cannot read), so no claim about the body is ever made, nor cached.
  check cold == (settled and replayForks)
  check refused == (settled and not replayForks)
  let second = symexFindAllWitnesses(sutB, db)
  checkpoint "second: " & $second
  let fresh = symexFindAllWitnesses(sutB, inMemoryDatabase())
  checkpoint "cold second: " & $fresh
  var coldClaims: seq[string]
  for f in fresh: coldClaims.add f.claim
  var stale = false
  for f in second:
    if f.status == sfSat and f.fromCache and f.claim notin coldClaims:
      stale = true
  check not stale
  pinNever(cell, not stale, "a stale cached claim after a body change")

suite "INT-31: the cache never serves a claim about another body":

  test "the C body behind an importc callee":
    neverStale(fa.sutF, fb.sutF)

  test "the callees of a method's override":
    neverStale(ma.sutM, mb.sutM, settled = false)

  test "the routine a global let proc value holds":
    neverStale(pa.sutL, pb.sutL)

  test "the routine a global var proc value holds":
    neverStale(pa.sutV, pb.sutV, settled = false)

proc sutPush(x: int8) =
  var y = x
  {.push overflowChecks: off.}
  y = y + 100
  {.pop.}
  if y < 0: symexTarget("p")

proc sutNoPush(x: int8) =
  var y = x
  y = y + 100
  if y < 0: symexTarget("p")

proc noPushHits(x: int8): bool =
  try:
    var y = x
    y = y + 100
    y < 0
  except OverflowDefect:
    false

suite "INT-31: a push inside fn":

  test "the walk makes no trusted claim the pushed body does not hold":
    let r = symexFind(sutPush, tLabel("p"))
    checkpoint $r.status & " " & r.errors.show
    if r.status == sxSat and r.trusted:
      var y = r.witness[0]
      {.push overflowChecks: off.}
      y = y + 100
      {.pop.}
      check y < 0

  test "a claim about the pushed body is not served to the unpushed one":
    let db = inMemoryDatabase()
    discard symexFindAllWitnesses(sutPush, db)
    let second = symexFindAllWitnesses(sutNoPush, db)
    checkpoint $second
    var stale = false
    for f in second:
      if f.status == sfSat and f.fromCache and not noPushHits(int8(firstInt(f))):
        stale = true
    check not stale
    pinNever(cell, not stale, "a cached claim about a pushed body")

suite "INT-31: an unknown reached through a replay of an open body":

  test "is not stored; one the key can see, or no replay made, is":
    let open = SymexProgram(body: mkBlock(@[]), implOpen: "importc int31Set")
    let closed = SymexProgram(body: mkBlock(@[]))
    let refuted = @[FindingHint(kind: feReplayRefuted, severity: sevHint,
                                msg: "r")]
    var errors: seq[string]
    let db = inMemoryDatabase()
    let t = tAssertionViolation()
    # An unknown a replay refuted, against a body the key cannot see.
    check not saveSymexVerdictImpl(db, open, t, defaultSymexSettings(),
      sfUnknown, Soundness(runTaint: {scIncomplete}), errors, @[], refuted)
    check loadSymexVerdictImpl(db, open, t, defaultSymexSettings(),
                               errors).isNone
    # The same unknown where the key sees every body: stored.
    check saveSymexVerdictImpl(db, closed, t, defaultSymexSettings(),
      sfUnknown, Soundness(runTaint: {scIncomplete}), errors, @[], refuted)
    # An unknown no replay shaped, on the open program: stored.
    check saveSymexVerdictImpl(db, open, t, defaultSymexSettings(),
      sfUnknown, Soundness(runTaint: {scIncomplete}), errors, @[], @[])
    check errors.len == 0
    pinNever(cell, replayedUnknown(open, refuted) and
                   not replayedUnknown(closed, refuted) and
                   not replayedUnknown(open, @[]),
      "an unknown a replay decided against a body the key cannot see is not cached")
