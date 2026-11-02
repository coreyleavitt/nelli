## RFC-0005 S8cr: two gaps a definition-of-done audit found in §6 item 2.
##
## (a) The live cap-veto pin. §6 item 2 asks for "a clean-path witness plus a
##     `sevError` decline behind an unreachable branch". The S0 and S9 pins
##     stopped holding a `sevError` when S8bc began dropping a decline on a path
##     `pathInfeasible` refutes: S0 now asserts no `sevError` at all, so it would
##     pass if the decline vanished, and S9 checks only the kind. An unreachable
##     branch that the feasibility check cannot refute keeps its decline
##     at `sevError`, so that is the shape here.
##
## (b) `symexForAll`. It defers to `symexFindAllWitnesses`, which has the pins,
##     but nothing checked that through `symexForAll` itself: not a raise, not
##     `rsConfirmed`, not a veto companion.
import std/[unittest, options, sequtils, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

const noReplay = SymexSettings(replay: false)

# =============================================================================
# (a) a sevError cap decline behind an unreachable branch, beside a clean witness
# =============================================================================
#
# M61 = 2^61 - 1 is prime. Both factors are in (1, 2^32), so `a * b` cannot wrap
# and a product of two such factors is never M61: the branch has no execution.
# Refuting it is the factoring problem, which `pathInfeasible`'s budget of
# `loopPruneRLimit` (250,000 units) does not reach, so the path is kept, tainted,
# and the decline stays `sevError`. The branch returns, so no target solve runs
# on the tainted path.
const M61 = 2305843009213693951'u64
const twoTo32 = 1'u64 shl 32

proc capUnreached(x: int; a, b: uint64) =
  if a > 1'u64 and b > 1'u64 and a < twoTo32 and b < twoTo32 and a * b == M61:
    let y = cast[int32](x) + 1
    discard y
    return
  if x == 42:
    symexTarget("s8cr_cap_unreached")

proc capUnreachedDead(x: int; a, b: uint64) =
  ## The same decline with no witness to report.
  if a > 1'u64 and b > 1'u64 and a < twoTo32 and b < twoTo32 and a * b == M61:
    let y = cast[int32](x) + 1
    discard y
    return
  if x == 42 and x == 43:
    symexTarget("s8cr_cap_unreached_dead")

proc sevErrorKinds(r: auto): seq[SymexErrorKind] =
  for e in r.errors:
    if e.severity == sevError: result.add e.kind

suite "RFC-0005 S8cr (a) -- a live sevError cap decline beside a clean witness":

  test "oracle: no pair of in-range factors multiplies to M61":
    ## M61's only divisors are 1 and itself, so any product equal to it has a
    ## factor outside (1, 2^32). The small divisors are checked here, the rest
    ## is the primality of 2^61 - 1.
    check M61 == (1'u64 shl 61) - 1
    for d in 2'u64 .. 10_000'u64:
      check M61 mod d != 0

  test "symexFind: sxSat, the witness, and the decline AT sevError":
    let r = symexFind(capUnreached, tLabel("s8cr_cap_unreached"))
    for e in r.errors: checkpoint($e.kind & " sev=" & $e.severity & ": " & e.msg)
    check r.status == sxSat
    check r.witness[0] == 42
    # The severity is the pin. A `sevHint` here means the branch was refuted or
    # the decline demoted, and then this file no longer exhibits §6 item 2.
    check sevErrorKinds(r) == @[feUnsupportedExprKind, feUnsupportedExprKind]
    check r.errors.anyIt(it.kind == feUnsupportedExprKind and
                         it.severity == sevError and
                         it.scope.kind == dskSiteAnchored)

  test "the witness is clean: no taint on its path, no replay, trusted":
    let r = symexFind(capUnreached, tLabel("s8cr_cap_unreached"))
    check r.soundness.pathTaint == {}
    check r.soundness.replay == rsNotNeeded
    check r.trusted
    # The decline stays in the run's coordinate, reported by `gaps()`.
    check scIncomplete in r.soundness.runTaint
    check r.gaps.anyIt(it.e.kind == feUnsupportedExprKind)

  test "the decline is live: the same run with no witness cannot prove sxUnsat":
    let r = symexFind(capUnreachedDead, tLabel("s8cr_cap_unreached_dead"))
    for e in r.errors: checkpoint($e.kind & " sev=" & $e.severity & ": " & e.msg)
    check r.status == sxUnknown
    check feUnsupportedExprKind in sevErrorKinds(r)

# =============================================================================
# (b) symexForAll: a raise, rsConfirmed, and the veto companions, through it
# =============================================================================
#
# `a < a` on a bool is the fresh-symbol site `feUnsupportedOpHavoc`
# (`dcFreshSymbol`), and in reality it is always false, so each replay outcome
# is fixed whatever the solver picks.

proc faConfirm(a: bool) =
  let o = a < a
  if not o:
    symexTarget("s8cr_fa_confirm")

proc faRefute(a: bool) =
  let o = a < a
  if o:
    symexTarget("s8cr_fa_refute")

proc faRaiseConfirm(a: bool) =
  let o = a < a
  assert o, "s8cr raise"          # fails for real on every input

proc faRaiseRefute(a: bool) =
  let o = a < a
  assert not o, "s8cr raise"      # holds for real on every input

proc faCap(x, a, b: int) =
  ## §6 item 2's cap companion, as (a) has it, over `int`: both factors are
  ## in (1, 2^31), so the product fits and is never M61.
  if a > 1 and b > 1 and a < (1 shl 31) and b < (1 shl 31) and a * b == int(M61):
    let y = cast[int32](x) + 1
    discard y
    return
  if x == 42:
    symexTarget("s8cr_fa_cap")

proc faClosure(xs: seq[int]; x: int) =
  ## §6 item 2's closure companion: `filter` over a symbolic-length seq
  ## declines `ceUnsupportedHof`, on the `x == 7` path only.
  if x == 7:
    let kept = xs.filter(proc(v: int): bool = v > 0)
    discard kept
  if x == 42:
    symexTarget("s8cr_fa_closure")

proc faGrouped(x, y: int; flag: bool) =
  if x == 3 and y == 4 and flag:
    symexTarget("s8cr_fa_grouped")

proc findingFor(fs: seq[SymexFinding]; desc: string): Option[SymexFinding] =
  for f in fs:
    if f.targetDesc == desc: return some(f)
  none(SymexFinding)

const smallRun = Settings(maxExamples: 5)

suite "RFC-0005 S8cr (b) -- symexForAll's own replay pins":

  test "a confirmed candidate: sfSat, rsConfirmed, on a path that stays tainted":
    let rep = symexForAll(booleans(), faConfirm, inMemoryDatabase(),
                          forAllSettings = smallRun)
    let f = rep.symexFindings.findingFor("label(\"s8cr_fa_confirm\")")
    check f.isSome
    check f.get.status == sfSat
    check f.get.soundness.replay == rsConfirmed
    check scSpurious in f.get.soundness.pathTaint
    check not f.get.fromCache
    check f.get.trusted

  test "a refuted candidate: sfUnknown, replay never claimed":
    let rep = symexForAll(booleans(), faRefute, inMemoryDatabase(),
                          forAllSettings = smallRun)
    let f = rep.symexFindings.findingFor("label(\"s8cr_fa_refute\")")
    check f.isSome
    check f.get.status == sfUnknown
    check f.get.soundness.replay != rsConfirmed
    check not f.get.trusted

  test "a confirmed tainted raise: sfRaised, rsConfirmed":
    let rep = symexForAll(booleans(), faRaiseConfirm, inMemoryDatabase(),
                          forAllSettings = smallRun)
    let f = rep.symexFindings.findingFor("raised(AssertionDefect)")
    check f.isSome
    check f.get.status == sfRaised
    check f.get.defectTypeId == "AssertionDefect"
    check f.get.soundness.replay == rsConfirmed
    check scSpurious in f.get.soundness.pathTaint

  test "a refuted tainted raise reports no raise":
    let rep = symexForAll(booleans(), faRaiseRefute, inMemoryDatabase(),
                          forAllSettings = smallRun)
    checkpoint($rep.symexFindings)
    check rep.symexFindings.findingFor("raised(AssertionDefect)").isNone
    for f in rep.symexFindings:
      check f.status notin {sfSat, sfRaised}

  test "replay off: the confirmed candidate stays sfUnknown":
    let rep = symexForAll(booleans(), faConfirm, inMemoryDatabase(),
                          symexSettings = noReplay, forAllSettings = smallRun)
    let f = rep.symexFindings.findingFor("label(\"s8cr_fa_confirm\")")
    check f.isSome
    check f.get.status == sfUnknown

suite "RFC-0005 S8cr (b) -- symexForAll's veto companions":

  test "the cap companion: sfSat beside the live decline, no replay":
    let rep = symexForAll(map(integers(0, 100), integers(0, 100), integers(0, 100)),
                          faCap, inMemoryDatabase(), forAllSettings = smallRun)
    let f = rep.symexFindings.findingFor("label(\"s8cr_fa_cap\")")
    check f.isSome
    check f.get.status == sfSat
    check f.get.soundness.pathTaint == {}
    check f.get.soundness.replay == rsNotNeeded
    check f.get.gaps.anyIt(it.kind == "feUnsupportedExprKind")

  test "grouped parameters count one by one (`x, a, b: int` was a compile error)":
    ## `faCap` above declares three parameters in one group. `symexForAll`
    ## counted the group as one and passed `fn` unwrapped, so that call did
    ## not compile. Here is the grouped-and-ungrouped mix.
    let rep = symexForAll(map(integers(0, 100), integers(0, 100), booleans()),
                          faGrouped, inMemoryDatabase(),
                          forAllSettings = smallRun)
    let f = rep.symexFindings.findingFor("label(\"s8cr_fa_grouped\")")
    check f.isSome
    check f.get.status == sfSat

  test "the closure companion: sfSat beside the disjoint decline, no replay":
    let rep = symexForAll(map(lists(integers(0, 9), maxLen = 2), integers(0, 100)),
                          faClosure, inMemoryDatabase(),
                          forAllSettings = smallRun)
    let f = rep.symexFindings.findingFor("label(\"s8cr_fa_closure\")")
    check f.isSome
    check f.get.status == sfSat
    check f.get.soundness.pathTaint == {}
    check f.get.soundness.replay == rsNotNeeded
    check f.get.gaps.anyIt(it.kind == "ceUnsupportedHof")

suite "RFC-0005 S8cr (pins): walker version":
  test "symexWalkerVersion >= 245 (no walker change: this slice adds pins)":
    check parseInt(symexWalkerVersion) >= 245
