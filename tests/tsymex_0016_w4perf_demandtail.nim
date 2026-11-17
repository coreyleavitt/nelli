## RFC-0016 W4 perf -- a replay candidate's tail is walked when a replay
## confirms it, and only then.
##
## The nightly's 60 s ceiling ratchet (record times 2.5) failed on the `n36`
## pair-loop family (`tsymex_r6_n36_raise_degrade`, `_d`,
## `tsymex_rfc0005_s1c_verdict`, `tsymex_rfc0005_s8ag_indexsplit_c`), bisected
## to the merge of W3-z R2 (7dbb8566): every `sxSat` label candidate's tail was
## walked before any replay ran. The pair-loop run hands out five candidates
## with distinct pins whose tails spent 1030, 125K, 1.9M, 15.0M and 82.9M
## units, the run's whole 100M tail budget, and no replay confirmed any of
## them: the verdict stayed `sxUnknown`, and the kinds those walks found were
## read by nothing.
##
## What R2 owes: a replay-confirmed candidate's verdict carries the kinds its
## tail is not shown defined in (`settleCandidate`). The kinds of a candidate
## no replay confirms reach no verdict, no finding and no ledger. So the run
## replays its candidates first, in the settle's order, and walks the tail of
## the one a replay confirms; a candidate it does not walk fails closed
## (`ubTailUnverified`), so nothing can settle it as a defined claim.
##
## The contract these pins hold, by count: a run makes one candidate tail
## walk per confirmed candidate, which is at most one.
import std/[unittest, strutils, os]
import nelli
import nelli/symex
import nelli/smt/runtime
import ./s8cu_helpers

# Built with `--overflowChecks:off` (its `.nim.cfg`), as the R2 suite is: a
# signed overflow is `ubSignedOverflow`.

var freshGlobal = false
  ## A module-level `var` nothing writes: a fresh symbol at its read
  ## (`feGlobalHavoc`, `dcFreshSymbol`) that really holds false.

proc freshFalse(a: bool): bool {.inline.} = freshGlobal and (a or not a)

proc allRefuted(a: bool; x: int64): int64 =
  ## Two candidates with distinct pins (`x = 1`, `x = 2`), both on the arm
  ## the fresh symbol opens and the real run never takes: replay refutes both.
  let o = freshFalse(a)
  if o:
    if x == 1:
      symexTarget("hit")
    if x == 2:
      symexTarget("hit")
  result = x + 1

proc oneConfirmed(a: bool; x: int64): int64 =
  ## A refuted candidate (`x = 1`) beside one the replay confirms (`x = 7`),
  ## whose tail overflows.
  let o = freshFalse(a)
  if o:
    if x == 1:
      symexTarget("hit")
  else:
    if x == 7:
      symexTarget("hit")
  result = x + high(int64)

proc tailUnitLines(log: string): seq[int] =
  ## The units of each tail walk (`k10b-tail` lines of the K7 units log).
  for line in readFile(log).splitLines:
    let f = line.split('\t')
    if f.len >= 2 and f[1] == "k10b-tail": result.add parseInt(f[0])

template tailWalks(fn: typed; tag: static string; res: untyped): seq[int] =
  let log = getTempDir() / ("w4demand_" & tag & "_" & $getCurrentProcessId() & ".log")
  removeFile(log)
  putEnv(walkUnitsLogEnv, log)
  let res = try: symexFind(fn, tLabel("hit"), pinSettingsConst)
            finally: delEnv(walkUnitsLogEnv)
  let tails = if fileExists(log): tailUnitLines(log) else: @[]
  removeFile(log)
  checkpoint tag & " " & $res.status & " tail walks: " & $tails
  checkpoint show(res.errors)
  tails

suite "RFC-0016 W4 perf: a candidate's tail is walked when a replay confirms it":

  test "walker 378: the version floor":
    check parseInt(symexWalkerVersion) >= 378

  test "no replay confirms a candidate: no tail is walked":
    # Red at dda778a7: two walks, one per distinct pins.
    let tails = tailWalks(allRefuted, "refuted", r)
    check r.status == sxUnknown
    check tails.len == 0

  test "one candidate confirmed: its tail alone is walked, and its kinds stand":
    # Red at dda778a7: two walks, the refuted candidate's too.
    let tails = tailWalks(oneConfirmed, "confirmed", r)
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check r.witness[1] == 7
    check not r.trusted
    check r.soundness.undefinedKinds == {UbKind(ubSignedOverflow)}
    check tails.len == 1
