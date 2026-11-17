## RFC-0016 W4 perf -- a tail walk's branch asks carry only the pools they reach.
##
## The nightly's 60 s ceiling ratchet (record times 2.5) went red on
## 2026-11-09 and stayed red: `tsymex_rfc0005_s8cf_point_b` (cpp 63.8 s ->
## 358 s), `tsymex_r6_n36_raise_degrade_d` (cpp 92.8 s record -> 359.8 s),
## `tsymex_r6_n36_raise_degrade`, `tsymex_rfc0005_s1c_verdict`,
## `tsymex_rfc0005_s8ag_indexsplit_c`. Bisected over main's first parent from
## 3fbb1676: the time arrives with the K10b tail walk (d428e924..03365b35) and
## grows with the replay candidates' tail walks (W3-z R2).
##
## The mechanism: the tail walk decides each branch with two scratch asks
## under the witness's pins (`concreteBranchAsk`), and each ask carried every
## run-wide pool (`globalRoots`): every regex definition, strip and index
## split the run had lowered, all over the subject string the pins fix to a
## ground value. With `s = "abcde"` pinned, `if s == "abcde"` spent the whole
## 20M-unit bound of one scratch check undecided because of three
## `findBounds` definitions it never reads; `s8cf_point_b` spent 60M and 80M
## units of tail walk where its explore walks spent 111K.
##
## The contract these pins hold, by count rather than wall time: a tail walk
## over a subject the pins fix decides its branches without a capped scratch
## check, so its units stay under one check's bound.
##
## Not covered here: the `n36` pair-loop family (`tsymex_r6_n36_raise_degrade`,
## `_d`, `tsymex_rfc0005_s1c_verdict`, `tsymex_rfc0005_s8ag_indexsplit_c`).
## Their replay candidates' tails (W3-z R2) spend the run's whole 100M-unit
## tail budget on asks that genuinely need the chained index splits of the
## pinned subject (13-16M units each); slicing does not shrink them. No
## replay confirms any of those candidates, so walker 378 walks none of
## their tails (`tsymex_0016_w4perf_demandtail`).
import std/[unittest, re, strutils, os]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/walk_log

proc tailUnitLines(log: string): seq[int] =
  ## The units of each tail walk (`k10b-tail` lines of the K7 units log).
  for line in readFile(log).splitLines:
    let f = line.split('\t')
    if f.len >= 2 and f[1] == "k10b-tail": result.add parseInt(f[0])

template tailUnits(fn: typed; lbl: static string; outStatus: var SymexStatusKind): seq[int] =
  let log = getTempDir() / ("w4perf_" & lbl & "_" & $getCurrentProcessId() & ".log")
  removeFile(log)
  putEnv(walkUnitsLogEnv, log)
  let r = try: symexFind(fn, tLabel(lbl))
          finally: delEnv(walkUnitsLogEnv)
  outStatus = r.status
  let tails = if fileExists(log): tailUnitLines(log) else: @[]
  removeFile(log)
  checkpoint lbl & " " & $r.status & " tail walk units: " & $tails
  tails

proc lastPinned(s: string) =
  if s == "abcde" and s.findBounds(re"(*UTF)(*ANY).+").last == 4:
    symexTarget("w4_last_pinned")

proc boundsPinned(s: string) =
  if s == "abcde":
    let b = s.findBounds(re"(*UTF)(*ANY).+")
    if b.first == 0 and b.last == 4:
      symexTarget("w4_bounds_pinned")

let oneCheck = int(concreteBranchRLimit(defaultSymexSettings()))

suite "RFC-0016 W4 perf: a tail walk's asks carry only the pools they reach":

  test "walker 377: the version floor":
    check parseInt(symexWalkerVersion) >= 377

  test "a pinned subject's tail decides its branches without a capped check":
    # Red at main 822f0fe6 (cpp, Z3 5.1): one tail walk of 41,095,494 units,
    # capped asks, where the explore walk spent about 111K.
    var st: SymexStatusKind
    let tails = tailUnits(lastPinned, "w4_last_pinned", st)
    check st == sxSat
    check tails.len == 1
    for u in tails: check u < oneCheck

  test "two findBounds reads of a pinned subject: still no capped check":
    # Red at main 822f0fe6 (cpp, Z3 5.1): 72,397,699 units, capped asks.
    var st: SymexStatusKind
    let tails = tailUnits(boundsPinned, "w4_bounds_pinned", st)
    check st == sxSat
    check tails.len == 1
    for u in tails: check u < oneCheck

