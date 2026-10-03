## RFC-0005 (soundness channels) slice S8bm -- step 1's search is
## independent of S8ay's facts-first check.
##
## Pinned here (the RFC's "As landed (S8bm)" note has the mechanism and
## the measurements):
##   (1) Z3's search on a walker query follows what the walk's shared
##       context already holds: one unrelated constant created before
##       B1-1's target query moved its step-1 search from 172,215 units to
##       5,280,185 (Z3 5.1). S8ay's facts-first check is one such
##       perturbation (3,365,417 units with it). Step 1 now searches in a
##       context of its own, so the same query costs the same with and
##       without a facts-first check before it;
##   (2) B1-1's byte test reads an element of a slice
##       (`str.at(str.substr(data, 4, ..), 0)`). It now takes its character
##       form, as a byte test on the string itself does: B1-1 is back under
##       a tight unit ceiling on both Z3 versions.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc opDataStyleSlice(data: seq[byte]) =
  ## S8ag's B1-1 probe (`tsymex_r6_b1_stringbacked`).
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  let payload = data[4 .. ^1]
  if payload.len > 3 and payload[0] == 42'u8:
    symexTarget("opdata_slice_sat")

proc walkB11(factsFirst: bool): tuple[status: SymexStatusKind,
                                      stats: seq[SymexQueryStat]] =
  ## B1-1's walk, recorded, with or without the facts-first check.
  symexQueryStats = @[]
  symexFactsFirstOff = not factsFirst
  let r = symexFind(opDataStyleSlice, tLabel("opdata_slice_sat"))
  symexFactsFirstOff = false
  checkpoint (if factsFirst: "with" else: "without") &
    " facts-first:\n" & symexQueryStatsSummary()
  result = (r.status, symexQueryStats)
  symexQueryStats = @[]

suite "S8bm (1): step 1 is independent of the facts-first check":

  test "B1-1's target query searches the same with and without it":
    let a = walkB11(factsFirst = true)
    let b = walkB11(factsFirst = false)
    check a.status == sxSat and b.status == sxSat
    check a.stats.len > 0 and b.stats.len > 0
    if a.stats.len > 0 and b.stats.len > 0:
      # The target query is the walk's last, SAT at step 1: the same text,
      # the same search.
      let qa = a.stats[^1]
      let qb = b.stats[^1]
      check qa.status == "sat" and qb.status == "sat"
      check qa.query == qb.query
      check qa.decisions == qb.decisions
      check qa.conflicts == qb.conflicts
      # Its units differ only by the facts-first check's own (about 4k on
      # Z3 5.1, 2k on 4.13.4: 28,573 against 24,693, and 63,126 against
      # 61,109). Before S8bm: 3,365,417 against 11,771,578 on 5.1.
      checkpoint "q10 units " & $qa.rlimitDelta & " / " & $qb.rlimitDelta
      check abs(qa.rlimitDelta - qb.rlimitDelta) * 4 <= qb.rlimitDelta

  test "a target hit's spend counts step 1's own context":
    ## `solveTargetHit` classifies a hit by what it spent (S8y's
    ## budget-out, S8ag's slow SAT), read from the walk context's counter
    ## (`rlimitCountNow`). Step 1's units are spent in a context of its
    ## own, so the reading adds them (`ownContextUnits`): without that, a
    ## hit whose step 1 ran out of budget read as cheap. B1-1's hit is its
    ## target query, SAT at step 1.
    symexTargetSolveStats = (budgetOut: 0, declined: 0, slowSat: 0, units: 0)
    let w = walkB11(factsFirst = true)
    check w.status == sxSat
    if w.stats.len > 0:
      checkpoint "hit units " & $symexTargetSolveStats.units & ", query " &
        $w.stats[^1].rlimitDelta
      check symexTargetSolveStats.units >= w.stats[^1].rlimitDelta

suite "S8bm (2): B1-1 under a tight unit ceiling":

  test "B1-1's byte test on a slice element is in character form":
    let w = walkB11(factsFirst = true)
    check w.status == sxSat
    var units = 0
    for q in w.stats: units += q.rlimitDelta
    checkpoint "units=" & $units
    if w.stats.len > 0:
      # The target query decides the byte test as a one-character string
      # equality, not as `int2bv(str.to_code(..)) == 42`.
      check "str.to_code" notin w.stats[^1].query
    ## A ceiling per linked Z3, about 2x the measurement on 621af8f + S8bm:
    ## 46,533 units on 5.1 and 79,494 on 4.13.4 (the same as the process's
    ## first walk and as its third). Before S8bm: 3,383,332 on 5.1 (and
    ## 11,786,591 as a process's second walk without facts-first) and
    ## 7,766,466 on 4.13.4 (25,652,149 as a process's only walk, its target
    ## query out of budget).
    let v = z3Version()
    if v.major >= 5: check units <= 100_000
    else: check units <= 160_000

suite "S8bm: walker version floor":

  test "symexWalkerVersion >= 214":
    check parseInt(symexWalkerVersion) >= 214
