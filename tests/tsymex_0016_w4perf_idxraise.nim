## W4 perf: an in-bounds `s[i]` read inside a loop forks an `IndexDefect`
## raise arm, and that arm was solved by a full `trySolve` (`routeRaise`)
## even when the path's own facts make it infeasible (a loop guard
## `i < s.len` beside a read `s[i]`: the out-of-container side is UNSAT).
## `indexOobSide` now asks the bounded feasibility check the loop guards use
## (`loopArmInfeasible`) first, and drops an arm it refutes; an undecided
## check keeps the arm. This file pins (1) the number of Z3 searches of a
## small in-bounds loop read, (2) that an out-of-bounds read still raises
## `IndexDefect`, (3) that an index whose bound the path does not decide
## still forks the raise arm, and (4) the version floor.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sumLoop(s: seq[int]; k: int) =
  ## Every read is in bounds: the guard decides it.
  var i = 0
  var acc = 0
  while i < s.len:
    acc += s[i]
    inc i
  if s.len >= 0: symexTarget("hit")

proc oobRead(s: seq[int]; k: int) =
  ## No bound on `k`: the read raises.
  if s[k] == 7: symexTarget("hit")

proc halfGuarded(s: seq[int]; k: int) =
  ## The path decides `k >= 0` and nothing about `k < s.len`.
  if k >= 0:
    if s[k] == 7: symexTarget("hit")

suite "W4 perf: an infeasible IndexDefect arm is dropped without a full solve":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 491

  test "an in-bounds loop read costs a bounded number of searches":
    symexZ3CallCount = 0
    let r = pinFind(sumLoop, tLabel("hit"))
    echo "IDXRAISE searches ", symexZ3CallCount
    check r.status == sxSat
    ## Before: 10 searches; after: 5 (the loop guards and the target).
    check symexZ3CallCount <= 5

  test "an out-of-bounds read still yields its IndexDefect raise":
    let r = pinFind(oobRead, tRaisedExn("IndexDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

  test "an index whose bound the path does not decide still forks the raise":
    let r = pinFind(halfGuarded, tRaisedExn("IndexDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
