## RFC-0005 review R1-01 -- an `elif` condition's preamble ran before the `if`.
##
## A condition is parsed into an expression plus a preamble: the statements
## that must run before it is tested (a seq bounds fork, a hoisted call, a
## defect fork). Every `if` lowering -- the statement arm, the value-position
## `nnkIfExpr` arm and the iterator-body arm -- appended EVERY condition's
## preamble ahead of the whole construct. A later condition's preamble then
## ran on the paths that take an earlier branch:
##
##   `if i >= s.len: <label> elif s[i] == 3: ...` forked `s[i]`'s IndexDefect
##   before `i >= s.len` was tested -- a trusted `sxRaised` with `s=@[], i=0`,
##   where native reaches the label;
##
##   `if a == 1: (if s.len == 0: <label>) elif bump(s): ...` ran `bump`'s
##   `s.add 1` before `a == 1`, so the label was a clean false `sxUnsat`.
##
## The lowering now nests: `if c1: A elif c2: B else: C` with a non-empty
## preamble for `c2` is `if c1: A else: (pre2; if c2: B else: C)`.
##
## Each row runs the routine natively beside the walk's verdict.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc stmtIdx(s: seq[int], i: int) =
  if i < 0: return
  if i >= s.len: symexTarget("hit")
  elif s[i] == 3: discard

proc valueIdx(s: seq[int], i: int) =
  if i < 0: return
  let y = if i >= s.len: 1 elif s[i] == 0: 2 else: 3
  if y == 1: symexTarget("hit")

proc bump(s: var seq[int]): bool =
  s.add 1
  true

proc stmtCall(a: int, s0: seq[int]) =
  var s = s0
  if a == 1:
    if s.len == 0: symexTarget("hit")
  elif bump(s): discard

proc valueCall(a: int, s0: seq[int]) =
  var s = s0
  let y = if a == 1: s.len elif bump(s): 7 else: 8
  if a == 1 and y == 0: symexTarget("hit")

iterator pick(s: seq[int], i: int): int =
  if i >= s.len: yield 1
  elif s[i] == 3: yield 2

proc iterIdx(s: seq[int], i: int) =
  if i < 0: return
  for v in pick(s, i):
    if v == 1: symexTarget("hit")

# Three arms: the third condition's preamble runs only where neither of the
# first two holds.
proc threeArms(s: seq[int], i: int) =
  if i < 0: return
  if i >= s.len: symexTarget("hit")
  elif i == 0: discard
  elif s[i] == 3: discard

# Controls: a later condition's IndexDefect is still found where it is real.
proc laterRealIdx(s: seq[int], i: int) =
  if i == 5: discard
  elif s[i] == 3: discard

proc laterRealIdxElse(s: seq[int], i: int) =
  if i == 5: discard
  elif i == 6: discard
  elif s[i] == 3: discard
  else: symexTarget("hit")

suite "R1-01: an elif condition's preamble runs only when it is reached":

  test "the walker version carries the round 1 fixes":
    check parseInt(symexWalkerVersion) >= 269

  test "statement if: the bounds fork follows the first condition":
    check native(stmtIdx(@[], 0)) == "hit"
    decides(stmtIdx, sxSat)                       # was sxRaised IndexDefect
    let r = symexFind(stmtIdx, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat                     # was a clean sxRaised

  test "value-position if: the same":
    check native(valueIdx(@[], 0)) == "hit"
    decides(valueIdx, sxSat)                      # was sxRaised IndexDefect
    let r = symexFind(valueIdx, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a var-seq call in an elif runs only when the elif is tested":
    check native(stmtCall(1, @[])) == "hit"
    decides(stmtCall, sxSat)                      # was a clean sxUnsat
    check native(valueCall(1, @[])) == "hit"
    decides(valueCall, sxSat)

  test "iterator-body if: the same":
    check native(iterIdx(@[], 0)) == "hit"
    decides(iterIdx, sxSat)                       # was sxRaised IndexDefect
    let r = symexFind(iterIdx, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "three arms":
    check native(threeArms(@[], 0)) == "hit"
    decides(threeArms, sxSat)
    let r = symexFind(threeArms, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a later condition's real IndexDefect is still found":
    check native(laterRealIdx(@[], 0)) == "IndexDefect"
    let r = symexFind(laterRealIdx, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxRaised
    check native(laterRealIdxElse(@[3], 0)) == "ran"
    check native(laterRealIdxElse(@[4], 0)) == "hit"
    decides(laterRealIdxElse, sxSat)
