## RFC-0016 int6 D1. A call in command syntax (`f x`) is a call.
##
## Overload resolution builds the typed call with the node kind the source
## spelled (Nim 2.2.10 `sigmatch.nim`: `m.call = newNodeIT(n.kind, ...)`),
## so a command reaches the walker as `nnkCommand`: `move result`, the last
## statement of Nim 2.2.10's `filterIt` (sequtils.nim), and `let y = f x`.
## `parseExpr` read only `nnkCall` as a call: the command declined with
## `feUnsupportedExprKind` on every path, so a `filterIt` over a
## `seq[seq[int]]` parameter (`tsymex_0016_k9cg_unbacked_p_*`'s FilterIt
## probe) never had a clean hit at any unroll. The label marker in command
## syntax (`symexTarget "t"`) was walked as an ordinary call, not a label.
##
## The FilterIt probe's wall time at the default unroll is the k-unroll's
## own path growth, which a clean loop pays alike; this file pins the call,
## not that cost (see `mkUnwind3`).
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc filterNested(o: seq[seq[int]]) =
  ## The k9cg FilterIt probe's shape, with a label only a non-empty element
  ## reaches.
  let m = o.filterIt(it.len > 0)
  if m.len >= 1: symexTarget("hit")

proc moveCommand(x: int) =
  ## `move s` in command syntax: its value is `s`'s.
  var s = @[x]
  let t = move s
  if t.len == 1 and t[0] == 7: symexTarget("hit")

proc moveCommandSource(x: int) =
  ## `move s` in command syntax leaves `s` empty.
  var s = @[x]
  let t = move s
  if t.len == 1 and s.len != 0: symexTarget("hit")

proc twice(x: int): int = 2 * x

proc userCommand(x: int) =
  ## A user routine called in command syntax in expression position.
  let y = twice x
  if y == 14: symexTarget("hit")

proc markerCommand(x: int) =
  ## The label marker in command syntax, at statement position.
  if x == 3: symexTarget "hit"

proc mkUnwind3(): SymexSettings =
  ## The pin settings at a loop unroll of 3. The `filterIt` pins are of the
  ## command call, not of the unroll: its loop over a `seq[seq[int]]` forks
  ## per element whatever the call's lowering, about 12x the wall per unroll
  ## step (measured on this fix, c: 0.17 s at 1, 3.7 s at 3, 43 s at 4; at
  ## the default 5 the walk meets the 600 s solver stall backstop). Before
  ## the fix every unroll declined the `move result`.
  result = pinSettingsConst
  result.budget.maxLoopUnwind = 3

const unwind3 = mkUnwind3()

proc noCommandDecline[T](r: SymexResult[T]): bool =
  for e in r.errors:
    if e.kind == feUnsupportedExprKind and "nnkCommand" in e.msg:
      return false
  true

suite "int6 D1: a command-syntax call is a call":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 470

  test "`move s` in command syntax is the moved value":
    let r = pinFind(moveCommand, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check noCommandDecline(r)
    check r.status == sxSat
    check r.trusted
    if r.status == sxSat: check r.witness[0] == 7

  test "`move s` in command syntax leaves the source empty":
    let r = pinFind(moveCommandSource, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check noCommandDecline(r)
    check r.status == sxUnsat
    check r.trusted

  test "a user routine in command syntax is the call":
    let r = pinFind(userCommand, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check noCommandDecline(r)
    check r.status == sxSat
    check r.trusted
    if r.status == sxSat: check r.witness[0] == 7

  test "the label marker in command syntax is the label":
    let r = pinFind(markerCommand, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted
    if r.status == sxSat: check r.witness[0] == 3

  test "filterIt over a seq[seq[int]] parameter reaches a verdict":
    let r = pinFind(filterNested, tLabel("hit"), unwind3)
    checkpoint show(r.errors)
    check noCommandDecline(r)
    check r.status == sxSat
    check r.trusted
