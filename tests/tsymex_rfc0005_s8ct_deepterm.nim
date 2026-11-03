## RFC-0005 S8ct: a term deeper than a recursive walk may take.
##
## `var pad: array[4096, int]` puts a chain of stores in a query, and S8by's
## `mergeMemberships` recursed a level at a time down it: the analysis ended the
## process at Nim's call depth limit, or by a real stack overflow in a build with
## no stack traces. This is the failure the sort recorded as replay's (row B19).
##
## A conjunct past `termWalkMaxDepth` is now left as it is. The rewrite keeps every
## model, so skipping it costs at most the merge: the pins below hold a term
## measured past the limit on a query with a known SAT and a known UNSAT answer,
## each checked natively. Without the merge an empty query may come back unknown.
## It may not come back SAT.

import std/[unittest, strutils, re]
import nelli/symex
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc deepSat(s: string; k: int) =
  ## `k == 5` makes the disjunction true whatever `s` holds, so `"b", 5` hits.
  var pad: array[4096, int]
  pad[k and 7] = k
  let a = pad[k and 7] == 5
  if s.endsWith(re"b+") and (a or not s.contains(re"b")):
    symexTarget("sat")

proc deepUnsat(s: string; k: int) =
  ## `a` is false, so `s` must end in `b` and hold none: no input hits.
  var pad: array[4096, int]
  pad[k and 7] = k
  let a = pad[k and 7] == 5
  if k != 5 and s.endsWith(re"b+") and (a or not s.contains(re"b")):
    symexTarget("unsat")

proc words(n: int): seq[string] =
  ## Every string over `a` and `b` of at most `n` characters.
  result = @[""]
  var last = @[""]
  for i in 1 .. n:
    var next: seq[string]
    for w in last:
      for c in "ab": next.add w & c
    result.add next
    last = next

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    label in symexCaptureEnd()

template measured(call: untyped): untyped =
  block:
    deepTermsLeftAlone = @[]
    let r = call
    for d in deepTermsLeftAlone: checkpoint "left alone at depth " & $d
    for e in r.errors: checkpoint $e.kind & ": " & e.msg
    (r: r, depths: deepTermsLeftAlone)

proc chain(ctx: Z3Context; n: int; leaf: Z3Bool): Z3Bool =
  ## `leaf` under `n` disjunctions with false constants.
  result = leaf
  for i in 0 ..< n:
    result = mkBoolVar(ctx, "b" & $(i mod 8)) or result

suite "S8ct: termDepth":
  test "it counts levels, takes no stack, and stops at its cap":
    let ctx = newContext()
    let leaf = mkBoolVar(ctx, "leaf")
    check termDepth(ctx, leaf.raw) == 0
    check termDepth(ctx, chain(ctx, 10, leaf).raw) == 10
    # Ten times the 2000 frames Nim allows a recursion in a build with stack traces.
    check termDepth(ctx, chain(ctx, 20_000, leaf).raw, cap = 1_000_000) == 20_000
    check termDepth(ctx, chain(ctx, 20_000, leaf).raw, cap = 100) == 101
    check not termTooDeep(ctx, chain(ctx, termWalkMaxDepth, leaf).raw)
    check termTooDeep(ctx, chain(ctx, termWalkMaxDepth + 1, leaf).raw)

  test "a shared term is counted once, not once per path":
    let ctx = newContext()
    var t = mkBoolVar(ctx, "leaf")
    for i in 0 ..< 200: t = t or t   # 2^200 paths
    check termDepth(ctx, t.raw) == 200

suite "S8ct: a term past the limit costs the merge, not the verdict":
  test "native: the SAT query's witness hits and the UNSAT query has none":
    check reproduces(deepSat("b", 5), "sat")
    for w in words(6):
      for k in -9 .. 9:
        check not reproduces(deepUnsat(w, k), "unsat")

  test "SAT: confirmed, with the term measured past the limit":
    let m = measured(symexFind(deepSat, tLabel("sat")))
    check m.depths.len > 0
    for d in m.depths: check d > termWalkMaxDepth
    check m.r.status == sxSat
    if m.r.status == sxSat:
      check reproduces(deepSat(m.r.witness[0], m.r.witness[1]), "sat")

  test "UNSAT: unsat or unknown, never sat, with the term measured past the limit":
    let m = measured(symexFind(deepUnsat, tLabel("unsat")))
    check m.depths.len > 0
    for d in m.depths: check d > termWalkMaxDepth
    check m.r.status in {sxUnsat, sxUnknown}

  test "the rewrite leaves a conjunct past the limit and takes one at it":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let r = range(mkString(ctx, "b"), mkString(ctx, "b"))
    let lit = not matches(s, r)
    let top = matches(s, plus(r))
    let deep = chain(ctx, termWalkMaxDepth + 1, lit)
    let kept = mergeMemberships(ctx, [top, deep])
    check kept.len == 2
    check kept[1].raw == deep.raw
    let shallow = chain(ctx, 3, lit)
    let merged = mergeMemberships(ctx, [top, shallow])
    check merged.len == 2
    check merged[1].raw != shallow.raw

suite "S8ct: other deep walks":
  test "a deep or-chain does not stop a solve":
    let ctx = newContext()
    let t = chain(ctx, 20_000, mkBoolVar(ctx, "leaf"))
    let kept = mergeMemberships(ctx, [t])
    check kept.len == 1

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 256
