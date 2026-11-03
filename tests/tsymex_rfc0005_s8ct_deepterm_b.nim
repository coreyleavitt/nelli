## RFC-0005 S8ct: a term deeper than a recursive walk may take.
##
## `var pad: array[4096, int]` read at `pad[k and 7]` put a 4096-deep chain in a
## query, and S8by's `mergeMemberships` recursed a level at a time down it: the
## analysis ended the process at Nim's call depth limit, or by a real stack
## overflow in a build with no stack traces. This is the failure the sort recorded
## as replay's (row B19). Such an array access now declines before it builds the
## chain (`arrayAccessTooWide`, pinned below), so the terms here come from a string
## concatenated 300 times.
##
## A conjunct past `termWalkMaxDepth` is left as it is. The rewrite keeps every
## model, so skipping it costs at most the merge: the pins below hold a term
## measured past the limit on a query with a known SAT and a known UNSAT answer,
## each checked natively. Without the merge an empty query may come back unknown.
## It may not come back SAT.
##
## Row B19's exact SUT is its own file, `tsymex_rfc0005_s8ct_b19` (batch 11): it
## was 86 s of this suite's 186 s on Windows, against the leg's 240 s kill.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8ct_deepterm`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 148 s).

import std/[unittest, strutils, re, macros, locks]
import nelli/symex
import nelli/smt/runtime
import nelli/smt/types
import nelli/smt/canonicalize
import z3

macro deepened(t: untyped; s: string; times: static int): untyped =
  ## `var t = s`, then `t = t & ""` `times` times: the value of `s`, as a term
  ## `times` levels deep. Flat statements, not one nested expression: a
  ## 300-deep expression overflowed the compiler's own stack on Windows
  ## (0xC00000FD).
  result = newStmtList(newVarStmt(t, s))
  for i in 0 ..< times:
    result.add newAssignment(t, infix(t, "&", newLit("")))

proc deepSat(s: string; k: int) =
  ## `k == 5` makes the disjunction true whatever `s` holds, so `"b", 5` hits.
  deepened(t, s, 300)
  let a = k == 5
  if t.endsWith(re"b+") and (a or not t.contains(re"b")):
    symexTarget("sat")

proc deepUnsat(s: string; k: int) =
  ## `a` is false, so `s` must end in `b` and hold none: no input hits.
  deepened(t, s, 300)
  let a = k == 5
  if k != 5 and t.endsWith(re"b+") and (a or not t.contains(re"b")):
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

macro aliasChain(n: static int): untyped =
  ## `type L0 = int; L1 = L0; ...`
  let section = newNimNode(nnkTypeSection)
  section.add nnkTypeDef.newTree(ident"L0", newEmptyNode(), ident"int")
  for i in 1 .. n:
    section.add nnkTypeDef.newTree(ident("L" & $i), newEmptyNode(), ident("L" & $(i - 1)))
  result = newStmtList(section)

aliasChain(40)

var gLock: Lock
initLock(gLock)

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

  test "UNSAT: the verdict, with the term measured past the limit":
    let m = measured(symexFind(deepUnsat, tLabel("unsat")))
    check m.depths.len > 0
    for d in m.depths: check d > termWalkMaxDepth
    # Z3 5.1 proves it within the query's budget. Z3 4.13.4 (the Windows
    # symex leg's) returns unknown under the same rlimit, measured: the
    # verdict is `sxUnknown` with `beSolverUndef`, never `sxSat`.
    checkpoint "z3 " & z3FullVersion()
    if z3FullVersion().startsWith("4."):
      check m.r.status == sxUnknown
      var undef = false
      for e in m.r.errors:
        if e.kind == beSolverUndef: undef = true
      check undef
    else:
      check m.r.status == sxUnsat

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
    check parseInt(symexWalkerVersion) >= 261
