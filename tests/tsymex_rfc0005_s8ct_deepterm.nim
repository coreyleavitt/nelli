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

proc wideRead(k: int) =
  ## `pad[k and 7]` may name any of 4096 positions by its type.
  var pad: array[4096, int]
  if pad[k and 7] == 0:
    symexTarget("t")

proc wideWrite(k: int) =
  var pad: array[4096, int]
  pad[k and 7] = 1
  if k == 3:
    symexTarget("t")

proc narrowRead(k: int) =
  var pad: array[8, int]
  pad[k and 7] = k
  if pad[k and 7] == 6:
    symexTarget("t")

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

type
  ObjBase = object
    x: int
  ObjOne = ObjBase
  ObjTwo = ObjOne

proc sutChain(a: L40) =
  if a == 7: symexTarget("t")

proc sutTwoAliases(a: ObjTwo) =
  if a.x == 7: symexTarget("t")

var gLock: Lock
initLock(gLock)

proc holdsIt(k: int) {.symexOpaque.} =
  acquire(gLock)
  release(gLock)

proc sutLock(k: int) =
  symexAssume(k == 3)
  holdsIt(k)
  symexTarget("t")

suite "S8ct: S8bl's alias step":
  # `getTypeInst` of the alias on the right of `Lock = SysLock` is `Lock`: the
  # step came back to where it began, and the VM's call depth stopped the build.
  test "a chain of 40 aliases to a builtin is followed to its end":
    let r = symexFind(sutChain, tLabel("t"))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
      check reproduces(sutChain(r.witness[0]), "t")

  test "two aliases to an object build, and decline as main does":
    let r = symexFind(sutTwoAliases, tLabel("t"))
    check r.status == sxUnknown
    var unsupported = false
    for e in r.errors:
      if e.kind == feUnsupportedParamType: unsupported = true
    check unsupported

  test "an opaque routine naming a `Lock` global builds":
    let r = symexFind(sutLock, tLabel("t"))
    # On Windows the child cannot be handed a `Lock`, so replay declines.
    check r.status == (when defined(windows): sxUnknown else: sxSat)

suite "S8ct: an array access wider than a term walk declines":
  test "a read past the limit is a fresh value, named":
    let r = symexFind(wideRead, tLabel("t"))
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOpHavoc and "termWalkMaxDepth" in e.msg:
        named = true
    check named
    # The fresh value makes the hit a candidate, which replay confirms.
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed

  test "a write past the limit is dropped, named, and never unsat":
    let r = symexFind(wideWrite, tLabel("t"))
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedStmtKind and "termWalkMaxDepth" in e.msg:
        named = true
    check named
    check r.status != sxUnsat

  test "an array at the limit is still modelled":
    let r = symexFind(narrowRead, tLabel("t"))
    check r.status == sxSat
    for e in r.errors: check "termWalkMaxDepth" notin e.msg
    if r.status == sxSat:
      check reproduces(narrowRead(r.witness[0]), "t")

# One context for both: a second context made after one holding the 20,000-level
# chains below was destroyed built terms 800 times slower (200 `or`s, 119 s
# against 0.14 s, Z3 4.13.4; RFC-0016).
let termCtx = newContext()

suite "S8ct: termDepth":
  test "it counts levels, takes no stack, and stops at its cap":
    let ctx = termCtx
    let leaf = mkBoolVar(ctx, "leaf")
    check termDepth(ctx, leaf.raw) == 0
    check termDepth(ctx, chain(ctx, 10, leaf).raw) == 10
    # Ten times the 2000 frames Nim allows a recursion in a build with stack traces.
    check termDepth(ctx, chain(ctx, 20_000, leaf).raw, cap = 1_000_000) == 20_000
    check termDepth(ctx, chain(ctx, 20_000, leaf).raw, cap = 100) == 101
    check not termTooDeep(ctx, chain(ctx, termWalkMaxDepth, leaf).raw)
    check termTooDeep(ctx, chain(ctx, termWalkMaxDepth + 1, leaf).raw)

  test "a shared term is counted once, not once per path":
    let ctx = termCtx
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
