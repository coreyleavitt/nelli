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
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8ct_deepterm_b`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 148 s).

import std/[unittest, strutils, re, macros, locks]
import nelli/symex
import nelli/smt/runtime
import nelli/smt/types
import nelli/smt/canonicalize
import z3

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

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    label in symexCaptureEnd()

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
