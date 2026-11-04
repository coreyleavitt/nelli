## RFC-0005 review R1-04 -- a lowering decline's path taint lands on the path
## that produced it.
##
## A lowering decline (`lowerDegrade`: an unwritten global read, among
## others) cannot fork a path from inside `lower`; it queues its taint in
## `loweringPendingTaint`, and the walk arm that called `lower` drains it onto
## the path it lowered for (`drainPendingLowerEffects`). Two arms called the
## raw `lower` and never drained: the runtime-discriminator variant
## constructor's plain fields (`isVariantConstructSym`) and a `Table` key
## (`walkIndexArm`). Their queued taint was drained by whatever lowering ran
## next -- on a sibling path, or on nothing -- so the path that read the
## unwritten global stayed clean, and a target on it was a clean `sxSat`
## natively unreachable.
##
## Each row runs the routine natively (`native`) beside the walk's verdict.
import std/[unittest, tables]
import nelli
import nelli/symex
import ./s8cu_helpers

var gN: int
var gKey: string

type
  Op = enum opRrq, opWrq
  Pkt = object
    tag: int
    case opcode: Op
    of opRrq: rq: int
    of opWrq: wq: int

# The finding's shape: the discriminator is a branch fork, so two paths reach
# the constructor, and `gN` (never written: 0 natively) is a plain field.
proc ctorFork(b: byte) =
  let op = if b == 1'u8: opRrq else: opWrq
  if b > 3:
    let p = Pkt(opcode: op, tag: gN)
    if p.tag == 5: symexTarget("hit")

# One path into the constructor.
proc ctorOne(b: byte, o: Op) =
  if b > 3:
    let p = Pkt(opcode: o, tag: gN)
    if p.tag == 5: symexTarget("hit")

# Controls: a plain field the walk knows exactly.
proc ctorKnown(b: byte) =
  let op = if b == 1'u8: opRrq else: opWrq
  if b > 3:
    let p = Pkt(opcode: op, tag: int(b))
    if p.tag == 5: symexTarget("hit")

proc ctorKnownDead(b: byte) =
  let op = if b == 1'u8: opRrq else: opWrq
  if b > 3:
    let p = Pkt(opcode: op, tag: int(b))
    if p.tag == 2: symexTarget("hit")

# The Table-key site: the key is an unwritten global.
proc tabKeyFork(b: byte) =
  var t = initTable[string, int]()
  t["a"] = 1
  let k = if b == 1'u8: 1 else: 2
  if b > 3:
    if t[gKey] == 1 and k == 2: symexTarget("hit")

proc clean(r: SymexResult): bool =
  r.status == sxSat and r.soundness.pathTaint == {} and
    r.soundness.replay == rsNotNeeded

suite "R1-04: a lowering decline taints the path that produced it":

  test "variant constructor over a forked discriminator":
    check native(ctorFork(4)) == "ran"
    check native(ctorFork(1)) == "ran"
    let r = symexFind(ctorFork, tLabel("hit"))
    checkpoint show(r.errors)
    checkpoint $r.status & " " & $r.soundness.pathTaint & " " &
      $r.soundness.replay
    check not r.clean                # was a clean sxSat
    check not trusted(r) or r.status == sxUnsat

  test "variant constructor on one path":
    check native(ctorOne(4, opWrq)) == "ran"
    let r = symexFind(ctorOne, tLabel("hit"))
    checkpoint show(r.errors)
    check not r.clean
    check not trusted(r) or r.status == sxUnsat

  test "controls: a known plain field decides":
    check native(ctorKnown(5)) == "hit"
    decides(ctorKnown, sxSat)
    check native(ctorKnownDead(2)) == "ran"
    decides(ctorKnownDead, sxUnsat)

  test "Table key read from an unwritten global":
    expect KeyError: tabKeyFork(4)
    let r = symexFind(tabKeyFork, tLabel("hit"))
    checkpoint show(r.errors)
    checkpoint $r.status & " " & $r.soundness.pathTaint
    check not r.clean
