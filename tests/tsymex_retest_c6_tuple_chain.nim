## Chapulin 0.1.0 re-test triage — catalog #6 (chained dependent scans →
## "REGRESSED sxUnknown→crash"), walker v64. Root cause was NOT the Q1/R14
## loop machinery: DESTRUCTURING a tuple return from a loop-bearing callee
## that can raise sent a composite-typed retSym into `retBindEq`, whose
## non-primitive arm RAISED ValueError from inside the walk — unwinding
## through live `seq[Path]` state, the b7258f7/CR-1c C-backend silent-loss
## hazard. That one raise manifested nondeterministically: chapulin's
## re-test saw a hard native crash (bare non-zero exit); the same repro on
## the same commit also surfaced as a net-caught `weInternalWalkerFault`.
## v64 replaces the raise with an in-band classified degrade
## (`feUnsupportedOp`, path tainted uncertain) at the scalar-raise drain's
## binding site — deterministic, sound, never a crash.
##
## Kind-pinning note (verified while landing v64): the STRING-building
## chapulin shape (`readCStringTwin` with `s.add char(b)`) now degrades
## EARLIER, at the pre-existing `seUnsupportedStringOp` classified gap for
## a char-arg `.add` — so those tests pin "classified sxUnknown, never the
## walker-fault route", not one specific kind. The INT-only tuple shape
## (`scanPair`) has no string op to degrade at, reaches the composite
## `retBindEq` bind itself, and pins the new guard's `feUnsupportedOp`.
import std/[unittest, strutils, sequtils]
import proptest/symex
import proptest/smt/canonicalize
import proptest/smt/types

type ScanError = object of CatchableError

proc readCStringTwin(data: seq[int], offset: int): (string, int) =
  var s = ""
  var i = offset
  while i < data.len:
    let b = ((data[i] mod 256) + 256) mod 256
    if b == 0:
      return (s, i + 1)
    s.add char(b)
    i.inc
  raise newException(ScanError, "Unterminated at " & $offset)

proc scanPair(data: seq[int], offset: int): (int, int) =
  ## String-free tuple-returning scan — nothing degrades before the return
  ## bind, so this exercises the composite-retSym drain guard itself.
  var i = offset
  while i < data.len:
    if ((data[i] mod 256) + 256) mod 256 == 0:
      return (i, i + 1)
    i.inc
  raise newException(ScanError, "Unterminated at " & $offset)

proc singleDiscard(data: seq[int]) =
  if data.len < 2: return
  discard readCStringTwin(data, 2)

proc singleDestructure(data: seq[int]) =
  if data.len < 2: return
  let (_, p1) = readCStringTwin(data, 2)
  if p1 > data.len:
    return

proc destructurePair(data: seq[int]) =
  if data.len < 2: return
  let (a, b) = scanPair(data, 2)
  if a > b:
    return

proc chained(data: seq[int]) =
  ## The catalog-#6 headline shape: 2nd scan's offset = 1st's symbolic result.
  let (_, p1) = readCStringTwin(data, 2)
  discard readCStringTwin(data, p1)

suite "symex re-test C6 — tuple-return destructure through the raise drain":

  test "discarded tuple-returning call still proves sxUnsat (capability pin)":
    let r = symexFind(singleDiscard, tIndexError())
    check r.status == sxUnsat

  test "int-tuple destructure from a raising scan: the drain guard classifies (feUnsupportedOp)":
    let r = symexFind(destructurePair, tIndexError())
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedOp)
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "destructured string-tuple return: deterministic classified degrade, never the walker-fault route":
    let r = symexFind(singleDestructure, tIndexError())
    check r.status == sxUnknown
    check r.errors.len > 0
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "chained dependent scans (the catalog-#6 repro): classified sxUnknown, never a crash":
    let r = symexFind(chained, tIndexError())
    check r.status == sxUnknown
    check r.errors.len > 0
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

suite "symex re-test C6 — walker version pin":

  test "walker version floor >= 64 (composite-return drain degrade)":
    check parseInt(symexWalkerVersion) >= 64
