## RFC-0016 int6-w2: an opaque callee that calls `toSeq(s.items)` builds.
##
## The opaque effect summary (`dsl_parser.scanOpaqueEffects`) read a
## declaration's type slot as code. `toSeq`'s fallback branch declares
## `var result: seq[typeof(iter)]`, and the typed body keeps that type
## untyped: `[](seq, typeof(s.items))` over an open symbol choice. The summary
## read `typeof` as a stdlib call and asked its argument's type, which it has
## none of: `Error: node has no type` (`dsl_typebridge.viewTypeInst`), the
## whole build failed. It predates int6.
##
## A type slot and a conversion's target type run nothing and are no longer
## read; an expression whose type the summary reads but which has none
## (`dsl_parser.typeless`) makes the call non-inert, never a compile failure.
##
## Pinned: the verdict is the one aaa74c4b (walker 480, before int6-t) has with
## this fix applied alone (on aaa74c4b itself the file does not build). The two
## sibling shapes built before the fix too; they hold that an anonymous range
## conversion's untyped target type and a walked callee using `toSeq` keep
## building.

import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s8cu_helpers

proc id(x: int): int {.noinline.} = x

proc opToSeq(s: seq[int]) {.symexOpaque.} = discard id(toSeq(s.items).len)
proc sutToSeq(v: int) =
  if v == 5: symexTarget("hit")
  opToSeq(@[v, 2])

proc opRangeConv(x: int) {.symexOpaque.} =
  discard id(int(range[0 .. 10]((x and 3))))
proc sutRangeConv(v: int) =
  if v == 5: symexTarget("hit")
  opRangeConv(v)

proc plainToSeq(s: seq[int]): int = toSeq(s.items).len
proc sutPlainToSeq(v: int) =
  if v == 5: symexTarget("hit")
  discard id(plainToSeq(@[v, 2]))

suite "int6-w2: an opaque toSeq(s.items)":
  test "builds, with the verdict of aaa74c4b plus this fix":
    check native(sutToSeq(5)) == "hit"
    let r = pinFind(sutToSeq, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check not r.trusted
    check r.soundness.undefinedKinds ==
      {UbKind(ubSignedOverflow), ubTailUnverified}

suite "int6-w2: the sibling shapes build":
  test "an opaque anonymous range conversion":
    check native(sutRangeConv(5)) == "hit"
    let r = pinFind(sutRangeConv, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
    check r.status == sxSat

  test "a walked callee using toSeq(s.items)":
    check native(sutPlainToSeq(5)) == "hit"
    let r = pinFind(sutPlainToSeq, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
    check r.status == sxSat

suite "int6-w2: walker version":
  test "walker version floor >= 483":
    check parseInt(symexWalkerVersion) >= 483
