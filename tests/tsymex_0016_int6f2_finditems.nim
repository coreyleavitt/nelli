## RFC-0016 int6-f2: `findIt`'s counter step is read through only over a
## stdlib `items` whose yields a length bounds.
##
## int6-x2 read through the `unCheckedInc` step of `findIt`'s counter `i`
## (`check_options.loopIncCounters`). `i` is stepped once per item that
## `items(s)` yields and fails the predicate, and `s` is untyped: a user
## `items` that yields forever steps `i` past `high(int)`, undefined behaviour
## with the step's overflow check off. Admitting that rested on time alone
## (2^63 yields are infeasible), which is not an argument for soundness.
##
## The counter now admits a `findIt` step only when the typed loop around it
## calls an `items` iterator of `system/iterators.nim` whose yields are
## bounded below `high(int)`: over an openArray, array, seq or string (its
## length), a set (at most 65536 elements) or a cstring (the bytes of one
## object); over an ordinal `Slice` or an enum type only when the element is
## at most 4 bytes, since an `int` slice can yield 2^64 values. Read from the
## resolved iterator symbol (its owner module, name and declaration), never
## from the text. Any other `items` (a user's, a `{.closure.}` one, sequtils'
## over a closure iterator) leaves the step unreadable.
##
## `keepItIf`, `toSeq` and `toSeq2` need no such rule: each step is preceded
## by a checked index whose length bounds the counter, whatever iterator
## drives the loop (`tests/0016-allowlist/pushexempt.txt`).

import std/[unittest, strutils, sequtils, macros]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/check_options
import nelli/smt/errorkind
import ./s8cu_helpers

proc id(x: int): int {.noinline.} = x

type
  Ticker = object
    start: int
  Clock = object
    start: int

iterator items(t: Ticker): int =
  ## Yields `t.start`, `t.start + 1`, ... and never stops on its own.
  var k = t.start
  while true:
    yield k
    k = k + 1

iterator items(c: Clock): int {.closure.} =
  ## The same, as a closure iterator.
  var k = c.start
  while true:
    yield k
    k = k + 1

proc opSeq(s: seq[int]) {.symexOpaque.} = discard id(s.findIt(it == 2))
proc sutSeq(v: int) =
  if v == 5: symexTarget("hit")
  opSeq(@[v, 2])

proc opTicker(t: Ticker) {.symexOpaque.} =
  discard id(t.findIt(it > t.start + 2))
proc sutTicker(v: int) =
  if v == 5: symexTarget("hit")
  opTicker(Ticker(start: v))

proc opClock(c: Clock) {.symexOpaque.} =
  discard id(c.findIt(it > c.start + 2))
proc sutClock(v: int) =
  if v == 5: symexTarget("hit")
  opClock(Clock(start: v))

proc opSlice(n: int) {.symexOpaque.} = discard id((0 .. n).findIt(it == 2))
proc sutSlice(v: int) =
  if v == 5: symexTarget("hit")
  opSlice(v)

proc opSlice8(n: int8) {.symexOpaque.} =
  discard id((0'i8 .. n).findIt(it == 2))
proc sutSlice8(v: int) =
  if v == 5: symexTarget("hit")
  opSlice8(3'i8)

proc opCloIter(n: int) {.symexOpaque.} =
  let gen = iterator (): int {.closure.} =
    var k = n
    while true:
      yield k
      k = k + 1
  discard id(gen.findIt(it > n + 2))

proc opString(s: string) {.symexOpaque.} = discard id(s.findIt(it == 'b'))
proc sutString(v: int) =
  if v == 5: symexTarget("hit")
  opString("ab")

macro stepUnreadable(fn: typed): bool =
  ## Does the opaque scan find a check push in `fn`'s typed body
  ## (`check_options.bodyCheckPragma`), the `findIt` step not read through?
  let impl = fn.getImpl
  newLit(bodyCheckPragma(impl[6], impl) != nil)

template verdict(fn: untyped; trustedWant: bool; kinds: set[UbKind]) =
  let r = pinFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
  check r.status == sxSat
  check r.trusted == trustedWant
  check r.soundness.undefinedKinds == kinds

template unreadable(fn: untyped) =
  verdict(fn, false, {UbKind(ubTailUnverified)})

suite "int6-f2: findIt over a stdlib items bounded by a length":
  test "over a seq: {ubSignedOverflow} untrusted, as at f07b43b5":
    check native(sutSeq(5)) == "hit"
    verdict(sutSeq, false, {UbKind(ubSignedOverflow)})

  test "over a string: {ubSignedOverflow} untrusted, as at f07b43b5":
    check native(sutString(5)) == "hit"
    verdict(sutString, false, {UbKind(ubSignedOverflow)})

  test "over an int8 slice (at most 256 yields): a trusted sxSat, as at f07b43b5":
    check native(sutSlice8(5)) == "hit"
    verdict(sutSlice8, true, default(set[UbKind]))

suite "int6-f2: findIt over an items no length bounds stays unreadable":
  test "natively the user's items runs on until the predicate holds":
    # It yields forever; a finite run (three items fail the predicate)
    # steps the counter and returns, so the call is reached natively.
    check Ticker(start: 7).findIt(it > 9) == 3
    check native(sutTicker(5)) == "hit"

  test "a user-defined items that yields forever":
    unreadable(sutTicker)

  test "natively the user's closure items runs on until the predicate holds":
    check Clock(start: 7).findIt(it > 9) == 3
    check native(sutClock(5)) == "hit"

  test "a user-defined {.closure.} items":
    unreadable(sutClock)

  test "natively an int slice is reached":
    check (0 .. 9).findIt(it == 2) == 2
    check native(sutSlice(5)) == "hit"

  test "an int slice (up to 2^64 yields; a trusted sxSat at f07b43b5)":
    unreadable(sutSlice)

suite "int6-f2: the scan reads the step by the resolved items":
  test "over a seq, a string or an int8 slice the step is read through":
    check not stepUnreadable(opSeq)
    check not stepUnreadable(opString)
    check not stepUnreadable(opSlice8)

  test "over a user's items that yields forever it is not":
    check stepUnreadable(opTicker)

  test "over a user's {.closure.} items it is not":
    check stepUnreadable(opClock)

  test "over sequtils' items of a closure iterator it is not":
    check stepUnreadable(opCloIter)

  test "over an int slice it is not":
    check stepUnreadable(opSlice)

suite "int6-f2: walker version":
  test "walker version floor >= 485":
    check parseInt(symexWalkerVersion) >= 485
