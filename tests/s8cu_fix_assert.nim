## RFC-0005 S8cu fixture: `assert` under `assertions` and `checks` pushes, and a
## global's initialiser under a push. Every label is reachable only at v == 4.
## Each `mitems` and `pairs` row has an element type of its own: an iterator's
## instance takes the options of its first instantiation.
import std/tables
import nelli

{.push assertions: off.}
proc aOff*(v: int) =
  if v == 4:
    assert v != 4
    symexTarget("hit")
proc daOff*(v: int) =
  if v == 4:
    doAssert v != 4
    symexTarget("hit")
proc gAOff[T](v: T) =
  if v == 4:
    assert v != 4
    symexTarget("hit")
template tAOff(v: int) =
  assert v != 4
{.pop.}

proc gAClean[T](v: T) =
  if v == 4:
    assert v != 4
    symexTarget("hit")

proc viaGAOff*(v: int) = gAOff(v)
{.push assertions: off.}
proc viaGACleanInPush*(v: int) = gAClean(v)
proc viaTAClean*(v: int) =
  if v == 4:
    tAOff(v)
    symexTarget("hit")
{.pop.}
proc viaTAOff*(v: int) =
  if v == 4:
    tAOff(v)
    symexTarget("hit")

{.push assertions: on.}
proc aOn*(v: int) =
  if v == 4:
    assert v != 4
    symexTarget("hit")
{.pop.}

{.push checks: off.}
proc aChecksOff*(v: int) =
  if v == 4:
    assert v != 4
    symexTarget("hit")
{.pop.}

# `mitems[int16]` is first instantiated here, under the push: no assert.
{.push assertions: off.}
proc mitemsFirstOff*(v: int) =
  if v == 4:
    var s = @[1'i16, 2, 3]
    for x in s.mitems:
      if s.len == 3: s.add 9
    symexTarget("hit")
proc pairsFirstOff*(v: int) =
  if v == 4:
    var t = initTable[int16, int16]()
    t[1] = 1
    for k in t.keys:
      if t.len == 1: t[2] = 2
    symexTarget("hit")
{.pop.}
# Outside the push, in a module with one: `mitems[int32]` has its assert.
proc mitemsOutside*(v: int) =
  if v == 4:
    var s = @[1'i32, 2, 3]
    for x in s.mitems:
      if s.len == 3: s.add 9
    symexTarget("hit")

# A global's initialiser under a push: the walker does not evaluate it.
var gOne = 1
{.push overflowChecks: off.}
let gWrapped = high(int) + gOne
{.pop.}
proc readWrapped*(v: int) =
  if v == 4 and gWrapped < 0: symexTarget("hit")
proc readWrappedNot*(v: int) =
  if v == 4 and gWrapped >= 0: symexTarget("hit")
