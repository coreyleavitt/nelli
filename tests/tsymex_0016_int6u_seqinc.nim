## RFC-0016 int6-u: the opaque defect scan reads through `sequtils`' own
## loop-counter step, inside that module's routines.
##
## int6-t made a routine whose typed body holds a check pragma unreadable to
## the scan ("may raise any Defect", "may be undefined"), with one audited
## exemption: `system/iterators.nim`'s `unCheckedInc` (`{.push overflowChecks:
## off.}` `inc(i)` `{.pop.}`) inside that module's iterators. `sequtils` has
## its own copy of the template; an opaque callee that reached a `sequtils`
## routine using it lost the verdict it had before int6-t. That copy joins the
## allowlist (`tests/0016-allowlist/pushexempt.txt`), audited use site by use
## site: inside `sequtils`' own routines every step is held below `high(int)`
## by an earlier comparison or a checked operation.
##
## Pinned: the verdicts below are the ones the same callees had on the commit
## before int6-t (aaa74c4b, walker 480), measured there.
##
## `keepIf` and `delete` held `ubTailUnverified` before int6-t already, from
## another part of their bodies than the step; the pin is that set, exactly.
## Without the exemption (dc5d1d11) every one of these callees is
## `{ubTailUnverified}` alone.
##
## RFC-0016 int6-w2: `count`, which steps `result`, is exempt too (the
## region's shape admits the routine's `result` as well as a local `var`):
## `result` starts at 0 and is stepped at most once per item of `s`, so it
## stays below `len(s)`. Its verdict is aaa74c4b's, `{ubSignedOverflow}`.
## The exported templates `findIt`, `keepItIf` and `toSeq` expand the step
## into the caller's own routine; they are exempt there by their counter
## (int6-x2, `tsymex_0016_int6x2_seqctr`).

import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/check_options
import nelli/smt/errorkind
import ./s8cu_helpers

proc id(x: int): int {.noinline.} = x

proc opConcat(s: seq[int]) {.symexOpaque.} = discard id(concat(s, s).len)
proc sutConcat(v: int) =
  if v == 5: symexTarget("hit")
  opConcat(@[v, 2])

proc opCycle(s: seq[int]) {.symexOpaque.} = discard id(cycle(s, 2).len)
proc sutCycle(v: int) =
  if v == 5: symexTarget("hit")
  opCycle(@[v, 2])

proc opDistribute(s: seq[int]) {.symexOpaque.} =
  discard id(distribute(s, 2).len)
proc sutDistribute(v: int) =
  if v == 5: symexTarget("hit")
  opDistribute(@[v, 2, 3])

proc gt1(x: int): bool = x > 1
proc opKeepIf(s: seq[int]) {.symexOpaque.} =
  var t = s
  keepIf(t, gt1)
  discard id(t.len)
proc sutKeepIf(v: int) =
  if v == 5: symexTarget("hit")
  opKeepIf(@[v, 2])

proc opInsert(s: seq[int]) {.symexOpaque.} =
  var t = s
  t.insert([7, 8], 1)
  discard id(t.len)
proc sutInsert(v: int) =
  if v == 5: symexTarget("hit")
  opInsert(@[v, 2])

proc opDelete(s: seq[int]) {.symexOpaque.} =
  var t = s
  t.delete(0 .. 0)
  discard id(t.len)
proc sutDelete(v: int) =
  if v == 5: symexTarget("hit")
  opDelete(@[v, 2])

proc opCount(s: seq[int]) {.symexOpaque.} = discard id(count(s, 2))
proc sutCount(v: int) =
  if v == 5: symexTarget("hit")
  opCount(@[v, 2])

template preT(fn: untyped; kinds: set[UbKind]) =
  ## The verdict on aaa74c4b (walker 480), before int6-t: sxSat, untrusted,
  ## exactly these undefined kinds.
  let r = pinFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
  check r.status == sxSat
  check not r.trusted
  check r.soundness.undefinedKinds == kinds

suite "int6-u: sequtils' own loop-counter step is read through":
  test "an opaque concat":
    check native(sutConcat(5)) == "hit"
    preT(sutConcat, {UbKind(ubSignedOverflow)})

  test "an opaque cycle":
    check native(sutCycle(5)) == "hit"
    preT(sutCycle, {UbKind(ubSignedOverflow)})

  test "an opaque distribute":
    check native(sutDistribute(5)) == "hit"
    preT(sutDistribute, {UbKind(ubIntMinModMinusOne), ubSignedOverflow,
                         ubSignedDivZero})

  test "an opaque insert":
    check native(sutInsert(5)) == "hit"
    preT(sutInsert, {UbKind(ubSignedOverflow)})

  test "an opaque keepIf":
    check native(sutKeepIf(5)) == "hit"
    preT(sutKeepIf, {UbKind(ubSignedOverflow), ubTailUnverified})

  test "an opaque delete":
    check native(sutDelete(5)) == "hit"
    preT(sutDelete, {UbKind(ubSignedOverflow), ubTailUnverified})

suite "int6-w2: the sequtils step of result":
  test "count steps result":
    check native(sutCount(5)) == "hit"
    preT(sutCount, {UbKind(ubSignedOverflow)})

suite "int6-u: the exemption allowlist":
  test "sequtils' template is on it":
    var known: seq[string]
    for e in loopIncExemptions: known.add e.file & ":" & e.name
    check "pure/collections/sequtils.nim:unCheckedInc" in known

suite "int6-u: walker version":
  test "walker version floor >= 483":
    check parseInt(symexWalkerVersion) >= 483
