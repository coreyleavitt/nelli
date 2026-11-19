## RFC-0016 int6-x2: the opaque defect scan reads through `sequtils`'
## exported templates' own loop-counter step, matched by the counter.
##
## int6-u exempted `sequtils`' `unCheckedInc` only inside a routine of
## `sequtils` itself; `findIt`, `keepItIf`, `toSeq` and `toSeq2` expand it into
## the caller's routine, so an opaque callee using them was unreadable and lost
## its aaa74c4b verdict. The owner rule cannot simply be dropped:
## `import std/sequtils {.all.}` lets user code step any variable of its own
## with the unexported template, unbounded (`tsymex_0016_int6w2_seqtpl`).
##
## The rule now admits a routine outside `sequtils` when the stepped counter's
## symbol is declared, by its own declaration's position, at one of the four
## audited counter declarations in `sequtils`' text
## (`check_options.loopIncCounters`, `tests/0016-allowlist/pushexempt.txt`).
## Each is a local the template generates (gensym), which no code outside the
## template can name; a user's `{.all.}` step steps a variable the user
## declared, in the user's file.
##
## Pinned: `findIt` and `keepItIf` have their aaa74c4b (walker 480) verdicts
## again, measured there: `{ubSignedOverflow}` untrusted sxSat, and a trusted
## sxSat. The user's own `{.all.}` step stays unreadable, and so does its twin
## in another module whose counter is declared at `findIt`'s line and column
## (`s0016_int6x2_fakectr`): the match is the declaration in the toolchain's
## file, not its text or position alone.

import std/[unittest, strutils, os, sequtils {.all.}]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/check_options
import nelli/smt/errorkind
import ./s8cu_helpers
import ./s0016_int6x2_fakectr

proc id(x: int): int {.noinline.} = x

proc opFindIt(s: seq[int]) {.symexOpaque.} = discard id(s.findIt(it == 2))
proc sutFindIt(v: int) =
  if v == 5: symexTarget("hit")
  opFindIt(@[v, 2])

proc opKeepItIf(s: seq[int]) {.symexOpaque.} =
  var t = s
  t.keepItIf(it > 1)
  discard id(t.len)
proc sutKeepItIf(v: int) =
  if v == 5: symexTarget("hit")
  opKeepItIf(@[v, 2])

proc bump(x: var int) = unCheckedInc(x)

proc opBump(v: int) {.symexOpaque.} =
  var x = v
  unCheckedInc(x)
  discard id(x)
proc sutBump(v: int) =
  if v == 5: symexTarget("hit")
  opBump(v)

proc sutFake(v: int) =
  if v == 5: symexTarget("hit")
  discard id(fakeFindIt(v))

template preT(fn: untyped; kinds: set[UbKind]) =
  ## aaa74c4b's verdict: sxSat, untrusted, exactly these undefined kinds.
  let r = pinFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
  check r.status == sxSat
  check not r.trusted
  check r.soundness.undefinedKinds == kinds

template preTrusted(fn: untyped) =
  ## aaa74c4b's verdict: a trusted sxSat.
  let r = pinFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
  check r.status == sxSat
  check r.trusted
  check r.soundness.undefinedKinds == {}

template unreadable(fn: untyped) =
  let r = pinFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
  check r.status == sxSat
  check not r.trusted
  check r.soundness.undefinedKinds == {UbKind(ubTailUnverified)}

const seqSites = loopIncCounterSites("pure/collections/sequtils.nim")

suite "int6-x2: sequtils' templates' own counter step is read through":
  test "an opaque findIt has its aaa74c4b verdict":
    check native(sutFindIt(5)) == "hit"
    preT(sutFindIt, {UbKind(ubSignedOverflow)})

  test "an opaque keepItIf has its aaa74c4b verdict":
    check native(sutKeepItIf(5)) == "hit"
    preTrusted(sutKeepItIf)

suite "int6-x2: a user's step with the template stays unreadable":
  test "natively an {.all.} step of a user's variable is unchecked":
    var x = high(int)
    var raised = false
    try: bump(x)
    except OverflowDefect: raised = true
    check not raised   # the C addition, undefined: no OverflowDefect

  test "an opaque user routine stepping its own variable":
    check native(sutBump(5)) == "hit"
    unreadable(sutBump)

  test "natively the twin's step at findIt's position is unchecked":
    var raised = false
    try: discard fakeFindIt(high(int))
    except OverflowDefect: raised = true
    check not raised

  test "a counter declared at findIt's line and column in another module":
    check native(sutFake(5)) == "hit"
    unreadable(sutFake)

suite "int6-x2: the audited counter sites":
  test "each template declares its counter once, at the listed position":
    check seqSites.len == 4
    let text = readFile(currentSourcePath().parentDir() / "0016-allowlist" /
                        "pushexempt.txt")
    for s in seqSites:
      checkpoint s.tpl & " " & $s.line & ":" & $s.col
      check ("`" & s.tpl & "` line " & $s.line & " column " & $s.col) in text

  test "findIt's counter sits where the twin declares its own":
    var found = false
    for s in seqSites:
      if s.tpl == "findIt": found = s.line == 337 and s.col == 4
    check found

suite "int6-x2: walker version":
  test "walker version floor >= 484":
    check parseInt(symexWalkerVersion) >= 484
