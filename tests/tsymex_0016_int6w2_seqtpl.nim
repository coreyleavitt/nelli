## RFC-0016 int6-w2: why a step with `sequtils`' `unCheckedInc` outside
## `sequtils`' routines is not read through by its push alone.
##
## `sequtils`' `unCheckedInc` is not exported (`template unCheckedInc(x)`, no
## `*`, on 2.2.10), so a push at its body might seem to come only from
## `sequtils`' own text: its 12 routine sites and the 4 in the templates
## `findIt`, `keepItIf`, `toSeq` and `toSeq2`, all bounded. It does
## not: `import std/sequtils {.all.}` makes a module's private symbols
## visible, and a user routine can then step any variable of its own with it,
## unbounded. Natively below, `unCheckedInc` on `high(int)` raises no
## `OverflowDefect` (the plain C addition, undefined). A push identified
## by its position at the template body alone would read that step as
## checked. So the exemption keeps its owner rule
## (`check_options.loopIncExempt`): the routine the step expands into must be
## one of `sequtils`' own, or (int6-x2, `tsymex_0016_int6x2_seqctr`) the
## stepped counter must be one of the four templates' own, by its symbol's
## declaration in `sequtils`' text; a user's variable is neither.
## `system/iterators.nim`'s template is used only by that module's iterators
## and by templates local to them, which expand inside those iterators.
##
## Pinned: the user step below stays unreadable. `findIt` and `keepItIf`
## have their aaa74c4b verdicts again (int6-x2, `tsymex_0016_int6x2_seqctr`).
## `toSeq(s.items)` keeps aaa74c4b's verdict
## (`tsymex_0016_int6w2_opaquetoseq`): its expansion there has no step.

import std/[unittest, strutils, sequtils {.all.}]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s8cu_helpers

proc id(x: int): int {.noinline.} = x

proc bump(x: var int) = unCheckedInc(x)

proc opBump(v: int) {.symexOpaque.} =
  var x = v
  unCheckedInc(x)
  discard id(x)
proc sutBump(v: int) =
  if v == 5: symexTarget("hit")
  opBump(v)

template unreadable(fn: untyped) =
  let r = pinFind(fn, tLabel("hit"), pinSettingsConst)
  checkpoint $r.status & " " & show(r.errors) & " " & $r.soundness
  check r.status == sxSat
  check not r.trusted
  check r.soundness.undefinedKinds == {UbKind(ubTailUnverified)}

suite "int6-w2: sequtils' unCheckedInc outside sequtils' routines":
  test "natively an {.all.} import steps a user's variable unchecked":
    var x = high(int)
    var raised = false
    try: bump(x)
    except OverflowDefect: raised = true
    check not raised   # the C addition, undefined: no OverflowDefect

  test "an opaque user routine stepping with it is unreadable":
    check native(sutBump(5)) == "hit"
    unreadable(sutBump)

suite "int6-w2: walker version":
  test "walker version floor >= 483":
    check parseInt(symexWalkerVersion) >= 483
