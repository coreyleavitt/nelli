## RFC-0010 slice A1 — pins for `zeroFilled`, the macro A1 used to stage the
## flip. **Deleted by A3**, along with `tests/zerofill.nim`, once the last pin
## is gone from the suite.
##
## This file also carried A1's characterization of the defect: assertions that
## the documented object-literal idiom built a materially different engine than
## `defaultSettings()`. Those were green at A1 and went red the moment A2
## landed, which is what a characterization test is for and is the direction
## the seed had inverted. §6 has A3 delete them; they are deleted here instead,
## because the alternative is committing a knowingly-red suite for the length
## of a round, and their result is now permanently recorded by
## `tests/tconfigdefaults.nim` asserting the opposite. For the record, at A2
## they failed exactly as designed: the README literal stopped differing from
## the defaults in eight fields, stopped exhausting a filtered property after
## two examples, and stopped silencing labels and event output.
##
## What remains is the macro's own pins, which stay load-bearing while any
## `zeroFilled(` call is left in the suite.

import std/unittest
import nelli
import zerofill

# A type that declares field defaults, which is the only place the macro's
# behaviour is observable: `zeroFilled` exists to defeat declared defaults, so
# a type without them cannot tell a working macro from a broken one.
type PinProbe = object
  a: int = 100
  b: bool = true
  c: string = "set"
  d: int

suite "RFC-0010 A1 — zeroFilled defeats declared field defaults":

  test "an unwrapped partial literal picks up declared defaults":
    # Nim 2.2.10's behaviour, and the whole mechanism RFC-0010 adopts. If this
    # ever fails, §3's empirical result has been invalidated and A2 is built
    # on sand.
    let lit = PinProbe(d: 7)
    check lit.a == 100
    check lit.b
    check lit.c == "set"
    check lit.d == 7

  test "zeroFilled zeroes every field the literal did not list":
    let pinned = zeroFilled(PinProbe(d: 7))
    check pinned.a == 0
    check not pinned.b
    check pinned.c == ""
    check pinned.d == 7

  test "zeroFilled preserves explicitly-written values, including zeros":
    let pinned = zeroFilled(PinProbe(a: 0, b: false, c: "", d: 1))
    check pinned.a == 0
    check not pinned.b
    check pinned.c == ""
    check pinned.d == 1

  test "zeroFilled on an empty literal is the all-zero value":
    let pinned = zeroFilled(PinProbe())
    check pinned == PinProbe(a: 0, b: false, c: "", d: 0)

  test "zeroFilled evaluates at compile time":
    # A1 wrapped `const` settings literals too, so the rewrite has to survive
    # VM evaluation, not just runtime.
    const pinned = zeroFilled(PinProbe(d: 3))
    check pinned.a == 0
    check pinned.d == 3

  test "zeroFilled now does real work on Settings":
    # At A1 this was a no-op and asserted equality with the bare literal. After
    # A2 the bare literal carries the defaults and the pinned one does not —
    # which is precisely why the 115 pinned call sites did not change
    # behaviour when the defaults flipped underneath them.
    let pinned = zeroFilled(Settings(maxExamples: 7))
    check pinned.maxExamples == 7
    check pinned.maxRejections == 0
    check not pinned.autoLabels
    check pinned != Settings(maxExamples: 7)
