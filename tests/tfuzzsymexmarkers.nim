## RFC-z3-optional S1c — the symex markers survive the 0.7.0 break.
##
## `symexTarget` / `symexAssert` / `symexAssume` are annotations you put in
## PRODUCTION code, not in a test: they say "this is a coverage target",
## "this invariant holds", "this precondition restricts the domain". Outside
## symex they are no-ops (or a plain `doAssert`) by design, and they are
## entirely Z3-free.
##
## Until this slice they lived in `symex.nim` and reached ordinary callers
## only because `fuzzmacro` re-exported the whole walker. Dropping that
## re-export — the point of this RFC — would have made every
## marker-annotated SUT stop compiling under bare `import nelli`, forcing
## consumers to import the Z3-bound module *from their production code*
## just to keep a no-op annotation resolving. That is the opposite of the
## seam this RFC builds.
##
## So the markers move to `engine/markers.nim`, which is Z3-free, and reach
## `import nelli` through the already-public `engine` export chain.
## `symex.nim` re-exports them by name, exactly as it already does for
## `engineTypes` symbols, so `import nelli/symex` callers are unchanged.
##
## **This file imports `nelli` and nothing else.** That is the assertion.
## `tests/tz3free_probe.nim` carries the same usage under a compile with no
## z3 on the path at all, so "resolves" and "resolves without the walker"
## are both mechanically checked rather than assumed.
import std/[unittest, sets]
import nelli

proc annotatedSut(x: int): int =
  ## An ordinary production proc carrying all three markers — the shape a
  ## consumer actually writes.
  symexAssume(x >= 0)
  if x > 10:
    symexTarget("big")
    result = x * 2
  else:
    symexTarget("small")
    result = x
  symexAssert(result >= 0)

suite "RFC-z3-optional S1c — symex markers resolve under bare `import nelli`":

  test "all three markers compile and run as their documented no-op selves":
    check annotatedSut(4) == 4
    check annotatedSut(20) == 40

  test "symexAssert still asserts at runtime outside symex":
    # Documented behavior: outside symex it is a real `doAssert`, so random
    # PBT catches violations too. Moving the marker must not quietly turn
    # that into a no-op.
    proc violates() =
      symexAssert(1 == 2)
    expect AssertionDefect:
      violates()

  test "symexTarget records into an active capture, and only into an active one":
    # The capture cluster travels WITH the markers — `symexTarget`'s
    # non-no-op behavior IS `symexCaptureRecord`, so relocating one without
    # the other would leave `assertCoveredBy` reading an empty hit-set and
    # failing at a distance.
    symexCaptureBegin()
    discard annotatedSut(20)
    let hits = symexCaptureEnd()
    check "big" in hits
    check "small" notin hits

    # With no capture active the marker is inert again — the documented
    # cost is one threadvar load and a branch.
    discard annotatedSut(4)
    symexCaptureBegin()
    let empty = symexCaptureEnd()
    check empty.len == 0
