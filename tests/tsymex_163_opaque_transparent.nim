## Issue #163 — an opaque call ahead of the target must not cost the answer.
##
## Two defects, one arm. `walk`'s `#137` opaque-call arm (`runtime.nim`) set
## `w.sawUnknown` bare and tainted every continuation, so:
##
##  1. nelli's OWN instrumentation (`{.cover.}`'s `recordEdge`, `{.covercmp.}`'s
##     `logCmp`) degraded the whole run — the fuzzer needs `{.cover.}` on the
##     code under test, and the solver could not see through it, so one proc
##     could not serve both;
##  2. the degrade was UNCLASSIFIED, tripping the Invariant-7 backstop
##     (`weInternalWalkerFault`, "the walker itself hit a bug here") instead of
##     naming the call that cost the answer.
##
## Method note (inherited from #162): every symbolic expectation below is
## paired with the SAME computation run for real in this file. A taint bug is
## exactly the shape where a test can encode the engine's own wrong model and
## pass; running Nim removes the model from the loop.
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/coverage

const Magic = 0x5A4D

# --- the instrumented SUTs -------------------------------------------------
# `{.cover.}` injects `recordEdge(id)` at the top of every branch arm, so the
# raise below sits BEHIND an opaque call on its own path.

proc covered(x: int) {.cover.} =
  if x == Magic: raise newException(ValueError, "magic")

# `{.covercmp.}` is a `{.cover.}` SIBLING, not an extension: it rewrites each
# COMPARISON into a temp-bind + `logCmp(lTmp, rTmp, op)` + the comparison, so
# its instrumentation lands in a different AST position (and, unlike
# `recordEdge`, ahead of the branch rather than inside its arm).

proc cmpLogged(x: int) {.covercmp.} =
  if x == Magic: raise newException(ValueError, "magic")

proc bothInstrumented(x: int) {.cover, covercmp.} =
  if x == Magic: raise newException(ValueError, "magic")

# The instrumentation need not be on the proc under query: an uninstrumented
# SUT calling an instrumented helper walks the helper's body, instrumentation
# and all.

proc innerCovered(x: int): int {.cover.} =
  if x == Magic: 1 else: 0

proc callsCovered(x: int) =
  if innerCovered(x) == 1: raise newException(ValueError, "magic")

# --- calls that are GENUINELY opaque ---------------------------------------
# Where the taint is right, the degrade must still say WHY, and name the call
# that cost the answer. Before #163 this arm set `w.sawUnknown` bare, which
# tripped the Invariant-7 backstop and reported `weInternalWalkerFault` -- "the
# walker itself hit a bug here" -- for an ordinary unmodelled call.

proc readSensor(): int {.symexOpaque.} = 42

proc usesSensor(x: int) =
  let s = readSensor()          ## result is USED: the taint is correct
  if x + s == Magic: raise newException(ValueError, "magic")

suite "issue 163 -- nelli's own instrumentation is transparent to the solver":

  test "oracle: every instrumented SUT really does raise on Magic, and only then":
    for sut in [covered, cmpLogged, bothInstrumented, callsCovered]:
      expect ValueError:
        sut(Magic)
      sut(0)

  test "a {.cover.}'d proc's raise is FOUND, not degraded to sxUnknown":
    let r = symexFind(covered, tRaisedExn("ValueError"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised

  test "a {.covercmp.}'d proc's raise is FOUND -- logCmp sits AHEAD of the branch":
    let r = symexFind(cmpLogged, tRaisedExn("ValueError"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised

  test "{.cover, covercmp.} together are still transparent":
    let r = symexFind(bothInstrumented, tRaisedExn("ValueError"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised

  test "instrumentation in a CALLEE does not degrade its uninstrumented caller":
    let r = symexFind(callsCovered, tRaisedExn("ValueError"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised

suite "issue 163 -- a genuine opaque call degrades with its name attached":

  test "a used opaque result still degrades -- but says why, and names the callee":
    let r = symexFind(usesSensor, tRaisedExn("ValueError"))
    var classified = false
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "readSensor" in e.msg:
        classified = true
      if e.kind == weInternalWalkerFault:
        internalFault = true
    check r.status == sxUnknown
    check classified
    check not internalFault

# --- slice 4: a value-only, statement-position opaque call is INERT --------
# `echo` is the motivating case: void, every argument plainly value-typed, no
# result bound. It costs nothing -- no taint, no classified degrade -- for a
# target reached either on the raise path or past it.

proc withEcho(x: int) =
  echo "checking"
  if x == Magic:
    raise newException(ValueError, "magic")
  symexTarget("t_echo")

# The predicate is NOT "void means inert": a `var`-param opaque callee still
# writes through, so it still taints even though it too returns nothing.

proc mutate(x: var int) {.symexOpaque.} =
  x.inc

proc withMutate(x: int) =
  var m = x
  mutate(m)
  if x == Magic: raise newException(ValueError, "magic")

# Nor is it "no `var` formal means inert": a copied `ref` ARGUMENT still lets
# the callee write through the pointee, so it still taints too.

type
  Box = ref object
    v: int

proc touch(n: Box) {.symexOpaque.} =
  discard

proc withTouch(x: int) =
  let b = Box(v: x)
  touch(b)
  if x == Magic: raise newException(ValueError, "magic")

suite "issue 163 slice 4 -- an inert opaque call does not taint the walk":

  test "oracle: withEcho raises on Magic, and only then, and prints to stdout":
    expect ValueError:
      withEcho(Magic)
    withEcho(0)

  test "a raise BEHIND a statement-position echo is found, not degraded":
    let r = symexFind(withEcho, tRaisedExn("ValueError"))
    var opaqueUnmodelled = false
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled: opaqueUnmodelled = true
      if e.kind == weInternalWalkerFault: internalFault = true
    check r.status == sxRaised
    check not opaqueUnmodelled
    check not internalFault

  test "a label BEHIND the same echo, on the non-raise path, is reachable":
    let r = symexFind(withEcho, tLabel("t_echo"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

  test "a var-param opaque callee still degrades -- void is not the whole test":
    let r = symexFind(withMutate, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "mutate" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

  test "a ref-arg opaque callee still degrades -- a copied ref can be written through":
    let r = symexFind(withTouch, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "touch" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

suite "issue 163 -- walker version pin":

  test "walker version floor >= 132 (#163: opaque-call taint + classification)":
    ## 131 is slice 3 (the degrade names the callee -- an `r.errors` change,
    ## and `r.errors` is cached). 132 is slice 4 (an inert opaque call does
    ## not taint -- a verdict change). Slice 1 deliberately bumped NOTHING:
    ## `{.symexTransparent.}` is a parse-time drop, so the IR itself differs
    ## and `canonicalize(prog)` moves the cache key without help.
    check parseInt(symexWalkerVersion) >= 132
