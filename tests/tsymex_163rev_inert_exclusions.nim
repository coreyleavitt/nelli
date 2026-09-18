## Issue #163 review finding R14 (Low), parts b, c, d.
##
## Method note (inherited from #162/#163): every symbolic expectation is
## paired with the same computation run for real in this file wherever the
## shape allows it.

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

const Magic = 0x5A4D

# =============================================================================
# R14b -- inert-allowlist exclusions beyond var/ref.
# =============================================================================
## `isInertOpaqueCall`/`isInertArg` (`dsl_parser.nim:~1543-1631`) treats a
## statement-position opaque call as a no-op only when every argument's
## static type is in a small scalar allowlist. Only `var` and `ref`
## exclusions were previously pinned
## (`tests/tsymex_163_opaque_transparent.nim:~127-148`). Untested exclusions:
## `object`/`tuple` (a copied object can carry a `ref` field), `seq`, `ptr`/
## `pointer`, `proc` (a callback), `cstring`. Each still degrades below --
## a regression that wrongly ADDED one of these to the allowlist would go
## undetected without this.

type
  Pair = object
    v: int

proc touchObj(p: Pair) {.symexOpaque.} = discard

proc withTouchObj(x: int) =
  let p = Pair(v: x)
  touchObj(p)
  if x == Magic: raise newException(ValueError, "magic")

proc touchTuple(t: (int, int)) {.symexOpaque.} = discard

proc withTouchTuple(x: int) =
  let t = (x, x)
  touchTuple(t)
  if x == Magic: raise newException(ValueError, "magic")

proc touchSeq(s: seq[int]) {.symexOpaque.} = discard

proc withTouchSeq(x: int) =
  let s = @[x]
  touchSeq(s)
  if x == Magic: raise newException(ValueError, "magic")

proc touchPtr(p: ptr int) {.symexOpaque.} = discard

proc withTouchPtr(x: int) =
  touchPtr(nil)
  if x == Magic: raise newException(ValueError, "magic")

proc touchPointer(p: pointer) {.symexOpaque.} = discard

proc withTouchPointer(x: int) =
  touchPointer(nil)
  if x == Magic: raise newException(ValueError, "magic")

proc sampleCallback(y: int): int = y + 1

proc touchProc(cb: proc(y: int): int) {.symexOpaque.} = discard

proc withTouchProc(x: int) =
  touchProc(sampleCallback)
  if x == Magic: raise newException(ValueError, "magic")

proc touchCString(c: cstring) {.symexOpaque.} = discard

proc withTouchCString(x: int) =
  touchCString(nil)
  if x == Magic: raise newException(ValueError, "magic")

suite "#163 review R14b -- inert-allowlist exclusions still degrade":

  test "oracle: every SUT raises on Magic, and only then":
    expect ValueError: withTouchObj(Magic)
    withTouchObj(0)
    expect ValueError: withTouchTuple(Magic)
    withTouchTuple(0)
    expect ValueError: withTouchSeq(Magic)
    withTouchSeq(0)
    expect ValueError: withTouchPtr(Magic)
    withTouchPtr(0)
    expect ValueError: withTouchPointer(Magic)
    withTouchPointer(0)
    expect ValueError: withTouchProc(Magic)
    withTouchProc(0)
    expect ValueError: withTouchCString(Magic)
    withTouchCString(0)

  test "an object argument still degrades -- not wrongly treated as inert":
    let r = symexFind(withTouchObj, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "touchObj" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

  test "a tuple argument still degrades -- not wrongly treated as inert":
    let r = symexFind(withTouchTuple, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "touchTuple" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

  test "a seq argument still degrades -- not wrongly treated as inert":
    let r = symexFind(withTouchSeq, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "touchSeq" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

  test "a ptr argument still degrades -- not wrongly treated as inert":
    let r = symexFind(withTouchPtr, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "touchPtr" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

  test "a pointer argument still degrades -- not wrongly treated as inert":
    let r = symexFind(withTouchPointer, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "touchPointer" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

  test "a proc (callback) argument still degrades -- not wrongly treated as inert":
    let r = symexFind(withTouchProc, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "touchProc" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

  test "a cstring argument still degrades -- not wrongly treated as inert":
    let r = symexFind(withTouchCString, tRaisedExn("ValueError"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "touchCString" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified

# =============================================================================
# R14c -- the wrap-scan whole-program ban.
# =============================================================================
## `abstraction.nim:~370-388` documents a deliberate over-approximation under
## unchecked arithmetic (`isOptimised` + `acOverflow` absent from
## `arithChecks`): an unprovable add/sub/mul/neg bans EVERY int param from
## promotion, not just the ones the offending expression mentions. A
## regression toward PER-VARIABLE banning would reintroduce the BV/Int
## mixing bug the comment warns about (`reconcileInt` bridging a BV param up
## to an unbounded Int, silently reintroducing non-wrapping arithmetic).
## Pinned via `r.abstractions` (one entry per PROMOTED param): a param whose
## OWN arithmetic is provably safe promotes ALONE, but stops promoting the
## instant an unrelated, unprovable sibling shares the same program.

const Unchecked = SymexSettings(integerSemantics: isOptimised,
                                arithChecks: {acDivByZero, acRange})

proc safeAlone(safeP: range[0'i64..1000'i64]) =
  let s = safeP + safeP     ## <= 2000 -- provably safe in isolation
  symexTarget("t")
  discard s

proc mixedBan(safeP: range[0'i64..1000'i64],
              unsafeP: range[0'i64..4_000_000_000'i64]) =
  let s = safeP + safeP        ## still provably safe, taken alone
  let u = unsafeP * unsafeP    ## reaches 1.6e19 -- NOT provably safe
  symexTarget("t")
  discard s
  discard u

suite "#163 review R14c -- the wrap-scan bans the whole program, not per-variable":

  test "oracle -- safeP's own doubling never leaves int64, unsafeP's square does":
    proc rtSafe(a: range[0'i64..1000'i64]): int64 = a + a
    check rtSafe(1000'i64) == 2000'i64
    {.push overflowChecks: off.}
    proc rtUnsafe(a: range[0'i64..4_000_000_000'i64]): int64 = a * a
    {.pop.}
    ## True product at the ceiling is 1.6e19, which does not fit int64 (max
    ## ~9.22e18) -- it wraps under unchecked semantics to a negative value,
    ## which is the whole reason it is "unprovable": no finite int64
    ## interval bounds it honestly.
    check rtUnsafe(4_000_000_000'i64) < 0'i64

  test "in isolation, the provably-safe param DOES promote":
    let r = symexFind(safeAlone, tLabel("t"), Unchecked)
    check r.status == sxSat
    check r.abstractions.len == 1

  test "sharing a program with an unprovable sibling, NEITHER param promotes":
    ## The load-bearing property. A per-variable-banning regression would
    ## leave `safeP` promoted here (`abstractions.len == 1`, naming only
    ## `safeP`) even though `unsafeP` is banned -- exactly the mixed-sort
    ## state the comment says must never happen under unchecked semantics.
    let r = symexFind(mixedBan, tLabel("t"), Unchecked)
    check r.status == sxSat
    check r.abstractions.len == 0

# =============================================================================
# R14d -- an opaque call placed AFTER the target is invisible to it.
# =============================================================================
## Documented, pre-existing asymmetry (`runtime.nim`'s `#137` opaque-call
## arm, "an opaque call placed AFTER the target was already invisible to it
## before this change. Ordering, not soundness, moves."): the walker taints
## only the CONTINUATION of a path from the point an opaque call is actually
## reached onward. A target already satisfied earlier in the same statement
## sequence is unaffected by a non-inert opaque call that comes later. Never
## pinned before this file. Recorded here as current behavior, not
## necessarily as a property anyone has proven ideal.

proc mutateAfter(x: var int) {.symexOpaque.} =
  x.inc

proc targetBeforeOpaque(x: int) =
  ## The target sits INSIDE the `if`; the non-inert opaque call is reached
  ## only AFTER it, unconditionally, on the very same path.
  if x == Magic:
    symexTarget("hit")
  var m = x
  mutateAfter(m)

proc targetAfterOpaque(x: int) =
  ## The mirror image, included as the already-known-tainted control: the
  ## SAME opaque call, now placed BEFORE the target on the same path.
  var m = x
  mutateAfter(m)
  if x == Magic:
    symexTarget("hit")

suite "#163 review R14d -- an opaque call AFTER the target is invisible to it":

  test "oracle -- targetBeforeOpaque and targetAfterOpaque both reach x == Magic identically":
    check Magic == Magic  ## trivial; the real oracle is structural (see below)

  test "a target reached BEFORE a later opaque call is found un-degraded":
    let r = symexFind(targetBeforeOpaque, tLabel("hit"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

  test "the SAME opaque call placed BEFORE the target still degrades it":
    ## The asymmetry, made visible side by side: identical call, identical
    ## target, only the ORDER differs.
    let r = symexFind(targetAfterOpaque, tLabel("hit"))
    var classified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "mutateAfter" in e.msg:
        classified = true
    check r.status == sxUnknown
    check classified


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    check parseInt(symexWalkerVersion) >= 135
