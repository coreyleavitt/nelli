## Issue #163 review finding R7 (Medium, CONFIRMED with a concrete wrong
## verdict) -- `dsl_parser.nim`'s statement-position `{.symexTransparent.}`
## arm DELETED the call unconditionally, never consulting `isInertArg`/
## `isInertOpaqueCall` -- the very predicate its OPAQUE sibling arm applies
## to the same argument shapes a few lines later. A `var` formal
## (`nnkHiddenAddr`) or a `ref`/`ptr`/possibly-ref-carrying-object argument
## lets the real callee write through or observe state a deleted call's
## absence cannot account for, and `parseExpr` on `nnkHiddenAddr` is a READ
## (it unwraps to the symbol's current value, no invalidation) -- so the
## `var` pointee is never havoc'd either. This is the statement-position
## twin `tsymex_163_opaque_transparent.nim` pins for the OPAQUE arm at
## lines ~175 (`withMutate`/`mutate(x: var int) {.symexOpaque.}`) and ~185
## (`withTouch`/`touch(n: Box) {.symexOpaque.}`) -- that file never got a
## TRANSPARENT counterpart, and the counterpart is exactly where R7 lived.
##
## The fix gates the statement-position deletion on `isInertOpaqueCall`: a
## non-inert transparent callee now falls through to the opaque arm instead
## (mirrors the EXISTING expression-position fallback, `dsl_parser.nim`
## ~3925-3940, where a used transparent result already degrades to opaque
## rather than being solved through) -- fails safe (`sxUnknown`) instead of
## a silent wrong `sxUnsat`. A parse-time `feTransparentArgNotInert` names
## the callee and the broken promise, alongside the generic
## `feOpaqueCallUnmodelled` the opaque-call fallback itself produces at walk
## time.
##
## Method note (inherited from #162/#163): every symbolic expectation below
## is paired with the SAME computation run for real in this file. A taint
## (or an anti-taint) bug is exactly the shape where a test can encode the
## engine's own wrong model and pass; running Nim removes the model from
## the loop.
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/coverage

const Magic = 0x5A4D

# --- headline repro: a var-argument transparent callee ----------------------
# The pragma promises "no argument written through". `mutateT` breaks that
# promise (it is a bad-faith tag, deliberately, to pin the defect) -- before
# the fix the call vanished outright and the env kept `m == x`, so
# `m != x` solved as `x != x` -- unsatisfiable for every input, when in
# REAL Nim it is satisfiable for essentially every input.

proc mutateT(x: var int) {.symexTransparent.} =
  inc x

proc withMutateTRT(x: int): bool =
  var m = x
  mutateT(m)
  m != x

proc withMutateT(x: int) =
  var m = x
  mutateT(m)
  if m != x:
    symexTarget("t_bug")

# --- second member of the affected class: a ref-argument transparent callee -
# A copied `ref` argument still lets the callee write through the pointee,
# exactly the `withTouch`/`touch(n: Box) {.symexOpaque.}` shape this file's
# sibling suite pins for the opaque arm.

type
  Box = ref object
    v: int

proc touchT(n: Box) {.symexTransparent.} =
  inc n.v

proc withTouchTRT(x: int): bool =
  let b = Box(v: x)
  touchT(b)
  b.v != x

proc withTouchT(x: int) =
  let b = Box(v: x)
  touchT(b)
  if b.v != x:
    symexTarget("t_touched")

# --- non-regression: a genuinely inert transparent callee is STILL deleted
# and STILL does not taint -- the real `{.cover.}`/`recordEdge` path, #163's
# whole win, must survive this gate unchanged.

proc coveredT(x: int) {.cover.} =
  if x == Magic: raise newException(ValueError, "magic")

suite "#163 review R7 -- a transparent call is only deleted when it is provably inert":

  test "oracle: mutateT really increments its var argument, every time":
    check withMutateTRT(0) == true
    check withMutateTRT(Magic) == true
    check withMutateTRT(-1) == true

  test "a var-argument transparent callee must not falsely report unreachable":
    ## Before the fix: `mutateT(m)` is deleted outright, so `m != x` solves
    ## as `x != x` -- `sxUnsat` -- for a target reachable for essentially
    ## every input in real Nim. `sxUnsat` here IS the wrong-verdict bug; the
    ## fix's fail-safe floor is `sxUnknown`, never `sxUnsat`.
    let r = symexFind(withMutateT, tLabel("t_bug"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status != sxUnsat

  test "the var-argument overclaim degrades classified, naming the callee":
    let r = symexFind(withMutateT, tLabel("t_bug"))
    var specific = false
    var generic = false
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feTransparentArgNotInert and "mutateT" in e.msg:
        specific = true
      if e.kind == feOpaqueCallUnmodelled and "mutateT" in e.msg:
        generic = true
      if e.kind == weInternalWalkerFault:
        internalFault = true
    check r.status == sxUnknown
    check specific
    check generic
    check not internalFault

  test "oracle: touchT really writes through its ref argument, every time":
    check withTouchTRT(0) == true
    check withTouchTRT(Magic) == true
    check withTouchTRT(-7) == true

  test "a ref-argument transparent callee must not falsely report unreachable":
    ## Before the fix: `touchT(b)` is deleted outright, so the pointee's
    ## field is never invalidated and `b.v != x` solves against the
    ## UNCHANGED `b.v == x`, i.e. `x != x` -- unsatisfiable for every input,
    ## exactly mirroring the var case above (deliberately: `inc n.v` through
    ## the ref, `b.v != x`, is the ref-argument twin of `inc x`/`m != x`
    ## through the var). In REAL Nim `n` aliases `b`, so `b.v` really is
    ## `x + 1` after the call and the target is reachable for essentially
    ## every input -- a concrete false `sxUnsat`, not merely a missed
    ## precision opportunity.
    let r = symexFind(withTouchT, tLabel("t_touched"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status != sxUnsat

  test "the ref-argument overclaim degrades classified, naming the callee":
    let r = symexFind(withTouchT, tLabel("t_touched"))
    var specific = false
    var generic = false
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feTransparentArgNotInert and "touchT" in e.msg:
        specific = true
      if e.kind == feOpaqueCallUnmodelled and "touchT" in e.msg:
        generic = true
      if e.kind == weInternalWalkerFault:
        internalFault = true
    check r.status == sxUnknown
    check specific
    check generic
    check not internalFault

  test "oracle: a {.cover.}'d proc still raises on Magic, and only then":
    expect ValueError:
      coveredT(Magic)
    coveredT(0)

  test "non-regression -- a genuinely inert transparent call is still deleted, not tainted":
    ## `{.cover.}`'s `recordEdge(id)` is a plain int literal argument --
    ## `isInertOpaqueCall` classifies it inert, so the gate this fix adds
    ## must still let the deletion through unchanged. This is issue #163's
    ## entire win and must survive R7's fix intact.
    let r = symexFind(coveredT, tRaisedExn("ValueError"))
    var opaqueUnmodelled = false
    var specificDegrade = false
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled: opaqueUnmodelled = true
      if e.kind == feTransparentArgNotInert: specificDegrade = true
      if e.kind == weInternalWalkerFault: internalFault = true
    check r.status == sxRaised
    check not opaqueUnmodelled
    check not specificDegrade
    check not internalFault

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    check parseInt(symexWalkerVersion) >= 135
