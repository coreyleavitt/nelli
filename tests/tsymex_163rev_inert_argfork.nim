## Issue #163 review finding R1 (Critical, soundness regression) -- an opaque
## call the parser proved INERT (`isInertOpaqueCall`, dsl_parser.nim) is a
## no-op in the walker's fast path (`runtime.nim`'s `if stmt.opaqueInert:
## return paths`), but the fast path never lowers `stmt.cargs`. Lowering is
## the ONLY place that populates the raise-fork sinks (`divByZeroConds`,
## `overflowConds`, `parseIntRaiseConds`, `strIndexOobConds`, ...) that
## `drainScalarRaiseForks` turns into raise obligations. Skip the lowering
## and the obligation never exists -- so an argument expression that would
## raise for REAL (div/mod by zero, signed overflow, `parseInt`, `s[i]`,
## seq slice OOB -- `rhsHasInlineDefectFork`'s class) is silently admitted,
## and the solver is free to pick the raising input for a target reached
## only past the call.
##
## `isInertArg` (dsl_parser.nim) checks only the argument's STATIC RESULT
## TYPE (`a.typeKind in inertArgTypeKinds`), never its expression shape --
## so `sink(a div b)` is misclassified inert exactly the same way
## `sink(x)` (a genuinely inert plain-value argument) is.
##
## NOTE on the SUT shape: the review's own illustration uses `echo(a div b)`.
## A user `{.symexOpaque.}` proc reaches the identical `isInertOpaqueCall`/
## `mkOpaqueCall` code path as a stdlib `OpaqueEffectfulProcs` entry like
## `echo` (`dsl_parser.nim`'s `m.kind == smkOpaqueEffectful or
## hasSymexOpaquePragma(calleeSym)` disjunction) -- so a `{.symexOpaque.}`
## sink reproduces the SAME defect. `echo` specifically is avoided here
## because passing a non-string value through it goes through an
## UNRELATED, pre-existing gap (Nim inserts a hidden `$`-conversion call
## for a non-string vararg element, and the expression parser's `nnkHiddenCallConv`
## is not a supported node kind at all -- a separate, orthogonal limitation
## this file must not conflate with R1; `tsymex_163_opaque_transparent.nim`'s
## own `withEcho` sidesteps the same gap by echoing a string LITERAL, never
## the int parameter itself).
##
## Before issue #163 slice 4 introduced the fast path, EVERY opaque call
## tainted (`w.sawUnknown = true`), so this was harmless: taint alone made
## any downstream target degrade to `sxUnknown`. The fast path removed the
## taint and left the missing lowering underneath. This is a REGRESSION,
## not a pre-existing gap.
##
## Method note (inherited from #162/#163audit): every symbolic expectation
## below is paired with the SAME computation run for real in this file.
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

const Magic = 0x5A4D

# A user `{.symexOpaque.}` proc with a single plain-`int` formal -- reaches
# `isInertOpaqueCall` exactly like `echo` does, without echo's unrelated
# `varargs[string, `$`]` conversion gap.
proc sink(x: int) {.symexOpaque.} = discard

# --- headline repro: div-by-zero inside an "inert" opaque call's argument --
# `a div b`'s STATIC type is `ntyInt` (in `inertArgTypeKinds`), so
# `isInertOpaqueCall` classifies the call inert -- even though `a div b`
# itself can raise `DivByZeroDefect`.

proc withDivArgRT(a, b: int): int =
  a div b

proc withDivArg(a, b: int) =
  sink(a div b)
  symexTarget("reached")

# --- second member of the affected class: `parseInt` in an inert call's
# argument. `parseInt(s)`'s result type is also `ntyInt`, so this call is
# inert by the same misclassification.

proc withParseIntArgRT(s: string): int =
  parseInt(s)

proc withParseIntArg(s: string) =
  sink(parseInt(s))
  symexTarget("reached")

# --- non-regression: slice 4's win must survive. A GENUINELY inert opaque
# call (a bare plain-value argument, no inline defect-fork shape at all)
# must still not taint the walk -- this is the entire point of the fast
# path this fix must not undo.

proc withPlainSink(x: int) =
  sink(x)
  if x == Magic:
    raise newException(ValueError, "magic")
  symexTarget("t_reached")

suite "#163 review R1 -- inert opaque calls assert their arguments' defect forks":

  test "oracle: a div b really raises DivByZeroDefect at b == 0, and only then":
    expect DivByZeroDefect:
      discard withDivArgRT(1, 0)
    check withDivArgRT(10, 5) == 2

  test "div-by-zero inside an inert opaque call's argument is found, not lost":
    ## Before the fix: `stmt.cargs` is never lowered on the inert fast path,
    ## so `divByZeroConds` is never populated and no raise fork exists at
    ## all -- this target is not found as a raise.
    let r = symexFind(withDivArg, tRaisedExn("DivByZeroDefect"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

  test "reaching the target past the call requires the real non-raising input":
    ## Before the fix: with no fork asserted, the solver is free to pick
    ## ANY (a, b) for a target that is trivially reachable through an
    ## inert-classified call -- including b == 0, which in REAL Nim raises
    ## `DivByZeroDefect` out of the `sink` argument before `symexTarget` is
    ## ever reached. That is the unsound witness this test pins against.
    let r = symexFind(withDivArg, tLabel("reached"))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] != 0

  test "oracle: parseInt raises ValueError on a non-digit string, and only then":
    expect ValueError:
      discard withParseIntArgRT("abc")
    check withParseIntArgRT("42") == 42

  test "parseInt inside an inert opaque call's argument is found, not lost":
    let r = symexFind(withParseIntArg, tRaisedExn("ValueError"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "ValueError"

  test "oracle: withPlainSink raises on Magic, and only then":
    expect ValueError:
      withPlainSink(Magic)
    withPlainSink(0)

  test "non-regression -- a raise BEHIND a plain-value inert call is found, not degraded":
    let r = symexFind(withPlainSink, tRaisedExn("ValueError"))
    var opaqueUnmodelled = false
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled: opaqueUnmodelled = true
      if e.kind == weInternalWalkerFault: internalFault = true
    check r.status == sxRaised
    check not opaqueUnmodelled
    check not internalFault

  test "non-regression -- a label BEHIND the same plain-value inert call is reachable":
    let r = symexFind(withPlainSink, tLabel("t_reached"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    ## One bump covers R1/R2/R3/R4/R15 -- every one a verdict change, so a
    ## cache entry written under any one of them can replay a wrong verdict
    ## under the others. Compared numerically, not lexicographically:
    ## `"1000" < "135"` as strings.
    check parseInt(symexWalkerVersion) >= 135
