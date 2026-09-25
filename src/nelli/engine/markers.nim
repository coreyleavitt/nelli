## Symbolic-execution markers — the Z3-free annotations you put in
## PRODUCTION code.
##
## `symexTarget` / `symexAssert` / `symexAssume` say "this is a coverage
## target", "this invariant holds", "this precondition restricts the
## domain". The walker reads them out of the parsed AST; at runtime they are
## a no-op, a `doAssert`, and a no-op respectively. Nothing here touches Z3,
## the walker, or any of the symex stack.
##
## **Why they live in `engine/` and not in `symex.nim`** (RFC-z3-optional
## S1c). Annotations belong in the code being described, so a
## marker-annotated SUT is ordinary library code that happens to be
## symex-legible. Until 0.7.0 these reached ordinary callers only because
## `fuzzmacro` re-exported the whole walker — so removing that re-export,
## which is the point of the RFC, would have made every annotated SUT stop
## compiling under bare `import nelli`, forcing consumers to import the
## Z3-bound module *from production code* to keep a no-op resolving. That
## is exactly backwards.
##
## `engine.nim` re-exports this module the same way it already re-exports
## `frame`/`eval`/`render`/`targeting`/`phases`, and that chain is already
## public through `nelli.nim` — so this costs zero new lines there.
## `symex.nim` re-exports the same names, so `import nelli/symex` callers
## are unchanged.
##
## `engine/types.nim` was considered as the destination and rejected: it is
## the semantically pure *type* module, and these are procs.
import std/sets

# ---- assertCoveredBy capture context ----------------------------------------
#
# Phase 7's `assertCoveredBy` proves that a user-supplied `testFn`
# exercises a symex-reachable target on its concrete witness. The
# coverage signal is the same `symexTarget(name)` markers the parser
# already recognizes — outside symex they were no-ops, now they
# additionally feed a thread-local hit-set when an `assertCoveredBy`
# capture is active. The cost when no capture is active is one
# threadvar load + branch.
#
# This cluster travels WITH the markers: `symexTarget`'s only non-no-op
# behavior IS `symexCaptureRecord`, so splitting them would leave
# `assertCoveredBy` reading an empty hit-set and failing at a distance.
#
# RFC-0005 S2 (§4.2 "Capture reentrancy"): the context is a STACK of frames.
# Replay (`replayWitness`, `symex.nim`) executes the real SUT and reads its
# hits through this same context -- and after RFC-0005 S10 it does so INSIDE
# `symexFind`, which a user may well call from within their own active
# `assertCoveredBy` capture (or a `testFn` that itself replays). The original
# single-frame shape `clear()`ed the hit-set on `symexCaptureBegin` and went
# inactive on `symexCaptureEnd`, so an engine-internal replay silently wiped
# the user's in-flight hits and blinded the rest of their capture. Now
# `symexCaptureBegin` pushes a fresh frame (saving the enclosing one) and
# `symexCaptureEnd` pops it, restoring the enclosing frame intact.
#
# A hit is recorded into the INNERMOST frame only. That isolation is the
# point: an inner replay runs the SUT on SOLVER-CHOSEN inputs, and letting its
# hits leak outward would credit the user's `testFn` with coverage it never
# earned on its own inputs.

type SymexCaptureCtx* = ref object
  active*:           bool
    ## True iff at least one capture frame is open on this thread.
  hits*:             HashSet[string]
    ## The INNERMOST open frame's hit-set (the one `symexCaptureRecord`
    ## writes and the matching `symexCaptureEnd` returns).
  enclosing*:        seq[HashSet[string]]
    ## RFC-0005 S2: the saved hit-sets of the enclosing open frames,
    ## outermost first. Empty when at most one frame is open.

var symexCapture* {.threadvar.}: SymexCaptureCtx

proc symexCaptureBegin*() =
  ## Opens a new, empty capture frame. Nests: an already-open frame is saved
  ## (NOT cleared) and restored by the matching `symexCaptureEnd` -- RFC-0005
  ## S2's reentrancy fix.
  if symexCapture.isNil:
    symexCapture = SymexCaptureCtx()
  if symexCapture.active:
    symexCapture.enclosing.add move(symexCapture.hits)
  symexCapture.active = true
  symexCapture.hits = initHashSet[string]()

proc symexCaptureEnd*(): HashSet[string] =
  ## Closes the innermost capture frame and returns the set of `symexTarget`
  ## names hit while it was the innermost one. The enclosing frame (if any)
  ## becomes innermost again with its hits intact; after closing the
  ## outermost frame the context is inactive. With no frame open, returns
  ## the empty set.
  if symexCapture.isNil or not symexCapture.active:
    return initHashSet[string]()
  result = move(symexCapture.hits)
  if symexCapture.enclosing.len > 0:
    symexCapture.hits = symexCapture.enclosing.pop()
  else:
    symexCapture.active = false
    symexCapture.hits = initHashSet[string]()

proc symexCaptureRecord*(name: string) {.inline.} =
  if not symexCapture.isNil and symexCapture.active:
    symexCapture.hits.incl(name)

# ---- the markers themselves --------------------------------------------------

proc symexTarget*(name: string) {.inline.} =
  ## Marker: a coverage target for `symexFind(..., tLabel(name))`.
  ## Outside symex, calling this is a no-op — unless an
  ## `assertCoveredBy` capture is active on this thread, in which
  ## case `name` is recorded as hit. Phase 7.
  symexCaptureRecord(name)

proc symexAssert*(cond: bool) {.inline.} =
  ## Marker: an invariant the user claims always holds. Outside
  ## symex, asserted at runtime via `doAssert` so random PBT also
  ## catches violations. Inside symex, the parser maps this to an
  ## IR node the walker treats as a fork point for
  ## `tAssertionViolation` searches.
  doAssert cond, "symexAssert violated"

proc symexAssume*(cond: bool) {.inline.} =
  ## Marker: a precondition restricting the input domain. Phase 1
  ## ships with no-op outside symex (the richer "early-return on
  ## violation" semantics is deferred until needed — `symexAssume`'s
  ## body markers in Phase 1 are recognized by the parser but don't
  ## yet affect the SUT's normal-run behavior). Inside symex, the
  ## walker conjoins `cond` into the path condition.
  discard cond
