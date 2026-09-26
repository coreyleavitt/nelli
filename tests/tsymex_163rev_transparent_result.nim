## Issue #163 review finding R10 (Medium) -- `feOpaqueCallUnmodelled`'s
## message tells the caller to "mark it `{.symexTransparent.}` and symex will
## drop it instead". That is correct advice for a genuinely `{.symexOpaque.}`
## callee, but it is actively wrong for a callee that already carries
## `{.symexTransparent.}` and whose RESULT IS USED -- that call falls back to
## `{.symexOpaque.}` handling at the expression-position arm
## (`dsl_parser.nim`), reaches the SAME generic message, and gets told to
## apply a pragma it already has. The real problem is that the promise is
## honoured only in STATEMENT position, which was documented in
## `symex.nim`'s pragma comment but never surfaced at the point of failure.
##
## R7 (`tsymex_163rev_transparent_guard.nim`) closed the SIBLING route --
## statement position, non-inert argument -- with a parse-time
## `feTransparentArgNotInert` degrade emitted alongside the generic message.
## This suite closes the REMAINING route (expression position, result used)
## the same way: a parse-time `feTransparentResultUsed` degrade, naming the
## callee and the real broken promise, emitted alongside (not instead of) the
## generic `feOpaqueCallUnmodelled` the resulting opaque-call fallback still
## produces at walk time.
##
## `tsymex_163_opaque_transparent.nim`'s W5 suite already pins this shape's
## VERDICT behaviour (`usesProbe` falls back to opaque, `sxUnknown`, no
## internal fault) -- this suite is about the MESSAGE, not the verdict, so it
## does not duplicate those assertions.
##
## Method note (inherited from #162/#163): every symbolic expectation below
## is paired with the SAME computation run for real in this file.
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/coverage

const Magic = 0x5A4D

# --- a transparent callee whose result IS used -- the expression-position
# over-claim route R10 closes. `probeR` reads a MODULE-LEVEL var on purpose
# (mirrors `tsymex_163_opaque_transparent.nim`'s W5 `probe`): the walker has
# no `env` binding for a module-level var, so a wrong fallback here would hit
# a free-reference internal fault, not merely a precision loss.

var probeRState = 11   ## module-level: unmodellable, and deliberately so

proc probeR(): int {.symexTransparent.} = probeRState

proc usesProbeR(x: int) =
  let p = probeR()               ## result is USED: the promise is NOT honoured
  if x + p == Magic:
    symexTarget("hit_r")

suite "#163 review R10 -- a transparent result used in expression position names the real problem":

  test "oracle: usesProbeR really gates on x + 11 == Magic":
    doAssert probeRState == 11
    usesProbeR(0)
    usesProbeR(Magic - 11)

  test "the specific finding fires, naming the callee and the real problem":
    ## RFC-0005 S8 (§13.3, i3): the finding rides the annotation-violation
    ## channel (`r.annotationViolations`), not `r.errors` -- it is not a
    ## decline. The generic opaque-call degrade still taints the path.
    let r = symexFind(usesProbeR, tLabel("hit_r"))
    var generic = false
    var internalFault = false
    var retiredKind = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feOpaqueCallUnmodelled and "probeR" in e.msg:
        generic = true
      if e.kind == weInternalWalkerFault:
        internalFault = true
      if e.kind in {feTransparentResultUsed, feTransparentArgNotInert}:
        retiredKind = true
    check r.annotationViolations.len == 1
    let av = r.annotationViolations[0]
    check av.pragma == saSymexTransparent
    check av.kind == avResultUsed
    check av.callee == "probeR"
    check "tsymex_163rev_transparent_result" in av.site
    let specificMsg = av.msg
    # Never a clean-looking verdict the model cannot back: the opaque
    # fallback taints the hit, so the verdict is `sxUnknown` unless S10's
    # replay confirmed the solver's witness against the real `usesProbeR`.
    check r.status in {sxUnknown, sxSat}
    if r.status == sxSat:
      check r.witness[0] + probeRState == Magic
    check generic
    check not internalFault
    check not retiredKind
    # The whole point of R10: the specific message must NOT repeat the
    # generic message's (here, wrong) advice to apply the pragma -- the
    # callee already carries it. It must instead name the actual constraint:
    # the promise only holds in statement position.
    check "symexTransparent" in specificMsg
    check "statement position" in specificMsg
    check "mark it" notin specificMsg

  test "non-regression -- a statement-position transparent call still gets no such degrade":
    ## `withAnnounce` (`tsymex_163_opaque_transparent.nim`'s W5 shape) honours
    ## the pragma in statement position -- must not spuriously pick up R10's
    ## new kind.
    proc announceR() {.symexTransparent.} =
      discard
    proc withAnnounceR(x: int) =
      announceR()
      if x == Magic:
        symexTarget("hit_announce")
    let r = symexFind(withAnnounceR, tLabel("hit_announce"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    check r.annotationViolations.len == 0   # RFC-0005 S8 channel

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    check parseInt(symexWalkerVersion) >= 135
