## RFC-0016 review D1 (slice S1): the one owner of the arithmetic regime.
##
## Which signed arithmetic a routine body is parsed and walked under used to be
## decided at a dozen sites in `dsl_parser.nim` and `runtime.nim`, each reading
## `buildWraps()`, `RoutineChecks.overflowOn`, the inherit flag and the IR stamp
## in its own way. This module is the single decision and the single query
## surface; the sites migrate onto it in slices S3 to S6, and S1 adds nothing
## but the module and its tests, so no walker semantics and no key byte moves.
##
## Pure and Z3-free. Two vocabularies, deliberately separate:
##   * `Regime` is what arithmetic IS (checked or unchecked): the question
##     every walker and parser site asks.
##   * `ArithScope` is where a stamp CAME FROM (the build, a pragma row, a
##     stdlib row, or no claim). Its names are cache-key bytes
##     (`canonicalize.nim` renders `$blkArith`), so they are never renamed and
##     `asInherit` stays ordinal 0. It is provenance, read through
##     `ArithStamp`, whose scope is private: only `decide` mints one, and it
##     does so by consulting the admission tables itself (D2).
##
## S1 imports `types` for `ArithScope` and `ArithCheck` (their definitions move
## here in S2, and `types` then imports this module; the `import` below goes
## with the move). Nothing here is read by a parser or walker site yet.
import ./buildprofile
import ./admission
import ./definedness
import ./pragmaaxes
import ./stdlib_rows
import ./types

type
  Regime* = enum
    ## Whether signed arithmetic is checked (`OverflowDefect`, `DivByZeroDefect`
    ## raise) or unchecked (the C operation, undefined on overflow unless
    ## `-fwrapv`) where the code being parsed or walked now stands.
    rgChecked
    rgUnchecked

  ArithStamp* = object
    ## The IR stamp of a routine body. The scope is private: a stamp is made by
    ## `decide`/`stampFor` and by nothing else (D2).
    scope: ArithScope

  RoutineArithFacts* = object
    ## What the parser knows of a routine, in this module's terms. Copied from
    ## `RoutineChecks` as returned (S3's adapter), never recomputed (F-4).
    readable*: bool         ## `RoutineChecks.why.len == 0`
    overflowOn*: bool       ## `RoutineChecks.overflowOn`, as returned
    overflowDeviates*: bool ## `coOverflow in RoutineChecks.checks`: the
                            ## routine's overflow checks may differ from the
                            ## build's. NOT `not overflowOn`: a routine of the
                            ## own runtime returns early with `checks == {}`
                            ## and `overflowOn == false`.
    overflowRowKey*: string ## the stdlib row behind `overflowModelled`, "" if
                            ## none (`RoutineChecks.overflowRow.cell.key`)
    inherit*: bool          ## a magic: expanded at the call site, under the
                            ## caller's options

  ArithDecision* = object
    stamp*: ArithStamp
    declineOverflow*: bool  ## the `feOverflowCheckOption` marker
                            ## (`withCheckDeclines`): the routine is pushed
                            ## off in a build that checks, and no row models it

  ArithFrames* = object
    ## The lexical stack of regimes: the top is the routine body now parsed or
    ## walked. The base frame is the build's and is never popped.
    frames: seq[Regime]

const noRowKey* = ""
  ## `RoutineArithFacts.overflowRowKey` of a routine no stdlib row models.

func buildRegime*(b: BuildSemantics = buildSemantics): Regime =
  ## The build's own arithmetic. `coOverflow` off is `buildWraps()`.
  if coOverflow in b.checks: rgChecked else: rgUnchecked

func programMayWrap*(b: BuildSemantics = buildSemantics): bool =
  ## Whether any part of the program may run unchecked signed arithmetic. The
  ## abstraction asks about the whole program (F-5): in D1 it is the build's
  ## own regime, so it equals `buildWraps()`.
  buildRegime(b) == rgUnchecked

func modelled(f: RoutineArithFacts): bool = f.overflowRowKey.len > 0

func parseScope(f: RoutineArithFacts; b: BuildSemantics): ArithScope =
  ## `arithScopeFor` of a non-inherit routine (`dsl_parser.nim:1598`): where
  ## the build is unchecked but the routine's position was read as `push
  ## overflowChecks: on`, `asChecked`; where a stdlib row models its push off in
  ## a build that checks, `asUnchecked`; else `asBuild`, whose meaning is the
  ## build's own.
  let wraps = buildRegime(b) == rgUnchecked
  if wraps and f.overflowOn and f.readable: asChecked
  elif f.modelled and not wraps: asUnchecked
  else: asBuild

func scopeRegime(s: ArithScope; b: BuildSemantics): Regime =
  case s
  of asChecked: rgChecked
  of asUnchecked: rgUnchecked
  of asBuild: buildRegime(b)
  of asInherit: raiseAssert "scopeRegime: asInherit is no regime"

proc decide*(f: RoutineArithFacts;
             b: BuildSemantics = buildSemantics): ArithDecision =
  ## The one decision: the stamp of a routine's body block and whether it
  ## declines. A claim is made only in a build that is unchecked or where a
  ## stdlib row models the routine (`arithStamp`, `dsl_parser.nim:1672`), and
  ## never by an inherit routine. The stamp is a proof of the axis that made
  ## the claim, so the pragma row and the stdlib row are consulted here.
  let wraps = buildRegime(b) == rgUnchecked
  # `withCheckDeclines` (`dsl_parser.nim:1819`).
  result.declineOverflow = f.overflowDeviates and f.readable and not wraps and
                           not f.modelled
  if f.inherit or (not wraps and not f.modelled):
    result.stamp = ArithStamp(scope: asInherit)
    return
  case parseScope(f, b)
  of asChecked:
    let a = admitPragma(ppRoutine, "overflowChecks", psRoutineDecl)
    doAssert a.admitted, "decide: the overflowChecks pragma row is declined"
    result.stamp = ArithStamp(scope: asChecked)
  of asUnchecked:
    let a = admitStdlibBody(f.overflowRowKey, ssBodyWalk)
    doAssert a.admitted, "decide: the stdlib row " & f.overflowRowKey &
      " is declined"
    doAssert coOverflow in a.payload.exercises,
      "decide: the stdlib row " & f.overflowRowKey &
      " does not exercise overflowChecks"
    result.stamp = ArithStamp(scope: asUnchecked)
  of asBuild:
    doAssert wraps, "decide: a build claim in a build that checks"
    result.stamp = ArithStamp(scope: asBuild)
  of asInherit:
    raiseAssert "decide: parseScope never answers asInherit"

proc stampFor*(f: RoutineArithFacts;
               b: BuildSemantics = buildSemantics): ArithStamp =
  decide(f, b).stamp

func provenance*(s: ArithStamp): ArithScope = s.scope

func claims*(s: ArithStamp): bool = s.scope != asInherit

func keyText*(s: ArithStamp): string =
  ## The cache-key bytes of a stamp: the scope's enum name.
  $s.scope

func init*(T: type ArithFrames;
           b: BuildSemantics = buildSemantics): ArithFrames =
  ArithFrames(frames: @[buildRegime(b)])

func regime*(f: ArithFrames): Regime = f.frames[^1]

proc enterBody*(f: var ArithFrames; s: ArithStamp) =
  ## The walk rule (`pushArith`, `runtime.nim:2187`): a stamp that claims
  ## pushes its regime (`asBuild` and `asUnchecked` unchecked, `asChecked`
  ## checked); `asInherit` pushes NOTHING, so the callee runs under the
  ## caller's regime and the caller pairs `leave` with a claiming stamp only.
  ## F-2: in a build that checks, the parse rule (`enterParse`) gives an
  ## unstamped non-magic callee the build's regime where this one gives it the
  ## caller's; harmless while every stdlib row that deviates calls only magics
  ## (the census in `tsymex_0016_d1_regime`), fixed by D1-F2's total stamp.
  case s.scope
  of asInherit: discard
  of asChecked: f.frames.add rgChecked
  of asBuild, asUnchecked: f.frames.add rgUnchecked

proc enterParse*(f: var ArithFrames; facts: RoutineArithFacts;
                 b: BuildSemantics = buildSemantics) =
  ## The parse rule (`pushArithScope`, `dsl_parser.nim:1662`): every routine
  ## opens a frame; an inherit routine repeats its caller's, any other takes
  ## `arithScopeFor`'s answer, claimed or not. `leave` always pairs.
  if facts.inherit: f.frames.add f.frames[^1]
  else: f.frames.add scopeRegime(parseScope(facts, b), b)

proc leave*(f: var ArithFrames) =
  doAssert f.frames.len > 1, "arith frame stack underflow"
  f.frames.setLen(f.frames.len - 1)

func emits*(f: ArithFrames; ac: ArithCheck;
            b: BuildSemantics = buildSemantics): bool =
  ## Whether check `ac` is emitted where the walk now stands (`checked`,
  ## `runtime.nim:9362`): the build's checks, or a routine pushed on in a build
  ## that is off (so the routine is not the build). F-3: in a build that
  ## checks, an `asUnchecked` body still answers true for `acOverflow` while
  ## its regime is unchecked; not observable today, kept.
  let buildChecks =
    (ac in {acOverflow, acDivByZero} and coOverflow in b.checks) or
    (ac == acRange and coRange in b.checks)
  buildChecks or
    (ac in {acOverflow, acDivByZero} and buildRegime(b) == rgUnchecked and
     f.regime == rgChecked)

func profile*(r: Regime; b: BuildSemantics = buildSemantics): DefProfile =
  ## The definedness table's column for a regime (`defProfile`,
  ## `runtime.nim:9372`).
  case r
  of rgChecked: dpChecked
  of rgUnchecked: (if b.fwrapv: dpFwrapv else: dpUnchecked)

func ownerProfile*(f: RoutineArithFacts;
                   b: BuildSemantics = buildSemantics): DefProfile =
  ## The column for the owner of an opaque callee, read from the routine's own
  ## `overflowOn` as returned (F-4: false on every early return, so an unread
  ## owner is over-tainted, never under-). A nil owner is checked:
  ## `RoutineArithFacts(overflowOn: true)`.
  if f.overflowOn: dpChecked else: profile(rgUnchecked, b)

func wrapDefined*(r: Regime; op: ArithOp; width: int;
                  b: BuildSemantics = buildSemantics): bool =
  ## Whether an unchecked signed `+`, `-` or `*` at `width` bits is a DEFINED
  ## wrap (`signedWrapDefined(width) and wraps()`, `runtime.nim:9632`): 8 and
  ## 16 bit always, 32 and 64 bit under `-fwrapv`; never where checked. It
  ## reads the definedness table, whose rows say exactly that.
  doAssert op in {aoAdd, aoSub, aoMul}, "wrapDefined: not a wrapping op"
  doAssert width in {8, 16, 32, 64}, "wrapDefined: not a signed width"
  let c = if width in {32, 64}: ocSignedWide else: ocSignedNarrow
  definedness(op, c, profile(r, b)).kind == dkDefined

func inlinableIterator*(f: RoutineArithFacts; caller: Regime;
                        b: BuildSemantics = buildSemantics): bool =
  ## The overflow half of whether a closure iterator may be inlined
  ## (`dsl_parser.nim:21804-21811`): its position was read, its overflow checks
  ## agree with the build's (no deviation in a build that checks), and where
  ## the build is unchecked the iterator is compiled under the caller's regime
  ## (inlined, it is walked under that one). The other check options stay the
  ## caller's business.
  let wraps = buildRegime(b) == rgUnchecked
  f.readable and (not f.overflowDeviates or wraps) and
    (not wraps or scopeRegime(parseScope(f, b), b) == caller)
