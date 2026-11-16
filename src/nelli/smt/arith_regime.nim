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
## S2: the vocabulary (`ArithScope`, `ArithCheck`, `ArithScopeProof` and its
## constructors, `buildWraps`, `arithChecksFor`, `signedWrapDefined`) is defined
## here, and `types` imports and re-exports it under the same names; this
## module imports no `types`. Nothing here is read by a parser or walker site
## through the `Regime` surface yet.
import ./buildprofile
import ./admission
import ./definedness
import ./pragmaaxes
import ./stdlib_rows

type
  ArithScope* = enum
    ## RFC-0016 W1-d2c. Which arithmetic a routine body is walked under, in a
    ## build whose own overflow checks are off (`buildWraps()`). Checked-ness is
    ## per routine: the build's setting unless an enclosing `push overflowChecks:
    ## on` says otherwise. The parser stamps the routine's body block; the
    ## walker pushes it for the block and pops it after, so a
    ## caller's scope never leaks into a callee and back.
    asInherit   ## no claim (every block but a routine body; any body in a checks-on build)
    asBuild     ## unchecked signed arithmetic: the build's (`ubSignedOverflow`)
    asChecked   ## `push overflowChecks: on` in a checks-off build: `OverflowDefect`
    asUnchecked ## RFC-0016 K4c. A stdlib body under a push that turns its
                ## overflow checks off (`math.nim`'s `checks: off`) in a build
                ## that checks: unchecked signed arithmetic, as `asBuild` is
                ## in a checks-off build. Only a `stdlibAxis` row stamps it.

  ArithCheck* = enum
    ## R16-1 (Phase 16 ADR-0011 F2). Which arithmetic defect forks the walker
    ## EMITS. RFC-0016 K10d: the build alone decides (`arithChecksFor`); the
    ## `SymexSettings.arithChecks` setting that used to override it is gone.
    ## An unchecked kind is never forked so it never pays path-multiplicative
    ## cost. `defectExclusions` is the orthogonal "surfacing" axis: the fork is
    ## emitted but the finding is suppressed when the kind is excluded.
    ##
    ## ORDINAL-STABILITY RULE: ALWAYS APPEND new members at the END of this
    ## enum; the ordinals are the order the build profile reads.
    acOverflow   ## fork +/-/* overflow → OverflowDefect raise
    acDivByZero  ## fork div/mod-by-zero → DivByZeroDefect raise. Only with
                 ## `acOverflow` also on (RFC-0005 S8aa): Nim emits its zero
                 ## check under `overflowChecks` alone, so with that off a
                 ## zero divisor reaches the C division, which traps (SIGFPE);
                 ## it is then a survivor-only trap, never a raise.
    acRange      ## fork float→int out-of-range → RangeDefect raise (R16-2);
                 ## also int-width narrowing (R16-5, deferred). Scope in R16-1:
                 ## float→int domain checks only (RD2) — no fork emitted yet.

  ArithScopeProof* = object
    ## RFC-0016 ADM-IR (section 8.1). The proof that a block's arithmetic
    ## claim was stamped by the axis that owns it: the pragma axis (a `push
    ## overflowChecks: on` row), the stdlib-body axis (a routine whose
    ## check-option delta is modelled) or the build (its own arithmetic is
    ## unchecked). The scope is private, so `mkArithBlock` cannot be handed a
    ## bare `ArithScope` and the three constructors below are the only way in.
    scope: ArithScope

func arithScope*(p: ArithScopeProof): ArithScope = p.scope

func arithFromPragma*(a: Admit[PragmaModel]): ArithScopeProof =
  ## `asChecked`: the admitted `routine/overflowChecks` pragma row (a `push
  ## overflowChecks: on` in a build whose own checks are off).
  doAssert a.admitted, "arithFromPragma: " & a.decline[1]
  doAssert a.cell.scope == axPragma and a.cell.key == "routine/overflowChecks",
    "arithFromPragma: " & render(a.cell) & " is not the overflowChecks row"
  ArithScopeProof(scope: asChecked)

func arithFromStdlib*(a: Admit[StdlibBody]): ArithScopeProof =
  ## `asUnchecked`: an admitted stdlib-body row whose body trips
  ## `overflowChecks` (`exercises`), which `math.nim`'s push turns off.
  doAssert a.admitted, "arithFromStdlib: " & a.decline[1]
  doAssert coOverflow in a.payload.exercises,
    "arithFromStdlib: " & render(a.cell) & " does not exercise overflowChecks"
  ArithScopeProof(scope: asUnchecked)

func replayArith*(s: ArithScope): ArithScopeProof =
  ## The IR emit's rebuild of a stamp it already read. The parser's emit is
  ## the only caller; `tests/tsymex_0016_admir.nim` counts the uses.
  doAssert s != asInherit, "replayArith: asInherit is no claim"
  ArithScopeProof(scope: s)

func arithChecksFor*(b: BuildSemantics = buildSemantics): set[ArithCheck] =
  ## RFC-0016 W1-d2. The arithmetic checks a build `b` implies: the checks its
  ## compiled code performs. The one source the walker's check gates read
  ## (K10d removed the `SymexSettings.arithChecks` override).
  if coOverflow in b.checks: result.incl {acOverflow, acDivByZero}
  if coRange in b.checks: result.incl acRange

func buildWraps*(b: BuildSemantics = buildSemantics): bool =
  ## RFC-0016 W1-d2 (W-07). Whether signed `+`, `-`, `*` (and `div`) in this
  ## build are UNCHECKED: with `overflowChecks` off the C operation is
  ## undefined on overflow (not a wrap, unless the build is `-d:nelliFwrapv`,
  ## which `signedWrapDefined` reports), so the walker does not model a wrap
  ## and a trusted answer for 32 and 64 bit. The ONE predicate
  ## `wraps()`, the wrap scan and the exact-offset promotion read;
  ## settings never feed it (the build is what the native program does). A routine under
  ## `{.push overflowChecks: off.}` is a separate route: its marker declines.
  coOverflow notin b.checks

func arithFromBuild*(b: BuildSemantics = buildSemantics): ArithScopeProof =
  ## `asBuild`: the build's own signed arithmetic is unchecked. Not a table
  ## row: the build axis's claim is the build itself.
  doAssert buildWraps(b), "arithFromBuild: the build checks its arithmetic"
  ArithScopeProof(scope: asBuild)

func signedWrapDefined*(width: int; b: BuildSemantics = buildSemantics): bool =
  ## RFC-0016 K5a. Whether an unchecked signed `+`, `-`, `*` or negation at
  ## `width` bits is a DEFINED wrap in build `b`: always below `int`'s width
  ## (8 and 16 bit: C computes in the promoted `int` and the narrowing wraps),
  ## and at 32 and 64 bit only when the build compiles with `-fwrapv`
  ## (`-d:nelliFwrapv`). `low(T) div -1` and `mod -1` are not covered by it.
  width in {8, 16} or b.fwrapv

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

func regime*(f: ArithFrames; b: BuildSemantics = buildSemantics): Regime =
  ## The regime now; a stack nobody has entered is the build's own (a
  ## zero-initialised `ArithFrames`, as `ParseCtx` holds, has no base frame).
  if f.frames.len > 0: f.frames[^1] else: buildRegime(b)

proc ensureBase(f: var ArithFrames; b: BuildSemantics) =
  if f.frames.len == 0: f.frames.add buildRegime(b)

proc enterBody*(f: var ArithFrames; s: ArithScope): bool =
  ## The walk rule (`pushArith`, `runtime.nim:2187`): a stamp that claims
  ## pushes its regime (`asBuild` and `asUnchecked` unchecked, `asChecked`
  ## checked); `asInherit` pushes NOTHING, so the callee runs under the
  ## caller's regime. Answers whether it pushed: the walker calls `leave` only
  ## then (the parser's `enterParse` always pushes and always leaves).
  ## F-2: in a build that checks, the parse rule (`enterParse`) gives an
  ## unstamped non-magic callee the build's regime where this one gives it the
  ## caller's; harmless while every stdlib row that deviates calls only magics
  ## (the census in `tsymex_0016_d1_regime`), fixed by D1-F2's total stamp.
  ## Takes the scope until S5 seals the IR stamp as an `ArithStamp`; this
  ## overload only reads it, so it mints nothing.
  f.ensureBase buildSemantics
  case s
  of asInherit: return false
  of asChecked: f.frames.add rgChecked
  of asBuild, asUnchecked: f.frames.add rgUnchecked
  true

proc enterBody*(f: var ArithFrames; s: ArithStamp): bool =
  f.enterBody s.scope

proc enterParse*(f: var ArithFrames; facts: RoutineArithFacts;
                 b: BuildSemantics = buildSemantics) =
  ## The parse rule (`pushArithScope`, `dsl_parser.nim:1662`): every routine
  ## opens a frame; an inherit routine repeats its caller's, any other takes
  ## `arithScopeFor`'s answer, claimed or not. `leave` always pairs.
  f.ensureBase b
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

const anyProfile* = dpChecked
  ## The column of a definedness row whose answer does not depend on the
  ## profile (the same under all three), where a caller needs to name one.

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
