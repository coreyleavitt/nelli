## RFC-0016 review D1 (slice S1): the one owner of the arithmetic regime.
##
## Which signed arithmetic a routine body is parsed and walked under used to be
## decided at a dozen sites in `dsl_parser.nim` and `runtime.nim`, each reading
## the build's overflow checks, `RoutineChecks.overflowOn`, the inherit flag and the IR stamp
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
## S6: this module is the only owner. `ArithScope` and `ArithCheck` are
## defined here and `types` re-exports them (the parser, walker and cache key
## name them); the old build predicates (`buildWraps`, `arithChecksFor`,
## `signedWrapDefined`) and the walker's own scope stack are gone, and every
## site asks `buildRegime`, `programMayWrap`, `wrapDefined`, `emits`, `profile`.
import ./buildprofile
import ./admission
import ./definedness
import ./pragmaaxes
import ./stdlib_rows

type
  ArithScope* = enum
    ## RFC-0016 W1-d2c. Which arithmetic a routine body is walked under, in a
    ## build whose own overflow checks are off (`buildRegime() == rgUnchecked`). Checked-ness is
    ## per routine: the build's setting unless an enclosing `push overflowChecks:
    ## on` says otherwise. The parser stamps the routine's body block; the
    ## walker pushes it for the block and pops it after, so a
    ## caller's scope never leaks into a callee and back.
    asInherit   ## no claim: every block that is not a routine body, and the
                ## body of a magic (expanded at its call site, under the
                ## caller's options). D1-F2: NO other routine body is
                ## unclaimed; each states its own regime.
    asBuild     ## the build's own arithmetic: unchecked (`ubSignedOverflow`)
                ## in a build whose overflow checks are off, checked in one
                ## that checks (D1-F2: a routine body in a checks-on build
                ## carries this claim, so a caller pushed off does not leak)
    asChecked   ## `push overflowChecks: on` in a checks-off build: `OverflowDefect`
    asUnchecked ## RFC-0016 K4c. A stdlib body under a push that turns its
                ## overflow checks off (`math.nim`'s `checks: off`) in a build
                ## that checks: unchecked signed arithmetic, as `asBuild` is
                ## in a checks-off build. Only a `stdlibAxis` row stamps it.
    asPushedOff ## RFC-0016 int6-o. A user routine under `push overflowChecks:
                ## off` (or `checks: off`) in a build that checks, read off at
                ## its position on every reading: unchecked signed arithmetic,
                ## as in a `--overflowChecks:off` build (undefined on overflow,
                ## a defined wrap at 8 and 16 bits or under `-fwrapv`). The
                ## pragma row stamps it, as `asChecked` for the opposite push.

  ArithCheck* = enum
    ## R16-1 (Phase 16 ADR-0011 F2). Which arithmetic defect forks the walker
    ## EMITS. RFC-0016 K10d: the build alone decides (`emits`); the
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
    overflowOff*: bool      ## RFC-0016 int6-o. `coOverflow in
                            ## RoutineChecks.offModelled`: a user routine's
                            ## (int6-a: or a stdlib routine's no row models)
                            ## position turns the build's overflow checks off
                            ## on every reading, with no importer's push
                            ## reaching it. Not a deviation (`overflowDeviates`
                            ## is false): the routine is walked `asPushedOff`.
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
  ## The build's own arithmetic. `coOverflow` off is `rgUnchecked`.
  if coOverflow in b.checks: rgChecked else: rgUnchecked

func programMayWrap*(b: BuildSemantics = buildSemantics): bool =
  ## Whether the build's own signed arithmetic is unchecked: the abstraction's
  ## whole-program question (F-5), which picks how a parameter is ENCODED
  ## before the walk (`runtime.nim`'s wrap scan and `offsetExact`).
  ##
  ## RFC-0016 int6-o: a program in a build that checks may still hold
  ## unchecked regions (`asPushedOff`, K4c's `asUnchecked`), and this stays
  ## the build's answer on purpose. It is an encoding choice, not the wrap
  ## model: every parameter it lets promote to an Int is width-stamped
  ## (`promoteSound`, `offsetStamp`), and the arithmetic on a stamped Int
  ## reads the regime where the walk stands (`regime`, `wrapDefined`,
  ## `emits`), so in an unchecked region it halts on undefined overflow or
  ## wraps exactly as the bit-vector does (RFC-0005 S8w), and a value it
  ## leaves behind is inside its type's window for the checked code after
  ## the call. Each consumer is annotated where it reads this.
  buildRegime(b) == rgUnchecked

func modelled(f: RoutineArithFacts): bool = f.overflowRowKey.len > 0

func parseScope(f: RoutineArithFacts; b: BuildSemantics): ArithScope =
  ## `arithScopeFor` of a non-inherit routine (`dsl_parser.nim`'s `pushArithScope`): where
  ## the build is unchecked but the routine's position was read as `push
  ## overflowChecks: on`, `asChecked`; where a stdlib row models its push off in
  ## a build that checks, `asUnchecked`; else `asBuild`, whose meaning is the
  ## build's own.
  let wraps = buildRegime(b) == rgUnchecked
  if wraps and f.overflowOn and f.readable: asChecked
  elif f.modelled and not wraps: asUnchecked
  elif f.overflowOff and f.readable and not wraps: asPushedOff
  else: asBuild

func scopeRegime(s: ArithScope; b: BuildSemantics): Regime =
  case s
  of asChecked: rgChecked
  of asUnchecked, asPushedOff: rgUnchecked
  of asBuild: buildRegime(b)
  of asInherit: raiseAssert "scopeRegime: asInherit is no regime"

proc decide*(f: RoutineArithFacts;
             b: BuildSemantics = buildSemantics): ArithDecision =
  ## The one decision: the stamp of a routine's body block and whether it
  ## declines. D1-F2: every routine body claims its regime, in every build
  ## (an unstamped body once ran under its caller's regime in the walk but
  ## under the build's in the parse); only a magic (inherit) does not claim. The stamp is a proof of the axis that made
  ## the claim, so the pragma row and the stdlib row are consulted here.
  let wraps = buildRegime(b) == rgUnchecked
  # `withCheckDeclines` (`dsl_parser.nim`).
  result.declineOverflow = f.overflowDeviates and f.readable and not wraps and
                           not f.modelled
  if f.inherit:
    result.stamp = ArithStamp(scope: asInherit)
    return
  case parseScope(f, b)
  of asChecked, asPushedOff:
    let a = admitPragma(ppRoutine, "overflowChecks", psRoutineDecl)
    doAssert a.admitted, "decide: the overflowChecks pragma row is declined"
    result.stamp = ArithStamp(scope: parseScope(f, b))
  of asUnchecked:
    let a = admitStdlibBody(f.overflowRowKey, ssBodyWalk)
    doAssert a.admitted, "decide: the stdlib row " & f.overflowRowKey &
      " is declined"
    doAssert coOverflow in a.payload.exercises,
      "decide: the stdlib row " & f.overflowRowKey &
      " does not exercise overflowChecks"
    result.stamp = ArithStamp(scope: asUnchecked)
  of asBuild:
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

proc enterBody*(f: var ArithFrames; st: ArithStamp;
                b: BuildSemantics = buildSemantics): bool =
  ## The walk rule (the `enterBody` call in `runtime.nim`'s block arm): a stamp that claims
  ## pushes its regime (`asBuild` the build's, `asUnchecked` and
  ## `asPushedOff` unchecked, `asChecked` checked). `asInherit` pushes NOTHING: it is a block that is
  ## not a routine body, or a magic's, which runs under the enclosing
  ## regime. F-2 (D1-F2): every other routine body claims, so no callee takes
  ## its caller's regime by inheritance, as natively. Answers whether it
  ## pushed: the walker calls `leave` only then.
  f.ensureBase b
  case st.scope
  of asInherit: return false
  of asChecked: f.frames.add rgChecked
  of asBuild: f.frames.add buildRegime(b)
  of asUnchecked, asPushedOff: f.frames.add rgUnchecked
  true

proc enterParse*(f: var ArithFrames; facts: RoutineArithFacts;
                 b: BuildSemantics = buildSemantics) =
  ## The parse rule (`dsl_parser.nim`'s `pushArithScope`): every routine
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
  ## the walker's `checked(ac: ArithCheck)` in `runtime.nim`). F-3 (D1-F2): the overflow and zero-divisor checks
  ## follow the REGIME alone (`f.regime == rgChecked`), the one value
  ## `wrapDefined` and `profile` also read, so an `asUnchecked` body in a
  ## build that checks neither emits the check nor ever has it and a defined
  ## wrap together. The range check is the build's.
  case ac
  of acOverflow, acDivByZero: f.regime(b) == rgChecked
  of acRange: coRange in b.checks

func profile*(r: Regime; b: BuildSemantics = buildSemantics): DefProfile =
  ## The definedness table's column for a regime (`defProfile`,
  ## in `runtime.nim`).
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
  ## wrap (the walker's wrap decision, the `wrapDefined` call in the
  ## unchecked arm of `runtime.nim`'s signed `+`/`-`/`*` lowering): 8 and
  ## 16 bit always, 32 and 64 bit under `-fwrapv`; never where checked. It
  ## reads the definedness table, whose rows say exactly that.
  doAssert op in {aoAdd, aoSub, aoMul}, "wrapDefined: not a wrapping op"
  doAssert width in {8, 16, 32, 64}, "wrapDefined: not a signed width"
  let c = if width in {32, 64}: ocSignedWide else: ocSignedNarrow
  definedness(op, c, profile(r, b)).kind == dkDefined

func inlinableIterator*(f: RoutineArithFacts; caller: Regime;
                        b: BuildSemantics = buildSemantics): bool =
  ## The overflow half of whether a closure iterator may be inlined
  ## (`dsl_parser.nim`'s closure-iterator inlining test, the
  ## `inlinableIterator` call sites): its position was read, its overflow checks
  ## agree with the build's (no deviation in a build that checks), and the
  ## iterator is compiled under the caller's regime (inlined, it is walked
  ## under that one). RFC-0016 int6-o: in either build, since a build that
  ## checks now holds unchecked regions (`asPushedOff`) too. The other check
  ## options stay the caller's business.
  let wraps = buildRegime(b) == rgUnchecked
  f.readable and (not f.overflowDeviates or wraps) and
    scopeRegime(parseScope(f, b), b) == caller
