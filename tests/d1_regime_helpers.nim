## RFC-0016 review D1 (slice S1). What the three `tsymex_0016_d1_regime*` suites
## share: the oracles (transcriptions of the CURRENT parser and walker rules,
## each line citing where it lives) and the checks run against `arith_regime`.
##
## An oracle is either a live exported proc (`definedness`, `mkArithBlock`,
## `canonicalize`) or a transcription of a rule, with its file:line. The
## retired build predicates (`buildWraps`, `signedWrapDefined`,
## `arithChecksFor`) survive here as the literal transcriptions `refWraps`,
## `refWrapDefined` and `refChecks`: the property stays pinned against the
## module alone. The three suites differ only in the build
## they are compiled for (their `.nim.cfg`), which fixes `buildSemantics`; the
## synthetic builds below cover every combination in each of them, so the
## default-argument path is checked against the compiled build and the
## argument path against all four.
import std/[unittest, strutils, options, os, compilesettings]
import nelli/smt/buildprofile
import nelli/smt/admission
import nelli/smt/errorkind
import nelli/smt/definedness
import nelli/smt/pragmaaxes
import nelli/smt/stdlib_rows
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/arith_regime

type Cfg* = tuple[name: string, b: BuildSemantics]

func withBuild*(checksOn, fwrapv: bool): BuildSemantics =
  result = buildSemantics
  result.fwrapv = fwrapv
  if checksOn: result.checks.incl coOverflow else: result.checks.excl coOverflow

const rowKey* = "math.floorDiv"  # a stdlib row that exercises overflowChecks

proc builds*(): seq[Cfg] =
  @[("checks-on", withBuild(true, false)),
    ("checks-on+fwrapv", withBuild(true, true)),       # k5b_cfg_fwrapv
    ("checks-off", withBuild(false, false)),
    ("checks-off+fwrapv", withBuild(false, true))]     # w3z_p2_fwrapv

iterator allFacts*(): RoutineArithFacts =
  ## readable x overflowOn x deviates x {"" , a row} x overflowOff x inherit
  for readable in [false, true]:
    for on in [false, true]:
      for dev in [false, true]:
        for key in ["", rowKey]:
          for off in [false, true]:
            for inh in [false, true]:
              yield RoutineArithFacts(readable: readable, overflowOn: on,
                overflowDeviates: dev, overflowRowKey: key, overflowOff: off,
                inherit: inh)

# ---- oracles: the current rules, transcribed -------------------------------

func refWraps(b: BuildSemantics): bool =
  ## The retired `buildWraps`: signed arithmetic is unchecked in this build.
  coOverflow notin b.checks

func refWrapDefined(width: int; b: BuildSemantics): bool =
  ## The retired `signedWrapDefined` (K5a): below `int`'s width always, at 32
  ## and 64 bit only under `-fwrapv`.
  width in {8, 16} or b.fwrapv

func refChecks(b: BuildSemantics): set[ArithCheck] =
  ## The retired `arithChecksFor`: the checks the build compiles in.
  if coOverflow in b.checks: result.incl {acOverflow, acDivByZero}
  if coRange in b.checks: result.incl acRange

func refScope(f: RoutineArithFacts; b: BuildSemantics): ArithScope =
  ## dsl_parser.nim:1598 `arithScopeFor(c, caller, inherit = false)`.
  if refWraps(b) and f.overflowOn and f.readable: asChecked
  elif f.overflowRowKey.len > 0 and not refWraps(b): asUnchecked
  elif f.overflowOff and f.readable and not refWraps(b): asPushedOff  # int6-o
  else: asBuild

func refRegimeOf(sc: ArithScope; b: BuildSemantics): Regime =
  ## The regime a non-inherit scope walks under.
  case sc
  of asChecked: rgChecked
  of asUnchecked, asPushedOff: rgUnchecked
  else: (if refWraps(b): rgUnchecked else: rgChecked)

func refStamp(f: RoutineArithFacts; b: BuildSemantics): ArithScope =
  ## D1-F2: every routine body claims, and none by an inherit routine.
  if f.inherit: asInherit
  else: refScope(f, b)

func refDecline(f: RoutineArithFacts; b: BuildSemantics): bool =
  ## dsl_parser.nim:1819 (`coOverflow in c.checks and c.why.len == 0 and not
  ## buildWraps() and not c.overflowModelled`).
  f.overflowDeviates and f.readable and not refWraps(b) and
    f.overflowRowKey.len == 0

func refParseChecked(f: RoutineArithFacts; b: BuildSemantics): bool =
  ## dsl_parser.nim:1662 `pushArithScope` (non-inherit) then :1614
  ## `overflowChecked`.
  refRegimeOf(refScope(f, b), b) == rgChecked

func refDefProfile(wraps: bool; b: BuildSemantics): DefProfile =
  ## runtime.nim:9372 `defProfile`.
  if not wraps: dpChecked elif b.fwrapv: dpFwrapv else: dpUnchecked

func refChecked(ac: ArithCheck; wraps: bool; b: BuildSemantics): bool =
  ## runtime.nim:9362 `checked`: the overflow and zero-divisor checks follow
  ## the regime where the walk stands (F-3, D1-F2), the range check the build.
  if ac in {acOverflow, acDivByZero}: not wraps
  else: ac in refChecks(b)

# ---- the checks -------------------------------------------------------------

proc checkTruthTable*() =
  for (nm, b) in builds():
    for f in allFacts():
      let d = decide(f, b)
      checkpoint nm & " " & $f
      check d.stamp.provenance == refStamp(f, b)
      check d.stamp.claims == (refStamp(f, b) != asInherit)
      check d.declineOverflow == refDecline(f, b)
      check stampFor(f, b).provenance == d.stamp.provenance
      check d.stamp.keyText == $d.stamp.provenance

proc checkLiterals*() =
  ## The same table as literals, for the rows that matter, with the line each
  ## encodes. `K` models its overflow row, `deviates` is `coOverflow in
  ## c.checks`.
  let off = withBuild(false, false)
  let on = withBuild(true, false)
  func fx(readable, ovfOn, dev: bool; key: string; inh = false):
      RoutineArithFacts =
    RoutineArithFacts(readable: readable, overflowOn: ovfOn,
      overflowDeviates: dev, overflowRowKey: key, inherit: inh)
  # checks-off build: every non-inherit routine claims (dsl_parser.nim:1676
  # `buildWraps()` lets it through), asChecked only for a read `push on`
  # (:1608 is not reached: `not refWraps()` is false; :1605 is).
  check stampFor(fx(true, false, true, ""), off).provenance == asBuild
  check stampFor(fx(true, true, false, ""), off).provenance == asChecked
  check stampFor(fx(false, true, false, ""), off).provenance == asBuild  # :1605 needs why.len == 0
  check stampFor(fx(true, false, true, rowKey), off).provenance == asBuild  # :1608 needs `not refWraps()`
  check stampFor(fx(true, true, true, rowKey), off).provenance == asChecked
  check stampFor(fx(true, true, false, "", true), off).provenance == asInherit  # :1676 `or inherit`
  check not decide(fx(true, false, true, ""), off).declineOverflow  # :1820 `not refWraps()`
  # checks-on build (D1-F2): every body claims; a modelled routine as
  # asUnchecked (:1608), any other as asBuild (checked); a deviating
  # unmodelled routine declines (:1819-1821).
  check stampFor(fx(true, false, true, ""), on).provenance == asBuild
  check stampFor(fx(true, true, false, ""), on).provenance == asBuild
  check stampFor(fx(true, false, true, rowKey), on).provenance == asUnchecked
  check stampFor(fx(true, false, true, rowKey, true), on).provenance == asInherit
  check decide(fx(true, false, true, ""), on).declineOverflow
  # int6-o: a user routine read pushed off on every reading is no deviation
  # (`overflowDeviates` false) and walks unchecked; unread, it is the build's
  let po = RoutineArithFacts(readable: true, overflowOff: true)
  check stampFor(po, on).provenance == asPushedOff
  check not decide(po, on).declineOverflow
  check stampFor(po, off).provenance == asBuild
  check stampFor(RoutineArithFacts(overflowOff: true), on).provenance == asBuild
  check not decide(fx(true, false, true, rowKey), on).declineOverflow  # :1821 `not c.overflowModelled`
  check not decide(fx(false, false, true, ""), on).declineOverflow     # :1820 `c.why.len == 0`
  check not decide(fx(true, false, false, ""), on).declineOverflow     # an own-runtime routine: checks == {} (check_options.nim:955)
  # the key bytes are the enum names (canonicalize.nim:6772) and asInherit is 0
  check ord(asInherit) == 0
  check $asBuild == "asBuild" and $asChecked == "asChecked" and
        $asUnchecked == "asUnchecked" and $asInherit == "asInherit"
  check $asPushedOff == "asPushedOff" and ord(asPushedOff) == ord(asUnchecked) + 1

proc checkProfiles*() =
  for (nm, b) in builds():
    checkpoint nm
    check buildRegime(b) == (if refWraps(b): rgUnchecked else: rgChecked)
    check programMayWrap(b) == refWraps(b)           # F-5, D1
    for r in [rgChecked, rgUnchecked]:
      check profile(r, b) == refDefProfile(r == rgUnchecked, b)
      for op in [aoAdd, aoSub, aoMul]:
        for w in [8, 16, 32, 64]:
          # runtime.nim:9632: `refWrapDefined(width) and wraps()`
          check wrapDefined(r, op, w, b) ==
                (r == rgUnchecked and refWrapDefined(w, b))
          # and the table agrees (runtime.nim:9402)
          let ans = definedness(op, (if w in {32, 64}: ocSignedWide
                                     else: ocSignedNarrow), profile(r, b))
          check wrapDefined(r, op, w, b) == (ans.kind == dkDefined)
    # an owner that is checked reads the checked column; one that is not reads
    # the unchecked one, or `-fwrapv`'s (dsl_parser.nim:4807, plus F-1: the
    # divide row follows the table under `-fwrapv`)
    check ownerProfile(RoutineArithFacts(overflowOn: true), b) == dpChecked
    check ownerProfile(RoutineArithFacts(overflowOn: false), b) ==
          (if b.fwrapv: dpFwrapv else: dpUnchecked)

proc checkFrames*() =
  for (nm, b) in builds():
    checkpoint nm
    var w = ArithFrames.init(b)
    check w.regime == buildRegime(b)                    # runtime.nim:2178
    for ac in ArithCheck:
      check w.emits(ac, b) == refChecked(ac, refWraps(b), b)
    # the walk: every stamp a routine can carry, entered and left
    for f in allFacts():
      let s = stampFor(f, b)
      if not s.claims: continue                         # runtime.nim:25498
      check enterBody(w, s, b)
      let wraps = (case s.provenance
                   of asChecked: false
                   of asUnchecked, asPushedOff: true
                   else: refWraps(b))                    # runtime.nim:2189
      check (w.regime == rgUnchecked) == wraps
      for ac in ArithCheck:
        check w.emits(ac, b) == refChecked(ac, wraps, b)
      check profile(w.regime, b) == refDefProfile(wraps, b)
      w.leave
      check w.regime == buildRegime(b)
    # the parse: from a checked and from an unchecked caller frame
    for f in allFacts():
      for base in [asChecked, asUnchecked]:
        var p = ArithFrames.init(b)
        # seed the caller's frame with a real routine's
        let seed = RoutineArithFacts(readable: true, overflowOn: base == asChecked,
          overflowDeviates: true,
          overflowRowKey: (if base == asUnchecked: rowKey else: ""))
        p.enterParse(seed, b)
        let callerChecked = p.regime == rgChecked
        p.enterParse(f, b)
        if f.inherit:
          check (p.regime == rgChecked) == callerChecked
        else:
          check (p.regime == rgChecked) == refParseChecked(f, b)
        p.leave
        check (p.regime == rgChecked) == callerChecked
        p.leave
        check p.regime == buildRegime(b)
    # P2 (dsl_parser.nim:21807): the iterator is compiled under the caller's
    # scope or declines, in either build (int6-o: a build that checks holds
    # unchecked regions too); agrees (:21801) needs the overflow checks to be
    # the build's
    for f in allFacts():
      for caller in [rgChecked, rgUnchecked]:
        let sameScope = refRegimeOf(refScope(f, b), b) == caller
        let agrees = f.readable and (not f.overflowDeviates or refWraps(b))
        check inlinableIterator(f, caller, b) == (agrees and sameScope)

proc checkConstPure*() =
  ## `stampFor` is const-pure: the emit (S5) evaluates it at compile time.
  const rows = [
    (RoutineArithFacts(readable: true, overflowOn: true), "checked"),
    (RoutineArithFacts(readable: true, overflowDeviates: true), "unmod"),
    (RoutineArithFacts(readable: true, overflowDeviates: true,
                       overflowRowKey: rowKey), "row"),
    (RoutineArithFacts(inherit: true), "inherit")]
  const ctProv = [stampFor(rows[0][0]).provenance, stampFor(rows[1][0]).provenance,
                  stampFor(rows[2][0]).provenance, stampFor(rows[3][0]).provenance]
  const ctDecl = [decide(rows[0][0]).declineOverflow,
                  decide(rows[1][0]).declineOverflow,
                  decide(rows[2][0]).declineOverflow,
                  decide(rows[3][0]).declineOverflow]
  for i in 0 ..< rows.len:
    check ctProv[i] == stampFor(rows[i][0]).provenance
    check ctDecl[i] == decide(rows[i][0]).declineOverflow
    check ctProv[i] == refStamp(rows[i][0], buildSemantics)

proc checkKeyBytes*() =
  ## The cache key of a stamped block: `canonicalize.nim:6772` renders
  ## `"@" & $blkArith & ":"` for a claim and nothing for `asInherit`. D1-F2: a
  ## body claims in every build.
  let body = @[mkBreak()]
  let plain = canonicalize(mkBlock(body))
  check "@as" notin plain
  let b = buildSemantics
  let cases = [RoutineArithFacts(readable: true, overflowOn: false,
                                 overflowDeviates: true),
               RoutineArithFacts(readable: true, overflowOn: true),
               RoutineArithFacts(readable: true, overflowDeviates: true,
                                 overflowRowKey: rowKey)]
  var seen: seq[string]
  for f in cases:
    let s = stampFor(f, b)
    if not s.claims:
      check "@as" notin canonicalize(mkBlock(body))
      continue
    let blk = mkArithBlock(s, body)
    let key = canonicalize(blk)
    check "@" & s.keyText & ":" in key
    check blk.blkArith.provenance == s.provenance
    check key.startsWith("St<Bk:@" & s.keyText & ":[")
    seen.add s.keyText
  if coOverflow notin buildSemantics.checks:
    check seen.len >= 2 and "asBuild" in seen and "asChecked" in seen
  else:
    check seen == @["asBuild", "asBuild", "asUnchecked"]

proc checkTotalStamp*() =
  ## D1-F2 (F-2): no body's regime comes from inheritance. Every non-magic
  ## routine body claims, in every build, so a callee entered from an
  ## `asUnchecked` body is walked under its own regime (the parse rule's), as
  ## natively; only a magic stays `asInherit`. The cache key then carries the
  ## claim (`@asBuild:` for a body that used to render nothing).
  ## F-3: the overflow check and the defined wrap read one regime, so they are
  ## never both on, in any build, in any stamped body.
  for (nm, b) in builds():
    checkpoint nm
    for f in allFacts():
      let s = stampFor(f, b)
      check s.claims == (not f.inherit)
    # a caller under `asUnchecked` (a modelled stdlib body, checks-on build),
    # then an ordinary non-magic callee: the callee's own claim, not the caller's
    let caller = stampFor(RoutineArithFacts(readable: true,
      overflowDeviates: true, overflowRowKey: rowKey), b)
    let callee = stampFor(RoutineArithFacts(readable: true), b)
    check callee.claims
    var w = ArithFrames.init(b)
    check enterBody(w, caller, b)
    check enterBody(w, callee, b)
    check w.regime == buildRegime(b)       # the callee is the build's, natively
    w.leave
    check w.regime == (if caller.provenance == asUnchecked: rgUnchecked
                       else: buildRegime(b))
    w.leave
    # F-3
    for s in [caller, callee]:
      var v = ArithFrames.init(b)
      check enterBody(v, s, b)
      for op in [aoAdd, aoSub, aoMul]:
        for width in [8, 16, 32, 64]:
          check not (v.emits(acOverflow, b) and wrapDefined(v.regime, op, width, b))
      check v.emits(acOverflow, b) == (v.regime == rgChecked)
      check v.emits(acDivByZero, b) == (v.regime == rgChecked)
      v.leave
  # the key bytes: the claim of a body that used to be unstamped
  let key = canonicalize(mkArithBlock(
    stampFor(RoutineArithFacts(readable: true), withBuild(true, false)),
    @[mkBreak()]))
  check key.startsWith("St<Bk:@asBuild:[")
