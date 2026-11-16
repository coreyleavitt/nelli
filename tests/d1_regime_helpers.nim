## RFC-0016 review D1 (slice S1). What the three `tsymex_0016_d1_regime*` suites
## share: the oracles (transcriptions of the CURRENT parser and walker rules,
## each line citing where it lives) and the checks run against `arith_regime`.
##
## An oracle is either a live exported proc (`buildWraps`, `signedWrapDefined`,
## `definedness`, `mkArithBlock`, `canonicalize`) or a transcription of a
## private rule, with its file:line. The three suites differ only in the build
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
  ## readable x overflowOn x deviates x {"" , a row} x inherit
  for readable in [false, true]:
    for on in [false, true]:
      for dev in [false, true]:
        for key in ["", rowKey]:
          for inh in [false, true]:
            yield RoutineArithFacts(readable: readable, overflowOn: on,
              overflowDeviates: dev, overflowRowKey: key, inherit: inh)

# ---- oracles: the current rules, transcribed -------------------------------

func refScope(f: RoutineArithFacts; b: BuildSemantics): ArithScope =
  ## dsl_parser.nim:1598 `arithScopeFor(c, caller, inherit = false)`.
  if buildWraps(b) and f.overflowOn and f.readable: asChecked
  elif f.overflowRowKey.len > 0 and not buildWraps(b): asUnchecked
  else: asBuild

func refStamp(f: RoutineArithFacts; b: BuildSemantics): ArithScope =
  ## dsl_parser.nim:1672 `arithStamp`: no claim in a build that checks unless
  ## a row models the routine, and none by an inherit routine.
  if (not buildWraps(b) and f.overflowRowKey.len == 0) or f.inherit: asInherit
  else: refScope(f, b)

func refDecline(f: RoutineArithFacts; b: BuildSemantics): bool =
  ## dsl_parser.nim:1819 (`coOverflow in c.checks and c.why.len == 0 and not
  ## buildWraps() and not c.overflowModelled`).
  f.overflowDeviates and f.readable and not buildWraps(b) and
    f.overflowRowKey.len == 0

func refParseChecked(f: RoutineArithFacts; b: BuildSemantics): bool =
  ## dsl_parser.nim:1662 `pushArithScope` (non-inherit) then :1614
  ## `overflowChecked`.
  let sc = refScope(f, b)
  (not buildWraps(b) and sc != asUnchecked) or sc == asChecked

func refDefProfile(wraps: bool; b: BuildSemantics): DefProfile =
  ## runtime.nim:9372 `defProfile`.
  if not wraps: dpChecked elif b.fwrapv: dpFwrapv else: dpUnchecked

func refChecked(ac: ArithCheck; wraps: bool; b: BuildSemantics): bool =
  ## runtime.nim:9362 `checked`, over `arithChecksFor` (types.nim:5248).
  ac in arithChecksFor(b) or
    (ac in {acOverflow, acDivByZero} and buildWraps(b) and not wraps)

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
  # (:1608 is not reached: `not buildWraps()` is false; :1605 is).
  check stampFor(fx(true, false, true, ""), off).provenance == asBuild
  check stampFor(fx(true, true, false, ""), off).provenance == asChecked
  check stampFor(fx(false, true, false, ""), off).provenance == asBuild  # :1605 needs why.len == 0
  check stampFor(fx(true, false, true, rowKey), off).provenance == asBuild  # :1608 needs `not buildWraps()`
  check stampFor(fx(true, true, true, rowKey), off).provenance == asChecked
  check stampFor(fx(true, true, false, "", true), off).provenance == asInherit  # :1676 `or inherit`
  check not decide(fx(true, false, true, ""), off).declineOverflow  # :1820 `not buildWraps()`
  # checks-on build: a claim only for a modelled routine (:1676), as
  # asUnchecked (:1608); a deviating unmodelled routine declines (:1819-1821).
  check stampFor(fx(true, false, true, ""), on).provenance == asInherit
  check stampFor(fx(true, true, false, ""), on).provenance == asInherit
  check stampFor(fx(true, false, true, rowKey), on).provenance == asUnchecked
  check stampFor(fx(true, false, true, rowKey, true), on).provenance == asInherit
  check decide(fx(true, false, true, ""), on).declineOverflow
  check not decide(fx(true, false, true, rowKey), on).declineOverflow  # :1821 `not c.overflowModelled`
  check not decide(fx(false, false, true, ""), on).declineOverflow     # :1820 `c.why.len == 0`
  check not decide(fx(true, false, false, ""), on).declineOverflow     # an own-runtime routine: checks == {} (check_options.nim:955)
  # the key bytes are the enum names (canonicalize.nim:6772) and asInherit is 0
  check ord(asInherit) == 0
  check $asBuild == "asBuild" and $asChecked == "asChecked" and
        $asUnchecked == "asUnchecked" and $asInherit == "asInherit"

proc checkProfiles*() =
  for (nm, b) in builds():
    checkpoint nm
    check buildRegime(b) == (if buildWraps(b): rgUnchecked else: rgChecked)
    check programMayWrap(b) == buildWraps(b)           # F-5, D1
    for r in [rgChecked, rgUnchecked]:
      check profile(r, b) == refDefProfile(r == rgUnchecked, b)
      for op in [aoAdd, aoSub, aoMul]:
        for w in [8, 16, 32, 64]:
          # runtime.nim:9632: `signedWrapDefined(width) and wraps()`
          check wrapDefined(r, op, w, b) ==
                (r == rgUnchecked and signedWrapDefined(w, b))
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
      check w.emits(ac, b) == refChecked(ac, buildWraps(b), b)
    # the walk: every stamp a routine can carry, entered and left
    for f in allFacts():
      let s = stampFor(f, b)
      if not s.claims: continue                         # runtime.nim:25498
      check enterBody(w, s)
      let wraps = s.provenance != asChecked              # runtime.nim:2189
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
    # scope or declines, in a build that wraps; agrees (:21801) needs the
    # overflow checks to be the build's
    for f in allFacts():
      for caller in [rgChecked, rgUnchecked]:
        let sameScope = (not buildWraps(b)) or
          ((if refScope(f, b) == asChecked: rgChecked else: rgUnchecked) == caller)
        let agrees = f.readable and (not f.overflowDeviates or buildWraps(b))
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
  ## `"@" & $blkArith & ":"` for a claim and nothing for `asInherit`.
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
  if buildWraps():
    check seen.len >= 2 and "asBuild" in seen and "asChecked" in seen
  else:
    check seen == @["asUnchecked"]

const overflowRowBodyIdents = [
  # the vocabulary of the six bodies, all operators and compiler magics
  "func", "result", "x", "y", "r", "T", "abs", "ord", "dec", "inc", "div",
  "mod", "shr", "or", "and", "not", "if", "elif", "else", "when", "defined",
  "sizeof", "cpu64", "int", "return", "let", "SomeInteger", "SomeNumber",
  "since", "true", "false", "isPowerOfTwo", "nextPowerOfTwo", "floorDiv",
  "floorMod", "euclDiv", "euclMod", "bool"]

proc bodyOf(src, name: string): string =
  ## The text of `func <name>*` up to the next top-level line, with its doc
  ## comments and `runnableExamples` block removed.
  let lines = src.splitLines
  var i = 0
  while i < lines.len and not (lines[i].startsWith("func " & name & "*") or
                               lines[i].startsWith("proc " & name & "*")): inc i
  doAssert i < lines.len, "no routine " & name
  let sig = lines[i]
  inc i
  var skipping = false
  result = sig.substr(sig.find("=") + 1) & "\n"   # past the signature
  while i < lines.len and (lines[i].len == 0 or lines[i][0] in {' ', '\t'}):
    let l = lines[i]
    inc i
    let t = l.strip
    if t.startsWith("##"): continue
    if t.startsWith("runnableExamples:"):
      skipping = true
      continue
    if skipping:
      if l.len > 0 and not l.startsWith("    ") and t.len > 0: skipping = false
      else: continue
    result.add l & "\n"

proc identsOf(s: string): seq[string] =
  var cur = ""
  for c in s & " ":
    if c in IdentChars + {'_'}:
      cur.add c
    else:
      if cur.len > 0 and cur[0] notin Digits: result.add cur
      cur = ""

proc checkOverflowRowCensus*() =
  ## F-2's guard until D1-F2 stamps every body. A deviating routine walked
  ## under `asUnchecked` in a build that checks calls only magics, so the
  ## parser/walker disagreement about an unstamped non-magic callee cannot be
  ## reached. The set of rows that can trip `overflowChecks` is pinned to the
  ## six audited at 31d94909, and each body's identifiers to the magic and
  ## operator vocabulary: a new row, or a body that calls another routine,
  ## fails here and needs D1-F2 first.
  const mathSrc = staticRead(querySetting(libPath) / "pure" / "math.nim")
  var keys: seq[string]
  for k in stdlibAxis.keys:
    let a = admitStdlibBody(k, ssBodyWalk)
    if a.admitted and a.payload.deltaKnown and coOverflow in a.payload.exercises:
      keys.add k
  check keys.len == 6
  for want in ["math.isPowerOfTwo", "math.floorDiv", "math.floorMod",
               "math.euclDiv", "math.euclMod", "math.nextPowerOfTwo"]:
    check want in keys
  for k in keys:
    checkpoint k
    let name = k["math.".len .. ^1]
    check k.startsWith("math.")
    for id in identsOf(bodyOf(mathSrc, name)):
      if id notin overflowRowBodyIdents:
        checkpoint "callee outside the magic vocabulary: " & id & " in " & k
        check id in overflowRowBodyIdents
