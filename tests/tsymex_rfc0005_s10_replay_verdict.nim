## RFC-0005 (soundness channels) slice S10 -- the SAT relaxation: §2.3 rule 3
## wired into the verdict of BOTH `runSymex` consumers (§4.2 "Plumbing").
## Walker 146 -> 147.
##
## Before S10 a run whose only SAT lay on an `scSpurious`-tainted path stayed
## `sxUnknown` whatever reality said (rule 4), and the solved model sat in
## `RawResult.candidates` unread. Now each entry macro settles the candidates
## after `runSymex` returns (`emitRunSymexReplayed`, `symex.nim`): the
## candidate's witness is RUN against the real `fn`, and only a confirming
## replay reports `sxSat`/`sxRaised`. Pinned here:
##   (a) DoD §6.2's trio through `symexFind`: a witness on a
##       `dcFreshSymbol`-tainted path reports `sxSat` with the replay
##       confirmed in the reporting path; a refuted companion stays
##       `sxUnknown` (with `feReplayRefuted`); an `scSpurious`-tainted raise is
##       routed and replay-gated (confirmed -> `sxRaised`, refuted ->
##       `sxUnknown`). Plus the guards: an ineligible (⊤) candidate never runs
##       `fn`; a clean witness never runs it either.
##   (b) the `parseInt` `+`/`_` over-report (RFC-0005 S7's note): Z3's
##       `str.to_int` rejects what Nim's `parseInt` accepts, so the raise on
##       such a string was a CLEAN, sometimes false `sxRaised`. S10 splits the
##       predicate; the lax half is a candidate and replay classifies it.
##       (RFC-0005 S8b made the `+` sign exact -- only `_` is lax now -- so
##       the `+` pins below are clean verdicts, and the replayed lax pins use
##       `_` strings.)
##   (c) the trio through `symexFindAllWitnesses` and `symexForAll`, and the
##       cache: replay precedes persist, a confirmed candidate is stored as
##       the `sxSat`/`sxRaised` it became, a refuted one as `sfUnknown`, and
##       a served entry is never replayed again.
##   (d) candidacy is unspellable as sat: `SatCandidate` exposes no witness
##       (compile-time pin) and `runSymex` is emitted from exactly one place
##       in `symex.nim`, the settle emitter (structural pin).
import std/[unittest, strutils, os, options, unicode]
import nelli
import nelli/symex
import nelli/engine/types
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import audit_scan_utils

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc severityOf(errs: seq[SymexErrorInfo]; k: SymexErrorKind): SymexErrorSeverity =
  for e in errs:
    if e.kind == k: return e.severity
  raiseAssert "no " & $k

var sideEffects = 0   ## counts REAL executions of the SUTs below: symex never
                      ## runs `fn`, so every increment during a `symexFind`
                      ## is a verdict-time replay

proc tick() {.symexTransparent.} =
  ## A real side effect the walker is promised it cannot observe (statement
  ## position, void), so the SUTs stay modelled and replay is countable.
  inc sideEffects

# =============================================================================
# SUTs. `a < a` on a bool is system's magic `<`, which the walker models as a
# FRESH symbol (`feUnsupportedOpHavoc`, `dcFreshSymbol`): every path past it
# carries exactly `{scSpurious}` -- replay-eligible. Reality: `a < a` is
# always false, so `not o` always holds and `o` never does. That makes each
# replay outcome deterministic whatever witness the solver picks.
# =============================================================================

proc s10Confirm(a: bool; x: int) =
  tick()
  let o = a < a
  if not o:
    if x == 42:
      symexTarget("s10_confirm")

proc s10Refute(a: bool; x: int) =
  tick()
  let o = a < a
  if o:
    if x == 42:
      symexTarget("s10_refute")

proc s10RaiseConfirm(a: bool; x: int) =
  tick()
  let o = a < a
  if not o and x == 7:
    raise newException(ValueError, "s10 confirm")

proc s10RaiseRefute(a: bool; x: int) =
  tick()
  let o = a < a
  if o and x == 7:
    raise newException(ValueError, "s10 refute")

proc s10Sensor(): int {.symexOpaque.} = 7
  ## Opaque and USED: `feOpaqueCallUnmodelled`, `dcSubstituted` -- a ⊤ path
  ## taint, outside replay's eligibility gate.

proc s10Ineligible(x: int) =
  tick()
  if s10Sensor() + x == 50:
    symexTarget("s10_ineligible")

proc s10Clean(x: int) =
  tick()
  if x == 42:
    symexTarget("s10_clean")

# ---- parseInt: the `+` / `_` over-report ------------------------------------

proc s10ParsePlusDigit(s: string) =
  tick()
  if s == "+5":
    discard parseInt(s)      ## Nim: 5. Z3 `str.to_int("+5")` = -1 -> "raises"

proc s10ParsePlusAlpha(s: string) =
  tick()
  if s == "+x":
    discard parseInt(s)      ## Nim raises too: a real ValueError

proc s10ParseUnderscoreAlpha(s: string) =
  tick()
  if s == "1_x":
    discard parseInt(s)      ## Nim raises too: `x` is no digit

proc s10ParseUnderscore(s: string) =
  tick()
  if s == "1_0":
    discard parseInt(s)      ## Nim: 10 (`_` is a digit separator)

proc s10ParseAlpha(s: string) =
  tick()
  if s == "abc":
    discard parseInt(s)      ## the EXACT half: raises in both, forked clean

# ---- symexFindAllWitnesses / symexForAll: single-param SUTs ------------------

proc s10AllConfirm(a: bool) =
  tick()
  let o = a < a
  if not o:
    symexTarget("s10_all_confirm")

proc s10AllRefute(a: bool) =
  tick()
  let o = a < a
  if o:
    symexTarget("s10_all_refute")

proc s10AllAssertConfirm(a: bool) =
  tick()
  let o = a < a
  assert o, "s10 assert"     ## fails for real on every input

proc s10AllAssertRefute(a: bool) =
  tick()
  let o = a < a
  assert not o, "s10 assert" ## holds for real on every input

# ---- replay's splat: rendered witness type != parameter type; non-void fn ---

proc s10RuneConfirm(a: bool; r: Rune) =
  ## The witness reader renders a `Rune` as `int`; replay converts it back.
  tick()
  let o = a < a
  if not o and r == Rune(0x41):
    symexTarget("s10_rune_confirm")

proc s10RuneRefute(a: bool; r: Rune) =
  tick()
  let o = a < a
  if o and r == Rune(0x41):
    symexTarget("s10_rune_refute")

proc s10NonVoid(a: bool; x: int): int =
  tick()
  let o = a < a
  if not o and x == 42:
    symexTarget("s10_nonvoid")
  x

# =============================================================================
# ---- the opt-out: `SymexSettings.replay = false` ------------------------------

proc s10NoSuchSymbol(x: int): bool {.importc: "s10_no_such_symbol_rfc0005".}
  ## Deliberately UNLINKABLE: no C definition exists anywhere. A SUT that
  ## calls it is analysable (an opaque call) but cannot be executed -- and,
  ## with replay on, could not even be linked, since replay's codegen
  ## references `fn`. This test binary linking at all is the structural pin
  ## that the opt-out emits no reference to `fn`.

proc s10Unlinkable(a: bool; x: int) =
  ## The unlinkable call is kept OUT of the target's guard: a bodiless
  ## `importc` is walked as an empty body today (a pre-existing false
  ## `sxUnsat` when its result guards a target -- reported with S10, not
  ## pinned here). The guard is the replay-eligible fresh-symbol shape.
  discard s10NoSuchSymbol(x)
  let o = a < a
  if not o and x == 42:
    symexTarget("s10_unlinkable")

const s10NoReplay = block:
  var s = defaultSymexSettings()
  s.replay = false
  s

# =============================================================================
# =============================================================================

suite "RFC-0005 S10 (a) -- symexFind: rule 3, the replay-gated SAT relaxation":

  test "a witness on a dcFreshSymbol-tainted path reports sxSat, replay confirmed":
    sideEffects = 0
    let r = symexFind(s10Confirm, tLabel("s10_confirm"))
    check r.status == sxSat
    check r.witness[1] == 42
    ## The path is tainted -- by a dcFreshSymbol kind only -- so rules 1-2
    ## could not have produced this: `runSymex` itself decided sxUnknown
    ## (the unvetoed verdict of the same pools) ...
    check r.errors.hasKind(feUnsupportedOpHavoc)
    check classOf(feUnsupportedOpHavoc) == dcFreshSymbol
    check rfc0005UnvetoedStatus == sxUnknown
    ## ... and the reporting path ran the real fn on the witness, exactly once.
    check sideEffects == 1
    check not r.errors.hasKind(feReplayRefuted)

  test "a companion whose witness the real fn refutes stays sxUnknown":
    sideEffects = 0
    let r = symexFind(s10Refute, tLabel("s10_refute"))
    check r.status == sxUnknown
    check sideEffects == 1                       ## replay RAN ...
    check r.errors.hasKind(feReplayRefuted)      ## ... and refuted it
    check r.errors.severityOf(feReplayRefuted) == sevHint
    check r.errors.hasKind(feUnsupportedOpHavoc)

  test "an scSpurious-tainted raise is routed and replay-gated: confirmed -> sxRaised":
    sideEffects = 0
    let r = symexFind(s10RaiseConfirm, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[1] == 7
    check rfc0005UnvetoedStatus == sxUnknown     ## a candidate, not a winner
    check sideEffects == 1

  test "an scSpurious-tainted raise the real fn does not raise stays sxUnknown":
    sideEffects = 0
    let r = symexFind(s10RaiseRefute, tRaisedExn("ValueError"))
    check r.status == sxUnknown
    check sideEffects == 1
    check r.errors.hasKind(feReplayRefuted)

  test "an ineligible (⊤-tainted) candidate is never executed":
    sideEffects = 0
    let r = symexFind(s10Ineligible, tLabel("s10_ineligible"))
    check r.status == sxUnknown
    check r.errors.hasKind(feOpaqueCallUnmodelled)
    check sideEffects == 0
    check not r.errors.hasKind(feReplayRefuted)

  test "a clean witness is reported without running fn":
    sideEffects = 0
    let r = symexFind(s10Clean, tLabel("s10_clean"))
    check r.status == sxSat
    check sideEffects == 0

  test "replay inside a user's active capture leaves that capture intact":
    symexCaptureBegin()
    symexTarget("userBefore")
    let r = symexFind(s10Confirm, tLabel("s10_confirm"))
    symexTarget("userAfter")
    let hits = symexCaptureEnd()
    check r.status == sxSat
    check "userBefore" in hits and "userAfter" in hits
    check "s10_confirm" notin hits

  test "a converted witness (Rune rendered as int) confirms on a hit":
    sideEffects = 0
    let r = symexFind(s10RuneConfirm, tLabel("s10_rune_confirm"))
    check r.status == sxSat
    check sideEffects == 1

  test "a converted witness's miss is inconclusive, never a refutation":
    sideEffects = 0
    let r = symexFind(s10RuneRefute, tLabel("s10_rune_refute"))
    check r.status == sxUnknown
    check sideEffects == 1                       ## it ran ...
    check not r.errors.hasKind(feReplayRefuted)  ## ... but a conversion may round

  test "a non-void fn is replayed with its result discarded":
    sideEffects = 0
    let r = symexFind(s10NonVoid, tLabel("s10_nonvoid"))
    check r.status == sxSat
    check r.witness[1] == 42
    check sideEffects == 1

suite "RFC-0005 S10 (b) -- parseInt's `+` / `_` over-report, classified by replay":

  test "\"+5\": Nim parses it -- no raise at all, sxUnsat (S10: a refuted lax raise; before S10 a clean false sxRaised)":
    # RFC-0005 S8b: the `+` sign is modelled exactly (`rawParseInt`), so
    # "+5" parses and the ValueError target is unreachable -- a clean
    # verdict with no candidate to replay.
    sideEffects = 0
    let r = symexFind(s10ParsePlusDigit, tRaisedExn("ValueError"))
    check r.status == sxUnsat
    check not r.errors.hasKind(feReplayRefuted)
    check sideEffects == 0

  test "\"1_0\": `_` is a digit separator in Nim -- refuted, sxUnknown":
    sideEffects = 0
    let r = symexFind(s10ParseUnderscore, tRaisedExn("ValueError"))
    check r.status == sxUnknown
    check r.errors.hasKind(feReplayRefuted)
    check sideEffects == 1

  test "\"+x\": Nim raises too -- since S8b an exact, clean sxRaised, no replay":
    sideEffects = 0
    let r = symexFind(s10ParsePlusAlpha, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[0] == "+x"
    check sideEffects == 0

  test "\"1_x\": Nim raises too -- the lax raise is confirmed, sxRaised":
    sideEffects = 0
    let r = symexFind(s10ParseUnderscoreAlpha, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[0] == "1_x"
    check sideEffects == 1

  test "the exact half stays a clean sxRaised, no replay":
    sideEffects = 0
    let r = symexFind(s10ParseAlpha, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedWitness[0] == "abc"
    check sideEffects == 0

  test "seParseIntLaxSyntax is dcFreshSymbol: the lax raise is replay-eligible, never voids sxUnsat":
    check classOf(seParseIntLaxSyntax) == dcFreshSymbol
    check replayEligible(pathTaint(classOf(seParseIntLaxSyntax)))
    check scIncomplete notin runTaint(classOf(seParseIntLaxSyntax))

proc findingFor(fs: seq[SymexFinding]; desc: string): Option[SymexFinding] =
  for f in fs:
    if f.targetDesc == desc: return some(f)
  none(SymexFinding)

suite "RFC-0005 S10 (c) -- symexFindAllWitnesses / symexForAll, and the cache":

  test "symexFindAllWitnesses: a confirmed candidate is sfSat, and is persisted as one":
    let db = inMemoryDatabase()
    sideEffects = 0
    let fs = symexFindAllWitnesses(s10AllConfirm, db)
    let f = fs.findingFor("label(\"s10_all_confirm\")")
    check f.isSome
    check f.get.status == sfSat
    check f.get.witnessChoices.len > 0
    check not f.get.fromCache
    check sideEffects == 1
    ## Replay precedes persist: the SAT slot holds the replayed witness, and
    ## a second run serves it without replaying again.
    let stored = loadSymexWitnesses(db, s10AllConfirm, tLabel("s10_all_confirm"),
                                    defaultSymexSettings())
    check stored.len == 1
    sideEffects = 0
    let again = symexFindAllWitnesses(s10AllConfirm, db).findingFor(
      "label(\"s10_all_confirm\")")
    check again.isSome and again.get.status == sfSat and again.get.fromCache
    check sideEffects == 0

  test "symexFindAllWitnesses: a refuted candidate is sfUnknown, never persisted as sat":
    let db = inMemoryDatabase()
    sideEffects = 0
    let f = symexFindAllWitnesses(s10AllRefute, db).findingFor(
      "label(\"s10_all_refute\")")
    check f.isSome
    check f.get.status == sfUnknown
    check sideEffects == 1
    check loadSymexWitnesses(db, s10AllRefute, tLabel("s10_all_refute"),
                             defaultSymexSettings()).len == 0
    check loadSymexVerdict(db, s10AllRefute, tLabel("s10_all_refute"),
                           defaultSymexSettings()) == some(sfUnknown)

  test "symexFindAllWitnesses: an scSpurious-tainted raise is replay-gated (confirmed -> sfRaised)":
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(s10AllAssertConfirm, db)
    checkpoint($fs)
    let f = fs.findingFor("raised(AssertionDefect)")
    check f.isSome
    check f.get.status == sfRaised
    check f.get.defectTypeId == "AssertionDefect"

  test "symexFindAllWitnesses: a refuted tainted raise reports no raise":
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(s10AllAssertRefute, db)
    checkpoint($fs)
    check fs.findingFor("raised(AssertionDefect)").isNone
    var anyUnknown = false
    for f in fs:
      check f.status notin {sfSat, sfRaised}
      if f.status == sfUnknown: anyUnknown = true
    check anyUnknown

  test "symexForAll: the confirmed candidate reaches the report as sfSat":
    let report = symexForAll(booleans(), s10AllConfirm, inMemoryDatabase())
    let f = report.symexFindings.findingFor("label(\"s10_all_confirm\")")
    check f.isSome
    check f.get.status == sfSat

  test "symexForAll: the refuted companion stays sfUnknown":
    let report = symexForAll(booleans(), s10AllRefute, inMemoryDatabase())
    let f = report.symexFindings.findingFor("label(\"s10_all_refute\")")
    check f.isSome
    check f.get.status == sfUnknown

suite "RFC-0005 S10 (e) -- the opt-out: SymexSettings.replay = false":

  test "an unlinkable SUT is analysed under the opt-out (no reference to fn is emitted)":
    ## Reaching this line proves the binary linked with `s10Unlinkable`'s
    ## `symexFind` in it (see `s10NoSuchSymbol`).
    let r = symexFind(s10Unlinkable, tLabel("s10_unlinkable"), s10NoReplay)
    check r.status == sxUnknown          ## a candidate, not replayed
    check rfc0005UnvetoedStatus == sxUnknown
    let fs = symexFindAllWitnesses(s10Unlinkable, inMemoryDatabase(), s10NoReplay)
    check fs.findingFor("label(\"s10_unlinkable\")").isSome

  test "a candidate a replay would confirm stays sxUnknown under the opt-out, and fn never runs":
    sideEffects = 0
    let r = symexFind(s10Confirm, tLabel("s10_confirm"), s10NoReplay)
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedOpHavoc)
    check not r.errors.hasKind(feReplayRefuted)
    check sideEffects == 0
    let f = symexFindAllWitnesses(s10AllConfirm, inMemoryDatabase(),
                                  s10NoReplay).findingFor(
      "label(\"s10_all_confirm\")")
    check f.isSome and f.get.status == sfUnknown
    check sideEffects == 0

  test "replay participates in the cache key only when off (default keys unchanged)":
    var on = defaultSymexSettings()
    check on.replay
    check "rp=" notin canonicalize(on)
    check ";rp=off" in canonicalize(s10NoReplay)

  test "symexForAll honours the opt-out":
    let report = symexForAll(booleans(), s10AllConfirm, inMemoryDatabase(),
                             s10NoReplay)
    let f = report.symexFindings.findingFor("label(\"s10_all_confirm\")")
    check f.isSome and f.get.status == sfUnknown


const symexSrcPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                     "symex.nim"

proc codeLinesNaming(path, ident: string): seq[string] =
  ## Non-comment lines of `path` containing `ident` followed by `(` or `"`
  ## (a call, or a `bindSym"ident"`), excluding its own declaration.
  for raw in readFile(path).splitLines():
    let t = raw.strip()
    if t.len == 0 or isCommentLine(t): continue
    if t.startsWith("proc " & ident) or t.startsWith("func " & ident): continue
    if (ident & "(") in t or (ident & "\"") in t: result.add t

suite "RFC-0005 S10 (d) -- candidacy is unspellable as sat":

  test "a SatCandidate exposes no witness outside symex.nim's replay codegen":
    var c: SatCandidate
    check compiles(c.status)
    check compiles(c.pathTaint)
    check not compiles(c.input)
    check not compiles(c.witness)
    check not compiles(c.raisedWitness)
    check not compiles(candidateInput(c))
    check not compiles(settleCandidate(RawResult(status: sxUnknown), c,
                                       roConfirmed))

  test "runSymex is emitted from exactly one place in symex.nim: the settle emitter":
    let calls = codeLinesNaming(symexSrcPath, "runSymex")
    checkpoint($calls)
    check calls.len == 1
    check calls.len == 1 and "runSymex(`prog`, `target`, `settings`)" in calls[0]

  test "the candidate readers are reached only through the settle emitter's bindSym":
    let inputs = codeLinesNaming(symexSrcPath, "candidateInput")
    let settles = codeLinesNaming(symexSrcPath, "settleCandidate")
    checkpoint($inputs & " / " & $settles)
    check inputs == @["let inputSym  = bindSym\"candidateInput\""]
    check settles == @["let settleSym = bindSym\"settleCandidate\""]

  test "both entry macros route through emitRunSymexReplayed":
    let uses = codeLinesNaming(symexSrcPath, "emitRunSymexReplayed")
    checkpoint($uses)
    check uses.len == 2

suite "RFC-0005 S10 -- walker version pin":
  test "walker version floor >= 147 (rule 3 wired; parseInt's raise split)":
    check parseInt(symexWalkerVersion) >= 147
