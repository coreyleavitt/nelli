## Wiring audit (wave 4), C-4 to C-6: every renderer shows what the report
## carries.
##
## * C-4: `Report.dbErrors` is in the text report (so JUnit's system-out) and
##   the GitHub annotations, as it was in JSON.
## * C-5: a finding's `undefined` behaviours and non-winning `diagnostics`
##   (the unsafe-witness ones among them) are GitHub annotations too.
## * C-6: a hint's severity is in the text, and a warning-severity hint is a
##   `::warning` annotation.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/engine/types

proc finding(): SymexFinding =
  SymexFinding(
    status: sfSat, targetDesc: "label(\"w\")",
    hints: @[FindingHint(kind: feReplayCrashed, severity: sevHint, msg: "h1"),
             FindingHint(kind: seUnsupportedRegex, severity: sevWarning,
                         msg: "h2")],
    undefined: @[FindingUndefined(kind: "ubUnsignedDivZero", site: "a.nim(1, 2)",
                                  witnessChoices: @[])],
    diagnostics: @[FindingDiagnostic(raisedTypeId: "ValueError", raisedMsg: "m",
                                     witnessUnsafe: false),
                   FindingDiagnostic(raisedTypeId: "IndexDefect", isDefect: true,
                                     witnessUnsafe: true)])

suite "wiring audit C-4: Report.dbErrors in every renderer":
  let r = Report[int](outcome: otPassed, dbErrors: @["disk full", "bad key"])

  test "text, and JUnit's system-out":
    check "db_error=disk full" in renderReport(r, ofText)
    check "db_error=bad key" in renderReport(r, ofText)
    let j = renderReport(r, ofJunit)
    check "<system-out>" in j
    check "db_error=disk full" in j

  test "GitHub, one warning per error":
    let g = renderReport(r, ofGithubAnnotation)
    check g.count("::warning title=symex db error::") == 2
    check "disk full" in g

  test "a report with none renders none":
    let c = Report[int](outcome: otPassed)
    check "db_error" notin renderReport(c, ofText)
    check "system-out" notin renderReport(c, ofJunit)
    check "db error" notin renderReport(c, ofGithubAnnotation)

suite "wiring audit C-5, C-6: a finding's undefined, diagnostics and hints":
  let r = Report[int](outcome: otPassed, symexFindings: @[finding()])

  test "GitHub shows undefined behaviour and diagnostics":
    let g = renderReport(r, ofGithubAnnotation)
    check "::warning title=symex undefined behaviour::" in g
    check "ubUnsignedDivZero" in g
    check "::notice title=symex also raised::" in g
    check "ValueError" in g
    check "::warning title=symex also raised::" in g   # the unsafe witness
    check "witnessUnsafe" in g

  test "a warning hint is a warning, in GitHub and its severity is in text":
    let g = renderReport(r, ofGithubAnnotation)
    check "::notice title=symex hint::" in g
    check "::warning title=symex hint::" in g
    let t = renderReport(r, ofText)
    check "hint feReplayCrashed: h1" in t
    check "hint seUnsupportedRegex (sevWarning): h2" in t
