## RFC-0016 W3-z R5. U6: `SymexFinding.undefined` is rendered (text and JSON).
## U7: a diagnostic raise carries its own soundness, so a caller can tell which
## witness is safe to run in-process.
import std/[unittest, strutils, json]
import nelli
import nelli/symex
import nelli/db
import nelli/smt/[types, soundness]
import nelli/engine/types as etypes

proc sutUDivSat(k: uint64) =
  let r = 10'u64 div k
  if r == 5: symexTarget("hit")

proc undefRaise(k, m: int) =
  ## The raise at `doAssert` is reached after a read of an uninitialised slot.
  var x {.noinit.}: int
  let y = x + 0
  doAssert m != 5
  if k == 7 and m == 3 and y == 1: symexTarget("hit")

proc cleanRaise(k: int) =
  doAssert k != 4

proc report(f: SymexFinding): Report[int] =
  Report[int](outcome: otPassed, examples: 1, symexFindings: @[f])

suite "W3-z R5 U6: the undefined behaviour a run reached is rendered":
  test "text and JSON name each undefined behaviour":
    let db = inMemoryDatabase()
    var f: SymexFinding
    var found = false
    for c in symexFindAllWitnesses(sutUDivSat, db):
      if c.targetDesc == "label(\"hit\")":
        f = c; found = true
    check found
    check f.undefined.len == 1
    let t = renderReport(report(f), ofText)
    checkpoint t
    check "undefined ubUnsignedDivZero" in t
    let j = parseJson(renderReport(report(f), ofJson))
    let u = j["symexFindings"][0]["undefined"]
    check u.len == 1
    check u[0]["kind"].getStr == "ubUnsignedDivZero"
    check u[0]["site"].getStr.len > 0
    check u[0]["witnessChoiceCount"].getInt > 0

suite "W3-z R5 U7: a raise carries its own soundness":
  test "allRaiseFindings: the raise past undefined behaviour reports it":
    let r = symexFind(undefRaise, tLabel("hit"))
    check r.status == sxRaised
    let all = allRaiseFindings(r)
    check all.len == 1
    check all[0].witnessUndefined == ubOrdinals({UbKind(ubIndeterminateRead)})
    check not hostRunnable(all[0])

  test "a clean raise is host-runnable":
    let r = symexFind(cleanRaise, tRaisedExn("AssertionDefect"))
    let all = allRaiseFindings(r)
    check all.len == 1
    check all[0].witnessUndefined == {}
    check hostRunnable(all[0])

  test "the flag is rendered, and survives the notes record":
    let d = FindingDiagnostic(raisedTypeId: "SIGSEGV", isDefect: true,
      witnessUnsafe: true)
    var f = SymexFinding(targetDesc: "label(\"hit\")", status: sfSat,
                         diagnostics: @[d])
    let t = renderReport(report(f), ofText)
    check "witnessUnsafe" in t
    check "(not host-runnable)" in t
    let j = parseJson(renderReport(report(f), ofJson))
    let jd = j["symexFindings"][0]["diagnostics"][0]
    check jd["witnessUnsafe"].getBool
    check not jd["hostRunnable"].getBool
    let db = inMemoryDatabase()
    let prog = SymexProgram(body: IRStmt(kind: isBlock))
    var errs: seq[string]
    saveSymexNotesImpl(db, prog, tLabel("hit"), defaultSymexSettings(), @[],
                       @[d, FindingDiagnostic(raisedTypeId: "IndexDefect")], @[],
                       errs)
    let n = loadSymexNotesImpl(db, prog, tLabel("hit"), defaultSymexSettings(),
                               errs)
    check errs.len == 0
    check n.diagnostics.len == 2
    check n.diagnostics[0].witnessUnsafe
    check not n.diagnostics[1].witnessUnsafe
