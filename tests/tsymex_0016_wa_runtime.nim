## RFC-0016 WA-B, the checks-on rows.
##
## * S4. `crashRaise` marks a crash claim `witnessUnsafe` (its witness ends
##   the process wherever it runs), but `settleWinner` assigned the replay's
##   `endsChild` over it: a crash claim whose witness renders lossily was
##   reported `hostRunnable`, and `assertCoveredBy` ran it in the host. The
##   claim's own flag now survives the settle, and the cache stores it.
## * P4. `Soundness.witnessUndefined` was never rendered; it is, by `UbKind`
##   name, in the text line, the JSON and a GitHub warning.
import std/[unittest, strutils, json]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

type
  WaDist = object
    ## A `seq` of tuples, which no heap cell holds: a `ref` to an object with
    ## one renders lossily (`wfLossy`).
    x: int
    ys: seq[(int, int)]
  WaBox = object
    n: int
    s: WaDist

proc lossyNil(p: ref WaBox) =
  ## A clean path to a nil dereference; the witness renders lossily and the
  ## replay does not run for the target (`replayInScope`).
  if p == nil or p.n == 5:
    discard p.n

proc report(fs: seq[SymexFinding]): Report[int] =
  Report[int](outcome: otPassed, examples: 1, symexFindings: fs)

suite "WA-B S4: a crash claim stays witnessUnsafe":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 286

  test "a lossy crash claim is unsafe, and not host-runnable":
    let r = symexFind(lossyNil, tNilAccess())
    checkpoint $r.status & " " & $r.soundness
    check r.status == sxRaised
    check r.soundness.witnessUnsafe
    check not hostRunnable(r.soundness)

suite "WA-B P4: witnessUndefined is rendered":
  let f = SymexFinding(targetDesc: "label(\"u\")", status: sfSat,
                       soundness: Soundness(
                         replay: rsConfirmed,
                         witnessUndefined: ubOrdinals({UbKind(ubSignedOverflow),
                                                       UbKind(ubSignedDivZero)})))
  let clean = SymexFinding(targetDesc: "label(\"u\")", status: sfSat,
                           soundness: Soundness(replay: rsConfirmed))

  test "the text line names the kinds":
    let t = renderReport(report(@[f]), ofText)
    checkpoint t
    check "witnessUndefined=ubSignedOverflow,ubSignedDivZero" in t
    check "witnessUndefined" notin renderReport(report(@[clean]), ofText)

  test "the JSON lists the kinds":
    let j = parseJson(renderReport(report(@[f]), ofJson))
    let u = j["symexFindings"][0]["soundness"]["witnessUndefined"]
    check u.len == 2
    check u[0].getStr == "ubSignedOverflow"
    check u[1].getStr == "ubSignedDivZero"
    let c = parseJson(renderReport(report(@[clean]), ofJson))
    check c["symexFindings"][0]["soundness"]["witnessUndefined"].len == 0

  test "a GitHub warning names the kinds":
    let g = renderReport(report(@[f]), ofGithubAnnotation, "p")
    checkpoint g
    check "::warning title=symex witness undefined::" in g
    check "ubSignedOverflow, ubSignedDivZero" in g
    check "witness undefined" notin renderReport(report(@[clean]),
                                                 ofGithubAnnotation, "p")
