## RFC-0016 WA-B (M2), `witnessUndefined` end to end. The render test in
## `tsymex_0016_wa_runtime.nim` builds a finding by hand; on a real run only
## `ubIndeterminateRead` can ride a witness (`unwrittenUb`; the arithmetic
## `ub*` kinds halt the path). This drives that one kind through the public
## entry points: `symexFind`, `renderReport`, `symexFindAllWitnesses` over an
## in-memory database, and `assertCoveredBy`.
import std/[unittest, strutils, json]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/[canonicalize, replayproc]

proc scrub() {.noinline.} =
  ## Zero the stack below the caller, where the replay's frames land, so the
  ## `{.noinit.}` slot reads zero natively and the replay confirms.
  var a {.volatile.}: array[8192, int]
  for i in 0 ..< a.len: a[i] = 0

var ueRan = 0

proc ueNoinit(k: int) =
  ## `k` keeps the parameter list non-empty, which `symexFindAllWitnesses`
  ## needs; the read of `x` is on the path to the label. The label does not
  ## depend on the value `x` happens to hold (`x == x`), so the replay reaches
  ## it on any stack layout, whichever entry point runs it.
  var x {.noinit.}: int
  if k > 0 and x == x: symexTarget("ue")

proc ueProbe(k: int) =
  ## The `testFn` of the coverage check: counts the runs the host makes.
  inc ueRan

proc report(f: SymexFinding): Report[int] =
  Report[int](outcome: otPassed, examples: 1, symexFindings: @[f])

suite "WA-B M2: a real noinit witness":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 286

  when defined(cpp) or replayReexecs:
    ## The replay's frames differ (cpp) or are a fresh stack (re-executed), so
    ## the scrubbed slot is not zero there and the witness is not confirmed.
    test "skipped: the replay stack is not the scrubbed one":
      skip()
  else:
    test "symexFind: the witness carries the kind, and is not host-runnable":
      scrub()
      let r = symexFind(ueNoinit, tLabel("ue"))
      checkpoint $r.status & " " & $r.soundness
      check r.status == sxSat
      check r.soundness.witnessUndefined == ubOrdinals({UbKind(ubIndeterminateRead)})
      check r.soundness.undefinedKinds == {UbKind(ubIndeterminateRead)}
      check not hostRunnable(r.soundness)
      check not r.trusted

    test "the report names the kind in text and in JSON":
      scrub()
      let db = inMemoryDatabase()
      let fs = symexFindAllWitnesses(ueNoinit, db)
      check fs.len == 1
      let t = renderReport(report(fs[0]), ofText)
      checkpoint t
      check "witnessUndefined=ubIndeterminateRead" in t
      let j = parseJson(renderReport(report(fs[0]), ofJson))
      let u = j["symexFindings"][0]["soundness"]["witnessUndefined"]
      check u.len == 1
      check u[0].getStr == "ubIndeterminateRead"

    test "a second run over the same database answers from the cache":
      scrub()
      let db = inMemoryDatabase()
      let cold = symexFindAllWitnesses(ueNoinit, db)
      check cold.len == 1
      check not cold[0].fromCache
      check cold[0].soundness.undefinedKinds == {UbKind(ubIndeterminateRead)}
      let warm = symexFindAllWitnesses(ueNoinit, db)
      check warm.len == 1
      check warm[0].fromCache
      check warm[0].soundness.undefinedKinds == {UbKind(ubIndeterminateRead)}
      check warm[0].soundness.witnessUndefined ==
            cold[0].soundness.witnessUndefined
      check not hostRunnable(warm[0].soundness)

    test "assertCoveredBy does not run the witness in the host":
      scrub()
      ueRan = 0
      var msg = ""
      var raised = false
      try:
        discard assertCoveredBy(ueNoinit, tLabel("ue"), ueProbe)
      except SymexCoverageDefect as e:
        raised = true
        msg = e.msg
      checkpoint msg
      check ueRan == 0
      check raised
      check "ubIndeterminateRead" in msg
