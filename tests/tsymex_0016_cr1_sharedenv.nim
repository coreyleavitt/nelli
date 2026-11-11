## RFC-0016 0.10.0 review H1. Closures that share one captured environment on
## the host share it in the replay's child. A forked child (this file, the
## Linux and macOS default) is a copy of the host, so it does; a re-executed
## one (`tsymex_0016_cr1_sharedenv_reexec`, which includes this file under
## `-d:nelliReplayReexec`; Windows' default) is handed the environments on the
## wire, which writes each once and names it again by identity
## (`replaywire.putEnv`), as it does a `ref`. Before the fix the wire wrote a
## copy per closure: the closure that wrote the value and the one that read it
## no longer met, and the re-executed child confirmed a trusted `sxSat` the
## program cannot reach, while a forked child refuted it.
##
## The SUTs (`helpers/cr1_sharedenv_sut`): natively each computes 1 from a
## fresh start, so its target is unreachable. The engine treats the opaque
## call as havoc, finds the target satisfiable, and the replay must refute it
## (or decline, naming why). Never a trusted `sxSat`.
import std/[unittest, strutils, options]
import nelli
import nelli/symex
import nelli/smt/types
from nelli/smt/runtime import hostAdmission
from nelli/smt/replayproc import replayForks
import ./s8cu_helpers except show
import helpers/cr1_sharedenv_sut

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  parts.join("\n")

proc refuted(r: SymexResult): bool =
  for e in r.errors:
    if e.kind == feReplayRefuted: return true

const cr1Mode = when replayForks: "fork" else: "reexec"

suite "0.10.0 review H1: closures sharing one environment (" & cr1Mode & ")":
  test "the walker's version floor (H1)":
    check parseInt(symexWalkerVersion) >= 358

  test "an int shared by two closures: natively 1, the replay refutes 0":
    mkShared()
    runShared(3)
    check gShOut == 1
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkShared()
      let r = symexFind(sutShared, tLabel("t"))
      checkpoint show(r.errors)
      check not (r.status == sxSat and r.trusted)
      check r.status == sxUnknown
      check refuted(r)

  test "a string shared by two closures (the codec path): refuted":
    mkSharedStr()
    runSharedStr(3)
    check gShOut == 1
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkSharedStr()
      let r = symexFind(sutSharedStr, tLabel("t"))
      checkpoint show(r.errors)
      check not (r.status == sxSat and r.trusted)
      check r.status == sxUnknown
      check refuted(r)

  test "one environment reached from a closure and a ref's field: not trusted":
    ## The route scan reads module-level closure variables only
    ## (`closureRouteGuard`): a closure held in a `ref`'s field opens the
    ## routes (`feGlobalRouteUnproved`), so this run does not reach the label's
    ## replay today. Were it admitted, the wire names the environment in the
    ## one `cells` table it names `ref` cells in, so the field's closure and
    ## the variable's still share it. Either way, never a trusted `sxSat`.
    mkSharedBox()
    runSharedBox(3)
    check gShOut == 1
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkSharedBox()
      let r = symexFind(sutSharedBox, tLabel("t"))
      checkpoint show(r.errors)
      check not (r.status == sxSat and r.trusted)
      check r.status == sxUnknown
