## RFC-0016 W3-z R10. A module-level closure variable that holds, when the run
## starts, a closure WITH a captured environment, under a forked replay (the
## host's default on Linux and macOS). The re-executed half is in
## `tsymex_0016_prc02_reexec` (the same SUTs, `helpers/r10_closenv_sut`).
##
## The closure's routine is nested, so the settle names it by an address only
## module-level code can take (`nestedRoutineAddrs`); a forked child is a copy
## of the host, so the environment it runs with is the host's. What the
## routine's body may reach then replaces the call's "may be undefined".
## A closure whose environment holds an address is not lifted, and the
## confirmed claim says why (`feReplayDeclined`), never a bare kind.
##
## A build without `fork` (Windows) re-executes: the same tests pin re-exec
## cells there (`mode`), and a cell only a fork reaches asserts the re-exec
## child's named decline instead.
import std/[unittest, strutils, options]
import nelli
import nelli/symex
import nelli/smt/types
from nelli/smt/runtime import hostAdmission
from nelli/smt/replayproc import replayForks
import ./s8cu_helpers except show
import helpers/r10_closenv_sut

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  parts.join("\n")

const mode = when replayForks: "fork/" else: "reexec/"
  ## The replay mode this build runs: a build with no `fork` (Windows)
  ## re-executes, and its verdicts are re-exec cells.

suite "W3-z R10: a start-value closure with an environment (fork)":
  test "the walker's version floor (R10)":
    check parseInt(symexWalkerVersion) >= 346

  test "a captured int, a checked routine: exact":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartEnv()
      discard pinExact(sutStartEnv, cellKey(faCallShape,
                       mode & "procValueClosureStartEnv"), tLabel("t"))
      gStartEnv = nil

  test "a captured int that makes an unchecked routine overflow":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartOvf()
      pinUndefined(sutStartOvf, cellKey(faCallShape,
                   mode & "procValueClosureStartEnvUnchecked"),
                   UbKind(ubSignedOverflow), tLabel("t"))
      gStartEnvOvf = nil

  test "a captured ptr: confirmed, not lifted, and the hint says why":
    mkStartPtr()
    let r = symexFind(sutStartPtr, tLabel("t"))
    gStartEnvPtr = nil
    checkpoint show(r.errors)
    check not r.trusted
    if hostAdmission().isNone:
      var named = false
      when replayForks:
        check r.status == sxSat
        check UbKind(ubTailUnverified) in r.soundness.undefinedKinds
        for e in r.errors:
          if e.kind == feReplayDeclined and "`gStartEnvPtr`" in e.msg and
             "not its bytes alone" in e.msg and "ubTailUnverified" in e.msg:
            named = true
      else:
        # No fork (Windows): the re-executed child cannot be handed the
        # address, so the replay does not run and nothing confirms the hit.
        # The decline names the variable and why, as the forked hint does.
        check r.status == sxUnknown
        for e in r.errors:
          if e.kind == feReplayDeclined and "`gStartEnvPtr` holds" in e.msg and
             "not its bytes alone" in e.msg and
             "a Linux or macOS run forks" in e.msg:
            named = true
      check named
