## RFC-0016 W3-z R12. A module-level closure variable that holds, when the run
## starts, a closure whose environment R11's route guard declined, under a
## forked replay (the host's default on Linux and macOS). The re-executed half
## is in `tsymex_0016_prc02_reexec` (the same SUTs, `helpers/r12_closenv_sut`).
##
## * Two or more captured values of one type (two strings, three seqs).
## * A captured value of a library type (`HSlice[string, string]`, `Table[int,
##   string]`). The hook probe resolves `=destroy` to the hook the type
##   carries wherever it is declared, a library's counted. An object of
##   another user module still declines, at the route scan (its copy hooks).
## * A closure of a routine nested in a nested one: its environment links to
##   the enclosing routine's, whose destructor the compiler generates too.
import std/[unittest, strutils, options]
import nelli
import nelli/symex
import nelli/smt/types
from nelli/smt/runtime import hostAdmission
import ./s8cu_helpers except show
import helpers/r12_closenv_sut
import helpers/r12_hooked

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  parts.join("\n")

suite "W3-z R12: a start-value closure R11 declined (fork)":
  test "the walker's version floor (R12)":
    check parseInt(symexWalkerVersion) >= 346

  test "two captured strings: exact":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartStrPair()
      discard pinExact(sutStartStrPair, cellKey(faCallShape,
                       "fork/procValueClosureStartStrPair"), tLabel("t"))
      gStartStrPair = nil

  test "three captured seqs, one making an unchecked routine overflow":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartSeqTrio()
      pinUndefined(sutStartSeqTrio, cellKey(faCallShape,
                   "fork/procValueClosureStartSeqTrio"),
                   UbKind(ubSignedOverflow), tLabel("t"))
      gStartSeqTrio = nil

  test "a captured library HSlice[string, string]: exact":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartSlice()
      discard pinExact(sutStartSlice, cellKey(faCallShape,
                       "fork/procValueClosureStartSlice"), tLabel("t"))
      gStartSlice = nil

  test "a captured library Table[int, string]: the route stands, confirmed":
    # R11 declined the route (a library type's hooks were not read). The
    # replay confirms the hit; the lookup's hash arithmetic is unchecked,
    # which keeps the claim's own undefinedness open (not this slice's).
    mkStartTable()
    let r = symexFind(sutStartTable, tLabel("t"))
    gStartTable = nil
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    for e in r.errors:
      check e.kind != feGlobalRouteUnproved

  test "a captured object declared in another module still declines":
    # Proven unliftable here: the builder's code holds a value of a type of
    # another module, and a `=copy` or `=sink` that module does not export
    # resolves by overload, so no probe outside it can see one
    # (`routeProbeRead`). The environment's own hooks are type-bound and read.
    mkStartForeignBox()
    let r = symexFind(sutStartForeignBox, tLabel("t"))
    gStartForeignBox = nil
    checkpoint show(r.errors)
    check not r.trusted
    var named = false
    for e in r.errors:
      if e.kind == feGlobalRouteUnproved and "`BoxR12` is declared in " &
         "another module" in e.msg:
        named = true
    check named

  test "a closure of a routine nested in a nested one: exact":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartNested()
      discard pinExact(sutStartNested, cellKey(faCallShape,
                       "fork/procValueClosureStartNested"), tLabel("t"))
      gStartNested = nil

  test "a captured object whose module hides a =destroy still declines":
    mkStartForeignHooked()
    let r = symexFind(sutStartForeignHooked, tLabel("t"))
    gStartForeignHooked = nil
    checkpoint show(r.errors)
    check not r.trusted
    check r.errors.named(feGlobalRouteUnproved)
