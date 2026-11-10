## RFC-0016 W3-z R11. A module-level closure variable that holds, when the run
## starts, a closure whose environment captures a `string`, a `seq` of plain
## values, or an object of them, under a forked replay (the host's default on
## Linux and macOS). The re-executed half is in `tsymex_0016_prc02_reexec`
## (the same SUTs, `helpers/r11_closstr_sut`).
##
## Such an environment's type has a destructor the compiler generated, which
## frees the captured buffers and runs no user code: it is no route the scan
## misses (`closureRouteGuard`'s benign set, `envBenignWhy`). An environment
## that captures a value whose type has a user hook still declines, naming
## the variable (`tsymex_0016_w3z_r11_hooked`: a module that declares a hook
## declines the replay of a value of any type it declares, so the hooked type
## is kept apart from this module's object).
import std/[unittest, strutils, options]
import nelli
import nelli/symex
import nelli/smt/types
from nelli/smt/runtime import hostAdmission
import ./s8cu_helpers except show
import helpers/r11_closstr_sut

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  parts.join("\n")

# An object of this module holding a string: its hooks are the compiler's.
type BoxR11 = object
  s: string
  n: int

var gStartBox: proc (v: int): int
proc mkStartBox() =
  var b = BoxR11(s: "abcd", n: 1)
  gStartBox = proc (v: int): int = v + b.s.len + b.n
proc runStartBox(v: int) {.symexOpaque.} =
  if v == 99: mkStartBox()
  gStrOut = gStartBox(v)
proc sutStartBox(v: int) =
  symexAssume(v == 3)
  runStartBox(v)
  if gStrOut == 8: symexTarget("t")


suite "W3-z R11: a start-value closure whose environment holds buffers (fork)":
  test "the walker's version floor (R11)":
    check parseInt(symexWalkerVersion) >= 345

  test "a captured string, a checked routine: exact":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartStr()
      discard pinExact(sutStartStr, cellKey(faCallShape,
                       "fork/procValueClosureStartStr"), tLabel("t"))
      gStartStr = nil

  test "a captured seq[int] whose element makes an unchecked routine overflow":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartSeqOvf()
      pinUndefined(sutStartSeqOvf, cellKey(faCallShape,
                   "fork/procValueClosureStartSeqUnchecked"),
                   UbKind(ubSignedOverflow), tLabel("t"))
      gStartSeqOvf = nil

  test "the run appends to the captured string: exact":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartStrMut()
      discard pinExact(sutStartStrMut, cellKey(faCallShape,
                       "fork/procValueClosureStartStrMut"), tLabel("t"))
      gStartStrMut = nil

  test "a captured object of a string and an int, no user hook: exact":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartBox()
      discard pinExact(sutStartBox, cellKey(faCallShape,
                       "fork/procValueClosureStartBox"), tLabel("t"))
      gStartBox = nil

  test "two captured values, a string among them: a fork copies them, exact":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      mkStartTwo()
      discard pinExact(sutStartTwo, cellKey(faCallShape,
                       "fork/procValueClosureStartTwo"), tLabel("t"))
      gStartTwo = nil
