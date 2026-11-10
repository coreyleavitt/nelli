## RFC-0016 W3-z R11. A module-level closure variable that holds, when the run
## starts, a closure whose environment captures an object with a user
## `=destroy` declared in the module the check runs in: the hook probe
## (`symexEnvHooksFree`) sees the hook, so the environment is not benign and
## the route stays open, naming the variable (R8's reason). Kept apart from
## `tsymex_0016_w3z_r11_closstr`: a module that declares a hook declines the
## replay of a value of any type it declares, that file's object included.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  parts.join("\n")

var gHookOut: int

type HookedR11 = object
  x: int
var gHookR11: int
proc `=destroy`(h: HookedR11) = gHookR11 = h.x

var gStartHooked: proc (v: int): int
proc mkStartHooked() =
  var h = HookedR11(x: 1)
  gStartHooked = proc (v: int): int = v + h.x
proc runStartHooked(v: int) {.symexOpaque.} =
  if v == 99: mkStartHooked()
  gHookOut = gStartHooked(v)
proc sutStartHooked(v: int) =
  symexAssume(v == 3)
  runStartHooked(v)
  if gHookOut == 4: symexTarget("t")

suite "W3-z R11: a captured object with a user hook":
  test "the walker's version floor (R11)":
    check parseInt(symexWalkerVersion) >= 345

  test "a captured object with a user =destroy still declines, named":
    mkStartHooked()
    let r = symexFind(sutStartHooked, tLabel("t"))
    gStartHooked = nil
    checkpoint show(r.errors)
    check not r.trusted
    var named = false
    for e in r.errors:
      if e.kind == feGlobalRouteUnproved and "`gStartHooked`" in e.msg and
         "environment" in e.msg:
        named = true
    check named
