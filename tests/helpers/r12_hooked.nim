## RFC-0016 W3-z R12. A closure whose captured environment holds an object
## declared here with a `=destroy` this module does not export: dropping the
## environment runs it. The check runs in another module, where no overload
## of the hook is visible. A guard pin: it must decline whichever rule reads
## it first (today the route scan's rule for a type of another module, whose
## copy hooks no probe outside it can rule out; the environment's own hook
## probe resolves `=destroy` to the hook the type carries). Kept apart from
## `r12_closenv_sut`: a module that declares a hook declines the replay of a
## value of any type it declares.
import nelli
import nelli/symex

type HookedR12 = object
  x: int
var gHookR12Seen*: int
proc `=destroy`(h: HookedR12) = gHookR12Seen = h.x

var gR12HookOut*: int
var gStartForeignHooked*: proc (v: int): int
proc mkStartForeignHooked*() =
  var h = HookedR12(x: 1)
  gStartForeignHooked = proc (v: int): int = v + h.x
proc runStartForeignHooked(v: int) {.symexOpaque.} =
  if v == 99: mkStartForeignHooked()
  gR12HookOut = gStartForeignHooked(v)
proc sutStartForeignHooked*(v: int) =
  symexAssume(v == 3)
  runStartForeignHooked(v)
  if gR12HookOut == 4: symexTarget("t")
