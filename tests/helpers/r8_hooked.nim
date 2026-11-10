## RFC-0016 W3-z R8. A closure whose captured environment holds a value with a
## user `=destroy`: dropping the environment runs the hook. Kept apart from the
## PRC-02 test module, whose replays decline a value of a type declared in a
## module that declares a hook.

type HookedCap = object
  x: int
var gHookSeen*: int
proc `=destroy`(h: HookedCap) = gHookSeen = h.x

proc mkHooked*(): proc (v: int): int =
  var h = HookedCap(x: 1)
  result = proc (v: int): int = v + h.x
