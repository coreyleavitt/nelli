## RFC-0005 W3 (WA-3). A module that compiles `assert` out around a `for` over a
## seq: `items[T]` takes the options of its first instantiation, so the walker's
## model of its length assert is not known here. `uint8` and `int8` are
## instantiated nowhere else under the suite.
import nelli/symex

{.push assertions: off.}
proc itemsPopOff*(v: int) =
  if v == 4:
    var s = @[1'u8, 2, 3]
    for _ in s: discard s.pop()
    symexTarget("hit")
{.pop.}

proc itemsPopOutside*(v: int) =
  if v == 4:
    var s = @[1'i8, 2, 3]
    for _ in s: discard s.pop()
    symexTarget("hit")
