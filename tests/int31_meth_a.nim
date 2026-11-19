## Helper for `tsymex_0016_int31_keyholes.nim` (INT-31, W-18): the SUT is
## the same in each `int31_meth_*` module; only what the override calls
## differs (`int31_meth_b`'s ends the process).
import nelli
import nelli/symex

type
  Base* = ref object of RootObj
  Der* = ref object of Base

var freshM = false
proc freshFalse(a: bool): bool {.inline.} = freshM and (a or not a)

proc helperM() {.symexTransparent.} = discard

method poke*(o: Base) {.base.} = discard
method poke*(o: Der) = helperM()

proc sutM*(a: bool; x: int) =
  let o: Base = Der()
  o.poke()
  if not freshFalse(a) and x == 42: symexTarget("k")
