## RFC-0016 int6-w: the module `tsymex_0016_int6w_scantext` rewrites while it
## compiles. Do not edit by hand: the test strips its marker lines, and a
## marker line left here by an interrupted compile is removed by the next.
import nelli/symex

{.push overflowChecks: off.}
proc offShifted*(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")
{.pop.}

proc chkShifted*(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")
