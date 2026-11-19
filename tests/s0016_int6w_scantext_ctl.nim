## RFC-0016 int6-w: the control of `tsymex_0016_int6w_scantext`, the same
## routines in a module nothing rewrites.
import nelli/symex

{.push overflowChecks: off.}
proc offSteady*(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")
{.pop.}

proc chkSteady*(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")
