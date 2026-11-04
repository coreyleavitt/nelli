## Helper for `tsymex_rfc0005_r1_keyimpl.nim` (review R1-09): the SUT is the
## same in each `r1_keyimpl_*` module; only its opaque callee differs.
import nelli
import nelli/symex

{.push overflowChecks: off.}
proc helperK*(x: int): int {.symexOpaque.} = x + 1
{.pop.}

proc sutK*(x: int) =
  if helperK(x) == 3: symexTarget("k")
