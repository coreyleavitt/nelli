## RFC-0016 K9d-8. A suite module that imports `pinFind` alone
## (`from ./s8cu_helpers import pinFind`), as `tsymex_phase15_F5_float_conv`
## and seven other suites import the helpers selectively. `pinFind`'s
## expansion named its helpers (`setStringHints`, `boundaryOf`, `witnessAs`,
## `nativeRun`, `showArg`, ...) as bare identifiers, so they resolved in the
## caller's scope and did not compile here. They are bound in the helpers'
## module now (open, so a suite's own `boundaryOf` overload still applies).
## `tsymex_0016_k9d_pinfind` calls the probes below.
import nelli/symex
from ./s8cu_helpers import pinFind

proc selSat(x: float; n: int) =
  if x > 0.5 and n == 3: symexTarget("hit")

proc selUnsat(x: float32) =
  if x != x and x == x: symexTarget("hit")

proc selectiveSat*(): SymexStatusKind = pinFind(selSat, tLabel("hit")).status
proc selectiveUnsat*(): SymexStatusKind = pinFind(selUnsat, tLabel("hit")).status
