## Helper for `tsymex_rfc0005_r1_keyimpl.nim` (review R1-09): the opaque
## callee is the same; what it calls differs.
import nelli
import nelli/symex

proc innerK(x: int): int = x + 2
proc helperK*(x: int): int {.symexOpaque.} = innerK(x)

proc sutK*(x: int) =
  if helperK(x) == 3: symexTarget("k")
