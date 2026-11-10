## RFC-0016 W3-z P8: SUTs that live in an imported module, where `isMainModule`
## is false (the compiler folds it per using module).
import nelli
import nelli/symex

proc sutIsMainImported*(a: int) =
  if isMainModule and a == 3: symexTarget("hit")

proc sutNotMainImported*(a: int) =
  if not isMainModule and a == 3: symexTarget("hit")
