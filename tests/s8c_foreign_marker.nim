## RFC-0005 S8c helper module (not a test file): a SUT that declares its OWN
## `symexAssume` -- a plain no-op proc that merely shares the DSL marker's
## name. It lives in its own module because a module importing nelli's marker
## could not also declare a same-signature proc (ambiguity). The SUT's target
## is reachable for real (x == 2); read as nelli's marker, the "assume"
## would prune it (a false sxUnsat).
from nelli/engine/markers import symexTarget

proc symexAssume*(cond: bool) =
  ## NOT nelli's marker: a user proc that ignores its argument.
  discard cond

proc s8cForeignAssume*(x: int) =
  symexAssume(x == 1)
  if x == 2:
    symexTarget("s8c_foreign_assume")
