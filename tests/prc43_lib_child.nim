## RFC-0016 PRC-43: the child `tsymex_0016_prc43_libpath` builds under a
## `--lib:` override. It prints the walker's verdict on a `math.ceilDiv` it
## models exactly when the stdlib is recognised as the stdlib.
import std/math
import nelli
import nelli/symex

proc sCeil(x: int) =
  if x >= 1 and x <= 99 and ceilDiv(x, 7) == 3: symexTarget("hit")

let r = symexFind(sCeil, tLabel("hit"))
echo "VERDICT status=", r.status, " trusted=", r.trusted, " errors=", r.errors.len
for e in r.errors: echo "ERR ", e.kind
