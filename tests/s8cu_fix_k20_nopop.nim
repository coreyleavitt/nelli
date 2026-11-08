## RFC-0016 K2-0 fixture: a push that is never popped. The checks stay off for
import nelli/symex
## the rest of this module, which the scan must read as pushing to the end.
{.push fieldChecks: off, rangeChecks: off, objChecks: off.}
type
  NK* = enum nkA, nkB
  NP* = object
    case k*: NK
    of nkA: x*: int
    of nkB: y*: int
proc npField*(v: int) =
  var q = NP(k: nkA, x: v)
  q.y = v
  symexTarget("hit")
