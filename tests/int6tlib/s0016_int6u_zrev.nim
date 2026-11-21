## RFC-0016 CR4-H1 (round 3). The reverse of `zinc`: the pushing template is
## in the includer, the routine that sits in its call is in the included file.
import nelli/symex

template rangeOffRev(body: untyped) =
  {.push rangeChecks: off.}
  body
  {.pop.}

include ./s0016_int6u_zrevbody
