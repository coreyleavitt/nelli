## RFC-0016 CR4-H1 (round 3). The pushing template, in a file only
## `s0016_int6u_zinc` includes.
template rangeOffInc*(body: untyped) =
  {.push rangeChecks: off.}
  body
  {.pop.}
