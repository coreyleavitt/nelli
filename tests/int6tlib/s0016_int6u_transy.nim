## RFC-0016 CR4-H1 (round 3). The pushing template of the transitive case:
## `s0016_int6u_transx` wraps it, the test imports only that one.
template rangeOffY*(body: untyped) =
  {.push rangeChecks: off.}
  body
  {.pop.}
