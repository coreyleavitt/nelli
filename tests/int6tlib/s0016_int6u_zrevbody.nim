## Included by `s0016_int6u_zrev`, whose template this file calls.
type RR = range[0 .. 10]

rangeOffRev:
  proc innerRev(w: int): int = int(RR(w))

proc outerRev*(v: int) =
  if innerRev(v) == 300: symexTarget("hit")
