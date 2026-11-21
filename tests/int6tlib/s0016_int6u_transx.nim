## RFC-0016 CR4-H1 (round 3). A template that pushes nothing itself: its
## text calls `rangeOffY` of a module the test never imports.
import ./s0016_int6u_transy

template wrapX*(body: untyped) =
  rangeOffY(body)
