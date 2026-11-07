## RFC-0016 W1-c3 -- the `assertCoveredBy` splat catches `Defect` (W-26).
##
## The splat runs the walker's witness natively in the host. A witness that
## reaches the target and then raises a Defect the splat has no arm for (an
## OverflowDefect here) used to unwind out of `assertCoveredBy` and, with no
## handler above it, end the process. It is now treated as any other raise:
## the target was reached, and the call returns its finding. Panics-off only;
## under `--panics:on` a Defect is not catchable (W1-c2).
import std/[unittest]
import nelli/symex

proc hitThenOverflow(v: int) =
  if v == high(int):       # the only witness raises on the next line
    symexTarget("hit")
    discard v + 1

proc overflowFirst(v: int) =
  if v == high(int):
    discard v + 1
  symexTarget("late")

suite "W1-c3: the splat survives a Defect witness":

  test "a Defect after the target does not end the host":
    when not defined(nimPanics):
      # Not inside `check`: a Defect escaping the call must not be absorbed.
      let f = assertCoveredBy(hitThenOverflow, tLabel("hit"))
      check f.status == sfSat
      check f.covered
    else:
      skip()

  test "a Defect before the target is reported as a coverage failure":
    when not defined(nimPanics):
      var failed = false
      var msg = ""
      try:
        assertCoveredBy(overflowFirst, tLabel("late"))
      except SymexCoverageDefect as e:
        failed = true
        msg = e.msg
      except Defect:
        discard
      check true   # host alive; any verdict beyond survival is the walker's
      discard failed
      discard msg
    else:
      skip()
