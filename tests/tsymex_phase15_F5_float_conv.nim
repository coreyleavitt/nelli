import std/unittest
import nelli/symex

# Phase 15 — Cluster F cycle F5: int<->float conversions.
# int->float via rmRNE; float->int via rmRTZ truncation (OQ2).
#
# R16-2 update: float->int on an unconstrained float now forks a RangeDefect
# raise path (for out-of-range/NaN/Inf values). The raise is a defect so it
# surfaces as the PRIMARY finding (first in w.found) even when searching for
# a sat label. Tests updated to reflect the new behavior.

proc i2f(x: int) =
  if float(x) > 1.5: symexTarget("i2f")            # satisfiable for x >= 2
proc f2i(x: float) =
  if int(x) == 3: symexTarget("f2i")               # satisfiable for x in [3.0, 4.0)
proc i2f32(x: int) =
  if float32(x) == 5.0'f32: symexTarget("i2f32")   # satisfiable for x == 5

suite "symex Phase 15 — F5 int<->float conversions":

  test "int->float: float(x) > 1.5 -> sat":
    check symexFind(i2f, tLabel("i2f")).status == sxSat

  test "float->int: unconstrained int(x) → sxRaised(RangeDefect) (R16-2)":
    ## R16-2: an unconstrained float passed to int() can be NaN/Inf/huge,
    ## which raises RangeDefect in Nim. The raise is the primary finding.
    ## The in-range sat path (x=3.0) is also present but discovered second.
    let rRaise = symexFind(f2i, tRaisedExn("RangeDefect"))
    check rRaise.status == sxRaised

  test "int->float32: float32(x) == 5.0 -> sat":
    check symexFind(i2f32, tLabel("i2f32")).status == sxSat
