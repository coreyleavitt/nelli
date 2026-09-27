import std/unittest
import nelli/symex

# Phase 15 — Cluster F cycle F5: int<->float conversions.
# int->float via rmRNE; float->int via rmRTZ truncation (OQ2).
#
# RFC-0005 S8g: float->int never raises (Nim 2.2.10 casts first and checks the
# cast value); out of range the model gives a fresh, degrade-tainted value.

proc i2f(x: int) =
  if float(x) > 1.5: symexTarget("i2f")            # satisfiable for x >= 2
proc f2i(x: float) =
  if int(x) == 3: symexTarget("f2i")               # satisfiable for x in [3.0, 4.0)
proc i2f32(x: int) =
  if float32(x) == 5.0'f32: symexTarget("i2f32")   # satisfiable for x == 5

suite "symex Phase 15 — F5 int<->float conversions":

  test "int->float: float(x) > 1.5 -> sat":
    check symexFind(i2f, tLabel("i2f")).status == sxSat

  test "float->int: unconstrained int(x) never raises; int(x)==3 is sat (S8g)":
    ## RFC-0005 S8g: Nim's int(f) never raises (probed: int(1e30), int(NaN),
    ## int(Inf) give low(int)); the R16-2 RangeDefect fork was fictional.
    check symexFind(f2i, tRaisedExn("RangeDefect")).status == sxUnsat
    let r = symexFind(f2i, tLabel("f2i"))
    check r.status == sxSat
    if r.status == sxSat: check int(r.witness[0]) == 3

  test "int->float32: float32(x) == 5.0 -> sat":
    check symexFind(i2f32, tLabel("i2f32")).status == sxSat
