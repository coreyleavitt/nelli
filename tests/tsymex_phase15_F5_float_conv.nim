import std/unittest
import proptest/symex

# Phase 15 — Cluster F cycle F5: int<->float conversions.
# int->float via rmRNE; float->int via rmRTZ truncation (OQ2). Out-of-range
# float->int overflow -> sxRaised(RangeDefect) is deferred to post-cluster-E
# (sxRaised does not exist yet); these tests exercise the in-range paths.

proc i2f(x: int) =
  if float(x) > 1.5: symexTarget("i2f")            # satisfiable for x >= 2
proc f2i(x: float) =
  if int(x) == 3: symexTarget("f2i")               # satisfiable for x in [3.0, 4.0)
proc i2f32(x: int) =
  if float32(x) == 5.0'f32: symexTarget("i2f32")   # satisfiable for x == 5

suite "symex Phase 15 — F5 int<->float conversions":

  test "int->float: float(x) > 1.5 -> sat":
    check symexFind(i2f, tLabel("i2f")).status == sxSat

  test "float->int: int(x) == 3 -> sat":
    check symexFind(f2i, tLabel("f2i")).status == sxSat

  test "int->float32: float32(x) == 5.0 -> sat":
    check symexFind(i2f32, tLabel("i2f32")).status == sxSat
